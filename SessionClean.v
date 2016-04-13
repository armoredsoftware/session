Require Export Crypto.
Require Import Program.
Require Import Arith.
Require Import Eqdep_dec.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import CpdtTactics.



Inductive protoType : Type :=
| Send : type -> protoType -> protoType
| Receive : type -> protoType -> protoType
| Choice : protoType -> protoType -> protoType
| Offer : protoType -> protoType -> protoType  
| Eps : type -> protoType.
                                                 
Inductive protoExp : type -> protoType -> Type :=
| SendC {t:type} {T:type} {p':protoType}  : (message t) -> (protoExp T p')
    -> protoExp T (Send t p')
| ReceiveC {t:type} {T:type} {p':protoType} : ((message t)->(protoExp T p'))     -> protoExp T  (Receive t p') 
| ChoiceC (b:bool) {r s:protoType} {R S:type} :(protoExp R r) -> (protoExp S s)
    -> (protoExp (if(b) then R else S) (Choice r s))
| OfferC {r s : protoType} {R S:type} : (protoExp R r) -> (protoExp S s)
                                        -> protoExp (Either R S) (Offer r s)
| ReturnC {t:type} : (message t) -> protoExp t (Eps t).


Notation "x :!: y" := (Send x y)
                        (at level 50, left associativity). 
Notation "x :!: y" := (protoExp (Send x y))
                        (at level 50, left associativity).

Notation "x :?: y" := (Receive x y)
                        (at level 50, left associativity).  
Notation "x :?: y" := (protoExp (Receive x y))
                        (at level 50, left associativity).

Notation "x :+: y" := (Choice x y)
                        (at level 50, left associativity).
Notation "x :+: y" := (protoExp (Choice x y))
                        (at level 50, left associativity).  

Notation "x :&: y" := (Offer x y)
                        (at level 50, left associativity).
Notation "x :&: y" := (protoExp (Offer x y))
                        (at level 50, left associativity). 

Notation "'send' n ; p" := (SendC n p)
                            (right associativity, at level 60).
Notation "x <- 'receive' ; p " := (ReceiveC (fun x => p)) 
                                    (right associativity, at level 60). 

Notation "'offer'" := OfferC.

Notation "'choice'" := ChoiceC.  

Definition EpsC := ReturnC (basic 0).

Fixpoint DualT (t t':protoType) : Prop :=
  match t with
  | Send p1T p1' =>
    match t' with
    | Receive p2T p2' => (p1T = p2T) /\ (DualT p1' p2')    
    | _ => False
    end
  | Receive p1T p1' =>
    match t' with
    | Send p2T p2' => (p1T = p2T) /\ (DualT p1' p2')                                
    | _ => False
    end
  | Choice p1' p1'' =>
    match t' with
    | Offer p2' p2'' => (DualT p1' p2') /\ (DualT p1'' p2'')                                                             
    | _ => False
    end
  | Offer p1' p1'' =>
    match t' with
    | Choice p2' p2'' => (DualT p1' p2') /\ (DualT p1'' p2'')                                                               
    | _ => False
    end
  | Eps _ =>
    match t' with
    | Eps _ => True           
    | _ => False
    end
  end.

Fixpoint DualT_dec (t t':protoType) : {DualT t t'} + {~ DualT t t'}.
Proof.
  destruct t; destruct t';

  (* Eliminate all un-interesting cases *)
  try (right; unfold not; intros; inversion H; contradiction);

  (* For the Send/Receive, Receive/Send cases *)
  try (
  destruct (eq_type_dec t t1); destruct (DualT_dec t0 t');
  try (right; unfold not; intros; inversion H; contradiction);
  try (left; split; assumption)
  );

  (* For the Choice/Offer, Offer/Choice cases *)
  try (
  destruct (DualT_dec t1 t'1); destruct (DualT_dec t2 t'2);
  try (right; unfold not; intros; inversion H; contradiction);
  try( left; split; assumption)
    ).

  (* Eps/Eps case *)
  left. simpl. trivial.
  
Defined.

Definition Dual {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') : Prop := DualT t t'.

Fixpoint runProto {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') 
  : (Dual p1 p2) -> (message T).
Proof.

       intro pf. destruct p1 (*eqn : p1Val*); destruct p2 (*eqn : p2Val*); try (inversion pf).

       subst. apply (runProto _ _ _ _ p1 (p m)). unfold Dual. assumption.
       subst. apply (runProto _ _ _ _ (p m) p2). unfold Dual. assumption.

       destruct b.
       apply (runProto _ _ _ _ p1_1 p2_1 ). unfold Dual. assumption.
       apply (runProto _ _ _ _ p1_2 p2_2 ). unfold Dual. assumption.
       
       destruct b.
       assert (message R).
       apply (runProto _ _ _ _ p1_1 p2_1 ). unfold Dual. assumption. exact (leither _ _ X).
       assert (message S).
       apply (runProto _ _ _ _ p1_2 p2_2 ). unfold Dual. assumption. exact (reither _ _ X).

       exact m.
Defined.

(*Definition realType{t:type} (m:message t) : type :=
  match m with
  | leither t1 _ _ => t1
  | reither _ t2 _ => t2
  | _ => t
  end.

Definition realEither (t:type) (b:bool) : type :=
  match t with
  | Either t1 t2 => if b then t1 else t2
  | _ => t
  end.

Fixpoint realEither'{t t':protoType} {T T':type}
           (p1:protoExp T t) (p2:protoExp T' t') : type :=
  match p1 with
  | OfferC p1' p1'' =>
    match p2 with
    | ChoiceC b p2' p2'' => realEither T b
    | _ => T
    end
  | SendC m p1' =>
    match p2 with
    | ReceiveC f => realEither' p1' (f (bad (funType f)))
    | _ => T
    end
  | _ => T
  end.

Hint Unfold realEither' realEither.
*)


Inductive runProtoBigStep : forall (T T':type), forall (t t':protoType) (p1:protoExp T t) (p2:protoExp T' t') (m:message T)(*(realEither' p1 p2))*), Prop :=
  
| returnR : forall T T' (m:message T) (m':message T'),
    runProtoBigStep _ _ _ _ (ReturnC m) (ReturnC m') m
| sendR : forall X Y Y' p1t p2t
            (p1':protoExp Y p1t)
            (f: ((message X) -> (protoExp Y' p2t)))
            (m:message X) m'(*(m':message (realEither' p1' (f m)))*)
            ,
                   
        runProtoBigStep _ _ p1t p2t p1' (f m) m' ->
        runProtoBigStep _ _ _ _ (SendC m p1') (ReceiveC f) m'
| receiveR : forall X Y Y' p1t p2t m'
            (m:message X)
            (f: ((message X) -> (protoExp Y' p2t)))
            (p1':protoExp Y p1t),
            runProtoBigStep _ _ _ _ (f m) p1' m' ->
            runProtoBigStep _ _ _ _ (ReceiveC f) (SendC m p1') m'
| choiceRt : forall R R' S S' r r' s s'
               (r:protoExp R r) (r0:protoExp R' r')
               (s:protoExp S s) (s0:protoExp S' s')
               (m:message R) (m':message S),
    runProtoBigStep _ _ _ _ r r0 m ->
    runProtoBigStep _ _ _ _ s s0 m' ->
    runProtoBigStep _ _ _ _ (ChoiceC true r s) (OfferC r0 s0) m

| choiceRf : forall R R' S S' r r' s s'
               (r:protoExp R r) (r0:protoExp R' r')
               (s:protoExp S s) (s0:protoExp S' s')
               (m:message R) (m':message S),
    runProtoBigStep _ _ _ _ r r0 m ->
    runProtoBigStep _ _ _ _ s s0 m' ->
    runProtoBigStep _ _ _ _ (ChoiceC false r s) (OfferC r0 s0) m'

| offerRt : forall R R' S S' r r' s s' m m'
              (r:protoExp R r) (r0:protoExp R' r')
              (s:protoExp S s) (s0:protoExp S' s'),
    runProtoBigStep _ _ _ _ r r0 m ->
    runProtoBigStep _ _ _ _ s s0 m' ->
    runProtoBigStep _ _ _ _ (OfferC r s) (ChoiceC true r0 s0) (leither _ _ m) 

| offerRf : forall R R' S S' r r' s s' m m'
              (r:protoExp R r) (r0:protoExp R' r')
              (s:protoExp S s) (s0:protoExp S' s'),
    runProtoBigStep _ _ _ _ r r0 m ->
    runProtoBigStep _ _ _ _ s s0 m' ->
    runProtoBigStep _ _ _ _ (OfferC r s) (ChoiceC false r0 s0) (reither _ _ m').

Inductive step : forall (T R T' T'':type), forall (t r t' t'':protoType), (protoExp T t) -> (protoExp R r) -> ( (protoExp T' t') * (protoExp T'' t'') ) -> Prop :=
| ST_Send_Rec : forall X x Y y  mt
                  (m:message mt) (p1':protoExp X x)
                  (f:(message mt) -> protoExp Y y),
    step _ _ _ _ _ _ _ _ (SendC m p1') (ReceiveC f) (p1', (f m))
| ST_Rec_Send : forall X x Y y mt (m:message mt) (p1':protoExp X x)
                       (f:(message mt) -> protoExp Y y),                     
    step _ _ _ _ _ _ _ _ (ReceiveC f) (SendC m p1') ((f m), p1')
| ST_Choice_true : forall R R' S S' r r' s s'
                     (r:protoExp R r) (r0:protoExp R' r')
                     (s:protoExp S s) (s0:protoExp S' s'),
    step _ _ _ _ _ _ _ _ (ChoiceC true r s) (OfferC r0 s0) (r, r0)
| ST_Choice_false : forall R R' S S' r r' s s'
                     (r:protoExp R r) (r0:protoExp R' r')
                     (s:protoExp S s) (s0:protoExp S' s'),
    step _ _ _ _ _ _ _ _ (ChoiceC false r s) (OfferC r0 s0) (s,s0)
| ST_Offer_true : forall R R' S S' r r' s s'
                     (r:protoExp R r) (r0:protoExp R' r')
                     (s:protoExp S s) (s0:protoExp S' s'),
    step _ _ _ _ _ _ _ _ (OfferC r0 s0) (ChoiceC true r s)  (r0, r)
| ST_Offer_false : forall R R' S S' r r' s s'
                     (r:protoExp R r) (r0:protoExp R' r')
                     (s:protoExp S s) (s0:protoExp S' s'),
    step _ _ _ _ _ _ _ _ (OfferC r0 s0) (ChoiceC false r s) (s0, s).

Definition proto1 :=
  send (basic 1);
  EpsC.

Definition proto2 :=
  x <- receive;
  ReturnC (t:=Basic) x.

Notation "'stepe'" := (step _ _ _ _ _ _ _ _).

Example stepEx1 : stepe proto1 proto2 (EpsC, (ReturnC (basic 1))).
Proof.
  constructor.
Qed.

Definition proto3 (b:bool) :=
  choice b EpsC
         proto1. Check proto3.

Definition proto4 :=
  offer EpsC
        proto2. Check proto4.

Example stepEx2 : stepe (proto3 true) proto4 (EpsC, EpsC).
Proof.
  unfold proto3. unfold proto4. constructor.
Qed.

Example stepEx2' : stepe (proto3 false) proto4 (proto1, proto2).
Proof.
  constructor.
Qed.

Example stepEx3' : stepe proto4 (proto3 true) (EpsC, EpsC).
Proof.
  unfold proto3. unfold proto4. constructor.
Qed.

Example stepEx3 : stepe proto4 (proto3 false) (proto2, proto1).
Proof.
  constructor.
Qed.

Inductive multi : forall (T R T':type), forall (t r t':protoType), (protoExp T t) -> (protoExp R r) -> (protoExp T' t') -> Prop :=
| multi_refl : forall (T R T':type) (t r t':protoType) (x:protoExp T t) (y:protoExp R r),
    multi _ _ _ _ _ _ x y x
| multi_step : forall (T T' R R2 S:type) (t t' r r2 s:protoType),
    forall (x:protoExp T t) (x':protoExp T' t')
      (y:protoExp R r) (y2:protoExp R2 r2) (*(y':protoExp R' r') *)
      (z:protoExp S s),
                    step _ _ _ _ _ _ _ _ x x' (y, y2) ->
                    multi _ _ _ _ _ _ y y2 z ->
                    multi _ _ _ _ _ _ x x' z.

Notation "'multie'" := (multi _ _ _ _ _ _).

Definition incPayload (m:message Basic) : (message Basic) :=
  match m with
  | basic n => basic (n + 1)
  | _ => basic 0                 
  end.

Definition proto5 :=
  send (basic 1);
  x <- receive;
  ReturnC (t:=Basic) x.

Definition proto6 :=
  y <- receive;
  send (incPayload y);
  EpsC.

Example multiEx1 : multi _ _ _ _ _ _ proto5 proto6 (ReturnC (basic 2)).
Proof. Print multi_step. specialize multi_step. intros. apply H with (R:=Basic) (R2:=Basic) (r:=(Receive Basic (Eps Basic))) (r2:=(Send Basic (Eps Basic))) (y:=  x <- receive; ReturnC (t:=Basic) x) (y2:=send (incPayload (basic 1));EpsC). constructor. apply H with (R:=Basic) (R2:=Basic) (r:=(Eps Basic)) (r2:=(Eps Basic)) (y:= ReturnC (basic 2)) (y2:=EpsC). constructor. constructor. exact (Basic). exact (Eps Basic).
Qed.

Theorem big_multistep_equiv {t t':protoType} {T T':type} {p1:protoExp T t} {p2:protoExp T' t'} : forall m, runProtoBigStep _ _ _ _ p1 p2 m <->
                         multi _ _ _ _ _ _ p1 p2 (ReturnC m).
Proof.
  intros. split.

  (* -> *)
  generalize dependent t'. generalize dependent T'. dependent induction p1; destruct p2; try (intros H; inversion H; contradiction).
  intros H. dep_destruct H. specialize multi_step. intros H0. apply H0 with (R:=Y) (r:=p') (y:=p1) (y2:=p m). constructor. apply IHp1. assumption.
  intros H0. dep_destruct H0. specialize multi_step. intros H1. apply H1 with (R:=Y') (r:=p') (y:=p m0) (y2:=p2). constructor. apply H. assumption.

  intros HH. inversion HH.
  intros HH. inversion HH.
  intros HH. inversion HH.
  intros HH. inversion HH.
  intros H. dep_destruct H. specialize multi_step. intros H0. apply H0 with (R:=R) (r:=r) (y:=p1_1) (y2:=p2_1). constructor. apply IHp1_1. assumption.
  specialize multi_step. intros H0. apply H0 with (R:=S) (r:=s) (y:=p1_2) (y2:=p2_2). constructor. apply IHp1_2. assumption.
  
  intros H. dep_destruct H. specialize multi_step. intros H0. apply H0 with (R:=R) (r:=r) (y:=p1_1) (y2:=p2_1). constructor. (*apply IHp1_1.*) admit.
  specialize multi_step. intros H0. apply H0 with (R:=S) (r:=s) (y:=p1_2) (y2:=p2_2). constructor. (*apply IHp1_2.*) admit.

  intros H. dep_destruct H. constructor. exact (Basic). exact (Eps Basic).

  (* <- *)
  Admitted.

Theorem runProto_iff_multi{t t':protoType} {T T':type} {p1:protoExp T t} {p2:protoExp T' t'}{p:Dual p1 p2} : forall m,
      ((runProto p1 p2 p) = m) <-> multi _ _ _ _ _ _ p1 p2 (ReturnC m).
Proof.
  intros. split.

  (* -> *)
  generalize dependent t'. generalize dependent T'. dependent induction p1; destruct p2; try (intros H; inversion H; contradiction).
    intros. inversion p0. subst. specialize multi_step. intros H0. apply H0 with (R:=T) (r:=p') (y:=p1) (y2:=p m). constructor. apply IHp1 with (p:=H1). destruct p0. simpl. simpl_eq. cbn. assert (H1 = d). apply proof_irrelevance. rewrite H. reflexivity.
    intros. inversion p0. subst. specialize multi_step. intros H0. apply H0 with (R:=T) (r:=p') (y:=p m0) (y2:=p2). constructor. apply H with (p0:=H2). destruct p0. simpl. simpl_eq. cbn. assert (H2 = d). apply proof_irrelevance. rewrite H1. reflexivity.

    intros HH. inversion HH.
    intros HH. inversion HH.
    intros HH. inversion HH.
    intros HH. inversion HH.
    intros. destruct b.
    dep_destruct H. destruct p. specialize multi_step. intros H0. apply H0 with (R:=R) (r:=r) (y:=p1_1) (y2:=p2_1). constructor. apply IHp1_1 with (p:=d). reflexivity.
    dep_destruct H. destruct p. specialize multi_step. intros H0. apply H0 with (R:=S) (r:=s) (y:=p1_2) (y2:=p2_2). constructor. apply IHp1_2 with (p:=d0). reflexivity.
    intros. destruct b. dep_destruct H. destruct p. specialize multi_step. intros H0. apply H0 with (R:=R) (r:=r) (y:=p1_1) (y2:=p2_1). constructor. (*apply IHp1_1. *) admit.
    dep_destruct H. destruct p. specialize multi_step. intros H0. apply H0 with (R:=S) (r:=s)  (y:=p1_2) (y2:=p2_2). constructor. (*apply IHp1_2. *) admit.

    intros. dep_destruct H. destruct p. apply multi_refl. exact t. exact (Eps t).

    (* <- *)
    generalize dependent t'. generalize dependent T'. dependent induction p1; destruct p2; try (intros H; inversion H; contradiction).
    intros. inversion p0. subst. inversion H. simpl_existTs. subst.
    destruct p0. simpl. simpl_eq. cbn. dep_destruct H10. apply IHp1. assumption.
    intros.
    inversion p0. subst. inversion H0. simpl_existTs. subst.
    destruct p0. simpl. simpl_eq. cbn. dep_destruct H11. apply H. assumption.
    
    intros HH. inversion HH.
    intros HH. inversion HH.
    intros HH. inversion HH.                                                     intros HH. inversion HH.

    intros.  destruct b. inversion p. inversion H. simpl_existTs. subst. destruct p. simpl. apply IHp1_1. dep_destruct H11. assumption.
    inversion p. inversion H. simpl_existTs. subst. destruct p. simpl. apply IHp1_2. dep_destruct H11. assumption.

    intros. destruct b. inversion p. inversion H. simpl_existTs. subst. destruct p. simpl. (*apply IHp1_1.*) admit.

    inversion p. inversion H. simpl_existTs. subst. destruct p. simpl. (*apply IHp1_2. *) admit.
    
    intros. destruct p. simpl. inversion H. simpl_existTs. subst. inversion  H5. simpl_existTs. subst. reflexivity. simpl_existTs. subst. inversion H9.

    Admitted.

Theorem runProto_iff_bigStep{t t':protoType} {T T':type} {p1:protoExp T t} {p2:protoExp T' t'}{p:Dual p1 p2} : forall m,
    ((runProto p1 p2 p) = m) <-> runProtoBigStep _ _ _ _ p1 p2 m.
Proof.
  intro m.
  assert (((runProto p1 p2 p) = m) <-> multi _ _ _ _ _ _ p1 p2 (ReturnC m)).
  apply runProto_iff_multi.
  assert (runProtoBigStep _ _ _ _ p1 p2 m <->
          multi _ _ _ _ _ _ p1 p2 (ReturnC m)).
  apply big_multistep_equiv. symmetry in H0.
  apply (iff_trans H H0).
Qed.