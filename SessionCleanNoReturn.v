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
                                                 
Inductive protoExp : protoType -> Type :=
| SendC {t:type} {p':protoType}  : (message t) -> (protoExp p')
    -> protoExp (Send t p')
| ReceiveC {t:type} {p':protoType} : ((message t)->(protoExp p'))
                                     -> protoExp (Receive t p')
| ChoiceC (b:bool) {r s:protoType} :(protoExp r) -> (protoExp s)
    -> (protoExp (Choice r s))
| OfferC {r s : protoType} : (protoExp r) -> (protoExp s)
                                        -> protoExp (Offer r s)
| ReturnC {t:type} : (message t) -> protoExp (Eps t).

Fixpoint returnType (pt : protoType) : type :=
  match pt with
  | Eps t => t
  | Send _ pt' => returnType pt'
  | Receive _ pt' => returnType pt'
  | Choice pt' pt'' => Either (returnType pt') (returnType pt'')
  | Offer pt' pt'' => Either (returnType pt') (returnType pt'')
  end.
  

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

Definition Dual {t t':protoType} (p1:protoExp t) (p2:protoExp t') : Prop := DualT t t'.


Fixpoint retTypeReal {t t':protoType} (p1:protoExp t) (p2:protoExp t') 
  : (Dual p1 p2) -> type. 
Proof.
  intros. destruct p1; destruct p2; try inversion H.
  subst. apply (retTypeReal _ _ p1 (p m)). unfold Dual. assumption.
  subst. apply (retTypeReal _ _ (p m) p2). unfold Dual. assumption.
  destruct b.
  apply (retTypeReal _ _ p1_1 p2_1). unfold Dual. assumption.
  apply (retTypeReal _ _ p1_2 p2_2). unfold Dual. assumption.
  destruct b.
  apply (retTypeReal _ _ p1_1 p2_1). unfold Dual. assumption.
  apply (retTypeReal _ _ p1_2 p2_2). unfold Dual. assumption.
  exact t.
Defined.


Fixpoint runProto {t t':protoType} (p1:protoExp t) (p2:protoExp t')
  : (Dual p1 p2) -> (message (returnType t)).
Proof.

       intro pf. destruct p1 (*eqn : p1Val*); destruct p2 (*eqn : p2Val*); try (inversion pf).

       subst. apply (runProto _ _ p1 (p m)). unfold Dual. assumption.
       subst. apply (runProto _ _ (p m) p2). unfold Dual. assumption.

       destruct b.
       simpl. assert (message (returnType r)).
       apply (runProto _ _ p1_1 p2_1 ). unfold Dual. assumption.
       exact (leither _ _ X).
       simpl. assert (message (returnType s)).
       apply (runProto _ _ p1_2 p2_2 ). unfold Dual. assumption.
       exact (reither _ _ X).
       
       destruct b.
       assert (message (returnType r)).
       apply (runProto _ _ p1_1 p2_1 ). unfold Dual. assumption. exact (leither _ _ X).
       assert (message (returnType s)).
       apply (runProto _ _ p1_2 p2_2 ). unfold Dual. assumption. exact (reither _ _ X).
       exact m.
Defined.

  
Inductive runProtoBigStep : forall (t t':protoType) (rt:type) (p1:protoExp t) (p2:protoExp t') (m:message rt (*(realEither p1 p2)*) (*(returnType t)*)), Prop :=
  
| returnR : forall T T' (m:message T) (m':message T'),
    runProtoBigStep _ _ _ (ReturnC m) (ReturnC m') m
| sendR : forall X p1t p2t rt
            (p1':protoExp p1t)
            (f: ((message X) -> (protoExp p2t)))
            (m:message X) (m': message rt(*(returnType p2t)*)) (*(m':message (realEither p1' (f m)))*)
            ,
                   
        runProtoBigStep _ _ _ p1' (f m) m' ->
        runProtoBigStep _ _ _ (SendC m p1') (ReceiveC f) m'
| receiveR : forall X p1t p2t rt (m': message rt (*(returnType p2t)*)) (*TODO:  try p1t *)
            (m:message X)
            (f: ((message X) -> (protoExp p2t)))
            (p1':protoExp p1t),
            runProtoBigStep _ _ _ (f m) p1' m' ->
            runProtoBigStep _ _ _ (ReceiveC f) (SendC m p1') m'
| choiceRt : forall rt rt' st st' mt (m:message mt)
               (r:protoExp rt) (r0:protoExp rt')
               (s:protoExp st) (s0:protoExp st')
               (*(m:message (returnType rt)) (m':message (returnType st))*),
    runProtoBigStep _ _ _ r r0 m ->
    (*runProtoBigStep _ _ s s0 m' -> *)
    runProtoBigStep _ _ _ (ChoiceC true r s) (OfferC r0 s0) m (*(leither _ _ m) *)

| choiceRf : forall rt rt' st st' mt (m':message mt)
               (r:protoExp rt) (r0:protoExp rt')
               (s:protoExp st) (s0:protoExp st')
               (*(m:message (returnType rt)) (m':message (returnType st))*),
    (*runProtoBigStep _ _ r r0 m -> *)
    runProtoBigStep _ _ _ s s0 m' -> 
    runProtoBigStep _ _ _ (ChoiceC false r s) (OfferC r0 s0) m' (*(reither _ _ m')*)

| offerRt : forall rt rt' st st' mt (m : message mt(*(returnType rt)*)) (*m'*)
              (r:protoExp rt) (r0:protoExp rt')
              (s:protoExp st) (s0:protoExp st'),
    runProtoBigStep _ _ _ r r0 m ->
    (*runProtoBigStep _ _ s s0 m' -> *)
    runProtoBigStep _ _ _ (OfferC r s) (ChoiceC true r0 s0) m (*(leither _ _ m)*)

| offerRf : forall rt rt' st st' mt (*m*) (m' : message mt(*(returnType st)*))
              (r:protoExp rt) (r0:protoExp rt')
              (s:protoExp st) (s0:protoExp st'),
    (*runProtoBigStep _ _ r r0 m ->*)
    runProtoBigStep _ _ _ s s0 m' ->
    runProtoBigStep _ _ _ (OfferC r s) (ChoiceC false r0 s0) m'. (*(reither _ _ m') *)

Inductive step : forall (t r t' t'':protoType), (protoExp t) -> (protoExp r) -> ( (protoExp t') * (protoExp t'') ) -> Prop :=
| ST_Send_Rec : forall x y  mt
                  (m:message mt) (p1':protoExp x)
                  (f:(message mt) -> protoExp y),
    step _ _ _ _ (SendC m p1') (ReceiveC f) (p1', (f m))
| ST_Rec_Send : forall x y mt (m:message mt) (p1':protoExp x)
                       (f:(message mt) -> protoExp y),                     
    step _ _ _ _ (ReceiveC f) (SendC m p1') ((f m), p1')
| ST_Choice_true : forall rt rt' st st'
                     (r:protoExp rt) (r0:protoExp rt')
                     (s:protoExp st) (s0:protoExp st'),
    step _ _ _ _ (ChoiceC true r s) (OfferC r0 s0) (r, r0)
| ST_Choice_false : forall rt rt' st st'
                     (r:protoExp rt) (r0:protoExp rt')
                     (s:protoExp st) (s0:protoExp st'),
    step _ _ _ _ (ChoiceC false r s) (OfferC r0 s0) (s,s0)
| ST_Offer_true : forall rt rt' st st'
                     (r:protoExp rt) (r0:protoExp rt')
                     (s:protoExp st) (s0:protoExp st'),
    step _ _ _ _ (OfferC r0 s0) (ChoiceC true r s)  (r0, r)
| ST_Offer_false : forall rt rt' st st'
                     (r:protoExp rt) (r0:protoExp rt')
                     (s:protoExp st) (s0:protoExp st'),
    step _ _ _ _ (OfferC r0 s0) (ChoiceC false r s) (s0, s).

Definition proto1 :=
  send (basic 1);
  EpsC.

Definition proto2 :=
  x <- receive;
  ReturnC (t:=Basic) x.

Notation "'stepe'" := (step _ _ _ _).

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

Fixpoint unwrapMt {T:type} (m:message T) : type :=
  match m with
  | basic _ => Basic
  | key _ => Key
  | encrypt t m' _ => unwrapMt m'
  | hash _ _ => Hash
  | pair t1 t2 _ _ => Pair t1 t2
  | leither _ _ m' => unwrapMt m'
  | reither _ _ m' => unwrapMt m'
  | bad t1 => Basic
  end.

Fixpoint unwrapM {T:type} (m:message T) : (message (unwrapMt m)).
Proof.
  destruct m; simpl.
  exact (basic n).
  exact (key k).
  exact (unwrapM _ m).
  exact (hash t m).
  exact (pair t1 t2 m1 m2).
  exact (unwrapM _ m).
  exact (unwrapM _ m).
  exact (bad Basic).
Defined.

Inductive multi : forall (t r t':protoType), (protoExp t) -> (protoExp r) -> (protoExp t') -> Prop :=
| multi_refl : forall (t r t':protoType) (x:protoExp t) (y:protoExp r),
    multi _ _ _ x y x 
| multi_refl_u : forall t t0 (m:message t) (m0:message t0), multi _ _ _ (ReturnC m) (ReturnC m0) (ReturnC (unwrapM m))
| multi_step : forall (t t' r r2 s:protoType),
    forall (x:protoExp t) (x':protoExp t')
      (y:protoExp r) (y2:protoExp r2) (*(y':protoExp R' r') *)
      (z:protoExp s),
                    step _ _ _ _ x x' (y, y2) ->
                    multi _ _ _ y y2 z ->
                    multi _ _ _ x x' z.

Notation "'multie'" := (multi _ _ _).

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

Example multiEx1 : multi _ _ _ proto5 proto6 (ReturnC (basic 2)).
Proof. Print multi_step. specialize multi_step. intros. apply H with (r:=(Receive Basic (Eps Basic))) (r2:=(Send Basic (Eps Basic))) (y:=  x <- receive; ReturnC (t:=Basic) x) (y2:=send (incPayload (basic 1));EpsC). constructor. apply H with (r:=(Eps Basic)) (r2:=(Eps Basic)) (y:= ReturnC (basic 2)) (y2:=EpsC). constructor. assert ((unwrapM (basic 2)) = (basic 2)). reflexivity. rewrite <- H0 at 2. unfold EpsC. apply multi_refl_u with (m:=(basic 2)).
Qed.

Theorem big_multistep_equiv {t t':protoType}{T:type} {p1:protoExp t} {p2:protoExp t'} : forall (m : message T(*(returnType t)*)), runProtoBigStep _ _ _ p1 p2 m <->
                         multi _ _ _ p1 p2 (ReturnC m).
Proof.
  intros. split.

  (* -> *)
  generalize dependent t'. dependent induction p1; destruct p2; try (intros H; inversion H; contradiction).
  intros H. dep_destruct H. specialize multi_step. intros H0. apply H0 with (r:=p') (y:=p1) (y2:=p m). constructor. apply IHp1. assumption.
  intros H0. dep_destruct H0. specialize multi_step. intros H1. apply H1 with (r:=p') (y:=p m0) (y2:=p2). constructor. apply H. assumption.

  intros HH. inversion HH.
  intros HH. inversion HH.
  intros HH. inversion HH.
  intros HH. inversion HH.
  intros H. dep_destruct H. apply multi_step with (r:=r) (y:=p1_1) (y2:=p2_1). constructor. apply IHp1_1. assumption.
  apply multi_step with (y:=p1_2) (y2:=p2_2). constructor. apply IHp1_2. assumption.
  
  intros H. dep_destruct H. apply multi_step with (y:=p1_1) (y2:=p2_1). constructor. apply IHp1_1. assumption. (*apply IHp1_1.*)
  apply multi_step with (y:=p1_2) (y2:=p2_2). constructor. apply IHp1_2. assumption.

  intros H. dep_destruct H. constructor. exact (Eps Basic).

  (* <- *)
Admitted.

Axiom eitherToOr : forall T r s, (T = Either (returnType r) (returnType s))
                            -> (T = (returnType r)) \/ (T = (returnType s)).



Theorem runProto_iff_multi{t t':protoType} {p1:protoExp t} {p2:protoExp t'}{p:Dual p1 p2} : forall m,
      (unwrapM (runProto p1 p2 p) = m) <-> multi _ _ _ p1 p2 (ReturnC m).
Proof.
  intros. split.

  (* -> *)
  generalize dependent t'. dependent induction p1; destruct p2; try (intros H; inversion H; contradiction).
  intros. inversion p0. subst. apply multi_step with (y:=p1) (y2:=p m). constructor. destruct p0. cbn. simpl_eq. cbn. apply IHp1. reflexivity.

  intros. inversion p0. subst. apply multi_step with  (y:=p m) (y2:=p2). constructor. destruct p0. cbn. simpl_eq. cbn. apply H. reflexivity.

    intros HH. inversion HH.
    intros HH. inversion HH.
    intros HH. inversion HH.
    intros HH. inversion HH.
    intros. destruct b.
    dep_destruct H. destruct p. subst.


    apply multi_step with (y:=p1_1) (y2:=p2_1). constructor.
    (*apply IHp1_1 with (m:=(unwrapM
           (leither (returnType r) (returnType s) (runProto p1_1 p2_1 d)))).*)

    apply IHp1_1. simpl. reflexivity.
    
    dep_destruct H. destruct p. subst. apply multi_step with (y:=p1_2) (y2:=p2_2). constructor. apply IHp1_2. simpl. reflexivity.


    intros. destruct b.
    dep_destruct H. destruct p. apply multi_step with (y:=p1_1) (y2:=p2_1). constructor. apply IHp1_1. simpl. reflexivity.
    dep_destruct H. destruct p. apply multi_step with (y:=p1_2) (y2:=p2_2). constructor. apply IHp1_2. simpl. reflexivity.

    intros. subst. destruct p. cbn. constructor.

    (* <- *)
    generalize dependent t'. dependent induction p1; destruct p2; try (intros H; inversion H; contradiction).
    intros. inversion p0. subst. inversion H. simpl_existTs. subst.
    destruct p0. simpl. simpl_eq. cbn. dep_destruct H8. simpl. simpl_eq. cbn

    apply IHp1. assumption.
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