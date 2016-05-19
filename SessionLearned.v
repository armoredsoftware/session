Require Export Crypto.
Require Import HeteroLists.
Require Import Program.
Require Import Arith.
Require Import Eqdep_dec.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import CpdtTactics.
Require Import SfLib.
Require Import Coq.Logic.Classical_Pred_Type.

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

(*
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
*)

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
    (*runProtoBigStep _ _ _ s s0 m' -> *)
    runProtoBigStep _ _ _ (ChoiceC true r s) (OfferC r0 s0) m (*(leither _ _ m) *)

| choiceRf : forall rt rt' st st' mt (m':message mt) 
               (r:protoExp rt) (r0:protoExp rt')
               (s:protoExp st) (s0:protoExp st')
               (*(m:message (returnType rt)) (m':message (returnType st))*),
    (*runProtoBigStep _ _ _ r r0 m -> *)
    runProtoBigStep _ _ _ s s0 m' -> 
    runProtoBigStep _ _ _ (ChoiceC false r s) (OfferC r0 s0) m' (*(reither _ _ m')*)

| offerRt : forall rt rt' st st' mt (m : message mt(*(returnType rt)*))
              (r:protoExp rt) (r0:protoExp rt')
              (s:protoExp st) (s0:protoExp st'),
    runProtoBigStep _ _ _ r r0 m ->
   (* runProtoBigStep _ _ _ s s0 m' -> *)
    runProtoBigStep _ _ _ (OfferC r s) (ChoiceC true r0 s0) m (*(leither _ _ m)*)

| offerRf : forall rt rt' st st' mt (m' : message mt)
              (r:protoExp rt) (r0:protoExp rt')
              (s:protoExp st) (s0:protoExp st'),
    (*runProtoBigStep _ _ _ r r0 m -> *)
    runProtoBigStep _ _ _ s s0 m' ->
    runProtoBigStep _ _ _ (OfferC r s) (ChoiceC false r0 s0) m'. (*(reither _ _ m') *)

(*
Theorem bigstep_implies_dual : forall t t' T (m:message T) (p1: protoExp t) (p2:protoExp t'), runProtoBigStep _ _ _ p1 p2 m -> Dual p1 p2.
Proof.
  intros. generalize dependent t'. generalize dependent T. induction p1; destruct p2; try (intros H; inversion H; contradiction). 
  intros. dep_destruct H. constructor. reflexivity. unfold Dual in IHp1. apply IHp1 with (p2:=(p m)) (m:=m'). assumption.
  intros. dep_destruct H0. constructor. reflexivity. apply H with (p2:=p2) (m:=m0) (m0:=m'). assumption.
  intros HH. inversion HH.
  intros HH. inversion HH.
  intros HH. inversion HH.
  intros HH. inversion HH.
  intros. dep_destruct H. constructor. apply IHp1_1 with (p2:=p2_1) (m:=m). assumption. apply IHp1_2 with (p2:=p2_2) (m:=m'). assumption.
  constructor. apply IHp1_1 with (p2:= p2_1) (m:=m). assumption.
  apply IHp1_2 with (p2:=p2_2) (m:=m'). assumption.
  intros. dep_destruct H. constructor. apply IHp1_1 with (p2:=p2_1) (m:=m). assumption.
  apply IHp1_2 with (p2:= p2_2) (m:=m'). assumption.
  constructor. apply IHp1_1 with (p2:= p2_1) (m:=m). assumption.
  apply IHp1_2 with (p2:= p2_2) (m:=m'). assumption.
  
  intros. constructor.
  Qed.
*)

Inductive step : forall (t r t':protoType), (protoExp t) -> (protoExp r) -> (protoExp t') -> Prop :=
| ST_Send_Rec : forall x y  mt
                  (m:message mt) (p1':protoExp x)
                  (f:(message mt) -> protoExp y),
    step _ _ _ (SendC m p1') (ReceiveC f) p1'
| ST_Rec_Send : forall x y mt (m:message mt) (p1':protoExp x)
                       (f:(message mt) -> protoExp y),                     
    step _ _ _ (ReceiveC f) (SendC m p1') (f m)
| ST_Choice_true : forall rt rt' st st'
                     (r:protoExp rt) (r0:protoExp rt')
                     (s:protoExp st) (s0:protoExp st'),
    (*step _ _ _ _ (ChoiceC false r s) (OfferC r0 s0) (s, s0) -> *)
    step _ _ _ (ChoiceC true r s) (OfferC r0 s0) r
| ST_Choice_false : forall rt rt' st st'
                     (r:protoExp rt) (r0:protoExp rt')
                     (s:protoExp st) (s0:protoExp st'),
   (* step _ _ _ _ (ChoiceC true r s) (OfferC r0 s0) (r, r0) -> *)
    step _ _ _ (ChoiceC false r s) (OfferC r0 s0) s
| ST_Offer_true : forall rt rt' st st'
                     (r:protoExp rt) (r0:protoExp rt')
                     (s:protoExp st) (s0:protoExp st'),
   (* step _ _ _ _ (OfferC r0 s0) (ChoiceC false r s) (s0, s) -> *)
    step _ _ _ (OfferC r0 s0) (ChoiceC true r s) r0
| ST_Offer_false : forall rt rt' st st'
                     (r:protoExp rt) (r0:protoExp rt')
                     (s:protoExp st) (s0:protoExp st'),
   (* step _ _ _ _ (OfferC r0 s0) (ChoiceC true r s)  (r0, r) -> *)
    step _ _ _ (OfferC r0 s0) (ChoiceC false r s) s0.

Definition proto1 :=
  send (basic 1);
  EpsC.

Definition proto2 :=
  (*x <- receive;*)
  ReceiveC (fun x => (
  ReturnC (t:=Basic) x)).



Notation "'stepe'" := (step _ _ _).

Example stepEx1 : stepe proto1 proto2 EpsC.
Proof.
  constructor.
Qed.

Definition proto3 (b:bool) :=
  choice b EpsC
         proto1. Check proto3.

Definition proto4 :=
  offer EpsC
        proto2. Check proto4.

Example stepEx2 : stepe (proto3 true) proto4 EpsC.
Proof.
  unfold proto3. unfold proto4. constructor.
Qed.

Example stepEx2' : stepe (proto3 false) proto4 proto1.
Proof.
  constructor.
Qed.

Example stepEx3' : stepe proto4 (proto3 true) EpsC.
Proof.
  unfold proto3. unfold proto4. constructor.
Qed.

Example stepEx3 : stepe proto4 (proto3 false) proto2.
Proof.
  constructor.
Qed.



(* TODO:  check validity *)
(*
Axiom wrapM : forall T m (m1:message (unwrapMt m)), unwrapM (T:=T) m = m1.

Theorem wrapmT : forall T m (m1:message (unwrapMt m)), unwrapM (T:=T) m = m1.
Proof.
  intros.
  dep_destruct m1. generalize dependent n. induction m. intros. simpl.
Abort.
*)

Inductive multi : forall (t r t':protoType), (protoExp t) -> (protoExp r)
                                        -> (protoExp t') -> Prop :=
| multi_refl : forall (t r :protoType) (x:protoExp t) (y:protoExp r),
    multi _ _ _ x y x
(*| multi_refl_u : forall t t0 (m:message t) (m0:message t0), multi _ _ _ (ReturnC m) (ReturnC m0) (ReturnC (unwrapM m)) *)
| multi_step : forall (t t' r r2 s:protoType),
    forall (x:protoExp t) (x':protoExp t')
      (y:protoExp r) (y2:protoExp r2)
      (z1:protoExp s),
                    step _ _ _ x x' y ->
                    step _ _ _ x' x y2 -> 
                    multi _ _ _ (*_*) y y2 z1 ->
                    multi _ _ _ (*_*) x x' z1.

Notation "'multie'" := (multi _ _ _).

Definition normal_form {p1t p2t:protoType} (p1:protoExp p1t)(p2:protoExp p2t)  (*(R:relation X) (t:X)*) : Prop :=
  ~ exists  t' (x:protoExp t'), step _ _ _ p1 p2 x.

Theorem nf_ex : normal_form (ReturnC (basic 0)) (ReturnC (basic 1)).
Proof.
 unfold normal_form. unfold not. intros. destruct H. destruct H. inversion H.
Qed.

Definition nf_of {p1t p2t t t':protoType} (p1:protoExp p1t) (p2:protoExp p2t)(res1 : protoExp t)(res2 : protoExp t') :=
  (multi _ _ _ p1 p2 res1) /\ (multi _ _ _ p2 p1 res2) /\ normal_form res1 res2.

Definition nextType{t t':protoType} (p1:protoExp t) (p2:protoExp t') : (Dual p1 p2) -> protoType.
  intros; destruct p1; destruct p2; try inversion H. exact p'. exact p'. destruct b. exact r. exact s. destruct b. exact r. exact s. exact (Eps t0).
Defined.

Definition runProto'OneStep {t t':protoType} (p1:protoExp t) (p2:protoExp t') (p:Dual p1 p2) : (protoExp (nextType p1 p2 p)).
  destruct p1; destruct p2; try inversion p.
simpl. destruct p. exact p1.
simpl. destruct p. subst. exact (p0 m).
destruct b.
simpl. destruct p. exact p1_1.
simpl. destruct p. exact p1_2.
destruct b.
simpl. destruct p. exact p1_1.
simpl. destruct p. exact p1_2.
simpl. destruct p. exact (ReturnC m0).
Defined.

Fixpoint DualTSymm {t t':protoType} : DualT t t' -> DualT t' t.
Proof.
  intros. destruct t; destruct t'; try (inversion H); try (
  split;
  subst; trivial;
  apply (DualTSymm); assumption).
Defined.

Lemma DualSymm {t t':protoType} {p1:protoExp t} {p2:protoExp t'} : (Dual p1 p2) -> (Dual p2 p1).
Proof.
  intros. unfold Dual in H. apply DualTSymm in H. assumption.
Defined.

Definition runProtoOneStep {t t':protoType} (p1:protoExp t) (p2:protoExp t') (p:Dual p1 p2) : ((protoExp (nextType p1 p2 p)) * (protoExp (nextType p2 p1 (DualSymm p)) )) :=
  let x := (runProto'OneStep p1 p2 p) in
  let y := (runProto'OneStep p2 p1 (DualTSymm p)) in
  (x,y).

Theorem dualInner {t t':protoType} {p1:protoExp t} {p2:protoExp t'} (p:Dual p1 p2) : Dual (fst (runProtoOneStep p1 p2 p)) (snd (runProtoOneStep p1 p2 p)).
                                                                             Proof. simpl. destruct p1; destruct p2; try (inversion p).  destruct p. assumption. destruct p. assumption. destruct b. simpl. destruct p. assumption. destruct p. assumption. destruct b. destruct p. assumption. destruct p. assumption. destruct p. simpl. cbv. trivial.
Defined.
  
                                                                             
Theorem normalizing{p1t p2t :protoType} : forall (p1:protoExp p1t) (p2:protoExp p2t), (Dual p1 p2) -> exists p3t p4t (p3:protoExp p3t) (p4:protoExp p4t), (multi _ _ _ p1 p2 p3) /\ (multi _ _ _ p2 p1 p4) /\ normal_form p3 p4.
Proof.
  intros. 

  generalize dependent p2t.
  dependent induction p1; destruct p2;
  try (intros H; inversion H).
  inversion H. subst.
  dep_destruct (IHp1 p'0 (p m)).
  inversion H. apply H4.
  destruct H0. destruct H0. destruct H0. destruct H0. destruct H4.

  eexists. eexists. eexists. eexists.
  
  split. subst. eapply multi_step. constructor. constructor. apply H0.
  split. eapply multi_step. constructor. constructor. apply H4. apply H5.

  intros HH. inversion HH. subst.
  dep_destruct (H m p'0 p2).
  inversion HH. apply H2.

  destruct x. inversion HH. apply H3. destruct H2. destruct H2. destruct H2. destruct H2. destruct H3.
  eexists. eexists. eexists. eexists. split. eapply multi_step. constructor. constructor. apply H2.
  split.
  eapply multi_step. constructor. constructor. apply H3. apply H4.

  intros. inversion H0.
  intros. inversion H0.
  intros. inversion H0.
  intros. inversion H0.

  destruct b. dep_destruct (IHp1_1 r0 p2_1). apply H0. destruct x. apply H0. destruct H2. destruct H2. destruct H2. destruct H2. destruct H4.

  eexists. eexists. eexists. eexists. split. eapply multi_step. constructor. constructor. apply H2.
  split. eapply multi_step. constructor. constructor. apply H4. apply H5.

  dep_destruct (IHp1_2 s0 p2_2). apply H1. destruct x. apply H1. destruct H2. destruct H2. destruct H2. destruct H2. destruct H4.

  eexists. eexists. eexists. eexists. split. eapply multi_step. constructor. constructor. apply H2.
  split. eapply multi_step. constructor. constructor. apply H4. apply H5.

    destruct b. dep_destruct (IHp1_1 r0 p2_1). apply H0. destruct x. apply H0. destruct H2. destruct H2. destruct H2. destruct H2. destruct H4.

  eexists. eexists. eexists. eexists. split. eapply multi_step. constructor. constructor. apply H2.
  split. eapply multi_step. constructor. constructor. apply H4. apply H5.

  dep_destruct (IHp1_2 s0 p2_2). apply H1. destruct x. apply H1. destruct H2. destruct H2. destruct H2. destruct H2. destruct H4.

  eexists. eexists. eexists. eexists. split. eapply multi_step. constructor. constructor. apply H2.
  split. eapply multi_step. constructor. constructor. apply H4. apply H5.

  eexists. eexists. eexists. eexists. split. apply multi_refl.
  split. apply multi_refl. cbv. intros. destruct H0. destruct H0. inversion H0.
Qed.

Definition incPayload (m:message Basic) : (message Basic) :=
  match m with
  | basic n => basic (n + 1)
  | _ => basic 0                 
  end.

Definition proto5 :=
  send (basic 1);
  ReceiveC (fun x => (*x <- receive;*)
  ReturnC (t:=Basic) x).

Definition proto6 :=
  (*y <- receive;*)
  ReceiveC (fun y => (
  send (incPayload y);
  EpsC)).


Example multiEx1 : multi _ _ _ proto5 proto6 (ReturnC (basic 2)).
Proof.
  apply multi_step with (r:=(Receive Basic (Eps Basic))) (r2:=(Send Basic (Eps Basic))) (y:= ReceiveC (fun x => (*x <- receive;*) (ReturnC (t:=Basic) x))) (y2:=send (incPayload (basic 1));EpsC).
  constructor. constructor.
  apply multi_step with (r:=(Eps Basic)) (r2:=(Eps Basic)) (y:= ReturnC (basic 2)) (y2:=EpsC).
  constructor. constructor. constructor.
Qed.

Definition isValue {t:protoType} (p:protoExp t) : Prop :=
  match p with
  | ReturnC _ => True
  | _ => False
  end.

Inductive value {T:type} : (protoExp (Eps T)) -> Prop :=
  v_ret : forall m, value (ReturnC m).

Theorem ex_value : value (ReturnC (basic 1)).
Proof.
  constructor. Qed.

Theorem ex_isValue : isValue (ReturnC (basic 1)).
Proof.
  simpl. trivial.
Qed.

Theorem strong_progress {t t':protoType} :
  forall (p1:protoExp t) (p2:protoExp t'),
    (Dual p1 p2) -> isValue p1 \/ (exists t'' (p3:protoExp t''), step _ _ _ p1 p2 p3).
Proof.
  intros. generalize dependent t'. induction p1; destruct p2; try (intros H; inversion H; contradiction).
  intros. inversion H. subst. right. exists p'. exists p1. constructor.

  intros. inversion H0. subst. right. exists p'. exists (p m). constructor.
  intros HH. inversion HH.
  intros HH. inversion HH.
  intros HH. inversion HH.
  intros HH. inversion HH.
  intros. destruct b; right.
  exists r. exists p1_1. constructor.
  exists s. exists p1_2. constructor.
  intros. destruct b; right.
  exists r. exists p1_1. constructor.
  exists s. exists p1_2. constructor.
  intros. left. simpl. trivial.
Qed.
  
Theorem bigstep_multistep {t t':protoType}{T:type} {p1:protoExp t} {p2:protoExp t'} : forall (m : message T(*(returnType t)*)), runProtoBigStep _ _ _ p1 p2 m ->
                         multi _ _ _ p1 p2 (ReturnC m).
Proof.
  intros.

  (* -> *)
  generalize dependent t'. dependent induction p1; destruct p2; try (intros H; inversion H; contradiction).
  intros H. dep_destruct H. specialize multi_step. intros H0. apply H0 with (r:=p') (y:=p1) (y2:=p m). constructor. constructor. apply IHp1. assumption.
  intros H0. dep_destruct H0. specialize multi_step. intros H1. apply H1 with (r:=p') (y:=p m0) (y2:=p2). constructor. constructor. apply H. assumption.

  intros HH. inversion HH.
  intros HH. inversion HH.
  intros HH. inversion HH.
  intros HH. inversion HH.
  intros H. dep_destruct H. apply multi_step with (r:=r) (y:=p1_1) (y2:=p2_1). constructor. constructor. apply IHp1_1. assumption.
  apply multi_step with (y:=p1_2) (y2:=p2_2). constructor. constructor. apply IHp1_2. assumption.
  
  intros H. dep_destruct H. apply multi_step with (y:=p1_1) (y2:=p2_1). constructor. constructor. apply IHp1_1. assumption. (*apply IHp1_1.*)
  apply multi_step with (y:=p1_2) (y2:=p2_2). constructor. constructor. apply IHp1_2. assumption.

  intros H. dep_destruct H. constructor.
Qed.

Definition unWrapRet{mt:type} (p:protoExp (Eps mt)) : message mt.
Proof.
  inversion p.
  assumption.
Defined.

Lemma unWrapRetLemma {mt:type} : forall (p1v:protoExp (Eps mt)), p1v = ReturnC (unWrapRet p1v).
Proof.
  intros. dep_destruct p1v. cbv. reflexivity.
Qed.
                                                        
Theorem multistep_bigstep {p1t p2t:protoType}{mt mt':type} {p1:protoExp p1t} {p2:protoExp p2t} : forall p1v p2v, nf_of p1 p2 p1v p2v -> exists (m:message mt) (m':message mt'), (p1v = (ReturnC m)) /\ (p2v = (ReturnC m')) /\ 

    runProtoBigStep _ _ _ p1 p2 m.

  (* <- *)
      intros. unfold nf_of in H. destruct H. destruct H0. remember (unWrapRet p1v) as XX eqn:XXX. exists (XX). remember (unWrapRet p2v) as XX' eqn:XXX'. exists (XX'). split. subst. apply unWrapRetLemma. split. subst. apply unWrapRetLemma.

      


      generalize dependent p2t. dependent induction p1; destruct p2;
      try (intros H; dep_destruct H; solve by inversion 1).

      intros H H'. dep_destruct H. dep_destruct s0. dep_destruct s1. constructor. eapply IHp1 with (p1v := p1v) (p2v:=p2v). assumption. reflexivity. reflexivity. assumption. dep_destruct H'. dep_destruct s2. dep_destruct s3. assumption.
      intros H' H''. dep_destruct H'. dep_destruct s0. dep_destruct s1. constructor. eapply H with (p1v:=p1v) (p2v:=p2v). assumption. reflexivity. reflexivity. assumption. dep_destruct H''. dep_destruct s2. dep_destruct s3. assumption.

      intros. solve by inversion 2.
      intros. solve by inversion 2.
      intros. solve by inversion 2.
      intros. solve by inversion 2.
      intros. destruct b. dep_destruct H. dep_destruct H0. eapply choiceRt. eapply IHp1_1. apply H1. subst. reflexivity. reflexivity. dep_destruct s2. dep_destruct s3. assumption. dep_destruct s4. dep_destruct s5. assumption.
      apply choiceRf. 

      eapply IHp1_2. apply H1. subst. reflexivity. reflexivity. dep_destruct H. dep_destruct s2. dep_destruct s3. assumption. dep_destruct H0. dep_destruct s2. dep_destruct s3. assumption.

      intros. destruct b. dep_destruct H. dep_destruct H0. eapply offerRt. eapply IHp1_1. apply H1. subst. reflexivity. reflexivity. dep_destruct s2. dep_destruct s3. assumption. dep_destruct s4. dep_destruct s5. assumption.
      apply offerRf. eapply IHp1_2. apply H1. subst. reflexivity. reflexivity. dep_destruct H. dep_destruct s2. dep_destruct s3. assumption. dep_destruct H0. dep_destruct s2. dep_destruct s3. assumption.

      intros. solve by inversion 2.
      intros. solve by inversion 2.
      intros. solve by inversion 2.
      intros. solve by inversion 2.
      intros. dep_destruct H. constructor. dep_destruct s0.
Qed.

(*
Definition normal_form {p1t p2t:protoType} (p1:protoExp p1t)(p2:protoExp p2t)  (*(R:relation X) (t:X)*) : Prop :=
  ~ exists  t' (x:protoExp t'), step _ _ _ p1 p2 x.
 *)

(*
Definition isValue {t:protoType} (p:protoExp t) : Prop :=
  match p with
  | ReturnC _ => True
  | _ => False
  end.

Inductive value {T:type} : (protoExp (Eps T)) -> Prop :=
  v_ret : forall m, value (ReturnC m).
 *)

Lemma value_is_nf {t t':protoType} (p1:protoExp t) (p2:protoExp t') :
  (isValue p1) /\ (isValue p2) -> normal_form p1 p2.
Proof.
  intros.
  destruct p1; destruct p2; try (solve by inversion 2).
  unfold normal_form. unfold not. intros. destruct H0. destruct H0. inversion H0.
Qed.

Lemma nf_is_value {t t':protoType} (p1:protoExp t) (p2:protoExp t') : (Dual p1 p2) -> 
  normal_form p1 p2 -> (isValue p1) /\ (isValue p2).
Proof.
  intros D H.
  destruct p1; destruct p2; try (inversion D).
  destruct H. eexists. eexists. subst. constructor.
  destruct H. exists p'. subst. exists (p m). constructor.
  destruct b.
  destruct H. exists r. exists p1_1. constructor.
  destruct H. exists s. exists p1_2. constructor.
  destruct b.
  destruct H. exists r. exists p1_1. constructor.
  destruct H. exists s. exists p1_2. constructor.
  
  simpl. split; trivial.
Qed.

Corollary nf_same_as_value {t t':protoType} (p1:protoExp t) (p2:protoExp t')
  : (Dual p1 p2) -> normal_form p1 p2 <-> (isValue p1) /\ (isValue p2).
Proof.
  intros. split.
  intros. apply nf_is_value in H0. assumption. assumption.
  intros. apply value_is_nf in H0. assumption.
Qed.

Inductive protocolComposition : Type :=
| protoEnd : protocolComposition
| protoComp {p1t p2t:protoType} : (protoExp p1t) -> (protoExp p2t) -> 
    ((message (returnType p1t)) -> protocolComposition) ->  
    protocolComposition.

Notation "x <- 'doProto' p1 p2 ; p" := (protoComp p1 p2 (fun x => p))
  (right associativity, at level 70, p1 ident, p2 ident).

Definition proto1' :=
  x <- receive;
  let y := (incPayload x) in
  send y;
    ReturnC y.

Definition other (m:message Basic (*Key*)) :=
  send m;
  x <- receive;
  let _ := incPayload x in
  ReturnC (*(key (public 0)).*) (t:=Basic) x.

Definition proto2' :=
  x <- receive;
  let y := incPayload (incPayload x) in
  send y;
  ReturnC y.

Definition payload := (basic 0).
Definition p1s := (other (*key (public 1))*) payload).
                                    
Definition client :=
  x <- doProto p1s proto1';
  let aaa := (other x) in
  y  <- doProto aaa proto2' ; 
  protoEnd.
 
  (*protoComp p1s proto1' (fun x =>
  protoComp (other x) proto2' (fun (y:message Basic) =>
                                 protoEnd _ y)). *)

Definition messageEq {t t':type} (m:message t) (m':message t') : Prop.
Proof.
  destruct (eq_type_dec t t').
  subst. exact (m = m').
  exact False.
Defined.

Definition isEnd (p:protocolComposition) : bool :=
  match p with
  | protoEnd => true
  | _ => false
  end.



Fixpoint biggerStep{t:type} (p:protocolComposition) (m:message t) : Prop :=
  match p with
  | protoEnd => False (* should never reach this case*)
  | protoComp p1 p2 f  =>
    exists m', runProtoBigStep _ _ _ p1 p2 m' /\
          if(isEnd (f m')) then messageEq m' m
          else biggerStep (f m') m
  end.
    
  (*| protoComp p1 p2 f  => exists m', runProtoBigStep _ _ _ p1 p2 m' /\
                        biggerStep (f m') m
                              
  end. *)

Example incTwice : biggerStep client (basic 3).
Proof.
  cbn.
  unfold p1s. unfold other. unfold proto1'. unfold proto2'.
  eexists. split; repeat constructor.
  eexists. split; repeat constructor.
Qed.


Fixpoint superMultiStep{t:type} (p:protocolComposition) (m:message t) : Prop :=
  match p with
  | protoEnd => False (* should never reach this case*)
  | protoComp p1 p2 f  =>
    exists m', multi _ _ _ p1 p2 (ReturnC m') /\
          if(isEnd (f m')) then messageEq m' m
          else superMultiStep (f m') m
  end.

Example incTwiceMulti : superMultiStep client (basic 3).
Proof.
  cbn.
  unfold p1s. unfold other. unfold proto1'. unfold proto2'.
  eexists. split; repeat econstructor.
Qed.

Section hlisttry.
(* begin thide *)
Implicit Arguments HNil [A B].
Implicit Arguments HCons [A B x ls].

Implicit Arguments HFirst [A elm ls].
Implicit Arguments HNext [A elm x ls].
(* end thide *)

(** By putting the parameters [A] and [B] in [Type], we enable fancier kinds of polymorphism than in mainstream functional languages.  For instance, one use of [hlist] is for the simple heterogeneous lists that we referred to earlier. *)

Fixpoint typesLearned' {t t':protoType} (p1:protoExp t) (p2:protoExp t')
  (pf:Dual p1 p2) (l':list Type) : list Type.
Proof.
  intros. destruct p1; destruct p2; try (inversion pf).
  subst. exact (typesLearned' _ _ p1 (p m) H0 l').
  assert (list Type). subst. exact (typesLearned' _ _ (p m) p2 H0 l').
  exact ((message t) :: X).
  destruct b.
  exact (typesLearned' _ _ p1_1 p2_1 H l').
  exact (typesLearned' _ _ p1_2 p2_2 H0 l').
  destruct b.
  exact (typesLearned' _ _ p1_1 p2_1 H l').
  exact (typesLearned' _ _ p1_2 p2_2 H0 l').
  exact l'.
Defined.

Definition typesLearned {t t':protoType} (p1:protoExp t) (p2:protoExp t')
           (pf:Dual p1 p2) : list Type := typesLearned' p1 p2 pf nil.

Definition mList (x:list Type) := hlist (fun T : Type => T) x.

Definition someMtypes : list Type := (message Basic) :: (message Key) :: nil.

Definition someMValues : hlist (fun T : Type => T) someMtypes :=
  HCons (basic 0) (HCons (key (public 0)) HNil).

Definition noMTypes : list Type := nil.
Definition noMValues : mList noMTypes := HNil.

Example steptypesLearned {t t':protoType} (p1:protoExp t) (p2:protoExp t')
           (pf:Dual p1 p2) (l:list Type) : (list Type).
Proof.
  destruct p1; destruct p2; inversion pf; subst.
  exact l.
  exact ((message t0) :: l).
  exact l.
  exact l.
  exact l.
Defined.

Definition gett (pt:protoType) : type :=
  match pt with
  | Receive t _ => t
  | _ => Basic
  end.

Definition stl {t t':protoType} (p1:protoExp t) (p2:protoExp t')
           (l:list Type) : (list Type) :=
  match p1 with
  | ReceiveC f => (message (gett t)) :: l 
  | _ => l
  end.
  
Inductive stepM : forall l l' (ml:mList l) (t r t':protoType) (p1:protoExp t) (p2:protoExp r), (protoExp t') -> mList l' -> Prop :=
| ST_Send_Recm : forall x y  mt 
                  (m:message mt) (p1':protoExp x)
                  (f:(message mt) -> protoExp y) l' ml,
    stepM _ l' ml _ _ _ (SendC m p1') (ReceiveC f) p1' ml
| ST_Rec_Sendm : forall x y mt (m:message mt) (p1':protoExp x)
                       (f:(message mt) -> protoExp y) l ml, 
    stepM l ((message mt) :: l)  ml _ _ _ (ReceiveC f) (SendC m p1') (f m) (HCons m ml)
| ST_Choice_truem : forall rt rt' st st'
                     (r:protoExp rt) (r0:protoExp rt')
                     (s:protoExp st) (s0:protoExp st') l' ml,
    (*step _ _ _ _ (ChoiceC false r s) (OfferC r0 s0) (s, s0) -> *)
    stepM _ l' ml _ _ _ (ChoiceC true r s) (OfferC r0 s0) r ml
| ST_Choice_falsem : forall rt rt' st st'
                     (r:protoExp rt) (r0:protoExp rt')
                     (s:protoExp st) (s0:protoExp st') l' ml,
   (* step _ _ _ _ (ChoiceC true r s) (OfferC r0 s0) (r, r0) -> *)
    stepM _ l' ml _ _ _ (ChoiceC false r s) (OfferC r0 s0) s ml
| ST_Offer_truem : forall rt rt' st st'
                     (r:protoExp rt) (r0:protoExp rt')
                     (s:protoExp st) (s0:protoExp st') l' ml,
   (* step _ _ _ _ (OfferC r0 s0) (ChoiceC false r s) (s0, s) -> *)
    stepM _ l' ml _ _ _ (OfferC r0 s0) (ChoiceC true r s) r0 ml
| ST_Offer_falsem : forall rt rt' st st'
                     (r:protoExp rt) (r0:protoExp rt')
                     (s:protoExp st) (s0:protoExp st') l' ml,
   (* step _ _ _ _ (OfferC r0 s0) (ChoiceC true r s)  (r0, r) -> *)
    stepM _ l' ml _ _ _ (OfferC r0 s0) (ChoiceC false r s) s0 ml.

Example stepEx1m : stepM _ _ noMValues _ _ _ proto1 proto2 EpsC noMValues.
Proof.
  constructor.
Qed.

Example stepEx2m : stepM _ _ noMValues _ _ _ proto2 proto1 (ReturnC (basic 1)) (HCons (basic 1) noMValues).
Proof.
  constructor.
Qed.


Inductive multim : forall l (ml:mList l) ml' (t r t':protoType) (p1:protoExp t) (p2:protoExp r),
    (protoExp t') -> (mList ml') (*(typesLearned p1 p2 pf))*) -> Prop :=
| multi_reflm : forall (t r :protoType) (x:protoExp t) (y:protoExp r) l ml,
    multim l ml _ _ _ _ x y x ml
           
| multi_stepm : forall (t t' r r2 s:protoType),
    forall (x:protoExp t) (x':protoExp t')
      (y:protoExp r) (y2:protoExp r2)
      (z1:protoExp s) (*l' l''*) l ml ml1't (*ml' ml''*) l' mls1' ml1',
                    stepM l l' ml _ _ _ x x' y mls1' ->
                    step _ _ _ x' x y2 -> 
                    (*stepM l' l'' ml' _ _ _ x' x y2 ml'' -> *)
                    multim _ mls1' ml1't _ _ _(*_*) y y2 z1 ml1' ->
                    multim _ ml _ _ _ _ (*_*) x x' z1 ml1'.

Notation "'multiem' ml p1 p2 p3 ml'" := (multim _ ml _ _ _ _ p1 p2 p3 ml') (right associativity, at level 200).

Example multiEx1' : (*let r:= (ReturnC (basic 2)) in
                    let l' := (HCons (basic 2) noMValues) in
     (multiem noMValues proto5 proto6 r l'). *)
  multim _ noMValues _ _ _ _ proto5 proto6 (ReturnC (basic 2)) (HCons (basic 2) noMValues).
Proof.
  unfold proto5. unfold proto6.
  repeat econstructor.
Qed.

Check client.

Inductive protocolCompositionM : Type :=
| protoEndM : protocolCompositionM
| protoCompM {p1t p2t:protoType} l l' :
    (protoExp p1t) -> (protoExp p2t) ->
    (mList l) ->
    ((message (returnType p1t)) -> (mList l') -> protocolCompositionM) ->  
    protocolCompositionM.

(*Notation "x y <- 'doProtoM' p1 p2 ml ; p" := (protoCompM _ _ p1 p2 ml (fun x y => p))
                                               (right associativity, at level 70, p1 ident, p2 ident). *)

Definition clientM :=
  protoCompM _ ((message Basic) :: nil) p1s proto1' noMValues (fun x y =>
  protoEndM).

(*  x y <- doProtoM p1s proto1'.
  protoEnd.

Definition clientM :=
  x y <- doProtoM p1s proto1'.
  let aaa := (other x) in
  y  <- doProtoM aaa proto2' ; 
  protoEnd.
 *)


Definition clientM2 :=
  protoCompM _ ((message Basic) :: nil) p1s proto1' noMValues (fun x y =>
  let aaa := (other x) in                                                      protoCompM _ ((message Basic) :: (message Basic) :: nil) aaa proto2' y (fun x' y' =>           
  protoEndM)).


Definition isEndM (p:protocolCompositionM) : bool :=
  match p with
  | protoEndM => true
  | _ => false
  end.

Fixpoint eqLists lt1 lt2 (ml1:mList lt1) (ml2:mList lt2) : Prop :=
  match ml1 with
  | HNil =>
    match ml2 with
    | HNil => True
    | _ => False
    end
  | HCons x h' =>
    match ml2 with
    | HCons x' h'' => JMeq ml1 ml2
    | _ => False
    end
  end.

Fixpoint superMultiStepM l l' (p:protocolCompositionM) (ml:mList l) (ml':mList l') : Prop :=
  match p with
  | protoEndM => False (* should never reach this case*)
  | protoCompM _ _ p1 p2 ml f => 
    exists m' ml'', multim _ ml _ _ _ _ p1 p2 (ReturnC m') ml'' /\
          if(isEndM (f m' ml'')) then eqLists _ _ ml'' ml'
          else superMultiStepM _ _ (f m' ml'') ml'' ml'
  end.

Example incMultiM : superMultiStepM _ _ clientM noMValues (HCons (basic 1) noMValues).
Proof.
  repeat econstructor.
Qed.

Example incTwiceMultiM : superMultiStepM _ _ clientM2 noMValues (HCons (basic 3) (HCons (basic 1) noMValues)).
Proof.
  repeat econstructor.
Qed.

Example incTwiceMultiMGen : exists n, superMultiStepM _ _ clientM2 noMValues (HCons (basic 3) (HCons (basic n) noMValues)).
Proof.
  repeat econstructor.
Qed.










