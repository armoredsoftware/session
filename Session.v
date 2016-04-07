Require Export Crypto.
Require Import Program.
Require Import Arith.
Require Import Eqdep_dec.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import CpdtTactics.
Add LoadPath "/Users/adampetz/Documents/Fall_2015_Courses/armored/session/protosynth".
Require Import ProtocolSynthesis4.

Inductive protoType : Type :=
| Send : type -> protoType -> protoType
| Receive : type -> protoType -> protoType
| Choice : protoType -> protoType -> protoType
| Offer : protoType -> protoType -> protoType  
| Eps : type -> protoType.

(*
Section mSection.
  
Axiom networkReceive : nat -> Message.

Fixpoint sessionToProtoExp (s:Session) (n:nat) : (type * protoType).
Proof.
  intros. 
  destruct s eqn : mm.
  exact (Basic, snd (sessionToProtoExp s0 (S n))).
  specialize (networkReceive n). intros.
  destruct H eqn : mmm.
  exact (Basic, snd (sessionToProtoExp (s0 m))).
  exact (Basic, (Eps Basic)).
Defined.  Check sessionToProtoExp.


End mSection.

Check sessionToProtoExp.
*)
                                                  
Inductive protoExp : type -> protoType -> Type :=
| SendC {t:type} {T:type} {p':protoType}  : (message t) -> (protoExp T p')
    -> protoExp T (Send t p')
| ReceiveC {t:type} {T:type} {p':protoType} : ((message t)->(protoExp T p'))     -> protoExp T  (Receive t p') 
| ChoiceC (b:bool) {r s:protoType} {R S:type} :(protoExp R r) -> (protoExp S s)
    -> (protoExp (if(b) then R else S) (Choice r s))
| OfferC {r s : protoType} {R S:type} : (protoExp R r) -> (protoExp S s)
                                        -> (protoExp (Either R S) (Offer r s))| ReturnC {t:type} : (message t) -> protoExp t (Eps t).

Inductive DualR : forall (T T':type), forall (t t':protoType), (protoExp T t) -> (protoExp T' t') -> Prop :=
| returnR' : forall T T' (m:message T) (m':message T'),
    DualR _ _ _ _ (ReturnC m) (ReturnC m')
| sendR' : forall X Y Y' p1t p2t
            (m:message Y)
            (f: ((message Y) -> (protoExp Y' p2t)))
            (p1':protoExp X p1t),
        DualR _ _ _ _ p1' (f m) ->
        DualR _ _ _ _ (SendC m p1') (ReceiveC f)
| receiveR' : forall X Y Y' p1t p2t
            (m:message Y)
            (f: ((message Y) -> (protoExp Y' p2t)))
            (p1':protoExp X p1t),
            DualR _ _ _ _ (f m) p1' ->
            DualR _ _ _ _ (ReceiveC f) (SendC m p1')
| choiceRt' : forall R R' S S' r r' s s'
               (r:protoExp R r) (r0:protoExp R' r')
               (s:protoExp S s) (s0:protoExp S' s'),
    DualR _ _ _ _ r r0 ->
    DualR _ _ _ _ s s0 ->
    DualR _ _ _ _ (ChoiceC true r s) (OfferC r0 s0)

| choiceRf' : forall R R' S S' r r' s s'
               (r:protoExp R r) (r0:protoExp R' r')
               (s:protoExp S s) (s0:protoExp S' s'),
    DualR _ _ _ _ r r0 ->
    DualR _ _ _ _ s s0 ->
    DualR _ _ _ _ (ChoiceC false r s) (OfferC r0 s0)

| offerRt' : forall R R' S S' r r' s s'
              (r:protoExp R r) (r0:protoExp R' r')
              (s:protoExp S s) (s0:protoExp S' s'),
    DualR _ _ _ _ r r0 ->
    DualR _ _ _ _ s s0 ->
    DualR _ _ _ _ (OfferC r s) (ChoiceC true r0 s0)

| offerRf' : forall R R' S S' r r' s s'
              (r:protoExp R r) (r0:protoExp R' r')
              (s:protoExp S s) (s0:protoExp S' s'),
    DualR _ _ _ _ r r0 ->
    DualR _ _ _ _ s s0 ->
    DualR _ _ _ _ (OfferC r s) (ChoiceC false r0 s0). 

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
(*Notation "x <- 'receive' ; p " := (ReceiveC (fun x => p)) 
                                    (right associativity, at level 60). *)

Notation "'offer'" := OfferC.

Notation "'choice'" := ChoiceC.  

Definition EpsC := ReturnC (basic 0).

Fixpoint protoExpLength {T:type} {pt:protoType} (p: protoExp T pt) : nat :=
  match p with
  | SendC  _ p' => 1 + (protoExpLength p')
  | ReceiveC f => 1 + (protoExpLength (f (bad _)))
  | ChoiceC b p' p'' =>  max (protoExpLength p') (protoExpLength p'')
  | OfferC  p' p'' => max (protoExpLength p') (protoExpLength p'')
  | ReturnC _ => 1
  end.                                                               

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

Theorem ifDualThenDualR {t t':protoType} {T T':type} : forall (p1:protoExp T t) (p2:protoExp T' t'), Dual p1 p2 -> DualR _ _ _ _ p1 p2.
Proof.
  
  intros p1. generalize dependent t'. generalize dependent T'. 
  induction p1; dependent inversion p2; try (intros; inversion H1).
  subst. constructor. apply IHp1. unfold Dual. assumption.
  inversion H2. subst. constructor. apply H. unfold Dual. assumption.
  inversion H2.
  inversion H2.
  inversion H2.
  inversion H2.
  destruct b. constructor. subst. apply IHp1_1. unfold Dual. assumption.
  apply IHp1_2. unfold Dual. assumption.
  constructor. subst. apply IHp1_1. unfold Dual. assumption.
  apply IHp1_2. unfold Dual. assumption.
  destruct b. constructor. subst. apply IHp1_1. unfold Dual. assumption.
  apply IHp1_2. unfold Dual. assumption.
  constructor. subst. apply IHp1_1. unfold Dual. assumption.
  apply IHp1_2. unfold Dual. assumption.
  constructor.
Qed.
                                       
Theorem ifDualRthenDual {t t':protoType} {T T':type} : forall (p1:protoExp T t) (p2:protoExp T' t'), DualR _ _ _ _ p1 p2 -> Dual p1 p2.
Proof.
  intros p1. generalize dependent t'. generalize dependent T'. 
  induction p1.  destruct p2.

  try (intro xx; inversion xx; contradiction).
  intro. unfold Dual. simpl. inversion H. simpl_existTs.
  split. assumption.
  subst. apply (IHp1 T0 p'0 (p m1) H3).
  try (intro xx; inversion xx; contradiction).
  try (intro xx; inversion xx; contradiction).
  try (intro xx; inversion xx; contradiction).

  generalize dependent t. generalize dependent T.  destruct p2.
  intros. unfold Dual. dep_destruct H0. 
  split. reflexivity. unfold Dual in H. apply (H m _ p'0 p2 x).

  intro aa. inversion aa.
  intro aa. inversion aa.
  intro aa. inversion aa.
  intro aa. inversion aa.
  dependent inversion p2.
  intro aa. inversion aa.
  intro aa. inversion aa.
  intro aa. inversion aa.
  intro aa. inversion aa. simpl_existTs. subst. unfold Dual. simpl. split. unfold Dual in IHp1_1. apply (IHp1_1 _ _ _ H5). apply (IHp1_2 _ _ _ H16).
  simpl_existTs. subst. unfold Dual. split. apply (IHp1_1 _ _ _ H5). apply (IHp1_2 _ _ _ H16).
  intro aa. inversion aa.
    dependent inversion p2.
  intro aa. inversion aa.
  intro aa. inversion aa.
  intro aa. inversion aa. simpl_existTs. subst. unfold Dual. simpl. split. unfold Dual in IHp1_1. apply (IHp1_1 _ _ _ H5). apply (IHp1_2 _ _ _ H16).
  simpl_existTs. subst. unfold Dual. split. apply (IHp1_1 _ _ _ H5). apply (IHp1_2 _ _ _ H16).
  intro aa. inversion aa.
  intro aa. inversion aa.
  dependent inversion p2.
   intro aa. inversion aa.
   intro aa. inversion aa.
     intro aa. inversion aa.
     intro aa. inversion aa.
     intro. unfold Dual. simpl. trivial.
Qed.

Fixpoint runProto' {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') 
  : (Dual p1 p2) -> (message T).
Proof.

       intro pf. destruct p1 (*eqn : p1Val*); destruct p2 (*eqn : p2Val*); try (inversion pf).

       subst. apply (runProto' _ _ _ _ p1 (p m)). unfold Dual. assumption.
       subst. apply (runProto' _ _ _ _ (p m) p2). unfold Dual. assumption.

       destruct b.
       apply (runProto' _ _ _ _ p1_1 p2_1 ). unfold Dual. assumption.
       apply (runProto' _ _ _ _ p1_2 p2_2 ). unfold Dual. assumption.
       
       destruct b.
       assert (message R).
       apply (runProto' _ _ _ _ p1_1 p2_1 ). unfold Dual. assumption. exact (leither _ _ X).
       assert (message S).
       apply (runProto' _ _ _ _ p1_2 p2_2 ). unfold Dual. assumption. exact (reither _ _ X).

       exact m.
Defined.

Fixpoint DualTSymm {t t':protoType} : DualT t t' -> DualT t' t.
Proof.
  intros. destruct t; destruct t'; try (inversion H); try (
  split;
  subst; trivial;
  apply (DualTSymm); assumption).
Defined.

Lemma DualSymm {t t':protoType} {T T':type} {p1:protoExp T t} {p2:protoExp T' t'} : (Dual p1 p2) -> (Dual p2 p1).
Proof.
  intros. unfold Dual in H. apply DualTSymm in H. assumption.
Defined.

Lemma notDualSymm {t t':protoType} {T T':type} {p1:protoExp T t} {p2:protoExp T' t'} : (~ Dual p1 p2) -> (~ Dual p2 p1).
Proof. 
  intros. unfold not. intros. apply DualTSymm in H0. unfold Dual in H. contradiction.
Defined.

Definition runProto {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') : (Dual p1 p2) -> (message T * message T') :=
  fun pf =>
    let x := runProto' p1 p2 pf in
    let y := runProto' p2 p1 (DualTSymm pf) in
    (x , y).

Definition nextType{T T':type} {t t':protoType} (p1:protoExp T t) (p2:protoExp T' t') : (Dual p1 p2) -> protoType.
  intros; destruct p1; destruct p2; try inversion H. exact p'. exact p'. destruct b. exact r. exact s. destruct b. exact r. exact s. exact (Eps t0).
Defined. Print nextType.

Definition recFunNextpType {t T:type} {p':protoType} (p: (message t) -> (protoExp T p')) : protoType := p'.

Definition recFunNextType {t T:type} {p':protoType} (p: (message t) -> (protoExp T p')) : type := T.

Definition ptOf {T:type} {t:protoType} (p1:protoExp T t) : protoType := t.
Definition tOf {T:type} {t:protoType} (p1:protoExp T t) : type := T.
Definition mType {t:type} (m:message t) : type := t.

Definition nextType'{T T':type} {t t':protoType} (p1:protoExp T t) (p2:protoExp T' t') : protoType :=
  match p1 with
  | SendC _ p' => ptOf p'
  | ReceiveC p => recFunNextpType p
  | ChoiceC b p1' p1'' =>
    match p2 with
    | OfferC _ _ => if b then ptOf p1' else ptOf p1''   
    | _ => Eps Basic
    end
  | OfferC p1' p1'' =>
    match p2 with
    | ChoiceC b _ _ => if b then ptOf p1' else ptOf p1''
    | _ => Eps Basic
    end
  | ReturnC m => Eps (mType m)
  end.

Definition nextRtype {T T':type} {t t':protoType} (p1:protoExp T t) (p2:protoExp T' t') : (Dual p1 p2) -> type.
  intros; destruct p1; destruct p2; try inversion H. exact T. exact T. destruct b. exact R. exact S. destruct b. exact R. exact S. exact t0.
Defined.

Definition nextRtype' {T T':type} {t t':protoType} (p1:protoExp T t) (p2:protoExp T' t') : type :=
  match p1 with
  | SendC _ p' => tOf p'
  | ReceiveC p => recFunNextType p
  | ChoiceC b p1' p1'' => match p2 with
    | OfferC _ _ => if b then tOf p1' else tOf p1''
    | _ => Basic
    end
  | OfferC p1' p1'' =>
    match p2 with
    | ChoiceC b _ _ => if b then tOf p1' else tOf p1''
    | _ => Basic
    end
  | ReturnC m => mType m                            
  end.

Theorem senRecOnce{t T1 T2:type}{t1 t2:protoType}{p1':protoExp T1 t1} {f : (message t) -> (protoExp T2 t2)} : forall (m:message t),
    (nextRtype' (SendC m p1') (ReceiveC f)) = (nextRtype' p1' (f m)).
Proof.
  intros. simpl. unfold tOf. unfold nextRtype'. Abort.

Theorem senRecOnce'{t T1 T2:type}{t1 t2:protoType}{p1':protoExp T1 t1} {f : (message t) -> (protoExp T2 t2)} : forall (m:message t),
    (nextRtype' (SendC m p1') (ReceiveC f)) = T1.
Proof.
  intros. simpl. unfold tOf. reflexivity. Qed.
  

Definition runProto'OneStep {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') (p:Dual p1 p2) : (protoExp (nextRtype' p1 p2) (nextType' p1 p2)).
  destruct p1; destruct p2; try inversion p.
simpl. destruct p. exact p1.
simpl. destruct p. subst. exact (p0 m).
destruct b.
simpl. destruct p. exact p1_1.
simpl. destruct p. exact p1_2.
destruct b.
simpl. destruct p. exact p1_1.
simpl. destruct p. exact p1_2.
simpl. destruct p. exact (ReturnC m).
Defined.

Definition runProtoOneStep {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') (p:Dual p1 p2) : ((protoExp (nextRtype' p1 p2) (nextType' p1 p2)) * (protoExp (nextRtype' p2 p1) (nextType' p2 p1) )) :=
  let x := (runProto'OneStep p1 p2 p) in
  let y := (runProto'OneStep p2 p1 (DualTSymm p)) in
  (x,y).

Fixpoint runProtoMultiStep' {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') (n:nat) : (Dual p1 p2) -> (message T * message T').
  refine
  ( fun pf => 
    match n with
    | O => _
    | S n' => _
    end). destruct p1; destruct p2; try inversion pf.
  exact (bad T, bad T0).
  exact (bad T, bad T0).
  destruct b.
    exact (bad R, bad (Either R0 S0)).
    exact (bad S, bad (Either R0 S0)).
  destruct b.
    exact (bad (Either R S), bad R0).
    exact (bad (Either R S), bad S0).
  exact (m, m0).
  destruct (runProtoOneStep p1 p2 pf);
    destruct p1; destruct p2; try inversion pf;
  try
  (subst; destruct pf; cbv in p;  cbv in p0;  destruct (runProtoMultiStep' _ _ _ _ p p0 n' H0); exact (m0, m1)).
  destruct b.
  destruct pf. cbv in p. cbv in p0. destruct (runProtoMultiStep' _ _ _ _ p p0 n' H). exact (m, leither _ _ m0).
  destruct pf. cbv in p. cbv in p0. destruct (runProtoMultiStep' _ _ _ _ p p0 n' H0). exact (m, reither _ _ m0).
  destruct b.
    destruct pf. cbv in p. cbv in p0. destruct (runProtoMultiStep' _ _ _ _ p p0 n' H). exact (leither _ _  m, m0).
    destruct pf. cbv in p. cbv in p0. destruct (runProtoMultiStep' _ _ _ _ p p0 n' H0). exact (reither _ _ m, m0).
    destruct pf. cbv in p. cbv in p0. assert (Dual p p0). reflexivity. destruct (runProtoMultiStep' _ _ _ _ p p0 n' H). exact (m1, m2). Defined.

Definition runProtoMultiStep {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') : (Dual p1 p2) -> (message T * message T') :=
  fun pf =>
  runProtoMultiStep' p1 p2 (max (protoExpLength p1) (protoExpLength p2)) pf.

Inductive runProtoR : forall (T T':type), forall (t t':protoType), (protoExp T t) -> (protoExp T' t') -> (message T) -> Prop :=
  
| returnR : forall T T' (m:message T) (m':message T'),
    runProtoR _ _ _ _ (ReturnC m) (ReturnC m') m
| sendR : forall X Y Y' p1t p2t m'
            (m:message X)
            (f: ((message X) -> (protoExp Y' p2t)))
            (p1':protoExp Y p1t),
        
        runProtoR _ _ p1t p2t p1' (f m) m' ->
        runProtoR _ _ _ _ (SendC m p1') (ReceiveC f) m'
| receiveR : forall X Y Y' p1t p2t m'
            (m:message X)
            (f: ((message X) -> (protoExp Y' p2t)))
            (p1':protoExp Y p1t),
            runProtoR _ _ _ _ (f m) p1' m' ->
            runProtoR _ _ _ _ (ReceiveC f) (SendC m p1') m'
| choiceRt : forall R R' S S' r r' s s'
               (r:protoExp R r) (r0:protoExp R' r')
               (s:protoExp S s) (s0:protoExp S' s')
               (m:message R) (m':message S),
    runProtoR _ _ _ _ r r0 m ->
    runProtoR _ _ _ _ s s0 m' ->
    runProtoR _ _ _ _ (ChoiceC true r s) (OfferC r0 s0) m

| choiceRf : forall R R' S S' r r' s s'
               (r:protoExp R r) (r0:protoExp R' r')
               (s:protoExp S s) (s0:protoExp S' s')
               (m:message R) (m':message S),
    runProtoR _ _ _ _ r r0 m ->
    runProtoR _ _ _ _ s s0 m' ->
    runProtoR _ _ _ _ (ChoiceC false r s) (OfferC r0 s0) m'

| offerRt : forall R R' S S' r r' s s' m m'
              (r:protoExp R r) (r0:protoExp R' r')
              (s:protoExp S s) (s0:protoExp S' s'),
    runProtoR _ _ _ _ r r0 m ->
    runProtoR _ _ _ _ s s0 m' ->
    runProtoR _ _ _ _ (OfferC r s) (ChoiceC true r0 s0) (leither _ _ m) 

| offerRf : forall R R' S S' r r' s s' m m'
              (r:protoExp R r) (r0:protoExp R' r')
              (s:protoExp S s) (s0:protoExp S' s'),
    runProtoR _ _ _ _ r r0 m ->
    runProtoR _ _ _ _ s s0 m' ->
    runProtoR _ _ _ _ (OfferC r s) (ChoiceC false r0 s0) (reither _ _ m').


Example rEx1 : runProtoR _ _ _ _ (ReturnC (basic 1)) (ReturnC (key (public 0))) (basic 1).
Proof.
  constructor. Qed.

Definition payload1 := (basic 1).
Definition payload2 := (key (public 0)).

Definition protoSimple1 :=
  send payload1;
  EpsC.

(*Definition protoSimple2 :=
  x <- receive;
  ReturnC (t:=Basic) x. *)

(*Example rEx2 : runProtoR _ _ _ _ protoSimple2 protoSimple1 (basic 1).
Proof. repeat constructor. Qed. *)

Theorem rIfDual {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') : DualR _ _ _ _ p1 p2 -> (exists m, runProtoR _ _ _ _ p1 p2 m).
Proof.
  intros H.
  dependent induction p1; dependent induction p2; try (inversion H).
  exists (bad T). inversion H0. clear H4. subst.
  apply sendR. Abort.
                                                                             
Theorem DualIfR {t t':protoType} {T T':type} : forall (p1:protoExp T t) (p2:protoExp T' t') m,
    runProtoR T T' t t' p1 p2 m -> DualR T T' t t' p1 p2.
Proof.
  intros p1. generalize dependent t'. generalize dependent T'. 
  induction p1; dependent inversion p2; try (intros m1 runR; inversion runR; contradiction).
  intros. dep_destruct H1. constructor. apply IHp1 with (m:=m'). assumption.
  intros. dep_destruct H2. constructor. apply H with (m0:=m'). assumption.
  intros. destruct b. constructor. subst. apply IHp1_1 with (m:=m). dep_destruct H1. assumption. subst. dep_destruct H1. apply IHp1_2 with (m:=m'). assumption.
  constructor. dep_destruct H1. subst. apply IHp1_1 with (m:=m). dep_destruct H1. assumption. subst. dep_destruct H1. apply IHp1_2 with (m:=m'). assumption.

  intros. dep_destruct H1. constructor. apply IHp1_1 with (m:=m0). assumption.
  apply IHp1_2 with (m:=m'). assumption.
  constructor. apply IHp1_1 with (m:=m0). assumption. apply IHp1_2 with (m:=m'). assumption.

  intros. constructor.
Qed.


(* fst (runProtoMultiStep p1 (p m) H) =
   fst (runProtoMultiStep (send m; p1) (ReceiveC p) pf) *)

Lemma osEval : forall t T p' T' p'' (p:(message t)->(protoExp T' p'')) (m:message t) (p1:protoExp T p') H pf , (runProtoMultiStep p1 (p m) H) =
                                                                                                         (runProtoMultiStep (SendC m p1) (ReceiveC p) pf).
Proof.
Admitted.

Lemma osEvalFlipped : forall t T p' T' p'' (p:(message t)->(protoExp T' p'')) (m:message t) (p1:protoExp T p') H pf , (runProtoMultiStep (p m) (p1) H) =
                                                                                                         (runProtoMultiStep (ReceiveC p) (SendC m p1) pf).
Proof.
Admitted.

Lemma osEvalChT : forall R r S s R' r' S' s' (p1_1:protoExp R r) (p:protoExp R' r') H2 (p1_2:protoExp S s) (p0:protoExp S' s') pf,
    let (r0, r1) := (runProtoMultiStep p1_1 p H2) in
    ((r0, (leither R' S' r1))       =
     (runProtoMultiStep (choice true p1_1 p1_2) (offer p p0) pf)
    ). Admitted.

Lemma osEvalChF : forall R r S s R' r' S' s' (p1_1:protoExp R r) (p:protoExp R' r') (p1_2:protoExp S s) (p0:protoExp S' s') pf H2,
    let (r0, r1) := (runProtoMultiStep p1_2 p0 H2) in
    ((r0, (reither R' S' r1))       =
     (runProtoMultiStep (choice false p1_1 p1_2) (offer p p0) pf)
    ). Admitted.

Lemma DualInner {t t':protoType} {T T':type} {p1:protoExp T t} {p2:protoExp T' t'} (pf:Dual p1 p2) : (Dual (runProto'OneStep p1 p2 pf)
                              (runProto'OneStep p2 p1 (DualSymm pf))).
Proof.
Admitted.

Hint Resolve nextType nextRtype.

Theorem rIfMulti {t t':protoType} {T T':type} : forall (p1:protoExp T t) (p2:protoExp T' t') (pf:Dual p1 p2) m, fst (runProtoMultiStep p1 p2 pf) = m -> runProtoR T T' t t' p1 p2 m.
Proof.
   intros p1. generalize dependent t'. generalize dependent T'.
   induction p1; dependent inversion p2; try (intros m1 runR; inversion runR; contradiction).
   intros. inversion pf. subst. constructor. assert (Dual p1 (p m)). admit.
   assert ((runProto'OneStep (send m; p1) (ReceiveC p) pf) = p1).
   unfold runProto'OneStep. destruct pf. reflexivity.
   
   apply IHp1 with (pf := H). assert ( (runProtoMultiStep p1 (p m) H) =
                                       (runProtoMultiStep (send m; p1) (ReceiveC p) pf) ). unfold runProtoMultiStep at 2. assert ((Init.Nat.max (protoExpLength (send m; p1))
        (protoExpLength (ReceiveC p))) = 1). admit. rewrite H1. inversion pf.  unfold runProtoMultiStep'.  unfold runProtoOneStep. unfold nextRtype'. unfold nextType'. unfold recFunNextType. unfold recFunNextpType. unfold tOf. unfold ptOf. unfold runProto'OneStep. unfold recFunNextType. unfold recFunNextpType. cbv. simpl_eq. 

   apply osEval. rewrite H0. reflexivity.
   intros. inversion pf. subst. constructor. assert (Dual (p m) p0). admit. apply H with (pf := H0). assert ( (runProtoMultiStep (p m) p0 H0) =
   (runProtoMultiStep (ReceiveC p) (send m; p0)  pf) ). apply osEvalFlipped. rewrite H1. reflexivity.


   intros. inversion pf. subst. destruct b. assert (message R). exact ((fst (runProtoMultiStep (choice true p1_1 p1_2) (offer p p0) pf))).  assert (exists m, runProtoR S S0 s s0 p1_2 p0 m). exists (fst (runProtoMultiStep p1_2 p0 H3)).  apply IHp1_2 with (pf:=H3). reflexivity. destruct H.
   
   apply choiceRt with (m':=x). apply IHp1_1 with (pf := H2). assert (     let (r0, r1) := (runProtoMultiStep p1_1 p H2) in
    ((r0, (leither _ _ r1))       =
     (runProtoMultiStep (choice true p1_1 p1_2) (offer p p0) pf)
    )). apply osEvalChT. admit. assumption.

   assert (message S). exact ((fst (runProtoMultiStep (choice false p1_1 p1_2) (offer p p0) pf))). assert (exists m, runProtoR R R0 r r0 p1_1 p m). exists (fst (runProtoMultiStep p1_1 p H2)).  apply IHp1_1 with (pf:=H2). reflexivity. destruct H.
   apply choiceRf with (m:=x). assumption. apply IHp1_2 with (pf:=H3). assert (     let (r0, r1) := (runProtoMultiStep p1_2 p0 H3) in
    ((r0, (reither R0 S0 r1))       =
     (runProtoMultiStep (choice false p1_1 p1_2) (offer p p0) pf)
    )). apply osEvalChF. admit.

   intros. inversion pf. subst. destruct b. assert ((fst (runProtoMultiStep (offer p1_1 p1_2) (choice true p p0) pf)) = (leither R S (fst (runProtoMultiStep p1_1 p H2)))). admit. rewrite H. apply offerRt with (m':= (fst (runProtoMultiStep p1_2 p0 H3))). apply IHp1_1 with (pf:=H2). reflexivity. apply IHp1_2 with (pf:=H3). reflexivity.

   assert ((fst (runProtoMultiStep (offer p1_1 p1_2) (choice false p p0) pf)) = (reither R S (fst (runProtoMultiStep p1_2 p0 H3)))). admit. rewrite H. apply offerRf with (m:=(fst (runProtoMultiStep p1_1 p H2))). apply IHp1_1 with (pf:=H2). reflexivity. apply IHp1_2 with (pf:= H3). reflexivity.

   intros. inversion H1. assert ((fst (runProtoMultiStep (ReturnC m) (ReturnC m0) pf)) = m). admit. rewrite H3. constructor.
   
   
   Check ( (fst (runProtoMultiStep (offer p1_1 p1_2) (choice true p p0) pf))). 

   apply offerRt.

   assert (message (Either R S)). exact (fst (runProtoMultiStep (offer p1_1 p1_2) (choice true p p0) pf)).  assert (exists m, runProtoR R R0 r r0 p1_1 p m). exists (fst (runProtoMultiStep p1_1 p H2)).  apply IHp1_1 with (pf:=H2). reflexivity. destruct H. apply offerRt with (m':=x).








   
   (*unfold runProtoMultiStep *) destruct pf. unfold runProtoMultiStep. assert ((max (protoExpLength p1) (protoExpLength (p m))) = 3). admit. assert ((max (protoExpLength (send m; p1)) (protoExpLength (ReceiveC p))) = 3). admit.  rewrite H0. rewrite H1. assert 




   unfold runProtoMultiStep' at 2. cbn. unfold nextRtype.

   unfold runProtoOneStep unfold runProto'OneStep
                                                                                                                                           
Theorem multiIfR {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') (pf:Dual p1 p2) : forall m, runProtoR T T' t t' p1 p2 m -> fst (runProtoMultiStep p1 p2 pf) = m.
Proof. 
  intros. dep_destruct p1. dep_destruct p2. dep_destruct H. unfold runProtoMultiStep. 



(*End session.*)