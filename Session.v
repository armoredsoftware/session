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
                                        -> (protoExp (Either R S) (Offer r s))| ReturnC {t:type} : (message t) -> protoExp t (Eps t).

(*
Inductive DualR' : forall (T T':type), forall (t t':protoType), (protoExp T t) -> (protoExp T' t') -> Prop :=

| returnR' : forall T T' r1 r2, DualR' T T' (Eps T) (Eps T') r1 r2
| sendR' : forall T T' t' t'' x y r1 r2 r3 r4,
    (T = T') ->
    DualR' x y t' t'' r3 r4 ->
    DualR' x y (Send T t') (Receive T t'') r1 r2.   *)  

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
Notation "x <- 'receive' ; p " := (ReceiveC (fun x => p)) 
                                    (right associativity, at level 60).

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

  (*repeat match goal with        
  (*| [ |- {DualT (?T _ _) (?T _ _)} + {~ DualT (?T _ _) (?T _ _)} ]
    => right; unfold not; trivial  *)
  | [ |- _ ] =>  right; unfold not; intros; inversion H; contradiction
  end. *)

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
    );

  (* Eps/Eps case *)
  left. simpl. trivial.
  
Defined.

Definition Dual {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') : Prop := DualT t t'.

(*
Fixpoint ifDualThenDualR {t t':protoType} {T T':type} (n:nat) (p1:protoExp T t) (p2:protoExp T' t') : Dual p1 p2 -> DualR _ _ _ _ p1 p2.
  refine ( fun H => 
      match n with
      | O => _
      | S n' => _
      end ). 
  dependent inversion p1; subst; dependent inversion p2; subst; try inversion H. subst. constructor. apply ifDualThenDualR. exact n'. unfold Dual. assumption. subst. constructor. apply ifDualThenDualR. exact n'. unfold Dual. assumption.
  destruct b.
  constructor. apply ifDualThenDualR. exact n'. unfold Dual. assumption. apply ifDualThenDualR. exact n'. unfold Dual. assumption.
  constructor. apply ifDualThenDualR. exact n'. unfold Dual. assumption. apply ifDualThenDualR. exact n'. unfold Dual. assumption.
  destruct b.
    constructor. apply ifDualThenDualR. exact n'. unfold Dual. assumption. apply ifDualThenDualR. exact n'. unfold Dual. assumption.
    constructor. apply ifDualThenDualR. exact n'. unfold Dual. assumption. apply ifDualThenDualR. exact n'. unfold Dual. assumption.
    constructor. 
Abort. 
  
  


  try inversion H. dependent induction p

  
  apply ifDualThenDualR. apply H. apply ifDualThenDualR. apply H. apply ifDualThenDualR. apply H. apply ifDualThenDualR. apply H. constructor. Defined.
  

  
Abort. *)

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
  constructor. Qed.


  (*
  f0 : message t0 -> protoExp T p'
  H10 : t0 = t0
  H4 : DualR T T0 p' p'0 (f0 m) p2
             p : message t0 -> protoExp T p' 
  H : forall (m : message t0) (T' : type) (t' : protoType)
        (p2 : protoExp T' t'), DualR T T' p' t' (p m) p2 -> Dual (p m) p2
   *)

Definition sameExpType {T T':type} {p p':protoType} (a:protoExp T p) (b:protoExp T' p') : Prop := p = p' /\ T = T'.

(* x : DualR X Y' p' p'0 a (p m0)  *)
Lemma poopypants : forall T x y p1 p2 a p (m0 m:message T), DualR x y p1 p2 a (p m0) -> DualR x y p1 p2 a (p m).
Proof.
  Abort.

    
Lemma sameTypeDualR {T T' p2T:type} {p p' p2t:protoType} : forall  (b:protoExp T' p') (a:protoExp T p) p2, (sameExpType a b) -> (DualR _ p2T _ p2t a p2) -> (DualR _ _ _ _ b p2).
Proof.
  intros b a p2 same aDual.
  inversion same; subst.
  induction b. dep_destruct a. dep_destruct p2. generalize dependent m.  inversion aDual. dep_destruct aDual.  (*apply poopypants with (m:=m) in x0. constructor. *)

Abort.

(*rewrite H9.





















  
  admit.                                                   
  inversion H1.
  inversion H1.
  inversion H1.
  inversion H1.
  inversion H2.
  admit.
  inversion H2.
  inversion H2.
  inversion H2.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
  admit.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
  admit.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
  constructor. *)

                                       
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

  (*intro. unfold Dual. inversion H0. subst. simpl_existTs. subst. split.  assumption. *)
   (*apply (H _ _ _ _ H4). *)

  
  (*generalize dependent p.*) generalize dependent t. generalize dependent T.  destruct p2.
  intros. unfold Dual. dep_destruct H0. (*simpl_existTs; subst. *) 
  split. reflexivity. unfold Dual in H. apply (H m _ p'0 p2 x).

  (*
  assert (DualR T T0 p' p'0 (p m) p2). Print sameTypeDualR. apply (sameTypeDualR (f0 m) (p m)). unfold sameExpType. reflexivity. assumption. apply (H m T0 p'0 p2 H1).

  admit. apply (H _ _ _ p2 H4).

  inversion H0. simpl_existTs. rewrite H12 in H4. apply IHp2.
  admit.


                          apply inj_pairT2 in H8. apply inj_pairT2 in H8. apply inj_pairT2 in H8
  simpl_existTs split. reflexivity.

  generalize dependent p. dependent inversion p2.
  intro. inversion H2. simpl_existTs. assert (protoExp T p'). exact (f0 m1). assert (X0 = (f m1)). subst.
  
  

  unfold Dual. simpl. inversion H0. simpl_existTs. split. assumption. subst. unfold Dual in H. apply (H _ _ _ p2 H4).

  apply (H _ _ _ p2 H4).
  
  try (intro xx; inversion xx; contradiction)
  intro. unfold Dual in H. unfold Dual. simpl. split. inversion H0. simpl_existTs.  subst. assumption. inversion H0. simpl_existTs. subst. assert (protoExp T p'). exact (p m). unfold Dual in IHp2.

  apply (H _ _ _ p2 H4).

      apply f0 in m. subst apply (H _ _ _ _ H6).
  split. assumption.
  simpl_existTs.
  *)
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

Fixpoint runProto' {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') 
  : (Dual p1 p2) -> (message T).
Proof.

  intros; destruct p1; destruct p2; try inversion H.

       subst. apply (runProto' _ _ _ _ p1 (p m) (*l*)(*(protoExpLength (p m))*)). assumption.
       subst. apply (runProto' _ _ _ _ (p m) p2 ). assumption.

       destruct b.
       apply (runProto' _ _ _ _ p1_1 p2_1 ). assumption.
       apply (runProto' _ _ _ _ p1_2 p2_2 ). assumption.
       
       destruct b.
       assert (message R).
       apply (runProto' _ _ _ _ p1_1 p2_1 ). assumption. exact (leither _ _ X).
       assert (message S).
       apply (runProto' _ _ _ _ p1_2 p2_2 ). assumption. exact (reither _ _ X).

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
Defined.

Definition nextRtype {T T':type} {t t':protoType} (p1:protoExp T t) (p2:protoExp T' t') : (Dual p1 p2) -> type.
  intros; destruct p1; destruct p2; try inversion H. exact T. exact T. destruct b. exact R. exact S. destruct b. exact R. exact S. exact t0.
Defined.

Fixpoint nextRtype' {T T':type} {t t':protoType} (p1:protoExp T t) (p2:protoExp T' t') : type.
  refine (
  match p1 with
  | SendC _ _ =>
    match p2 with
    | ReceiveC f => _ 
    | _ => _
    end
  | ReceiveC _ =>
    match p2 with
    | SendC _ _ => _                            
    | _ => _
    end
  | ChoiceC b _ _ => match p2 with
    | OfferC _ _ => _                                                         
    | _ => _
    end
  | OfferC _ _ =>
    match p2 with
    | ChoiceC b _ _ => _
    | _ => _
    end
  | ReturnC _ => _
  end).
  exact T.
  destruct (eq_type_dec t0 t2).
    subst. apply (nextRtype' _ _ _ _ p0 (f m)).
    exact T.
  exact T.
  exact T.
  exact T.
 
  destruct (eq_type_dec t0 t2).
    subst. apply (nextRtype' _ _ _ _ (p0 m) p4).
    exact T.
  exact T.
  exact T.
  exact T.
  exact T.

  exact T.
  exact T.
  exact T.
  destruct b.
    apply (nextRtype' _ _ _ _ p3 p7).
    apply (nextRtype' _ _ _ _ p4 p8).
  exact T.
    
  exact T.
  exact T.
  destruct b.
    apply (nextRtype' _ _ _ _ p3 p7).
    apply (nextRtype' _ _ _ _ p4 p8).  
  exact T.
  exact T.

  exact t0.
Defined.


Theorem senRecOnce{t T1 T2:type}{t1 t2:protoType}{p1':protoExp T1 t1} {f : (message t) -> (protoExp T2 t2)} : forall (m:message t),
    (nextRtype' (SendC m p1') (ReceiveC f)) = (nextRtype' p1' (f m)).
Proof.
  intros. simpl. Abort.
  

Definition runProto'OneStep {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') (p:Dual p1 p2) : (protoExp (nextRtype p1 p2 p) (nextType p1 p2 p)).
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

Definition runProtoOneStep {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') (p:Dual p1 p2) : ((protoExp (nextRtype p1 p2 p) (nextType p1 p2 p)) * (protoExp (nextRtype p2 p1 (DualSymm p)) (nextType p2 p1 (DualSymm p)) )) :=
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
  (subst; destruct pf; cbv in p;  cbv in p0;  destruct (runProtoMultiStep' _ _ _ _ p p0 n' d); exact (m0, m1)).
  destruct b.
  destruct pf. cbv in p. cbv in p0. destruct (runProtoMultiStep' _ _ _ _ p p0 n' d). exact (m, leither _ _ m0).
  destruct pf. cbv in p. cbv in p0. destruct (runProtoMultiStep' _ _ _ _ p p0 n' d0). exact (m, reither _ _ m0).
  destruct b.
    destruct pf. cbv in p. cbv in p0. destruct (runProtoMultiStep' _ _ _ _ p p0 n' d). exact (leither _ _  m, m0).
    destruct pf. cbv in p. cbv in p0. destruct (runProtoMultiStep' _ _ _ _ p p0 n' d0). exact (reither _ _ m, m0).
    destruct pf. cbv in p. cbv in p0. assert (Dual p p0). reflexivity. destruct (runProtoMultiStep' _ _ _ _ p p0 n' H). exact (m2, m1). Defined.

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

Definition protoSimple2 :=
  x <- receive;
  ReturnC (t:=Basic) x.

Example rEx2 : runProtoR _ _ _ _ protoSimple2 protoSimple1 (basic 1).
Proof. repeat constructor. Qed.

Theorem rIfDual {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') : DualR _ _ _ _ p1 p2 -> (exists m, runProtoR _ _ _ _ p1 p2 m).
Proof.
  intros H.
  dependent induction p1; dependent induction p2; try (inversion H).
  exists (bad T). inversion H0. clear H4. subst.
  apply sendR. Abort.
                                                                                        
(*Fixpoint dualIfR {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') : (exists m, runProtoR _ _ _ _ p1 p2 m) -> DualR _ _ _ _ p1 p2.
Proof.
  intros H. dependent inversion p1. dependent inversion p2.
  inversion H. subst. inversion H4.
  inversion H. inversion H4. simpl_existTs. subst. inversion H7. simpl_existTs. subst. inversion H4. simpl_existTs. inversion H3. simpl_existTs. clear H28. clear H3. subst. constructor. dependent inversion p. 
  inversion H1.
  inversion H1.
  inversion H1.
  inversion H1.
  admit.
  inversion H1.
  admit.
  inversion H1.
  constructor.
  inversion H. subst. inversion H4. simpl_existTs. clear H3. subst. constructor.



  
  intros. dependent induction p1; dependent induction p2; try (inversion H); try (inversion H0).

  admit. admit. inversion H1. inversion H2. inversion H1. inversion H1. inversion H1. inversion H1. simpl_existTs. destruct b. constructor. assumption. assumption. subst.



  dependent inversion H1. simpl_existTs. inversion H5. simpl_existTs. clear H24. clear H5. subst. constructor. dependent inversion p1.
  

  clear H5. subst. apply sendR'.

  specialize IHp1 with (ReceiveC p). subst. Abort. (*apply IHp1.

  runProtoR T T0 p' p'0 p1' (f0 m1) m'
  intros. destruct p1; destruct p2. inversion H; inversion H0.
  split.
  inversion H0. reflexivity.
  induction H4. simpl. trivial.
  simpl.
  split. reflexivity.
  subst. inversion H9. Abort. (*
  apply (IHrunProtoR p1' f m' f).
  match goal with
  | [ H : (existT (fun x : type => _) _ _ = existT _ _ _) |- _ ] => inversion H; try subst
  end

  inversion H0 reflexivity
  inversion H0. inversion H4. subst. simpl. trivial. inversion H4. subst. simpl. split. trivial. Abort *) *) *)
  
Theorem multiIfR {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') (pf:Dual p1 p2) : forall m, runProtoR T T' t t' p1 p2 m -> fst (runProtoMultiStep p1 p2 pf) = m.
Proof. 
  intros. destruct p1; destruct p2; destruct pf. Abort.

  (*destruct m0; destruct m. destruct n; destruct n0. inversion H. subst.  apply inj_pair2_eq_dec in H11.  apply inj_pair2_eq_dec in H11.  apply inj_pair2_eq_dec in H11.  apply inj_pair2_eq_dec in H12.  apply inj_pair2_eq_dec in H8.  apply inj_pair2_eq_dec in H8.  apply inj_pair2_eq_dec in H7. rewrite <- H11. rewrite <- H8. inversion H3.  apply inj_pair2_eq_dec in H17.  apply inj_pair2_eq_dec in H16.  apply inj_pair2_eq_dec in H14.  subst. inversion H3.  apply inj_pair2_eq_dec in H6.  apply inj_pair2_eq_dec in H4.  apply inj_pair2_eq_dec in H4.  apply inj_pair2_eq_dec in H2.  apply inj_pair2_eq_dec in H2.  apply inj_pair2_eq_dec in H16.  apply inj_pair2_eq_dec in H14. subst.  inversion H3.  apply inj_pair2_eq_dec in H6.  apply inj_pair2_eq_dec in H7.  apply inj_pair2_eq_dec in H7.  apply inj_pair2_eq_dec in H8. subst. cbv. subst. cbv 
*)



(*End session.*)