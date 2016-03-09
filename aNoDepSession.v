Require Export NoDepCrypto.
Require Import Program.
Require Import Arith.
Require Import Eqdep_dec.

Inductive protoType : Type :=
| Send : type -> protoType -> protoType
| Receive : type -> protoType -> protoType
| Choice : protoType -> protoType -> protoType
| Offer : protoType -> protoType -> protoType  
| Eps : protoType.

(*
(* (protoExp T' (Send S s' )) ->  *)

Inductive protoExp : type -> protoType -> Type :=
| SendC  (m:message) : forall T T' t r', (protoExp T' (Receive (hasType m) r' )) -> (message -> protoExp T t) -> protoExp T (Send (hasType m) t)
| RecC {T T' S:type}{t s':protoType} : (message -> protoExp T t) -> protoExp T (Receive S t)
| ReturnC (m:message) : protoExp (hasType m) (Eps).

Definition p1 := (SendC (basic 1) _ _ _ _
                        (RecC (T':=Basic) (s':=Eps) (fun x => (ReturnC (x))))
                 (fun x => ReturnC (basic 0))). Eval compute in p1.
*)
                                                                             
Inductive protoExp : Type :=
| SendC (m:message) : protoExp -> protoExp
| ReceiveC : (message -> protoExp) -> protoExp
| ChoiceC (b:bool) : protoExp -> protoExp -> protoExp
| OfferC : protoExp -> protoExp -> protoExp
| ReturnC (m:message) : protoExp.

Definition prot1 := SendC (basic 1) (ReturnC (basic 1)).
Definition proto2 := ReceiveC (fun x => (ReturnC x)).

Fixpoint Dual (p1: protoExp) (p2:protoExp) : Prop.
  refine (
  match p1 with
  | SendC m p1' =>
    match p2 with
    | ReceiveC f => Dual p1' (f m)
    | _ => False
    end
  | ReceiveC f =>
    match p2 with
    | SendC m p1' => Dual (f m) p1'                            
    | _ => False
    end
  | ChoiceC b p1' p2' =>
    match p2 with
    | OfferC p1'' p2'' => if(b) then Dual p1' p1'' else Dual p2' p2''             | _ => False
    end
  | OfferC p1' p2' =>
    match p2 with
    | ChoiceC b p1'' p2'' => if(b) then Dual p1' p1'' else Dual p2' p2''
    | _ => False
    end
  | ReturnC _ =>
    match p2 with
    | ReturnC _ => True
    | _ => False
    end
  end). Defined.

Fixpoint 
                    

(*

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

Fixpoint runProto' {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') 
  : (Dual p1 p2) -> (message T).
Proof. intros; destruct p1; destruct p2; try inversion H.

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
            (m:message Y)
            (f: ((message Y) -> (protoExp Y' p2t)))
            (p1':protoExp X p1t),
        runProtoR _ _ _ _ p1' (f m) m' ->
        runProtoR _ _ _ _ (SendC m p1') (ReceiveC f) m'
| receiveR : forall X Y Y' p1t p2t m'
            (m:message Y)
            (f: ((message Y) -> (protoExp Y' p2t)))
            (p1':protoExp X p1t),
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

Theorem rIffDual {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') : (exists m, runProtoR _ _ _ _ p1 p2 m) -> Dual p1 p2.
Proof.
  intros. destruct p1; destruct p2; inversion H; inversion H0.
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
  inversion H0. inversion H4. subst. simpl. trivial. inversion H4. subst. simpl. split. trivial. Abort *)
  
Theorem rIffmulti {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') (pf:Dual p1 p2) : forall m, runProtoR T T' t t' p1 p2 m -> fst (runProtoMultiStep p1 p2 pf) = m.
Proof. 
  intros. destruct p1; destruct p2; destruct pf.

  (*destruct m0; destruct m. destruct n; destruct n0. inversion H. subst.  apply inj_pair2_eq_dec in H11.  apply inj_pair2_eq_dec in H11.  apply inj_pair2_eq_dec in H11.  apply inj_pair2_eq_dec in H12.  apply inj_pair2_eq_dec in H8.  apply inj_pair2_eq_dec in H8.  apply inj_pair2_eq_dec in H7. rewrite <- H11. rewrite <- H8. inversion H3.  apply inj_pair2_eq_dec in H17.  apply inj_pair2_eq_dec in H16.  apply inj_pair2_eq_dec in H14.  subst. inversion H3.  apply inj_pair2_eq_dec in H6.  apply inj_pair2_eq_dec in H4.  apply inj_pair2_eq_dec in H4.  apply inj_pair2_eq_dec in H2.  apply inj_pair2_eq_dec in H2.  apply inj_pair2_eq_dec in H16.  apply inj_pair2_eq_dec in H14. subst.  inversion H3.  apply inj_pair2_eq_dec in H6.  apply inj_pair2_eq_dec in H7.  apply inj_pair2_eq_dec in H7.  apply inj_pair2_eq_dec in H8. subst. cbv. subst. cbv 
*)


*)
(*End session.*)