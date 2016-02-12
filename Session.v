Require Export SfLib.
Require Export CpdtTactics.
Require Export Setoid.
Require Export Crypto.

Module session.

Inductive protoType : Type :=
| Send : type -> protoType -> protoType
| Receive : type -> protoType -> protoType
| Choice : protoType -> protoType -> protoType
| Offer : protoType -> protoType -> protoType  
| Eps : type -> protoType.


Definition t1 := Send (Basic) (Eps Basic). Check t1.
  
Inductive protoExp : type -> protoType -> Type :=
| SendC {t:type} {T:type} {p':protoType}  : (message t) -> (protoExp T p')
    -> protoExp T (Send t p')
| ReceiveC {t:type} {T:type} {p':protoType} : ((message t)->(protoExp T p'))     -> protoExp T  (Receive t p') 
| ChoiceC (b:bool) {r s:protoType} {R S:type} :(protoExp R r) -> (protoExp S s)
    -> (protoExp (if(b) then R else S) (Choice r s))
| OfferC {r s : protoType} {R S:type} : (protoExp R r) -> (protoExp S s)
    -> (protoExp (Either R S) (Offer r s))  
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
Definition proto1 := SendC (basic 1) EpsC.
Check proto1.

Definition unwrapBasic (m:message Basic) : nat :=
  match m with
  | basic n => n
  | _ => 0
  end.


Definition enc1 := encrypt Basic (basic 42) (public 1). Check enc1.
Definition enc2 := encrypt _ enc1 (public 2).
Eval compute in decryptM enc1 (private 1).
Eval compute in decryptM enc1 (private 0).
Eval compute in decryptM enc2 (private 2).
Eval compute in decryptM (decryptM enc2 (private 2)) (private 1).

Definition getP1Type (t:type):type :=
  match t with
  | Pair t1 t2 => t1
  | _ => t
  end.

Definition getP2Type (t:type):type :=
  match t with
  | Pair t1 t2 => t2
  | _ => t
  end.

Definition pairFst{t1 t2: type} (m:message (Pair t1 t2)) : message t1 :=
  match m in message t' return message (getP1Type t') with 
  | pair _ _ m1 _ => m1
  | bad _ => bad _ (*(getP1Type tb1) *)
  | _ => bad _                
  end.

Definition pair1 := pair _ _ (basic 1) (basic 2).
Eval compute in pairFst pair1.
Definition pair1' := pair _ _ (bad Basic) (basic 2).
Eval compute in pairFst pair1'.
Definition pair1'' := pair _ _ (basic 1) (bad Basic).
Eval compute in pairFst pair1''.

Definition pairSnd{t1 t2: type} (m:message (Pair t1 t2)) : message t2 :=
  match m in message t' return message (getP2Type t') with
  | pair _ _ _ m2 => m2
  | bad _ => bad _ (*(getP1Type tb1) *)
  | _ => bad _                
  end.

Definition pair2 := pair _ _ (basic 1) (basic 2).
Eval compute in pairSnd pair2.
Definition pair2' := pair _ _ (basic 1) (bad Basic).
Eval compute in pairSnd pair2'.

Fixpoint protoTypeLength (t:protoType) : nat :=
  match t with
  | Send _ t' => 1 + (protoTypeLength t')
  | Receive _ t' => 1 + (protoTypeLength t')
  | Choice p1 p2 => 1 + protoTypeLength p2
  | Offer p1 p2 => 1 + protoTypeLength p2
  | Eps _ => 1                               
  end.

Definition protoLength {t:protoType} {T:type} (p1:protoExp T t) : nat := protoTypeLength t.

Eval compute in protoTypeLength (Send Basic (Eps Basic)).

Fixpoint DualT' (t t':protoType) : Prop :=
  match t with
  | Send p1T p1' =>
    match t' with
    | Receive p2T p2' => (p1T = p2T) /\ (DualT' p1' p2')    
    | _ => False
    end
  | Receive p1T p1' =>
    match t' with
    | Send p2T p2' => (p1T = p2T) /\ (DualT' p1' p2')                                
    | _ => False
    end
  | Choice p1' p1'' =>
    match t' with
    | Offer p2' p2'' => (DualT' p1' p2') /\ (DualT' p1'' p2'')                                                             
    | _ => False
    end
  | Offer p1' p1'' =>
    match t' with
    | Choice p2' p2'' => (DualT' p1' p2') /\ (DualT' p1'' p2'')                                                               
    | _ => False
    end
  | Eps _ =>
    match t' with
    | Eps _ => True           
    | _ => False
    end
  end.

Definition DualT (t t':protoType) : Prop := DualT' t t'.

Fixpoint DualT_dec (t t':protoType) : {DualT t t'} + {~ DualT t t'}. destruct t. destruct t'. right. simpl. unfold not. trivial. assert ({t = t2} + {t <> t2}). apply (eq_type_dec t t2). assert ({DualT t0 t'} + {~ DualT t0 t'}). apply (DualT_dec t0 t'). destruct H. destruct H0. apply left. unfold DualT. simpl. split; assumption. fold DualT'. apply right. simpl. unfold not. intros. destruct H. contradiction. apply right. unfold not. intros. destruct H. contradiction. right. unfold not. intros. inversion H. right. unfold not. intros. inversion H. right. unfold not. intros. inversion H.
                                                                     destruct t'. assert ({t = t2} + {t <> t2}). apply (eq_type_dec t t2). assert ({DualT t0 t'} + {~ DualT t0 t'}). apply (DualT_dec t0 t'). destruct H. destruct H0. apply left. simpl. split; assumption.  right. unfold not. intros. destruct H. contradiction. apply right. unfold not. intros. destruct H. contradiction. right. unfold not. intros. inversion H. apply right. unfold not. intros. inversion H. apply right. unfold not. intros. inversion H. apply right. unfold not. intros. inversion H. destruct t'. right. unfold not. intros. inversion H. intros. right. unfold not. intros. inversion H. right. unfold not. intros. inversion H. assert ({DualT t2 t'1 } + {~ DualT t2 t'1}). apply (DualT_dec t2 t'1). assert ({DualT t3 t'2} + {~ DualT t3 t'2}). apply (DualT_dec t3 t'2). destruct H. destruct H0. left. unfold DualT. simpl. split. unfold DualT in d.  unfold DualT in d0. assumption. assumption. right. unfold not. intros. destruct H. contradiction. right. unfold not. intros. destruct H. contradiction. right. unfold not. intros. inversion H.  destruct t'. right. unfold not. intros. inversion H. right. unfold not. intros. inversion H. assert ({DualT t2 t'1} + {~ DualT t2 t'1}). apply (DualT_dec t2 t'1). assert ({DualT t3 t'2} + {~ DualT t3 t'2}). apply (DualT_dec t3 t'2). destruct H. destruct H0. left. simpl. split; assumption. right. unfold not. intros. destruct H. contradiction. right. unfold not. intros. destruct H. contradiction. right. unfold not. intros. inversion H. right. unfold not. intros. inversion H. destruct t'. right. unfold not. intros. inversion H. right. unfold not. intros. inversion H. right. unfold not. intros. inversion H. right. unfold not. intros. inversion H. left. simpl. trivial. Defined.

Definition Dual {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') : Prop := DualT t t'.            


Fixpoint runProto' {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') (l: nat)
  : (message T) + {(~ (Dual p1 p2))}.
                    case_eq p1. case_eq p2. intros. apply inright. unfold DualT. unfold not. trivial. intros. assert ({t0 = t2} + {t0 <> t2}). apply (eq_type_dec t0 t2). destruct H1. subst. clear H. clear H0. assert (message T1 + {~ Dual p0 (p m)}). apply (runProto' p'0 p' T1 T0 p0 (p m) (protoTypeLength p'0)). destruct X. apply inleft. exact m0. apply inright. intros. unfold Dual. simpl. unfold Dual in n. unfold not in n. unfold not.  intros. destruct H.  apply n in H0.  assumption. apply inright. unfold Dual. simpl. unfold not. unfold not in n. intros. destruct H1. symmetry in H1. apply n in H1.  assumption. intros. apply inright. unfold Dual. simpl. unfold not. trivial. intros. apply inright. unfold Dual. unfold not. trivial. intros. apply inright. unfold Dual. unfold not. trivial. destruct p2. intros. assert ({t0 = t2} + {t0 <> t2}). apply (eq_type_dec t0 t2). destruct H0. subst. assert (message T1 + {~ Dual (p m) p2 }). apply (runProto' p'0 p' T1 T0 (p m) p2 (protoTypeLength p'0)). destruct X. apply inleft. exact m0. apply inright. intros. unfold Dual. simpl. unfold Dual in n. unfold not in n. unfold not.  intros. destruct H0.  apply n in H1.  assumption. apply inright. unfold Dual. simpl. unfold not. unfold not in n. intros. destruct H0. symmetry in H0. apply n in H0.  assumption. intros. apply inright. unfold Dual. unfold not. trivial. intros.  apply inright. intros. unfold not. intros. inversion H0. intros. apply inright. unfold not. intros. inversion H0. intros. apply inright. unfold not. intros. inversion H0.  intros. destruct p2. destruct b. apply inright. unfold not. intros. inversion H0. apply inright. unfold not. intros. inversion H0. apply inright. unfold not. intros. inversion H0. apply inright. unfold not. intros. inversion H0. destruct b.

                    unfold Dual. assert ({DualT r r0} + {~ DualT r r0}). apply (DualT_dec r r0). assert ({DualT s s0} + {~ DualT s s0}). apply (DualT_dec s s0). destruct H0. destruct H1. destruct (runProto' r r0 R R0 p p2_1 (protoTypeLength r0)). left. exact m. unfold not in n. unfold Dual in n. apply n in d. inversion d. right. unfold not. intros. destruct H0. contradiction. right. unfold not. intros. destruct H0. contradiction.

                    unfold Dual. assert ({DualT s s0} + {~ DualT s s0}). apply (DualT_dec s s0). assert ({DualT r r0} + {~ DualT r r0}). apply (DualT_dec r r0). destruct H0. destruct H1. destruct (runProto' s s0 S S0 p0 p2_2 (protoTypeLength s0)). left. exact m. unfold not in n. unfold Dual in n. apply n in d. inversion d. right. unfold not. intros. destruct H0. contradiction. right. unfold not. intros. destruct H0. contradiction. apply inright. intros. unfold not. intros. inversion H0. intros.

                    destruct p2. right. unfold not. intros. inversion H0. right. unfold not. intros. inversion H0. destruct b. unfold Dual. assert ({DualT r r0} + {~ DualT r r0}). apply (DualT_dec r r0). assert ({DualT s s0} + {~ DualT s s0}). apply (DualT_dec s s0). destruct H0. destruct H1. destruct (runProto' s s0 S S0 p0 p2_2 (protoTypeLength s0)). left. exact (reither R S m). unfold not in n. unfold Dual in n. apply n in d0. inversion d0. right. unfold not. intros. destruct H0. contradiction. right. unfold not. intros. destruct H0. contradiction. unfold Dual. assert ({DualT r r0} + {~ DualT r r0}). apply (DualT_dec r r0). assert ({DualT s s0} + {~ DualT s s0}). apply (DualT_dec s s0). destruct H0. destruct H1. destruct (runProto' r r0 R R0 p p2_1 (protoTypeLength r0)). left. exact (leither R S m). unfold not in n. unfold Dual in n. apply n in d. inversion d. right. unfold not. intros. destruct H0. contradiction. right. unfold not. intros. destruct H0. contradiction. right. unfold not. intros. inversion H0. right. unfold not. intros. inversion H0. intros. destruct p2. right. unfold not. intros. inversion H0. right. unfold not. intros. inversion H0. right. unfold not. intros. inversion H0. right. unfold not. intros. inversion H0. left. exact m. Defined.

  
Definition runProto {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t')
  : (message T) + {(~ (Dual p1 p2))} := runProto' p1 p2 (max (protoLength p1) (protoLength p2)).

Definition proto3 :=
  send (basic 42);
  ReturnC (t:=Basic) (basic 1). Check proto3.

Definition proto3' :=
  x <- receive;
  ReturnC (t:=Basic) x. Check proto3'.

Eval compute in (runProto proto3' proto3).

Definition incPayload (m:message Basic) : (message Basic) :=
  match m with
  | basic n => basic (n + 1)
  | _ => basic 0                 
  end.
  
Definition proto4 :=
  x <- receive;
  send (incPayload x);
  ReturnC x.
Check proto4.

Definition proto5 :=
  send (basic 42);
  x <- receive;
  ReturnC (t:=Basic) x.
Check proto5.

Example dual45 : Dual proto4 proto5. unfold Dual. simpl. auto. Qed.

Eval compute in (runProto proto5 proto4).
Eval compute in (runProto proto4 proto5).

Definition proto6 (b:bool) :=
  choice b EpsC
         proto5. Check proto6.

Definition proto7 :=
  offer EpsC
        proto4. Check proto7.

Example dual67 : Dual (proto6 false) proto7. unfold Dual. simpl. auto. Qed.

Eval compute in (runProto (proto6 false) proto7).
Eval compute in (runProto (proto6 true) proto7).

Eval compute in (runProto proto5 proto3).



Definition aPub := (public 1).
Definition bPub := (public 2).
Definition aPubBad := (public 3).
Definition bPubBad := (public 4).
Definition aPri := (private 1).
Definition aPriBad := (private 5).
Definition bPri := (private 2).

Definition Needham_A :=
  send (encrypt Basic (basic 1) bPub);
  x <- receive;
  (*y <- decrypt x using aPri; *)
  send (encrypt _ (pairSnd (t1:=Basic) (t2:=Basic)
                  (decryptM x aPri)) bPub);
  ReturnC ((pairSnd (t1:=Basic) (t2:=Basic)
                  (decryptM x aPri))). Check Needham_A.

Definition Needham_B :=
  x <- receive;
  (*y <- decrypt x using bPri; *)
  send (encrypt _ (pair Basic Basic (decryptM x bPri) (basic 2)) aPub);
  z <- receive;
  ReturnC (t:= Pair Basic (Encrypt Basic)) (pair _ _ (decryptM x bPri) z). Check Needham_B.

Example DualNeedham : Dual Needham_A Needham_B.
Proof. unfold Dual; simpl. repeat( split;trivial). Qed.

Eval compute in runProto Needham_A Needham_B.
Eval compute in runProto Needham_B Needham_A.
       


End session.