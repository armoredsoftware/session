Require Export SfLib.
Require Export CpdtTactics.
Require Export Crypto.

Module try10.

Inductive protoType : Type :=
| Send : type -> protoType -> protoType
| Receive : type -> protoType -> protoType
| Choice : protoType -> protoType -> protoType
| Offer : protoType -> protoType -> protoType   
| Eps : type -> protoType.

(*Inductive Either (A:Type) (B:Type) : Type :=
| eLeft : A -> Either A B
| eRight : B -> Either A B. *)

  
Inductive protoExp : type -> protoType -> Type :=
| SendC {t:type} {T:type} {p':protoType}  : (message t) -> (protoExp T p') -> protoExp T (Send t p')
| ReceiveC {t:type} {T:type} {p':protoType} : ((message t)->(protoExp T p')) -> protoExp T  (Receive t p') 
| ChoiceC (b:bool) {r s: protoType} {R S:type}
  : (protoExp R r) -> (protoExp S s) -> (protoExp (if(b) then R else S) (Choice r s))
| OfferC {r s : protoType} {R S:type}
  : (protoExp R r) -> (protoExp S s) -> (protoExp (Either R S) (Offer r s))
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

(*Notation "'send' n ; p" := (SendC n p)
                            (right associativity, at level 60).
Notation "x <- 'receive' ; p " := (ReceiveC (fun x => p)) 
                                    (right associativity, at level 60). *)

Notation "'offer'" := OfferC.

Notation "'choice'" := ChoiceC.

Definition EpsC := ReturnC (basic 0).
Definition proto1 := SendC (basic 1) EpsC.
Check proto1.

Definition unwrapBasic (m:message Basic) : nat :=
  match m with
  | basic n => n
  end.


Definition proto2 :=
  SendC (basic 1)
  ( ReceiveC (fun x =>
  ( ReceiveC (fun y =>
  ( SendC (basic ((unwrapBasic x) + (unwrapBasic y)))
  ( EpsC)))))).                   
Check proto2.

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
  refine (                                                     
  match t with
  | Send p1T p1' =>
    match t' with
    | Receive p2T p2' => _
    | _ => right _
    end
  | Receive p1T p1' =>
    match t' with
    | Send p2T p2' => _
    | _ => right _
    end
  | Choice p1' p1'' =>
    match t' with
    | Offer p2' p2'' => _
    | _ => right _
    end
  | Offer p1' p1'' =>
    match t' with
    | Choice p2' p2'' => _
    | _ => right _ 
    end
  | Eps _ =>
    match t' with
    | Eps _ => left _
    | _ => right _
    end
  end). unfold not. intros. inversion H. assert ({p1T = p2T} + {p1T <> p2T}). apply (eq_type_dec p1T p2T). assert ({DualT p1' p2'} + {~ DualT p1' p2'}). apply (DualT_dec p1' p2'). destruct H. destruct H0. left. simpl. split; assumption. right. unfold not. intros. inversion H. contradiction. right. unfold not. intros. inversion H. contradiction. unfold not. intros. inversion H. unfold not. intros. inversion H. unfold not. intros. inversion H. assert ({p1T = p2T} + {p1T <> p2T}). apply (eq_type_dec p1T p2T). assert ({DualT p1' p2'} + {~ DualT p1' p2'}). apply (DualT_dec p1' p2'). destruct H. destruct H0. left. simpl. split; assumption. right. unfold not. intros. inversion H. contradiction. right. unfold not. intros. inversion H. contradiction. unfold not. intros. inversion H. unfold not. intros. inversion H. unfold not. intros. inversion H. unfold not. intros. inversion H. unfold not. intros. inversion H. unfold not. intros. inversion H. unfold not. intros. inversion H. assert ({DualT p1' p2'} + {~ DualT p1' p2'}). apply (DualT_dec p1' p2'). assert ({DualT p1'' p2''} + {~ DualT p1'' p2''}). apply (DualT_dec p1'' p2''). destruct H. destruct H0. left. simpl. split; assumption. right. unfold not. intros. inversion H. contradiction. right. unfold not. intros. inversion H. contradiction. unfold not. intros. inversion H. unfold not. intros. inversion H. unfold not. intros. inversion H. assert ({DualT p1' p2'} + {~ DualT p1' p2'}). apply (DualT_dec p1' p2'). assert ({DualT p1'' p2''} + {~ DualT p1'' p2''}). apply (DualT_dec p1'' p2''). destruct H. destruct H0. left. simpl. split; assumption. right. unfold not. intros. inversion H. contradiction. right. unfold not. intros. inversion H. contradiction. unfold not. intros. inversion H. unfold not. intros. inversion H. unfold not. intros. inversion H. unfold not. intros. inversion H. unfold not. intros. inversion H. unfold not. intros. inversion H. simpl. trivial. Defined.


Definition Dual {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') : Prop := DualT t t'.
  
Definition incPayload (m:message Basic) : (message Basic) :=
  match m with
  | basic n => basic (n + 1)
  end.
  
(*Definition proto4 :=
  x <- receive;
  send (incPayload x);
  ReturnC x.
Check proto4.

Definition proto5 :=
  send (basic 1);
  x <- receive;
  ReturnC (t:=Basic) x.
Check proto5. *)

(*Hint Constructors DualT.
Example dual45 : Dual proto4 proto5. unfold Dual. auto. Qed.

Definition proto6 :=
  choice true EpsC
         proto4. Check proto6.

Definition proto7 :=
  offer EpsC
        proto5. Check proto7.

Example dual67 : Dual proto6 proto7. unfold Dual. auto. Qed.

Eval compute in eq_type_dec Basic Basic.

Hint Resolve eq_type_dec.

Example dual45OneStep : DualOneStep proto4 proto5. unfold DualOneStep. reflexivity. Qed.

Example dual67OneStep : DualOneStep proto6 proto7. unfold DualOneStep. reflexivity. Qed.



Theorem sendsend t t' t0 t1 : (DualT (Send t t0) (Send t' t1)) -> False.
Proof.
  intros. inversion H.
  Qed. *)

Fixpoint protoTypeLength (t:protoType) : nat :=
  match t with
  | Send _ t' => 1 + (protoTypeLength t')
  | Receive _ t' => 1 + (protoTypeLength t')
  | Choice p1 p2 => protoTypeLength p1
  | Offer p1 p2 => protoTypeLength p1
  | Eps _ => 1                                
  end.

Eval compute in protoTypeLength (Send Basic (Eps Basic)).

Definition protoExpType {t:protoType} {T:type} (p1:protoExp T t) : type := T.

(*Eval compute in protoExpType proto4. *)

Fixpoint runProto {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') (p:Dual p1 p2) (l: nat) : (message (protoExpType p1)).
  refine(
  match p1 in (protoExp p1T p1'T) with
  | SendC _ _ _ m p1' =>
    match p2 in (protoExp p2T p2'T) with
    | ReceiveC _ _ _ f => _
    | _ => _
    end
  | ReceiveC _ _ _ f =>
    match p2 in (protoExp p2T p2'T) with
    | SendC _ _ _ m p2' => _
    | _ =>  _
    end
  | ChoiceC b _ _ _ _ p1' p1'' =>
    match p2 in (protoExp p2T p2'T) with
    | OfferC _ _ _ _ p2' p2'' => _
    | _ => _
    end
  | OfferC _ _ _ _ p1' p1'' =>
    match p2 in (protoExp p2T p2'T) with
    | ChoiceC b _ _ _ _ p2' p2'' => _
    | _ =>  _ 
    end
  | ReturnC _ m =>
    match p2 in (protoExp p2T p2'T) with
    | ReturnC _ _ => m
    | _ =>  _
    end
  end).  






      
                    case_eq p1. case_eq p2. intros. apply inright. unfold DualT. unfold not. trivial. intros. assert ({t0 = t1} + {t0 <> t1}). apply (eq_type_dec t0 t1). destruct H1. subst. clear H. clear H0. assert (message T1 + {~ Dual p0 (p m)}). apply (runProto p'0 p' T1 T0 p0 (p m) (protoTypeLength p'0)). destruct X. apply inleft. exact m0. apply inright. intros. unfold Dual. simpl. unfold Dual in n. unfold not in n. unfold not.  intros. destruct H.  apply n in H0.  assumption. apply inright. unfold Dual. simpl. unfold not. unfold not in n. intros. destruct H1. symmetry in H1. apply n in H1.  assumption. intros. apply inright. unfold Dual. simpl. unfold not. trivial. intros. apply inright. unfold Dual. unfold not. trivial. intros. apply inright. unfold Dual. unfold not. trivial. destruct p2. intros. assert ({t0 = t1} + {t0 <> t1}). apply (eq_type_dec t0 t1). destruct H0. subst. assert (message T1 + {~ Dual (p m) p2 }). apply (runProto p'0 p' T1 T0 (p m) p2 (protoTypeLength p'0)). destruct X. apply inleft. exact m0. apply inright. intros. unfold Dual. simpl. unfold Dual in n. unfold not in n. unfold not.  intros. destruct H0.  apply n in H1.  assumption. apply inright. unfold Dual. simpl. unfold not. unfold not in n. intros. destruct H0. symmetry in H0. apply n in H0.  assumption. intros. apply inright. unfold Dual. unfold not. trivial. intros.  apply inright. intros. unfold not. intros. inversion H0. intros. apply inright. unfold not. intros. inversion H0. intros. apply inright. unfold not. intros. inversion H0.  intros. destruct p2. destruct b. apply inright. unfold not. intros. inversion H0. apply inright. unfold not. intros. inversion H0. apply inright. unfold not. intros. inversion H0. apply inright. unfold not. intros. inversion H0. destruct b. 

                    unfold Dual. assert ({DualT r r0} + {~ DualT r r0}). apply (DualT_dec r r0). assert ({DualT s s0} + {~ DualT s s0}). apply (DualT_dec s s0). destruct H0. destruct H1. destruct (runProto r r0 R R0 p p2_1 (protoTypeLength r0)). left. exact m. unfold not in n. unfold Dual in n. apply n in d. inversion d. right. unfold not. intros. destruct H0. contradiction. right. unfold not. intros. destruct H0. contradiction.

                    unfold Dual. assert ({DualT s s0} + {~ DualT s s0}). apply (DualT_dec s s0). assert ({DualT r r0} + {~ DualT r r0}). apply (DualT_dec r r0). destruct H0. destruct H1. destruct (runProto s s0 S S0 p0 p2_2 (protoTypeLength s0)). left. exact m. unfold not in n. unfold Dual in n. apply n in d. inversion d. right. unfold not. intros. destruct H0. contradiction. right. unfold not. intros. destruct H0. contradiction. apply inright. intros. unfold not. intros. inversion H0. intros.  

                    destruct p2. right. unfold not. intros. inversion H0. right. unfold not. intros. inversion H0. destruct b. unfold Dual. assert ({DualT r r0} + {~ DualT r r0}). apply (DualT_dec r r0). assert ({DualT s s0} + {~ DualT s s0}). apply (DualT_dec s s0). destruct H0. destruct H1. destruct (runProto s s0 S S0 p0 p2_2 (protoTypeLength s0)). left. exact (reither R S m). unfold not in n. unfold Dual in n. apply n in d0. inversion d0. right. unfold not. intros. destruct H0. contradiction. right. unfold not. intros. destruct H0. contradiction. unfold Dual. assert ({DualT r r0} + {~ DualT r r0}). apply (DualT_dec r r0). assert ({DualT s s0} + {~ DualT s s0}). apply (DualT_dec s s0). destruct H0. destruct H1. destruct (runProto r r0 R R0 p p2_1 (protoTypeLength r0)). left. exact (leither R S m). unfold not in n. unfold Dual in n. apply n in d. inversion d. right. unfold not. intros. destruct H0. contradiction. right. unfold not. intros. destruct H0. contradiction. right. unfold not. intros. inversion H0. right. unfold not. intros. inversion H0. intros. destruct p2. right. unfold not. intros. inversion H0. right. unfold not. intros. inversion H0. right. unfold not. intros. inversion H0. right. unfold not. intros. inversion H0. left. exact m. Defined.

                  (*  right. unfold not. intros. inversion H0. right. unfold not. intros. inversion H0. left. exact m. Defined.

                    symmetry in H0. apply n in H0.  assumption. intros. apply inright. unfold DualOneStep. unfold not. trivial. intros. apply inright. unfold DualOneStep. unfold not. trivial. intros. apply inright. unfold DualOneStep. unfold not. trivial. intros. apply inright. unfold DualOneStep. unfold not. trivial. intros. destruct p2. intros. apply inright. unfold DualOneStep. unfold not. trivial. intros. apply inright. unfold DualOneStep. unfold not. trivial. intros. apply inright. unfold DualOneStep. unfold not. trivial. destruct b. apply (runProto _ _ _ _ _ _). apply (runProto _ _ _ _ _ _). intros. apply inright. unfold DualOneStep. unfold not. trivial. destruct p2. intros. apply inright. unfold DualOneStep. unfold not. trivial. intros. apply inright. unfold DualOneStep. unfold not. trivial. intros. apply (runProto _ _ _ _ _ _). intros. apply inright. unfold DualOneStep. unfold not. trivial. intros. apply inright. unfold DualOneStep. unfold not. trivial. destruct p2. intros. apply inright. unfold DualOneStep. unfold not. trivial. intros. apply inright. unfold DualOneStep. unfold not. trivial. intros. apply inright. unfold DualOneStep. unfold not. trivial. intros. apply inright. unfold DualOneStep. unfold not. trivial. intros. apply inleft. exact m0. Defined.  refine(
  match p1 with
  | SendC SentType p1T p1'T a p1' =>
    match p2 with
    | ReceiveC RecType p2T p2'T f =>
      match (eq_type_dec SentType RecType) with
      | left _ => _
      | right _ => inright _
      end
    | _ => inright _
    end
  | _ => inleft _
  end). Proof. unfold DualOneStep. unfold not. trivial.
    *)                                                                     
Hint Resolve eq_type_dec.

Definition proto3 :=
  send (basic 1);
  ReturnC (t:=Basic) (basic 1).

Definition proto3' :=
  x <- receive;
  ReturnC (t:=Basic) x.
           
Eval compute in (runProto proto3 proto3' 10).
  

End try10.