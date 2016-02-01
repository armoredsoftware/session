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
  Qed. 

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

*)
  

End try10.

Module try11.

Inductive protoType : Type :=
| Send : type -> protoType -> protoType
| Receive : type -> protoType -> protoType
| Choice : protoType -> protoType -> protoType
| Offer : protoType -> protoType -> protoType
| Decrypt : protoType -> protoType                                    
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
| DecryptC {p':protoType} {mt T:type} : (message (Encrypt mt)) -> keyType -> ((message mt) -> protoExp T p') -> protoExp T (Decrypt p')   
| ReturnC {t:type} : (message t) -> protoExp t (Eps t).

Notation "x :!: y" := (Send x y)
                        (at level 50, left associativity). 
Notation "x :!: y" := (protoExp (Send x y))
                        (at level 50, left associativity).

Notation "x :?: y" := (Receive x y)
                        (at level 50, left associativity).  
Notation "x :?: y" := (protoExp (Receive x y))
                        (at level 50, left associativity).

(*Notation "x :D: y" := (Decrypt x y)
                        (at level 50, left associativity).  
Notation "x :D: y" := (protoExp (Decrypt x y))
                        (at level 50, left associativity). *)

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

Notation "z <- 'decrypt' m 'using' k ; p " := (DecryptC m k (fun z => p)) 
                                    (right associativity, at level 60(*, m ident, k ident)*)).
Notation "'offer'" := OfferC.

Notation "'choice'" := ChoiceC.

Definition EpsC := ReturnC (basic 0).
Definition proto1 := SendC (basic 1) EpsC.
Check proto1.

Definition unwrapBasic (m:message Basic) : nat :=
  match m with
  | basic n => n
  end.

Definition unwrapEncrypt {mt:type} (m:message (Encrypt mt)) : message mt :=
  match m with
  | encrypt _ m' _ => m'
  end.


Definition enc1 := encrypt Basic (basic 42) (public 1). Check enc1.
Definition enc2 := encrypt _ enc1 (public 2).
Eval compute in unwrapEncrypt enc1.
Eval compute in unwrapEncrypt enc2.


Definition proto2 :=
  SendC (basic 1)
  ( ReceiveC (fun x =>
  ( ReceiveC (fun y =>
  ( DecryptC enc1 (public 1) (fun z =>                            
  ( SendC (basic ((unwrapBasic x) + (unwrapBasic y)))
  ( EpsC)))))))).              
Check proto2.
Check DecryptC.
Definition proto2D :=
  send (basic 1);
  x <- receive;
  y <- receive;
  z <- decrypt enc1 using (public 1);                        
  ( SendC (basic ((unwrapBasic x) + (unwrapBasic y)))
  ( EpsC)).              
Check proto2.

Definition dec1 := SendC (basic 1)
                         (DecryptC enc1 (public 1) (fun x => (ReturnC x))). Check dec1.

Check (public 1).

Definition dec2 := DecryptC enc1 (public 1) (fun x => ReturnC x). Check dec2.
Definition dec2Proro :=
  x <- decrypt (enc1) using (public 1) ; ((ReturnC x)).

Definition decryptProto :=
  send (basic 1);
  x <- decrypt enc1 using (public 1);
  send (basic 1); EpsC.

Definition pairFst{t1 t2: type} (m:message (Pair t1 t2)) : message t1 :=
  match m with
  | pair _ _ m1 _ => m1
  end.

Definition pairSnd{t1 t2: type} (m:message (Pair t1 t2)) : message t2 :=
  match m with
  | pair _ _ _ m2 => m2
  end.


Fixpoint protoTypeLength (t:protoType) : nat :=
  match t with
  | Send _ t' => 1 + (protoTypeLength t')
  | Receive _ t' => 1 + (protoTypeLength t')
  | Choice p1 p2 => 1 + protoTypeLength p2
  | Offer p1 p2 => 1 + protoTypeLength p2
  | Decrypt p' => 1 + (protoTypeLength p')
  | Eps _ => 1                               
  end.

Definition protoLength {t:protoType} {T:type} (p1:protoExp T t) : nat := protoTypeLength t.

Eval compute in protoTypeLength (Send Basic (Eps Basic)).

(*Fixpoint DualT' (t t':protoType) : Prop :=
  match t with
  | Send p1T p1' =>
    match t' with
    | Receive p2T p2' => (p1T = p2T) /\ (DualT' p1' p2')
    | Decrypt t'' => DualT' t t''            
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
  | Decrypt p1' => DualT' p1' t' (*Check this *) 
  | Eps _ =>
    match t' with
    | Eps _ => True           
    | _ => False
    end
  end. *)
   

Fixpoint DualT' (t t':protoType) (n:nat) : Prop :=
  match t with
  | Send p1T p1' =>
    match t' with
    | Receive p2T p2' => (p1T = p2T) /\ (DualT' p1' p2' (protoTypeLength p1'))
    | Decrypt t'' => DualT' t t'' (protoTypeLength t'')               
    | _ => False
    end
  | Receive p1T p1' =>
    match t' with
    | Send p2T p2' => (p1T = p2T) /\ (DualT' p1' p2' (protoTypeLength p1'))                                
    | _ => False
    end
  | Choice p1' p1'' =>
    match t' with
    | Offer p2' p2'' => (DualT' p1' p2' (protoTypeLength p1')) /\ (DualT' p1'' p2'' (protoTypeLength p1'))                                                             
    | _ => False
    end
  | Offer p1' p1'' =>
    match t' with
    | Choice p2' p2'' => (DualT' p1' p2' (protoTypeLength p1')) /\ (DualT' p1'' p2'' (protoTypeLength p1'))                                                               
    | _ => False
    end
  | Decrypt p1' => DualT' p1' t' (protoTypeLength p1') (*Check this *) 
  | Eps _ =>
    match t' with
    | Eps _ => True           
    | _ => False
    end
  end.

Eval compute in (max 0 5).

Definition DualT (t t':protoType) : Prop := DualT' t t' (protoTypeLength t') (*(max (protoTypeLength t) (protoTypeLength t'))*).

Fixpoint DualT_dec (t t':protoType) : {DualT t t'} + {~ DualT t t'}. destruct t. destruct t'. apply right. simpl. unfold not. trivial. assert ({t = t1} + {t <> t1}). apply (eq_type_dec t t1). assert ({DualT t0 t'} + {~ DualT t0 t'}). apply (DualT_dec t0 t'). destruct H. destruct H0. apply left. unfold DualT. simpl. split; assumption. fold DualT'. apply right. simpl. unfold not. intros. destruct H. contradiction. apply right. unfold not. intros. destruct H. contradiction. right. unfold not. intros. inversion H. right. unfold not. intros. inversion H. apply (DualT_dec (Send t t0) (Decrypt t')).

                                                                     right. unfold not. intros. inversion H.  destruct t'. assert ({t = t1} + {t <> t1}). apply (eq_type_dec t t1). assert ({DualT t0 t'} + {~ DualT t0 t'}). apply (DualT_dec t0 t'). destruct H. destruct H0. apply left. simpl. split. assumption. unfold DualT in d. assumption. right. unfold not. intros. destruct H. contradiction. apply right. unfold not. intros. destruct H. contradiction. right. unfold not. intros. inversion H. apply right. unfold not. intros. inversion H. apply right. unfold not. intros. inversion H. apply right. unfold not. intros. inversion H. right. unfold not. intros. inversion H. destruct t'. apply right. unfold not. intros. inversion H. apply right. unfold not. intros. inversion H. apply right. unfold not. intros. inversion H. assert ({DualT' t1 t'1 (max (protoTypeLength t2) (protoTypeLength t'2))} + {~ DualT' t1 t'1 (max (protoTypeLength t2) (protoTypeLength t'2))}). apply (DualT_dec t1 t'1). assert ({DualT t2 t'2} + {~ DualT t2 t'2}). apply (DualT_dec t2 t'2). destruct H. destruct H0. left. unfold DualT. simpl. split. unfold DualT in d.  unfold DualT in d0. assumption. assumption. right. unfold not. intros. destruct H. contradiction. right. unfold not. intros. destruct H. contradiction. right. unfold not. intros. inversion H. right. unfold not. intros. inversion H. destruct t'. right. unfold not. intros. inversion H.  right. unfold not. intros. inversion H. assert ({DualT t1 t'1} + {~ DualT t1 t'1}). apply (DualT_dec t1 t'1). assert ({DualT t2 t'2} + {~ DualT t2 t'2}). apply (DualT_dec t2 t'2). destruct H. destruct H0. left. simpl. split; assumption. right. unfold not. intros. destruct H. contradiction. right. unfold not. intros. destruct H. contradiction. right. unfold not. intros. inversion H. right. unfold not. intros. inversion H. right. unfold not. intros. inversion H. destruct t'. destruct t. right. unfold not. intros. inversion H. assert ({DualT (Receive t t1) (Send t0 t')} + {~DualT (Receive t t1) (Send t0 t')}). 

assert ({t = t0} + {t <> t0}). apply (eq_type_dec t t0). assert ({DualT t1 t'} + {~ DualT t1 t'}). apply (DualT_dec t1 t'). destruct H. destruct H0. left. simpl. split; assumption. right. unfold not. intros. destruct H. contradiction. right. unfold not. intros. destruct H. contradiction. destruct H. left. simpl. destruct d. split; assumption. right. apply n. right. unfold not. intros. inversion H. right. unfold not. intros. inversion H. assert ({DualT t (Send t0 t')} + {~ DualT t (Send t0 t')}). apply (DualT_dec t (Send t0 t')). destruct H. left. simpl. apply d. right. unfold not. intros. simpl in H. contradiction. right. unfold not. intros. inversion H.

assert ({DualT t (Receive t0 t')} + {~ DualT t (Receive t0 t')}). apply (DualT_dec t (Receive t0 t')). destruct H. left. simpl. apply d. right. simpl. apply n.  assert ({DualT t (Choice t'1 t'2)} + {~ DualT t (Choice t'1 t'2)}). apply (DualT_dec t (Choice t'1 t'2)). destruct H. left. simpl. apply d. right. simpl. apply n. assert ({DualT t (Offer t'1 t'2)} + {~ DualT t (Offer t'1 t'2)}). apply (DualT_dec t (Offer t'1 t'2)). destruct H. left. simpl. apply d. right. simpl. apply n. assert ({DualT t (Decrypt t')} + {~ DualT t (Decrypt t')}). apply (DualT_dec t (Decrypt t')). destruct H. left. simpl. apply d. right. simpl. apply n. assert ({DualT t (Eps t0)} + {~ DualT t (Eps t0)}). apply (DualT_dec t (Eps t0)). destruct H. left. simpl. apply d. right. simpl. apply n. destruct t'. right. unfold not. intros. inversion H. right. unfold not. intros. inversion H. right. unfold not. intros. inversion H. right. unfold not. intros. inversion H. right. unfold not. intros. inversion H. left. simpl. trivial. Defined.

Definition isDual := DualT_dec (Decrypt (Eps Basic)) (Eps Basic).
Eval compute in isDual.

Definition Dual {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') : Prop := DualT t t'.

Definition dualProto1 :=
  send (basic 1);
  x <- decrypt enc1 using (public 0);
  y <- receive;
  ReturnC (t:=Basic) y.

Definition dualProto2 :=
  x <- receive;
  send (basic 1);
  ReturnC (t:=Basic) x.

Example dual12 : Dual dualProto1 dualProto2. unfold Dual. simpl. split. trivial. split; trivial. Qed.

Definition aPub := (public 1).
Definition bPub := (public 2).
Definition aPri := (private 1).
Definition bPri := (private 2).

Definition Needham_A :=
  send (encrypt Basic (basic 1) bPub);
  x <- receive;
  y <- decrypt x using aPri;
  send (encrypt _ (pairSnd (t1:=Basic) (t2:=Basic) y) (public 2));
  EpsC. Check Needham_A.

Definition Needham_B :=
  x <- receive;
  y <- decrypt x using bPri;
  send (encrypt (Pair Basic Basic) (pair Basic Basic y (basic 2)) aPub);
  z <- receive;
  ReturnC (t:= Encrypt Basic) z. Check Needham_B.

Example DualTNeed : DualT
(Send (Encrypt Basic) (* (Decrypt ( *)
  (Receive (Encrypt (Pair Basic Basic))
    (Send (Encrypt Basic) (Eps Basic)))) (* )) *)

(Receive (Encrypt Basic)
  (Send (Encrypt (Pair Basic Basic)) (Decrypt (
    (Receive (Encrypt Basic) (Eps (Encrypt Basic))))))). simpl. split; trivial. split;trivial. split;trivial.

Example DualNeedham : Dual Needham_A Needham_B.
Proof. unfold Dual. simpl

(*Definition Dual_dec {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') : {Dual p1 p2} + {~ Dual p1 p2}. assert ({DualT t t'} + {~DualT t t'}). apply (DualT_dec t t'). destruct p1. destruct p2. right. unfold not. intros. inversion H0.
  refine (
      match (DualT_dec t t') with
      | left _ => left _
      | right _ => right _
      end                  
  ). *)




Inductive protoError {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') : Prop :=
| NotDual : (~Dual p1 p2) -> protoError p1 p2
| NoDecrypt : (*forall  (m:message t) (k:keyType), (is_not_decryptable t m k) -> *) protoError p1 p2.              

Fixpoint runProto' {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') (l: nat)
  : (message T) + {(protoError p1 p2)}. (*{(~ (Dual p1 p2))}*)
                    case_eq p1. case_eq p2. intros. apply inright. apply NotDual. unfold not. trivial. intros. assert ({t0 = t1} + {t0 <> t1}). apply (eq_type_dec t0 t1). destruct H1. subst. clear H. clear H0. assert (message T1 + {(protoError p0 (p m))}). apply (runProto' p'0 p' T1 T0 p0 (p m) (protoTypeLength p'0)). destruct X. apply inleft. exact m0. apply inright. destruct p3. apply NotDual. unfold not. intros. inversion H0. contradiction. apply NoDecrypt. clear H. clear H0. apply inright. apply NotDual. unfold not. intros. inversion H. symmetry in H0. contradiction. intros. apply inright. apply NotDual. unfold not. intros. inversion H1. intros. apply inright. apply NotDual. unfold not. intros. inversion H1. intros. apply inright. apply NotDual. unfold not. intros. inversion H1. intros. apply inright. apply NotDual. unfold not. intros. inversion H1. intros. destruct p2. assert ({t0 = t1} + {t0 <> t1}). apply (eq_type_dec t0 t1). destruct H0. subst. clear H. assert (message T0 + {(protoError (p m) p2)}). apply (runProto' _ _ _ _ (p m) p2 (protoTypeLength p')). destruct X. apply inleft. exact m0. apply inright. destruct p0. apply NotDual. unfold not. intros. inversion H0. contradiction. apply NoDecrypt. clear H. apply inright. apply NotDual. unfold not. intros. inversion H. contradiction. apply inright. apply NotDual. unfold not. intros. inversion H0. apply inright. apply NotDual. unfold not. intros. inversion H0. apply inright. apply NotDual. unfold not. intros. inversion H0. apply inright. apply NotDual. unfold not. intros. inversion H0. apply inright. apply NotDual. unfold not. intros. inversion H0. intros. destruct b. destruct p2. apply inright. apply NotDual. unfold not. intros. inversion H0. apply inright. apply NotDual. unfold not. intros. inversion H0. apply inright. apply NotDual. unfold not. intros. inversion H0.
                    assert ({DualT r r0} + {~ DualT r r0}). apply (DualT_dec r r0). assert ({DualT s s0} + {~ DualT s s0}). apply (DualT_dec s s0). destruct H0. destruct H1. destruct (runProto' r r0 R R0 p p2_1 (protoTypeLength r0)). left. exact m. apply inright. destruct p2. contradiction. apply NoDecrypt. apply inright. apply NotDual. unfold not. intros. inversion H0. contradiction. apply inright. apply NotDual. unfold not. intros. inversion H0. contradiction. apply inright. apply NotDual. unfold not. intros. inversion H0.  apply inright. apply NotDual. unfold not. intros. inversion H0. destruct p2. apply inright. apply NotDual. unfold not. intros. inversion H0. apply inright. apply NotDual. unfold not. intros. inversion H0. apply inright. apply NotDual. unfold not. intros. inversion H0.

                    assert ({DualT r r0} + {~ DualT r r0}). apply (DualT_dec r r0). assert ({DualT s s0} + {~ DualT s s0}). apply (DualT_dec s s0). destruct H0. destruct H1. destruct (runProto' _ _ _ _ p0 p2_2 (protoTypeLength s)). left. exact m. apply inright. destruct p2. contradiction. apply NoDecrypt. apply inright. apply NotDual. unfold not. intros. inversion H0. contradiction. apply inright. apply NotDual. unfold not. intros. inversion H0. contradiction. apply inright. apply NotDual. unfold not. intros. inversion H0.  apply inright. apply NotDual. unfold not. intros. inversion H0. intros. destruct p2. apply inright. apply NotDual. unfold not. intros. inversion H0. apply inright. apply NotDual. unfold not. intros. inversion H0. assert ({DualT r r0} + {~ DualT r r0}). apply (DualT_dec r r0). assert ({DualT s s0} + {~ DualT s s0}). apply (DualT_dec s s0). destruct H0. destruct H1. destruct b. destruct (runProto' _ _ _ _ p p2_1 (protoTypeLength r)). apply inleft. exact (leither _ _ m). apply inright. destruct p2. apply NotDual. unfold not. intros. inversion H1. contradiction. apply NoDecrypt. destruct (runProto' _ _ _ _ p0 p2_2 (protoTypeLength s)). apply inleft. exact (reither _ _ m). apply inright. destruct p2. apply NotDual. unfold not. intros. inversion H1. contradiction. apply NoDecrypt. apply inright. apply NotDual. unfold not. intros. inversion H0. contradiction. apply inright. apply NotDual. unfold not. intros. inversion H0. contradiction. apply inright. apply NotDual. unfold not. intros. inversion H0. apply inright. apply NotDual. unfold not. intros. inversion H0. apply inright. apply NotDual. unfold not. intros. inversion H0. intros. clear H. destruct (is_not_decryptable

                    apply inright. apply NotDual. unfold not. intros. inversion H0.

                    apply NotDual. unfold not in n. unfold Dual in n. apply n in d. inversion d. right. unfold not. intros. destruct H0. contradiction. right. unfold not. intros. destruct H0. contradiction.

                    unfold Dual. assert ({DualT s s0} + {~ DualT s s0}). apply (DualT_dec s s0). assert ({DualT r r0} + {~ DualT r r0}). apply (DualT_dec r r0). destruct H0. destruct H1. destruct (runProto' s s0 S S0 p0 p2_2 (protoTypeLength s0)). left. exact m. unfold not in n. unfold Dual in n. apply n in d. inversion d. right. unfold not. intros. destruct H0. contradiction. right. unfold not. intros. destruct H0. contradiction. apply inright. intros. unfold not. intros. inversion H0. intros.


                    

                                                                                                                                                                                                                                                                                                                                                                                                     intros. unfold Dual. simpl. unfold Dual in n. unfold not in n. unfold not.  intros. destruct H.  apply n in H0.  assumption. apply inright. unfold Dual. simpl. unfold not. unfold not in n. intros. destruct H1. symmetry in H1. apply n in H1.  assumption. intros. apply inright. unfold Dual. simpl. unfold not. trivial. intros. apply inright. unfold Dual. unfold not. trivial. intros. apply inright. unfold Dual. unfold not. trivial. destruct p2. intros. assert ({t0 = t1} + {t0 <> t1}). apply (eq_type_dec t0 t1). destruct H0. subst. assert (message T1 + {~ Dual (p m) p2 }). apply (runProto' p'0 p' T1 T0 (p m) p2 (protoTypeLength p'0)). destruct X. apply inleft. exact m0. apply inright. intros. unfold Dual. simpl. unfold Dual in n. unfold not in n. unfold not.  intros. destruct H0.  apply n in H1.  assumption. apply inright. unfold Dual. simpl. unfold not. unfold not in n. intros. destruct H0. symmetry in H0. apply n in H0.  assumption. intros. apply inright. unfold Dual. unfold not. trivial. intros.  apply inright. intros. unfold not. intros. inversion H0. intros. apply inright. unfold not. intros. inversion H0. intros. apply inright. unfold not. intros. inversion H0.  intros. destruct p2. destruct b. apply inright. unfold not. intros. inversion H0. apply inright. unfold not. intros. inversion H0. apply inright. unfold not. intros. inversion H0. apply inright. unfold not. intros. inversion H0. destruct b. 

                    unfold Dual. assert ({DualT r r0} + {~ DualT r r0}). apply (DualT_dec r r0). assert ({DualT s s0} + {~ DualT s s0}). apply (DualT_dec s s0). destruct H0. destruct H1. destruct (runProto' r r0 R R0 p p2_1 (protoTypeLength r0)). left. exact m. unfold not in n. unfold Dual in n. apply n in d. inversion d. right. unfold not. intros. destruct H0. contradiction. right. unfold not. intros. destruct H0. contradiction.

                    unfold Dual. assert ({DualT s s0} + {~ DualT s s0}). apply (DualT_dec s s0). assert ({DualT r r0} + {~ DualT r r0}). apply (DualT_dec r r0). destruct H0. destruct H1. destruct (runProto' s s0 S S0 p0 p2_2 (protoTypeLength s0)). left. exact m. unfold not in n. unfold Dual in n. apply n in d. inversion d. right. unfold not. intros. destruct H0. contradiction. right. unfold not. intros. destruct H0. contradiction. apply inright. intros. unfold not. intros. inversion H0. intros.  

                    destruct p2. right. unfold not. intros. inversion H0. right. unfold not. intros. inversion H0. destruct b. unfold Dual. assert ({DualT r r0} + {~ DualT r r0}). apply (DualT_dec r r0). assert ({DualT s s0} + {~ DualT s s0}). apply (DualT_dec s s0). destruct H0. destruct H1. destruct (runProto' s s0 S S0 p0 p2_2 (protoTypeLength s0)). left. exact (reither R S m). unfold not in n. unfold Dual in n. apply n in d0. inversion d0. right. unfold not. intros. destruct H0. contradiction. right. unfold not. intros. destruct H0. contradiction. unfold Dual. assert ({DualT r r0} + {~ DualT r r0}). apply (DualT_dec r r0). assert ({DualT s s0} + {~ DualT s s0}). apply (DualT_dec s s0). destruct H0. destruct H1. destruct (runProto' r r0 R R0 p p2_1 (protoTypeLength r0)). left. exact (leither R S m). unfold not in n. unfold Dual in n. apply n in d. inversion d. right. unfold not. intros. destruct H0. contradiction. right. unfold not. intros. destruct H0. contradiction. right. unfold not. intros. inversion H0. right. unfold not. intros. inversion H0. intros. destruct p2. right. unfold not. intros. inversion H0. right. unfold not. intros. inversion H0. right. unfold not. intros. inversion H0. right. unfold not. intros. inversion H0. left. exact m. Defined.

Inductive protoError {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') : Type :=
| NotDual : (~ Dual p1 p2) -> protoError p1 p2
| NoDecrypt : protoError p1 p2.
  
Definition runProto {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t')
  : (message T) + {(~ (Dual p1 p2))} := runProto' p1 p2 (protoLength p1).

Definition proto3 :=
  send (basic 1);
  ReturnC (t:=Basic) (basic 1).

Definition proto3' :=
  x <- receive;
  ReturnC (t:=Basic) x.

Definition incPayload (m:message Basic) : (message Basic) :=
  match m with
  | basic n => basic (n + 1)
  end.
  
Definition proto4 :=
  x <- receive;
  send (incPayload x);
  ReturnC x.
Check proto4.

Definition proto5 :=
  send (basic 1);
  x <- receive;
  ReturnC (t:=Basic) x.
Check proto5.

Example dual45 : Dual proto4 proto5. unfold Dual. simpl. auto.

Definition proto6 :=
  choice true EpsC
         proto4. Check proto6.

Definition proto7 :=
  offer EpsC
        proto5. Check proto7.

Example dual67 : Dual proto6 proto7. unfold Dual. simpl. auto. Qed.
           
Eval compute in (runProto proto3 proto3').

Eval compute in (runProto proto4 proto5).
Eval compute in (runProto proto5 proto4).
Eval compute in (runProto proto5 proto3).
Eval compute in (runProto proto6 proto7).



End try11.