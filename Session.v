Require Export SfLib.
Require Export CpdtTactics.
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
  destruct (eq_type_dec t t2); destruct (DualT_dec t0 t');
  try (right; unfold not; intros; inversion H; contradiction);
  try (left; split; assumption)
  );

  (* For the Choice/Offer, Offer/Choice cases *)
  try (
  destruct (DualT_dec t2 t'1); destruct (DualT_dec t3 t'2);
  try (right; unfold not; intros; inversion H; contradiction);
  try( left; split; assumption)
    ).

  (* Eps/Eps case *)
  left. simpl. trivial.
  
Defined.

Definition Dual {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') : Prop := DualT t t'.            


Fixpoint runProto' {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') (l: nat)
  : (message T) + {(~ (Dual p1 p2))}.
Proof.
  case_eq p1; case_eq p2; intros;
  (* Eliminate all un-interesting cases (20 of the 25 subgoals!) *)
  try (right; unfold not; intros; contradiction).

  (* Send/Receive case *)
  destruct (eq_type_dec t0 t2). subst. clear H. clear H0. assert (message T1 + {~ Dual p0 (p m)}). apply (runProto' p'0 p' T1 T0 p0 (p m) (protoTypeLength p'0)). destruct X; try (right; unfold not; intros HH; inversion HH; contradiction). apply inleft. exact m0. right. unfold not. intros HH. inversion HH. symmetry in H1. contradiction.

  (* Receive/Send case *)
  destruct (eq_type_dec t0 t2). subst. clear H. clear H0. assert (message T1 + {~ Dual (p0 m) p }). apply (runProto' _ _ _ _ (p0 m) p (protoTypeLength p'0)). destruct X; try (right; unfold not; intros HH; inversion HH; contradiction). apply inleft. exact m0. right. unfold not. intros HH. inversion HH. symmetry in H1. contradiction.

  (* Choice/Offer case *)
  destruct b; destruct (DualT_dec r0 r); destruct (DualT_dec s0 s).

    (* true case *)
    clear H.  clear H0. destruct (runProto' _ _ _ _ p3 p (protoTypeLength r0)); try (right; unfold not; intros; destruct H1; contradiction). left. exact m. unfold not in n. unfold Dual in n. apply n in d. inversion d. right. unfold not. intros. destruct H1. contradiction. right. unfold not. intros. destruct H1. contradiction. right. unfold not. intros. destruct H1. contradiction.

    (* false case *)
    clear H.  clear H0. destruct (runProto' _ _ _ _ p4 p0 (protoTypeLength s0)); try (right; unfold not; intros; destruct H1; contradiction). left. exact m. unfold not in n. unfold Dual in n. apply n in d0. inversion d0. right. unfold not. intros. destruct H1. contradiction. right. unfold not. intros. destruct H1. contradiction. right. unfold not. intros. destruct H1. contradiction.

  (* Offer/Choice case *)
  destruct b; destruct (DualT_dec r0 r); destruct (DualT_dec s0 s).

    (* true case *)
    clear H.  clear H0. destruct (runProto' _ _ _ _ p3 p (protoTypeLength r0)); try (right; unfold not; intros; destruct H1; contradiction). left. exact (leither _ _ m). unfold not in n. unfold Dual in n. apply n in d. inversion d. right. unfold not. intros. destruct H1. contradiction. right. unfold not. intros. destruct H1. contradiction. right. unfold not. intros. destruct H1. contradiction.

    (* false case *)
    clear H.  clear H0. destruct (runProto' _ _ _ _ p4 p0 (protoTypeLength s0)); try (right; unfold not; intros; destruct H1; contradiction). left. exact (reither _ _  m). unfold not in n. unfold Dual in n. apply n in d0. inversion d0. right. unfold not. intros. destruct H1. contradiction. right. unfold not. intros. destruct H1. contradiction. right. unfold not. intros. destruct H1. contradiction.

  (* Return case *)
  left. exact m0. Defined.

  
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