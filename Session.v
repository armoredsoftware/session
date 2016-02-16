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
                                        -> (protoExp (Either R S) (Offer r s))| ReturnC {t:type} : (message t) -> protoExp t (Eps t).

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


Definition enc1 := encrypt (basic 42) (public 1). Check enc1.
Definition enc2 := encrypt enc1 (public 2).
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

Definition pair1 := pair (basic 1) (basic 2).
Eval compute in pairFst pair1.
Definition pair1' := pair (bad Basic) (basic 2).
Eval compute in pairFst pair1'.
Definition pair1'' := pair  (basic 1) (bad Basic).
Eval compute in pairFst pair1''.

Definition pairSnd{t1 t2: type} (m:message (Pair t1 t2)) : message t2 :=
  match m in message t' return message (getP2Type t') with
  | pair _ _ _ m2 => m2
  | bad _ => bad _ (*(getP1Type tb1) *)
  | _ => bad _                
  end.

Definition pair2 := pair (basic 1) (basic 2).
Eval compute in pairSnd pair2.
Definition pair2' := pair (basic 1) (bad Basic).
Eval compute in pairSnd pair2'.

(*Fixpoint protoTypeLength (t:protoType) : nat :=
  match t with
  | Send _ t' => 1 + (protoTypeLength t')
  | Receive _ t' => 1 + (protoTypeLength t')
  | Choice p1 p2 => 1 + protoTypeLength p1
  | Offer p1 p2 => 1 + protoTypeLength p1
  | Eps _ => 1                               
  end. *)

Fixpoint protoExpLength {T:type} {pt:protoType} (p: protoExp T pt) : nat :=
  match p with
  | SendC _ _ _ _ p' => 1 + (protoExpLength p')
  | ReceiveC t _ _ f => 1 + (protoExpLength (f (bad t)))
  | ChoiceC b _ _ _ _ p' p'' => if b then (protoExpLength p')
                               else (protoExpLength p'')
  | OfferC _ _ _ _ p' p'' => max (protoExpLength p') (protoExpLength p'')
  | ReturnC _ _ => 1
  end.                                                                                   

Definition protoLength {t:protoType} {T:type} (p1:protoExp T t) : nat := (*protoTypeLength t*) protoExpLength p1.

(*Eval compute in protoTypeLength (Send Basic (Eps Basic)). *)

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


Fixpoint runProto'' {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') (l: nat)
  : (message T) + {(~ (Dual p1 p2))}.
Proof. destruct l. left. exact (bad T).
  case_eq p1; case_eq p2; intros;
       
  (* Eliminate all un-interesting cases (20 of the 25 subgoals!) *)
  try (right; unfold not; intros; contradiction).

  (* Send/Receive case *)
  destruct (eq_type_dec t0 t2). subst. clear H. clear H0. assert (message T1 + {~ Dual p0 (p m)}). apply (runProto'' p'0 p' T1 T0 p0 (p m) l(*(protoExpLength (p m))*)). destruct X; try (right; unfold not; intros HH; inversion HH; contradiction). apply inleft. exact m0. right. unfold not. intros HH. inversion HH. symmetry in H1. contradiction.

  (* Receive/Send case *)
  destruct (eq_type_dec t0 t2). subst. clear H. clear H0. assert (message T1 + {~ Dual (p0 m) p }). apply (runProto'' _ _ _ _ (p0 m) p (*(protoExpLength (p0 m))*) l). destruct X; try (right; unfold not; intros HH; inversion HH; contradiction). apply inleft. exact m0. right. unfold not. intros HH. inversion HH. symmetry in H1. contradiction.

  (* Choice/Offer case *)
  destruct b; destruct (DualT_dec r0 r); destruct (DualT_dec s0 s).

    (* true case *)
    clear H.  clear H0. destruct (runProto'' _ _ _ _ p3 p (*(protoExpLength p3)*) l); try (right; unfold not; intros; destruct H1; contradiction). left. exact m. unfold not in n. unfold Dual in n. apply n in d. inversion d. right. unfold not. intros. destruct H1. contradiction. right. unfold not. intros. destruct H1. contradiction. right. unfold not. intros. destruct H1. contradiction.

    (* false case *)
    clear H.  clear H0. destruct (runProto'' _ _ _ _ p4 p0 (*(protoExpLength p4)*) l); try (right; unfold not; intros; destruct H1; contradiction). left. exact m. unfold not in n. unfold Dual in n. apply n in d0. inversion d0. right. unfold not. intros. destruct H1. contradiction. right. unfold not. intros. destruct H1. contradiction. right. unfold not. intros. destruct H1. contradiction.

  (* Offer/Choice case *)
  destruct b; destruct (DualT_dec r0 r); destruct (DualT_dec s0 s).

    (* true case *)
    clear H.  clear H0. destruct (runProto'' _ _ _ _ p3 p (*(protoExpLength p3)*) l); try (right; unfold not; intros; destruct H1; contradiction). left. exact (leither _ _ m). unfold not in n. unfold Dual in n. apply n in d. inversion d. right. unfold not. intros. destruct H1. contradiction. right. unfold not. intros. destruct H1. contradiction. right. unfold not. intros. destruct H1. contradiction.

    (* false case *)
    clear H.  clear H0. destruct (runProto'' _ _ _ _ p4 p0 (*(protoExpLength p4)*) l); try (right; unfold not; intros; destruct H1; contradiction). left. exact (reither _ _  m). unfold not in n. unfold Dual in n. apply n in d0. inversion d0. right. unfold not. intros. destruct H1. contradiction. right. unfold not. intros. destruct H1. contradiction. right. unfold not. intros. destruct H1. contradiction.

  (* Return case *)
    left. exact m0.

   
Defined.

  
Definition runProto' {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t')
  : (message T) + {(~ (Dual p1 p2))} := runProto'' p1 p2 (1 + (max (protoLength p1) (protoLength p2))).

Fixpoint DualTSymm {t t':protoType} : DualT t t' -> DualT t' t.
Proof.
  intros. destruct t; destruct t'; try (inversion H); try (
  split;
  subst; trivial;
  apply (DualTSymm); assumption). Defined.

Hint Resolve DualTSymm.

Lemma notDualSymm {t t':protoType} {T T':type} {p1:protoExp T t} {p2:protoExp T' t'} : (~ Dual p1 p2) -> (~ Dual p2 p1).
Proof. 
  intros. unfold not. intros. apply DualTSymm in H0. unfold Dual in H. contradiction. Qed.

  
Definition runProto {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') : ((message T * message T') + {~ (Dual p1 p2)}).
  refine(
  match (runProto' p1 p2) with
  | inleft m =>
    match (runProto' p2 p1) with
    | inleft m' => inleft (m, m')
    | inright p => inright (notDualSymm p)
    end
  | inright p => inright p           
  end). Defined.

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

Eval compute in runProto proto4 proto5.

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
Definition bPri := (private 2).
Definition aPriBad := (private 5).
Definition bPriBad := (private 6).

Definition Needham_A (myPri theirPub:keyType) :=
  send (encrypt (basic 1) theirPub);
  x <- receive; (* x : Encrypt (Pair Basic Basic) *) 
  let y := decryptM x myPri in (* y : Pair Basic Basic *) 
  let y' := (pairSnd (t1:=Basic) (t2:=Basic) y) in 
  send (encrypt y' theirPub);
  ReturnC (t:= (Pair Basic Basic)) y. Check Needham_A.

Definition Needham_B (myPri theirPub:keyType) :=
  x <- receive; (* x : Encrypt Basic *)
  let y := decryptM x myPri in (* y : Basic *)
  send (encrypt (pair y (basic 2)) theirPub);
  z <- receive; (* z : Encrypt Basic *)
  let z' := decryptM z myPri in    (* z' : Basic *)
  ReturnC (t:= Pair Basic (Basic)) (pair y z'). Check Needham_B.



Example DualNeedham {a b c d:keyType} : Dual (Needham_A a b) (Needham_B c d).
Proof. unfold Dual; simpl. repeat( split;trivial). Qed.

Definition Needham_A_good := (Needham_A aPri bPub).
Definition Needham_B_good := (Needham_B bPri aPub).

Eval compute in runProto Needham_A_good Needham_B_good.

Definition Needham_A_badAuth := (Needham_A aPriBad bPub).
Definition Needham_A_badEncrypt := (Needham_A aPri bPubBad).
Definition Needham_B_badAuth := (Needham_B bPriBad aPub).
Definition Needham_B_badEncrypt := (Needham_B bPri aPubBad).

Eval compute in runProto Needham_A_good Needham_B_badAuth.
Eval compute in runProto Needham_A_good Needham_B_badEncrypt.

Eval compute in runProto Needham_B_good Needham_A_badAuth.
Eval compute in runProto Needham_B_good Needham_A_badEncrypt.

Eval compute in runProto Needham_A_badAuth Needham_B_badAuth.
Eval compute in runProto Needham_A_badAuth Needham_B_badEncrypt.

Eval compute in runProto Needham_A_badEncrypt Needham_B_badAuth.
Eval compute in runProto Needham_A_badEncrypt Needham_B_badEncrypt.

Definition protoAuth1 (theirPub:keyType) :=
  let m1 := encrypt (basic 1) theirPub in
  send m1;
  x <- receive;
  ReturnC (t:=Basic) x. Check protoAuth1.

Definition protoAuth2 (myPri:keyType) :=
  x <- receive;
  let m1 := decryptM x myPri in
  send m1;
  ReturnC (t:=Basic) m1. Check protoAuth2.

Definition protoAuthGoodResult :=  runProto (protoAuth1 (public 2)) (protoAuth2 (private 2)). Eval compute in protoAuthGoodResult.

Example uniqueAuth : forall k,
    (runProto (protoAuth1 (public 2)) (protoAuth2 k)) = protoAuthGoodResult
    -> (k = (private 2)).
Proof.
  intros. destruct protoAuthGoodResult. inversion H. destruct (eq_key_dec k (private 2)). assumption. Abort.
       
End session.