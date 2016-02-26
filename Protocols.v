Require Import Crypto.
Require Import Session.
Require Import Peano_dec.


Module protocols.

Definition proto1 := SendC (basic 1) EpsC.
Check proto1.

Definition protoSimple1 :=
  send (basic 1);
  EpsC.

Definition protoSimple2 :=
  x <- receive;
  ReturnC (t:=Basic) x.

Example dualSimple12 : Dual protoSimple1 protoSimple2. unfold Dual. simpl. split. reflexivity. trivial. 
Defined. Check dualSimple12. Eval compute in dualSimple12.

Example dualSimple21 : Dual protoSimple2 protoSimple1. split; reflexivity.
Defined. Check dualSimple21. Eval compute in dualSimple21.

Example sameProofs : dualSimple12 = dualSimple21. reflexivity. Qed.

Eval compute in runProto protoSimple1 protoSimple2  dualSimple21.
Eval compute in runProto protoSimple2 protoSimple1  dualSimple21.

Example simpleResult : fst (runProto protoSimple2 protoSimple1 dualSimple21) = (basic 1).
Proof. auto. Qed.

Definition proto3 :=
  send (basic 42);
  ReturnC (t:=Basic) (basic 1). Check proto3.

Definition proto3' :=
  x <- receive;
  ReturnC (t:=Basic) x. Check proto3'.

Example dual33' : Dual proto3 proto3'. unfold Dual. simpl. auto. Defined.

Eval compute in (runProto proto3' proto3 dual33').

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

Example dual45 : Dual proto4 proto5. unfold Dual. simpl. auto. Defined.

Eval compute in runProto proto4 proto5 dual45.

Example eval45 : fst (runProto proto4 proto5 dual45) = basic 42.
auto. Qed.

Definition proto6 (b:bool) :=
  choice b EpsC
         proto5. Check proto6.

Definition proto7 :=
  offer EpsC
        proto4. Check proto7.

Example dual67 : forall b, Dual (proto6 b) proto7. unfold Dual. simpl. auto. Defined.

Eval compute in (runProto (proto6 false) proto7 (dual67 false)).
Eval compute in (runProto (proto6 true) proto7 (dual67 true)).

Example notDual35 : ~ (Dual proto3  proto5). auto. Defined.
Eval compute in (runProto proto5 proto3).

(* Simplest possible encrypt/decrypt protocol pair *)
Definition protoEncrypt1 (theirPub:keyType) :=
  send (encrypt (basic 42) theirPub);
  EpsC.

Definition protoDecrypt1 (myPri:keyType) :=
  x <- receive;
  ReturnC (t:=Basic) (decryptM x myPri).

Example dualEncDec1 : forall k k', Dual (protoEncrypt1 k) (protoDecrypt1 k'). split; reflexivity.
Defined.

Example dualDecEnc1 : forall k k', Dual (protoDecrypt1 k) (protoEncrypt1 k') . split; reflexivity.
Defined.

Definition encDecDual1 := dualEncDec1 (private 1) (private 1).

Eval compute in runProto'OneStep (protoEncrypt1 (public 1)) (protoDecrypt1 (private 1)) (dualDecEnc1 (public 1) (private 1)).

Eval compute in runProtoOneStep (protoEncrypt1 (public 1)) (protoDecrypt1 (private 1)) (dualDecEnc1 (public 1) (private 1)).

Eval compute in runProto (protoDecrypt1 (private 1)) (protoEncrypt1 (public 1)).

Eval compute in fst (runProto (protoDecrypt1 (private 1)) (protoEncrypt1 (public 1)) encDecDual1).

Eval compute in runProtoMultiStep (protoDecrypt1 (private 1)) (protoEncrypt1 (public 1)) encDecDual1.


Definition isBad {t:type} (m:message t) : Prop :=
  match m with
  | bad _ => True
  | _ => False
  end.

(*Inductive isBad' {t:type} : (message t) -> Prop :=
| aa : isBad' (bad t). *)

Lemma is_dec_info{t:type} : forall (m:message t) k k', (is_decryptable (encrypt m k) k') -> k = inverse k'.
Proof.
  intros.
  inversion H. assert ((inverse (inverse k)) = k). apply inverse_inverse. symmetry in H1. assumption. Qed.

Lemma notBadContra {t:type} : forall (m:message t) k k', (~isBad m) -> decryptM (encrypt m k) k' = m -> is_not_decryptable (encrypt m k) k' -> False.
Proof.
  intros. unfold decryptM in H0. destruct (decrypt (encrypt m k) k').
    inversion p. inversion H2. simpl in H1. contradiction. 
    unfold not in H. apply H. subst. constructor.
Qed.

Eval compute in decryptM (encrypt (bad Basic) (public 1)) (private 2).

Lemma decryptSuccess{t:type} : forall (m : message t) k k', (~ isBad m) ->  decryptM (encrypt m k) k' = m -> k = inverse k'.
Proof.
  intros. destruct m eqn:hh;
  try (destruct (decrypt (encrypt m k) k'); [inversion p; apply is_dec_info in H1; assumption | exfalso; rewrite <- hh in H0; rewrite <- hh in H; apply (notBadContra m k k' H H0 i)]).
Qed.
  
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

Example dualProtoAuth12 {k k':keyType} : Dual (protoAuth1 k) (protoAuth2 k').
Proof. unfold Dual; simpl. repeat( split;trivial). Defined.

Eval compute in runProto (protoAuth1 (public 2))
                         (protoAuth2 (private 2))
                         dualProtoAuth12.
Eval compute in runProtoMultiStep
                  (protoAuth1 (public 2))
                  (protoAuth2 (private 2))         
                         dualProtoAuth12.

Example goodResult : fst (runProto (protoAuth1 (private 1)) (protoAuth2 (public 1)) dualProtoAuth12) = (basic 1).
Proof. auto. Qed.

Example uniqueAuth : forall k k',
    fst (runProto (protoAuth1 k) (protoAuth2 k') dualProtoAuth12)
      = (basic 1)
    -> (k = (inverse k')).
Proof.
  intros. destruct (is_inverse k k'). 
  assumption.
  simpl in H. Abort.

Example uniqueAuth : forall k k',
    fst (runProtoMultiStep (protoAuth1 k) (protoAuth2 k') dualProtoAuth12)
      = (basic 1)
    -> (k = (inverse k')).
Proof.
  intros. destruct (is_inverse k k').
  assumption.
  simpl in H. assert (~ isBad (basic 1)). unfold not. intros. inversion H0. assert (k = inverse k'). apply (decryptSuccess (basic 1) k k' H0 H). assumption.
Qed.

Example badAuth : forall k', 
    fst (runProto (protoAuth1 (public 2)) (protoAuth2 k') dualProtoAuth12)
    = bad Basic -> k' <> (private 2).
Proof. intros.  destruct (eq_key_dec k' (private 2)).
       subst. simpl in H. inversion H. assumption.
Qed.

Example badAuth' : forall k', 
    fst (runProtoMultiStep (protoAuth1 (public 2)) (protoAuth2 k') dualProtoAuth12) = bad Basic ->
    k' <> (private 2).
Proof.
  intros.  destruct (eq_key_dec k' (private 2)).
  subst. simpl in H. inversion H. assumption.
Qed.

Lemma invPub : forall n k', (public n = inverse k') -> k' = private n.
Proof.
  intros. destruct k'. simpl in H. inversion H. inversion H. reflexivity. inversion H. Qed.

Example goodAuth : forall k',
    fst (runProto (protoAuth1 (public 2)) (protoAuth2 k') dualProtoAuth12)
        = basic 1 ->
    k' = (private 2).
Proof.
  intros. destruct (eq_key_dec k' (private 2)).
  assumption.
  simpl in H. Abort.

Example goodAuth : forall k',
    fst (runProtoMultiStep (protoAuth1 (public 2)) (protoAuth2 k') dualProtoAuth12) = basic 1 ->
    k' = (private 2).
Proof.
  intros. destruct (eq_key_dec k' (private 2)).
  assumption.
  simpl in H. assert (~ isBad (basic 1)). unfold not. intros. inversion H0. assert ((public 2) = inverse k'). apply (decryptSuccess (basic 1) (public 2) k' H0 H). apply invPub in H1. assumption.
Qed.


(*********************** Needham-Schroeder   **********************)

Definition aPub := (public 1).
Definition bPub := (public 2).
Definition aPubBad := (public 3).
Definition bPubBad := (public 4).
Definition aPri := (private 1).
Definition bPri := (private 2).
Definition aPriBad := (private 5).
Definition bPriBad := (private 6).

Definition aNonce := (basic 1).
Definition bNonce := (basic 2).
                    

Definition Needham_A (myPri theirPub:keyType) :=
  send (encrypt aNonce theirPub);
  x <- receive; (* x : Encrypt (Pair Basic Basic) *) 
  let y := decryptM x myPri in (* y : Pair Basic Basic *)
  let y' := (pairFst (t1:=Basic) (t2:=Basic) y) in
  let y'' := (pairSnd y) in 
  send (encrypt y'' theirPub);
  ReturnC (pair y' y''). Check Needham_A.

Eval compute in protoExpLength (Needham_A aPri bPub).

Definition Needham_B (myPri theirPub:keyType) :=
  x <- receive; (* x : Encrypt Basic *)
  let y := decryptM x myPri in (* y : Basic *)
  send (encrypt (pair y bNonce) theirPub);
  z <- receive; (* z : Encrypt Basic *)
  let z' := decryptM z myPri in    (* z' : Basic *)
  ReturnC (t:= Pair Basic (Basic)) (pair y z'). Check Needham_B.

Definition Needham_A_good := (Needham_A aPri bPub).
Definition Needham_B_good := (Needham_B bPri aPub).

Example DualNeedham {a b c d:keyType} : Dual (Needham_A a b) (Needham_B c d).
Proof. unfold Dual; simpl. repeat( split;trivial). Defined.

Eval compute in (runProtoOneStep (Needham_A aPri bPub) (Needham_B bPri aPub) DualNeedham).

Eval compute in runProto Needham_A_good Needham_B_good DualNeedham.
Eval compute in runProtoMultiStep Needham_A_good Needham_B_good DualNeedham.

Definition Needham_A_badAuth := (Needham_A aPriBad bPub).
Definition Needham_A_badEncrypt := (Needham_A aPri bPubBad).
Definition Needham_B_badAuth := (Needham_B bPriBad aPub).
Definition Needham_B_badEncrypt := (Needham_B bPri aPubBad).

(* A is good, B is an intruder.
   A returns (bad, basic 2).  The bad propogates from the fact that B is
     unable to decrypt A's first sent message(A's nonce), and hence is 
     unable to send it back to A.
   B returns (bad, bad).  The first bad is because B cannot decrypt A's
     first message.  The second bad is because B cannot decrypt A's second
     sent message (A sending back the nonce it received from B). *)
Eval compute in runProto Needham_A_good Needham_B_badAuth DualNeedham.
Definition aGoodBbadAuth := runProtoMultiStep Needham_A_good Needham_B_badAuth DualNeedham.
Eval compute in aGoodBbadAuth.
Eval compute in pairFst (fst aGoodBbadAuth).
                                              
(* Are the badEncrypt cases worth demonstrating??
   i.e: Do we care about results when encrypting with the wrong pub key? *)
Eval compute in runProto Needham_A_good Needham_B_badEncrypt DualNeedham.

Eval compute in runProto Needham_A_badAuth Needham_B_good DualNeedham. 
Eval compute in runProto Needham_A_badEncrypt Needham_B_good DualNeedham.

Eval compute in runProto Needham_A_badAuth Needham_B_badAuth DualNeedham.
Eval compute in runProto Needham_A_badAuth Needham_B_badEncrypt DualNeedham.

Eval compute in runProto Needham_A_badEncrypt Needham_B_badAuth DualNeedham.
Eval compute in runProto Needham_A_badEncrypt Needham_B_badEncrypt DualNeedham.


Theorem needham_auth : forall k k',
    pairFst (fst (runProto (Needham_A aPri k) (Needham_B k' aPub) DualNeedham)) = aNonce ->
    k = inverse k'.
Proof.
  intros. destruct (is_inverse k k').
  assumption.
  simpl in H. assert (~ isBad aNonce). unfold not. intros. inversion H0. assert (k = inverse k'). apply (decryptSuccess aNonce k k' H0 H). assumption.
Qed.
  
Theorem needham_auth' : forall k k',
    pairFst (fst (runProtoMultiStep (Needham_A aPri k) (Needham_B k' aPub) DualNeedham)) = aNonce ->
    k = inverse k'.
Proof.
  intros. destruct (is_inverse k k').
  assumption.
  simpl in H. assert (~ isBad aNonce). unfold not. intros. inversion H0. assert (k = inverse k'). apply (decryptSuccess aNonce k k' H0 H). assumption.
Qed.

Theorem needham_auth_gen : forall k k' j j',
    pairFst ( fst (runProto (Needham_A j' k) (Needham_B k' j) DualNeedham)) = aNonce ->
    j = inverse j' -> 
    k = inverse k'.
Proof.
  intros. apply inverse_info in H0. destruct H0. destruct H0. inversion H0. subst. destruct (is_inverse k k').
  assumption.
  cbv in H. Abort.

Lemma invertInverse : forall k k', k = inverse k' -> inverse k = k'.
Proof.
  intros.
  destruct k; destruct k'; try inversion H. simpl. inversion H. subst. reflexivity. inversion H. subst. reflexivity. subst. reflexivity. Qed.

  
Theorem needham_auth'' : forall k, pairFst (fst (runProtoMultiStep (Needham_A aPri bPub) (Needham_B k aPub) DualNeedham)) = aNonce -> k = inverse bPub.
Proof. intros. symmetry. apply (invertInverse bPub k). apply (needham_auth bPub k H).
Qed.

(* END Needham-Schroeder ********************************)

Definition unwrapBasic (m:message Basic) : nat :=
  match m with
  | basic n => n
  | _ => 0
  end. 

Definition server1 := offer (
  a <- receive;
  b <- receive;
  let x := unwrapBasic a in
  let y := unwrapBasic b in
  send (basic (x + y));
    EpsC)
   (                         
   a <- receive; 
   let x := unwrapBasic a in
   send (basic (0 - x));
   EpsC  ). Check server1.

Definition server2 := offer
   EpsC
   (                         
   a <- receive; 
   let x := unwrapBasic a in
   send (basic (0 - x));
     EpsC  ). Check server2.

Definition client :=
  choice false
         EpsC
        (
           send (basic 1);
           y <- receive;
           ReturnC (t:=Basic) y
        ). Check client.

Definition client' {T:type} {t:protoType} {r: protoExp T t} :=
  choice false
         r
        (
           send (basic 1);
           y <- receive;
           ReturnC (t:=Basic) y
         ). Check client.

Example dual2c : Dual server2 client. unfold Dual. repeat (split;auto).
Defined.

Example dual2c' : Dual server2 (client' (r:=EpsC)). unfold Dual. repeat (split;auto).
Defined.

Definition protoStep1 :=
  send (basic 1);
  x <- receive;
  send (basic 2);
  y <- receive;
  send (basic 3);
  z <- receive;
  ReturnC (t:= Pair Basic (Pair Basic Basic)) (pair x (pair y z)). Check protoStep1.

Definition protoStep2 :=
  a <- receive;
  send (incPayload a);
  b <- receive;
  send (incPayload b);
  c <- receive;
  send (incPayload c);
  EpsC.

Example DualProtoStep : Dual protoStep1 protoStep2.
Proof.
  unfold Dual; repeat(split; reflexivity). split. reflexivity. split. reflexivity. split. reflexivity. split. reflexivity. split. reflexivity. split. reflexivity. split. Defined.

Eval compute in runProto protoStep1 protoStep2 DualProtoStep.
Eval compute in runProtoMultiStep protoStep1 protoStep2 DualProtoStep.


(*
Definition oneStep1 := fst (runProtoOneStep protoStep1 protoStep2 DualProtoStep). Eval compute in oneStep1. 
Definition twoStep1 := snd (runProtoOneStep protoStep1 protoStep2 DualProtoStep). Eval cbv in twoStep1.

Theorem dualInner {t t':protoType} {T T':type} {p1:protoExp T t} {p2:protoExp T' t'} (p:Dual p1 p2) : let (p1', p2') := (runProtoOneStep p1 p2 p) in
                                                                                                      Dual p1' p2'. simpl. destruct p1; destruct p2; try (inversion p).  destruct p. assumption. destruct p. assumption. destruct b. simpl. destruct p. assumption. destruct p. assumption. destruct b. destruct p. assumption. destruct p. assumption. destruct p. simpl. cbv. trivial. Defined.

Definition oneStep2 := fst (runProtoOneStep oneStep1 twoStep1 (dualInner DualProtoStep)). Eval compute in oneStep2.

Definition twoStep2 := snd (runProtoOneStep oneStep1 twoStep1 (dualInner DualProtoStep)). Eval compute in twoStep2.

Eval cbv in nextRtype oneStep1 twoStep1 (dualInner DualProtoStep).
Eval cbv in nextType oneStep1 twoStep1 (dualInner DualProtoStep).

Definition oneStep3 := fst (runProtoOneStep oneStep2 twoStep2 (dualInner (dualInner DualProtoStep))). Eval compute in oneStep3.

Definition twoStep3 := snd (runProtoOneStep oneStep2 twoStep2 (dualInner (dualInner DualProtoStep))). Eval compute in twoStep3.

Eval cbv in nextRtype oneStep2 twoStep2 (dualInner (dualInner DualProtoStep)).
Eval cbv in nextType oneStep2 twoStep2 (dualInner (dualInner (DualProtoStep))).

Definition oneStep4 := fst (runProtoOneStep oneStep3 twoStep3 (dualInner (dualInner (dualInner DualProtoStep)))). Eval cbv in oneStep4.

Definition twoStep4 := snd (runProtoOneStep oneStep3 twoStep3 (dualInner (dualInner (dualInner DualProtoStep)))). Eval compute in twoStep4.

Eval cbv in nextRtype oneStep3 twoStep3 (dualInner (dualInner (dualInner DualProtoStep))).
Eval cbv in nextType oneStep3 twoStep3 (dualInner (dualInner ( dualInner (DualProtoStep)))).

Definition oneStep5 := fst (runProtoOneStep oneStep4 twoStep4 (dualInner (dualInner (dualInner (dualInner (DualProtoStep)))))). Eval cbv in oneStep5.

Definition twoStep5 := snd (runProtoOneStep oneStep4 twoStep4 (dualInner (dualInner (dualInner (dualInner (DualProtoStep)))))). Eval compute in twoStep5.

Eval cbv in nextRtype oneStep4 twoStep4 (dualInner (dualInner (dualInner (dualInner DualProtoStep)))).
Eval cbv in nextType oneStep4 twoStep4 (dualInner (dualInner ( dualInner (dualInner (DualProtoStep))))).
 *)

End protocols.