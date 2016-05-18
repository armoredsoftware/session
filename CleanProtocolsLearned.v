Require Import Crypto.
Require Import SessionLearned.
Require Import HeteroLists.
Require Import CpdtTactics.



(* Simplest possible encrypt/decrypt protocol pair *)
Definition protoEncrypt1 (theirPub:keyType) :=
  send (encrypt _ (basic 42) theirPub);
  EpsC.

Definition protoDecrypt1 (myPri:keyType) :=
  x <- receive;
  ReturnC (t:=Basic) (decryptM x myPri).

Example dualEncDec1 : forall k k', Dual (protoEncrypt1 k) (protoDecrypt1 k').
split; reflexivity.
Defined.

Eval compute in (typesLearned (protoDecrypt1 (private 1)) (protoEncrypt1 (public 1)) (dualEncDec1 (public 1) (private 1))).

Example result1 : multie (protoDecrypt1 (private 1)) (protoEncrypt1 (public 1)) (ReturnC (basic 42)).
Proof.
  unfold protoDecrypt1. unfold protoEncrypt1.
  eapply multi_step. constructor. constructor.
  cbv. constructor.
Qed.

Definition isBad {t:type} (m:message t) : Prop :=
  match m with
  | bad _ => True
  | _ => False
  end.

(*Inductive isBad' {t:type} : (message t) -> Prop :=
| aa : isBad' (bad t). *)

Lemma is_dec_info{t:type} : forall (m:message t) k k', (is_decryptable (encrypt _ m k) k') -> k = inverse k'.
Proof.
  intros.
  inversion H. assert ((inverse (inverse k)) = k). apply inverse_inverse. symmetry in H1. assumption. Qed.

Lemma notBadContra {t:type} : forall (m:message t) k k', (~isBad m) -> decryptM (encrypt _ m k) k' = m -> is_not_decryptable (encrypt _ m k) k' -> False.
Proof.
  intros. unfold decryptM in H0. destruct (decrypt (encrypt _ m k) k').
    inversion p. inversion H2. simpl in H1. contradiction. 
    unfold not in H. apply H. subst. constructor.
Qed.

Lemma decryptSuccess{t:type} : forall (m : message t) k k', (~ isBad m) ->  decryptM (encrypt _ m k) k' = m -> k = inverse k'.
Proof.
  intros. destruct m eqn:hh;
  try (destruct (decrypt (encrypt _ m k) k'); [inversion p; apply is_dec_info in H1; assumption | exfalso; rewrite <- hh in H0; rewrite <- hh in H; apply (notBadContra m k k' H H0 i)]).
Qed.

Example result1Gen : forall k k',
    multie (protoDecrypt1 k) (protoEncrypt1 k') (ReturnC (basic 42)) ->
    (k' = inverse k).
Proof.
  intros.
  assert (~ isBad (basic 42)). unfold not. intros. inversion H0.
  dep_destruct H. dep_destruct s0. dep_destruct s1. dep_destruct x1.
  eapply decryptSuccess. apply H0. assumption.
  inversion s2.
Qed.

Example badResult1 : forall k k',
    (k <> inverse k') ->
    multie (protoDecrypt1 k) (protoEncrypt1 k') (ReturnC (bad Basic)).
Proof.
  intros.
  eapply multi_step. constructor. constructor.
  assert ((decryptM (encrypt Basic (basic 42) k') k) = (bad Basic)).
  unfold decryptM. 
  dep_destruct (decrypt (encrypt Basic (basic 42) k') k).
  destruct p. contradiction. reflexivity.
  rewrite H0. apply multi_refl.
Qed.

Definition aNonceSecret := 11.
Definition bNonceSecret := 22.
Definition aNonce := (basic aNonceSecret).
Definition bNonce := (basic bNonceSecret).

Definition aPub := (public 1).
Definition bPub := (public 2).
Definition aPubBad := (public 3).
Definition bPubBad := (public 4).
Definition aPri := (private 1).
Definition bPri := (private 2).
Definition aPriBad := (private 5).
Definition bPriBad := (private 6).

Definition Needham_A (myPri theirPub:keyType) :=
  send (encrypt _ aNonce theirPub);
  x <- receive; (* x : Encrypt (Pair Basic Basic) *) 
  let y := decryptM x myPri in (* y : Pair Basic Basic *)
  (*let y' := (pairFst (t1:=Basic) (t2:=Basic) y) in *)
  let y'' := (pairSnd (t1:=Basic) (t2:=Basic) y) in 
  send (encrypt _ y'' theirPub);
  ReturnC (y''). Check Needham_A.

Definition Needham_B (myPri theirPub:keyType) :=
  ReceiveC (fun x: message (Encrypt Basic) => ( 
  (*x <- receive; (* x : Encrypt Basic *) *)
  let y : (message Basic) := decryptM x myPri in (* y : Basic *)
  send (encrypt (Pair Basic Basic) (pair _ _ y bNonce) theirPub);
  ReceiveC (fun z : message (Encrypt Basic) => ( 
  (*z <- receive; (* z : Encrypt Basic *) *)
  let z' := decryptM z myPri in   (* z' : Basic *)
  ReturnC y)))). Check Needham_B.

Example DualNeedham {a b c d:keyType} : Dual (Needham_A a b) (Needham_B c d).
Proof. unfold Dual; simpl. repeat( split;trivial). Defined.

Eval compute in (typesLearned (Needham_B bPri aPub) (Needham_A aPri bPub)  DualNeedham).

Theorem needham_A_auth : forall k,
    multie (Needham_A k bPub) (Needham_B bPri aPub) (ReturnC bNonce)
    -> (k = inverse aPub).
Proof.
  intros.
  dep_destruct H. clear H.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x1. clear x1.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x2. clear x2.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x1. clear x1. clear x. clear x0. cbn in x2.
  unfold decryptM in x2.
  destruct (decrypt
           (encrypt (Pair Basic Basic)
                    (pair Basic Basic aNonce (basic bNonceSecret)) aPub) k). dep_destruct p. assumption. inversion x2.
 
  inversion s0.
Qed.

Theorem needham_B_auth : forall k,
    multie (Needham_B k aPub) (Needham_A aPri bPub) (ReturnC aNonce)
    -> (k = inverse bPub).
Proof.
    intros.
  dep_destruct H. clear H.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x1. clear x1.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x2. clear x2.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x1. clear x1. clear x. clear x0. cbn in x2.
  unfold decryptM in x2.
  destruct (decrypt (encrypt Basic (basic aNonceSecret) bPub) k).
  dep_destruct p. assumption. inversion x2.
  inversion s0.
Qed.
















(*Definition Needham_A (myPri theirPub:keyType) :=
  send (encrypt _ aNonce theirPub);
  x <- receive; (* x : Encrypt (Pair Basic Basic) *) 
  let y := decryptM x myPri in (* y : Pair Basic Basic *)
  let y' := (pairFst (t1:=Basic) (t2:=Basic) y) in
  let y'' := (pairSnd y) in 
  send (encrypt _ y'' theirPub);
  ReturnC (pair _ _ y' y''). Check Needham_A.

Definition Needham_B (myPri theirPub:keyType) :=
  x <- receive; (* x : Encrypt Basic *)
  let y := decryptM x myPri in (* y : Basic *)
  send (encrypt _ (pair _ _ y bNonce) theirPub);
  z <- receive; (* z : Encrypt Basic *)
  let z' := decryptM z myPri in    (* z' : Basic *)
  ReturnC (t:= Pair Basic (Basic)) (pair _ _ y z'). Check Needham_B.*)
