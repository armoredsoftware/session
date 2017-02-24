Require Import Crypto.
Require Import ProtoRep.
Require Import ProtoStateSemantics.
Require Import CpdtTactics.

Definition isBad {t:type} (m:message t) : Prop :=
  match m with
  | bad _ => True
  | _ => False
  end.

(*Inductive isBad' {t:type} : (message t) -> Prop :=
| aa : isBad' (bad t). *)

(*
Lemma is_dec_info{t:type} : forall (m:message t) k k', (is_decryptable (encrypt _ m k) k') -> k = inverse k'.
Proof.
  intros.
  inversion H. assert ((inverse (inverse k)) = k). apply inverse_inverse. symmetry in H1. assumption. Qed.
*)

Lemma notBadContra {t:type} : forall (m:message t) k k', (~isBad m) -> decryptM (encrypt _ m k) k' = m -> is_not_decryptable (encrypt _ m k) k' -> False.
Proof.
  intros. unfold decryptM in H0. destruct (decrypt (encrypt _ m k) k').
    inversion p. inversion H2. simpl in H1. contradiction. 
    unfold not in H. apply H. subst. constructor.
Qed.
(*
Lemma decryptSuccess{t:type} : forall (m : message t) k k', (~ isBad m) ->  decryptM (encrypt _ m k) k' = m -> k = inverse k'.
Proof.
  intros. destruct m eqn:hh;
  try (destruct (decrypt (encrypt _ m k) k'); [inversion p; apply is_dec_info in H1; assumption | exfalso; rewrite <- hh in H0; rewrite <- hh in H; apply (notBadContra m k k' H H0 i)]).
Qed.
*)


(* Simple increment example *)

Definition incPayload (m:message Basic) : (message Basic) :=
  match m with
  | basic n => basic (n + 1)
  | _ => bad Basic                 
  end.

Definition proto1A (m:(message Basic)) :=
  send m;
  x <- receive;
  ReturnC (t:=Basic) x.
Check proto1A.

Definition proto1B :=
  x <- receive;
  send (incPayload x);
  ReturnC x.
Check proto1B.
(*
Theorem dual1AB : forall (x:message Basic), Dual (proto1A x) proto1B.
Proof.
  cbv.
  split.
  reflexivity.
  split.
    reflexivity.
    trivial.
Qed.*)

Theorem incPropertyAB : forall x x' st st',
    multi st _ _ _ (proto1A x) proto1B (ReturnC x') st' ->
    x' = incPayload x.
Proof.
  intros x x' st st' multiProof.
  dep_destruct multiProof. clear multiProof.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x2. clear x2.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x3. reflexivity.
  inversion s1.
Qed.

(* TPM and CA *)

Definition pubEK : keyType := (public 0).

Definition tpmHost (m:(message Basic)) (priEK:keyType) :=
  send m;
  x <- receive;
  let v := decryptM x priEK in
  send v;
  ReturnC (t:=Basic) v.
Check tpmHost.

Definition certAuth :=
  x <- receive;
  send (encrypt (Basic) x pubEK);
  v <- receive;
  ReturnC (t:=Basic) v.
Check certAuth.

Example dualtpmcert : forall m k, Dual (tpmHost m k) certAuth.
Proof.
  intros.
  split. simpl. split. reflexivity. split. reflexivity. split; reflexivity.
Qed.

Theorem tpm_auth : forall (k:keyType) (x:message Basic) st st', 
    multi
      st
      _ _ _
      (certAuth)
      (tpmHost x k)
      (ReturnC x)
      st'
    -> (k = inverse pubEK).
Proof.
  intros k x st st' multiProof.
  dep_destruct multiProof. clear multiProof.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x2. clear x2.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x3. clear x3.
  (*dep_destruct x2. clear x2. clear x. cbn in x0.
  unfold decryptM in x3.*)
  destruct  (decrypt
            (encrypt _ x0 pubEK) k) as [p | _].
  destruct p as (m , i).
    dep_destruct i. reflexivity.
    inversion x2
  inversion s4.
Qed.



(* Needham Schroeder *)


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
  let y : (message (Pair Basic Basic)):= decryptM x myPri in (* y : Pair Basic Basic *)
  let y' := (pairFst y) in
  let y'' := (pairSnd y) in 
  send (encrypt _ y'' theirPub);
  ReturnC (pair _ _ y' y''). Check Needham_A.

Definition Needham_B (myPri theirPub:keyType) :=
  ReceiveC (fun x: message (Encrypt Basic) => ( 
  (*x <- receive; (* x : Encrypt Basic *) *)
  let y : (message Basic) := decryptM x myPri in (* y : Basic *)
  send (encrypt (Pair Basic Basic) (pair _ _ y bNonce) theirPub);
  ReceiveC (fun z : message (Encrypt Basic) => ( 
  (*z <- receive; (* z : Encrypt Basic *) *)
                let z' := decryptM z myPri in   (* z' : Basic *)
  (*ReturnC y)))).  Check Needham_B. *)
  ReturnC (pair _ _ y z'))))). Check Needham_B.

Example dualNeedham : forall ka ka' kb kb',
    Dual (Needham_A ka kb') (Needham_B kb ka').
Proof.
  intros.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  reflexivity.
Qed.

Theorem needham_A_auth : forall (k:keyType) (x:message Basic) st st', 
    multi
      st
      _ _ _
      (Needham_A k bPub)
      (Needham_B bPri aPub)
      (ReturnC (pair _ _ x bNonce))
      st'
    -> (k = inverse aPub).
Proof.
  intros k x st st' multiProof.
  dep_destruct multiProof. clear multiProof.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x2. clear x2.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x3. clear x3.
  dep_destruct s1. dep_destruct s4. clear s1. clear s4.
  dep_destruct x2. clear x2. clear x. cbn in x0.
  unfold decryptM in x0.
  destruct  (decrypt
            (encrypt _ (pair _ _ aNonce (basic bNonceSecret)) aPub)
            k) as [p | _].
  destruct p as (m , i).
    dep_destruct i. reflexivity. simpl in x0.
    inversion x0.
  inversion s4.
Qed.


Definition normalizeState : State -> State := fun _ => emptyState.

(* Future Work *)
Definition hoare_triple{p1t p2t p3t:protoType}{t:type}
           (P:Assertion)
           (p1:protoExp p1t) (p2:protoExp p2t) (p3:protoExp p3t)
           (Q:Assertion) : Prop :=
  forall st st',
     P st ->
     multi st _ _ _ p1 p2 p3 st' ->
     Q (normalizeState st').

Definition notInPb : (message Basic) -> State -> Prop := fun _ _ => True.
Definition inPb : (message Basic) -> State -> Prop := fun _ _ => True.


Definition learnedB {p1t p2t p3t:protoType}
           (m:message Basic)
           (p1:protoExp p1t) (p2:protoExp p2t) (p3:protoExp p3t) : Prop :=
  hoare_triple (t:=Basic) (notInPb m) p1 p2 p3 (inPb m).
 

Definition p1 :=
  send (basic 33);
  EpsC.

Definition p2 :=
  x <- receive;
  ReturnC (t:=Basic) x.

Definition learnedProof : learnedB (basic 33) p2 p1 (ReturnC (basic 33)).
Proof.
  intros.
  unfold p1. unfold p2. unfold learnedB. unfold hoare_triple.
  intros.
  dep_destruct H0. clear H0.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x1. clear x1. simpl. cbn. trivial.
  Abort.








(* Simplest possible encrypt/decrypt protocol pair *)
Definition protoEncrypt1 (theirPub:keyType) :=
  send (encrypt _ (basic 42) theirPub);
  EpsC.

Definition protoDecrypt1 (myPri:keyType) :=
  x <- receive;
  ReturnC (t:=Basic) (decryptM x myPri).

Example result1 : 
    multi
      emptyState
      _ _ _
      (protoDecrypt1 (private 1))
      (protoEncrypt1 (public 1))
      (ReturnC (basic 42))
      (updateState (encrypt Basic (basic 42) (public 1)) emptyState).
Proof.
  eapply multi_step with (st2:=emptyState).
  constructor.
  constructor.
  apply multi_refl.
Qed.

Example auth1 : forall k k',
    multi
      emptyState
      _ _ _
      (protoDecrypt1 k')
      (protoEncrypt1 k)
      (ReturnC (basic 42))
      (updateState (encrypt Basic (basic 42) (public 1)) emptyState)
      -> (k = inverse k').
Proof.
  intros.
  dep_destruct H. dep_destruct s0. dep_destruct x1.
  apply decryptSuccess with (m:= (basic 42)).
  unfold not. intros. inversion H0.
  assumption.
  dep_destruct s2.
Qed.

Example auth1' : forall k k' st',
    multi
      emptyState
      _ _ _
      (protoDecrypt1 k')
      (protoEncrypt1 k)
      (ReturnC (basic 42))
      st'
      -> (k = inverse k').
Proof.
  intros.
  dep_destruct H. clear H. dep_destruct s0. clear s0. dep_destruct x1.
  apply decryptSuccess with (m:= (basic 42)).
  unfold not. intros. inversion H.
  assumption.
  inversion s2.
Qed.
  


