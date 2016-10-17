Require Import Crypto.
Require Import Peano_dec.

Lemma infoPri : forall k' n', (k' <> (private n')) ->
                         exists n, (k' = (public n)) \/
                          ((k' = (symmetric n)) \/
                         exists n, (k' = (private n)) /\ (n <> n')).
Proof.
  intros. destruct k'. destruct k. exists 0. right. left. reflexivity.
  exists (S k). right. left. reflexivity. destruct (eq_nat_dec k n'). subst. unfold not in H. assert (private n' = private n'). reflexivity. apply H in H0. inversion H0. exists 0. right. right. exists k. split. reflexivity. assumption. exists k. left. reflexivity.
Defined.

Lemma inverse_info : forall k k',
    k = inverse k' ->
    exists n, k = symmetric n /\  k' = symmetric n \/
    exists n, (k = public n) /\ (k' = private n) \/
                          exists n, (k = private n) /\ (k' = public n).
Proof.
  intros. destruct k; destruct k'; try inversion H. inversion H. exists k0. left.  split; reflexivity. exists 0. right. exists 0. right. exists k0. split; reflexivity. exists 0. right. exists k0. left. split; reflexivity. 
Defined.

(** Various proofs for keys and properties of the inverse operation.  All keys
  must have an inverse.  All keys have a unique inverse.  Equal inverses come
  from equal keys *)

Theorem inverse_injective : forall k1 k2, inverse k1 = inverse k2 -> k1 = k2.
Proof.
  intros.
  destruct k1; destruct k2; simpl in H; try (inversion H); try (reflexivity).
Defined.

Hint Resolve inverse_injective.

Theorem inverse_inverse : forall k, inverse (inverse k) = k.
Proof.
  intros. destruct k; try reflexivity.
Defined.

Hint Resolve inverse_inverse.

Theorem inverse_surjective : forall k, exists k', (inverse k) = k'.
Proof.
  intros. exists (inverse k). auto.
Defined.

Hint Resolve inverse_surjective.

Theorem inverse_bijective : forall k k',
    inverse k = inverse k' -> k = k'
  /\ forall k, exists k'', inverse k = k''.
Proof.
  auto.
Defined.

(** Prove that is_not_decryptable and is_decryptable are inverses.  This is a
  bit sloppy.  Should really only have one or the other, but this theorem
  assures they play together correctly.  Note that it is not installed as
  a Hint.  *)

Theorem decryptable_inverse: forall t:type, forall m:(message t), forall k,
    (is_not_decryptable m k) <-> not (is_decryptable m k).
Proof.
  intros.
  split. destruct m; try (tauto).
  simpl. intros. assumption.
  intros. destruct m; try (reflexivity).
  simpl. tauto.
Defined.


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