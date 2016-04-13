Require Import Crypto.
Require Import SessionClean.
(*Require Import Peano_dec.  *)
Require Import Program.
Require Import CpdtTactics.
(*Require Import Eqdep_dec. *)

Module protocols.
  
Definition protoSimple1 :=
  send (basic 42);
  EpsC.

Definition protoSimple2 :=
  x <- receive;
  ReturnC (t:=Basic) x.

Example dualSimple12 : Dual protoSimple1 protoSimple2. unfold Dual. simpl. split. reflexivity. trivial. 
Defined. Check dualSimple12. Eval compute in dualSimple12.

Example dualSimple21 : Dual protoSimple2 protoSimple1. split; reflexivity.
Defined. Check dualSimple21. Eval compute in dualSimple21.

Example sameProofs1221 : dualSimple12 = dualSimple21. reflexivity. Qed.

Eval compute in runProto protoSimple1 protoSimple2  dualSimple21.
Eval compute in runProto protoSimple2 protoSimple1  dualSimple21.

Definition incPayload (m:message Basic) : (message Basic) :=
  match m with
  | basic n => basic (n + 1)
  | _ => basic 0                 
  end.
  
Definition proto4 :=
  x <- receive;
  send (incPayload x);
  ReturnC x.          Check proto4.

Definition payload5 := (basic 42).
Definition proto5 :=
  send payload5;
  x <- receive;
  ReturnC (t:=Basic) x.   Check proto5.

Example dual45 : Dual proto4 proto5. unfold Dual. simpl. auto. Defined.

Eval compute in runProto proto4 proto5 dual45.
Eval compute in runProto proto5 proto4 dual45.

Hint Constructors runProtoBigStep.
Example bigStep45 : runProtoBigStep _ _ _ _ proto4 proto5 payload5.
Proof.
  unfold proto4. unfold proto5. auto.
Qed.

Definition proto6 (b:bool) :=
  choice b EpsC
         proto5. Check proto6.

Definition proto7 :=
  offer EpsC
        proto4. Check proto7.

Example dual67 : forall b, Dual (proto6 b) proto7. unfold Dual. simpl. auto. Defined.

Eval compute in (runProto (proto6 false) proto7 (dual67 false)).
Eval compute in (runProto (proto6 true) proto7 (dual67 true)).
Eval compute in (runProto  proto7 (proto6 false) (dual67 false)).
Eval compute in (runProto  proto7 (proto6 true) (dual67 true)).

(* Simplest possible encrypt/decrypt protocol pair *)
Definition protoEncrypt1 (theirPub:keyType) :=
  send (encrypt (basic 42) theirPub);
  EpsC.

Definition protoDecrypt1 (myPri:keyType) :=
  x <- receive;
  ReturnC (t:=Basic) (decryptM x myPri).

Example dualEncDec1 : forall k k', Dual (protoEncrypt1 k) (protoDecrypt1 k'). split; reflexivity.
Defined.

Example encDecOneStep : stepe (protoEncrypt1 (public 1)) (protoDecrypt1 (private 1)) (EpsC, (ReturnC (basic 42))).
Proof. constructor.
Qed.

Example encDecMultiStep : multie (protoDecrypt1 (private 1))
                                 (protoEncrypt1 (public 1))
                                 (ReturnC (basic 42)).
Proof.
  unfold protoDecrypt1. unfold protoEncrypt1. apply multi_step with (y:=(ReturnC (basic 42))) (y2:=EpsC). constructor. constructor. exact Basic. exact (Eps Basic).
Qed.


(*First truly interesting crypto protcol *)
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

Eval compute in runProto (protoAuth1 (public 1))
                         (protoAuth2 (private 1))
                         dualProtoAuth12.

Example auth12Multi : multie (protoAuth1 (public 1))
                             (protoAuth2 (private 1))
                             (ReturnC (basic 1)).
Proof.
  unfold protoAuth1. unfold protoAuth2. eapply multi_step. constructor. eapply multi_step. constructor. constructor. exact Basic. exact (Eps Basic).
Qed.

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

Lemma decryptSuccess{t:type} : forall (m : message t) k k', (~ isBad m) ->  decryptM (encrypt m k) k' = m -> k = inverse k'.
Proof.
  intros. destruct m eqn:hh;
  try (destruct (decrypt (encrypt m k) k'); [inversion p; apply is_dec_info in H1; assumption | exfalso; rewrite <- hh in H0; rewrite <- hh in H; apply (notBadContra m k k' H H0 i)]).
Qed.

Example uniqueAuth : forall k k',
    (runProto (protoAuth1 k) (protoAuth2 k') dualProtoAuth12)
    = (basic 1)
    -> (k = inverse k').
Proof.
  intros. dep_destruct H. cbn in x1.
  apply decryptSuccess with (m:=(basic 1)). unfold not. intros. inversion H0.
  assumption.
Qed.

Example uniqueAuth' : forall k k',
    (runProtoBigStep _ _ _ _ (protoAuth1 k)
                     (protoAuth2 k')
                     (basic 1) )
    -> (k = inverse k').
Proof.
  intros. dep_destruct H. dep_destruct x. dep_destruct x0. apply decryptSuccess with (m:=(basic 1)). unfold not. intros. inversion H0. assumption.
Qed.

Example goodAuth : forall k',
    (runProto (protoAuth1 (public 2)) (protoAuth2 k') dualProtoAuth12)
        = basic 1 ->
    k' = (private 2).
Proof.
  intros. (*destruct (eq_key_dec k' (private 2)).
  assumption.
  simpl in H. Abort. *)
  dep_destruct H.
  destruct (eq_key_dec k' (private 2)).
  assumption.
  cbn in x1. cbn in x0. dep_destruct x0. symmetry. assert ((public 2) = inverse k'). apply decryptSuccess with (m:=(basic 1)). unfold not. intros. inversion H0. assumption. apply inverse_info in H0. destruct H0. destruct H0. destruct H0. inversion H0. destruct H0. destruct H0. destruct H0. inversion H0. subst. reflexivity. destruct H0. destruct H0. inversion H0.
Qed.

Example goodAuth' : forall k',
    (runProtoBigStep _ _ _ _  (protoAuth1 (public 2))
                     (protoAuth2 k') (basic 1)) ->
    k' = (private 2).
Proof.
  intros.
  dep_destruct H. dep_destruct x. dep_destruct x0.
  Abort.






  
  







End protocols.


