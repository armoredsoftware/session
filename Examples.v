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

Theorem needham_A_auth : forall k st st',
    multi
      st
      _ _ _
      (Needham_A k bPub)
      (Needham_B bPri aPub)
      (ReturnC bNonce)
      st'
    -> (k = inverse aPub).
Proof.
  intros.
  dep_destruct H. clear H.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x1. clear x1.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x2. clear x2.
  dep_destruct s1. dep_destruct s4. clear s1. clear s4.
  dep_destruct x1. clear x1. clear x. clear x0. cbn in x2.
    unfold decryptM in x2.
    destruct  (decrypt
              (encrypt _ (pair _ _ aNonce (basic bNonceSecret)) aPub)
              k).
      destruct p. assumption.
      inversion x2.
  
    inversion s5.
Qed.


Definition incPayload (m:message Basic) : (message Basic) :=
  match m with
  | basic n => basic (n + 1)
  | _ => bad Basic                 
  end.

Definition proto4 (payload4:(message Basic)) :=
  send payload4;
  x <- receive;
  ReturnC (t:=Basic) x.
Check proto4.

Definition proto5 :=
  x <- receive;
  send (incPayload x);
  ReturnC x.
Check proto5.

Example dual45 : forall x, Dual (proto4 x) proto5.
Proof.
  cbv.
  split.
  reflexivity.
  split.
    reflexivity.
    trivial.
Qed.

Definition property45 : forall x4 x5 st st',
    multi st _ _ _ (proto4 x4) proto5 (ReturnC x5) st' ->
    x5 = incPayload x4.
Proof.
  intros.
  dep_destruct H. clear H.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x1. clear x1.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x2. reflexivity. 
  inversion s1.
Qed.
    
    


Definition hoare_triple{p1t p2t p3t:protoType}{t:type}
           (P:Assertion)
           (p1:protoExp p1t) (p2:protoExp p2t) (p3:protoExp p3t)
           (Q:Assertion) : Prop :=
  forall st st',
     P st ->
     multi st _ _ _ p1 p2 p3 st' ->
     Q (newState st').

(*Definition inPb : forall mt (m:message mt) (pf: mt = Basic) (s:State),
    Prop.
Proof.
  intros. subst. destruct (my_in m s.(basics)). exact True. exact False.
Qed.

Definition inPk : forall mt (m:message mt) (pf: mt = Key) (s:State),
    Prop.
Proof.
  intros. subst. destruct (my_in m s.(keys)). exact True. exact False.
Qed.
*)

Definition inPb (m:message Basic) (s:State) :=
  if (my_inB m s.(basics)) then True
  else False.

Definition inPk (m:message Key) (s:State) :=
  if (my_inK m s.(keys)) then True
  else False.
         

(*Definition inP t (m:message t) (s:State) :=
  match t as t' return (t = t') -> Prop with
  | Basic => fun pf => (inPb t m pf s)
  | Key => fun pf => (inPk t m pf s)
  | _ => fun _ => False                 
  end (eq_refl t). 

Definition notInP t (m:message t) (s:State) :=
  ~ (inP t m s).
 *)

Definition notInPb (m:message Basic) (s:State) :=
  ~ (inPb m s).



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
  inversion s1.
Qed.

Definition p3Payload := (basic 42).
Definition p3 :=
  send encrypt _ p3Payload (public 0);
  EpsC.

Definition p4 :=
  x <- receive;
  ReturnC (t:=Encrypt Basic) x.

Axiom inInfo : forall (m:message Key) (st:State),
    inPk m st ->
    exists kl b kob bob, st = (mkState (m :: kl) b kob bob).

Definition hoare_triple'{p1t p2t p3t:protoType}{t:type} (st:State)
           (p1:protoExp p1t) (p2:protoExp p2t) (p3:protoExp p3t)
           (Q:Assertion) : Prop :=
  forall st',
     multi st _ _ _ p1 p2 p3 st' ->
     Q (newState st').

Definition notLearnedIf : hoare_triple' (t:= Encrypt Basic)
                          emptyState
                          p4 p3 (ReturnC (encrypt _ p3Payload (public 0)))
                          (notInPb p3Payload).
Proof.
  unfold p3. unfold p4. unfold hoare_triple'.
  intros.
  dep_destruct H. clear H. 
  dep_destruct s0. clear s0. dep_destruct s1. clear s1.
  cbn in x1. 
  dep_destruct x1. cbv. intros H. inversion H.
  inversion s2.
Qed.

Definition learnedIf : hoare_triple' (t:= Encrypt Basic)
                       (updateState (key (public 0)) emptyState)
                       p4 p3 (ReturnC (encrypt _ p3Payload (public 0)))
                       (inPb p3Payload).
Proof.
  unfold p3. unfold p4. unfold hoare_triple'.
  intros.
  dep_destruct H. clear H. 
  dep_destruct s0. clear s0. dep_destruct s1. clear s1.
  cbn in x1.
  dep_destruct x1. clear x1. cbv. trivial.
  inversion s2.
Qed.

  
  
  


