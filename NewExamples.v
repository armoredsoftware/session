Require Import Crypto.
Require Import ProtoRep.
Require Import ProtoSemantics.
Require Import CpdtTactics.
Require Import Arith.

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

Theorem dual1AB : forall (x:message Basic), Dual (proto1A x) proto1B.
Proof.
  cbv.
  split.
  reflexivity.
  split.
    reflexivity.
    trivial.
Qed.

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


(* Needham Schroeder *)

Definition Nonce := Basic.
Definition Id := Basic.
Definition null := basic 0.

Definition resT := Pair (Pair Nonce Nonce) Id.
Definition res : message resT :=
  pair _ _ (pair _ _ (bad Nonce) (bad Nonce)) (bad Id).
Print res.
Definition ares : message resT :=
  pair _ _ (pair _ _ (basic 0) (bad Nonce)) (bad Id).
Print ares.
Definition bres : message resT :=
  pair _ _ (pair _ _ (bad Nonce) (basic 0)) (bad Id).
Print bres.
Definition idres : message resT :=
  pair _ _ (pair _ _ (bad Nonce) (bad Nonce)) (basic 0).
Print idres.

Definition getAnonce (rIn:message resT) : message Nonce :=
  pairFst (pairFst rIn).
Eval compute in getAnonce ares.
Eval compute in getAnonce bres.
Eval compute in getAnonce idres.

Definition getBnonce (rIn:message resT) : message Nonce :=
  pairSnd (pairFst rIn).
Eval compute in getBnonce ares.
Eval compute in getBnonce bres.
Eval compute in getBnonce idres.

Definition getId (rIn:message resT) : message Id :=
  pairSnd rIn.

Eval compute in getId ares.
Eval compute in getId bres.
Eval compute in getId idres.

Definition updateA (aNonce:message Nonce) (rIn:message resT) : message resT :=
  pair _ _ (pair _ _ aNonce (getBnonce rIn)) (getId rIn).

Eval compute in updateA (basic 0) res.

Definition updateB (bNonce:message Nonce) (rIn:message resT) : message resT :=
  pair _ _ (pair _ _ (getAnonce rIn) bNonce) (getId rIn).

Eval compute in updateB (basic 0) res.

Definition updateId (id:message Id) (rIn:message resT) : message resT :=
  pair _ _ (pair _ _ (getAnonce rIn) (getBnonce rIn)) id.

Eval compute in updateId (basic 0) res.

Definition initT := Pair Nonce Id.
Definition init : message initT
  := pair _ _ (bad Nonce) (bad Id).

Definition getPubkey (m:message Id) :=
  match m with
  | basic n => public n
  | _ => public 0
  end.

Definition bLast (id:message Id) (aRes:message resT) :=
  x <- receive;
  ReturnC (pair Nonce _ x id).

Definition iLast :=
  x <- receive;
  send x;
  ReturnC (t:=Encrypt Nonce) x.

Definition aLast (id:message Id) (aRes:message resT) :=
  x <- receive;
  let na := pairFst (t1:=Nonce) x in
  let nb := pairSnd x in
      send (encrypt Nonce nb (getPubkey id));
    ReturnC null.

Definition extractPayload (m:message Basic) : nat :=
  match m with
  | basic n => n
  | _ => 0
  end.

Definition aId : (message Id) := (basic 0).
Definition bId : (message Id) := (basic 1).
Definition iId : (message Id) := (basic 2).

Definition nslA (myPri:keyType) (theirId:message Id) :=
  let myNonce := basic 0 in
  let myId        : (message Id)    := aId  in
  let theirPubkey : (keyType)       := (getPubkey theirId) in 
  let s1          : (message (Encrypt (Pair Nonce Id)))
                                    := encrypt _
                                       (pair _ _ myNonce myId) theirPubkey in
  send s1;
  r1 <- receive;
  let decTry      : (message (Pair (Pair Nonce Nonce) Id))
                                    := decryptM r1 myPri in
  let myNonce'    : (message  Nonce)
                                    := pairFst (pairFst decTry) in
  let theirNonce  : (message Nonce) := pairSnd (pairFst decTry) in
  let newId       : (message Id)    := pairSnd decTry in
  let newPubkey   : (keyType)       := (getPubkey newId) in
  let s2          : (message (Encrypt Nonce))
                                    := encrypt _ theirNonce newPubkey in
  send s2;
  ReturnC (pair _ _ myNonce' theirNonce).
Check nslA.

Definition nslB (myPri:keyType) (intruder:bool) :=
  r1 <- receive;
  let myId        : (message Id)    := bId  in
  let myNonce     : (message Nonce) := (basic 1) in
  let newR1       : (message (Encrypt(Pair Nonce Id)))
                    := if (intruder) then
                         let decI := decryptM r1 (private 2) in
                           encrypt _ decI (getPubkey bId)
                       else
                         r1 in
  let decB := decryptM newR1 myPri in
  let they := extractPayload (pairSnd decB) in
  let theirNonce := pairFst decB in
  let theirId := pairSnd decB in
  let theirPub := (public they) in
  let s1 := encrypt _
             (pair _ _ (pair _ _ theirNonce myNonce) myId) (theirPub) in
  send s1;
  r2 <- receive;
  let decB2 := if (intruder) then
                 decryptM r2 (private 2)
               else decryptM r2 myPri in
  let myNonce' := decB2 in
  let ab := pair Nonce Nonce theirNonce myNonce' in
  ReturnC (pair _ _ ab theirId).
Check nslB.

Example dualab : forall x y z b, Dual (nslA x y) (nslB z b).
Proof.
  intros; unfold nslA; unfold nslB; cbn;
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  trivial.
Defined.

Definition expectedA :=
  pair _ _ (basic 0) (basic 1).

Definition expectedB :=
  pair _ _
       (pair _ _ (basic 0) (basic 1))
       aId.


Example aResult :
  let intruder := false in
  let theirId := if(intruder)
                 then iId
                 else bId in
  let aPri := (private 0) in
  let bPri := (private 1) in
  
  forall st m, 
    multi st _ _ _ (nslA aPri theirId) (nslB bPri intruder) (ReturnC m) st ->
    (m = expectedA).
Proof.
  intros.
  unfold nslA. unfold nslB.
  dep_destruct H. clear H.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x1. clear x1. dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x2. clear x2. dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x1. clear x1. reflexivity.
  inversion s1.
Qed.

Example bResult :
  let intruder := false in
  let theirId := if(intruder)
                 then iId
                 else bId in
  let aPri := (private 0) in
  let bPri := (private 1) in
  
  forall st m, 
    multi st _ _ _ (nslB bPri intruder) (nslA aPri theirId) (ReturnC m) st ->
    (m = expectedB).
Proof.
  intros.
  unfold nslA. unfold nslB.
  dep_destruct H. clear H.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x1. clear x1. dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x2. clear x2. dep_destruct s1. dep_destruct s3. clear s1. clear s3.
  dep_destruct x1. clear x1. cbv. reflexivity.
  inversion s3.
Qed.

Definition nsA (myPri:keyType) (theirId:message Id) :=
  let myNonce := basic 0 in
  let myId        : (message Id)    := aId  in
  let theirPubkey : (keyType)       := (getPubkey theirId) in 
  let s1          : (message (Encrypt (Pair Nonce Id)))
                                    := encrypt _
                                       (pair _ _ myNonce myId) theirPubkey in
  send s1;
  r1 <- receive;
  let decTry      : (message (Pair Nonce Nonce))
                                    := decryptM r1 myPri in
  let myNonce'    : (message  Nonce)
                                    := (pairFst decTry) in
  let theirNonce  : (message Nonce) := (pairSnd decTry) in
  (*let newId       : (message Id)    := pairSnd decTry in*)
  let newPubkey   : (keyType)       := (getPubkey theirId(*newId*)) in
  let s2          : (message (Encrypt Nonce))
                                    := encrypt _ theirNonce newPubkey in
  send s2;
  ReturnC (pair _ _ myNonce' theirNonce).
Check nsA.

Definition nsB (myPri:keyType) (intruder:bool) :=
  r1 <- receive;
  (*let myId        : (message Id)    := bId  in*)
  let myNonce     : (message Nonce) := (basic 1) in
  let newR1       : (message (Encrypt(Pair Nonce Id)))
                    := if (intruder) then
                         let decI := decryptM r1 (private 2) in
                           encrypt _ decI (getPubkey bId)
                       else
                         r1 in
  let decB := decryptM newR1 myPri in
  let they := extractPayload (pairSnd decB) in
  let theirNonce := pairFst decB in
  let theirId := pairSnd decB in
  let theirPub := (public they) in
  let s1 := encrypt _
             (pair _ _ theirNonce myNonce) (theirPub) in
  send s1;
  r2 <- receive;
  let decB2 := if (intruder) then
                 decryptM r2 (private 2)
               else decryptM r2 myPri in
  let myNonce' := decB2 in
  let ab := pair Nonce Nonce theirNonce myNonce' in
  ReturnC (pair _ _ ab theirId).
Check nsB.

Example dualab' : forall x y z b, Dual (nsA x y) (nsB z b).
Proof.
  intros; unfold aa; unfold bb; cbn;
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  trivial.
Defined.


Example bResult' :
  let intruder := true in
  let theirId := if(intruder)
                 then iId
                 else bId in
  let aPri := (private 0) in
  let bPri := (private 1) in
  
  forall st m, 
    multi st _ _ _ (nsB bPri intruder) (nsA aPri theirId) (ReturnC m) st ->
    (m = expectedB).
Proof.
  intros.
  unfold aa. unfold bb.
  dep_destruct H. clear H.
  dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x1. clear x1. dep_destruct s0. dep_destruct s1. clear s0. clear s1.
  dep_destruct x2. clear x2. dep_destruct s1. dep_destruct s3. clear s1. clear s3.
  dep_destruct x1. clear x1. cbv. simpl. reflexivity.
  inversion s3.
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

Definition oneEnc := (encrypt _ (basic 0) (public 0)).
Definition twoEnc := (encrypt _ oneEnc (public 1)).

Eval compute in oneEnc.
Eval compute in twoEnc.

Definition oneDec := decryptM twoEnc (private 2).
Eval compute in oneDec.

Definition twoDec := decryptM oneDec (private 0).
Eval compute in twoDec.

Eval compute in decryptM (bad (Encrypt Basic)) (public 0).

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

(*

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
*)


