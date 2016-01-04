Require Export SfLib.
(* Require Import Maybe.*)
Require Export Crypto.

Module try1.

Inductive ProtoA : Type :=
| SendA : forall (A:Type), ProtoA -> ProtoA
| RecA : forall (A:Type), ProtoA -> ProtoA
| ChoiceA : ProtoA -> ProtoA -> ProtoA
| OfferA : ProtoA -> ProtoA -> ProtoA
| Eps : ProtoA.

Notation "x :!: y" := (SendA x y)
                          (at level 50, left associativity).

Notation "x :?: y" := (RecA x y)
                        (at level 50, left associativity).

Notation "x :+: y" := (ChoiceA x y)
                        (at level 50, left associativity).

Notation "x :&: y" := (OfferA x y)
                          (at level 50, left associativity).

Check (nat :!: (bool :?: Eps)).

Inductive Dual : ProtoA -> ProtoA -> Prop :=
| senRec : forall (A:Type) (R S : ProtoA),
    Dual R S -> Dual (A :!: R) (A :?: S)
| recSen : forall (A:Type) (R S : ProtoA),
    Dual R S -> Dual (A :?: R) (A :!: S)
| choiceOffer : forall (R S T U: ProtoA),
    Dual R S -> Dual T U -> Dual (R :+: T) (S :&: U)
| offerChoice : forall (R S T U: ProtoA),
    Dual R S -> Dual T U -> Dual (R :&: T) (S :+: U)
| epsDual : Dual Eps Eps.

Example dual1 : Dual (nat :!: Eps) (nat :?: Eps).
Proof.
  apply senRec.
  apply epsDual.
Qed.

Hint Constructors Dual.

Example dual2 : Dual (nat :!: (bool :?: Eps)) (nat :?: (bool :!: Eps)).
Proof. auto. Qed.

Example dual3 : Dual ((nat :!: (bool :?: Eps)) :+: (bool :!: (nat :?: Eps)))
                     ((nat :?: (bool :!: Eps)) :&: (bool :?: (nat :!: Eps))).
Proof. auto. Qed.

(* How can we make the type of send more expressive?  It should be something like (a :!: r) -> r *)
Inductive Session (P P':ProtoA) (T:Type) :=
| send {A:Type} :  A -> Session P P' T.


Check (Session (nat :!: Eps) (nat :?: Eps) nat).

End try1.


Module try2.

Inductive sendT (A:Type) (R:Type) :=.
Inductive recieveT (A:Type) (R:Type) :=.
Inductive choiceT (R:Type) (S:Type) :=.
Inductive offerT (R:Type) (S:Type) :=.

Notation "x :!: y" := (sendT x y)
                          (at level 50, left associativity).

Notation "x :?: y" := (recieveT x y)
                        (at level 50, left associativity).

Notation "x :+: y" := (choiceT x y)
                        (at level 50, left associativity).

Notation "x :&: y" := (offerT x y)
                        (at level 50, left associativity).

(*Definition send {A:Type} {R:Type} : (A :!: R) -> A -> R := *)

End try2.

Module try3.

(* Protocol expressions *)
Inductive PExp : Set :=
| Nat  : nat -> PExp
| Plus : PExp -> PExp -> PExp
| Send : PExp -> PExp -> PExp
| Rec :  PExp -> PExp -> PExp
| Eps : PExp.
(*| Bool : bool -> PExp
| And : PExp -> PExp -> PExp *)

(* Protocol Types *)
Inductive PType : Type :=
| TNat
| TEps
| TSend : PType -> PType -> PType
| TRec :  PType -> PType -> PType.

Inductive hasType : PExp -> PType -> Prop :=
| HtNat : forall n, hasType (Nat n) TNat
| HtEps : hasType Eps TEps
| HtPlus : forall e1 e2, hasType e1 TNat ->
                    hasType e2 TNat ->
                    hasType (Plus e1 e2 ) TNat
| HtSend : forall e1 e2 t1 t2, hasType e1 t1 ->
                       hasType e2 t2 ->
                       hasType (Send e1 e2) (TSend t1 t2)
| HtRec : forall e1 e2 t1 t2,  hasType e1 TNat ->
                       hasType e2 t1 ->
                       hasType (Rec e1 e2) (TRec t1 t2).



Notation "x :!: y" := (Send x y)
                          (at level 50, left associativity).

Notation "x :?: y" := (Rec x y)
                        (at level 50, left associativity).

Notation "x ! y" := (TSend x y)
                          (at level 50, left associativity).

Notation "x ? y" := (TRec x y)
                      (at level 50, left associativity).

Notation "x :T: y" := (hasType x y)
                       (at level 50, left associativity).

Check ((Nat 4) :!: Eps).

Definition Session (a:PType) (b:PType) := (a, b).

(*Definition send {A:Type} {a r : PType} : A -> (Session (a ! r) (r)) -> nat := 3. *)

Hint Constructors hasType.

Example sendWellTyped1 : hasType ((Nat 4) :!: Eps) (TNat ! TEps).
Proof. auto. Qed.

Example sendWellTyped1' : ((Nat 4) :!: Eps) :T: (TNat ! TEps).
Proof. auto. Qed.

Example sendWellTyped2 : ((Plus (Nat 3) (Nat 1)) :!: Eps) :T: (TNat ! TEps).
Proof. auto. Qed.

Example sendWellTypedConcerning : ((Nat 4) :!: (Nat 4)) :T: (TNat ! TNat).
Proof. eauto. Qed.


Inductive Dual : PType -> PType -> Prop :=
| senRec : forall a r s,
    Dual r s -> Dual (a ! r) (a ? s)
| recSen : forall a r s,
    Dual r s -> Dual (a ? r) (a ! s)
(*| choiceOffer : forall r s t u,
    Dual r s -> Dual t u -> Dual (r :+: t) (s :&: u)
| offerChoice : forall r s t u
    Dual r s -> Dual t u -> Dual (r :&: t) (s :+: u) *)
| natDual : Dual TNat TNat
| epsDual : Dual TEps TEps.

Hint Constructors Dual.


Example simpleDual : Dual (TNat ! TEps) (TNat ? TEps).
Proof. eauto. Qed.

Definition sendNat (n:nat) := (Nat n :!: Eps).
Check sendNat.

Example sendNatType : forall n, hasType (sendNat n) (TNat ! TEps).
Proof. unfold sendNat. eauto. Qed.

Example existsDual' : forall p1 t1, hasType p1 t1 -> exists p2 t2, and (hasType p2 t2) (Dual t1 t2).
Proof.
  eauto. Abort.

Example existsDual' : forall p1 t1, hasType p1 t1 -> exists p2 t2, and (hasType p2 t2) (Dual t1 t2).
Proof.
  intros. inversion H. subst. exists (Nat 1). exists TNat. split; eauto.
  Abort. (*exists (Eps). exists TEps. split; eauto. subst.
  exists (Nat 1). exists TNat. split; eauto.
  exists (e1 :?: e2). exists (t0 ? t2). split. apply HtRec. destruct t0. apply H0.
Qed. *)

Example dualUnique : forall t1 t2 t3, and (Dual t1 t2) (Dual t1 t3) -> t2 = t3.
Proof. eauto. Abort.



End try3.

Module try4.

Definition SendT (A:Type) (R:Type) :=
  fun (x:A) => R.

    
Inductive EpsT := epsC.


Check SendT nat EpsT.

(*Inductive ProtoT (R:Type) : Type :=
| sendC {A:Type} : SendT A (ProtoT R) -> ProtoT R
| receiveC {A:Type} : RecT A (ProtoT R) -> ProtoT R.

Check sendC EpsT (

Check sendC nat (EpsT).

Definition isSend : Prop 

Definition send {A R :Type} (a:A) (p: (SendT A R)) : R := match p with end.

Check send 3 _. *)


End try4.

Module try5.

Inductive SendT (A:Type) (R:Type) : Type := sendC : A -> R -> SendT A R.
Inductive RecT  (A:Type) (R:Type) : Type := recC : R -> RecT A R.
Inductive EpsT := epsC.

Notation "x :!: y" := (SendT x y)
                        (at level 50, left associativity).

Notation "x :?: y" := (RecT x y)
                        (at level 50, left associativity).

Eval compute in sendC nat EpsT.

Definition send {A R :Type} (s : A :!: R) : R :=
  match s with
    sendC _ r => r
  end.

(* Should we account for the received value of type A here?  With the current implementation, it simply disappears.  Maybe it should return a pair:  (A,R) *)
Definition receive {A R :Type} (s : A :?: R) : R :=
  match s with
    recC r => r
  end.


Definition proto1 := (sendC nat EpsT).
Check proto1.

Definition proto1Applied := proto1 3 epsC.
Print proto1Applied.

Definition afterSend := send proto1Applied.
Eval compute in afterSend.

Definition proto2 := (recC nat EpsT).
Check proto2.

Definition proto2Applied := proto2 epsC.
Check proto2Applied.

(* Where does the received value go after this application? *)
Definition afterReceive := receive proto2Applied.
Eval compute in afterReceive.

Definition proto3 := sendC nat (RecT nat EpsT).
Eval compute in proto3.

Definition proto3Applied := proto3 1 proto2Applied.
Eval compute in proto3Applied.

Inductive Dual : Type -> Type -> Prop :=
| senRec : forall a r s, Dual r s -> Dual (a :!: r) (a :?: s)
| recSen : forall a r s, Dual r s -> Dual (a :?: r) (a :!: s)
| dualEps : Dual EpsT EpsT.

Hint Constructors Dual SendT RecT EpsT.

Example dual1 : Dual (nat :!: EpsT) (nat :?: EpsT).
Proof. auto. Qed.

Example dual2 : Dual (nat :!: (nat :?: EpsT)) (nat :?: (nat :!: EpsT)).
Proof. auto. Qed.

End try5.

Module try6.

(** [session] is parameterized over message type [B].  [epsC] is the epsilon
  transition, [send x] sends the message [x] of type [B], [receive x] receives
  the message [x] of type [B].  [choice] indicates the choice made between
  two remote protocols and continue executing.  [offer] uses its input to
  select between left and right protocols. *)

(** Note that [B] really should be infered to allow the use of infix operations
  that just don't work well right now *)

Inductive session : Type :=
| epsC : session
| sendC : message -> session -> session
| receiveC : message -> session -> session
| choiceC : bool -> session -> session
| offerC : bool -> session -> session -> session.

Notation "x :!: y" := (sendC x y)
                        (at level 50, left associativity).

Notation "x :?: y" := (receiveC x y)
                        (at level 50, left associativity).

Notation "x :+: y" := (choiceC x y)
                        (at level 50, left associativity).

Notation "x :&: y" := (offerC x y)
                        (at level 50, left associativity).

Check sendC (basic 3) (receiveC (basic 3) epsC).

Check (basic 3) :!: ((basic 4) :?: epsC).

Definition unwrap(s:session) : session :=
  match s with
  | epsC => s
  | sendC _ s' => s'
  | receiveC _ s' => s'
  | choiceC _ s' => s'
  | offerC b r s => if (b) then r else s                                  
  end.

Definition sendReady(s:session) : Prop :=
  match s with
  | epsC => False
  | sendC _ _ => True
  | receiveC _ _ => False
  | choiceC _ _ => False
  | offerC _ _ _ => False
  end.

Definition receiveReady(s:session) : Prop :=
  match s with
  | epsC => False
  | sendC A _ => False
  | receiveC _ _ => True
  | choiceC _ _ => False
  | offerC _ _ _ => False
  end.

Check sendC (basic 3) (receiveC (basic 3) epsC).

Example sendReady_ex1: sendReady ((basic 3) :!: ((basic 3) :?: epsC)).
reflexivity.
Qed.

Example sendReady_ex2: ~(sendReady ((basic 3) :?: epsC)).
unfold not. intros. inversion H. Qed.

(** [send] returns a new session resulting from one unwrap of [s] if
  [s] is [sendReady] with respect to some type [A].  Choking right now
  on boolean argument to [choice]/[offer] that is input to [unwrap] *)

Definition send (x:message) (s:session) : (sendReady s) -> 
  {u:session | u = (unwrap s)}.
    refine
      (fun p  =>
      match s with 
      | sendC _ _ => _
      | receiveC _ _ => _
      | epsC => _
      | choiceC _ _ => _
      | offerC _ _ _ => _
      end).
    unfold sendReady in p. destruct s in p. contradiction. unfold unwrap. apply (exist _ epsC). reflexivity. contradiction. contradiction. contradiction.
    unfold sendReady in p. destruct s in p. contradiction. unfold unwrap. apply (exist _ s0). reflexivity. contradiction. contradiction. contradiction.
    unfold sendReady in p. destruct s in p. contradiction. unfold unwrap. apply (exist _ s0). reflexivity. contradiction. contradiction. contradiction.
    unfold sendReady in p. destruct s in p. contradiction. unfold unwrap. apply (exist _ s0). reflexivity. contradiction. contradiction. contradiction.
    unfold sendReady in p. destruct s in p. contradiction. unfold unwrap. destruct b. apply (exist _ s0). reflexivity. apply (exist _ s1). reflexivity. contradiction. contradiction. contradiction.
Defined.

(** [A] is the message type, [pa] is a predicate on the message representing
  a precondition as a subset type, [s] is a session, [c] is the input to
  a [choice] operation. *)

Definition send' {pa:message->Prop} (ss:{x:message | pa x}) (s:session) : (sendReady s) -> 
  {u:session | u = (unwrap s)}.
    refine
      (fun p  =>
      match s with 
      | sendC _ _ => _
      | receiveC _ _ => _
      | epsC => _
      | offerC _ _ _ => _
      | choiceC _ _ => _
      end).
    unfold sendReady in p. destruct s in p. contradiction. unfold unwrap. apply (exist _ epsC). reflexivity. contradiction. contradiction. contradiction.
    unfold sendReady in p. destruct s in p. contradiction. unfold unwrap. apply (exist _ s0). reflexivity. contradiction. contradiction. contradiction.
    unfold sendReady in p. destruct s in p. contradiction. unfold unwrap. apply (exist _ s0). reflexivity. contradiction. contradiction. contradiction.
    unfold sendReady in p. destruct s in p. contradiction. unfold unwrap. apply (exist _ s0). reflexivity. contradiction. contradiction. contradiction.
    unfold sendReady in p. destruct s in p. contradiction. unfold unwrap. destruct b. apply (exist _ s0). reflexivity. apply (exist _ s1). reflexivity. contradiction. contradiction. contradiction.
Defined.

(* TODO:  make the return type a sumor.  The left side returns the current return type: a subset type that represents the "rest" of the protocol.  The right side returns a proof that the input predicate on the (x:A) could not be proven.  Note, this may require putting an additional restriction on the input predicate that it is decidable. *)
Definition receive (x:message) (s:session) (c:bool) : (receiveReady s) -> 
  {u:session | u = (unwrap s)}.
    refine
      (fun p  =>
      match s with 
      | sendC _ _ => _
      | receiveC _ _ => _
      | epsC => _
      | choiceC _ _ => _
      | offerC _ _ _ => _
      end).
    unfold receiveReady in p. destruct s in p. contradiction. contradiction. unfold unwrap. apply (exist _ epsC). reflexivity. contradiction. contradiction.
    unfold receiveReady in p. destruct s in p. contradiction. contradiction. unfold unwrap. apply (exist _ s0). reflexivity. contradiction. contradiction.
    unfold receiveReady in p. destruct s in p. contradiction. contradiction. unfold unwrap. apply (exist _ s0). reflexivity. contradiction. contradiction.
    unfold sendReady in p. destruct s in p. contradiction. unfold unwrap. apply (exist _ s0). reflexivity.  unfold unwrap. apply (exist _  s0). reflexivity. unfold unwrap. apply (exist _ s0). reflexivity. unfold unwrap. apply (exist _  s0). reflexivity. unfold unwrap.  destruct b. apply (exist _  s0). reflexivity. apply (exist _ s1). reflexivity.
Defined.

Definition proto2 := sendC (basic 3) (sendC (basic 3) epsC).
Print proto2.

Example sendReady2 : sendReady proto2. reflexivity. Qed.

Eval compute in ((send (basic 3) proto2) sendReady2).
Eval compute in unwrap proto2.
Print proto2.

Definition proto1 := unwrap proto2.
Eval compute in proto1.

Example sendReady1 : sendReady (proto1). reflexivity. Qed.

Eval compute in ((send (basic 1) (proto1)) sendReady1).
Eval compute in unwrap (proto1).

Inductive Dual:session -> session -> Prop :=
| dualEps : Dual epsC epsC
| senRec : forall r s x, Dual s r -> Dual (x :!: s) (x :?: r)
| recSen : forall r s x, Dual s r -> Dual (x :?: s) (x :!: r)
| chOff : forall b l r t, Dual r t -> Dual l t -> Dual (choiceC b t) (offerC b l r)
| offCh : forall b l r t, Dual r t -> Dual l t -> Dual (offerC b l r) (choiceC b t).

Hint Constructors Dual.

Definition proto3 := receiveC (basic 3) (receiveC (basic 3) epsC).
Print proto3.

Example dualExample : Dual proto2 proto3. unfold proto2. unfold proto3. auto. Qed.

Example receiveReady3 : receiveReady proto3. reflexivity. Qed.

Eval compute in proj1_sig ((receive (basic 3) proto3) true receiveReady3).
(*Eval compute in unwrap proto3. *)

Definition proto4 := unwrap proto3.
Eval compute in proto4.

Example receiveReady4 : receiveReady proto4. reflexivity. Qed.

Eval compute in ((receive (basic 1) proto4) true receiveReady4).
Eval compute in unwrap proto4.


Definition proto2' := sendC (basic 3) (sendC (basic 3) epsC).
Print proto2'.

Example sendReady2' : sendReady proto2'. reflexivity. Qed.

Definition proto2'Pred := (fun (x:message) => True).
Example proto2'PredProof : (proto2'Pred (basic 3)). reflexivity. Qed.

Eval compute in send' (exist proto2'Pred (basic 3) proto2'PredProof) proto2 sendReady2'.
Eval compute in unwrap proto2.

(** Some remaining things:

+ Integrate the [message] type from Crypto.v.
- Define a [run] operation over two values of the same session type that
  are also duals.
- Make the result of running a [sumor] or [sumbool] to allow for errors and
  capture of intermediate results using monadic constructs like [maybe]. *)

(** If one protocol is the dual of another, then they should be composable. *)

(** Can we capture the type of the protocol result from the session type? *)

(** Right now the session type is [session] and values of type [session] are
  traces.  [sendC] and [receiveC] are instantiated with values not types.
  Can we make [session] a type family where instances of [session] are 
  types?  Then define structures of that type called [trace]?  Maybe
  [protocol] should be the type family and [session] remain what it is. *)

(** Can we automatically synthesize a decision procedure to determine if a
  [session]: (i) ran properly; and (ii) generated the right value.  Ran
  properly is a property of crypto signatures while generated the right
  value is a property of the generated values.

  For example, a quote [<n,PCR>k-1] ran right if [n] is the correct nonce and
  the signature is correct.  The system is configured properly if [PCR] has
  the right value. Can those decision procedures be synthesized from the
  type? *)

Notation "!!" := (inright _ _).
Notation "[|| x ||]" := (inleft _ x).

Notation "x <-- e1 ; e2" := (match e1 with
                             | inleft x => e2
                             | inright _ => !!
                             end)
                              (right associativity, at level 60).

Eval compute in (unwrap (unwrap proto3)).

Eval compute in (match (inleft (unwrap proto3)) with inleft z => (inleft (unwrap z)) | !! => (inright I) end).

Check (fun (s:session+{True}) => match s with inleft s' => inleft (unwrap s') | !! => (inright I) end).

Check (fun (s:session+{True}) => match s with inleft s' => inleft (unwrap s') | !! => s end).

Definition unwrap'(s:(session+{True})) :=
  match s with
  | inleft s' => inleft (unwrap s')
  | !! => s
  end.

Check unwrap'.

Eval compute in (unwrap' (inleft proto3)).

Eval compute in (unwrap' (unwrap' (inleft proto3))).
      
Definition seq:(session+{True})->(session+{True}).
                               refine (fun s => (x <-- (unwrap' s) ; (unwrap' [||x||]))).
                               reflexivity.
                               Defined.

Eval compute in seq([||proto3||]).

(** First case works.  Second two cases match, but don't have complete
  proofs.  Final two cases are not matching *)

Definition dual_dec: forall s s', {Dual s s'}+{not (Dual s s')}.
Proof.
  intros s s'.
  induction s; induction s';
  match goal with
  | [ |- {Dual epsC epsC}+{not (Dual epsC epsC)} ] => left; auto
  | [ |- {Dual (?M :!: ?S) (?M' :?: ?S')}+{not (Dual (?M :!: ?S) (?M' :?: ?S'))} ] => simpl
  | [ |- {Dual (?M :?: ?S) (?M' :!: ?S')}+{not (Dual (?M :?: ?S) (?M' :!: ?S'))} ] => simpl
  | [ |- {Dual (?R :+: ?T) (?S :&: ?U)}+{~(Dual (?R :+: ?T) (?S :&: ?U))} ] => simpl
  | [ |- {Dual (?S :&: ?U) (?R :+: ?T)}+{~(Dual (?S :&: ?U) (?R :+: ?T))} ] => simpl
  | [ |- _ ] => right; unfold not; intros; inversion H
  end.
  Admitted.

End try6.

Module try7.
(* 
protoType is the type language for protocols.

Var- Represents a placeholder(natural number-indexed variable) in a protocol.  The idea is that it will bring new things received into scope for the rest of the protocol.

Eps- The empty protocol's type.

TODO: What is the best way to make global data(keys, for example) available to the protocol?  Include an environment structure?
*)
  
Inductive protoType : Type :=
| Send : forall (A:Type), protoType -> protoType
| Receive : forall (A:Type), protoType -> protoType
| Offer : protoType -> protoType -> protoType
| Choice : protoType -> protoType -> protoType
| Eps : protoType.

Inductive protoExp : protoType -> Type :=
| SendC {A:Type} {p:protoType} : A -> (protoExp p) -> protoExp (Send A p)
| ReceiveC {A:Type} {p:protoType}
  : A -> (protoExp p) -> protoExp (Receive A p)
| OfferC {p q:protoType} : (protoExp p) -> (protoExp q) -> (protoExp (Offer p q))
| ChoiceC {p q:protoType} : bool -> (protoExp p) -> (protoExp q) -> (protoExp (Choice p q))
| EpsC : protoExp Eps.

Inductive DualT : protoType -> protoType -> Prop :=
| senRec : forall A r s, DualT r s -> DualT (Send A r) (Receive A s)
| recSen : forall A r s, DualT r s -> DualT (Receive A s) (Send A r)
| offCho : forall r r' s s', DualT r r' -> DualT s s' -> DualT (Offer r s) (Choice r' s')
| choOff : forall r r' s s', DualT r r' -> DualT s s' -> DualT (Choice r s) (Offer r' s')
| dualEps : DualT Eps Eps.

Hint Constructors DualT.

Definition Dual {t t': protoType} (r:protoExp t) (s:protoExp t') : Prop :=
  DualT t t'.

Notation "x :!: y" := (protoExp (Send x y))
                        (at level 50, left associativity).

Notation "x :?: y" := (protoExp (Receive x y))
                        (at level 50, left associativity).

Notation "x :+: y" := (protoExp (Choice x y))
                        (at level 50, left associativity).

Notation "x :&: y" := (protoExp (Offer x y))
                        (at level 50, left associativity).


Definition proto1 := SendC (basic 1) EpsC.
Check proto1.
Eval compute in proto1.

Definition proto2 := ReceiveC (basic 1) EpsC.
Check proto2.
Eval compute in proto2.

Definition proto1' := SendC (basic 1) EpsC.
Eval compute in proto1'.

Definition proto2' := ReceiveC (basic 1) EpsC.
Eval compute in proto2'.

Example simpleDual : Dual proto1 proto2.
Proof. unfold Dual. auto.

Theorem dual_dec: forall p p', {DualT p p'}+{not (DualT p p')}.
Proof.
  intros. induction p,p'.
  right. unfold not. intros. inversion H.
  left. apply senRec.
  

  
Definition proto3 := SendC 1 proto2.
Eval compute in proto3.


(* 
What should a protocol "produce"?(what is the return type of runProto?). 
-Can we determine what it produces by the session type alone?
-Is "what a protocol produces" simply what it adds to its environment(new things received)?  Is it a single primitive value?
-How do we capture not only "what" a protocol produces, but PROPERTIES about what it produces(proofs about message content, execution, etc.)
-How do we sequence and compose protocols (thread the result of one to the next)?
 *)

Definition environment := list bool.
Definition env1 : environment := [true ; false].
Check env1.


Definition runProto{t t' : protoType} (r:protoExp t) (s:protoExp t') (currentEnv : environment) (p:Dual r s) : environment.
                           
End try7.

