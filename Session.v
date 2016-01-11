Require Export SfLib.
Require Export CpdtTactics.
(*Require Export Crypto. *)

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

Inductive session : Type :=
| epsC : session
| sendC : forall (B:Type),  session -> session
| receiveC : forall (B:Type), session -> session
(*| choiceC : session -> session -> session
| offerC : session -> session -> session*).

Notation "x :!: y" := (sendC x y)
                        (at level 50, left associativity).

Notation "x :?: y" := (receiveC x y)
                        (at level 50, left associativity).

(*Notation "x :+: y" := (choiceC x y)
                        (at level 50, left associativity).

Notation "x :&: y" := (offerC x y)
                        (at level 50, left associativity). *)

Check sendC nat (receiveC bool epsC).

Definition unwrap (s:session) (*(b:bool)*) : session :=
  match s with
  | epsC => s
  | sendC B s' => s'
  | receiveC B s' => s'
  (*| choiceC r s => if (b) then r else s
  | offerC r s => if (b) then r else s   *)                                  
  end.

Definition sendReady (s:session) (A:Type) : Prop :=
  match s with
  | epsC => False
  | sendC A _ => True
  | receiveC _ _ => False
(*  | choiceC _ _ => False
  | offerC _ _ => False *)
  end.

Definition receiveReady (s:session) (A:Type) : Prop :=
  match s with
  | epsC => False
  | sendC A _ => False
  | receiveC _ _ => True
  (*| choiceC _ _ => False
  | offerC _ _ => False  *)                
  end.

Check sendC nat (receiveC bool epsC).

Definition trans (A:Type) (B:Type) := A -> B.
Definition transEx : trans nat bool := (fun (x:nat) => true).

Definition send {A:Type} (x:A) (s:session) : (sendReady s A) -> 
  {u:session | u = unwrap(s)}.
    refine
      (fun p  =>
      match s with 
      | sendC _ u => _
      | receiveC _ u => _
      | epsC => _
      end).
    unfold sendReady in p. destruct s in p. contradiction. unfold unwrap. apply (exist _ epsC). reflexivity. contradiction.
    unfold sendReady in p. destruct s in p. contradiction. unfold unwrap. apply (exist _ u). reflexivity. contradiction.
    unfold sendReady in p. destruct s in p. contradiction. unfold unwrap. apply (exist _ u). reflexivity. contradiction.
Defined.

Definition send' {A:Type} {pa:A->Prop} (ss:{x:A | pa x}) (s:session) : (sendReady s A) -> 
  {u:session | u = unwrap(s)}.
    refine
      (fun p  =>
      match s with 
      | sendC _ u => _
      | receiveC _ u => _
      | epsC => _
      end).
    unfold sendReady in p. destruct s in p. contradiction. unfold unwrap. apply (exist _ epsC). reflexivity. contradiction.
    unfold sendReady in p. destruct s in p. contradiction. unfold unwrap. apply (exist _ u). reflexivity. contradiction.
    unfold sendReady in p. destruct s in p. contradiction. unfold unwrap. apply (exist _ u). reflexivity. contradiction.
Defined.

(* TODO:  make the return type a sumor.  The left side returns the current return type: a subset type that represents the "rest" of the protocol.  The right side returns a proof that the input predicate on the (x:A) could not be proven.  Note, this may require putting an additional restriction on the input predicate that it is decidable. *)
Definition receive {A:Type} (x:A) (s:session) : (receiveReady s A) -> 
  {u:session | u = unwrap(s)}.
    refine
      (fun p  =>
      match s with 
      | sendC _ u => _
      | receiveC _ u => _
      | epsC => _
      end).
    unfold receiveReady in p. destruct s in p. contradiction. contradiction. unfold unwrap. apply (exist _ epsC). reflexivity. 
    unfold receiveReady in p. destruct s in p. contradiction. contradiction. unfold unwrap. apply (exist _ u). reflexivity.
    unfold receiveReady in p. destruct s in p. contradiction. contradiction. unfold unwrap. apply (exist _ u). reflexivity.
Defined.

Definition proto2 := sendC bool (sendC nat epsC).
Print proto2.

Example sendReady2 : sendReady proto2 bool. reflexivity. Qed.

Eval compute in ((send true proto2) sendReady2).
Eval compute in unwrap proto2.

Definition proto1 := unwrap proto2.
Eval compute in proto1.

Example sendReady1 : sendReady proto1 nat. reflexivity. Qed.

Eval compute in ((send 1 proto1) sendReady1).
Eval compute in unwrap proto1.

Inductive Dual : session -> session -> Prop :=
| dualEps : Dual epsC epsC
| senRec : forall A r s, Dual r s -> Dual (sendC A r) (receiveC A s)
| recSen : forall A r s, Dual r s -> Dual (receiveC A s) (sendC A r).                                    

Definition proto3 := receiveC bool (receiveC nat epsC).
Print proto3.

Hint Constructors Dual.
Example dualExample : Dual proto2 proto3. unfold proto2. unfold proto3. auto. Qed.

Example receiveReady3 : receiveReady proto3 bool. reflexivity. Qed.

Eval compute in proj1_sig ((receive true proto3) receiveReady3).
(*Eval compute in unwrap proto3. *)

Definition proto4 := unwrap proto3.
Eval compute in proto4.

Example receiveReady4 : receiveReady proto4 nat. reflexivity. Qed.

Eval compute in ((receive 1 proto4) receiveReady4).
Eval compute in unwrap proto4.


Definition proto2' := sendC bool (sendC nat epsC).
Print proto2'.

Example sendReady2' : sendReady proto2' bool. reflexivity. Qed.

Definition proto2'Pred := (fun (x:bool) => True).
Example proto2'PredProof : (proto2'Pred true). reflexivity. Qed.

Eval compute in send' (exist proto2'Pred true proto2'PredProof) proto2 sendReady2'.
Eval compute in unwrap proto2.

Set Implicit Arguments.
(*Variable A : Set. *)
Inductive maybe (A : Set) (P : A -> Prop) : Set :=
| Unknown : maybe P
| Found : forall x : A, P x -> maybe P.

Notation "{{ x | P }}" := (maybe (fun x => P)).
Notation "??" := (Unknown ).
Notation "[| x |]" := (Found _ x  _).

Notation "x <- e1 ; e2" := (match e1 with
| Unknown => ??
| Found x _ => e2
end)
(right associativity, at level 60).
  
End try6.

Module try7.

Inductive VarT :=
| VarC : nat -> VarT.
  
Definition key_val : Type := nat.

(** Key types are [symmetric], [public] and [private]. *)
Inductive keyType: Type :=
| symmetric : key_val -> keyType
| private : key_val -> keyType
| public : key_val -> keyType.

(** Basic messages held abstract.  Compound messages are keys, encrypted and
  signed messages, hashes and pairs. *)

Inductive message : Type :=
| basic : nat -> message
| var : nat -> message
| key : keyType -> message
| encrypt : message -> keyType -> message
| sign : message -> keyType -> message
| hash : message -> message
| pair : message -> message -> message.


(* 
protoType is the type language for protocols.

Var- Represents a placeholder(natural number-indexed variable) in a protocol.  The idea is that it will bring new things received into scope for the rest of the protocol.

Eps- The empty protocol's type.

TODO: What is the best way to make global data(keys, for example) available to the protocol?  Include an environment structure?
*)
  
Inductive protoType : Type :=
| Send : forall (A:Type), protoType -> protoType
| Receive : forall (A:Type), protoType -> protoType
| Choice : protoType -> protoType -> protoType
| Offer : protoType -> protoType -> protoType                                  
(*| Var : nat -> protoType  (* TODO:  Does Var belong in protoType?  If not, could it be left external and only referenced as an argument to ReceiveC(below)?. If so, should the natural number index stay in the type? *)  *)              
| Eps : protoType.

Inductive protoExp : protoType -> Type :=
| SendC {A:Type} {p:protoType} : message -> (protoExp p) -> protoExp (Send A p)
| ReceiveC (A:Type) {p:protoType}
    : VarT -> (protoExp p) -> protoExp (Receive A p)          
(*| VarC (n:nat) :  protoExp (Var n) *)
| ChoiceC {r s: protoType}
  : bool -> (protoExp r) -> (protoExp s) -> (protoExp (Choice r s))
| OfferC {r s : protoType}
  : (protoExp r) -> (protoExp s) -> (protoExp (Offer r s))    
| EpsC : protoExp Eps.

Inductive DualT : protoType -> protoType -> Prop :=
| senRec : forall A r s, DualT r s -> DualT (Send A r) (Receive A s)
| recSen : forall A r s, DualT r s -> DualT (Receive A s) (Send A r)
| chOff : forall r s r' s', DualT r r' -> DualT s s' -> DualT (Choice r s) (Offer r' s')
| offCh : forall r s r' s', DualT r r' -> DualT s s' -> DualT (Offer r' s') (Choice r s)                                                        
| dualEps : DualT Eps Eps.

Definition Dual {t t': protoType} (r:protoExp t) (s:protoExp t') : Prop :=
  DualT t t'.

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
(*Notation "x :+: y" := (protoExp (Choice x y))
                        (at level 50, left associativity). *)

Notation "x :&: y" := (Offer x y)
                        (at level 50, left associativity).
Notation "x :&: y" := (protoExp (Offer x y))
                        (at level 50, left associativity).


Definition proto1 := SendC (A:=nat) (basic 1) EpsC.
Eval compute in proto1.

Definition proto2 := ReceiveC nat (VarC 1) EpsC.
Eval compute in proto2.

Definition protoChoiceValue := ChoiceC true proto1 (SendC (A:=nat) (basic 2) EpsC).
Eval compute in protoChoiceValue.

Definition protoOfferValue := OfferC (ReceiveC nat (VarC 1) EpsC) (ReceiveC bool (VarC 1) EpsC).
Eval compute in protoOfferValue.

Hint Constructors DualT.

Example simpleDual : Dual proto1 proto2.
Proof. unfold Dual. auto. Qed.

Definition proto3 := SendC (A:=nat) (basic 1) proto2.
Eval compute in proto3.


(* 
What should a protocol "produce"?(what is the return type of runProto?). 
-Can we determine what it produces by the session type alone?
-Is "what a protocol produces" simply what it adds to its environment(new things received)?  Is it a single primitive value?
-How do we capture not only "what" a protocol produces, but PROPERTIES about what it produces(proofs about message content, execution, etc.)
-How do we sequence and compose protocols (thread the result of one to the next)?
 *)



Definition var_id : Type := nat.
Definition env_val : Type := message.

Inductive environment : Type :=
| empty : environment
| item : var_id -> env_val -> environment -> environment.

Definition add (id:var_id) (m:env_val) (e:environment) : environment :=
  item id m e.

Fixpoint delete (id:var_id) (e:environment) : environment :=
  match e with
  | empty => empty
  | item id' m e' => if( beq_nat id id') then (delete id e') else item id' m (delete id e')
  end.

Fixpoint retrieve (id:var_id) (e:environment) : option env_val := 
  match e with
  | empty => None
  | item id' m e' =>
    if (beq_nat id id')
                    then Some m
                    else retrieve id e'
  end.

Definition empty_env := empty.
Definition env_1 := add 1 (basic 1) empty_env.
Print env_1.
Definition env_2 := add 2 (basic 2) env_1.
Definition env_3 := add 2 (basic 3) env_2.
Definition env_4 := delete 2 env_3.
Eval compute in env_4.
Definition env_5 := delete 1 env_3.
Eval compute in env_5.
Eval compute in retrieve 2 env_5.

Fixpoint evalMessage (m:message) (e:environment) : option message :=
  match m with
  | basic n => Some (basic n)
  | var v => retrieve v e
  | key k => Some (key k)
  | encrypt m' k' =>
    match (evalMessage m' e) with
    | Some m'' => Some (encrypt m'' k')
    | None => None
    end
  | sign m' k' =>
    match (evalMessage m' e) with
    | Some m'' => Some (sign m'' k')
    | None => None
    end      
  | hash m' =>
    match (evalMessage m' e) with
    | Some m'' => Some (hash m'')
    | None => None
    end
  | pair m1 m2 =>
    match (evalMessage m1 e) with
    | Some m'' =>
      match (evalMessage m2 e) with
      | Some m''' => Some (pair m'' m''')
      | None => None
      end
    | None => None
    end
      
  end.

  
Fixpoint runProto' {t t' : protoType} (p1:protoExp t) (p2:protoExp t') (p1Env : environment) (p2Env : environment) : option (environment * environment) :=
match p1 with
| SendC _ _ a p1' =>
  match p2 with
  | ReceiveC _ _ v p2' =>
    match v with
    | VarC n =>
      match (evalMessage a p1Env) with
      | Some m => runProto' p1' p2' p1Env (add n m p2Env)
      | None => None
      end
    end
  | _ => None
  end
| ReceiveC _ _ v p1' =>
  match p2 with
  | SendC _ _ a p2' =>  
    match v with
    | VarC n =>
      match (evalMessage a p2Env) with
      | Some m => runProto' p1' p2' (add n m p1Env) p2Env
      | None => None
      end
    end
  | _ => None
  end
| ChoiceC _ _ b p1' p1'' =>
  match p2 with
  | OfferC _ _ p2' p2'' => if (b) then runProto' p1' p2' p1Env p2Env
                             else runProto' p1'' p2'' p1Env p2Env
  | _ => None
  end
| EpsC => Some (p1Env, p2Env)    
| _ => None
end.

Definition runProto {t t' : protoType} (r:protoExp t) (s:protoExp t') (rEnv : environment) (sEnv : environment) (p:Dual r s) : option (environment * environment) := runProto' r s rEnv sEnv.

Eval compute in runProto proto1 proto2 empty_env empty_env simpleDual.

Definition proto1' := SendC (A:=bool) (basic 2)
                      (ReceiveC bool (VarC 42) 
                      EpsC).
Check proto1'.

Definition proto2' := ReceiveC bool (VarC 1)
                      (SendC (A:=bool) (sign (var 1) (private 0))
                      EpsC).
Check proto2'.

Example dual12' : Dual proto1' proto2'. unfold Dual. auto. Qed.

Eval compute in runProto proto1' proto2' empty_env empty_env dual12'.

Definition proto3' (b:bool) := ChoiceC b
                             proto1'
                             proto2'.

Definition proto4' := OfferC
                        proto2'
                        proto1'.

Example dual3'4' : Dual (proto3' true) proto4'. unfold Dual. auto. Qed.

Eval compute in runProto (proto3' true) proto4' empty_env empty_env dual3'4'.

(*Definition proto5 := ReceiveC bool (VarC 1)
                     (proto3' (beq_nat (basic 2) (VarC 1))). *)

Definition proto6 := SendC (A:=bool) (basic 2)
                     proto4'.

                     
                     
End try7.

Module try8.

Inductive protoType : Type :=
| Send : forall (A:Type), protoType -> protoType
| Receive : forall (A:Type), protoType -> protoType
| Choice : protoType -> protoType -> protoType
| Offer : protoType -> protoType -> protoType   
| Eps : forall (A:Type), protoType.

Inductive protoExp : protoType -> Type :=
| SendC {A:Type} {p':protoType} : A -> (protoExp p') -> protoExp (Send A p')
| ReceiveC {A:Type} {p':protoType}: (A->(protoExp p')) -> protoExp (Receive A p') 
| ChoiceC (b:bool) {r s: protoType}
  : (protoExp r) -> (protoExp s) -> (protoExp (Choice r s))
| OfferC {r s : protoType}
  : (protoExp r) -> (protoExp s) -> (protoExp (Offer r s)) 
| ReturnC {T:Type}  : T -> protoExp (Eps T).

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

Inductive DualT : protoType -> protoType -> Prop :=
| senRec : forall A r s, DualT r s -> DualT (Send A r) (Receive A s)
| recSen : forall A r s, DualT r s -> DualT (Receive A s) (Send A r)
| chOff : forall r s r' s', DualT r r' -> DualT s s' -> DualT (Choice r s) (Offer r' s')
| offCh : forall r s r' s', DualT r r' -> DualT s s' -> DualT (Offer r' s') (Choice r s)                                                        
| dualEps : forall T1 T2,  DualT (Eps T1) (Eps T2).

Definition Dual {t t': protoType} (r:protoExp t) (s:protoExp t') : Prop :=
  DualT t t'.

Definition EpsC := ReturnC tt.
Definition proto1 := SendC 1 EpsC.
Check proto1.


Definition proto2 :=
  SendC 1
  ( ReceiveC (fun x =>
  ( ReceiveC (fun y =>
  ( SendC (x + y)
  ( EpsC)))))).                   
Check proto2.

Notation "'send' n ; p" := (SendC n p)
                            (right associativity, at level 60).
Notation "x <- 'receive' ; p " := (ReceiveC (fun x => p))
                                    (right associativity, at level 60).

Notation "'offer'" := OfferC.

Notation "'choice'" := ChoiceC. 

Definition proto1' :=
  send 1;
  EpsC.
Check proto1'.

Definition proto2' :=
  send 1;
  x <- receive;
  y <- receive;
  send (x + y);
  EpsC.
Check proto2'.

Definition proto2'' :=
  send 1;
  x <- receive;
  y <- receive;
  send (andb x y);
  EpsC.
Check proto2''.

Definition constNat (b:bool) : nat := 42.

Definition proto3 :=
  x <- receive;
  send (x+3);
  send x;
  y <- receive;
  ReturnC (constNat y).
Check proto3.

Definition proto4 :=
  x <- receive;
  send (x + 1);
  ReturnC x.
Check proto4.

Definition proto5 :=
  send 1;
  x <- receive;
  ReturnC (T:=nat) x.
Check proto5.

Definition proto6 :=
  offer EpsC
        proto5. Check proto6.

Definition proto7 (b:bool) :=
  choice b
         EpsC
         proto4. Check (proto7 true).


  
  

Hint Constructors DualT.

Example dual45 : Dual proto4 proto5. Proof. unfold Dual. auto. Qed.

Example dual67 : Dual proto6 (proto7 true). Proof. unfold Dual. auto. Qed.


(*Fixpoint getReturnType {p1t:protoType} (p1: protoExp p1t) : Type.
  refine (
  match p1 with
  | SendC _ p' _ p1' => getReturnType p' p1'
  | ReceiveC _ p' f => getReturnType p' _
  | _ => _
  end). *)

  
Fixpoint runProto' {t t' : protoType} {A:Type} (p1:protoExp t) (p2:protoExp t') (d:Dual p1 p2) : A.
  refine (
  match p1 with
| SendC A p1t a p1' =>
  match p2 with
  | ReceiveC A _ f => runProto' _ _ A p1' (f a) _ 
  | _ => _
  end
| ReceiveC _ _ f =>
  match p2 with
  | SendC _ _ a p2' => _ (*runProto' (f a) p2' *)
  | _ => _
  end
| ChoiceC b _ _ p1' p1'' =>
  match p2 with
  | OfferC _ _ p2' p2'' => if (b) then _ (*runProto' _ _ _ p1' p2'*)
                             else _ (*runProto' _ _ _ p1'' p2''*)
  | _ => _
  end
| ReturnC A a => _ 
| _ => _
end). destruct p1. destruct p2. unfold Dual in d. inversion d.

Definition runProto {A:Type} {t t' : protoType} (r:protoExp t) (s:protoExp t') (p:Dual r s) : A  := runProto' r s.



End try8.