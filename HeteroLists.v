Require Export Crypto.
Require Import SessionLearned.
Require Import CpdtTactics.
Require Import SfLib.



Lemma zgtz : 0 > 0 -> False.
  crush.
Qed.
Print sig.
Definition pred_strong2 (s : {n : nat | n > 0}) : nat :=
  match s with
    | exist _ O pf => match zgtz pf with end
    | exist _ (S n') _ => n'
  end.

Section hlist.

  
Set Implicit Arguments.
Set Asymmetric Patterns.
  Variable A : Type.
  Variable B : A -> Type.

  (* EX: Define a type [hlist] indexed by a [list A], where the type of each element is determined by running [B] on the corresponding element of the index list. *)

  (** We parameterize our heterogeneous lists by a type [A] and an [A]-indexed type [B].%\index{Gallina terms!hlist}% *)

(* begin thide *)
  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (x : A) (ls : list A), B x -> hlist ls -> hlist (x :: ls).

  (** We can implement a variant of the last section's [get] function for [hlist]s.  To get the dependent typing to work out, we will need to index our element selectors (in type family [member]) by the types of data that they point to.%\index{Gallina terms!member}% *)

(* end thide *)
  (* EX: Define an analogue to [get] for [hlist]s. *)

(* begin thide *)
  Variable elm : A.

  Inductive member : list A -> Type :=
  | HFirst : forall ls, member (elm :: ls)
  | HNext : forall x ls, member ls -> member (x :: ls).

  (** Because the element [elm] that we are "searching for" in a list does not change across the constructors of [member], we simplify our definitions by making [elm] a local variable.  In the definition of [member], we say that [elm] is found in any list that begins with [elm], and, if removing the first element of a list leaves [elm] present, then [elm] is present in the original list, too.  The form looks much like a predicate for list membership, but we purposely define [member] in [Type] so that we may decompose its values to guide computations.

     We can use [member] to adapt our definition of [get] to [hlist]s.  The same basic [match] tricks apply.  In the [HCons] case, we form a two-element convoy, passing both the data element [x] and the recursor for the sublist [mls'] to the result of the inner [match].  We did not need to do that in [get]'s definition because the types of list elements were not dependent there. *)

  Fixpoint hget ls (mls : hlist ls) : member ls -> B elm :=
    match mls with
      | HNil => fun mem =>
        match mem in member ls' return (match ls' with
                                          | nil => B elm
                                          | _ :: _ => unit
                                        end) with
          | HFirst _ => tt
          | HNext _ _ _ => tt
        end
      | HCons _ _ x mls' => fun mem =>
        match mem in member ls' return (match ls' with
                                          | nil => Empty_set
                                          | x' :: ls'' =>
                                            B x' -> (member ls'' -> B elm)
                                            -> B elm
                                        end) with
          | HFirst _ => fun x _ => x
          | HNext _ _ mem' => fun _ get_mls' => get_mls' mem'
        end x (hget mls')
    end.

Fixpoint lengthHlist ls (h : (hlist ls)) : nat :=
  match h with
  | HNil => 0
  | HCons _ _ _ h' => 1 + lengthHlist h'
  end.

  
(* end thide *)
End hlist.


Section hlisttry.
(* begin thide *)
Implicit Arguments HNil [A B].
Implicit Arguments HCons [A B x ls].

Implicit Arguments HFirst [A elm ls].
Implicit Arguments HNext [A elm x ls].
(* end thide *)

(** By putting the parameters [A] and [B] in [Type], we enable fancier kinds of polymorphism than in mainstream functional languages.  For instance, one use of [hlist] is for the simple heterogeneous lists that we referred to earlier. *)

Definition someTypes : list Set := nat :: bool :: nil.

Definition someMtypes : list Type := (message Basic) :: (message Key) :: nil.

End hlisttry.

Unset Implicit Arguments. 
Unset Asymmetric Patterns.


Definition isSend {t:protoType} (p:protoExp t) : Prop :=
  match p with
  | SendC _ _ => True
  | _ => False
  end.

Theorem isSend_dec {t:protoType} (p:protoExp t) : {isSend p} + {~(isSend p)}.
Proof.
  dep_destruct p;
  try (right; unfold not; intros; inversion H; contradiction).
  left. simpl. trivial.
Defined.

Definition isReceive {t:protoType} (p:protoExp t) : Prop :=
  match p with
  | ReceiveC _ => True
  | _ => False
  end.



           
Theorem isReceive_dec {t:protoType} (p:protoExp t) : {isReceive p} + {~(isReceive p)}.
Proof.
  dep_destruct p;
  try (right; unfold not; intros; inversion H; contradiction).
  left. simpl. trivial.
Defined.


Fixpoint typesLearned' {t t':protoType} (p1:protoExp t) (p2:protoExp t')
  (pf:Dual p1 p2) (l':list Type) : list Type.
Proof.
  intros. destruct p1; destruct p2; try inversion pf.
  subst. exact (typesLearned' _ _ p1 (p m) H0 l').
  assert (list Type). subst. exact (typesLearned' _ _ (p m) p2 H0 l').
  exact ((message t) :: X).
  destruct b.
  exact (typesLearned' _ _ p1_1 p2_1 H l').
  exact (typesLearned' _ _ p1_2 p2_2 H0 l').
  destruct b.
  exact (typesLearned' _ _ p1_1 p2_1 H l').
  exact (typesLearned' _ _ p1_2 p2_2 H0 l').
  exact l'.
Defined.


Definition getRest{t0 t:type}{p'0 p':protoType} (f:(message t0 -> protoExp p'0)) (m:message t) (p1:protoExp p') (pf:Dual(send m; p1) (ReceiveC f))  : (protoExp p'0).
Proof.
  inversion pf. subst.
  exact (f m).
Defined.

Print getRest.



  t : type
  p' : protoType
  m : message t
  p1 : protoExp p'
  t0 : type
  p'0 : protoType
  p : message t0 -> protoExp p'0
  pf : Dual (send m; p1) (x <- receive ; p x)

Definition typesLearned {t t':protoType} (p1:protoExp t) (p2:protoExp t')
  (pf:Dual p1 p2) : list Type := typesLearned' p1 p2 pf nil.
  
  
  
(* begin thide *)

Example someValues : hlist (fun T : Set => T) someTypes :=
  HCons 5 (HCons true HNil).

Example someMValues : hlist (fun T : Type => T) someMtypes :=
  HCons (basic 0) (HCons (key (public 0)) HNil).

Eval simpl in hget someValues HFirst.

Eval simpl in hget someMValues HFirst.
Eval cbv in lengthHlist someMValues.

  
(** %\vspace{-.15in}% [[
     = 5
     : (fun T : Set => T) nat
]]
*)

Eval simpl in hget someValues (HNext HFirst).
(** %\vspace{-.15in}% [[
     = true
     : (fun T : Set => T) bool
]]
*)

(** We can also build indexed lists of pairs in this way. *)

Example somePairs : hlist (fun T : Set => T * T)%type someTypes :=
  HCons (1, 2) (HCons (true, false) HNil). 

End hlisttry.

 