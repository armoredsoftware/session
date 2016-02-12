(** 
Perfect Crypto - Simple definitions for message encryption and signing using
symmetric and assymetric keys

Perry Alexander
The University of Kansas

Provides definitions for:

- [keyType] - [symmetric], [public] and [private] key constructors.
- [inverse] - defines the inverse of any key.
- [is_inverse] - proof that [inverse] is decidable and provides a decision procesure for [inverse].
- [is_not_decryptable] - predicate indicating that a message is or is not decryptable using a specified key.
- [decrypt] - attempts to decrypt a message with a given key.  Returns the decrypted message if decryption occurs.  Returns a proof that the message cannot be decrypted with the key if decryption does not occur.
- [is_signed] - proof that signature checking is decidable and provides a decision procedure for signature check.
- [check] - checks a signature on a message with a given key.  Returns a proof that the check succeeds or does not succeed.
- [check_dec] - proof that signature checking is decidable and provides a decision procedure for signature checking.  Alternative function for [check].
*)

Require Import Omega.
Require Import Ensembles.
Require Import CpdtTactics.
Require Import Eqdep_dec.
Require Import Peano_dec.
Require Import Coq.Program.Equality.

(** Ltac helper functions for discharging cases generated from sumbool types
  using one or two boolean cases. *)

Ltac eq_not_eq P := destruct P;
  [ (left; subst; reflexivity) |
    (right; unfold not; intros; inversion H; contradiction) ].

Ltac eq_not_eq' P Q := destruct P; destruct Q;
  [ (subst; left; reflexivity) |
    (right; unfold not; intros; inversion H; contradiction) |
    (right; unfold not; intros; inversion H; contradiction) |
    (right; unfold not; intros; inversion H; contradiction) ].

(** Key values will be [nat] by default.  Could be anything satisfying
 properties following.  *)

Definition key_val : Type := nat.

(** Key types are [symmetric], [public] and [private]. *)
Inductive keyType: Type :=
| symmetric : key_val -> keyType
| private : key_val -> keyType
| public : key_val -> keyType.

(** A [symmetric] key is its own inverse.  A [public] key is the inverse of
  the [private] key with the same [key_val].  A [private] key is the inverse of
  the [public] key with the same [key_val]. *)

Fixpoint inverse(k:keyType):keyType :=
match k with
| symmetric k => symmetric k
| public k => private k
| private k => public k
end.

(** Proof that inverse is decidable for any two keys. The resulting proof
 gives us the function [is_inverse] that is a decision procedure for key 
 inverse checking.  It will be used in [decrypt] and [check] later in the
 specification. *)

Theorem is_inverse:forall k k', {k = (inverse k')}+{k <> (inverse k')}.
Proof.
  intros.
  destruct k; destruct k';
  match goal with
  | [ |- {symmetric ?P = (inverse (symmetric ?Q))}+{symmetric ?P <> (inverse (symmetric ?Q))} ] => (eq_not_eq (eq_nat_dec P Q))
  | [ |- {private ?P = (inverse (public ?Q))}+{private ?P <> (inverse (public ?Q))} ] => (eq_not_eq (eq_nat_dec P Q))
  | [ |- {public ?P = (inverse (private ?Q))}+{public ?P <> (inverse (private ?Q))} ] => (eq_not_eq (eq_nat_dec P Q))
  | [ |- _ ] => right; simpl; unfold not; intros; inversion H
  end.
Defined.

Eval compute in (is_inverse (public 1) (private 1)).

Eval compute in (is_inverse (public 1) (private 2)).

Eval compute in (is_inverse (public 2) (private 1)).

Eval compute in (is_inverse (private 1) (public 1)).

Eval compute in (is_inverse (symmetric 1) (symmetric 1)).

Eval compute in (is_inverse (symmetric 1) (symmetric 2)).

(** Various proofs for keys and properties of the inverse operation.  All keys
  must have an inverse.  All keys have a unique inverse.  Equal inverses come
  from equal keys *)

Theorem inverse_injective : forall k1 k2, inverse k1 = inverse k2 -> k1 = k2.
Proof.
  intros.
  destruct k1; destruct k2; simpl in H; try (inversion H); try (reflexivity).
Qed.

Hint Resolve inverse_injective.

Theorem inverse_inverse : forall k, inverse (inverse k) = k.
Proof.
  intros. destruct k; try reflexivity.
Qed.

Hint Resolve inverse_inverse.

Theorem inverse_surjective : forall k, exists k', (inverse k) = k'.
Proof.
  intros. exists (inverse k). auto.
Qed.

Hint Resolve inverse_surjective.

Theorem inverse_bijective : forall k k',
    inverse k = inverse k' ->
    k = k' /\ forall k, exists k'', inverse k = k''.
Proof.
  auto.
Qed.

Inductive type : Type :=
| Basic : type
| Key : type
| Encrypt : type -> type
| Hash : type -> type
| Pair : type -> type -> type
| Either : type -> type -> type.

(** Basic messages are natural numbers.  Really should be held abstract, but we
  need an equality decision procedure to determine message equality.  Compound 
  messages are keys, encrypted messages, hashes and pairs. Note that signed
  messages are pairs of a message and encrypted hash. *) 

Inductive message : type -> Type :=
| basic : nat -> message Basic
| key : keyType -> message Key
| encrypt : forall t, message t -> keyType -> message (Encrypt t)
| hash : forall t, message t -> message (Hash t)
| pair : forall t1 t2, message t1 -> message t2 -> message (Pair t1 t2)
| leither : forall t1 t2, message t1 -> message (Either t1 t2)
| reither : forall t1 t2, message t2 -> message (Either t1 t2)
| bad : forall t1,  message t1.


(** Predicate that determines if a message cannot be decrypted.  Could be
  that it is not encrypted to begin with or the wrong key is used. *)

Definition is_not_decryptable{t:type}(m:message t)(k:keyType):Prop :=
  match m with
  | encrypt t m' k' => k <> inverse k'
  (*| bad _ => False     *)                         
  | _ => True
  end.

Definition is_decryptable{t:type}(m:message t)(k:keyType):Prop :=
  match m with
  | encrypt t m' k' => k = inverse k'
  (*| bad _ => True*)                                
  | _ => False
  end.

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
  simpl. tauto. Qed.
  (*simpl. unfold not in H. simpl in H. apply H. trivial. 
Qed. *)

(** [decrypt] returns either a decrypted message or a proof of why the message
  cannot be decrypted.  Really should be able to shorten the proof. *)

(*
Inductive sumor (A : Type) (B : Prop) : Type :=
    inleft : A -> A + {B} | inright : B -> A + {B}
*)

Theorem is_not_decryptable_basic: forall n k, is_not_decryptable (basic n) k.
Proof.
  intros.
  reflexivity.
Qed.

Theorem is_not_decryptable_key: forall k k', is_not_decryptable (key k) k'.
Proof.
  intros.
  reflexivity.
Qed.  

Theorem is_not_decryptable_hash: forall t n k, is_not_decryptable (hash t n) k.
Proof.
  intros.
  reflexivity.
Qed.

Theorem is_not_decryptable_pair: forall t u n m k, is_not_decryptable (pair t u n m) k.
Proof.
  intros.
  reflexivity.
Qed.

Theorem is_not_decryptable_bad: forall t k, is_not_decryptable (bad t) k.
Proof.
  intros.
  reflexivity.
Qed.

Definition decrypt_type(t:type):type :=
  match t with
  | Encrypt t' => t'
  | _ => t
  end.
                 

Fixpoint decrypt{t:type}(m:message (Encrypt t))(k:keyType):message t+{(is_not_decryptable m k)}.
  refine match m in message t' return message (decrypt_type t') + {(is_not_decryptable m k)} with
         | basic _ => inright _ _
         | key _ => inright _ _
         | encrypt t m' j => (if (is_inverse k j) then (inleft _ m') else (inright _ _ ))
         | hash _ _ => inright _ _
         | pair _ _ _ _ => inright _ _
         | leither _ _ _ => inright _ _
         | reither _ _ _ => inright _ _                           
         | bad _ => inright _ _
         end.
Proof.
  reflexivity.
  reflexivity.
  simpl. assumption.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  (*exact (bad t1).n*)
  reflexivity.
Defined.

Definition decryptM{t:type} (m:message (Encrypt t)) (k:keyType):message t :=
  match decrypt m k with
  | inleft m' => m'
  | inright _ => bad t
  end.

(*Fixpoint decrypt'{t:type}(m:message (Encrypt t))(k:keyType):message t+{(is_not_decryptable m k)}.
refine
  match m with
  | basic _ => inright _ is_not_decryptable_basic
  | key _ => inright _ is_not_decryptable_key
  | encrypt t m' j => (if (is_inverse k j) then (inleft _ m') else (inright _ _ ))
  | hash _ _ => inright _ is_not_decryptable_hash
  | pair _ _ _ _ => inright _ is_not_decryptable_pair
  end.
Proof.
  simpl. assumption.
Abort. *)

(** This should solve the previous proof if there is a way to try it on every
  proof generated by refine

  repeat try (match goal with
  | [ |- is_not_decryptable (encrypt ?X ?Y) ?Z ] => simpl; assumption
  | [ |- _ ] => reflexivity
  end).
*)

Eval compute in decrypt(encrypt Basic (basic 1) (symmetric 1)) (symmetric 1).

Eval compute in decrypt(encrypt Basic (basic 1) (symmetric 1)) (symmetric 2).

(** Generate a signature using encryption and hash *)

Definition sign{t:type}(m:message t)(k:keyType) :=
  (pair t (Encrypt (Hash t)) m (encrypt (Hash t) (hash t m) k)).

Eval compute in sign (basic 1) (public 1).

Ltac eq_key_helper :=
  match goal with
  | [ |- {symmetric ?P = symmetric ?Q} + {symmetric ?P <> symmetric ?Q} ] =>
    (eq_not_eq (eq_nat_dec P Q))
  | [ |- {public ?P = public ?Q} + {public ?P <> public ?Q} ] =>
    (eq_not_eq (eq_nat_dec P Q))
  | [ |- {private ?P = private ?Q} + {private ?P <> private ?Q} ] =>
    (eq_not_eq (eq_nat_dec P Q))
  | [ |- _ ] => right; unfold not; intros; inversion H
  end.

Theorem eq_key_dec: forall k k':keyType, {k=k'}+{k<>k'}.
Proof.
  intros.
  destruct k; destruct k'; eq_key_helper.
Defined.
  
Hint Resolve eq_key_dec.

Theorem eq_type_dec: forall x y : type, {x = y} + {x <> y}.
Proof.
  induction x, y;
  match goal with
  | [ |- {?T = ?T} + {?T <> ?T} ] => left; reflexivity
  | [ |- {?C ?T = ?C ?U} + {?C ?T <> ?C ?U} ] => specialize IHx with y; destruct IHx; [ left; subst; reflexivity | right; unfold not; intros; inversion H; contradiction ]
  | [ |- {?C ?T ?U = ?C ?T' ?U'} + {?C ?T ?U <> ?C ?T' ?U'} ] => specialize IHx1 with y1; specialize IHx2 with y2; destruct IHx1; destruct IHx2; 
  [ left; subst; reflexivity
   | subst; right; unfold not; intros; inversion H; contradiction
   | subst; right; unfold not; intros; inversion H; contradiction
   | subst; right; unfold not; intros; inversion H; contradiction ]
  | [ |- _ ] => right; unfold not; intros; inversion H 
  end.
  Defined.

Theorem message_eq_lemma: forall t, forall m:(message t), forall m':(message t), forall k k',
    {m=m'}+{m<>m'} ->
    {k=k'}+{k<>k'} ->
    {(encrypt t m k)=(encrypt t m' k')}+{(encrypt t m k) <> (encrypt t m' k')}.
Proof.
  intros.
  destruct H; destruct H0.
  left; subst; reflexivity.
  right; subst; unfold not; intros; inversion H; contradiction.
  right. subst. unfold not. intros. inversion H. apply inj_pair2_eq_dec in H1. contradiction.
  apply eq_type_dec.
  right. unfold not. intros. inversion H. apply inj_pair2_eq_dec in H1. contradiction.
  apply eq_type_dec.
Defined.

Hint Resolve message_eq_lemma.

Ltac whack_right :=
  match goal with
  | [ |- {basic ?P = basic ?Q}+{basic ?P <> basic ?Q} ] =>
    (eq_not_eq (eq_nat_dec P Q))
  | [ |- {key ?P = key ?Q}+{key ?P <> key ?Q} ] =>
    (eq_not_eq (eq_key_dec P Q))
  | [ |- {encrypt ?P ?P' = encrypt ?Q ?Q'}+{encrypt ?P ?P' <> encrypt ?Q ?Q'} ] =>
    auto 
  | [ H : {?P = ?Q}+{?P <> ?Q} |- {hash ?P = hash ?Q}+{hash ?P <> hash ?Q} ] =>
    (eq_not_eq H)
  | [ H1 : {?P = ?P'}+{?P <> ?P'},
      H2 : {?Q = ?Q'}+{?Q <> ?Q'}
      |- {pair ?P ?Q = pair ?P' ?Q'}+{pair ?P ?Q <> pair ?P' ?Q'} ] =>
    (eq_not_eq' H1 H2)
  | [ |- _ ] => right; unfold not; intros; inversion H
  end.

(*Theorem message_eq_dec: forall t, forall m:(message t), forall m':(message t), {m=m'}+{m<>m'}.
Proof.
  dependent induction m; dependent induction m'.
  (eq_not_eq (eq_nat_dec n n0)).
  right; unfold not; intros; inversion H.
  (eq_not_eq (eq_key_dec k k0)).
  right; unfold not; intros; inversion H.

  specialize IHm with m'.
  destruct IHm; destruct (eq_key_dec k k0);
  [ left; subst; reflexivity
  | right; unfold not; intros; inversion H; contradiction
  | right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1;
    [contradiction | apply eq_type_dec]
  | right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1;
    [contradiction | apply eq_type_dec]].

  right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1.
  
  specialize IHm with m'.
  destruct IHm;
  [ left; subst; reflexivity 
  | right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1;
    [contradiction | apply eq_type_dec]].

  right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1.

  specialize IHm2 with m'2.
  specialize IHm1 with m'1.
  destruct IHm1; destruct IHm2;
  [ left; subst; reflexivity 
  | right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1; apply inj_pair2_eq_dec in H2; [ contradiction | apply eq_type_dec | apply eq_type_dec | apply eq_type_dec ]
  | right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1; apply inj_pair2_eq_dec in H2; [ contradiction | apply eq_type_dec | apply eq_type_dec | apply eq_type_dec ]
  | right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1; apply inj_pair2_eq_dec in H2; [ contradiction | apply eq_type_dec | apply eq_type_dec | apply eq_type_dec ]]. 

  right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1.
  right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1
  right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1.
  right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1.
  right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1.
  right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1.
  left; reflexivity.
Defined. *)

(*Hint Resolve message_eq_dec. *)

Print encrypt.

(*Definition is_signed{t:type}(m:message (Pair t (Encrypt (Hash t))))(k:keyType):Prop :=
  match m with
  | pair t t' n n' => n' = sign n k
  | _ => False
  end.
  
  match m with
  | (pair r (Encrypt (Hash r')) m' m'') => match (decrypt m'' k) with
                      | inleft (hash r m''') => m'=m'''
                      | inleft _ => False
                      | inright _ => False
                      end
  | _ => False
  end.



    
  | (pair t t' m m') => match m' with
                       | encrypt t m'' k' =>  match m'' with
                                            | (hash t m''') => m=m''' /\ (k = inverse k')
                                      end
                  end
  end. 

Example sign_1_ex: is_signed (pair (basic 1) (encrypt (hash (basic 1)) (private sf1))) (public 1).
Proof.
  simpl. tauto.
Qed.

Example sign_2_ex: not (is_signed (pair (basic 1) (encrypt (hash (basic 1)) (private 1))) (public 2)).
Proof.
  unfold not. intros.
  simpl in H. inversion H. inversion H1.
Qed.

Theorem check_dec: forall m:message, forall k, {(is_signed m k)}+{not (is_signed m k)}.
Proof.
  intros.
  destruct m; try tauto.
  destruct m2; try tauto.
    destruct m2; try tauto.
      destruct (is_inverse k k0).
        destruct (message_eq_dec m1 m2); try tauto.
        left. subst. simpl. tauto.
          right. unfold not. intros. simpl in H. tauto.
          right. unfold not. intros. simpl in H. tauto.
Defined. 
            
Eval compute in check_dec (sign (basic 1) (private 1)) (public 1).

Eval compute in check_dec (sign (basic 1) (private 1)) (public 2).

Notation " 'good' " := (left _ _).

Notation " 'bad' " := (right _ _).

Eval compute in check_dec (sign (basic 1) (private 1)) (public 1).

Eval compute in check_dec (sign (basic 1) (private 1)) (public 2). *)

Theorem m2 : forall P Q R: Prop, P -> Q -> R -> Q.
Proof.
  intros. match goal with | [ B : _ |- _ ] => exact B end.
Qed.                                                 

(** [notHyp] determines if [P] is in the assumption set of a proof state.
  The first match case simply checks to see if [P] matches any assumption and
  fails if it does.  The second match case grabs everything else.  If [P]
  is a conjunction, it checks to see if either of its conjuncts is an
  assumption calling [notHyp] recursively. 

*)

Ltac notHyp P :=
  match goal with
  | [ _ : P |- _ ] => fail 1
  | _ =>
    match P with
    | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
    | _ => idtac
    end
  end.
                           
Ltac extend pf :=
  let t := type of pf in
  notHyp t; generalize pf; intro.