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

(*Require Import Omega.
Require Import Ensembles.
Require Import CpdtTactics.
Require Import Eqdep_dec.
Require Import Coq.Program.Equality.*)
Require Import Peano_dec.


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

Theorem is_inverse (k k':keyType) : {k = (inverse k')}+{k <> (inverse k')}.
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

Inductive type : Type :=
| Basic : type
| Key : type
| Encrypt : type -> type
| Pair : type -> type -> type.

(** Basic messages are natural numbers.  Really should be held abstract, but we
  need an equality decision procedure to determine message equality.  Compound 
  messages are keys, encrypted messages, hashes and pairs. Note that signed
  messages are pairs of a message and encrypted hash. *) 

Inductive message : type -> Type :=
| basic : nat -> message Basic
| key : keyType -> message Key
| encrypt : forall t, message t -> keyType -> message (Encrypt t)
| pair : forall t1 t2, message t1 -> message t2 -> message (Pair t1 t2)
| bad : forall t1,  message t1.

Definition getP1Type (t:type):type :=
  match t with
  | Pair t1 t2 => t1
  | _ => t
  end.

Definition getP2Type (t:type):type :=
  match t with
  | Pair t1 t2 => t2
  | _ => t
  end.

Definition pairFst{t1 t2: type} (m:message (Pair t1 t2)) : message t1 :=
  match m in message t' return message (getP1Type t') with 
  | pair _ _ m1 _ => m1
  | bad _ => bad _
  | _ => bad _                
  end.

(*Eval compute in pairFst (pair _ _ (basic 0) (basic 1)).
Eval compute in pairFst (bad (Pair Basic Basic)).
Eval compute in pairFst (pair _ _ (basic 0) (bad Basic)).
Eval compute in pairFst (pair _ _ (bad Basic) (basic 0)).
*)

Definition pairSnd{t1 t2: type} (m:message (Pair t1 t2)) : message t2 :=
  match m in message t' return message (getP2Type t') with
  | pair _ _ _ m2 => m2
  | bad _ => bad _ 
  | _ => bad _                
  end.

Definition putFst{t1 t2: type}(x:message t1) (m:message (Pair t1 t2)) :
  (message (Pair t1 t2)) :=
  pair _ _ x (pairSnd m).

Definition putSnd{t1 t2: type}(x:message t2) (m:message (Pair t1 t2)) :
  (message (Pair t1 t2)) :=
  pair _ _ (pairFst m) x.
                                                                        

(*Eval compute in pairSnd (pair _ _ (basic 1) (basic 2)).
Eval compute in pairSnd (pair  _ _ (basic 1) (bad Basic)).
*)

(** Predicate that determines if a message cannot be decrypted.  Could be
  that it is not encrypted to begin with or the wrong key is used. *)

Definition is_not_decryptable{t:type}(m:message t)(k:keyType):Prop :=
  match m with
  | encrypt _ m' k' => k <> inverse k'                       
  | _ => True
  end.

Definition is_decryptable{t:type}(m:message t)(k:keyType):Prop :=
  match m with
  | encrypt _ m' k' => k = inverse k'                               
  | _ => False
  end.

(** [decrypt] returns either a decrypted message or a proof of why the message
  cannot be decrypted.  Really should be able to shorten the proof. *)

Definition decrypt_type(t:type):type :=
  match t with
  | Encrypt t' => t'
  | _ => t
  end.

Definition decrypt{t:type}(m:message (Encrypt t))(k:keyType) :
  (message t * is_decryptable m k)+
  {(is_not_decryptable m k)}.
  refine match m in message t' return (message (decrypt_type t') * is_decryptable m k) + {(is_not_decryptable m k)} with
         | encrypt _ m' j => (if (is_inverse k j) then (inleft _ (m',_)) else (inright _ _ ))     
         | _ => inright _ _
         end;
  try reflexivity; try (simpl; assumption).
Defined.

(** This should solve the previous proof if there is a way to try it on every
  proof generated by refine

  repeat try (match goal with
  | [ |- is_not_decryptable (encrypt ?X ?Y) ?Z ] => simpl; assumption
  | [ |- _ ] => reflexivity
  end).
*)

Definition decryptM {t:type} (m:message (Encrypt t)) (k:keyType):message t :=
  match decrypt m k with
  | inleft (m',_) => m'
  | inright _ => bad t
  end.









Theorem eq_type_dec : forall (x y:type), {x = y} + {x <> y}.
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























(*
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

Theorem eq_key_type_dec (k k':keyType) : {k=k'}+{k<>k'}.
Proof.
  intros.
  destruct k; destruct k'; eq_key_helper.
Defined.

Theorem eq_key_dec : forall (k k':message Key), {k=k'}+{k<>k'}.
Proof.
  intros.
  dep_destruct k; dep_destruct k'.
  destruct k0; destruct k1; try (right; unfold not; intros; inversion H; contradiction).
  destruct (eq_nat_dec k0 k1).
  left. subst. reflexivity.
  right. unfold not. intros. inversion H. contradiction.
  destruct (eq_nat_dec k0 k1).
  left. subst. reflexivity.
  right. unfold not. intros. inversion H. contradiction.
    destruct (eq_nat_dec k0 k1).
  left. subst. reflexivity.
  right. unfold not. intros. inversion H. contradiction.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  left. reflexivity.
Defined.

Print eq_key_dec.

Check eq_key_dec.
  
Hint Resolve eq_key_dec.

Theorem eq_type_dec : forall (x y:type), {x = y} + {x <> y}.
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
  end. (*destruct IHx. subst. admit.*)
Defined.

Theorem message_eq_lemma: forall t, forall m:(message t), forall m':(message t), forall k k',
    {m=m'}+{m<>m'} ->
    {k=k'}+{k<>k'} ->
    {(encrypt _ m k)=(encrypt _ m' k')}+{(encrypt _ m k) <> (encrypt _ m' k')}.
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
  (eq_not_eq (eq_key_type_dec k k0)).
  right; unfold not; intros; inversion H.

  specialize IHm with m'.
  destruct IHm; destruct (eq_key_type_dec k k0);
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
Defined.
 *)

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
Defined.

Example sign_2_ex: not (is_signed (pair (basic 1) (encrypt (hash (basic 1)) (private 1))) (public 2)).
Proof.
  unfold not. intros.
  simpl in H. inversion H. inversion H1.
Defined.

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
Defined.                                                 

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


*)