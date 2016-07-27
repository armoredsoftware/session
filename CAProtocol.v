Require Import Omega.
Require Import ProtoComp.
Require Import ProtoRep.
Require Import ProtoStateSemantics.
Require Import Crypto.

Definition agent_id : Type := nat.
Definition key_val : Type := nat.

Inductive key_store : Type :=
| empty : key_store
| item : agent_id -> key_val -> key_store -> key_store.

Definition add (id : agent_id) (k : key_val) (s: key_store) : key_store :=
  item id k s.

Fixpoint delete (id : agent_id) (s: key_store) : key_store :=
  match s with
  | empty => empty
  | item id' k s' => if( beq_nat id id') then (delete id s') else item id' k (delete id s')
  end.

Fixpoint retrieve (id:agent_id) (s:key_store) : option (keyType) :=
  match s with
  | empty => None
  | item id' kv s' => if (beq_nat id id') then Some (public kv)
                     else retrieve id s'
  end.
    

Definition storeInit := empty.

(*Definition decryptM {t:type} (m:message (Encrypt t)) (k:keyType):message t*)

Definition extractK (m:message (Encrypt Key)) : message Key :=
  let ekPrivate := (private 0) in
  decryptM m ekPrivate.

Definition attToCA (m:message Key) :=
  let myId := 1 in
  let x := (pair _ _ (basic myId) m) in
    send x;
    y <- receive;
    ReturnC (t:=Pair (Encrypt Key) (Encrypt (Encrypt Key))) y.

Definition unwrapBasic (m:message Basic) : nat :=
  match m with
  | basic n => n
  | _ => 0              
  end.

Definition caToAtt :=
  let keyStore := add 1 0 storeInit in
  x <- receive;
    let id := unwrapBasic (pairFst x) in
    let aikPub := pairSnd x in 
    let caPri := (private 1) in
    let caCert := (encrypt Key aikPub caPri) in
    let symKey := (symmetric 1) in
    let m1 :=
        match (retrieve id keyStore) with
        | None => bad (Encrypt Key)  (*encrypt _ symKey (bad Key)*)
        | Some ekPub => (encrypt _ (key symKey) ekPub)
        end in 
    
  send (pair _ _ m1 (encrypt _ caCert symKey));
      EpsC.

Theorem attCADual : Dual (attToCA (key (public 1))) caToAtt.
Proof.
  repeat (split; try reflexivity).
Qed.

Example attCAEval :
  let st' := (updateState (pair _ _
      (encrypt _ (key (symmetric 1)) (public 0))
      (encrypt _ (encrypt _ (key (public 1)) (private 1)) (symmetric 1)))
                           emptyState) in
                    
    multi emptyState _ _ _ (attToCA (key (public 1))) caToAtt
          (ReturnC (pair _ _ (encrypt _ (key (symmetric 1)) (public 0))
                         (encrypt _ (encrypt _ (key (public 1)) (private 1)) (symmetric 1)))) st'.
Proof.
 (* exists (updateState (pair _ _ (encrypt _ (key (symmetric 1)) (public 0))
                         (encrypt _ (encrypt _ (key (public 1)) (private 1)) (symmetric 1))) emptyState). *)
  unfold caToAtt. unfold attToCA.
  eapply multi_step with (st':=emptyState) (st2:=emptyState). constructor. constructor.
  cbn.


  eapply multi_step with
  (st':= (updateState (pair _ _
      (encrypt _ (key (symmetric 1)) (public 0))
      (encrypt _ (encrypt _ (key (public 1)) (private 1)) (symmetric 1)))
                      emptyState))
    (st2:= (updateState (pair _ _ (basic 1) (key (public 1))) emptyState)).
  constructor. constructor. constructor.
Qed.


Definition attTpm1 :=
  send (basic 44);
  x <- receive;
  ReturnC (t:= Key) x.

Definition tpmAtt1 :=
  v <- receive;
  let caPub := (key (public 1)) in
  send caPub;
  ReturnC (t:=Basic) v.

Definition attTpm2 (m:message (Encrypt Key)) :=
  send m;
  x <- receive;
  ReturnC (t:=Key) x.

Definition tpmAtt2 :=
  enc <- receive;
  let ekPri := (private 0) in
  let y := decryptM enc ekPri