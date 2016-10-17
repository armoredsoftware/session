Require Import Crypto.
Require Import SfLib.

Definition ob (t:type) := list ((message t) * (list (message Key))).

Record State : Type := mkState
        {keys : list (message Key);
         basics : list (message Basic);
         kOb : ob Key;
         bOb : ob Basic 
        }.

Definition emptyState := mkState nil nil nil nil.

Definition Assertion := State -> Prop.

Definition addKey : forall mt (m:message mt) (pf: mt = Key),
    (list (message Key)) -> (list (message Key)).
Proof.
  intros. subst. exact (m :: X).
Defined.

Definition addMKey t (m:message t) : (list (message Key)) -> (list (message Key)) := fun l => (
  match t as t' return (t = t') -> (list (message Key)) with
  | Key => fun pf => (addKey t m pf l)
  | _ => fun _ => l
  end (eq_refl t)).

Definition addBasic : forall mt (m:message mt) (pf: mt = Basic),
    (list (message Basic)) -> (list (message Basic)).
Proof.
  intros. subst. exact (m :: X).
Defined.

Definition addMBasic t (m:message t) : (list (message Basic)) -> (list (message Basic)) := fun l => (
  match t as t' return (t = t') -> (list (message Basic)) with
  | Basic => fun pf => (addBasic t m pf l)
  | _ => fun _ => l
  end (eq_refl t)).

Definition addP (t:type) : forall mt (pf:mt = t),  ((message mt) * (list (message Key))) -> (ob t) -> (ob t).
Proof.
  intros. subst. exact (X :: X0 ).
Defined.

Definition addMp mt (p:((message mt)*(list (message Key)))) : (ob Basic) -> (ob Basic) := fun l => (
  match mt as t' return (mt = t') -> (ob Basic) with
  | Basic => fun pf => (addP _ _ pf p l)
  | _ => fun _ => l
  end (eq_refl mt)).

Definition addMpK mt (p:((message mt)*(list (message Key)))) : (ob Key) -> (ob Key) := fun l => (
  match mt as t' return (mt = t') -> (ob Key) with
  | Key => fun pf => (addP _ _ pf p l)
  | _ => fun _ => l
  end (eq_refl mt)).

Fixpoint obligations'{mt:type} (m:message mt) (kl: list (message Key))
                               (l:ob Basic) : ob Basic :=
  match m with
  | encrypt mt' m' k => match mt' with
                       | Basic => let new := (m', (kl ++ [(key k)])) in
                                 addMp mt' new l
                       | _ => obligations' m' (kl ++ [(key k)]) l
                       end
  | pair _ _ m1 m2 => (obligations' m1 kl l) ++ (obligations' m2 kl l)
  | basic n => addMp _ ((basic n), kl) l
  | _ => addMp _ (m, nil) l                                           
  end.


Definition obligations{mt:type} (m:message mt) : ob Basic :=
  obligations' m nil nil.

Fixpoint obligationsK'{mt:type} (m:message mt) (kl: list (message Key))
                               (l:ob Key) : ob Key :=
  match m with
  | encrypt mt' m' k => match mt' with
                       | Key => let new := (m', (kl ++ [(key k)])) in
                                 addMpK _ new l
                       | _ => obligationsK' m' (kl ++ [(key k)]) l
                       end
  | pair _ _ m1 m2 => (obligationsK' m1 kl l) ++ (obligationsK' m2 kl l)
  | key k => addMpK _ ((key k), kl) l 
  | _ => addMpK _ (m, nil) l                                           
  end.

Definition obligationsK{mt:type} (m:message mt) : ob Key :=
  obligationsK' m nil nil.

Definition updateState{t:type} (m:message t) (sIn: State) : State :=
  match t with
  | Basic => mkState  sIn.(keys) (addMBasic t m sIn.(basics)) sIn.(kOb) sIn.(bOb)
  | Key => mkState (addMKey t m sIn.(keys)) sIn.(basics) sIn.(kOb) sIn.(bOb)
  | Encrypt _ => mkState sIn.(keys) sIn.(basics)
                                       ((obligationsK m) ++ sIn.(kOb))
                                       ((obligations m) ++ sIn.(bOb))                                                                    
  | _ =>  sIn
  end.