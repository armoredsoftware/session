Require Import Crypto.
Require Import ProtoRep.
Require Import CpdtTactics.
Require Import Eqdep_dec.
Require Import Program.
Require Import SfLib.
Require Import Coq.Program.Equality.
Require Import LibTactics.

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

Inductive step : forall (s:State) (t r t':protoType),
    (protoExp t) -> (protoExp r) -> (protoExp t') -> State -> Prop :=
| ST_Send_Rec : forall x y  mt
                  (m:message mt) (p1':protoExp x)
                  (f:(message mt) -> protoExp y) (s:State),
    step s _ _ _ (SendC m p1') (ReceiveC f) p1' s
| ST_Rec_Send : forall x y mt (m:message mt) (p1':protoExp x)
                       (f:(message mt) -> protoExp y) s,                     
    step s _ _ _ (ReceiveC f) (SendC m p1') (f m) (updateState m s)
| ST_Choice_true : forall rt rt' st st'
                     (r:protoExp rt) (r0:protoExp rt')
                     (s:protoExp st) (s0:protoExp st') stt,
    step stt _ _ _ (ChoiceC true r s) (OfferC r0 s0) r stt
| ST_Choice_false : forall rt rt' st st'
                     (r:protoExp rt) (r0:protoExp rt')
                     (s:protoExp st) (s0:protoExp st') stt,
    step stt _ _ _ (ChoiceC false r s) (OfferC r0 s0) s stt
| ST_Offer_true : forall rt rt' st st'
                     (r:protoExp rt) (r0:protoExp rt')
                     (s:protoExp st) (s0:protoExp st') stt,
    step stt _ _ _ (OfferC r0 s0) (ChoiceC true r s) r0 stt
| ST_Offer_false : forall rt rt' st st'
                     (r:protoExp rt) (r0:protoExp rt')                     (s:protoExp st) (s0:protoExp st') stt,
    step stt _ _ _ (OfferC r0 s0) (ChoiceC false r s) s0 stt.

(*Notation "'stepe' st st'" := (step st _ _ _ st') (at level 50).*)

Inductive multi : forall s (t r t':protoType),
    (protoExp t) -> (protoExp r)  -> (protoExp t') -> State -> Prop :=
| multi_refl : forall (t r :protoType) (x:protoExp t) (y:protoExp r) st,
    multi st _ _ _ x y x st
| multi_step : forall (t t' r r2 s:protoType),
    forall (x:protoExp t) (x':protoExp t')
      (y:protoExp r) (y2:protoExp r2)
      (z1:protoExp s) st st' st'' st2 st2',
                    step st _ _ _ x x' y st' ->
                    step st2 _ _ _ x' x y2 st2' -> 
                    multi st' _ _ _ y y2 z1 st'' ->
                    multi st _ _ _ x x' z1 st''.

Notation "'multie' st st'" := (multi st _ _ _ st')
                                (at level 50).

Definition normal_form {p1t p2t:protoType}
           (p1:protoExp p1t)(p2:protoExp p2t) : Prop :=
  forall st st',  ~ exists  t' (x:protoExp t'),  step st _ _ _ p1 p2 x st'.

Theorem nf_ex : normal_form (ReturnC (basic 0)) (ReturnC (basic 1)).
Proof.
 unfold normal_form. unfold not. intros. destruct H. destruct H. inversion H.
Qed.

Axiom updateBoth :  forall t (m:message t) x6 x7 p1t p2t p3t (p1:protoExp p1t) (p2:protoExp p2t) (p3: protoExp p3t),
    multi x6 _ _ _ p1 p2 p3 x7 ->
    multi (updateState m x6) _ _ _ p1 p2 p3 (updateState m x7).

Theorem normalization {p1t p2t :protoType} :
    forall (p1:protoExp p1t) (p2:protoExp p2t),
      (Dual p1 p2) ->
    exists p3t p4t (p3:protoExp p3t) (p4:protoExp p4t) st st' st2 st2',
      (multi st _ _ _ p1 p2 p3 st') /\ (multi st2 _ _ _ p2 p1 p4 st2')
      /\ normal_form p3 p4.
Proof.
  intros.
  generalize dependent p2. generalize dependent p2t.
  induction p1; destruct p2;
  try (intros H; inversion H).
  inversion H. subst.
  dep_destruct (IHp1 p'0 (p m)).
  inversion H. assumption.
  destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H4. eexists. eexists. exists x2. exists x3.
  exists x4. exists x5. exists x6. exists (updateState m x7).

  split. apply multi_step with (y:=p1) (y2:=(p m)) (st':=x4) (st2:=x6) (st2':=(updateState m x6)). constructor. constructor. assumption.
  split. apply multi_step with (y:=(p m)) (y2:=p1) (st':=(updateState m x6)) (st2:=x4) (st2':=x4). constructor. constructor.
  apply updateBoth. assumption. assumption.

  intros. inversion H0. subst.
  dep_destruct (H m _ p2).
  inversion H0. assumption.
  destruct H0.  destruct H1. destruct H1. destruct H1. destruct H1. destruct H1. destruct H1. destruct H1. destruct H1. destruct H4.

  eexists. eexists. exists x2. exists x3. exists x4. exists (updateState m x5). exists x6. exists x7.

  split. apply multi_step with (y:=(p m)) (y2:=p2) (st':=(updateState m x4)) (st2:=x6) (st2':=x6). constructor. constructor.
  apply updateBoth. assumption.
  split. apply multi_step with (y:=p2) (y2:=(p m)) (st':=x6) (st2:=x4) (st2':=(updateState m x4)). constructor. constructor. assumption. assumption.
  intros. inversion H0.
  intros. inversion H0.
  intros. inversion H0.
  intros. inversion H0.

  destruct b. dep_destruct (IHp1_1 r0 p2_1). assumption. destruct x. assumption. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H4.

    destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H6.

  eexists. eexists. eexists. eexists.

  exists x11. exists x12. exists x13. exists x14.
  split. apply multi_step with (y:=p1_1) (y2:=p2_1) (st':=x11) (st2:=x13) (st2':=x13). constructor. constructor. apply H3.
  split. apply multi_step with (y:=p2_1) (y2:=p1_1) (st':=x13) (st2:=x11) (st2':=x11). constructor. constructor. apply H6. assumption.

  dep_destruct (IHp1_2 s0 p2_2). assumption. destruct x. assumption.
  destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H4.

  destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H6.

  eexists. eexists. eexists. eexists.

  exists x11. exists x12. exists x13. exists x14.
  split. apply multi_step with (y:=p1_2) (y2:=p2_2) (st':=x11) (st2:=x13) (st2':=x13). constructor. constructor. apply H3.
  split. apply multi_step with (y:=p2_2) (y2:=p1_2) (st':=x13) (st2:=x11) (st2':=x11). constructor. constructor. apply H6. assumption.

  destruct b. dep_destruct (IHp1_1 r0 p2_1). assumption. destruct x. assumption. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H4.

    destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H6.

  eexists. eexists. eexists. eexists.

  exists x11. exists x12. exists x13. exists x14.
  split. apply multi_step with (y:=p1_1) (y2:=p2_1) (st':=x11) (st2:=x13) (st2':=x13). constructor. constructor. apply H3.
  split. apply multi_step with (y:=p2_1) (y2:=p1_1) (st':=x13) (st2:=x11) (st2':=x11). constructor. constructor. apply H6. assumption.

  dep_destruct (IHp1_2 s0 p2_2). assumption. destruct x. assumption.
  destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H4.

  destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H6.

  eexists. eexists. eexists. eexists.

  exists x11. exists x12. exists x13. exists x14.
  split. apply multi_step with (y:=p1_2) (y2:=p2_2) (st':=x11) (st2:=x13) (st2':=x13). constructor. constructor. apply H3.
  split. apply multi_step with (y:=p2_2) (y2:=p1_2) (st':=x13) (st2:=x11) (st2':=x11). constructor. constructor. apply H6. assumption.

  eexists. eexists. eexists. eexists. exists emptyState. exists emptyState. exists emptyState. exists emptyState.
  split. constructor. split. constructor.
  unfold normal_form. intros. unfold not. intros. destruct H0. destruct H0. inversion H0.
Qed.

Definition isValue {t:protoType} (p:protoExp t) : Prop :=
  match p with
  | ReturnC _ => True
  | _ => False
  end.

Theorem ex_isValue : isValue (ReturnC (basic 1)).
Proof.
  simpl. trivial.
Qed.

Ltac bool_destruct :=
  match goal with H: bool |- _ =>
                  destruct H
  end.

Theorem progress {t t':protoType} :
    forall (p1:protoExp t) (p2:protoExp t') st, 
    (Dual p1 p2) ->
    isValue p1 \/ (exists t''(p3:protoExp t'') st', step st _ _ _ p1 p2 p3 st').
Proof.
  intros p1 p2 st dualProof. destruct p1; destruct p2; inversion dualProof;
  (* Case:  p1 = SendC, p2 = ReceiveC *)
  (* Case:  p1 = ReceiveC, p2 = SendC *)
  (* Case:  p1 = ChoiceC, p2 = OfferC *)
  (* Case:  p1 = OfferC, p2 = ChoiceC *)                             
  try (right; 
       try (bool_destruct);
       subst; repeat (eexists); constructor).
  (* Case:  p1 = ReturnC, p2 = ReturnC *)
  left. simpl. trivial.
Qed.

Ltac steps_destruct :=
  match goal with H: step _ _ _ _ _ _ _ _ /\ _ |- _ =>
                  destruct H
  end.

Ltac step_destruct :=
  match goal with H: step _ _ _ _ _ _ _ _ |- _ =>
                  dep_destruct H; clear H
  end.
Theorem preservation {t t' p3t p4t : protoType} :
    forall (p1:protoExp t) (p2:protoExp t'), 
    (Dual p1 p2) -> 
    forall (p3:protoExp p3t) (p4:protoExp p4t) st st' st2 st2',
      step st _ _ _ p1 p2 p3 st' /\
      step st _ _ _ p1 p2 p3 st' /\
       step st2 _ _ _ p2 p1 p4 st2'
      -> (Dual p3 p4).
Proof.
  intros p1 p2 dualProof. destruct p1; destruct p2; inversion dualProof;
  intros; try (repeat steps_destruct); (repeat step_destruct); assumption.
Qed.

Lemma value_is_nf {t t':protoType} (p1:protoExp t) (p2:protoExp t') :
  (isValue p1) /\ (isValue p2) -> normal_form p1 p2.
Proof.
  intros.
  destruct p1; destruct p2;
  (cbv; intros; solve by inversion 3).
Qed.

Lemma nf_is_value {t t':protoType} (p1:protoExp t) (p2:protoExp t') : (Dual p1 p2) -> 
  normal_form p1 p2 -> (isValue p1) /\ (isValue p2).
Proof.
  unfold normal_form.
  intros D H.
  destruct p1; destruct p2; try (inversion D);
  try (try bool_destruct; destruct H with (st:=emptyState) (st':=emptyState);
       repeat eexists; subst; constructor).

  destruct H with (st:=emptyState) (st':=updateState m emptyState);
    eexists; subst; eexists; constructor.
  jauto.
Qed.

Corollary nf_same_as_value {t t':protoType} (p1:protoExp t) (p2:protoExp t')
  : (Dual p1 p2) -> normal_form p1 p2 <-> (isValue p1) /\ (isValue p2).
Proof. 
  intros. split.
  intros. apply nf_is_value in H0. assumption. assumption.
  intros. apply value_is_nf in H0. assumption.
Qed.