Require Import Crypto.
Require Import ProtoRep.
Require Import CpdtTactics.
Require Import Eqdep_dec.
Require Import Program.
Require Import SfLib.
Require Import Coq.Program.Equality.

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

Inductive runProtoBigStep : forall (s:State) (t t':protoType) (rt:type) (p1:protoExp t) (p2:protoExp t') (m:message rt), State -> Prop :=
  
| returnR : forall T T' (m:message T) (m':message T') s,
    runProtoBigStep s _ _ _ (ReturnC m) (ReturnC m') m s
                    
| sendR : forall X p1t p2t rt
            (p1':protoExp p1t)
            (f: ((message X) -> (protoExp p2t)))
            (m:message X) (m': message rt) s s',              
        runProtoBigStep s _ _ _ p1' (f m) m' s' ->
        runProtoBigStep s _ _ _ (SendC m p1') (ReceiveC f) m' s'
                        
| receiveR : forall X p1t p2t rt (m': message rt) (*TODO:  try p1t *)
            (m:message X)
            (f: ((message X) -> (protoExp p2t)))
            (p1':protoExp p1t) s s',
            runProtoBigStep s _ _ _ (f m) p1' m' s' ->
            runProtoBigStep s _ _ _ (ReceiveC f) (SendC m p1') m' (updateState m s')
                            
| choiceRt : forall rt rt' st st' mt (m:message mt)
               (r:protoExp rt) (r0:protoExp rt')
               (s:protoExp st) (s0:protoExp st') stt stt',
    runProtoBigStep stt _ _ _ r r0 m stt' ->
    runProtoBigStep stt _ _ _ (ChoiceC true r s) (OfferC r0 s0) m stt'

| choiceRf : forall rt rt' st st' mt (m':message mt) 
               (r:protoExp rt) (r0:protoExp rt')
               (s:protoExp st) (s0:protoExp st') stt stt',
    runProtoBigStep stt _ _ _ s s0 m' stt' -> 
    runProtoBigStep stt _ _ _ (ChoiceC false r s) (OfferC r0 s0) m' stt'

| offerRt : forall rt rt' st st' mt (m : message mt)
              (r:protoExp rt) (r0:protoExp rt')
              (s:protoExp st) (s0:protoExp st') stt stt',
    runProtoBigStep stt _ _ _ r r0 m stt' ->
    runProtoBigStep stt _ _ _ (OfferC r s) (ChoiceC true r0 s0) m stt'

| offerRf : forall rt rt' st st' mt (m' : message mt)
              (r:protoExp rt) (r0:protoExp rt')
              (s:protoExp st) (s0:protoExp st') stt stt',
    runProtoBigStep stt _ _ _ s s0 m' stt' ->
    runProtoBigStep stt _ _ _ (OfferC r s) (ChoiceC false r0 s0) m' stt'.

(*Inductive step : forall (stIn:State) (t r t':protoType),
    (protoExp t) -> (protoExp r) -> (protoExp t') -> State -> Prop :=
| ST_Send_Rec : forall p1t p2t  mt
                  (m:message mt) (p1:protoExp p1t)
                  (f:(message mt) -> protoExp p2t) (st:State),
    step st _ _ _ (SendC m p1) (ReceiveC f) p1 st
| ST_Rec_Send : forall p1t p2t mt (m:message mt) (p1:protoExp p1t)
                       (f:(message mt) -> protoExp p2t) (st:State),       
    step st _ _ _ (ReceiveC f) (SendC m p1) (f m) (updateState m st)
| ST_Choice_true : forall pt1 pt1' pt2 pt2'
                     (r:protoExp pt1) (r0:protoExp pt1')
                     (s:protoExp pt2) (s0:protoExp pt2') (st:State),
    step st _ _ _ (ChoiceC true r s) (OfferC r0 s0) r st
| ST_Choice_false : forall pt1 pt1' pt2 pt2'
                     (r:protoExp pt1) (r0:protoExp pt1')
                     (s:protoExp pt2) (s0:protoExp pt2') (st:State),
    step st _ _ _ (ChoiceC false r s) (OfferC r0 s0) s st
| ST_Offer_true : forall pt1 pt1' pt2 pt2'
                     (r:protoExp pt1) (r0:protoExp pt1')
                     (s:protoExp pt2) (s0:protoExp pt2') (st:State),
    step st _ _ _ (OfferC r0 s0) (ChoiceC true r s) r0 st
| ST_Offer_false : forall pt1 pt1' pt2 pt2'
                     (r:protoExp pt1) (r0:protoExp pt1')                     (s:protoExp pt2) (s0:protoExp pt2') (st:State),
    step st _ _ _ (OfferC r0 s0) (ChoiceC false r s) s0 st.

Notation "'stepe' st st'" := (step st _ _ _ st') (at level 50) *)

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

Notation "'stepe' st st'" := (step st _ _ _ st') (at level 50).

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

Axiom updateBothR :  forall t r (m:message t) (m':message r) x6 x7 p1t p2t (p1:protoExp p1t) (p2:protoExp p2t),
    runProtoBigStep x6 _ _ _ p1 p2 m' x7 -> 
    runProtoBigStep (updateState m x6) _ _ _ p1 p2 m' (updateState m x7).

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

(*
Theorem dualInnerR{t t':protoType} {p1:protoExp t} {p2:protoExp t'} :
    (Dual p1 p2) ->
    exists p3t (p3:protoExp p3t) p4t (p4:protoExp p4t), forall st st' st2 st2',
      (step st _ _ _ p1 p2 p3 st' /\
       step st2 _ _ _ p2 p1 p4 st2')
      -> (Dual p3 p4).
         
Theorem normalizing{p1t p2t :protoType} :
  forall (p1:protoExp p1t) (p2:protoExp p2t),
    (Dual p1 p2) ->
    exists p3t p4t (p3:protoExp p3t) (p4:protoExp p4t) st st' st2 st2',
    (multi st _ _ _ p1 p2 p3 st') /\ (multi st2 _ _ _ p2 p1 p4 st2') /\ normal_form p3 p4.
*)
Theorem progress {t t':protoType} :
    forall (p1:protoExp t) (p2:protoExp t'), 
    (Dual p1 p2) ->
    isValue p1 \/ (exists t''(p3:protoExp t'') st st', step st _ _ _ p1 p2 p3 st').
Proof.
  intros p1 p2 dualProof. destruct p1; destruct p2; inversion dualProof.
  (* Case:  p1 = SendC, p2 = ReceiveC *)
  right. subst.
    exists p'. exists p1. exists emptyState. eexists. constructor.
  (* Case:  p1 = ReceiveC, p2 = SendC *)
  right. subst.
    exists p'. exists (p m). exists emptyState. eexists. constructor.
  (* Case:  p1 = ChoiceC, p2 = OfferC *)
  right. destruct b.
    exists r. exists p1_1. exists emptyState. eexists. constructor.
    exists s. exists p1_2. exists emptyState. eexists. constructor.
  (* Case:  p1 = OfferC, p2 = ChoiceC *)
  right. destruct b.
    exists r. exists p1_1. exists emptyState. eexists. constructor.
    exists s. exists p1_2. exists emptyState. eexists. constructor.
  (* Case:  p1 = ReturnC, p2 = ReturnC *)
  left. simpl. trivial.
Qed.

Theorem preservation {t t' p3t p4t : protoType} :
    forall (p1:protoExp t) (p2:protoExp t'), 
    (Dual p1 p2) -> 
    forall (p3:protoExp p3t) (p4:protoExp p4t) st st' st2 st2',
      (step st _ _ _ p1 p2 p3 st' /\
       step st2 _ _ _ p2 p1 p4 st2')
      -> (Dual p3 p4).
Proof.
  intros p1 p2 dualProof. destruct p1; destruct p2; inversion dualProof;
  try (intros; destruct H1; dep_destruct H1; dep_destruct H2; assumption).
  intros. destruct H. inversion H.
Qed.
  
Theorem bigstep_multistep {t t':protoType}{T:type} {p1:protoExp t} {p2:protoExp t'} : forall (m : message T) st st', runProtoBigStep st _ _ _ p1 p2 m st' ->
                         multi st _ _ _ p1 p2 (ReturnC m) st'.
Proof.
  intros.

  (* -> *)
  generalize dependent t'. dependent induction p1; destruct p2; try (intros H; inversion H; contradiction).
  intros H. dep_destruct H. apply multi_step with (y:=p1) (y2:=p m) (st':=s) (st2:=s) (st2':=(updateState m s)). constructor. constructor.
  apply IHp1. assumption.

  intros H0. dep_destruct H0. apply multi_step with (y:= p m0) (y2:=p2) (st':=updateState m0 s) (st2:=s) (st2':=s). constructor. constructor.
  apply H. apply updateBothR. assumption.
  intros HH. inversion HH.
  intros HH. inversion HH.
  intros HH. inversion HH.
  intros HH. inversion HH.

  intros H. dep_destruct H. apply multi_step with (y:=p1_1) (y2:=p2_1) (st':=stt) (st2:=stt) (st2':=stt). constructor. constructor. apply IHp1_1. assumption.
  apply multi_step with (y:=p1_2) (y2:=p2_2) (st':=stt) (st2:=stt) (st2':=stt). constructor. constructor. apply IHp1_2. assumption.
  
  intros H. dep_destruct H. apply multi_step with (y:=p1_1) (y2:=p2_1) (st':=stt) (st2:=stt) (st2':=stt). constructor. constructor. apply IHp1_1. assumption. (*apply IHp1_1.*)
  apply multi_step with (y:=p1_2) (y2:=p2_2) (st':=stt) (st2:=stt) (st2':=stt). constructor. constructor. apply IHp1_2. assumption.

  intros H. dep_destruct H. constructor.
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
  destruct p1; destruct p2; try (inversion D).
  destruct H with (st:=emptyState) (st':=emptyState). eexists. eexists. subst. constructor.
  destruct H with (st:=emptyState) (st':=updateState m emptyState). exists p'. subst. exists (p m). constructor.
  destruct b.
  destruct H with (st:=emptyState) (st':=emptyState). exists r. exists p1_1. constructor.
  destruct H with (st:=emptyState) (st':=emptyState). exists s. exists p1_2. constructor.
  destruct b.
  destruct H with (st:=emptyState) (st':=emptyState). exists r. exists p1_1. constructor.
  destruct H with (st:=emptyState) (st':=emptyState). exists s. exists p1_2. constructor.
  
  simpl. split; trivial.
Qed.

Corollary nf_same_as_value {t t':protoType} (p1:protoExp t) (p2:protoExp t')
  : (Dual p1 p2) -> normal_form p1 p2 <-> (isValue p1) /\ (isValue p2).
Proof.
  intros. split.
  intros. apply nf_is_value in H0. assumption. assumption.
  intros. apply value_is_nf in H0. assumption.
Qed.

Definition messageEq {t t':type} (m:message t) (m':message t') : Prop.
Proof.
  destruct (eq_type_dec t t').
  subst. exact (m = m').
  exact False.
Defined.




(*
Definition addMp(xxx:type) mt (p:((message mt)*(list (message Key)))) : (ob xxx) -> (ob xxx) := fun l => (
  match mt as t' return (mt = t') -> (ob xxx) with
  | xxx => fun pf => (addP _ _ pf p l)
  | _ => fun _ => l
  end (eq_refl mt)).
 *)





Definition encData := (basic 1).
Definition oneEnc{mt:type} (m:message mt) := encrypt _ m (public 0).
Definition twoEnc{mt:type} (m:message (Encrypt mt)) := encrypt _ m (public 1).
Definition triEncrypt{mt:type} (m:message mt) := encrypt _ (twoEnc (oneEnc m)) (public 2).

Eval compute in obligations (basic 0).

Eval compute in triEncrypt encData.
Eval compute in triEncrypt (basic 2).

Eval compute in obligations (triEncrypt (basic 1)).
Eval compute in obligations (pair _ _ (triEncrypt (basic 1)) (triEncrypt (basic 2))).

Check eq_key_dec.

Fixpoint m_eq {t t':type} (m:message t) (m':message t') : bool :=
    match m with
    | basic n => match m' with
                | basic n' => if (beq_nat n n') then true
                             else false
                | _ => false
                end
    | key kt => match m' with
               | key kt' => match kt with
                           | symmetric s0 => match kt' with
                                            | symmetric s0' => beq_nat s0 s0'
                                            | _ => false
                                            end           
                           | private p0 => match kt' with
                                          | private p0' => beq_nat p0 p0'
                                          | _ => false
                                          end             
                           | public pu0 => match kt' with
                                          | public pu0' => beq_nat pu0 pu0'
                                          | _ => false
                                          end
                           end                             
               | _ => false
               end
    | encrypt _ em _ => match m' with
                       | encrypt _ em' _ => m_eq em em'
                       | _ => false
                       end
    | hash _ hm => match m' with
                  | hash _ hm' => m_eq hm hm'
                  | _ => false
                  end
    | pair _ _ m1 m2 => match m' with
                       | pair _ _ m1' m2' => andb (m_eq m1 m1') (m_eq m2 m2')
                       | _ => false
                       end
    | leither _ _ em => match m' with
                       | leither _ _ em' => m_eq em em'
                       | _ => false
                       end
    | reither _ _ em => match m' with
                       | reither _ _ em' => m_eq em em'
                       | _ => false
                       end
    | bad _ => false
    end.

Eval compute in m_eq (key (public 0)) (key (public 1)).
Eval compute in m_eq (key (public 0)) (basic 0).

                        

(*Fixpoint my_remove {t:type} (m:message t) (l:list (message t)) : list (message t) :=
  match l with
  | [] => l
  | h :: t => if (m_eq m h) then my_remove m t
             else h :: (my_remove m t)
  end.
 *)

Fixpoint my_removeK (m:message Key) (l:list (message Key)) : list (message Key) :=
  match l with
  | [] => l
  | h :: t => if (m_eq m h) then my_removeK m t
             else h :: (my_removeK m t)
  end.

Fixpoint my_in {t:type} (m:message t) (l:list (message t)) : bool :=
  match l with
  | [] => false
  | h :: t => if (m_eq m h) then true
             else my_in m t
  end. 

Fixpoint my_inB (m:message Basic) (l:list (message Basic)) : bool :=
  match l with
  | [] => false
  | h :: t => if (m_eq m h) then true
             else my_inB m t
  end.

Fixpoint my_inK (m:message Key) (l:list (message Key)) : bool :=
  match l with
  | [] => false
  | h :: t => if (m_eq m h) then true
             else my_inK m t
  end.

Definition kList := [(key (public 0)); (key (private 0))].
Eval compute in my_removeK (key (private 0)) kList.

Definition empty {t:type} (l:list (message t)) : bool :=
  beq_nat 0 (length l).

Fixpoint ob_remove (m:message Key) (obIn:ob Key) : ob Key :=
  match obIn with
  | [] => obIn
  | h :: t => if (m_eq m (fst h)) then ob_remove m t
             else h :: (ob_remove m t)
  end.

Fixpoint ob_removeB (m:message Basic) (obIn:ob Basic) : ob Basic :=
  match obIn with
  | [] => obIn
  | h :: t => if (m_eq m (fst h)) then ob_removeB m t
             else h :: (ob_removeB m t)
  end.


(*Definition ob (t:type) := list ((message t) * (list (message Key))).

Record State : Type := mkState
        {keys : list (message Key);
         basics : list (message Basic);
         kOb : ob Key;
         bOb : ob Basic 
        }.
 *)

Fixpoint updateObs (k:message Key) (obK:ob Key) : (ob Key) :=
  match obK with
  | [] => obK
  | h :: t => let obs := (snd h) in
             if (my_inK k obs) then 
               let newObs := my_removeK k obs in
               let newH := ((fst h), newObs) in
               newH :: (updateObs k t)
             else h :: (updateObs k t)
  end.

Fixpoint updateObsB (k:message Key) (obB:ob Basic) : (ob Basic) :=
  match obB with
  | [] => obB
  | h :: t => let obs := (snd h) in
             if (my_inK k obs) then 
               let newObs := my_removeK k obs in
               let newH := ((fst h), newObs) in
               newH :: (updateObsB k t)
             else h :: (updateObsB k t)
  end.

Fixpoint getReleasedKeys' (obK:ob Key) (l:list (message Key)) : list (message Key) :=
  match obK with
  | [] => l
  | h :: t => let obs := (snd h) in
             if (empty obs) then
               getReleasedKeys' t (l++[(fst h)])
             else
               getReleasedKeys' t l
  end.

Definition getReleasedKeys (obK:ob Key) : list (message Key) :=
  getReleasedKeys' obK [].

Fixpoint getReleasedBasics' (obB:ob Basic) (l:list (message Basic)) : list (message Basic) :=
  match obB with
  | [] => l
  | h :: t => let obs := (snd h) in
             if (empty obs) then
               getReleasedBasics' t (l++[(fst h)])
             else
               getReleasedBasics' t l
  end.

Definition getReleasedBasics (obB:ob Basic) : list (message Basic) :=
  getReleasedBasics' obB [].

Fixpoint cleanOb (releasedKeys:list (message Key)) (obK:ob Key) : ob Key :=
  match releasedKeys with
  | [] => obK
  | h :: t => cleanOb t (ob_remove h obK)
  end.

Fixpoint cleanObB (releasedKeys:list (message Basic)) (obB:ob Basic) : ob Basic :=
  match releasedKeys with
  | [] => obB
  | h :: t => cleanObB t (ob_removeB h obB)
  end.
    
Definition normObk (k:message Key) (obK:ob Key) :
  ((ob Key)*(list (message Key))) :=
  let newObk := updateObs k obK in
  let releasedKeys := getReleasedKeys newObk in
  let cleanedNewObk := cleanOb releasedKeys newObk in
  (cleanedNewObk, releasedKeys).

Definition normObB (k:message Key) (obB:ob Basic) :
  ((ob Basic)*(list (message Basic))) :=
  let newObB := updateObsB k obB in
  let releasedBasics := getReleasedBasics newObB in
  let cleanedNewObB := cleanObB releasedBasics newObB in
  (cleanedNewObB, releasedBasics).

Fixpoint normState' (lIn:list (message Key)) (obk:ob Key)
         (newl:list (message Key)) :
  ((list (message Key)) * (ob Key)) :=
  match lIn with
  | [] => (newl, obk)
  | h :: t => let once := normObk h obk in
             let newOb := fst once in
             let newRel := snd once in
             normState' t newOb (newl ++ newRel)
  end.

Fixpoint normStateB' (lIn:list (message Key)) (obB:ob Basic)
         (newl:list (message Basic)) :
  ((list (message Basic)) * (ob Basic)) :=
  match lIn with
  | [] => (newl, obB)
  | h :: t => let once := normObB h obB in
             let newOb := fst once in
             let newRel := snd once in
             normStateB' t newOb (newl ++ newRel)
  end.

Definition normState (lIn:list (message Key)) (obk:ob Key) :
  ((list (message Key)) * (ob Key)) :=
  normState' lIn obk [].

Definition normStateB (lIn:list (message Key)) (obB:ob Basic) :
  ((list (message Basic)) * (ob Basic)) :=
  normStateB' lIn obB [].
    
Fixpoint normStateMulti' (lIn:list (message Key)) (obk:ob Key) (n:nat) :
  ((list (message Key)) * (ob Key)) :=
  match n with
  | O => (lIn, obk)
  | S n' => 
    let onePass := normState lIn obk in
    normStateMulti' (lIn ++ (fst onePass)) (snd onePass) n'
  end.

Fixpoint normStateMultiB' (lIn:list (message Key))
         (bIn:list (message Basic)) (obB:ob Basic) (n:nat) :
  ((list (message Basic)) * (ob Basic)) :=
  match n with
  | O => (bIn, obB)
  | S n' => 
    let onePass := normStateB lIn obB in
    normStateMultiB' lIn (bIn ++ (fst onePass)) (snd onePass) n'
  end.

Definition normStateMulti (lIn:list (message Key)) (obk:ob Key) :
  ((list (message Key)) * (ob Key)) :=
  normStateMulti' lIn obk 5.

Definition normStateMultiB (lIn:list (message Key))
           (bIn:list (message Basic)) (obB:ob Basic) :
  ((list (message Basic)) * (ob Basic)) :=
  normStateMultiB' lIn bIn obB 5.

Print oneEnc.

Definition obEx := obligations (pair _ _ (oneEnc (basic 1)) (triEncrypt (basic 2))).
Eval compute in obEx.

Definition obEx' := obligations (encrypt _ (pair _ _ (basic 3) (key (public 2))) (public 33)).
Definition obEx'K := obligationsK (encrypt _ (pair _ _ (basic 3) (key (public 2))) (public 33)).

Definition obExK := obligationsK (pair _ _ (oneEnc (key (public 33))) (triEncrypt (key (public 22)))).
Eval compute in obExK.

Eval compute in normState [(key (public 0))] obExK.
Eval compute in normStateMulti [(key (public 0)); (key (public 2))] obExK.

Definition newState (s:State) : State :=
  let oldKeys := s.(keys) in
  let oldKeyObs := s.(kOb) in
  let oldBasics := s.(basics) in
  let oldBasicObs := s.(bOb) in
  let keyNormResult := normStateMulti oldKeys oldKeyObs in
  let newKeys := fst keyNormResult in
  let newKeyObs := snd keyNormResult in
  let basicNormResult := normStateMultiB newKeys oldBasics oldBasicObs in
  let newBasics := fst basicNormResult in
  let newBasicObs := snd basicNormResult in
  mkState newKeys newBasics newKeyObs newBasicObs.


Definition st1 := mkState [(key (public 0))] [] obExK obEx.
Eval compute in st1.

Eval compute in newState st1.

Definition st2 := mkState [(key (public 0))] [] (obExK ++ obEx'K) (obEx' ++ obEx).

Eval compute in newState st2.



(*
Fixpoint biggerStep{t:type} (p:protocolComposition) (m:message t) : Prop :=
  match p with
  | protoEnd => False (* should never reach this case*)
  | protoComp p1 p2 f  =>
    exists m', runProtoBigStep _ _ _ p1 p2 m' /\
          if(isEnd (f m')) then messageEq m' m
          else biggerStep (f m') m
  end.

*)






(*
Definition unWrapRet{mt:type} (p:protoExp (Eps mt)) : message mt.
Proof.
  inversion p.
  assumption.
Defined.

Lemma unWrapRetLemma {mt:type} : forall (p1v:protoExp (Eps mt)), p1v = ReturnC (unWrapRet p1v).
Proof.
  intros. dep_destruct p1v. cbv. reflexivity.
Qed.

Definition nf_of {p1t p2t t t':protoType} (p1:protoExp p1t) (p2:protoExp p2t)(res1 : protoExp t)(res2 : protoExp t') :=
  (multi _ _ _ p1 p2 res1) /\ (multi _ _ _ p2 p1 res2) /\ normal_form res1 res2.
                                                        
Theorem multistep_bigstep {p1t p2t:protoType}{mt mt':type} {p1:protoExp p1t} {p2:protoExp p2t} :
  forall p1v p2v,
    nf_of p1 p2 p1v p2v ->
    exists (m:message mt) (m':message mt'),
      (p1v = (ReturnC m)) /\ (p2v = (ReturnC m')) /\ 
      runProtoBigStep _ _ _ p1 p2 m.

  (* <- *)
      intros. unfold nf_of in H. destruct H. destruct H0. remember (unWrapRet p1v) as XX eqn:XXX. exists (XX). remember (unWrapRet p2v) as XX' eqn:XXX'. exists (XX'). split. subst. apply unWrapRetLemma. split. subst. apply unWrapRetLemma.

      generalize dependent p2t. dependent induction p1; destruct p2;
      try (intros H; dep_destruct H; solve by inversion 1).

      intros H H'. dep_destruct H. dep_destruct s0. dep_destruct s1. constructor. eapply IHp1 with (p1v := p1v) (p2v:=p2v). assumption. reflexivity. reflexivity. assumption. dep_destruct H'. dep_destruct s2. dep_destruct s3. assumption.
      intros H' H''. dep_destruct H'. dep_destruct s0. dep_destruct s1. constructor. eapply H with (p1v:=p1v) (p2v:=p2v). assumption. reflexivity. reflexivity. assumption. dep_destruct H''. dep_destruct s2. dep_destruct s3. assumption.

      intros. solve by inversion 2.
      intros. solve by inversion 2.
      intros. solve by inversion 2.
      intros. solve by inversion 2.
      intros. destruct b. dep_destruct H. dep_destruct H0. eapply choiceRt. eapply IHp1_1. apply H1. subst. reflexivity. reflexivity. dep_destruct s2. dep_destruct s3. assumption. dep_destruct s4. dep_destruct s5. assumption.
      apply choiceRf. 

      eapply IHp1_2. apply H1. subst. reflexivity. reflexivity. dep_destruct H. dep_destruct s2. dep_destruct s3. assumption. dep_destruct H0. dep_destruct s2. dep_destruct s3. assumption.

      intros. destruct b. dep_destruct H. dep_destruct H0. eapply offerRt. eapply IHp1_1. apply H1. subst. reflexivity. reflexivity. dep_destruct s2. dep_destruct s3. assumption. dep_destruct s4. dep_destruct s5. assumption.
      apply offerRf. eapply IHp1_2. apply H1. subst. reflexivity. reflexivity. dep_destruct H. dep_destruct s2. dep_destruct s3. assumption. dep_destruct H0. dep_destruct s2. dep_destruct s3. assumption.

      intros. solve by inversion 2.
      intros. solve by inversion 2.
      intros. solve by inversion 2.
      intros. solve by inversion 2.
      intros. dep_destruct H. constructor. dep_destruct s0.
Qed.

*)