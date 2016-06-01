Require Import Crypto.
Require Import ProtoRep.
Require Import CpdtTactics.
(*Require Import Eqdep_dec.*)
Require Import Program.
Require Import SfLib.

Record State : Type := mkState
        {keys : list (message Key);
         basics : list (message Basic);
         (*kOb : ob Key;
         bOb : ob Basic *)
        }.

Definition emptyState := mkState nil nil.

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

Definition updateState{t:type} (m:message t) (sIn: State) : State :=
  match t with
  | Basic => mkState  sIn.(keys) (addMBasic t m sIn.(basics))
  | Key => mkState (addMKey t m sIn.(keys)) sIn.(basics)
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
            runProtoBigStep s _ _ _ (ReceiveC f) (SendC m p1') m' (updateState m' s)
                            
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


Definition hoare_triple{p1t p2t:protoType}{t:type}
           (P:Assertion) (p1:protoExp p1t) (p2:protoExp p2t) (Q:Assertion) : Prop :=
   forall st st' (m:message t),
     runProtoBigStep st _ _ _ p1 p2 m st' ->
     P st ->
     Q st'.


Inductive step : forall s (t r t':protoType),
    (protoExp t) -> (protoExp r) -> (protoExp t') -> State -> Prop :=
| ST_Send_Rec : forall x y  mt
                  (m:message mt) (p1':protoExp x)
                  (f:(message mt) -> protoExp y) s,
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
                     (r:protoExp rt) (r0:protoExp rt')
                     (s:protoExp st) (s0:protoExp st') stt,
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
  forall st st', ~ exists  t' (x:protoExp t'),  step st _ _ _ p1 p2 x st'.

Theorem nf_ex : normal_form (ReturnC (basic 0)) (ReturnC (basic 1)).
Proof.
 unfold normal_form. unfold not. intros. destruct H. destruct H. inversion H.
Qed.
                                                                          
Theorem normalizing{p1t p2t :protoType} :
  forall (p1:protoExp p1t) (p2:protoExp p2t),
    (Dual p1 p2) ->
    exists p3t p4t (p3:protoExp p3t) (p4:protoExp p4t) st st' st2 st2',
    (multi st _ _ _ p1 p2 p3 st') /\ (multi st2 _ _ _ p2 p1 p4 st2') /\ normal_form p3 p4.
Proof.
  intros. 

  generalize dependent p2t.
  dependent induction p1; destruct p2;
  try (intros H; inversion H).
  inversion H. subst.
  dep_destruct (IHp1 p'0 (p m)).
  inversion H. apply H4.
  destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.

  destruct H4.

  eexists. eexists. eexists. eexists. exists x4. exists x4. exists emptyState. eexists.
  split. subst. apply multi_step with (y:=p1) (y2:=(p m)) (st':=x4) (st2:=x6) (st2':=(updateState m x6)).

                constructor. constructor. Abort. (*apply H4.
                split. eapply multi_step with (y:=x3) (y2:=p1) (st':=updateState m x7).*) (*constructor.*)

 (*eapply ST_Rec_Send. constructor. constructor.
  

  eexists. eexists. eexists.
  
  split. subst. eapply multi_step. constructor. constructor. apply H0.
  split. eapply multi_step. constructor. constructor. eapply H4. apply H5.

  intros HH. inversion HH. subst.
  dep_destruct (H m p'0 p2).
  inversion HH. apply H2.

  destruct x. inversion HH. apply H3. destruct H2. destruct H2. destruct H2. destruct H2. destruct H3.
  eexists. eexists. eexists. eexists. split. eapply multi_step. constructor. constructor. apply H2.
  split.
  eapply multi_step. constructor. constructor. apply H3. apply H4.

  intros. inversion H0.
  intros. inversion H0.
  intros. inversion H0.
  intros. inversion H0.

  destruct b. dep_destruct (IHp1_1 r0 p2_1). apply H0. destruct x. apply H0. destruct H2. destruct H2. destruct H2. destruct H2. destruct H4.

  eexists. eexists. eexists. eexists. split. eapply multi_step. constructor. constructor. apply H2.
  split. eapply multi_step. constructor. constructor. apply H4. apply H5.

  dep_destruct (IHp1_2 s0 p2_2). apply H1. destruct x. apply H1. destruct H2. destruct H2. destruct H2. destruct H2. destruct H4.

  eexists. eexists. eexists. eexists. split. eapply multi_step. constructor. constructor. apply H2.
  split. eapply multi_step. constructor. constructor. apply H4. apply H5.

    destruct b. dep_destruct (IHp1_1 r0 p2_1). apply H0. destruct x. apply H0. destruct H2. destruct H2. destruct H2. destruct H2. destruct H4.

  eexists. eexists. eexists. eexists. split. eapply multi_step. constructor. constructor. apply H2.
  split. eapply multi_step. constructor. constructor. apply H4. apply H5.

  dep_destruct (IHp1_2 s0 p2_2). apply H1. destruct x. apply H1. destruct H2. destruct H2. destruct H2. destruct H2. destruct H4.

  eexists. eexists. eexists. eexists. split. eapply multi_step. constructor. constructor. apply H2.
  split. eapply multi_step. constructor. constructor. apply H4. apply H5.

  eexists. eexists. eexists. eexists. split. apply multi_refl.
  split. apply multi_refl. cbv. intros. destruct H0. destruct H0. inversion H0.
Qed.
*)

Definition isValue {t:protoType} (p:protoExp t) : Prop :=
  match p with
  | ReturnC _ => True
  | _ => False
  end.

Theorem ex_isValue : isValue (ReturnC (basic 1)).
Proof.
  simpl. trivial.
Qed.

Theorem strong_progress {t t':protoType} :
  forall (p1:protoExp t) (p2:protoExp t'),
    (Dual p1 p2) ->
    isValue p1 \/ (exists t'' (p3:protoExp t'') st st', step st _ _ _ p1 p2 p3 st').
Proof.
  intros. generalize dependent t'. induction p1; destruct p2; try (intros H; inversion H; contradiction).
  intros. inversion H. subst. right. exists p'. exists p1. exists emptyState. eexists. constructor.

  intros. inversion H0. subst. right. exists p'. exists (p m). exists emptyState. eexists. constructor.
  intros HH. inversion HH.
  intros HH. inversion HH.
  intros HH. inversion HH.
  intros HH. inversion HH.
  intros. destruct b; right.
  exists r. exists p1_1. exists emptyState. eexists. constructor.
  exists s. exists p1_2. exists emptyState. eexists. constructor.
  intros. destruct b; right.
  exists r. exists p1_1. exists emptyState. eexists. constructor.
  exists s. exists p1_2. exists emptyState. eexists. constructor.
  intros. left. simpl. trivial.
Qed.
  
Theorem bigstep_multistep {t t':protoType}{T:type} {p1:protoExp t} {p2:protoExp t'} : forall (m : message T) st st', runProtoBigStep st _ _ _ p1 p2 m st' ->
                         multi st _ _ _ p1 p2 (ReturnC m) st'.
Proof.
  intros.

  (* -> *)
  generalize dependent t'. dependent induction p1; destruct p2; try (intros H; inversion H; contradiction).
  intros H. dep_destruct H. eapply multi_step. constructor. constructor.
  apply IHp1. assumption.

  intros. dep_destruct H0. eapply multi_step. apply ST_Rec_Send. apply ST_Send_Rec. apply H. (*constructor.*) Abort.

  (*apply H

  specialize multi_step. intros H0. apply H0 with (r:=p') (y:=p1) (y2:=p m) (st':=s') (st2:=s) (st2':=s). constructor. constructor. apply IHp1. assumption.
  intros H0. dep_destruct H0. specialize multi_step. intros H1. apply H1 with (r:=p') (y:=p m0) (y2:=p2). constructor. constructor. apply H. assumption.

  intros HH. inversion HH.
  intros HH. inversion HH.
  intros HH. inversion HH.
  intros HH. inversion HH.
  intros H. dep_destruct H. apply multi_step with (r:=r) (y:=p1_1) (y2:=p2_1). constructor. constructor. apply IHp1_1. assumption.
  apply multi_step with (y:=p1_2) (y2:=p2_2). constructor. constructor. apply IHp1_2. assumption.
  
  intros H. dep_destruct H. apply multi_step with (y:=p1_1) (y2:=p2_1). constructor. constructor. apply IHp1_1. assumption. (*apply IHp1_1.*)
  apply multi_step with (y:=p1_2) (y2:=p2_2). constructor. constructor. apply IHp1_2. assumption.

  intros H. dep_destruct H. constructor.
Qed.
*)

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

Lemma value_is_nf {t t':protoType} (p1:protoExp t) (p2:protoExp t') :
  (isValue p1) /\ (isValue p2) -> normal_form p1 p2.
Proof.
  intros.
  destruct p1; destruct p2; try (solve by inversion 2).
  unfold normal_form. unfold not. intros. destruct H0. destruct H0. inversion H0.
Qed.

Lemma nf_is_value {t t':protoType} (p1:protoExp t) (p2:protoExp t') : (Dual p1 p2) -> 
  normal_form p1 p2 -> (isValue p1) /\ (isValue p2).
Proof.
  intros D H.
  destruct p1; destruct p2; try (inversion D).
  destruct H. eexists. eexists. subst. constructor.
  destruct H. exists p'. subst. exists (p m). constructor.
  destruct b.
  destruct H. exists r. exists p1_1. constructor.
  destruct H. exists s. exists p1_2. constructor.
  destruct b.
  destruct H. exists r. exists p1_1. constructor.
  destruct H. exists s. exists p1_2. constructor.
  
  simpl. split; trivial.
Qed.

Corollary nf_same_as_value {t t':protoType} (p1:protoExp t) (p2:protoExp t')
  : (Dual p1 p2) -> normal_form p1 p2 <-> (isValue p1) /\ (isValue p2).
Proof.
  intros. split.
  intros. apply nf_is_value in H0. assumption. assumption.
  intros. apply value_is_nf in H0. assumption.
Qed.

Theorem dualInnerR{t t':protoType} {p1:protoExp t} {p2:protoExp t'} :
    (Dual p1 p2) ->
    exists p3t (p3:protoExp p3t) p4t (p4:protoExp p4t),
      (step _ _ _ p1 p2 p3 /\
       step _ _ _ p2 p1 p4)
      -> (Dual p3 p4).
Proof.
  intros H. destruct p1; destruct p2; try (inversion H).
  exists p'. exists p1. exists p'0. subst. exists (p m). intros. assumption.
  exists p'. subst. exists (p m). exists p'0. exists p2. intros. assumption.
  exists r. exists p1_1. exists r0. exists p2_1. intros. assumption.
  exists r. exists p1_1. exists r0. exists p2_1. intros. assumption.
  exists (Eps t). exists (ReturnC m).  exists (Eps t). exists (ReturnC m).
  intros. destruct H0. dep_destruct H0.
Qed.
                                                                            
(* TODO:  check a choice/offer protocol in composition(Either type might 
          mess things up.  If so, do we really need returnType here??  Just put type as implicit param here *)
Inductive protocolComposition : Type :=
| protoEnd : protocolComposition
| protoComp {p1t p2t:protoType}{t:type} : (protoExp p1t) -> (protoExp p2t) -> 
    ((message t(*(returnType p1t)*)) -> protocolComposition) ->  
    protocolComposition.

Notation "x <- 'doProto' p1 p2 ; p" := (protoComp p1 p2 (fun x => p))
                                         (right associativity, at level 70, p1 ident, p2 ident).

Definition messageEq {t t':type} (m:message t) (m':message t') : Prop.
Proof.
  destruct (eq_type_dec t t').
  subst. exact (m = m').
  exact False.
Defined.

Definition isEnd (p:protocolComposition) : bool :=
  match p with
  | protoEnd => true
  | _ => false
  end.

Fixpoint biggerStep{t:type} (p:protocolComposition) (m:message t) : Prop :=
  match p with
  | protoEnd => False (* should never reach this case*)
  | protoComp p1 p2 f  =>
    exists m', runProtoBigStep _ _ _ p1 p2 m' /\
          if(isEnd (f m')) then messageEq m' m
          else biggerStep (f m') m
  end.

Fixpoint superMultiStep{t:type} (p:protocolComposition) (m:message t) : Prop :=
  match p with
  | protoEnd => False (* should never reach this case*)
  | protoComp p1 p2 f  =>
    exists m', multi _ _ _ p1 p2 (ReturnC m') /\
          if(isEnd (f m')) then messageEq m' m
          else superMultiStep (f m') m
  end.
