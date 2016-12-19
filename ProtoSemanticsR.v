Require Import Crypto.
Require Import ProtoRep.
Require Import CpdtTactics.
Require Import Eqdep_dec.
Require Import Program.
Require Import Coq.Program.Equality.
Require Import SfLib.
(*Require Import State.*)

Definition State := nat.
Definition updateState{t:type} (m:message t) (s:State) := s.

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


Inductive DualTR : protoType -> protoType -> Type :=
| senRecTR: forall (t t':protoType)(mt mt':type), (DualTR t t')
                                        -> (mt = mt')
                                        -> DualTR (Send mt t)
                                                 (Receive mt' t')
| recSenTR: forall (t t':protoType)(mt mt':type), (DualTR t' t)
                                        -> (mt = mt')
                                        -> DualTR  (Receive mt' t') 
                                                  (Send mt t)           
| choOffTR : forall (r s r' s':protoType), (DualTR r r')
                                -> (DualTR s s')
                                -> DualTR (Choice r s)
                                         (Offer r' s')
| offChoTR : forall (r s r' s':protoType), (DualTR r r')
                                -> (DualTR s s')
                                -> DualTR (Offer r' s')
                                         (Choice r s)   
| retTR : forall (mt mt':type), DualTR (Eps mt)
                                 (Eps mt').

Inductive DualR {t t':protoType} (p1:protoExp t) (p2:protoExp t') : Type :=
| isDualR : (DualTR t t') -> DualR p1 p2.

Definition innerProtoType {t t':protoType}
           (p1:protoExp t) (p2:protoExp t') (pf:DualR p1 p2) : protoType.
Proof.
  dep_destruct p1; dep_destruct p2; inversion pf; inversion H; subst.
  exact p'.
  exact p'.
  destruct b. exact r.
  exact s.
  destruct b. exact r.
  exact s.
  exact (Eps t).
Defined.

Theorem dualSym {t t':protoType} : (DualTR t t') -> (DualTR t' t).
Proof.
  dependent induction t; dep_destruct t'; intros H; inversion H; subst.
  constructor. apply IHt in H3. assumption. reflexivity.
  constructor. apply IHt in H3. assumption. reflexivity.
  constructor; assumption.
  constructor; assumption.
  constructor.
Defined.

Inductive protocol : Prop :=
| senRec : forall (t t':protoType) (mt:type), (DualTR (Send mt t) (Receive mt t')) -> 
                                      (protoExp (Send mt t)) ->
                                      (protoExp (Receive mt t')) ->
                                      protocol
| choOff : forall (r s r' s':protoType), (DualTR (Choice r s) (Offer r' s')) ->
                                    (protoExp (Choice r s)) ->
                                    (protoExp (Offer r' s')) ->
                                    protocol
| ret : forall (mt mt':type), (DualTR (Eps mt) (Eps mt')) ->
                          (protoExp (Eps mt)) ->
                          (protoExp (Eps mt')) ->
                          protocol.

Definition groupProto {t t':protoType}
           (p1:protoExp t) (p2:protoExp t') (pf:DualR p1 p2) : protocol.
Proof.
  dep_destruct p1; dep_destruct p2; inversion pf; inversion H; subst.
  apply (senRec p' p'0 t0); assumption.
  apply (senRec p'0 p' t); try (apply dualSym); assumption.
  apply (choOff r s r0 s0); assumption.
  apply (choOff r0 s0 r s); try constructor; assumption.
  apply (ret t t0); assumption.
Defined.

Definition oneStep (p:protocol) : protocol.
Proof.
  destruct p.
  dep_destruct t; dep_destruct t'; inversion H; inversion H3; subst.
  apply (senRec x x0 t1). assumption. dep_destruct X. assumption. dep_destruct X0. dep_destruct X. exact (p m).
  apply (senRec x0 x t0). constructor. apply dualSym. assumption. reflexivity. dep_destruct X0. dep_destruct X. exact (p m). dep_destruct X. assumption.
  apply (choOff x1 x2 x3 x4). assumption. dep_destruct H. dep_destruct X. assumption. dep_destruct X0. dep_destruct X. exact (p m).
  apply (choOff x3 x4 x1 x2). constructor. assumption. assumption. dep_destruct X0. dep_destruct X. exact (p m). dep_destruct X. assumption.
  apply (ret t0 t1). assumption. dep_destruct X. assumption. dep_destruct X0. dep_destruct X. exact (p m).
  dep_destruct r; dep_destruct r'; try solve by inversion 2.
  apply (choOff x s x0 s'). inversion H. subst. constructor. inversion H3. assumption. assumption. dep_destruct X. destruct b. Abort.


                                    
Fixpoint retType (p:protocol) : type.
Proof.
  exact (retType 



Fixpoint innerProto {t t':protoType}
         (p1:protoExp t) (p2:protoExp t') (pf:Dual p1 p2) : (protoExp (innerProtoType p1 p2 pf)).
Proof.
  generalize dependent p2. 
  dependent induction p1; destruct p2; inversion pf; inversion H.
  subst. dep_destruct pf. dep_destruct d. simpl.
  assert ((innerProtoType (send m; p1) (x <- receive ; p x) pf) = p').
  dep_destruct pf. dep_destruct d1. simpl. reflexivity.
  rewrite <- H0.
  exact (IHp1 (ReceiveC p) pf).

    subst. dep_destruct pf. dep_destruct d. simpl.
  assert ((innerProtoType (x <- receive ; p x) (send m; p2) pf) = p').
  dep_destruct pf. dep_destruct d1. simpl. reflexivity.
  rewrite <- H0.
  exact (innerProto _ _ (ReceiveC p) (send m; p2) pf).

  destruct b. dep_destruct pf. dep_destruct d. simpl.
  exact p1_1.
  dep_destruct pf. dep_destruct d. simpl.
  exact p1_2.

  destruct b. dep_destruct pf. dep_destruct d. simpl.
  exact p1_1.
  dep_destruct pf. dep_destruct d. simpl.
  exact p1_2.
  
  dep_destruct pf. dep_destruct d. simpl.
  exact (ReturnC m).
Defined.




  
  
Fixpoint retType {t t':protoType}
         (p1:protoExp t) (p2:protoExp t') (pf:Dual p1 p2) : type.
Proof.
  dep_destruct p1; dep_destruct p2; inversion pf; inversion H.
  subst. inversion H.  assert (Dual x (p m)). constructor. assumption.
    exact (retType _ _ (x) (p m) H3).
    subst. inversion H. clear H0. assert (Dual (p m) x). constructor. assumption. exact (retType _ _ (p m) x H0).
    destruct b. assert (Dual x1 x3). constructor. assumption.
    exact (retType _ _ x1 x3 H2).
    assert (Dual x2 x4). constructor. assumption.
    exact (retType _ _ x2 x4 H2).
    destruct b. assert (Dual x1 x3). constructor. assumption.
    exact (retType _ _ x1 x3 H2).
    assert (Dual x2 x4). constructor. assumption.
    exact (retType _ _ x2 x4 H2).
    exact t. 
Defined.




Fixpoint eval {t t':protoType} (p1:protoExp t) (p2:protoExp t') (pf:Dual p1 p2) : message (retType p1 p2 pf).
Proof.
  dep_destruct p1; dep_destruct p2; inversion pf; inversion H.
  subst. inversion H. clear H0. assert (Dual x (p m)). constructor. assumption.
  exact (eval _ _ x (p m) H0).
                                                                             


(*Notation "'multie' st st'" := (multi st _ _ _ st')
                                (at level 50). *)

(*

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

Theorem progress {t t':protoType} :
    forall (p1:protoExp t) (p2:protoExp t') st, 
    (Dual p1 p2) ->
    isValue p1 \/ (exists t''(p3:protoExp t'') st', step st _ _ _ p1 p2 p3 st').
Proof.
  intros p1 p2 st dualProof. destruct p1; destruct p2; inversion dualProof.
  (* Case:  p1 = SendC, p2 = ReceiveC *)
  right. subst.
    exists p'. exists p1. eexists. constructor.
  (* Case:  p1 = ReceiveC, p2 = SendC *)
  right. subst.
    exists p'. exists (p m). eexists. constructor.
  (* Case:  p1 = ChoiceC, p2 = OfferC *)
  right. destruct b.
    exists r. exists p1_1. eexists. constructor.
    exists s. exists p1_2. eexists. constructor.
  (* Case:  p1 = OfferC, p2 = ChoiceC *)
  right. destruct b.
    exists r. exists p1_1. eexists. constructor.
    exists s. exists p1_2. eexists. constructor.
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

*)