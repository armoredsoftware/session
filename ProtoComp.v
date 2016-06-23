Require Import Crypto.
Require Import ProtoRep.
Require Import ProtoStateSemantics.


Definition hoare_triple{p1t p2t p3t:protoType}{t:type}
           (P:Assertion)
           (p1:protoExp p1t) (p2:protoExp p2t) (p3:protoExp p3t)
           (Q:Assertion) : Prop :=
   forall st st',
     multi st _ _ _ p1 p2 p3 st' ->
     P st ->
     Q st'.

(* TODO:  check a choice/offer protocol in composition(Either type might 
          mess things up.  If so, do we really need returnType here??  Just put type as implicit param here *)
Inductive protocolComposition : Type :=
| protoEnd : protocolComposition
| protoComp {p1t p2t:protoType}(*{t:type}*) : (protoExp p1t) -> (protoExp p2t) -> 
    ((*message t*)message (returnType p1t) -> protocolComposition) ->  
    protocolComposition.

Notation "x <- 'doProto' p1 p2 ; p" := (protoComp p1 p2 (fun x => p))
                                         (right associativity, at level 70, p1 ident, p2 ident).

Definition isEnd (p:protocolComposition) : bool :=
  match p with
  | protoEnd => true
  | _ => false
  end.

Fixpoint superMultiStep{t:type} (p:protocolComposition) (m:message t) (st:State) (st':State) : Prop :=
  match p with
  | protoEnd => False (* should never reach this case*)
  | protoComp p1 p2 f  =>
    exists m' stI, multi st _ _ _ p1 p2 (ReturnC m') stI /\
          if(isEnd (f m')) then messageEq m' m /\ (stI = st')
          else superMultiStep (f m') m stI st'
  end.

Definition incPayload (m:message Basic) : (message Basic) :=
  match m with
  | basic n => basic (n + 1)
  | _ => basic 0                 
  end.

Definition proto1 :=
  x <- receive;
  let y := (incPayload x) in
  send y;
    ReturnC y.

Definition other (m:message Basic) :=
  send m;
  x <- receive;
  ReturnC (t:=Basic) x.

Definition proto2 :=
  x <- receive;
  let y := incPayload (incPayload x) in
  send y;
  ReturnC y.

Definition payload := (basic 0).
Definition p1s := (other payload).
                                    
Definition client :=
  x <- doProto p1s proto1;
  let ox := (other x) in
  y <- doProto ox proto1;
  protoEnd.

Example clientEval : exists st', superMultiStep client (basic 2) emptyState st'.
Proof.
  eexists.
  simpl.
  exists (basic 1). exists (updateState (basic 1) emptyState).

  split.
  unfold p1s. unfold proto1. unfold other. unfold payload.
  apply multi_step with (y:=(x <- receive; ReturnC (t:=Basic) x)) (y2:=(send incPayload (basic 0); ReturnC (incPayload (basic 0)))) (st':=emptyState) (st2:=emptyState) (st2':= (updateState (basic 0) emptyState)). constructor. constructor. unfold incPayload.
  apply multi_step with (y:= (ReturnC (basic 1))) (y2:=(ReturnC (basic 1))) (st':= updateState (basic 1) emptyState) (st2:= (updateState (basic 0) emptyState)) (st2':= (updateState (basic 0) emptyState)). constructor. constructor.
  apply multi_refl.

  exists (basic 2). unfold proto1. unfold other. exists (updateState (basic 2) (updateState (basic 1) emptyState)).
  
  split.
  apply multi_step with (y:=(x <- receive; ReturnC (t:=Basic) x)) (y2:=(send incPayload (basic 1); ReturnC (incPayload (basic 1)))) (st':=(updateState (basic 1) emptyState)) (st2:= (updateState (basic 0) emptyState)) (st2':= updateState (basic 1) (updateState (basic 0) emptyState)). constructor. constructor.
  apply multi_step with (y:=(ReturnC (basic 2))) (y2:=(ReturnC (basic 2))) (st':= (updateState (basic 2) (updateState (basic 1) emptyState))) (st2:= (updateState (basic 1) (updateState (basic 0) emptyState))) (st2':= updateState (basic 1) (updateState (basic 0) emptyState)). constructor. constructor. constructor.
  split. cbv. reflexivity. reflexivity.
Qed. Print clientEval.


Example clientEval2 : superMultiStep client (basic 2) emptyState (updateState (basic 2) (updateState (basic 1) emptyState)).
Proof.
  simpl.
  exists (basic 1). exists (updateState (basic 1) emptyState).

  split.
  unfold p1s. unfold proto1. unfold other. unfold payload.
  apply multi_step with (y:=(x <- receive; ReturnC (t:=Basic) x)) (y2:=(send incPayload (basic 0); ReturnC (incPayload (basic 0)))) (st':=emptyState) (st2:=emptyState) (st2':= (updateState (basic 0) emptyState)). constructor. constructor. unfold incPayload.
  apply multi_step with (y:= (ReturnC (basic 1))) (y2:=(ReturnC (basic 1))) (st':= updateState (basic 1) emptyState) (st2:= (updateState (basic 0) emptyState)) (st2':= (updateState (basic 0) emptyState)). constructor. constructor.
  apply multi_refl.

  exists (basic 2). unfold proto1. unfold other. exists (updateState (basic 2) (updateState (basic 1) emptyState)).
  
  split.
  apply multi_step with (y:=(x <- receive; ReturnC (t:=Basic) x)) (y2:=(send incPayload (basic 1); ReturnC (incPayload (basic 1)))) (st':=(updateState (basic 1) emptyState)) (st2:= (updateState (basic 0) emptyState)) (st2':= updateState (basic 1) (updateState (basic 0) emptyState)). constructor. constructor.
  apply multi_step with (y:=(ReturnC (basic 2))) (y2:=(ReturnC (basic 2))) (st':= (updateState (basic 2) (updateState (basic 1) emptyState))) (st2:= (updateState (basic 1) (updateState (basic 0) emptyState))) (st2':= updateState (basic 1) (updateState (basic 0) emptyState)). constructor. constructor. constructor.
  split. cbv. reflexivity. reflexivity.
Qed.

