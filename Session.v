Require Export Crypto.

Inductive protoType : Type :=
| Send : type -> protoType -> protoType
| Receive : type -> protoType -> protoType
| Choice : protoType -> protoType -> protoType
| Offer : protoType -> protoType -> protoType  
| Eps : type -> protoType.

Inductive protoExp : type -> protoType -> Type :=
| SendC {t:type} {T:type} {p':protoType}  : (message t) -> (protoExp T p')
    -> protoExp T (Send t p')
| ReceiveC {t:type} {T:type} {p':protoType} : ((message t)->(protoExp T p'))     -> protoExp T  (Receive t p') 
| ChoiceC (b:bool) {r s:protoType} {R S:type} :(protoExp R r) -> (protoExp S s)
    -> (protoExp (if(b) then R else S) (Choice r s))
| OfferC {r s : protoType} {R S:type} : (protoExp R r) -> (protoExp S s)
                                        -> (protoExp (Either R S) (Offer r s))| ReturnC {t:type} : (message t) -> protoExp t (Eps t).

Notation "x :!: y" := (Send x y)
                        (at level 50, left associativity). 
Notation "x :!: y" := (protoExp (Send x y))
                        (at level 50, left associativity).

Notation "x :?: y" := (Receive x y)
                        (at level 50, left associativity).  
Notation "x :?: y" := (protoExp (Receive x y))
                        (at level 50, left associativity).

Notation "x :+: y" := (Choice x y)
                        (at level 50, left associativity).
Notation "x :+: y" := (protoExp (Choice x y))
                        (at level 50, left associativity).  

Notation "x :&: y" := (Offer x y)
                        (at level 50, left associativity).
Notation "x :&: y" := (protoExp (Offer x y))
                        (at level 50, left associativity). 

Notation "'send' n ; p" := (SendC n p)
                            (right associativity, at level 60).
Notation "x <- 'receive' ; p " := (ReceiveC (fun x => p)) 
                                    (right associativity, at level 60).

Notation "'offer'" := OfferC.

Notation "'choice'" := ChoiceC.

Definition EpsC := ReturnC (basic 0).

Fixpoint protoExpLength {T:type} {pt:protoType} (p: protoExp T pt) : nat :=
  match p with
  | SendC  _ p' => 1 + (protoExpLength p')
  | ReceiveC f => 1 + (protoExpLength (f (bad _)))
  | ChoiceC b p' p'' =>  max (protoExpLength p') (protoExpLength p'')
  | OfferC  p' p'' => max (protoExpLength p') (protoExpLength p'')
  | ReturnC _ => 1
  end.                                                               

Fixpoint DualT (t t':protoType) : Prop :=
  match t with
  | Send p1T p1' =>
    match t' with
    | Receive p2T p2' => (p1T = p2T) /\ (DualT p1' p2')    
    | _ => False
    end
  | Receive p1T p1' =>
    match t' with
    | Send p2T p2' => (p1T = p2T) /\ (DualT p1' p2')                                
    | _ => False
    end
  | Choice p1' p1'' =>
    match t' with
    | Offer p2' p2'' => (DualT p1' p2') /\ (DualT p1'' p2'')                                                             
    | _ => False
    end
  | Offer p1' p1'' =>
    match t' with
    | Choice p2' p2'' => (DualT p1' p2') /\ (DualT p1'' p2'')                                                               
    | _ => False
    end
  | Eps _ =>
    match t' with
    | Eps _ => True           
    | _ => False
    end
  end.

  (*repeat match goal with        
  (*| [ |- {DualT (?T _ _) (?T _ _)} + {~ DualT (?T _ _) (?T _ _)} ]
    => right; unfold not; trivial  *)
  | [ |- _ ] =>  right; unfold not; intros; inversion H; contradiction
  end. *)

Fixpoint DualT_dec (t t':protoType) : {DualT t t'} + {~ DualT t t'}.
Proof. 
  destruct t; destruct t';

  (* Eliminate all un-interesting cases *)
  try (right; unfold not; intros; inversion H; contradiction);

  (* For the Send/Receive, Receive/Send cases *)
  try (
  destruct (eq_type_dec t t1); destruct (DualT_dec t0 t');
  try (right; unfold not; intros; inversion H; contradiction);
  try (left; split; assumption)
  );

  (* For the Choice/Offer, Offer/Choice cases *)
  try (
  destruct (DualT_dec t1 t'1); destruct (DualT_dec t2 t'2);
  try (right; unfold not; intros; inversion H; contradiction);
  try( left; split; assumption)
    );

  (* Eps/Eps case *)
  left. simpl. trivial.
  
Defined.

Definition Dual {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') : Prop := DualT t t'.        

Fixpoint runProto' {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') 
  : (Dual p1 p2) -> (message T).
Proof. intros; destruct p1; destruct p2; try inversion H.

       subst. apply (runProto' _ _ _ _ p1 (p m) (*l*)(*(protoExpLength (p m))*)). assumption.
       subst. apply (runProto' _ _ _ _ (p m) p2 ). assumption.

       destruct b.
       apply (runProto' _ _ _ _ p1_1 p2_1 ). assumption.
       apply (runProto' _ _ _ _ p1_2 p2_2 ). assumption.
       
       destruct b.
       assert (message R).
       apply (runProto' _ _ _ _ p1_1 p2_1 ). assumption. exact (leither _ _ X).
       assert (message S).
       apply (runProto' _ _ _ _ p1_2 p2_2 ). assumption. exact (reither _ _ X).

       exact m.
Defined.

Fixpoint DualTSymm {t t':protoType} : DualT t t' -> DualT t' t.
Proof.
  intros. destruct t; destruct t'; try (inversion H); try (
  split;
  subst; trivial;
  apply (DualTSymm); assumption).
Defined.

Lemma DualSymm {t t':protoType} {T T':type} {p1:protoExp T t} {p2:protoExp T' t'} : (Dual p1 p2) -> (Dual p2 p1).
Proof.
  intros. unfold Dual in H. apply DualTSymm in H. assumption.
Defined.

Lemma notDualSymm {t t':protoType} {T T':type} {p1:protoExp T t} {p2:protoExp T' t'} : (~ Dual p1 p2) -> (~ Dual p2 p1).
Proof. 
  intros. unfold not. intros. apply DualTSymm in H0. unfold Dual in H. contradiction.
Defined.

Definition runProto {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') : (Dual p1 p2) -> (message T * message T') :=
  fun pf =>
    let x := runProto' p1 p2 pf in
    let y := runProto' p2 p1 (DualTSymm pf) in
    (x , y).

Definition nextType{T T':type} {t t':protoType} (p1:protoExp T t) (p2:protoExp T' t') : (Dual p1 p2) -> protoType.
  intros; destruct p1; destruct p2; try inversion H. exact p'. exact p'. destruct b. exact r. exact s. destruct b. exact r. exact s. exact (Eps t0).
Defined.

Definition nextRtype {T T':type} {t t':protoType} (p1:protoExp T t) (p2:protoExp T' t') : (Dual p1 p2) -> type.
  intros; destruct p1; destruct p2; try inversion H. exact T. exact T. destruct b. exact R. exact S. destruct b. exact R. exact S. exact t0.
Defined.

Definition runProto'OneStep {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') (p:Dual p1 p2) : (protoExp (nextRtype p1 p2 p) (nextType p1 p2 p)).
  destruct p1; destruct p2; try inversion p.
simpl. destruct p. exact p1.
simpl. destruct p. subst. exact (p0 m).
destruct b.
simpl. destruct p. exact p1_1.
simpl. destruct p. exact p1_2.
destruct b.
simpl. destruct p. exact p1_1.
simpl. destruct p. exact p1_2.
simpl. destruct p. exact (ReturnC m0).
Defined.

Definition runProtoOneStep {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') (p:Dual p1 p2) : ((protoExp (nextRtype p1 p2 p) (nextType p1 p2 p)) * (protoExp (nextRtype p2 p1 (DualSymm p)) (nextType p2 p1 (DualSymm p)) )) :=
  let x := (runProto'OneStep p1 p2 p) in
  let y := (runProto'OneStep p2 p1 (DualTSymm p)) in
  (x,y).    

Fixpoint runProtoMultiStep' {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') (n:nat) : (Dual p1 p2) -> (message T * message T').
  refine
  ( fun pf => 
    match n with
    | O => _
    | S n' => _
    end). destruct p1; destruct p2; try inversion pf.
  exact (bad T, bad T0).
  exact (bad T, bad T0).
  destruct b.
    exact (bad R, bad (Either R0 S0)).
    exact (bad S, bad (Either R0 S0)).
  destruct b.
    exact (bad (Either R S), bad R0).
    exact (bad (Either R S), bad S0).
  exact (m, m0).
  destruct (runProtoOneStep p1 p2 pf);
  destruct p1; destruct p2; try inversion pf;
  try
  (subst; destruct pf; cbv in p;  cbv in p0;  destruct (runProtoMultiStep' _ _ _ _ p p0 n' d); exact (m0, m1)).
  destruct b.
  destruct pf. cbv in p. cbv in p0. destruct (runProtoMultiStep' _ _ _ _ p p0 n' d). exact (m, leither _ _ m0).
  destruct pf. cbv in p. cbv in p0. destruct (runProtoMultiStep' _ _ _ _ p p0 n' d0). exact (m, reither _ _ m0).
  destruct b.
    destruct pf. cbv in p. cbv in p0. destruct (runProtoMultiStep' _ _ _ _ p p0 n' d). exact (leither _ _  m, m0).
    destruct pf. cbv in p. cbv in p0. destruct (runProtoMultiStep' _ _ _ _ p p0 n' d0). exact (reither _ _ m, m0).
    destruct pf. cbv in p. cbv in p0. assert (Dual p p0). reflexivity. destruct (runProtoMultiStep' _ _ _ _ p p0 n' H). exact (m2, m1). Defined.

Definition runProtoMultiStep {t t':protoType} {T T':type} (p1:protoExp T t) (p2:protoExp T' t') : (Dual p1 p2) -> (message T * message T') :=
  fun pf =>
  runProtoMultiStep' p1 p2 (max (protoExpLength p1) (protoExpLength p2)) pf.
                      
(*End session.*)