Inductive maybe {A : Set} (P : A -> Prop) : Set :=
| Unknown : maybe P
| Found : forall x:A, P x -> maybe P.

Notation "{{ x | P }}" := (maybe (fun x => P)).
Notation "??" := (Unknown _).
Notation "[| x |]" := (Found _ x _).

Notation "x <- e1 ; e2" := (match e1 with
                              | Unknown => ??
                              | Found x _ => e2 end)
                             (right associativity, at level 60).
