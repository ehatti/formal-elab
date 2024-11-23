Record elab {V C : Type}
  {JV : V -> Type}
:= {
  elab_fwd : forall v, JV v -> C;
  elab_bwd : C -> V;
}.
Arguments elab {V} C JV.

Record correct {V C : Type}
  {JV : V -> Prop}
  {JC : C -> Prop}
  {m : elab C JV}
:= {
  preserve : forall v p, JC (m.(elab_fwd) v p);
  faithful : forall v p, JV (m.(elab_bwd) (m.(elab_fwd) v p))
}.
Arguments correct {V C} JV JC m.