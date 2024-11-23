Record raw_elaborator {V C : Type}
:= {
  fwd : V -> C;
  bwd : C -> V;
}.
Arguments raw_elaborator : clear implicits.

Record is_elaborator {V C : Type}
  (VJ : V -> Prop)
  (CJ : C -> Prop)
  (elab : raw_elaborator V C)
:= {
  correct  : forall e, VJ e -> CJ (elab.(fwd) e);
  faithful : forall e, VJ e -> VJ (elab.(bwd) (elab.(fwd) e))
}.