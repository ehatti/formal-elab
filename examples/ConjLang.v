Require Import Elaboration.
Require Import Coq.Lists.List.
Import ListNotations.

Inductive V := VA (l r : V) | VB (b : bool).
Definition C := list bool.

Inductive JV : V -> Prop :=
| JVA l r : JV l -> JV r -> JV (VA l r)
| JVB : JV (VB true).

Inductive CJ : C -> Prop :=
| JCS : CJ [true]
| JCC c : CJ c -> CJ (true :: c).

Fixpoint bwd (c : C) : V :=
  match c with
  | [] => VB false
  | [b] => VB b
  | b :: c => VA (VB b) (bwd c)
  end.

Lemma VJ_flat :
  forall c, CJ c -> JV (bwd c).
Proof.
  intros. induction H.
  { constructor. }
  {
    cbn. destruct c.
    {
      remember [].
      now destruct H.
    }
    {
      constructor.
      constructor.
      easy.
    }
  }
Qed.

Lemma CJ_split :
  forall e1 e2, CJ e1 -> CJ e2 -> CJ (e1 ++ e2).
Proof.
  intros. induction H;
  now constructor.
Qed.

Module Correct.

  Fixpoint fwd (v : V) : C :=
    match v with
    | VA l r => fwd l ++ fwd r
    | VB b => [b]
    end.

  Definition conj_elab : elab C JV := {|
    elab_fwd v _ := fwd v;
    elab_bwd := bwd
  |}.

  Lemma elab_correct :
    forall e, JV e -> CJ (fwd e).
  Proof.
    intros.
    induction H.
    { now apply CJ_split. }
    { constructor. }
  Qed.

  Lemma elab_faithful :
    forall e, JV e -> JV (bwd (fwd e)).
  Proof.
    intros.
    now apply VJ_flat, elab_correct.
  Qed.

  Theorem elab_conj_correct : correct JV CJ conj_elab.
  Proof.
    constructor.
    { apply elab_correct. }
    { apply elab_faithful. }
  Qed.

End Correct.

Module Incorrect.

  Definition fwd (v : V) : C :=
    [].
  
  Definition conj_elab : elab C JV := {|
    elab_fwd v _ := fwd v;
    elab_bwd := bwd
  |}.

  Theorem elab_conj_incorrect : ~correct JV CJ conj_elab.
  Proof.
    unfold not. intros. destruct H.
    assert (JV (VB true)) by constructor.
    specialize (faithful _ H).
    cbn in faithful.
    remember (VB false).
    now destruct faithful.
  Qed.

End Incorrect.