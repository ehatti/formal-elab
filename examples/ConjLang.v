Require Import Elaborator.

Inductive V := VA (l r : V) | VB (b : bool).
Definition C := list bool.

Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint fwdV (v : V) : C :=
  match v with
  | VA l r => fwdV l ++ fwdV r
  | VB b => [b]
  end.

Fixpoint bwdC (c : C) : V :=
  match c with
  | [] => VB false
  | [b] => VB b
  | b :: c => VA (VB b) (bwdC c)
  end.

Definition elab := {|
  fwd := fwdV;
  bwd := bwdC
|}.

Inductive JV : V -> Prop :=
| JVA l r : JV l -> JV r -> JV (VA l r)
| JVB : JV (VB true).

Inductive CJ : C -> Prop :=
| JCS : CJ [true]
| JCC c : CJ c -> CJ (true :: c).

Lemma CJ_split :
  forall e1 e2, CJ e1 -> CJ e2 -> CJ (e1 ++ e2).
Proof.
  intros. induction H;
  now constructor.
Qed.

Lemma VJ_flat :
  forall c, CJ c -> JV (bwdC c).
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

Lemma elab_correct :
  forall e, JV e -> CJ (fwdV e).
Proof.
  intros.
  induction H.
  { now apply CJ_split. }
  { constructor. }
Qed.

Lemma elab_faithful :
  forall e, JV e -> JV (bwdC (fwdV e)).
Proof.
  intros.
  now apply VJ_flat, elab_correct.
Qed.

Theorem elab_is_elaborator : is_elaborator JV CJ elab.
Proof.
  constructor.
  { apply elab_correct. }
  { apply elab_faithful. }
Qed.