Require Import Thesis.PTSSignature.

Module Type TPTS_SIGNATURE <: PTS_SIGNATURE.
  Include PTS_SIGNATURE.

  Parameter n : nat.
  Parameter index_of : Sort -> nat.

  Axiom index_range : forall x, 0 < index_of x /\ index_of x < n + 1.
  Axiom index_inj    : forall x y, index_of x = index_of y -> x = y.
  Axiom index_surj : forall i : nat, 0 < i /\ i < n + 1 -> exists x : Sort, index_of x = i.

  Axiom A_spec  : forall x y, A x y <-> index_of x < n /\ index_of y = S (index_of x).
  Axiom R_shape : forall x y z, R x y z -> y = z.
End TPTS_SIGNATURE.