Require Import Thesis.PTSSignature.

Module DisjointUnion (Sig1 Sig2 : PTS_SIGNATURE) <: PTS_SIGNATURE.

  Definition Sort := (Sig1.Sort + Sig2.Sort)%type.

  Definition A (x y : Sort) : Prop :=
    match x, y with
    | inl x1, inl y1 => Sig1.A x1 y1
    | inr x2, inr y2 => Sig2.A x2 y2
    | _, _ => False
    end.

  Definition R (x y z : Sort) : Prop :=
    match x, y, z with
    | inl x1, inl y1, inl z1 => Sig1.R x1 y1 z1
    | inr x2, inr y2, inr z2 => Sig2.R x2 y2 z2
    | _, _, _ => False
    end.

End DisjointUnion.