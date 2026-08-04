Require Import Thesis.TPTSSignature.
Require Import Thesis.PTS.

Module TPTS (Sig : TPTS_SIGNATURE).
Import Sig.
Module Base := PTS Sig.
Import Base.

End TPTS.