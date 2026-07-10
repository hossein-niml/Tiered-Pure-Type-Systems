Require Import List.
Import ListNotations.

Require Import Thesis.PTSSignature.
Require Import Thesis.PTS.

Module PTSExampleSig <: PTS_SIGNATURE.

Inductive ex_sort :=
  | Star
  | Box.

Definition Sort := ex_sort.

Inductive ex_A : Sort -> Sort -> Prop :=
    | ax_star : ex_A Star Box.

Definition A := ex_A.

Inductive ex_R : Sort -> Sort -> Sort -> Prop :=
    | rule_star : ex_R Star Star Star
    | rule_box : ex_R Box Box Box.

Definition R := ex_R.

End PTSExampleSig.


Module PTSExample := PTS(PTSExampleSig).

Import PTSExample.
Import PTSExampleSig.

Check typing.

Definition star : term :=
  t_sort Star.

Definition box : term :=
  t_sort Box.


Example star_typing :
  [] ⊢ star ∈ box.
Proof.
    unfold star, box.
    apply typing_axiom.
    apply ax_star.
Qed.

Definition x : var :=
  {| var_sort := Box;
     var_idx := 0 |}.

Definition y : var :=
  {| var_sort := Box;
     var_idx := 1 |}.

Example typingE1:
    [] ⊢ 
    (t_lam x star (t_lam y star (t_var x)))
    ∈
    (t_pi x star (t_pi y star star)).
Proof.
    unfold star.
    apply typing_lam with (s' := Box).

    - apply typing_lam with (s' := Box).

        + apply typing_weak with (x := y) (B := t_sort Star) (s := Box).
          * simpl. unfold is_fresh. simpl. destruct (eq_var_dec y x).
            ** discriminate.
            ** reflexivity.
          * reflexivity.
          * apply typing_var with (s := Box).
            ** reflexivity.
            ** reflexivity.
            ** apply typing_axiom. apply ax_star.
          * apply typing_axiom. apply ax_star.
        
        + apply typing_pi with (s1 := Box) (s2 := Box).
          * reflexivity.
          * apply typing_axiom. apply ax_star.
          * apply typing_axiom. apply ax_star.
          * apply rule_box.

    - apply typing_pi with (s1 := Box) (s2 := Box).
      + reflexivity.
      + apply typing_axiom. apply ax_star.
      + apply typing_pi with (s1 := Box) (s2 := Box).
        * reflexivity.
        * apply typing_axiom. apply ax_star.
        * apply typing_axiom. apply ax_star.
        * apply rule_box.
      + apply rule_box.
Qed.
