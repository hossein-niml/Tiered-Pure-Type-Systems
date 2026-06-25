Require Import List.
Import ListNotations.

Module PTS.

Parameter S : Type.

Parameter A : S -> S -> Prop.

Parameter R : S -> S -> S -> Prop.

Record var := mkvar {
  var_sort : S;
  var_idx  : nat
}.

Inductive term : Type :=
    | t_sort : S -> term
    | t_var  : var -> term
    | t_app  : term -> term -> term
    | t_lam  : var -> term -> term -> term
    | t_pi   : var -> term -> term -> term.

Axiom eq_var_dec : forall x y : var, {x = y} + {x <> y}.

Fixpoint fv (t : term) : list var :=
    match t with
    | t_sort _   => []
    | t_var x    => [x]
    | t_pi x A B => remove eq_var_dec x (fv A ++ fv B)
    | t_lam x A B => remove eq_var_dec x (fv A ++ fv B)
    | t_app M N  => fv M ++ fv N
    end.

Definition context := list (var * term).

Fixpoint lookup (c : context) (x : var) : option term :=
  match c with
  | [] => None
  | (y, A) :: c' =>
      if eq_var_dec x y
      then Some A
      else lookup c' x
  end.

Definition in_ctx (x : var) (c : context) : Prop :=
  exists A, lookup c x = Some A.

Definition fresh (x : var) (c : context) : Prop :=
  lookup c x = None.

Fixpoint dom (c : context) : list var :=
  match c with
  | [] => []
  | (x, _) :: c' => x :: dom c'
  end.

End PTS.
