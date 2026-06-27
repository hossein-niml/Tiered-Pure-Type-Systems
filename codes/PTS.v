Require Import List.
Import ListNotations.

Module PTS.

Parameter Sort : Type.

Parameter A : Sort -> Sort -> Prop.

Parameter R : Sort -> Sort -> Sort -> Prop.

Record var := mkvar {
  var_sort : Sort;
  var_idx  : nat
}.

Inductive term : Type :=
    | t_sort : Sort -> term
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

Definition is_fresh (x : var) (c : context) : Prop :=
  lookup c x = None.

Fixpoint dom (c : context) : list var :=
  match c with
  | [] => []
  | (x, _) :: c' => x :: dom c'
  end.

Fixpoint rename (x y : var) (t : term) : term :=
  match t with
  | t_sort s => t_sort s
  | t_var z => if eq_var_dec z x then t_var y else t_var z
  | t_pi z A B =>
      if eq_var_dec z x
      then t_pi z (rename x y A) B
      else t_pi z (rename x y A) (rename x y B)
  | t_lam z A B =>
      if eq_var_dec z x
      then t_lam z (rename x y A) B
      else t_lam z (rename x y A) (rename x y B)
  | t_app M N => t_app (rename x y M) (rename x y N)
  end.

Reserved Notation "t1 =a t2" (at level 70, no associativity).

Inductive alpha_eq : term -> term -> Prop :=

  | alpha_sort : forall s, t_sort s =a t_sort s

  | alpha_var : forall x, t_var x =a t_var x

  | alpha_app : forall M1 M2 N1 N2,
      M1 =a M2 -> N1 =a N2 -> t_app M1 N1 =a t_app M2 N2

  | alpha_prod_same : forall x A1 B1 A2 B2,
      (A1 =a A2) -> (B1 =a B2) -> ((t_pi x A1 B1) =a (t_pi x A2 B2))
      
  | alpha_prod_diff : forall x y A1 B1 A2 B2,
      ~ In y (fv (t_pi x A1 B1)) ->
      A1 =a A2 ->
      B1 =a (rename x y B2) ->
      t_pi x A1 B1 =a t_pi y A2 B2

  | alpha_lam_same : forall x A1 B1 A2 B2,
      A1 =a A2 ->
      B1 =a B2 ->
      t_lam x A1 B1 =a t_lam x A2 B2

  | alpha_lam_diff : forall x y A1 B1 A2 B2,
      ~ In y (fv (t_lam x A1 B1)) ->
      A1 =a A2 ->
      B1 =a (rename x y B2 ) ->
      t_lam x A1 B1 =a t_lam y A2 B2

where "t1 =a t2" := (alpha_eq t1 t2).

Lemma alpha_refl : forall t, t =a t.
Proof.
  induction t; constructor; auto.
Qed.

Fixpoint subst_term (x : var) (N : term) (t : term) : term :=
  match t with
  | t_sort s  => t_sort s
  | t_var y   => if eq_var_dec y x then N else t_var y
  | t_app P Q => t_app (subst_term x N P) (subst_term x N Q)

  | t_pi y A B =>
      if eq_var_dec y x
      then t_pi y (subst_term x N A) B
      else t_pi y (subst_term x N A) (subst_term x N B)

  | t_lam y A M =>
      if eq_var_dec y x
      then t_lam y (subst_term x N A) M
      else t_lam y (subst_term x N A) (subst_term x N M)
  end. 

End PTS.
