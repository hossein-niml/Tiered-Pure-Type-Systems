Require Import List.
Require Import Classical.
Import ListNotations.

Require Import Thesis.PTSSignature.

Module PTS (Sig : PTS_SIGNATURE).

Import Sig.  

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


Definition beta (M N : term) : Prop :=
  exists x A Body Arg,
    M = t_app (t_lam x A Body) Arg /\
    N = subst_term x Arg Body.

Reserved Notation "M ->b N" (at level 70, no associativity).

Inductive beta_red : term -> term -> Prop :=

  | beta_base : forall x A M N,
      t_app (t_lam x A M) N ->b subst_term x N M

  | beta_app_l : forall M M' N,
      M ->b M' ->
      t_app M N ->b t_app M' N

  | beta_app_r : forall M N N',
      N ->b N' ->
      t_app M N ->b t_app M N'

  | beta_lam_A : forall x A A' M,
      A ->b A' ->
      t_lam x A M ->b t_lam x A' M

  | beta_lam_M : forall x A M M',
      M ->b M' ->
      t_lam x A M ->b t_lam x A M'

  | beta_pi_A : forall x A A' B,
      A ->b A' ->
      t_pi x A B ->b t_pi x A' B

  | beta_pi_B : forall x A B B',
      B ->b B' ->
      t_pi x A B ->b t_pi x A B'

where "M ->b N" := (beta_red M N).

Reserved Notation "M ->>+b N" (at level 70, no associativity).

Inductive beta_trans : term -> term -> Prop :=
  | bt_step : forall M N,
      M ->b N ->
      M ->>+b N

  | bt_trans : forall M N P,
      M ->>+b N ->
      N ->>+b P ->
      M ->>+b P

where "M ->>+b N" := (beta_trans M N).

Reserved Notation "M ->>b N" (at level 70, no associativity).

Inductive beta_rtrans : term -> term -> Prop :=
  | brt_refl : forall M,
      M ->>b M

  | brt_step : forall M N,
      M ->b N ->
      M ->>b N

  | brt_trans : forall M N P,
      M ->>b N ->
      N ->>b P ->
      M ->>b P

where "M ->>b N" := (beta_rtrans M N).

Reserved Notation "M =b N" (at level 70, no associativity).

Inductive beta_eq : term -> term -> Prop :=
  | beq_refl : forall M,
      M =b M

  | beq_step : forall M N,
      M ->b N ->
      M =b N

  | beq_sym : forall M N,
      M =b N ->
      N =b M

  | beq_trans : forall M N P,
      M =b N ->
      N =b P ->
      M =b P

where "M =b N" := (beta_eq M N).

Lemma brt_from_trans : forall M N,
  M ->>+b N -> M ->>b N.
Proof.
  intros M N H.
  induction H.
  - apply brt_step; auto.
  - apply brt_trans with N; auto.
Qed.

Lemma beq_from_rtrans : forall M N,
  M ->>b N -> M =b N.
Proof.
  intros M N H.
  induction H.
  - apply beq_refl.
  - apply beq_step; auto.
  - apply beq_trans with N; auto.
Qed.

Definition normal_form (M : term) : Prop :=
  ~ exists N, M ->b N.

Fixpoint has_redex (M : term) : Prop :=
  match M with
  | t_sort _    => False
  | t_var _     => False
  | t_app (t_lam _ _ _) _ => True
  | t_app P Q   => has_redex P \/ has_redex Q
  | t_lam _ A M => has_redex A \/ has_redex M
  | t_pi  _ A B => has_redex A \/ has_redex B
  end.

Definition normal_form' (M : term) : Prop :=
  ~ has_redex M.

Definition weakly_normalizing (M : term) : Prop :=
  exists N, M ->>b N /\ normal_form N.

Definition strongly_normalizing (M : term) : Prop :=
  Acc (fun N M => M ->b N) M.

Lemma sn_implies_wn : forall M,
  strongly_normalizing M -> weakly_normalizing M.
Proof.
  intros M Hacc.
  induction Hacc as [M _ IH].
  destruct (classic (exists N, M ->b N)) as [[N Hstep] | Hnf].
  - destruct (IH N Hstep) as [P [HredP HnfP]].
    exists P. split.
    + apply brt_trans with N.
      * apply brt_step; auto.
      * auto.
    + auto.
  - exists M. split.
    + apply brt_refl.
    + unfold normal_form. auto.
Qed.

Lemma nf_is_sn : forall M,
  normal_form M -> strongly_normalizing M.
Proof.
  intros M Hnf.
  constructor.
  intros N Hstep.
  exfalso. apply Hnf.
  exists N. auto.
Qed.

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


Reserved Notation "Γ ⊢ M ∈ A" (at level 70, no associativity).

Inductive typing : context -> term -> term -> Prop :=
  | typing_axiom : forall Γ s s',
      A s s' ->
      Γ ⊢ (t_sort s) ∈ (t_sort s')

  | typing_var : forall Γ x A s,
      is_fresh x Γ ->
      var_sort x = s ->
      Γ ⊢ A ∈ t_sort s ->
      Γ ++ [(x, A)] ⊢ t_var x ∈ A

  | typing_weak : forall Γ x B M A s,
      is_fresh x Γ ->
      var_sort x = s ->
      Γ ⊢ M ∈ A ->
      Γ ⊢ B ∈ t_sort s ->
      Γ ++ [(x, B)] ⊢ M ∈ A

  | typing_pi : forall Γ x A B s1 s2 s',
      var_sort x = s1 ->
      Γ ⊢ A ∈ t_sort s1 ->
      Γ ++ [(x, A)] ⊢ B ∈ t_sort s2 ->
      R s1 s2 s' ->
      Γ ⊢ (t_pi x A B) ∈ (t_sort s')

  | typing_lam : forall Γ x A M B s',
      Γ ++ [(x, A)] ⊢ M ∈ B ->
      Γ ⊢ (t_pi x A B) ∈ (t_sort s') ->
      Γ ⊢ (t_lam x A M) ∈ (t_pi x A B)

  | typing_app : forall Γ M N A B x,
      Γ ⊢ M ∈ t_pi x A B ->
      Γ ⊢ N ∈ A ->
      Γ ⊢ t_app M N ∈ (subst_term x N B)

  | typing_conv : forall Γ M A B s,
      Γ ⊢ M ∈ A ->
      A =b B ->
      Γ ⊢ B ∈ t_sort s ->
      Γ ⊢ M ∈ B

where "Γ ⊢ M ∈ A" := (typing Γ M A).

End PTS.
