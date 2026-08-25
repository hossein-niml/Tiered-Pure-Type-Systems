Require Import List.
Require Import Classical.
From Stdlib Require Import Logic.IndefiniteDescription.
Import ListNotations.
From Stdlib.Program Require Import Program Wf.
From Stdlib Require Import Lia.
Require Import Coq.Arith.Arith.
Require Import ZArith.

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
    | t_pi x A B => fv A ++ remove eq_var_dec x (fv B)
    | t_lam x A B => fv A ++ remove eq_var_dec x (fv B)
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

Lemma rename_notin : forall M y z,
  ~ In y (fv M) ->
  rename y z M = M.
Proof.
  intros M y z H.
  induction M; auto.
  - simpl. destruct (eq_var_dec v y).
    + subst. destruct H. simpl. left. reflexivity.
    + reflexivity.
  - simpl in *. f_equal.
    + apply IHM1. intros Q. apply H. apply in_or_app. left. apply Q.
    + apply IHM2. intros Q. apply H. apply in_or_app. right. apply Q.
  - simpl in *. destruct (eq_var_dec v y).
    + subst. f_equal. apply IHM1. intros Q. apply H. apply in_or_app. left. apply Q.
    + f_equal.
      * apply IHM1. intros Q. apply H. apply in_or_app. left. apply Q.
      * apply IHM2. intros Q. apply H. apply in_or_app. right. apply in_in_remove; auto.
  - simpl in *. destruct (eq_var_dec v y).
    + subst. f_equal. apply IHM1. intros Q. apply H. apply in_or_app. left. apply Q.
    + f_equal.
      * apply IHM1. intros Q. apply H. apply in_or_app. left. apply Q.
      * apply IHM2. intros Q. apply H. apply in_or_app. right. apply in_in_remove; auto.
Qed.

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
      B1 =a (rename y x B2) ->
      t_pi x A1 B1 =a t_pi y A2 B2

  | alpha_lam_same : forall x A1 B1 A2 B2,
      A1 =a A2 ->
      B1 =a B2 ->
      t_lam x A1 B1 =a t_lam x A2 B2

  | alpha_lam_diff : forall x y A1 B1 A2 B2,
      ~ In y (fv (t_lam x A1 B1)) ->
      A1 =a A2 ->
      B1 =a (rename y x B2 ) ->
      t_lam x A1 B1 =a t_lam y A2 B2

where "t1 =a t2" := (alpha_eq t1 t2).

Lemma alpha_refl : forall t, t =a t.
Proof.
  induction t; constructor; auto.
Qed.

Fixpoint max_var_idx (xs : list var) : nat :=
  match xs with
  | [] => 0
  | v :: xs => Nat.max (var_idx v) (max_var_idx xs)
  end.

Definition fresh (s : Sort) (xs : list var) : var :=
  mkvar s (S (max_var_idx xs)).

Fixpoint size (t : term) : nat :=
  match t with
  | t_sort _ => 1
  | t_var _ => 1
  | t_app M N => 1 + size M + size N
  | t_pi _ A B => 1 + size A + size B
  | t_lam _ A M => 1 + size A + size M
  end.

Lemma rename_size :
  forall x y M,
    size (rename x y M) = size M.
Proof.
  intros x y M. induction M.
    - reflexivity.
    - simpl. destruct (eq_var_dec v x).
      + reflexivity.
      + reflexivity.
    - simpl. rewrite IHM1. rewrite IHM2. reflexivity.
    - simpl. destruct (eq_var_dec v x).
      + simpl. rewrite IHM1. reflexivity.
      + simpl. rewrite IHM1. rewrite IHM2. reflexivity.
    - simpl. destruct (eq_var_dec v x).
      + simpl. rewrite IHM1. reflexivity.
      + simpl. rewrite IHM1. rewrite IHM2. reflexivity.
Qed.

Reserved Notation "M ⁅ x ≔ N ⁆"
  (at level 20, left associativity).

Program Fixpoint subst_term (x : var) (N : term) (t : term) {measure (size t)} : term :=
  match t with
  | t_sort s  => t_sort s
  | t_var y   => if eq_var_dec y x then N else t_var y
  | t_app P Q => t_app (P⁅x ≔ N⁆) (Q⁅x ≔ N⁆)

  | t_pi y A B =>
    let z := if in_dec eq_var_dec y (fv N ++ fv B) 
    then fresh (var_sort y) (fv N ++ fv B) 
    else y in
    t_pi z (A⁅x ≔ N⁆) ((rename y z B)⁅x ≔ N⁆)

  | t_lam y A M =>
    let z := if in_dec eq_var_dec y (fv N ++ fv M) 
    then fresh (var_sort y) (fv N ++ fv M) 
    else y in
    t_lam z (A⁅x ≔ N⁆) ((rename y z M)⁅x ≔ N⁆)
  end
  
where "M ⁅ x ≔ N ⁆" := (subst_term x N M).
Next Obligation.
  simpl. lia.
Qed.
Next Obligation.
  simpl. lia.
Qed.
Next Obligation.
  simpl. lia.
Qed.
Next Obligation.
  rewrite rename_size. simpl. lia.
Qed.
Next Obligation.
  simpl. lia.
Qed.
Next Obligation.
  rewrite rename_size. simpl. lia.
Qed.

Axiom subst_sort : forall s x N,
  (t_sort s)⁅x ≔ N⁆ = t_sort s.

Axiom subst_var : forall y x N,
  (t_var y)⁅x ≔ N⁆ = if eq_var_dec y x then N else t_var y.

Axiom subst_app : forall M1 M2 x N,
  (t_app M1 M2)⁅x ≔ N⁆ = t_app (M1⁅x ≔ N⁆) (M2⁅x ≔ N⁆).

Axiom subst_pi : forall y A B x N,
  let z := if in_dec eq_var_dec y (fv N ++ fv B) then fresh (var_sort y) (fv N ++ fv B) else y in
  (t_pi y A B)⁅x ≔ N⁆ = t_pi z (A⁅x ≔ N⁆) ((rename y z B)⁅x ≔ N⁆).

Axiom subst_lam : forall y A M x N,
  let z := if in_dec eq_var_dec y (fv N ++ fv M) then fresh (var_sort y) (fv N ++ fv M) else y in
  (t_lam y A M)⁅x ≔ N⁆ = t_lam z (A⁅x ≔ N⁆) ((rename y z M)⁅x ≔ N⁆).

Definition beta (M N : term) : Prop :=
  exists x A Body Arg,
    M = t_app (t_lam x A Body) Arg /\
    N = Body⁅x ≔ Arg⁆.

Reserved Notation "M ->b N" (at level 70, no associativity).

Inductive beta_red : term -> term -> Prop :=

  | beta_base : forall x A M N,
      t_app (t_lam x A M) N ->b M⁅x ≔ N⁆

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

Definition dom (Γ : context) : list var :=
  map fst Γ.

Definition is_fresh (x : var) (Γ : context) :=
  ~ In x (dom Γ).

Reserved Notation "Γ ⊢ M ∈ A" (at level 70, no associativity).

Inductive typing : context -> term -> term -> Prop :=
  | typing_axiom : forall s s',
      A s s' ->
      [] ⊢ t_sort s ∈ t_sort s'

  | typing_var : forall Γ x A,
      is_fresh x Γ ->
      Γ ⊢ A ∈ t_sort (var_sort x) ->
      Γ ++ [(x, A)] ⊢ t_var x ∈ A

  | typing_weak : forall Γ x B M A,
      is_fresh x Γ ->
      Γ ⊢ M ∈ A ->
      Γ ⊢ B ∈ t_sort (var_sort x) ->
      Γ ++ [(x, B)] ⊢ M ∈ A

  | typing_pi : forall Γ x A B s s',
      Γ ⊢ A ∈ t_sort (var_sort x) ->
      Γ ++ [(x, A)] ⊢ B ∈ t_sort s ->
      R (var_sort x) s s' ->
      Γ ⊢ (t_pi x A B) ∈ (t_sort s')

  | typing_lam : forall Γ x A M B s',
      Γ ++ [(x, A)] ⊢ M ∈ B ->
      Γ ⊢ (t_pi x A B) ∈ (t_sort s') ->
      Γ ⊢ (t_lam x A M) ∈ (t_pi x A B)

  | typing_app : forall Γ M N A B x,
      Γ ⊢ M ∈ t_pi x A B ->
      Γ ⊢ N ∈ A ->
      Γ ⊢ t_app M N ∈ (B⁅x ≔ N⁆)

  | typing_conv : forall Γ M A B s,
      Γ ⊢ M ∈ A ->
      A =b B ->
      Γ ⊢ B ∈ t_sort s ->
      Γ ⊢ M ∈ B

where "Γ ⊢ M ∈ A" := (typing Γ M A).

Definition legal (Γ : context) : Prop :=
  exists M N, Γ ⊢ M ∈ N.

(* Meta-Theory *)

Lemma start_axiom :
  forall Γ s s',
    legal Γ ->
    A s s' ->
    Γ ⊢ t_sort s ∈ t_sort s'.
Proof.
  intros Γ s s' Hl Hs. destruct Hl as [M [N Htyp]].
  induction Htyp; auto.
  - apply typing_axiom. apply Hs.
  - apply typing_weak.
    + apply H.
    + apply IHHtyp.
    + apply Htyp.
  - apply typing_weak.
    + apply H.
    + apply IHHtyp1.
    + apply Htyp2.
Qed.

Lemma start_var :
  forall Γ x T,
    legal Γ ->
    In (x,T) Γ ->
    Γ ⊢ t_var x ∈ T.
Proof.
  intros Γ x T Hl Hin. destruct Hl as [M [N Htyp]].
  induction Htyp; auto.

  - contradiction.

  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + apply typing_weak.
      * apply H.
      * apply IHHtyp. apply Hin.
      * apply Htyp.
    + destruct Hin as [Hin | []]. inversion Hin. subst. apply typing_var.
      * apply H.
      * apply Htyp.
  
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + apply typing_weak.
      * apply H.
      * apply IHHtyp1. apply Hin.
      * apply Htyp2.
    + destruct Hin as [Hin | []]. inversion Hin. subst. apply typing_var.
      * apply H.
      * apply Htyp2.
Qed.

Definition subcontext (Γ Δ : context) : Prop :=
  forall x T,
    In (x, T) Γ ->
    In (x, T) Δ.

Notation "Γ ⊆ Δ" := (subcontext Γ Δ) (at level 70, no associativity).

Lemma subcontext_extend : forall Γ Δ z A,
  Γ ⊆ Δ ->
  is_fresh z Δ ->
  Γ ++ [(z, A)] ⊆ Δ ++ [(z, A)].
Proof.
  intros Γ Δ z A Hsub Hfr y T Hin.
  apply in_app_or in Hin.
  destruct Hin.
  - apply in_or_app. left. apply Hsub. assumption.
  - simpl in H.
    destruct H as [H | H].
    + inversion H; subst.
      apply in_or_app. right. left. reflexivity.
    + contradiction.
Qed.

Lemma subcontext_extend_r : forall Γ x T, Γ ⊆ Γ ++ [(x, T)].
Proof.
  intros.
  unfold subcontext. intros.
  apply in_or_app. left.
  apply H.
Qed.

Axiom thinning_fresh : forall Γ Δ x T M N,
  legal Δ ->
  Γ ⊆ Δ ->
  Γ ++ [(x, T)] ⊢ M ∈ N ->
  is_fresh x Δ.

Axiom pi_domain_valid : forall Γ x A B s',
  Γ ⊢ t_pi x A B ∈ t_sort s' ->
  Γ ⊢ A ∈ t_sort (var_sort x).

Lemma thinning :
  forall Γ Δ M N,
    legal Δ ->
    Γ ⊆ Δ ->
    Γ ⊢ M ∈ N ->
    Δ ⊢ M ∈ N.
Proof.
  intros Γ Δ M N Hleg Hsub Htyp.
  generalize dependent Δ.
  induction Htyp; intros Δ Hleg Hsub.

  - apply start_axiom.
    + apply Hleg.
    + apply H.

  - apply start_var.
    + apply Hleg.
    + unfold subcontext in Hsub. apply Hsub. apply in_or_app. right. 
    simpl. left. reflexivity.
  
  - apply IHHtyp1. 
    + apply Hleg.
    + unfold subcontext in Hsub. unfold subcontext. intros y T Hin. 
    apply Hsub. apply in_or_app. left. apply Hin.

  - apply typing_pi with s.
    + apply IHHtyp1.
      * apply Hleg.
      * apply Hsub.
    + apply IHHtyp2.
      * exists (t_var x). exists (A0). apply typing_var.
        ** apply thinning_fresh with (Γ:=Γ) (x:=x) (T:=A0) (M:=B) (N:=t_sort s); auto.
        ** apply IHHtyp1.
          *** apply Hleg.
          *** apply Hsub.
      * apply subcontext_extend.
        ** apply Hsub.
        ** apply thinning_fresh with (Γ:=Γ) (x:=x) (T:=A0) (M:=B) (N:=t_sort s); auto.
    + apply H.

  - apply typing_lam with s'.
    + apply IHHtyp1.
      * exists (t_var x). exists (A0). apply typing_var.
        ** apply thinning_fresh with (Γ:=Γ) (x:=x) (T:=A0) (M:=M) (N:=B); auto.
        ** apply pi_domain_valid with (B:=B) (s':=s'). apply IHHtyp2; auto.
      * apply subcontext_extend.
        ** apply Hsub.
        ** apply thinning_fresh with (Γ:=Γ) (x:=x) (T:=A0) (M:=M) (N:=B); auto.
    + apply IHHtyp2.
      * apply Hleg.
      * apply Hsub.

  - apply typing_app with A0; auto.

  - apply typing_conv with A0 s; auto. 
Qed.

Lemma app_singleton_injective :
  forall (Γ Δ : context)
         (x y : var)
         (M N : term),
    Γ ++ [(x, M)] = Δ ++ [(y, N)] ->
    Γ = Δ /\ x = y /\ M = N.
Proof.
  induction Γ as [| [v T] Γ IH].
  - intros Δ x y M N H.
    destruct Δ as [| [v' T'] Δ].
    + simpl in H.
      inversion H. subst.
      repeat split; reflexivity.
    + simpl in H.
      destruct Δ.
      * discriminate.
      * discriminate.

  - intros Δ x y M N H.
    destruct Δ as [| [v' T'] Δ].
    + simpl in H.
      destruct Γ.
      * discriminate.
      * discriminate.

    + simpl in H.
      inversion H. subst.
      specialize (IH Δ x y M N H3).
      destruct IH as [HΓ [Hx HM]].
      subst.
      repeat split; reflexivity.
Qed.

Lemma generation_sort :
  forall Γ s W,
    Γ ⊢ t_sort s ∈ W ->
    exists s',
      W =b t_sort s' /\ Sig.A s s'.
Proof.
  intros Γ s W H.
  remember (t_sort s) as T.
  induction H; inversion HeqT; subst.
  - exists s'. split.
    + apply beq_refl.
    + apply H.
  - apply IHtyping1. reflexivity.
  - destruct (IHtyping1 eq_refl) as [s' [HA HAx]]. exists s'. split.
    + apply beq_trans with (N := A0).
      * apply beq_sym. apply H0.
      * apply HA.
    + apply HAx.
Qed.

Lemma lookup_fresh :
  forall C y N, is_fresh y C -> lookup (C ++ [(y, N)]) y = Some N.
Proof.
  intros C y N F. unfold is_fresh in F. induction C.
  - simpl. destruct (eq_var_dec y y).
    + reflexivity.
    + contradiction.
  - destruct a as (v, T). simpl in *. destruct (eq_var_dec y v) as [Heq | Hneq].
    + unfold not in F. destruct F. left. symmetry. apply Heq.
    + apply IHC. unfold not. intros. unfold not in F. apply F. right. apply H.
Qed.

Lemma lookup_extend :
  forall C x y M N, (lookup C x = Some M) -> (lookup (C ++ [(y, N)]) x = Some M).
Proof.
  intros C x y M N H. induction C.
  - simpl in H. discriminate H.
  - destruct a as (v, T). simpl in *. destruct (eq_var_dec x v) as [Heq | Hneq].
    + apply H.
    + apply IHC. apply H.
Qed.

Lemma generation_var :
  forall Γ x N,
    Γ ⊢ t_var x ∈ N ->
    exists B,
      lookup Γ x = Some B /\
      Γ ⊢ B ∈ t_sort (var_sort x) /\
      N =b B.
Proof.
  intros Γ x N H.
  remember (t_var x) as T.
  induction H; inversion HeqT; subst.

  - exists A0. repeat split; auto.
    + apply lookup_fresh; auto.
    + apply typing_weak; auto.
    + apply beq_refl.
  
  - apply IHtyping1 in H2. destruct H2 as [B' [Q1 [Q2 Q3]]]. exists B'. repeat split; auto.
    + apply lookup_extend; auto.
    + apply typing_weak; auto.
    
  - apply IHtyping1 in H2. destruct H2 as [B' [Q1 [Q2 Q3]]]. exists B'. repeat split; auto.
    apply beq_trans with A0; auto. apply beq_sym; auto.
Qed.

Lemma generation_pi : 
  forall Γ x B C W, 
    Γ ⊢ t_pi x B C ∈ W ->
    exists s' s'',
      Γ ⊢ B ∈ t_sort (var_sort x) /\
      (Γ ++ [(x,B)]) ⊢ C ∈ t_sort s' /\
      Sig.R (var_sort x) s' s'' /\
      W =b t_sort s''.
Proof.
  intros Γ x B C W H. 
  remember (t_pi x B C) as T eqn:HT.
  induction H; inversion HT; subst.

  - apply IHtyping1 in H2. destruct H2 as [s' [s'' [HB [HC [HR Heq]]]]].
  exists s'. exists s''. repeat split; auto.
    + apply typing_weak; auto.
    + apply thinning with (Γ ++ [(x, B)]).
      * exists (t_var x). exists B. apply typing_var.
        ** apply thinning_fresh with (Γ:=Γ) (T:=B) (M:=C) (N:=t_sort s'); auto.
          *** exists (t_var x0). exists (B0). apply typing_var; auto.
          *** apply subcontext_extend_r.
        ** apply thinning with Γ; auto.
          *** exists (t_var x0). exists (B0). apply typing_var; auto.
          *** apply subcontext_extend_r.
      * apply subcontext_extend.
        ** apply subcontext_extend_r.
        ** apply thinning_fresh with (Γ:=Γ) (T:=B) (M:=C) (N:=t_sort s'); auto.
          *** exists (t_var x0). exists (B0). apply typing_var; auto.
          *** apply subcontext_extend_r.
      * apply HC.
  
  - exists s. exists s'. repeat split; auto. apply beq_refl.

  - apply IHtyping1 in H2. destruct H2 as [s' [s'' [HB [HC [HR Heq]]]]].
  exists s'. exists s''. repeat split; auto. apply beq_trans with A0; auto.
  apply beq_sym; auto.

Qed.

Lemma generation_lam : 
  forall Γ x B M T, 
    Γ ⊢ t_lam x B M ∈ T ->
    exists C s,
      Γ ⊢ (t_pi x B C) ∈ t_sort s /\
      (Γ ++ [(x,B)]) ⊢ M ∈ C /\
      T =b t_pi x B C.
Proof.
  intros Γ x B M T H. 
  remember (t_lam x B M) as W eqn:HW.
  induction H; inversion HW; subst.

  - apply IHtyping1 in H2. destruct H2 as [C [s [Q1 [Q2 Q3]]]].
  exists C. exists s. repeat split; auto.

    + apply thinning with Γ; auto.
      * exists (t_var x0). exists B0. apply typing_var; auto.
      * apply subcontext_extend_r.
    + apply thinning with (Γ ++ [(x, B)]); auto.
      * exists (t_var x0). exists B0. apply typing_weak.
        ** apply thinning_fresh with (Γ:=Γ) (T:=B) (M:=M) (N:=C); auto.
          *** exists (t_var x0). exists (B0). apply typing_var; auto.
          *** apply subcontext_extend_r.
        ** apply typing_var; auto.
        ** apply thinning with Γ.
          *** exists (t_var x0). exists (B0). apply typing_var; auto.
          *** apply subcontext_extend_r.
          *** apply generation_pi in Q1. destruct Q1 as [s' [s'' [Q1 _]]]. apply Q1.
      * apply subcontext_extend.
        ** apply subcontext_extend_r.
        ** apply thinning_fresh with (Γ:=Γ) (T:=B) (M:=M) (N:=C); auto.
          *** exists (t_var x0). exists (B0). apply typing_var; auto.
          *** apply subcontext_extend_r.

  - exists B0. exists s'. repeat split; auto. apply beq_refl.

  - apply IHtyping1 in H2. destruct H2 as [C [s' [Q1 [Q2 Q3]]]].
  exists C. exists s'. repeat split; auto. apply beq_trans with A0; auto.
  apply beq_sym; auto.

Qed.
    
Lemma generation_app:
  forall Γ M N T,
    Γ ⊢ (t_app M N) ∈ T ->
    exists x B C,
      Γ ⊢ M ∈ (t_pi x B C) /\
      Γ ⊢ N ∈ B /\
      T =b C⁅x ≔ N⁆.
Proof.
  intros Γ M N T H.
  remember (t_app M N) as W eqn:HW.
  induction H; inversion HW; subst.

  - apply IHtyping1 in H2. destruct H2 as [y [B' [C' [Q1 [Q2 Q3]]]]].
  exists y. exists B'. exists C'. repeat split; auto.
    + apply thinning with Γ; auto.
      * exists (t_var x). exists B. apply typing_var; auto.
      * apply subcontext_extend_r.
    + apply thinning with Γ; auto.
      * exists (t_var x). exists B. apply typing_var; auto.
      * apply subcontext_extend_r.
  
  - exists x. exists A0. exists B. repeat split; auto. apply beq_refl.

  - apply IHtyping1 in H2. destruct H2 as [y [B' [C' [Q1 [Q2 Q3]]]]].
  exists y. exists B'. exists C'. repeat split; auto.
  apply beq_trans with A0; auto. apply beq_sym; auto.
Qed.

Definition subst_decl (x : var) (N : term) '(y,T) : (var * term) := (y, T⁅x ≔ N⁆).

Definition subst_context (x : var) (N : term) (Γ : context) := map (subst_decl x N) Γ.

Notation "Γ ⌊ x ≔ N ⌋" := (subst_context x N Γ) (at level 20, left associativity).

Lemma map_fst_subst_decl : forall x N Δ,
  map fst (map (subst_decl x N) Δ) = map fst Δ.
Proof.
  intros x N Δ.
  induction Δ as [| [v A] Δ_tl IH].
  - reflexivity.
  - cbn [map subst_decl fst]. f_equal. exact IH.
Qed.

Axiom subst_fresh : forall Γ M A x N,
  is_fresh x Γ ->
  Γ ⊢ M ∈ A ->
  M ⁅ x ≔ N ⁆ = M /\ A ⁅ x ≔ N ⁆ = A.

Axiom fresh_eq : forall s A B,
  fresh (s) (A) = fresh (s) (B).

Lemma substitution :
  forall (Γ : context) (Δ : context) x C M B N,
    Γ ++ [(x,C)] ++ Δ ⊢ M ∈ B ->
    Γ ⊢ N ∈ C ->
    Γ ++ (Δ⌊x ≔ N⌋) ⊢ M⁅x ≔ N⁆ ∈ B⁅x ≔ N⁆.
Proof.
  intros Γ Δ x C M B N H1 H2.
  remember (Γ ++ [(x, C)] ++ Δ) as Z eqn: HZ.
  generalize dependent Δ.
  induction H1.

  - destruct Γ.
    + discriminate.
    + discriminate.

  - destruct Δ as [| (y, E) Δ1].
    + intros HZ. rewrite app_nil_r in HZ. apply app_singleton_injective in HZ. 
    destruct HZ as [HZ1 [HZ2 HZ3]]. subst.
    simpl in *. rewrite app_nil_r. assert (HX : t_var x ⁅ x ≔ N ⁆ = N).
      * cbn. destruct (eq_var_dec x x).
        ** reflexivity.
        ** destruct n. reflexivity.
      * rewrite HX. destruct (subst_fresh Γ C (t_sort (var_sort x)) x N H H1) as [HC _]. rewrite HC; auto. 
    + assert (Hnonempty : (y, E) :: Δ1 <> []) by discriminate.
    destruct (exists_last Hnonempty) as [Δ1' [[y0 E0] Hlast]]. rewrite Hlast in *.
    intros HZ. rewrite app_assoc in HZ. rewrite app_assoc in HZ.
      apply app_singleton_injective in HZ. destruct HZ as [Q1 [Q2 Q3]]. subst.
      unfold subst_context in *.
      rewrite map_app in *.
      simpl map in *.
      rewrite subst_var. destruct (eq_var_dec y0 x).
      * subst. destruct H. unfold dom. rewrite map_app. rewrite map_app. simpl.
      apply in_or_app. left. apply in_or_app. right. simpl. left. reflexivity.
      * rewrite app_assoc. apply typing_var.
        ** unfold is_fresh in *. unfold dom in *. rewrite map_app in *.
        rewrite map_app in *. simpl in *. intros Hin. apply H.
        apply in_app_or in Hin. destruct Hin as [Hin|Hin].
          *** apply in_or_app. left. apply in_or_app. left. apply Hin.
          *** apply in_or_app. right. rewrite map_fst_subst_decl in Hin. apply Hin. 
        ** rewrite subst_sort in IHtyping. apply IHtyping. rewrite app_assoc. reflexivity. 
  
  - intros Δ HZ. destruct Δ as [| (y, E) Δ1].
    + rewrite app_nil_r in HZ. apply app_singleton_injective in HZ. 
    destruct HZ as [HZ1 [HZ2 HZ3]]. subst.
    simpl in *. rewrite app_nil_r.
    destruct (subst_fresh Γ M A0 x N H H1_) as [HM HA0].
    rewrite HM, HA0. apply H1_.
    + assert (Hnonempty : (y, E) :: Δ1 <> []) by discriminate.
      destruct (exists_last Hnonempty) as [Δ1' [[y1 E1] Hlast]].
      rewrite Hlast in *.
      rewrite app_assoc in HZ. rewrite app_assoc in HZ.
      apply app_singleton_injective in HZ.
      destruct HZ as [HΓ0 [Hy1 HE1]]. subst.
      unfold subst_context in *. rewrite map_app. simpl map.
      rewrite app_assoc.
      apply typing_weak.
      * unfold is_fresh in *. intro Hin. apply H.
        unfold dom in *. rewrite map_app in *. rewrite map_app in *.
        apply in_app_or in Hin. destruct Hin as [Hin | Hin].
        ** apply in_or_app. left. apply in_or_app. left. exact Hin.
        ** apply in_or_app. right. rewrite map_fst_subst_decl in Hin. apply Hin. 
      * apply IHtyping1. rewrite <- app_assoc. reflexivity.
      * rewrite subst_sort in IHtyping2. apply IHtyping2. rewrite <- app_assoc. reflexivity.

  - intros Δ HZ. rewrite subst_sort in *. rewrite subst_pi.
  remember (fresh (var_sort x0) (fv N ++ fv B)) as w eqn:Hw.
  assert (Hsort: var_sort(w) = var_sort(x0)). rewrite Hw. reflexivity.
  apply typing_pi with s.
    * destruct (in_dec eq_var_dec x0 (fv N ++ fv B)). 
      ** rewrite Hsort. apply IHtyping1; auto.
      ** apply IHtyping1; auto.
    * admit. 
    * destruct (in_dec eq_var_dec x0 (fv N ++ fv B)); auto. rewrite Hsort. apply H.

  - intros Δ HZ. rewrite subst_sort in *. rewrite subst_lam in *. rewrite subst_pi in *.
  remember (fresh (var_sort x0) (fv N ++ fv M)) as w eqn:Hw.
  remember (fresh (var_sort x0) (fv N ++ fv B)) as v eqn:Hv.
  assert (Hvw : v = w). rewrite Hw. rewrite Hv. apply fresh_eq.
  rewrite Hvw in *.  admit.

Admitted.

Lemma type_correctness:
  forall Γ M N,
    Γ ⊢ M ∈ N ->
    (exists s, N = t_sort s) \/
    (exists s, Γ ⊢ N ∈ (t_sort s)) .
Proof.
  intros Γ M N Htyp.
  induction Htyp.

  - left. exists s'. reflexivity.

  - right. exists (var_sort x). apply typing_weak; auto.
  
  - destruct IHHtyp1 as [[s Hs] | [s Hs]].
    + left. exists s. apply Hs.
    + right. exists s. apply thinning with (Γ); auto.
      * exists (t_var x). exists (B). apply typing_var; auto.
      * apply subcontext_extend_r.
  
  - left. exists s'. reflexivity.

  - right. exists s'. apply Htyp2.

  - induction B.
    + left. exists s. rewrite subst_sort. reflexivity.
    + rewrite subst_var. destruct (eq_var_dec v x).
      * right. destruct IHHtyp2 as [[s Hs] | [s Hs]].
        ** exists s. rewrite <- Hs. apply Htyp2.
        ** exists s. destruct A0.
          *** 
Admitted.

Axiom permutation : 
  forall Γ Δ x y Tx Ty M C,
  ~ In x (fv Ty) ->
  Γ ++ [(x, Tx)] ++ [(y, Ty)] ++ Δ ⊢ M ∈ C ->
  Γ ++ [(y, Ty)] ++ [(x, Tx)] ++ Δ ⊢ M ∈ C.

Definition functional : Prop :=
  (forall s t t', A s t -> A s t' -> t = t') /\ 
  (forall s t u u', R s t u -> R s t u' -> u = u').

Axiom type_unicity : 
  functional -> 
  forall Γ M T1 T2, 
  Γ ⊢ M ∈ T1 ->
  Γ ⊢ M ∈ T2 ->
  T1 = T2.

Definition top_sort (s : Sort) : Prop := ~ (exists s', A s s').

Definition bottom_sort (s : Sort) : Prop := ~ (exists s', A s' s).

Axiom top_sort_lemma : 
  forall Γ x M N s,
  top_sort s ->
  (~ (Γ ⊢ t_sort s ∈ M)) /\ 
  (~ (Γ ⊢ t_var x ∈ t_sort s)) /\ 
  (~ (Γ ⊢ t_app M N ∈ t_sort s)).

Definition persistent : Prop :=
  functional /\
  (forall s s' t , A s t -> A s' t -> s = s') /\ 
  (forall s t u, R s t u -> t = u).

Definition tiered (n : nat) : Prop :=
  exists index_of : Sort -> nat,
    (forall x : Sort, 0 < index_of x /\ index_of x < n + 1) /\
    (forall x y : Sort, index_of x = index_of y -> x = y) /\
    (forall i : nat, 0 < i /\ i < n + 1 -> exists x : Sort, index_of x = i) /\
    (forall x y : Sort, A x y <-> index_of x < n /\ index_of y = S (index_of x)) /\
    (forall x y z : Sort, R x y z -> y = z).

Definition A_neighbor (s : Sort) (p : Sort * Sort) : Prop :=
  A (fst p) (snd p) /\ (fst p = s \/ snd p = s).

Lemma persistent_neighbor_bound :
  persistent ->
  forall s p1 p2 p3,
    A_neighbor s p1 -> A_neighbor s p2 -> A_neighbor s p3 ->
    p1 = p2 \/ p1 = p3 \/ p2 = p3.
Proof.
  intros [[Hfunc _] [Hpers _]] s [x1 y1] [x2 y2] [x3 y3]
    [HA1 [Hx1|Hy1]] [HA2 [Hx2|Hy2]] [HA3 [Hx3|Hy3]].
      - subst. simpl in *. subst. left. f_equal. eauto using Hfunc, Hpers.
      - subst. simpl in *. subst. left. f_equal. eauto using Hfunc, Hpers.
      - subst. simpl in *. subst. right. left. f_equal. eauto using Hfunc, Hpers.
      - subst. simpl in *. subst. right. right. f_equal. eauto using Hfunc, Hpers.
      - subst. simpl in *. subst. right. right. f_equal. eauto using Hfunc, Hpers.
      - subst. simpl in *. subst. right. left. f_equal. eauto using Hfunc, Hpers.
      - subst. simpl in *. subst. left. f_equal. eauto using Hfunc, Hpers.
      - subst. simpl in *. subst. left. f_equal. eauto using Hfunc, Hpers.
Qed.

Reserved Notation "s <A t" (at level 70, no associativity).

Inductive A_lt : Sort -> Sort -> Prop :=
  | A_lt_step  : forall s t, A s t -> s <A t
  | A_lt_trans : forall s t u, A s t -> t <A u -> s <A u

where "s <A t" := (A_lt s t). 

Reserved Notation "s ≤A t" (at level 70, no associativity).

Inductive A_le : Sort -> Sort -> Prop :=
  | A_le_refl : forall s, s ≤A s
  | A_le_step : forall s t u, A s t -> t ≤A u -> s ≤A u

where "s ≤A t" := (A_le s t).

Reserved Notation "s ≈A t" (at level 70, no associativity).

Inductive A_eq : Sort -> Sort -> Prop :=
  | A_eq_refl : forall s, s ≈A s
  | A_eq_step : forall s t, A s t -> s ≈A t
  | A_eq_sym  : forall s t, s ≈A t -> t ≈A s
  | A_eq_trans: forall s t u, s ≈A t -> t ≈A u -> s ≈A u

where "s ≈A t" := (A_eq s t).

Lemma A_le_of_lt : forall s t, s <A t -> s ≤A t.
Proof. induction 1; econstructor; eauto. apply A_le_refl. Qed.

Lemma A_lt_trans' : forall s t u, s <A t -> t <A u -> s <A u.
Proof.
  intros s t u H1 H2.
  induction H1.
  - apply A_lt_trans with t; auto.
  - apply IHA_lt in H2. apply A_lt_trans with t; auto.
Qed.

Fixpoint chain (c : list Sort) : Prop :=
  match c with
  | [] | [_] => True
  | t1 :: (t2 :: _) as rest => A t1 t2 /\ chain rest
  end.

Definition chain_from_to (s t : Sort) (c : list Sort) : Prop :=
  chain c /\ hd_error c = Some s /\ List.last c s = t.

Lemma last_default_irrelevant :
  forall (c : list Sort) (d1 d2 : Sort),
    c <> [] -> last c d1 = last c d2.
Proof.
  induction c as [| a c IH]; intros d1 d2 Hne.
  - contradiction.
  - destruct c as [| b c'].
    + reflexivity.
    + simpl. apply IH. discriminate.
Qed.

Lemma A_le_iff_chain : forall s t,
  s ≤A t <-> exists c, chain_from_to s t c.
Proof.
  intros s t. repeat split.
  - intros H. induction H as [| s t u H1 H2 [c IH]].
    + exists [s]. repeat split.
    + destruct IH as [Q1 [Q2 Q3]]. exists (s :: c). repeat split.
      * destruct c.
        ** reflexivity.
        ** repeat split; auto. simpl in Q2. injection Q2 as Q2. subst. apply H1.
      * destruct c as [| c0 c'] eqn:Hc.
        ** discriminate.
        ** simpl. simpl in Q3.
           injection Q2 as Q2. subst c0.
           destruct c' as [| c1 c''].
           *** exact Q3.
           *** rewrite (last_default_irrelevant (c1 :: c'') s t).
              **** exact Q3.
              **** discriminate.

  - intros [c Hc0]. generalize dependent s.
    induction c as [| a c IH]; intros s [H1 [H2 H3]].
    + discriminate.
    + injection H2 as H2. subst a.
      destruct c as [| c0 c'].
      * simpl in H3. subst t. apply A_le_refl.
      * simpl in H1. destruct H1 as [HA Hchain]. apply A_le_step with (t := c0).
        -- exact HA.
        -- apply IH. repeat split.
           ++ exact Hchain.
           ++ destruct c' as [| c1 c''] eqn:E'.
              ** simpl in H3 |- *. exact H3.
              ** simpl in H3 |- *.
                 destruct c'' as [| c2 c3].
                 --- exact H3.
                 --- rewrite (last_default_irrelevant (c2 :: c3) c0 s).
                     +++ exact H3.
                     +++ discriminate.
Qed.

Lemma persistent_chain_unique_from :
  persistent ->
  forall c1 c2 s,
    chain c1 -> chain c2 ->
    hd_error c1 = Some s -> hd_error c2 = Some s ->
    length c1 = length c2 ->
    c1 = c2.
Proof.
  intros Hpers c1.
  induction c1 as [| a1 c1 IH]; intros c2 s H1 H2 Hh1 Hh2 Hlen.
  - discriminate Hh1.
  - injection Hh1 as Hh1. subst a1. destruct c2 as [| a2 c2].
    + discriminate Hh2.
    + injection Hh2 as Hh2. subst a2. destruct c1 as [| b1 c1'].
      * destruct c2 as [| b2 c2']; auto. discriminate Hlen.
      * destruct c2 as [| b2 c2'].
        -- discriminate Hlen.
        -- simpl in H1, H2.
           destruct H1 as [HA1 Hc1'], H2 as [HA2 Hc2'].
           assert (Hb : b1 = b2).
           { destruct Hpers as [[Hfunc1 _] _].
             eapply Hfunc1; eauto. }
           subst b2.
           f_equal.
           apply IH with (s := b1); auto.
Qed.

Lemma chain_last :
  forall c x y,
    chain (c ++ [x;y]) ->
    A x y.
Proof.
  induction c as [|a c IH].
  - simpl. tauto.
  - destruct c.
    + simpl. tauto.
    + intros. destruct H as [_ H]; auto.
Qed.

Lemma chain_prefix :
  forall c x y,
    chain (c ++ [x; y]) ->
    chain (c ++ [x]).
Proof.
  induction c as [|a c IH].
  - reflexivity.
  - destruct c as [|b c].
    + simpl. tauto.
    + simpl. intros x y [Hab Hchain]. split; auto. apply IH with y; auto.
Qed.

Lemma chain_snoc_inv : forall l x,
  chain (l ++ [x]) ->
  chain l /\ (l <> [] -> A (last l x) x).
Proof.
  induction l as [| a l IH]; intros x Hc.
  - simpl. split; [exact I | intros []; reflexivity].
  - destruct l as [| b l'].
    + simpl in Hc. destruct Hc as [HA _].
      simpl. split; [exact I | intros _; simpl; exact HA].
    + simpl in Hc. destruct Hc as [HAab Hc'].
      destruct (IH x Hc') as [IHchain IHlast].
      split.
      * simpl. split; [exact HAab | exact IHchain].
      * intros _.
        specialize (IHlast ltac:(discriminate)).
        simpl in IHlast.
        simpl.
        exact IHlast.
Qed.

Lemma persistent_chain_unique_to :
  persistent ->
  forall c1 t s1 c2 s2,
    chain_from_to s1 t c1 -> chain_from_to s2 t c2 ->
    length c1 = length c2 ->
    c1 = c2.
Proof.
  intros Hpers c1.
  induction c1 as [| x l IH] using rev_ind; intros t s1 c2 s2 H1 H2 Hlen.
  - destruct H1 as [_ [Hh _]]. discriminate Hh.
  - destruct H1 as [Hc1 [Hh1 Hlast1]].
    rewrite last_last in Hlast1. subst x.
    destruct c2 as [| c2h c2t].
    + destruct H2 as [_ [Hh2 _]]. discriminate Hh2.
    + assert (Hne2 : c2h :: c2t <> []) by discriminate.
      destruct (exists_last Hne2) as [l2 [x2 Hl2eq]].
      rewrite Hl2eq in H2.
      destruct H2 as [Hc2 [Hh2 Hlast2]].
      rewrite last_last in Hlast2. subst x2.
      pose proof (chain_snoc_inv l t Hc1) as [Hcl Hal].
      pose proof (chain_snoc_inv l2 t Hc2) as [Hcl2 Hal2].
      destruct l as [| a l'].
      ++ destruct l2 as [| b l2'].
        * rewrite Hl2eq. reflexivity.
        * exfalso.
          assert (Hlen2 : length (c2h :: c2t) = length ((b :: l2') ++ [t])).
          { rewrite Hl2eq. reflexivity. }
          rewrite length_app in Hlen2.
          simpl in Hlen2, Hlen.
          lia.
      ++ destruct l2 as [| b l2'].
        * exfalso.
          assert (Hlen2 : length (c2h :: c2t) = length ([] ++ [t])).
          { rewrite Hl2eq. reflexivity. }
          simpl in Hlen2.
          rewrite length_app in Hlen.
          simpl in Hlen.
          lia.
        * assert (Hne : a :: l' <> []) by discriminate.
          assert (Hne2' : b :: l2' <> []) by discriminate.
          specialize (Hal Hne). specialize (Hal2 Hne2').
          assert (Ht' : last (a :: l') t = last (b :: l2') t).
          { destruct Hpers as [_ [Hpred _]]. exact (Hpred _ _ t Hal Hal2). }
          assert (Hlen' : length (a :: l') = length (b :: l2')).
          { simpl. rewrite Hl2eq, !length_app in Hlen. simpl in Hlen. lia. }
          assert (Heq : a :: l' = b :: l2').
          { apply (IH (last (a :: l') t) a (b :: l2') b).
            - split; [exact Hcl|]. split; [reflexivity|].
              apply (last_default_irrelevant (a :: l') a t). discriminate.
            - split; [exact Hcl2|]. split; [reflexivity|].
              rewrite Ht'.
              apply (last_default_irrelevant (b :: l2') b t). discriminate.
            - exact Hlen'. }
          rewrite Hl2eq. f_equal. exact Heq.
Qed.

Definition separable : Prop := 
  forall s s', R s s' s' -> s ≈A s'.

Definition atomic : Prop := 
  forall s s', s ≈A s'.

Definition ascending_chain_condition : Prop :=
  forall s : Sort, Acc (fun u v => u <A v) s.

Definition descending_chain_condition : Prop :=
  forall s : Sort, Acc (fun u v => v <A u) s.

Definition bounded : Prop := 
  ascending_chain_condition /\ descending_chain_condition.

Definition weakly_non_dependent : Prop :=
  forall s t u, R s t u -> u ≤A t /\ t ≤A s.

Definition stratified : Prop :=
  ascending_chain_condition /\ weakly_non_dependent.

Definition generalized_non_dependent : Prop :=
  stratified /\ persistent.

Definition bounded_non_dependent : Prop :=
  generalized_non_dependent /\ bounded.

Lemma wf_by_measure :
  forall (T : Type) (Rel : T -> T -> Prop) (f : T -> nat),
    (forall u v, Rel u v -> f u < f v) ->
    forall s, Acc (fun u v => Rel u v) s.
Proof.
  intros T Rel f Hmono s.
  remember (f s) as k eqn:Hk.
  generalize dependent s.
  induction k as [k IH] using (well_founded_induction Wf_nat.lt_wf).
  intros s Hk.
  constructor.
  intros y Hy.
  apply (IH (f y)).
  - rewrite Hk. apply Hmono. exact Hy.
  - reflexivity.
Qed.

Lemma acc_irrefl : 
  forall (T : Type) (Rel : T -> T -> Prop) (x : T), 
  Acc Rel x -> ~ Rel x x.
Proof.
  intros T Rel x Hacc.
  induction Hacc as [x _ IH].
  intro Hxx.
  exact (IH x Hxx Hxx).
Qed.

Lemma A_lt_irrefl : bounded -> forall s, ~ (s <A s).
Proof.
  intros Hbnd s Hlt.
  destruct Hbnd as [Hasc _].
  exact (acc_irrefl Sort (fun u v => u <A v) s (Hasc s) Hlt).
Qed.

Lemma chain_skipn : forall c k, chain c -> chain (skipn k c).
Proof.
  induction c as [| a c IH]; intros k Hc.
  - destruct k; simpl; exact I.
  - destruct k as [| k].
    + simpl. exact Hc.
    + simpl. apply IH.
      destruct c as [| b c']; simpl in Hc.
      * exact I.
      * destruct Hc as [_ Hc]. exact Hc.
Qed.

Lemma chain_firstn : forall c k, chain c -> chain (firstn k c).
Proof.
  induction c as [| a c IH]; intros k Hc.
  - destruct k; simpl; exact I.
  - destruct k as [| k].
    + simpl. exact I.
    + destruct c as [| b c'].
      * simpl. destruct k; exact I.
      * simpl in Hc |- *. destruct Hc as [HAab Hc'].
        assert (Hfk : chain (firstn k (b :: c'))) by (apply IH; simpl; assumption).
        destruct (firstn k (b :: c')) as [| t2 rest] eqn:Efk.
        -- exact I.
        -- split.
           ++ destruct k as [| k'].
              ** simpl in Efk. discriminate Efk.
              ** simpl in Efk. injection Efk as Ht2. subst t2. exact HAab.
           ++ exact Hfk.
Qed.

Lemma hd_error_skipn : forall c k a,
  nth_error c k = Some a -> hd_error (skipn k c : list Sort) = Some a.
Proof.
  induction c as [| x c IH]; intros k a Hnth.
  - destruct k; discriminate.
  - destruct k as [| k].
    + simpl in Hnth |- *. exact Hnth.
    + simpl in Hnth |- *. apply IH. exact Hnth.
Qed.

Lemma last_skipn : forall c k d,
  k < length c -> last (skipn k c : list Sort) d = last c d.
Proof.
  induction c as [| x c IH]; intros k d Hk.
  - simpl in Hk. lia.
  - destruct k as [| k].
    + reflexivity.
    + simpl. destruct c as [| y c'].
      * simpl in Hk. lia.
      * apply IH. simpl in *. lia.
Qed.

Lemma hd_error_firstn : forall c k a,
  hd_error c = Some a -> 0 < k -> hd_error (firstn k c : list Sort) = Some a.
Proof.
  intros c k a Hhd Hk.
  destruct c as [| x c]; [discriminate |].
  simpl in Hhd. injection Hhd as Hhd. subst x.
  destruct k as [| k]; [lia |]. reflexivity.
Qed.

Lemma last_firstn_nth : forall c k a d,
  nth_error c k = Some a -> last (firstn (S k) c : list Sort) d = a.
Proof.
  induction c as [| x c IH]; intros k a d Hnth.
  - destruct k as [| k']; simpl in Hnth; discriminate Hnth.
  - destruct k as [| k].
    + simpl in Hnth. injection Hnth as Hnth. subst a. simpl.
      destruct c; reflexivity.
    + simpl in Hnth. simpl.
      destruct c as [| y c'].
      * destruct k as [| k'']; simpl in Hnth; discriminate Hnth.
      * apply (IH k a d Hnth).
Qed.

Lemma length_skipn : forall (c : list Sort) k, 
  k <= length c -> length (skipn k c) = length c - k.
Proof. intros c k Hk. apply length_skipn. Qed.

Lemma length_firstn_le : forall (c : list Sort) k, 
  k <= length c -> length (firstn k c) = k.
Proof. intros c k Hk. rewrite length_firstn. lia. Qed.

Lemma chain_pos_length_A_lt :
  forall c a b, chain_from_to a b c -> 2 <= length c -> a <A b.
Proof.
  induction c as [| x l IH] using rev_ind; intros a b [Hc [Hh Hl]] Hlen.
  - simpl in Hlen. lia.
  - rewrite last_last in Hl. subst x.
    destruct l as [| y l'].
    + simpl in Hlen. lia.
    + destruct (chain_snoc_inv (y :: l') b Hc) as [Hcl Hal].
      specialize (Hal ltac:(discriminate)).
      destruct l' as [| z l''].
      * simpl in Hh. injection Hh as Hh. subst y.
        apply A_lt_step. exact Hal.
      * apply A_lt_trans' with (last (y :: z :: l'') b).
        -- apply IH.
           ++ split; [exact Hcl |]. split; [exact Hh |].
              apply last_default_irrelevant. discriminate.
           ++ simpl. lia.
        -- apply A_lt_step. exact Hal.
Qed.

Lemma nth_error_exists : forall (c : list Sort) k, 
  k < length c -> exists a, nth_error c k = Some a.
Proof.
  induction c as [| x c IH]; intros k Hk.
  - simpl in Hk. lia.
  - destruct k as [| k'].
    + exists x. reflexivity.
    + simpl. apply IH. simpl in Hk. lia.
Qed.

Lemma chain_same_end_relates :
  persistent ->
  forall s u t c1 c2,
    chain_from_to s t c1 -> chain_from_to u t c2 ->
    s <A u \/ s = u \/ u <A s.
Proof.
  intros Hpers s u t c1 c2 H1 H2.
  assert (Htri : length c1 < length c2 \/ length c1 = length c2 \/ length c2 < length c1) by lia.
  destruct Htri as [Hlt | [Heq | Hgt]].

  - (* c1 shorter: u <A s *)
    right. right.
    destruct H1 as [Hc1 [Hh1 Hl1]].
    destruct H2 as [Hc2 [Hh2 Hl2]].
    remember (length c2 - length c1) as k eqn:Hkeq.
    assert (Hc1ne : 1 <= length c1).
    { destruct c1 as [| ? ?]; simpl.
      - discriminate Hh1.
      - lia. }
    assert (Hk1 : 0 < k) by lia.
    assert (Hklt : k < length c2) by lia.
    destruct (nth_error_exists c2 k Hklt) as [a Hnth].
    pose proof (hd_error_skipn c2 k a Hnth) as Hheadskip.
    pose proof (chain_skipn c2 k Hc2) as Hchainskip.
    pose proof (last_skipn c2 k a Hklt) as Hlastskip.
    assert (Hlast_a_u : last c2 a = last c2 u).
    { apply last_default_irrelevant. destruct c2; [discriminate Hh2 | discriminate]. }
    assert (Hlastskip' : last (skipn k c2) a = t).
    { rewrite Hlastskip, Hlast_a_u. exact Hl2. }
    assert (Hsuffix : chain_from_to a t (skipn k c2)).
    { split; [exact Hchainskip | split; [exact Hheadskip | exact Hlastskip']]. }
    assert (Hlensuf : length (skipn k c2) = length c1).
    { rewrite (length_skipn c2 k ltac:(lia)). lia. }
    assert (Heqc : c1 = skipn k c2).
    { apply (persistent_chain_unique_to Hpers c1 t s (skipn k c2) a).
      - split; [exact Hc1 | split; [exact Hh1 | exact Hl1]].
      - exact Hsuffix.
      - symmetry. exact Hlensuf. }
    assert (Hsa : s = a).
    { assert (Hh1' : hd_error c1 = Some s) by exact Hh1.
      rewrite Heqc in Hh1'. rewrite Hheadskip in Hh1'. injection Hh1' as Hh1'. symmetry. exact Hh1'. }
    assert (Hprefix : chain_from_to u s (firstn (S k) c2)).
    { split.
      - apply chain_firstn. exact Hc2.
      - split.
        + apply hd_error_firstn; [exact Hh2 | lia].
        + pose proof (last_firstn_nth c2 k a u Hnth) as Hlf.
          rewrite Hsa. exact Hlf. }
    assert (Hlenpref : length (firstn (S k) c2) = S k).
    { apply length_firstn_le. lia. }
    apply (chain_pos_length_A_lt (firstn (S k) c2) u s Hprefix).
    rewrite Hlenpref. lia.

  - (* equal length: s = u *)
    right. left.
    destruct H1 as [Hc1 [Hh1 Hl1]].
    destruct H2 as [Hc2 [Hh2 Hl2]].
    assert (Heqc : c1 = c2).
    { apply (persistent_chain_unique_to Hpers c1 t s c2 u).
      - split; [exact Hc1 | split; [exact Hh1 | exact Hl1]].
      - split; [exact Hc2 | split; [exact Hh2 | exact Hl2]].
      - exact Heq. }
    rewrite Heqc in Hh1. rewrite Hh1 in Hh2. injection Hh2 as Hh2. exact Hh2.

  - (* c2 shorter: s <A u, mirror of the first case *)
    left.
    destruct H1 as [Hc1 [Hh1 Hl1]].
    destruct H2 as [Hc2 [Hh2 Hl2]].
    remember (length c1 - length c2) as k eqn:Hkeq.
    assert (Hc2ne : 1 <= length c2).
    { destruct c2 as [| ? ?]; simpl.
      - discriminate Hh2.
      - lia. }
    assert (Hk1 : 0 < k) by lia.
    assert (Hklt : k < length c1) by lia.
    destruct (nth_error_exists c1 k Hklt) as [a Hnth].
    pose proof (hd_error_skipn c1 k a Hnth) as Hheadskip.
    pose proof (chain_skipn c1 k Hc1) as Hchainskip.
    pose proof (last_skipn c1 k a Hklt) as Hlastskip.
    assert (Hlast_a_s : last c1 a = last c1 s).
    { apply last_default_irrelevant. destruct c1; [discriminate Hh1 | discriminate]. }
    assert (Hlastskip' : last (skipn k c1) a = t).
    { rewrite Hlastskip, Hlast_a_s. exact Hl1. }
    assert (Hsuffix : chain_from_to a t (skipn k c1)).
    { split; [exact Hchainskip | split; [exact Hheadskip | exact Hlastskip']]. }
    assert (Hlensuf : length (skipn k c1) = length c2).
    { rewrite (length_skipn c1 k ltac:(lia)). lia. }
    assert (Heqc : c2 = skipn k c1).
    { apply (persistent_chain_unique_to Hpers c2 t u (skipn k c1) a).
      - split; [exact Hc2 | split; [exact Hh2 | exact Hl2]].
      - exact Hsuffix.
      - symmetry. exact Hlensuf. }
    assert (Hua : u = a).
    { assert (Hh2' : hd_error c2 = Some u) by exact Hh2.
      rewrite Heqc in Hh2'. rewrite Hheadskip in Hh2'. injection Hh2' as Hh2'. symmetry. exact Hh2'. }
    assert (Hprefix : chain_from_to s u (firstn (S k) c1)).
    { split.
      - apply chain_firstn. exact Hc1.
      - split.
        + apply hd_error_firstn; [exact Hh1 | lia].
        + pose proof (last_firstn_nth c1 k a s Hnth) as Hlf.
          rewrite Hua. exact Hlf. }
    assert (Hlenpref : length (firstn (S k) c1) = S k).
    { apply length_firstn_le. lia. }
    apply (chain_pos_length_A_lt (firstn (S k) c1) s u Hprefix).
    rewrite Hlenpref. lia.
Qed.

Lemma chain_same_start_relates :
  persistent ->
  forall s t u c1 c2,
    chain_from_to s t c1 -> chain_from_to s u c2 ->
    t <A u \/ t = u \/ u <A t.
Proof.
  intros Hpers s t u c1 c2 H1 H2.
  assert (Htri : length c1 < length c2 \/ length c1 = length c2 \/ length c2 < length c1) by lia.
  destruct Htri as [Hlt | [Heq | Hgt]].

  - (* c1 shorter: t <A u *)
    left.
    destruct H1 as [Hc1 [Hh1 Hl1]].
    destruct H2 as [Hc2 [Hh2 Hl2]].
    assert (Hc1ne : 1 <= length c1).
    { destruct c1 as [| ? ?]; simpl.
      - discriminate Hh1.
      - lia. }
    remember (length c1 - 1) as j eqn:Hjeq.
    assert (Hjlt : j < length c2) by lia.
    destruct (nth_error_exists c2 j Hjlt) as [a Hnth].
    assert (Hlenpref : length (firstn (length c1) c2) = length c1).
    { apply length_firstn_le. lia. }
    assert (Hchainpref : chain (firstn (length c1) c2)).
    { apply chain_firstn. exact Hc2. }
    assert (Hheadpref : hd_error (firstn (length c1) c2) = Some s).
    { apply hd_error_firstn; [exact Hh2 | lia]. }
    assert (Heqc : c1 = firstn (length c1) c2).
    { apply (persistent_chain_unique_from Hpers c1 (firstn (length c1) c2) s).
      - exact Hc1.
      - exact Hchainpref.
      - exact Hh1.
      - exact Hheadpref.
      - symmetry. exact Hlenpref. }
    assert (Hat : a = t).
    { pose proof (last_firstn_nth c2 j a s Hnth) as Hlf.
      assert (HSj : S j = length c1) by lia.
      rewrite HSj in Hlf.
      rewrite <- Heqc in Hlf.
      rewrite Hl1 in Hlf.
      symmetry. exact Hlf. }
    pose proof (hd_error_skipn c2 j a Hnth) as Hheadskip.
    pose proof (chain_skipn c2 j Hc2) as Hchainskip.
    pose proof (last_skipn c2 j a Hjlt) as Hlastskip.
    assert (Hlast_a_s : last c2 a = last c2 s).
    { apply last_default_irrelevant. destruct c2; [discriminate Hh2 | discriminate]. }
    assert (Hlastskip' : last (skipn j c2) a = u).
    { rewrite Hlastskip, Hlast_a_s. exact Hl2. }
    assert (Hsuffix : chain_from_to t u (skipn j c2)).
    { rewrite <- Hat.
      split; [exact Hchainskip | split; [exact Hheadskip | exact Hlastskip']]. }
    assert (Hlensuf : length (skipn j c2) = length c2 - j).
    { apply length_skipn. lia. }
    apply (chain_pos_length_A_lt (skipn j c2) t u Hsuffix).
    rewrite Hlensuf. lia.

  - (* equal length: t = u *)
    right. left.
    destruct H1 as [Hc1 [Hh1 Hl1]].
    destruct H2 as [Hc2 [Hh2 Hl2]].
    assert (Heqc : c1 = c2).
    { apply (persistent_chain_unique_from Hpers c1 c2 s).
      - exact Hc1.
      - exact Hc2.
      - exact Hh1.
      - exact Hh2.
      - exact Heq. }
    rewrite Heqc in Hl1.
    rewrite Hl1 in Hl2.
    exact Hl2.

  - (* c2 shorter: u <A t, mirror of first case *)
    right. right.
    destruct H1 as [Hc1 [Hh1 Hl1]].
    destruct H2 as [Hc2 [Hh2 Hl2]].
    assert (Hc2ne : 1 <= length c2).
    { destruct c2 as [| ? ?]; simpl.
      - discriminate Hh2.
      - lia. }
    remember (length c2 - 1) as j eqn:Hjeq.
    assert (Hjlt : j < length c1) by lia.
    destruct (nth_error_exists c1 j Hjlt) as [a Hnth].
    assert (Hlenpref : length (firstn (length c2) c1) = length c2).
    { apply length_firstn_le. lia. }
    assert (Hchainpref : chain (firstn (length c2) c1)).
    { apply chain_firstn. exact Hc1. }
    assert (Hheadpref : hd_error (firstn (length c2) c1) = Some s).
    { apply hd_error_firstn; [exact Hh1 | lia]. }
    assert (Heqc : c2 = firstn (length c2) c1).
    { apply (persistent_chain_unique_from Hpers c2 (firstn (length c2) c1) s).
      - exact Hc2.
      - exact Hchainpref.
      - exact Hh2.
      - exact Hheadpref.
      - symmetry. exact Hlenpref. }
    assert (Hau : a = u).
    { pose proof (last_firstn_nth c1 j a s Hnth) as Hlf.
      assert (HSj : S j = length c2) by lia.
      rewrite HSj in Hlf.
      rewrite <- Heqc in Hlf.
      rewrite Hl2 in Hlf.
      symmetry. exact Hlf. }
    pose proof (hd_error_skipn c1 j a Hnth) as Hheadskip.
    pose proof (chain_skipn c1 j Hc1) as Hchainskip.
    pose proof (last_skipn c1 j a Hjlt) as Hlastskip.
    assert (Hlast_a_s : last c1 a = last c1 s).
    { apply last_default_irrelevant. destruct c1; [discriminate Hh1 | discriminate]. }
    assert (Hlastskip' : last (skipn j c1) a = t).
    { rewrite Hlastskip, Hlast_a_s. exact Hl1. }
    assert (Hsuffix : chain_from_to u t (skipn j c1)).
    { rewrite <- Hau.
      split; [exact Hchainskip | split; [exact Hheadskip | exact Hlastskip']]. }
    assert (Hlensuf : length (skipn j c1) = length c1 - j).
    { apply length_skipn. lia. }
    apply (chain_pos_length_A_lt (skipn j c1) u t Hsuffix).
    rewrite Hlensuf. lia.
Qed.

Lemma A_eq_lt_case :
  persistent -> bounded ->
  forall s t, s ≈A t -> s <A t \/ s = t \/ t <A s.
Proof.
  intros Hpers Hbnd s t Heq.
  induction Heq as
    [ s
    | s t Hst
    | s t Heq IH
    | s t u Heq1 IH1 Heq2 IH2 ].

  - right. left. reflexivity.

  - left. apply A_lt_step. exact Hst.

  - destruct IH as [IH | [IH | IH]].
    + right. right. exact IH.
    + right. left. symmetry. exact IH.
    + left. exact IH.

  - destruct IH1 as [Hst | [Hst | Hst]]; destruct IH2 as [Htu | [Htu | Htu]].
    + left. apply A_lt_trans' with t; auto.
    + subst u. left. exact Hst.
    + destruct (A_le_iff_chain s t) as [Hfwd1 _].
      destruct (A_le_iff_chain u t) as [Hfwd2 _].
      assert (Hc1 : exists c, chain_from_to s t c) by (apply Hfwd1; apply A_le_of_lt; exact Hst).
      assert (Hc2 : exists c, chain_from_to u t c) by (apply Hfwd2; apply A_le_of_lt; exact Htu).
      destruct Hc1 as [c1 Hc1]. destruct Hc2 as [c2 Hc2].
      apply (chain_same_end_relates Hpers s u t c1 c2 Hc1 Hc2).
    + subst t. left. exact Htu.
    + subst t. subst u. right. left. reflexivity.
    + subst t. right. right. exact Htu.
    + destruct (A_le_iff_chain t s) as [Hfwd1 _].
      destruct (A_le_iff_chain t u) as [Hfwd2 _].
      assert (Hc1 : exists c, chain_from_to t s c) by (apply Hfwd1; apply A_le_of_lt; exact Hst).
      assert (Hc2 : exists c, chain_from_to t u c) by (apply Hfwd2; apply A_le_of_lt; exact Htu).
      destruct Hc1 as [c1 Hc1]. destruct Hc2 as [c2 Hc2].
      apply (chain_same_start_relates Hpers t s u c1 c2 Hc1 Hc2).
    + subst u. right. right. exact Hst.
    + right. right. apply A_lt_trans' with t; auto.
Qed.

Lemma A_lt_total :
  persistent -> bounded -> atomic ->
  forall s t, s <A t \/ s = t \/ t <A s.
Proof.
  intros Hpers Hbnd Hato s t.
  apply (A_eq_lt_case Hpers Hbnd s t (Hato s t)).
Qed.

Axiom exists_top :
  bounded -> 
  forall s0 : Sort, exists top, s0 ≤A top /\ ~ exists t, top <A t.

Axiom exists_bottom :
  bounded -> 
  forall s0 : Sort, exists bottom, bottom ≤A s0 /\ ~ exists t, t <A bottom.

Lemma A_le_split : forall s t, s ≤A t -> s = t \/ s <A t.
Proof.
  intros s t H. induction H as [s | s t u Hst H IH].
  - left. reflexivity.
  - destruct IH as [IH | IH].
    + subst. right. apply A_lt_step. exact Hst.
    + right. apply A_lt_trans' with t; [apply A_lt_step; exact Hst | exact IH].
Qed.

Lemma A_le_lt_antisym :
  bounded ->
  forall s t, s ≤A t -> t <A s -> False.
Proof.
  intros Hbnd s t Hle Hlt.
  destruct (A_le_split s t Hle) as [Heq | Hlt2].
  - subst. exact (A_lt_irrefl Hbnd t Hlt).
  - exact (A_lt_irrefl Hbnd s (A_lt_trans' s t s Hlt2 Hlt)).
Qed.

Lemma top_unique :
  persistent -> bounded -> atomic ->
  forall top1 top2, 
  (forall s, s ≤A top1) -> 
  (forall s, s ≤A top2) -> 
  top1 = top2.
Proof.
  intros Hpers Hbnd Hato top1 top2 H1 H2.
  destruct (A_lt_total Hpers Hbnd Hato top1 top2) as [Hlt | [Heq | Hgt]].
  - exfalso. apply (A_le_lt_antisym Hbnd top2 top1 (H1 top2) Hlt).
  - exact Heq.
  - exfalso. apply (A_le_lt_antisym Hbnd top1 top2 (H2 top1) Hgt).
Qed.

Lemma bottom_unique :
  persistent -> bounded -> atomic ->
  forall bottom1 bottom2, 
  (forall s, bottom1 ≤A s) -> 
  (forall s, bottom2 ≤A s) -> 
  bottom1 = bottom2.
Proof.
  intros Hpers Hbnd Hato bottom1 bottom2 H1 H2.
  destruct (A_lt_total Hpers Hbnd Hato bottom1 bottom2) as [Hlt | [Heq | Hgt]].
  - exfalso. apply (A_le_lt_antisym Hbnd bottom2 bottom1 (H2 bottom1) Hlt).
  - exact Heq.
  - exfalso. apply (A_le_lt_antisym Hbnd bottom1 bottom2 (H1 bottom2) Hgt).
Qed.

Lemma nth_error_lt_length : forall (l : list Sort) i a,
  nth_error l i = Some a -> i < length l.
Proof.
  induction l as [| x l IH]; intros i a H.
  - destruct i; discriminate.
  - destruct i as [| i].
    + simpl. lia.
    + simpl in H. simpl. specialize (IH i a H). lia.
Qed.

Lemma chain_nth_A : forall c i a b,
  chain c -> nth_error c i = Some a -> nth_error c (S i) = Some b -> A a b.
Proof.
  induction c as [| x c IH]; intros i a b Hc Ha Hb.
  - destruct i as [| i]; simpl in Ha; discriminate Ha.
  - destruct i as [| i].
    + simpl in Ha. injection Ha as Ha. subst a.
      simpl in Hb.
      destruct c as [| y c'].
      * discriminate Hb.
      * simpl in Hc. destruct Hc as [HAxy _].
        injection Hb as Hb. subst b.
        exact HAxy.
    + simpl in Ha, Hb.
      destruct c as [| y c'].
      * destruct i as [| i']; simpl in Ha; discriminate Ha.
      * simpl in Hc. destruct Hc as [_ Hc'].
        apply (IH i a b Hc' Ha Hb).
Qed.

Lemma last_nth_error : forall (l : list Sort) d,
  l <> [] -> nth_error l (length l - 1) = Some (last l d).
Proof.
  induction l as [| x l IH]; intros d Hne.
  - contradiction.
  - destruct l as [| y l'].
    + reflexivity.
    + simpl. specialize (IH d ltac:(discriminate)). simpl in IH. rewrite <- IH. f_equal. lia.
Qed.

Lemma chain_lt_A : forall c i j a b,
  chain c -> i < j -> nth_error c i = Some a -> nth_error c j = Some b -> a <A b.
Proof.
  intros c i j a b Hc Hij.
  revert a b.
  induction j as [j IH] using (well_founded_induction Wf_nat.lt_wf).
  intros a b Ha Hb.
  destruct j as [| j'].
  - lia.
  - destruct (Nat.eq_dec i j') as [Heq | Hneq].
    + subst i. apply A_lt_step.
      apply (chain_nth_A c j' a b Hc Ha Hb).
    + assert (Hij' : i < j') by lia.
      destruct (nth_error_exists c j' ltac:(apply (nth_error_lt_length c (S j') b) in Hb; lia)) as [m Hm].
      apply A_lt_trans' with m.
      * apply (IH j' ltac:(lia) ltac:(lia) a m Ha Hm).
      * apply A_lt_step. apply (chain_nth_A c j' m b Hc Hm Hb).
Qed.

Lemma chain_pos_unique :
  persistent -> bounded ->
  forall c i j s, chain c -> nth_error c i = Some s -> nth_error c j = Some s -> i = j.
Proof.
  intros Hpers Hbnd c i j s Hc Hi Hj.
  destruct (Nat.lt_trichotomy i j) as [Hlt | [Heq | Hgt]]; auto.
  - exfalso. apply (A_lt_irrefl Hbnd s).
    apply (chain_lt_A c i j s s Hc Hlt Hi Hj).
  - exfalso. apply (A_lt_irrefl Hbnd s).
    apply (chain_lt_A c j i s s Hc Hgt Hj Hi).
Qed.

Lemma persistent_chain_prefix :
  persistent ->
  forall c1 c2 s,
    chain c1 -> chain c2 ->
    hd_error c1 = Some s -> hd_error c2 = Some s ->
    length c1 <= length c2 ->
    c1 = firstn (length c1) c2.
Proof.
  intros Hpers c1 c2 s Hc1 Hc2 Hh1 Hh2 Hlen.
  apply (persistent_chain_unique_from Hpers c1 (firstn (length c1) c2) s).
  - exact Hc1.
  - apply chain_firstn. exact Hc2.
  - exact Hh1.
  - apply hd_error_firstn; [exact Hh2 |].
    destruct c1; [discriminate Hh1 | simpl; lia].
  - symmetry. apply length_firstn_le. exact Hlen.
Qed.

Lemma app_nonempty_r : forall (l1 l2 : list Sort), l2 <> [] -> l1 ++ l2 <> [].
Proof.
  intros l1 l2 Hne Heq.
  apply Hne. destruct l1; simpl in Heq; auto; discriminate.
Qed.

Lemma last_app_r : forall (l1 l2 : list Sort) d, l2 <> [] -> last (l1 ++ l2) d = last l2 d.
Proof.
  induction l1 as [| x l1 IH]; intros l2 d Hne.
  - reflexivity.
  - simpl. destruct (l1 ++ l2) as [| y ys] eqn:E.
    + exfalso. apply (app_nonempty_r l1 l2 Hne). exact E.
    + rewrite <- E. apply IH. exact Hne.
Qed.

Lemma hd_error_app_l : forall (l1 l2 : list Sort) a,
  hd_error l1 = Some a -> hd_error (l1 ++ l2) = Some a.
Proof.
  intros l1 l2 a H. destruct l1; simpl in H; [discriminate | simpl; exact H].
Qed.

Lemma nth_error_app_l : forall (l1 l2 : list Sort) n,
  n < length l1 -> nth_error (l1 ++ l2) n = nth_error l1 n.
Proof.
  induction l1 as [| x l1 IH]; intros l2 n Hn.
  - simpl in Hn. lia.
  - destruct n as [| n'].
    + reflexivity.
    + simpl. apply IH. simpl in Hn. lia.
Qed.

Lemma nth_error_firstn : forall (l : list Sort) k i,
  i < k -> nth_error (firstn k l) i = nth_error l i.
Proof.
  induction l as [| x l IH]; intros k i Hik.
  - destruct k; simpl; destruct i; reflexivity.
  - destruct k as [| k'].
    + lia.
    + destruct i as [| i'].
      * reflexivity.
      * simpl. apply IH. lia.
Qed.

Lemma chain_app_general : forall (l1 l2 : list Sort) (m : Sort),
  chain (l1 ++ [m]) ->
  chain (m :: l2) ->
  chain (l1 ++ m :: l2).
Proof.
  induction l1 as [| x l1 IH]; intros l2 m H1 H2.
  - simpl. exact H2.
  - simpl in H1 |- *.
    destruct l1 as [| y l1'].
    + simpl in H1. destruct H1 as [HAxm _].
      simpl. split; [exact HAxm | exact H2].
    + simpl in H1. destruct H1 as [HAxy Hrest].
      simpl. split; [exact HAxy | apply IH; [exact Hrest | exact H2]].
Qed.

Lemma chain_from_to_app :
  forall c1 c2 b s t,
    chain_from_to b s c1 ->
    chain_from_to s t c2 ->
    chain_from_to b t (c1 ++ tl c2).
Proof.
  intros c1 c2 b s t [Hc1 [Hh1 Hl1]] [Hc2 [Hh2 Hl2]].
  destruct c2 as [| x2 c2'].
  - discriminate Hh2.
  - simpl in Hh2. injection Hh2 as Hh2. subst x2.
    simpl.
    assert (Hc1ne : c1 <> []).
    { destruct c1; [discriminate Hh1 | discriminate]. }
    destruct (exists_last Hc1ne) as [l1 [e Hc1eq]].
    assert (He : e = s).
    { assert (H1 : last c1 b = e).
      { rewrite Hc1eq. rewrite last_last. reflexivity. }
      rewrite Hl1 in H1. symmetry. exact H1. }
    subst e.
    destruct c2' as [| x2' c2''].
    + assert (Ht : t = s).
      { simpl in Hl2. symmetry. exact Hl2. }
      subst t.
      rewrite app_nil_r.
      split; [exact Hc1 | split; [exact Hh1 | exact Hl1]].
    + set (c2' := x2' :: c2'') in *.
      assert (Hc2'ne : c2' <> []) by (subst c2'; discriminate).
      split.
      * rewrite Hc1eq.
        rewrite <- app_assoc. simpl.
        apply (chain_app_general l1 c2' s).
        -- rewrite <- Hc1eq. exact Hc1.
        -- exact Hc2.
      * split.
        -- apply (hd_error_app_l c1 c2' b Hh1).
        -- rewrite (last_app_r c1 c2' b Hc2'ne).
           assert (Hl2' : last c2' s = t).
           { simpl in Hl2. exact Hl2. }
           rewrite <- Hl2'.
           apply last_default_irrelevant.
           exact Hc2'ne.
Qed.

Lemma chain_length_eq_of_same_ends :
  persistent -> bounded ->
  forall e c b t,
    chain_from_to b t e -> chain_from_to b t c ->
    length e = length c.
Proof.
  intros Hpers Hbnd e c b t He Hc.
  destruct He as [Hce [Hhe Hle]].
  destruct Hc as [Hcc [Hhc Hlc]].
  assert (Hene : e <> []) by (destruct e; [discriminate Hhe | discriminate]).
  assert (Hcne : c <> []) by (destruct c; [discriminate Hhc | discriminate]).
  assert (Hene1 : 1 <= length e) by (destruct e; [contradiction Hene; reflexivity | simpl; lia]).
  assert (Hcne1 : 1 <= length c) by (destruct c; [contradiction Hcne; reflexivity | simpl; lia]).
  destruct (Nat.lt_trichotomy (length e) (length c)) as [Hlt | [Heq | Hgt]]; auto.
  - exfalso.
    assert (Hpre : e = firstn (length e) c).
    { apply (persistent_chain_prefix Hpers e c b); [exact Hce | exact Hcc | exact Hhe | exact Hhc | lia]. }
    assert (Hte : nth_error e (length e - 1) = Some t).
    { rewrite (last_nth_error e b Hene). rewrite Hle. reflexivity. }
    assert (Htc : nth_error c (length c - 1) = Some t).
    { rewrite (last_nth_error c b Hcne). rewrite Hlc. reflexivity. }
    assert (Hte'' : nth_error (firstn (length e) c) (length e - 1) = Some t).
    { rewrite <- Hpre. exact Hte. }
    assert (Hte' : nth_error c (length e - 1) = Some t).
    { rewrite (nth_error_firstn c (length e) (length e - 1)) in Hte''.
      - exact Hte''.
      - lia. }
    assert (Heq2 : length e - 1 = length c - 1).
    { apply (chain_pos_unique Hpers Hbnd c (length e - 1) (length c - 1) t Hcc Hte' Htc). }
    lia.
  - exfalso.
    assert (Hpre : c = firstn (length c) e).
    { apply (persistent_chain_prefix Hpers c e b); [exact Hcc | exact Hce | exact Hhc | exact Hhe | lia]. }
    assert (Hte : nth_error e (length e - 1) = Some t).
    { rewrite (last_nth_error e b Hene). rewrite Hle. reflexivity. }
    assert (Htc : nth_error c (length c - 1) = Some t).
    { rewrite (last_nth_error c b Hcne). rewrite Hlc. reflexivity. }
    assert (Htc'' : nth_error (firstn (length c) e) (length c - 1) = Some t).
    { rewrite <- Hpre. exact Htc. }
    assert (Htc' : nth_error e (length c - 1) = Some t).
    { rewrite (nth_error_firstn e (length c) (length c - 1)) in Htc''.
      - exact Htc''.
      - lia. }
    assert (Heq2 : length c - 1 = length e - 1).
    { apply (chain_pos_unique Hpers Hbnd e (length c - 1) (length e - 1) t Hce Htc' Hte). }
    lia.
Qed.

Lemma tiered_iff_persistent_bounded_atomic :
  (exists n, tiered n) <-> persistent /\ bounded /\ atomic.
Proof.
  split.

  - intros [n [index_of [index_r [index_i [index_t [HA HR]]]]]]. split.
    + repeat split; auto.
      * intros s t u HA1 HA2. 
      apply HA in HA1 as [_ HA1].
      apply HA in HA2 as [_ HA2].
      apply index_i. rewrite HA1, HA2. reflexivity.
      * intros s t u v HR1 HR2.
      apply HR in HR1. apply HR in HR2. rewrite <- HR1. exact HR2.
      * intros s t u HA1 HA2.
      apply HA in HA1 as [_ HA1].
      apply HA in HA2 as [_ HA2].
      apply index_i. apply eq_add_S. rewrite <- HA1. exact HA2.
    
    + split. 

      * unfold bounded. 
      assert (A_lt_index_1 : forall s t, s <A t -> index_of s < index_of t).
      intros s t H. induction H as [s t Hst | s t u Hst _ IH].
        apply HA in Hst as [_ Heq]. lia.
        apply HA in Hst as [_ Heq]. lia.
      assert (A_lt_index_2 : forall s t, t <A s -> n - index_of s < n - index_of t).
      intros t s H. 
      induction H as [s t Hst | s t u Hst _ IH].
        apply HA in Hst as [_ Heq]. destruct (index_r s) as [_ Hsn], (index_r t) as [_ Htn]. lia.
        apply HA in Hst as [_ Heq]. destruct (index_r s) as [_ Hsn], (index_r t) as [_ Htn]. lia.
      split. 
        ** unfold ascending_chain_condition. intros s.
        apply (wf_by_measure Sort (fun u v => u <A v) index_of A_lt_index_1).
        ** unfold descending_chain_condition. intros s.
        apply (wf_by_measure Sort (fun u v => v <A u) (fun s => n - index_of s) A_lt_index_2).
      
      * assert (chain_eq : forall k i, i + k < n + 1 -> 0 < i ->
                forall x y, index_of x = i -> index_of y = i + k -> x ≈A y).
      { induction k as [| k IH]; intros i Hbound Hipos x y Hx Hy.
        - assert (Hy0 : index_of y = i) by lia.
          assert (Heq : index_of x = index_of y) by lia.
          apply index_i in Heq. subst y. apply A_eq_refl.
        - assert (Hrange : 0 < i + k /\ i + k < n + 1) by lia.
          destruct (index_t (i + k) Hrange) as [z Hz].
          assert (Hxz : x ≈A z).
          { apply IH with i; auto; lia. }
          assert (Hzy : z ≈A y).
          { apply A_eq_step. apply HA. split.
            - rewrite Hz. lia.
            - rewrite Hz, Hy. lia. }
          apply A_eq_trans with z; auto. }
      
      intros s s'.
      pose proof (index_r s) as [Hs1 Hs2].
      pose proof (index_r s') as [Hs1' Hs2'].
      assert (Hcase : index_of s <= index_of s' \/ index_of s' <= index_of s) by lia.
      destruct Hcase as [Hle | Hge].
        ** assert (Hk : index_of s' = index_of s + (index_of s' - index_of s)) by lia.
        apply (chain_eq (index_of s' - index_of s) (index_of s)); lia || auto.
        
        ** apply A_eq_sym.
        assert (Hk : index_of s = index_of s' + (index_of s - index_of s')) by lia.
        apply (chain_eq (index_of s - index_of s') (index_of s')); lia || auto.
  
  - intros [Hpers [Hbnd Hato]].
  destruct (classic (exists s : Sort, True)) as [[s0 _] | Hempty].
  + destruct (classic (exists s1 s2 : Sort, s1 <> s2)) as [[s1 [s2 Hne]] | Hone].
    * (* |S| >= 2 *)
      destruct (exists_top Hbnd s1) as [top [_ Htopmax]].
      destruct (exists_bottom Hbnd s1) as [bot [_ Hbotmin]].
      assert (Htop : forall s, s ≤A top).
      { intros s. destruct (A_lt_total Hpers Hbnd Hato s top) as [H|[H|H]].
        - apply A_le_of_lt; exact H.
        - subst; apply A_le_refl.
        - exfalso; apply Htopmax; exists s; exact H. }
      assert (Hbot : forall s, bot ≤A s).
      { intros s. destruct (A_lt_total Hpers Hbnd Hato s bot) as [H|[H|H]].
        - exfalso; apply Hbotmin; exists s; exact H.
        - subst; apply A_le_refl.
        - apply A_le_of_lt; exact H. }
      destruct (A_le_iff_chain bot top) as [Hfwd _].
      destruct (Hfwd (Hbot top)) as [c Hc].
      exists (length c).

      assert (Hpos : forall s : Sort, exists! i, nth_error c i = Some s).
      { intros s.
        pose proof (Hbot s) as Hbs.
        pose proof (Htop s) as Hst.
        destruct (proj1 (A_le_iff_chain bot s) Hbs) as [c1 Hc1].
        destruct (proj1 (A_le_iff_chain s top) Hst) as [c2 Hc2].
        assert (He : chain_from_to bot top (c1 ++ tl c2)).
        { apply (chain_from_to_app c1 c2 bot s top Hc1 Hc2). }
        assert (Hlen : length (c1 ++ tl c2) = length c).
        { apply (chain_length_eq_of_same_ends Hpers Hbnd (c1 ++ tl c2) c bot top He Hc). }
        assert (Heqec : c1 ++ tl c2 = c).
        { apply (persistent_chain_unique_from Hpers (c1 ++ tl c2) c bot).
          - destruct He as [Hce _]. exact Hce.
          - destruct Hc as [Hcc _]. exact Hcc.
          - destruct He as [_ [Hhe _]]. exact Hhe.
          - destruct Hc as [_ [Hhc _]]. exact Hhc.
          - exact Hlen. }
        destruct Hc1 as [Hcc1 [Hhc1 Hlc1]].
        assert (Hc1ne : c1 <> []) by (destruct c1; [discriminate Hhc1 | discriminate]).
        assert (Hpos_s : nth_error c1 (length c1 - 1) = Some s).
        { rewrite (last_nth_error c1 bot Hc1ne). rewrite Hlc1. reflexivity. }
        assert (Hc1ge1 : 1 <= length c1)
          by (destruct c1; [contradiction Hc1ne; reflexivity | simpl; lia]).
        assert (Hpos_e : nth_error (c1 ++ tl c2) (length c1 - 1) = Some s).
        { rewrite (nth_error_app_l c1 (tl c2) (length c1 - 1)).
          - exact Hpos_s.
          - lia. }
        rewrite Heqec in Hpos_e.
        exists (length c1 - 1).
        split.
        - exact Hpos_e.
        - intros i' Hi'. symmetry.
          apply (chain_pos_unique Hpers Hbnd c i' (length c1 - 1) s).
          + destruct Hc as [Hcc _]; exact Hcc.
          + exact Hi'.
          + exact Hpos_e. }
      assert (Hchoice : forall s, {i | nth_error c i = Some s}).
      { intros s. apply constructive_indefinite_description.
        destruct (Hpos s) as [i [Hi _]]. exists i. exact Hi. }
      set (index_of := fun s => S (proj1_sig (Hchoice s))).
      exists index_of. 
      
      split.

      (* range *)
      intros x. unfold index_of.
      pose proof (proj2_sig (Hchoice x)) as Hnth.
      pose proof (nth_error_lt_length c (proj1_sig (Hchoice x)) x Hnth) as Hlt.
      lia.

      split.

      (* injectivity *)
      intros x y Heq. unfold index_of in Heq.
      assert (Hixy : proj1_sig (Hchoice x) = proj1_sig (Hchoice y)) by lia.
      pose proof (proj2_sig (Hchoice x)) as Hx.
      pose proof (proj2_sig (Hchoice y)) as Hy.
      rewrite Hixy in Hx.
      assert (Hsome : Some x = Some y) by (rewrite <- Hx; exact Hy).
      injection Hsome as Hsome. exact Hsome.

      split.

      (* surjectivity *)
      intros i [Hi1 Hi2].
      assert (Hilt : i - 1 < length c) by lia.
      destruct (nth_error_exists c (i - 1) Hilt) as [x Hx].
      exists x.
      destruct (Hpos x) as [i0 [Hi0 Huniq]].
      assert (Heq0 : i0 = i - 1) by (apply Huniq; exact Hx).
      assert (Heqchoice : proj1_sig (Hchoice x) = i0).
      { symmetry. apply Huniq. exact (proj2_sig (Hchoice x)). }
      unfold index_of. rewrite Heqchoice. lia.

      split.

      (* A clause *)
      intros x y. split.

      assert (Hcne : c <> []).
      { destruct Hc as [_ [Hh _]]. destruct c; [discriminate Hh | discriminate]. }

      (* -> *)
      intro HAxy.
      assert (Hxlt : x <A y) by (apply A_lt_step; exact HAxy).
      assert (Hxnetop : x <> top).
      { intro Heq. subst x. apply Htopmax. exists y. exact Hxlt. }

      destruct (Hchoice x) as [ix Hix] eqn:Ex.
      assert (Hix_index : index_of x = S ix).
      { unfold index_of. simpl. rewrite Ex. reflexivity. }
      assert (Hixlt : ix < length c) by (apply (nth_error_lt_length c ix x); exact Hix).

      assert (Hixne : ix <> length c - 1).
      { intro Heq.
        apply Hxnetop.
        assert (Hlast : nth_error c (length c - 1) = Some top).
        { destruct Hc as [_ [_ Hl]].
          rewrite (last_nth_error c bot Hcne). rewrite Hl. reflexivity. }
        clear Ex.
        rewrite Heq in Hix.
        rewrite Hix in Hlast.
        injection Hlast as Hlast.
        exact Hlast. }

      assert (Hsix : S ix < length c) by lia.
      destruct (nth_error_exists c (S ix) Hsix) as [z Hz].
      assert (HAxz : A x z).
      { apply (chain_nth_A c ix x z);
          [destruct Hc as [Hcc _]; exact Hcc | exact Hix | exact Hz]. }
      assert (Hzy : z = y).
      { destruct Hpers as [[Hfunc1 _] _]. apply (Hfunc1 x); [exact HAxz | exact HAxy]. }
      subst z.

      destruct (Hchoice y) as [iy Hiy] eqn:Ey.
      assert (Hiy_index : index_of y = S iy).
      { unfold index_of. simpl. rewrite Ey. reflexivity. }
      assert (Hiyeq : iy = S ix).
      { destruct (Hpos y) as [i0 [Hi0 Huniq0]].
        assert (E1 : i0 = iy) by (apply Huniq0; exact Hiy).
        assert (E2 : i0 = S ix) by (apply Huniq0; exact Hz).
        lia. }

      split; lia.

      (* <- *)
      intros [Hlt Heqsucc].
      destruct (Hchoice x) as [ix Hix] eqn:Ex.
      assert (Hix_index : index_of x = S ix).
      { unfold index_of. simpl. rewrite Ex. reflexivity. }
      assert (Hsix : S ix < length c).
      { rewrite Hix_index in Hlt. exact Hlt. }
      destruct (nth_error_exists c (S ix) Hsix) as [z Hz].
      assert (HAxz : A x z).
      { apply (chain_nth_A c ix x z);
          [destruct Hc as [Hcc _]; exact Hcc | exact Hix | exact Hz]. }

      destruct (Hchoice y) as [iy Hiy] eqn:Ey.
      assert (Hiy_index : index_of y = S iy).
      { unfold index_of. simpl. rewrite Ey. reflexivity. }
      assert (Hiyeq : iy = S ix).
      { rewrite Hix_index, Hiy_index in Heqsucc. lia. }
      assert (Hzy : z = y).
      { assert (Hiy' : nth_error c (S ix) = Some y).
        { rewrite <- Hiyeq. exact Hiy. }
        rewrite Hz in Hiy'.
        injection Hiy' as Hiy'.
        exact Hiy'. }
      subst z.
      exact HAxz.

      (* R shape *)
      intros x y z HR. destruct Hpers as [_ [_ Hshape]]. eauto.


    * (* |S| = 1 *)
      exists 1, (fun _ => 1). 
      split. lia.
      split. intros x y _. destruct (classic (x = y)) as [|Hxy]; [auto|].
         exfalso. apply Hone. exists x, y. exact Hxy. 
      split. intros i [Hi1 Hi2]. exists s0. lia.
      split. intros x y. split. 
        ** intros HAxy. exfalso. assert (Hxy : x = y). 
        { destruct (classic (x = y)) as [|Hxy]; [auto|]. 
              exfalso. apply Hone. exists x, y. exact Hxy. }
          subst y. apply (A_lt_irrefl Hbnd x). apply A_lt_step. exact HAxy.
        ** intros [Hlt _]. lia.
        ** intros x y z HR. destruct Hpers as [_ [_ Hshape]]. eauto.
  + (* |S| = 0 *)
    exists 0, (fun _ => 0). split. 
    intros x. exfalso. apply Hempty. exists x. apply I. split. 
    intros x y _. exfalso. apply Hempty. exists x. apply I. split. 
    intros i [Hi1 Hi2]. lia. split. 
    intros x y. split. 
    intro HAxy. exfalso. apply Hempty. exists x. apply I. 
    intros [Hlt _]. lia.
    intros x y z HR. destruct Hpers as [_ [_ Hshape]]. eauto.
Qed.

Definition disjoint_union_of_tiered : Prop :=
  exists (n_of : Sort -> nat) (index_of : Sort -> nat),
    (forall s t, A s t -> s ≈A t) /\
    (forall s t u, R s t u -> s ≈A t) /\
    (forall s t, s ≈A t -> n_of s = n_of t) /\
    (forall s, 0 < index_of s /\ index_of s < n_of s + 1) /\
    (forall s t, s ≈A t -> index_of s = index_of t -> s = t) /\
    (forall s i, 0 < i -> i <= n_of s -> exists t, t ≈A s /\ index_of t = i) /\
    (forall s t, A s t <-> (s ≈A t /\ index_of s < n_of s /\ index_of t = S (index_of s))) /\
    (forall s t u, R s t u -> t = u).

Lemma A_lt_in_class :
  forall (HAclass : forall s t, A s t -> s ≈A t),
  forall u v, u <A v -> u ≈A v.
Proof.
  intros HAclass u v Huv.
  induction Huv as [u v Huv | u v w Huv _ IH].
  - apply A_eq_step. exact Huv.
  - apply A_eq_trans with v.
    + apply A_eq_step. exact Huv.
    + exact IH.
Qed.

Lemma A_lt_index_incr :
  forall (index_of : Sort -> nat) (n_of : Sort -> nat),
  forall (HA : forall s t, A s t <-> (s ≈A t /\ index_of s < n_of s /\ index_of t = S (index_of s))),
  forall u v, u <A v -> index_of u < index_of v.
Proof.
  intros index_of n_of HA u v Huv.
  induction Huv as [u v Huv | u v w Huv _ IH].
  - apply HA in Huv as [_ [_ Heq]]. lia.
  - apply HA in Huv as [_ [_ Heq]]. lia.
Qed.

Lemma A_lt_n_of_const :
  forall (n_of : Sort -> nat),
  forall (HAclass : forall s t, A s t -> s ≈A t)
         (Hnconst : forall s t, s ≈A t -> n_of s = n_of t),
  forall u v, u <A v -> n_of u = n_of v.
Proof.
  intros n_of HAclass Hnconst u v Huv.
  apply Hnconst.
  apply (A_lt_in_class HAclass u v Huv).
Qed.

Lemma A_le_in_class : forall s t, s ≤A t -> s ≈A t.
Proof.
  intros s t H. induction H as [s | s t u Hst H IH].
  - apply A_eq_refl.
  - apply A_eq_trans with t; [apply A_eq_step; exact Hst | exact IH].
Qed.

Lemma chain_elem_in_class : forall c a,
  chain (a :: c) -> forall i x, nth_error (a :: c) i = Some x -> x ≈A a.
Proof.
  induction c as [| y c IH]; intros a Hc i x Hn.
  - destruct i as [| i'].
    + simpl in Hn. injection Hn as Hn. subst x. apply A_eq_refl.
    + destruct i' as [| i'']; simpl in Hn; discriminate Hn.
  - simpl in Hc. destruct Hc as [HAay Hc'].
    destruct i as [| i'].
    + simpl in Hn. injection Hn as Hn. subst x. apply A_eq_refl.
    + simpl in Hn.
      assert (Hxy : x ≈A y) by (apply (IH y Hc' i' x Hn)).
      apply A_eq_trans with y. exact Hxy. apply A_eq_sym. apply A_eq_step. exact HAay. 
Qed.

Lemma chain_pos_in_class : forall c s0 bot,
  chain c -> hd_error c = Some bot -> bot ≈A s0 ->
  forall i a, nth_error c i = Some a -> a ≈A s0.
Proof.
  intros c s0 bot Hc Hh Hbs i a Hn.
  destruct c as [| x c'].
  - discriminate Hh.
  - simpl in Hh. injection Hh as Hh. subst x.
    assert (Ha_bot : a ≈A bot) by (apply (chain_elem_in_class c' bot Hc i a Hn)).
    apply A_eq_trans with bot; [exact Ha_bot | exact Hbs].
Qed.

Lemma class_tiered :
  persistent -> bounded ->
  forall s0 : Sort,
  exists n index_of,
    (forall t, t ≈A s0 -> 0 < index_of t /\ index_of t < n + 1) /\
    (forall t u, t ≈A s0 -> u ≈A s0 -> index_of t = index_of u -> t = u) /\
    (forall i, 0 < i -> i < n + 1 -> exists t, t ≈A s0 /\ index_of t = i) /\
    (forall t u, t ≈A s0 -> (A t u <-> (index_of t < n /\ index_of u = S (index_of t)))).
Proof.
  intros Hpers Hbnd s0.
  destruct (exists_top Hbnd s0) as [top [Hs0top Htopmax]].
  destruct (exists_bottom Hbnd s0) as [bot [Hbots0 Hbotmin]].
  assert (Htops0 : top ≈A s0) by (apply A_eq_sym; apply A_le_in_class; exact Hs0top).
  assert (Hbots0' : bot ≈A s0) by (apply A_le_in_class; exact Hbots0).

  assert (Htop : forall s, s ≈A s0 -> s ≤A top).
  { intros s Hs.
    assert (Hstop : s ≈A top) by (apply A_eq_trans with s0; [exact Hs | apply A_eq_sym; exact Htops0]).
    destruct (A_eq_lt_case Hpers Hbnd s top Hstop) as [Hlt | [Heq | Hgt]].
    - apply A_le_of_lt; exact Hlt.
    - subst; apply A_le_refl.
    - exfalso; apply Htopmax; exists s; exact Hgt. }

  assert (Hbot : forall s, s ≈A s0 -> bot ≤A s).
  { intros s Hs.
    assert (Hsbot : s ≈A bot) by (apply A_eq_trans with s0; [exact Hs | apply A_eq_sym; exact Hbots0']).
    destruct (A_eq_lt_case Hpers Hbnd s bot Hsbot) as [Hlt | [Heq | Hgt]].
    - exfalso; apply Hbotmin; exists s; exact Hlt.
    - subst; apply A_le_refl.
    - apply A_le_of_lt; exact Hgt. }

  destruct (A_le_iff_chain bot top) as [Hfwd _].
  assert (Hbotop : bot ≤A top) by (apply Hbot; exact Htops0).
  destruct (Hfwd Hbotop) as [c Hc].

  assert (Hcne : c <> []).
  { destruct Hc as [_ [Hh _]]. destruct c; [discriminate Hh | discriminate]. }

  assert (Hpos : forall s : Sort, s ≈A s0 -> exists! i, nth_error c i = Some s).
  { intros s Hs.
    pose proof (Hbot s Hs) as Hbs.
    pose proof (Htop s Hs) as Hst.
    destruct (proj1 (A_le_iff_chain bot s) Hbs) as [c1 Hc1].
    destruct (proj1 (A_le_iff_chain s top) Hst) as [c2 Hc2].
    assert (He : chain_from_to bot top (c1 ++ tl c2)) by (apply (chain_from_to_app c1 c2 bot s top Hc1 Hc2)).
    assert (Hlen : length (c1 ++ tl c2) = length c)
      by (apply (chain_length_eq_of_same_ends Hpers Hbnd (c1 ++ tl c2) c bot top He Hc)).
    assert (Heqec : c1 ++ tl c2 = c).
    { apply (persistent_chain_unique_from Hpers (c1 ++ tl c2) c bot).
      - destruct He as [Hce _]; exact Hce.
      - destruct Hc as [Hcc _]; exact Hcc.
      - destruct He as [_ [Hhe _]]; exact Hhe.
      - destruct Hc as [_ [Hhc _]]; exact Hhc.
      - exact Hlen. }
    destruct Hc1 as [Hcc1 [Hhc1 Hlc1]].
    assert (Hc1ne : c1 <> []) by (destruct c1; [discriminate Hhc1 | discriminate]).
    assert (Hpos_s : nth_error c1 (length c1 - 1) = Some s)
      by (rewrite (last_nth_error c1 bot Hc1ne); rewrite Hlc1; reflexivity).
    assert (Hc1ge1 : 1 <= length c1) by (destruct c1; [contradiction Hc1ne; reflexivity | simpl; lia]).
    assert (Hpos_e : nth_error (c1 ++ tl c2) (length c1 - 1) = Some s).
    { rewrite (nth_error_app_l c1 (tl c2) (length c1 - 1)); [exact Hpos_s | lia]. }
    rewrite Heqec in Hpos_e.
    exists (length c1 - 1). split.
    - exact Hpos_e.
    - intros i' Hi'. symmetry.
      apply (chain_pos_unique Hpers Hbnd c i' (length c1 - 1) s).
      + destruct Hc as [Hcc _]; exact Hcc.
      + exact Hi'.
      + exact Hpos_e. }

  assert (Hchoice : forall s, {i : nat |
    (s ≈A s0 -> nth_error c i = Some s) /\ (~ s ≈A s0 -> i = 0)}).
  { intros s.
    apply constructive_indefinite_description.
    destruct (classic (s ≈A s0)) as [Hs | Hs].
    - destruct (Hpos s Hs) as [i [Hi _]]. exists i.
      split; [intros _; exact Hi | intros Hcontra; contradiction].
    - exists 0. split; [intros Hcontra; contradiction | intros _; reflexivity]. }

  set (index_of := fun s => S (proj1_sig (Hchoice s))).
  exists (length c), index_of.
  split.

  - (* range *)
    intros t Ht. unfold index_of.
    destruct (Hchoice t) as [it Hit] eqn:E. simpl.
    pose proof (proj1 Hit Ht) as Hnth.
    pose proof (nth_error_lt_length c it t Hnth) as Hlt.
    lia.

  - split. (* injectivity *)
    intros t u Ht Hu Heq. unfold index_of in Heq.
    destruct (Hchoice t) as [it Hit] eqn:Et.
    destruct (Hchoice u) as [iu Hiu] eqn:Eu.
    simpl in Heq.
    assert (Hitu : it = iu) by lia.
    pose proof (proj1 Hit Ht) as Hntht.
    pose proof (proj1 Hiu Hu) as Hnthu.
    rewrite Hitu in Hntht.
    rewrite Hntht in Hnthu.
    injection Hnthu as Hnthu. exact Hnthu.
    split.

    (* surjectivity *)
    intros i Hi1 Hi2.
    assert (Hilt : i - 1 < length c) by lia.
    destruct (nth_error_exists c (i - 1) Hilt) as [t Ht].
    assert (Hclass : t ≈A s0).
    { destruct Hc as [Hcc [Hhc _]].
      apply (chain_pos_in_class c s0 bot Hcc Hhc Hbots0' (i - 1) t Ht). }
    exists t. split; [exact Hclass |].
    unfold index_of.
    destruct (Hchoice t) as [it Hit] eqn:E. simpl.
    destruct (Hpos t Hclass) as [i0 [Hi0 Huniq0]].
    assert (Heqchoice : it = i0) by (symmetry; apply Huniq0; exact (proj1 Hit Hclass)).
    assert (Heq2 : i - 1 = i0) by (symmetry; apply Huniq0; exact Ht).
    lia.

    (* A-iff *)
    intros t u Ht. split.
    + intro HAtu.
      assert (Htlt : t <A u) by (apply A_lt_step; exact HAtu).
      assert (Htnetop : t <> top).
      { intro Heq. subst t. apply Htopmax. exists u. exact Htlt. }
      destruct (Hchoice t) as [it Hit] eqn:Et.
      assert (Hit_index : index_of t = S it) by (unfold index_of; rewrite Et; reflexivity).
      pose proof (proj1 Hit Ht) as Hntht.
      assert (Hitlt : it < length c) by (apply (nth_error_lt_length c it t); exact Hntht).
      assert (Hitne : it <> length c - 1).
      { intro Heq. apply Htnetop.
        assert (Hlast : nth_error c (length c - 1) = Some top).
        { destruct Hc as [_ [_ Hl]]; rewrite (last_nth_error c bot Hcne); rewrite Hl; reflexivity. }
        assert (Hit' : nth_error c (length c - 1) = Some t) by (rewrite <- Heq; exact Hntht).
        rewrite Hit' in Hlast. injection Hlast as Hlast. exact Hlast. }
      assert (Hsit : S it < length c) by lia.
      destruct (nth_error_exists c (S it) Hsit) as [z Hz].
      assert (HAtz : A t z).
      { apply (chain_nth_A c it t z); [destruct Hc as [Hcc _]; exact Hcc | exact Hntht | exact Hz]. }
      assert (Hzu : z = u).
      { destruct Hpers as [[Hfunc1 _] _]. apply (Hfunc1 t); [exact HAtz | exact HAtu]. }
      subst z.
      assert (Hu0 : u ≈A s0).
      { apply A_eq_trans with t; [apply A_eq_sym; apply A_eq_step; exact HAtu | exact Ht]. }
      destruct (Hchoice u) as [iu Hiu] eqn:Eu.
      assert (Hiu_index : index_of u = S iu) by (unfold index_of; rewrite Eu; reflexivity).
      assert (Hiueq : iu = S it).
      { destruct (Hpos u Hu0) as [i0 [Hi0 Huniq0]].
        assert (E1 : i0 = iu) by (apply Huniq0; exact (proj1 Hiu Hu0)).
        assert (E2 : i0 = S it) by (apply Huniq0; exact Hz).
        lia. }
      split; lia.
    + intros [Hlt Heqsucc].
      destruct (Hchoice t) as [it Hit] eqn:Et.
      assert (Hit_index : index_of t = S it) by (unfold index_of; rewrite Et; reflexivity).
      assert (Hsit : S it < length c) by (rewrite Hit_index in Hlt; exact Hlt).
      destruct (nth_error_exists c (S it) Hsit) as [z Hz].
      assert (HAtz : A t z).
      { apply (chain_nth_A c it t z); [destruct Hc as [Hcc _]; exact Hcc | exact (proj1 Hit Ht) | exact Hz]. }
      destruct (Hchoice u) as [iu Hiu] eqn:Eu.
      assert (Hiu_index : index_of u = S iu) by (unfold index_of; rewrite Eu; reflexivity).
      assert (Hiueq : iu = S it) by (rewrite Hit_index, Hiu_index in Heqsucc; lia).
      assert (Hu0 : u ≈A s0).
      { destruct (classic (u ≈A s0)) as [H | H]; [exact H |].
        exfalso.
        assert (Hiu0 : iu = 0) by (apply (proj2 Hiu); exact H).
        lia. }
      assert (Hzu : z = u).
      { assert (Hiu' : nth_error c (S it) = Some u) by (rewrite <- Hiueq; exact (proj1 Hiu Hu0)).
        rewrite Hz in Hiu'. injection Hiu' as Hiu'. exact Hiu'. }
      subst z. exact HAtz.
Qed.

Lemma A_lt_pred : forall t u, t <A u -> exists w, A w u.
Proof.
  intros t u H. induction H as [t u Htu | t v u Htv _ IH].
  - exists t. exact Htu.
  - exact IH.
Qed.

Lemma no_pred_unique_in_class :
  persistent -> bounded ->
  forall s t u,
    t ≈A s -> u ≈A s ->
    (~ exists v, v ≈A s /\ A v t) ->
    (~ exists v, v ≈A s /\ A v u) ->
    t = u.
Proof.
  intros Hpers Hbnd s t u Ht Hu Hnpt Hnpu.
  destruct (classic (t = u)) as [Heq | Hneq]; [exact Heq |].
  assert (Htu : t ≈A u) by (apply A_eq_trans with s; [exact Ht | apply A_eq_sym; exact Hu]).
  destruct (A_eq_lt_case Hpers Hbnd t u Htu) as [Hlt | [Heq | Hgt]].
  - exfalso. destruct (A_lt_pred t u Hlt) as [w Hw].
    apply Hnpu. exists w. split; [| exact Hw].
    apply A_eq_trans with u; [apply A_eq_step; exact Hw | exact Hu].
  - exact Heq.
  - exfalso. destruct (A_lt_pred u t Hgt) as [w Hw].
    apply Hnpt. exists w. split; [| exact Hw].
    apply A_eq_trans with t; [apply A_eq_step; exact Hw | exact Ht].
Qed.

Lemma class_tiered_unique :
  persistent -> bounded ->
  forall s n1 n2 f1 f2,
    (forall t, t ≈A s -> 0 < f1 t /\ f1 t < n1 + 1) ->
    (forall t u, t ≈A s -> u ≈A s -> f1 t = f1 u -> t = u) ->
    (forall i, 0 < i -> i < n1 + 1 -> exists t, t ≈A s /\ f1 t = i) ->
    (forall t u, t ≈A s -> (A t u <-> (f1 t < n1 /\ f1 u = S (f1 t)))) ->
    (forall t, t ≈A s -> 0 < f2 t /\ f2 t < n2 + 1) ->
    (forall t u, t ≈A s -> u ≈A s -> f2 t = f2 u -> t = u) ->
    (forall i, 0 < i -> i < n2 + 1 -> exists t, t ≈A s /\ f2 t = i) ->
    (forall t u, t ≈A s -> (A t u <-> (f2 t < n2 /\ f2 u = S (f2 t)))) ->
    n1 = n2 /\ forall t, t ≈A s -> f1 t = f2 t.
Proof.
  intros Hpers Hbnd s n1 n2 f1 f2
    Hr1 Hi1 Hs1 HA1 Hr2 Hi2 Hs2 HA2.

  assert (Hnp1 : forall i, i = 1 -> forall t, t ≈A s -> f1 t = i ->
                 ~ exists v, v ≈A s /\ A v t).
  { intros i Hi1eq t Ht Hf1t [v [Hv HAvt]].
    apply (HA1 v t Hv) in HAvt as [_ Heq].
    destruct (Hr1 v Hv) as [Hf1vpos _].
    lia. }

  assert (Hmain : forall i, 0 < i -> i < n1 + 1 -> i < n2 + 1 ->
                    forall t, t ≈A s -> f1 t = i -> f2 t = i).
  { intros i.
    induction i as [i IH] using (well_founded_induction Wf_nat.lt_wf).
    intros Hi0 Hi1lt Hi2lt t Ht Hf1t.
    destruct i as [| i'].
    - lia.
    - destruct i' as [| i''].
      + (* i = 1: base case via no-predecessor uniqueness *)
        destruct (Hs2 1 ltac:(lia) Hi2lt) as [u [Hu Hf2u]].
        assert (Ht_np : ~ exists v, v ≈A s /\ A v t).
        { intros [v [Hv HAvt]].
          apply (HA1 v t Hv) in HAvt as [_ Heq].
          destruct (Hr1 v Hv) as [Hf1vpos _].
          rewrite Hf1t in Heq. lia. }
        assert (Hu_np : ~ exists v, v ≈A s /\ A v u).
        { intros [v [Hv HAvu]]. 
          apply (HA2 v u Hv) in HAvu as [_ Heq].
          destruct (Hr2 v Hv) as [Hf1vpos _].
          rewrite Hf2u in Heq.
          lia. }
        assert (Htu : t = u) by (apply (no_pred_unique_in_class Hpers Hbnd s t u Ht Hu Ht_np Hu_np)).
        rewrite Htu. exact Hf2u.
      + (* successor case *)
        destruct (Hs1 (S i'') ltac:(lia) ltac:(lia)) as [v [Hv Hf1v]].
        assert (HAvt : A v t).
        { apply (HA1 v t Hv). split; [lia | rewrite Hf1v, Hf1t; reflexivity]. }
        assert (Hf2v : f2 v = S i'') by (apply (IH (S i'') ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) v Hv Hf1v)).
        apply (HA2 v t Hv) in HAvt as [_ Hf2t].
        rewrite Hf2v in Hf2t. exact Hf2t. }

  assert (Hmain2 : forall i, 0 < i -> i < n1 + 1 -> i < n2 + 1 ->
                    forall t, t ≈A s -> f2 t = i -> f1 t = i).
  { intros i.
    induction i as [i IH] using (well_founded_induction Wf_nat.lt_wf).
    intros Hi0 Hi1lt Hi2lt t Ht Hf2t.
    destruct i as [| i'].
    - lia.
    - destruct i' as [| i''].
      + destruct (Hs1 1 ltac:(lia) Hi1lt) as [u [Hu Hf1u]].
        assert (Ht_np : ~ exists v, v ≈A s /\ A v t).
        { intros [v [Hv HAvt]]. 
          apply (HA2 v t Hv) in HAvt as [_ Heq].
          destruct (Hr2 v Hv) as [Hf1vpos _]. 
          rewrite Hf2t in Heq. 
          lia. }
        assert (Hu_np : ~ exists v, v ≈A s /\ A v u).
        { intros [v [Hv HAvu]]. 
          apply (HA1 v u Hv) in HAvu as [_ Heq]. 
          destruct (Hr1 v Hv) as [Hf1vpos _].
          rewrite Hf1u in Heq. 
          lia. }
        assert (Htu : t = u) by (apply (no_pred_unique_in_class Hpers Hbnd s t u Ht Hu Ht_np Hu_np)).
        rewrite Htu. exact Hf1u.
      + destruct (Hs2 (S i'') ltac:(lia) ltac:(lia)) as [v [Hv Hf2v]].
        assert (HAvt : A v t).
        { apply (HA2 v t Hv). split; [lia | rewrite Hf2v, Hf2t; reflexivity]. }
        assert (Hf1v : f1 v = S i'') by (apply (IH (S i'') ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) v Hv Hf2v)).
        apply (HA1 v t Hv) in HAvt as [_ Hf1t].
        rewrite Hf1v in Hf1t. exact Hf1t. }

  assert (Hn : n1 = n2).
  { destruct (Nat.lt_trichotomy n1 n2) as [Hlt | [Heq | Hgt]]; auto.
    - exfalso.
      destruct (Hs2 (n1+1) ltac:(lia) ltac:(lia)) as [u [Hu Hf2u]].
      destruct (Hr2 u Hu) as [_ Hf2u_lt].
      destruct (Nat.lt_trichotomy (f1 u) (n1+1)) as [Hc1 | [Hc2 | Hc3]].
      + assert (Hf1lt : f1 u < n1 + 1) by lia.
        destruct (Hr1 u Hu) as [Hf1pos _].
        assert (Hf2u' : f2 u = f1 u) by (apply (Hmain (f1 u) Hf1pos Hf1lt ltac:(lia) u Hu eq_refl)).
        rewrite Hf2u in Hf2u'. lia.
      + destruct (Hr1 u Hu) as [_ Hf1u_lt]. lia.
      + destruct (Hr1 u Hu) as [_ Hf1u_lt]. lia.
    - exfalso.
      destruct (Hs1 (n2+1) ltac:(lia) ltac:(lia)) as [u [Hu Hf1u]].
      destruct (Hr1 u Hu) as [_ Hf1u_lt].
      destruct (Nat.lt_trichotomy (f2 u) (n2+1)) as [Hc1 | [Hc2 | Hc3]].
      + assert (Hf2lt : f2 u < n2 + 1) by lia.
        destruct (Hr2 u Hu) as [Hf2pos _].
        assert (Hf1u' : f1 u = f2 u) by (apply (Hmain2 (f2 u) Hf2pos ltac:(lia) ltac:(lia) u Hu eq_refl)).
        rewrite Hf1u in Hf1u'. lia.
      + destruct (Hr2 u Hu) as [_ Hf2u_lt]. lia.
      + destruct (Hr2 u Hu) as [_ Hf2u_lt]. lia. }

  split; [exact Hn |].
  intros t Ht.
  destruct (Hr1 t Ht) as [Hpos Hlt]. symmetry.
  apply (Hmain (f1 t) Hpos ltac:(lia) ltac:(lia) t Ht eq_refl).
Qed.

Lemma persistent_bounded_seperable_iff_disjoint_union_of_tiered : 
  (persistent /\ bounded /\ separable) <-> disjoint_union_of_tiered.
Proof.
  split.

 - intros [Hpers [Hbnd Hsep]].
    assert (Hwit : forall s0 : Sort, {p : nat * (Sort -> nat) |
      (forall t, t ≈A s0 -> 0 < snd p t /\ snd p t < fst p + 1) /\
      (forall t u, t ≈A s0 -> u ≈A s0 -> snd p t = snd p u -> t = u) /\
      (forall i, 0 < i -> i < fst p + 1 -> exists t, t ≈A s0 /\ snd p t = i) /\
      (forall t u, t ≈A s0 -> (A t u <-> (snd p t < fst p /\ snd p u = S (snd p t))))}).
    { intros s0.
      apply constructive_indefinite_description.
      destruct (class_tiered Hpers Hbnd s0) as [n [index_of H]].
      exists (n, index_of). exact H. }

    set (n_of := fun s => fst (proj1_sig (Hwit s))).
    set (index_of := fun s => snd (proj1_sig (Hwit s)) s).

    assert (Hprop : forall s, 
      (forall t, t ≈A s -> 0 < snd (proj1_sig (Hwit s)) t /\ snd (proj1_sig (Hwit s)) t < fst (proj1_sig (Hwit s)) + 1) /\
      (forall t u, t ≈A s -> u ≈A s -> snd (proj1_sig (Hwit s)) t = snd (proj1_sig (Hwit s)) u -> t = u) /\
      (forall i, 0 < i -> i < fst (proj1_sig (Hwit s)) + 1 -> exists t, t ≈A s /\ snd (proj1_sig (Hwit s)) t = i) /\
      (forall t u, t ≈A s -> (A t u <-> (snd (proj1_sig (Hwit s)) t < fst (proj1_sig (Hwit s)) /\ snd (proj1_sig (Hwit s)) u = S (snd (proj1_sig (Hwit s)) t))))).
    { intros s. exact (proj2_sig (Hwit s)). }

    assert (Hagree : forall s t, s ≈A t -> forall u, u ≈A s ->
      fst (proj1_sig (Hwit s)) = fst (proj1_sig (Hwit t)) /\
      snd (proj1_sig (Hwit s)) u = snd (proj1_sig (Hwit t)) u).
        { intros s t Hst u Hu.
      destruct (Hprop s) as [Hr1 [Hi1 [Hs1 HA1]]].
      destruct (Hprop t) as [Hr2 [Hi2 [Hs2 HA2]]].
      assert (Hr2' : forall v, v ≈A s -> 0 < snd (proj1_sig (Hwit t)) v /\ snd (proj1_sig (Hwit t)) v < fst (proj1_sig (Hwit t)) + 1).
      { intros v Hv. apply Hr2. apply A_eq_trans with s; [exact Hv | exact Hst]. }
      assert (Hi2' : forall v w, v ≈A s -> w ≈A s -> snd (proj1_sig (Hwit t)) v = snd (proj1_sig (Hwit t)) w -> v = w).
      { intros v w Hv Hw. apply Hi2; apply A_eq_trans with s; auto. }
      assert (Hs2' : forall i, 0 < i -> i < fst (proj1_sig (Hwit t)) + 1 -> exists v, v ≈A s /\ snd (proj1_sig (Hwit t)) v = i).
      { intros i Hi0 Hilt. destruct (Hs2 i Hi0 Hilt) as [v [Hv Hvi]]. exists v. split; [| exact Hvi].
        apply A_eq_trans with t; [exact Hv | apply A_eq_sym; exact Hst]. }
      assert (HA2' : forall v w, v ≈A s -> (A v w <-> (snd (proj1_sig (Hwit t)) v < fst (proj1_sig (Hwit t)) /\ snd (proj1_sig (Hwit t)) w = S (snd (proj1_sig (Hwit t)) v)))).
      { intros v w Hv. apply HA2. apply A_eq_trans with s; [exact Hv | exact Hst]. }
      destruct (class_tiered_unique Hpers Hbnd s
                  (fst (proj1_sig (Hwit s))) (fst (proj1_sig (Hwit t)))
                  (snd (proj1_sig (Hwit s))) (snd (proj1_sig (Hwit t)))
                  Hr1 Hi1 Hs1 HA1 Hr2' Hi2' Hs2' HA2') as [Hn Hf].
      split; [exact Hn | apply Hf; exact Hu]. }

    exists n_of, index_of.
    split.

    (* A s t -> s ≈A t *)
    intros s t HAst.
    destruct (Hprop s) as [_ [_ [_ HAiff]]].
    assert (Hss : s ≈A s) by apply A_eq_refl.
    apply A_eq_step; exact HAst.
    split.

    (* R s t u -> s ≈A t *)
    intros s t u HR.
    destruct Hpers as [_ [_ Hshape]].
    assert (Htu : t = u) by (apply (Hshape s t u); exact HR).
    apply (Hsep s t). rewrite <- Htu in HR. exact HR.
    split.

    (* n_of constant on class *)
    intros s t Hst. unfold n_of.
    destruct (Hagree s t Hst s) as [Hn _]; [apply A_eq_refl |]. exact Hn.
    split.

    (* range *)
    intros s. unfold index_of.
    destruct (Hprop s) as [Hrange _].
    apply (Hrange s). apply A_eq_refl.
    split.

    (* injectivity *)
    intros s t Hst Heq. unfold index_of, n_of in *.
    assert (Hs_ind : snd (proj1_sig (Hwit s)) s = snd (proj1_sig (Hwit t)) t) by exact Heq.
    destruct (Hagree s t Hst s) as [_ Hval]; [apply A_eq_refl |].
    rewrite Hval in Hs_ind.
    destruct (Hprop t) as [_ [Hinj _]].
    apply (Hinj s t).
    apply A_eq_trans with s; [apply A_eq_refl | exact Hst].
    apply A_eq_refl.
    exact Hs_ind.
    split.

    (* surjectivity *)
    intros s i Hi1 Hi2. unfold n_of, index_of in *.
    destruct (Hprop s) as [_ [_ [Hsurj _]]].
    assert (Hi2' : i < fst (proj1_sig (Hwit s)) + 1) by lia.
    destruct (Hsurj i Hi1 Hi2') as [t [Ht Hti]].
    exists t. split; [exact Ht |]. apply A_eq_sym in Ht.
    destruct (Hagree s t Ht t) as [_ Hval]. apply A_eq_sym. apply Ht.
    rewrite <- Hval. exact Hti.
    split.

    (* A iff *)
    intros s t. split.

    intro HAst.
    assert (Hst_class : s ≈A t) by (apply A_eq_step; exact HAst).
    destruct (Hprop s) as [_ [_ [_ HAiff]]].
    apply (HAiff s t (A_eq_refl s)) in HAst as [H1 H2].
    split; [exact Hst_class |].
    unfold index_of, n_of.
    destruct (Hagree s t Hst_class t) as [Hn Hval]. apply A_eq_sym. apply Hst_class.
    split; [exact H1 | rewrite <- Hval; exact H2].

    intros [Hclass [Hlt Heq]].
    unfold index_of, n_of in *.
    destruct (Hprop s) as [_ [_ [_ HAiff]]].
    apply (HAiff s t (A_eq_refl s)).
    destruct (Hagree s t Hclass t) as [Hn Hval]; [apply A_eq_sym; exact Hclass |].
    split; [exact Hlt | rewrite Hval; exact Heq].

    (* R shape *)
    intros s t u HR.
    destruct Hpers as [_ [_ Hshape]]. eauto.

  - intros [n_of [index_of [HAclass [HRclass [Hnconst [Hrange [Hinj [Hsurj [HA HR]]]]]]]]].
    split.

    + (* persistent *)
      repeat split.
      * (* unique A-successor *)
        intros x y y' Hxy Hxy'.
        apply HA in Hxy as [Hxy1 [Hxy2 Hxy3]].
        apply HA in Hxy' as [Hxy1' [Hxy2' Hxy3']].
        apply Hinj.
        -- (* y ≈A y' *)
           apply A_eq_trans with x.
           ++ apply A_eq_sym. apply A_eq_step. apply HA. auto.
           ++ apply A_eq_step. apply HA. auto.
        -- rewrite Hxy3, Hxy3'. reflexivity.
      * (* unique R-shape (functional's 2nd component) *)
        intros s t u u' Hu Hu'.
        rewrite <- (HR s t u Hu), (HR s t u' Hu'). reflexivity.
      * (* unique A-predecessor *)
        intros x x' y Hxy Hxy'.
        apply HA in Hxy as [Hxy1 [Hxy2 Hxy3]].
        apply HA in Hxy' as [Hxy1' [Hxy2' Hxy3']].
        apply Hinj.
        -- apply A_eq_trans with y.
           ++ apply A_eq_step. apply HA. auto.
           ++ apply A_eq_sym. apply A_eq_step. apply HA. auto.
        -- assert (Heq : index_of x = index_of x') by lia.
           exact Heq.
      * (* R shape *)
        intros x y z HRxyz. exact (HR x y z HRxyz).

    + split. split.

      (* ascending chain condition *)
      intro s.
      apply (wf_by_measure Sort (fun u v => u <A v) index_of).
      intros u v Huv.
      apply (A_lt_index_incr index_of n_of HA u v Huv).

      (* descending chain condition *)
      intro s.
      apply (wf_by_measure Sort (fun u v => v <A u) (fun s => n_of s - index_of s)).
      intros u v Huv.
      pose proof (A_lt_index_incr index_of n_of HA v u Huv) as Hidx.
      pose proof (A_lt_n_of_const n_of HAclass Hnconst v u Huv) as Hn.
      pose proof (Hrange u) as [_ Hu2].
      pose proof (Hrange v) as [_ Hv2].
      lia.

      (* separable *)
      intros s s' HR'.
      apply HRclass in HR' as Hclass.
      pose proof (HR s s' s' HR') as Ht.
      exact Hclass.
Qed.

Definition non_dependent_tiered (n : nat) : Prop :=
  exists index_of : Sort -> nat,
    (forall x, 0 < index_of x /\ index_of x < n + 1) /\
    (forall x y, index_of x = index_of y -> x = y) /\
    (forall i, 0 < i -> i < n + 1 -> exists x, index_of x = i) /\
    (forall x y, A x y <-> index_of x < n /\ index_of y = S (index_of x)) /\
    (forall x y z, R x y z -> y = z /\ index_of y <= index_of x).

Definition disjoint_union_of_non_dependent_tiered : Prop :=
  exists (n_of : Sort -> nat) (index_of : Sort -> nat),
    (forall s t, A s t -> s ≈A t) /\
    (forall s t u, R s t u -> s ≈A t) /\
    (forall s t, s ≈A t -> n_of s = n_of t) /\
    (forall s, 0 < index_of s /\ index_of s < n_of s + 1) /\
    (forall s t, s ≈A t -> index_of s = index_of t -> s = t) /\
    (forall s i, 0 < i -> i <= n_of s -> exists t, t ≈A s /\ index_of t = i) /\
    (forall s t, A s t <-> (s ≈A t /\ index_of s < n_of s /\ index_of t = S (index_of s))) /\
    (forall s t u, R s t u -> t = u /\ index_of t <= index_of s).

(* Corollary 1 *)
Axiom bounded_non_dependent_iff_disjoint_union_of_non_dependent_tiered :
  bounded_non_dependent <-> disjoint_union_of_non_dependent_tiered.

(* Proposition 2 *)
Axiom weak_implies_strong_normalization_lift :
  (forall n, non_dependent_tiered n \/ tiered n ->
    (forall M, weakly_normalizing M -> strongly_normalizing M)) ->
  (persistent /\ bounded /\ separable ->
    (forall M, weakly_normalizing M -> strongly_normalizing M)).

Open Scope Z_scope.

Definition Zpos_tiered : Prop :=
  exists index_of : Sort -> Z,
    (forall x, 0 < index_of x) /\
    (forall x y, index_of x = index_of y -> x = y) /\
    (forall i : Z, 0 < i -> exists x, index_of x = i) /\
    (forall x y, A x y <-> index_of y = index_of x + 1) /\
    (forall x y z, R x y z -> y = z).

Definition Zneg_tiered : Prop :=
  exists index_of : Sort -> Z,
    (forall x, index_of x < 0) /\
    (forall x y, index_of x = index_of y -> x = y) /\
    (forall i : Z, i < 0 -> exists x, index_of x = i) /\
    (forall x y, A x y <-> index_of x <= -2 /\ index_of y = index_of x + 1) /\
    (forall x y z, R x y z -> y = z).

Definition Z_tiered : Prop :=
  exists index_of : Sort -> Z,
    (forall x y, index_of x = index_of y -> x = y) /\
    (forall i : Z, exists x, index_of x = i) /\
    (forall x y, A x y <-> index_of y = index_of x + 1) /\
    (forall x y z, R x y z -> y = z).

Close Scope Z_scope.

Axiom finite_or_Zneg_tiered_atomic_gen_non_dependent :
  forall n, tiered n \/ Zneg_tiered ->
    atomic /\ generalized_non_dependent.

Axiom weak_implies_strong_normalization_n_tiered_lift :
  (forall n, non_dependent_tiered n ->
    (forall M, weakly_normalizing M -> strongly_normalizing M)) ->
  (generalized_non_dependent ->
    (forall M, weakly_normalizing M -> strongly_normalizing M)).

Definition cyclic_tiered (n : nat) : Prop :=
  exists index_of : Sort -> nat,
    (forall x, 0 < index_of x /\ index_of x < n + 1) /\
    (forall x y, index_of x = index_of y -> x = y) /\
    (forall i, 0 < i -> i < n + 1 -> exists x, index_of x = i) /\
    (forall x y, A x y <->
       (index_of x < n /\ index_of y = S (index_of x)) \/
       (index_of x = n /\ index_of y = 1)) /\
    (forall x y z, R x y z -> y = z).

(* Proposition 4 *)
Axiom weak_implies_strong_normalization_persistent_separable_lift :
  (forall n, (tiered n \/ cyclic_tiered n) ->
    (forall M, weakly_normalizing M -> strongly_normalizing M)) ->
  (persistent /\ separable ->
    (forall M, weakly_normalizing M -> strongly_normalizing M)).



End PTS.