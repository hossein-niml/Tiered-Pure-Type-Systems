From Stdlib Require Import List.
From Stdlib Require Import Classical.
From Stdlib Require Import Logic.IndefiniteDescription.
Import ListNotations.
From Stdlib.Program Require Import Program Wf.
From Stdlib Require Import Lia.
Require Import Stdlib.Arith.Arith.
Require Import Thesis.TPTSSignature.
Require Import Thesis.PTS.

Module TPTS (Sig : TPTS_SIGNATURE).
Import Sig.
Module Base := PTS Sig.
Import Base.

Fixpoint deg (t : term) : nat :=
  match t with
  | t_sort s    => index_of s + 1
  | t_var x     => index_of (var_sort x) - 1
  | t_pi _ _ B  => deg B
  | t_lam _ _ M => deg M
  | t_app M _   => deg M
  end.

Definition T_eq (j : nat) (M : term) : Prop := deg M = j.
Definition T_geq (j : nat) (M : term) : Prop := j <= deg M.

Notation "'T_[' j ]" := (T_eq j) (at level 0).
Notation "'T_≥[' j ]" := (T_geq j) (at level 0).

Definition derivable (M : term) : Prop := exists Γ N, Γ ⊢ M ∈ N.

Lemma deg_typing_succ : forall Γ M N, Γ ⊢ M ∈ N -> deg N = deg M + 1.
Proof.
  intros Γ M N Htyp. induction Htyp; simpl in *.

  - apply A_spec in H as [H1 H2]. lia.

  - pose proof (index_range (var_sort x)) as [H1 H2]. lia.

  - exact IHHtyp1.

  - assert (Hshape : s = s') by (apply (R_shape (var_sort x) s s'); exact H).
    subst s'. exact IHHtyp2.

  - exact IHHtyp1.

  - (* typing_app *)
    admit.

  - (* typing_conv : M unchanged, type changes A -> B via =b *)
    admit.
Admitted.

Lemma deg_le_top : forall M, deg M <= n + 1.
Proof.
  induction M; simpl; auto.
  - pose proof (index_range s) as [_ H]. lia.
  - pose proof (index_range (var_sort v)) as [_ H]. lia.
Qed.

Lemma deg_top : forall M, (derivable M) ->
  (deg M = n + 1 <-> exists s, M = t_sort s /\ index_of s = n).
Proof.
  intros M [Γ [N Htyp]]. split.

  - intros Hdeg. induction Htyp.
    + exists s. split; [reflexivity |]. simpl in Hdeg. lia.
    + simpl in Hdeg. pose proof (index_range (var_sort x)) as [H1 H2]. lia.
    + apply IHHtyp1. exact Hdeg.
    + exfalso. simpl in Hdeg.
      assert (Hsucc : deg (t_sort s) = deg B + 1) by (apply deg_typing_succ with (Γ ++ [(x, A0)]); exact Htyp2).
      simpl in Hsucc. pose proof (index_range s) as [_ Hs2]. lia.
    + exfalso. simpl in Hdeg.
      assert (Hsucc1 : deg (t_sort s') = deg (t_pi x A0 B) + 1) by (apply deg_typing_succ with (Γ); exact Htyp2).
      assert (Hsucc2 : deg (B) = deg (M) + 1) by (apply deg_typing_succ with (Γ ++ [(x, A0)]); exact Htyp1).
      simpl in *. pose proof (index_range s') as [_ Hs2]. lia.
    + exfalso. simpl in Hdeg.
      assert (Hsucc : deg (t_pi x A0 B) = deg M + 1) by (apply deg_typing_succ with Γ; exact Htyp1).
      simpl in Hsucc. pose proof (deg_le_top B) as HB. lia.
    + apply IHHtyp1. exact Hdeg.
  
  - intros [s [Heq Hidx]]. subst M. simpl. lia.
Qed.

Lemma deg_top_type : forall M, (derivable M) ->
  deg M = n <-> exists Γ s, (Γ ⊢ M ∈ t_sort s /\ index_of s = n).
Proof.
  intros M [Γ [N Htyp]]. split.

  - intros Hdeg. induction Htyp.

    + exists [], s'. split.
      * apply typing_axiom. exact H.
      * pose proof (A_spec s s') as [HA _]. apply HA in H as [_ H]. simpl in *. lia.

    + pose proof ((deg_typing_succ Γ A0 (t_sort (var_sort x))) Htyp).
      simpl in *. assert (HA0 : index_of (var_sort x) = deg A0) by lia.
      pose proof (index_range (var_sort x)). lia.

    + apply IHHtyp1. apply Hdeg.

    + pose proof ((deg_typing_succ (Γ ++ [(x, A0)]) B (t_sort s)) Htyp2).
      simpl in *. assert (Hs : index_of s = n) by lia.
      apply IHHtyp2 in Hdeg. pose proof (R_shape (var_sort x) s s' H) as Heq.
      subst. exists Γ, s'. split; auto. apply typing_pi with s'; auto.

    + pose proof ((deg_typing_succ (Γ ++ [(x, A0)]) M B) Htyp1).
      pose proof ((deg_typing_succ Γ (t_pi x A0 B) (t_sort s')) Htyp2).
      simpl in *. assert (Hs : index_of s' = n + 1) by lia.
      pose proof (index_range (s')). lia.

    + simpl in Hdeg.
      pose proof (deg_typing_succ Γ M (t_pi x A0 B) Htyp1) as Hsucc1.
      simpl in Hsucc1.
      assert (HdegB : deg B = n + 1) by lia.
      assert (Hderiv_pi : exists s', Γ ⊢ t_pi x A0 B ∈ t_sort s').
      { destruct (type_correctness Γ M (t_pi x A0 B) Htyp1) as [[s Hcontra] | [s' Hs']].
        - discriminate Hcontra.
        - exists s'. exact Hs'. }
      destruct Hderiv_pi as [s' Hs'].
      pose proof (generation_pi Γ x A0 B (t_sort s') Hs')
        as [sB [sB' [HA0typ [HBtyp [HR Heqs]]]]].
      assert (Hderiv_B : derivable B) by (exists (Γ ++ [(x, A0)]), (t_sort sB); exact HBtyp).
      apply (proj1 (deg_top B Hderiv_B)) in HdegB as [s0 [HBeq Hidx0]].
      subst B.
      pose proof (deg_typing_succ (Γ ++ [(x, A0)]) (t_sort s0) (t_sort sB) HBtyp) as Hsucc2.
      simpl in Hsucc2.
      rewrite Hidx0 in Hsucc2.
      pose proof (index_range sB) as [_ HsBrange].
      lia.

    + apply IHHtyp1. exact Hdeg.

  - intros [Γ' [s [H1 H2]]].
    pose proof (deg_typing_succ Γ' M (t_sort s) H1). simpl in H. lia.
Qed.

Lemma deg_typing : forall M, derivable M -> forall i, (i > 0) -> (i < n) ->
  (deg M = i <-> (exists Γ N s, (Γ ⊢ M ∈ N) /\ (Γ ⊢ N ∈ t_sort s) /\ (index_of s = i + 1))).
Proof.
  intros M [Γ [T Htyp]] i Hi1 Hi2. split.

  - intros Hdeg. pose proof (deg_typing_succ Γ M T Htyp).
    pose proof (type_correctness Γ M T Htyp) as Hcor. destruct Hcor as [[s Hs] | [s Hs]].
    + subst T. simpl in *. pose proof (index_range s). assert (G : index_of s = i) by lia.
      assert (Hi : 0 < i + 1 < n + 1) by lia.
      pose proof (index_surj (i + 1) Hi) as Hs'. destruct Hs' as [s' Hs'].
      assert (Hss' : A s s') by (apply A_spec; lia).
      exists Γ, (t_sort s), s'. repeat split; auto. apply start_axiom; auto.
      exists M, (t_sort s); auto.
    + pose proof (deg_typing_succ Γ T (t_sort s) Hs). simpl in *.
      exists Γ, T, s. repeat split; auto; lia.

  - intros [Γ' [N [s [H1 [H2 H3]]]]].
    pose proof (deg_typing_succ Γ' M N H1) as Hdeg1.
    pose proof (deg_typing_succ Γ' N (t_sort s) H2) as Hdeg2.
    simpl in *. lia.
Qed.

Lemma deg_rename : forall M x y, var_sort x = var_sort y -> deg (rename x y M) = deg M.
Proof.
  intros M x y Hs. induction M; auto.
  - simpl. destruct (eq_var_dec v x); auto. subst. simpl. rewrite Hs; auto.
  - simpl. destruct (eq_var_dec v x); auto.
  - simpl. destruct (eq_var_dec v x); auto.
Qed.

Lemma deg_subst : forall M N x j, 
  (index_of (var_sort x) = j) ->
  (deg N = j - 1) ->
  (deg(M⁅x ≔ N⁆) = deg M).
Proof.
  intros M N x j Hx Hdeg. induction M.
  - rewrite subst_sort; auto.
  - rewrite subst_var. destruct (eq_var_dec v x); auto. subst; auto.
  - rewrite subst_app; auto.
  - rewrite subst_lam. simpl. 
    remember (fresh (var_sort v) (fv N ++ fv M2)) as z.
    remember (rename v z M2) as M2r.
    assert (Hs : var_sort v = var_sort z). rewrite Heqz; auto.
    pose proof (deg_rename M2 v z Hs).
    rewrite <- HeqM2r in *. admit.
  - rewrite subst_pi. simpl.
    remember (fresh (var_sort v) (fv N ++ fv M2)) as z.
    remember (rename v z M2) as M2r.
    assert (Hs : var_sort v = var_sort z). rewrite Heqz; auto.
    pose proof (deg_rename M2 v z Hs).
    rewrite <- HeqM2r in *. admit.
Admitted.

Lemma deg_beta : forall M N, (M ->>b N) -> (deg M = deg N).
Proof.
  intros M B Hbeta. induction Hbeta; auto.
  - induction H; auto. simpl. symmetry. 
    apply deg_subst with (index_of (var_sort x)); auto.
    admit.
  - rewrite IHHbeta1. rewrite <- IHHbeta2. reflexivity.
Admitted.

Definition full_with (i j : nat) : Prop :=
  forall l k : Sort,
  index_of l <= i ->
  index_of l <= index_of k ->
  index_of k <= j ->
  R l k k.

Definition full : Prop :=
  forall s1 s2 s3, R s1 s2 s3 -> full_with (index_of s2) (index_of s1).

(* For the remainder of this section, fix a full n-tiered pure type system λS. *)
Axiom is_full : full.

Definition R_star (s s' s'' : Sort) : Prop :=
  R s s' s'' /\ index_of s' <= index_of s.

Reserved Notation "Γ ⊢* M ∈ A" (at level 70, no associativity).

Inductive typing_star : context -> term -> term -> Prop :=
  | typing_star_axiom : forall s s',
      A s s' ->
      [] ⊢* t_sort s ∈ t_sort s'

  | typing_star_var : forall Γ x A,
      is_fresh x Γ ->
      Γ ⊢* A ∈ t_sort (var_sort x) ->
      Γ ++ [(x, A)] ⊢* t_var x ∈ A

  | typing_star_weak : forall Γ x B M A,
      is_fresh x Γ ->
      Γ ⊢* M ∈ A ->
      Γ ⊢* B ∈ t_sort (var_sort x) ->
      Γ ++ [(x, B)] ⊢* M ∈ A

  | typing_star_pi : forall Γ x A B s s',
      Γ ⊢* A ∈ t_sort (var_sort x) ->
      Γ ++ [(x, A)] ⊢* B ∈ t_sort s ->
      R_star (var_sort x) s s' ->
      Γ ⊢* (t_pi x A B) ∈ (t_sort s')

  | typing_star_lam : forall Γ x A M B s',
      Γ ++ [(x, A)] ⊢* M ∈ B ->
      Γ ⊢* (t_pi x A B) ∈ (t_sort s') ->
      Γ ⊢* (t_lam x A M) ∈ (t_pi x A B)

  | typing_star_app : forall Γ M N A B x,
      Γ ⊢* M ∈ t_pi x A B ->
      Γ ⊢* N ∈ A ->
      Γ ⊢* t_app M N ∈ (B⁅x ≔ N⁆)

  | typing_star_conv : forall Γ M A B s,
      Γ ⊢* M ∈ A ->
      A =b B ->
      Γ ⊢* B ∈ t_sort s ->
      Γ ⊢* M ∈ B

where "Γ ⊢* M ∈ A" := (typing_star Γ M A).

Definition legal_star (Γ : context) : Prop :=
  exists M N, Γ ⊢* M ∈ N.

Definition derivable_star (M : term) : Prop :=
  exists Γ N, Γ ⊢* M ∈ N.

Definition partial_sort_of (i : nat) (Hi : 0 < i < n + 1) : Sort :=
  proj1_sig (
    constructive_indefinite_description
      (fun s => index_of s = i)
      (index_surj i Hi)
  ).

Lemma one_in_range : 0 < 1 /\ 1 < n + 1.
Proof. pose proof n_range. lia. Qed.

Definition sort_of (i : nat) : Sort :=
  match (lt_dec 0 i, lt_dec i (n+1)) with
  | (left H1, left H2) => partial_sort_of i (conj H1 H2)
  | _ => partial_sort_of 1 one_in_range
  end.

(* Type-Level Translation *)
Parameter zero_var : var.

Fixpoint rho (i : nat) (M : term) : term :=
  match M with
  | t_sort s =>
      match i with
      | 0 => t_var zero_var
      | _ => t_sort (sort_of i)
      end
  | t_var x =>
      t_var (mkvar (sort_of (i + 2)) (var_idx x))
  | t_pi x A B =>
      (fix pi_tel (k : nat) : term :=
         match k with
         | 0    => t_pi x (rho i A) (rho i B)
         | S k' => t_pi x (rho (i + S k') A) (pi_tel k')
         end) (deg A - 1 - i)
  | t_lam x A M' =>
      (fix lam_tel (k : nat) : term :=
         match k with
         | 0    => t_lam x (rho (i + 1) A) (rho i M')
         | S k' => t_lam x (rho (i + 1 + S k') A) (lam_tel k')
         end) (deg A - 1 - (i + 1))
  | t_app M' N =>
      (fix app_tel (k : nat) : term :=
         match k with
         | 0    => t_app (rho i M') (rho i N)
         | S k' => t_app (app_tel k') (rho (i + S k') N)
         end) (deg N - 1 - i)
  end.

Fixpoint rho_ctx_tel (x : var) (T : term) (k : nat) : context :=
  let j := index_of (var_sort x) in
  match k with
  | 0    => [(x, rho (j - 1) T)]
  | S k' => (rho_ctx_tel x T k') ++ [(mkvar (sort_of (j - k)) (var_idx x), rho (j - k - 1) T)]
  end.

Fixpoint rho_ctx (i : nat) (Γ : context) : context :=
  match Γ with
  | [] => [(zero_var, t_sort (sort_of 1))]
  | (x, T) :: Γ' => (rho_ctx_tel x T (index_of (var_sort x) - i - 1)) ++ rho_ctx i Γ'
  end.

Axiom subcontext_append : 
  forall Γ1 Δ1 Γ2 Δ2,
  (Γ1 ⊆ Δ1) -> (Γ2 ⊆ Δ2) -> ((Γ1 ++ Γ2) ⊆ (Δ1 ++ Δ2)).

Axiom rho_ctx_tel_sub : 
  forall x T p q, p < q -> 
  rho_ctx_tel x T p ⊆ rho_ctx_tel x T q.

Lemma rho_ctx_sub : forall i j Γ, i < j -> rho_ctx j Γ ⊆ rho_ctx i Γ.
Proof.
  intros. induction Γ; auto.
  - simpl. unfold subcontext. auto.
  - destruct a as [y G]. simpl. apply subcontext_append; auto. 
    apply rho_ctx_tel_sub. assert (j + 1 > i + 1) by lia. admit.
Admitted.


End TPTS.