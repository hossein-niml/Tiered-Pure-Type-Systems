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

Axiom zero_var_distinct : 
  forall x : var, x <> zero_var.

Lemma zero_var_distinct' : 
  forall (x : var) (Hx : zero_var = x), False.
Proof.
  intros x Hx. apply zero_var_distinct with x; auto.
Qed.

Fixpoint rho_pi_tel (r : nat -> term -> term) (x : var) (A B : term) (i k : nat) : term :=
  match k with
  | 0    => t_pi x (r i A) (r i B)
  | S k' => t_pi x (r (i + S k') A) (rho_pi_tel r x A B i k')
  end.

Fixpoint rho_lam_tel (r : nat -> term -> term) (x : var) (A M' : term) (i k : nat) : term :=
  match k with
  | 0    => t_lam x (r (i + 1) A) (r i M')
  | S k' => t_lam x (r (i + 1 + S k') A) (rho_lam_tel r x A M' i k')
  end.

Fixpoint rho_app_tel (r : nat -> term -> term) (M' N : term) (i k : nat) : term :=
  match k with
  | 0    => t_app (r i M') (r i N)
  | S k' => t_app (rho_app_tel r M' N i k') (r (i + S k') N)
  end.

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
      match le_lt_dec (i + 1) (deg A) with
      | left _  => rho_pi_tel rho x A B i (deg A - 1 - i)
      | right _ => rho i B
      end
  | t_lam x A M' =>
      match le_lt_dec (i + 2) (deg A) with
      | left _  => rho_lam_tel rho x A M' i (deg A - 1 - (i + 1))
      | right _ => rho i M'
      end
  | t_app M' N =>
      match le_lt_dec (i + 1) (deg N) with
      | left _  => rho_app_tel rho M' N i (deg N - 1 - i)
      | right _ => rho i M'
      end
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

Lemma subcontext_append : 
  forall Γ1 Δ1 Γ2 Δ2,
  (Γ1 ⊆ Δ1) -> (Γ2 ⊆ Δ2) -> ((Γ1 ++ Γ2) ⊆ (Δ1 ++ Δ2)).
Proof.
  intros Γ1 Δ1 Γ2 Δ2 H1 H2 x T Hin. 
  apply in_app_or in Hin. destruct Hin; apply in_or_app.
  - left; auto.
  - right; auto.
Qed.

Axiom rho_ctx_tel_sub : 
  forall x T p q, 
  p < q -> rho_ctx_tel x T p ⊆ rho_ctx_tel x T q.

Definition ctx_above (b : nat) (Γ : context) : Prop :=
  forall x T, In (x, T) Γ -> b < index_of (var_sort x).

Lemma rho_ctx_sub : forall Γ i j,
  i < j -> ctx_above j Γ -> rho_ctx j Γ ⊆ rho_ctx i Γ.
Proof.
  induction Γ as [| [y T] Γ' IH]; intros i j Hij Habove.
  - simpl. unfold subcontext. auto.
  - simpl. apply subcontext_append.
    + apply rho_ctx_tel_sub.
      assert (Hy : j < index_of (var_sort y)).
      { apply Habove with T. left. reflexivity. }
      lia.
    + apply IH; auto. intros x' T' Hin. apply Habove with T'. right. exact Hin.
Qed.

Fixpoint rho_subst_tel (M N : term) (varidx i k : nat) : term :=
  match k with
  | O => M ⁅ mkvar (sort_of (i + 2)) (varidx) ≔ rho i N ⁆
  | S k' => rho_subst_tel (M ⁅ mkvar (sort_of (k + i + 2)) (varidx) ≔ rho (k + i) N ⁆) N varidx i k'
  end.

Definition rho_subst (M N : term) (x : var) (i : nat) : term :=
  let j := index_of (var_sort x) in
  match lt_dec j (i + 2) with
  | left _  => rho i M
  | right _ => rho_subst_tel (rho i M) (N) (var_idx x) (i) (j - i - 2)
  end.

Lemma sort_of_correct : forall i, 0 < i -> i < n + 1 -> index_of (sort_of i) = i.
Proof.
  intros i H1 H2. unfold sort_of.
  destruct (lt_dec 0 i) as [Hd1|Hd1]; [| lia].
  destruct (lt_dec i (n+1)) as [Hd2|Hd2]; [| lia].
  unfold partial_sort_of.
  destruct (constructive_indefinite_description (fun s => index_of s = i)
              (index_surj i (conj Hd1 Hd2))) as [s Hs].
  exact Hs.
Qed.

Lemma sort_of_inj : forall p q,
  0 < p -> p < n + 1 -> 0 < q -> q < n + 1 ->
  sort_of p = sort_of q -> p = q.
Proof.
  intros p q Hp1 Hp2 Hq1 Hq2 Heq.
  assert (Hp : index_of (sort_of p) = p) by (apply sort_of_correct; lia).
  assert (Hq : index_of (sort_of q) = q) by (apply sort_of_correct; lia).
  rewrite Heq in Hp. rewrite Hp in Hq. exact Hq.
Qed.

Axiom var_idx_neq_of_var_neq : forall x y : var, y <> x -> var_idx y <> var_idx x.

Lemma rename_id : forall v t, rename v v t = t.
Proof.
  intros v t. induction t.
  - reflexivity.
  - simpl. destruct (eq_var_dec v0 v) as [Heq | Hneq].
    + subst v0. reflexivity.
    + reflexivity.
  - simpl. rewrite IHt1, IHt2. reflexivity.
  - simpl. destruct (eq_var_dec v0 v) as [Heq | Hneq].
    + subst v0. rewrite IHt1. reflexivity.
    + rewrite IHt1, IHt2. reflexivity.
  - simpl. destruct (eq_var_dec v0 v) as [Heq | Hneq].
    + subst v0. rewrite IHt1. reflexivity.
    + rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma subst_pi_no_capture : forall y A B x N,
  var_idx y <> var_idx x ->
  ~ In y (fv N) ->
  ~ In y (fv B) ->
  (t_pi y A B) ⁅x ≔ N⁆ = t_pi y (A⁅x ≔ N⁆) (B⁅x ≔ N⁆).
Proof.
  intros y A B x N Hyx HyN HyB.
  rewrite subst_pi.
  simpl.
  destruct (in_dec eq_var_dec y (fv N ++ fv B)) as [Hin | Hnotin].
  - exfalso. apply in_app_or in Hin. destruct Hin as [Hin | Hin]; auto.
  - rewrite rename_id. reflexivity.
Qed.

Lemma rho_commutes_substitution : 
  forall i, 0 <= i <= n ->
  forall x, 1 <= index_of (var_sort x) <= n ->
  forall M, deg M >= i + 1 ->
  forall N, deg N = index_of (var_sort x) - 1 ->
  rho i (M ⁅ x ≔ N ⁆) = rho_subst M N x i.
Proof.
  intros i.
  induction i as [i IHouter] using
    (well_founded_induction (Wf_nat.well_founded_ltof nat (fun i => n - i))).
  intros Hi x Hx M.
  induction M as [s | y | P IHP Q IHQ | y A M' IHM' | y C IHC D IHD]; intros Hdeg N HdegN.

  - (* M = t_sort s *)
    rewrite subst_sort. unfold rho_subst. 
    destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [E | E]; auto.
    assert (Hconst : forall k M0,
                  k <= index_of (var_sort x) - i - 2 ->
                  (exists s0, M0 = t_sort s0) \/ (i = 0 /\ M0 = t_var zero_var /\
                    forall k', i+2 <= k' -> k' <= index_of (var_sort x) ->
                    {| var_sort := sort_of k'; var_idx := var_idx x |} <> zero_var) ->
                  rho_subst_tel M0 N (var_idx x) i k = M0).
        { induction k as [| k' IHk]; intros M0 Hkbound Hcase.
          - simpl. destruct Hcase as [[s0 Heq] | [Hi0 [Heq Hne]]]; subst M0.
            + rewrite subst_sort. reflexivity.
            + rewrite subst_var.
              destruct (eq_var_dec zero_var (mkvar (sort_of (i+2)) (var_idx x))) as [Heq2|Hne2]; auto.
              exfalso. 
              apply zero_var_distinct with ({| var_sort := sort_of (i + 2); var_idx := var_idx x |}).
              auto.
          - simpl. destruct Hcase as [[s0 Heq] | [Hi0 [Heq Hne]]]; subst M0.
            + rewrite subst_sort. apply IHk; [lia | left; exists s0; reflexivity].
            + rewrite subst_var.
              destruct (eq_var_dec zero_var (mkvar (sort_of (k'+i+2)) (var_idx x))) as [Heq2|Hne2].
              * exfalso. apply zero_var_distinct' with (Hx := Heq2).
              * destruct (eq_var_dec zero_var (mkvar (sort_of (S (k' + i + 2))) (var_idx x))) as [Heq3 | Hne3].
                -- exfalso. apply zero_var_distinct' with (Hx := Heq3).
                -- apply IHk; [lia | right; repeat split; [exact Hi0 | exact Hne]].
        }
    symmetry. apply Hconst; auto.
    destruct i as [| i'].
      + right. repeat split; auto. intros. apply zero_var_distinct.
      + left. exists (sort_of (S i')). reflexivity.

  - (* M = t_var y *)
    unfold rho_subst.
    destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [E | E].
    + simpl in Hdeg. assert (Hy : index_of (var_sort y) >= i + 2) by lia.
      rewrite subst_var. destruct (eq_var_dec y x); auto. exfalso. subst. lia.
    + rewrite subst_var. destruct (eq_var_dec y x).
      * subst y. remember (mkvar (sort_of (i+2)) (var_idx x)) as z.
        assert (Hz : rho i N = (t_var z) ⁅ z ≔ rho i N ⁆).
        rewrite subst_var. destruct (eq_var_dec z z). auto. destruct n0; auto.
        rewrite Hz. simpl. rewrite <- Heqz.
        assert (Hconst: forall k, k <= index_of (var_sort x) - i - 2 ->
          rho_subst_tel (t_var z) N (var_idx x) i k = (t_var z) ⁅ z ≔ rho i N ⁆).
        {induction k as [| k' IHk]; intros Hk.
          - simpl. rewrite <- Heqz. reflexivity.
          - simpl.
            assert (Hlevel_ne : mkvar (sort_of (S k' + i + 2)) (var_idx x) <> z).
            { rewrite Heqz. intro Hcontra.
              injection Hcontra as Hsort.
              assert (Heq2 : S k' + i + 2 = i + 2).
              { apply (sort_of_inj (S k' + i + 2) (i + 2)); [lia | lia | lia | lia | exact Hsort]. }
              lia. }
        rewrite subst_var.
        destruct (eq_var_dec z (mkvar (sort_of (S k' + i + 2)) (var_idx x))) as [Heq | Hne].
        + exfalso. apply Hlevel_ne. symmetry. exact Heq.
        + destruct (eq_var_dec z {| var_sort := sort_of (S (k' + i + 2)); var_idx := var_idx x |}). 
          * contradiction. 
          * apply IHk. lia.
        }
        symmetry. apply Hconst. lia.
      * assert (Hconst : forall y k, var_idx y <> var_idx x -> rho_subst_tel (t_var y) N (var_idx x) i k = t_var y).
        {
          intros y0 k Hyx. induction k as [| k' IHk]; simpl.
          - rewrite subst_var. destruct (eq_var_dec y0 (mkvar (sort_of (i+2)) (var_idx x))) as [Heq|Hne].
            + exfalso. apply Hyx. rewrite Heq. reflexivity.
            + reflexivity.
          - rewrite subst_var. destruct (eq_var_dec y0 (mkvar (sort_of (S k'+i+2)) (var_idx x))) as [Heq|Hne].
            + exfalso. apply Hyx. rewrite Heq. reflexivity.
            + destruct (eq_var_dec y0 {| var_sort := sort_of (S (k' + i + 2)); var_idx := var_idx x |}). 
              * contradiction. 
              * exact IHk.
        }
        symmetry. apply Hconst. simpl. apply var_idx_neq_of_var_neq. exact n0.

  - admit.
  
  - admit.

  - (* M = t_pi y C D *)
    simpl in Hdeg.
    unfold rho_subst.
    destruct (le_lt_dec (i + 1) (deg C)) as [HdegC | HdegC].

    + (* deg C >= i+1 *) admit.

    + (* deg C < i+1 *)
      rewrite subst_pi. 
      remember (fresh (var_sort y) (fv N ++ fv D)) as z.
      remember (if in_dec eq_var_dec y (fv N ++ fv D) then z else y) as y'.
      remember (rename y y' D) as D'.
      
      destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [Hj | Hj].

      ++ simpl. assert (Q : deg (C ⁅ x ≔ N ⁆) = deg C). apply deg_subst with (index_of (var_sort x)); auto.
      rewrite Q. destruct (le_lt_dec (i + 1) (deg C)).
        * lia.
        * assert (Q' : deg (D' ⁅ x ≔ N ⁆) = deg D'). apply deg_subst with (index_of (var_sort x)); auto.
          assert (W : deg D' = deg D). rewrite HeqD'. apply deg_rename. destruct (in_dec eq_var_dec y (fv N ++ fv D)).
            ** subst. reflexivity.
            ** subst. reflexivity.
            **
          
          +++ rewrite HeqD'. rewrite deg_rename with (M := D ⁅ x ≔ N ⁆).
Admitted.    


End TPTS.