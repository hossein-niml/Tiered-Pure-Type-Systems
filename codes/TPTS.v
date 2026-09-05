From Stdlib Require Import List.
From Stdlib Require Import Classical.
From Stdlib Require Import Logic.IndefiniteDescription.
From Stdlib.Program Require Import Program Wf.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import ZArith.
Import ListNotations.

Require Import Thesis.TPTSSignature.
Require Import Thesis.PTS.

Module TPTS (Sig : TPTS_SIGNATURE).

Import Sig.

Module Base := PTS Sig.
  
Import Base.

(* ================================================================= *)

Definition retag (x : var) (s : Sort) : var := x * (n + 2) + index_of s.

Lemma retag_inj : forall x1 s1 x2 s2,
  retag x1 s1 = retag x2 s2 -> x1 = x2 /\ s1 = s2.
Proof.
  intros x1 s1 x2 s2 H. unfold retag in H.
  pose proof (index_range s1) as [Hs1a Hs1b].
  pose proof (index_range s2) as [Hs2a Hs2b].
  assert (Hx : x1 = x2).
  { assert (E1 : (x1 * (n + 2) + index_of s1) / (n + 2) = x1).
    { rewrite Nat.div_add_l by lia. rewrite Nat.div_small by lia. lia. }
    assert (E2 : (x2 * (n + 2) + index_of s2) / (n + 2) = x2).
    { rewrite Nat.div_add_l by lia. rewrite Nat.div_small by lia. lia. }
    rewrite H in E1. rewrite E1 in E2. exact E2. }
  subst x1.
  assert (Hi : index_of s1 = index_of s2) by lia.
  split; [reflexivity | apply index_inj; exact Hi].
Qed.

Lemma retag_neq_of_atom_neq : forall x1 s1 x2 s2,
  x1 <> x2 -> retag x1 s1 <> retag x2 s2.
Proof. intros x1 s1 x2 s2 Hne Heq. apply retag_inj in Heq. tauto. Qed.

Lemma retag_neq_of_sort_neq : forall x s1 s2,
  s1 <> s2 -> retag x s1 <> retag x s2.
Proof. intros x s1 s2 Hne Heq. apply retag_inj in Heq. tauto. Qed.

Lemma retag_neq_mult : forall k x s, retag x s <> k * (n + 2).
Proof.
  intros k x s Heq. unfold retag in Heq.
  pose proof (index_range s) as [Hlo Hhi].
  assert (Hm : (x * (n + 2) + index_of s) mod (n + 2) = index_of s).
  { rewrite Nat.add_comm. rewrite Nat.Div0.mod_add by lia. apply Nat.mod_small; lia. }
  rewrite Heq in Hm.
  rewrite Nat.Div0.mod_mul in Hm by lia.
  lia.
Qed.

(* Degree *)

Fixpoint deg (t : term) : nat :=
  match t with
  | t_sort s     => index_of s + 1
  | t_bvar s _   => index_of s - 1
  | t_fvar s _   => index_of s - 1
  | t_app M _    => deg M
  | t_lam _ _ M  => deg M
  | t_pi  _ _ B  => deg B
  end.

Definition T_eq (j : nat) (M : term) : Prop := deg M = j.
Definition T_geq (j : nat) (M : term) : Prop := j <= deg M.

Notation "'T_[' j ]" := (T_eq j) (at level 0).
Notation "'T_≥[' j ]" := (T_geq j) (at level 0).

Definition derivable (M : term) : Prop := exists Γ N, Γ ⊢ M ∈ N.

Fixpoint closed_at (k : nat) (t : term) : Prop :=
  match t with
  | t_sort _    => True
  | t_bvar _ n  => n < k
  | t_fvar _ _  => True
  | t_app M _   => closed_at k M
  | t_lam _ _ M => closed_at (S k) M
  | t_pi  _ _ B => closed_at (S k) B
  end.

Lemma closed_at_open_rec_inv : forall t k u,
  closed_at k (open_rec k u t) ->
  (forall s m, u <> t_bvar s m) ->
  closed_at (S k) t.
Proof.
  induction t as [s0 | sn n | y | P IHP Q IHQ | s1 A IHA M IHM | s1 A IHA B IHB];
    intros k u Hc Hu; simpl in *; auto.
  - destruct (Nat.eqb n k) eqn:Heqb.
    + apply Nat.eqb_eq in Heqb. lia.
    + apply Nat.eqb_neq in Heqb.
      simpl in Hc. lia.
  - eapply IHP; eauto.
  - eapply IHM with (k := S k); eauto.
  - eapply IHB with (k := S k); eauto.
Qed.

Lemma lc_closed_at : forall t, lc t -> closed_at 0 t.
Proof.
  intros t Hlc.
  induction Hlc as [ s | x | M N HM IHM HN IHN
                    | s A B L HA IHA HB IHB
                    | s A M L HA IHA HM IHM ]; simpl; auto.
  - remember (fresh L) as x0 eqn:Hx0def.
    assert (Hx0L : ~ In x0 L) by (rewrite Hx0def; apply fresh_notin).
    specialize (IHB x0 Hx0L).
    unfold open_var in IHB.
    apply (closed_at_open_rec_inv B 0 (t_fvar s x0) IHB).
    intros sv m Hcontra. discriminate.
  - remember (fresh L) as x0 eqn:Hx0def.
    assert (Hx0L : ~ In x0 L) by (rewrite Hx0def; apply fresh_notin).
    specialize (IHM x0 Hx0L).
    unfold open_var in IHM.
    apply (closed_at_open_rec_inv M 0 (t_fvar s x0) IHM).
    intros sv m Hcontra. discriminate.
Qed.

Lemma deg_open_rec_gen : forall B k x s,
  bvar_tag_ok k s B ->
  deg B = deg (open_rec k (t_fvar s x) B).
Proof.
  induction B as [s0 | s_n n | y | P IHP Q IHQ | s1 A IHA M IHM | s1 A IHA B IHB];
    intros k x s Htag; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb n k) eqn:Heqb.
    + apply Nat.eqb_eq in Heqb. subst n.
      specialize (Htag eq_refl). subst s_n.
      reflexivity.
    + reflexivity.
  - reflexivity.
  - apply (IHP k x s Htag).
  - apply (IHM (S k) x s Htag).
  - apply (IHB (S k) x s Htag).
Qed.

Lemma deg_open : forall B x s,
  bvar_tag_ok 0 s B ->
  deg B = deg (open_var B s x).
Proof.
  intros B x s Htag.
  unfold open_var.
  apply deg_open_rec_gen. exact Htag.
Qed.

Lemma deg_open_rec_subst : forall B k u s,
  bvar_tag_ok k s B ->
  deg u = index_of s - 1 ->
  deg (open_rec k u B) = deg B.
Proof.
  induction B as [s0 | s_n n | y | P IHP Q IHQ | s1 A IHA M IHM | s1 A IHA B IHB];
    intros k u s Htag Hdegu; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb n k) eqn:Heqb.
    + apply Nat.eqb_eq in Heqb. subst n.
      specialize (Htag eq_refl). subst s_n.
      exact Hdegu.
    + reflexivity.
  - reflexivity.
  - apply (IHP k u s Htag Hdegu).
  - apply (IHM (S k) u s Htag Hdegu).
  - apply (IHB (S k) u s Htag Hdegu).
Qed.

Lemma deg_subst_open : forall B x s N,
  ~ In x (fv B) ->
  bvar_tag_ok 0 s B ->
  lc N ->
  deg N = index_of s - 1 ->
  deg ((open_var B s x) ⁅ x ≔ N ⁆) = deg (open_var B s x).
Proof.
  intros B x s N HxB Htag HlcN HdegN.
  rewrite (subst_open_var_eq B s x N HxB HlcN).
  pose proof (deg_open_rec_subst B 0 N s Htag HdegN) as Hgen.
  rewrite Hgen.
  unfold open_var.
  apply deg_open_rec_gen. exact Htag.
Qed.

Axiom deg_sort_typed : forall Γ A s,
  Γ ⊢ A ∈ t_sort s -> deg A = index_of s.

Axiom deg_conv_invariant : forall Γ M A B s,
  Γ ⊢ M ∈ A -> A =b B -> Γ ⊢ B ∈ t_sort s -> deg A = deg B.

Lemma typing_pi_subject_bvar_tag_ok : forall Γ M T,
  Γ ⊢ M ∈ T -> forall s A B, M = t_pi s A B -> bvar_tag_ok 0 s B.
Proof.
  intros Γ M T Htyp.
  induction Htyp as
    [ sa sb HA
    | Γ0 x0 A0 s0 Hfresh0 HA0 IHA0
    | Γ0 x0 B0 M0 A0 s0 Hfresh0 HM0 IHM0 HB0 IHB0
    | Γ0 A0 B0 s1 s2 s3 L HA IHA HTagB HB IHB HR
    | Γ0 A0 M0 B0 s1 s3 L HA IHA HTagM HM IHM HPi IHPi
    | Γ0 M0 N0 A0 B0 s1a HM IHM HN IHN
    | Γ0 M0 A0 B0 sd HM IHM Heq HB IHB ];
    intros s A B HeqM; try discriminate.
  - (* weak: subject unchanged *) apply (IHM0 s A B HeqM).
  - (* pi: this is the node that introduced it *)
    injection HeqM as Hs HA' HB'. subst. exact HTagB.
  - (* conv: subject unchanged *) apply (IHM s A B HeqM).
Qed.

Lemma deg_typing_succ : forall Γ M N, Γ ⊢ M ∈ N -> deg N = deg M + 1.
Proof.
  intros Γ M N Htyp.
  induction Htyp as
    [ sa sb HA
    | Γ0 x0 A0 s0 Hfresh0 HA0 IHA0
    | Γ0 x0 B0 M0 A0 s0 Hfresh0 HM0 IHM0 HB0 IHB0
    | Γ0 A0 B0 s1 s2 s3 L HA IHA HTagB HB IHB HR
    | Γ0 A0 M0 B0 s1 s3 L HA IHA HTagM HM IHM HPi IHPi
    | Γ0 M0 N0 A0 B0 s1a HM IHM HN IHN
    | Γ0 M0 A0 B0 sd HM IHM Heq HB IHB ];
    simpl in *.

  - (* axiom *)
    apply A_spec in HA as [Hlt Heq2]. lia.

  - (* var *)
    unfold deg in IHA0. simpl in IHA0.
    pose proof (index_range s0) as [Hr1 Hr2]. unfold deg. lia.

  - (* weak *)
    exact IHM0.

  - (* pi *)
    remember (fresh (L ++ fv B0)) as x0 eqn:Hx0def.
    assert (Hx0L : ~ In x0 L).
    { rewrite Hx0def. intro Hc. apply (fresh_notin (L ++ fv B0)).
      apply in_or_app. left. exact Hc. }
    specialize (IHB x0 Hx0L). unfold deg in IHB. simpl in IHB.
    rewrite (deg_open B0 x0 s1 HTagB).
    pose proof (R_shape s1 s2 s3 HR) as Hshape. subst s3. unfold deg.
    lia.

  - (* lam *)
    remember (fresh (L ++ fv M0 ++ fv B0)) as x0 eqn:Hx0def.
    assert (Hx0L : ~ In x0 L).
    { rewrite Hx0def. intro Hc. apply (fresh_notin (L ++ fv M0 ++ fv B0)).
      apply in_or_app. left. exact Hc. }
    assert (HtypM : Γ0 ++ [(x0, (s1, A0))] ⊢ open_var M0 s1 x0 ∈ open_var B0 s1 x0)
      by (apply HM; auto).
    specialize (IHM x0 Hx0L). unfold deg in IHM. simpl in IHM.
    rewrite (deg_open M0 x0 s1 HTagM).
    assert (HTagB0 : bvar_tag_ok 0 s1 B0)
      by (apply (typing_pi_subject_bvar_tag_ok Γ0 (t_pi s1 A0 B0) (t_sort s3) HPi
                   s1 A0 B0 eq_refl)).
    rewrite (deg_open B0 x0 s1 HTagB0). unfold deg.
    lia.

  - (* app *)
    pose proof (type_correctness Γ0 M0 (t_pi s1a A0 B0) HM) as Hcor.
    destruct Hcor as [[s Hs] | [s Hs]].
    + discriminate Hs.
    + destruct (generation_pi Γ0 s1a A0 B0 (t_sort s) Hs)
        as [s2 [s3 [L [HB1 [HTag1 [HB2 [HB3 HB4]]]]]]].
      assert (Hdeg_A0 : deg A0 = index_of s1a) by (apply (deg_sort_typed Γ0 A0 s1a HB1)).
      assert (Hdeg_N0 : deg N0 = index_of s1a - 1) by (unfold deg in *; lia).
      pose proof (typing_lc Γ0 N0 A0 HN) as [HlcN0 _].
      remember (fresh (fv B0)) as x0 eqn:Hx0def.
      assert (Hx0B : ~ In x0 (fv B0)).
      { rewrite Hx0def. apply fresh_notin. }
      assert (Heqterm : B0 ^^ N0 = (open_var B0 s1a x0) ⁅ x0 ≔ N0 ⁆)
        by (apply subst_intro; [exact Hx0B | exact HlcN0]).
      assert (Hdegsub : deg ((open_var B0 s1a x0) ⁅ x0 ≔ N0 ⁆) = deg (open_var B0 s1a x0))
        by (apply deg_subst_open; [exact Hx0B | exact HTag1 | exact HlcN0 | exact Hdeg_N0]).
      assert (Hdegopen : deg B0 = deg (open_var B0 s1a x0))
        by (apply deg_open; exact HTag1).
      unfold deg. rewrite Heqterm.
      unfold deg in Hdegsub, Hdegopen.
      rewrite Hdegsub. rewrite <- Hdegopen.
      exact IHM.

  - (* conv *)
    pose proof (deg_conv_invariant Γ0 M0 A0 B0 sd HM Heq HB) as Hcv.
    unfold deg in *. lia.
Qed.

Lemma deg_le_top : forall t, deg t <= n + 1.
Proof.
  induction t as [s | s_n0 n0 | sv v | P IHP Q IHQ | s A IHA M IHM | s A IHA B IHB];
    simpl; auto.
  - pose proof (index_range s) as [_ H]. lia.
  - pose proof (index_range s_n0) as [_ H]. lia.
  - pose proof (index_range sv) as [_ H]. lia.
Qed.

Lemma deg_top : forall M, (derivable M) ->
  (deg M = n + 1 <-> exists s, M = t_sort s /\ index_of s = n).
Proof.
  intros M [Γ [N Htyp]]. split.

  - intros Hdeg. induction Htyp as
      [ sa sb HA
      | Γ0 x0 A0 s0 Hfresh0 HA0 IHA0
      | Γ0 x0 B0 M0 A0 s0 Hfresh0 HM0 IHM0 HB0 IHB0
      | Γ0 A0 B0 s1 s2 s3 L HA IHA HTagB HB IHB HR
      | Γ0 A0 M0 B0 s1 s3 L HA IHA HTagM HM IHM HPi IHPi
      | Γ0 M0 N0 A0 B0 s1a HM IHM HN IHN
      | Γ0 M0 A0 B0 sd HM IHM Heq HB IHB ].
    + exists sa. split; [reflexivity |]. unfold deg in Hdeg. simpl in Hdeg. lia.
    + unfold deg in Hdeg. simpl in Hdeg.
      pose proof (index_range s0) as [H1 H2]. lia.
    + apply IHM0. exact Hdeg.
    + exfalso. unfold deg in Hdeg. simpl in Hdeg.
      assert (Hsucc : deg (t_sort s3) = deg (t_pi s1 A0 B0) + 1)
        by (apply deg_typing_succ with Γ0;
            apply (typing_pi Γ0 A0 B0 s1 s2 s3 L HA HTagB HB HR)).
      unfold deg in Hsucc. simpl in Hsucc.
      pose proof (index_range s3) as [_ Hs2]. lia.
    + exfalso. unfold deg in Hdeg. simpl in Hdeg.
      assert (Hsucc1 : deg (t_pi s1 A0 B0) = deg (t_lam s1 A0 M0) + 1)
        by (apply deg_typing_succ with Γ0;
            apply (typing_lam Γ0 A0 M0 B0 s1 s3 L HA HTagM HM HPi)).
      unfold deg in Hsucc1. simpl in Hsucc1.
      pose proof (deg_le_top B0) as HB'. unfold deg in *. lia.
    + exfalso. unfold deg in Hdeg. simpl in Hdeg.
      assert (Hsucc : deg (t_pi s1a A0 B0) = deg M0 + 1)
        by (apply deg_typing_succ with Γ0; exact HM).
      unfold deg in Hsucc. simpl in Hsucc.
      pose proof (deg_le_top B0) as HB'. unfold deg in *. lia.
    + apply IHM. exact Hdeg.

  - intros [s [Heq Hidx]]. subst M. unfold deg. simpl. lia.
Qed.

Lemma deg_top_type : forall M, (derivable M) ->
  deg M = n <-> exists Γ s, (Γ ⊢ M ∈ t_sort s /\ index_of s = n).
Proof.
  intros M [Γ [N Htyp]]. split.

  - intros Hdeg. induction Htyp as
      [ sa sb HA
      | Γ0 x0 A0 s0 Hfresh0 HA0 IHA0
      | Γ0 x0 B0 M0 A0 s0 Hfresh0 HM0 IHM0 HB0 IHB0
      | Γ0 A0 B0 s1 s2 s3 L HA IHA HTagB HB IHB HR
      | Γ0 A0 M0 B0 s1 s3 L HA IHA HTagM HM IHM HPi IHPi
      | Γ0 M0 N0 A0 B0 s1a HM IHM HN IHN
      | Γ0 M0 A0 B0 sd HM IHM Heq HB IHB ].

    + exists [], sb. split.
      * apply typing_axiom. exact HA.
      * pose proof (A_spec sa sb) as [HAiff _]. apply HAiff in HA as [_ HAeq].
        unfold deg in Hdeg. simpl in Hdeg. lia.

    + pose proof (deg_typing_succ Γ0 A0 (t_sort s0) HA0) as Hs.
      unfold deg in *. simpl in *.
      pose proof (index_range s0). lia.

    + apply IHM0. apply Hdeg.

    + exists Γ0, s3. split.
      * apply (typing_pi Γ0 A0 B0 s1 s2 s3 L HA HTagB HB HR).
      * pose proof (deg_typing_succ Γ0 (t_pi s1 A0 B0) (t_sort s3)
                      (typing_pi Γ0 A0 B0 s1 s2 s3 L HA HTagB HB HR)) as Hsucc.
        unfold deg in Hsucc, Hdeg. simpl in Hsucc, Hdeg. lia.

    + exfalso.
      assert (Hsucc1 : deg (t_pi s1 A0 B0) = deg (t_lam s1 A0 M0) + 1)
        by (apply deg_typing_succ with Γ0;
            apply (typing_lam Γ0 A0 M0 B0 s1 s3 L HA HTagM HM HPi)).
      unfold deg in Hsucc1, Hdeg. simpl in Hsucc1, Hdeg.
      assert (Htop : deg (t_pi s1 A0 B0) = n + 1) by (unfold deg; simpl; lia).
      assert (Hderiv : derivable (t_pi s1 A0 B0)).
      { unfold derivable. exists Γ0. exists (t_sort s3). exact HPi. }
      destruct (proj1 (deg_top (t_pi s1 A0 B0) Hderiv) Htop) as [s' [Heqs' _]].
      discriminate Heqs'.

    + exfalso.
      unfold deg in Hdeg. simpl in Hdeg.
      assert (Hsucc : deg (t_pi s1a A0 B0) = deg M0 + 1)
        by (apply deg_typing_succ with Γ0; exact HM).
      assert (Htop : deg (t_pi s1a A0 B0) = n + 1) by (unfold deg in *; simpl in *; lia).
      pose proof (type_correctness Γ0 M0 (t_pi s1a A0 B0) HM) as Hcor.
      destruct Hcor as [[s Hs] | [s Hs]].
      * discriminate Hs.
      * assert (Hderiv : derivable (t_pi s1a A0 B0)).
        { unfold derivable. exists Γ0. exists (t_sort s). exact Hs. }
        destruct (proj1 (deg_top (t_pi s1a A0 B0) Hderiv) Htop) as [s' [Heqs' _]].
        discriminate Heqs'.

    + apply IHM. exact Hdeg.

  - intros [Γ' [s [H1 H2]]].
    pose proof (deg_typing_succ Γ' M (t_sort s) H1). unfold deg in *. simpl in *. lia.
Qed.

Lemma deg_typing : forall M, derivable M -> forall i, (i > 0) -> (i < n) ->
  (deg M = i <-> (exists Γ N s, (Γ ⊢ M ∈ N) /\ (Γ ⊢ N ∈ t_sort s) /\ (index_of s = i + 1))).
Proof.
  intros M [Γ [T Htyp]] i Hi1 Hi2. split.

  - intros Hdeg. pose proof (deg_typing_succ Γ M T Htyp).
    pose proof (type_correctness Γ M T Htyp) as Hcor. destruct Hcor as [[s Hs] | [s Hs]].
    + subst T. unfold deg in *. simpl in *. pose proof (index_range s). assert (Gi : index_of s = i) by lia.
      assert (Hi : 0 < i + 1 < n + 1) by lia.
      pose proof (index_surj (i + 1) Hi) as Hs'. destruct Hs' as [s' Hs'].
      assert (Hss' : A s s') by (apply A_spec; lia).
      exists Γ, (t_sort s), s'. repeat split; auto. apply start_axiom; auto.
      exists M, (t_sort s); auto.
    + pose proof (deg_typing_succ Γ T (t_sort s) Hs). unfold deg in *. simpl in *.
      exists Γ, T, s. repeat split; auto; lia.

  - intros [Γ' [N [s [H1 [H2 H3]]]]].
    pose proof (deg_typing_succ Γ' M N H1) as Hdeg1.
    pose proof (deg_typing_succ Γ' N (t_sort s) H2) as Hdeg2.
    unfold deg in *. simpl in *. lia.
Qed.

Axiom deg_beta : forall M N, (M ->>b N) -> (deg M = deg N).

(* ================================================================= *)
(* Full System *)

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

(* ================================================================= *)
(* The non-dependent typing judgement *)

Reserved Notation "Γ ⊢* M ∈ A" (at level 70, no associativity).

Inductive typing_star : context -> term -> term -> Prop :=
  | typing_star_axiom : forall s s',
      A s s' ->
      [] ⊢* t_sort s ∈ t_sort s'

  | typing_star_var : forall Γ x A s,
      is_fresh x Γ ->
      Γ ⊢* A ∈ t_sort s ->
      Γ ++ [(x, (s, A))] ⊢* t_fvar s x ∈ A

  | typing_star_weak : forall Γ x B M A s,
      is_fresh x Γ ->
      Γ ⊢* M ∈ A ->
      Γ ⊢* B ∈ t_sort s ->
      Γ ++ [(x, (s, B))] ⊢* M ∈ A

  | typing_star_pi : forall Γ A B s1 s2 s3 L,
      Γ ⊢* A ∈ t_sort s1 ->
      (forall x, ~ In x L ->
         Γ ++ [(x, (s1, A))] ⊢* (open_var B s1 x) ∈ t_sort s2) ->
      R_star s1 s2 s3 ->
      Γ ⊢* (t_pi s1 A B) ∈ (t_sort s3)

  | typing_star_lam : forall Γ A M B s1 s3 L,
      Γ ⊢* A ∈ t_sort s1 ->
      (forall x, ~ In x L ->
         Γ ++ [(x, (s1, A))] ⊢* (open_var M s1 x) ∈ (open_var B s1 x)) ->
      Γ ⊢* (t_pi s1 A B) ∈ (t_sort s3) ->
      Γ ⊢* (t_lam s1 A M) ∈ (t_pi s1 A B)

  | typing_star_app : forall Γ M N A B s1,
      Γ ⊢* M ∈ t_pi s1 A B ->
      Γ ⊢* N ∈ A ->
      Γ ⊢* t_app M N ∈ (B ^^ N)

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

(* ================================================================= *)
(* Type-Level Translation *)
(* ρ i : T ≥i+1 → T i+1 *)

Definition zero_var : var := 0.

Lemma zero_var_retag_ne : forall (x : var) (s : Sort),
  retag x s <> zero_var.
Proof. intros x s. unfold zero_var. apply (retag_neq_mult 0). Qed.

Axiom typing_avoids_zero_var :
  forall Γ M N, Γ ⊢ M ∈ N ->
  forall x sA A, In (x, (sA, A)) Γ -> x <> zero_var.

Fixpoint rho_pi_tel (r : nat -> term -> term) (A B : term) (i k : nat) : term :=
  match k with
  | 0    => t_pi (sort_of i) (r i A) (r i B)
  | S k' => t_pi (sort_of (i + S k')) (r (i + S k') A) (rho_pi_tel r A B i k')
  end.

Fixpoint rho_lam_tel (r : nat -> term -> term) (A M' : term) (i k : nat) : term :=
  match k with
  | 0    => t_lam (sort_of (i + 1)) (r (i + 1) A) (r i M')
  | S k' => t_lam (sort_of (i + 1 + S k')) (r (i + 1 + S k') A) (rho_lam_tel r A M' i k')
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
      | 0 => t_fvar (sort_of 2) zero_var
      | _ => t_sort (sort_of i)
      end
  | t_bvar s0 k => t_bvar s0 k
  | t_fvar s0 x =>
      t_fvar (sort_of (i + 2)) (retag x (sort_of (i + 2)))
  | t_pi s A B =>
      match le_lt_dec (i + 1) (deg A) with
      | left _  => rho_pi_tel rho A B i (deg A - 1 - i)
      | right _ => rho i B
      end
  | t_lam s A M' =>
      match le_lt_dec (i + 2) (deg A) with
      | left _  => rho_lam_tel rho A M' i (deg A - 1 - (i + 1))
      | right _ => rho i M'
      end
  | t_app M' N =>
      match le_lt_dec (i + 1) (deg N) with
      | left _  => rho_app_tel rho M' N i (deg N - 1 - i)
      | right _ => rho i M'
      end
  end.

Lemma rho_pi_named : forall i s Dom B, i + 1 <= deg Dom ->
  rho i (t_pi s Dom B) = rho_pi_tel rho Dom B i (deg Dom - 1 - i).
Proof.
  intros i s Dom B Hdeg. simpl.
  destruct (le_lt_dec (i + 1) (deg Dom)); [reflexivity | lia].
Qed.

Lemma rho_lam_named : forall i s Dom B, i + 2 <= deg Dom ->
  rho i (t_lam s Dom B) = rho_lam_tel rho Dom B i (deg Dom - 1 - (i + 1)).
Proof.
  intros i s Dom B Hdeg. simpl.
  destruct (le_lt_dec (i + 2) (deg Dom)); [reflexivity | lia].
Qed.

Lemma rho_app_named : forall i P Q, i + 1 <= deg Q ->
  rho i (t_app P Q) = rho_app_tel rho P Q i (deg Q - 1 - i).
Proof.
  intros i P Q Hdeg. simpl.
  destruct (le_lt_dec (i + 1) (deg Q)); [reflexivity | lia].
Qed.

Fixpoint rho_ctx_tel (x : var) (s : Sort) (T : term) (k : nat) : context :=
  let j := index_of s in
  match k with
  | 0    => [(retag x (sort_of j), (sort_of j, rho (j - 1) T))]
  | S k' => (rho_ctx_tel x s T k')
            ++ [(retag x (sort_of (j - k)), (sort_of (j - k), rho (j - k - 1) T))]
  end.

Fixpoint rho_ctx (i : nat) (Γ : context) : context :=
  match Γ with
  | [] => [(zero_var, (sort_of 2, t_sort (sort_of 1)))]
  | (x, (s, T)) :: Γ' => (rho_ctx_tel x s T (index_of s - i - 1)) ++ rho_ctx i Γ'
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

Lemma rho_ctx_tel_step : forall x s T k,
  rho_ctx_tel x s T k ⊆ rho_ctx_tel x s T (S k).
Proof.
  intros x s T k y T' Hin.
  simpl. apply in_or_app. left. exact Hin.
Qed.

Lemma rho_ctx_tel_sub :
  forall x s T p q,
  p < q -> rho_ctx_tel x s T p ⊆ rho_ctx_tel x s T q.
Proof.
  intros x s T p q Hpq.
  remember (q - p - 1) as d eqn:Hd.
  assert (Hq : q = p + S d) by lia.
  subst q. clear Hpq Hd.
  induction d as [| d IH].
  - replace (p + 1) with (S p) by lia.
    apply rho_ctx_tel_step.
  - replace (p + S (S d)) with (S (p + S d)) by lia.
    intros y T' Hin.
    apply rho_ctx_tel_step.
    apply IH. exact Hin.
Qed.

Definition ctx_above (b : nat) (Γ : context) : Prop :=
  forall x s T, In (x, (s, T)) Γ -> b < index_of s.

Lemma rho_ctx_sub : forall Γ i j,
  i < j -> ctx_above j Γ -> rho_ctx j Γ ⊆ rho_ctx i Γ.
Proof.
  induction Γ as [| [y [s T]] Γ' IH]; intros i j Hij Habove.
  - simpl. unfold subcontext. auto.
  - simpl. apply subcontext_append.
    + apply rho_ctx_tel_sub.
      assert (Hy : j < index_of s).
      { apply Habove with y T. left. reflexivity. }
      lia.
    + apply IH; auto. intros x' s' T' Hin. apply Habove with x' T'. right. exact Hin.
Qed.

(* ================================================================= *)
(* rho commutes with substitution *)

Fixpoint rho_subst_tel (M N : term) (varidx i k : nat) : term :=
  match k with
  | O => M ⁅ retag varidx (sort_of (i + 2)) ≔ rho i N ⁆
  | S k' => rho_subst_tel (M ⁅ retag varidx (sort_of (k + i + 2)) ≔ rho (k + i) N ⁆) N varidx i k'
  end.

Definition rho_subst (M N : term) (x : var) (s : Sort) (i : nat) : term :=
  let j := index_of s in
  match lt_dec j (i + 2) with
  | left _  => rho i M
  | right _ => rho_subst_tel (rho i M) (N) (x) (i) (j - i - 2)
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

Lemma index_of_sort_of_any : forall p, index_of (sort_of p) = 1 \/ index_of (sort_of p) = p.
Proof.
  intros p. unfold sort_of.
  destruct (lt_dec 0 p) as [H1 | H1].
  - destruct (lt_dec p (n + 1)) as [H2 | H2].
    + right. unfold partial_sort_of.
      destruct (constructive_indefinite_description (fun s => index_of s = p)
                  (index_surj p (conj H1 H2))) as [s Hs].
      exact Hs.
    + left. unfold partial_sort_of.
      destruct (constructive_indefinite_description (fun s => index_of s = 1)
                  (index_surj 1 one_in_range)) as [s Hs].
      exact Hs.
  - left. unfold partial_sort_of.
    destruct (constructive_indefinite_description (fun s => index_of s = 1)
                (index_surj 1 one_in_range)) as [s Hs].
    exact Hs.
Qed.

Lemma sort_of_tier_neq : forall D m, m < D -> m + 2 <= n -> sort_of (D + 2) <> sort_of (m + 2).
Proof.
  intros D m Hmd Hmn Heq.
  assert (Hidx : index_of (sort_of (D + 2)) = index_of (sort_of (m + 2))) by (rewrite Heq; reflexivity).
  rewrite (sort_of_correct (m + 2) ltac:(lia) ltac:(lia)) in Hidx.
  destruct (index_of_sort_of_any (D + 2)) as [H | H]; lia.
Qed.

Lemma rho_min_tier_noop : forall M D m v N',
  m < D -> m + 2 <= n ->
  (rho D M) ⁅ retag v (sort_of (m + 2)) ≔ N' ⁆ = rho D M.
Proof.
  induction M as [s | s_k k | sy y | P IHP Q IHQ | s A IHA M' IHM' | s A IHA B IHB];
    intros D m v N' Hmd Hmn.
  - (* t_sort s *)
    destruct D as [| D']; [lia | simpl; reflexivity].
  - (* t_bvar k *)
    simpl; reflexivity.
  - (* t_fvar sy y *)
    simpl.
    destruct (eq_var_dec (retag y (sort_of (D + 2))) (retag v (sort_of (m + 2))))
      as [Heq | Hne]; [ | reflexivity].
    exfalso. apply retag_inj in Heq as [_ Hsort].
    exact (sort_of_tier_neq D m Hmd Hmn Hsort).
  - (* t_app P Q *)
    simpl.
    destruct (le_lt_dec (D + 1) (deg Q)) as [Hle | Hlt].
    + generalize (deg Q - 1 - D) as k.
      induction k as [| k' IHk]; intros.
      * simpl. f_equal.
        -- apply IHP; lia.
        -- apply IHQ; lia.
      * simpl. f_equal.
        -- exact IHk.
        -- apply IHQ; lia.
    + apply IHP; lia.
  - (* t_lam s A M' *)
    simpl.
    destruct (le_lt_dec (D + 2) (deg A)) as [Hle | Hlt].
    + generalize (deg A - 1 - (D + 1)) as k.
      induction k as [| k' IHk]; intros.
      * simpl. f_equal.
        -- apply IHA; lia.
        -- apply IHM'; lia.
      * simpl. f_equal.
        -- apply IHA; lia.
        -- exact IHk.
    + apply IHM'; lia.
  - (* t_pi s A B *)
    simpl.
    destruct (le_lt_dec (D + 1) (deg A)) as [Hle | Hlt].
    + generalize (deg A - 1 - D) as k.
      induction k as [| k' IHk]; intros.
      * simpl. f_equal.
        -- apply IHA; lia.
        -- apply IHB; lia.
      * simpl. f_equal.
        -- apply IHA; lia.
        -- exact IHk.
    + apply IHB; lia.
Qed.

Lemma eq_var_dec_refl : forall v : var, exists e, eq_var_dec v v = left e.
Proof.
  intros v. destruct (eq_var_dec v v) as [e | f].
  - exists e. reflexivity.
  - exfalso. apply f. reflexivity.
Qed.

Lemma subst_high_preserves_clean_low : forall P vhi R vlo,
  vhi <> vlo ->
  (forall N0, R ⁅ vlo ≔ N0 ⁆ = R) ->
  (forall N0, P ⁅ vlo ≔ N0 ⁆ = P) ->
  forall N1, (P ⁅ vhi ≔ R ⁆) ⁅ vlo ≔ N1 ⁆ = P ⁅ vhi ≔ R ⁆.
Proof.
  induction P as [s | s_k k | sy y | P1 IHP1 P2 IHP2 | s A IHA M' IHM' | s A IHA B IHB];
    intros vhi R vlo Hne HRclean HPclean N1.
  - reflexivity.
  - reflexivity.
  - rewrite subst_var. destruct (eq_var_dec y vhi) as [Heq | Hneq].
    + apply HRclean.
    + rewrite subst_var. destruct (eq_var_dec y vlo) as [Heq2 | Hneq2].
      * subst y. specialize (HPclean N1). rewrite subst_var in HPclean.
        destruct (eq_var_dec_refl vlo) as [e Heq]. rewrite Heq in HPclean.
        destruct (eq_var_dec vlo vhi) as [Hc | Hc]; [congruence | exact HPclean].
      * reflexivity.
  - assert (Hclean1 : forall N0, P1 ⁅ vlo ≔ N0 ⁆ = P1).
    { intros N0. specialize (HPclean N0). rewrite subst_app in HPclean. injection HPclean as H1 H2. exact H1. }
    assert (Hclean2 : forall N0, P2 ⁅ vlo ≔ N0 ⁆ = P2).
    { intros N0. specialize (HPclean N0). rewrite subst_app in HPclean. injection HPclean as H1 H2. exact H2. }
    rewrite subst_app. rewrite subst_app. f_equal.
    + apply IHP1; auto.
    + apply IHP2; auto.
  - assert (Hclean1 : forall N0, A ⁅ vlo ≔ N0 ⁆ = A).
    { intros N0. specialize (HPclean N0). rewrite subst_lam in HPclean. injection HPclean as H1 H2. exact H1. }
    assert (Hclean2 : forall N0, M' ⁅ vlo ≔ N0 ⁆ = M').
    { intros N0. specialize (HPclean N0). rewrite subst_lam in HPclean. injection HPclean as H1 H2. exact H2. }
    rewrite subst_lam. rewrite subst_lam. f_equal.
    + apply IHA; auto.
    + apply IHM'; auto.
  - assert (Hclean1 : forall N0, A ⁅ vlo ≔ N0 ⁆ = A).
    { intros N0. specialize (HPclean N0). rewrite subst_pi in HPclean. injection HPclean as H1 H2. exact H1. }
    assert (Hclean2 : forall N0, B ⁅ vlo ≔ N0 ⁆ = B).
    { intros N0. specialize (HPclean N0). rewrite subst_pi in HPclean. injection HPclean as H1 H2. exact H2. }
    rewrite subst_pi. rewrite subst_pi. f_equal.
    + apply IHA; auto.
    + apply IHB; auto.
Qed.

Fixpoint only_tagged (x : var) (s : Sort) (t : term) : Prop :=
  match t with
  | t_sort _    => True
  | t_bvar _ _  => True
  | t_fvar s0 y => y = x -> s0 = s
  | t_app P Q   => only_tagged x s P /\ only_tagged x s Q
  | t_pi _ A B  => only_tagged x s A /\ only_tagged x s B
  | t_lam _ A M => only_tagged x s A /\ only_tagged x s M
  end.

Lemma deg_subst_tagged : forall C x s N,
  only_tagged x s C -> lc N -> deg N = index_of s - 1 ->
  deg (C ⁅ x ≔ N ⁆) = deg C.
Proof.
  induction C as [s0 | s_k k | s0 y | P IHP Q IHQ | s1 A IHA M IHM | s1 A IHA B IHB];
    intros x s N Htag HlcN HdegN; simpl in *.
  - reflexivity.
  - reflexivity.
  - destruct (eq_var_dec y x) as [Heq | Hneq].
    + subst y. rewrite (Htag eq_refl). exact HdegN.
    + reflexivity.
  - destruct Htag as [HtagP _]. apply (IHP x s N HtagP HlcN HdegN).
  - destruct Htag as [_ HtagM]. apply (IHM x s N HtagM HlcN HdegN).
  - destruct Htag as [_ HtagB]. apply (IHB x s N HtagB HlcN HdegN).
Qed.

Lemma rho_subst_tel_noop_generic : forall P N varidx D i0 K,
  i0 + K + 2 <= n ->
  (forall m v N0, m < D -> m + 2 <= n -> P ⁅ retag v (sort_of (m + 2)) ≔ N0 ⁆ = P) ->
  i0 + K + 1 <= D ->
  rho_subst_tel P N varidx i0 K = P.
Proof.
  intros P N varidx D i0 K HKn HcleanP.
  revert i0 HKn HcleanP. induction K as [| K' IHK]; intros i0 HKn HcleanP Htop.
  - simpl. apply HcleanP; lia.
  - simpl.
    assert (HS1 : S (K' + i0) = (S K' + i0)) by lia. rewrite HS1.
    assert (HS2 : S (K' + i0 + 2) = S K' + i0 + 2) by lia. rewrite HS2.
    rewrite (HcleanP (S K' + i0) varidx (rho (S K' + i0) N)); [ | lia | lia].
    apply IHK; [lia | exact HcleanP | lia].
Qed.

Lemma rho_subst_tel_stays_clean : forall P N varidx D i0 K,
  D <= i0 ->
  (forall m v N0, m < D -> m + 2 <= n -> P ⁅ retag v (sort_of (m + 2)) ≔ N0 ⁆ = P) ->
  forall m v N0, m < D -> m + 2 <= n ->
    (rho_subst_tel P N varidx i0 K) ⁅ retag v (sort_of (m + 2)) ≔ N0 ⁆ = rho_subst_tel P N varidx i0 K.
Proof.
  intros P N varidx D i0 K. revert P.
  induction K as [| K' IHK]; intros P Hle HcleanP m v N0 Hmd Hmn.
  - simpl. apply subst_high_preserves_clean_low.
    + intro Hc. apply retag_inj in Hc as [_ Hsc]. apply (sort_of_tier_neq i0 m); [lia | lia | exact Hsc].
    + intros N1. apply rho_min_tier_noop; lia.
    + intros N1. apply HcleanP; auto.
  - simpl. apply IHK.
    + lia.
    + intros m' v' N0' Hmd' Hmn'. apply subst_high_preserves_clean_low.
      * intro Hc. apply retag_inj in Hc as [_ Hsc]. apply (sort_of_tier_neq (S K' + i0) m'); [lia | lia | exact Hsc].
      * intros N1. apply rho_min_tier_noop; lia.
      * intros N1. apply HcleanP; auto.
    + exact Hmd.
    + exact Hmn.
Qed.

Lemma rho_subst_tel_split : forall P N varidx i0 K D,
  i0 < D -> D <= i0 + K ->
  rho_subst_tel P N varidx i0 K
  = rho_subst_tel (rho_subst_tel P N varidx D (i0 + K - D)) N varidx i0 (D - i0 - 1).
Proof.
  intros P N varidx i0 K. revert P i0.
  induction K as [| K' IHK]; intros P i0 D Hlt Hle.
  - lia.
  - destruct (Nat.eq_dec D (i0 + S K')) as [Heq | Hneq].
    + subst D.
      replace (i0 + S K' - (i0 + S K')) with 0 by lia.
      simpl.
      replace (i0 + S K' - i0 - 1) with K' by lia.
      replace (i0 + S K') with (S K' + i0) by lia.
      reflexivity.
    + assert (HleK' : D <= i0 + K') by lia.
      simpl.
      assert (HS1 : S (K' + i0 + 2) = S K' + i0 + 2) by lia. rewrite HS1.
      assert (HS2 : S (K' + i0) = S K' + i0) by lia. rewrite HS2.
      rewrite (IHK (P ⁅ retag varidx (sort_of (S K' + i0 + 2)) ≔ rho (S K' + i0) N ⁆) i0 D Hlt HleK').
      replace (i0 + S K' - D) with (S (i0 + K' - D)) by lia.
      simpl.
      f_equal.
      replace (i0 + K' - D + D + 2) with (K' + i0 + 2) by lia.
      replace (i0 + K' - D + D) with (K' + i0) by lia.
      reflexivity.
Qed.

Lemma rho_subst_tel_pi_commute : forall N s' A' B' varidx i k,
  rho_subst_tel (t_pi s' A' B') N varidx i k
  = t_pi s' (rho_subst_tel A' N varidx i k) (rho_subst_tel B' N varidx i k).
Proof.
  intros N s' A' B' varidx i k.
  revert A' B' s'.
  induction k as [| k' IHk]; intros s' A' B'; simpl; auto.
Qed.

Lemma rho_subst_tel_pi_tel_commute : forall A B N varidx i0 k0 i1 k1,
  rho_subst_tel (rho_pi_tel rho A B i1 k1) N varidx i0 k0
  = rho_pi_tel (fun i' M => rho_subst_tel (rho i' M) N varidx i0 k0) A B i1 k1.
Proof.
  intros A B N varidx i0 k0 i1.
  induction k1 as [| k1' IHk1]; intros.
  - simpl. apply rho_subst_tel_pi_commute.
  - simpl. rewrite rho_subst_tel_pi_commute. f_equal. apply IHk1.
Qed.

Lemma rho_subst_tel_app_commute : forall N A' B' varidx i k,
  rho_subst_tel (t_app A' B') N varidx i k
  = t_app (rho_subst_tel A' N varidx i k) (rho_subst_tel B' N varidx i k).
Proof.
  intros N A' B' varidx i k.
  revert A' B'.
  induction k as [| k' IHk]; intros A' B'; simpl; auto.
Qed.

Lemma rho_subst_tel_app_tel_commute : forall A B N varidx i0 k0 i1 k1,
  rho_subst_tel (rho_app_tel rho A B i1 k1) N varidx i0 k0
  = rho_app_tel (fun i' M => rho_subst_tel (rho i' M) N varidx i0 k0) A B i1 k1.
Proof.
  intros A B N varidx i0 k0 i1.
  induction k1 as [| k1' IHk1]; intros.
  - simpl. apply rho_subst_tel_app_commute.
  - simpl. rewrite rho_subst_tel_app_commute. f_equal. apply IHk1.
Qed.

Lemma rho_subst_tel_lam_commute : forall N s' A' B' varidx i k,
  rho_subst_tel (t_lam s' A' B') N varidx i k
  = t_lam s' (rho_subst_tel A' N varidx i k) (rho_subst_tel B' N varidx i k).
Proof.
  intros N s' A' B' varidx i k.
  revert A' B' s'.
  induction k as [| k' IHk]; intros s' A' B'; simpl; auto.
Qed.

Lemma rho_subst_tel_lam_tel_commute : forall A B N varidx i0 k0 i1 k1,
  rho_subst_tel (rho_lam_tel rho A B i1 k1) N varidx i0 k0
  = rho_lam_tel (fun i' M => rho_subst_tel (rho i' M) N varidx i0 k0) A B i1 k1.
Proof.
  intros A B N varidx i0 k0 i1.
  induction k1 as [| k1' IHk1]; intros.
  - simpl. apply rho_subst_tel_lam_commute.
  - simpl. rewrite rho_subst_tel_lam_commute. f_equal. apply IHk1.
Qed.

Lemma rho_commutes_substitution :
  forall i, 0 <= i <= n ->
  forall x s, x <> zero_var -> 1 <= index_of s <= n ->
  forall M, deg M >= i + 1 -> only_tagged x s M ->
  forall N, deg N = index_of s - 1 -> lc N ->
  rho i (M ⁅ x ≔ N ⁆) = rho_subst M N x s i.
Proof.
  intros i.
  induction i as [i IHouter] using
    (well_founded_induction (Wf_nat.well_founded_ltof nat (fun i => n - i))).
  intros Hi x s Hxnz Hx M.
  induction M as [s0 | s_m m | sy y | D IHD C IHC | s1 C IHC D IHD | s1 C IHC D IHD];
    intros Hdeg Honly N HdegN HlcN.

  - (* M = t_sort s0 *)
    rewrite subst_sort. unfold rho_subst.
    destruct (lt_dec (index_of s) (i + 2)) as [E | E]; auto.
    assert (Hconst : forall k M0,
                  k <= index_of s - i - 2 ->
                  (exists s0', M0 = t_sort s0') \/ (i = 0 /\ M0 = t_fvar (sort_of 2) zero_var) ->
                  rho_subst_tel M0 N x i k = M0).
        { induction k as [| k' IHk]; intros M0 Hkbound Hcase.
          - simpl. destruct Hcase as [[s0' Heq] | [Hi0 Heq]]; subst M0.
            + rewrite subst_sort. reflexivity.
            + rewrite subst_var.
              destruct (eq_var_dec zero_var (retag x (sort_of (i + 2)))) as [Heq2 | Hne2]; auto.
              exfalso. apply (zero_var_retag_ne x (sort_of (i + 2))). symmetry. exact Heq2.
          - simpl. destruct Hcase as [[s0' Heq] | [Hi0 Heq]]; subst M0.
            + rewrite subst_sort. apply IHk; [lia | left; exists s0'; reflexivity].
            + rewrite subst_var.
              destruct (eq_var_dec zero_var (retag x (sort_of (k' + i + 2)))) as [Heq2 | Hne2].
              * exfalso. apply (zero_var_retag_ne x (sort_of (k' + i + 2))). symmetry. exact Heq2.
              * destruct (eq_var_dec zero_var (retag x (sort_of (S (k' + i + 2))))) as [Heq3 | Hne3].
                -- exfalso. apply (zero_var_retag_ne x (sort_of (S (k' + i + 2)))). symmetry. exact Heq3.
                -- apply IHk; [lia | right; split; [exact Hi0 | reflexivity]].
        }
    symmetry. apply Hconst; auto.
    destruct i as [| i'].
      + right. split; auto.
      + left. exists (sort_of (S i')). reflexivity.

  - (* M = t_bvar m *)
    rewrite subst_bvar. unfold rho_subst.
    destruct (lt_dec (index_of s) (i + 2)) as [E | E].
    + reflexivity.
    + assert (Hconst : forall sy0 y0 k, t_bvar sy0 y0 = rho_subst_tel (t_bvar sy0 y0) N x i k)
      by (induction k as [| k' IHk]; auto).
      apply Hconst.

  - (* M = t_fvar sy y *)
    cbn in Hdeg. unfold rho_subst.
    destruct (lt_dec (index_of s) (i + 2)) as [E | E].
    + rewrite subst_var. destruct (eq_var_dec y x) as [Heq | Hneq].
      * exfalso. subst y. simpl in Honly. specialize (Honly eq_refl). rewrite Honly in Hdeg.
        pose proof (index_range s) as [Hsr1 Hsr2]. lia.
      * reflexivity.
    + rewrite subst_var. destruct (eq_var_dec y x) as [Heq | Hneq].
      * subst y. remember (retag x (sort_of (i + 2))) as z eqn:Heqz.
        assert (Hz : rho i N = (t_fvar (sort_of (i + 2)) z) ⁅ z ≔ rho i N ⁆).
        { rewrite subst_var. destruct (eq_var_dec z z) as [_ | Hc]; [reflexivity | exfalso; apply Hc; reflexivity]. }
        rewrite Hz. simpl. rewrite <- Heqz.
        assert (Hconst : forall k, k <= index_of s - i - 2 ->
          rho_subst_tel (t_fvar (sort_of (i + 2)) z) N x i k = (t_fvar (sort_of (i + 2)) z) ⁅ z ≔ rho i N ⁆).
        { induction k as [| k' IHk]; intros Hk.
          - simpl. rewrite <- Heqz. reflexivity.
          - simpl.
            assert (Hlevel_ne : retag x (sort_of (S (k' + i + 2))) <> z).
            { rewrite Heqz. intro Hcontra.
              apply retag_inj in Hcontra as [_ Hsort].
              assert (Heq2 : S (k' + i + 2) = i + 2)
                by (apply (sort_of_inj (S (k' + i + 2)) (i + 2)); [lia | lia | lia | lia | exact Hsort]).
              lia. }
            destruct (eq_var_dec z (retag x (sort_of (S (k' + i + 2))))) as [Heq | Hne].
            + exfalso. apply Hlevel_ne. symmetry. exact Heq.
            + apply IHk. lia.
        }
        symmetry. apply Hconst. lia.
      * assert (Hconst : forall k, rho_subst_tel (t_fvar (sort_of (i + 2)) (retag y (sort_of (i + 2)))) N x i k
                          = t_fvar (sort_of (i + 2)) (retag y (sort_of (i + 2)))).
        { induction k as [| k' IHk].
          - simpl. destruct (eq_var_dec (retag y (sort_of (i + 2))) (retag x (sort_of (i + 2)))) as [Heq | Hne].
            + exfalso. apply retag_inj in Heq as [Heqxy _]. apply Hneq. exact Heqxy.
            + reflexivity.
          - simpl. destruct (eq_var_dec (retag y (sort_of (i + 2))) (retag x (sort_of (S (k' + i + 2))))) as [Heq | Hne].
            + exfalso. apply retag_inj in Heq as [Heqxy _]. apply Hneq. exact Heqxy.
            + exact IHk.
        }
        symmetry. apply Hconst.

  - (* M = t_app D C *)
    destruct Honly as [HonlyD HonlyC].
    assert (HdegEqC : deg (C ⁅ x ≔ N ⁆) = deg C)
    by (apply (deg_subst_tagged C x s N); auto).
    assert (HdegEqD : deg (D ⁅ x ≔ N ⁆) = deg D)
    by (apply (deg_subst_tagged D x s N); auto).

    destruct (le_lt_dec (i + 1) (deg C)) as [HdegC | HdegC].

    + (* deg C >= i+1 *)
      rewrite subst_app. unfold rho_subst in *.
      assert (E : i + 1 <= deg (C ⁅ x ≔ N ⁆)) by lia.
      rewrite (rho_app_named i (D⁅x≔N⁆) (C⁅x≔N⁆) E).
      rewrite (rho_app_named i D C HdegC).
      destruct (lt_dec (index_of s) (i + 2)) as [Hj | Hj].

        ++ (* j < i+2 *)
          rewrite HdegEqC. remember (deg C - 1 - i) as k.
          assert (Htel : forall k', k' <= k -> rho_app_tel rho (D⁅x≔N⁆) (C⁅x≔N⁆) i k' = rho_app_tel rho D C i k').
          { induction k' as [| k'' IHk']; intros Hk'.
            - simpl. f_equal.
              + apply IHD; auto.
              + apply IHC; auto.
            - simpl. f_equal.
              + apply IHk'. lia.
              + assert (HCle : deg C <= n + 1) by (apply deg_le_top).
                assert (HIH : rho (i + S k'') (C⁅x≔N⁆) = rho_subst C N x s (i + S k''))
                  by (apply IHouter; [unfold ltof; lia | lia | exact Hxnz | exact Hx | unfold deg in *; lia | exact HonlyC | exact HdegN | exact HlcN]).
                rewrite HIH. unfold rho_subst.
                destruct (lt_dec (index_of s) (i + S k'' + 2)) as [_ | Hcontra]; [reflexivity | lia]. }
           apply Htel; lia.

        ++ (* j >= i+2 *)
          rewrite HdegEqC.
          assert (FD : rho i (D ⁅ x ≔ N ⁆) = rho_subst_tel (rho i D) N x i (index_of s - i - 2))
          by (apply IHD; auto).
          assert (FC : rho i (C ⁅ x ≔ N ⁆) = rho_subst_tel (rho i C) N x i (index_of s - i - 2))
          by (apply IHC; auto).

          remember (fun i0 M0 => rho_subst M0 N x s i0) as f.
          assert (Step1 : forall k, k <= deg C - 1 - i ->
                    rho_app_tel rho (D⁅x≔N⁆) (C⁅x≔N⁆) i k = rho_app_tel f D C i k).
          { induction k as [| k' IHk]; intros Hk.
            - simpl. rewrite Heqf. f_equal.
              + unfold rho_subst.
                destruct (lt_dec (index_of s) (i + 2)) as [Hlt0 | Hge0]; [lia | exact FD].
              + unfold rho_subst.
                destruct (lt_dec (index_of s) (i + 2)) as [Hlt0 | Hge0]; [lia | exact FC].
            - simpl. rewrite Heqf. f_equal.
              + rewrite <- Heqf. apply IHk. lia.
              + assert (HCle : deg C <= n + 1) by (apply deg_le_top).
                apply IHouter; [unfold ltof; lia | lia | exact Hxnz | exact Hx | unfold deg in *; lia | exact HonlyC | exact HdegN | exact HlcN].
          }
          rewrite Step1; auto.

          assert (Step2 : forall k, k <= deg C - 1 - i ->
                rho_app_tel f D C i k = rho_subst_tel (rho_app_tel rho D C i k) N x i (index_of s - i - 2)).
          {
            intros k.
            rewrite (rho_subst_tel_app_tel_commute D C N x i (index_of s - i - 2) i k).
            induction k as [| k' IHk]; intros Hk.
            - simpl. rewrite Heqf. simpl. f_equal.
              + unfold rho_subst. destruct (lt_dec (index_of s) (i + 2)) as [Hlt0 | Hge0]; [lia | reflexivity].
              + unfold rho_subst. destruct (lt_dec (index_of s) (i + 2)) as [Hlt0 | Hge0]; [lia | reflexivity].
            - simpl. f_equal.
              + apply IHk. lia.
              + rewrite Heqf. simpl. unfold rho_subst.
                destruct (lt_dec (index_of s) (i + S k' + 2)) as [HjA | HjB].
                * assert (HCle : deg C <= n + 1) by (apply deg_le_top).
                  symmetry.
                  apply (rho_subst_tel_noop_generic (rho (i + S k') C) N x (i + S k') i (index_of s - i - 2)).
                  -- lia.
                  -- intros m v N0 Hm Hn. apply rho_min_tier_noop; lia.
                  -- lia.
                * assert (HCle : deg C <= n + 1) by (apply deg_le_top).
                  assert (Hsplit := rho_subst_tel_split (rho (i + S k') C) N x i (index_of s - i - 2) (i + S k')
                                       ltac:(lia) ltac:(lia)).
                  replace (i + (index_of s - i - 2) - (i + S k'))
                    with (index_of s - (i + S k') - 2) in Hsplit by lia.
                  rewrite Hsplit.
                  replace (i + S k' - i - 1) with k' by lia.
                  symmetry.
                  apply rho_subst_tel_noop_generic with (D := i + S k').
                  -- lia.
                  -- apply rho_subst_tel_stays_clean with (D := i + S k').
                     ++ lia.
                     ++ intros m v N0 Hm Hn. apply rho_min_tier_noop; lia.
                  -- lia.
          }
          rewrite Step2; auto.

    + (* deg C < i+1 *)
      assert (HdegC' : deg (C ⁅ x ≔ N ⁆) < i + 1) by lia.
      simpl.
      destruct (le_lt_dec (i + 1) (deg (C ⁅ x ≔ N ⁆))) as [E | E]. lia.
      unfold rho_subst in *.
      destruct (lt_dec (index_of s) (i + 2)) as [Hj | Hj].

      * (* j < i+2 *)
        simpl. destruct (le_lt_dec (i + 1) (deg C)) as [E' | E']. lia.
        apply IHD; auto.

      * (* j >= i+2 *)
        assert (F : rho i (D ⁅ x ≔ N ⁆) = rho_subst_tel (rho i D) N x i (index_of s - i - 2))
        by (apply IHD; auto).
        rewrite F. f_equal. simpl.
        destruct (le_lt_dec (i + 1) (deg C)) as [E' | E']. lia. auto.

  - (* M = t_lam s1 C D *)
    destruct Honly as [HonlyC HonlyD].
    assert (HdegEqC : deg (C ⁅ x ≔ N ⁆) = deg C)
    by (apply (deg_subst_tagged C x s N); auto).
    destruct (le_lt_dec (i + 2) (deg C)) as [HdegC | HdegC].

    + (* deg C >= i+2 *)
      rewrite subst_lam. unfold rho_subst in *.
      assert (E : i + 2 <= deg (C ⁅ x ≔ N ⁆)) by lia.
      assert (HCle : deg C <= n + 1) by (apply deg_le_top).
      rewrite (rho_lam_named i s1 (C⁅x≔N⁆) (D⁅x≔N⁆) E).
      rewrite (rho_lam_named i s1 C D HdegC).
      destruct (lt_dec (index_of s) (i + 2)) as [Hj | Hj].

        ++ (* j < i+2 *)
          rewrite HdegEqC. remember (deg C - 1 - (i + 1)) as k.
          assert (Htel : forall k', k' <= k -> rho_lam_tel rho (C⁅x≔N⁆) (D⁅x≔N⁆) i k' = rho_lam_tel rho C D i k').
          { induction k' as [| k'' IHk']; intros Hk'.
            - simpl. f_equal.
              + assert (HIH : rho (i + 1) (C⁅x≔N⁆) = rho_subst C N x s (i + 1))
                  by (apply IHouter; [unfold ltof; lia | lia | exact Hxnz | exact Hx | unfold deg in *; lia | exact HonlyC | exact HdegN | exact HlcN]).
                rewrite HIH. unfold rho_subst.
                destruct (lt_dec (index_of s) (i + 1 + 2)) as [_ | Hcontra]; [reflexivity | lia].
              + apply IHD; auto.
            - simpl. f_equal.
              + assert (HIH : rho (i + 1 + S k'') (C⁅x≔N⁆) = rho_subst C N x s (i + 1 + S k''))
                  by (apply IHouter; [unfold ltof; lia | lia | exact Hxnz | exact Hx | unfold deg in *; lia | exact HonlyC | exact HdegN | exact HlcN]).
                rewrite HIH. unfold rho_subst.
                destruct (lt_dec (index_of s) (i + 1 + S k'' + 2)) as [_ | Hcontra]; [reflexivity | lia].
              + apply IHk'. lia. }
           apply Htel; lia.

        ++ (* j >= i+2 *)
          rewrite HdegEqC.
          assert (FD : rho i (D ⁅ x ≔ N ⁆) = rho_subst_tel (rho i D) N x i (index_of s - i - 2))
          by (apply IHD; auto).

          remember (fun i0 M0 => rho_subst M0 N x s i0) as f.
          assert (Step1 : forall k, k <= deg C - 1 - (i + 1) ->
                    rho_lam_tel rho (C⁅x≔N⁆) (D⁅x≔N⁆) i k = rho_lam_tel f C D i k).
          { induction k as [| k' IHk]; intros Hk.
            - simpl. rewrite Heqf. f_equal.
              + apply IHouter; [unfold ltof; lia | lia | exact Hxnz | exact Hx | unfold deg in *; lia | exact HonlyC | exact HdegN | exact HlcN].
              + unfold rho_subst.
                destruct (lt_dec (index_of s) (i + 2)) as [Hlt0 | Hge0]; [lia | exact FD].
            - simpl. rewrite Heqf. f_equal.
              + apply IHouter; [unfold ltof; lia | lia | exact Hxnz | exact Hx | unfold deg in *; lia | exact HonlyC | exact HdegN | exact HlcN].
              + rewrite <- Heqf. apply IHk. lia.
          }
          rewrite Step1; auto.

          assert (Step2 : forall k, k <= deg C - 1 - (i + 1) ->
                rho_lam_tel f C D i k = rho_subst_tel (rho_lam_tel rho C D i k) N x i (index_of s - i - 2)).
          {
            intros k.
            rewrite (rho_subst_tel_lam_tel_commute C D N x i (index_of s - i - 2) i k).
            induction k as [| k' IHk]; intros Hk.
            - simpl. rewrite Heqf. simpl. f_equal.
              + unfold rho_subst.
                destruct (lt_dec (index_of s) (i + 1 + 2)) as [HjA | HjB].
                * symmetry.
                  apply (rho_subst_tel_noop_generic (rho (i + 1) C) N x (i + 1) i (index_of s - i - 2)).
                  -- lia.
                  -- intros m v N0 Hm Hn. apply rho_min_tier_noop; lia.
                  -- lia.
                * assert (Hsplit := rho_subst_tel_split (rho (i + 1) C) N x i (index_of s - i - 2) (i + 1)
                                       ltac:(lia) ltac:(lia)).
                  replace (i + (index_of s - i - 2) - (i + 1))
                    with (index_of s - (i + 1) - 2) in Hsplit by lia.
                  rewrite Hsplit.
                  replace (i + 1 - i - 1) with 0 by lia.
                  symmetry.
                  apply rho_subst_tel_noop_generic with (D := i + 1).
                  -- lia.
                  -- apply rho_subst_tel_stays_clean with (D := i + 1).
                     ++ lia.
                     ++ intros m v N0 Hm Hn. apply rho_min_tier_noop; lia.
                  -- lia.
              + unfold rho_subst. destruct (lt_dec (index_of s) (i + 2)) as [Hlt0 | Hge0]; [lia | reflexivity].
            - simpl. f_equal.
              + rewrite Heqf. simpl. unfold rho_subst.
                destruct (lt_dec (index_of s) (i + 1 + S k' + 2)) as [HjA | HjB].
                * symmetry.
                  apply (rho_subst_tel_noop_generic (rho (i + 1 + S k') C) N x (i + 1 + S k') i (index_of s - i - 2)).
                  -- lia.
                  -- intros m v N0 Hm Hn. apply rho_min_tier_noop; lia.
                  -- lia.
                * assert (Hsplit := rho_subst_tel_split (rho (i + 1 + S k') C) N x i (index_of s - i - 2) (i + 1 + S k')
                                       ltac:(lia) ltac:(lia)).
                  replace (i + (index_of s - i - 2) - (i + 1 + S k'))
                    with (index_of s - (i + 1 + S k') - 2) in Hsplit by lia.
                  rewrite Hsplit.
                  replace (i + 1 + S k' - i - 1) with (S k') by lia.
                  symmetry.
                  apply rho_subst_tel_noop_generic with (D := i + 1 + S k').
                  -- lia.
                  -- apply rho_subst_tel_stays_clean with (D := i + 1 + S k').
                     ++ lia.
                     ++ intros m v N0 Hm Hn. apply rho_min_tier_noop; lia.
                  -- lia.
              + apply IHk. lia.
          }
          rewrite Step2; auto.

    + (* deg C < i+2 *)
      assert (HdegC' : deg (C ⁅ x ≔ N ⁆) < i + 2) by lia.
      simpl.
      destruct (le_lt_dec (i + 2) (deg (C ⁅ x ≔ N ⁆))) as [E | E]. lia.
      unfold rho_subst in *.
      destruct (lt_dec (index_of s) (i + 2)) as [Hj | Hj].

      * (* j < i+2 *)
        simpl. destruct (le_lt_dec (i + 2) (deg C)) as [E' | E']. lia.
        apply IHD; auto.

      * (* j >= i+2 *)
        assert (F : rho i (D ⁅ x ≔ N ⁆) = rho_subst_tel (rho i D) N x i (index_of s - i - 2))
        by (apply IHD; auto).
        rewrite F. f_equal. simpl.
        destruct (le_lt_dec (i + 2) (deg C)) as [E' | E']. lia. auto.

  - (* M = t_pi s1 C D *)
    destruct Honly as [HonlyC HonlyD].
    assert (HdegEqC : deg (C ⁅ x ≔ N ⁆) = deg C)
    by (apply (deg_subst_tagged C x s N); auto).
    destruct (le_lt_dec (i + 1) (deg C)) as [HdegC | HdegC].

    + (* deg C >= i+1 *)
      rewrite subst_pi. unfold rho_subst in *.
      assert (E : i + 1 <= deg (C ⁅ x ≔ N ⁆)) by lia.
      rewrite (rho_pi_named i s1 (C⁅x≔N⁆) (D⁅x≔N⁆) E).
      rewrite (rho_pi_named i s1 C D HdegC).
      destruct (lt_dec (index_of s) (i + 2)) as [Hj | Hj].

        ++ (* j < i+2 *)
          rewrite HdegEqC. remember (deg C - 1 - i) as k.
          assert (Htel : forall k', k' <= k -> rho_pi_tel rho (C⁅x≔N⁆) (D⁅x≔N⁆) i k' = rho_pi_tel rho C D i k').
          { induction k' as [| k'' IHk']; intros Hk'.
            - simpl. f_equal.
              + apply IHC; auto.
              + apply IHD; auto.
            - simpl. f_equal.
              + assert (HCle : deg C <= n + 1) by (apply deg_le_top).
                assert (HIH : rho (i + S k'') (C⁅x≔N⁆) = rho_subst C N x s (i + S k''))
                  by (apply IHouter; [unfold ltof; lia | lia | exact Hxnz | exact Hx | unfold deg in *; lia | exact HonlyC | exact HdegN | exact HlcN]).
                rewrite HIH. unfold rho_subst.
                destruct (lt_dec (index_of s) (i + S k'' + 2)) as [_ | Hcontra]; [reflexivity | lia].
              + apply IHk'. lia. }
           apply Htel; lia.

        ++ (* j >= i+2 *)
          rewrite HdegEqC.
          assert (FD : rho i (D ⁅ x ≔ N ⁆) = rho_subst_tel (rho i D) N x i (index_of s - i - 2))
          by (apply IHD; auto).
          assert (FC : rho i (C ⁅ x ≔ N ⁆) = rho_subst_tel (rho i C) N x i (index_of s - i - 2))
          by (apply IHC; auto).

          remember (fun i0 M0 => rho_subst M0 N x s i0) as f.
          assert (Step1 : forall k, k <= deg C - 1 - i ->
                    rho_pi_tel rho (C⁅x≔N⁆) (D⁅x≔N⁆) i k = rho_pi_tel f C D i k).
          { induction k as [| k' IHk]; intros Hk.
            - simpl. rewrite Heqf. f_equal.
              + unfold rho_subst.
                destruct (lt_dec (index_of s) (i + 2)) as [Hlt0 | Hge0]; [lia | exact FC].
              + unfold rho_subst.
                destruct (lt_dec (index_of s) (i + 2)) as [Hlt0 | Hge0]; [lia | exact FD].
            - simpl. rewrite Heqf. f_equal.
              + assert (HCle : deg C <= n + 1) by (apply deg_le_top).
                apply IHouter; [unfold ltof; lia | lia | exact Hxnz | exact Hx | unfold deg in *; lia | exact HonlyC | exact HdegN | exact HlcN].
              + rewrite <- Heqf. apply IHk. lia.
          }
          rewrite Step1; auto.

          assert (Step2 : forall k, k <= deg C - 1 - i ->
                rho_pi_tel f C D i k = rho_subst_tel (rho_pi_tel rho C D i k) N x i (index_of s - i - 2)).
          {
            intros k.
            rewrite (rho_subst_tel_pi_tel_commute C D N x i (index_of s - i - 2) i k).
            induction k as [| k' IHk]; intros Hk.
            - simpl. rewrite Heqf. simpl. f_equal.
              + unfold rho_subst. destruct (lt_dec (index_of s) (i + 2)) as [Hlt0 | Hge0]; [lia | reflexivity].
              + unfold rho_subst. destruct (lt_dec (index_of s) (i + 2)) as [Hlt0 | Hge0]; [lia | reflexivity].
            - simpl. f_equal.
              + rewrite Heqf. simpl. unfold rho_subst.
                destruct (lt_dec (index_of s) (i + S k' + 2)) as [HjA | HjB].
                * assert (HCle : deg C <= n + 1) by (apply deg_le_top).
                  symmetry.
                  apply (rho_subst_tel_noop_generic (rho (i + S k') C) N x (i + S k') i (index_of s - i - 2)).
                  -- lia.
                  -- intros m v N0 Hm Hn. apply rho_min_tier_noop; lia.
                  -- lia.
                * assert (HCle : deg C <= n + 1) by (apply deg_le_top).
                  assert (Hsplit := rho_subst_tel_split (rho (i + S k') C) N x i (index_of s - i - 2) (i + S k')
                                       ltac:(lia) ltac:(lia)).
                  replace (i + (index_of s - i - 2) - (i + S k'))
                    with (index_of s - (i + S k') - 2) in Hsplit by lia.
                  rewrite Hsplit.
                  replace (i + S k' - i - 1) with k' by lia.
                  symmetry.
                  apply rho_subst_tel_noop_generic with (D := i + S k').
                  -- lia.
                  -- apply rho_subst_tel_stays_clean with (D := i + S k').
                     ++ lia.
                     ++ intros m v N0 Hm Hn. apply rho_min_tier_noop; lia.
                  -- lia.
              + apply IHk. lia.
          }
          rewrite Step2; auto.

    + (* deg C < i+1 *)
      assert (HdegC' : deg (C ⁅ x ≔ N ⁆) < i + 1) by lia.
      simpl.
      destruct (le_lt_dec (i + 1) (deg (C ⁅ x ≔ N ⁆))) as [E | E]. lia.
      unfold rho_subst in *.
      destruct (lt_dec (index_of s) (i + 2)) as [Hj | Hj].

      * (* j < i+2 *)
        simpl. destruct (le_lt_dec (i + 1) (deg C)) as [E' | E']. lia.
        apply IHD; auto.

      * (* j >= i+2 *)
        assert (F : rho i (D ⁅ x ≔ N ⁆) = rho_subst_tel (rho i D) N x i (index_of s - i - 2))
        by (apply IHD; auto).
        rewrite F. f_equal. simpl.
        destruct (le_lt_dec (i + 1) (deg C)) as [E' | E']. lia. auto.
Qed.

(* ================================================================= *)
(* rho commutes with beta *)

Lemma brt_pi_A : forall s A A' B, A ->>b A' -> t_pi s A B ->>b t_pi s A' B.
Proof.
  intros s A A' B H.
  induction H as [A | A A' HA | A A' A'' H1 IH1 H2 IH2].
  - apply brt_refl.
  - apply brt_step. apply beta_pi_A. exact HA.
  - apply brt_trans with (t_pi s A' B); auto.
Qed.

Lemma brt_pi_B : forall s A B B', B ->>b B' -> t_pi s A B ->>b t_pi s A B'.
Proof.
  intros s A B B' H.
  induction H as [B | B B' HB | B B' B'' H1 IH1 H2 IH2].
  - apply brt_refl.
  - apply brt_step. apply beta_pi_B. exact HB.
  - apply brt_trans with (t_pi s A B'); auto.
Qed.

Lemma brt_pi_congr : forall s A A' B B',
  A ->>b A' -> B ->>b B' -> t_pi s A B ->>b t_pi s A' B'.
Proof.
  intros s A A' B B' HA HB.
  apply brt_trans with (t_pi s A' B).
  - apply brt_pi_A. exact HA.
  - apply brt_pi_B. exact HB.
Qed.

Lemma brt_lam_A : forall s A A' M, A ->>b A' -> t_lam s A M ->>b t_lam s A' M.
Proof.
  intros s A A' M H.
  induction H as [A | A A' HA | A A' A'' H1 IH1 H2 IH2].
  - apply brt_refl.
  - apply brt_step. apply beta_lam_A. exact HA.
  - apply brt_trans with (t_lam s A' M); auto.
Qed.

Lemma brt_lam_M : forall s A M M', M ->>b M' -> t_lam s A M ->>b t_lam s A M'.
Proof.
  intros s A M M' H.
  induction H as [M | M M' HM | M M' M'' H1 IH1 H2 IH2].
  - apply brt_refl.
  - apply brt_step. apply beta_lam_M. exact HM.
  - apply brt_trans with (t_lam s A M'); auto.
Qed.

Lemma brt_lam_congr : forall s A A' M M',
  A ->>b A' -> M ->>b M' -> t_lam s A M ->>b t_lam s A' M'.
Proof.
  intros s A A' M M' HA HM.
  apply brt_trans with (t_lam s A' M).
  - apply brt_lam_A. exact HA.
  - apply brt_lam_M. exact HM.
Qed.

Lemma brt_app_l : forall M M' N, M ->>b M' -> t_app M N ->>b t_app M' N.
Proof.
  intros M M' N H.
  induction H as [M | M M' HM | M M' M'' H1 IH1 H2 IH2].
  - apply brt_refl.
  - apply brt_step. apply beta_app_l. exact HM.
  - apply brt_trans with (t_app M' N); auto.
Qed.

Lemma brt_app_r : forall M N N', N ->>b N' -> t_app M N ->>b t_app M N'.
Proof.
  intros M N N' H.
  induction H as [N | N N' HN | N N' N'' H1 IH1 H2 IH2].
  - apply brt_refl.
  - apply brt_step. apply beta_app_r. exact HN.
  - apply brt_trans with (t_app M N'); auto.
Qed.

Lemma brt_app_congr : forall M M' N N',
  M ->>b M' -> N ->>b N' -> t_app M N ->>b t_app M' N'.
Proof.
  intros M M' N N' HM HN.
  apply brt_trans with (t_app M' N).
  - apply brt_app_l. exact HM.
  - apply brt_app_r. exact HN.
Qed.

Lemma rho_pi_tel_dom_congr : forall C C' D i k,
  (forall m, i <= m <= i + k -> rho m C ->>b rho m C') ->
  rho_pi_tel rho C D i k ->>b rho_pi_tel rho C' D i k.
Proof.
  induction k as [| k' IHk]; intros Hall; simpl.
  - apply brt_pi_A. apply Hall. lia.
  - apply brt_pi_congr.
    + apply Hall. lia.
    + apply IHk. intros m Hm. apply Hall. lia.
Qed.

Lemma rho_pi_tel_body_congr : forall A B B' i k,
  rho i B ->>b rho i B' ->
  rho_pi_tel rho A B i k ->>b rho_pi_tel rho A B' i k.
Proof.
  induction k as [| k' IHk]; intros Hb; simpl.
  - apply brt_pi_B. exact Hb.
  - apply brt_pi_B. apply IHk. exact Hb.
Qed.

Lemma rho_lam_tel_dom_congr : forall C C' M' i k,
  (forall m, i + 1 <= m <= i + 1 + k -> rho m C ->>b rho m C') ->
  rho_lam_tel rho C M' i k ->>b rho_lam_tel rho C' M' i k.
Proof.
  induction k as [| k' IHk]; intros Hall; simpl.
  - apply brt_lam_A. apply Hall. lia.
  - apply brt_lam_congr.
    + apply Hall. lia.
    + apply IHk. intros m Hm. apply Hall. lia.
Qed.

Lemma rho_lam_tel_body_congr : forall A M' M'' i k,
  rho i M' ->>b rho i M'' ->
  rho_lam_tel rho A M' i k ->>b rho_lam_tel rho A M'' i k.
Proof.
  induction k as [| k' IHk]; intros Hb; simpl.
  - apply brt_lam_M. exact Hb.
  - apply brt_lam_M. apply IHk. exact Hb.
Qed.

Lemma rho_app_tel_func_congr : forall P P' Q i k,
  rho i P ->>b rho i P' ->
  rho_app_tel rho P Q i k ->>b rho_app_tel rho P' Q i k.
Proof.
  induction k as [| k' IHk]; intros Hp; simpl.
  - apply brt_app_l. exact Hp.
  - apply brt_app_l. apply IHk. exact Hp.
Qed.

Lemma rho_app_tel_arg_congr : forall P Q Q' i k,
  (forall m, i <= m <= i + k -> rho m Q ->>b rho m Q') ->
  rho_app_tel rho P Q i k ->>b rho_app_tel rho P Q' i k.
Proof.
  induction k as [| k' IHk]; intros Hall; simpl.
  - apply brt_app_r. apply Hall. lia.
  - apply brt_app_congr.
    + apply IHk. intros m Hm. apply Hall. lia.
    + apply Hall. lia.
Qed.

Axiom rho_commutes_beta_base : forall i, 0 <= i <= n ->
  forall s A M Q, deg M >= i + 1 ->
  rho i (t_app (t_lam s A M) Q) ->>b rho i (M ^^ Q).

Lemma rho_commutes_beta_aux :
  forall i, 0 <= i <= n ->
  forall M, deg M >= i + 1 ->
  forall N, M ->b N ->
  rho i M ->>b rho i N.
Proof.
  intros i.
  induction i as [i IHouter] using
    (well_founded_induction (Wf_nat.well_founded_ltof nat (fun i => n - i))).
  intros Hi M.
  induction M as [s | s_m m | y | P IHP Q IHQ | s A IHA M' IHM' | s A IHA B IHB];
    intros Hdeg N Hstep.

  - (* t_sort *) inversion Hstep.
  - (* t_bvar *) inversion Hstep.
  - (* t_fvar *) inversion Hstep.

  - (* t_app P Q *)
    simpl in Hdeg.
    inversion Hstep; subst; clear Hstep.

    + (* beta_base *)
      apply rho_commutes_beta_base; [exact Hi | ].
      simpl in Hdeg. exact Hdeg.

    + (* beta_app_l *)
      match goal with
      | Hs : P ->b ?P' |- _ =>
        assert (HdegP : deg P >= i + 1) by exact Hdeg;
        destruct (le_lt_dec (i + 1) (deg Q)) as [E | E];
        [ rewrite (rho_app_named i P Q E); rewrite (rho_app_named i P' Q E);
          apply rho_app_tel_func_congr;
          apply IHP; auto
        | assert (Hrho1 : rho i (t_app P Q) = rho i P) by (simpl; destruct (le_lt_dec (i+1) (deg Q)); [lia | reflexivity]);
          assert (Hrho2 : rho i (t_app P' Q) = rho i P') by (simpl; destruct (le_lt_dec (i+1) (deg Q)); [lia | reflexivity]);
          rewrite Hrho1, Hrho2;
          apply IHP; auto ]
      end.

    + (* beta_app_r *)
      match goal with
      | Hs : Q ->b ?Q' |- _ =>
        assert (HdegQeq : deg Q = deg Q') by (apply deg_beta; apply brt_step; exact Hs);
        destruct (le_lt_dec (i + 1) (deg Q)) as [E | E];
        [ assert (E' : i + 1 <= deg Q') by lia;
          rewrite (rho_app_named i P Q E); rewrite (rho_app_named i P Q' E');
          assert (Hk : deg Q - 1 - i = deg Q' - 1 - i) by lia;
          rewrite Hk;
          apply rho_app_tel_arg_congr;
          intros mtier Hmtier;
          assert (HQle : deg Q <= n + 1) by (apply deg_le_top);
          assert (HdegQm : deg Q >= mtier + 1) by lia;
          destruct (Nat.eq_dec mtier i) as [Heqm | Hneqm];
          [ subst mtier; apply IHQ; [unfold deg in *; lia | exact Hs]
          | apply IHouter; [unfold ltof; lia | lia | unfold deg in *; lia | exact Hs] ]
        | assert (E' : ~ i + 1 <= deg Q') by lia;
          assert (Hrho1 : rho i (t_app P Q) = rho i P) by (simpl; destruct (le_lt_dec (i+1) (deg Q)); [lia | reflexivity]);
          assert (Hrho2 : rho i (t_app P Q') = rho i P) by (simpl; destruct (le_lt_dec (i+1) (deg Q')); [lia | reflexivity]);
          rewrite Hrho1, Hrho2; apply brt_refl ]
      end.

  - (* t_lam s A M' *)
    inversion Hstep; subst; clear Hstep.

    + (* beta_lam_A *)
      match goal with
      | Hs : A ->b ?A1' |- _ =>
        assert (HdegAA' : deg A = deg A1') by (apply deg_beta; apply brt_step; exact Hs);
        destruct (le_lt_dec (i + 2) (deg A)) as [E | E];
        [ assert (E' : i + 2 <= deg A1') by lia;
          rewrite (rho_lam_named i s A M' E); rewrite (rho_lam_named i s A1' M' E');
          assert (Hk : deg A - 1 - (i + 1) = deg A1' - 1 - (i + 1)) by lia;
          rewrite Hk;
          apply rho_lam_tel_dom_congr;
          intros mtier Hmtier;
          assert (HAle : deg A <= n + 1) by (apply deg_le_top);
          assert (HdegAm : deg A >= mtier + 1) by lia;
          apply IHouter; [unfold ltof; lia | lia | unfold deg in *; lia | exact Hs]
        | assert (E' : ~ i + 2 <= deg A1') by lia;
          assert (Hrho1 : rho i (t_lam s A M') = rho i M') by (simpl; destruct (le_lt_dec (i+2) (deg A)); [lia | reflexivity]);
          assert (Hrho2 : rho i (t_lam s A1' M') = rho i M') by (simpl; destruct (le_lt_dec (i+2) (deg A1')); [lia | reflexivity]);
          rewrite Hrho1, Hrho2; apply brt_refl ]
      end.

    + (* beta_lam_M *)
      match goal with
      | Hs : M' ->b ?M1' |- _ =>
        assert (HdegM' : deg M' >= i + 1) by exact Hdeg;
        destruct (le_lt_dec (i + 2) (deg A)) as [E | E];
        [ rewrite (rho_lam_named i s A M' E); rewrite (rho_lam_named i s A M1' E);
          apply rho_lam_tel_body_congr;
          apply IHM'; auto
        | assert (Hrho1 : rho i (t_lam s A M') = rho i M') by (simpl; destruct (le_lt_dec (i+2) (deg A)); [lia | reflexivity]);
          assert (Hrho2 : rho i (t_lam s A M1') = rho i M1') by (simpl; destruct (le_lt_dec (i+2) (deg A)); [lia | reflexivity]);
          rewrite Hrho1, Hrho2;
          apply IHM'; auto ]
      end.

  - (* t_pi s A B *)
    inversion Hstep; subst; clear Hstep.

    + (* beta_pi_A *)
      match goal with
      | Hs : A ->b ?A1' |- _ =>
        assert (HdegAA' : deg A = deg A1') by (apply deg_beta; apply brt_step; exact Hs);
        destruct (le_lt_dec (i + 1) (deg A)) as [E | E];
        [ assert (E' : i + 1 <= deg A1') by lia;
          rewrite (rho_pi_named i s A B E); rewrite (rho_pi_named i s A1' B E');
          assert (Hk : deg A - 1 - i = deg A1' - 1 - i) by lia;
          rewrite Hk;
          apply rho_pi_tel_dom_congr;
          intros mtier Hmtier;
          assert (HAle : deg A <= n + 1) by (apply deg_le_top);
          assert (HdegAm : deg A >= mtier + 1) by lia;
          destruct (Nat.eq_dec mtier i) as [Heqm | Hneqm];
          [ subst mtier; apply IHA; [unfold deg in *; lia | exact Hs]
          | apply IHouter; [unfold ltof; lia | lia | unfold deg in *; lia | exact Hs] ]
        | assert (E' : ~ i + 1 <= deg A1') by lia;
          assert (Hrho1 : rho i (t_pi s A B) = rho i B) by (simpl; destruct (le_lt_dec (i+1) (deg A)); [lia | reflexivity]);
          assert (Hrho2 : rho i (t_pi s A1' B) = rho i B) by (simpl; destruct (le_lt_dec (i+1) (deg A1')); [lia | reflexivity]);
          rewrite Hrho1, Hrho2; apply brt_refl ]
      end.

    + (* beta_pi_B *)
      match goal with
      | Hs : B ->b ?B1' |- _ =>
        assert (HdegB : deg B >= i + 1) by exact Hdeg;
        destruct (le_lt_dec (i + 1) (deg A)) as [E | E];
        [ rewrite (rho_pi_named i s A B E); rewrite (rho_pi_named i s A B1' E);
          apply rho_pi_tel_body_congr;
          apply IHB; auto
        | assert (Hrho1 : rho i (t_pi s A B) = rho i B) by (simpl; destruct (le_lt_dec (i+1) (deg A)); [lia | reflexivity]);
          assert (Hrho2 : rho i (t_pi s A B1') = rho i B1') by (simpl; destruct (le_lt_dec (i+1) (deg A)); [lia | reflexivity]);
          rewrite Hrho1, Hrho2;
          apply IHB; auto ]
      end.
Qed.

Lemma rho_commutes_beta :
  forall i, 0 <= i <= n ->
  forall M, deg M >= i + 1 ->
  forall N, M ->>b N ->
  rho i M ->>b rho i N.
Proof.
  intros i Hi M Hdeg N Hbeta.
  induction Hbeta as [M | M N Hstep | M N P Hstep1 IH1 Hstep2 IH2].
  - apply brt_refl.
  - apply (rho_commutes_beta_aux i Hi M Hdeg N Hstep).
  - apply brt_trans with (rho i N); auto.
    apply IH2; auto.
    rewrite <- (deg_beta M N Hstep1); auto.
Qed.

(* ================================================================= *)
(* rho commutes with typing *)

Axiom n_at_least_two : n >= 2.

Axiom typing_star_weakening_incl : forall Γ Δ M A,
  Γ ⊆ Δ -> Γ ⊢* M ∈ A -> Δ ⊢* M ∈ A.

Lemma subcontext_app_same : forall Γ1 Γ2 Δ,
  Γ1 ⊆ Δ -> Γ2 ⊆ Δ -> Γ1 ++ Γ2 ⊆ Δ.
Proof.
  intros Γ1 Γ2 Δ H1 H2 x T Hin.
  apply in_app_or in Hin. destruct Hin; [apply H1 | apply H2]; auto.
Qed.

Lemma rho_ctx_tel_idx : forall y s T k v A,
  In (v, A) (rho_ctx_tel y s T k) -> exists s', v = retag y s'.
Proof.
  intros y s T k.
  induction k as [| k' IHk]; intros v A Hin; simpl in Hin.
  - destruct Hin as [Heq | []]. injection Heq as Hv HA.
    exists (sort_of (index_of s)). symmetry. exact Hv.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + eapply IHk; eauto.
    + destruct Hin as [Heq | []]. injection Heq as Hv HA.
      exists (sort_of (index_of s - S k')). symmetry. exact Hv.
Qed.

Lemma rho_ctx_tel_last : forall y s T k,
  In (retag y (sort_of (index_of s - k)),
      (sort_of (index_of s - k), rho (index_of s - k - 1) T))
     (rho_ctx_tel y s T k).
Proof.
  intros y s T k.
  destruct k as [| k'].
  - simpl. left. replace (index_of s - 0) with (index_of s) by lia.
    replace (index_of s - 0 - 1) with (index_of s - 1) by lia. reflexivity.
  - simpl. apply in_or_app. right. left. reflexivity.
Qed.

Lemma rho_ctx_incl_old : forall Γ0 i x s T,
  rho_ctx i Γ0 ⊆ rho_ctx i (Γ0 ++ [(x, (s, T))]).
Proof.
  induction Γ0 as [| [y [sy Ty]] Γ0' IH]; intros i x s T p q Hpq.
  - simpl in Hpq. destruct Hpq as [Hpq | []]. inversion Hpq; subst.
    simpl. apply in_or_app. right. left. reflexivity.
  - simpl in Hpq |- *. apply in_app_or in Hpq. apply in_or_app.
    destruct Hpq as [Hpq | Hpq].
    + left. exact Hpq.
    + right. apply (IH i x s T). exact Hpq.
Qed.

Lemma rho_ctx_incl_new : forall Γ0 i x s T,
  rho_ctx_tel x s T (index_of s - i - 1) ⊆ rho_ctx i (Γ0 ++ [(x, (s, T))]).
Proof.
  induction Γ0 as [| [y [sy Ty]] Γ0' IH]; intros i x s T p q Hpq.
  - simpl. apply in_or_app. left. exact Hpq.
  - simpl. apply in_or_app. right. apply (IH i x s T). exact Hpq.
Qed.

Lemma rho_ctx_fresh : forall Γ0 i x s,
  x <> zero_var -> is_fresh x Γ0 -> is_fresh (retag x s) (rho_ctx i Γ0).
Proof.
  induction Γ0 as [| [y [sy Ty]] Γ0' IH]; intros i x s Hxnz Hfresh.
  - simpl. unfold is_fresh, dom. simpl. intro Hin.
    destruct Hin as [Heq | []]. apply (zero_var_retag_ne x s). symmetry. exact Heq.
  - assert (Hfresh' : is_fresh x Γ0') by (intros Hin; apply Hfresh; simpl; right; exact Hin).
    assert (Hxy : x <> y)
      by (intro Heq; apply Hfresh; simpl; left; symmetry; exact Heq).
    unfold is_fresh, dom in *. simpl.
    intro Hin. apply in_map_iff in Hin. destruct Hin as [[v A] [Hveq Hin']]. simpl in Hveq. subst v.
    apply in_app_or in Hin'. destruct Hin' as [Hin' | Hin'].
    + pose proof (rho_ctx_tel_idx y sy Ty _ _ _ Hin') as [s' Hs'].
      exact (retag_neq_of_atom_neq x s y s' Hxy Hs').
    + apply (IH i x s Hxnz Hfresh').
      apply in_map_iff. exists (retag x s, A). split; [reflexivity | exact Hin'].
Qed.

Lemma subcontext_trans : forall Γ1 Γ2 Γ3, Γ1 ⊆ Γ2 -> Γ2 ⊆ Γ3 -> Γ1 ⊆ Γ3.
Proof. intros Γ1 Γ2 Γ3 H12 H23 x T Hin. apply H23, H12, Hin. Qed.

Lemma rho_ctx_tel_mono : forall y s T k1 k2, k1 <= k2 ->
  rho_ctx_tel y s T k1 ⊆ rho_ctx_tel y s T k2.
Proof.
  intros y s T k1 k2 Hle.
  induction k2 as [| k2' IH].
  - assert (k1 = 0) by lia. subst. intros p q Hpq. exact Hpq.
  - destruct (Nat.eq_dec k1 (S k2')) as [Heq | Hneq].
    + subst. intros p q Hpq. exact Hpq.
    + assert (Hle' : k1 <= k2') by lia.
      intros p q Hpq. simpl. apply in_or_app. left. apply (IH Hle'). exact Hpq.
Qed.

Lemma app_subset_app : forall (Γ1 Γ2 Δ1 Δ2 : context),
  Γ1 ⊆ Δ1 -> Γ2 ⊆ Δ2 -> Γ1 ++ Γ2 ⊆ Δ1 ++ Δ2.
Proof.
  intros Γ1 Γ2 Δ1 Δ2 H1 H2 p q Hpq.
  apply in_app_or in Hpq. apply in_or_app.
  destruct Hpq as [Hpq | Hpq]; [left; apply H1 | right; apply H2]; exact Hpq.
Qed.

Lemma rho_ctx_mono : forall Γ i i', i <= i' -> rho_ctx i' Γ ⊆ rho_ctx i Γ.
Proof.
  induction Γ as [| [y [sy Ty]] Γ' IH]; intros i i' Hle.
  - simpl. intros p q Hpq. exact Hpq.
  - simpl. apply app_subset_app.
    + apply rho_ctx_tel_mono. lia.
    + apply (IH i i' Hle).
Qed.

Axiom rho_pi_domain_erased_below :
  forall Γ0 x A0 B0 s1 T i,
    is_fresh x Γ0 ->
    Γ0 ⊢ A0 ∈ t_sort s1 ->
    index_of s1 < i + 1 ->
    rho_ctx (i + 1) (Γ0 ++ [(x, (s1, A0))]) ⊢* rho i (open_var B0 s1 x) ∈ T ->
    rho_ctx (i + 1) Γ0 ⊢* rho i B0 ∈ T.

Axiom rho_pi_tower :
  forall Γ0 A0 B0 s1 i L,
    Γ0 ⊢ A0 ∈ t_sort s1 ->
    index_of s1 >= i + 1 ->
    (forall x, ~ In x L ->
       rho_ctx (i + 1) (Γ0 ++ [(x, (s1, A0))]) ⊢* rho i (open_var B0 s1 x) ∈ t_sort (sort_of (i + 1))) ->
    rho_ctx (i + 1) Γ0 ⊢* rho_pi_tel rho A0 B0 i (deg A0 - 1 - i) ∈ t_sort (sort_of (i + 1)).

Axiom rho_lam_domain_erased_below :
  forall Γ0 x A0 M0 B0 s1 i,
    is_fresh x Γ0 ->
    Γ0 ⊢ A0 ∈ t_sort s1 ->
    index_of s1 < i + 2 ->
    rho_ctx (i + 1) (Γ0 ++ [(x, (s1, A0))]) ⊢* rho i (open_var M0 s1 x) ∈ rho (i + 1) (open_var B0 s1 x) ->
    rho_ctx (i + 1) Γ0 ⊢* rho i M0 ∈ rho (i + 1) B0.

Axiom rho_lam_tower :
  forall Γ0 A0 M0 B0 s1 i L,
    Γ0 ⊢ A0 ∈ t_sort s1 ->
    index_of s1 >= i + 2 ->
    (forall x, ~ In x L ->
       rho_ctx (i + 1) (Γ0 ++ [(x, (s1, A0))]) ⊢* rho i (open_var M0 s1 x) ∈ rho (i + 1) (open_var B0 s1 x)) ->
    rho_ctx (i + 1) Γ0 ⊢* rho_lam_tel rho A0 M0 i (deg A0 - 1 - (i + 1))
                        ∈ rho_pi_tel rho A0 B0 (i + 1) (deg A0 - 1 - (i + 1)).

Axiom rho_app_tower :
  forall Γ0 M0 N0 A0 B0 s1a i,
    Γ0 ⊢ M0 ∈ t_pi s1a A0 B0 ->
    Γ0 ⊢ N0 ∈ A0 ->
    deg N0 >= i + 1 ->
    rho_ctx (i + 1) Γ0 ⊢* rho i M0 ∈ rho (i + 1) (t_pi s1a A0 B0) ->
    rho_ctx (i + 1) Γ0 ⊢* rho i (t_app M0 N0) ∈ rho (i + 1) (B0 ^^ N0).

Axiom rho_erased_subst_below : forall B N i,
  deg N < i + 1 -> rho (i + 1) (B ^^ N) = rho (i + 1) B.

Lemma deg_beq : forall M N, M =b N -> deg M = deg N.
Proof.
  intros M N Heq.
  induction Heq as [M | M N Hstep | M N Heq IH | M N P Heq1 IH1 Heq2 IH2].
  - reflexivity.
  - apply deg_beta. apply brt_step. exact Hstep.
  - symmetry. exact IH.
  - rewrite IH1. exact IH2.
Qed.

Lemma rho_commutes_beta_eq : forall i, 0 <= i <= n ->
  forall M N, deg M >= i + 1 -> M =b N -> rho i M =b rho i N.
Proof.
  intros i Hi M N Hdeg Heq.
  revert Hdeg.
  induction Heq as [M | M N Hstep | M N Heq IH | M N P Heq1 IH1 Heq2 IH2]; intros Hdeg.
  - apply beq_refl.
  - apply beq_from_rtrans. apply (rho_commutes_beta i Hi M Hdeg N (brt_step M N Hstep)).
  - assert (HdegM : deg M >= i + 1) by (rewrite (deg_beq M N Heq); exact Hdeg).
    apply beq_sym. apply (IH HdegM).
  - assert (HdegN : deg N >= i + 1) by (rewrite <- (deg_beq M N Heq1); exact Hdeg).
    apply beq_trans with (rho i N).
    + apply (IH1 Hdeg).
    + apply (IH2 HdegN).
Qed.

Lemma rho_commutes_typing :
  forall i, 0 <= i <= n ->
  forall Γ M N, Γ ⊢ M ∈ N ->
  deg M >= i + 1 ->
  rho_ctx (i + 1) Γ ⊢* (rho i M) ∈ (rho (i + 1) N).
Proof.
  intros i.
  induction i as [i IHouter] using
    (well_founded_induction (Wf_nat.well_founded_ltof nat (fun i => n - i))).
  intros Hi Γ M N Htype.
  induction Htype as
    [ s s' HA
    | Γ0 x A0 s0 Hfresh HA IHA
    | Γ0 x B0 M0 A0 s0 Hfresh HM IHM HB IHB
    | Γ0 A0 B0 s1 s2 s3 L HA IHA HTagB HB IHB HR
    | Γ0 A0 M0 B0 s1 s3 L HA IHA HTagM HM IHM HPi IHPi
    | Γ0 M0 N0 A0 B0 s1a HM IHM HN IHN
    | Γ0 M0 A0 B0 s HM IHM Heq HB IHB ];
    intros Hdeg.

  - (* typing_axiom *)
    simpl in Hdeg.
    apply A_spec in HA as [Hjn Hjs'].
    pose proof n_at_least_two as Hn2.
    assert (HzeroTyped : [] ⊢* t_sort (sort_of 1) ∈ t_sort (sort_of 2)).
    { apply typing_star_axiom. apply A_spec.
      rewrite (sort_of_correct 1 ltac:(lia) ltac:(lia)).
      rewrite (sort_of_correct 2 ltac:(lia) ltac:(lia)).
      lia. }
    destruct i as [| i'].
    + (* i = 0 *)
      simpl.
      apply typing_star_var with (Γ := []).
      * unfold is_fresh, dom. simpl. auto.
      * exact HzeroTyped.
    + (* i = S i' *)
      assert (HiSn : S i' < n) by lia.
      replace (S i' + 1) with (S (S i')) by lia.
      simpl.
      apply typing_star_weak with (Γ := []) (x := zero_var) (B := t_sort (sort_of 1)).
      * unfold is_fresh, dom. simpl. auto.
      * apply typing_star_axiom. apply A_spec.
        rewrite (sort_of_correct (S i') ltac:(lia) ltac:(lia)).
        rewrite (sort_of_correct (S (S i')) ltac:(lia) ltac:(lia)).
        lia.
      * exact HzeroTyped.

  - (* typing_var *)
    simpl in Hdeg.
    pose proof (index_range s0) as [Hxlo Hxhi].
    assert (HdegA0 : deg A0 = index_of s0).
    { pose proof (deg_typing_succ Γ0 A0 (t_sort s0) HA) as Hds.
      unfold deg in *. simpl in Hds. lia. }
    assert (Hj2 : index_of s0 >= i + 2) by lia.
    assert (Hlt : ltof nat (fun k => n - k) (i + 1) i) by (unfold ltof; lia).
    assert (Hij : 0 <= i + 1 <= n) by (pose proof (index_range s0); lia).
    assert (HdegA0' : deg A0 >= (i + 1) + 1) by (lia).
    pose proof (IHouter (i + 1) Hlt Hij Γ0 A0 (t_sort s0) HA HdegA0') as HIH.
    replace (i + 1 + 1) with (S (S i)) in HIH by lia.
    simpl in HIH.
    replace (S (S i)) with (i + 2) in HIH by lia.
    pose (x' := retag x (sort_of (i + 2))).
    assert (Hxnz : x <> zero_var)
      by (apply (typing_avoids_zero_var (Γ0 ++ [(x, (s0, A0))]) (t_fvar s0 x) A0
                   (typing_var Γ0 x A0 s0 Hfresh HA) x s0 A0);
          apply in_or_app; right; left; reflexivity).
    assert (Hfreshx' : is_fresh x' (rho_ctx (i + 2) Γ0))
      by (apply rho_ctx_fresh; [exact Hxnz | exact Hfresh]).
    assert (Hstep : rho_ctx (i + 2) Γ0 ++ [(x', (sort_of (i + 2), rho (i + 1) A0))]
                    ⊢* t_fvar (sort_of (i + 2)) x' ∈ rho (i + 1) A0)
      by (apply typing_star_var; [exact Hfreshx' | exact HIH]).
    assert (Hmem : In (x', (sort_of (i + 2), rho (i + 1) A0))
                     (rho_ctx_tel x s0 A0 (index_of s0 - (i + 1) - 1))).
    { replace (index_of s0 - (i + 1) - 1)
        with (index_of s0 - i - 2) by lia.
      pose proof (rho_ctx_tel_last x s0 A0 (index_of s0 - i - 2)) as Htel.
      replace (index_of s0 - (index_of s0 - i - 2) - 1)
        with (i + 1) in Htel by lia.
      replace (index_of s0 - (index_of s0 - i - 2))
        with (i + 2) in Htel by lia.
      unfold x'. exact Htel.
    }
    assert (Hincl : rho_ctx (i + 2) Γ0 ++ [(x', (sort_of (i + 2), rho (i + 1) A0))]
                    ⊆ rho_ctx (i + 1) (Γ0 ++ [(x, (s0, A0))])).
    { apply subcontext_app_same.
      - apply (subcontext_trans _ (rho_ctx (i + 1) Γ0)).
        + apply rho_ctx_mono. lia.
        + apply rho_ctx_incl_old.
      - intros p q Hpq. destruct Hpq as [Heq | []]. inversion Heq; subst.
        apply (rho_ctx_incl_new Γ0 (i + 1) x s0 A0). exact Hmem.
    }
    simpl. unfold x' in Hstep, Hincl.
    apply (typing_star_weakening_incl _ _ _ _ Hincl Hstep).

  - (* typing_weak *)
    exact (typing_star_weakening_incl _ _ _ _ (rho_ctx_incl_old Γ0 (i + 1) x s0 B0)
             (IHM Hdeg)).

  - (* typing_pi *)
    simpl in Hdeg.
    assert (Hs32 : s3 = s2) by (symmetry; apply (R_shape s1 s2 s3 HR)).
    subst s3.
    assert (HdegA0 : deg A0 = index_of s1) by (apply (deg_sort_typed Γ0 A0 s1 HA)).
    set (x0 := fresh (dom Γ0 ++ L)).
    assert (Hx0dom : is_fresh x0 Γ0).
    { intro Hc. apply (fresh_notin (dom Γ0 ++ L)).
      apply in_or_app. left. exact Hc. }
    assert (Hx0L : ~ In x0 L).
    { intro Hc. apply (fresh_notin (dom Γ0 ++ L)).
      apply in_or_app. right. exact Hc. }
    assert (HBx0 : Γ0 ++ [(x0, (s1, A0))] ⊢ open_var B0 s1 x0 ∈ t_sort s2) by (apply HB; exact Hx0L).
    assert (Hdegopen : deg (open_var B0 s1 x0) >= i + 1)
      by (rewrite <- (deg_open B0 x0 s1 HTagB); exact Hdeg).
    assert (Hcast : rho (i + 1) (t_sort s2) = t_sort (sort_of (i + 1))).
    { replace (i + 1) with (S i) by lia. reflexivity. }
    destruct (le_lt_dec (i + 1) (deg A0)) as [HJge | HJlt].

    + (* j >= i+1 *)
      rewrite (rho_pi_named i s1 A0 B0 HJge).
      rewrite Hcast.
      apply (rho_pi_tower Γ0 A0 B0 s1 i L HA).
      * lia.
      * intros x Hx.
        assert (HBx : Γ0 ++ [(x, (s1, A0))] ⊢ open_var B0 s1 x ∈ t_sort s2) by (apply HB; exact Hx).
        assert (Hd : deg (open_var B0 s1 x) >= i + 1)
          by (rewrite <- (deg_open B0 x s1 HTagB); exact Hdeg).
        pose proof (IHB x Hx Hd) as HIH.
        rewrite Hcast in HIH. exact HIH.

    + (* j < i+1 *)
      assert (Hcollapse : rho i (t_pi s1 A0 B0) = rho i B0)
        by (simpl; destruct (le_lt_dec (i + 1) (deg A0)); [lia | reflexivity]).
      rewrite Hcollapse, Hcast.
      assert (Hjlt' : index_of s1 < i + 1) by lia.
      apply (rho_pi_domain_erased_below Γ0 x0 A0 B0 s1 (t_sort (sort_of (i + 1))) i
               Hx0dom HA Hjlt').
      pose proof (IHB x0 Hx0L Hdegopen) as HIH.
      rewrite Hcast in HIH. exact HIH.

  - (* typing_lam *)
    simpl in Hdeg.
    assert (HdegA0 : deg A0 = index_of s1) by (apply (deg_sort_typed Γ0 A0 s1 HA)).
    set (x0 := fresh (dom Γ0 ++ L)).
    assert (Hx0dom : is_fresh x0 Γ0).
    { intro Hc. apply (fresh_notin (dom Γ0 ++ L)).
      apply in_or_app. left. exact Hc. }
    assert (Hx0L : ~ In x0 L).
    { intro Hc. apply (fresh_notin (dom Γ0 ++ L)).
      apply in_or_app. right. exact Hc. }
    assert (HMx0 : Γ0 ++ [(x0, (s1, A0))] ⊢ open_var M0 s1 x0 ∈ open_var B0 s1 x0) by (apply HM; exact Hx0L).
    assert (Hdegopen : deg (open_var M0 s1 x0) >= i + 1)
      by (rewrite <- (deg_open M0 x0 s1 HTagM); exact Hdeg).
    destruct (le_lt_dec (i + 2) (deg A0)) as [HJge | HJlt].

    + (* deg C >= i+2 *)
      assert (Hlam : rho i (t_lam s1 A0 M0) = rho_lam_tel rho A0 M0 i (deg A0 - 1 - (i + 1)))
        by (apply (rho_lam_named i s1 A0 M0 HJge)).
      assert (HJge' : i + 1 + 1 <= deg A0) by lia.
      assert (Hpi : rho (i + 1) (t_pi s1 A0 B0) = rho_pi_tel rho A0 B0 (i + 1) (deg A0 - 1 - (i + 1)))
        by (apply (rho_pi_named (i + 1) s1 A0 B0 HJge')).
      rewrite Hlam, Hpi.
      apply (rho_lam_tower Γ0 A0 M0 B0 s1 i L HA).
      * lia.
      * intros x Hx.
        assert (HMx : Γ0 ++ [(x, (s1, A0))] ⊢ open_var M0 s1 x ∈ open_var B0 s1 x) by (apply HM; exact Hx).
        assert (Hd : deg (open_var M0 s1 x) >= i + 1)
          by (rewrite <- (deg_open M0 x s1 HTagM); exact Hdeg).
        apply (IHM x Hx Hd).

    + (* deg C < i+2 *)
      assert (Hcollapse1 : rho i (t_lam s1 A0 M0) = rho i M0)
        by (simpl; destruct (le_lt_dec (i + 2) (deg A0)); [lia | reflexivity]).
      assert (Hcollapse2 : rho (i + 1) (t_pi s1 A0 B0) = rho (i + 1) B0)
        by (simpl; destruct (le_lt_dec (i + 1 + 1) (deg A0)); [lia | reflexivity]).
      rewrite Hcollapse1, Hcollapse2.
      assert (HJlt' : index_of s1 < i + 2) by lia.
      apply (rho_lam_domain_erased_below Γ0 x0 A0 M0 B0 s1 i Hx0dom HA HJlt').
      apply (IHM x0 Hx0L Hdegopen).

  - (* typing_app *)
    simpl in Hdeg.
    assert (HdegC : deg A0 = deg N0 + 1)
      by (pose proof (deg_typing_succ Γ0 N0 A0 HN) as Hh; lia).
    destruct (le_lt_dec (i + 1) (deg N0)) as [HNge | HNlt].

    + (* deg N >= i+1 *)
      apply (rho_app_tower Γ0 M0 N0 A0 B0 s1a i HM HN HNge).
      exact (IHM Hdeg).

    + (* deg N < i+1 *)
      assert (Hcollapse_app : rho i (t_app M0 N0) = rho i M0)
        by (simpl; destruct (le_lt_dec (i + 1) (deg N0)); [lia | reflexivity]).
      rewrite Hcollapse_app.
      assert (Hcol2 : rho (i + 1) (t_pi s1a A0 B0) = rho (i + 1) B0)
        by (simpl; destruct (le_lt_dec (i + 1 + 1) (deg A0)); [lia | reflexivity]).
      assert (Htgt : rho (i + 1) (B0 ^^ N0) = rho (i + 1) (t_pi s1a A0 B0)).
      { rewrite Hcol2. apply (rho_erased_subst_below B0 N0 i HNlt). }
      rewrite Htgt.
      exact (IHM Hdeg).

  - (* typing_conv *)
    simpl in Hdeg.
    destruct (typing_lc _ _ _ HM) as [HlcM _].
    assert (HdegM0 : deg M0 >= i + 1) by (lia).
    assert (HdegA0 : deg A0 = deg M0 + 1)
      by (pose proof (deg_typing_succ Γ0 M0 A0 HM); lia).
    assert (HdegAB : deg A0 = deg B0)
      by (apply (deg_conv_invariant Γ0 M0 A0 B0 s HM Heq HB)).
    assert (HdegBs : deg B0 = index_of s) by (apply (deg_sort_typed Γ0 B0 s HB)).
    pose proof (index_range s) as [Hslo Hshi].
    assert (HsGe : index_of s >= i + 2) by lia.
    assert (Hlt : ltof nat (fun k => n - k) (i + 1) i) by (unfold ltof; lia).
    assert (Hij : 0 <= i + 1 <= n) by lia.
    assert (HdegA0' : deg A0 >= (i + 1) + 1) by lia.
    assert (HeqRho : rho (i + 1) A0 =b rho (i + 1) B0)
      by (apply (rho_commutes_beta_eq (i + 1) Hij A0 B0 HdegA0' Heq)).
    assert (HIH1 : rho_ctx (i + 1) Γ0 ⊢* rho i M0 ∈ rho (i + 1) A0)
      by (exact (IHM Hdeg)).
    assert (HdegB0' : deg B0 >= (i + 1) + 1) by (lia).
    pose proof (IHouter (i + 1) Hlt Hij Γ0 B0 (t_sort s) HB HdegB0') as HIH2.
    replace (i + 1 + 1) with (S (S i)) in HIH2 by lia.
    simpl in HIH2.
    replace (S (S i)) with (i + 2) in HIH2 by lia.
    assert (HIH2' : rho_ctx (i + 1) Γ0 ⊢* rho (i + 1) B0 ∈ t_sort (sort_of (i + 2))).
    { apply (typing_star_weakening_incl (rho_ctx (i + 2) Γ0) _ _ _
               (rho_ctx_mono Γ0 (i + 1) (i + 2) ltac:(lia)) HIH2). }
    apply (typing_star_conv (rho_ctx (i + 1) Γ0) (rho i M0) (rho (i + 1) A0)
             (rho (i + 1) B0) (sort_of (i + 2)) HIH1 HeqRho HIH2').
Qed.

(* ================================================================= *)
(* Term-Level Translation *)
(* γ : T → T 0 *)

Definition bullet_var : var := n + 2.
Definition prod_var : var := 2 * (n + 2).

Lemma bullet_var_retag_ne : forall x s, retag x s <> bullet_var.
Proof.
  intros x s. unfold bullet_var. replace (n + 2) with (1 * (n + 2)) by lia.
  apply (retag_neq_mult 1).
Qed.

Lemma prod_var_retag_ne : forall x s, retag x s <> prod_var.
Proof. intros x s. unfold prod_var. apply (retag_neq_mult 2). Qed.

Lemma prod_var_ne_bullet_var : prod_var <> bullet_var.
Proof. unfold prod_var, bullet_var. pose proof n_range. lia. Qed.

Lemma prod_var_ne_zero_var : prod_var <> zero_var.
Proof. unfold prod_var, zero_var. pose proof n_range. lia. Qed.

Lemma bullet_var_ne_zero_var : bullet_var <> zero_var.
Proof. unfold bullet_var, zero_var. pose proof n_range. lia. Qed.

Fixpoint gamma_pi_tel (A body : term) (k : nat) : term :=
  match k with
  | 0    => t_pi (sort_of 0) (rho 0 A) body
  | S k' => t_pi (sort_of (S k')) (rho (S k') A) (gamma_pi_tel A body k')
  end.

Fixpoint gamma_lam_tel (A body : term) (k : nat) : term :=
  match k with
  | 0    => t_lam (sort_of 0) (rho 0 A) body
  | S k' => t_lam (sort_of (S k')) (rho (S k') A) (gamma_lam_tel A body k')
  end.

Fixpoint gamma_app_tel (M' N : term) (k : nat) : term :=
  match k with
  | 0    => t_app M' (rho 0 N)
  | S k' => gamma_app_tel (t_app M' (rho (S k') N)) N k'
  end.

Fixpoint gamma (M : term) : term :=
  match M with
  | t_sort s   => t_fvar (sort_of 1) bullet_var
  | t_bvar s0 k => t_bvar s0 k
  | t_fvar s0 x => t_fvar (sort_of 1) (retag x (sort_of 1))
  | t_pi s A B =>
      t_app (t_app (t_app (t_fvar (sort_of 1) prod_var)
                      (gamma_pi_tel A (t_fvar (sort_of 2) zero_var) (deg A - 1)))
                    (gamma A))
            (gamma_lam_tel A (gamma B) (deg A - 1))
  | t_lam s A M' =>
      t_app (t_lam (sort_of 1) (t_fvar (sort_of 2) zero_var)
               (gamma_lam_tel A (gamma M') (deg A - 1)))
            (gamma A)
  | t_app M' N =>
      t_app (gamma_app_tel (gamma M') N (deg N - 1)) (gamma N)
  end.

(* ================================================================= *)
(** * gamma commutes with typing *)

(* prod : ΠA s1 . 0 → A → 0, requires the rule (s2,s1), which we assume appear in λS. *)
Axiom R_s2_s1 : R (sort_of 2) (sort_of 1) (sort_of 1).

Lemma sort_of_1_ne_2 : sort_of 1 <> sort_of 2.
Proof.
  pose proof n_at_least_two as Hn2.
  intro Heq.
  assert (H1 : index_of (sort_of 1) = 1) by (apply sort_of_correct; lia).
  assert (H2 : index_of (sort_of 2) = 2) by (apply sort_of_correct; lia).
  rewrite Heq in H1. lia.
Qed.

Lemma R_s1_s1_s1 : R (sort_of 1) (sort_of 1) (sort_of 1).
Proof.
  pose proof n_at_least_two as Hn2.
  pose proof (is_full _ _ _ R_s2_s1) as Hfw.
  unfold full_with in Hfw.
  apply Hfw.
  - rewrite (sort_of_correct 1 ltac:(lia) ltac:(lia)). lia.
  - rewrite (sort_of_correct 1 ltac:(lia) ltac:(lia)). lia.
  - rewrite (sort_of_correct 1 ltac:(lia) ltac:(lia)).
    rewrite (sort_of_correct 2 ltac:(lia) ltac:(lia)).
    lia.
Qed.

Definition T_prod : term :=
  t_pi (sort_of 2) (t_sort (sort_of 1))
    (t_pi (sort_of 1) (t_fvar (sort_of 2) zero_var)
       (t_pi (sort_of 1) (t_bvar (sort_of 2) 1) (t_fvar (sort_of 2) zero_var))).

Lemma subcontext_app_l : forall Γ Δ', Γ ⊆ Γ ++ Δ'.
Proof. intros Γ Δ' x T Hin. apply in_or_app. left. exact Hin. Qed.

Lemma subcontext_app_r : forall Γ Δ', Γ ⊆ Δ' ++ Γ.
Proof. intros Γ Δ' x T Hin. apply in_or_app. right. exact Hin. Qed.

Lemma zero_var_typed :
  [(zero_var, (sort_of 2, t_sort (sort_of 1)))] ⊢* t_fvar (sort_of 2) zero_var ∈ t_sort (sort_of 1).
Proof.
  pose proof n_at_least_two as Hn2.
  apply (typing_star_var [] zero_var (t_sort (sort_of 1)) (sort_of 2)).
  - unfold is_fresh, dom. simpl. auto.
  - apply typing_star_axiom. apply A_spec.
    rewrite (sort_of_correct 1 ltac:(lia) ltac:(lia)).
    rewrite (sort_of_correct 2 ltac:(lia) ltac:(lia)).
    lia.
Qed.

Lemma Tprod_typed :
  [(zero_var, (sort_of 2, t_sort (sort_of 1))); (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var))]
  ⊢* T_prod ∈ t_sort (sort_of 1).
Proof.
  pose proof n_at_least_two as Hn2.
  pose proof zero_var_typed as Hz1.
  assert (HtsortA : [(zero_var, (sort_of 2, t_sort (sort_of 1))); (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var))]
                     ⊢* t_sort (sort_of 1) ∈ t_sort (sort_of 2)).
  { apply (typing_star_weakening_incl []).
    - intros x T [].
    - apply typing_star_axiom. apply A_spec.
      rewrite (sort_of_correct 1 ltac:(lia) ltac:(lia)).
      rewrite (sort_of_correct 2 ltac:(lia) ltac:(lia)).
      lia. }
  apply (typing_star_pi
           [(zero_var, (sort_of 2, t_sort (sort_of 1))); (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var))]
           (t_sort (sort_of 1))
           (t_pi (sort_of 1) (t_fvar (sort_of 2) zero_var)
              (t_pi (sort_of 1) (t_bvar (sort_of 2) 1) (t_fvar (sort_of 2) zero_var)))
           (sort_of 2) (sort_of 1) (sort_of 1)
           (dom [(zero_var, (sort_of 2, t_sort (sort_of 1))); (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var))])).
  - exact HtsortA.
  - intros x Hx.
    unfold open_var. simpl.
    assert (Hx_typed :
              [(zero_var, (sort_of 2, t_sort (sort_of 1))); (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var));
               (x, (sort_of 2, t_sort (sort_of 1)))]
              ⊢* t_fvar (sort_of 2) x ∈ t_sort (sort_of 1)).
    { apply (typing_star_var
               [(zero_var, (sort_of 2, t_sort (sort_of 1))); (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var))]
               x (t_sort (sort_of 1)) (sort_of 2)).
      - exact Hx.
      - exact HtsortA. }
    apply (typing_star_pi
             [(zero_var, (sort_of 2, t_sort (sort_of 1))); (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var));
              (x, (sort_of 2, t_sort (sort_of 1)))]
             (t_fvar (sort_of 2) zero_var)
             (t_pi (sort_of 1) (t_fvar (sort_of 2) x) (t_fvar (sort_of 2) zero_var))
             (sort_of 1) (sort_of 1) (sort_of 1) []).
    + apply (typing_star_weakening_incl [(zero_var, (sort_of 2, t_sort (sort_of 1)))]).
      * apply (subcontext_app_l [(zero_var, (sort_of 2, t_sort (sort_of 1)))]).
      * exact Hz1.
    + intros y Hy.
      unfold open_var. simpl.
      apply (typing_star_pi
               [(zero_var, (sort_of 2, t_sort (sort_of 1))); (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var));
                (x, (sort_of 2, t_sort (sort_of 1))); (y, (sort_of 1, t_fvar (sort_of 2) zero_var))]
               (t_fvar (sort_of 2) x) (t_fvar (sort_of 2) zero_var) (sort_of 1) (sort_of 1) (sort_of 1) []).
      * apply (typing_star_weakening_incl
                 [(zero_var, (sort_of 2, t_sort (sort_of 1))); (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var));
                  (x, (sort_of 2, t_sort (sort_of 1)))]).
        -- apply (subcontext_app_l
                     [(zero_var, (sort_of 2, t_sort (sort_of 1))); (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var));
                      (x, (sort_of 2, t_sort (sort_of 1)))]).
        -- exact Hx_typed.
      * intros z Hz.
        unfold open_var. simpl.
        apply (typing_star_weakening_incl [(zero_var, (sort_of 2, t_sort (sort_of 1)))]).
        -- apply (subcontext_app_l [(zero_var, (sort_of 2, t_sort (sort_of 1)))]).
        -- exact Hz1.
      * split; [exact R_s1_s1_s1 |].
        rewrite (sort_of_correct 1 ltac:(lia) ltac:(lia)). lia.
    + split; [exact R_s1_s1_s1 |].
      rewrite (sort_of_correct 1 ltac:(lia) ltac:(lia)). lia.
  - split; [exact R_s2_s1 |].
    rewrite (sort_of_correct 1 ltac:(lia) ltac:(lia)).
    rewrite (sort_of_correct 2 ltac:(lia) ltac:(lia)).
    lia.
Qed.

Lemma bullet_typed :
  [(zero_var, (sort_of 2, t_sort (sort_of 1)));
   (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var));
   (prod_var, (sort_of 1, T_prod))] ⊢* t_fvar (sort_of 1) bullet_var ∈ t_fvar (sort_of 2) zero_var.
Proof.
  pose proof n_at_least_two as Hn2.
  pose proof zero_var_typed as Hz1.
  assert (Hb1 : [(zero_var, (sort_of 2, t_sort (sort_of 1))); (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var))]
                ⊢* t_fvar (sort_of 1) bullet_var ∈ t_fvar (sort_of 2) zero_var).
  { apply (typing_star_var [(zero_var, (sort_of 2, t_sort (sort_of 1)))] bullet_var (t_fvar (sort_of 2) zero_var) (sort_of 1)).
    - unfold is_fresh, dom. simpl.
      intros [Heq | []].
      apply bullet_var_ne_zero_var. symmetry. exact Heq.
    - exact Hz1. }
  apply (typing_star_weak
           [(zero_var, (sort_of 2, t_sort (sort_of 1))); (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var))]
           prod_var T_prod (t_fvar (sort_of 1) bullet_var) (t_fvar (sort_of 2) zero_var) (sort_of 1)).
  - unfold is_fresh, dom. simpl.
    intros [Heq | [Heq | []]].
    + apply prod_var_ne_zero_var. symmetry. exact Heq.
    + apply prod_var_ne_bullet_var. symmetry. exact Heq.
  - exact Hb1.
  - exact Tprod_typed.
Qed.

Lemma zero_var_typed_Δ :
  [(zero_var, (sort_of 2, t_sort (sort_of 1)));
   (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var));
   (prod_var, (sort_of 1, T_prod))] ⊢* t_fvar (sort_of 2) zero_var ∈ t_sort (sort_of 1).
Proof.
  apply (typing_star_weakening_incl [(zero_var, (sort_of 2, t_sort (sort_of 1)))]).
  - apply (subcontext_app_l [(zero_var, (sort_of 2, t_sort (sort_of 1)))]).
  - exact zero_var_typed.
Qed.

Lemma prod_var_typed_Δ :
  [(zero_var, (sort_of 2, t_sort (sort_of 1)));
   (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var));
   (prod_var, (sort_of 1, T_prod))] ⊢* t_fvar (sort_of 1) prod_var ∈ T_prod.
Proof.
  apply (typing_star_var [(zero_var, (sort_of 2, t_sort (sort_of 1))); (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var))]
           prod_var T_prod (sort_of 1)).
  - unfold is_fresh, dom. simpl.
    intros [Heq | [Heq | []]].
    + apply prod_var_ne_zero_var. symmetry. exact Heq.
    + apply prod_var_ne_bullet_var. symmetry. exact Heq.
  - exact Tprod_typed.
Qed.

Axiom gamma_pi_tower :
  forall Δ0 Γ0 A0 s1,
    Δ0 ⊢* t_fvar (sort_of 2) zero_var ∈ t_sort (sort_of 1) ->
    Γ0 ⊢ A0 ∈ t_sort s1 ->
    Δ0 ++ rho_ctx 0 Γ0 ⊢* gamma_pi_tel A0 (t_fvar (sort_of 2) zero_var) (deg A0 - 1) ∈ t_sort (sort_of 1).

Axiom gamma_lam_tower :
  forall Δ0 Γ0 A0 B0 s1 L,
    Δ0 ⊢* t_fvar (sort_of 2) zero_var ∈ t_sort (sort_of 1) ->
    Γ0 ⊢ A0 ∈ t_sort s1 ->
    (forall x, ~ In x L ->
       Δ0 ++ rho_ctx 0 (Γ0 ++ [(x, (s1, A0))]) ⊢* gamma (open_var B0 s1 x) ∈ t_fvar (sort_of 2) zero_var) ->
    Δ0 ++ rho_ctx 0 Γ0 ⊢* gamma_lam_tel A0 (gamma B0) (deg A0 - 1)
                        ∈ gamma_pi_tel A0 (t_fvar (sort_of 2) zero_var) (deg A0 - 1).

Lemma gamma_pi_tel_eq_rho_pi_tel : forall A B k,
  gamma_pi_tel A (rho 0 B) k = rho_pi_tel rho A B 0 k.
Proof.
  intros A B k. induction k as [| k' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma rho0_pi_eq_gamma_pi_tel : forall Γ0 A0 B0 s1,
  Γ0 ⊢ A0 ∈ t_sort s1 ->
  rho 0 (t_pi s1 A0 B0) = gamma_pi_tel A0 (rho 0 B0) (deg A0 - 1).
Proof.
  intros Γ0 A0 B0 s1 HA.
  pose proof (deg_sort_typed Γ0 A0 s1 HA) as HdegA0.
  pose proof (index_range s1) as [Hlo Hhi].
  assert (Hge : 0 + 1 <= deg A0) by lia.
  rewrite (rho_pi_named 0 s1 A0 B0 Hge).
  replace (deg A0 - 1 - 0) with (deg A0 - 1) by lia.
  symmetry. apply gamma_pi_tel_eq_rho_pi_tel.
Qed.

Axiom gamma_lam_tower_D :
  forall Δ0 Γ0 A0 M0 B0 s1 L,
    Γ0 ⊢ A0 ∈ t_sort s1 ->
    (forall x, ~ In x L ->
       Δ0 ++ rho_ctx 0 (Γ0 ++ [(x, (s1, A0))]) ⊢* gamma (open_var M0 s1 x) ∈ rho 0 (open_var B0 s1 x)) ->
    Δ0 ++ rho_ctx 0 Γ0 ⊢* gamma_lam_tel A0 (gamma M0) (deg A0 - 1)
                        ∈ gamma_pi_tel A0 (rho 0 B0) (deg A0 - 1).

Axiom gamma_lam_applied :
  forall Δ0 Γ0 A0 lamTerm piType,
    Δ0 ++ rho_ctx 0 Γ0 ⊢* lamTerm ∈ piType ->
    Δ0 ++ rho_ctx 0 Γ0 ⊢* piType ∈ t_sort (sort_of 1) ->
    Δ0 ++ rho_ctx 0 Γ0 ⊢* gamma A0 ∈ t_fvar (sort_of 2) zero_var ->
    Δ0 ++ rho_ctx 0 Γ0 ⊢*
      t_app (t_lam (sort_of 1) (t_fvar (sort_of 2) zero_var) lamTerm) (gamma A0) ∈ piType.

Axiom gamma_app_tower :
  forall Δ0 Γ0 M0 N0 A0 B0 s1a,
    Γ0 ⊢ M0 ∈ t_pi s1a A0 B0 ->
    Γ0 ⊢ N0 ∈ A0 ->
    Δ0 ++ rho_ctx 0 Γ0 ⊢* gamma M0 ∈ rho 0 (t_pi s1a A0 B0) ->
    Δ0 ++ rho_ctx 0 Γ0 ⊢* gamma N0 ∈ rho 0 A0 ->
    Δ0 ++ rho_ctx 0 Γ0 ⊢* t_app (gamma_app_tel (gamma M0) N0 (deg N0 - 1)) (gamma N0)
                        ∈ rho 0 (B0 ^^ N0).

Axiom gamma_prod_applied :
  forall Δ0 Γ0 A0 lamterm,
    Δ0 ++ rho_ctx 0 Γ0 ⊢* t_fvar (sort_of 1) prod_var ∈ T_prod ->
    Δ0 ++ rho_ctx 0 Γ0 ⊢* gamma_pi_tel A0 (t_fvar (sort_of 2) zero_var) (deg A0 - 1) ∈ t_sort (sort_of 1) ->
    Δ0 ++ rho_ctx 0 Γ0 ⊢* gamma A0 ∈ t_fvar (sort_of 2) zero_var ->
    Δ0 ++ rho_ctx 0 Γ0 ⊢* lamterm ∈ gamma_pi_tel A0 (t_fvar (sort_of 2) zero_var) (deg A0 - 1) ->
    Δ0 ++ rho_ctx 0 Γ0 ⊢*
      t_app (t_app (t_app (t_fvar (sort_of 1) prod_var) (gamma_pi_tel A0 (t_fvar (sort_of 2) zero_var) (deg A0 - 1)))
                   (gamma A0))
            lamterm
      ∈ t_fvar (sort_of 2) zero_var.

Lemma gamma_commutes_typing :
  forall Γ M N, Γ ⊢ M ∈ N ->
  [(zero_var, (sort_of 2, t_sort (sort_of 1)));
   (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var));
   (prod_var, (sort_of 1, T_prod))] ++ rho_ctx 0 Γ ⊢* gamma M ∈ rho 0 N.
Proof.
  intros Γ M N Htype.
  remember ([(zero_var, (sort_of 2, t_sort (sort_of 1)));
             (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var));
             (prod_var, (sort_of 1, T_prod))]) as Δ.
  induction Htype as
    [ s s' HA
    | Γ0 x A0 s0 Hfresh HA IHA
    | Γ0 x B0 M0 A0 s0 Hfresh HM IHM HB IHB
    | Γ0 A0 B0 s1 s2 s3 L HA IHA HTagB HB IHB HR
    | Γ0 A0 M0 B0 s1 s3 L HA IHA HTagM HM IHM HPi IHPi
    | Γ0 M0 N0 A0 B0 s1a HM IHM HN IHN
    | Γ0 M0 A0 B0 s HM IHM Heq HB IHB ].

  - (* typing_axiom *)
    simpl.
    apply (typing_star_weakening_incl Δ).
    + apply (subcontext_app_l Δ).
    + rewrite HeqΔ. exact bullet_typed.

  - (* typing_var *)
    pose proof (index_range s0) as [Hxlo Hxhi].
    pose proof (deg_sort_typed Γ0 A0 s0 HA) as HdegA0.
    assert (Hdeg1 : deg A0 >= 0 + 1) by lia.
    pose proof (rho_commutes_typing 0 (ltac:(lia)) Γ0 A0 (t_sort s0) HA Hdeg1) as HB1.
    simpl in HB1.
    assert (HB0 : rho_ctx 0 Γ0 ⊢* rho 0 A0 ∈ t_sort (sort_of 1))
      by (apply (typing_star_weakening_incl (rho_ctx 1 Γ0) (rho_ctx 0 Γ0));
          [apply rho_ctx_mono; lia | exact HB1]).
    pose (x' := retag x (sort_of 1)).
    assert (Hxnz : x <> zero_var)
      by (apply (typing_avoids_zero_var (Γ0 ++ [(x, (s0, A0))]) (t_fvar s0 x) A0
                   (typing_var Γ0 x A0 s0 Hfresh HA) x s0 A0);
          apply in_or_app; right; left; reflexivity).
    assert (Hfreshx' : is_fresh x' (rho_ctx 0 Γ0))
      by (apply rho_ctx_fresh; [exact Hxnz | exact Hfresh]).
    assert (Hstep : rho_ctx 0 Γ0 ++ [(x', (sort_of 1, rho 0 A0))] ⊢* t_fvar (sort_of 1) x' ∈ rho 0 A0)
      by (apply typing_star_var; [exact Hfreshx' | exact HB0]).
    assert (Hmem : In (x', (sort_of 1, rho 0 A0))
                     (rho_ctx_tel x s0 A0 (index_of s0 - 0 - 1))).
    { pose proof (rho_ctx_tel_last x s0 A0 (index_of s0 - 0 - 1)) as Htel.
      replace (index_of s0 - (index_of s0 - 0 - 1))
        with 1 in Htel by lia.
      simpl in Htel.
      unfold x'. exact Htel.
    }
    assert (Hincl : rho_ctx 0 Γ0 ++ [(x', (sort_of 1, rho 0 A0))]
                    ⊆ rho_ctx 0 (Γ0 ++ [(x, (s0, A0))])).
    { apply subcontext_app_same.
      - apply rho_ctx_incl_old.
      - intros p q Hpq. destruct Hpq as [Heq | []]. inversion Heq; subst.
        apply (rho_ctx_incl_new Γ0 0 x s0 A0). exact Hmem.
    }
    assert (Hfinal : rho_ctx 0 (Γ0 ++ [(x, (s0, A0))]) ⊢* t_fvar (sort_of 1) x' ∈ rho 0 A0)
      by (apply (typing_star_weakening_incl _ _ _ _ Hincl Hstep)).
    simpl. unfold x' in Hfinal.
    apply (typing_star_weakening_incl (rho_ctx 0 (Γ0 ++ [(x, (s0, A0))]))
             (Δ ++ rho_ctx 0 (Γ0 ++ [(x, (s0, A0))]))).
    + apply (subcontext_app_r (rho_ctx 0 (Γ0 ++ [(x, (s0, A0))])) Δ).
    + exact Hfinal.

  - (* typing_weak *)
    apply (typing_star_weakening_incl (Δ ++ rho_ctx 0 Γ0)
             (Δ ++ rho_ctx 0 (Γ0 ++ [(x, (s0, B0))]))).
    + apply app_subset_app.
      * intros p q Hpq. exact Hpq.
      * apply rho_ctx_incl_old.
    + exact IHM.

  - (* typing_pi *)
    simpl.
    assert (HzeroΔ0 : Δ ⊢* t_fvar (sort_of 2) zero_var ∈ t_sort (sort_of 1))
      by (rewrite HeqΔ; exact zero_var_typed_Δ).
    assert (HProdTyped : Δ ++ rho_ctx 0 Γ0 ⊢* t_fvar (sort_of 1) prod_var ∈ T_prod).
    { apply (typing_star_weakening_incl Δ).
      - apply (subcontext_app_l Δ).
      - rewrite HeqΔ. exact prod_var_typed_Δ. }
    assert (HpiTel : Δ ++ rho_ctx 0 Γ0 ⊢* gamma_pi_tel A0 (t_fvar (sort_of 2) zero_var) (deg A0 - 1)
                      ∈ t_sort (sort_of 1))
      by (apply (gamma_pi_tower Δ Γ0 A0 s1 HzeroΔ0 HA)).
    assert (HgammaA : Δ ++ rho_ctx 0 Γ0 ⊢* gamma A0 ∈ t_fvar (sort_of 2) zero_var)
      by (simpl in IHA; exact IHA).
    assert (HBcofin : forall x, ~ In x L ->
               Δ ++ rho_ctx 0 (Γ0 ++ [(x, (s1, A0))]) ⊢* gamma (open_var B0 s1 x) ∈ t_fvar (sort_of 2) zero_var).
    { intros x Hx. pose proof (IHB x Hx) as H. simpl in H. exact H. }
    assert (HlamTel : Δ ++ rho_ctx 0 Γ0 ⊢* gamma_lam_tel A0 (gamma B0) (deg A0 - 1)
                        ∈ gamma_pi_tel A0 (t_fvar (sort_of 2) zero_var) (deg A0 - 1))
      by (apply (gamma_lam_tower Δ Γ0 A0 B0 s1 L HzeroΔ0 HA HBcofin)).
    apply (gamma_prod_applied Δ Γ0 A0 (gamma_lam_tel A0 (gamma B0) (deg A0 - 1))
             HProdTyped HpiTel HgammaA HlamTel).

  - (* typing_lam *)
    rewrite (rho0_pi_eq_gamma_pi_tel Γ0 A0 B0 s1 HA).
    assert (HdegPi1 : deg (t_pi s1 A0 B0) >= 0 + 1)
      by (pose proof (index_range s3) as [Hlo Hhi];
          pose proof (deg_sort_typed Γ0 (t_pi s1 A0 B0) s3 HPi); lia).
    pose proof (rho_commutes_typing 0 (ltac:(lia)) Γ0 (t_pi s1 A0 B0) (t_sort s3) HPi HdegPi1)
      as HpiTelD1.
    simpl in HpiTelD1.
    assert (HpiTelD0 : rho_ctx 0 Γ0 ⊢* rho 0 (t_pi s1 A0 B0) ∈ t_sort (sort_of 1))
      by (apply (typing_star_weakening_incl (rho_ctx 1 Γ0) (rho_ctx 0 Γ0));
          [apply rho_ctx_mono; lia | exact HpiTelD1]).
    rewrite (rho0_pi_eq_gamma_pi_tel Γ0 A0 B0 s1 HA) in HpiTelD0.
    assert (HpiTelD : Δ ++ rho_ctx 0 Γ0 ⊢* gamma_pi_tel A0 (rho 0 B0) (deg A0 - 1)
                        ∈ t_sort (sort_of 1))
      by (apply (typing_star_weakening_incl (rho_ctx 0 Γ0) (Δ ++ rho_ctx 0 Γ0));
          [apply (subcontext_app_r (rho_ctx 0 Γ0) Δ) | exact HpiTelD0]).
    assert (HgammaA : Δ ++ rho_ctx 0 Γ0 ⊢* gamma A0 ∈ t_fvar (sort_of 2) zero_var)
      by (simpl in IHA; exact IHA).
    assert (HMcofin : forall x, ~ In x L ->
               Δ ++ rho_ctx 0 (Γ0 ++ [(x, (s1, A0))]) ⊢* gamma (open_var M0 s1 x) ∈ rho 0 (open_var B0 s1 x)).
    { intros x Hx. exact (IHM x Hx). }
    assert (HlamTelD : Δ ++ rho_ctx 0 Γ0 ⊢* gamma_lam_tel A0 (gamma M0) (deg A0 - 1)
                        ∈ gamma_pi_tel A0 (rho 0 B0) (deg A0 - 1))
      by (apply (gamma_lam_tower_D Δ Γ0 A0 M0 B0 s1 L HA HMcofin)).
    apply (gamma_lam_applied Δ Γ0 A0
             (gamma_lam_tel A0 (gamma M0) (deg A0 - 1))
             (gamma_pi_tel A0 (rho 0 B0) (deg A0 - 1))
             HlamTelD HpiTelD HgammaA).

  - (* typing_app *)
    apply (gamma_app_tower Δ Γ0 M0 N0 A0 B0 s1a HM HN IHM IHN).

  - (* typing_conv *)
    assert (HdegA0 : deg A0 >= 0 + 1)
      by (pose proof (deg_typing_succ Γ0 M0 A0 HM); lia).
    assert (HeqRho : rho 0 A0 =b rho 0 B0)
      by (apply (rho_commutes_beta_eq 0 (ltac:(lia)) A0 B0 HdegA0 Heq)).
    assert (HdegB1 : deg B0 >= 0 + 1)
      by (pose proof (index_range s) as [Hlo Hhi];
          pose proof (deg_sort_typed Γ0 B0 s HB); lia).
    pose proof (rho_commutes_typing 0 (ltac:(lia)) Γ0 B0 (t_sort s) HB HdegB1) as HrhoB1.
    simpl in HrhoB1.
    assert (HrhoB0 : rho_ctx 0 Γ0 ⊢* rho 0 B0 ∈ t_sort (sort_of 1))
      by (apply (typing_star_weakening_incl (rho_ctx 1 Γ0) (rho_ctx 0 Γ0));
          [apply rho_ctx_mono; lia | exact HrhoB1]).
    assert (HrhoB0Δ : Δ ++ rho_ctx 0 Γ0 ⊢* rho 0 B0 ∈ t_sort (sort_of 1))
      by (apply (typing_star_weakening_incl (rho_ctx 0 Γ0) (Δ ++ rho_ctx 0 Γ0));
          [apply (subcontext_app_r (rho_ctx 0 Γ0) Δ) | exact HrhoB0]).
    apply (typing_star_conv (Δ ++ rho_ctx 0 Γ0) (gamma M0) (rho 0 A0) (rho 0 B0)
             (sort_of 1) IHM HeqRho HrhoB0Δ).
Qed.

(* ================================================================= *)
(* gamma commutes with substitution *)

Fixpoint gamma_subst_tel (M B : term) (x : var) (K : nat) : term :=
  match K with
  | O    => M
  | S K' => gamma_subst_tel (M ⁅ retag x (sort_of (K' + 2)) ≔ rho K' B ⁆) B x K'
  end.

Definition gamma_subst (A B : term) (x : var) (s : Sort) : term :=
  (gamma_subst_tel (gamma A) B x (index_of s - 1)) ⁅ retag x (sort_of 1) ≔ gamma B ⁆.

Lemma sort_of_1_ne_sort_of_m : forall m, 2 <= m -> m < n + 1 -> sort_of 1 <> sort_of m.
Proof.
  intros m Hm2 Hmn Heq.
  assert (H1 : index_of (sort_of 1) = 1) by (apply sort_of_correct; lia).
  assert (H2 : index_of (sort_of m) = m) by (apply sort_of_correct; lia).
  rewrite Heq in H1. lia.
Qed.

Lemma gamma_subst_tel_fvar_const : forall sC C x B K,
  (forall m, 2 <= m -> m <= K + 1 -> retag x (sort_of m) <> C) ->
  gamma_subst_tel (t_fvar sC C) B x K = t_fvar sC C.
Proof.
  intros sC C x B K.
  induction K as [| K' IH]; intros Hm.
  - reflexivity.
  - simpl.
    destruct (eq_var_dec C (retag x (sort_of (K' + 2)))) as [Heq | Hneq].
    + exfalso. apply (Hm (K' + 2) ltac:(lia) ltac:(lia)). symmetry. exact Heq.
    + apply IH. intros m Hm2 Hm3. apply Hm; lia.
Qed.

Lemma gamma_subst_tel_bvar_const : forall s0 k0 x B K,
  gamma_subst_tel (t_bvar s0 k0) B x K = t_bvar s0 k0.
Proof.
  intros s0 k0 x B K.
  induction K as [| K' IH].
  - reflexivity.
  - simpl. exact IH.
Qed.

Lemma gamma_subst_tel_app_commute : forall P Q x B K,
  gamma_subst_tel (t_app P Q) B x K
  = t_app (gamma_subst_tel P B x K) (gamma_subst_tel Q B x K).
Proof.
  intros P Q x B K. revert P Q.
  induction K as [| K' IH]; intros P Q.
  - reflexivity.
  - simpl. apply IH.
Qed.

Lemma gamma_subst_tel_lam_commute : forall s' A' M' x B K,
  gamma_subst_tel (t_lam s' A' M') B x K
  = t_lam s' (gamma_subst_tel A' B x K) (gamma_subst_tel M' B x K).
Proof.
  intros s' A' M' x B K. revert A' M'.
  induction K as [| K' IH]; intros A' M'.
  - reflexivity.
  - simpl. apply IH.
Qed.

Lemma gamma_subst_sentinel_const : forall sC C B x s,
  (forall y sy, retag y sy <> C) ->
  (gamma_subst_tel (t_fvar sC C) B x (index_of s - 1))
    ⁅ retag x (sort_of 1) ≔ gamma B ⁆
  = t_fvar sC C.
Proof.
  intros sC C B x s Hsent.
  assert (Hconst : gamma_subst_tel (t_fvar sC C) B x (index_of s - 1) = t_fvar sC C).
  { apply gamma_subst_tel_fvar_const.
    intros m Hm2 Hm3 Heq. apply (Hsent x (sort_of m)). exact Heq. }
  rewrite Hconst. simpl.
  destruct (eq_var_dec C (retag x (sort_of 1))) as [Heq | Hneq].
  - exfalso. apply (Hsent x (sort_of 1)). symmetry. exact Heq.
  - reflexivity.
Qed.

Axiom gamma_pi_tel_commutes_subst : forall C B x s KC,
  x <> zero_var -> 1 <= index_of s <= n ->
  deg B = index_of s - 1 -> lc B -> only_tagged x s C ->
  (gamma_subst_tel (gamma_pi_tel C (t_fvar (sort_of 2) zero_var) KC) B x (index_of s - 1))
    ⁅ retag x (sort_of 1) ≔ gamma B ⁆
  = gamma_pi_tel (C ⁅ x ≔ B ⁆) (t_fvar (sort_of 2) zero_var) KC.

Axiom gamma_lam_tel_commutes_subst : forall C D B x s KC,
  x <> zero_var -> 1 <= index_of s <= n ->
  deg B = index_of s - 1 -> lc B -> only_tagged x s C ->
  (gamma_subst_tel (gamma_lam_tel C D KC) B x (index_of s - 1))
    ⁅ retag x (sort_of 1) ≔ gamma B ⁆
  = gamma_lam_tel (C ⁅ x ≔ B ⁆)
      ((gamma_subst_tel D B x (index_of s - 1))
         ⁅ retag x (sort_of 1) ≔ gamma B ⁆)
      KC.

Axiom gamma_app_tel_commutes_subst : forall MG C B x s KC,
  x <> zero_var -> 1 <= index_of s <= n ->
  deg B = index_of s - 1 -> lc B -> only_tagged x s C ->
  (gamma_subst_tel (gamma_app_tel MG C KC) B x (index_of s - 1))
    ⁅ retag x (sort_of 1) ≔ gamma B ⁆
  = gamma_app_tel
      ((gamma_subst_tel MG B x (index_of s - 1))
         ⁅ retag x (sort_of 1) ≔ gamma B ⁆)
      (C ⁅ x ≔ B ⁆) KC.

Lemma gamma_commutes_substitution :
  forall x s, x <> bullet_var -> x <> zero_var -> x <> prod_var ->
  1 <= index_of s <= n ->
  forall A, only_tagged x s A ->
  forall B, deg B = index_of s - 1 -> lc B ->
  gamma (A ⁅ x ≔ B ⁆) = gamma_subst A B x s.
Proof.
  intros x s Hxb Hxz Hxp Hxrange A.
  unfold gamma_subst.
  induction A as [s0 | s_m m | sy y | D IHD C IHC | s1 C IHC D IHD | s1 C IHC D IHD];
    intros HonlyA B HdegB HlcB.

  - (* A = t_sort s0 *)
    rewrite subst_sort. simpl.
    rewrite (gamma_subst_sentinel_const (sort_of 1) bullet_var B x s bullet_var_retag_ne).
    reflexivity.

  - (* A = t_bvar s_m m *)
    rewrite subst_bvar. simpl.
    rewrite gamma_subst_tel_bvar_const, subst_bvar.
    reflexivity.

  - (* A = t_fvar sy y *)
    rewrite subst_var.
    destruct (eq_var_dec y x) as [Heq | Hneq].
    + subst y.
      simpl.
      assert (Hconst : gamma_subst_tel (t_fvar (sort_of 1) (retag x (sort_of 1))) B x (index_of s - 1)
                        = t_fvar (sort_of 1) (retag x (sort_of 1))).
      { apply gamma_subst_tel_fvar_const.
        intros m Hm2 Hm3 Heq2.
        apply retag_inj in Heq2 as [_ Hsc].
        apply (sort_of_1_ne_sort_of_m m Hm2 ltac:(lia)).
        symmetry. exact Hsc. }
      rewrite Hconst. simpl.
      destruct (eq_var_dec (retag x (sort_of 1)) (retag x (sort_of 1))) as [_ | Hne2].
      * reflexivity.
      * exfalso. apply Hne2. reflexivity.
    + simpl.
      assert (Hconst : gamma_subst_tel (t_fvar (sort_of 1) (retag y (sort_of 1))) B x (index_of s - 1)
                        = t_fvar (sort_of 1) (retag y (sort_of 1))).
      { apply gamma_subst_tel_fvar_const.
        intros m Hm2 Hm3 Heq2.
        apply retag_inj in Heq2 as [Hxeq _]. apply Hneq. symmetry. exact Hxeq. }
      rewrite Hconst. simpl.
      destruct (eq_var_dec (retag y (sort_of 1)) (retag x (sort_of 1))) as [Heq2 | Hneq2].
      * exfalso. apply retag_inj in Heq2 as [Hc _]. apply Hneq. exact Hc.
      * reflexivity.

  - (* A = t_app D C *)
    simpl in HonlyA. destruct HonlyA as [HonlyD HonlyC].
    assert (HdegC : deg (C ⁅ x ≔ B ⁆) = deg C)
      by (apply (deg_subst_tagged C x s B HonlyC HlcB HdegB)).
    rewrite subst_app. simpl. rewrite HdegC.
    rewrite gamma_subst_tel_app_commute, subst_app.
    rewrite (gamma_app_tel_commutes_subst (gamma D) C B x s (deg C - 1) Hxz Hxrange HdegB HlcB HonlyC).
    rewrite <- (IHD HonlyD B HdegB HlcB), <- (IHC HonlyC B HdegB HlcB).
    reflexivity.

  - (* A = t_lam s1 C D *)
    simpl in HonlyA. destruct HonlyA as [HonlyC HonlyD].
    assert (HdegC : deg (C ⁅ x ≔ B ⁆) = deg C)
      by (apply (deg_subst_tagged C x s B HonlyC HlcB HdegB)).
    rewrite subst_lam. simpl. rewrite HdegC.
    rewrite gamma_subst_tel_app_commute, subst_app.
    rewrite gamma_subst_tel_lam_commute, subst_lam.
    rewrite (gamma_subst_sentinel_const (sort_of 2) zero_var B x s zero_var_retag_ne).
    rewrite (gamma_lam_tel_commutes_subst C (gamma D) B x s (deg C - 1) Hxz Hxrange HdegB HlcB HonlyC).
    rewrite <- (IHD HonlyD B HdegB HlcB), <- (IHC HonlyC B HdegB HlcB).
    reflexivity.

  - (* A = t_pi s1 C D *)
    simpl in HonlyA. destruct HonlyA as [HonlyC HonlyD].
    assert (HdegC : deg (C ⁅ x ≔ B ⁆) = deg C)
      by (apply (deg_subst_tagged C x s B HonlyC HlcB HdegB)).
    rewrite subst_pi. simpl. rewrite HdegC.
    rewrite gamma_subst_tel_app_commute, subst_app.
    rewrite gamma_subst_tel_app_commute, subst_app.
    rewrite gamma_subst_tel_app_commute, subst_app.
    rewrite (gamma_subst_sentinel_const (sort_of 1) prod_var B x s prod_var_retag_ne).
    rewrite (gamma_pi_tel_commutes_subst C B x s (deg C - 1) Hxz Hxrange HdegB HlcB HonlyC).
    rewrite (gamma_lam_tel_commutes_subst C (gamma D) B x s (deg C - 1) Hxz Hxrange HdegB HlcB HonlyC).
    rewrite <- (IHD HonlyD B HdegB HlcB), <- (IHC HonlyC B HdegB HlcB).
    reflexivity.
Qed.


(* ================================================================= *)
(* gamma commutes with beta *)

Lemma gamma_pi_tel_dom_congr : forall C C' body k,
  (forall m, m <= k -> rho m C ->>b rho m C') ->
  gamma_pi_tel C body k ->>b gamma_pi_tel C' body k.
Proof.
  induction k as [| k' IHk]; intros Hall; simpl.
  - apply brt_pi_A. apply Hall. lia.
  - apply brt_pi_congr.
    + apply Hall. lia.
    + apply IHk. intros m Hm. apply Hall. lia.
Qed.

Lemma gamma_lam_tel_dom_congr : forall C C' body k,
  (forall m, m <= k -> rho m C ->>b rho m C') ->
  gamma_lam_tel C body k ->>b gamma_lam_tel C' body k.
Proof.
  induction k as [| k' IHk]; intros Hall; simpl.
  - apply brt_lam_A. apply Hall. lia.
  - apply brt_lam_congr.
    + apply Hall. lia.
    + apply IHk. intros m Hm. apply Hall. lia.
Qed.

Lemma gamma_lam_tel_body_congr : forall C body body' k,
  body ->>b body' -> gamma_lam_tel C body k ->>b gamma_lam_tel C body' k.
Proof.
  induction k as [| k' IHk]; intros Hb; simpl.
  - apply brt_lam_M. exact Hb.
  - apply brt_lam_M. apply IHk. exact Hb.
Qed.

Lemma gamma_app_tel_func_congr : forall M M' N k,
  M ->>b M' -> gamma_app_tel M N k ->>b gamma_app_tel M' N k.
Proof.
  intros M M' N k. revert M M'.
  induction k as [| k' IH]; intros M M' Hstep; simpl.
  - apply brt_app_l. exact Hstep.
  - apply IH. apply brt_app_l. exact Hstep.
Qed.

Lemma gamma_app_tel_arg_congr : forall MG N N' k,
  (forall j, j <= k -> rho j N ->>b rho j N') ->
  gamma_app_tel MG N k ->>b gamma_app_tel MG N' k.
Proof.
  intros MG N N' k. revert MG.
  induction k as [| k' IH]; intros MG Hall; simpl.
  - apply brt_app_r. apply Hall. lia.
  - apply brt_trans with (gamma_app_tel (t_app MG (rho (S k') N')) N k').
    + apply gamma_app_tel_func_congr. apply brt_app_r. apply Hall. lia.
    + apply IH. intros j Hj. apply Hall. lia.
Qed.

Axiom rho_commutes_beta_below : forall i, 0 <= i <= n ->
  forall M N, deg M < i + 1 -> M ->>b N -> rho i M ->>b rho i N.

Lemma rho_commutes_beta_total :
  forall i, 0 <= i <= n -> forall M N, M ->>b N -> rho i M ->>b rho i N.
Proof.
  intros i Hi M N Hbeta.
  destruct (le_lt_dec (i + 1) (deg M)) as [E | E].
  - apply rho_commutes_beta; [lia | lia | exact Hbeta].
  - apply rho_commutes_beta_below; [lia | lia | exact Hbeta].
Qed.

Lemma bt_pi_A : forall s A A' B, A ->>+b A' -> t_pi s A B ->>+b t_pi s A' B.
Proof.
  intros s A A' B H.
  induction H as [A A' Hs | A A'' A' H1 IH1 H2 IH2].
  - apply bt_step. apply beta_pi_A. exact Hs.
  - apply bt_trans with (t_pi s A'' B); auto.
Qed.

Lemma bt_pi_B : forall s A B B', B ->>+b B' -> t_pi s A B ->>+b t_pi s A B'.
Proof.
  intros s A B B' H.
  induction H as [B B' Hs | B B'' B' H1 IH1 H2 IH2].
  - apply bt_step. apply beta_pi_B. exact Hs.
  - apply bt_trans with (t_pi s A B''); auto.
Qed.

Lemma bt_lam_A : forall s A A' M, A ->>+b A' -> t_lam s A M ->>+b t_lam s A' M.
Proof.
  intros s A A' M H.
  induction H as [A A' Hs | A A'' A' H1 IH1 H2 IH2].
  - apply bt_step. apply beta_lam_A. exact Hs.
  - apply bt_trans with (t_lam s A'' M); auto.
Qed.

Lemma bt_lam_M : forall s A M M', M ->>+b M' -> t_lam s A M ->>+b t_lam s A M'.
Proof.
  intros s A M M' H.
  induction H as [M M' Hs | M M'' M' H1 IH1 H2 IH2].
  - apply bt_step. apply beta_lam_M. exact Hs.
  - apply bt_trans with (t_lam s A M''); auto.
Qed.

Lemma bt_app_l : forall M M' N, M ->>+b M' -> t_app M N ->>+b t_app M' N.
Proof.
  intros M M' N H.
  induction H as [M M' Hs | M M'' M' H1 IH1 H2 IH2].
  - apply bt_step. apply beta_app_l. exact Hs.
  - apply bt_trans with (t_app M'' N); auto.
Qed.

Lemma bt_app_r : forall M N N', N ->>+b N' -> t_app M N ->>+b t_app M N'.
Proof.
  intros M N N' H.
  induction H as [N N' Hs | N N'' N' H1 IH1 H2 IH2].
  - apply bt_step. apply beta_app_r. exact Hs.
  - apply bt_trans with (t_app M N''); auto.
Qed.

Lemma brt_bt_trans : forall M K N, M ->>b K -> K ->>+b N -> M ->>+b N.
Proof.
  intros M K N Hmk.
  induction Hmk as [M | M K Hs | M Q K H1 IH1 H2 IH2]; intros Hkn.
  - exact Hkn.
  - apply bt_trans with K; [apply bt_step; exact Hs | exact Hkn].
  - apply IH1. apply IH2. exact Hkn.
Qed.

Lemma bt_brt_trans : forall M K N, K ->>b N -> M ->>+b K -> M ->>+b N.
Proof.
  intros M K N Hkn.
  induction Hkn as [K | K N Hs | K Q N H1 IH1 H2 IH2]; intros Hmk.
  - exact Hmk.
  - apply bt_trans with K; [exact Hmk | apply bt_step; exact Hs].
  - apply IH2. apply IH1. exact Hmk.
Qed.

Lemma bt_app_congr_L : forall M M' N N',
  M ->>+b M' -> N ->>b N' -> t_app M N ->>+b t_app M' N'.
Proof.
  intros M M' N N' HM HN.
  apply (bt_brt_trans (t_app M N) (t_app M' N) (t_app M' N')).
  - apply brt_app_r. exact HN.
  - apply bt_app_l. exact HM.
Qed.

Lemma bt_app_congr_R : forall M M' N N',
  M ->>b M' -> N ->>+b N' -> t_app M N ->>+b t_app M' N'.
Proof.
  intros M M' N N' HM HN.
  apply (brt_bt_trans (t_app M N) (t_app M' N) (t_app M' N')).
  - apply brt_app_l. exact HM.
  - apply bt_app_r. exact HN.
Qed.

Lemma gamma_app_tel_func_congr_plus : forall M M' N k,
  M ->>+b M' -> gamma_app_tel M N k ->>+b gamma_app_tel M' N k.
Proof.
  intros M M' N k. revert M M'.
  induction k as [| k' IH]; intros M M' Hstep; simpl.
  - apply bt_app_l. exact Hstep.
  - apply IH. apply bt_app_l. exact Hstep.
Qed.

Lemma gamma_lam_tel_body_congr_plus : forall C body body' k,
  body ->>+b body' -> gamma_lam_tel C body k ->>+b gamma_lam_tel C body' k.
Proof.
  induction k as [| k' IHk]; intros Hb; simpl.
  - apply bt_lam_M. exact Hb.
  - apply bt_lam_M. apply IHk. exact Hb.
Qed.

Axiom gamma_commutes_beta_base : forall s A M N,
  gamma (t_app (t_lam s A M) N) ->>+b gamma (M ^^ N).

Lemma gamma_commutes_beta_aux :
  forall M N, M ->b N -> gamma M ->>+b gamma N.
Proof.
  induction M as [s | s_m m | y | P IHP Q IHQ | s A IHA M' IHM' | s A IHA B IHB];
    intros N Hstep.

  - (* t_sort *) inversion Hstep.
  - (* t_bvar *) inversion Hstep.
  - (* t_fvar *) inversion Hstep.

  - (* t_app P Q *)
    inversion Hstep; subst; clear Hstep.

    + (* beta_base *)
      apply gamma_commutes_beta_base.

    + (* beta_app_l *)
      match goal with
      | Hs : P ->b ?P' |- _ =>
        simpl; apply bt_app_l; apply gamma_app_tel_func_congr_plus; apply IHP; exact Hs
      end.

    + (* beta_app_r *)
      match goal with
      | Hs : Q ->b ?Q' |- _ =>
        assert (HdegQeq : deg Q = deg Q') by (apply deg_beta; apply brt_step; exact Hs);
        assert (HQle : deg Q <= n + 1) by (apply deg_le_top);
        simpl; rewrite <- HdegQeq;
        apply bt_app_congr_R;
        [ apply gamma_app_tel_arg_congr;
          intros j Hj; apply rho_commutes_beta_total; [lia | apply brt_step; exact Hs]
        | apply IHQ; exact Hs ]
      end.

  - (* t_lam s A M' *)
    inversion Hstep; subst; clear Hstep.

    + (* beta_lam_A *)
      match goal with
      | Hs : A ->b ?A1' |- _ =>
        assert (HdegAeq : deg A = deg A1') by (apply deg_beta; apply brt_step; exact Hs);
        assert (HAle : deg A <= n + 1) by (apply deg_le_top);
        simpl; rewrite <- HdegAeq;
        apply bt_app_congr_R;
        [ apply brt_lam_M; apply gamma_lam_tel_dom_congr;
          intros mtier Hmtier; apply rho_commutes_beta_total; [lia | apply brt_step; exact Hs]
        | apply IHA; exact Hs ]
      end.

    + (* beta_lam_M *)
      match goal with
      | Hs : M' ->b ?M1' |- _ =>
        simpl; apply bt_app_l; apply bt_lam_M; apply gamma_lam_tel_body_congr_plus;
        apply IHM'; exact Hs
      end.

  - (* t_pi s A B *)
    inversion Hstep; subst; clear Hstep.

    + (* beta_pi_A *)
      match goal with
      | Hs : A ->b ?A1' |- _ =>
        assert (HdegAeq : deg A = deg A1') by (apply deg_beta; apply brt_step; exact Hs);
        assert (HAle : deg A <= n + 1) by (apply deg_le_top);
        simpl; rewrite <- HdegAeq;
        apply bt_app_congr_L;
        [ apply bt_app_congr_R;
          [ apply brt_app_r; apply gamma_pi_tel_dom_congr;
            intros mtier Hmtier; apply rho_commutes_beta_total; [lia | apply brt_step; exact Hs]
          | apply IHA; exact Hs ]
        | apply gamma_lam_tel_dom_congr;
          intros mtier Hmtier; apply rho_commutes_beta_total; [lia | apply brt_step; exact Hs] ]
      end.

    + (* beta_pi_B *)
      match goal with
      | Hs : B ->b ?B1' |- _ =>
        simpl; apply bt_app_r; apply gamma_lam_tel_body_congr_plus; apply IHB; exact Hs
      end.
Qed.

Lemma gamma_commutes_beta :
  forall M N, M ->>b N -> gamma M ->>b gamma N.
Proof.
  intros M N Hbeta.
  induction Hbeta as [M | M N Hstep | M N P Hstep1 IH1 Hstep2 IH2].
  - apply brt_refl.
  - apply brt_from_trans. apply (gamma_commutes_beta_aux M N Hstep).
  - apply brt_trans with (gamma N); auto.
Qed.

(* ================================================================= *)
(** Main Theorem: λS is strongly normalizing iff λS∗ is *)

Lemma bt_forward_acc : forall X Y, X ->>+b Y ->
  (forall Z, X ->b Z -> Acc (fun N M => M ->>+b N) Z) ->
  Acc (fun N M => M ->>+b N) Y.
Proof.
  intros X Y HXY.
  induction HXY as [X Y Hstep | X Z Y H1 IH1 H2 IH2]; intros Hbase.
  - apply Hbase. exact Hstep.
  - apply IH2.
    intros Z0 HstepZ.
    destruct (IH1 Hbase) as [f].
    apply f. apply bt_step. exact HstepZ.
Qed.

Lemma Acc_atomic_implies_Acc_plus : forall X,
  strongly_normalizing X -> Acc (fun N M => M ->>+b N) X.
Proof.
  intros X HX.
  induction HX as [X _ IH].
  constructor.
  intros Y HXY.
  exact (bt_forward_acc X Y HXY IH).
Qed.

Lemma sn_reflection_core :
  forall b, Acc (fun N M => M ->>+b N) b ->
  forall M, b = gamma M -> strongly_normalizing M.
Proof.
  intros b Hacc.
  induction Hacc as [b _ IH].
  intros M Heq.
  constructor.
  intros M' HstepM.
  apply (IH (gamma M')).
  - rewrite Heq. apply gamma_commutes_beta_aux. exact HstepM.
  - reflexivity.
Qed.

Lemma sn_reflection : forall M,
  strongly_normalizing (gamma M) -> strongly_normalizing M.
Proof.
  intros M Hsn.
  exact (sn_reflection_core (gamma M) (Acc_atomic_implies_Acc_plus (gamma M) Hsn) M eq_refl).
Qed.

Lemma gamma_commutes_typing_derivable : forall M,
  derivable M -> derivable_star (gamma M).
Proof.
  intros M [Γ [N HMN]].
  exists ([(zero_var, (sort_of 2, t_sort (sort_of 1)));
           (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var));
           (prod_var, (sort_of 1, T_prod))] ++ rho_ctx 0 Γ), (rho 0 N).
  exact (gamma_commutes_typing Γ M N HMN).
Qed.

Axiom derivable_star_implies_derivable : forall M,
  derivable_star M -> derivable M.

Definition system_strongly_normalizing (P : term -> Prop) : Prop :=
  forall M, P M -> strongly_normalizing M.

Theorem lambdaS_SN_iff_lambdaS_star_SN :
  system_strongly_normalizing derivable <-> system_strongly_normalizing derivable_star.
Proof.
  split.

  - (* λS SN -> λS∗ SN *)
    intros HSN M HMstar.
    apply HSN.
    apply derivable_star_implies_derivable.
    exact HMstar.

  - (* λS∗ SN -> λS SN *)
    intros HSNstar M HM.
    apply sn_reflection.
    apply HSNstar.
    apply gamma_commutes_typing_derivable.
    exact HM.
Qed.

End TPTS.
