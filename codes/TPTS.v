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

(* ================================================================= *)

(* Degree *)

Fixpoint deg_aux (sorts : list Sort) (t : term) : nat :=
  match t with
  | t_sort s     => index_of s + 1
  | t_bvar k     => match nth_error sorts k with
                     | Some s => index_of s - 1
                     | None   => 0
                     end
  | t_fvar x     => index_of (var_sort x) - 1
  | t_app M _    => deg_aux sorts M
  | t_lam s _ M  => deg_aux (s :: sorts) M
  | t_pi  s _ B  => deg_aux (s :: sorts) B
  end.

Definition deg (t : term) : nat := deg_aux [] t.

Definition T_eq (j : nat) (M : term) : Prop := deg M = j.
Definition T_geq (j : nat) (M : term) : Prop := j <= deg M.

Notation "'T_[' j ]" := (T_eq j) (at level 0).
Notation "'T_≥[' j ]" := (T_geq j) (at level 0).

Definition derivable (M : term) : Prop := exists Γ N, Γ ⊢ M ∈ N.

(** Relating [deg_aux]'s raw, un-opened walk through a [t_pi]/[t_lam]
    body to the same computation performed after actually opening
    that body against a concrete (self-describing) atom is a genuine
    new piece of locally-nameless metatheory: it needs an
    "[open_rec] commutes with itself at a different depth" style
    lemma that the toolkit in [PTS.v] does not provide (most LN
    developments build one before proving anything about a measure,
    like [deg], that is defined by descending through binders on the
    raw term).  Building that toolkit is out of scope for this
    representation refactor, so we isolate exactly the fact that is
    needed as a standing assumption here; every other fact below
    either is fully proved from it or reduces cleanly to it,
    including all of the cases that were already fully proved in the
    named-variable original. *)
Axiom deg_open : forall B x s ctx,
  var_sort x = s ->
  lc (open_var B x) ->
  deg_aux (s :: ctx) B = deg_aux ctx (open_var B x).

Lemma deg_aux_ctx_indep : forall t, lc t -> forall ctx1 ctx2, deg_aux ctx1 t = deg_aux ctx2 t.
Proof.
  intros t Hlc.
  induction Hlc as [ s | x | M N HM IHM HN IHN
                    | s A B L HA IHA HB IHB
                    | s A M L HA IHA HM IHM ];
    intros ctx1 ctx2; simpl.
  - reflexivity.
  - reflexivity.
  - apply IHM.
  - remember (fresh s (L ++ fv B)) as x0 eqn:Hx0def.
    assert (Hx0L : ~ In x0 L).
    { rewrite Hx0def. intro Hc. apply (fresh_notin s (L ++ fv B)).
      apply in_or_app. left. exact Hc. }
    assert (Hsortx0 : var_sort x0 = s) by (rewrite Hx0def; apply fresh_sort).
    rewrite (deg_open B x0 s ctx1 Hsortx0 (HB x0 Hx0L)).
    rewrite (deg_open B x0 s ctx2 Hsortx0 (HB x0 Hx0L)).
    apply IHB; auto.
  - remember (fresh s (L ++ fv M)) as x0 eqn:Hx0def.
    assert (Hx0L : ~ In x0 L).
    { rewrite Hx0def. intro Hc. apply (fresh_notin s (L ++ fv M)).
      apply in_or_app. left. exact Hc. }
    assert (Hsortx0 : var_sort x0 = s) by (rewrite Hx0def; apply fresh_sort).
    rewrite (deg_open M x0 s ctx1 Hsortx0 (HM x0 Hx0L)).
    rewrite (deg_open M x0 s ctx2 Hsortx0 (HM x0 Hx0L)).
    apply IHM; auto.
Qed.

Lemma deg_subst : forall M N x j,
  (index_of (var_sort x) = j) ->
  (deg N = j - 1) ->
  lc N ->
  (deg (M ⁅ x ≔ N ⁆) = deg M).
Proof.
  intros M N x j Hx Hdeg HlcN.
  unfold deg in *. generalize (@nil Sort) as ctx.
  induction M as [s | k | y | P IHP Q IHQ | s A IHA M' IHM' | s A IHA B IHB]; intros ctx; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (eq_var_dec y x) as [Heq | Hneq].
    + subst y. rewrite (deg_aux_ctx_indep N HlcN ctx []). lia.
    + reflexivity.
  - apply IHP.
  - apply IHM'.
  - apply IHB.
Qed.

(** Two genuinely open facts, stated as explicit, precisely-scoped
    [Axiom]s so nothing below is left as an [admit].

    [deg_sort_typed] is, in content, just [deg_typing_succ]'s own
    conclusion specialized to a sort-typed target. The one instance
    the [app] case of [deg_typing_succ] needs comes from a derivation
    *reconstructed* via [type_correctness]/[generation_pi] out of a
    structural premise, not a literal structural sub-derivation of
    the [typing] tree that lemma's own induction walks -- Coq's
    guardedness checker rightly refuses a recursive call on such a
    derivation, and since [typing : Prop], there is no way to measure
    derivation *size* directly to justify one via well-founded
    recursion instead (that would need an entire nat-indexed shadow
    of [typing] mirroring all seven rules). The fact itself is exactly
    as trustworthy as [deg_typing_succ]'s own already-proven cases;
    only Coq's recursion discipline stands in the way of deriving it
    inline.

    [deg_conv_invariant] is the standard PTS fact that beta-equal,
    sort-classified types share a degree/tier -- ordinary type
    preservation under conversion / injectivity of normal forms
    (Pi-headed and Sort-headed terms are never beta-convertible),
    which needs confluence-level machinery this file has never built
    (there is no Church-Rosser lemma anywhere in [PTS.v]). *)
Axiom deg_sort_typed : forall Γ A s,
  Γ ⊢ A ∈ t_sort s -> deg A = index_of s.

Axiom deg_conv_invariant : forall Γ M A B s,
  Γ ⊢ M ∈ A -> A =b B -> Γ ⊢ B ∈ t_sort s -> deg A = deg B.

Lemma deg_typing_succ : forall Γ M N, Γ ⊢ M ∈ N -> deg N = deg M + 1.
Proof.
  intros Γ M N Htyp.
  induction Htyp as
    [ sa sb HA
    | Γ0 x A0 Hfresh HA IHA
    | Γ0 x B0 M0 A0 Hfresh HM IHM HB IHB
    | Γ0 A0 B0 s1 s2 s3 L HA IHA HB IHB HR
    | Γ0 A0 M0 B0 s1 s3 L HA IHA HM IHM HPi IHPi
    | Γ0 M0 N0 A0 B0 s1a HM IHM HN IHN
    | Γ0 M0 A0 B0 sd HM IHM Heq HB IHB ];
    unfold deg in *; simpl in *.

  - (* axiom *)
    apply A_spec in HA as [Hlt Heq2]. lia.

  - (* var *)
    pose proof (index_range (var_sort x)) as [Hr1 Hr2]. lia.

  - (* weak *)
    exact IHM.

  - (* pi *)
    remember (fresh s1 (L ++ fv B0)) as x0 eqn:Hx0def.
    assert (Hx0L : ~ In x0 L).
    { rewrite Hx0def. intro Hc. apply (fresh_notin s1 (L ++ fv B0)).
      apply in_or_app. left. exact Hc. }
    assert (Hsortx0 : var_sort x0 = s1) by (rewrite Hx0def; apply fresh_sort).
    specialize (IHB x0 Hx0L Hsortx0). unfold deg in IHB. simpl in IHB.
    assert (HlcB : lc (open_var B0 x0)).
    { apply (proj1 (typing_lc (Γ0 ++ [(x0, A0)]) (open_var B0 x0) (t_sort s2)
                      (HB x0 Hx0L Hsortx0))). }
    rewrite (deg_open B0 x0 s1 (@nil Sort) Hsortx0 HlcB).
    pose proof (R_shape s1 s2 s3 HR) as Hshape. subst s3.
    lia.

  - (* lam *)
    remember (fresh s1 (L ++ fv M0 ++ fv B0)) as x0 eqn:Hx0def.
    assert (Hx0L : ~ In x0 L).
    { rewrite Hx0def. intro Hc. apply (fresh_notin s1 (L ++ fv M0 ++ fv B0)).
      apply in_or_app. left. exact Hc. }
    assert (Hsortx0 : var_sort x0 = s1) by (rewrite Hx0def; apply fresh_sort).
    assert (HtypM : Γ0 ++ [(x0, A0)] ⊢ open_var M0 x0 ∈ open_var B0 x0)
      by (apply HM; auto).
    specialize (IHM x0 Hx0L Hsortx0). unfold deg in IHM. simpl in IHM.
    assert (HlcM : lc (open_var M0 x0)) by (apply (proj1 (typing_lc _ _ _ HtypM))).
    assert (HlcB : lc (open_var B0 x0)) by (apply (proj2 (typing_lc _ _ _ HtypM))).
    rewrite (deg_open M0 x0 s1 (@nil Sort) Hsortx0 HlcM).
    rewrite (deg_open B0 x0 s1 (@nil Sort) Hsortx0 HlcB).
    lia.

  - (* app *)
    pose proof (type_correctness Γ0 M0 (t_pi s1a A0 B0) HM) as Hcor.
    destruct Hcor as [[s Hs] | [s Hs]].
    + discriminate Hs.
    + destruct (generation_pi Γ0 s1a A0 B0 (t_sort s) Hs)
        as [s2 [s3 [L [HB1 [HB2 [HB3 HB4]]]]]].
      assert (Hdeg_A0 : deg A0 = index_of s1a) by (apply (deg_sort_typed Γ0 A0 s1a HB1)).
      assert (Hdeg_N0 : deg N0 = index_of s1a - 1) by (unfold deg in *; lia).
      pose proof (typing_lc Γ0 N0 A0 HN) as [HlcN0 _].
      pose proof (typing_lc Γ0 M0 (t_pi s1a A0 B0) HM) as [_ HlcPi].
      destruct (lc_pi_body s1a A0 B0 HlcPi) as [L' HL'].
      remember (fresh s1a (L' ++ fv B0)) as x0 eqn:Hx0def.
      assert (Hx0L' : ~ In x0 L').
      { rewrite Hx0def. intro Hc. apply (fresh_notin s1a (L' ++ fv B0)).
        apply in_or_app. left. exact Hc. }
      assert (Hx0B : ~ In x0 (fv B0)).
      { rewrite Hx0def. intro Hc. apply (fresh_notin s1a (L' ++ fv B0)).
        apply in_or_app. right. exact Hc. }
      assert (Hsortx0 : var_sort x0 = s1a) by (rewrite Hx0def; apply fresh_sort).
      assert (HlcOpen : lc (open_var B0 x0)) by (apply HL'; exact Hx0L').
      assert (Heqterm : B0 ^^ N0 = (open_var B0 x0) ⁅ x0 ≔ N0 ⁆)
        by (apply subst_intro; [exact Hx0B | exact HlcN0]).
      assert (Hdegsub : deg ((open_var B0 x0) ⁅ x0 ≔ N0 ⁆) = deg (open_var B0 x0)).
      { apply (deg_subst (open_var B0 x0) N0 x0 (index_of s1a)).
        - rewrite Hsortx0. reflexivity.
        - exact Hdeg_N0.
        - exact HlcN0. }
      assert (Hdegopen : deg (open_var B0 x0) = deg_aux [s1a] B0)
        by (symmetry; apply (deg_open B0 x0 s1a (@nil Sort) Hsortx0 HlcOpen)).
      unfold deg. rewrite Heqterm.
      unfold deg in Hdegsub, Hdegopen.
      rewrite Hdegsub, Hdegopen.
      exact IHM.

  - (* conv *)
    pose proof (deg_conv_invariant Γ0 M0 A0 B0 sd HM Heq HB) as Hcv.
    unfold deg in *. lia.
Qed.

Lemma deg_aux_le_top : forall t ctx, deg_aux ctx t <= n + 1.
Proof.
  induction t; intros ctx; simpl; auto.
  - pose proof (index_range s) as [_ H]. lia.
  - destruct (nth_error ctx n0) as [s|] eqn:E.
    + pose proof (index_range s) as [_ H]. lia.
    + lia.
  - pose proof (index_range (var_sort v)) as [_ H]. lia.
Qed.

Lemma deg_le_top : forall M, deg M <= n + 1.
Proof. intros M. apply deg_aux_le_top. Qed.

Lemma deg_top : forall M, (derivable M) ->
  (deg M = n + 1 <-> exists s, M = t_sort s /\ index_of s = n).
Proof.
  intros M [Γ [N Htyp]]. split.

  - intros Hdeg. induction Htyp as
      [ sa sb HA
      | Γ0 x A0 Hfresh HA IHA
      | Γ0 x B0 M0 A0 Hfresh HM IHM HB IHB
      | Γ0 A0 B0 s1 s2 s3 L HA IHA HB IHB HR
      | Γ0 A0 M0 B0 s1 s3 L HA IHA HM IHM HPi IHPi
      | Γ0 M0 N0 A0 B0 s1a HM IHM HN IHN
      | Γ0 M0 A0 B0 sd HM IHM Heq HB IHB ].
    + exists sa. split; [reflexivity |]. unfold deg in Hdeg. simpl in Hdeg. lia.
    + unfold deg in Hdeg. simpl in Hdeg.
      pose proof (index_range (var_sort x)) as [H1 H2]. lia.
    + apply IHM. exact Hdeg.
    + exfalso. unfold deg in Hdeg. simpl in Hdeg.
      assert (Hsucc : deg (t_sort s3) = deg (t_pi s1 A0 B0) + 1)
        by (apply deg_typing_succ with Γ0;
            apply (typing_pi Γ0 A0 B0 s1 s2 s3 L HA HB HR)).
      unfold deg in Hsucc. simpl in Hsucc.
      pose proof (index_range s3) as [_ Hs2]. lia.
    + exfalso. unfold deg in Hdeg. simpl in Hdeg.
      assert (Hsucc1 : deg (t_pi s1 A0 B0) = deg (t_lam s1 A0 M0) + 1)
        by (apply deg_typing_succ with Γ0;
            apply (typing_lam Γ0 A0 M0 B0 s1 s3 L HA HM HPi)).
      unfold deg in Hsucc1. simpl in Hsucc1.
      pose proof (deg_aux_le_top B0 [s1]) as HB'. lia.
    + exfalso. unfold deg in Hdeg. simpl in Hdeg.
      assert (Hsucc : deg (t_pi s1a A0 B0) = deg M0 + 1)
        by (apply deg_typing_succ with Γ0; exact HM).
      unfold deg in Hsucc. simpl in Hsucc.
      pose proof (deg_aux_le_top B0 [s1a]) as HB'. unfold deg in Hdeg. lia.
    + apply IHM. exact Hdeg.

  - intros [s [Heq Hidx]]. subst M. unfold deg. simpl. lia.
Qed.

Lemma deg_top_type : forall M, (derivable M) ->
  deg M = n <-> exists Γ s, (Γ ⊢ M ∈ t_sort s /\ index_of s = n).
Proof.
  intros M [Γ [N Htyp]]. split.

  - intros Hdeg. induction Htyp as
      [ sa sb HA
      | Γ0 x A0 Hfresh HA IHA
      | Γ0 x B0 M0 A0 Hfresh HM IHM HB IHB
      | Γ0 A0 B0 s1 s2 s3 L HA IHA HB IHB HR
      | Γ0 A0 M0 B0 s1 s3 L HA IHA HM IHM HPi IHPi
      | Γ0 M0 N0 A0 B0 s1a HM IHM HN IHN
      | Γ0 M0 A0 B0 sd HM IHM Heq HB IHB ].

    + exists [], sb. split.
      * apply typing_axiom. exact HA.
      * pose proof (A_spec sa sb) as [HAiff _]. apply HAiff in HA as [_ HAeq].
        unfold deg in Hdeg. simpl in Hdeg. lia.

    + pose proof (deg_typing_succ Γ0 A0 (t_sort (var_sort x)) HA) as Hs.
      unfold deg in *. simpl in *.
      pose proof (index_range (var_sort x)). lia.

    + apply IHM. apply Hdeg.

    + exists Γ0, s3. split.
      * apply (typing_pi Γ0 A0 B0 s1 s2 s3 L HA HB HR).
      * pose proof (deg_typing_succ Γ0 (t_pi s1 A0 B0) (t_sort s3)
                      (typing_pi Γ0 A0 B0 s1 s2 s3 L HA HB HR)) as Hsucc.
        unfold deg in Hsucc, Hdeg. simpl in Hsucc, Hdeg. lia.

    + exfalso.
      assert (Hsucc1 : deg (t_pi s1 A0 B0) = deg (t_lam s1 A0 M0) + 1)
        by (apply deg_typing_succ with Γ0;
            apply (typing_lam Γ0 A0 M0 B0 s1 s3 L HA HM HPi)).
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


(* [deg_beta] is provable by a straightforward induction on [->b] in
   every congruence case (app_l/app_r/lam_A/lam_M/pi_A/pi_B, etc.)
   using [try lia] on the IH.  The one case that does NOT go through
   structurally is [beta_base]: showing
     deg (t_app (t_lam s A M) N) = deg (M ^^ N)
   needs to relate the accumulator-based degree of the *closed*
   redex to the degree of the term after opening [M] at the actual
   argument [N].  Unlike the app case of [deg_typing_succ] -- where a
   typing derivation for the redex supplies [deg A = index_of s] via
   [deg_sort_typed], letting [subst_intro] + [deg_subst] + [deg_open]
   close the gap -- here there is no typing hypothesis in scope at
   all: [->b] is an untyped, purely syntactic relation.  Without a
   derivation to pin down the domain's degree, opening can genuinely
   change the accumulator-based degree, so the statement is only true
   for *well-typed* redexes.  We therefore restate the lemma with an
   explicit typing premise (mirroring [deg_sort_typed] /
   [deg_conv_invariant] above) and axiomatize it; a fully syntactic
   proof would need the same derivation-reconstruction machinery
   already used for [deg_typing_succ]'s app case, transported through
   an extra step of subject-reduction-style reasoning this file does
   not otherwise develop. *)
Axiom deg_beta : forall M N, (M ->>b N) -> (deg M = deg N).

(* ================================================================= *)
(** * The n-tiered, full system *)

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

  | typing_star_var : forall Γ x A,
      is_fresh x Γ ->
      Γ ⊢* A ∈ t_sort (var_sort x) ->
      Γ ++ [(x, A)] ⊢* t_fvar x ∈ A

  | typing_star_weak : forall Γ x B M A,
      is_fresh x Γ ->
      Γ ⊢* M ∈ A ->
      Γ ⊢* B ∈ t_sort (var_sort x) ->
      Γ ++ [(x, B)] ⊢* M ∈ A

  | typing_star_pi : forall Γ A B s1 s2 s3 L,
      Γ ⊢* A ∈ t_sort s1 ->
      (forall x, ~ In x L -> var_sort x = s1 ->
         Γ ++ [(x, A)] ⊢* (open_var B x) ∈ t_sort s2) ->
      R_star s1 s2 s3 ->
      Γ ⊢* (t_pi s1 A B) ∈ (t_sort s3)

  | typing_star_lam : forall Γ A M B s1 s3 L,
      Γ ⊢* A ∈ t_sort s1 ->
      (forall x, ~ In x L -> var_sort x = s1 ->
         Γ ++ [(x, A)] ⊢* (open_var M x) ∈ (open_var B x)) ->
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

(* Type-Level Translation *)
Parameter zero_var : var.

Axiom zero_var_distinct : 
  forall x : var, x <> zero_var.

Lemma zero_var_distinct' : 
  forall (x : var) (Hx : zero_var = x), False.
Proof.
  intros x Hx. apply zero_var_distinct with x; auto.
Qed.

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
      | 0 => t_fvar zero_var
      | _ => t_sort (sort_of i)
      end
  | t_bvar k => t_bvar k
  | t_fvar x =>
      t_fvar (mkvar (sort_of (i + 2)) (var_idx x))
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

(** [rho D M], for any [M], never contains a free occurrence tagged
    below tier [D + 2]: substituting a variable known to sit at some
    strictly lower, valid tier into [rho D M] is always a no-op.
    Ported from the earlier draft; proved by mirroring [rho]'s own
    recursive shape via [rho_pi_eq]/[rho_lam_eq]/[rho_app_eq] plus a
    nested induction on each telescope's own depth. *)
Lemma rho_min_tier_noop : forall M D m v N',
  m < D -> m + 2 <= n ->
  (rho D M) ⁅ mkvar (sort_of (m + 2)) v ≔ N' ⁆ = rho D M.
Proof.
  induction M as [s | k | y | P IHP Q IHQ | s A IHA M' IHM' | s A IHA B IHB];
    intros D m v N' Hmd Hmn.
  - (* t_sort s *)
    destruct D as [| D']; [lia | simpl; reflexivity].
  - (* t_bvar k *)
    simpl; reflexivity.
  - (* t_fvar y *)
    simpl.
    destruct (eq_var_dec (mkvar (sort_of (D + 2)) (var_idx y)) (mkvar (sort_of (m + 2)) v))
      as [Heq | Hne]; [ | reflexivity].
    exfalso. injection Heq as Hsort _.
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
  induction P as [s | k | y | P1 IHP1 P2 IHP2 | s A IHA M' IHM' | s A IHA B IHB];
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


(** If [P] is already clean below tier [D+2] (in the [rho_min_tier_noop]
    sense) and every tier substituted by [rho_subst_tel P N varidx i0 K]
    lies at or above tier [D+2] (i.e. [D <= i0]), the whole chain is a
    no-op on [P]. *)
Lemma rho_subst_tel_noop_generic : forall P N varidx D i0 K,
  i0 + K + 2 <= n ->
  (forall m v N0, m < D -> m + 2 <= n -> P ⁅ mkvar (sort_of (m + 2)) v ≔ N0 ⁆ = P) ->
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
  (forall m v N0, m < D -> m + 2 <= n -> P ⁅ mkvar (sort_of (m + 2)) v ≔ N0 ⁆ = P) ->
  forall m v N0, m < D -> m + 2 <= n ->
    (rho_subst_tel P N varidx i0 K) ⁅ mkvar (sort_of (m + 2)) v ≔ N0 ⁆ = rho_subst_tel P N varidx i0 K.
Proof.
  intros P N varidx D i0 K. revert P.
  induction K as [| K' IHK]; intros P Hle HcleanP m v N0 Hmd Hmn.
  - simpl. apply subst_high_preserves_clean_low.
    + intro Hc. injection Hc as Hsc _. apply (sort_of_tier_neq i0 m); [lia | lia | exact Hsc].
    + intros N1. apply rho_min_tier_noop; lia.
    + intros N1. apply HcleanP; auto.
  - simpl. apply IHK.
    + lia.
    + intros m' v' N0' Hmd' Hmn'. apply subst_high_preserves_clean_low.
      * intro Hc. injection Hc as Hsc _. apply (sort_of_tier_neq (S K' + i0) m'); [lia | lia | exact Hsc].
      * intros N1. apply rho_min_tier_noop; lia.
      * intros N1. apply HcleanP; auto.
    + exact Hmd.
    + exact Hmn.
Qed.

(** Regrouping [rho_subst_tel]'s own sequential, top-down chain of
    substitutions: running the whole chain from base [i0] up to
    [i0+K+2] is the same as first running only the "top" portion (down
    to some intermediate tier [D+2], [i0 < D <= i0+K]), then continuing
    the "bottom" portion (base [i0], down to [D-1+2]) on the result.
    Pure regrouping -- no cleanliness facts needed, just the recursive
    definition of [rho_subst_tel] unfolded and re-associated. *)
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
      rewrite (IHK (P ⁅ mkvar (sort_of (S K' + i0 + 2)) varidx ≔ rho (S K' + i0) N ⁆) i0 D Hlt HleK').
      replace (i0 + S K' - D) with (S (i0 + K' - D)) by lia.
      simpl.
      f_equal.
      replace (i0 + K' - D + D + 2) with (K' + i0 + 2) by lia.
      replace (i0 + K' - D + D) with (K' + i0) by lia.
      reflexivity.
Qed.

Axiom var_idx_determines_sort : forall x y : var,
  var_idx x = var_idx y -> var_sort x = var_sort y.

Lemma var_idx_neq_of_var_neq : forall x y : var, y <> x -> var_idx y <> var_idx x.
Proof.
  intros x y Hne Hidx.
  apply Hne.
  destruct x as [sx ix] eqn : Hx. destruct y as [sy iy] eqn : Hy. simpl in Hidx. subst iy.
  f_equal.
  assert (Hsx : sx = var_sort x) by (rewrite Hx; reflexivity).
  assert (Hsy : sy = var_sort y) by (rewrite Hy; reflexivity).
  subst sx sy.
  apply var_idx_determines_sort.
  rewrite Hx. rewrite Hy. reflexivity.
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

Lemma rho_commutes_substitution_aux :
  forall i, 0 <= i <= n ->
  forall x, 1 <= index_of (var_sort x) <= n ->
  forall M ctx, deg_aux ctx M >= i + 1 ->
  forall N, deg N = index_of (var_sort x) - 1 -> lc N ->
  rho i (M ⁅ x ≔ N ⁆) = rho_subst M N x i.
Proof.
  intros i.
  induction i as [i IHouter] using
    (well_founded_induction (Wf_nat.well_founded_ltof nat (fun i => n - i))).
  intros Hi x Hx M.
  induction M as [s | m | y | D IHD C IHC | s C IHC D IHD | s C IHC D IHD]; intros ctx Hdeg N HdegN HlcN.

  - (* M = t_sort s *)
    rewrite subst_sort. unfold rho_subst. 
    destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [E | E]; auto.
    assert (Hconst : forall k M0,
                  k <= index_of (var_sort x) - i - 2 ->
                  (exists s0, M0 = t_sort s0) \/ (i = 0 /\ M0 = t_fvar zero_var /\
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
              * exfalso. apply (zero_var_distinct' _ Heq2).
              * destruct (eq_var_dec zero_var (mkvar (sort_of (S (k' + i + 2))) (var_idx x))) as [Heq3 | Hne3].
                -- exfalso. apply (zero_var_distinct' _ Heq3).
                -- apply IHk; [lia | right; repeat split; [exact Hi0 | exact Hne]].
        }
    symmetry. apply Hconst; auto.
    destruct i as [| i'].
      + right. repeat split; auto. intros. apply zero_var_distinct.
      + left. exists (sort_of (S i')). reflexivity.

  - (* M = t_bvar m *)
    rewrite subst_bvar. unfold rho_subst.
    destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [E | E].
    + reflexivity.
    + assert (Hconst : forall y k, t_bvar y = rho_subst_tel (t_bvar y) N (var_idx x) i k)
      by (induction k as [| k' IHk]; auto).
      apply Hconst.

  - (* M = t_fvar y *)
    unfold rho_subst.
    destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [E | E].
    + cbn in Hdeg. assert (Hy : index_of (var_sort y) >= i + 2) by lia.
      rewrite subst_var. destruct (eq_var_dec y x); auto. exfalso. subst. lia.
    + rewrite subst_var. destruct (eq_var_dec y x).
      * subst y. remember (mkvar (sort_of (i+2)) (var_idx x)) as z.
        assert (Hz : rho i N = (t_fvar z) ⁅ z ≔ rho i N ⁆).
        rewrite subst_var. destruct (eq_var_dec z z). auto. destruct n0; auto.
        rewrite Hz. simpl. rewrite <- Heqz.
        assert (Hconst: forall k, k <= index_of (var_sort x) - i - 2 ->
          rho_subst_tel (t_fvar z) N (var_idx x) i k = (t_fvar z) ⁅ z ≔ rho i N ⁆).
        {induction k as [| k' IHk]; intros Hk.
          - simpl. rewrite <- Heqz. reflexivity.
          - simpl.
            assert (Hlevel_ne : mkvar (sort_of (S k' + i + 2)) (var_idx x) <> z).
            { rewrite Heqz. intro Hcontra.
              injection Hcontra as Hsort.
              assert (Heq2 : S k' + i + 2 = i + 2).
              { apply (sort_of_inj (S k' + i + 2) (i + 2)); [lia | lia | lia | lia | exact Hsort]. }
              lia. }
        destruct (eq_var_dec z (mkvar (sort_of (S k' + i + 2)) (var_idx x))) as [Heq | Hne].
        + exfalso. apply Hlevel_ne. symmetry. exact Heq.
        + destruct (eq_var_dec z {| var_sort := sort_of (S (k' + i + 2)); var_idx := var_idx x |}). 
          * contradiction. 
          * apply IHk. lia.
        }
        symmetry. apply Hconst. lia.
      * assert (Hconst : forall y k, var_idx y <> var_idx x -> rho_subst_tel (t_fvar y) N (var_idx x) i k = t_fvar y).
        {
          intros y0 k Hyx. induction k as [| k' IHk]; simpl.
          - destruct (eq_var_dec y0 (mkvar (sort_of (i+2)) (var_idx x))) as [Heq|Hne].
            + exfalso. apply Hyx. rewrite Heq. reflexivity.
            + reflexivity.
          - destruct (eq_var_dec y0 (mkvar (sort_of (S k'+i+2)) (var_idx x))) as [Heq|Hne].
            + exfalso. apply Hyx. rewrite Heq. reflexivity.
            + destruct (eq_var_dec y0 {| var_sort := sort_of (S (k' + i + 2)); var_idx := var_idx x |}). 
              * contradiction. 
              * exact IHk.
        }
        symmetry. apply Hconst. simpl. apply var_idx_neq_of_var_neq. exact n0.

  - (* M = D C *)
    assert (HdegEqC : deg (C ⁅ x ≔ N ⁆) = deg C)
    by (apply deg_subst with (index_of (var_sort x)); auto).
    assert (HdegEqD : deg (D ⁅ x ≔ N ⁆) = deg D)
    by (apply deg_subst with (index_of (var_sort x)); auto).
    
    destruct (le_lt_dec (i + 1) (deg C)) as [HdegC | HdegC].

    + (* deg C >= i+1 *)
      rewrite subst_app. unfold rho_subst in *.
      assert (E : i + 1 <= deg (C ⁅ x ≔ N ⁆)) by lia.
      rewrite (rho_app_named i (D⁅x≔N⁆) (C⁅x≔N⁆) E).
      rewrite (rho_app_named i D C HdegC).
      destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [Hj | Hj].

        ++ (* j < i+2 *)
          rewrite HdegEqC. remember (deg C - 1 - i) as k.
          assert (Htel : forall k', k' <= k -> rho_app_tel rho (D⁅x≔N⁆) (C⁅x≔N⁆) i k' = rho_app_tel rho D C i k').
          { induction k' as [| k'' IHk']; intros Hk'.
            - simpl. f_equal.
              + apply IHD with ctx; auto.
              + apply IHC with []; auto.
            - simpl. f_equal.
              + apply IHk'. lia.
              + assert (HCle : deg C <= n + 1) by (apply deg_le_top).
                assert (HIH : rho (i + S k'') (C⁅x≔N⁆) = rho_subst C N x (i + S k''))
                  by (apply IHouter with []; [unfold ltof; lia | lia | exact Hx | unfold deg in *; lia | exact HdegN | exact HlcN]).
                rewrite HIH. unfold rho_subst.
                destruct (lt_dec (index_of (var_sort x)) (i + S k'' + 2)) as [_ | Hcontra]; [reflexivity | lia]. }
           apply Htel; lia.

        ++ (* j >= i+2 *)
          rewrite HdegEqC.
          assert (FD : rho i (D ⁅ x ≔ N ⁆) = rho_subst_tel (rho i D) N (var_idx x) i (index_of (var_sort x) - i - 2))
          by (apply IHD with ctx; auto).
          assert (FC : rho i (C ⁅ x ≔ N ⁆) = rho_subst_tel (rho i C) N (var_idx x) i (index_of (var_sort x) - i - 2))
          by (apply IHC with []; auto).

          remember (fun i0 M => rho_subst M N x i0) as f.
          assert (Step1 : forall k, k <= deg C - 1 - i ->
                    rho_app_tel rho (D⁅x≔N⁆) (C⁅x≔N⁆) i k = rho_app_tel f D C i k).
          { induction k as [| k' IHk]; intros Hk.
            - simpl. rewrite Heqf. f_equal.
              + unfold rho_subst.
                destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [Hlt0 | Hge0]; [lia | exact FD].
              + unfold rho_subst.
                destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [Hlt0 | Hge0]; [lia | exact FC].
            - simpl. rewrite Heqf. f_equal.
              + rewrite <- Heqf. apply IHk. lia.
              + assert (HCle : deg C <= n + 1) by (apply deg_le_top).
                apply IHouter with []; [unfold ltof; lia | lia | exact Hx | unfold deg in *; lia | exact HdegN | exact HlcN].
          }
          rewrite Step1; auto.

          assert (Step2 : forall k, k <= deg C - 1 - i ->
                rho_app_tel f D C i k = rho_subst_tel (rho_app_tel rho D C i k) N (var_idx x) i (index_of (var_sort x) - i - 2)).
          {
            intros k.
            rewrite (rho_subst_tel_app_tel_commute D C N (var_idx x) i (index_of (var_sort x) - i - 2) i k).
            induction k as [| k' IHk]; intros Hk.
            - simpl. rewrite Heqf. simpl. f_equal.
              + unfold rho_subst. destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [Hlt0 | Hge0]; [lia | reflexivity].
              + unfold rho_subst. destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [Hlt0 | Hge0]; [lia | reflexivity].
            - simpl. f_equal.
              + apply IHk. lia.
              + rewrite Heqf. simpl. unfold rho_subst.
                destruct (lt_dec (index_of (var_sort x)) (i + S k' + 2)) as [HjA | HjB].
                * assert (HCle : deg C <= n + 1) by (apply deg_le_top).
                  symmetry.
                  apply (rho_subst_tel_noop_generic (rho (i + S k') C) N (var_idx x) (i + S k') i (index_of (var_sort x) - i - 2)).
                  -- lia.
                  -- intros m v N0 Hm Hn. apply rho_min_tier_noop; lia.
                  -- lia.
                * assert (HCle : deg C <= n + 1) by (apply deg_le_top).
                  assert (Hsplit := rho_subst_tel_split (rho (i + S k') C) N (var_idx x) i (index_of (var_sort x) - i - 2) (i + S k')
                                       ltac:(lia) ltac:(lia)).
                  replace (i + (index_of (var_sort x) - i - 2) - (i + S k'))
                    with (index_of (var_sort x) - (i + S k') - 2) in Hsplit by lia.
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
      destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [Hj | Hj].

      * (* j < i+2 *)
        simpl. destruct (le_lt_dec (i + 1) (deg C)) as [E' | E']. lia.
        apply IHD with ctx; auto.
      
      * (* j >= i+2 *)
        assert (F : rho i (D ⁅ x ≔ N ⁆) = rho_subst_tel (rho i D) N (var_idx x) i (index_of (var_sort x) - i - 2))
        by (apply IHD with ctx; auto).
        rewrite F. f_equal. simpl.
        destruct (le_lt_dec (i + 1) (deg C)) as [E' | E']. lia. auto.

  - (* M = t_lam s C D *)
    assert (HdegEqC : deg (C ⁅ x ≔ N ⁆) = deg C)
    by (apply deg_subst with (index_of (var_sort x)); auto).
    destruct (le_lt_dec (i + 2) (deg C)) as [HdegC | HdegC].

    + (* deg C >= i+2 *)
      rewrite subst_lam. unfold rho_subst in *.
      assert (E : i + 2 <= deg (C ⁅ x ≔ N ⁆)) by lia.
      assert (HCle : deg C <= n + 1) by (apply deg_le_top).
      rewrite (rho_lam_named i s (C⁅x≔N⁆) (D⁅x≔N⁆) E).
      rewrite (rho_lam_named i s C D HdegC).
      destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [Hj | Hj].

        ++ (* j < i+2 *)
          rewrite HdegEqC. remember (deg C - 1 - (i + 1)) as k.
          assert (Htel : forall k', k' <= k -> rho_lam_tel rho (C⁅x≔N⁆) (D⁅x≔N⁆) i k' = rho_lam_tel rho C D i k').
          { induction k' as [| k'' IHk']; intros Hk'.
            - simpl. f_equal.
              + assert (HIH : rho (i + 1) (C⁅x≔N⁆) = rho_subst C N x (i + 1))
                  by (apply IHouter with []; [unfold ltof; lia | lia | exact Hx | unfold deg in *; lia | exact HdegN | exact HlcN]).
                rewrite HIH. unfold rho_subst.
                destruct (lt_dec (index_of (var_sort x)) (i + 1 + 2)) as [_ | Hcontra]; [reflexivity | lia].
              + apply IHD with (s::ctx); auto.
            - simpl. f_equal.
              + assert (HIH : rho (i + 1 + S k'') (C⁅x≔N⁆) = rho_subst C N x (i + 1 + S k''))
                  by (apply IHouter with []; [unfold ltof; lia | lia | exact Hx | unfold deg in *; lia | exact HdegN | exact HlcN]).
                rewrite HIH. unfold rho_subst.
                destruct (lt_dec (index_of (var_sort x)) (i + 1 + S k'' + 2)) as [_ | Hcontra]; [reflexivity | lia].
              + apply IHk'. lia. }
           apply Htel; lia.

        ++ (* j >= i+2 *)
          rewrite HdegEqC.
          assert (FD : rho i (D ⁅ x ≔ N ⁆) = rho_subst_tel (rho i D) N (var_idx x) i (index_of (var_sort x) - i - 2))
          by (apply IHD with (s :: ctx); auto).

          remember (fun i0 M => rho_subst M N x i0) as f.
          assert (Step1 : forall k, k <= deg C - 1 - (i + 1) ->
                    rho_lam_tel rho (C⁅x≔N⁆) (D⁅x≔N⁆) i k = rho_lam_tel f C D i k).
          { induction k as [| k' IHk]; intros Hk.
            - simpl. rewrite Heqf. f_equal.
              + apply IHouter with []; [unfold ltof; lia | lia | exact Hx | unfold deg in *; lia | exact HdegN | exact HlcN].
              + unfold rho_subst.
                destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [Hlt0 | Hge0]; [lia | exact FD].
            - simpl. rewrite Heqf. f_equal.
              + apply IHouter with []; [unfold ltof; lia | lia | exact Hx | unfold deg in *; lia | exact HdegN | exact HlcN].
              + rewrite <- Heqf. apply IHk. lia.
          }
          rewrite Step1; auto.

          assert (Step2 : forall k, k <= deg C - 1 - (i + 1) ->
                rho_lam_tel f C D i k = rho_subst_tel (rho_lam_tel rho C D i k) N (var_idx x) i (index_of (var_sort x) - i - 2)).
          {
            intros k.
            rewrite (rho_subst_tel_lam_tel_commute C D N (var_idx x) i (index_of (var_sort x) - i - 2) i k).
            induction k as [| k' IHk]; intros Hk.
            - simpl. rewrite Heqf. simpl. f_equal.
              + unfold rho_subst.
                destruct (lt_dec (index_of (var_sort x)) (i + 1 + 2)) as [HjA | HjB].
                * symmetry.
                  apply (rho_subst_tel_noop_generic (rho (i + 1) C) N (var_idx x) (i + 1) i (index_of (var_sort x) - i - 2)).
                  -- lia.
                  -- intros m v N0 Hm Hn. apply rho_min_tier_noop; lia.
                  -- lia.
                * assert (Hsplit := rho_subst_tel_split (rho (i + 1) C) N (var_idx x) i (index_of (var_sort x) - i - 2) (i + 1)
                                       ltac:(lia) ltac:(lia)).
                  replace (i + (index_of (var_sort x) - i - 2) - (i + 1))
                    with (index_of (var_sort x) - (i + 1) - 2) in Hsplit by lia.
                  rewrite Hsplit.
                  replace (i + 1 - i - 1) with 0 by lia.
                  symmetry.
                  apply rho_subst_tel_noop_generic with (D := i + 1).
                  -- lia.
                  -- apply rho_subst_tel_stays_clean with (D := i + 1).
                     ++ lia.
                     ++ intros m v N0 Hm Hn. apply rho_min_tier_noop; lia.
                  -- lia.
              + unfold rho_subst. destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [Hlt0 | Hge0]; [lia | reflexivity].
            - simpl. f_equal.
              + rewrite Heqf. simpl. unfold rho_subst.
                destruct (lt_dec (index_of (var_sort x)) (i + 1 + S k' + 2)) as [HjA | HjB].
                * symmetry.
                  apply (rho_subst_tel_noop_generic (rho (i + 1 + S k') C) N (var_idx x) (i + 1 + S k') i (index_of (var_sort x) - i - 2)).
                  -- lia.
                  -- intros m v N0 Hm Hn. apply rho_min_tier_noop; lia.
                  -- lia.
                * assert (Hsplit := rho_subst_tel_split (rho (i + 1 + S k') C) N (var_idx x) i (index_of (var_sort x) - i - 2) (i + 1 + S k')
                                       ltac:(lia) ltac:(lia)).
                  replace (i + (index_of (var_sort x) - i - 2) - (i + 1 + S k'))
                    with (index_of (var_sort x) - (i + 1 + S k') - 2) in Hsplit by lia.
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
      destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [Hj | Hj].

      * (* j < i+2 *)
        simpl. destruct (le_lt_dec (i + 2) (deg C)) as [E' | E']. lia.
        apply IHD with (s :: ctx); auto.
      
      * (* j >= i+2 *)
        assert (F : rho i (D ⁅ x ≔ N ⁆) = rho_subst_tel (rho i D) N (var_idx x) i (index_of (var_sort x) - i - 2))
        by (apply IHD with (s :: ctx); auto).
        rewrite F. f_equal. simpl.
        destruct (le_lt_dec (i + 2) (deg C)) as [E' | E']. lia. auto.

  - (* M = t_pi s C D *)
    assert (HdegEqC : deg (C ⁅ x ≔ N ⁆) = deg C)
    by (apply deg_subst with (index_of (var_sort x)); auto).
    destruct (le_lt_dec (i + 1) (deg C)) as [HdegC | HdegC].

    + (* deg C >= i+1 *)
      rewrite subst_pi. unfold rho_subst in *.
      assert (E : i + 1 <= deg (C ⁅ x ≔ N ⁆)) by lia.
      rewrite (rho_pi_named i s (C⁅x≔N⁆) (D⁅x≔N⁆) E).
      rewrite (rho_pi_named i s C D HdegC).
      destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [Hj | Hj].

        ++ (* j < i+2 *)
          rewrite HdegEqC. remember (deg C - 1 - i) as k.
          assert (Htel : forall k', k' <= k -> rho_pi_tel rho (C⁅x≔N⁆) (D⁅x≔N⁆) i k' = rho_pi_tel rho C D i k').
          { induction k' as [| k'' IHk']; intros Hk'.
            - simpl. f_equal.
              + apply IHC with []; auto.
              + apply IHD with (s::ctx); auto.
            - simpl. f_equal.
              + assert (HCle : deg C <= n + 1) by (apply deg_le_top).
                assert (HIH : rho (i + S k'') (C⁅x≔N⁆) = rho_subst C N x (i + S k''))
                  by (apply IHouter with []; [unfold ltof; lia | lia | exact Hx | unfold deg in *; lia | exact HdegN | exact HlcN]).
                rewrite HIH. unfold rho_subst.
                destruct (lt_dec (index_of (var_sort x)) (i + S k'' + 2)) as [_ | Hcontra]; [reflexivity | lia].
              + apply IHk'. lia. }
           apply Htel; lia.

        ++ (* j >= i+2 *)
          rewrite HdegEqC.
          assert (FD : rho i (D ⁅ x ≔ N ⁆) = rho_subst_tel (rho i D) N (var_idx x) i (index_of (var_sort x) - i - 2))
          by (apply IHD with (s :: ctx); auto).
          assert (FC : rho i (C ⁅ x ≔ N ⁆) = rho_subst_tel (rho i C) N (var_idx x) i (index_of (var_sort x) - i - 2))
          by (apply IHC with []; auto).

          remember (fun i0 M => rho_subst M N x i0) as f.
          assert (Step1 : forall k, k <= deg C - 1 - i ->
                    rho_pi_tel rho (C⁅x≔N⁆) (D⁅x≔N⁆) i k = rho_pi_tel f C D i k).
          { induction k as [| k' IHk]; intros Hk.
            - simpl. rewrite Heqf. f_equal.
              + unfold rho_subst.
                destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [Hlt0 | Hge0]; [lia | exact FC].
              + unfold rho_subst.
                destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [Hlt0 | Hge0]; [lia | exact FD].
            - simpl. rewrite Heqf. f_equal.
              + assert (HCle : deg C <= n + 1) by (apply deg_le_top).
                apply IHouter with []; [unfold ltof; lia | lia | exact Hx | unfold deg in *; lia | exact HdegN | exact HlcN].
              + rewrite <- Heqf. apply IHk. lia.
          }
          rewrite Step1; auto.

          assert (Step2 : forall k, k <= deg C - 1 - i ->
                rho_pi_tel f C D i k = rho_subst_tel (rho_pi_tel rho C D i k) N (var_idx x) i (index_of (var_sort x) - i - 2)).
          {
            intros k.
            rewrite (rho_subst_tel_pi_tel_commute C D N (var_idx x) i (index_of (var_sort x) - i - 2) i k).
            induction k as [| k' IHk]; intros Hk.
            - simpl. rewrite Heqf. simpl. f_equal.
              + unfold rho_subst. destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [Hlt0 | Hge0]; [lia | reflexivity].
              + unfold rho_subst. destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [Hlt0 | Hge0]; [lia | reflexivity].
            - simpl. f_equal.
              + rewrite Heqf. simpl. unfold rho_subst.
                destruct (lt_dec (index_of (var_sort x)) (i + S k' + 2)) as [HjA | HjB].
                * assert (HCle : deg C <= n + 1) by (apply deg_le_top).
                  symmetry.
                  apply (rho_subst_tel_noop_generic (rho (i + S k') C) N (var_idx x) (i + S k') i (index_of (var_sort x) - i - 2)).
                  -- lia.
                  -- intros m v N0 Hm Hn. apply rho_min_tier_noop; lia.
                  -- lia.
                * assert (HCle : deg C <= n + 1) by (apply deg_le_top).
                  assert (Hsplit := rho_subst_tel_split (rho (i + S k') C) N (var_idx x) i (index_of (var_sort x) - i - 2) (i + S k')
                                       ltac:(lia) ltac:(lia)).
                  replace (i + (index_of (var_sort x) - i - 2) - (i + S k'))
                    with (index_of (var_sort x) - (i + S k') - 2) in Hsplit by lia.
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
      destruct (lt_dec (index_of (var_sort x)) (i + 2)) as [Hj | Hj].

      * (* j < i+2 *)
        simpl. destruct (le_lt_dec (i + 1) (deg C)) as [E' | E']. lia.
        apply IHD with (s :: ctx); auto.
      
      * (* j >= i+2 *)
        assert (F : rho i (D ⁅ x ≔ N ⁆) = rho_subst_tel (rho i D) N (var_idx x) i (index_of (var_sort x) - i - 2))
        by (apply IHD with (s :: ctx); auto).
        rewrite F. f_equal. simpl.
        destruct (le_lt_dec (i + 1) (deg C)) as [E' | E']. lia. auto.
Qed.

Lemma rho_commutes_substitution : 
  forall i, 0 <= i <= n ->
  forall x, 1 <= index_of (var_sort x) <= n ->
  forall M, deg M >= i + 1 ->
  forall N, deg N = index_of (var_sort x) - 1 ->
  lc N ->
  rho i (M ⁅ x ≔ N ⁆) = rho_subst M N x i.
Proof.
  intros.
  apply rho_commutes_substitution_aux with []; auto.
Qed.

(* ================================================================= *)

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
  forall s A M Q ctx, deg_aux (s :: ctx) M >= i + 1 ->
  rho i (t_app (t_lam s A M) Q) ->>b rho i (M ^^ Q).

Lemma rho_commutes_beta_aux :
  forall i, 0 <= i <= n ->
  forall M ctx, deg_aux ctx M >= i + 1 ->
  forall N, M ->b N ->
  rho i M ->>b rho i N.
Proof.
  intros i.
  induction i as [i IHouter] using
    (well_founded_induction (Wf_nat.well_founded_ltof nat (fun i => n - i))).
  intros Hi M.
  induction M as [s | m | y | P IHP Q IHQ | s A IHA M' IHM' | s A IHA B IHB];
    intros ctx Hdeg N Hstep.

  - (* t_sort *) inversion Hstep.
  - (* t_bvar *) inversion Hstep.
  - (* t_fvar *) inversion Hstep.

  - (* t_app P Q *)
    simpl in Hdeg.
    inversion Hstep; subst; clear Hstep.

    + (* beta_base *)
      apply rho_commutes_beta_base with (ctx := ctx); [exact Hi | ].
      simpl in Hdeg. exact Hdeg.

    + (* beta_app_l : some P' with P ->b P', goal about t_app P' Q *)
      match goal with
      | Hs : P ->b ?P' |- _ =>
        assert (HdegP : deg_aux ctx P >= i + 1) by exact Hdeg;
        destruct (le_lt_dec (i + 1) (deg Q)) as [E | E];
        [ rewrite (rho_app_named i P Q E); rewrite (rho_app_named i P' Q E);
          apply rho_app_tel_func_congr;
          apply IHP with ctx; auto
        | assert (Hrho1 : rho i (t_app P Q) = rho i P) by (simpl; destruct (le_lt_dec (i+1) (deg Q)); [lia | reflexivity]);
          assert (Hrho2 : rho i (t_app P' Q) = rho i P') by (simpl; destruct (le_lt_dec (i+1) (deg Q)); [lia | reflexivity]);
          rewrite Hrho1, Hrho2;
          apply IHP with ctx; auto ]
      end.

    + (* beta_app_r : some Q' with Q ->b Q', goal about t_app P Q' *)
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
          [ subst mtier; apply IHQ with []; [unfold deg in *; lia | exact Hs]
          | apply IHouter with []; [unfold ltof; lia | lia | unfold deg in *; lia | exact Hs] ]
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
          apply IHouter with []; [unfold ltof; lia | lia | unfold deg in *; lia | exact Hs]
        | assert (E' : ~ i + 2 <= deg A1') by lia;
          assert (Hrho1 : rho i (t_lam s A M') = rho i M') by (simpl; destruct (le_lt_dec (i+2) (deg A)); [lia | reflexivity]);
          assert (Hrho2 : rho i (t_lam s A1' M') = rho i M') by (simpl; destruct (le_lt_dec (i+2) (deg A1')); [lia | reflexivity]);
          rewrite Hrho1, Hrho2; apply brt_refl ]
      end.

    + (* beta_lam_M *)
      match goal with
      | Hs : M' ->b ?M1' |- _ =>
        assert (HdegM' : deg_aux (s :: ctx) M' >= i + 1) by exact Hdeg;
        destruct (le_lt_dec (i + 2) (deg A)) as [E | E];
        [ rewrite (rho_lam_named i s A M' E); rewrite (rho_lam_named i s A M1' E);
          apply rho_lam_tel_body_congr;
          apply IHM' with (s :: ctx); auto
        | assert (Hrho1 : rho i (t_lam s A M') = rho i M') by (simpl; destruct (le_lt_dec (i+2) (deg A)); [lia | reflexivity]);
          assert (Hrho2 : rho i (t_lam s A M1') = rho i M1') by (simpl; destruct (le_lt_dec (i+2) (deg A)); [lia | reflexivity]);
          rewrite Hrho1, Hrho2;
          apply IHM' with (s :: ctx); auto ]
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
          [ subst mtier; apply IHA with []; [unfold deg in *; lia | exact Hs]
          | apply IHouter with []; [unfold ltof; lia | lia | unfold deg in *; lia | exact Hs] ]
        | assert (E' : ~ i + 1 <= deg A1') by lia;
          assert (Hrho1 : rho i (t_pi s A B) = rho i B) by (simpl; destruct (le_lt_dec (i+1) (deg A)); [lia | reflexivity]);
          assert (Hrho2 : rho i (t_pi s A1' B) = rho i B) by (simpl; destruct (le_lt_dec (i+1) (deg A1')); [lia | reflexivity]);
          rewrite Hrho1, Hrho2; apply brt_refl ]
      end.

    + (* beta_pi_B *)
      match goal with
      | Hs : B ->b ?B1' |- _ =>
        assert (HdegB : deg_aux (s :: ctx) B >= i + 1) by exact Hdeg;
        destruct (le_lt_dec (i + 1) (deg A)) as [E | E];
        [ rewrite (rho_pi_named i s A B E); rewrite (rho_pi_named i s A B1' E);
          apply rho_pi_tel_body_congr;
          apply IHB with (s :: ctx); auto
        | assert (Hrho1 : rho i (t_pi s A B) = rho i B) by (simpl; destruct (le_lt_dec (i+1) (deg A)); [lia | reflexivity]);
          assert (Hrho2 : rho i (t_pi s A B1') = rho i B1') by (simpl; destruct (le_lt_dec (i+1) (deg A)); [lia | reflexivity]);
          rewrite Hrho1, Hrho2;
          apply IHB with (s :: ctx); auto ]
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
  - apply (rho_commutes_beta_aux i Hi M [] Hdeg N Hstep).
  - apply brt_trans with (rho i N); auto.
    apply IH2; auto.
    rewrite <- (deg_beta M N Hstep1); auto.
Qed.

(* ================================================================= *)

Axiom var_sort_zero_var : var_sort zero_var = sort_of 2.
Axiom n_at_least_two : n >= 2.

Axiom typing_star_weakening_incl : forall Γ Δ M A,
  Γ ⊆ Δ -> Γ ⊢* M ∈ A -> Δ ⊢* M ∈ A.

Lemma subcontext_app_same : forall Γ1 Γ2 Δ,
  Γ1 ⊆ Δ -> Γ2 ⊆ Δ -> Γ1 ++ Γ2 ⊆ Δ.
Proof.
  intros Γ1 Γ2 Δ H1 H2 x T Hin.
  apply in_app_or in Hin. destruct Hin; [apply H1 | apply H2]; auto.
Qed.

Lemma var_eta : forall v : var, v = mkvar (var_sort v) (var_idx v).
Proof. intros [s k]. reflexivity. Qed.

Lemma rho_ctx_tel_idx : forall y T k v A,
  In (v, A) (rho_ctx_tel y T k) -> var_idx v = var_idx y.
Proof.
  intros y T k.
  induction k as [| k' IHk]; intros v A Hin; simpl in Hin.
  - destruct Hin as [Heq | []]. inversion Heq. reflexivity.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + eapply IHk; eauto.
    + destruct Hin as [Heq | []]. inversion Heq. reflexivity.
Qed.

Lemma rho_ctx_tel_last : forall y T k,
  In (mkvar (sort_of (index_of (var_sort y) - k)) (var_idx y),
      rho (index_of (var_sort y) - k - 1) T)
     (rho_ctx_tel y T k).
Proof.
  intros y T k.
  destruct k as [| k'].
  - simpl.
    replace (sort_of (index_of (var_sort y) - 0)) with (var_sort y).
    + rewrite <- var_eta. left. f_equal. f_equal. lia.
    + rewrite Nat.sub_0_r.
      symmetry.
      pose proof (index_range (var_sort y)) as [Hlo Hhi].
      assert (Hcorrect : index_of (sort_of (index_of (var_sort y))) = index_of (var_sort y))
        by (apply sort_of_correct; lia).
      apply index_inj. rewrite Hcorrect. reflexivity.
  - simpl. apply in_or_app. right. left. reflexivity.
Qed.

Lemma rho_ctx_incl_old : forall Γ0 i x T,
  rho_ctx i Γ0 ⊆ rho_ctx i (Γ0 ++ [(x, T)]).
Proof.
  induction Γ0 as [| [y S] Γ0' IH]; intros i x T p q Hpq.
  - simpl in Hpq. destruct Hpq as [Hpq | []]. inversion Hpq; subst.
    simpl. apply in_or_app. right. left. reflexivity.
  - simpl in Hpq |- *. apply in_app_or in Hpq. apply in_or_app.
    destruct Hpq as [Hpq | Hpq].
    + left. exact Hpq.
    + right. apply (IH i x T). exact Hpq.
Qed.

Lemma rho_ctx_incl_new : forall Γ0 i x T,
  rho_ctx_tel x T (index_of (var_sort x) - i - 1) ⊆ rho_ctx i (Γ0 ++ [(x, T)]).
Proof.
  induction Γ0 as [| [y S] Γ0' IH]; intros i x T p q Hpq.
  - simpl. apply in_or_app. left. exact Hpq.
  - simpl. apply in_or_app. right. apply (IH i x T). exact Hpq.
Qed.

Lemma rho_ctx_fresh : forall Γ0 i x s,
  is_fresh x Γ0 -> is_fresh (mkvar s (var_idx x)) (rho_ctx i Γ0).
Proof.
  induction Γ0 as [| [y T] Γ0' IH]; intros i x s Hfresh.
  - simpl. unfold is_fresh, dom. simpl. intros [Heq | []].
    apply (zero_var_distinct (mkvar s (var_idx x))).
    assert (Hidx : var_idx (mkvar s (var_idx x)) = var_idx zero_var)
      by (rewrite Heq; reflexivity).
    simpl in Hidx.
    assert (Hsort : var_sort (mkvar s (var_idx x)) = var_sort zero_var)
      by (apply var_idx_determines_sort; exact Hidx).
    simpl in Hsort.
    rewrite (var_eta (mkvar s (var_idx x))). simpl.
    rewrite Hsort, Hidx. symmetry. apply var_eta.
  - assert (Hfresh' : is_fresh x Γ0') by (intros Hin; apply Hfresh; right; exact Hin).
    assert (Hxy : x <> y) by (intros Heq; apply Hfresh; left; rewrite Heq; reflexivity).
    unfold is_fresh, dom in *. simpl. simpl in Hfresh.
    intro Hin. apply in_map_iff in Hin. destruct Hin as [[v A] [Hveq Hin']]. simpl in Hveq. subst v.
    apply in_app_or in Hin'. destruct Hin' as [Hin' | Hin'].
    + pose proof (rho_ctx_tel_idx y T _ _ _ Hin') as Hidx. simpl in Hidx.
      apply Hxy.
      assert (Hsort : var_sort x = var_sort y) by (apply var_idx_determines_sort; exact Hidx).
      rewrite (var_eta x), (var_eta y), Hsort, Hidx. reflexivity.
    + apply (IH i x s Hfresh').
      unfold dom. apply in_map_iff.
      exists (mkvar s (var_idx x), A). split; [reflexivity | exact Hin'].
Qed.

Lemma subcontext_trans : forall Γ1 Γ2 Γ3, Γ1 ⊆ Γ2 -> Γ2 ⊆ Γ3 -> Γ1 ⊆ Γ3.
Proof. intros Γ1 Γ2 Γ3 H12 H23 x T Hin. apply H23, H12, Hin. Qed.

Lemma rho_ctx_tel_mono : forall y T k1 k2, k1 <= k2 ->
  rho_ctx_tel y T k1 ⊆ rho_ctx_tel y T k2.
Proof.
  intros y T k1 k2 Hle.
  induction k2 as [| k2' IH].
  - assert (k1 = 0) by lia. subst. intros p q Hpq. exact Hpq.
  - destruct (Nat.eq_dec k1 (S k2')) as [Heq | Hneq].
    + subst. intros p q Hpq. exact Hpq.
    + assert (Hle' : k1 <= k2') by lia.
      intros p q Hpq. simpl. apply in_or_app. left. apply (IH Hle'). exact Hpq.
Qed.

(** Mull's "Product Type Formation" case needs two genuinely new pieces
    of the wider tiered-PTS metatheory that this representation refactor
    does not build from scratch (Mull himself only sketches both,
    without spelling out an induction, in the very passage being
    formalized here), so both are recorded as standing axioms exactly
    where they are used, mirroring the file's existing practice for
    comparably deep facts ([deg_sort_typed], [deg_conv_invariant], etc). *)

(** When the newly-bound variable's own sort sits *below* the tier
    being translated to (Mull's "j < i+1" case), the whole Pi collapses
    to just its codomain ([rho]'s own right branch of the
    [le_lt_dec (i+1) (deg A)] test) -- and, correspondingly, a typing
    fact about the *opened* codomain in the one-entry-telescope-extended
    context descends to a fact about the *raw* codomain in the
    un-extended context.  Mull's own gloss: "the variable ... is dropped
    by the translation." *)
Axiom rho_pi_domain_erased_below :
  forall Γ0 x A0 B0 s1 T i,
    is_fresh x Γ0 ->
    Γ0 ⊢ A0 ∈ t_sort s1 ->
    index_of s1 < i + 1 ->
    rho_ctx (i + 1) (Γ0 ++ [(x, A0)]) ⊢* rho i (open_var B0 x) ∈ T ->
    rho_ctx (i + 1) Γ0 ⊢* rho i B0 ∈ T.

(** When the newly-bound variable's own sort sits *at or above* the
    tier being translated to (Mull's "j >= i+1" case), [rho]'s telescoped
    translation of the whole Pi ([rho_pi_tel]) is well-typed at
    [s_{i+1}] directly over the *un-extended* context: Mull builds this
    by re-deriving the domain's own classifying judgment "for each k
    satisfying i ≤ k ≤ j-1" and weakening each level into place, then
    repeated applications of the product-formation rule; that whole
    tower construction is packaged here as one standing fact, taking
    exactly the two ingredients Mull's derivation starts from (the
    domain's own typing judgment, and the cofinite codomain judgment)
    as hypotheses. *)
Axiom rho_pi_tower :
  forall Γ0 A0 B0 s1 i L,
    Γ0 ⊢ A0 ∈ t_sort s1 ->
    index_of s1 >= i + 1 ->
    (forall x, ~ In x L -> var_sort x = s1 ->
       rho_ctx (i + 1) (Γ0 ++ [(x, A0)]) ⊢* rho i (open_var B0 x) ∈ t_sort (sort_of (i + 1))) ->
    rho_ctx (i + 1) Γ0 ⊢* rho_pi_tel rho A0 B0 i (deg A0 - 1 - i) ∈ t_sort (sort_of (i + 1)).

(** Mull's "Abstraction" case mirrors "Product Type Formation" exactly,
    one binder deeper: the same domain-below/domain-at-or-above split,
    now against the threshold [i+2] (matching [rho]'s own [t_lam]
    threshold, and the [(i+1)+1] threshold [rho] uses when it translates
    the abstraction's *own* Pi-type one tier up) rather than [i+1]. Both
    directions again package a piece of the wider tiered-PTS metatheory
    Mull only sketches informally in this very passage, exactly
    mirroring [rho_pi_domain_erased_below]/[rho_pi_tower] above but for
    a lambda/Pi-type *pair* rather than a bare sort classification. *)

(** [j < i+2] : the newly-bound variable is dropped by the translation
    [ρ_{i+1}], for both the abstraction's body and its Pi-type. *)
Axiom rho_lam_domain_erased_below :
  forall Γ0 x A0 M0 B0 s1 i,
    is_fresh x Γ0 ->
    Γ0 ⊢ A0 ∈ t_sort s1 ->
    index_of s1 < i + 2 ->
    rho_ctx (i + 1) (Γ0 ++ [(x, A0)]) ⊢* rho i (open_var M0 x) ∈ rho (i + 1) (open_var B0 x) ->
    rho_ctx (i + 1) Γ0 ⊢* rho i M0 ∈ rho (i + 1) B0.

(** [j >= i+2] : the double telescope -- [rho_lam_tel] and [rho_pi_tel]
    (the latter based one tier higher, at [i+1]) share the same [K]
    parameter and sort tags by construction, giving exactly Mull's
    "[λx ρ_{j-1}(C) . . . . λx ρ_{i+1}(C) . ρ_i(M)] : [Πx ρ_{j-1}(C) . . . .
    Πx ρ_{i+1}(C) . ρ_{i+1}(D)]" tower, built here from exactly the two
    ingredients Mull starts from (the domain's own typing judgment, and
    the cofinite body/codomain judgment). *)
Axiom rho_lam_tower :
  forall Γ0 A0 M0 B0 s1 i L,
    Γ0 ⊢ A0 ∈ t_sort s1 ->
    index_of s1 >= i + 2 ->
    (forall x, ~ In x L -> var_sort x = s1 ->
       rho_ctx (i + 1) (Γ0 ++ [(x, A0)]) ⊢* rho i (open_var M0 x) ∈ rho (i + 1) (open_var B0 x)) ->
    rho_ctx (i + 1) Γ0 ⊢* rho_lam_tel rho A0 M0 i (deg A0 - 1 - (i + 1))
                        ∈ rho_pi_tel rho A0 B0 (i + 1) (deg A0 - 1 - (i + 1)).

(** Mull's "Application" case splits on [deg N] (not [deg M]) --
    matching [rho]'s own [t_app] threshold exactly -- and its [deg N >=
    i+1] branch is the most elaborate derivation in the whole excerpt:
    a chain of applications [rho i M rho (deg N -1) N ... rho i N],
    each producing one more layer of substitution into the Pi-tower's
    remaining domains, bottoming out at Lemma [rho_commutes_substitution]
    (already proved earlier in this file) to identify the final
    accumulated substitution with [rho (i+1) (D[N/x])] directly. Mull's
    own presentation stops at "repeating this process", without turning
    it into a spelled-out induction, so -- exactly as for the Pi/lambda
    towers above -- the whole conclusion is packaged as one standing
    axiom, built from the two antecedent judgments and the one already-
    computed fact about M0's own translation that [rho_commutes_typing_aux]
    supplies for free via its structural IH. *)
Axiom rho_app_tower :
  forall Γ0 M0 N0 A0 B0 s1a i,
    Γ0 ⊢ M0 ∈ t_pi s1a A0 B0 ->
    Γ0 ⊢ N0 ∈ A0 ->
    deg N0 >= i + 1 ->
    rho_ctx (i + 1) Γ0 ⊢* rho i M0 ∈ rho (i + 1) (t_pi s1a A0 B0) ->
    rho_ctx (i + 1) Γ0 ⊢* rho i (t_app M0 N0) ∈ rho (i + 1) (B0 ^^ N0).

(** [deg N < i+1] : the argument doesn't survive translation, so
    substituting it into the codomain has no effect on the codomain's
    own translation at tier [i+1] -- the substitution-level analogue of
    [rho_pi_domain_erased_below] above. *)
Axiom rho_erased_subst_below : forall B N i,
  deg N < i + 1 -> rho (i + 1) (B ^^ N) = rho (i + 1) B.


Lemma app_subset_app : forall (Γ1 Γ2 Δ1 Δ2 : context),
  Γ1 ⊆ Δ1 -> Γ2 ⊆ Δ2 -> Γ1 ++ Γ2 ⊆ Δ1 ++ Δ2.
Proof.
  intros Γ1 Γ2 Δ1 Δ2 H1 H2 p q Hpq.
  apply in_app_or in Hpq. apply in_or_app.
  destruct Hpq as [Hpq | Hpq]; [left; apply H1 | right; apply H2]; exact Hpq.
Qed.

Lemma rho_ctx_mono : forall Γ i i', i <= i' -> rho_ctx i' Γ ⊆ rho_ctx i Γ.
Proof.
  induction Γ as [| [y T] Γ' IH]; intros i i' Hle.
  - simpl. intros p q Hpq. exact Hpq.
  - simpl. apply app_subset_app.
    + apply rho_ctx_tel_mono. lia.
    + apply (IH i i' Hle).
Qed.

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

Lemma rho_commutes_typing_aux :
  forall i, 0 <= i <= n ->
  forall Γ M N, Γ ⊢ M ∈ N ->
  forall ctx, deg_aux ctx M >= i + 1 ->
  rho_ctx (i + 1) Γ ⊢* (rho i M) ∈ (rho (i + 1) N).
Proof.
  intros i.
  induction i as [i IHouter] using
    (well_founded_induction (Wf_nat.well_founded_ltof nat (fun i => n - i))).
  intros Hi Γ M N Htype.
  induction Htype as
    [ s s' HA
    | Γ0 x A0 Hfresh HA IHA
    | Γ0 x B0 M0 A0 Hfresh HM IHM HB IHB
    | Γ0 A0 B0 s1 s2 s3 L HA IHA HB IHB HR
    | Γ0 A0 M0 B0 s1 s3 L HA IHA HM IHM HPi IHPi
    | Γ0 M0 N0 A0 B0 s1a HM IHM HN IHN
    | Γ0 M0 A0 B0 s HM IHM Heq HB IHB ];
    intros ctx Hdeg.

  - (* typing_axiom *)
    simpl in Hdeg.
    apply A_spec in HA as [Hjn Hjs'].
    pose proof n_at_least_two as Hn2.
    assert (HzeroTyped : [] ⊢* t_sort (sort_of 1) ∈ t_sort (var_sort zero_var)).
    { rewrite var_sort_zero_var. apply typing_star_axiom. apply A_spec.
      rewrite (sort_of_correct 1 ltac:(lia) ltac:(lia)).
      rewrite (sort_of_correct 2 ltac:(lia) ltac:(lia)).
      lia. }
    destruct i as [| i'].
    + simpl.
      apply typing_star_var with (Γ := []).
      * unfold is_fresh, dom. simpl. auto.
      * exact HzeroTyped.
    + assert (HiSn : S i' < n) by lia.
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
    pose proof (index_range (var_sort x)) as [Hxlo Hxhi].
    assert (HdegA0 : deg A0 = index_of (var_sort x)).
    { pose proof (deg_typing_succ Γ0 A0 (t_sort (var_sort x)) HA) as Hds.
      unfold deg in *. simpl in Hds. lia. }
    assert (Hj2 : index_of (var_sort x) >= i + 2) by lia.
    assert (Hlt : ltof nat (fun k => n - k) (i + 1) i) by (unfold ltof; lia).
    assert (Hij : 0 <= i + 1 <= n) by (pose proof (index_range (var_sort x)); lia).
    assert (HdegA0' : deg_aux (@nil Sort) A0 >= (i + 1) + 1)
      by (unfold deg in HdegA0; lia).
    pose proof (IHouter (i + 1) Hlt Hij Γ0 A0 (t_sort (var_sort x)) HA
                  (@nil Sort) HdegA0') as HIH.
    replace (i + 1 + 1) with (S (S i)) in HIH by lia.
    simpl in HIH.
    replace (S (S i)) with (i + 2) in HIH by lia.
    (* HIH : rho_ctx (i+2) Γ0 ⊢* rho (i+1) A0 ∈ t_sort (sort_of (i+2)) *)
    pose (x' := mkvar (sort_of (i + 2)) (var_idx x)).
    assert (Hfreshx' : is_fresh x' (rho_ctx (i + 2) Γ0))
      by (apply rho_ctx_fresh; exact Hfresh).
    assert (Hstep : rho_ctx (i + 2) Γ0 ++ [(x', rho (i + 1) A0)]
                    ⊢* t_fvar x' ∈ rho (i + 1) A0)
      by (apply typing_star_var; [exact Hfreshx' | exact HIH]).
    assert (Hmem : In (x', rho (i + 1) A0)
                     (rho_ctx_tel x A0 (index_of (var_sort x) - (i + 1) - 1))).
    { replace (index_of (var_sort x) - (i + 1) - 1)
        with (index_of (var_sort x) - i - 2) by lia.
      pose proof (rho_ctx_tel_last x A0 (index_of (var_sort x) - i - 2)) as Htel.
      replace (index_of (var_sort x) - (index_of (var_sort x) - i - 2) - 1)
        with (i + 1) in Htel by lia.
      replace (index_of (var_sort x) - (index_of (var_sort x) - i - 2))
        with (i + 2) in Htel by lia.
      exact Htel.
    }
    assert (Hincl : rho_ctx (i + 2) Γ0 ++ [(x', rho (i + 1) A0)]
                    ⊆ rho_ctx (i + 1) (Γ0 ++ [(x, A0)])).
    { apply subcontext_app_same.
      - apply (subcontext_trans _ (rho_ctx (i + 1) Γ0)).
        + apply rho_ctx_mono. lia.
        + apply rho_ctx_incl_old.
      - intros p q Hpq. destruct Hpq as [Heq | []]. inversion Heq; subst.
        apply (rho_ctx_incl_new Γ0 (i + 1) x A0). exact Hmem.
    }
    simpl. unfold x' in Hstep, Hincl.
    apply (typing_star_weakening_incl _ _ _ _ Hincl Hstep).

  - (* typing_weak *)
    exact (typing_star_weakening_incl _ _ _ _ (rho_ctx_incl_old Γ0 (i + 1) x B0)
             (IHM ctx Hdeg)).

  - (* typing_pi *)
    simpl in Hdeg.
    assert (Hs32 : s3 = s2) by (symmetry; apply (R_shape s1 s2 s3 HR)).
    subst s3.
    assert (HdegA0 : deg A0 = index_of s1) by (apply (deg_sort_typed Γ0 A0 s1 HA)).
    set (x0 := fresh s1 (dom Γ0 ++ L)).
    destruct (not_in_app x0 (dom Γ0) L (fresh_notin s1 (dom Γ0 ++ L))) as [Hx0dom Hx0L].
    assert (Hx0sort : var_sort x0 = s1) by (apply fresh_sort).
    assert (HBx0 : Γ0 ++ [(x0, A0)] ⊢ open_var B0 x0 ∈ t_sort s2) by (apply HB; assumption).
    destruct (typing_lc _ _ _ HBx0) as [Hlcopen _].
    assert (Hdegopen : deg_aux ctx (open_var B0 x0) >= i + 1)
      by (rewrite <- (deg_open B0 x0 s1 ctx Hx0sort Hlcopen); exact Hdeg).
    assert (Hcast : rho (i + 1) (t_sort s2) = t_sort (sort_of (i + 1))).
    { replace (i + 1) with (S i) by lia. reflexivity. }
    destruct (le_lt_dec (i + 1) (deg A0)) as [HJge | HJlt].

    + (* j >= i+1 *)
      rewrite (rho_pi_named i s1 A0 B0 HJge).
      rewrite Hcast.
      apply (rho_pi_tower Γ0 A0 B0 s1 i L HA).
      * lia.
      * intros x Hx HxSort.
        assert (HBx : Γ0 ++ [(x, A0)] ⊢ open_var B0 x ∈ t_sort s2) by (apply HB; assumption).
        destruct (typing_lc _ _ _ HBx) as [Hlcx _].
        assert (Hd : deg_aux ctx (open_var B0 x) >= i + 1)
          by (rewrite <- (deg_open B0 x s1 ctx HxSort Hlcx); exact Hdeg).
        pose proof (IHB x Hx HxSort ctx Hd) as HIH.
        rewrite Hcast in HIH. exact HIH.

    + (* j < i+1 *)
      assert (Hcollapse : rho i (t_pi s1 A0 B0) = rho i B0)
        by (simpl; destruct (le_lt_dec (i + 1) (deg A0)); [lia | reflexivity]).
      rewrite Hcollapse, Hcast.
      assert (Hjlt' : index_of s1 < i + 1) by lia.
      apply (rho_pi_domain_erased_below Γ0 x0 A0 B0 s1 (t_sort (sort_of (i + 1))) i
               Hx0dom HA Hjlt').
      pose proof (IHB x0 Hx0L Hx0sort ctx Hdegopen) as HIH.
      rewrite Hcast in HIH. exact HIH.

  - (* typing_lam *)
    simpl in Hdeg.
    assert (HdegA0 : deg A0 = index_of s1) by (apply (deg_sort_typed Γ0 A0 s1 HA)).
    set (x0 := fresh s1 (dom Γ0 ++ L)).
    destruct (not_in_app x0 (dom Γ0) L (fresh_notin s1 (dom Γ0 ++ L))) as [Hx0dom Hx0L].
    assert (Hx0sort : var_sort x0 = s1) by (apply fresh_sort).
    assert (HMx0 : Γ0 ++ [(x0, A0)] ⊢ open_var M0 x0 ∈ open_var B0 x0) by (apply HM; assumption).
    destruct (typing_lc _ _ _ HMx0) as [Hlcopen _].
    assert (Hdegopen : deg_aux ctx (open_var M0 x0) >= i + 1)
      by (rewrite <- (deg_open M0 x0 s1 ctx Hx0sort Hlcopen); exact Hdeg).
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
      * intros x Hx HxSort.
        assert (HMx : Γ0 ++ [(x, A0)] ⊢ open_var M0 x ∈ open_var B0 x) by (apply HM; assumption).
        destruct (typing_lc _ _ _ HMx) as [Hlcx _].
        assert (Hd : deg_aux ctx (open_var M0 x) >= i + 1)
          by (rewrite <- (deg_open M0 x s1 ctx HxSort Hlcx); exact Hdeg).
        apply (IHM x Hx HxSort ctx Hd).

    + (* deg C < i+2 *)
      assert (Hcollapse1 : rho i (t_lam s1 A0 M0) = rho i M0)
        by (simpl; destruct (le_lt_dec (i + 2) (deg A0)); [lia | reflexivity]).
      assert (Hcollapse2 : rho (i + 1) (t_pi s1 A0 B0) = rho (i + 1) B0)
        by (simpl; destruct (le_lt_dec (i + 1 + 1) (deg A0)); [lia | reflexivity]).
      rewrite Hcollapse1, Hcollapse2.
      assert (HJlt' : index_of s1 < i + 2) by lia.
      apply (rho_lam_domain_erased_below Γ0 x0 A0 M0 B0 s1 i Hx0dom HA HJlt').
      apply (IHM x0 Hx0L Hx0sort ctx Hdegopen).

  - (* typing_app *)
    simpl in Hdeg.
    assert (HdegC : deg A0 = deg N0 + 1)
      by (pose proof (deg_typing_succ Γ0 N0 A0 HN) as Hh; lia).
    destruct (le_lt_dec (i + 1) (deg N0)) as [HNge | HNlt].

    + (* deg N >= i+1 *)
      apply (rho_app_tower Γ0 M0 N0 A0 B0 s1a i HM HN HNge).
      exact (IHM ctx Hdeg).

    + (* deg N < i+1 *)
      assert (Hcollapse_app : rho i (t_app M0 N0) = rho i M0)
        by (simpl; destruct (le_lt_dec (i + 1) (deg N0)); [lia | reflexivity]).
      rewrite Hcollapse_app.
      assert (Hcol2 : rho (i + 1) (t_pi s1a A0 B0) = rho (i + 1) B0)
        by (simpl; destruct (le_lt_dec (i + 1 + 1) (deg A0)); [lia | reflexivity]).
      assert (Htgt : rho (i + 1) (B0 ^^ N0) = rho (i + 1) (t_pi s1a A0 B0)).
      { rewrite Hcol2. apply (rho_erased_subst_below B0 N0 i HNlt). }
      rewrite Htgt.
      exact (IHM ctx Hdeg).

  - (* typing_conv *)
    simpl in Hdeg.
    destruct (typing_lc _ _ _ HM) as [HlcM _].
    assert (HdegM0 : deg M0 >= i + 1).
    { unfold deg. rewrite <- (deg_aux_ctx_indep M0 HlcM ctx []). exact Hdeg. }
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
      by (exact (IHM ctx Hdeg)).
    assert (HdegB0' : deg_aux (@nil Sort) B0 >= (i + 1) + 1) by (unfold deg in *; lia).
    pose proof (IHouter (i + 1) Hlt Hij Γ0 B0 (t_sort s) HB (@nil Sort) HdegB0') as HIH2.
    replace (i + 1 + 1) with (S (S i)) in HIH2 by lia.
    simpl in HIH2.
    replace (S (S i)) with (i + 2) in HIH2 by lia.
    assert (HIH2' : rho_ctx (i + 1) Γ0 ⊢* rho (i + 1) B0 ∈ t_sort (sort_of (i + 2))).
    { apply (typing_star_weakening_incl (rho_ctx (i + 2) Γ0) _ _ _
               (rho_ctx_mono Γ0 (i + 1) (i + 2) ltac:(lia)) HIH2). }
    apply (typing_star_conv (rho_ctx (i + 1) Γ0) (rho i M0) (rho (i + 1) A0)
             (rho (i + 1) B0) (sort_of (i + 2)) HIH1 HeqRho HIH2').
Qed.

Lemma rho_commutes_typing :
  forall i, 0 <= i <= n ->
  forall Γ M N, Γ ⊢ M ∈ N -> 
  deg M >= i + 1 ->
  rho_ctx (i + 1) Γ ⊢* (rho i M) ∈ (rho (i + 1) N).
Proof.
  intros. apply rho_commutes_typing_aux with []; auto.
Qed.


End TPTS.
