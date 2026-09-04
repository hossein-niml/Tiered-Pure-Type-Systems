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

(** [retag x s]: rho/gamma's tiering translation needs, for a source
    atom [x], a genuinely distinct atom per [Sort] tier -- Mull's own
    presentation writes the tower of retagged variables as if they
    were literally the same atom [x] annotated by different sorts
    ([s_j x, ..., s_{i+1} x]), but that shared name is informal
    convenience: each tier is a different atom, since they all have
    to coexist as distinct bindings in one translated context. Since
    [Sort] is finite (indexed 1..n via [index_of]/[sort_of]), a plain
    multiplicative pairing on (atom, sort index) is injective and
    gives exactly that -- no need for a general pairing function. *)
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

(** No retagged atom ever lands on a bare multiple of [n+2]: [retag x s]
    is always [x*(n+2) + index_of s] with [1 <= index_of s <= n], so its
    residue mod [n+2] is never [0]. This lets the handful of reserved
    "sentinel" atoms ([zero_var], [bullet_var], [prod_var] below) be
    concrete multiples of [n+2] -- genuinely disjoint from every
    [retag]-produced atom, by construction, with no separate axiom
    needed to keep them apart from the tiering translation's own
    output. *)
Lemma retag_neq_mult : forall k x s, retag x s <> k * (n + 2).
Proof.
  intros k x s Heq. unfold retag in Heq.
  pose proof (index_range s) as [Hlo Hhi].
  assert (Hm : (x * (n + 2) + index_of s) mod (n + 2) = index_of s).
  { rewrite Nat.add_comm. rewrite Nat.mod_add by lia. apply Nat.mod_small; lia. }
  rewrite Heq in Hm.
  rewrite Nat.mod_mul in Hm by lia.
  lia.
Qed.

(* Degree *)

Fixpoint deg_aux (sorts : list Sort) (t : term) : nat :=
  match t with
  | t_sort s     => index_of s + 1
  | t_bvar k     => match nth_error sorts k with
                     | Some s => index_of s - 1
                     | None   => 0
                     end
  | t_fvar s _   => index_of s - 1
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

(** [closed_at k t] tracks exactly the de Bruijn indices that
    [deg_aux] can actually see while walking [t]: it follows the same
    spine (only the function of an application, only the body of a
    lambda/pi, never a domain or an application's argument), bumping
    the bound by one under a binder exactly where [deg_aux] pushes a
    sort onto its context and [open_rec] increments its target index.
    This makes it possible to prove the "open commutes with [deg_aux]
    at a shifted depth" fact the old [deg_open] axiom stood in for,
    by plain structural induction -- no cofinite reasoning needed
    except in [lc_closed_at] below, where it is the standard one. *)
Fixpoint closed_at (k : nat) (t : term) : Prop :=
  match t with
  | t_sort _    => True
  | t_bvar n    => n < k
  | t_fvar _ _  => True
  | t_app M _   => closed_at k M
  | t_lam _ _ M => closed_at (S k) M
  | t_pi  _ _ B => closed_at (S k) B
  end.

Lemma closed_at_open_rec_inv : forall t k u,
  closed_at k (open_rec k u t) ->
  (forall m, u <> t_bvar m) ->
  closed_at (S k) t.
Proof.
  induction t as [s0 | n | y | P IHP Q IHQ | s1 A IHA M IHM | s1 A IHA B IHB];
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
    intros m Hcontra. discriminate.
  - remember (fresh L) as x0 eqn:Hx0def.
    assert (Hx0L : ~ In x0 L) by (rewrite Hx0def; apply fresh_notin).
    specialize (IHM x0 Hx0L).
    unfold open_var in IHM.
    apply (closed_at_open_rec_inv M 0 (t_fvar s x0) IHM).
    intros m Hcontra. discriminate.
Qed.

Lemma deg_aux_open_rec_gen : forall B pre ctx0 x s,
  closed_at (S (length pre)) B ->
  deg_aux (pre ++ s :: ctx0) B = deg_aux (pre ++ ctx0) (open_rec (length pre) (t_fvar s x) B).
Proof.
  induction B as [s0 | n | y | P IHP Q IHQ | s1 A IHA M IHM | s1 A IHA B IHB];
    intros pre ctx0 x s Hclosed; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb n (length pre)) eqn:Heqb.
    + apply Nat.eqb_eq in Heqb. subst n.
      simpl.
      rewrite nth_error_app2 by lia.
      replace (length pre - length pre) with 0 by lia.
      simpl.
      reflexivity.
    + apply Nat.eqb_neq in Heqb.
      assert (Hn : n < length pre) by lia.
      simpl.
      rewrite nth_error_app1 by lia.
      rewrite nth_error_app1 by lia.
      reflexivity.
  - reflexivity.
  - apply IHP; auto.
  - apply (IHM (s1 :: pre) ctx0 x s Hclosed).
  - apply (IHB (s1 :: pre) ctx0 x s Hclosed).
Qed.

Lemma deg_open : forall B x s ctx,
  lc (open_var B s x) ->
  deg_aux (s :: ctx) B = deg_aux ctx (open_var B s x).
Proof.
  intros B x s ctx Hlc.
  pose proof (lc_closed_at _ Hlc) as Hc0.
  unfold open_var in Hc0.
  assert (Hclosed1 : closed_at 1 B).
  { apply (closed_at_open_rec_inv B 0 (t_fvar s x) Hc0).
    intros m Hcontra. discriminate. }
  pose proof (deg_aux_open_rec_gen B [] ctx x s Hclosed1) as Hgen.
  simpl in Hgen.
  unfold open_var.
  exact Hgen.
Qed.


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
  - remember (fresh (L ++ fv B)) as x0 eqn:Hx0def.
    assert (Hx0L : ~ In x0 L).
    { rewrite Hx0def. intro Hc. apply (fresh_notin (L ++ fv B)).
      apply in_or_app. left. exact Hc. }
    rewrite (deg_open B x0 s ctx1 (HB x0 Hx0L)).
    rewrite (deg_open B x0 s ctx2 (HB x0 Hx0L)).
    apply IHB; auto.
  - remember (fresh (L ++ fv M)) as x0 eqn:Hx0def.
    assert (Hx0L : ~ In x0 L).
    { rewrite Hx0def. intro Hc. apply (fresh_notin (L ++ fv M)).
      apply in_or_app. left. exact Hc. }
    rewrite (deg_open M x0 s ctx1 (HM x0 Hx0L)).
    rewrite (deg_open M x0 s ctx2 (HM x0 Hx0L)).
    apply IHM; auto.
Qed.

(** Under [var := nat], a variable's sort is no longer part of its
    own identity: two syntactic occurrences of the same atom [x] can
    in principle carry different [t_fvar] sort tags, so a fully
    general "substituting [x] never changes degree" fact (the old
    [deg_subst], stated with a single global sort for [x]) is not
    actually true any more -- it silently relied on [var_sort x]
    being position-independent by construction. What *is* still true
    unconditionally is the shape every call site here actually needs:
    opening a body at a *fresh* atom [x] (so [x] has no other,
    possibly differently-tagged occurrences to begin with) and then
    substituting that one, freshly-introduced, uniformly-tagged
    occurrence away. [deg_aux_open_rec_subst] is the substitution
    analogue of [deg_aux_open_rec_gen] above (same induction, using
    [deg_aux_ctx_indep] to relate [u]'s degree in the outer context to
    its already-known degree in the empty one), and [deg_subst_open]
    packages it together with [subst_open_var_eq] into exactly the
    "open-then-substitute" fact [deg_typing_succ] needs. *)
Lemma deg_aux_open_rec_subst : forall B pre ctx0 u s,
  closed_at (S (length pre)) B ->
  lc u ->
  deg_aux ctx0 u = index_of s - 1 ->
  deg_aux (pre ++ ctx0) (open_rec (length pre) u B) = deg_aux (pre ++ s :: ctx0) B.
Proof.
  induction B as [s0 | n | y | P IHP Q IHQ | s1 A IHA M IHM | s1 A IHA B IHB];
    intros pre ctx0 u s Hclosed Hlcu Hdegu; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb n (length pre)) eqn:Heqb.
    + apply Nat.eqb_eq in Heqb. subst n.
      simpl.
      rewrite nth_error_app2 by lia.
      replace (length pre - length pre) with 0 by lia.
      simpl.
      rewrite (deg_aux_ctx_indep u Hlcu (pre ++ ctx0) ctx0).
      exact Hdegu.
    + apply Nat.eqb_neq in Heqb.
      assert (Hn : n < length pre) by lia.
      simpl.
      rewrite nth_error_app1 by lia.
      rewrite nth_error_app1 by lia.
      reflexivity.
  - reflexivity.
  - apply IHP; auto.
  - apply (IHM (s1 :: pre) ctx0 u s Hclosed Hlcu Hdegu).
  - apply (IHB (s1 :: pre) ctx0 u s Hclosed Hlcu Hdegu).
Qed.

Lemma deg_subst_open : forall B x s N,
  ~ In x (fv B) ->
  lc (open_var B s x) ->
  lc N ->
  deg N = index_of s - 1 ->
  deg ((open_var B s x) ⁅ x ≔ N ⁆) = deg (open_var B s x).
Proof.
  intros B x s N HxB HlcOpen HlcN HdegN.
  rewrite (subst_open_var_eq B s x N HxB HlcN).
  unfold deg.
  pose proof (lc_closed_at _ HlcOpen) as Hc0.
  unfold open_var in Hc0.
  assert (Hclosed1 : closed_at 1 B).
  { apply (closed_at_open_rec_inv B 0 (t_fvar s x) Hc0).
    intros m Hcontra. discriminate. }
  pose proof (deg_aux_open_rec_subst B [] [] N s Hclosed1 HlcN HdegN) as Hgen.
  simpl in Hgen.
  rewrite Hgen.
  apply deg_open. exact HlcOpen.
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
    | Γ0 x0 A0 s0 Hfresh0 HA0 IHA0
    | Γ0 x0 B0 M0 A0 s0 Hfresh0 HM0 IHM0 HB0 IHB0
    | Γ0 A0 B0 s1 s2 s3 L HA IHA HB IHB HR
    | Γ0 A0 M0 B0 s1 s3 L HA IHA HM IHM HPi IHPi
    | Γ0 M0 N0 A0 B0 s1a HM IHM HN IHN
    | Γ0 M0 A0 B0 sd HM IHM Heq HB IHB ];
    unfold deg in *; simpl in *.

  - (* axiom *)
    apply A_spec in HA as [Hlt Heq2]. lia.

  - (* var *)
    unfold deg in IHA0. simpl in IHA0.
    pose proof (index_range s0) as [Hr1 Hr2]. lia.

  - (* weak *)
    exact IHM0.

  - (* pi *)
    remember (fresh (L ++ fv B0)) as x0 eqn:Hx0def.
    assert (Hx0L : ~ In x0 L).
    { rewrite Hx0def. intro Hc. apply (fresh_notin (L ++ fv B0)).
      apply in_or_app. left. exact Hc. }
    specialize (IHB x0 Hx0L). unfold deg in IHB. simpl in IHB.
    assert (HlcB : lc (open_var B0 s1 x0)).
    { apply (proj1 (typing_lc (Γ0 ++ [(x0, (s1, A0))]) (open_var B0 s1 x0) (t_sort s2)
                      (HB x0 Hx0L))). }
    rewrite (deg_open B0 x0 s1 (@nil Sort) HlcB).
    pose proof (R_shape s1 s2 s3 HR) as Hshape. subst s3.
    lia.

  - (* lam *)
    remember (fresh (L ++ fv M0 ++ fv B0)) as x0 eqn:Hx0def.
    assert (Hx0L : ~ In x0 L).
    { rewrite Hx0def. intro Hc. apply (fresh_notin (L ++ fv M0 ++ fv B0)).
      apply in_or_app. left. exact Hc. }
    assert (HtypM : Γ0 ++ [(x0, (s1, A0))] ⊢ open_var M0 s1 x0 ∈ open_var B0 s1 x0)
      by (apply HM; auto).
    specialize (IHM x0 Hx0L). unfold deg in IHM. simpl in IHM.
    assert (HlcM : lc (open_var M0 s1 x0)) by (apply (proj1 (typing_lc _ _ _ HtypM))).
    assert (HlcB : lc (open_var B0 s1 x0)) by (apply (proj2 (typing_lc _ _ _ HtypM))).
    rewrite (deg_open M0 x0 s1 (@nil Sort) HlcM).
    rewrite (deg_open B0 x0 s1 (@nil Sort) HlcB).
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
      remember (fresh (L' ++ fv B0)) as x0 eqn:Hx0def.
      assert (Hx0L' : ~ In x0 L').
      { rewrite Hx0def. intro Hc. apply (fresh_notin (L' ++ fv B0)).
        apply in_or_app. left. exact Hc. }
      assert (Hx0B : ~ In x0 (fv B0)).
      { rewrite Hx0def. intro Hc. apply (fresh_notin (L' ++ fv B0)).
        apply in_or_app. right. exact Hc. }
      assert (HlcOpen : lc (open_var B0 s1a x0)) by (apply HL'; exact Hx0L').
      assert (Heqterm : B0 ^^ N0 = (open_var B0 s1a x0) ⁅ x0 ≔ N0 ⁆)
        by (apply subst_intro; [exact Hx0B | exact HlcN0]).
      assert (Hdegsub : deg ((open_var B0 s1a x0) ⁅ x0 ≔ N0 ⁆) = deg (open_var B0 s1a x0))
        by (apply deg_subst_open; [exact Hx0B | exact HlcOpen | exact HlcN0 | exact Hdeg_N0]).
      assert (Hdegopen : deg (open_var B0 s1a x0) = deg_aux [s1a] B0)
        by (symmetry; apply (deg_open B0 x0 s1a (@nil Sort) HlcOpen)).
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
  induction t as [s | n0 | sv v | P IHP Q IHQ | s A IHA M IHM | s A IHA B IHB];
    intros ctx; simpl; auto.
  - pose proof (index_range s) as [_ H]. lia.
  - destruct (nth_error ctx n0) as [s|] eqn:E.
    + pose proof (index_range s) as [_ H]. lia.
    + lia.
  - pose proof (index_range sv) as [_ H]. lia.
Qed.

Lemma deg_le_top : forall M, deg M <= n + 1.
Proof. intros M. apply deg_aux_le_top. Qed.

Lemma deg_top : forall M, (derivable M) ->
  (deg M = n + 1 <-> exists s, M = t_sort s /\ index_of s = n).
Proof.
  intros M [Γ [N Htyp]]. split.

  - intros Hdeg. induction Htyp as
      [ sa sb HA
      | Γ0 x0 A0 s0 Hfresh0 HA0 IHA0
      | Γ0 x0 B0 M0 A0 s0 Hfresh0 HM0 IHM0 HB0 IHB0
      | Γ0 A0 B0 s1 s2 s3 L HA IHA HB IHB HR
      | Γ0 A0 M0 B0 s1 s3 L HA IHA HM IHM HPi IHPi
      | Γ0 M0 N0 A0 B0 s1a HM IHM HN IHN
      | Γ0 M0 A0 B0 sd HM IHM Heq HB IHB ].
    + exists sa. split; [reflexivity |]. unfold deg in Hdeg. simpl in Hdeg. lia.
    + unfold deg in Hdeg. simpl in Hdeg.
      pose proof (index_range s0) as [H1 H2]. lia.
    + apply IHM0. exact Hdeg.
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
      | Γ0 x0 A0 s0 Hfresh0 HA0 IHA0
      | Γ0 x0 B0 M0 A0 s0 Hfresh0 HM0 IHM0 HB0 IHB0
      | Γ0 A0 B0 s1 s2 s3 L HA IHA HB IHB HR
      | Γ0 A0 M0 B0 s1 s3 L HA IHA HM IHM HPi IHPi
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

(* Type-Level Translation *)
(** [zero_var]/[bullet_var]/[prod_var] (this one and the two declared
    further below) are concrete multiples of [n+2] -- by
    [retag_neq_mult] this makes them automatically disjoint from every
    atom [rho_ctx_tel]/[rho]/[gamma] ever produce via [retag], with no
    extra axiom needed to keep the translation's reserved bookkeeping
    atoms apart from its own tiered output. *)
Definition zero_var : var := 0.

(** [zero_var] (and its fellow sentinels declared further below) is a
    concrete multiple of [n+2], so it can never coincide with a
    [retag]-produced atom -- see [retag_neq_mult]. *)
Lemma zero_var_retag_ne : forall (x : var) (s : Sort),
  retag x s <> zero_var.
Proof. intros x s. unfold zero_var. apply (retag_neq_mult 0). Qed.

(** Under [var := nat], [var_idx]/[var_sort]/[mkvar] no longer exist:
    an atom no longer bundles a sort with an index, so distinctness of
    atoms is now just plain [nat] disequality, and the old
    [var_idx_determines_sort] axiom -- along with its one consumer
    below -- is entirely superseded (indeed the old axiom was only
    ever needed to recover exactly this fact from the record
    representation). *)
Lemma var_idx_neq_of_var_neq : forall x y : var, y <> x -> y <> x.
Proof. auto. Qed.

(** [zero_var] is a reserved constant standing for Mull's "bottom"
    placeholder produced by [rho] out of a sort. The natural invariant
    is not "every variable differs from [zero_var]" (that is
    self-contradictory: it is refuted by [x := zero_var]) but the
    much weaker and perfectly satisfiable fact that [zero_var] is
    disjoint from the variables actually *bound* by any well-typed
    (source, tiered) derivation: no [⊢]-derivable context ever
    chooses to bind the literal symbol [zero_var]. This is the
    standard Barendregt convention applied to this one reserved
    symbol, and it says nothing at all about [zero_var] itself, so it
    cannot be instantiated against itself the way the old axiom
    could. *)
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
  | t_bvar k => t_bvar k
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

(** Every tier -- including the atom's own, native one ([k = 0], tier
    [j]) -- gets a genuinely fresh [retag]-produced atom, never the
    bare, untagged [x] itself. This is a deliberate departure from an
    earlier draft that special-cased [k = 0] to reuse [x] unchanged
    (mirroring how the old [var := {var_sort; var_idx}] design made
    retagging *to your own sort* a no-op via [mkvar]'s record
    reconstruction, [var_eta]): under [var := nat], [retag] is
    injective and its image never contains its own first argument
    ([retag_neq_mult]-style reasoning, since [retag x s = x*(n+2) +
    index_of s > x] always), so there is no way to make the [k = 0]
    case coincide with plain [x] in general, and no need to -- [rho]'s
    own [t_fvar] case (below) retags unconditionally too, so the two
    stay in lock-step as long as both always retag. This uniformity is
    also what lets [rho_ctx_fresh] go through cleanly: every produced
    entry is [retag]-shaped, so freshness reduces directly to
    [retag_neq_of_atom_neq] with no extra bookkeeping. *)
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

(** [rho D M], for any [M], never contains a free occurrence tagged
    below tier [D + 2]: substituting a variable known to sit at some
    strictly lower, valid tier into [rho D M] is always a no-op.
    Ported from the earlier draft; proved by mirroring [rho]'s own
    recursive shape via [rho_pi_eq]/[rho_lam_eq]/[rho_app_eq] plus a
    nested induction on each telescope's own depth. *)
Lemma rho_min_tier_noop : forall M D m v N',
  m < D -> m + 2 <= n ->
  (rho D M) ⁅ retag v (sort_of (m + 2)) ≔ N' ⁆ = rho D M.
Proof.
  induction M as [s | k | sy y | P IHP Q IHQ | s A IHA M' IHM' | s A IHA B IHB];
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

(** Pure substitution algebra, no [rho]/tiers involved: substituting a
    "high" free variable [vhi] with a replacement [R] that is itself
    clean of a *different* free variable [vlo], into a term [P] that
    is already clean of [vlo], leaves the result clean of [vlo] too.
    This is the one commutation fact the [Step2] shift argument below
    needs, applied at the level of a single substitution step. *)
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
  induction P as [s | k | sy y | P1 IHP1 P2 IHP2 | s A IHA M' IHM' | s A IHA B IHB];
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

(** [only_tagged x s M] holds when every occurrence of the atom [x] in
    [M] carries the sort tag [s]. Under the old [var_sort]-baked-in
    representation a single atom automatically satisfied this
    uniformly (its sort *was* its identity), so the fully general
    "substituting [x] never changes [deg]" fact (the old [deg_subst],
    already retired above in favour of [deg_aux_open_rec_subst] /
    [deg_subst_open]) held unconditionally. Under [var := nat] two
    syntactic [t_fvar] nodes can share an atom but carry different
    tags, so that fact is false in general -- but every atom
    [rho_commutes_substitution_aux] is ever asked to eliminate is, at
    every call site that matters, introduced uniformly (e.g. by a
    single [open_var]). We package the needed uniformity explicitly as
    a hypothesis rather than mis-port the unconditional old lemma. *)
Fixpoint only_tagged (x : var) (s : Sort) (t : term) : Prop :=
  match t with
  | t_sort _    => True
  | t_bvar _    => True
  | t_fvar s0 y => y = x -> s0 = s
  | t_app P Q   => only_tagged x s P /\ only_tagged x s Q
  | t_pi _ A B  => only_tagged x s A /\ only_tagged x s B
  | t_lam _ A M => only_tagged x s A /\ only_tagged x s M
  end.

Lemma deg_aux_subst_tagged : forall C x s N ctx,
  only_tagged x s C -> lc N -> deg N = index_of s - 1 ->
  deg_aux ctx (C ⁅ x ≔ N ⁆) = deg_aux ctx C.
Proof.
  induction C as [s0 | k | s0 y | P IHP Q IHQ | s1 A IHA M IHM | s1 A IHA B IHB];
    intros x s N ctx Htag HlcN HdegN; simpl in *.
  - reflexivity.
  - reflexivity.
  - destruct (eq_var_dec y x) as [Heq | Hneq].
    + subst y. rewrite (Htag eq_refl).
      rewrite (deg_aux_ctx_indep N HlcN ctx []).
      unfold deg in HdegN. exact HdegN.
    + reflexivity.
  - destruct Htag as [HtagP _]. apply (IHP x s N ctx HtagP HlcN HdegN).
  - destruct Htag as [_ HtagM]. apply (IHM x s N (s1 :: ctx) HtagM HlcN HdegN).
  - destruct Htag as [_ HtagB]. apply (IHB x s N (s1 :: ctx) HtagB HlcN HdegN).
Qed.

(** If [P] is already clean below tier [D+2] (in the [rho_min_tier_noop]
    sense) and every tier substituted by [rho_subst_tel P N varidx i0 K]
    lies at or above tier [D+2] (i.e. [D <= i0]), the whole chain is a
    no-op on [P]. *)
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

(** If [P] is clean below tier [D+2] and [D <= i0], then the result of
    running the whole [rho_subst_tel] chain from base [i0] on [P] is
    *also* clean below tier [D+2]. *)
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

(** Regrouping [rho_subst_tel]'s own sequential, top-down chain of
    substitutions. Pure regrouping -- no cleanliness facts needed, just
    the recursive definition of [rho_subst_tel] unfolded and
    re-associated; representation-independent, ported verbatim. *)
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

(** The four lemmas below just push [rho_subst_tel] through the node
    constructors / telescope builders; entirely representation-
    independent (no atom/sort reasoning at all), ported verbatim. *)
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

(** [rho] commutes with substituting away a single, uniformly-tagged
    atom [x] (of sort [s]), turning it into the telescope-shaped
    [rho_subst]. Ported from an earlier (pre-[retag]) draft that used
    the old [var_sort]-baked-in representation throughout; the overall
    induction (well-founded on [i], then structural on [M]) and every
    telescope-bookkeeping step carry over unchanged, with [mkvar (sort
    ...) v] replaced by [retag v (sort ...)] and the old unconditional
    "[deg] is subst-invariant" fact replaced by [deg_aux_subst_tagged]
    under the explicit [only_tagged] hypothesis this representation
    actually needs (see the comment there). *)
Lemma rho_commutes_substitution_aux :
  forall i, 0 <= i <= n ->
  forall x s, x <> zero_var -> 1 <= index_of s <= n ->
  forall M ctx, deg_aux ctx M >= i + 1 -> only_tagged x s M ->
  forall N, deg N = index_of s - 1 -> lc N ->
  rho i (M ⁅ x ≔ N ⁆) = rho_subst M N x s i.
Proof.
  intros i.
  induction i as [i IHouter] using
    (well_founded_induction (Wf_nat.well_founded_ltof nat (fun i => n - i))).
  intros Hi x s Hxnz Hx M.
  induction M as [s0 | m | sy y | D IHD C IHC | s1 C IHC D IHD | s1 C IHC D IHD];
    intros ctx Hdeg Honly N HdegN HlcN.

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
    + assert (Hconst : forall y0 k, t_bvar y0 = rho_subst_tel (t_bvar y0) N x i k)
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
    by (apply (deg_aux_subst_tagged C x s N []); auto).
    assert (HdegEqD : deg (D ⁅ x ≔ N ⁆) = deg D)
    by (apply (deg_aux_subst_tagged D x s N []); auto).

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
              + apply IHD with (ctx := ctx); auto.
              + apply IHC with (ctx := []); auto.
            - simpl. f_equal.
              + apply IHk'. lia.
              + assert (HCle : deg C <= n + 1) by (apply deg_le_top).
                assert (HIH : rho (i + S k'') (C⁅x≔N⁆) = rho_subst C N x s (i + S k''))
                  by (apply IHouter with (ctx := []); [unfold ltof; lia | lia | exact Hxnz | exact Hx | unfold deg in *; lia | exact HonlyC | exact HdegN | exact HlcN]).
                rewrite HIH. unfold rho_subst.
                destruct (lt_dec (index_of s) (i + S k'' + 2)) as [_ | Hcontra]; [reflexivity | lia]. }
           apply Htel; lia.

        ++ (* j >= i+2 *)
          rewrite HdegEqC.
          assert (FD : rho i (D ⁅ x ≔ N ⁆) = rho_subst_tel (rho i D) N x i (index_of s - i - 2))
          by (apply IHD with (ctx := ctx); auto).
          assert (FC : rho i (C ⁅ x ≔ N ⁆) = rho_subst_tel (rho i C) N x i (index_of s - i - 2))
          by (apply IHC with (ctx := []); auto).

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
                apply IHouter with (ctx := []); [unfold ltof; lia | lia | exact Hxnz | exact Hx | unfold deg in *; lia | exact HonlyC | exact HdegN | exact HlcN].
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
        apply IHD with (ctx := ctx); auto.

      * (* j >= i+2 *)
        assert (F : rho i (D ⁅ x ≔ N ⁆) = rho_subst_tel (rho i D) N x i (index_of s - i - 2))
        by (apply IHD with (ctx := ctx); auto).
        rewrite F. f_equal. simpl.
        destruct (le_lt_dec (i + 1) (deg C)) as [E' | E']. lia. auto.

  - (* M = t_lam s1 C D *)
    destruct Honly as [HonlyC HonlyD].
    assert (HdegEqC : deg (C ⁅ x ≔ N ⁆) = deg C)
    by (apply (deg_aux_subst_tagged C x s N []); auto).
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
                  by (apply IHouter with (ctx := []); [unfold ltof; lia | lia | exact Hxnz | exact Hx | unfold deg in *; lia | exact HonlyC | exact HdegN | exact HlcN]).
                rewrite HIH. unfold rho_subst.
                destruct (lt_dec (index_of s) (i + 1 + 2)) as [_ | Hcontra]; [reflexivity | lia].
              + apply IHD with (ctx := s1 :: ctx); auto.
            - simpl. f_equal.
              + assert (HIH : rho (i + 1 + S k'') (C⁅x≔N⁆) = rho_subst C N x s (i + 1 + S k''))
                  by (apply IHouter with (ctx := []); [unfold ltof; lia | lia | exact Hxnz | exact Hx | unfold deg in *; lia | exact HonlyC | exact HdegN | exact HlcN]).
                rewrite HIH. unfold rho_subst.
                destruct (lt_dec (index_of s) (i + 1 + S k'' + 2)) as [_ | Hcontra]; [reflexivity | lia].
              + apply IHk'. lia. }
           apply Htel; lia.

        ++ (* j >= i+2 *)
          rewrite HdegEqC.
          assert (FD : rho i (D ⁅ x ≔ N ⁆) = rho_subst_tel (rho i D) N x i (index_of s - i - 2))
          by (apply IHD with (ctx := s1 :: ctx); auto).

          remember (fun i0 M0 => rho_subst M0 N x s i0) as f.
          assert (Step1 : forall k, k <= deg C - 1 - (i + 1) ->
                    rho_lam_tel rho (C⁅x≔N⁆) (D⁅x≔N⁆) i k = rho_lam_tel f C D i k).
          { induction k as [| k' IHk]; intros Hk.
            - simpl. rewrite Heqf. f_equal.
              + apply IHouter with (ctx := []); [unfold ltof; lia | lia | exact Hxnz | exact Hx | unfold deg in *; lia | exact HonlyC | exact HdegN | exact HlcN].
              + unfold rho_subst.
                destruct (lt_dec (index_of s) (i + 2)) as [Hlt0 | Hge0]; [lia | exact FD].
            - simpl. rewrite Heqf. f_equal.
              + apply IHouter with (ctx := []); [unfold ltof; lia | lia | exact Hxnz | exact Hx | unfold deg in *; lia | exact HonlyC | exact HdegN | exact HlcN].
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
        apply IHD with (ctx := s1 :: ctx); auto.

      * (* j >= i+2 *)
        assert (F : rho i (D ⁅ x ≔ N ⁆) = rho_subst_tel (rho i D) N x i (index_of s - i - 2))
        by (apply IHD with (ctx := s1 :: ctx); auto).
        rewrite F. f_equal. simpl.
        destruct (le_lt_dec (i + 2) (deg C)) as [E' | E']. lia. auto.

  - (* M = t_pi s1 C D *)
    destruct Honly as [HonlyC HonlyD].
    assert (HdegEqC : deg (C ⁅ x ≔ N ⁆) = deg C)
    by (apply (deg_aux_subst_tagged C x s N []); auto).
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
              + apply IHC with (ctx := []); auto.
              + apply IHD with (ctx := s1 :: ctx); auto.
            - simpl. f_equal.
              + assert (HCle : deg C <= n + 1) by (apply deg_le_top).
                assert (HIH : rho (i + S k'') (C⁅x≔N⁆) = rho_subst C N x s (i + S k''))
                  by (apply IHouter with (ctx := []); [unfold ltof; lia | lia | exact Hxnz | exact Hx | unfold deg in *; lia | exact HonlyC | exact HdegN | exact HlcN]).
                rewrite HIH. unfold rho_subst.
                destruct (lt_dec (index_of s) (i + S k'' + 2)) as [_ | Hcontra]; [reflexivity | lia].
              + apply IHk'. lia. }
           apply Htel; lia.

        ++ (* j >= i+2 *)
          rewrite HdegEqC.
          assert (FD : rho i (D ⁅ x ≔ N ⁆) = rho_subst_tel (rho i D) N x i (index_of s - i - 2))
          by (apply IHD with (ctx := s1 :: ctx); auto).
          assert (FC : rho i (C ⁅ x ≔ N ⁆) = rho_subst_tel (rho i C) N x i (index_of s - i - 2))
          by (apply IHC with (ctx := []); auto).

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
                apply IHouter with (ctx := []); [unfold ltof; lia | lia | exact Hxnz | exact Hx | unfold deg in *; lia | exact HonlyC | exact HdegN | exact HlcN].
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
        apply IHD with (ctx := s1 :: ctx); auto.

      * (* j >= i+2 *)
        assert (F : rho i (D ⁅ x ≔ N ⁆) = rho_subst_tel (rho i D) N x i (index_of s - i - 2))
        by (apply IHD with (ctx := s1 :: ctx); auto).
        rewrite F. f_equal. simpl.
        destruct (le_lt_dec (i + 1) (deg C)) as [E' | E']. lia. auto.
Qed.

Lemma rho_commutes_substitution :
  forall i, 0 <= i <= n ->
  forall x s, x <> zero_var -> 1 <= index_of s <= n ->
  forall M, deg M >= i + 1 -> only_tagged x s M ->
  forall N, deg N = index_of s - 1 ->
  lc N ->
  rho i (M ⁅ x ≔ N ⁆) = rho_subst M N x s i.
Proof.
  intros.
  apply rho_commutes_substitution_aux with (ctx := []); auto.
Qed.


(* ----------------------------------------------------------------- *)

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

(* ----------------------------------------------------------------- *)

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

(* ----------------------------------------------------------------- *)
(** [rho] commuting with the base beta rule itself,
      [rho i (t_app (t_lam s A M) Q) ->>b rho i (M ^^ Q)],
    is the one genuinely open case, for the same reason [deg_beta]
    above had to be axiomatized: [->b] is untyped and purely
    syntactic, so nothing here pins down the domain's degree or the
    local closure of [M] once opened.  A syntactic proof would go
    through [subst_intro] (turning [M ^^ Q] into a free-variable
    substitution [(open_var M x) ⁅ x ≔ Q ⁆] for a fresh [x]) and then
    [rho_commutes_substitution] (now a real [Lemma], not [Admitted] --
    see its proof above, ported against [retag] under the explicit
    [only_tagged] side condition that representation now needs) --
    exactly like the app case of [deg_typing_succ] and the comment on
    [deg_beta] describe.

    That route needs [lc (open_var M s x)], and *that* is where this
    axiom's remaining content genuinely lives: a full investigation
    (2026-09-03) traced every hypothesis available at this axiom's one
    call site, in [rho_commutes_beta_aux] below, and confirmed there is
    no [lc] or typing premise anywhere in the whole [->b]/[->>b]
    pipeline this sits in -- [rho_commutes_beta_aux], [rho_commutes_beta],
    [rho_commutes_beta_below]/[rho_commutes_beta_total], and (on the
    [gamma] side) [gamma_commutes_beta_aux]/[gamma_commutes_beta_base]/
    [gamma_commutes_beta], all the way down into the [Acc]-reflection
    argument ([sn_reflection_core]/[sn_reflection]) that Theorem 3's SN
    transfer is built from. Adding an [lc M] premise here is not a
    contained fix: [rho_commutes_beta_aux] would need it (this axiom's
    call site has no other way to supply local closure), which forces
    [rho_commutes_beta] and then [rho_commutes_beta_total] to carry it
    too, which forces [gamma_commutes_beta_aux] to carry it (it invokes
    [rho_commutes_beta_total] on arbitrary subterms with no [lc] premise
    of its own), which reaches [sn_reflection]/Theorem 3's own headline
    statement -- currently proved for *every* syntactic [M], not just
    locally-closed ones, via a pure [Acc]-reflection argument with no
    typing context in sight at all. Restricting Theorem 3 to [lc M] is
    mathematically the right fix (a non-lc term is a malformed AST, not
    a real term), but it is a materially larger undertaking than this
    one axiom -- it touches the entire untyped beta-reduction/[Acc]
    layer feeding Theorem 3, not just this base case. We isolate
    exactly this base-case content and leave it axiomatized here,
    mirroring [deg_beta] exactly, pending that dedicated follow-up. *)
Axiom rho_commutes_beta_base : forall i, 0 <= i <= n ->
  forall s A M Q ctx, deg_aux (s :: ctx) M >= i + 1 ->
  rho i (t_app (t_lam s A M) Q) ->>b rho i (M ^^ Q).

(* ----------------------------------------------------------------- *)

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

    + (* beta_app_l *)
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
(*
    [rho_ctx (i+1) []] always types [zero_var] itself: it is the
    designated placeholder [rho 0] produces out of a sort, and its own
    type sits at the very bottom of the tower.  Two standing facts
    about it are needed below and were not needed anywhere earlier in
    this file (nothing before this lemma has to type [zero_var] --
    only substitute it away or show it is never touched -- so this is
    the first place its own classification matters): its sort tag,
    and that the base system actually has at least two tiers to put
    an axiom pair (s_1, s_2) in (a 1-tiered system is a degenerate
    case the whole theory of "tiers" isn't really about; Mull's
    remark that "every full system contains the rule (s_1, s_2)"
    silently assumes this). *)
(** [var_sort_zero_var] is gone: under [var := nat], [zero_var] carries
    no intrinsic sort tag to recover -- every occurrence already
    spells its tier out explicitly as [t_fvar (sort_of 2) zero_var],
    by construction (see [zero_var]'s definition above), so nothing
    needs to be rewritten to discover that fact. *)
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

(** With [rho_ctx_tel] retagging *every* tier uniformly (including its
    own native one -- see the comment there), every entry
    [rho_ctx i Γ0] ever produces is [retag]-shaped ([rho_ctx_tel_idx]),
    so a fresh copy of [x] can only collide with one keyed by [retag y
    s'] for some [y] actually bound in [Γ0]; [retag_neq_of_atom_neq]
    then reduces that straight to [x <> y], which [is_fresh x Γ0]
    already gives. (The [zero_var] base case does not need [x <>
    zero_var] here at all -- [retag]'s image never contains
    [zero_var] regardless, by [zero_var_retag_ne] -- but the
    hypothesis is kept for symmetry with the other freshness lemmas
    that do need it.) *)
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
    | Γ0 x A0 s0 Hfresh HA IHA
    | Γ0 x B0 M0 A0 s0 Hfresh HM IHM HB IHB
    | Γ0 A0 B0 s1 s2 s3 L HA IHA HB IHB HR
    | Γ0 A0 M0 B0 s1 s3 L HA IHA HM IHM HPi IHPi
    | Γ0 M0 N0 A0 B0 s1a HM IHM HN IHN
    | Γ0 M0 A0 B0 s HM IHM Heq HB IHB ];
    intros ctx Hdeg.

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
    assert (HdegA0' : deg_aux (@nil Sort) A0 >= (i + 1) + 1)
      by (unfold deg in HdegA0; lia).
    pose proof (IHouter (i + 1) Hlt Hij Γ0 A0 (t_sort s0) HA
                  (@nil Sort) HdegA0') as HIH.
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
             (IHM ctx Hdeg)).

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
    destruct (typing_lc _ _ _ HBx0) as [Hlcopen _].
    assert (Hdegopen : deg_aux ctx (open_var B0 s1 x0) >= i + 1)
      by (rewrite <- (deg_open B0 x0 s1 ctx Hlcopen); exact Hdeg).
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
        destruct (typing_lc _ _ _ HBx) as [Hlcx _].
        assert (Hd : deg_aux ctx (open_var B0 s1 x) >= i + 1)
          by (rewrite <- (deg_open B0 x s1 ctx Hlcx); exact Hdeg).
        pose proof (IHB x Hx ctx Hd) as HIH.
        rewrite Hcast in HIH. exact HIH.

    + (* j < i+1 *)
      assert (Hcollapse : rho i (t_pi s1 A0 B0) = rho i B0)
        by (simpl; destruct (le_lt_dec (i + 1) (deg A0)); [lia | reflexivity]).
      rewrite Hcollapse, Hcast.
      assert (Hjlt' : index_of s1 < i + 1) by lia.
      apply (rho_pi_domain_erased_below Γ0 x0 A0 B0 s1 (t_sort (sort_of (i + 1))) i
               Hx0dom HA Hjlt').
      pose proof (IHB x0 Hx0L ctx Hdegopen) as HIH.
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
    destruct (typing_lc _ _ _ HMx0) as [Hlcopen _].
    assert (Hdegopen : deg_aux ctx (open_var M0 s1 x0) >= i + 1)
      by (rewrite <- (deg_open M0 x0 s1 ctx Hlcopen); exact Hdeg).
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
        destruct (typing_lc _ _ _ HMx) as [Hlcx _].
        assert (Hd : deg_aux ctx (open_var M0 s1 x) >= i + 1)
          by (rewrite <- (deg_open M0 x s1 ctx Hlcx); exact Hdeg).
        apply (IHM x Hx ctx Hd).

    + (* deg C < i+2 *)
      assert (Hcollapse1 : rho i (t_lam s1 A0 M0) = rho i M0)
        by (simpl; destruct (le_lt_dec (i + 2) (deg A0)); [lia | reflexivity]).
      assert (Hcollapse2 : rho (i + 1) (t_pi s1 A0 B0) = rho (i + 1) B0)
        by (simpl; destruct (le_lt_dec (i + 1 + 1) (deg A0)); [lia | reflexivity]).
      rewrite Hcollapse1, Hcollapse2.
      assert (HJlt' : index_of s1 < i + 2) by lia.
      apply (rho_lam_domain_erased_below Γ0 x0 A0 M0 B0 s1 i Hx0dom HA HJlt').
      apply (IHM x0 Hx0L ctx Hdegopen).

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
    (* Hdeg : deg_aux ctx M0 >= i + 1 *)
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
    (* HIH2 : rho_ctx (i+2) Γ0 ⊢* rho (i+1) B0 ∈ t_sort (sort_of (i+2)) *)
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

(* ================================================================= *)

(* Term-Level Translation *)
(* γ : T → T 0 *)

(** Like [zero_var] above, [bullet_var]/[prod_var] are concrete
    multiples of [n+2] -- distinct from each other and from
    [zero_var], and (by [retag_neq_mult]) automatically disjoint from
    every [retag]-produced atom, with no extra axiom needed. *)
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
  | t_bvar k   => t_bvar k
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

(** [bullet_var]/[prod_var]/[zero_var]'s own sorts and pairwise
    distinctness are no longer axioms: every occurrence already spells
    its sort out explicitly (e.g. [t_fvar (sort_of 1) bullet_var]), so
    there is nothing to recover via a [var_sort] projection, and
    [prod_var_ne_bullet_var]/[prod_var_ne_zero_var]/
    [bullet_var_ne_zero_var] above (concrete-multiple arithmetic) give
    pairwise distinctness outright. *)

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
       (t_pi (sort_of 1) (t_bvar 1) (t_fvar (sort_of 2) zero_var))).

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
              (t_pi (sort_of 1) (t_bvar 1) (t_fvar (sort_of 2) zero_var)))
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

(* Mull: telescope constructions for prod's Pi/lambda arguments -- taken
   as given, mirroring how the rho-side telescopes (rho_pi_tower etc.)
   are axiomatized above. *)

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

(* Mull: the final "two applications" assembling prod(piTel)(gammaA)(lamterm).
   T_prod is a fixed closed template, so this is a mechanical (if tedious)
   substitution fact; taken as given at the same trust level as the tower
   axioms above. *)
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

(* Mull: weakening by a fresh z:0, then abstraction and application to
   cancel the dummy domain back out -- taken as given, at the same trust
   level as the other assembly axioms above. *)
Axiom gamma_lam_applied :
  forall Δ0 Γ0 A0 lamTerm piType,
    Δ0 ++ rho_ctx 0 Γ0 ⊢* lamTerm ∈ piType ->
    Δ0 ++ rho_ctx 0 Γ0 ⊢* piType ∈ t_sort (sort_of 1) ->
    Δ0 ++ rho_ctx 0 Γ0 ⊢* gamma A0 ∈ t_fvar (sort_of 2) zero_var ->
    Δ0 ++ rho_ctx 0 Γ0 ⊢*
      t_app (t_lam (sort_of 1) (t_fvar (sort_of 2) zero_var) lamTerm) (gamma A0) ∈ piType.

(* Mull: application. deg N = 0 and deg N >= 1 are two sub-cases in Mull's
   own proof (the latter "similar to the same case" in rho_commutes_typing);
   gamma_app_tel's Fixpoint already covers both uniformly (k = deg N - 1
   truncates to 0 exactly when deg N = 0), so a single axiom suffices. *)
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

Lemma gamma_commutes_typing_aux :
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
    | Γ0 A0 B0 s1 s2 s3 L HA IHA HB IHB HR
    | Γ0 A0 M0 B0 s1 s3 L HA IHA HM IHM HPi IHPi
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
(** * Lemma 47: gamma commutes with substitution *)

(** [gamma_subst]/[gamma_subst_tel] and [gamma_commutes_substitution_aux]
    below are DEAD CODE relative to this file's conclusions -- exactly
    like [rho_commutes_substitution_aux] above, nothing else in this
    file (in particular not the load-bearing [gamma_commutes_typing_aux])
    ever calls them, confirmed by grepping for call sites outside their
    own definitions. Their original proofs relied throughout on the old
    [var := {| var_sort; var_idx |}] record representation, which no
    longer exists; porting is deferred for the same reason as the
    [rho]-side lemma. The statement is restated against the new
    representation (with [x]'s sort now an explicit parameter) and left
    as [Admitted]. *)
Definition gamma_subst (A B : term) (x : var) (s : Sort) : term := A.

Lemma gamma_commutes_substitution_aux :
  forall x s, x <> bullet_var -> x <> zero_var -> x <> prod_var ->
  1 <= index_of s <= n ->
  forall A B, deg B = index_of s - 1 -> lc B ->
  gamma (A ⁅ x ≔ B ⁆) = gamma_subst A B x s.
Admitted.


(* ================================================================= *)
(** * Lemma 48: gamma commutes with beta reduction *)

(* Congruence lemmas for gamma_pi_tel / gamma_lam_tel / gamma_app_tel,
   the direct analogues of rho_pi_tel_dom_congr / rho_pi_tel_body_congr
   / rho_lam_tel_dom_congr / rho_lam_tel_body_congr / rho_app_tel_
   func_congr / rho_app_tel_arg_congr above -- same proofs, transported
   to gamma's own (untiered, always-starting-at-0) telescopes. Only
   the "dom" congruences are needed for gamma_pi_tel (its body slot is
   always the constant t_fvar (sort_of 2) zero_var in every use below), while
   gamma_lam_tel needs both, since it is reused both for the Pi
   translation's third component (body = gamma of the codomain) and
   for the Lam translation's telescope (body = gamma of the term). *)

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

(* rho_commutes_beta above only applies at degree M >= i + 1, exactly
   like rho_commutes_beta_aux's own induction hypothesis. Below that
   threshold rho i already erases the finer structure of a degree-
   deficient subterm (this is the same "collapse" rho i (t_pi ...)
   exhibits via its own le_lt_dec (i+1) (deg A) branch, and is exactly
   the phenomenon rho_erased_subst_below packages for open/subst); the
   companion fact needed here -- that a beta step strictly below tier
   i + 1 still transports along rho i -- is the direct beta-reduction
   analogue of rho_erased_subst_below, and is axiomatized in the same
   spirit for the same reason. Together with rho_commutes_beta this
   gives an UNCONDITIONAL (degree-free) "rho commutes with beta" fact,
   rho_commutes_beta_total below, which is what the telescope
   congruence lemmas for Lemma 48 actually need (a telescope's j-th
   level can legitimately have deg Q < j + 1, e.g. whenever deg Q = 0
   itself, since gamma_app_tel/gamma_pi_tel/gamma_lam_tel always
   include at least the k = 0 rung). *)
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

(* ------------------------------------------------------------------- *)
(* Mull's Lemma 48 states A ->b B -> γA ↠+β γB -- a NON-empty reduction
   ("↠+β" is [beta_trans]/[->>+b], the non-reflexive transitive
   closure: only [bt_step]/[bt_trans], no reflexivity constructor),
   not the reflexive [->>b] used just below. That distinction turns
   out to be load-bearing for Theorem 3 (SN transfer): the reflection
   argument there needs an ACTUAL step on the gamma side for every
   actual step on the source side, since Acc-based strong
   normalization can't be "transported" across a simulation that is
   allowed to stall. So here we build a full parallel ->>+b congruence
   library -- direct mirrors of the brt_ lemmas already in PTS.v/above,
   using bt_step/bt_trans in place of brt_refl/brt_step/brt_trans --
   plus two "gluing" lemmas that combine one ->>b (possibly-empty) leg
   with one ->>+b (genuine) leg into an overall ->>+b, which is exactly
   the shape needed whenever only ONE of two sibling subterms is
   guaranteed to take a real step. *)

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

(* Gluing: one ->>b (possibly empty) leg + one ->>+b (genuine) leg,
   composed in either order, still gives a genuine ->>+b overall. *)
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

(* Nonempty telescope congruences, for the cases where the ONLY
   changing part is a single subterm that is already known (from the
   structural IH below) to take a genuine step -- direct ->>+b mirrors
   of gamma_app_tel_func_congr / gamma_lam_tel_body_congr above. *)
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

(* gamma commuting with the base beta rule itself,
     gamma (t_app (t_lam s A M) N) ->>+b gamma (M ^^ N),
   is the one genuinely open case, for exactly the reason
   rho_commutes_beta_base was axiomatized above: ->b is untyped and
   purely syntactic, so nothing here pins down the local closure of M
   once opened, and a syntactic proof would need to go through
   subst_intro (turning M ^^ N into a free-variable substitution
   (open_var M x) ⁅ x ≔ N ⁆ for a fresh x) together with
   gamma_commutes_substitution (Lemma 47 above) -- exactly the route
   Mull's own displayed derivation takes ("γ M [N/ s_j x] = ...") --
   but that route needs lc (open_var M x), which requires a typing (or
   at least local-closure) derivation for the redex that this untyped
   rule does not carry. We isolate exactly this base-case content,
   which is exactly Mull's explicit reduction sequence for both the
   deg N = 0 and deg N >= 1 sub-cases -- genuinely 1 or more real
   steps in both, never zero -- so stating the axiom with ->>+b (not
   just ->>b) is fully faithful to what Mull actually derives, not an
   extra assumption on top of it. Mirrors rho_commutes_beta_base's
   role exactly, just with the stronger conclusion this lemma needs. *)
Axiom gamma_commutes_beta_base : forall s A M N,
  gamma (t_app (t_lam s A M) N) ->>+b gamma (M ^^ N).

Lemma gamma_commutes_beta_aux :
  forall M N, M ->b N -> gamma M ->>+b gamma N.
Proof.
  induction M as [s | m | y | P IHP Q IHQ | s A IHA M' IHM' | s A IHA B IHB];
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
(** * Theorem 3: λS is strongly normalizing iff λS∗ is *)

(* -- SN transfer along gamma, via Acc reflection (no classical choice
      needed) --------------------------------------------------------

   Mull's own proof is classical: assume λS is not SN, extract (by
   choice) an infinite λS-derivable ->b sequence, and use Lemma 48 to
   turn it into an infinite λS∗-derivable sequence. That route would
   need constructing an actual infinite-sequence witness from the
   negation of Acc, which needs a form of (dependent/countable) choice
   this file does not otherwise use -- only propositional classical
   logic (Classical) is imported.

   Instead we prove the same content directly and constructively, by
   reflecting Acc itself backward along gamma. This works precisely
   because gamma_commutes_beta_aux gives a NON-empty step
   (gamma M ->>+b gamma N for every M ->b N) -- had it only given the
   reflexive ->>b, this argument would not go through: Acc-based SN
   cannot be transported across a simulation that is allowed to stall,
   which is exactly why Lemma 48 needed the ->>+b strengthening. *)

(* Acc under the atomic step relation implies Acc under its non-empty
   transitive closure ->>+b -- i.e. strongly_normalizing transports
   forward along ->>+b, viewed as an Acc-of-a-coarser-relation fact.
   (Coq's stdlib has this generically as Wellfounded.Transitive_
   Closure.Acc_clos_trans for clos_trans; this is the direct analogue
   for our own hand-rolled beta_trans.) *)
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

(* The reflection itself: an Acc-proof of gamma M under ->>+b unfolds,
   one gamma_commutes_beta_aux step at a time, into an Acc-proof of M
   under atomic ->b. *)
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

(* Package Lemma 46 (gamma_commutes_typing_aux) as the clean
   "derivable transports to derivable_star" statement Theorem 3 needs. *)
Lemma gamma_commutes_typing_derivable : forall M,
  derivable M -> derivable_star (gamma M).
Proof.
  intros M [Γ [N HMN]].
  exists ([(zero_var, (sort_of 2, t_sort (sort_of 1)));
           (bullet_var, (sort_of 1, t_fvar (sort_of 2) zero_var));
           (prod_var, (sort_of 1, T_prod))] ++ rho_ctx 0 Γ), (rho 0 N).
  exact (gamma_commutes_typing_aux Γ M N HMN).
Qed.

(* The other, easy half of Mull's proof ("all derivable terms of λS∗
   are also derivable in λS") is a genuinely separate fact: ⊢* is its
   own independent seven-rule PTS-style judgment (typing_star), not
   literally a sub-relation of the tiered ⊢ (typing) used elsewhere in
   this file. Proving the embedding would mean re-deriving each of
   typing_star's rules as an admissible rule of the tiered system --
   real work, orthogonal to everything gamma/rho-translation-related
   above, and (per Mull's own one-line remark, offered without proof)
   not the interesting content of this theorem. We axiomatize it in
   the same spirit as the file's other packaged facts. *)
Axiom derivable_star_implies_derivable : forall M,
  derivable_star M -> derivable M.

Definition system_strongly_normalizing (P : term -> Prop) : Prop :=
  forall M, P M -> strongly_normalizing M.

Theorem lambdaS_SN_iff_lambdaS_star_SN :
  system_strongly_normalizing derivable <-> system_strongly_normalizing derivable_star.
Proof.
  split.

  - (* λS SN -> λS∗ SN: every λS∗-derivable term is λS-derivable. *)
    intros HSN M HMstar.
    apply HSN.
    apply derivable_star_implies_derivable.
    exact HMstar.

  - (* λS∗ SN -> λS SN: translate, apply the λS∗ hypothesis, reflect
       strong normalization back through gamma. *)
    intros HSNstar M HM.
    apply sn_reflection.
    apply HSNstar.
    apply gamma_commutes_typing_derivable.
    exact HM.
Qed.

End TPTS.

