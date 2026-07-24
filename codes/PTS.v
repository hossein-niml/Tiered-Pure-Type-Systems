Require Import List.
Require Import Classical.
Import ListNotations.
From Stdlib.Program Require Import Program Wf.
Require Import Lia.

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
    let z := fresh (var_sort y) (fv N ++ fv B) in
    t_pi z (A⁅x ≔ N⁆) ((rename y z B)⁅x ≔ N⁆)

  | t_lam y A M =>
    let z := fresh (var_sort y) (fv N ++ fv M) in
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
  
  -

End PTS.
