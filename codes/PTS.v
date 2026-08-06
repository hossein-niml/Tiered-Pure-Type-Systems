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

Axiom subst_sort : forall s x N,
  (t_sort s)⁅x ≔ N⁆ = t_sort s.

Axiom subst_var : forall y x N,
  (t_var y)⁅x ≔ N⁆ = if eq_var_dec y x then N else t_var y.

Axiom subst_app : forall M1 M2 x N,
  (t_app M1 M2)⁅x ≔ N⁆ = t_app (M1⁅x ≔ N⁆) (M2⁅x ≔ N⁆).

Axiom subst_pi : forall y A B x N,
  let z := fresh (var_sort y) (fv N ++ fv B) in
  (t_pi y A B)⁅x ≔ N⁆ = t_pi z (A⁅x ≔ N⁆) ((rename y z B)⁅x ≔ N⁆).

Axiom subst_lam : forall y A M x N,
  let z := fresh (var_sort y) (fv N ++ fv M) in
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
    * rewrite Hsort. apply IHtyping1; auto.
    * admit. 
    * rewrite Hsort. apply H.

  - intros Δ HZ. rewrite subst_sort in *. rewrite subst_lam in *. rewrite subst_pi in *.
  remember (fresh (var_sort x0) (fv N ++ fv M)) as w eqn:Hw.
  remember (fresh (var_sort x0) (fv N ++ fv B)) as v eqn:Hv.
  assert (Hvw : v = w). rewrite Hw. rewrite Hv. apply fresh_eq.
  rewrite Hvw in *. apply typing_lam with s'; auto. admit.

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

Axiom A_lt_irrefl : persistent -> bounded -> forall s, ~ (s <A s).

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
      admit.
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
          subst y. apply (A_lt_irrefl Hpers Hbnd x). apply A_lt_step. exact HAxy.
        ** intros [Hlt _]. lia.
        ** intros x y z HR. destruct Hpers as [_ [_ Hshape]]. eauto.
  + (* |S| = 0 *)
    exists 0, (fun _ => 1).
    split. 
    * intros.
Admitted.


End PTS.