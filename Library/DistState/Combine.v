From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qround.
From Stdlib Require Import QArith.QArith_base.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.R_sqrt.
From Stdlib Require Import List.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ClassicalChoice.
From Stdlib Require Import ZArith.ZArith.
Import ListNotations.
Set Default Goal Selector "!".

Require Import Library.UtilityQR.
Require Import Library.DistState.CoreDef.
Require Import Library.DistState.ValidDst.
Require Import Library.DistState.Domain.
Require Import Library.DistState.Arithmetic.
Require Import Library.DistState.Partial.

Open Scope list_scope.
Open Scope R_scope.
Open Scope dstate_scope.
(************************The joint sub-distribution ⊗ **************************************************)
(************ union local_sts  ************)
Lemma union_nil_left_eq: forall s, union_state [] s = s.
Proof.
  destruct s as [| v s'];simpl; reflexivity.
Qed.
Lemma union_nil_right_eq: forall s, union_state s [] = s.
Proof.
  destruct s as [| v s'];simpl; try destruct v; reflexivity.
Qed.

Lemma union_state_comm: forall s0 s1, 
  beq_state (union_state s0 s1) (union_state s1 s0) = true.
Proof.
  intros. generalize dependent s1.
  induction s0 as [|v0 nv0 IH0]; destruct s1 as [|v1 nv1]; 
    try destruct v0; try destruct v1; simpl in *; try apply state_eq_refl; try reflexivity. 
  - destruct (q ?= q) eqn: Hv1. 
    + apply state_eq_refl. 
    + apply Qlt_alt in Hv1. apply Qlt_irrefl in Hv1. contradiction.
    + apply Qgt_alt in Hv1. apply Qlt_irrefl in Hv1. contradiction.  
  - destruct (q ?= q) eqn: Hv1. 
    + apply state_eq_refl. 
    + apply Qlt_alt in Hv1. apply Qlt_irrefl in Hv1. contradiction.
    + apply Qgt_alt in Hv1. apply Qlt_irrefl in Hv1. contradiction.
  - destruct (q ?= q) eqn: Hv1. 
    + apply IH0. 
    + apply Qlt_alt in Hv1. apply Qlt_irrefl in Hv1. contradiction.
    + apply Qgt_alt in Hv1. apply Qlt_irrefl in Hv1. contradiction.
  - destruct (q ?= q) eqn: Hv1. 
    + apply IH0. 
    + apply Qlt_alt in Hv1. apply Qlt_irrefl in Hv1. contradiction.
    + apply Qgt_alt in Hv1. apply Qlt_irrefl in Hv1. contradiction.
  - apply IH0.
Qed.

Lemma union_default_left_eq: forall s0 s1, 
  st_all_none s1 = true ->
  beq_state s0 (union_state s1 s0) = true.
Proof.
  intros. generalize dependent s1.
  induction s0 as [|v0 s0' IH]; destruct s1 as [|v1 s1']; intros; 
    try destruct v0; try destruct v1; simpl in *; 
      try apply state_eq_refl; try reflexivity; try discriminate; try assumption. 
  - destruct (q ?= q) eqn: H'. 
    * apply state_eq_refl.
    * apply Qlt_alt in H'. apply Qlt_irrefl in H'. contradiction.
    * apply Qgt_alt in H'. apply Qlt_irrefl in H'. contradiction.
  - destruct (q ?= q) eqn: H'. 
    * apply IH. assumption.
    * apply Qlt_alt in H'. apply Qlt_irrefl in H'. contradiction.
    * apply Qgt_alt in H'. apply Qlt_irrefl in H'. contradiction.
  - apply IH. assumption.
Qed.

Lemma union_state_eq_compat_r: forall s0 s1 s, 
  beq_state s0 s1 = true -> 
  beq_state (union_state s0 s) (union_state s1 s) = true.
Proof.
  intros. generalize dependent s1. generalize dependent s0.
  induction s as [|v s' IHs]; destruct s0 as [|v0 s0']; destruct s1 as [|v1 s1']; intros; 
    try destruct v; try destruct v0; try destruct v1; simpl in *; 
      try apply state_eq_refl; try reflexivity; try discriminate; try assumption. 
  - destruct (q ?= q) eqn: H'. 
    + apply state_eq_refl.
    + apply Qlt_alt in H'. apply Qlt_irrefl in H'. contradiction.
    + apply Qgt_alt in H'. apply Qlt_irrefl in H'. contradiction.
  - destruct (q ?= q) eqn: H'. 
    + apply union_default_left_eq. assumption.
    + apply Qlt_alt in H'. apply Qlt_irrefl in H'. contradiction.
    + apply Qgt_alt in H'. apply Qlt_irrefl in H'. contradiction.
  - apply union_default_left_eq. assumption.
  - destruct (q ?= q) eqn: H'.  
    + simpl. rewrite state_eq_sym. apply union_default_left_eq. assumption.
    + apply Qlt_alt in H'. apply Qlt_irrefl in H'. contradiction.
    + apply Qgt_alt in H'. apply Qlt_irrefl in H'. contradiction.
  - rewrite state_eq_sym. apply union_default_left_eq. assumption.
  - destruct (q ?= q) eqn: H'. 
    + apply IHs. assumption.
    + apply Qlt_alt in H'. apply Qlt_irrefl in H'. contradiction.
    + apply Qgt_alt in H'. apply Qlt_irrefl in H'. contradiction.
  - destruct (q ?= q0) eqn: Hv01; try discriminate.  
    apply IHs; try assumption.
  - apply IHs. assumption.
Qed.

Lemma union_state_assoc: forall s0 s1 s2, 
  is_domain_intersect (return_domain s0) (return_domain s1) = false ->
  is_domain_intersect (return_domain s0) (return_domain s2) = false ->
  is_domain_intersect (return_domain s1) (return_domain s2) = false ->
  beq_state (union_state s0 (union_state s1 s2)) 
            (union_state (union_state s0 s1) s2) = true.
Proof.
  intros. generalize dependent s2. generalize dependent s1.
  induction s0 as [|v0 s0']; destruct s1 as [|v1 s1']; destruct s2 as [|v2 s2']; intros.
  - simpl. reflexivity. 
  - simpl. destruct v2; simpl in *; try apply state_eq_refl.
    destruct (q ?= q) eqn: Hv2. 
    + apply state_eq_refl.
    + apply Qlt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
    + apply Qgt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.  
  - simpl. destruct v1; simpl in *; try apply state_eq_refl. 
    destruct (q ?= q) eqn: Hv2. 
    + apply state_eq_refl.
    + apply Qlt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
    + apply Qgt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.  
  - destruct v1; destruct v2; simpl in *; try apply state_eq_refl; try reflexivity.
    * destruct (q ?= q) eqn: Hv2. 
      + apply state_eq_refl.
      + apply Qlt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
      + apply Qgt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
    *  destruct (q ?= q) eqn: Hv2. 
      + apply state_eq_refl.
      + apply Qlt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
      + apply Qgt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
  - destruct v0; simpl in *; try apply state_eq_refl. 
    destruct (q ?= q) eqn: Hv2. 
    + apply state_eq_refl.
    + apply Qlt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
    + apply Qgt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
  - destruct v0; destruct v2; simpl in *; try apply state_eq_refl; try reflexivity.
    * destruct (q ?= q) eqn: Hv2. 
      + apply state_eq_refl.
      + apply Qlt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
      + apply Qgt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
    *  destruct (q ?= q) eqn: Hv2. 
      + apply state_eq_refl.
      + apply Qlt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
      + apply Qgt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
  - destruct v0; destruct v1; simpl in *; try apply state_eq_refl; try reflexivity.
    * destruct (q ?= q) eqn: Hv2. 
      + apply state_eq_refl.
      + apply Qlt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
      + apply Qgt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
    *  destruct (q ?= q) eqn: Hv2. 
      + apply state_eq_refl.
      + apply Qlt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
      + apply Qgt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
  - destruct v0; destruct v1; destruct v2; simpl in *; 
      try apply state_eq_refl; try reflexivity; try discriminate.
    * destruct (q ?= q) eqn: Hv2. 
      + apply IHs0'; assumption.
      + apply Qlt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
      + apply Qgt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
    * destruct (q ?= q) eqn: Hv2. 
      + apply IHs0'; assumption.
      + apply Qlt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
      + apply Qgt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
    * destruct (q ?= q) eqn: Hv2.
      + apply IHs0'; assumption.
      + apply Qlt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
      + apply Qgt_alt in Hv2. apply Qlt_irrefl in Hv2. contradiction.
    * apply IHs0'; assumption.
Qed.

Lemma union_eq_orb_dom: forall s1 s2, (*union_eq_orb*)
  is_domain_intersect (return_domain s1) (return_domain s2) = false ->
  (orb_domain (return_domain s1) (return_domain s2) == return_domain (union_state s1 s2))%domain. 
Proof.
  intros. generalize dependent s2. 
  induction s1 as [|v1 s1' IH]; intros; destruct s2 as [|v2 s2']; 
    try destruct v1; try destruct v2; simpl in *; try apply dom_equiv_refl; try discriminate.
  - apply IH in H. destruct H. split; simpl; try assumption.
  - apply IH in H. destruct H. split; simpl; try assumption.
  - apply IH in H. destruct H. split; simpl; try assumption.
Qed.

(***********The properties of the combination operation of partial dist_state. ********************************************)
Lemma combine_nil_r_eq: forall mu, mu ⊗ [] = [].
Proof.
  intros.
  induction mu as [|(s,p) mu' Hmu]; simpl.
  - reflexivity.
  - apply Hmu.
Qed.
Lemma combine_cons_l_distr_eq: forall s p mu mu1, 
  ((s, p) :: mu) ⊗ mu1 = ([(s, p)] ⊗ mu1) + (mu ⊗ mu1).
Proof.
  intros. unfold combine_dst at 1. fold combine_dst. unfold add_dist.
  f_equal. simpl. rewrite app_nil_r. reflexivity.
Qed.
Lemma combine_onest_cons_distr_eq: forall s0 p0 s1 p1 mu,
  [(s0, p0)] ⊗ ((s1, p1) :: mu) = 
  [(union_state s0 s1, (p0 * p1)%R)] + ([(s0, p0)] ⊗ mu).
Proof.
  intros. simpl. rewrite app_nil_r. simpl. f_equal. 
Qed.

Lemma combine_add_distr_l_eq: forall mu1 mu2 mu3,
  (mu1 + mu2) ⊗ mu3 = (mu1 ⊗ mu3) + (mu2 ⊗ mu3).
Proof.
  intros. generalize dependent mu3. generalize dependent mu2.
  induction mu1 as [|(s, p) mu1' Hmu1].
  - simpl. intros. reflexivity.
  - intros. specialize (Hmu1 mu2 mu3).
  replace (((s, p) :: mu1') + mu2) with ((s, p) :: (mu1' + mu2)) by reflexivity.
  rewrite combine_cons_l_distr_eq. rewrite combine_cons_l_distr_eq with (mu:= mu1').
  rewrite Hmu1. apply dst_add_assoc_eq.
Qed. 

Lemma combine_onest_mult_coef_eq: forall s0 p0 p mu,
  p <> 0 ->
  [(s0, (p * p0)%R)] ⊗ mu = p * ([(s0, p0)] ⊗ mu).
Proof.
  intros. induction mu as [|(s1, p1) mu1 Hmu1].
  - simpl. intros. reflexivity.
  - rewrite combine_onest_cons_distr_eq. 
  simpl. destruct (Req_dec_T p 0) eqn: Hp. 
    + rewrite e in H. contradiction.
    + rewrite Rmult_assoc. f_equal. simpl in Hmu1. assumption.
Qed.

Lemma combine_onest_mult_coef_r_eq: forall s0 p0 p mu,
  p <> 0 ->
  [(s0, p0)] ⊗ (p * mu) = p * ([(s0, p0)] ⊗ mu).
Proof.
  intros. induction mu as [|(s1, p1) mu1 Hmu1]; try reflexivity.
  rewrite combine_onest_cons_distr_eq. 
  simpl. destruct (Req_dec_T p 0) eqn: Hp. 
    + rewrite e in H. contradiction.
    + rewrite <- Rmult_comm. rewrite Rmult_assoc. 
    rewrite Rmult_comm with (r1:= p0). simpl in Hmu1. 
    rewrite <- Hmu1. reflexivity.
Qed.

Lemma combine_mult_l_assoc_eq: forall mu0 mu1 p, 
  (p * mu0) ⊗ mu1 = p * (mu0 ⊗ mu1).
Proof.
  intros. destruct (Req_dec_T p 0) eqn: Hp. 
  - rewrite e. repeat rewrite dst_mult_0_l. simpl. reflexivity.
  - generalize dependent mu1. 
    induction mu0 as [|(s0, p0) mu0' Hmu0].
    + simpl. intros. reflexivity.
    + intros. rewrite dst_cons_mult_distr; try assumption.
    rewrite combine_cons_l_distr_eq. 
    rewrite combine_cons_l_distr_eq with (mu:= mu0'). 
    rewrite dst_mult_plus_distr_r_eq.
    specialize (Hmu0 mu1). rewrite Hmu0. f_equal.
    apply combine_onest_mult_coef_eq; try assumption.
Qed.   
 
Lemma combine_mult_r_assoc_eq: forall mu0 mu1 p, 
  mu0 ⊗ (p * mu1) = p * (mu0 ⊗ mu1).
Proof.
  intros. destruct (Req_dec_T p 0) eqn: Hp. 
  - rewrite e. repeat rewrite dst_mult_0_l. 
  rewrite combine_nil_r_eq. reflexivity.
  - generalize dependent mu1. 
    induction mu0 as [|(s0, p0) mu0' Hmu0].
    + simpl. intros. reflexivity.
    + intros. 
    rewrite combine_cons_l_distr_eq. 
    rewrite combine_cons_l_distr_eq with (mu:= mu0'). 
    rewrite dst_mult_plus_distr_r_eq.
    specialize (Hmu0 mu1). rewrite Hmu0. f_equal.
    apply combine_onest_mult_coef_r_eq; try assumption.
Qed.   

Lemma combine_onest_sym: forall s p mu, [(s, p)] ⊗ mu == mu ⊗ [(s, p)].
Proof.
  intros. induction mu as [|(s1, p1) mu1 IH1].
  - simpl. apply dst_equiv_refl.
  - simpl in *. 
    apply dst_add_preserves_equiv with 
      (mu0:= [(union_state s s1, (p * p1)%R)]) (mu1:= [(union_state s1 s, (p1 * p)%R)]).
    + simpl. apply Peq_one_st. split.
      * apply union_state_comm. * rewrite Rmult_comm. reflexivity.
    + simpl. apply IH1. 
Qed.
Lemma combine_cons_l_distr: forall mu mu' s p, 
  ((s, p) :: mu') ⊗ mu == ([(s,p)] ⊗ mu) + (mu' ⊗ mu).
Proof.
  intros. generalize dependent mu'.
  induction mu as [|(s1, p1) mu1 IH1].
  - simpl. intros. apply dst_equiv_refl.
  - intros. simpl. rewrite app_nil_r. apply dst_equiv_refl.
Qed.

Lemma combine_cons_r_distr: forall mu mu' s p, 
  mu ⊗ ((s, p) :: mu') == mu ⊗ [(s,p)] + mu ⊗ mu'.
Proof.
  intros. generalize dependent mu'.
  induction mu as [|(s1,p1) mu1 Hmu1]; intros.
  - simpl. apply dst_equiv_refl.
  - apply dst_equiv_trans with (mu1:= 
      combine_dst [(s1, p1)] ((s, p) :: mu') + combine_dst mu1 ((s, p) :: mu')); 
      try apply combine_cons_l_distr.
    apply dst_equiv_trans with (mu1:= 
      combine_dst [(s1, p1)] ((s, p) :: mu') + (combine_dst mu1 [(s, p)] + combine_dst mu1 mu')).
    + apply dst_add_inj_l. apply Hmu1.
    + apply dst_equiv_trans with (mu1:= 
        (combine_dst [(s1, p1)] ((s, p) :: mu') + combine_dst mu1 [(s, p)]) + combine_dst mu1 mu'). 
        { rewrite <- dst_add_assoc_eq. try apply dst_equiv_refl. }
      apply dst_equiv_trans with (mu1:=  
        (combine_dst [(s1, p1)] [(s, p)] + combine_dst mu1 [(s, p)]) + 
            (combine_dst [(s1, p1)] mu' + combine_dst mu1 mu')).
      * apply dst_equiv_trans with (mu1:= 
        ((combine_dst [(s1, p1)] [(s, p)] + combine_dst mu1 [(s, p)]) +
        combine_dst [(s1, p1)] mu') + combine_dst mu1 mu'). 
        ** apply dst_add_inj_r. 
        apply dst_equiv_trans with (mu1:= 
          combine_dst [(s1, p1)] [(s, p)] + combine_dst mu1 [(s, p)] + combine_dst [(s1, p1)] mu'); 
            try apply dst_equiv_refl.
        apply dst_equiv_trans with (mu1:= 
          combine_dst [(s1, p1)] [(s, p)] + combine_dst [(s1, p1)] mu' + combine_dst mu1 [(s, p)]).
        -- apply dst_equiv_trans with (mu1:= 
        (combine_dst [(s1, p1)] [(s, p)] + combine_dst [(s1, p1)] mu') + combine_dst mu1 [(s, p)]);
        try simpl; try apply dst_equiv_refl.
        -- repeat rewrite <- dst_add_assoc_eq. apply dst_add_inj_l. try apply dst_add_comm.
        ** rewrite <- dst_add_assoc_eq. apply dst_equiv_refl. 
      * simpl. rewrite app_nil_r. apply dst_equiv_refl.
Qed.

Lemma combine_sym: forall mu0 mu1, (mu0 ⊗ mu1) == (mu1 ⊗ mu0).
Proof.
  intros. generalize dependent mu1.
  induction mu0 as [|(s0,p0) mu0' Hmu0]; destruct mu1 as [|(s1,p1) mu1'].
  - simpl. apply dst_equiv_refl.
  - simpl. generalize dependent mu1'. induction mu1' as [|(s1',p1') mu' H'].
    + simpl. apply dst_equiv_refl.
    + simpl. apply H'.
  - simpl. specialize (Hmu0 []). simpl in Hmu0. apply Hmu0.
  - apply dst_equiv_trans with (mu1:= 
    combine_dst ((s0, p0) :: mu0') [(s1, p1)] + combine_dst ((s0, p0) :: mu0') mu1'); 
      try apply combine_cons_r_distr.
    apply dst_equiv_trans with (mu1:= 
    ([(union_state s0 s1, (p0 * p1)%R)] + combine_dst mu0' [(s1, p1)]) +
    (combine_dst [(s0, p0)] mu1' + combine_dst mu0' mu1')).
    + apply dst_add_preserves_equiv; try apply dst_equiv_refl; try apply combine_cons_l_distr.
    + apply dst_equiv_sym.
    apply dst_equiv_trans with (mu1:= 
    combine_dst ((s1, p1) :: mu1') [(s0, p0)] + combine_dst ((s1, p1) :: mu1') mu0'); 
      try apply combine_cons_r_distr.
    apply dst_equiv_trans with (mu1:= 
    ([(union_state s1 s0, (p1 * p0)%R)] + combine_dst mu1' [(s0, p0)]) +
    (combine_dst [(s1, p1)] mu0' + combine_dst mu1' mu0')).
      * apply dst_add_preserves_equiv; try apply dst_equiv_refl; try apply combine_cons_l_distr.
      * rewrite <- dst_add_assoc_eq. rewrite <- dst_add_assoc_eq. apply dst_add_preserves_equiv.
      ** apply Peq_one_st. split;
        [ apply union_state_comm| rewrite Rmult_comm; reflexivity].
      ** rewrite dst_add_assoc_eq. rewrite dst_add_assoc_eq. apply dst_add_preserves_equiv.
      ++ apply dst_equiv_trans with (mu1:= combine_dst [(s1, p1)] mu0' + combine_dst mu1' [(s0, p0)]).
      -- apply dst_add_comm.
      -- apply dst_add_preserves_equiv; [apply combine_onest_sym| apply dst_equiv_sym;apply combine_onest_sym].
      ++ apply dst_equiv_sym. apply Hmu0.
Qed.

Lemma combine_onest_add_distr_r: forall s p mu0 mu1, 
  [(s, p)] ⊗ (mu0 + mu1) == 
  [(s, p)] ⊗ mu0 + [(s, p)] ⊗ mu1.
Proof.
  intros. generalize dependent mu1.
  induction mu0 as [|(s0,p0) mu0' Hmu0]; intros.
  - rewrite dst_add_0_l. 
  apply dst_equiv_trans with (mu1:= combine_dst [] [(s, p)] + combine_dst [(s, p)] mu1).
    + simpl. apply dst_equiv_refl.
    + apply dst_add_inj_r. apply combine_sym.
  - simpl. apply dst_add_inj_l with (mu:= [(union_state s s0, (p * p0)%R)]).
  specialize (Hmu0 mu1).  simpl in Hmu0. apply Hmu0.
Qed. 

Lemma combine_add_distr_r: forall mu0 mu1 mu, 
  mu ⊗ (mu0 + mu1) == mu ⊗ mu0 + mu ⊗ mu1.
Proof.
  intros. induction mu as [|(s,p) mu' IH].
  - simpl. apply dst_equiv_refl.
  - apply dst_equiv_trans with (mu1:= 
      combine_dst [(s,p)] (mu0 + mu1) + combine_dst mu' (mu0 + mu1)); 
        try apply combine_cons_l_distr.
    apply dst_equiv_trans with (mu1:= 
      (combine_dst [(s, p)] mu0 + combine_dst [(s, p)] mu1) + combine_dst mu' (mu0 + mu1)); 
      try apply dst_add_inj_r; try apply combine_onest_add_distr_r.
    apply dst_equiv_trans with (mu1:= 
      (combine_dst [(s, p)] mu0 + combine_dst [(s, p)] mu1) + (combine_dst mu' mu0 + combine_dst mu' mu1)); 
      try apply dst_add_inj_l; try apply IH.
    apply dst_equiv_trans with (mu1:= 
      (combine_dst [(s, p)] mu0 + combine_dst mu' mu0) + combine_dst ((s, p) :: mu') mu1).
    + rewrite <- dst_add_assoc_eq. rewrite <- dst_add_assoc_eq. 
      apply dst_add_preserves_equiv; try apply dst_equiv_refl.
      apply dst_equiv_trans with (mu1:= 
          combine_dst mu' mu0 + combine_dst [(s, p)] mu1 + combine_dst mu' mu1).
      * rewrite dst_add_assoc_eq. apply dst_add_inj_r. apply dst_add_comm. 
      * rewrite <- dst_add_assoc_eq. apply dst_add_inj_l. 
        simpl. rewrite app_nil_r. apply dst_equiv_refl.
    + apply dst_add_inj_r. apply dst_equiv_sym. apply combine_cons_l_distr.
Qed.

Lemma combine_add_distr_l: forall mu0 mu1 mu, 
  (mu0 + mu1) ⊗ mu  == mu0 ⊗ mu + mu1 ⊗ mu.
Proof.
  intros.
  apply dst_equiv_trans with (mu1:= combine_dst mu (mu0 + mu1)).
  - apply combine_sym.
  - apply dst_equiv_trans with (mu1:= mu ⊗ mu0 + mu ⊗ mu1).
    + apply combine_add_distr_r.
    + apply dst_add_preserves_equiv; apply combine_sym.
Qed.

Lemma st_eq_implies_combine_merge: forall s0 s1 p0 p1 mu,
  beq_state s0 s1 = true ->
  [(s0, p0)] ⊗ mu + [(s1, p1)] ⊗ mu ==
    [(s1, (p0 + p1)%R)] ⊗ mu.
Proof.
  intros. 
  induction mu as [|(s,p) mu' Hmu]; intros.
  - simpl in *. apply dst_equiv_refl.
  - apply dst_equiv_trans with (mu1:= 
      (combine_dst [(s0, p0)] [(s, p)] + combine_dst [(s0, p0)] mu') +
      (combine_dst [(s1, p1)] [(s, p)] + combine_dst [(s1, p1)] mu')).
    + apply dst_add_preserves_equiv; apply combine_cons_r_distr.
    + apply dst_equiv_trans with (mu1:= 
        (combine_dst [(s0, p0)] [(s, p)] + combine_dst [(s1, p1)] [(s, p)]) +
        (combine_dst [(s0, p0)] mu' + combine_dst [(s1, p1)] mu')); 
          try apply dst_add_shuffle.
      apply dst_equiv_trans with (mu1:= combine_dst [(s1, (p0 + p1)%R)] [(s, p)] + 
                                          combine_dst [(s1, (p0 + p1)%R)] mu').
      * apply dst_add_preserves_equiv; try apply Hmu.
      simpl. unfold dst_equiv. intros. simpl.
      destruct (beq_state s2 (union_state s0 s)) eqn: Hst.
      ++ apply union_state_eq_compat_r with (s:=s) in H.
        apply state_eq_trans with (s2:= (union_state s1 s)) in Hst; try assumption.
        rewrite Hst. repeat rewrite Rplus_0_r. rewrite <- Rmult_plus_distr_r. reflexivity.
      ++ apply union_state_eq_compat_r with (s:=s) in H. 
        apply state_eq_compat_left with (s:= s2) in H; try assumption.
        rewrite H in Hst. rewrite Hst. reflexivity.
      * apply dst_equiv_sym. apply combine_cons_r_distr.
Qed.

Lemma combine_insert_l_decom_equiv: forall s1 p1 mu mu1, 
  (insert_st_pair s1 p1 mu) ⊗ mu1 ==
    [(s1, p1)] ⊗ mu1 + mu ⊗ mu1.
Proof.
  intros. generalize dependent mu1.
  induction mu as [|(s,p) mu' Hmu]; intros.
  - simpl. repeat rewrite dst_add_0_r. apply dst_equiv_refl.
  - unfold insert_st_pair. destruct (beq_state s1 s) eqn: Hst.
    + apply dst_equiv_trans with (mu1:= 
        combine_dst [(s, (p1 + p)%R)] mu1 + combine_dst mu' mu1); try apply combine_cons_l_distr.
      apply dst_equiv_trans with (mu1:= 
        combine_dst [(s1, p1)] mu1 +
        (combine_dst [(s, p)] mu1 + combine_dst mu' mu1)). 
      * rewrite dst_add_assoc_eq. apply dst_add_inj_r. apply dst_equiv_sym. 
      apply st_eq_implies_combine_merge. assumption.
      * try apply dst_add_inj_l. apply dst_equiv_sym. try apply combine_cons_l_distr.
    + fold insert_st_pair. destruct (ble_state s1 s) eqn: Hcmp; try apply combine_cons_l_distr.
      apply dst_equiv_trans with (mu1:= 
        combine_dst [(s, p)] mu1 + combine_dst (insert_st_pair s1 p1 mu') mu1); try apply combine_cons_l_distr.
      apply dst_equiv_trans with (mu1:= 
        combine_dst [(s1, p1)] mu1 + (combine_dst [(s, p)] mu1 + combine_dst mu' mu1)).
      * apply dst_equiv_trans with (mu1:= 
          combine_dst [(s1, p1)] mu1 + combine_dst [(s, p)] mu1 + combine_dst mu' mu1).
      ** apply dst_equiv_trans with (mu1:= 
          combine_dst [(s, p)] mu1 + combine_dst [(s1, p1)] mu1 + combine_dst mu' mu1).
      ++ apply dst_equiv_trans with (mu1:= 
          combine_dst [(s, p)] mu1 + (combine_dst [(s1, p1)] mu1 + combine_dst mu' mu1)).
      -- apply dst_add_inj_l. specialize (Hmu mu1). assumption.
      -- rewrite dst_add_assoc_eq. apply dst_equiv_refl.
      ++ apply dst_add_inj_r. apply dst_add_comm. 
      ** rewrite dst_add_assoc_eq. apply dst_equiv_refl.
      * apply dst_add_inj_l. apply dst_equiv_sym. apply combine_cons_l_distr.
Qed. 

Lemma combine_left_sort_equiv: forall mu mu', 
  mu ⊗ mu' == (sort_dst mu) ⊗ mu'.
Proof.
  intros. generalize dependent mu'.
  induction mu as [|(s1,p1) mu1 Hmu]; intros. 
  - simpl in *. apply dst_equiv_refl.
  - apply dst_equiv_trans with (mu1:= combine_dst [(s1,p1)] mu' + combine_dst mu1 mu'); 
    try apply combine_cons_l_distr.
    unfold sort_dst. fold sort_dst.
    apply dst_equiv_trans with (mu1:= combine_dst [(s1, p1)] mu' + combine_dst (sort_dst mu1) mu').
    +  apply dst_add_inj_l. apply Hmu.
    + apply dst_equiv_sym.  apply combine_insert_l_decom_equiv.
Qed.

Lemma dst_eq_implies_combine_compat_r: forall mu0 mu1 mu, 
  beq_dst mu0 mu1 = true -> mu0 ⊗ mu == mu1 ⊗ mu.
Proof.
  intros mu0 mu1 mu Hbeq. generalize dependent mu. generalize dependent mu1.
  induction mu0 as [|(s0,p0) mu0' Hmu0]; destruct mu1 as [|(s1,p1) mu1']; intros.
  - simpl in *. apply dst_equiv_refl.
  - simpl in Hbeq. discriminate.
  - simpl in Hbeq. discriminate.
  - simpl in Hbeq. apply andb_true_iff in Hbeq. destruct Hbeq. 
  apply andb_true_iff in H. destruct H. 
  apply dst_equiv_trans with (mu1:= combine_dst [(s0,p0)] mu + combine_dst mu0' mu); 
    try apply combine_cons_l_distr.
  apply dst_equiv_trans with (mu1:= combine_dst [(s1,p1)] mu + combine_dst mu1' mu).
    + apply dst_add_preserves_equiv. 
      * induction mu as [|(s,p) mu']; intros.
        ** simpl. apply dst_equiv_refl.
        ** apply dst_equiv_trans with (mu1:= 
            combine_dst [(s0,p0)] [(s,p)] + combine_dst [(s0,p0)] mu'); try apply combine_cons_r_distr.
          apply dst_equiv_trans with (mu1:= 
            combine_dst [(s1,p1)] [(s,p)] + combine_dst [(s1,p1)] mu').
        ++ apply dst_add_preserves_equiv; try assumption.
          simpl. apply Peq_one_st. split.
        -- apply union_state_eq_compat_r. apply H.
        -- unfold Req_bool in H1. destruct (Req_EM_T p0 p1); try discriminate.
          rewrite e. reflexivity.
        ++ apply dst_equiv_sym. apply combine_cons_r_distr.
      * apply Hmu0. apply H0.
    + apply dst_equiv_sym. apply combine_cons_l_distr.
Qed.


Lemma dst_equiv_implies_combine_compat_r: forall mu0 mu1 mu, 
  Valid_dist mu0 -> Valid_dist mu1 ->
  mu0 == mu1 -> mu0 ⊗ mu == mu1 ⊗ mu.
Proof.
  intros mu0 mu1 mu H0 H1 Hmu_Peq. 
  pose (mu0_sorted := sort_dst mu0).
  pose (mu1_sorted := sort_dst mu1).
  assert (Hsorted0: Sorted_dst mu0_sorted). { 
    apply WF_dist_implies_sortdst_Sorted. assumption. }
  assert (Hsorted1: Sorted_dst mu1_sorted). { 
    apply WF_dist_implies_sortdst_Sorted. assumption. }
  assert (Hvalid0: Valid_dist mu0_sorted). { 
    apply Valid_implies_sort_Valid. assumption. }
  assert (Hvalid1: Valid_dist mu1_sorted). { 
    apply Valid_implies_sort_Valid. assumption. }
  assert (Hsort_trans: mu0_sorted == mu1_sorted). { 
    apply dst_equiv_trans with (mu1:= mu0).
    - apply dst_equiv_sym. apply dst_equiv_sort.
    - apply dst_equiv_trans with (mu1:= mu1); [assumption|apply dst_equiv_sort]. }
  assert (Htemp_beq: beq_dst mu0_sorted mu1_sorted = true). { 
    apply Sort_Valid_Peq_implies_beq_True; try split; try assumption. }
  assert (Heq0: combine_dst mu0 mu == combine_dst mu0_sorted mu) by
    apply combine_left_sort_equiv. 
  assert (Heq1: combine_dst mu1 mu == combine_dst mu1_sorted mu) by
    apply combine_left_sort_equiv. 
  apply dst_equiv_trans with (mu1:= combine_dst mu0_sorted mu); try assumption.
  apply dst_equiv_trans with (mu1:= combine_dst mu1_sorted mu); 
    try apply dst_equiv_sym in Heq1; try assumption. 
  apply dst_eq_implies_combine_compat_r.
  apply Htemp_beq.
Qed.

Lemma dst_equiv_implies_combine_compat_l: forall mu0 mu1 mu, 
  Valid_dist mu0 -> Valid_dist mu1 ->
  mu0 == mu1 -> 
  mu ⊗ mu0 == mu ⊗ mu1.
Proof.
  intros. apply dst_equiv_trans with (mu1:= combine_dst mu0 mu); try apply combine_sym.
  apply dst_equiv_trans with (mu1:= combine_dst mu1 mu); try apply combine_sym.
  apply dst_equiv_implies_combine_compat_r; try assumption.
Qed.

Lemma dst_equiv_preserves_combine: forall mu0 mu1 mu2 mu3, 
  Valid_dist mu0 -> Valid_dist mu1 -> Valid_dist mu2 -> Valid_dist mu3 ->
  mu0 == mu1 -> mu2 == mu3 ->
  mu0 ⊗ mu2 == mu1 ⊗ mu3.
Proof.
  intros. apply dst_equiv_implies_combine_compat_r with (mu:= mu2) in H3; try assumption.
  apply dst_equiv_trans with (mu1:= mu1 ⊗ mu2); try assumption.
  apply dst_equiv_implies_combine_compat_l with (mu:= mu1) in H4; try assumption.
Qed.

(*********************Combine operation maintains Valid. *************************************************)
Lemma prob_combine_left_one_le_mult_p: forall s p mu, 
  (sum_probs ([(s, p)] ⊗ mu) <= (p * sum_probs mu)%R)%R.
Proof.
  intros. induction mu as [|(s',p') mu' Hmu]; intros.
  - simpl. rewrite Rmult_0_r. apply Rle_refl.
  - simpl. apply Rle_trans with (r2:= (p * p' + (p * sum_probs mu'))%R).
    + apply Rplus_le_compat_l. apply Hmu.
    + rewrite Rmult_plus_distr_l. apply Rle_refl.
Qed.

Lemma posi_prob_combine_one: forall s p mu, 
  (0 < p <= 1)%R -> positive_probs mu ->
  positive_probs ([(s, p)] ⊗ mu).
Proof.
  intros s p mu Hp H.
  induction mu as [|(s',p') mu' Hmu']; intros.
  - simpl. apply I.
  - simpl. simpl in H. destruct H. split.
    + unfold prob_is_positive in H. unfold prob_is_positive. 
      destruct Hp. destruct H. split.
      * apply Rmult_lt_0_compat; assumption.
      * rewrite <- Rmult_1_l with (r:=1%R). 
        apply Rmult_le_compat; try (assumption); apply Rlt_le; assumption.
    + apply Hmu'. apply H0.
Qed. 

Lemma Valid_combine_one_left: forall s p mu,
  (0 < p <= 1)%R -> Valid_dist mu ->
  Valid_dist ([(s, p)] ⊗ mu).
Proof.
  intros.
  unfold Valid_dist. split.
  - split.
    + induction mu as [|(s',p') mu' Hmu]; intros.
      * simpl. apply Rle_refl.
      * simpl. destruct H. apply Valid_dist_conj in H0. 
      destruct H0. destruct H0. simpl in H0. 
      rewrite Rplus_0_r in H0. destruct H0.
      apply Hmu in H2. rewrite <- Rplus_0_l with (r:= 0%R).
      apply Rplus_le_compat.
      ** rewrite <- Rmult_0_l with (r:=0%R).
      apply Rmult_le_compat; try apply Rle_refl; try assumption.
      apply Rlt_le. assumption.
      ** apply H2. 
    + apply Rle_trans with (r2:= (p * sum_probs mu)%R). 
      * apply prob_combine_left_one_le_mult_p.
      * apply Valid_mult_cofe with (p:= p) in H0.
      -- unfold Valid_dist in H0. destruct H0. destruct H0.
        apply Rle_trans with (r2:= (sum_probs (p * mu)%dist_state)%R).
      ++ rewrite dst_sum_prob_coef_mult. apply Rle_refl.
      ++ apply H2.
      -- apply R_01_split. right. assumption.
  - apply posi_prob_combine_one; try assumption.
  unfold Valid_dist in H0. destruct H0.  assumption.
Qed.

Lemma sum_prob_combine_le_compat: forall mu0 mu1, 
  Valid_dist mu0 -> Valid_dist mu1 ->
  (sum_probs (mu0 ⊗ mu1) <= sum_probs mu0)%R.
Proof.
  intros mu0 mu1 Hvalid0 Hvalid1.  
  generalize dependent mu1.
  induction mu0 as [|(s, p) mu0' Hmu]; intros.
  - simpl. apply Rle_refl.
  - rewrite combine_cons_l_distr_eq. rewrite dst_sum_prob_decom. 
    rewrite dst_cons_eq_add with (mu:= mu0').
    rewrite dst_sum_prob_decom with (mu0:=[(s,p)]) (mu1:= mu0').
    apply Rplus_le_compat.
    + apply Rle_trans with (r2:= (p * sum_probs mu1)%R); try apply prob_combine_left_one_le_mult_p.
    simpl. rewrite Rplus_0_r. rewrite <- Rmult_1_r with (r:= p) at 2.
    apply Valid_dist_conj in Hvalid0. destruct Hvalid0 as [H1 H2].
    unfold Valid_dist in H1. destruct H1 as [Hsum0 Hpos0]. 
    simpl in Hpos0. destruct Hpos0 as [Hp HI]. unfold prob_is_positive in Hp. 
    unfold Valid_dist in Hvalid1. destruct Hvalid1 as [Hsum1 Hpos1]. 
    destruct Hsum1. apply Rmult_le_compat; try assumption.
      * apply Rlt_le. destruct Hp. assumption.
      * apply Rle_refl.
    + apply Valid_dist_inv in Hvalid0. apply Hmu; try assumption. 
Qed.

Lemma Valid_after_combine: forall mu0 mu1,  
  Valid_dist mu0 -> Valid_dist mu1 -> 
  Valid_dist (mu0 ⊗ mu1).
Proof.
  intros. generalize dependent mu1.
  induction mu0 as [|(s0, p0) mu0' Hmu0]; intros.
  - simpl. apply H.
  - unfold Valid_dist. split.
    + split.
      * apply Valid_dist_conj in H. destruct H.
      specialize (Hmu0 H1 mu1 H0). unfold Valid_dist in Hmu0. 
      destruct Hmu0. destruct H2. 
      rewrite <- Rplus_0_l with (r:= 0%R). 
      rewrite combine_cons_l_distr_eq. rewrite dst_sum_prob_decom. 
      apply Rplus_le_compat; try assumption.
      apply Valid_combine_one_left with (s:=s0) (p:=p0) in H0.
      ** unfold Valid_dist in H0. destruct H0. destruct H0. apply H0.
      ** unfold Valid_dist in H. simpl in H. destruct H. destruct H5. 
      unfold prob_is_positive in H5. apply H5.
      * apply Rle_trans with (r2:= sum_probs ((s0, p0) :: mu0')).
      ** apply sum_prob_combine_le_compat; try assumption.
      ** unfold Valid_dist in H. destruct H. destruct H.
      apply H2.
    + rewrite combine_cons_l_distr_eq. apply dst_positive_decom. split.
      * unfold Valid_dist in H. destruct H.
        unfold Valid_dist in H0. destruct H0. 
        apply posi_prob_combine_one; try assumption.
        simpl in H1. destruct H1. unfold prob_is_positive in H1. apply H1.
      * apply Valid_dist_inv in H. specialize (Hmu0 H mu1 H0).
        unfold Valid_dist in Hmu0. destruct Hmu0. apply H2.
Qed.

(*******************associativity *********************)
Lemma combine_twost_l_assoc: forall s0 p0 s1 p1 mu X0 X1 X,
  (domain_equiv X0 (return_domain s0)) -> 
  (domain_equiv X1 (return_domain s1)) -> 
  partial_dst_Prop X mu ->
  is_domain_intersect X0 X1 = false ->
  is_domain_intersect X1 X = false ->
  is_domain_intersect X0 X = false ->
  [(s0, p0)] ⊗ ([(s1, p1)] ⊗ mu) == ([(s0, p0)] ⊗ [(s1, p1)]) ⊗ mu.
Proof.
  intros. induction mu as [|(s,p) mu' Hmu]; intros.
  - simpl. apply dst_equiv_refl.
  - rewrite combine_onest_cons_distr_eq. 
    apply dst_equiv_trans with (mu1:= ([(s0, p0)] ⊗ [(union_state s1 s, (p1 * p)%R)] + 
                                      [(s0, p0)] ⊗ ([(s1, p1)] ⊗ mu'))); 
                                      try apply combine_onest_add_distr_r.
    assert (Heq: [(s0, p0)] ⊗ [(s1, p1)] = [(union_state s0 s1, (p0 * p1)%R)]) 
      by reflexivity. 
    rewrite Heq. 
    rewrite combine_onest_cons_distr_eq with (mu:= mu'). 
    apply dst_add_preserves_equiv. 
    + apply Peq_one_st. split. 
      * inversion H1; subst.
        apply union_state_assoc; try assumption.
      ** apply dom_eq_intersect_preserves_equiv with 
        (l0:= X0) (l1:= (return_domain s0)) in H0; try assumption.
      rewrite <- H0. assumption.
      ** apply dom_eq_intersect_preserves_equiv with 
        (l0:= X0) (l1:= (return_domain s0)) in H7; try assumption.
      rewrite <- H7. assumption.
      ** apply dom_eq_intersect_preserves_equiv with 
        (l0:= X1) (l1:= (return_domain s1)) in H7; try assumption.
      rewrite <- H7. assumption.
      * rewrite Rmult_assoc. reflexivity.
    + rewrite Heq in Hmu. apply Hmu. 
      apply PD_inv in H1. assumption. 
Qed. 

Lemma combine_onest_l_assoc: forall s0 X0 p0 mu1 mu2 X1 X2,
  Valid_dist mu1 -> Valid_dist mu2 -> Valid_dist [(s0, p0)] ->
  partial_dst_Prop X1 mu1 -> partial_dst_Prop X2 mu2 -> 
  (domain_equiv X0 (return_domain s0)) -> 
  is_domain_intersect X0 X1 = false ->
  is_domain_intersect X0 X2 = false ->
  is_domain_intersect X1 X2 = false ->
  [(s0, p0)] ⊗ (mu1 ⊗ mu2) == ([(s0, p0)] ⊗ mu1) ⊗ mu2 .
Proof.
  intros. generalize dependent mu2.
  induction mu1 as [|(s1,p1) mu1' Hmu1]; intros.
  - simpl. apply dst_equiv_refl.
  - rewrite combine_cons_l_distr_eq with (mu:= mu1') (mu1:= mu2). 
    apply dst_equiv_trans with (mu1:= (combine_dst [(s0, p0)] (combine_dst [(s1, p1)] mu2)) + 
          (combine_dst [(s0, p0)] (combine_dst mu1' mu2))); try apply combine_add_distr_r.
    apply dst_equiv_trans with (mu1:= ([(s0, p0)] ⊗ [(s1, p1)] + [(s0, p0)] ⊗ mu1') ⊗ mu2).
    * apply dst_equiv_trans with (mu1:= ([(s0, p0)] ⊗ [(s1, p1)]) ⊗ mu2 + ([(s0, p0)] ⊗ mu1') ⊗ mu2 ).
      + apply dst_add_preserves_equiv.
      ** unfold combine_dst at 4. rewrite app_nil_r. repeat rewrite dst_add_0_r.
        induction mu2 as [|(s2,p2) mu2' Hmu2]; intros.
        -- simpl. apply dst_equiv_refl.
        -- assert (Heq: [(s0, p0)] ⊗ [(s1, p1)] = [(union_state s0 s1, (p0 * p1)%R)]) by reflexivity. 
          rewrite <- Heq. 
          apply combine_twost_l_assoc with (X0:= X0) (X1:= X1) (X:= X2); try assumption. 
          inversion H2; try assumption.
      ** apply Hmu1; try assumption.
        -- apply Valid_dist_inv in H. assumption.
        -- inversion H2; try assumption.
      + apply dst_equiv_sym. apply combine_add_distr_l.
    * apply dst_equiv_implies_combine_compat_r.
      + assert (Heq: [(s0, p0)] ⊗ [(s1, p1)] + [(s0, p0)] ⊗ mu1'= [(s0, p0)] ⊗ ((s1, p1):: mu1')) by reflexivity.
        rewrite Heq. apply Valid_after_combine; try assumption.
      + apply Valid_after_combine; try assumption. 
      + simpl. apply dst_equiv_refl.
Qed.

Lemma combine_assoc: forall mu0 mu1 mu2 X0 X1 X2, 
  Valid_dist mu0 -> Valid_dist mu1 -> Valid_dist mu2 ->
  partial_dst_Prop X0 mu0 -> partial_dst_Prop X1 mu1 -> partial_dst_Prop X2 mu2 ->
  is_domain_intersect X0 X1 = false ->
  is_domain_intersect X0 X2 = false ->
  is_domain_intersect X1 X2 = false ->
  (mu0 ⊗ (mu1 ⊗ mu2)) == ((mu0 ⊗ mu1) ⊗ mu2).
Proof.
  intros.
  generalize dependent mu2. generalize dependent mu1.
  induction mu0 as [|(s0,p0) mu0' Hmu0]; intros. 
  - simpl. apply dst_equiv_refl.
  - rewrite combine_cons_l_distr_eq. 
    rewrite combine_cons_l_distr_eq with (mu1:= mu1) (mu:= mu0'). 
      apply dst_equiv_trans with (mu1:= 
          (combine_dst (combine_dst [(s0, p0)] mu1) mu2) + (combine_dst (combine_dst mu0' mu1) mu2)). 
      * apply dst_add_preserves_equiv; try apply Hmu0; try assumption.
        + apply combine_onest_l_assoc with (X0:= X0) (X1:= X1) (X2:= X2); try assumption.
        ++ apply Valid_dist_conj in H. destruct H. assumption.
        ++ inversion H2; subst; try assumption.
        + apply Valid_dist_conj in H. destruct H. assumption.
        + inversion H2; subst; try assumption.
      * apply dst_equiv_sym. apply combine_add_distr_l.
Qed.

(*************************** PD predicate ***********************************************)

Lemma PD_combine_onest_mult_coef_left: forall mu X p s0 p0, 
  partial_dst_Prop X ([(s0, p0)] ⊗ mu) -> 
  partial_dst_Prop X ([(s0, (p * p0)%R)] ⊗ mu).
Proof.
  intros mu X p s0 p0 H. generalize dependent X.
  generalize dependent s0. induction mu as [|(s1, p1) mu']; intros. 
  - rewrite combine_nil_r_eq. apply PD_nil.
  - rewrite combine_onest_cons_distr_eq. apply PD_decom. 
    rewrite combine_onest_cons_distr_eq in H. apply PD_decom in H. destruct H.
    split.
    + inversion H; subst. apply PD_cons; try assumption.
    + apply IHmu'; try assumption.
Qed. 

Lemma PD_combine_onest_mult_coef_right: forall mu X p s0 p0, 
  partial_dst_Prop X ([(s0, p0)] ⊗ mu) -> 
  partial_dst_Prop X ([(s0, p0)] ⊗ (p * mu)).
Proof.
  intros mu X p s0 p0 H. generalize dependent X.
  generalize dependent s0. induction mu as [|(s1, p1) mu']; intros. 
  - rewrite combine_nil_r_eq. apply PD_nil.
  - destruct (Req_dec_T p 0) eqn: Hp. 
    + rewrite e. rewrite dst_mult_0_l. rewrite combine_nil_r_eq. apply PD_nil.
    + rewrite dst_cons_mult_distr; try assumption.
    rewrite combine_onest_cons_distr_eq. apply PD_decom. 
    rewrite combine_onest_cons_distr_eq in H. apply PD_decom in H. destruct H.
    split.
      * inversion H; subst. apply PD_cons; try assumption.
      * apply IHmu'; try assumption.
Qed. 

Lemma PD_combine_mult_coef_left: forall mu0 mu1 X p, 
  partial_dst_Prop X (mu0 ⊗ mu1) -> 
  partial_dst_Prop X ((p * mu0) ⊗ mu1).
Proof.
  intros mu0 mu1 X p H. generalize dependent mu1. generalize dependent X.
  induction mu0 as [|(s0, p0) mu0']; intros. 
  - simpl. apply PD_nil.
  - simpl. destruct (Req_dec_T p 0) eqn: Hp. 
    * simpl. apply PD_nil.
    * rewrite combine_cons_l_distr_eq. apply PD_decom. 
      rewrite combine_cons_l_distr_eq in H. apply PD_decom in H. destruct H. 
      split. 
      + apply PD_combine_onest_mult_coef_left; try assumption.
      + apply IHmu0'; try assumption. 
Qed.

Lemma PD_combine_mult_coef_right: forall mu0 mu1 X p, 
  partial_dst_Prop X (mu0 ⊗ mu1) -> 
  partial_dst_Prop X (mu0 ⊗ (p * mu1)).
Proof.
  intros mu0 mu1 X p H. 
  generalize dependent mu1. generalize dependent X.
  induction mu0 as [|(s0, p0) mu0']; intros. 
  - simpl. apply PD_nil.
  - destruct (Req_dec_T p 0) eqn: Hp. 
    * rewrite e. rewrite dst_mult_0_l. rewrite combine_nil_r_eq. apply PD_nil.
    * rewrite combine_cons_l_distr_eq. apply PD_decom. 
      rewrite combine_cons_l_distr_eq in H. apply PD_decom in H. destruct H. 
      split. 
      + apply PD_combine_onest_mult_coef_right; try assumption.
      + apply IHmu0'; try assumption. 
Qed.


Lemma PD_combine_mult_coef_2: forall mu0 mu1 X p0 p1, 
  partial_dst_Prop X (mu0 ⊗ mu1) -> 
  partial_dst_Prop X ((p0 * mu0) ⊗ (p1 * mu1)).
Proof.
  intros mu0 mu1 X p0 p1 H. 
  apply PD_combine_mult_coef_left.
  apply PD_combine_mult_coef_right.
  assumption.
Qed.

Lemma PD_combine_onest_left: forall s1 p1 dom1 pd, 
  partial_dst_Prop dom1 [(s1, p1)] -> 
  is_domain_intersect dom1 pd.(dom) = false ->
  partial_dst_Prop (orb_domain dom1 pd.(dom)) ([(s1, p1)] ⊗ pd.(mu)).
Proof.
  intros s1 p1 dom1 pd Hdom1 Hpd. destruct pd. 
  induction mu as [| (s,p) mu' IH].
  - simpl. apply PD_nil.
  - unfold mu. rewrite combine_onest_cons_distr_eq. 
    rewrite <- dst_cons_eq_add. apply PD_cons; try assumption.
    + simpl. simpl in Hpd. inversion Hdom1; subst. inversion all_partial; subst.
      assert (H': (orb_domain dom1 dom == orb_domain (return_domain s1) (return_domain s))%domain). {
        apply dom_eq_orb_compat_right with (l2:= dom) in H1; try assumption.
        apply dom_equiv_trans with (l1:= orb_domain (return_domain s1) dom); try assumption.
        rewrite orb_domain_comm. 
        apply dom_eq_orb_compat_right with (l2:= (return_domain s1)) in H2; try assumption.
        apply dom_equiv_trans with (l1:= orb_domain (return_domain s) (return_domain s1)); try assumption.
        rewrite orb_domain_comm. apply dom_equiv_refl. }
      apply dom_equiv_trans with (l1:= orb_domain (return_domain s1) (return_domain s)); try assumption.
      apply union_eq_orb_dom; try assumption. 
      rewrite <- dom_eq_intersect_preserves_equiv with (l0:= dom1) (l2:= dom); try assumption.
    + assert (HPar_copy: partial_dst_Prop dom ((s, p) :: mu')) by assumption. 
    apply PD_inv in HPar_copy. specialize (IH HPar_copy). 
    apply IH; try assumption.
Qed.  

Lemma PD_combine_invar_mu: forall pd1 pd2, 
  is_domain_intersect pd1.(dom) pd2.(dom) = false ->
  partial_dst_Prop (orb_domain pd1.(dom) pd2.(dom)) (pd1.(mu) ⊗ pd2.(mu)).
Proof. 
  intros. generalize dependent pd2. destruct pd1 as [dom1 mu1]. simpl in *.
  induction mu1 as [|(s1,p1) mu1']; intros.
  - simpl. apply PD_nil.
  - destruct pd2 as [dom2 mu2]. unfold mu. rewrite combine_cons_l_distr_eq.
    apply PD_decom. split. 
    + apply PD_combine_onest_left; try assumption.
    rewrite dst_cons_eq_add in all_partial. apply PD_decom in all_partial. 
    destruct all_partial. assumption. 
    + apply IHmu1'; try assumption. apply PD_inv in all_partial. assumption.
Qed.

Definition combine_pd (pd0 pd1 : partial_dist) 
                    (Hdom: is_domain_intersect (dom pd0) (dom pd1) = false) : partial_dist :=
  {| 
    dom := (dom pd0) ∪ (dom pd1); 
    mu := mu pd0 ⊗ mu pd1;
    all_partial :=  PD_combine_invar_mu pd0 pd1 Hdom
  |}.
(*************** The equality of probability of combine ********)
Lemma sum_probs_combine_onest_eq: forall mu s p, 
  sum_probs ([(s, p)] ⊗ mu) = (p * sum_probs mu)%R.
Proof.
  intros. induction mu as [|(s', p') mu' Hmu].
  - simpl. rewrite Rmult_0_r. reflexivity.
  - rewrite combine_onest_cons_distr_eq.
  rewrite dst_sum_prob_decom. rewrite Hmu.
  rewrite dst_cons_eq_add with (mu:= mu'). 
  rewrite dst_sum_prob_decom.
  rewrite Rmult_plus_distr_l. f_equal. simpl. repeat rewrite Rplus_0_r.
  reflexivity.
Qed.

Lemma sum_probs_combine_eq_mult: forall mu1 mu2, (*lemma 2*)
  sum_probs (mu1 ⊗ mu2) = (sum_probs mu1 * sum_probs mu2)%R.
Proof.
  intros. generalize dependent mu2.
  induction mu1 as [|(s, p) mu1' Hmu1].
  - simpl. intros. rewrite Rmult_0_l. reflexivity.
  - intros. rewrite combine_cons_l_distr_eq. specialize (Hmu1 mu2).
  rewrite dst_sum_prob_decom. rewrite Hmu1.
  rewrite dst_cons_eq_add with (mu:= mu1'). rewrite dst_sum_prob_decom.
  rewrite Rmult_plus_distr_r. f_equal. rewrite sum_probs_combine_onest_eq.
  simpl. repeat rewrite Rplus_0_r. reflexivity.
Qed.

(**********************************************)
Lemma combine_nil_implies_nil: forall mu0 mu1, 
  mu0 ⊗ mu1 = [] -> mu0 = [] \/ mu1 =[].
Proof.
  induction mu0 as [|(s, p) mu0' Hmu0]; intros.
  - left. reflexivity.
  - right. rewrite combine_cons_l_distr_eq in H. destruct mu1 as [|(s', p') mu1'].
    + reflexivity. + rewrite combine_onest_cons_distr_eq in H. discriminate.
Qed.

Lemma comb_nil_implies_nil_inv: forall mu0 mu1,
  Valid_dist mu0 -> Valid_dist mu1 ->
  mu0 ⊗ mu1 == [] -> mu0 == [] \/ mu1 == [].
Proof.
  intros mu0 mu1 Hvalid0 Hvalid1 Heq.
  generalize dependent mu1. induction mu0 as [|(s,p) mu0']; intros.
  - left. apply dst_equiv_refl.
  - destruct mu1 as [|(s',p') mu1']; intros.
    + right. apply dst_equiv_refl.
    + assert (Hcomb: ((s, p) :: mu0') ⊗ ((s', p') :: mu1') = 
      (union_state s s', (p * p')%R) :: [(s, p)] ⊗ mu1' + mu0' ⊗ ((s', p') :: mu1')).
        { rewrite combine_cons_l_distr_eq. 
        rewrite combine_onest_cons_distr_eq.
        rewrite <- dst_add_assoc_eq.
        rewrite <- dst_cons_eq_add. reflexivity. }
      rewrite Hcomb in Heq.
      apply dst_cons_valid_contra in Heq; try assumption.
      * contradiction.
      * rewrite <- Hcomb. apply Valid_after_combine; try assumption.
Qed.