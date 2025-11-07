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
Require Import Library.DistState.Support.
Require Import Library.DistState.Arithmetic.
Require Import Library.DistState.Combine.
Require Import Library.DistState.Restrict.
Require Import Library.DistState.Bulid.
Require Import Library.DistState.Partial.
Require Import Library.PIMP.Syntax.
Require Import Library.PIMP.EvalProps.
Require Import Library.PIMP.Semantics.

Require Import Library.Assertion.Asserts.
Open Scope list_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope dstate_scope.
Set Default Goal Selector "!".

(***********************************************)
Lemma dst_satisfy_df_implies_dom: forall df pd, 
  [[Pdeter df]] pd -> 
  is_domain_subset (get_var_in_Pformular (Pdeter df)) (dom pd) = true.
Proof.
  intros df pd Hsem. generalize dependent pd. induction df as [|].
  - intros. destruct pd. simpl in *. destruct Hsem. assumption.
  - intros. destruct pd. simpl. destruct Hsem. simpl in H. assumption.
Qed.

Lemma satisfy_implies_dom_sub: forall phi pd, 
  well_defined_Pf phi -> [[phi]] pd -> 
  is_domain_subset (get_var_in_Pformular phi) pd.(dom) = true.
Proof.
  intros phi pd HWD Hsem. generalize dependent pd. induction phi as[| | | |]; intros.
  - apply dst_satisfy_df_implies_dom. assumption. 
  - destruct Hsem as [Hcase1 | Hsem].
    + destruct Hcase1 as [Hp_case1 H]. 
    destruct H as [pd01 H]. destruct H as [pd02 H].
    destruct H as [HWF01 H]. destruct H as [HWF02 H]. 
    destruct H as [Hdom01 H]. destruct H as [Hdom02 H].
    destruct H as [Hsem01 H]. destruct H as [Hsem02 H].
    simpl. inversion HWD; subst.  
    apply IHphi1 in Hsem01; try assumption. 
    apply IHphi2 in Hsem02; try assumption.
    apply dom_subset_eq_compat_left with (Z:= (get_var_in_Pformular phi1)) in Hdom01; try assumption.
    apply dom_subset_eq_compat_left with (Z:= (get_var_in_Pformular phi2)) in Hdom02; try assumption.
    destruct Hp_case1 as [Hgt0 Hlt1]. 
    destruct (Rle_lt_dec r 0) eqn: Hp0; destruct (Rle_lt_dec 1 r) eqn: Hp1; try assumption.
    apply dom_subset_orb_fst_iff. split; try assumption.
    + destruct Hsem as [Hcase2| Hcase3].
      * destruct Hcase2 as [Hp_case2 H]. 
        destruct H as [pd01 H]. destruct H as [HWF01 H]. 
        destruct H as [Hpdeq01 H]. destruct Hpdeq01 as [Hdom01 Hmu].
        destruct H as [Hsem01 Hsum]. 
        simpl. inversion HWD; subst.
        apply IHphi1 in Hsem01; try assumption. 
        apply dom_subset_eq_compat_left with (Z:= (get_var_in_Pformular phi1)) in Hdom01; try assumption.
        destruct (Rle_lt_dec 1 0); destruct (Rle_lt_dec 1 1); try apply Rlt_irrefl in r0; try contradiction.
          ** apply Rle_not_lt in r. unfold not in r. exfalso. apply r. apply Rlt_0_1. 
          ** assumption.
      * destruct Hcase3 as [Hp_case3 H]. 
        destruct H as [pd01 H]. destruct H as [HWF01 H]. 
        destruct H as [Hpdeq01 H]. destruct Hpdeq01 as [Hdom01 Hmu].
        destruct H as [Hsem01 Hsum]. 
        simpl. inversion HWD; subst. 
        apply IHphi2 in Hsem01; try assumption. 
        apply dom_subset_eq_compat_left with (Z:= (get_var_in_Pformular phi2)) in Hdom01; try assumption.
        destruct (Rle_lt_dec 0 0); destruct (Rle_lt_dec 1 0); try apply Rlt_irrefl in r; try contradiction.
          ** apply Rle_not_lt in r0. unfold not in r0. exfalso. apply r0. apply Rlt_0_1. 
          ** assumption. 
  - destruct Hsem as [Hcase1 | Hsem]. 
    + destruct Hcase1 as [p1 H]. destruct H as [p2 H]. 
      destruct H as [Hp1 H]. destruct H as [Hp2 H]. destruct H as [Hp_eq H].
      destruct H as [pd01 H]. destruct H as [pd02 H].
      destruct H as [HWF01 H]. destruct H as [HWF02 H]. 
      destruct H as [Hdom01 H]. destruct H as [Hdom02 H].
      destruct H as [Hsem01 H]. destruct H as [Hsem02 H].
      simpl. inversion HWD; subst. 
      apply IHphi1 in Hsem01; try assumption. 
      apply IHphi2 in Hsem02; try assumption. 
      apply dom_subset_eq_compat_left with (Z:= (get_var_in_Pformular phi1)) in Hdom01; try assumption.
      apply dom_subset_eq_compat_left with (Z:= (get_var_in_Pformular phi2)) in Hdom02; try assumption.
      apply dom_subset_orb_fst_iff. split; try assumption.
    + destruct Hsem as [Hcase2| Hcase3].
      * destruct Hcase2 as [pd01 H]. destruct H as [HWF01 H]. 
        destruct H as [Hpdeq01 H]. destruct Hpdeq01 as [Hdom01 Hmu].
        destruct H as [Hsub H]. 
        destruct H as [Hsem01 Hsum]. 
        simpl. inversion HWD; subst. 
        apply IHphi1 in Hsem01; try assumption. 
        apply dom_subset_eq_compat_left with (Z:= (get_var_in_Pformular phi1)) in Hdom01; try assumption.
        apply dom_subset_orb_fst_iff. split; try assumption.
      * destruct Hcase3 as [pd01 H]. destruct H as [HWF01 H]. 
        destruct H as [Hpdeq01 H]. destruct Hpdeq01 as [Hdom01 Hmu].
        destruct H as [Hsub H]. 
        destruct H as [Hsem01 Hsum]. 
        simpl. inversion HWD; subst.
        apply IHphi2 in Hsem01; try assumption. 
        apply dom_subset_eq_compat_left with (Z:= (get_var_in_Pformular phi2)) in Hdom01; try assumption.
        apply dom_subset_orb_fst_iff. split; try assumption. 
  - simpl in Hsem. 
    destruct Hsem as [pd01 H]. destruct H as [pd02 H].
    destruct H as [Hvar H]. destruct H as [HWF01 H]. destruct H as [HWF02 H]. 
    destruct H as [Hsem01 H]. destruct H as [Hsem02 H]. 
    destruct H. simpl in H. simpl in H0. simpl. 
    inversion HWD; subst. 
    apply dom_subset_trans with (l1:= (orb_domain (dom pd01) (dom pd02))); try assumption.
    apply dom_subset_orb_compat. 
    + apply IHphi1; try assumption.
    + apply IHphi2; try assumption.
  - simpl in *. destruct Hsem as [Hsem01 Hsem02]. 
    inversion HWD; subst. 
    apply IHphi1 in Hsem01; try assumption. 
    apply IHphi2 in Hsem02; try assumption.
    apply dom_subset_orb_fst_iff. split; try assumption.
Qed.
(******************************)

Lemma emp_dst_satisfies_phi: forall phi X, 
  well_defined_Pf phi -> 
  is_domain_subset (get_var_in_Pformular phi) X = true -> (* This is a requirement of Oplus *)
  [[phi]] (pd_emp X).
Proof. 
  intros phi X H Hsub. generalize dependent X. 
  induction phi as [| | | |]; simpl; intros.
  - split; try assumption. intros. discriminate.
  - inversion H; subst. 
    assert (Hq_case: 0 < r < 1 \/ r = 1 \/ r = 0). { 
        apply R_01_decom3. assumption. }
    destruct Hq_case as [Hq_case1| Hq_case]. 
    + assert (Hsub_simpl: is_domain_subset 
        (get_var_in_Pformular phi1 ∪ get_var_in_Pformular phi2)%domain X = true). {
          destruct Hq_case1 as [Hgt0 Hlt1]. 
          destruct (Rle_lt_dec r 0) eqn: Hp0; destruct (Rle_lt_dec 1 r) eqn: Hp1; try assumption.
          - destruct H3. 
            assert (Hr: r = 1). { apply Rle_antisym; try assumption. }
            assert (Hcontra: 1<1). { rewrite Hr in Hlt1. assumption. }
            apply Rlt_irrefl in Hcontra. contradiction.
          - destruct H3. 
            assert (Hr: r = 0). { apply Rle_antisym; try assumption. }
            assert (Hcontra: 0<0). { rewrite Hr in Hgt0. assumption. }
            apply Rlt_irrefl in Hcontra. contradiction.
          - destruct H3. 
            assert (Hr: r = 1). { apply Rle_antisym; try assumption. }
            assert (Hcontra: 1<1). { rewrite Hr in Hlt1. assumption. }
            apply Rlt_irrefl in Hcontra. contradiction. }
          apply dom_subset_orb_fst_iff in Hsub_simpl. 
          destruct Hsub_simpl as [Hsub1 Hsub2]. 
          apply IHphi1 with (X:= X) in H4; try assumption. 
          apply IHphi2 with (X:= X) in H5; try assumption.
          left. split; try assumption. 
            exists (pd_emp X), (pd_emp X).
            split; try apply Valid_dist_nil. 
            split; try apply Valid_dist_nil. 
            split. { simpl. try apply dom_equiv_refl. } 
            split; try apply dom_equiv_refl.
            split; try assumption. 
            split; try assumption. 
            simpl. split; try reflexivity. 
            split; try reflexivity.
            apply dst_equiv_refl.
    + destruct Hq_case as [Hq_case2| Hq_case3]. 
      * subst. 
        assert (Hsub_simpl: is_domain_subset (get_var_in_Pformular phi1) X = true). { 
          destruct (Rle_lt_dec 1 0); destruct (Rle_lt_dec 1 1); try apply Rlt_irrefl in r0; try contradiction.
            * apply Rle_not_lt in r. unfold not in r. exfalso. apply r. apply Rlt_0_1. 
            * assumption. }  
        right. left. split; try reflexivity. 
        exists (pd_emp X).
        split; try apply Valid_dist_nil.
        split; try apply pd_equiv_refl.
        split. { apply IHphi1; try assumption. }
        split; try assumption. 
      * subst. 
        assert (Hsub_simpl: is_domain_subset (get_var_in_Pformular phi2) X = true). { 
          destruct (Rle_lt_dec 0 0); destruct (Rle_lt_dec 1 0); try apply Rlt_irrefl in r; try contradiction.
            * apply Rle_not_lt in r0. unfold not in r0. exfalso. apply r0. apply Rlt_0_1. 
            * assumption. }  
        right. right. split; try reflexivity.
        exists (pd_emp X).
        split; try apply Valid_dist_nil.
        split; try apply pd_equiv_refl.
        split; try apply IHphi2; try assumption. 
        simpl. reflexivity. 
  - inversion H; subst.
    right. left. 
    exists (pd_emp X). 
    split; try apply Valid_dist_nil.
    split; try apply pd_equiv_refl.
    apply dom_subset_orb_fst_iff in Hsub. destruct Hsub as [Hsub1 Hsub2].
    split; simpl; try assumption. 
    split; try reflexivity.
    apply IHphi1; try assumption.
  - inversion H; subst. 
    apply dom_subset_orb_fst_iff in Hsub. destruct Hsub as [Hsub1 Hsub2].
    apply IHphi1 with (X:= (get_var_in_Pformular phi1)) in H2; try apply dom_subset_refl.
    apply IHphi2 with (X:= (get_var_in_Pformular phi2)) in H3; try apply dom_subset_refl.
    exists (pd_emp (get_var_in_Pformular phi1)), (pd_emp (get_var_in_Pformular phi2)).
    simpl. exists H4.
    split; try apply Valid_dist_nil. 
    split; try apply Valid_dist_nil.
    split; try assumption.
    split; try assumption.
    split; simpl; try apply dst_equiv_refl.
    apply dom_subset_orb_fst_iff; split; try assumption. 
  - inversion H; subst. 
    apply dom_subset_orb_fst_iff in Hsub. destruct Hsub as [Hsub1 Hsub2].
    apply IHphi1 with (X:= X) in H2; try assumption. 
    apply IHphi2 with (X:= X) in H3; try assumption. 
    split; assumption.
Qed. 
(*************************The semantic properties of deterministic formulas*************************)

Theorem df_sem_conj_mu: 
  forall (dom : domain) (mu : dist_state) (s : partial_st) (p : R) df
         (Hpd0 : partial_dst_Prop dom [(s, p)])
         (Hpd' : partial_dst_Prop dom ((s, p) :: mu)),
    let pd0 := Build_partial_dist dom [(s,p)] Hpd0 in
    let pd' := Build_partial_dist dom ((s,p)::mu) Hpd' in 
    [[Pdeter df]] pd' ->
    [[Pdeter df]] pd0 /\ [[Pdeter df]] (Build_partial_dist dom mu (PD_inv s p mu dom Hpd')).
Proof.
  intros dom mu s p df Hpd0 Hpd' pd0 pd' Hsem. induction df.
  - inversion Hpd0; subst. inversion Hpd'; subst.
    split.
    + destruct Hsem as [Hdom Hsem]. split; try assumption.
      simpl in *. intros. apply orb_true_iff in H. 
      destruct H; try discriminate.
      specialize (Hsem st). apply Hsem. 
      unfold supp_mu. simpl. 
      rewrite insert_st_pair_fst_eq_insert_st.
      rewrite in_supp_insert_eq.
      apply orb_true_iff. left. assumption.
    + destruct Hsem as [Hdom Hsem]. split; try assumption.
      simpl in *. intros. 
      specialize (Hsem st). apply Hsem. 
      unfold supp_mu. simpl. 
      rewrite insert_st_pair_fst_eq_insert_st.
      rewrite in_supp_insert_eq.
      apply orb_true_iff. right. assumption.
  - split. 
    + simpl. destruct Hsem as [Hdom Hsem]. split; try assumption.
      intros. 
      apply orb_true_iff in H. 
      destruct H; try discriminate.
      specialize (Hsem st). apply Hsem. 
      unfold supp_mu. simpl. 
      rewrite insert_st_pair_fst_eq_insert_st.
      rewrite in_supp_insert_eq.
      apply orb_true_iff. left. assumption.
    + simpl in *. destruct Hsem as [Hdom Hsem]. split; try assumption.
      intros. 
      specialize (Hsem st). apply Hsem; try assumption. 
      unfold supp_mu. simpl. 
      rewrite insert_st_pair_fst_eq_insert_st.
      rewrite in_supp_insert_eq.
      apply orb_true_iff. right. assumption.
Qed. 

Lemma df_sem_linear_add: 
  forall pd0 pd1 pd df p1 p2, 
    (0 < p1 < 1) -> (0 < p2 < 1) ->  
    Valid_dist (mu pd0) -> Valid_dist (mu pd1) -> Valid_dist (mu pd) ->
    (dom pd0 == dom pd)%domain -> (dom pd1 == dom pd)%domain -> 
    (mu pd) == (p1 * (mu pd0) + p2 * (mu pd1))%dist_state ->  
    [[Pdeter df]] pd0 -> [[Pdeter df]] pd1 -> 
    [[Pdeter df]] pd.
Proof.
  intros pd0 pd1 pd df p1 p2 Hp1 Hp2 HWF0 HWF1 HWF Hdom0 Hdom1 Hmu Hsem0 Hsem1.
  simpl. destruct Hsem0 as [Hsub0 Hsem0]. destruct Hsem1 as [Hsub1 Hsem1]. split.
  - apply dom_subset_eq_compat_left with (Z:= (get_var_in_Dformular df)) in Hdom0; try assumption.
  - intros.
  apply in_supp_mu_app_or with (mu0:= p1 * (mu pd0)) (mu1:= p2 * (mu pd1)) in H; try assumption. 
    * inversion H.
      + apply Hsem0. destruct Hp1. rewrite <- supp_eq_mult_coef in H0; try assumption.  
      + apply Hsem1. destruct Hp2. rewrite <- supp_eq_mult_coef in H0; try assumption.
    * apply Valid_mult_cofe; try assumption. apply Rbound_loss. assumption.
    * apply Valid_mult_cofe; try assumption. apply Rbound_loss. assumption.
Qed.

Lemma df_sem_decom: 
  forall pd0 pd1 df p1 (Hdom: (dom pd0 == dom pd1)%domain), 
    (0 < p1 < 1) -> 
    Valid_dist (mu pd0) -> Valid_dist (mu pd1) -> 
    [[Pdeter df]] (pd_add (cofe_pd pd0 p1) (cofe_pd pd1 (1-p1)) Hdom) ->
    [[Pdeter df]] pd0 /\ [[Pdeter df]] pd1.
Proof. 
  intros pd0 pd1 df p1 Hdom Hp1 HWF0 HWF1 Hsem. split. 
  - simpl. destruct Hsem as [Hsub Hsem]. split. 
    + simpl in Hsub. assumption.
    + intros. apply Hsem. simpl. 
      apply in_supp_r_if_subset with (ls0:= (supp_mu (mu pd0))); try assumption.
      rewrite supp_eq_mult_coef with (p:= p1).
      * apply supp_mu_subset_decom_add_l. 
      * destruct Hp1. intuition.
  - simpl. destruct Hsem as [Hsub Hsem]. split. 
    + simpl in Hsub. 
    apply dom_subset_eq_compat_left with (X:= dom pd0); try assumption.
    + intros. apply Hsem. simpl. 
      apply in_supp_r_if_subset with (ls0:= (supp_mu (mu pd1))); try assumption.
      rewrite supp_eq_mult_coef with (p:= 1- p1).
      * apply supp_mu_subset_decom_add_r. 
      * destruct Hp1. intuition. 
      apply Rp_lt1_minus_p_bounds with (p:= p1). split; assumption.
Qed.

Lemma df_add_sem_decom: 
  forall pd0 pd1 pd df p1, 
    (0 < p1 < 1) -> 
    Valid_dist (mu pd0) -> Valid_dist (mu pd1) -> Valid_dist (mu pd) ->
    (dom pd0 == dom pd)%domain -> (dom pd1 == dom pd)%domain -> 
    (mu pd) == (p1 * (mu pd0) + (1-p1) * (mu pd1))%dist_state ->  
    [[Pdeter df]] pd ->
    [[Pdeter df]] pd0 /\ [[Pdeter df]] pd1.
Proof.
  intros pd0 pd1 pd df p1 Hp1 HWF0 HWF1 HWF Hdom0 Hdom1 Hmu Hsem. split.
  - simpl. destruct Hsem as [Hsub Hsem]. split.
    + apply dom_equiv_sym in Hdom0.
      apply dom_subset_eq_compat_left with (Z:= (get_var_in_Dformular df)) in Hdom0; try assumption. 
    + intros. apply Hsem. 
      apply in_supp_r_if_subset with (ls0:= (supp_mu (mu pd0))); try assumption. 
      apply dst_equiv_implies_beq_supp in Hmu; intuition.
      * apply supp_eq_implies_subset_conj in Hmu. destruct Hmu. 
        apply supp_subset_trans with (ls1:= (supp_mu (p1 * mu pd0 + (1 - p1) * mu pd1))); 
          try assumption; try apply Sort_supp_if_WF_supp; try assumption.
        rewrite supp_eq_mult_coef with (p:= p1); try assumption.
        apply supp_mu_subset_decom_add_l. 
      * apply Valid_linear; try assumption. 
      ** apply Rbound_loss. split; assumption.
      ** apply Rbound_loss. apply Rp_lt1_minus_p_bounds with (p:= p1). split; assumption.
      ** rewrite R_plus_sub_eq_1. apply Rle_refl.
  - simpl. destruct Hsem as [Hsub Hsem]. split.
    + apply dom_equiv_sym in Hdom1.
      apply dom_subset_eq_compat_left with (Z:= (get_var_in_Dformular df)) in Hdom1; try assumption. 
    + intros. apply Hsem. 
      apply in_supp_r_if_subset with (ls0:= (supp_mu (mu pd1))); try assumption. 
      apply dst_equiv_implies_beq_supp in Hmu; intuition.
      * apply supp_eq_implies_subset_conj in Hmu. destruct Hmu. 
        apply supp_subset_trans with (ls1:= (supp_mu (p1 * mu pd0 + (1 - p1) * mu pd1))); 
          try assumption; try apply Sort_supp_if_WF_supp; try assumption.
        rewrite supp_eq_mult_coef with (p:= 1-p1); try assumption.
      ** apply supp_mu_subset_decom_add_r. 
      ** apply Rp_lt1_minus_p_bounds with (p:= p1). split; assumption.
      * apply Valid_linear; try assumption. 
      ** apply Rbound_loss. split; assumption.
      ** apply Rbound_loss. apply Rp_lt1_minus_p_bounds with (p:= p1). split; assumption.
      ** rewrite R_plus_sub_eq_1. apply Rle_refl.
Qed.

(******************Coef and additive decomposition of phi probability formula semantics *******************************)
Lemma pd_equiv_preserves_sem: 
  forall pd0 pd1 phi,
    Valid_dist pd0.(mu) -> Valid_dist pd1.(mu) ->
    well_defined_Pf phi ->
    pd1 ≡ pd0 ->
    [[phi]] pd0 -> 
    [[phi]] pd1.
Proof.
  intros pd0 pd1 phi Hvalid0 Hvalid1 HWD Heq Hsem.
  generalize dependent pd1. generalize dependent pd0.
  induction phi as[| | | |].
  - simpl in *. intros. destruct Heq as [Hdom Hmu]. 
    split. 
    + apply dom_equiv_sym in Hdom. destruct Hsem. 
    apply dom_subset_eq_compat_left with (Z:= (get_var_in_Dformular d)) in Hdom; try assumption.
    + intros. apply Hsem. 
    apply dst_equiv_implies_beq_supp in Hmu; try assumption.
    rewrite in_supp_beq_supp_compat with (l1:= supp_mu (mu pd0)) in H; try assumption.
  - intros. destruct Heq as [Hdom Heq].
    assert (Hsum: sum_probs (mu pd1) = sum_probs (mu pd0)). {
        apply dst_equiv_implies_sum_probs_eq; try assumption. }
    destruct Hsem as [Hcase1 | Hsem]. 
    + destruct Hcase1 as [Hp_case1 H]. 
    destruct H as [pd01 H]. destruct H as [pd02 H].
    destruct H as [HWF01 H]. destruct H as [HWF02 H]. 
    destruct H as [Hdom01 H]. destruct H as [Hdom02 H].
    destruct H as [Hphi01 H]. destruct H as [Hphi02 H].
    destruct H as [Hsum01 H]. destruct H as [Hsum02 Hmu].
    simpl. left. split; try assumption. 
    exists pd01, pd02. 
    split; try assumption. 
    split; try assumption. 
    split. { apply dom_equiv_sym in Hdom. apply dom_equiv_trans with (l1:= dom pd0); try assumption. }
    split. { apply dom_equiv_sym in Hdom. apply dom_equiv_trans with (l1:= dom pd0); try assumption. }
    split; try assumption. 
    split; try assumption.
    split. { rewrite Hsum01. rewrite Hsum. reflexivity. } 
    split. { rewrite Hsum02. rewrite Hsum. reflexivity. }
    apply dst_equiv_trans with (mu1:= mu pd0); try assumption.
    + destruct Hsem as [Hcase2| Hcase3].
      * destruct Hcase2 as [Hp_case2 H]. destruct H as [pd01 H]. 
      destruct H as [HWF01 H]. destruct H as [Heq01 H]. 
      destruct H as [Hsub2 H]. 
      simpl. right. left. split; try assumption.
      exists pd01. split; try assumption.
      split. { 
        apply pd_equiv_trans with (pd1:= pd0); try assumption. 
        apply pd_equiv_sym. split; try assumption. }
      split; try assumption.
      rewrite Hsum. assumption.
      * destruct Hcase3 as [Hp_case3 H]. destruct H as [pd02 H]. 
      destruct H as [HWF02 H]. destruct H as [Heq02 H]. 
      destruct H as [Hsub1 H]. 
      simpl. right. right. split; try assumption.
      exists pd02. split; try assumption.
      split. { 
        apply pd_equiv_trans with (pd1:= pd0); try assumption. 
        apply pd_equiv_sym. split; try assumption. }
      split; try assumption.
      rewrite Hsum. assumption.
  - intros. destruct Heq as [Hdom Heq].
    assert (Hsum: sum_probs (mu pd1) = sum_probs (mu pd0)). {
        apply dst_equiv_implies_sum_probs_eq; try assumption. }
    destruct Hsem as [Hcase1 | Hsem]. 
    + destruct Hcase1 as [p1 H]. destruct H as [p2 H]. 
    destruct H as [Hp1 H]. destruct H as [Hp2 H].
    destruct H as [Hsump H]. 
    destruct H as [pd01 H]. destruct H as [pd02 H].
    destruct H as [HWF01 H]. destruct H as [HWF02 H]. 
    destruct H as [Hdom01 H]. destruct H as [Hdom02 H].
    destruct H as [Hphi01 H]. destruct H as [Hphi02 H].
    destruct H as [Hsum01 H]. destruct H as [Hsum02 Hmu].
    simpl. left. 
    exists p1, p2. split; try assumption. 
    split; try assumption. split; try assumption. 
    exists pd01, pd02. 
    split; try assumption. 
    split; try assumption. 
    split. { apply dom_equiv_sym in Hdom. apply dom_equiv_trans with (l1:= dom pd0); try assumption. }
    split. { apply dom_equiv_sym in Hdom. apply dom_equiv_trans with (l1:= dom pd0); try assumption. }
    split; try assumption. 
    split; try assumption.
    split. { rewrite Hsum01. rewrite Hsum. reflexivity. } 
    split. { rewrite Hsum02. rewrite Hsum. reflexivity. }
    apply dst_equiv_trans with (mu1:= mu pd0); try assumption.
    + destruct Hsem as [Hcase2| Hcase3].
      * destruct Hcase2 as [pd01 H]. destruct H as [HWF01 H]. 
      destruct H as [Heq01 H]. 
      destruct H as [Hsub2 H]. 
      destruct H as [Hphi01 Hsum01]. 
      simpl. right. left. 
      exists pd01. split; try assumption.
      split. { 
        apply pd_equiv_trans with (pd1:= pd0); try assumption. 
        apply pd_equiv_sym. split; try assumption. }
      split. {
        apply dom_subset_eq_compat_left with (X:= dom pd0); try assumption.
        apply dom_equiv_sym. assumption. }
      split; try assumption.
      rewrite Hsum. assumption.
      * destruct Hcase3 as [pd02 H]. destruct H as [HWF02 H].
      destruct H as [Heq02 H]. 
      destruct H as [Hsub1 H]. 
      destruct H as [Hphi02 Hsum02]. 
      simpl. right. right. 
      exists pd02. split; try assumption.
      split. { 
        apply pd_equiv_trans with (pd1:= pd0); try assumption. 
        apply pd_equiv_sym. split; try assumption. }
      split. {
        apply dom_subset_eq_compat_left with (X:= dom pd0); try assumption.
        apply dom_equiv_sym. assumption. }
      split; try assumption.
      rewrite Hsum. assumption.
  - intros. simpl in *. 
    destruct Hsem as [pd01 H]. destruct H as [pd02 H].
    destruct H as [Hdom_int H]. 
    destruct H as [Hvalid01 H]. destruct H as [Hvalid02 H].
    destruct H as [Hphi01 H]. destruct H as [Hphi02 H]. 
    exists pd01, pd02. exists Hdom_int. intuition.
    destruct H. simpl in H. simpl in H0.
    destruct Heq as [Hdom_eq Hmu_eq].
    split; simpl. 
    + apply dom_equiv_sym in Hdom_eq. 
      apply dom_subset_eq_compat_left with 
        (Z:= (orb_domain (dom pd01) (dom pd02))) in Hdom_eq; try assumption.
    + apply dst_equiv_trans with 
        (mu1:= (mu pd0 \| (orb_domain (dom pd01) (dom pd02)))); try assumption.
      apply Peq_implies_res_eq; try assumption.
  - intros. simpl in *. destruct Hsem. inversion HWD; subst.
    split; [apply IHphi1 with (pd0:= pd0); try assumption|
            apply IHphi2 with (pd0:= pd0); try assumption].
Qed. 

Lemma sem_mult_cofe: (*lemma 3*)
  forall pd phi p,  
    0 <= p -> well_defined_Pf phi ->
    Valid_dist (mu pd) ->
    0 <= sum_probs (p * (mu pd)) <= 1-> 
    [[phi]] pd ->
    [[phi]] (Build_partial_dist (dom pd) (p * (mu pd)) (pd_mult_preserve_PD pd p)). 
Proof. 
  intros pd phi p Hp HWD HWF Hsum Hsem.
  inversion Hp as [Hp0| Hp0].
  { generalize dependent pd. generalize dependent p. 
    induction phi as [| | | |].
    * simpl in *. intros. 
      destruct Hsem as [Hvalid Hsem]. 
      split; try assumption. 
      intros. apply Hsem. 
      assert (Hsupp_eq: supp_mu (mu pd) = supp_mu (p * (mu pd))). { 
        apply supp_eq_mult_coef; try assumption. }
      rewrite <- Hsupp_eq in H. assumption.
    * intros. simpl in Hsem. destruct Hsem as [Hcase1 | Hsem]. 
      - destruct Hcase1 as [Hq_case1 H]. destruct H as [pd1 H]. destruct H as [pd2 H].
        destruct H as [Hvalid1 H]. destruct H as [Hvalid2 H].
        destruct H as [Hdom1 H]. destruct H as [Hdom2 H].
        destruct H as [Hphi1 H]. destruct H as [Hphi2 H]. 
        destruct H as [Hsum1 H]. destruct H as [Hsum2 Hmu].
        simpl. left. split; try assumption. 
        pose (pd1':= Build_partial_dist (dom pd1) (p * (mu pd1)) (pd_mult_preserve_PD pd1 p)).
        pose (pd2':= Build_partial_dist (dom pd2) (p * (mu pd2)) (pd_mult_preserve_PD pd2 p)).
        exists pd1', pd2'. 
        assert (Hsum1_p: 0 <= sum_probs (p * (mu pd1)) <= 1). { 
            rewrite dst_sum_prob_coef_mult.
            rewrite dst_sum_prob_coef_mult in Hsum. 
            rewrite <- Hsum1 in Hsum. assumption. }
        assert (Hsum2_p: 0 <= sum_probs (p * (mu pd2)) <= 1). { 
            rewrite dst_sum_prob_coef_mult.
            rewrite dst_sum_prob_coef_mult in Hsum. 
            rewrite <- Hsum2 in Hsum. assumption. }
        split; try apply Valid_mult_under_eq_prob; try assumption.
        split; try apply Valid_mult_under_eq_prob; try assumption.
        split. { simpl. assumption. }
        split. { simpl. assumption. }
        inversion HWD; subst.
        split. { try apply IHphi1; try assumption. }
        split. { try apply IHphi2; try assumption. }
        simpl. repeat rewrite dst_sum_prob_coef_mult. rewrite Hsum1. rewrite Hsum2. 
        split; try reflexivity. 
        split; try reflexivity.
        rewrite dst_mult_comm_eq. rewrite dst_mult_comm_eq with (mu:= mu pd2).
        rewrite <- dst_mult_plus_distr_r_eq. apply dst_mult_preserves_equiv. 
        try assumption.
      - destruct Hsem as [Hcase2 | Hcase3]. 
        + simpl. right. left. destruct Hcase2 as [Hq_case2 H]. 
        destruct H as [pd1 H]. destruct H as [Hvalid1 H]. 
        destruct H as [Heq1 H]. 
        destruct H as [Hphi1 Hsum1].
        split; try assumption. 
        pose (pd1':= Build_partial_dist (dom pd1) (p * (mu pd1)) (pd_mult_preserve_PD pd1 p)).
        exists pd1'. 
        assert (Hsum1_p: 0 <= sum_probs (p * (mu pd1)) <= 1). { 
            rewrite dst_sum_prob_coef_mult.
            rewrite dst_sum_prob_coef_mult in Hsum. 
            rewrite <- Hsum1 in Hsum. assumption. }
        split; try apply Valid_mult_under_eq_prob; try assumption.
        split. { destruct Heq1. split; simpl; try assumption. apply dst_mult_preserves_equiv; assumption. }
        inversion HWD; subst.
        split. { apply IHphi1; try assumption. }
        simpl. repeat rewrite dst_sum_prob_coef_mult. rewrite Hsum1. reflexivity.
        + simpl. right. right. destruct Hcase3 as [Hq_case3 H]. 
        destruct H as [pd1 H]. destruct H as [Hvalid1 H]. 
        destruct H as [Heq1 H]. 
        destruct H as [Hphi1 Hsum1].
        split; try assumption. 
        pose (pd1':= Build_partial_dist (dom pd1) (p * (mu pd1)) (pd_mult_preserve_PD pd1 p)).
        exists pd1'. 
        assert (Hsum1_p: 0 <= sum_probs (p * (mu pd1)) <= 1). { 
            rewrite dst_sum_prob_coef_mult.
            rewrite dst_sum_prob_coef_mult in Hsum. 
            rewrite <- Hsum1 in Hsum. assumption. }
        split; try apply Valid_mult_under_eq_prob; try assumption.
        split. { destruct Heq1. split; simpl; try assumption. apply dst_mult_preserves_equiv; assumption. }
        inversion HWD; subst.
        split. { apply IHphi2; try assumption. }
        simpl. repeat rewrite dst_sum_prob_coef_mult. rewrite Hsum1. reflexivity.
    * intros. simpl in *. destruct Hsem as [Hcase1 | Hsem]. 
      { destruct Hcase1 as [p1 H]. destruct H as [p2 H]. 
        destruct H as [Hp1 H]. destruct H as [Hp2 H].
        destruct H as [Hp12 H]. destruct H as [pd1 H]. destruct H as [pd2 H].
        destruct H as [Hvalid1 H]. destruct H as [Hvalid2 H].
        destruct H as [Hdom1 H]. destruct H as [Hdom2 H].
        destruct H as [Hphi1 H]. destruct H as [Hphi2 H].
        destruct H as [Hsum1 H]. destruct H as [Hsum2 Hmu].
        left. exists p1,p2. split; try assumption. 
        split; try assumption. split; try assumption.
        pose (pd1':= Build_partial_dist (dom pd1) (p * (mu pd1)) (pd_mult_preserve_PD pd1 p)).
        pose (pd2':= Build_partial_dist (dom pd2) (p * (mu pd2)) (pd_mult_preserve_PD pd2 p)).
        exists pd1', pd2'. 
        assert (Hsum1_p: 0 <= sum_probs (p * (mu pd1)) <= 1). { 
            rewrite dst_sum_prob_coef_mult.
            rewrite dst_sum_prob_coef_mult in Hsum. 
            rewrite <- Hsum1 in Hsum. assumption. }
        assert (Hsum2_p: 0 <= sum_probs (p * (mu pd2)) <= 1). { 
            rewrite dst_sum_prob_coef_mult.
            rewrite dst_sum_prob_coef_mult in Hsum. 
            rewrite <- Hsum2 in Hsum. assumption. } 
        split; try apply Valid_mult_under_eq_prob; try assumption.
        split; try apply Valid_mult_under_eq_prob; try assumption.
        split. { simpl. assumption. }
        split. { simpl. assumption. }
        inversion HWD; subst.
        split. { apply IHphi1; try assumption. }
        split. { apply IHphi2; try assumption. }
        simpl. repeat rewrite dst_sum_prob_coef_mult. rewrite Hsum1. rewrite Hsum2. 
        split; try reflexivity. 
        split; try reflexivity.
        rewrite dst_mult_comm_eq. rewrite dst_mult_comm_eq with (mu:= mu pd2).
        rewrite <- dst_mult_plus_distr_r_eq. apply dst_mult_preserves_equiv. 
        try assumption.
      }
      destruct Hsem as [Hcase2 | Hcase3]. 
        + simpl. right. left. destruct Hcase2 as [pd1 H]. 
          destruct H as [Hvalid1 H]. destruct H as [Heq1 H]. 
          destruct H as [Hdom1 H]. 
          destruct H as [Hphi1 Hsum1].
          pose (pd1':= Build_partial_dist (dom pd1) (p * (mu pd1)) (pd_mult_preserve_PD pd1 p)).
          exists pd1'.
          assert (Hsum1_p: 0 <= sum_probs (p * (mu pd1)) <= 1). { 
            rewrite dst_sum_prob_coef_mult. 
            rewrite dst_sum_prob_coef_mult in Hsum. 
            rewrite <- Hsum1 in Hsum. assumption. }
          split; try apply Valid_mult_under_eq_prob; try assumption.
          split. { destruct Heq1. split; simpl; try assumption. apply dst_mult_preserves_equiv; assumption. }
          split. { simpl. assumption. }
          inversion HWD; subst.
          split. { apply IHphi1; try assumption. }
          simpl. repeat rewrite dst_sum_prob_coef_mult. rewrite Hsum1. reflexivity.
        + simpl. right. right. destruct Hcase3 as [pd1 H]. 
          destruct H as [Hvalid1 H]. destruct H as [Heq1 H]. 
          destruct H as [Hdom1 H]. 
          destruct H as [Hphi1 Hsum1].
          pose (pd1':= Build_partial_dist (dom pd1) (p * (mu pd1)) (pd_mult_preserve_PD pd1 p)).
          exists pd1'.
          assert (Hsum1_p: 0 <= sum_probs (p * (mu pd1)) <= 1). { 
            rewrite dst_sum_prob_coef_mult. 
            rewrite dst_sum_prob_coef_mult in Hsum. 
            rewrite <- Hsum1 in Hsum. assumption. }
          split; try apply Valid_mult_under_eq_prob; try assumption.
          split. { destruct Heq1. split; simpl; try assumption. apply dst_mult_preserves_equiv; assumption. }
          split. { simpl. assumption. }
          inversion HWD; subst.
          split. { apply IHphi2; try assumption. }
          simpl. repeat rewrite dst_sum_prob_coef_mult. rewrite Hsum1. reflexivity.
    * intros. simpl in Hsem. 
      destruct Hsem as [pd1 H]. destruct H as [pd2 H]. 
      destruct H as [Hvar H]. destruct H as [Hvalid1 H]. destruct H as [Hvalid2 H].
      destruct H as [Hphi1 H]. destruct H as [Hphi2 Hsub].
      simpl. 
      pose (A:= sum_probs (mu pd1)). pose (B:= sum_probs (mu pd2)). 
      pose (C:= sum_probs (mu pd)). destruct pd2 as [dom2 mu2 HPD2].
      destruct mu2 as [|(s2,p2) mu2].
      - simpl in *. destruct Hsub. simpl in H. simpl in H0.
      rewrite combine_nil_r_eq in H0. 
      assert (H': (mu pd) = []). {
          apply dst_res_nil_implies_nil with (X:= (orb_domain (dom pd1) (dom2))).
          apply dst_eq_nil_iff. split; try assumption. 
          apply Valid_after_resX. try assumption. }
      pose (pd1':= pd_emp (dom pd1)).
      pose (pd2':= pd_emp (dom2)).
      exists pd1', pd2'. simpl. exists Hvar. 
      split; try apply Valid_dist_nil.
      split; try apply Valid_dist_nil.
      inversion HWD; subst.
      split. { apply emp_dst_satisfies_phi; try assumption. apply satisfy_implies_dom_sub; assumption. }
      split. { try apply emp_dst_satisfies_phi; try assumption. apply satisfy_implies_dom_sub in Hphi2; assumption. }
      split; simpl; try assumption. 
      rewrite H'. simpl. apply dst_equiv_refl.
      - pose (pd1':= Build_partial_dist (dom pd1) ((p*B) * mu pd1) (pd_mult_preserve_PD pd1 (p*B))).
        pose (pd2:= Build_partial_dist dom2 ((s2,p2)::mu2) HPD2).
        pose (pd2':= Build_partial_dist (dom pd2) ((/B) * (mu pd2)) 
                        (pd_mult_preserve_PD pd2 (/B))).
        exists pd1', pd2'. exists Hvar.
        assert (HC: C = (A * B)%R). { 
          unfold C. rewrite sum_eq_after_res with (X:= (orb_domain (dom pd1) dom2)).
          unfold A. unfold B. rewrite <- sum_probs_combine_eq_mult.
          apply dst_equiv_implies_sum_probs_eq; try assumption.
          - apply Valid_after_resX. assumption.
          - apply Valid_after_combine; assumption.
          - destruct Hsub. simpl in *. assumption. }
        assert (HBp: 0 <= p * B). { 
          apply Rmult_le_pos; try assumption. 
          destruct Hvalid2. destruct H. apply positive_sum_ge_0. assumption. }
        assert (Hsum1: 0 <= sum_probs (p * B * mu pd1) <= 1). { 
          rewrite dst_sum_prob_coef_mult. fold A.
          rewrite Rmult_assoc. rewrite <- Rmult_comm with (r1:= A).
          rewrite <- HC. rewrite dst_sum_prob_coef_mult in Hsum. assumption. }
        split; try apply Valid_mult_under_eq_prob; try assumption.
        assert (HBgt0: 0 < B). {
          unfold B. simpl. destruct Hvalid2. destruct H0. destruct H0. 
          apply Rplus_lt_le_0_compat; try assumption.
          apply positive_sum_ge_0. assumption. }
        assert (HB0: 0 < / B). { apply Rinv_0_lt_compat. assumption. }
        assert (Hsum2: 0 <= sum_probs (/ B * ((s2, p2) :: mu2)) <= 1). { 
          rewrite dst_sum_prob_coef_mult. unfold B. simpl.
          rewrite <- Rinv_l_sym with (r:= (p2 + sum_probs mu2)%R). 
          - split; try apply Rle_refl. apply Rle_0_1.
          - unfold not. intros. unfold B in HBgt0. simpl in HBgt0. 
            rewrite H in HBgt0. apply Rlt_irrefl in HBgt0. assumption. }
        split; try apply Valid_mult_under_eq_prob; try apply Rlt_le; try assumption.
        inversion HWD; subst.
        assert (HBp0: 0 < p * B). { apply Rmult_lt_0_compat; assumption. }
        assert(HBp_neq0: / B <> 0). { 
          unfold not. intros. rewrite H in HB0. apply Rlt_irrefl in HB0. assumption. }
        split. { try apply IHphi1; try assumption. }
        split. { apply IHphi2; try apply Rlt_le; try assumption. }
        destruct Hsub. simpl in H. simpl in H0.
        split. 
        -- simpl. assumption.
        -- simpl. destruct (Req_dec_T (/ B) 0) eqn: Hp_B. 
          + rewrite e in HBp_neq0. contradiction.
          + rewrite res_dst_to_X_mult_coef. 
            rewrite <- dst_cons_mult_distr; try assumption.
            rewrite combine_mult_l_assoc_eq; try assumption.
            rewrite combine_mult_r_assoc_eq; try assumption.
            rewrite dst_mult_assoc_eq.
            rewrite Rmult_assoc. 
            assert (HB': B <> 0). {
              unfold not. intros. rewrite H4 in HBgt0. apply Rlt_irrefl in HBgt0. assumption. }
            rewrite Rinv_r; try assumption. 
            rewrite Rmult_1_r.
            apply dst_mult_preserves_equiv. assumption.
    * intros. simpl in Hsem. destruct Hsem. simpl. 
      inversion HWD; subst. split.
      + apply IHphi1; assumption. + apply IHphi2; assumption.
  }
  assert (Hde: {| dom := dom pd; mu := p * mu pd; all_partial := pd_mult_preserve_PD pd p |} ≡ 
                (pd_emp (dom pd))). {
                  split; simpl in *.
                  - apply dom_equiv_refl.
                  - rewrite <- Hp0. rewrite dst_mult_0_l. apply dst_equiv_refl. }
  apply pd_equiv_preserves_sem with (phi:= phi) in Hde; try assumption.
    + simpl. apply Valid_dist_nil.
    + simpl. apply Valid_mult_under_eq_prob; try assumption.
    + apply emp_dst_satisfies_phi; try assumption. apply satisfy_implies_dom_sub; assumption. 
Qed. 

(*The semantic properties of partial states*)
Lemma st_eq_implies_df_sem: forall s s' df, 
  beq_state s s' = true -> df_sem df s -> 
  df_sem df s'.
Proof.
  intros. generalize dependent s'. generalize dependent s. 
  induction df; intros.
  - simpl in *. intros. destruct H0.
    assert (Hdom': is_domain_subset (get_variables_in_bexp b) (return_domain s') = true). {
      apply st_eq_implies_dom_equiv in H. 
      apply dom_subset_eq_compat_left with (Z:= (get_variables_in_bexp b)) in H; try assumption. }
    split; try assumption.
    assert (Hbs: evalB_st b s = evalB_st b s'). {
      apply st_eq_implies_evalB with (b:= b) in H. assumption. } 
    rewrite <- Hbs. assumption.
  - simpl in *. inversion H0.
      assert (Hdom': is_domain_subset (get_var_in_Dformular df) (return_domain s') = true). {
        apply st_eq_implies_dom_equiv in H. 
        apply dom_subset_eq_compat_left with (Z:= (get_var_in_Dformular df)) in H; try assumption. }
      split; try assumption. 
      destruct H2. exists x. 
      apply st_eq_implies_update_eq with (x:= n) (n1:= x) (n2:= x) in H; 
      try reflexivity.
      apply IHdf with (s:= (update s n x)); assumption.
Qed.

Lemma df_sem_iff_res_st: forall s df, 
  well_defined_Df df ->
  (df_sem df s) <-> 
  (df_sem df (res_st_to_X s (get_var_in_Dformular df))).
Proof. 
  intros s df HWD. split. 
  { intros Hsem. generalize dependent s.
    induction df; intros. 
    - simpl in *. destruct Hsem. split.
      + apply res_dom_eq_iff_subset in H. 
        apply dom_subset_eq_compat_right with 
          (Z:= (return_domain (res_st_to_X s (get_variables_in_bexp b)))) in H;
          try assumption.
        apply dom_subset_refl.
      + apply res_dom_eq_iff_subset in H. 
        destruct (evalB_st b s) eqn: Hs. 
        * rewrite <- evalB_eq_res_st in Hs. rewrite Hs. assumption.
        * rewrite <- evalB_eq_res_st in Hs. rewrite Hs. assumption.
    - inversion HWD; subst. destruct Hsem. 
      destruct H0. 
        simpl. 
        split. { apply res_dom_eq_iff_subset in H. destruct H. try assumption. }
        exists x. 
        apply update_eq_res_st with (s:=s) (q:=x) in H1.
        apply st_eq_implies_df_sem with (df:= df) in H1; try assumption.
        apply IHdf; assumption. }
  intros Hsem. generalize dependent s.
  induction df; intros. 
  - simpl in *. destruct Hsem. split; try assumption.
    + apply dom_subset_trans with (l1:= (return_domain (res_st_to_X s (get_variables_in_bexp b))));
      try assumption. apply res_dom_subst.
    + rewrite evalB_eq_res_st in H0. assumption. 
  - inversion HWD; subst. inversion Hsem. 
    destruct H0. 
      split; try assumption. { 
        apply dom_subset_trans with (l1:= (return_domain (res_st_to_X s (get_var_in_Dformular df))));
          try apply res_dom_subst; try assumption. }
    exists x. 
    apply IHdf; try assumption.
    apply update_eq_res_st with (s:=s) (q:=x) in H1.
    rewrite state_eq_sym in H1.
    apply st_eq_implies_df_sem with (df:= df) in H1; try assumption.
Qed.

Lemma df_sem_res_df_iff_res_V: forall df V s,
  well_defined_Df df ->
  is_domain_subset (get_var_in_Pformular (Pdeter df)) V = true ->
  is_domain_subset V (return_domain s) = true ->
  df_sem df (res_st_to_X s (get_var_in_Dformular df)) <->
  df_sem df (res_st_to_X s V).
Proof. 
  intros df V s HWD. split. { 
    intros. generalize dependent s. generalize dependent V.
    induction df; intros. 
    - simpl. intros. simpl in H. simpl in H1.
      assert (Hdom: is_domain_subset (get_variables_in_bexp b) (return_domain s) = true). { 
        apply dom_subset_trans with (l1:= V); try assumption. }
      apply res_dom_eq_iff_subset in Hdom. destruct Hdom. 
      destruct H1. split; try assumption.
      + apply dom_subset_eq_compat_left with (X:= V); try assumption.
        apply dom_equiv_sym. apply res_dom_eq_iff_subset. assumption.
      + rewrite <- evalB_st_preserve_bool; try assumption.
    - inversion HWD; subst. 
      * simpl. 
        destruct H1 as [Hsub_ndf Hx]. destruct Hx as [x Hsem_up]. 
        split. { 
          simpl in *. 
          apply dom_subset_trans with 
            (l1:= (return_domain (res_st_to_X s (get_var_in_Dformular df))));
              try apply res_dom_subst; try assumption. 
          apply subst_implies_res_subst. assumption.
        }
        exists x. 
        assert (Hsub': is_domain_subset (singleton_bool_list n) V = true). {
          apply dom_subset_trans with (l1:= (get_var_in_Dformular df)); 
            try assumption. }
        assert (Heq: (res_st_to_X (update s n x) V == update (res_st_to_X s V) n x)%state). {
          apply update_eq_res_st with (s:= s) (q:= x) in Hsub'. assumption. }
        apply st_eq_implies_df_sem with (df:= df) in Heq; try assumption.
        apply IHdf; try assumption.
          + apply dom_subset_trans with (l1:= (return_domain s)); try assumption.
          apply update_subst_implies_dom_eq. 
          + assert (Heq': ((res_st_to_X (update s n x) (get_var_in_Dformular df)) ==
                          (update (res_st_to_X s (get_var_in_Dformular df)) n x))%state). { 
              apply update_eq_res_st with (s:= s) (q:= x) in H4. assumption. }
          rewrite state_eq_sym in Heq'.
          apply st_eq_implies_df_sem with (df:= df) in Heq'; try assumption.
  }
  intros Hsem_res. generalize dependent s. generalize dependent V.
  induction df; intros.
  - inversion HWD; subst. apply df_sem_iff_res_st in Hsem_res; try assumption. 
    assert (Heq: ((res_st_to_X (res_st_to_X s V) (get_var_in_Dformular (Dpred b))) == 
    (res_st_to_X s (get_var_in_Dformular (Dpred b))))%state). {
      apply st_conti_res_eq with (s:= s) in H.
      rewrite state_eq_sym. try assumption. }
    apply st_eq_implies_df_sem with (s:= res_st_to_X (res_st_to_X s V) (get_var_in_Dformular (Dpred b))); try assumption.
  - inversion HWD; subst. inversion Hsem_res. 
    destruct H2 as [x Hdf].
    split. { simpl. simpl in H.
        assert (H': is_domain_subset (get_var_in_Dformular df) (return_domain s) = true). {
          apply dom_subset_trans with (l1:= V); try assumption. }
        apply res_dom_eq_iff_subset in H'. destruct H'. assumption. 
      } 
      exists x. 
      assert (Heq': ((res_st_to_X (update s n x) (get_var_in_Dformular df)) ==
                    (update (res_st_to_X s (get_var_in_Dformular df)) n x))%state). { 
          apply update_eq_res_st with (s:= s) (q:= x) in H3. assumption. }
      rewrite state_eq_sym in Heq'.
      rewrite state_eq_sym in Heq'.
      apply st_eq_implies_df_sem with (df:= df) in Heq'; try assumption.
      simpl in H. apply IHdf with (V:= V); try assumption. 
      * apply dom_subset_trans with (l1:= (return_domain s)); try assumption.
        apply update_subst_implies_dom_eq. 
      * assert (Hsub': is_domain_subset (singleton_bool_list n) V = true). { 
        apply dom_subset_trans with (l1:= (get_var_in_Dformular df)); try assumption. }
      assert (Heq: (res_st_to_X (update s n x) V == update (res_st_to_X s V) n x)%state). {
        apply update_eq_res_st with (s:= s) (q:= x) in Hsub'. assumption. }
      rewrite state_eq_sym in Heq.
      apply st_eq_implies_df_sem with (df:= df) in Heq; try assumption.
Qed.  
Lemma df_sem_iff_res_V: forall df V s, 
  well_defined_Df df ->
  is_domain_subset (get_var_in_Pformular (Pdeter df)) V = true ->
  is_domain_subset V (return_domain s) = true ->
  df_sem df s <->
  df_sem df (res_st_to_X s V).
Proof.
  intros. split. 
  - intros. apply df_sem_res_df_iff_res_V; try assumption.
  apply df_sem_iff_res_st in H2; assumption. 
  - intros. apply df_sem_res_df_iff_res_V in H2; try assumption.
  apply df_sem_iff_res_st in H2; assumption. 
Qed.
Open Scope dstate_scope.

Lemma df_sem_resV_implies_pd: (*determinated version of lemma 4 *)
  forall pd df V (HV: is_domain_subset V pd.(dom) = true),
    well_defined_Pf (Pdeter df) ->
    is_domain_subset (get_var_in_Pformular (Pdeter df)) V = true -> 
    [[Pdeter df]] (Build_partial_dist V (pd.(mu) \| V) 
                    (PD_after_res V (dom pd) (mu pd) HV (pd.(all_partial)))) -> 
    [[Pdeter df]] pd.
Proof. 
  intros pd df V HV HWD Hsub_Vdf Hsem. 
  destruct Hsem as [Hdom Hsem].
  simpl in Hdom. simpl in Hsem. split.
  - apply dom_subset_trans with (l1:= V); try assumption.
  - simpl. intros. specialize (Hsem (res_st_to_X st V)).
    assert (Hin: is_in_supp (res_st_to_X st V) (supp_mu ((mu pd) \| V)) = true). {
      apply supp_after_res; try assumption.  }
    specialize (Hsem Hin).
    inversion HWD; subst. apply df_sem_iff_res_st; try assumption.
    apply df_sem_res_df_iff_res_V with (V:= V); try assumption.
    apply in_supp_return_domain_eq in H. 
    apply dom_equiv_sym in H.
    apply dom_subset_eq_compat_left with (Z:= V) in H; try assumption.
Qed. 

Lemma sem_resV_implies_pd: (*One side of lemma 4 *)
  forall pd phi V (HV: is_domain_subset V pd.(dom) = true), 
    Valid_dist pd.(mu) -> 
    well_defined_Pf phi ->
    is_domain_subset (get_var_in_Pformular phi) V = true ->
    [[phi]] (Build_partial_dist V (pd.(mu) \| V) 
                    (PD_after_res V (dom pd) (mu pd) HV (pd.(all_partial)))) ->
    [[phi]] pd.
Proof. 
  intros pd phi V HV HWF HWD Hsub Hsem. 
  generalize dependent pd. generalize dependent V. 
  induction phi; intros.
  - apply df_sem_resV_implies_pd with (V:= V) (HV:= HV); try assumption.
  - simpl in Hsem. destruct Hsem as [Hcase1 | Hsem].
    + simpl. left. destruct Hcase1 as [Hp_case1 H]. 
    destruct H as [pd1 H]. destruct H as [pd2 H]. 
    destruct H as [HWF1 H]. destruct H as [HWF2 H].
    destruct H as [Hdom1 H]. destruct H as [Hdom2 H].
    destruct H as [Hsem1 H]. destruct H as [Hsem2 H]. 
    destruct H as [Hsum1 H].  destruct H as [Hsum2 Hmu].
    split; try assumption. 
    assert (Hp_minus: 0 < 1- r < 1). { apply Rp_lt1_minus_p_bounds with (p:= r). assumption. }
    assert (HWFV: Valid_dist ((mu pd) \| V)). { apply Valid_after_resX with (X:= V) in HWF. assumption. }
    assert (HSspV: Sorted_supp (supp_mu ((mu pd) \| V))). {
      apply Sort_supp_if_WF_supp. }
    assert (HWF_linear: Valid_dist (r * mu pd1 + (1 - r) * mu pd2)). {
      apply Valid_linear_under_eq_prob; try assumption.
      - destruct Hp_case1. apply Rlt_le. assumption.
      - destruct Hp_minus. apply Rlt_le. assumption.
      - rewrite Hsum1. rewrite Hsum2. rewrite <- Rmult_plus_distr_r.
      rewrite R_plus_sub_eq_1. rewrite Rmult_1_l.
      destruct HWFV. assumption. }
    assert (Hsupp: (supp_mu ((mu pd) \| V) == supp_mu (r * mu pd1 + (1 - r) * mu pd2))%supp). {
      apply dst_equiv_implies_beq_supp; try assumption. }
    assert (Hspsub: is_supp_subset (supp_mu (mu pd1)) (supp_mu ((mu pd) \| V)) = true /\ 
                    is_supp_subset (supp_mu (mu pd2)) (supp_mu ((mu pd) \| V)) = true ). {
      apply supp_eq_implies_subset_conj in Hsupp. destruct Hsupp. 
      apply supp_mu_subset_decom_l in H0; try assumption.
      - destruct Hp_case1. destruct Hp_minus. destruct H0.
        rewrite <- supp_eq_mult_coef in H0; try assumption.
        rewrite <- supp_eq_mult_coef in H5; try assumption.
        split; try assumption. }
    destruct Hspsub. 
    pose (pd1':= Build_partial_dist (dom pd) (bulid_dst_sub (mu pd1) (mu pd) V) 
                    (PD_bulid_proj pd1 pd V)).
    pose (pd2':= Build_partial_dist (dom pd) (bulid_dst_sub (mu pd2) (mu pd) V) 
                    (PD_bulid_proj pd2 pd V)).
    assert (HWF1': Valid_dist (mu pd1')). { apply WF_dist_after_bulid_mu; try assumption. }
    assert (HWF2': Valid_dist (mu pd2')). { apply WF_dist_after_bulid_mu; try assumption. }
    exists pd1', pd2'. 
    split; try assumption.
    split; try assumption.
    split. { simpl. apply dom_equiv_refl. }
    split. { simpl. apply dom_equiv_refl. }
    split. { 
      inversion HWD; subst. 
      simpl in Hsub. destruct Hp_case1 as [Hgt0 Hlt1].
      destruct (Rle_lt_dec r 0) eqn: Hp0; destruct (Rle_lt_dec 1 r) eqn: Hp1.
      - destruct H4. 
        assert (Hr: r = 1). { apply Rle_antisym; try assumption. }
        assert (Hcontra: 1<1). { rewrite Hr in Hlt1. assumption. }
        apply Rlt_irrefl in Hcontra. contradiction.
      - destruct H4. 
        assert (Hr: r = 0). { apply Rle_antisym; try assumption. }
        assert (Hcontra: 0<0). { rewrite Hr in Hgt0. assumption. }
        apply Rlt_irrefl in Hcontra. contradiction.
      - destruct H4. 
        assert (Hr: r = 1). { apply Rle_antisym; try assumption. }
        assert (Hcontra: 1<1). { rewrite Hr in Hlt1. assumption. }
        apply Rlt_irrefl in Hcontra. contradiction.
      -
      apply dom_subset_orb_fst_iff in Hsub. destruct Hsub.
      assert (HsubV': is_domain_subset V (dom pd1') = true). { 
        apply dom_subset_eq_compat_left with (X:= (dom pd)); try assumption.
        simpl. apply dom_equiv_refl. }
      specialize (IHphi1 H5 V H1 pd1' HsubV'). 
      apply IHphi1; try assumption.
      apply pd_equiv_preserves_sem with (pd0:= pd1); try assumption.
      * simpl. apply Valid_after_resX. assumption.
      * split; simpl; try assumption. 
        + apply dom_equiv_sym. assumption.
        + apply bulid_res_implies_Peq; try assumption. }
    split. { 
      inversion HWD; subst. 
      simpl in Hsub. destruct Hp_case1 as [Hgt0 Hlt1].
      destruct (Rle_lt_dec r 0) eqn: Hp0; destruct (Rle_lt_dec 1 r) eqn: Hp1.
      - destruct H4. 
        assert (Hr: r = 1). { apply Rle_antisym; try assumption. }
        assert (Hcontra: 1<1). { rewrite Hr in Hlt1. assumption. }
        apply Rlt_irrefl in Hcontra. contradiction.
      - destruct H4. 
        assert (Hr: r = 0). { apply Rle_antisym; try assumption. }
        assert (Hcontra: 0<0). { rewrite Hr in Hgt0. assumption. }
        apply Rlt_irrefl in Hcontra. contradiction.
      - destruct H4. 
        assert (Hr: r = 1). { apply Rle_antisym; try assumption. }
        assert (Hcontra: 1<1). { rewrite Hr in Hlt1. assumption. }
        apply Rlt_irrefl in Hcontra. contradiction.
      - 
      apply dom_subset_orb_fst_iff in Hsub. destruct Hsub.
      assert (HsubV': is_domain_subset V (dom pd2') = true). { 
        apply dom_subset_eq_compat_left with (X:= (dom pd)); try assumption.
        simpl. apply dom_equiv_refl. }
      specialize (IHphi2 H6 V H2 pd2' HsubV'). 
      apply IHphi2; try assumption.
      apply pd_equiv_preserves_sem with (pd0:= pd2); try assumption.
      * simpl. apply Valid_after_resX. assumption.
      * split; simpl; try assumption. 
        + apply dom_equiv_sym. assumption.
        + apply bulid_res_implies_Peq; try assumption. }
    split. {
      simpl. rewrite sum_probs_bulid; try assumption.
      rewrite Hsum1. rewrite <- sum_eq_after_res. reflexivity. }
    split. {
      simpl. rewrite sum_probs_bulid; try assumption.
      rewrite Hsum2. rewrite <- sum_eq_after_res. reflexivity. }
    apply res_bulid_linear; try assumption.
    + destruct Hsem as [Hcase2 | Hcase3].
      * destruct Hcase2 as [Hp1 H]. 
        destruct H as [pd1 H]. destruct H as [HWF1 H]. 
        destruct H as [Heq1 H]. destruct Heq1 as [Hdom1 Heq1].
        simpl in Hdom1. simpl in Heq1. 
        destruct H as [Hsem1 Hsum1]. 
        assert (HWFV: Valid_dist ((mu pd) \| V)). {
          apply Valid_after_resX; try assumption. }
        assert (Hsupp: (supp_mu (mu pd1) == supp_mu ((mu pd) \| V))%supp). {
            apply dst_equiv_implies_beq_supp; try assumption. }
        apply supp_eq_implies_subset_conj in Hsupp. destruct Hsupp. 
        simpl. right. left. split; try assumption.
        pose (pd1':= Build_partial_dist (dom pd) (bulid_dst_sub (mu pd1) (mu pd) V) 
                    (PD_bulid_proj pd1 pd V)).
        assert (HWF1': Valid_dist (mu pd1')). { apply WF_dist_after_bulid_mu; try assumption. }
        exists pd1'.
        split; try assumption.
        split. { 
          split; simpl; try apply dom_equiv_refl.
          unfold dst_equiv. intros. simpl. 
          rewrite Peq_implies_res_bulid_Peq; try assumption.
          reflexivity. }
        split. {
          inversion HWD; subst. 
          simpl in Hsub. 
          destruct (Rle_lt_dec 1 0); destruct (Rle_lt_dec 1 1); try apply Rlt_irrefl in r0; try contradiction.
          * apply Rle_not_lt in r. unfold not in r. exfalso. apply r. apply Rlt_0_1. 
          * assert (HsubV': is_domain_subset V (dom pd1') = true). { 
              apply dom_subset_eq_compat_left with (X:= (dom pd)); try assumption.
              simpl. apply dom_equiv_refl. }
            specialize (IHphi1 H5 V Hsub pd1' HsubV'). 
            apply IHphi1; try assumption.
            apply pd_equiv_preserves_sem with (pd0:= pd1); try assumption.
          - simpl. apply Valid_after_resX. assumption.
          - split; simpl; try assumption.  
            + apply dom_equiv_sym. assumption.
            + apply bulid_res_implies_Peq; try assumption. }
        simpl. rewrite sum_probs_bulid; try assumption.
        rewrite Hsum1. rewrite <- sum_eq_after_res. reflexivity.
      * destruct Hcase3 as [Hp0 H]. 
        destruct H as [pd2 H]. destruct H as [HWF2 H]. 
        destruct H as [Heq2 H]. destruct Heq2 as [Hdom2 Heq2].
        simpl in Hdom2. simpl in Heq2. 
        destruct H as [Hsem2 Hsum2]. 
        assert (HWFV: Valid_dist ((mu pd) \| V)). {
          apply Valid_after_resX; try assumption. }
        assert (Hsupp: (supp_mu (mu pd2) == supp_mu ((mu pd) \| V))%supp). {
            apply dst_equiv_implies_beq_supp; try assumption. }
        apply supp_eq_implies_subset_conj in Hsupp. destruct Hsupp. 
        simpl. right. right. split; try assumption.
        pose (pd2':= Build_partial_dist (dom pd) (bulid_dst_sub (mu pd2) (mu pd) V) 
                    (PD_bulid_proj pd2 pd V)).
        assert (HWF2': Valid_dist (mu pd2')). { apply WF_dist_after_bulid_mu; try assumption. }
        exists pd2'.
        split; try assumption.
        split. { 
          split; simpl; try apply dom_equiv_refl.
          unfold dst_equiv. intros. simpl. 
          rewrite Peq_implies_res_bulid_Peq; try assumption.
          reflexivity. }
        split. {
          inversion HWD; subst. 
          simpl in Hsub. 
          destruct (Rle_lt_dec 0 0); destruct (Rle_lt_dec 1 0); try apply Rlt_irrefl in r; try contradiction.
          * apply Rle_not_lt in r0. unfold not in r0. exfalso. apply r0. apply Rlt_0_1. 
          * assert (HsubV': is_domain_subset V (dom pd2') = true). { 
              apply dom_subset_eq_compat_left with (X:= (dom pd)); try assumption.
              simpl. apply dom_equiv_refl. }
            specialize (IHphi2 H6 V Hsub pd2' HsubV'). 
            apply IHphi2; try assumption.
            apply pd_equiv_preserves_sem with (pd0:= pd2); try assumption.
          - simpl. apply Valid_after_resX. assumption.
          - split; simpl; try assumption.  
            + apply dom_equiv_sym. assumption.
            + apply bulid_res_implies_Peq; try assumption. }
        simpl. rewrite sum_probs_bulid; try assumption.
        rewrite Hsum2. rewrite <- sum_eq_after_res. reflexivity.
  - simpl in Hsem. destruct Hsem as [Hcase1 | Hsem]. 
    + simpl. left. 
      destruct Hcase1 as [p1 H]. destruct H as [p2 H]. 
      destruct H as [Hp1 H]. destruct H as [Hp2 H].
      destruct H as [Hp_case1 H]. 
      destruct H as [pd1 H]. destruct H as [pd2 H]. 
      destruct H as [HWF1 H]. destruct H as [HWF2 H].
      destruct H as [Hdom1 H]. destruct H as [Hdom2 H].
      destruct H as [Hsem1 H]. destruct H as [Hsem2 H]. 
      destruct H as [Hsum1 H].  destruct H as [Hsum2 Hmu].
      exists p1, p2. split; try assumption. split; try assumption. split; try assumption. 
      assert (HWFV: Valid_dist ((mu pd) \| V)). { apply Valid_after_resX with (X:= V) in HWF. assumption. }
      assert (HSspV: Sorted_supp (supp_mu ((mu pd) \| V))). {
        apply Sort_supp_if_WF_supp.  }
      assert (HWF_linear: Valid_dist (p1 * mu pd1 + p2 * mu pd2)). {
        apply Valid_linear_under_eq_prob; try assumption.
        - destruct Hp1. apply Rlt_le. assumption.
        - destruct Hp2. apply Rlt_le. assumption.
        - rewrite Hsum1. rewrite Hsum2. rewrite <- Rmult_plus_distr_r.
          rewrite Hp_case1. rewrite Rmult_1_l.
          destruct HWFV. assumption. }
      assert (Hsupp: (supp_mu ((mu pd) \| V) == supp_mu (p1 * mu pd1 + p2 * mu pd2))%supp). {
            apply dst_equiv_implies_beq_supp; try assumption. }
      assert (Hspsub: is_supp_subset (supp_mu (mu pd1)) (supp_mu ((mu pd) \| V)) = true /\ 
                      is_supp_subset (supp_mu (mu pd2)) (supp_mu ((mu pd) \| V)) = true ). {
        apply supp_eq_implies_subset_conj in Hsupp. destruct Hsupp. 
        apply supp_mu_subset_decom_l in H0; try assumption.
        - destruct Hp1. destruct Hp2. destruct H0.
          rewrite <- supp_eq_mult_coef in H0; try assumption.
          rewrite <- supp_eq_mult_coef in H5; try assumption.
          split; try assumption. }
      destruct Hspsub. 
      pose (pd1':= Build_partial_dist (dom pd) (bulid_dst_sub (mu pd1) (mu pd) V) 
                      (PD_bulid_proj pd1 pd V)).
      pose (pd2':= Build_partial_dist (dom pd) (bulid_dst_sub (mu pd2) (mu pd) V) 
                      (PD_bulid_proj pd2 pd V)).
      assert (HWF1': Valid_dist (mu pd1')). { apply WF_dist_after_bulid_mu; try assumption. }
      assert (HWF2': Valid_dist (mu pd2')). { apply WF_dist_after_bulid_mu; try assumption. }
      exists pd1', pd2'. 
      split; try assumption.
      split; try assumption.
      split. { simpl. apply dom_equiv_refl. }
      split. { simpl. apply dom_equiv_refl. }
      split. { 
        inversion HWD; subst. 
        simpl in Hsub. apply dom_subset_orb_fst_iff in Hsub. destruct Hsub.
        assert (HsubV': is_domain_subset V (dom pd1') = true). { 
          apply dom_subset_eq_compat_left with (X:= (dom pd)); try assumption.
          simpl. apply dom_equiv_refl. }
        specialize (IHphi1 H3 V H1 pd1' HsubV'). 
        apply IHphi1; try assumption.
        apply pd_equiv_preserves_sem with (pd0:= pd1); try assumption.
        - simpl. apply Valid_after_resX. assumption.
        - split; simpl; try assumption. 
          + apply dom_equiv_sym. assumption.
          + apply bulid_res_implies_Peq; try assumption. }
      split. { 
        inversion HWD; subst. 
        simpl in Hsub. apply dom_subset_orb_fst_iff in Hsub. destruct Hsub.
        assert (HsubV': is_domain_subset V (dom pd2') = true). { 
          apply dom_subset_eq_compat_left with (X:= (dom pd)); try assumption.
          simpl. apply dom_equiv_refl. }
        specialize (IHphi2 H4 V H2 pd2' HsubV'). 
        apply IHphi2; try assumption.
        apply pd_equiv_preserves_sem with (pd0:= pd2); try assumption.
        - simpl. apply Valid_after_resX. assumption.
        - split; simpl; try assumption. 
          + apply dom_equiv_sym. assumption.
          + apply bulid_res_implies_Peq; try assumption. }
      split. {
        simpl. rewrite sum_probs_bulid; try assumption.
        rewrite Hsum1. rewrite <- sum_eq_after_res. reflexivity. }
      split. {
        simpl. rewrite sum_probs_bulid; try assumption.
        rewrite Hsum2. rewrite <- sum_eq_after_res. reflexivity. }
      simpl. apply res_bulid_linear2p; try assumption.
    + destruct Hsem as [Hcase2 | Hcase3].
      * destruct Hcase2 as [pd1 H]. destruct H as [HWF1 H]. 
        destruct H as [Heq1 H]. destruct Heq1 as [Hdom1 Heq1].
        simpl in Hdom1. simpl in Heq1. 
        destruct H as [HsubV H]. 
        destruct H as [Hsem1 Hsum1]. 
        assert (HWFV: Valid_dist ((mu pd) \| V)). {
          apply Valid_after_resX; try assumption. }
        assert (Hsupp: (supp_mu (mu pd1) == supp_mu ((mu pd) \| V))%supp). {
            apply dst_equiv_implies_beq_supp; try assumption. }
        apply supp_eq_implies_subset_conj in Hsupp. destruct Hsupp. 
        simpl. right. left. 
        pose (pd1':= Build_partial_dist (dom pd) (bulid_dst_sub (mu pd1) (mu pd) V) 
                    (PD_bulid_proj pd1 pd V)).
        assert (HWF1': Valid_dist (mu pd1')). { apply WF_dist_after_bulid_mu; try assumption. }
        exists pd1'.
        split; try assumption.
        split. { 
          split; simpl; try apply dom_equiv_refl.
          unfold dst_equiv. intros. simpl. 
          rewrite Peq_implies_res_bulid_Peq; try assumption.
          reflexivity. }
        split. {
          simpl in Hsub. apply dom_subset_orb_fst_iff in Hsub. destruct Hsub.
          apply dom_subset_trans with (l1:= V); try assumption. }
        split. {
          inversion HWD; subst. 
          simpl in Hsub. apply dom_subset_orb_fst_iff in Hsub. destruct Hsub.
          assert (HsubV': is_domain_subset V (dom pd1') = true). { 
            apply dom_subset_eq_compat_left with (X:= (dom pd)); try assumption.
            simpl. apply dom_equiv_refl. }
          specialize (IHphi1 H3 V H1 pd1' HsubV'). 
          apply IHphi1; try assumption.
          apply pd_equiv_preserves_sem with (pd0:= pd1); try assumption.
          - simpl. apply Valid_after_resX. assumption.
          - split; simpl; try assumption.  
            + apply dom_equiv_sym. assumption.
            + apply bulid_res_implies_Peq; try assumption. }
        simpl. rewrite sum_probs_bulid; try assumption.
        rewrite Hsum1. rewrite <- sum_eq_after_res. reflexivity.
      * destruct Hcase3 as [pd2 H]. destruct H as [HWF2 H]. 
        destruct H as [Heq2 H]. destruct Heq2 as [Hdom2 Heq2].
        simpl in Hdom2. simpl in Heq2. 
        destruct H as [HsubV H]. 
        destruct H as [Hsem2 Hsum2]. 
        assert (HWFV: Valid_dist ((mu pd) \| V)). {
          apply Valid_after_resX; try assumption. }
        assert (Hsupp: (supp_mu (mu pd2) == supp_mu ((mu pd) \| V))%supp). {
            apply dst_equiv_implies_beq_supp; try assumption. }
        apply supp_eq_implies_subset_conj in Hsupp. destruct Hsupp. 
        simpl. right. right. 
        pose (pd2':= Build_partial_dist (dom pd) (bulid_dst_sub (mu pd2) (mu pd) V) 
                    (PD_bulid_proj pd2 pd V)).
        assert (HWF2': Valid_dist (mu pd2')). { apply WF_dist_after_bulid_mu; try assumption. }
        exists pd2'.
        split; try assumption.
        split. { 
          split; simpl; try apply dom_equiv_refl.
          unfold dst_equiv. intros. simpl. 
          rewrite Peq_implies_res_bulid_Peq; try assumption.
          reflexivity. }
        split. {
          simpl in Hsub. apply dom_subset_orb_fst_iff in Hsub. destruct Hsub.
          apply dom_subset_trans with (l1:= V); try assumption. }
        split. {
          inversion HWD; subst. 
          simpl in Hsub. apply dom_subset_orb_fst_iff in Hsub. destruct Hsub.
          assert (HsubV': is_domain_subset V (dom pd2') = true). { 
            apply dom_subset_eq_compat_left with (X:= (dom pd)); try assumption.
            simpl. apply dom_equiv_refl. }
          specialize (IHphi2 H4 V H2 pd2' HsubV'). 
          apply IHphi2; try assumption.
          apply pd_equiv_preserves_sem with (pd0:= pd2); try assumption.
          - simpl. apply Valid_after_resX. assumption.
          - split; simpl; try assumption.  
            + apply dom_equiv_sym. assumption.
            + apply bulid_res_implies_Peq; try assumption. }
        simpl. rewrite sum_probs_bulid; try assumption.
        rewrite Hsum2. rewrite <- sum_eq_after_res. reflexivity.
  - simpl in Hsem. 
    destruct Hsem as [pd1 H]. destruct H as [pd2 H].
    destruct H as [Hvar H]. 
    destruct H as [HWF1 H]. destruct H as [HWF2 H].
    destruct H as [Hsem1 H]. destruct H as [Hsem2 H].
    destruct H as [Hsub' Heq]. simpl in Hsub'. simpl in Heq.
    exists pd1, pd2, Hvar. 
    split; try assumption.
    split; try assumption.
    split; try assumption.
    split; try assumption.
    split. { simpl. apply dom_subset_trans with (l1:= V); try assumption. }
    simpl. apply dst_equiv_trans with (mu1:= ((mu pd) \| V) \| (orb_domain (dom pd1) (dom pd2))); try assumption.
    apply res_to_subset_equiv; try assumption.
  - simpl in Hsem. destruct Hsem as [Hsem1 Hsem2].
    inversion HWD; subst. simpl in *. apply dom_subset_orb_fst_iff in Hsub. destruct Hsub.
    split. 
    + specialize (IHphi1 H1 V H pd HV). apply IHphi1; try assumption.
    + specialize (IHphi2 H2 V H0 pd HV). apply IHphi2; try assumption.
Qed. 
(***********************************************************************)
Lemma df_sem_project_implies_V: 
  forall pd df V (HV: is_domain_subset V pd.(dom) = true),
    Valid_dist pd.(mu) -> well_defined_Pf (Pdeter df) ->
    is_domain_subset (get_var_in_Dformular df) V = true -> 
    [[Pdeter df]] pd -> 
    [[Pdeter df]] (Build_partial_dist V (pd.(mu) \| V) 
                    (PD_after_res V (dom pd) (mu pd) HV (pd.(all_partial)))).
Proof. 
  intros pd df V HV HWF HWD Hsub Hsem. generalize dependent pd.
  induction df.
  - destruct pd as [dom mu HPD]. intros. 
    induction mu as [|(s,p) mu' IH]; intros. 
    + simpl in *. destruct Hsem. split; try assumption. 
    + assert (Hpd0: partial_dst_Prop dom [(s,p)]). { 
        assert (H: partial_dst_Prop dom ((s,p)::mu')) by assumption.
        rewrite dst_cons_eq_add in H. apply PD_decom in H. destruct H. assumption. }
      pose proof (df_sem_conj_mu dom mu' s p (Dpred b) Hpd0 HPD Hsem) as [Hsem0 Hsem1].
      inversion HPD; subst. simpl. 
      split; try assumption. intros. 
      unfold supp_mu in H. simpl in H. rewrite insert_st_pair_fst_eq_insert_st in H.
      rewrite in_supp_insert_eq in H. apply orb_true_iff in H. destruct H. 
      * assert (Hin: is_in_supp s (supp_mu (mu {| dom := dom; mu := [(s, p)]; all_partial := Hpd0 |})) = true). {
            simpl. now rewrite state_eq_refl. } 
        apply Hsem0 in Hin. 
        rewrite state_eq_sym in H. 
        apply st_eq_implies_df_sem with (df:= Dpred b) in H; try assumption.
        inversion HWD; subst.
        apply df_sem_iff_res_V; try assumption. 
        simpl in HV. simpl in Hsub. 
        apply dom_subset_eq_compat_left with (X:= dom); try assumption.
      * apply Valid_dist_conj in HWF. destruct HWF.
        simpl in IH. simpl in HV. specialize (IH H3 HV H2 Hsem1). 
        unfold pf_sem in IH. apply IH; try assumption. 
  - intros. destruct pd as [dom mu HPD]. 
    simpl in HV. simpl in HWF. simpl in Hsub. 
    assert (HWDdf: well_defined_Pf (Pdeter df)). {
        inversion HWD; subst. inversion H0; subst. 
        apply WD_Pdeter. assumption. }
    specialize (IHdf HWDdf Hsub). 
    induction mu as [|(s,p) mu' IH]; intros. 
    + simpl in *. 
    destruct Hsem. split; try assumption. 
    + assert (Hpd0: partial_dst_Prop dom [(s,p)]). { 
        assert (H: partial_dst_Prop dom ((s,p)::mu')) by assumption.
        rewrite dst_cons_eq_add in H. apply PD_decom in H. destruct H. assumption. }
      pose proof (df_sem_conj_mu dom mu' s p (Dexist n df) Hpd0 HPD Hsem) as [Hsem0 Hsem1].
      clear Hsem. inversion HPD; subst. 
      assert (Hsubs: is_domain_subset V (return_domain s) = true). {
          apply dom_subset_eq_compat_left with (Z:= V) in H1; try assumption. }
      unfold pf_sem. 
      split; try assumption. 
      intros. unfold supp_mu in H. simpl in H. 
      rewrite insert_st_pair_fst_eq_insert_st in H.
      rewrite in_supp_insert_eq in H. apply orb_true_iff in H. destruct H. 
      * assert (Hin: is_in_supp s (supp_mu (mu {| dom := dom; mu := [(s, p)]; all_partial := Hpd0 |})) = true). {
            simpl. now rewrite state_eq_refl. } 
        apply Hsem0 in Hin. rewrite state_eq_sym in H. 
        apply st_eq_implies_df_sem with (df:= (Dexist n df)) in H; try assumption.
        destruct Hin.
      ** inversion HWD; subst. destruct H2. inversion H5; subst. 
      split; try assumption. 
      -- apply dom_subset_eq_compat_left with (Z:= V) in H1; try assumption. 
        apply res_dom_eq_iff_subset in H1. apply dom_equiv_sym in H1.
        apply dom_subset_eq_compat_left with (X:= V); try assumption.
      -- exists x. 
      assert (HsubV: is_domain_subset (singleton_bool_list n) V = true). { 
            apply dom_subset_trans with (l1:= (get_var_in_Dformular df)); 
              try assumption. }
        assert (Heq': ((res_st_to_X (update s n x) V) ==
                      (update (res_st_to_X s V) n x))%state). { 
            apply update_eq_res_st with (s:= s) (q:= x) in HsubV. assumption. }
        apply st_eq_implies_df_sem with (df:= df) in Heq'; try assumption.
        apply df_sem_iff_res_V; try assumption.
        apply dom_subset_trans with (l1:= (return_domain s)); try assumption.
        apply update_subst_implies_dom_eq.
    * clear Hsem0. apply Valid_dist_conj in HWF. destruct HWF. 
        specialize (IH H3 H2 Hsem1). 
        apply IH; try assumption. 
Qed.   


Lemma sem_satisfies_project_implies_phi: 
  forall pd phi (Hdom: is_domain_subset (get_var_in_Pformular phi) pd.(dom) = true),
    Valid_dist pd.(mu) -> well_defined_Pf phi ->
    [[phi]] pd -> 
    [[phi]] (Build_partial_dist (get_var_in_Pformular phi) (pd.(mu) \| (get_var_in_Pformular phi)) 
                    (PD_after_res (get_var_in_Pformular phi) (dom pd) (mu pd) Hdom (pd.(all_partial)))).
Proof.
  intros pd phi Hdom HWF HWD Hsem. generalize dependent pd.
  induction phi; intros.
  - apply df_sem_project_implies_V with (V:= (get_var_in_Pformular (Pdeter d))); try assumption. 
    simpl. apply dom_equiv_refl.
  - simpl in Hsem. destruct Hsem as [Hcase1| Hsem].
    + destruct Hcase1 as [Hp_case1 H]. 
      destruct H as [pd1 H]. destruct H as [pd2 H].
      destruct H as [HWF1 H]. destruct H as [HWF2 H]. 
      destruct H as [Hdom1 H]. destruct H as [Hdom2 H].
      destruct H as [Hphi1 H]. destruct H as [Hphi2 H].
      destruct H as [Hsum1 H]. destruct H as [Hsum2 Hmu].
      left. split; try assumption.
      pose (V:= (orb_domain (get_var_in_Pformular phi1) (get_var_in_Pformular phi2))).
      assert (Hdom_simpl: is_domain_subset V pd.(dom) = true). {
        simpl in Hdom. destruct Hp_case1 as [Hgt0 Hlt1]. inversion HWD; subst.
        destruct (Rle_lt_dec r 0%R) eqn: Hp0; destruct (Rle_lt_dec 1 r) eqn: Hp1.
        - destruct H2. 
          assert (Hr: r = 1). { apply Rle_antisym; try assumption. }
          assert (Hcontra: 1<1). { rewrite Hr in Hlt1. assumption. }
          apply Rlt_irrefl in Hcontra. contradiction.
        - destruct H2. 
          assert (Hr: r = 0). { apply Rle_antisym; try assumption. }
          assert (Hcontra: 0<0). { rewrite Hr in Hgt0. assumption. }
          apply Rlt_irrefl in Hcontra. contradiction.
        - destruct H2. 
          assert (Hr: r = 1). { apply Rle_antisym; try assumption. }
          assert (Hcontra: 1<1). { rewrite Hr in Hlt1. assumption. }
          apply Rlt_irrefl in Hcontra. contradiction.
        - assumption. } 
      assert (HV1': is_domain_subset V pd1.(dom) = true). {
          apply dom_equiv_sym in Hdom1.
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
      pose (pd1':= Build_partial_dist V (pd1.(mu) \| V) 
                      (PD_after_res V (dom pd1) (mu pd1) HV1' (pd1.(all_partial)))).
      assert (HV2': is_domain_subset V pd2.(dom) = true). {
          apply dom_equiv_sym in Hdom2.
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
      pose (pd2':= Build_partial_dist V (pd2.(mu) \| V) 
                      (PD_after_res V (dom pd2) (mu pd2) HV2' (pd2.(all_partial)))).
      exists pd1', pd2'.
      split. { simpl. apply Valid_after_resX. assumption. }
      split. { simpl. apply Valid_after_resX. assumption. }
      split. { simpl. destruct Hp_case1 as [Hgt0 Hlt1]. inversion HWD; subst.
        destruct (Rle_lt_dec r 0%R) eqn: Hp0; destruct (Rle_lt_dec 1 r) eqn: Hp1.
        - destruct H2. 
          assert (Hr: r = 1). { apply Rle_antisym; try assumption. }
          assert (Hcontra: 1<1). { rewrite Hr in Hlt1. assumption. }
          apply Rlt_irrefl in Hcontra. contradiction.
        - destruct H2. 
          assert (Hr: r = 0). { apply Rle_antisym; try assumption. }
          assert (Hcontra: 0<0). { rewrite Hr in Hgt0. assumption. }
          apply Rlt_irrefl in Hcontra. contradiction.
        - destruct H2. 
          assert (Hr: r = 1). { apply Rle_antisym; try assumption. }
          assert (Hcontra: 1<1). { rewrite Hr in Hlt1. assumption. }
          apply Rlt_irrefl in Hcontra. contradiction.
        - apply dom_equiv_refl. }
      split. { simpl. destruct Hp_case1 as [Hgt0 Hlt1]. inversion HWD; subst.
        destruct (Rle_lt_dec r 0%R) eqn: Hp0; destruct (Rle_lt_dec 1 r) eqn: Hp1.
        - destruct H2. 
          assert (Hr: r = 1). { apply Rle_antisym; try assumption. }
          assert (Hcontra: 1<1). { rewrite Hr in Hlt1. assumption. }
          apply Rlt_irrefl in Hcontra. contradiction.
        - destruct H2. 
          assert (Hr: r = 0). { apply Rle_antisym; try assumption. }
          assert (Hcontra: 0<0). { rewrite Hr in Hgt0. assumption. }
          apply Rlt_irrefl in Hcontra. contradiction.
        - destruct H2. 
          assert (Hr: r = 1). { apply Rle_antisym; try assumption. }
          assert (Hcontra: 1<1). { rewrite Hr in Hlt1. assumption. }
          apply Rlt_irrefl in Hcontra. contradiction.
        - apply dom_equiv_refl. }
      inversion HWD; subst. apply dom_subset_orb_fst_iff in Hdom_simpl. 
      split. { destruct Hdom_simpl. 
        apply dom_equiv_sym in Hdom1. 
        apply dom_subset_eq_compat_left with (Y:= dom pd1) in H; try assumption.
        specialize (IHphi1 H3 pd1 H HWF1 Hphi1). 
        assert (HV: is_domain_subset (get_var_in_Pformular phi1) V = true). { 
            apply dom_subset_orb_dom_r. apply dom_subset_refl. }
        apply sem_resV_implies_pd with (V:= get_var_in_Pformular phi1) (HV:= HV); try assumption. 
          - apply Valid_after_resX. assumption.
          - apply dom_equiv_refl.
          - apply pd_equiv_preserves_sem with (pd0:= 
          {|
            dom := get_var_in_Pformular phi1;
            mu := (mu pd1) \| (get_var_in_Pformular phi1);
            all_partial :=
              PD_after_res (get_var_in_Pformular phi1) (dom pd1) 
                    (mu pd1) H (all_partial pd1)
          |}); try assumption. 
            + simpl. apply Valid_after_resX. assumption.
            + simpl. apply Valid_after_resX. apply Valid_after_resX. assumption.
            + simpl. split; simpl; try apply dom_equiv_refl.
          apply dst_equiv_sym. apply res_to_subset_equiv. assumption. }
      split. { destruct Hdom_simpl. 
        apply dom_equiv_sym in Hdom2. 
        apply dom_subset_eq_compat_left with (Y:= dom pd2) in H0; try assumption.
        specialize (IHphi2 H4 pd2 H0 HWF2 Hphi2). 
        assert (HV: is_domain_subset (get_var_in_Pformular phi2) V = true). { 
            apply dom_subset_orb_dom_l. apply dom_subset_refl. }
        apply sem_resV_implies_pd with (V:= get_var_in_Pformular phi2) (HV:= HV); try assumption. 
          - apply Valid_after_resX. assumption.
          - apply dom_equiv_refl.
          - apply pd_equiv_preserves_sem with (pd0:= 
          {|
            dom := get_var_in_Pformular phi2;
            mu := (mu pd2) \| (get_var_in_Pformular phi2);
            all_partial :=
              PD_after_res (get_var_in_Pformular phi2) (dom pd2) 
                (mu pd2) H0 (all_partial pd2)
          |}); try assumption. 
            + simpl. apply Valid_after_resX. assumption.
            + simpl. apply Valid_after_resX. apply Valid_after_resX. assumption.
            + simpl. split; simpl; try apply dom_equiv_refl.
          apply dst_equiv_sym. apply res_to_subset_equiv. assumption. }
      split. { simpl. repeat rewrite <- sum_eq_after_res. assumption. }
      split. { simpl. repeat rewrite <- sum_eq_after_res. assumption. }
      simpl. destruct Hp_case1 as [Hgt0 Hlt1].  
        inversion HWD; subst.
        destruct (Rle_lt_dec r 0%R) eqn: Hp0; destruct (Rle_lt_dec 1 r) eqn: Hp1.
        * destruct H2. 
          assert (Hr: r = 1). { apply Rle_antisym; try assumption. }
          assert (Hcontra: 1<1). { rewrite Hr in Hlt1. assumption. }
          apply Rlt_irrefl in Hcontra. contradiction.
        * destruct H2. 
          assert (Hr: r = 0). { apply Rle_antisym; try assumption. }
          assert (Hcontra: 0<0). { rewrite Hr in Hgt0. assumption. }
          apply Rlt_irrefl in Hcontra. contradiction.
        * destruct H2. 
          assert (Hr: r = 1). { apply Rle_antisym; try assumption. }
          assert (Hcontra: 1<1). { rewrite Hr in Hlt1. assumption. }
          apply Rlt_irrefl in Hcontra. contradiction.
        * repeat rewrite <- res_dst_to_X_mult_coef.
          rewrite <- res_add_decom_eq.  
          apply Peq_implies_res_eq; try assumption.
          apply Valid_linear_under_eq_prob; try assumption. 
          ** apply Rlt_le. assumption.
          ** assert (Hp_minus: 0 < 1-r < 1). { apply Rp_lt1_minus_p_bounds with (p:= r). split; assumption. }
            destruct Hp_minus. apply Rlt_le. assumption.
          ** rewrite Hsum1. rewrite Hsum2. rewrite <- Rmult_plus_distr_r. 
            rewrite R_plus_sub_eq_1. rewrite Rmult_1_l.
            destruct HWF. assumption.
    + destruct Hsem as [Hcase2 |Hcase3]. 
      * destruct Hcase2 as [Hp_case2 H]; subst. destruct H as [pd1 H].
      destruct H as [HWF1 H]. destruct H as [Heq1 H].
      destruct H as [Hphi1 Hsum1]. destruct Heq1 as [Hdom1 Hmu1]. 
      assert (Hdom_simpl: is_domain_subset (get_var_in_Pformular phi1) pd.(dom) = true). {
        simpl in Hdom.  
        destruct (Rle_lt_dec 1 0); destruct (Rle_lt_dec 1 1); try apply Rlt_irrefl in r0; try contradiction.
          * apply Rle_not_lt in r. unfold not in r. exfalso. apply r. apply Rlt_0_1. 
          * assumption. }           
      simpl. right. left. split; try reflexivity.
      pose (V:= (get_var_in_Pformular phi1)).
      assert (HV1': is_domain_subset V pd1.(dom) = true). {
          apply dom_equiv_sym in Hdom1.
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
      pose (pd1':= Build_partial_dist V (pd1.(mu) \| V) 
                      (PD_after_res V (dom pd1) (mu pd1) HV1' (pd1.(all_partial)))).
      exists pd1'.
      split. { simpl. apply Valid_after_resX. assumption. }
      split. { split; simpl; 
          destruct (Rle_lt_dec 1 0); destruct (Rle_lt_dec 1 1); try apply Rlt_irrefl in r0; try contradiction.
          * apply Rle_not_lt in r. unfold not in r. exfalso. apply r. apply Rlt_0_1. 
          * simpl. apply dom_equiv_refl. 
          * apply Rle_not_lt in r. unfold not in r. exfalso. apply r. apply Rlt_0_1. 
          * apply Peq_implies_res_eq; try assumption. }
      inversion HWD; subst. 
      split. { 
        apply dom_equiv_sym in Hdom1. 
        apply dom_subset_eq_compat_left with (Y:= dom pd1) in Hdom_simpl; try assumption.
        specialize (IHphi1 H3 pd1 Hdom_simpl HWF1 Hphi1). 
        assert (HV: is_domain_subset (get_var_in_Pformular phi1) V = true). { 
             apply dom_subset_refl. }
        apply sem_resV_implies_pd with (V:= get_var_in_Pformular phi1) (HV:= HV); try assumption. 
          - apply Valid_after_resX. assumption.
          - apply pd_equiv_preserves_sem with (pd0:= 
          {|
            dom := get_var_in_Pformular phi1;
            mu := (mu pd1) \| (get_var_in_Pformular phi1);
            all_partial :=
              PD_after_res (get_var_in_Pformular phi1) (dom pd1) 
                    (mu pd1) Hdom_simpl (all_partial pd1)
          |}); try assumption. 
            + simpl. apply Valid_after_resX. assumption.
            + simpl. apply Valid_after_resX. apply Valid_after_resX. assumption.
            + simpl. split; simpl; try apply dom_equiv_refl.
          apply dst_equiv_sym. apply res_to_subset_equiv. assumption. }
      simpl. repeat rewrite <- sum_eq_after_res. assumption.
      * destruct Hcase3 as [Hp_case3 H]; subst. destruct H as [pd2 H].
      destruct H as [HWF2 H]. destruct H as [Heq2 H].
      destruct H as [Hphi2 Hsum2].
      simpl. right. right. split; try reflexivity.
      destruct Heq2 as [Hdom2 Hmu2].
      assert (Hdom_simpl: is_domain_subset (get_var_in_Pformular phi2) pd.(dom) = true). {
        simpl in Hdom.  
        destruct (Rle_lt_dec 0 0); destruct (Rle_lt_dec 1 0); try apply Rlt_irrefl in r; try contradiction.
          * apply Rle_not_lt in r0. unfold not in r0. exfalso. apply r0. apply Rlt_0_1. 
          * assumption. }           
      pose (V:= (get_var_in_Pformular phi2)).
      assert (HV2': is_domain_subset V pd2.(dom) = true). {
          apply dom_equiv_sym in Hdom2.
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
      pose (pd2':= Build_partial_dist V (pd2.(mu) \| V) 
                      (PD_after_res V (dom pd2) (mu pd2) HV2' (pd2.(all_partial)))).
      exists pd2'.
      split. { simpl. apply Valid_after_resX. assumption. }
      split. { split; simpl; try apply dom_equiv_refl;
        destruct (Rle_lt_dec 0 0); destruct (Rle_lt_dec 1 0); try apply Rlt_irrefl in r; try contradiction.
          * try apply Rle_not_lt in r0; try unfold not in r0; try exfalso; try apply r0; apply Rlt_0_1. 
          * simpl. apply dom_equiv_refl. 
          * try apply Rle_not_lt in r0; try unfold not in r0; try exfalso; try apply r0; apply Rlt_0_1. 
          *
          apply Peq_implies_res_eq; try assumption. }
      inversion HWD; subst. 
      split. { 
        apply dom_equiv_sym in Hdom2. 
        apply dom_subset_eq_compat_left with (Y:= dom pd2) in Hdom_simpl; try assumption.
        specialize (IHphi2 H4 pd2 Hdom_simpl HWF2 Hphi2). 
        assert (HV: is_domain_subset (get_var_in_Pformular phi2) V = true). { 
            apply dom_subset_refl. }
        apply sem_resV_implies_pd with (V:= get_var_in_Pformular phi2) (HV:= HV); try assumption. 
          - apply Valid_after_resX. assumption.
          - apply pd_equiv_preserves_sem with (pd0:= 
          {|
            dom := get_var_in_Pformular phi2;
            mu := (mu pd2) \| (get_var_in_Pformular phi2);
            all_partial :=
              PD_after_res (get_var_in_Pformular phi2) (dom pd2) 
                (mu pd2) Hdom_simpl (all_partial pd2)
          |}); try assumption. 
            + simpl. apply Valid_after_resX. assumption.
            + simpl. apply Valid_after_resX. apply Valid_after_resX. assumption.
            + simpl. split; simpl; try apply dom_equiv_refl.
          apply dst_equiv_sym. apply res_to_subset_equiv. assumption. }
      simpl. repeat rewrite <- sum_eq_after_res. assumption.
  - intros. simpl in Hsem. destruct Hsem as [Hcase1 |Hsem]. 
    + destruct Hcase1 as [p1 H]. destruct H as [p2 H]. 
      destruct H as [Hp1 H]. destruct H as [Hp2 H].
      destruct H as [Hp_case1 H]. 
      destruct H as [pd1 H]. destruct H as [pd2 H].
      destruct H as [HWF1 H]. destruct H as [HWF2 H].
      destruct H as [Hdom1 H]. destruct H as [Hdom2 H].
      destruct H as [Hphi1 H]. destruct H as [Hphi2 H].
      destruct H as [Hsum1 H]. destruct H as [Hsum2 Hmu].
      simpl. left. 
      exists p1, p2. split; try assumption. split; try assumption. split; try assumption.
      simpl in *.
      pose (V:= (orb_domain (get_var_in_Pformular phi1) (get_var_in_Pformular phi2))).
      assert (HV1': is_domain_subset V pd1.(dom) = true). {
          apply dom_equiv_sym in Hdom1.
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
      pose (pd1':= Build_partial_dist V (pd1.(mu) \| V) 
                      (PD_after_res V (dom pd1) (mu pd1) HV1' (pd1.(all_partial)))).
      assert (HV2': is_domain_subset V pd2.(dom) = true). {
          apply dom_equiv_sym in Hdom2.
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
      pose (pd2':= Build_partial_dist V (pd2.(mu) \| V) 
                      (PD_after_res V (dom pd2) (mu pd2) HV2' (pd2.(all_partial)))).
      exists pd1', pd2'.    
      split. { simpl. apply Valid_after_resX. assumption. }
      split. { simpl. apply Valid_after_resX. assumption. }
      split. { simpl. apply dom_equiv_refl. }
      split. { simpl. apply dom_equiv_refl. }
      inversion HWD; subst. 
      simpl in Hdom. apply dom_subset_orb_fst_iff in Hdom. 
      split. { destruct Hdom. 
        apply dom_equiv_sym in Hdom1. 
        apply dom_subset_eq_compat_left with (Y:= dom pd1) in H; try assumption.
        specialize (IHphi1 H1 pd1 H HWF1 Hphi1). 
        assert (HV: is_domain_subset (get_var_in_Pformular phi1) V = true). { 
            apply dom_subset_orb_dom_r. apply dom_subset_refl. }
        apply sem_resV_implies_pd with (V:= get_var_in_Pformular phi1) (HV:= HV); try assumption. 
          - apply Valid_after_resX. assumption.
          - apply dom_equiv_refl.
          - apply pd_equiv_preserves_sem with (pd0:= 
          {|
            dom := get_var_in_Pformular phi1;
            mu := (mu pd1) \| (get_var_in_Pformular phi1);
            all_partial :=
              PD_after_res (get_var_in_Pformular phi1) (dom pd1) 
                    (mu pd1) H (all_partial pd1)
          |}); try assumption. 
            + simpl. apply Valid_after_resX. assumption.
            + simpl. apply Valid_after_resX. apply Valid_after_resX. assumption.
            + simpl. split; simpl; try apply dom_equiv_refl.
          apply dst_equiv_sym. apply res_to_subset_equiv. assumption. }
      split. { destruct Hdom. 
        apply dom_equiv_sym in Hdom2. 
        apply dom_subset_eq_compat_left with (Y:= dom pd2) in H0; try assumption.
        specialize (IHphi2 H2 pd2 H0 HWF2 Hphi2). 
        assert (HV: is_domain_subset (get_var_in_Pformular phi2) V = true). { 
            apply dom_subset_orb_dom_l. apply dom_subset_refl. }
        apply sem_resV_implies_pd with (V:= get_var_in_Pformular phi2) (HV:= HV); try assumption. 
          - apply Valid_after_resX. assumption.
          - apply dom_equiv_refl.
          - apply pd_equiv_preserves_sem with (pd0:= 
          {|
            dom := get_var_in_Pformular phi2;
            mu := (mu pd2) \| (get_var_in_Pformular phi2);
            all_partial :=
              PD_after_res (get_var_in_Pformular phi2) (dom pd2) 
                (mu pd2) H0 (all_partial pd2)
          |}); try assumption. 
            + simpl. apply Valid_after_resX. assumption.
            + simpl. apply Valid_after_resX. apply Valid_after_resX. assumption.
            + simpl. split; simpl; try apply dom_equiv_refl.
          apply dst_equiv_sym. apply res_to_subset_equiv. assumption. }
      split. { simpl. repeat rewrite <- sum_eq_after_res. assumption. }
      split. { simpl. repeat rewrite <- sum_eq_after_res. assumption. }
      simpl. repeat rewrite <- res_dst_to_X_mult_coef.
      rewrite <- res_add_decom_eq. 
      apply Peq_implies_res_eq; try assumption.
      apply Valid_linear_under_eq_prob; try assumption. 
      * destruct Hp1. apply Rlt_le. assumption.
      * destruct Hp2. apply Rlt_le. assumption.
      * rewrite Hsum1. rewrite Hsum2. rewrite <- Rmult_plus_distr_r. 
        rewrite Hp_case1. rewrite Rmult_1_l.
        destruct HWF. assumption.
    + destruct Hsem as [Hcase2 |Hcase3]. 
      * destruct Hcase2 as [pd1 H].
      destruct H as [HWF1 H]. destruct H as [Heq1 H].
      destruct H as [Hsub2 H]. 
      destruct H as [Hphi1 Hsum1].
      simpl. right. left. 
      destruct Heq1 as [Hdom1 Hmu1].
      pose (V:= (orb_domain (get_var_in_Pformular phi1) (get_var_in_Pformular phi2))).
      assert (HV1': is_domain_subset V pd1.(dom) = true). {
          apply dom_equiv_sym in Hdom1.
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
      pose (pd1':= Build_partial_dist V (pd1.(mu) \| V) 
                      (PD_after_res V (dom pd1) (mu pd1) HV1' (pd1.(all_partial)))).
      exists pd1'.
      split. { simpl. apply Valid_after_resX. assumption. }
      split. { split; simpl; try apply dom_equiv_refl. apply Peq_implies_res_eq; try assumption. }
      inversion HWD; subst. simpl in Hdom. apply dom_subset_orb_fst_iff in Hdom.
      split. { apply dom_subset_orb_snd_l_r. } 
      split. { destruct Hdom. 
        apply dom_equiv_sym in Hdom1. 
        apply dom_subset_eq_compat_left with (Y:= dom pd1) in H; try assumption.
        specialize (IHphi1 H1 pd1 H HWF1 Hphi1). 
        assert (HV: is_domain_subset (get_var_in_Pformular phi1) V = true). { 
            apply dom_subset_orb_dom_r. apply dom_subset_refl. }
        apply sem_resV_implies_pd with (V:= get_var_in_Pformular phi1) (HV:= HV); try assumption. 
          - apply Valid_after_resX. assumption.
          - apply dom_equiv_refl.
          - apply pd_equiv_preserves_sem with (pd0:= 
          {|
            dom := get_var_in_Pformular phi1;
            mu := (mu pd1) \| (get_var_in_Pformular phi1);
            all_partial :=
              PD_after_res (get_var_in_Pformular phi1) (dom pd1) 
                    (mu pd1) H (all_partial pd1)
          |}); try assumption. 
            + simpl. apply Valid_after_resX. assumption.
            + simpl. apply Valid_after_resX. apply Valid_after_resX. assumption.
            + simpl. split; simpl; try apply dom_equiv_refl.
          apply dst_equiv_sym. apply res_to_subset_equiv. assumption. }
      simpl. repeat rewrite <- sum_eq_after_res. assumption.
      * destruct Hcase3 as [pd2 H].
      destruct H as [HWF2 H]. destruct H as [Heq2 H].
      destruct H as [Hsub1 H].
      destruct H as [Hphi2 Hsum2].
      simpl. right. right. 
      destruct Heq2 as [Hdom2 Hmu2].
      pose (V:= (orb_domain (get_var_in_Pformular phi1) (get_var_in_Pformular phi2))).
      assert (HV2': is_domain_subset V pd2.(dom) = true). {
          apply dom_equiv_sym in Hdom2.
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
      pose (pd2':= Build_partial_dist V (pd2.(mu) \| V) 
                      (PD_after_res V (dom pd2) (mu pd2) HV2' (pd2.(all_partial)))).
      exists pd2'.
      split. { simpl. apply Valid_after_resX. assumption. }
      split. { split; simpl; try apply dom_equiv_refl. apply Peq_implies_res_eq; try assumption. }
      inversion HWD; subst. simpl in Hdom. apply dom_subset_orb_fst_iff in Hdom. 
      split. { apply dom_subset_orb_snd_l_r. } 
      split. { destruct Hdom. 
        apply dom_equiv_sym in Hdom2. 
        apply dom_subset_eq_compat_left with (Y:= dom pd2) in H0; try assumption.
        specialize (IHphi2 H2 pd2 H0 HWF2 Hphi2). 
        assert (HV: is_domain_subset (get_var_in_Pformular phi2) V = true). { 
            apply dom_subset_orb_dom_l. apply dom_subset_refl. }
        apply sem_resV_implies_pd with (V:= get_var_in_Pformular phi2) (HV:= HV); try assumption. 
          - apply Valid_after_resX. assumption.
          - apply dom_equiv_refl.
          - apply pd_equiv_preserves_sem with (pd0:= 
          {|
            dom := get_var_in_Pformular phi2;
            mu := (mu pd2) \| (get_var_in_Pformular phi2);
            all_partial :=
              PD_after_res (get_var_in_Pformular phi2) (dom pd2) 
                (mu pd2) H0 (all_partial pd2)
          |}); try assumption. 
            + simpl. apply Valid_after_resX. assumption.
            + simpl. apply Valid_after_resX. apply Valid_after_resX. assumption.
            + simpl. split; simpl; try apply dom_equiv_refl.
          apply dst_equiv_sym. apply res_to_subset_equiv. assumption. }
      simpl. repeat rewrite <- sum_eq_after_res. assumption.
  - simpl in Hsem. 
    destruct Hsem as [pd1 H]. destruct H as [pd2 H]. 
    destruct H as [Hinter H]. 
    destruct H as [HWF1 H]. destruct H as [HWF2 H]. 
    destruct H as [Hphi1 H]. destruct H as [Hphi2 H].
    destruct H as [Hsub_comb Hmu_comb]. simpl in *. 
    assert (Hsub1: is_domain_subset (get_var_in_Pformular phi1) (dom pd1) = true). { 
      inversion HWD; subst. apply satisfy_implies_dom_sub in Hphi1; try assumption. }
    assert (Hsub2: is_domain_subset (get_var_in_Pformular phi2) (dom pd2) = true). { 
      inversion HWD; subst. apply satisfy_implies_dom_sub in Hphi2; try assumption. }
    pose (pd1':= Build_partial_dist (get_var_in_Pformular phi1) 
                    (pd1.(mu) \| (get_var_in_Pformular phi1) ) 
                    (PD_after_res (get_var_in_Pformular phi1)  (dom pd1) (mu pd1) Hsub1 (pd1.(all_partial)))). 
    pose (pd2':= Build_partial_dist (get_var_in_Pformular phi2) 
                    (pd2.(mu) \| (get_var_in_Pformular phi2)) 
                    (PD_after_res (get_var_in_Pformular phi2) (dom pd2) (mu pd2) Hsub2 (pd2.(all_partial)))). 
    exists pd1', pd2'. simpl. 
    inversion HWD; subst. 
    exists H3. 
    split. { simpl. apply Valid_after_resX. assumption. }
    split. { simpl. apply Valid_after_resX. assumption. }
    split. { apply IHphi1; try assumption. }
    split. {  apply IHphi2; try assumption.  }

    split; simpl. 
      + apply dom_subset_orb_compat; try apply dom_subset_refl. 
      + simpl. 
      simpl in *. apply dst_equiv_sym.
      pose (X':= (orb_domain (get_var_in_Pformular phi1) (get_var_in_Pformular phi2))).
      fold X'. apply dst_equiv_trans with (mu1:= ((mu pd) \| X')). 
        * apply dst_equiv_trans with (mu1:= ((mu pd1) ⊗ (mu pd2)) \| X').
        ** apply combine_res_merge_equiv; try assumption.
        ** apply dst_equiv_sym. 
        apply dst_equiv_trans with (mu1:= (mu pd) \| (orb_domain (dom pd1) (dom pd2)) \| X'). 
        -- apply res_to_subset_equiv; try assumption. 
          apply dom_subset_orb_compat; try assumption.
        -- apply Peq_implies_res_eq with (X:= X') in Hmu_comb; try assumption. 
          ++ apply Valid_after_resX. assumption.
          ++ apply Valid_after_combine; try assumption.
        * apply res_to_subset_equiv; try assumption. apply dom_subset_refl.
  - simpl in Hsem. destruct Hsem.
    inversion HWD; subst. 
    assert (HsubV: is_domain_subset (get_var_in_Pformular phi1 ∪ get_var_in_Pformular phi2)%domain
                                    (dom pd) = true) by assumption.
    simpl in HsubV. apply dom_subset_orb_fst_iff in HsubV. destruct HsubV.
    simpl. split; simpl.
    + apply IHphi1 with (Hdom:= H1) in H; try assumption. 
      assert (HV: is_domain_subset (get_var_in_Pformular phi1) 
                                    (get_var_in_Pformular phi1 ∪ get_var_in_Pformular phi2)%domain = true). {
        apply dom_subset_orb_snd_l_r; try assumption. }
      apply sem_resV_implies_pd with (V:= (get_var_in_Pformular phi1)) (HV:= HV); try assumption.
      * apply Valid_after_resX. assumption.
      * apply dom_equiv_refl.
      * apply pd_equiv_preserves_sem with (pd0:= 
          {|
          dom := get_var_in_Pformular phi1;
          mu := (mu pd) \| (get_var_in_Pformular phi1);
          all_partial :=
            PD_after_res (get_var_in_Pformular phi1) (dom pd) 
              (mu pd) H1 (all_partial pd)
        |}); try assumption. 
        ** apply Valid_after_resX. assumption.
        ** apply Valid_after_resX. apply Valid_after_resX. assumption.
        ** simpl. split; simpl; try apply dom_equiv_refl.
          apply dst_equiv_sym. apply res_to_subset_equiv. assumption.
    + apply IHphi2 with (Hdom:= H2) in H0; try assumption. 
      assert (HV: is_domain_subset (get_var_in_Pformular phi2) 
                                    (get_var_in_Pformular phi1 ∪ get_var_in_Pformular phi2)%domain = true). {
        apply dom_subset_orb_snd_l_r; try assumption. }
      apply sem_resV_implies_pd with (V:= (get_var_in_Pformular phi2)) (HV:= HV); try assumption.
      * apply Valid_after_resX. assumption.
      * apply dom_equiv_refl.
      * apply pd_equiv_preserves_sem with (pd0:= 
          {|
          dom := get_var_in_Pformular phi2;
          mu := (mu pd) \| (get_var_in_Pformular phi2);
          all_partial := PD_after_res (get_var_in_Pformular phi2) (dom pd) 
                                      (mu pd) H2 (all_partial pd)
        |}); try assumption. 
        ** apply Valid_after_resX. assumption.
        ** apply Valid_after_resX. apply Valid_after_resX. assumption.
        ** simpl. split; simpl; try apply dom_equiv_refl.
          apply dst_equiv_sym. apply res_to_subset_equiv. assumption.

Qed. 

Lemma sem_satisfies_project_implies_V: (*Another side of lemma 4 *)
  forall pd phi V (HV: is_domain_subset V pd.(dom) = true),
    Valid_dist pd.(mu) -> well_defined_Pf phi ->
    is_domain_subset (get_var_in_Pformular phi) V = true -> 
    [[phi]] pd -> 
    [[phi]] (Build_partial_dist V (pd.(mu) \| V) 
                    (PD_after_res V (dom pd) (mu pd) HV (pd.(all_partial)))).
Proof.
  intros pd phi V HV HWF HWD HsubV Hsem.
  generalize dependent pd. generalize dependent V.
  induction phi.
  - intros. apply df_sem_project_implies_V with (V:= V); try assumption.
  - intros. simpl in Hsem. destruct Hsem as [Hcase1| Hsem].
    + destruct Hcase1 as [Hp_case1 H]. 
      destruct H as [pd1 H]. destruct H as [pd2 H].
      destruct H as [HWF1 H]. destruct H as [HWF2 H]. 
      destruct H as [Hdom1 H]. destruct H as [Hdom2 H].
      destruct H as [Hphi1 H]. destruct H as [Hphi2 H].
      destruct H as [Hsum1 H]. destruct H as [Hsum2 Hmu].
      simpl. left. split; try assumption.
      assert (HV1': is_domain_subset V pd1.(dom) = true). {
          apply dom_equiv_sym in Hdom1.
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
      pose (pd1':= Build_partial_dist V (pd1.(mu) \| V) 
                      (PD_after_res V (dom pd1) (mu pd1) HV1' (pd1.(all_partial)))).
      assert (HV2': is_domain_subset V pd2.(dom) = true). {
          apply dom_equiv_sym in Hdom2.
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
      pose (pd2':= Build_partial_dist V (pd2.(mu) \| V) 
                      (PD_after_res V (dom pd2) (mu pd2) HV2' (pd2.(all_partial)))).
      exists pd1', pd2'.
      split. { simpl. apply Valid_after_resX. assumption. }
      split. { simpl. apply Valid_after_resX. assumption. }
      split. { simpl. apply dom_equiv_refl. }
      split. { simpl. apply dom_equiv_refl. }
      inversion HWD; subst. 
      simpl in HsubV. 
      destruct Hp_case1 as [Hgt0 Hlt1].
      destruct (Rle_lt_dec r 0) eqn: Hp0; destruct (Rle_lt_dec 1 r) eqn: Hp1.
      * destruct H2. 
        assert (Hr: r = 1). { apply Rle_antisym; try assumption. }
        assert (Hcontra: 1<1). { rewrite Hr in Hlt1. assumption. }
        apply Rlt_irrefl in Hcontra. contradiction.
      * destruct H2. 
        assert (Hr: r = 0). { apply Rle_antisym; try assumption. }
        assert (Hcontra: 0<0). { rewrite Hr in Hgt0. assumption. }
        apply Rlt_irrefl in Hcontra. contradiction.
      * destruct H2. 
        assert (Hr: r = 1). { apply Rle_antisym; try assumption. }
        assert (Hcontra: 1<1). { rewrite Hr in Hlt1. assumption. }
        apply Rlt_irrefl in Hcontra. contradiction.
      * apply dom_subset_orb_fst_iff in HsubV. destruct HsubV. 
        split. { apply IHphi1; try assumption. }
        split. { apply IHphi2; try assumption. }
        split. { simpl. repeat rewrite <- sum_eq_after_res. assumption. }
        split. { simpl. repeat rewrite <- sum_eq_after_res. assumption. }
        simpl. repeat rewrite <- res_dst_to_X_mult_coef.
        rewrite <- res_add_decom_eq. 
        apply Peq_implies_res_eq; try assumption.
        apply Valid_linear_under_eq_prob; try assumption. 
        ** apply Rlt_le. assumption.
        ** assert (Hp_minus: 0 < 1-r < 1). { apply Rp_lt1_minus_p_bounds with (p:= r). split; assumption. }
          destruct Hp_minus. apply Rlt_le. assumption.
        ** rewrite Hsum1. rewrite Hsum2. rewrite <- Rmult_plus_distr_r. 
          rewrite R_plus_sub_eq_1. rewrite Rmult_1_l.
          destruct HWF. assumption.
    + destruct Hsem as [Hcase2 |Hcase3]. 
      * destruct Hcase2 as [Hp_case2 H]. destruct H as [pd1 H].
      destruct H as [HWF1 H]. destruct H as [Heq1 H].
      destruct H as [Hphi1 Hsum1].
      simpl. right. left. split; try assumption.
      destruct Heq1 as [Hdom1 Hmu1].
      assert (HV1': is_domain_subset V pd1.(dom) = true). {
          apply dom_equiv_sym in Hdom1.
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
      pose (pd1':= Build_partial_dist V (pd1.(mu) \| V) 
                      (PD_after_res V (dom pd1) (mu pd1) HV1' (pd1.(all_partial)))).
      exists pd1'.
      split. { simpl. apply Valid_after_resX. assumption. }
      split. { split; simpl; try apply dom_equiv_refl. apply Peq_implies_res_eq; try assumption. }
      simpl in HsubV. subst. 
      destruct (Rle_lt_dec 1 0); destruct (Rle_lt_dec 1 1); try apply Rlt_irrefl in r0; try contradiction.
      ** apply Rle_not_lt in r. unfold not in r. exfalso. apply r. apply Rlt_0_1. 
      ** split. { inversion HWD; subst. apply IHphi1; try assumption. }
      simpl. repeat rewrite <- sum_eq_after_res. assumption.
      * destruct Hcase3 as [Hp_case3 H]. destruct H as [pd2 H].
      destruct H as [HWF2 H]. destruct H as [Heq2 H].
      destruct H as [Hphi2 Hsum2].
      simpl. right. right. split; try assumption.
      destruct Heq2 as [Hdom2 Hmu2].
      assert (HV2': is_domain_subset V pd2.(dom) = true). {
          apply dom_equiv_sym in Hdom2.
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
      pose (pd2':= Build_partial_dist V (pd2.(mu) \| V) 
                      (PD_after_res V (dom pd2) (mu pd2) HV2' (pd2.(all_partial)))).
      exists pd2'.
      split. { simpl. apply Valid_after_resX. assumption. }
      split. { split; simpl; try apply dom_equiv_refl. apply Peq_implies_res_eq; try assumption. }
      simpl in HsubV. subst.
      destruct (Rle_lt_dec 0 0); destruct (Rle_lt_dec 1 0); try apply Rlt_irrefl in r; try contradiction.
      ** apply Rle_not_lt in r0. unfold not in r0. exfalso. apply r0. apply Rlt_0_1. 
      ** split. { inversion HWD; subst. apply IHphi2; try assumption. }
        simpl. repeat rewrite <- sum_eq_after_res. assumption.
  - intros. simpl in Hsem. destruct Hsem as [Hcase1 |Hsem]. 
    + destruct Hcase1 as [p1 H]. destruct H as [p2 H]. 
      destruct H as [Hp1 H]. destruct H as [Hp2 H].
      destruct H as [Hp_case1 H]. 
      destruct H as [pd1 H]. destruct H as [pd2 H].
      destruct H as [HWF1 H]. destruct H as [HWF2 H].
      destruct H as [Hdom1 H]. destruct H as [Hdom2 H].
      destruct H as [Hphi1 H]. destruct H as [Hphi2 H].
      destruct H as [Hsum1 H]. destruct H as [Hsum2 Hmu].
      simpl. left. 
      exists p1, p2. split; try assumption. split; try assumption. split; try assumption.
      simpl in *.
      assert (HV1': is_domain_subset V pd1.(dom) = true). {
          apply dom_equiv_sym in Hdom1.
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
      pose (pd1':= Build_partial_dist V (pd1.(mu) \| V) 
                      (PD_after_res V (dom pd1) (mu pd1) HV1' (pd1.(all_partial)))).
      assert (HV2': is_domain_subset V pd2.(dom) = true). {
          apply dom_equiv_sym in Hdom2.
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
      pose (pd2':= Build_partial_dist V (pd2.(mu) \| V) 
                      (PD_after_res V (dom pd2) (mu pd2) HV2' (pd2.(all_partial)))).
      exists pd1', pd2'.    
      split. { simpl. apply Valid_after_resX. assumption. }
      split. { simpl. apply Valid_after_resX. assumption. }
      split. { simpl. apply dom_equiv_refl. }
      split. { simpl. apply dom_equiv_refl. }
      inversion HWD; subst. 
      simpl in HsubV. apply dom_subset_orb_fst_iff in HsubV. destruct HsubV. 
      split. { apply IHphi1; try assumption. }
      split. { apply IHphi2; try assumption. }
      split. { simpl. repeat rewrite <- sum_eq_after_res. assumption. }
      split. { simpl. repeat rewrite <- sum_eq_after_res. assumption. }
      simpl. repeat rewrite <- res_dst_to_X_mult_coef.
      rewrite <- res_add_decom_eq. 
      apply Peq_implies_res_eq; try assumption.
      apply Valid_linear_under_eq_prob; try assumption. 
      * destruct Hp1. apply Rlt_le. assumption.
      * destruct Hp2. apply Rlt_le. assumption.
      * rewrite Hsum1. rewrite Hsum2. rewrite <- Rmult_plus_distr_r. 
        rewrite Hp_case1. rewrite Rmult_1_l.
        destruct HWF. assumption.
    + destruct Hsem as [Hcase2 |Hcase3]. 
      * destruct Hcase2 as [pd1 H].
      destruct H as [HWF1 H]. destruct H as [Heq1 H].
      destruct H as [Hsub2 H]. 
      destruct H as [Hphi1 Hsum1].
      simpl. right. left. 
      destruct Heq1 as [Hdom1 Hmu1].
      assert (HV1': is_domain_subset V pd1.(dom) = true). {
          apply dom_equiv_sym in Hdom1.
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
      pose (pd1':= Build_partial_dist V (pd1.(mu) \| V) 
                      (PD_after_res V (dom pd1) (mu pd1) HV1' (pd1.(all_partial)))).
      exists pd1'.
      split. { simpl. apply Valid_after_resX. assumption. }
      split. { split; simpl; try apply dom_equiv_refl. apply Peq_implies_res_eq; try assumption. }
      simpl in HsubV. apply dom_subset_orb_fst_iff in HsubV. destruct HsubV.
      split. { assumption. }
      split. { inversion HWD; subst. apply IHphi1; try assumption. }
      simpl. repeat rewrite <- sum_eq_after_res. assumption.
      * destruct Hcase3 as [pd2 H].
      destruct H as [HWF2 H]. destruct H as [Heq2 H].
      destruct H as [Hsub1 H].
       destruct H as [Hphi2 Hsum2].
      simpl. right. right. 
      destruct Heq2 as [Hdom2 Hmu2].
      assert (HV2': is_domain_subset V pd2.(dom) = true). {
          apply dom_equiv_sym in Hdom2.
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
      pose (pd2':= Build_partial_dist V (pd2.(mu) \| V) 
                      (PD_after_res V (dom pd2) (mu pd2) HV2' (pd2.(all_partial)))).
      exists pd2'.
      split. { simpl. apply Valid_after_resX. assumption. }
      split. { split; simpl; try apply dom_equiv_refl. apply Peq_implies_res_eq; try assumption. }
      simpl in HsubV. apply dom_subset_orb_fst_iff in HsubV. destruct HsubV. 
      split. { assumption. }
      split. { inversion HWD; subst. apply IHphi2; try assumption. }
      simpl. repeat rewrite <- sum_eq_after_res. assumption.
  - intros. 
    assert (Hsub': is_domain_subset (get_var_in_Pformular (phi1 ⊙ phi2)) (dom pd) = true ). { 
      apply dom_subset_trans with (l1:= V); try assumption. }
    pose (pd':= Build_partial_dist (get_var_in_Pformular (phi1 ⊙ phi2))  ((pd.(mu))\| (get_var_in_Pformular (phi1 ⊙ phi2))) 
              (PD_after_res (get_var_in_Pformular (phi1 ⊙ phi2)) (dom pd) (mu pd) Hsub' (pd.(all_partial)))).
    assert (Hsem': [[phi1 ⊙ phi2]] pd'). { 
      apply sem_satisfies_project_implies_phi with (Hdom:= Hsub') in Hsem; try assumption. }
    destruct Hsem'. destruct H. destruct H. destruct H. destruct H0. destruct H1. destruct H2.
    destruct H3. simpl in H3. simpl in H4. 
    simpl. exists x, x0, x1. 
    split; try assumption. 
    split; try assumption.
    split. { assumption. }
    split. { assumption. }
    split; simpl; try assumption.
    + apply dom_subset_trans with (l1:= (orb_domain (get_var_in_Pformular phi1) (get_var_in_Pformular phi2))); try assumption.
    + pose (X':= (orb_domain (get_var_in_Pformular phi1) (get_var_in_Pformular phi2))).
      fold X' in H4. 
      apply dst_equiv_trans with (mu1:= (mu pd) \| X' \| (dom x ∪ dom x0)%domain); try assumption.
      apply dst_equiv_trans with (mu1:= ((mu pd) \| (dom x ∪ dom x0)%domain)). 
        * apply dst_equiv_sym. apply res_to_subset_equiv; try assumption. 
          apply dom_subset_trans with (l1:= X'); try assumption.
        * apply res_to_subset_equiv; try assumption. 
  - intros. simpl in Hsem. destruct Hsem.
    inversion HWD; subst. 
    simpl in HsubV. apply dom_subset_orb_fst_iff in HsubV. destruct HsubV.
    simpl. split; simpl.
    + apply IHphi1; try assumption.
    + apply IHphi2; try assumption.
Qed.  

Lemma sem_preserve_subst_pd : 
  forall pd pd' (phi : Pformula),
    Valid_dist pd.(mu) -> Valid_dist pd'.(mu) ->
    well_defined_Pf phi ->
    is_domain_subset (get_var_in_Pformular phi) pd.(dom) = true ->
    pd ⊑ pd' -> [[phi]] pd -> 
    [[phi]] pd'.
Proof.
  intros pd pd' phi HV HV' HWD Hsub Hpd Hsem.
  destruct Hpd. 
  apply sem_resV_implies_pd with (V:= dom pd) (HV:= H); try assumption.
  assert (Heq: {|
        dom := dom pd;
        mu := (mu pd') \| (dom pd);
        all_partial := PD_after_res (dom pd) (dom pd') (mu pd') H (all_partial pd')
      |} ≡ pd). { 
      split; simpl; try apply dom_equiv_refl. assumption. }
  apply pd_equiv_preserves_sem with (pd0:= pd); try assumption.
  simpl. apply Valid_after_resX. assumption.
Qed.

(*************************************)
Lemma odot_satisfies_iff: forall pd phi1 phi2,
  let X1:= (get_var_in_Pformular phi1) in 
  let X2:= (get_var_in_Pformular phi2) in 
    (well_defined_Pf (phi1 ⊙ phi2) /\ Valid_dist pd.(mu) /\ [[phi1 ⊙ phi2]] pd) <-> 
    (well_defined_Pf phi1 /\ well_defined_Pf phi2 /\ 
      Valid_dist (mu pd) /\ 
      [[phi1]] pd /\ [[phi2]] pd /\ 
      (independent pd.(mu) X1 X2) /\
      is_domain_intersect X1 X2 = false ).
Proof. 
  split. 
  { 
    intros. destruct H as [HWD H]. destruct H as [HWF H].
    inversion HWD; subst. 
    destruct H as [mu0 H]. destruct H as [mu1 H]. 
    destruct H as [HPD' H]. 
    destruct H as [Hvalid0 H]. destruct H as [Hvalid1 H].
    destruct H as [Hsem0 H]. destruct H as [Hsem1 H].
    simpl in *. 
    split; try assumption.
    split; try assumption.
    split; try assumption.
    split. { 
      destruct H. simpl in H. simpl in H0.
      apply dom_subset_orb_fst_iff in H. 
      destruct H.
      apply sem_resV_implies_pd with (V:= dom mu0) (HV:= H); try assumption.
      - apply satisfy_implies_dom_sub; assumption.
      - pose (p:= sum_probs (mu mu1)).
      assert (Hp: 0 <= p <= 1). { unfold p. destruct Hvalid1. assumption. }
      pose (pd0':= Build_partial_dist (dom mu0) (p*(mu mu0)) (pd_mult_preserve_PD mu0 p)).
      apply pd_equiv_preserves_sem with (pd0:= pd0'); try assumption. 
        + simpl. apply Valid_mult_cofe; try assumption. 
        + simpl. apply Valid_after_resX. assumption.
        + split; simpl; try apply dom_equiv_refl. 
          apply Peq_implies_res_eq with (X:= dom mu0) in H0; try assumption.
          * apply dst_equiv_trans with (mu1:= ((mu pd) \| (orb_domain (dom mu0) (dom mu1))) \| (dom mu0)) . 
          ** apply res_to_subset_equiv. apply dom_subset_orb_snd_l_r.
          ** apply dst_equiv_trans with (mu1:= (mu mu0 ⊗ mu mu1) \| (dom mu0)); try assumption.
          unfold p. apply res_comb_equiv; try assumption.
          * apply Valid_after_resX. assumption.
          * apply Valid_after_combine; try assumption.
        + assert (HWF0': Valid_dist (mu pd0')). {
            apply Valid_mult_cofe; try assumption. }
          destruct HWF0'.  simpl in H5.
          destruct Hp. apply sem_mult_cofe; try assumption.
    }
    split. { 
      destruct H. simpl in H. simpl in H0.
      apply dom_subset_orb_fst_iff in H. 
      destruct H.
      apply sem_resV_implies_pd with (V:= dom mu1) (HV:= H1); try assumption.
      - apply satisfy_implies_dom_sub; assumption.
      - pose (p:= sum_probs (mu mu0)).
      assert (Hp: 0 <= p <= 1). { unfold p. destruct Hvalid0. assumption. }
      pose (pd1':= Build_partial_dist (dom mu1) (p*(mu mu1)) (pd_mult_preserve_PD mu1 p)).
      apply pd_equiv_preserves_sem with (pd0:= pd1'); try assumption. 
        + simpl. apply Valid_mult_cofe; try assumption. 
        + simpl. apply Valid_after_resX. assumption.
        + split; simpl; try apply dom_equiv_refl. 
        apply Peq_implies_res_eq with (X:= dom mu1) in H0; try assumption.
          * apply dst_equiv_trans with (mu1:= ((mu pd) \| (orb_domain (dom mu0) (dom mu1))) \| (dom mu1)) . 
          ** apply res_to_subset_equiv. apply dom_subset_orb_snd_l_r.
          ** apply dst_equiv_trans with (mu1:= (mu mu0 ⊗ mu mu1) \| (dom mu1)); try assumption.
          apply dst_equiv_trans with (mu1:= (mu mu1 ⊗ mu mu0) \| (dom mu1)).
          -- apply Peq_implies_res_eq; try apply Valid_after_combine; try assumption.
              apply combine_sym.
          -- unfold p. apply res_comb_equiv; try assumption. 
          rewrite intersect_comm. assumption.
          * apply Valid_after_resX. assumption.
          * apply Valid_after_combine; try assumption.
        + assert (HWF0': Valid_dist (mu pd1')). {
            apply Valid_mult_cofe; try assumption. }
          destruct HWF0'. simpl in H5.
          destruct Hp. apply sem_mult_cofe; try assumption.
    }
    split; try assumption. 
    assert (Hsubmu0: is_domain_subset (dom mu0) (dom pd) = true). { 
      destruct H. simpl in H. apply dom_subset_orb_fst_iff in H. destruct H. assumption. }  
    assert (Hsubmu1: is_domain_subset (dom mu1) (dom pd) = true). { 
      destruct H. simpl in H. apply dom_subset_orb_fst_iff in H. destruct H. assumption. }  
    assert (Hsub1: is_domain_subset (get_var_in_Pformular phi1) (dom mu0) = true). { 
      apply satisfy_implies_dom_sub in Hsem0; assumption. }
    assert (Hsub2: is_domain_subset (get_var_in_Pformular phi2) (dom mu1) = true). { 
      apply satisfy_implies_dom_sub in Hsem1; assumption. }
    apply dst_subst_implies_independent in H; try assumption.
    eapply subst_preserves_independent; try assumption.
    - apply Hsub1.
    - apply Hsub2.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
  }
  { 
    intros. destruct H as [Hphi1 H]. destruct H as [Hphi2 H].
    destruct H as [HWF H]. 
    destruct H as [Hsem1 H]. destruct H as [Hsem2 H].
    destruct H as [Hinde H].
    split; try assumption.
    - apply WD_Odot; try assumption.
    - split; try assumption.
      destruct pd as [dom mu HPD]. 
      simpl in HWF. 
      pose (X1:= get_var_in_Pformular phi1).
      pose (X2:= get_var_in_Pformular phi2).
      assert (Hsub1: is_domain_subset X1 dom = true). { 
          apply satisfy_implies_dom_sub in Hsem1; assumption. }
      pose (pd1:= Build_partial_dist X1 (mu\| X1) 
                    (PD_after_res X1 dom mu Hsub1 HPD)).
      assert (Hsub2: is_domain_subset X2 dom = true). { 
        apply satisfy_implies_dom_sub in Hsem2; assumption. }
      pose (p:= sum_probs (mu)).
      assert (HPD_p: partial_dst_Prop dom (p*mu)). { apply PD_mult_coef; try assumption. }
      pose (pd2:= Build_partial_dist X2 ((mu\| X2))
                    (PD_after_res X2 dom mu Hsub2 HPD)).
      pose (Pd':= Build_partial_dist (dom) (p*mu) HPD_p).
      assert (Hsem_p: [[phi1 ⊙ phi2]] Pd'). {
        exists pd1, pd2. simpl. exists H.
        split. { apply Valid_after_resX. assumption. }
        split. { apply Valid_after_resX. assumption. }
        split. { unfold pd1. 
                apply  sem_satisfies_project_implies_V with (V:= X1) (HV:= Hsub1) in Hsem1; try assumption.
                apply dom_subset_refl. }
        split. { unfold pd2. 
                apply  sem_satisfies_project_implies_V with (V:= X2) (HV:= Hsub2) in Hsem2; try assumption.
                apply dom_subset_refl. }
        split; simpl in *. 
        + apply dom_subset_orb_fst_iff. split; assumption.
        + unfold independent in Hinde. fold X1 in Hinde. fold X2 in Hinde. 
          rewrite res_dst_to_X_mult_coef.
          apply dst_equiv_trans with (mu0:= p * (mu \| (X1 ∪ X2)%domain)) in Hinde; try assumption.
          unfold p. apply dst_equiv_refl. }
      destruct (Req_dec_T p 0).
      * apply sum_probs0_implies_nil in e; try assumption. 
        assert (Heq_pd: {| dom := dom; mu := mu; all_partial := HPD |} ≡ pd_emp dom). {
          split; simpl; try apply dom_equiv_refl. rewrite e. apply dst_equiv_refl. }
        apply pd_equiv_preserves_sem with (pd0:= pd_emp dom); try assumption.
      ** simpl. apply Valid_dist_nil.
      ** apply WD_Odot; try assumption.
      ** apply emp_dst_satisfies_phi; try apply WD_Odot; try assumption.
        apply dom_subset_orb_fst_iff. split; assumption.
      * apply sem_mult_cofe with (p:= 1/p) in Hsem_p; try assumption.
      ** assert (Heq_pd: {| dom := dom; mu := mu; all_partial := HPD |} ≡
        {|
          dom := (CoreDef.dom Pd');
          mu := 1 / p * (CoreDef.mu Pd');
          all_partial := pd_mult_preserve_PD Pd' (1 / p)
        |}  ). {
          split; simpl; try apply dom_equiv_refl.
          rewrite dst_mult_assoc_eq. unfold Rdiv. 
          rewrite Rmult_1_l. rewrite <- Rinv_l_sym; try assumption.
          rewrite dst_mult_1_l. apply dst_equiv_refl. }
        apply pd_equiv_preserves_sem with (pd1:= {| dom := dom; mu := mu; all_partial := HPD |}) 
          in Hsem_p; try assumption.
      ++ simpl. rewrite dst_mult_assoc_eq. unfold Rdiv. rewrite Rmult_1_l. 
        rewrite <- Rinv_l_sym; try assumption. rewrite dst_mult_1_l. assumption. 
      ++ apply WD_Odot; try assumption.
      ** apply Rlt_le. unfold Rdiv. rewrite Rmult_1_l. apply Rinv_0_lt_compat.
        destruct HWF. destruct H0. destruct H0; try assumption.
        rewrite H0 in n. contradiction.
      ** apply WD_Odot; try assumption.
      ** simpl. apply Valid_mult_cofe; try assumption. destruct HWF. assumption.
      ** simpl. rewrite dst_mult_assoc_eq. unfold Rdiv. rewrite Rmult_1_l. 
        rewrite <- Rinv_l_sym; try assumption.
        destruct HWF. rewrite dst_mult_1_l. assumption. 
  }
Qed.
(*************************************)
Lemma df_sem_add: 
  forall pd0 pd1 pd df, 
    Valid_dist (mu pd0) -> Valid_dist (mu pd1) -> Valid_dist (mu pd) ->
    (dom pd0 == dom pd)%domain -> (dom pd1 == dom pd)%domain -> 
    (mu pd) == (mu pd0 + mu pd1)%dist_state ->  
    [[Pdeter df]] pd0 -> [[Pdeter df]] pd1 -> 
    [[Pdeter df]] pd.
Proof.
  intros pd0 pd1 pd df HWF0 HWF1 HWF Hdom0 Hdom1 Hmu Hsem0 Hsem1.
  simpl. destruct Hsem0 as [Hsub0 Hsem0]. destruct Hsem1 as [Hsub1 Hsem1]. split.
  - apply dom_subset_eq_compat_left with (Z:= (get_var_in_Dformular df)) in Hdom0; try assumption.
  - intros.
  apply in_supp_mu_app_or with (mu0:= mu pd0) (mu1:= mu pd1) in H; try assumption.
  inversion H.
    + apply Hsem0. assumption. 
    + apply Hsem1. assumption. 
Qed.
Fixpoint exclude_odot (phi : Pformula) : Prop :=
  match phi with
  | Pdeter _ => True
  | Pplus _ f1 f2 => exclude_odot f1 /\ exclude_odot f2
  | Oplus f1 f2 => exclude_odot f1 /\ exclude_odot f2
  | Odot _ _ => False
  | Pand f1 f2 => exclude_odot f1 /\ exclude_odot f2
  end.
Lemma phi_sem_add: forall pd0 pd1 pd phi, (*The most important problem of the while rule*)
  Valid_dist pd.(mu) -> Valid_dist pd0.(mu) -> Valid_dist pd1.(mu) -> 
  (dom pd0 == dom pd)%domain -> (dom pd1 == dom pd)%domain ->
  pd.(mu) == pd0.(mu) + pd1.(mu) -> 
  (sum_probs pd.(mu) = sum_probs (pd0.(mu)) + sum_probs (pd1.(mu)))%R ->
  well_defined_Pf (phi) -> exclude_odot phi ->
  [[phi]] pd0 -> [[phi]] pd1 -> 
  [[phi]] pd. 
Proof.
  intros pd0 pd1 pd phi HWF HWF0 HWF1 Hdom0 Hdom1 Hmu_eq Hsum_eq HWD HEX Hsem0 Hsem1. 
  generalize dependent pd1. generalize dependent pd0.
  generalize dependent pd. induction phi as [ | | | |].
  - intros. apply df_sem_add with (pd0:= pd0) (pd1:= pd1); try assumption.
  - intros. inversion HWD; subst. 
    destruct Hsem0 as [Hsem0_case1 | Hsem0]. {
      destruct Hsem0_case1 as [Hp_case1 H']. 
      destruct H' as [pd01 H']. destruct H' as [pd02 H']. 
      destruct H' as [Hvalid01 H']. destruct H' as [Hvalid02 H'].
      destruct H' as [Hdom01 H']. destruct H' as [Hdom02 H'].
      destruct H' as [Hphi01 H']. destruct H' as [Hphi02 H'].
      destruct H' as [Hsum01 H']. destruct H' as [Hsum02 Hmu0].
      simpl in Hsem1. destruct Hsem1 as [Hsem1_case1 | Hsem1]. 
      - destruct Hsem1_case1 as [Hp_case1' H']. 
        destruct H' as [pd11 H']. destruct H' as [pd12 H']. 
        destruct H' as [Hvalid11 H']. destruct H' as [Hvalid12 H'].
        destruct H' as [Hdom11 H']. destruct H' as [Hdom12 H'].
        destruct H' as [Hphi11 H']. destruct H' as [Hphi12 H'].
        destruct H' as [Hsum11 H']. destruct H' as [Hsum12 Hmu1].
        simpl in *. left. split; try assumption.
        assert (Hdom01': (dom pd01 == dom pd)%domain). {
              apply dom_equiv_trans with (l1:= dom pd0); assumption. }
        assert (Hdom11': (dom pd11 == dom pd)%domain). {
              apply dom_equiv_trans with (l1:= dom pd1); assumption. }
        assert (Hdom02': (dom pd02 == dom pd)%domain). {
              apply dom_equiv_trans with (l1:= dom pd0); assumption. }
        assert (Hdom12': (dom pd12 == dom pd)%domain). {
              apply dom_equiv_trans with (l1:= dom pd1); assumption. }
        assert (HPD1': partial_dst_Prop (dom pd) (mu pd01+mu pd11)). {
            apply PD_decom. split.
            - destruct pd01; subst. simpl in *.
              apply Peq_dom_PD_Prop with (dom:= dom); try assumption.
              apply dom_equiv_sym. assumption.
            - destruct pd11; subst. simpl in *.
              apply Peq_dom_PD_Prop with (dom:= dom); try assumption.
              apply dom_equiv_sym. assumption. }
        pose (pd1':= Build_partial_dist (dom pd) (mu pd01+mu pd11) HPD1').
        assert (HPD2': partial_dst_Prop (dom pd) (mu pd02+mu pd12)). {
            apply PD_decom. split.
            - destruct pd02; subst. simpl in *.
              apply Peq_dom_PD_Prop with (dom:= dom); try assumption.
              apply dom_equiv_sym. assumption.
            - destruct pd12; subst. simpl in *.
              apply Peq_dom_PD_Prop with (dom:= dom); try assumption.
              apply dom_equiv_sym. assumption. }
        pose (pd2':= Build_partial_dist (dom pd) (mu pd02+mu pd12) HPD2').
        exists pd1', pd2'. 
        assert (HWF_add1: Valid_dist (mu pd01 + mu pd11)). {
          rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq.
          apply Valid_linear_under_eq_prob; try assumption; try apply Rle_0_1.
          repeat rewrite Rmult_1_l. rewrite Hsum01. rewrite Hsum11. 
          rewrite <- Hsum_eq. destruct HWF. assumption. }
        assert (HWF_add2: Valid_dist (mu pd02 + mu pd12)). {
          rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq.
          apply Valid_linear_under_eq_prob; try assumption; try apply Rle_0_1.
          repeat rewrite Rmult_1_l. rewrite Hsum02. rewrite Hsum12. 
          rewrite <- Hsum_eq. destruct HWF. assumption. }
        split; try assumption. split; try assumption.
        split. { simpl. apply dom_equiv_refl. }
        split. { simpl. apply dom_equiv_refl. }
        split. { 
          apply IHphi1 with (pd0:= pd01) (pd1:= pd11); 
            simpl; try assumption; try apply dst_equiv_refl.
          - inversion HEX; subst. assumption. 
          - apply dst_sum_prob_decom. }
        split. { 
          apply IHphi2 with (pd0:= pd02) (pd1:= pd12); 
            simpl; try assumption; try apply dst_equiv_refl.
          - inversion HEX; subst. assumption. 
          - apply dst_sum_prob_decom. }
        split. {
          simpl. rewrite dst_sum_prob_decom. 
          rewrite Hsum_eq. rewrite Hsum01. rewrite Hsum11. reflexivity. }
        split. {
          simpl. rewrite dst_sum_prob_decom. 
          rewrite Hsum_eq. rewrite Hsum02. rewrite Hsum12. reflexivity. }
        simpl. repeat rewrite dst_mult_plus_distr_r_eq. 
        apply dst_equiv_trans with (mu1:= r * (mu pd01) + (1 - r) * (mu pd02) + 
                              (r * (mu pd11) + (1 - r) * (mu pd12))); try apply dst_add_shuffle.
        apply dst_equiv_trans with (mu1:= mu pd0 + mu pd1); try assumption.
        apply dst_add_preserves_equiv; assumption.
      - destruct Hsem1 as [Hsem1_case2| Hsem1_case3].
        + destruct Hsem1_case2 as [Hp_case2' H']. 
          destruct Hp_case1. rewrite Hp_case2' in H0. 
          apply Rlt_irrefl in H0. contradiction.
        + destruct Hsem1_case3 as [Hp_case3' H'].
          destruct Hp_case1. rewrite Hp_case3' in H. 
          apply Rlt_irrefl in H. contradiction. 
      }
      destruct Hsem0 as [Hsem0_case2 | Hsem0_case3]. {
      destruct Hsem0_case2 as [Hp_case2 H']. 
      destruct H' as [pd01 H']. destruct H' as [Hvalid01 H']. 
      destruct H' as [Heq01 H']. destruct Heq01 as [Hdom01 Hmu0_eq].
      destruct H' as [Hphi01 Hsum01]. 
      simpl in Hsem1. destruct Hsem1 as [Hsem1_case1 | Hsem1]. 
      - destruct Hsem1_case1 as [Hp_case1 H']. 
        destruct Hp_case1. rewrite Hp_case2 in H0. 
        apply Rlt_irrefl in H0. contradiction.
      - destruct Hsem1 as [Hsem1_case2 | Hsem1_case3]. 
        + destruct Hsem1_case2 as [Hp_case2' H']. 
          destruct H' as [pd11 H']. destruct H' as [Hvalid11 H']. 
          destruct H' as [Heq11 H']. destruct Heq11 as [Hdom11 Hmu1_eq].
          destruct H' as [Hphi1 Hsum11].
          simpl. right. left. split; try assumption. 
          assert (Hdom01': (dom pd01 == dom pd)%domain). {
              apply dom_equiv_trans with (l1:= dom pd0); assumption. }
          assert (Hdom11': (dom pd11 == dom pd)%domain). {
              apply dom_equiv_trans with (l1:= dom pd1); assumption. }
          assert (HPD1': partial_dst_Prop (dom pd) (mu pd01+mu pd11)). {
            apply PD_decom. split.
            - destruct pd01; subst. simpl in *.
              apply Peq_dom_PD_Prop with (dom:= dom); try assumption.
              apply dom_equiv_sym. assumption.
            - destruct pd11; subst. simpl in *.
              apply Peq_dom_PD_Prop with (dom:= dom); try assumption.
              apply dom_equiv_sym. assumption. }
          pose (pd1':= Build_partial_dist (dom pd) (mu pd01+mu pd11) HPD1').
          exists pd1'. 
          assert (HWF_add1: Valid_dist (mu pd01 + mu pd11)). {
            rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq.
            apply Valid_linear_under_eq_prob; try assumption; try apply Rle_0_1.
            repeat rewrite Rmult_1_l. rewrite Hsum01. rewrite Hsum11. 
            rewrite <- Hsum_eq. destruct HWF. assumption. }
          split; try assumption. 
          split. { 
              split; try apply dom_equiv_refl. simpl. 
              apply dst_equiv_trans with (mu1:= mu pd0 + mu pd1); try assumption.
              - apply dst_add_preserves_equiv; assumption.
              - apply dst_equiv_sym. assumption. }
          split. { 
              apply IHphi1 with (pd0:= pd01) (pd1:= pd11); 
                simpl; try assumption; try apply dst_equiv_refl.
              - inversion HEX; subst. assumption. 
              - apply dst_sum_prob_decom. }
          simpl. rewrite dst_sum_prob_decom. 
          rewrite Hsum_eq. rewrite Hsum01. rewrite Hsum11. reflexivity.
        + destruct Hsem1_case3. rewrite Hp_case2 in H. apply R1_neq_R0 in H. contradiction.
      }
      destruct Hsem0_case3 as [Hp_case3 H']. 
      destruct H' as [pd02 H']. destruct H' as [Hvalid02 H']. 
      destruct H' as [Heq02 H']. destruct Heq02 as [Hdom02 Hmu0_eq].
      destruct H' as [Hphi02 Hsum02]. 
      simpl in Hsem1. destruct Hsem1 as [Hsem1_case1 | Hsem1]. 
      + destruct Hsem1_case1 as [Hp_case1 H']. 
        destruct Hp_case1. rewrite Hp_case3 in H. 
        apply Rlt_irrefl in H. contradiction.
      + destruct Hsem1 as [Hsem1_case2 | Hsem1_case3]. 
        * destruct Hsem1_case2 as [Hp_case2 H']. 
          rewrite Hp_case2 in Hp_case3. apply R1_neq_R0 in Hp_case3. contradiction.
        * destruct Hsem1_case3 as [Hp_case3' H'].
          destruct H' as [pd12 H']. destruct H' as [Hvalid12 H']. 
          destruct H' as [Heq12 H']. destruct Heq12 as [Hdom12 Hmu1_eq].
          destruct H' as [Hphi2 Hsum12].
          simpl. right. right. split; try assumption. 
          assert (Hdom02': (dom pd02 == dom pd)%domain). {
              apply dom_equiv_trans with (l1:= dom pd0); assumption. }
          assert (Hdom12': (dom pd12 == dom pd)%domain). {
              apply dom_equiv_trans with (l1:= dom pd1); assumption. }
          assert (HPD2': partial_dst_Prop (dom pd) (mu pd02+mu pd12)). {
            apply PD_decom. split.
            - destruct pd02; subst. simpl in *.
              apply Peq_dom_PD_Prop with (dom:= dom); try assumption.
              apply dom_equiv_sym. assumption.
            - destruct pd12; subst. simpl in *.
              apply Peq_dom_PD_Prop with (dom:= dom); try assumption.
              apply dom_equiv_sym. assumption. }
          pose (pd2':= Build_partial_dist (dom pd) (mu pd02+mu pd12) HPD2').
          exists pd2'. 
          assert (HWF_add1: Valid_dist (mu pd02 + mu pd12)). {
            rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq.
            apply Valid_linear_under_eq_prob; try assumption; try apply Rle_0_1.
            repeat rewrite Rmult_1_l. rewrite Hsum02. rewrite Hsum12. 
            rewrite <- Hsum_eq. destruct HWF. assumption. }
          split; try assumption. 
          split. { 
              split; try apply dom_equiv_refl. simpl. 
              apply dst_equiv_trans with (mu1:= mu pd0 + mu pd1); try assumption.
              - apply dst_add_preserves_equiv; assumption.
              - apply dst_equiv_sym. assumption. }
          split. { 
              apply IHphi2 with (pd0:= pd02) (pd1:= pd12); 
                simpl; try assumption; try apply dst_equiv_refl.
              - inversion HEX; subst. assumption. 
              - apply dst_sum_prob_decom. }
          simpl. rewrite dst_sum_prob_decom. 
          rewrite Hsum_eq. rewrite Hsum02. rewrite Hsum12. reflexivity.
  - intros. inversion HWD; subst.
    pose (A:= sum_probs (mu pd0)). pose (B:= sum_probs (mu pd1)). 
    pose (C:= sum_probs (mu pd)). 
    assert (HCAB: (C = A + B)%R). { 
      unfold A. unfold B. unfold C. apply Hsum_eq. }
    destruct pd as [dom mu HPD].  
    destruct mu as [|(s,p) mu'].
    -- assert (Hmu_nil: (mu pd0)= [] /\ (mu pd1) = []). { 
          apply dst_add_eq_nil_iff. 
          split; try assumption. split; try assumption. }
      destruct Hmu_nil; subst. simpl in Hdom0. simpl in Hdom1. 
      assert (Hequiv: {| dom := dom; mu := []; all_partial := HPD |} ≡ pd0). {
        split; simpl. 
        - apply dom_equiv_sym. assumption.
        - rewrite H. apply dst_equiv_refl. }
      apply pd_equiv_preserves_sem with (pd0:= pd0); try assumption.
    -- assert (HC: C <> 0). { 
          unfold C. simpl. symmetry. apply Rlt_not_eq. 
          apply Valid_dist_conj in HWF. destruct HWF. 
          destruct H. destruct H3. destruct H3. 
          destruct H0. apply positive_sum_ge_0 in H6. 
          apply Rplus_lt_le_0_compat; try assumption. } 
        assert (HC_gt0: 0 < C). { 
            destruct HWF. simpl in H. destruct H. unfold C. simpl.
            destruct H; try assumption.
            rewrite H in HC. unfold C in HC. simpl in HC. contradiction. }
        destruct Hsem0 as [Hsem0_case1 | Hsem0]. { (*There are three situations for mu0*)
          destruct Hsem0_case1 as [p01 H]. destruct H as [p02 H].
          destruct H as [Hp01 H]. destruct H as [Hp02 H].
          destruct H as [Hp0_case1 H]. 
          destruct H as [pd01 H]. destruct H as [pd02 H]. 
          destruct H as [Hvalid01 H]. destruct H as [Hvalid02 H].
          destruct H as [Hdom01 H]. destruct H as [Hdom02 H].
          destruct H as [Hphi01 H]. destruct H as [Hphi02 H].
          destruct H as [Hsum01 H]. destruct H as [Hsum02 Hmu0].
          simpl in Hsem1. destruct Hsem1 as [Hsem1_case1 | Hsem1]. (*There are three situations for mu1*)
          + destruct Hsem1_case1 as [p11 H]. destruct H as [p12 H].
            destruct H as [Hp11 H]. destruct H as [Hp12 H].
            destruct H as [Hp1_case1 H].   
            destruct H as [pd11 H]. destruct H as [pd12 H]. 
            destruct H as [Hvalid11 H]. destruct H as [Hvalid12 H].
            destruct H as [Hdom11 H]. destruct H as [Hdom12 H].
            destruct H as [Hphi11 H]. destruct H as [Hphi12 H].
            destruct H as [Hsum11 H]. destruct H as [Hsum12 Hmu1].
            simpl in *. left.  
            pose (p1:= (p01*A + p11*B)/C). pose (p2:= (p02*A + p12*B)/C).
            exists p1, p2.
            split. { 
              unfold p1. unfold A. unfold B. unfold C. 
              apply Rdiv_num_lt_den; try assumption.
              - destruct HWF0. assumption.
              - destruct HWF1. assumption. }
            split. { 
              unfold p2. unfold A. unfold B. unfold C. 
              apply Rdiv_num_lt_den; try assumption.
              - destruct HWF0. assumption.
              - destruct HWF1. assumption. } 
            split. { 
              unfold p1. unfold p2. rewrite <- Rdiv_plus_distr. unfold Rdiv.  
              rewrite Rplus_comm with (r1:= (p02 * A)%R).
              rewrite Rplus_assoc. rewrite <- Rplus_assoc with (r1:= (p11 * B)%R).
              rewrite <- Rmult_plus_distr_r. rewrite Hp1_case1.
              rewrite Rplus_comm with (r2:= (p02 * A)%R).
              rewrite <- Rplus_assoc.
              rewrite <- Rmult_plus_distr_r. rewrite Hp0_case1. 
              repeat rewrite Rmult_1_l.
              rewrite <- HCAB. apply Rinv_r; try assumption. }
            pose (p0':= ((C*p01)/(p01*A+p11*B))%R).
            pose (p1':= ((C*p11)/(p01*A+p11*B))%R).
            pose (p2':= ((C*p02)/(p02*A+p12*B))%R).
            pose (p3':= ((C*p12)/(p02*A+p12*B))%R).
            assert (Hp0'_gt0: 0 < p0'). { 
              unfold p0'. destruct Hp01. destruct Hp11.
              destruct HWF0. destruct H5. 
              destruct HWF1. destruct H8. 
              apply Rdiv_lt_0_compat; try assumption. 
              - apply Rmult_lt_0_compat; try assumption.
              - apply Rplus_gt0_linear; try assumption. 
              rewrite <- HCAB. assumption. }
            assert (Hp1'_gt0: 0 < p1'). { 
              unfold p1'. destruct Hp01. destruct Hp11.
              destruct HWF0. destruct H5. 
              destruct HWF1. destruct H8. 
              apply Rdiv_lt_0_compat; try assumption. 
              - apply Rmult_lt_0_compat; try assumption.
              - apply Rplus_gt0_linear; try assumption. 
              rewrite <- HCAB. assumption. }
            assert (Hp2'_gt0: 0 < p2'). { 
              unfold p2'. destruct Hp02. destruct Hp12.
              destruct HWF0. destruct H5. 
              destruct HWF1. destruct H8.  
              apply Rdiv_lt_0_compat; try assumption. 
              - apply Rmult_lt_0_compat; try assumption.
              - apply Rplus_gt0_linear; try assumption. 
              rewrite <- HCAB. assumption. }          
              assert (Hp3'_gt0: 0 < p3'). { 
              unfold p3'. destruct Hp02. destruct Hp12.
              destruct HWF0. destruct H5. 
              destruct HWF1. destruct H8. 
              apply Rdiv_lt_0_compat; try assumption. 
              - apply Rmult_lt_0_compat; try assumption.
              - apply Rplus_gt0_linear; try assumption. 
              rewrite <- HCAB. assumption. }
            assert (Hneq0: (p01*A + p11*B)%R <> 0%R). { 
              symmetry. apply Rlt_not_eq. 
              apply R_inte_help with (C:= C).
              * apply R_ge0_iff. split; try assumption. 
              unfold C. destruct HWF. destruct H. assumption.
              * apply Rdiv_num_le_den; try assumption.
                + destruct HWF0. assumption.
                + destruct HWF1. assumption.
                + destruct Hp01. split; try apply Rlt_le; try assumption.
                + destruct Hp11. split; try apply Rlt_le; try assumption. }
            assert (Hneq1: (p02*A+p12*B)%R <> 0%R). { 
              symmetry. apply Rlt_not_eq. 
              apply R_inte_help with (C:= C).
              * apply R_ge0_iff. split; try assumption. 
              unfold C. destruct HWF. destruct H. assumption.
              * apply Rdiv_num_le_den; try assumption.
                + destruct HWF0. assumption.
                + destruct HWF1. assumption.
                + destruct Hp02. split; try apply Rlt_le; try assumption.
                + destruct Hp12. split; try apply Rlt_le; try assumption. }
            assert (HPD1': partial_dst_Prop dom (p0'*(mu pd01)+p1'*(mu pd11))). {
              apply PD_linear; try assumption.
              - apply Rlt_le; try assumption.
              - apply Rlt_le; try assumption.
              - apply dom_equiv_trans with (l1:= CoreDef.dom pd0); try assumption. 
              - apply dom_equiv_trans with (l1:= CoreDef.dom pd1); try assumption. } 
            pose (pd1':= Build_partial_dist dom (p0'*(mu pd01)+p1'*(mu pd11)) HPD1').
            assert (HPD2': partial_dst_Prop dom (p2'*(mu pd02)+p3'*(mu pd12))). {
              apply PD_linear; try assumption.
              - apply Rlt_le; try assumption.
              - apply Rlt_le; try assumption.
              - apply dom_equiv_trans with (l1:= CoreDef.dom pd0); try assumption. 
              - apply dom_equiv_trans with (l1:= CoreDef.dom pd1); try assumption. } 
            pose (pd2':= Build_partial_dist dom (p2'*(mu pd02)+p3'*(mu pd12)) HPD2').
            exists pd1', pd2'. simpl.
            assert (Hv01: Valid_dist (p0' * mu pd01 + p1' * mu pd11)). { 
              try apply Valid_linear_under_eq_prob; try assumption.
              + apply Rlt_le; try assumption.
              + apply Rlt_le; try assumption.
              + rewrite Hsum01. rewrite Hsum11. split.
                - destruct HWF0. destruct H. 
                destruct HWF1. destruct H4. rewrite <- Rplus_0_l at 1. 
                apply Rplus_le_compat; apply Rmult_le_pos; try assumption;apply Rlt_le; try assumption.
                - unfold p0'. unfold p1'. unfold Rdiv.
                repeat rewrite Rmult_assoc. rewrite <- Rmult_plus_distr_l. 
                repeat rewrite Rmult_comm with (r1:= / (p01 * A + p11 * B)).
                repeat rewrite <- Rmult_assoc. rewrite <- Rmult_plus_distr_r.
                fold A. fold B. rewrite <- Rdiv_def. rewrite Rdiv_diag; try assumption.
                rewrite Rmult_1_r. destruct HWF. destruct H. assumption. }
            assert (Hv23: Valid_dist (p2' * mu pd02 + p3' * mu pd12)). { 
              try apply Valid_linear_under_eq_prob; try assumption; try apply Rlt_le; try assumption.
              rewrite Hsum02. rewrite Hsum12. split.
              - destruct HWF0. destruct H. destruct HWF1. destruct H4.
              rewrite <- Rplus_0_l at 1. 
              apply Rplus_le_compat; apply Rmult_le_pos; try assumption; try apply Rlt_le; try assumption.
              - unfold p2'. unfold p3'. unfold Rdiv.
              repeat rewrite Rmult_assoc. rewrite <- Rmult_plus_distr_l. 
              repeat rewrite Rmult_comm with (r1:= / (p02 * A + p12 * B)).
              repeat rewrite <- Rmult_assoc. rewrite <- Rmult_plus_distr_r.
              fold A. fold B. rewrite <- Rdiv_def. rewrite Rdiv_diag; try assumption.
              rewrite Rmult_1_r. destruct HWF. destruct H. assumption. }
            split; try assumption.
            split; try assumption. 
            split; try apply dom_equiv_refl. 
            split; try apply dom_equiv_refl. 
            split. { 
              pose (pd01':= Build_partial_dist (CoreDef.dom pd01) (p0' * (mu pd01)) (pd_mult_preserve_PD pd01 p0')).
              pose (pd11':= Build_partial_dist (CoreDef.dom pd11) (p1' * (mu pd11)) (pd_mult_preserve_PD pd11 p1')). 
              apply IHphi1 with (pd0:= pd01') (pd1:= pd11'); try assumption. 
              - inversion HEX; subst. assumption. 
              - simpl. apply Valid_add_decom in Hv01. destruct Hv01. assumption.
              - simpl. apply dom_equiv_trans with (l1:= CoreDef.dom pd0); try assumption.
              - apply sem_mult_cofe; try assumption; try apply Rlt_le; try assumption. 
                apply Valid_add_decom in Hv01. destruct Hv01. destruct H. assumption. 
              - simpl. apply Valid_add_decom in Hv01. destruct Hv01. assumption.
              - simpl. apply dom_equiv_trans with (l1:= CoreDef.dom pd1); try assumption.
              - simpl. apply dst_equiv_refl.
              - simpl. rewrite dst_sum_prob_decom. reflexivity.
              - apply sem_mult_cofe; try assumption; try apply Rlt_le; try assumption. 
                apply Valid_add_decom in Hv01. destruct Hv01. destruct H0. assumption. }
            split. { 
              pose (pd02':= Build_partial_dist (CoreDef.dom pd02) (p2' * (mu pd02)) (pd_mult_preserve_PD pd02 p2')).
              pose (pd12':= Build_partial_dist (CoreDef.dom pd12) (p3' * (mu pd12)) (pd_mult_preserve_PD pd12 p3')). 
              apply IHphi2 with (pd0:= pd02') (pd1:= pd12'); try assumption. 
              - inversion HEX; subst. assumption. 
              - simpl. apply Valid_add_decom in Hv23. destruct Hv23. assumption.
              - simpl. apply dom_equiv_trans with (l1:= CoreDef.dom pd0); try assumption.
              - apply sem_mult_cofe; try assumption; try apply Rlt_le; try assumption. 
                apply Valid_add_decom in Hv23. destruct Hv23. destruct H. assumption. 
              - simpl. apply Valid_add_decom in Hv23. destruct Hv23. assumption.
              - simpl. apply dom_equiv_trans with (l1:= CoreDef.dom pd1); try assumption.
              - simpl. apply dst_equiv_refl.
              - simpl. rewrite dst_sum_prob_decom. reflexivity.
              - apply sem_mult_cofe; try assumption; try apply Rlt_le; try assumption. 
                apply Valid_add_decom in Hv23. destruct Hv23. destruct H0. assumption. }
            repeat rewrite dst_sum_prob_decom.
            repeat rewrite dst_sum_prob_coef_mult.
            rewrite Hsum01. rewrite Hsum11. rewrite Hsum02. rewrite Hsum12.
            repeat fold A. repeat fold B. repeat fold C.
            split. { 
              unfold p0'. unfold p1'. unfold Rdiv.
              repeat rewrite Rmult_assoc. rewrite <- Rmult_plus_distr_l. 
              repeat rewrite Rmult_comm with (r1:= / (p01 * A + p11 * B)).
              repeat rewrite <- Rmult_assoc. rewrite <- Rmult_plus_distr_r.
              rewrite Rinv_r; try apply Rmult_1_r; try assumption. }
            split. { unfold p2'. unfold p3'. unfold Rdiv.
              repeat rewrite Rmult_assoc. rewrite <- Rmult_plus_distr_l. 
              repeat rewrite Rmult_comm with (r1:= / (p02 * A + p12 * B)).
              repeat rewrite <- Rmult_assoc. rewrite <- Rmult_plus_distr_r.
              rewrite Rinv_r; try apply Rmult_1_r; try assumption. }
            repeat rewrite dst_mult_plus_distr_r_eq.
            repeat rewrite dst_mult_assoc_eq.
            apply dst_equiv_trans with (mu1:= p1 * p0' * mu pd01 + p2 * p2' * mu pd02 + (p1 * p1' * mu pd11 + p2 * p3' * mu pd12));
              try assumption; try apply dst_add_shuffle.
            apply dst_equiv_trans with (mu1:= mu pd0 + mu pd1); try assumption.
            assert (H01: (p1 * p0' = p01)%R). { 
                unfold p0'. rewrite Rmult_comm. rewrite Rmult_comm with (r1:= C).
                rewrite <- Rmult_1_r with (r:= p01) at 3.
                unfold Rdiv. rewrite Rmult_assoc. 
                rewrite Rmult_assoc with (r1:= p01).
                apply Rmult_eq_compat_l.
                unfold p1. unfold Rdiv.
                rewrite <- Rmult_assoc with (r3:= /C). 
                rewrite <- Rinv_l_sym with (r:= (p01 * A + p11 * B)%R).
                - rewrite Rmult_1_l. apply Rinv_r. assumption.
                - assumption. }
            rewrite H01. 
            assert (H02: (p2 * p2' = p02)%R). { 
                unfold p2'. rewrite Rmult_comm. rewrite Rmult_comm with (r1:= C).
                rewrite <- Rmult_1_r with (r:= p02) at 3.
                unfold Rdiv. rewrite Rmult_assoc. 
                rewrite Rmult_assoc with (r1:= p02).
                apply Rmult_eq_compat_l.
                unfold p2. unfold Rdiv.
                rewrite <- Rmult_assoc with (r3:= /C). 
                rewrite <- Rinv_l_sym with (r:= (p02 * A + p12 * B)%R).
                - rewrite Rmult_1_l. apply Rinv_r. assumption.
                - assumption. }
            rewrite H02. 
            assert (H11: (p1 * p1' = p11)%R). { 
                unfold p1'. rewrite Rmult_comm. rewrite Rmult_comm with (r1:= C).
                rewrite <- Rmult_1_r with (r:= p11) at 3.
                unfold Rdiv. rewrite Rmult_assoc. 
                rewrite Rmult_assoc with (r1:= p11).
                apply Rmult_eq_compat_l.
                unfold p1. unfold Rdiv.
                rewrite <- Rmult_assoc with (r3:= /C).
                rewrite <- Rinv_l_sym with (r:= (p01 * A + p11 * B)%R).
                - rewrite Rmult_1_l. apply Rinv_r. assumption.
                - assumption. }
            rewrite H11.
            assert (H12: (p2 * p3' = p12)%R). {
                unfold p3'. rewrite Rmult_comm. rewrite Rmult_comm with (r1:= C).
                rewrite <- Rmult_1_r with (r:= p12) at 3.
                unfold Rdiv. rewrite Rmult_assoc. 
                rewrite Rmult_assoc with (r1:= p12).
                apply Rmult_eq_compat_l.
                unfold p2. unfold Rdiv.
                rewrite <- Rmult_assoc with (r3:= /C).
                rewrite <- Rinv_l_sym with (r:= (p02 * A + p12 * B)%R).
                - rewrite Rmult_1_l. apply Rinv_r. assumption.
                - assumption. }
            rewrite H12.
            apply dst_add_preserves_equiv; try assumption.
          + destruct Hsem1 as [Hsem1_case2| Hsem1_case3].  
            * destruct Hsem1_case2. (*mu1 only satisfies the left half formula phi1*)
              destruct H as [Hvalidx H]. destruct H as [Heq1 H].
              destruct H as [Hsub1 H]. 
              destruct H as [Hphi1x Hsumx]. 
              pose (p1:= (p01*A + B)/C). pose (p2:= (p02*A)/C).
              destruct pd0 as [dom0 mu0 HPD0]. destruct mu0 as [|(s0,p0) mu0'].
            ++ simpl. right. left. 
              exists x. split; try assumption. 
              split. { destruct Heq1. split; simpl in *. 
                - apply dom_equiv_trans with (l1:= CoreDef.dom pd1); assumption.
                - apply dst_equiv_trans with (mu1:=mu pd1); try assumption. 
                  apply dst_equiv_sym; try assumption. }
              split. { 
                simpl in Hdom1. 
                apply dom_subset_eq_compat_left with (X:= CoreDef.dom pd1); assumption. }
              split; try assumption. 
              simpl in *. rewrite Hsum_eq. rewrite Rplus_0_l. assumption. 
            ++ assert (HA: A <> 0). { unfold A. simpl. symmetry. apply Rlt_not_eq.
                apply Valid_dist_conj in HWF0. destruct HWF0. 
                destruct H. destruct H3. destruct H3. 
                destruct H0. destruct H0.
                apply Rplus_lt_le_0_compat; try assumption. }
              left. exists p1, p2.
              split. { unfold p1. rewrite HCAB.
                apply Rdiv_num_lt_den2; try assumption. 
                - destruct HWF0. destruct H. simpl in H. 
                unfold A. simpl in *. apply R_ge0_iff; split; try assumption.
                - destruct HWF1. destruct H. assumption.
                - rewrite <- HCAB. assumption. }
              split. { unfold p2. rewrite HCAB.
                apply Rdiv_pA_in_01; try assumption. 
                - destruct HWF0. destruct H. assumption. 
                - destruct HWF1. destruct H. assumption.
                - rewrite <- HCAB. assumption. } 
              split. { unfold p1. unfold p2. 
                rewrite <- Rdiv_plus_distr. rewrite Rplus_assoc.
                rewrite <- Rplus_comm with (r2:= B).
                rewrite <- Rplus_assoc. 
                rewrite <- Rmult_plus_distr_r. 
                rewrite Hp0_case1. 
                repeat rewrite Rmult_1_l.
                rewrite <- HCAB. apply Rinv_r; try assumption. }
              pose (p0':= ((C*p01)/(p01*A+ 1*B))%R).
              pose (p1':= (C/(p01*A+ 1*B))%R).
              pose (p2':= ((C*p02)/(p02*A))%R).
              assert (Hneq0: (p01*A+ 1*B)%R <> 0%R). { 
                symmetry. apply Rlt_not_eq. 
                apply R_inte_help with (C:= C).
                * apply R_ge0_iff. split; try assumption. unfold C. 
                destruct HWF. destruct H. assumption.
                * apply Rdiv_num_le_den; try assumption.
                  + destruct HWF0. assumption.
                  + destruct HWF1. assumption.
                  + destruct Hp01. split; try apply Rlt_le; try assumption. 
                  + split; [apply Rlt_0_1| apply Rle_refl]. }
              assert (Hneq1: ((p02*A)%R <> 0)). { 
                symmetry. apply Rlt_not_eq. destruct Hp02. 
                apply Rmult_lt_0_compat; try assumption.
                apply R_ge0_iff. split; try assumption. 
                destruct HWF0. destruct H3. assumption. } 
              assert (Hp0'_gt0: 0 <= p0'). { 
                unfold p0'. destruct Hp01. 
                destruct HWF0. destruct H3. 
                destruct HWF1. destruct H6. 
                destruct HWF. destruct H9. 
                apply Rdiv_all_pos; try assumption; apply Rlt_le; try assumption. 
                apply Rlt_0_1. }
              assert (Hp1'_gt0: 0 <= p1'). { 
                unfold p1'. destruct Hp01. 
                destruct HWF0. destruct H3. 
                destruct HWF1. destruct H6. 
                destruct HWF. destruct H9. 
                unfold Rdiv. apply Rmult_le_pos; try assumption.
                apply Rlt_le. apply Rinv_0_lt_compat; try assumption. 
                  apply Rplus_lt_le_0_compat; try assumption. 
                  + apply Rmult_lt_0_compat; try assumption. apply R_ge0_iff. split; try assumption.
                  + rewrite Rmult_1_l. try assumption. }
              assert (Hp2'_gt0: 0 <= p2'). { 
                unfold p2'. destruct Hp02. 
                destruct HWF0. destruct H3. 
                destruct HWF1. destruct H6. 
                destruct HWF. destruct H9.
                unfold Rdiv. apply Rmult_le_pos; try assumption.
                - apply Rmult_le_pos; try assumption. apply Rlt_le; try assumption.
                - apply Rlt_le. apply Rinv_0_lt_compat; try assumption.
                  apply Rmult_lt_0_compat; try assumption. apply R_ge0_iff. split; try assumption. }
              assert (HPD1': partial_dst_Prop dom (p0'*(mu pd01)+p1'*(mu x))). {
                apply PD_linear; try assumption.
                - destruct Heq1. simpl in Hdom1. simpl in *. 
                apply dom_equiv_trans with (l1:= dom0); try assumption. 
                - destruct Heq1. simpl in *. 
                apply dom_equiv_trans with (l1:= CoreDef.dom pd1); try assumption. } 
              pose (pd1':= Build_partial_dist dom (p0'*(mu pd01)+p1'*(mu x)) HPD1').
              assert (HPD2': partial_dst_Prop dom (p2'*(mu pd02))). {
                apply PD_mult_coef; try assumption. 
                simpl in *. 
                assert (Hdom_trans: (CoreDef.dom pd02 == dom)%domain). {
                  apply dom_equiv_trans with (l1:= dom0); try assumption. }
                apply dom_equiv_sym in Hdom_trans.
                apply Peq_dom_PD_Prop with (mu:= (mu pd02)) in Hdom_trans; try assumption.
                destruct pd02. assumption. } 
              pose (pd2':= Build_partial_dist dom (p2'*(mu pd02)) HPD2').
              exists pd1', pd2'. 
              assert (Hv01: Valid_dist (p0' * mu pd01 + p1' * mu x)). { 
                try apply Valid_linear_under_eq_prob; try assumption.
                rewrite Hsum01. rewrite Hsumx. split.
                - destruct HWF0. destruct H. 
                destruct HWF1. destruct H4. 
                rewrite <- Rplus_0_l at 1. 
                apply Rplus_le_compat; apply Rmult_le_pos; try assumption.
                - unfold p0'. unfold p1'. unfold Rdiv.
                repeat rewrite Rmult_assoc. rewrite <- Rmult_plus_distr_l. 
                repeat rewrite Rmult_comm with (r1:= / (p01 * A + 1 * B)).
                repeat rewrite <- Rmult_assoc. rewrite <- Rmult_plus_distr_r.
                fold A. fold B. rewrite <- Rdiv_def. rewrite <- Rmult_1_l with (r:= B) at 1. 
                rewrite Rdiv_diag; try assumption.
                rewrite Rmult_1_r. destruct HWF. destruct H. assumption. }
              assert (Hp2'_A: (p2' * A = C)%R). {
                unfold p2'. unfold Rdiv. rewrite Rmult_comm. rewrite <- Rmult_assoc. 
                rewrite Rmult_comm with (r1:= A). rewrite Rmult_assoc with (r1:= C).
                rewrite Rmult_assoc. rewrite Rinv_r; try assumption.
                rewrite Rmult_1_r. reflexivity. }
              assert (Hv23: Valid_dist (p2' * mu pd02)). { 
                try apply Valid_mult_under_eq_prob; try assumption.
                rewrite dst_sum_prob_coef_mult. rewrite Hsum02.
                simpl. 
                replace ((p0 + sum_probs mu0')%R) with A by reflexivity.
                rewrite Hp2'_A. destruct HWF. assumption. }
              split; try assumption. split; try assumption.
              split. { simpl. apply dom_equiv_refl. }
              split. { simpl. apply dom_equiv_refl. }
              split. { 
                pose (pd01':= Build_partial_dist (CoreDef.dom pd01) (p0' * (mu pd01)) (pd_mult_preserve_PD pd01 p0')).
                pose (pd11':= Build_partial_dist (CoreDef.dom x) (p1' * (mu x)) (pd_mult_preserve_PD x p1')). 
                apply IHphi1 with (pd0:= pd01') (pd1:= pd11'); try assumption. 
                - inversion HEX; subst. assumption. 
                - simpl. apply Valid_add_decom in Hv01. destruct Hv01. assumption.
                - simpl. apply dom_equiv_trans with (l1:= dom0); try assumption.
                - apply sem_mult_cofe; try assumption; try apply Rlt_le; try assumption. 
                  apply Valid_add_decom in Hv01. destruct Hv01. destruct H. assumption. 
                - simpl. apply Valid_add_decom in Hv01. destruct Hv01. assumption.
                - simpl. destruct Heq1. apply dom_equiv_trans with (l1:= CoreDef.dom pd1); try assumption.
                - simpl. apply dst_equiv_refl.
                - simpl. rewrite dst_sum_prob_decom. reflexivity.
                - apply sem_mult_cofe; try assumption; try apply Rlt_le; try assumption. 
                  apply Valid_add_decom in Hv01. destruct Hv01. destruct H0. assumption. }  
              split. {
                pose (pd02':= Build_partial_dist (CoreDef.dom pd02) (p2' * (mu pd02)) (pd_mult_preserve_PD pd02 p2')).
                apply IHphi2 with (pd0:= pd02') (pd1:= pd_emp dom); try assumption. 
                - inversion HEX; subst. assumption. 
                - simpl. apply dom_equiv_trans with (l1:= dom0); try assumption.
                - apply sem_mult_cofe; try assumption; try apply Rlt_le; try assumption. 
                  destruct Hv23. assumption. 
                - simpl. apply Valid_dist_nil.
                - simpl. apply dom_equiv_refl.
                - simpl. rewrite dst_add_0_r. apply dst_equiv_refl.
                - simpl. rewrite Rplus_0_r. reflexivity.
                - apply emp_dst_satisfies_phi; try assumption. 
                apply satisfy_implies_dom_sub in Hphi02; try assumption.
                apply dom_subset_eq_compat_left with (X:= (CoreDef.dom pd02)); try assumption.
                simpl in *. 
                apply dom_equiv_trans with (l1:= dom0); try assumption.
                } 
              simpl. repeat rewrite dst_sum_prob_decom.
              repeat rewrite dst_sum_prob_coef_mult.
              rewrite Hsum01. rewrite Hsum02. rewrite Hsumx.
              repeat fold A. repeat fold B. repeat fold C.
              split. { unfold p0'. unfold p1'. unfold Rdiv.
                repeat rewrite Rmult_assoc. rewrite <- Rmult_plus_distr_l. 
                repeat rewrite Rmult_comm with (r1:= / (p01 * A + 1 * B)).
                repeat rewrite <- Rmult_assoc. rewrite <- Rmult_plus_distr_r.
                rewrite <- Rmult_1_l with (r:= B) at 1.
                rewrite Rinv_r; try apply Rmult_1_r; try assumption. }
              split; try assumption.
              repeat rewrite dst_mult_plus_distr_r_eq.
              repeat rewrite dst_mult_assoc_eq.
              apply dst_equiv_trans with (mu1:= p1 * p0' * mu pd01 + p2 * p2' * mu pd02 + (p1 * p1' * mu x)); try assumption.
              +++ apply dst_equiv_trans with (mu1:= ((s0, p0) :: mu0') + mu pd1); try assumption.
                  assert (H01: (p1 * p0' = p01)%R). { 
                    unfold p0'. rewrite Rmult_comm. rewrite Rmult_comm with (r1:= C).
                    rewrite <- Rmult_1_r with (r:= p01) at 3.
                    unfold Rdiv. rewrite Rmult_assoc. 
                    rewrite Rmult_assoc with (r1:= p01).
                    apply Rmult_eq_compat_l.
                    unfold p1. unfold Rdiv.
                    rewrite <- Rmult_assoc with (r3:= /C). 
                    rewrite <- Rmult_1_l with (r:= B) at 2.
                    rewrite <- Rinv_l_sym with (r:= (p01 * A + 1 * B)%R).
                    - rewrite Rmult_1_l. apply Rinv_r. assumption.
                    - assumption. }
                  rewrite H01. 
                  assert (H02: (p2 * p2' = p02)%R). { 
                    unfold p2'. rewrite Rmult_comm. rewrite Rmult_comm with (r1:= C).
                    rewrite <- Rmult_1_r with (r:= p02) at 3.
                    unfold Rdiv. rewrite Rmult_assoc. 
                    rewrite Rmult_assoc with (r1:= p02).
                    apply Rmult_eq_compat_l.
                    unfold p2. unfold Rdiv.
                    rewrite <- Rmult_assoc with (r3:= /C). 
                    rewrite <- Rinv_l_sym with (r:= (p02 * A)%R).
                    - rewrite Rmult_1_l. apply Rinv_r. assumption.
                    - assumption. }
                  rewrite H02. 
                  assert (H11: (p1 * p1' = 1)%R). { 
                    unfold p1'. unfold p1.
                    rewrite <- Rmult_1_l with (r:= B) at 1.
                    unfold Rdiv. rewrite Rmult_assoc.
                    rewrite <- Rmult_assoc with (r1:= /C).
                    rewrite <- Rinv_l_sym with (r:= (C)%R); try assumption.
                    repeat rewrite Rmult_1_l. apply Rinv_r.
                    rewrite <- Rmult_1_l with (r:= B).
                    assumption. }
                  rewrite H11. rewrite dst_mult_1_l.
                  apply dst_add_preserves_equiv; try assumption. 
                  destruct Heq1. apply dst_equiv_sym; try assumption.
              +++ repeat rewrite <- dst_add_assoc_eq. apply dst_add_inj_l. apply dst_add_comm.
            * destruct Hsem1_case3. (*mu1 only satisfies the right-hand half formula phi2*)
              destruct H as [Hvalidx H]. destruct H as [Heq1 H].
              destruct H as [Hsub1 H]. 
              destruct H as [Hphi1x Hsumx]. 
              pose (p1:= (p01*A)/C). pose (p2:= (p02*A + B)/C).
              destruct pd0 as [dom0 mu0 HPD0]. destruct mu0 as [|(s0,p0) mu0'].
            ++ simpl. right. right. exists x. split; try assumption. 
              split. { destruct Heq1. split; simpl in *. 
                - apply dom_equiv_trans with (l1:= CoreDef.dom pd1); assumption.
                - apply dst_equiv_trans with (mu1:=mu pd1); try assumption. 
                  apply dst_equiv_sym; try assumption. }
              split. { 
                simpl in Hdom1. 
                apply dom_subset_eq_compat_left with (X:= CoreDef.dom pd1); assumption. }
              split; try assumption. 
              simpl in *. rewrite Hsum_eq. rewrite Rplus_0_l. assumption. 
            ++ assert (HA: A <> 0). { 
                  unfold A. simpl. symmetry. apply Rlt_not_eq.
                  apply Valid_dist_conj in HWF0. destruct HWF0. 
                  destruct H0. destruct H0. destruct H. destruct H5. destruct H5.
                  apply Rplus_lt_le_0_compat; try assumption. }
              left. exists p1, p2.
              split. { unfold p1. rewrite HCAB.
                apply Rdiv_pA_in_01; try assumption. 
                - destruct HWF0. destruct H. assumption. 
                - destruct HWF1. destruct H. assumption.
                - rewrite <- HCAB. assumption. } 
              split. { unfold p2. rewrite HCAB.
                apply Rdiv_num_lt_den2; try assumption. 
                - destruct HWF0. destruct H. simpl in H. 
                unfold A. simpl in *. apply R_ge0_iff; split; try assumption.
                - destruct HWF1. destruct H. assumption.
                - rewrite <- HCAB. assumption. }
              split. { unfold p1. unfold p2. 
                rewrite <- Rdiv_plus_distr. rewrite <- Rplus_assoc.  
                rewrite <- Rmult_plus_distr_r. 
                rewrite Hp0_case1. 
                repeat rewrite Rmult_1_l.
                rewrite <- HCAB. apply Rinv_r; try assumption. }
              pose (p2':= ((C*p02)/(p02*A+ 1*B))%R).
              pose (p3':= (C/(p02*A+ 1*B))%R).
              pose (p0':= ((C*p01)/(p01*A))%R).
              assert (Hneq0: (p02*A+ 1*B)%R <> 0%R). { 
                symmetry. apply Rlt_not_eq. 
                apply R_inte_help with (C:= C).
                * apply R_ge0_iff. split; try assumption. 
                  unfold C. destruct HWF. destruct H. assumption.
                * apply Rdiv_num_le_den; try assumption.
                  + destruct HWF0. assumption.
                  + destruct HWF1. assumption.
                  + destruct Hp02. split; try apply Rlt_le; assumption.
                  + split; [apply Rlt_0_1| apply Rle_refl]. }
              assert (Hneq1: (p01*A)%R <> 0%R). { 
                symmetry. apply Rlt_not_eq. destruct Hp01. 
                apply Rmult_lt_0_compat; try assumption.
                apply R_ge0_iff. split; try assumption. 
                destruct HWF0. destruct H3. assumption. } 
              assert (Hp0'_gt0: 0 <= p0'). { 
                unfold p0'. destruct Hp01. 
                destruct HWF0. destruct H3. 
                destruct HWF1. destruct H6. 
                destruct HWF. destruct H9. 
                unfold Rdiv. apply Rmult_le_pos; try assumption.
                - apply Rmult_le_pos; try assumption. apply Rlt_le; try assumption.
                - apply Rlt_le. apply Rinv_0_lt_compat; try assumption.
                  apply Rmult_lt_0_compat; try assumption. 
                  apply R_ge0_iff. split; try assumption. }        
              assert (Hp2'_gt0: 0 <= p2'). { 
                unfold p2'. destruct Hp02. 
                destruct HWF0. destruct H3. 
                destruct HWF1. destruct H6. 
                destruct HWF. destruct H9.
                apply Rdiv_all_pos; try assumption; apply Rlt_le; try assumption. 
                apply Rlt_0_1. }
              assert (Hp3'_gt0: 0 <= p3'). { 
                unfold p3'. destruct Hp02. 
                destruct HWF0. destruct H3. 
                destruct HWF1. destruct H6. 
                destruct HWF. destruct H9.
                unfold Rdiv. apply Rmult_le_pos; try assumption.
                apply Rlt_le. apply Rinv_0_lt_compat; try assumption. 
                  apply Rplus_lt_le_0_compat; try assumption. 
                  + apply Rmult_lt_0_compat; try assumption. 
                  apply R_ge0_iff. split; try assumption.
                  + rewrite Rmult_1_l. try assumption. }
              assert (HPD1': partial_dst_Prop dom (p0'*(mu pd01))). {
                apply PD_mult_coef; try assumption. 
                simpl in *. 
                assert (Hdom_trans: (CoreDef.dom pd01 == dom)%domain). {
                  apply dom_equiv_trans with (l1:= dom0); try assumption. }
                apply dom_equiv_sym in Hdom_trans.
                apply Peq_dom_PD_Prop with (mu:= (mu pd01)) in Hdom_trans; try assumption.
                destruct pd01. assumption. } 
              pose (pd1':= Build_partial_dist dom (p0'*(mu pd01)) HPD1').
              assert (HPD2': partial_dst_Prop dom (p2'*(mu pd02)+p3'*(mu x))). {
                apply PD_linear; try assumption.
                - destruct Heq1. simpl in Hdom1. simpl in *. 
                apply dom_equiv_trans with (l1:= dom0); try assumption. 
                - destruct Heq1. simpl in *. 
                apply dom_equiv_trans with (l1:= CoreDef.dom pd1); try assumption. } 
              pose (pd2':= Build_partial_dist dom (p2'*(mu pd02)+p3'*(mu x)) HPD2').
              exists pd1', pd2'. 
              assert (Hp0'_A: (p0' * A = C)%R). {
                unfold p0'. unfold Rdiv. rewrite Rmult_comm. rewrite <- Rmult_assoc. 
                rewrite Rmult_comm with (r1:= A). rewrite Rmult_assoc with (r1:= C).
                rewrite Rmult_assoc. rewrite Rinv_r; try assumption.
                rewrite Rmult_1_r. reflexivity. }
              assert (Hv01: Valid_dist (p0' * mu pd01)). { 
                try apply Valid_mult_under_eq_prob; try assumption.
                rewrite dst_sum_prob_coef_mult. rewrite Hsum01. simpl. 
                replace ((p0 + sum_probs mu0')%R) with A by reflexivity.
                rewrite Hp0'_A. destruct HWF. assumption. }
              assert (Hv23: Valid_dist (p2' * mu pd02 + p3' * mu x)). { 
                try apply Valid_linear_under_eq_prob; try assumption.
                rewrite Hsum02. rewrite Hsumx. split.
                - destruct HWF0. destruct H. destruct HWF1. destruct H4. 
                rewrite <- Rplus_0_l at 1. apply Rplus_le_compat; apply Rmult_le_pos; try assumption.
                - unfold p2'. unfold p3'. unfold Rdiv.
                repeat rewrite Rmult_assoc. rewrite <- Rmult_plus_distr_l. 
                repeat rewrite Rmult_comm with (r1:= / (p02 * A + 1 * B)).
                repeat rewrite <- Rmult_assoc. rewrite <- Rmult_plus_distr_r.
                fold A. fold B. rewrite <- Rdiv_def. rewrite <- Rmult_1_l with (r:= B) at 1. 
                rewrite Rdiv_diag; try assumption.
                rewrite Rmult_1_r. destruct HWF. destruct H. assumption. }
              split; try assumption. 
              split; try assumption.
              split. { simpl. apply dom_equiv_refl. }
              split. { simpl. apply dom_equiv_refl. }
              split. {
                pose (pd01':= Build_partial_dist (CoreDef.dom pd01) (p0' * (mu pd01)) (pd_mult_preserve_PD pd01 p0')).
                apply IHphi1 with (pd0:= pd01') (pd1:= pd_emp dom); try assumption. 
                - inversion HEX; subst. assumption. 
                - simpl. apply dom_equiv_trans with (l1:= dom0); try assumption.
                - apply sem_mult_cofe; try assumption; try apply Rlt_le; try assumption. 
                  destruct Hv01. assumption. 
                - simpl. apply Valid_dist_nil.
                - simpl. apply dom_equiv_refl.
                - simpl. rewrite dst_add_0_r. apply dst_equiv_refl.
                - simpl. rewrite Rplus_0_r. reflexivity.
                - apply emp_dst_satisfies_phi; try assumption.
                apply satisfy_implies_dom_sub in Hphi01; try assumption.
                apply dom_subset_eq_compat_left with (X:= (CoreDef.dom pd01)); try assumption.
                simpl in *. 
                apply dom_equiv_trans with (l1:= dom0); try assumption.
                }
              split. { 
                pose (pd02':= Build_partial_dist (CoreDef.dom pd02) (p2' * (mu pd02)) (pd_mult_preserve_PD pd02 p2')).
                pose (pd12':= Build_partial_dist (CoreDef.dom x) (p3' * (mu x)) (pd_mult_preserve_PD x p3')). 
                apply IHphi2 with (pd0:= pd02') (pd1:= pd12'); try assumption. 
                - inversion HEX; subst. assumption. 
                - simpl. apply Valid_add_decom in Hv23. destruct Hv23. assumption.
                - simpl. apply dom_equiv_trans with (l1:= dom0); try assumption.
                - apply sem_mult_cofe; try assumption; try apply Rlt_le; try assumption. 
                  apply Valid_add_decom in Hv23. destruct Hv23. destruct H. assumption. 
                - simpl. apply Valid_add_decom in Hv23. destruct Hv23. assumption.
                - simpl. destruct Heq1. apply dom_equiv_trans with (l1:= CoreDef.dom pd1); try assumption.
                - simpl. apply dst_equiv_refl.
                - simpl. rewrite dst_sum_prob_decom. reflexivity.
                - apply sem_mult_cofe; try assumption; try apply Rlt_le; try assumption. 
                  apply Valid_add_decom in Hv23. destruct Hv23. destruct H0. assumption. }  
              simpl. repeat rewrite dst_sum_prob_decom.
              repeat rewrite dst_sum_prob_coef_mult.
              rewrite Hsum01. rewrite Hsum02. rewrite Hsumx.
              repeat fold A. repeat fold B. 
              split. { rewrite Hp0'_A. reflexivity. }
              split. { unfold p2'. unfold p3'. unfold Rdiv.
                      repeat rewrite Rmult_assoc.
                      rewrite <- Rmult_plus_distr_l. 
                      repeat rewrite Rmult_comm with (r1:= / (p02 * A + 1 * B)).
                      repeat rewrite <- Rmult_assoc. rewrite <- Rmult_plus_distr_r.
                      rewrite <- Rmult_1_l with (r:= B) at 1.
                      rewrite Rinv_r; try apply Rmult_1_r; try assumption. }
              repeat rewrite dst_mult_plus_distr_r_eq.
              repeat rewrite dst_mult_assoc_eq.
              apply dst_equiv_trans with (mu1:= p1 * p0' * mu pd01 + p2 * p2' * mu pd02 + (p2 * p3' * mu x)); try assumption.
              +++ apply dst_equiv_trans with (mu1:= ((s0, p0) :: mu0') + mu pd1); try assumption.
                  assert (H01: (p1 * p0' = p01)%R). { 
                    unfold p0'. rewrite Rmult_comm. rewrite Rmult_comm with (r1:= C).
                    rewrite <- Rmult_1_r with (r:= p01) at 3.
                    unfold Rdiv. rewrite Rmult_assoc. 
                    rewrite Rmult_assoc with (r1:= p01).
                    apply Rmult_eq_compat_l.
                    unfold p1. unfold Rdiv.
                    rewrite <- Rmult_assoc with (r3:= /C). 
                    rewrite <- Rinv_l_sym with (r:= (p01 * A)%R).
                    - rewrite Rmult_1_l. apply Rinv_r. assumption.
                    - assumption. }
                  rewrite H01. 
                  assert (H02: (p2 * p2' = p02)%R). { 
                      unfold p2'. rewrite Rmult_comm. rewrite Rmult_comm with (r1:= C).
                      rewrite <- Rmult_1_r with (r:= p02) at 3.
                      unfold Rdiv. rewrite Rmult_assoc. 
                      rewrite Rmult_assoc with (r1:= p02).
                      apply Rmult_eq_compat_l.
                      unfold p2. unfold Rdiv.
                      rewrite <- Rmult_assoc with (r3:= /C). 
                      rewrite <- Rmult_1_l with (r:= B) at 2.
                      rewrite <- Rinv_l_sym with (r:= (p02 * A + 1 * B)%R).
                      - rewrite Rmult_1_l. apply Rinv_r. assumption.
                      - assumption. }
                      rewrite H02. 
                    assert (H11: (p2 * p3' = 1)%R). { 
                        unfold p3'. unfold p2.
                        rewrite <- Rmult_1_l with (r:= B) at 1.
                        unfold Rdiv. rewrite Rmult_assoc.
                        rewrite <- Rmult_assoc with (r1:= /C).
                        rewrite <- Rinv_l_sym with (r:= (C)%R); try assumption.
                        repeat rewrite Rmult_1_l. apply Rinv_r.
                        rewrite <- Rmult_1_l with (r:= B).
                        assumption. }
                        rewrite H11. rewrite dst_mult_1_l.
                      apply dst_add_preserves_equiv; try assumption. 
                      destruct Heq1. apply dst_equiv_sym; try assumption.
              +++ rewrite dst_add_assoc_eq. apply dst_equiv_refl. 
        }
        { destruct Hsem0 as [Hsem0_case2|Hsem0_case3]. 
          - destruct Hsem0_case2. destruct H as [Hvalidx H]. 
            destruct H as [Heq0 H]. 
            destruct H as [Hsub2 H]. 
            destruct H as [Hphi1x Hsumx].   
            destruct Hsem1 as [Hsem1_case1 | Hsem1]. (*There are three situations for mu1*)
            { destruct Hsem1_case1 as [p11 H]. destruct H as [p12 H].
              destruct H as [Hp11 H]. destruct H as [Hp12 H].
              destruct H as [Hp1_case1 H].   
              destruct H as [pd11 H]. destruct H as [pd12 H]. 
              destruct H as [Hvalid11 H]. destruct H as [Hvalid12 H].
              destruct H as [Hdom11 H]. destruct H as [Hdom12 H].
              destruct H as [Hphi11 H]. destruct H as [Hphi12 H].
              destruct H as [Hsum11 H]. destruct H as [Hsum12 Hmu1].
              simpl in *.
              pose (p1:= (A + p11*B)/C). pose (p2:= (p12*B)/C).
              destruct pd1 as [dom1 mu1 HPD1]. destruct mu1 as [|(s1,sp1) mu1'].
              ++ simpl. right. left. 
                exists x. split; try assumption. 
                split. { destruct Heq0. split; simpl in *. 
                  - apply dom_equiv_trans with (l1:= CoreDef.dom pd0); assumption.
                  - apply dst_equiv_trans with (mu1:=mu pd0); try assumption. 
                    rewrite dst_add_0_r in Hmu_eq.
                    apply dst_equiv_sym; try assumption. }
                split. { 
                  simpl in Hdom1. 
                  apply dom_subset_eq_compat_left with (X:= CoreDef.dom pd0); assumption. }
                split; try assumption. 
                simpl in *. rewrite Hsum_eq. rewrite Rplus_0_r. assumption. 
              ++ assert (HB: B <> 0). { 
                    unfold B. simpl. symmetry. apply Rlt_not_eq.
                    apply Valid_dist_conj in HWF1. destruct HWF1. destruct H. 
                    destruct H3. destruct H3.
                    destruct H0. destruct H0. 
                    apply positive_sum_ge_0 in H6. 
                    apply Rplus_lt_le_0_compat; try assumption. } 
                simpl. left. exists p1, p2.
                split. { unfold p1. rewrite HCAB. 
                        rewrite Rplus_comm. rewrite <- Rplus_comm with (r1:= B).
                        apply Rdiv_num_lt_den2; try assumption.
                        - destruct HWF1. destruct H. simpl in H. 
                          unfold B. simpl in *. apply R_ge0_iff; split; try assumption.
                        - destruct HWF0. destruct H. assumption.
                        - rewrite Rplus_comm. rewrite <- HCAB. assumption. }
                split. { unfold p2. rewrite HCAB. rewrite Rplus_comm. 
                        apply Rdiv_pA_in_01; try assumption. 
                        - destruct HWF1. destruct H. assumption. 
                        - destruct HWF0. destruct H. assumption.
                        - rewrite Rplus_comm. rewrite <- HCAB. assumption. }
                split. { unfold p1. unfold p2. 
                        rewrite <- Rdiv_plus_distr. rewrite Rplus_assoc.
                        rewrite <- Rplus_comm with (r2:= A).
                        rewrite <- Rmult_plus_distr_r. 
                        rewrite Hp1_case1. 
                        repeat rewrite Rmult_1_l. rewrite Rplus_comm.
                        rewrite <- HCAB. apply Rinv_r; try assumption. } 
                pose (p0':= ((C)/(1*A+ p11*B))%R).
                pose (p1':= (C*p11/(1*A+ p11*B))%R).
                pose (p3':= ((C*p12)/(p12*B))%R).
                assert (Hneq0: (1*A+ p11*B)%R <> 0%R). { 
                  symmetry. apply Rlt_not_eq. 
                  apply R_inte_help with (C:= C).
                  * apply R_ge0_iff. split; try assumption. unfold C. 
                    destruct HWF. destruct H. assumption.
                  * apply Rdiv_num_le_den; try assumption.
                    + destruct HWF0. assumption.
                    + destruct HWF1. assumption.
                    + split; [apply Rlt_0_1| apply Rle_refl].
                    + destruct Hp11. split; try apply Rlt_le; assumption. }
                assert (Hneq1: (p12* B)%R <> 0%R). { 
                  symmetry. apply Rlt_not_eq. destruct Hp12. 
                  apply Rmult_lt_0_compat; try assumption.
                  apply R_ge0_iff. split; try assumption. 
                  destruct HWF1. destruct H3. assumption. } 
                assert (Hp0'_gt0: 0 <= p0'). { 
                  unfold p0'. destruct Hp11. 
                  destruct HWF0. destruct H3. 
                  destruct HWF1. destruct H6. 
                  destruct HWF. destruct H9. 
                  unfold Rdiv. apply Rmult_le_pos; try assumption.
                  apply Rlt_le. apply Rinv_0_lt_compat; try assumption.
                  rewrite Rplus_comm. apply Rplus_lt_le_0_compat; try assumption. 
                    + apply Rmult_lt_0_compat; try assumption. apply R_ge0_iff. 
                    split; try assumption.
                    + rewrite Rmult_1_l. try assumption. }
                assert (Hp1'_gt0: 0 <= p1'). { 
                  unfold p1'. destruct Hp11. 
                  destruct HWF0. destruct H3. 
                  destruct HWF1. destruct H6. 
                  destruct HWF. destruct H9. 
                  unfold Rdiv. apply Rmult_le_pos; try assumption.
                  - apply Rmult_le_pos; try assumption. apply Rlt_le; try assumption.
                  - apply Rlt_le. apply Rinv_0_lt_compat; try assumption.
                    apply Rplus_le_lt_0_compat; try assumption.
                    + rewrite Rmult_1_l. assumption.
                    + apply Rmult_lt_0_compat; try assumption. apply R_ge0_iff. 
                    split; try assumption. }
                assert (Hp3'_gt0: 0 <= p3'). { 
                  unfold p3'. destruct Hp12.
                  destruct HWF0. destruct H3. 
                  destruct HWF1. destruct H6. 
                  destruct HWF. destruct H9. 
                  unfold Rdiv. apply Rmult_le_pos; try assumption.
                  - apply Rmult_le_pos; try assumption. apply Rlt_le; try assumption.
                  - apply Rlt_le. apply Rinv_0_lt_compat; try assumption.
                    apply Rmult_lt_0_compat; try assumption. 
                    apply R_ge0_iff. split; try assumption. } 
                assert (HPD1': partial_dst_Prop dom (p0'*(mu x)+p1'*(mu pd11))). {
                  apply PD_linear; try assumption.
                  - destruct Heq0. simpl in *. 
                    apply dom_equiv_trans with (l1:= CoreDef.dom pd0); try assumption. 
                  - destruct Heq0. simpl in *. 
                    apply dom_equiv_trans with (l1:= dom1); try assumption. } 
                pose (pd1':= Build_partial_dist dom (p0'*(mu x)+p1'*(mu pd11)) HPD1').
                assert (HPD2': partial_dst_Prop dom (p3'*(mu pd12))). {
                  apply PD_mult_coef; try assumption. 
                  simpl in *. 
                  assert (Hdom_trans: (CoreDef.dom pd12 == dom)%domain). {
                    simpl in *.
                    apply dom_equiv_trans with (l1:=dom1); try assumption. }
                  apply dom_equiv_sym in Hdom_trans.
                  apply Peq_dom_PD_Prop with (mu:= (mu pd12)) in Hdom_trans; try assumption.
                  destruct pd12. assumption. } 
                pose (pd2':= Build_partial_dist dom (p3'*(mu pd12)) HPD2').
                exists pd1', pd2'. 
                assert (Hv01: Valid_dist (p0' * mu x + p1' * mu pd11)). { 
                  try apply Valid_linear_under_eq_prob; try assumption.
                  rewrite Hsum11. rewrite Hsumx. split.
                  - destruct HWF0. destruct H. destruct HWF1. destruct H5. destruct H4.
                  rewrite <- Rplus_0_l at 1. apply Rplus_le_compat; apply Rmult_le_pos; try assumption.
                  - unfold p0'. unfold p1'. unfold Rdiv.
                  repeat rewrite Rmult_assoc. rewrite <- Rmult_plus_distr_l. 
                  repeat rewrite Rmult_comm with (r1:= / (1 * A + p11 * B)).
                  repeat rewrite <- Rmult_assoc. rewrite <- Rmult_plus_distr_r.
                  fold A. fold B. rewrite <- Rdiv_def. rewrite <- Rmult_1_l with (r:= A) at 1. 
                  rewrite Rdiv_diag; try assumption.
                  rewrite Rmult_1_r. destruct HWF. destruct H. assumption. }
                assert (Hp3'_B: (p3' * B = C)%R). {
                  unfold p3'. rewrite Rmult_comm. 
                  unfold Rdiv. 
                  rewrite <- Rmult_assoc. rewrite Rmult_comm with (r1:= B).
                  rewrite Rmult_assoc with (r1:= C).
                  rewrite Rmult_assoc. 
                  rewrite Rinv_r; try assumption.
                  rewrite Rmult_1_r. reflexivity. }
                assert (Hv23: Valid_dist (p3' * mu pd12)). { 
                  try apply Valid_mult_under_eq_prob; try assumption.
                  rewrite dst_sum_prob_coef_mult. fold B in Hsum12. rewrite Hsum12. 
                  rewrite Hp3'_B. destruct HWF. assumption. }
                split; try assumption. split; try assumption.
                split. { simpl. apply dom_equiv_refl. }
                split. { simpl. apply dom_equiv_refl. }
                split. { 
                  pose (pd01':= Build_partial_dist (CoreDef.dom x) (p0' * (mu x)) (pd_mult_preserve_PD x p0')). 
                  pose (pd11':= Build_partial_dist (CoreDef.dom pd11) (p1' * (mu pd11)) (pd_mult_preserve_PD pd11 p1')).
                  apply IHphi1 with (pd0:= pd01') (pd1:= pd11'); try assumption. 
                  - inversion HEX; subst. assumption. 
                  - simpl. apply Valid_add_decom in Hv01. destruct Hv01. assumption.
                  - simpl. destruct Heq0. apply dom_equiv_trans with (l1:= CoreDef.dom pd0); try assumption.
                  - apply sem_mult_cofe; try assumption; try apply Rlt_le; try assumption. 
                    apply Valid_add_decom in Hv01. destruct Hv01. destruct H. assumption. 
                  - simpl. apply Valid_add_decom in Hv01. destruct Hv01. assumption.
                  - simpl in *. apply dom_equiv_trans with (l1:= dom1); try assumption.
                  - simpl. apply dst_equiv_refl.
                  - simpl. rewrite dst_sum_prob_decom. reflexivity.
                  - apply sem_mult_cofe; try assumption; try apply Rlt_le; try assumption. 
                    apply Valid_add_decom in Hv01. destruct Hv01. destruct H0. assumption. }  
                split. {
                  pose (pd01':= Build_partial_dist (CoreDef.dom pd12) (p3' * (mu pd12)) (pd_mult_preserve_PD pd12 p3')).
                  apply IHphi2 with (pd0:= pd01') (pd1:= pd_emp dom); try assumption. 
                  - inversion HEX; subst. assumption. 
                  - simpl in *. apply dom_equiv_trans with (l1:= dom1); try assumption.
                  - apply sem_mult_cofe; try assumption; try apply Rlt_le; try assumption. 
                    destruct Hv23. assumption. 
                  - simpl. apply Valid_dist_nil.
                  - simpl. apply dom_equiv_refl.
                  - simpl. rewrite dst_add_0_r. apply dst_equiv_refl.
                  - simpl. rewrite Rplus_0_r. reflexivity.
                  - apply emp_dst_satisfies_phi; try assumption. simpl in *.
                    apply satisfy_implies_dom_sub in Hphi12; try assumption.
                    apply dom_subset_eq_compat_left with (X:= (CoreDef.dom pd12)); try assumption.
                    simpl in *. 
                    apply dom_equiv_trans with (l1:= dom1); try assumption. }
                simpl. repeat rewrite dst_sum_prob_decom.
                repeat rewrite dst_sum_prob_coef_mult.
                rewrite Hsum11. rewrite Hsum12. rewrite Hsumx.
                repeat fold A. repeat fold B. repeat fold C.
                split. { unfold p0'. unfold p1'. unfold Rdiv.
                  repeat rewrite Rmult_assoc. rewrite <- Rmult_plus_distr_l. 
                  repeat rewrite Rmult_comm with (r1:= / (1 * A + p11 * B)).
                  repeat rewrite <- Rmult_assoc. rewrite <- Rmult_plus_distr_r.
                  rewrite <- Rmult_1_l with (r:= A) at 1.
                  rewrite Rinv_r; try apply Rmult_1_r; try assumption. }
                split; try assumption.
                repeat rewrite dst_mult_plus_distr_r_eq.
                repeat rewrite dst_mult_assoc_eq.
                apply dst_equiv_trans with (mu1:= p1 * p0' * mu x + (p1 * p1' * mu pd11 + p2 * p3' * mu pd12)); try assumption.
                +++ apply dst_equiv_trans with (mu1:= mu pd0 + ((s1, sp1) :: mu1')); try assumption.
                  assert (H01: (p1 * p0' = 1)%R). { 
                    unfold p1. unfold p0'.
                    rewrite <- Rmult_1_l with (r:= A) at 1.
                    unfold Rdiv. rewrite Rmult_assoc.
                    rewrite <- Rmult_assoc with (r1:= /C).
                    rewrite <- Rinv_l_sym with (r:= (C)%R); try assumption.
                    repeat rewrite Rmult_1_l. apply Rinv_r.
                    rewrite <- Rmult_1_l with (r:= A).
                    assumption. }
                  rewrite H01. 
                  assert (H02: (p1 * p1' = p11)%R). { 
                    unfold p1'. rewrite Rmult_comm. rewrite Rmult_comm with (r1:= C).
                    rewrite <- Rmult_1_r with (r:= p11) at 3.
                    unfold Rdiv. rewrite Rmult_assoc. 
                    rewrite Rmult_assoc with (r1:= p11).
                    apply Rmult_eq_compat_l.
                    unfold p1. unfold Rdiv.
                    rewrite <- Rmult_assoc with (r3:= /C).
                    rewrite <- Rmult_1_l with (r:= A) at 2. 
                    rewrite <- Rinv_l_sym with (r:= ((1 * A + p11 * B))%R).
                    - rewrite Rmult_1_l. apply Rinv_r. assumption.
                    - assumption. }
                  rewrite H02. 
                  assert (H11: (p2 * p3' = p12)%R). { 
                    unfold p3'. rewrite Rmult_comm. rewrite Rmult_comm with (r1:= C).
                    rewrite <- Rmult_1_r with (r:= p12) at 3.
                    unfold Rdiv. rewrite Rmult_assoc. 
                    rewrite Rmult_assoc with (r1:= p12).
                    apply Rmult_eq_compat_l.
                    unfold p2. unfold Rdiv.
                    rewrite <- Rmult_assoc with (r3:= /C).
                    rewrite <- Rinv_l_sym with (r:= (p12 * B)%R).
                    - rewrite Rmult_1_l. apply Rinv_r. assumption.
                    - assumption. }
                  rewrite H11. rewrite dst_mult_1_l.
                  apply dst_add_preserves_equiv; try assumption. 
                  destruct Heq0. apply dst_equiv_sym; try assumption.
                +++ repeat rewrite <- dst_add_assoc_eq. apply dst_add_inj_l. apply dst_equiv_refl.
            }
            destruct Hsem1 as [Hsem1_case2 | Hsem1_case3]. 
            + destruct Hsem1_case2. (*mu1 only satisfies the left half formula phi1*)
              destruct H as [Hvalidx0 H]. destruct H as [Heq1 H].
              destruct H as [Hsub1 H]. 
              destruct H as [Hphi1x0 Hsumx0]. 
              simpl. right. left. 
              assert (HPD': partial_dst_Prop (dom) (mu x + mu x0)). {
                  apply PD_decom. split.
                  - destruct x as [domx mux Hx]; subst. simpl in *. 
                    destruct Heq0. simpl in *.
                    apply Peq_dom_PD_Prop with (dom:= domx); try assumption.
                    apply dom_equiv_sym. 
                    apply dom_equiv_trans with (l1:= CoreDef.dom pd0); assumption.
                  - destruct x0 as [domx0 mux0 Hx0]; subst. simpl in *. 
                    destruct Heq1. simpl in *.
                    apply Peq_dom_PD_Prop with (dom:= domx0); try assumption.
                    apply dom_equiv_sym. apply dom_equiv_trans with (l1:= CoreDef.dom pd1); assumption. }
              pose (pd':= Build_partial_dist (dom) ((mu x + mu x0)%dist_state) HPD').
              exists pd'. simpl.
              assert (Hv: Valid_dist (mu x + mu x0)). {
                rewrite <- dst_mult_1_l with (mu:=mu x). rewrite <- dst_mult_1_l with (mu:= mu x0). 
                apply Valid_linear_under_eq_prob; try assumption; try apply Rle_0_1.
                repeat rewrite Rmult_1_l. rewrite Hsumx. rewrite Hsumx0.
                fold A. fold B. rewrite <- HCAB.
                destruct HWF. assumption. }
              split; try assumption.
              split. { split; simpl; try apply dom_equiv_refl. 
                      simpl in Hmu_eq. apply dst_equiv_sym in Hmu_eq.
                      destruct Heq0. destruct Heq1.  
                      apply dst_equiv_trans with (mu1:= mu pd0 + mu pd1); try assumption.
                      apply dst_add_preserves_equiv; try assumption. }
              split. { apply dom_subset_eq_compat_left with (X:= (CoreDef.dom pd1)); try assumption. }
              split. {
                apply IHphi1 with (pd0:=x) (pd1:=x0); try assumption; try reflexivity; try apply dst_equiv_refl.
                + inversion HEX; subst. assumption. 
                + simpl. destruct Heq0. 
                  apply dom_equiv_trans with (l1:= CoreDef.dom pd0); assumption.
                + simpl. destruct Heq1. 
                  apply dom_equiv_trans with (l1:= CoreDef.dom pd1); assumption.
                + simpl. rewrite dst_sum_prob_decom. reflexivity.  }
              rewrite dst_sum_prob_decom. rewrite Hsumx. rewrite Hsumx0. 
              fold A. fold B. rewrite <- HCAB. try reflexivity.
            + destruct Hsem1_case3. (*Mu1 only satisfies the left half formula phi1*)
              destruct H as [Hvalidx0 H]. destruct H as [Heq1 H].
              destruct H as [Hsub1 H]. 
              destruct H as [Hphi1x0 Hsumx0]. 
              destruct pd0 as [dom0 mu0 HPD0]. destruct mu0 as [|(s0,sp0) mu0'].
              -- simpl. right. right. exists x0. 
                split; try assumption. 
                split. { destruct Heq1. split; simpl in *. 
                        - apply dom_equiv_trans with (l1:= CoreDef.dom pd1); assumption.
                        - apply dst_equiv_sym in Hmu_eq. 
                        apply dst_equiv_trans with (mu1:= mu pd1); try assumption. }
                split. { apply dom_subset_eq_compat_left with (X:= (CoreDef.dom pd1)); try assumption. }
                split; try assumption.
                simpl in *. rewrite Hsum_eq. rewrite Rplus_0_l. assumption.
              -- assert (HA: A<>0). { 
                    unfold A. simpl. symmetry. apply Rlt_not_eq.
                    apply Valid_dist_conj in HWF0. destruct HWF0. destruct H. 
                    destruct H3. destruct H3.
                    destruct H0. destruct H0. apply positive_sum_ge_0 in H6. 
                    apply Rplus_lt_le_0_compat; try assumption. }
                  destruct pd1 as [dom1 mu1 HPD1]. destruct mu1 as [|(s1,sp1) mu1'].
                  ++ simpl. right. left. exists x. 
                    split; try assumption. 
                    split. { destruct Heq0. split; simpl in *. 
                        - apply dom_equiv_trans with (l1:= dom0); assumption.
                        - rewrite dst_add_0_r in Hmu_eq. apply dst_equiv_sym in Hmu_eq. 
                        apply dst_equiv_trans with (mu1:= (s0, sp0) :: mu0'); try assumption. }
                    split. { simpl in *. apply dom_subset_eq_compat_left with (X:= dom0); try assumption. }
                    split; try assumption.
                    simpl in *. rewrite Hsum_eq. rewrite Rplus_0_r. assumption.
                  ++ left. exists (A/C)%R, (B/C)%R.
                    assert (HB: B <> 0). { 
                        unfold B. simpl. symmetry. apply Rlt_not_eq.
                        apply Valid_dist_conj in HWF1. destruct HWF1. destruct H. 
                        destruct H3. destruct H3. destruct H0. 
                        apply positive_sum_ge_0 in H6. 
                        apply Rplus_lt_le_0_compat; try assumption. }
                    split. { rewrite HCAB. destruct HWF0. destruct HWF1. 
                    apply Rfrac_bound_lt1; try assumption. }
                    split. { rewrite HCAB. rewrite Rplus_comm. destruct HWF0. destruct HWF1. 
                    apply Rfrac_bound_lt1; try assumption. }
                    split. { rewrite <- Rdiv_plus_distr. rewrite <- HCAB. unfold Rdiv. apply Rinv_r. assumption. }
                    pose (pd1':= Build_partial_dist (CoreDef.dom x) (C/A * mu x) (pd_mult_preserve_PD x (C/A))).
                    pose (pd2':= Build_partial_dist (CoreDef.dom x0) (C/B * mu x0) (pd_mult_preserve_PD x0 (C/B))).
                    exists pd1', pd2'. simpl.
                    assert (Hv: Valid_dist (C / A * mu x)). {
                      apply Valid_mult_under_eq_prob; try assumption; try apply Rle_0_1.
                      - unfold Rdiv. apply Rlt_le. apply Rmult_lt_0_compat. 
                        + apply R_ge0_iff. split; try assumption.
                        destruct HWF. destruct H. assumption. 
                        + apply Rinv_0_lt_compat; try assumption. 
                          destruct HWF0. destruct H. 
                          apply R_ge0_iff. split; try assumption. 
                      - rewrite dst_sum_prob_coef_mult. rewrite Hsumx. 
                        fold A. unfold Rdiv. rewrite Rmult_assoc. 
                        rewrite <- Rinv_l_sym with (r:= A); try assumption.
                        rewrite Rmult_1_r. destruct HWF. assumption. }
                    assert (Hv1: Valid_dist (C / B * mu x0)). {
                      apply Valid_mult_under_eq_prob; try assumption; try apply Rle_0_1.
                      - unfold Rdiv. apply Rlt_le. apply Rmult_lt_0_compat. 
                        + apply R_ge0_iff. split; try assumption.
                        destruct HWF. destruct H. assumption. 
                        + apply Rinv_0_lt_compat; try assumption. 
                          destruct HWF1. destruct H. 
                          apply R_ge0_iff. split; try assumption.
                      - rewrite dst_sum_prob_coef_mult. simpl in *. rewrite Hsumx0.
                        fold B. unfold Rdiv. rewrite Rmult_assoc. 
                        rewrite <- Rinv_l_sym with (r:= B); try assumption.
                        rewrite Rmult_1_r. destruct HWF. assumption. }
                    split; try assumption.
                    split; try assumption. 
                    split. { destruct Heq0. simpl in *. apply dom_equiv_trans with (l1:= dom0); assumption. }
                    split. { destruct Heq1. simpl in *. apply dom_equiv_trans with (l1:= dom1); assumption. }
                    split. {  
                      apply sem_mult_cofe; try assumption.
                        * apply Rlt_le. 
                        apply Rdiv_lt_0_compat; apply R_ge0_iff; split; try assumption.
                          - destruct HWF. destruct H. assumption.
                          - destruct HWF0. destruct H. assumption.
                        * rewrite dst_sum_prob_coef_mult.
                        rewrite Hsumx. simpl in *. fold A. unfold Rdiv. rewrite Rmult_assoc. 
                        rewrite <- Rinv_l_sym with (r:= A); try assumption. 
                        rewrite Rmult_1_r. destruct HWF. assumption. }
                    split. {  
                      apply sem_mult_cofe; try assumption.
                      * apply Rlt_le. apply Rdiv_lt_0_compat; apply R_ge0_iff; split; try assumption.
                        - destruct HWF. destruct H. assumption. 
                        - destruct HWF1. destruct H. assumption.
                      * rewrite dst_sum_prob_coef_mult. rewrite Hsumx0. 
                      simpl in *. 
                      fold B.
                      unfold Rdiv. rewrite Rmult_assoc. 
                      rewrite <- Rinv_l_sym with (r:= B); try assumption. 
                      rewrite Rmult_1_r. destruct HWF. assumption. }
                    simpl. repeat rewrite dst_sum_prob_coef_mult. 
                    rewrite Hsumx. rewrite Hsumx0. fold A. fold B. 
                    split. { unfold Rdiv. rewrite Rmult_assoc. rewrite <- Rinv_l_sym with (r:= A); try assumption. rewrite Rmult_1_r. reflexivity. }
                    split. { unfold Rdiv. rewrite Rmult_assoc. rewrite <- Rinv_l_sym with (r:= B); try assumption. rewrite Rmult_1_r. reflexivity. }
                    apply dst_equiv_trans with (mu1:= ((s0, sp0) :: mu0') + ((s1, sp1) :: mu1')); try assumption.
                    repeat rewrite dst_mult_assoc_eq.
                    apply dst_add_preserves_equiv; try assumption.
                    --- unfold Rdiv. rewrite Rmult_assoc. rewrite <-Rmult_assoc with (r1:= /C).
                      rewrite <- Rinv_l_sym with (r:= C); try assumption.
                      rewrite Rmult_1_l.
                      rewrite <- Rinv_r_sym with (r:= A); try assumption.
                      rewrite dst_mult_1_l. destruct Heq0. 
                      apply dst_equiv_sym; try assumption.
                    --- unfold Rdiv. rewrite Rmult_assoc. rewrite <-Rmult_assoc with (r1:= /C).
                      rewrite <- Rinv_l_sym with (r:= C); try assumption.
                      rewrite Rmult_1_l.
                      rewrite <- Rinv_r_sym with (r:= B); try assumption.
                      rewrite dst_mult_1_l. destruct Heq1.
                      apply dst_equiv_sym; try assumption.
          - destruct Hsem0_case3. destruct H as [Hvalidx H]. 
            destruct H as [Heq0 H]. 
            destruct H as [Hsub2 H]. 
            destruct H as [Hphi1x Hsumx].   
            destruct Hsem1 as [Hsem1_case1 | Hsem1].
            { destruct Hsem1_case1 as [p11 H]. destruct H as [p12 H].
              destruct H as [Hp11 H]. destruct H as [Hp12 H].
              destruct H as [Hp1_case1 H].   
              destruct H as [pd11 H]. destruct H as [pd12 H]. 
              destruct H as [Hvalid11 H]. destruct H as [Hvalid12 H].
              destruct H as [Hdom11 H]. destruct H as [Hdom12 H].
              destruct H as [Hphi11 H]. destruct H as [Hphi12 H].
              destruct H as [Hsum11 H]. destruct H as [Hsum12 Hmu1].
              simpl in *.
              pose (p1:= (p11*B)/C). pose (p2:= (A + p12*B)/C).            
              destruct pd1 as [dom1 mu1 HPD1]. destruct mu1 as [|(s1,sp1) mu1'].
              ++ simpl. right. right.
                exists x. split; try assumption. 
                split. { destruct Heq0. split; simpl in *. 
                  - apply dom_equiv_trans with (l1:= CoreDef.dom pd0); assumption.
                  - apply dst_equiv_trans with (mu1:=mu pd0); try assumption. 
                    rewrite dst_add_0_r in Hmu_eq.
                    apply dst_equiv_sym; try assumption. }
                split. { 
                  simpl in Hdom1. 
                  apply dom_subset_eq_compat_left with (X:= CoreDef.dom pd0); assumption. }
                split; try assumption. 
                simpl in *. rewrite Hsum_eq. rewrite Rplus_0_r. assumption.
              ++ assert (HB: B <> 0). { 
                      unfold B. simpl. symmetry. apply Rlt_not_eq.
                      apply Valid_dist_conj in HWF1. destruct HWF1. destruct H. 
                      destruct H3. destruct H3.
                      destruct H0. destruct H0.
                      apply positive_sum_ge_0 in H6. 
                      apply Rplus_lt_le_0_compat; try assumption. } 
                simpl. left. exists p1, p2.  
                split. { unfold p1. rewrite HCAB. rewrite Rplus_comm. 
                        apply Rdiv_pA_in_01; try assumption.     
                        - destruct HWF1. destruct H. assumption. 
                        - destruct HWF0. destruct H. assumption.
                        - rewrite Rplus_comm. rewrite <- HCAB. assumption. }
                split. { unfold p2. rewrite HCAB. rewrite Rplus_comm. 
                        rewrite <- Rplus_comm with (r1:= B).
                        apply Rdiv_num_lt_den2; try assumption.
                        - destruct HWF1. destruct H. simpl in H. 
                          unfold B. simpl in *. apply R_ge0_iff; split; try assumption.
                        - destruct HWF0. destruct H. assumption.
                        - rewrite Rplus_comm. rewrite <- HCAB. assumption. }
                split. { unfold p1. unfold p2. 
                        rewrite <- Rdiv_plus_distr. 
                        rewrite <- Rplus_comm with (r2:= A).
                        rewrite <- Rplus_assoc.
                        rewrite <- Rmult_plus_distr_r. 
                        rewrite Hp1_case1. 
                        repeat rewrite Rmult_1_l. rewrite Rplus_comm.
                        rewrite <- HCAB. apply Rinv_r; try assumption. } 
                pose (p2':= (C/(1*A+ p12*B))%R).
                pose (p3':= (C*p12/(1*A+ p12*B))%R).
                pose (p1':= (C * p11/(p11*B))%R).
                assert (Hneq0: (1*A+ p12*B)%R <> 0%R). { 
                  symmetry. apply Rlt_not_eq. 
                  apply R_inte_help with (C:= C).
                  * apply R_ge0_iff. split; try assumption. 
                  unfold C. destruct HWF. destruct H. assumption.
                  * apply Rdiv_num_le_den; try assumption.
                    + destruct HWF0. assumption.
                    + destruct HWF1. assumption.
                    + split; [apply Rlt_0_1| apply Rle_refl].
                    + destruct Hp12. split; try apply Rlt_le; assumption. }
                assert (Hneq1: (p11* B)%R <> 0%R). { 
                  symmetry. apply Rlt_not_eq. destruct Hp11. 
                  apply Rmult_lt_0_compat; try assumption.
                  apply R_ge0_iff. split; try assumption. 
                  destruct HWF1. destruct H3. assumption. } 
                assert (Hp1'_gt0: 0 <= p1'). { 
                  unfold p1'. destruct Hp11. 
                  destruct HWF0. destruct H3. 
                  destruct HWF1. destruct H6. 
                  destruct HWF. destruct H9. 
                  unfold Rdiv. apply Rmult_le_pos; try assumption.
                  - apply Rmult_le_pos; try assumption. apply Rlt_le; try assumption.
                  - apply Rlt_le. apply Rinv_0_lt_compat; try assumption.
                  apply Rmult_lt_0_compat; try assumption. 
                  apply R_ge0_iff. split; try assumption. }
                assert (Hp2'_gt0: 0 <= p2'). { 
                  unfold p2'. destruct Hp12. 
                  destruct HWF0. destruct H3. 
                  destruct HWF1. destruct H6. 
                  destruct HWF. destruct H9.
                  unfold Rdiv. apply Rmult_le_pos; try assumption.
                  apply Rlt_le. apply Rinv_0_lt_compat; try assumption.
                  apply Rplus_le_lt_0_compat; try assumption.
                    + rewrite Rmult_1_l. assumption.
                    + apply Rmult_lt_0_compat; try assumption. apply R_ge0_iff. 
                    split; try assumption. }
                assert (Hp3'_gt0: 0 <= p3'). { 
                  unfold p3'. destruct Hp12. 
                  destruct HWF0. destruct H3. 
                  destruct HWF1. destruct H6. 
                  destruct HWF. destruct H9.
                  destruct Hp11. 
                  unfold Rdiv. apply Rmult_le_pos; try assumption.
                  - apply Rmult_le_pos; try assumption. apply Rlt_le; try assumption.
                  - apply Rlt_le. apply Rinv_0_lt_compat; try assumption.
                  apply Rplus_le_lt_0_compat; try assumption.
                  + rewrite Rmult_1_l. assumption.
                  + apply Rmult_lt_0_compat; try assumption. apply R_ge0_iff. 
                  split; try assumption. } 
                pose (pd1':= Build_partial_dist (CoreDef.dom pd11) (p1' * mu pd11) (pd_mult_preserve_PD pd11 p1')).
                assert (HPD2': partial_dst_Prop dom (p2'*(mu x)+p3'*(mu pd12))). {
                  apply PD_linear; try assumption.
                  - destruct Heq0. simpl in *. 
                    apply dom_equiv_trans with (l1:= CoreDef.dom pd0); try assumption. 
                  - destruct Heq0. simpl in *. 
                    apply dom_equiv_trans with (l1:= dom1); try assumption. } 
                pose (pd2':= Build_partial_dist dom (p2'*(mu x)+p3'*(mu pd12)) HPD2').
                exists pd1', pd2'.     
                assert (Hp1'_B: (p1' * B = C)%R). {
                  unfold p1'. unfold Rdiv. 
                  rewrite Rmult_assoc.
                  rewrite Rmult_assoc with (r1:= C). 
                  rewrite <- Rmult_1_r with (r:= C) at 2.
                  apply Rmult_eq_compat_l; try assumption.
                  rewrite <- Rmult_comm with (r1:= B).
                  rewrite <- Rmult_assoc with (r1:= p11).
                  rewrite Rinv_r; try assumption. reflexivity. }
                simpl.
                assert (Hv01: Valid_dist (p1' * mu pd11)). { 
                  try apply Valid_mult_under_eq_prob; try assumption.
                  rewrite dst_sum_prob_coef_mult. fold B in Hsum12. rewrite Hsum11.
                  fold B. rewrite Hp1'_B. destruct HWF. assumption. }
                assert (Hv23: Valid_dist (p2' * mu x + p3' * mu pd12)). { 
                  try apply Valid_linear_under_eq_prob; try assumption.
                  rewrite Hsum12. rewrite Hsumx. split.
                  - destruct HWF0. destruct H. destruct HWF1. destruct H4. 
                  rewrite <- Rplus_0_l at 1. apply Rplus_le_compat; apply Rmult_le_pos; try assumption.
                  - unfold p2'. unfold p3'. unfold Rdiv.
                  repeat rewrite Rmult_assoc. rewrite <- Rmult_plus_distr_l. 
                  repeat rewrite Rmult_comm with (r1:= / (1 * A + p12 * B)).
                  repeat rewrite <- Rmult_assoc. rewrite <- Rmult_plus_distr_r.
                  fold A. fold B. rewrite <- Rdiv_def. rewrite <- Rmult_1_l with (r:= A) at 1.
                  unfold Rdiv. 
                  rewrite Rinv_r with (r:= (1 * A + p12 * B)%R); try assumption.
                  rewrite Rmult_1_r. destruct HWF. destruct H. assumption. }
                split; try assumption. 
                split; try assumption.
                split. { simpl in *.
                        apply dom_equiv_trans with (l1:=dom1); try assumption. }
                split; try apply dom_equiv_refl.
                split. {
                  try apply sem_mult_cofe; try assumption. 
                  destruct Hv01. assumption. }
                split. {
                  pose (pd02':= Build_partial_dist (CoreDef.dom x) (p2' * (mu x)) (pd_mult_preserve_PD x p2')). 
                  pose (pd12':= Build_partial_dist (CoreDef.dom pd12) (p3' * (mu pd12)) (pd_mult_preserve_PD pd12 p3')).
                  apply IHphi2 with (pd0:= pd02') (pd1:= pd12'); try assumption. 
                  - inversion HEX; subst. assumption. 
                  - simpl. apply Valid_add_decom in Hv23. destruct Hv23. assumption.
                  - destruct Heq0. simpl in *. apply dom_equiv_trans with (l1:= CoreDef.dom pd0); try assumption.
                  - apply sem_mult_cofe; try assumption; try apply Rlt_le; try assumption. 
                    apply Valid_add_decom in Hv23. destruct Hv23. destruct H. assumption. 
                  - simpl. apply Valid_add_decom in Hv23. destruct Hv23. assumption.
                  - simpl. apply dom_equiv_trans with (l1:= dom1); try assumption.
                  - simpl. apply dst_equiv_refl.
                  - simpl. rewrite dst_sum_prob_decom. reflexivity.
                  - apply sem_mult_cofe; try assumption; try apply Rlt_le; try assumption. 
                    apply Valid_add_decom in Hv23. destruct Hv23. destruct H0. assumption. }  
                repeat rewrite dst_sum_prob_decom.
                repeat rewrite dst_sum_prob_coef_mult.
                rewrite Hsum11. rewrite Hsum12. rewrite Hsumx.
                repeat fold A. repeat fold B. simpl in C. repeat fold C.
                split; try assumption.
                split. { unfold p2'. unfold p3'. unfold Rdiv.
                        repeat rewrite Rmult_assoc. rewrite <- Rmult_plus_distr_l. 
                        repeat rewrite Rmult_comm with (r1:= / (1 * A + p12 * B)).
                        repeat rewrite <- Rmult_assoc. rewrite <- Rmult_plus_distr_r.
                        rewrite <- Rmult_1_l with (r:= A) at 1.
                        rewrite Rinv_r; try apply Rmult_1_r; try assumption. }
                repeat rewrite dst_mult_plus_distr_r_eq.
                repeat rewrite dst_mult_assoc_eq.
                apply dst_equiv_trans with (mu1:= mu pd0 + ((s1, sp1) :: mu1')); try assumption.
                assert (H01: (p2 * p2' = 1)%R). { 
                    unfold p2. unfold p2'.
                    rewrite <- Rmult_1_l with (r:= A) at 1.
                    unfold Rdiv. rewrite Rmult_assoc.
                    rewrite <- Rmult_assoc with (r1:= /C).
                    rewrite <- Rinv_l_sym with (r:= (C)%R); try assumption.
                    repeat rewrite Rmult_1_l. apply Rinv_r.
                    rewrite <- Rmult_1_l with (r:= A).
                    assumption. }
                rewrite H01. 
                assert (H02: (p1 * p1' = p11)%R). { 
                  unfold p1'. rewrite Rmult_comm. rewrite Rmult_comm with (r1:= C).
                  rewrite <- Rmult_1_r with (r:= p11) at 3.
                  unfold Rdiv. rewrite Rmult_assoc. 
                  rewrite Rmult_assoc with (r1:= p11).
                  apply Rmult_eq_compat_l.
                  unfold p1. unfold Rdiv.
                  rewrite <- Rmult_assoc with (r3:= /C).
                  rewrite <- Rinv_l_sym with (r:= (p11 * B)%R).
                  - rewrite Rmult_1_l. apply Rinv_r. assumption.
                  - assumption. }
                rewrite H02. 
                assert (H11: (p2 * p3' = p12)%R). { 
                  unfold p3'. rewrite Rmult_comm. rewrite Rmult_comm with (r1:= C).
                  rewrite <- Rmult_1_r with (r:= p12) at 3.
                  unfold Rdiv. rewrite Rmult_assoc. 
                  rewrite Rmult_assoc with (r1:= p12).
                  apply Rmult_eq_compat_l.
                  unfold p2. unfold Rdiv.
                  rewrite <- Rmult_assoc with (r3:= /C). 
                  rewrite <- Rmult_1_l with (r:= A) at 2. 
                  rewrite <- Rinv_l_sym with (r:= (1 * A + p12 * B)%R).
                  - rewrite Rmult_1_l. apply Rinv_r. assumption.
                  - assumption. }
                rewrite H11. rewrite dst_mult_1_l.
                rewrite <- dst_add_0_l with (mu:=p11 * mu pd11).
                apply dst_equiv_trans with (mu1:= [] + mu x + (p11 * mu pd11 + p12 * mu pd12)); try apply dst_add_shuffle.
                simpl.
                apply dst_add_preserves_equiv; try assumption. 
                destruct Heq0.
                apply dst_equiv_sym; try assumption. 
            }
            destruct Hsem1 as [Hsem1_case2 | Hsem1_case3]. 
            + destruct Hsem1_case2. destruct H as [Hvalidx0 H]. destruct H as [Heq1 H].
              destruct H as [Hsub1 H]. 
              destruct H as [Hphi1x0 Hsumx0]. 
              destruct pd0 as [dom0 mu0 HPD0]. destruct mu0 as [|(s0,sp0) mu0'].
              -- simpl. right. left. exists x0. split; try assumption. 
                split. { destruct Heq1. destruct Heq0. split; simpl in *. 
                        - apply dom_equiv_trans with (l1:= CoreDef.dom pd1); assumption.
                        - apply dst_equiv_sym in Hmu_eq. 
                        apply dst_equiv_trans with (mu1:= mu pd1); try assumption. }
                split. { simpl in *. 
                        apply dom_subset_eq_compat_left with (Y:= dom) in Hsub1; try assumption. }
                split; try assumption.
                simpl in *. rewrite Hsum_eq. rewrite Rplus_0_l. assumption.
              -- assert (HA: A<>0). { unfold A. simpl. symmetry. apply Rlt_not_eq.
                                      apply Valid_dist_conj in HWF0. destruct HWF0.
                                      destruct H.  
                                      destruct H3. destruct H3.
                                      destruct H0. destruct H0.
                                      apply positive_sum_ge_0 in H6. 
                                      apply Rplus_lt_le_0_compat; try assumption. }
                destruct pd1 as [dom1 mu1 HPD1]. destruct mu1 as [|(s1,sp1) mu1'].
                ++ simpl. right. right. exists x. split; try assumption. 
                  split. { destruct Heq0. simpl in *. split; simpl in *. 
                          - apply dom_equiv_trans with (l1:= dom0); try assumption.
                          - rewrite dst_add_0_r in Hmu_eq . apply dst_equiv_sym in Hmu_eq.
                          apply dst_equiv_trans with (mu1:= (s0, sp0) :: mu0'); try assumption. }
                  split. { simpl in *. apply dom_subset_eq_compat_left with (X:= dom0); try assumption. }
                  split; try assumption.
                  simpl in *. rewrite Hsum_eq. rewrite Rplus_0_r. assumption.
                ++ simpl. left. exists (B/C)%R, (A/C)%R.
                  assert (HB: B<>0). { unfold B. simpl. symmetry. apply Rlt_not_eq.
                                      apply Valid_dist_conj in HWF1. destruct HWF1. destruct H. 
                                      destruct H3. destruct H3.
                                      destruct H0. destruct H0.
                                      apply positive_sum_ge_0 in H6. 
                                      apply Rplus_lt_le_0_compat; try assumption. }
                  split. { rewrite HCAB. rewrite Rplus_comm. destruct HWF0. 
                          destruct HWF1. apply Rfrac_bound_lt1; try assumption.  }
                  split. { rewrite HCAB. destruct HWF0. 
                          destruct HWF1. apply Rfrac_bound_lt1; try assumption. }
                  split. { rewrite <- Rdiv_plus_distr. rewrite Rplus_comm. 
                          rewrite <- HCAB. unfold Rdiv. apply Rinv_r. assumption.  }
                  pose (pd1':= Build_partial_dist (CoreDef.dom x0) (C/B * mu x0) (pd_mult_preserve_PD x0 (C/B))).
                  pose (pd2':= Build_partial_dist (CoreDef.dom x) (C/A * mu x) (pd_mult_preserve_PD x (C/A))).
                  exists pd1', pd2'. simpl. 
                  assert (Hv: Valid_dist (C / A * mu x)). {
                    apply Valid_mult_under_eq_prob; try assumption; try apply Rle_0_1.
                      - unfold Rdiv. apply Rlt_le. apply Rmult_lt_0_compat. 
                        + apply R_ge0_iff. split; try assumption.
                        destruct HWF. destruct H. assumption. 
                        + apply Rinv_0_lt_compat; try assumption. 
                          destruct HWF0. destruct H. 
                          apply R_ge0_iff. split; try assumption. 
                      - rewrite dst_sum_prob_coef_mult. rewrite Hsumx. 
                        fold A. unfold Rdiv. rewrite Rmult_assoc. 
                        rewrite <- Rinv_l_sym with (r:= A); try assumption.
                        rewrite Rmult_1_r. destruct HWF. assumption. }
                    assert (Hv1: Valid_dist (C / B * mu x0)). {
                      apply Valid_mult_under_eq_prob; try assumption; try apply Rle_0_1.
                      - unfold Rdiv. apply Rlt_le. apply Rmult_lt_0_compat. 
                        + apply R_ge0_iff. split; try assumption.
                        destruct HWF. destruct H. assumption. 
                        + apply Rinv_0_lt_compat; try assumption. 
                          destruct HWF1. destruct H. 
                          apply R_ge0_iff. split; try assumption.
                      - rewrite dst_sum_prob_coef_mult. simpl in *. rewrite Hsumx0. 
                        fold B. unfold Rdiv. rewrite Rmult_assoc.
                        rewrite <- Rinv_l_sym with (r:= B); try assumption.
                        rewrite Rmult_1_r. destruct HWF. assumption. }
                    split; try assumption.
                    split; try assumption. 
                    split. { destruct Heq1. simpl in *. apply dom_equiv_trans with (l1:= dom1); assumption. }
                    split. { destruct Heq0. simpl in *. apply dom_equiv_trans with (l1:= dom0); assumption. }
                    split. {  
                      apply sem_mult_cofe; try assumption.
                      * apply Rlt_le. 
                      apply Rdiv_lt_0_compat; apply R_ge0_iff; split; try assumption.
                        - destruct HWF. destruct H. assumption.
                        - destruct HWF1. destruct H. assumption.
                      * rewrite dst_sum_prob_coef_mult.
                      rewrite Hsumx0. simpl in *. fold B. unfold Rdiv. rewrite Rmult_assoc. 
                      rewrite <- Rinv_l_sym with (r:= B); try assumption. 
                      rewrite Rmult_1_r. destruct HWF. assumption. }
                    split. {  
                      apply sem_mult_cofe; try assumption.
                        * apply Rlt_le. 
                        apply Rdiv_lt_0_compat; apply R_ge0_iff; split; try assumption.
                          - destruct HWF. destruct H. assumption.
                          - destruct HWF0. destruct H. assumption.
                        * rewrite dst_sum_prob_coef_mult.
                        rewrite Hsumx. simpl in *. fold A. unfold Rdiv. rewrite Rmult_assoc. 
                        rewrite <- Rinv_l_sym with (r:= A); try assumption. 
                        rewrite Rmult_1_r. destruct HWF. assumption. }
                    repeat rewrite dst_sum_prob_coef_mult.
                    rewrite Hsumx. rewrite Hsumx0. fold A. fold B. 
                    split. { unfold Rdiv. rewrite Rmult_assoc. rewrite <- Rinv_l_sym with (r:= B); try assumption. rewrite Rmult_1_r. reflexivity. }
                    split. { unfold Rdiv. rewrite Rmult_assoc. rewrite <- Rinv_l_sym with (r:= A); try assumption. rewrite Rmult_1_r. reflexivity. }
                    apply dst_equiv_trans with (mu1:= ((s0, sp0) :: mu0') + ((s1, sp1) :: mu1')); try assumption.
                    repeat rewrite dst_mult_assoc_eq.
                    apply dst_equiv_trans with (mu1:= ((s1, sp1) :: mu1') + ((s0, sp0) :: mu0')); try apply dst_add_comm.
                    apply dst_add_preserves_equiv; try assumption.
                      --- unfold Rdiv. rewrite Rmult_assoc. rewrite <-Rmult_assoc with (r1:= /C).
                      rewrite <- Rinv_l_sym with (r:= C); try assumption.
                      rewrite Rmult_1_l.
                      rewrite <- Rinv_r_sym with (r:= B); try assumption.
                      rewrite dst_mult_1_l. destruct Heq1. 
                      apply dst_equiv_sym; try assumption.
                      --- unfold Rdiv. rewrite Rmult_assoc. rewrite <-Rmult_assoc with (r1:= /C).
                      rewrite <- Rinv_l_sym with (r:= C); try assumption.
                      rewrite Rmult_1_l.
                      rewrite <- Rinv_r_sym with (r:= A); try assumption.
                      rewrite dst_mult_1_l. destruct Heq0.
                      apply dst_equiv_sym; try assumption.
            + destruct Hsem1_case3. destruct H as [Hvalidx0 H]. destruct H as [Heq1 H].
              destruct H as [Hsub1 H]. 
              destruct H as [Hphi1x0 Hsumx0]. 
              simpl. right. right. 
              assert (HPD': partial_dst_Prop (dom) (mu x + mu x0)). {
                  apply PD_decom. split.
                  - destruct x as [domx mux Hx]; subst. simpl in *. 
                    destruct Heq0. simpl in *.
                    apply Peq_dom_PD_Prop with (dom:= domx); try assumption.
                    apply dom_equiv_sym. 
                    apply dom_equiv_trans with (l1:= CoreDef.dom pd0); assumption.
                  - destruct x0 as [domx0 mux0 Hx0]; subst. simpl in *. 
                    destruct Heq1. simpl in *.
                    apply Peq_dom_PD_Prop with (dom:= domx0); try assumption.
                    apply dom_equiv_sym. apply dom_equiv_trans with (l1:= CoreDef.dom pd1); assumption. }
              pose (pd':= Build_partial_dist (dom) ((mu x + mu x0)%dist_state) HPD').
              exists pd'. simpl.
              assert (Hv: Valid_dist (mu x + mu x0)). {
                rewrite <- dst_mult_1_l with (mu:=mu x). rewrite <- dst_mult_1_l with (mu:= mu x0). 
                apply Valid_linear_under_eq_prob; try assumption; try apply Rle_0_1.
                repeat rewrite Rmult_1_l. rewrite Hsumx. rewrite Hsumx0.
                fold A. fold B. rewrite <- HCAB.
                destruct HWF. assumption. }
              split; try assumption.
              split. { split; simpl; try apply dom_equiv_refl. 
                      simpl in Hmu_eq. apply dst_equiv_sym in Hmu_eq.
                      destruct Heq0. destruct Heq1.  
                      apply dst_equiv_trans with (mu1:= mu pd0 + mu pd1); try assumption.
                      apply dst_add_preserves_equiv; try assumption. }
              split. { apply dom_subset_eq_compat_left with (X:= (CoreDef.dom pd1)); try assumption. }
              split. {
                apply IHphi2 with (pd0:=x) (pd1:=x0); try assumption; try reflexivity; try apply dst_equiv_refl.
                + inversion HEX; subst. assumption. 
                + simpl. destruct Heq0. 
                  apply dom_equiv_trans with (l1:= CoreDef.dom pd0); assumption.
                + simpl. destruct Heq1. 
                  apply dom_equiv_trans with (l1:= CoreDef.dom pd1); assumption.
                + simpl. rewrite dst_sum_prob_decom. reflexivity.  }
              rewrite dst_sum_prob_decom. rewrite Hsumx. rewrite Hsumx0. 
              fold A. fold B. rewrite <- HCAB. try reflexivity. }
  - intros. simpl in HEX. contradiction.   
  - intros. simpl in *. destruct Hsem0. destruct Hsem1. inversion HWD; subst. inversion HEX; subst.  
    split. 
      + apply IHphi1 with (pd0:= pd0) (pd1:= pd1); try assumption; try apply dst_equiv_refl.  
      + apply IHphi2 with (pd0:= pd0) (pd1:= pd1); try assumption; try apply dst_equiv_refl. 
Qed.

(*******************************************************************)
Lemma bT_sem_iff: forall b pd, 
  [[Pdeter (Dpred b)]] pd <-> 
  WF_bexp_with_pd b pd /\ (b_supp_classify b pd = All_nil \/ b_supp_classify b pd = All_True). 
Proof. 
  split. 
  { intros. destruct H as [Hsub Hsem].
    destruct pd as [dom mu HPD]. split; try assumption. simpl in Hsem.
    induction mu as [|(s,p) mu' Hmu ]; unfold WF_bexp_with_pd; unfold b_supp_classify.
    - simpl in *. left. reflexivity.
    - simpl in *. 
      assert (Hst: evalB_st b s = true). 
      { assert (Hin: is_in_supp s (supp_mu ((s, p) :: mu')) = true) by apply in_supp_mu_cons_head.
        specialize (Hsem s Hin). destruct Hsem as [Hb Heval].
        destruct (evalB_st b s) eqn:Hst; try contradiction.
        reflexivity. } 
      unfold supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st.
      rewrite supp_insert_evalB. 
      rewrite Hst. simpl. 
      inversion HPD; subst. specialize (Hmu H3 Hsub).
      assert (Hsem': forall st : partial_st,
              is_in_supp st (supp_mu (mu {| dom := dom; mu := mu'; all_partial := H3 |})) = true ->
                df_sem (Dpred b) st). {
        intros st Hin. apply Hsem. simpl. apply in_supp_mu_cons_r; try assumption. }
      specialize (Hmu Hsem'). 
      destruct Hmu as [Hmu|Hmu].
      + unfold b_supp_classify in Hmu. simpl in Hmu. 
        destruct mu'.
        ** simpl. right. reflexivity.
        ** destruct (forallb (fun s : partial_st => evalB_st b s) (supp_mu (p0 :: mu'))); 
          destruct (forallb (fun s : partial_st => negb (evalB_st b s)) (supp_mu (p0 :: mu'))); try discriminate.
      + unfold b_supp_classify in Hmu. simpl in Hmu. unfold supp_mu in Hmu.
        destruct mu'; try discriminate. right.
        destruct (forallb (fun s : partial_st => evalB_st b s) (map fst (sort_dst (p0 :: mu')))); 
          destruct (forallb (fun s : partial_st => negb (evalB_st b s)) (map fst (sort_dst (p0 :: mu')))); 
            try discriminate; try reflexivity.
  }     
    intros. destruct pd as [dom mu HPD]. destruct H as [Hb H].
    unfold WF_bexp_with_pd in Hb. unfold b_supp_classify in H.
    simpl in *. split; try assumption.
    intros. split.
    - apply in_supp_return_domain_eq with (pd:= Build_partial_dist dom mu HPD) in H0.
      simpl in H0. apply dom_equiv_sym in H0. 
      apply dom_subset_eq_compat_left with (X:= dom); try assumption.
    - induction mu as [|(s,p) mu' Hmu ]; simpl in *; try discriminate. 
      inversion HPD; subst. specialize (Hmu H5). 
      unfold supp_mu in H0. simpl in H0. rewrite insert_st_pair_fst_eq_insert_st in H0.
      rewrite in_supp_insert_eq in H0. 
      apply orb_true_iff in H0. destruct H0.
      + rewrite st_eq_implies_evalB with (st2:= s); try assumption.
        destruct (evalB_st b s) eqn:Hst; try apply I.
        simpl in H. destruct H; try discriminate.
        ++destruct (forallb (fun s : partial_st => evalB_st b s) (supp_mu ((s, p) :: mu'))); try discriminate.
          destruct (forallb (fun s : partial_st => negb (evalB_st b s)) (supp_mu ((s, p) :: mu'))); try discriminate.
        ++ destruct (forallb (fun s : partial_st => evalB_st b s) (supp_mu ((s, p) :: mu')))eqn: Hcontra; try discriminate. 
        -- unfold supp_mu in Hcontra. simpl in Hcontra. rewrite insert_st_pair_fst_eq_insert_st in Hcontra.
        rewrite supp_insert_evalB in Hcontra. apply andb_true_iff in Hcontra. destruct Hcontra as [Hcontra].
        rewrite Hst in Hcontra. discriminate.
        -- destruct (forallb (fun s : partial_st => negb (evalB_st b s)) (supp_mu ((s, p) :: mu'))); try discriminate.
      + destruct H. 
        ++ destruct (forallb (fun s : partial_st => evalB_st b s) (supp_mu ((s, p) :: mu'))); try discriminate. 
        destruct (forallb (fun s : partial_st => negb (evalB_st b s)) (supp_mu ((s, p) :: mu'))); try discriminate.
        ++ destruct (forallb (fun s : partial_st => evalB_st b s) (supp_mu ((s, p) :: mu'))) eqn: Htmp; 
        destruct (forallb (fun s : partial_st => negb (evalB_st b s)) (supp_mu ((s, p) :: mu')));
        try discriminate. 
        ** apply Hmu; try assumption. destruct mu'. 
        -- left. reflexivity.
        -- right. unfold supp_mu in Htmp. simpl in Htmp. rewrite insert_st_pair_fst_eq_insert_st in Htmp.
        rewrite supp_insert_evalB in Htmp. apply andb_true_iff in Htmp. destruct Htmp. 
        unfold supp_mu. simpl. rewrite H2. reflexivity. 
        ** apply Hmu; try assumption. destruct mu'. 
        -- left. reflexivity.
        -- right. unfold supp_mu in Htmp. simpl in Htmp. rewrite insert_st_pair_fst_eq_insert_st in Htmp.
        rewrite supp_insert_evalB in Htmp. apply andb_true_iff in Htmp. destruct Htmp. 
        unfold supp_mu. simpl. rewrite H2. reflexivity. 
Qed.   

Lemma bF_sem_iff: forall b pd, 
  [[Pdeter (Dpred (Bnot b))]] pd <-> 
    WF_bexp_with_pd b pd /\ (b_supp_classify b pd = All_nil \/b_supp_classify b pd = All_False).
Proof. 
  split. 
  * intros. destruct H as [Hsub Hsem].
    destruct pd as [dom mu HPD]. split; try assumption.
    induction mu as [|(s,p) mu' Hmu ]; unfold WF_bexp_with_pd; unfold b_supp_classify.
    - simpl in *. left. reflexivity.  
    - simpl in *. right.
      assert (Hst: evalB_st b s = false). 
      { assert (Hin: is_in_supp s (supp_mu ((s, p) :: mu')) = true) by apply in_supp_mu_cons_head.
        specialize (Hsem s Hin). destruct Hsem as [Hb Heval].
        destruct (evalB_st b s) eqn:Hst; try contradiction.
        reflexivity. }
      unfold supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st.
      rewrite supp_insert_negbevalB.  
      rewrite Hst. simpl. 
      inversion HPD; subst. specialize (Hmu H3 Hsub).
      assert (Hsem': forall st : partial_st,
              is_in_supp st (supp_mu (mu {| dom := dom; mu := mu'; all_partial := H3 |})) = true ->
                df_sem (Dpred (~b)) st). {
        intros st Hin. apply Hsem. simpl. apply in_supp_mu_cons_r; try assumption. }
      specialize (Hmu Hsem'). destruct Hmu as [Hmu|Hmu].
      + unfold b_supp_classify in Hmu. simpl in Hmu. 
        destruct mu'; try discriminate.
        ** simpl. rewrite Hst. simpl. reflexivity.
        ** destruct (forallb (fun s : partial_st => evalB_st b s) (supp_mu (p0 :: mu'))); 
          destruct (forallb (fun s : partial_st => negb (evalB_st b s)) (supp_mu (p0 :: mu'))); try discriminate.
      + rewrite supp_insert_evalB. rewrite Hst. simpl. 
        unfold b_supp_classify in Hmu. simpl in Hmu. 
        destruct (mu'); try discriminate.
        destruct (forallb (fun s : partial_st => evalB_st b s) (supp_mu (p0 :: l))); try discriminate.
        unfold supp_mu in Hmu. assumption.
  * intros. destruct pd as [dom mu HPD]. destruct H as [Hb H].
    unfold WF_bexp_with_pd in Hb. unfold b_supp_classify in H.
    simpl in *. split; try assumption.
    intros. split.
    - apply in_supp_return_domain_eq with (pd:= Build_partial_dist dom mu HPD) in H0.
      simpl in H0. apply dom_equiv_sym in H0. 
      apply dom_subset_eq_compat_left with (X:= dom); try assumption.
    - induction mu as [|(s,p) mu' Hmu ]; simpl in *; try discriminate. 
      inversion HPD; subst. specialize (Hmu H5). 
      unfold supp_mu in H0. simpl in H0. rewrite insert_st_pair_fst_eq_insert_st in H0.
      rewrite in_supp_insert_eq in H0. 
      apply orb_true_iff in H0. destruct H0.
      + rewrite st_eq_implies_evalB with (st2:= s); try assumption.
        destruct (evalB_st b s) eqn:Hst; try apply I. simpl.
        simpl in H. destruct H; try discriminate.
        ++ destruct (forallb (fun s : partial_st => evalB_st b s) (supp_mu ((s, p) :: mu'))); try discriminate.
        destruct (forallb (fun s : partial_st => negb (evalB_st b s)) (supp_mu ((s, p) :: mu'))); try discriminate.
        ++ destruct (forallb (fun s : partial_st => evalB_st b s) (supp_mu ((s, p) :: mu'))); try discriminate.
        destruct (forallb (fun s : partial_st => negb (evalB_st b s)) (supp_mu ((s, p) :: mu'))) eqn: Hcontra; try discriminate.
        unfold supp_mu in Hcontra. simpl in Hcontra. rewrite insert_st_pair_fst_eq_insert_st in Hcontra.
        rewrite supp_insert_negbevalB in Hcontra.  
        rewrite Hst in Hcontra. apply andb_true_iff in Hcontra. destruct Hcontra as [Hcontra].
        simpl in Hcontra. discriminate.
      + destruct mu'. 
        -- apply Hmu; try assumption. left. reflexivity.
        -- apply Hmu; try assumption. right.      
        destruct H. 
        ++ destruct (forallb (fun s : partial_st => evalB_st b s) (supp_mu ((s, p) :: p0 :: mu'))); try discriminate. 
        destruct (forallb (fun s : partial_st => negb (evalB_st b s)) (supp_mu ((s, p) :: p0 :: mu'))); try discriminate.
        ++ destruct (forallb (fun s : partial_st => evalB_st b s) (supp_mu ((s, p) :: p0 :: mu'))); try discriminate. 
        destruct (forallb (fun s : partial_st => negb (evalB_st b s)) (supp_mu ((s, p) :: p0 :: mu'))) eqn: Htmp; try discriminate.
        unfold supp_mu in Htmp. simpl in Htmp. rewrite insert_st_pair_fst_eq_insert_st in Htmp.
        rewrite supp_insert_negbevalB in Htmp.  
        apply andb_true_iff in Htmp. destruct Htmp.
        unfold supp_mu. simpl. 
        rewrite H2. apply negb_true_iff in H1. 
        destruct p0. simpl in *.
        rewrite insert_st_pair_fst_eq_insert_st. 
        rewrite supp_insert_evalB.
        rewrite insert_st_pair_fst_eq_insert_st in H2. 
        rewrite supp_insert_negbevalB in H2.
        apply andb_true_iff in H2. 
        destruct H2. apply negb_true_iff in H2.
        rewrite H2. simpl. reflexivity.
Qed.

Lemma Oplus_implies_fst_under_All_true: 
  forall b pd phi0 phi1, 
  Valid_dist (mu pd) -> well_defined_Pf (phi0 ∧ Pdeter (Dpred b) ⊕ phi1 ∧ Pdeter (Dpred (~ b)))%formula ->
  b_supp_classify b pd = All_True ->
  [[phi0 ∧ Pdeter (Dpred b) ⊕ phi1 ∧ Pdeter (Dpred (~ b))]] pd ->
  [[phi0 ∧ Pdeter (Dpred b)]] pd.
Proof. 
  intros b pd phi0 phi1 Hvalid HWD Hbclass Hsem.
  destruct Hsem as [Hcase1 | Hsem]. 
    + destruct Hcase1 as [p1 H]. destruct H as [p2 H]. 
      destruct H as [Hp1 H]. destruct H as [Hp2 H]. destruct H as [Hp_eq H].
      destruct H as [pd01 H]. destruct H as [pd02 H].
      destruct H as [HWF01 H]. destruct H as [HWF02 H]. 
      destruct H as [Hdom01 H]. destruct H as [Hdom02 H].
      destruct H as [Hsem01 H]. destruct H as [Hsem02 H].
      destruct H as [Hsum0 H]. destruct H as [Hsum1 Hmu].
      assert (Hvalid': Valid_dist (p1 * mu pd01 + p2 * mu pd02)%dist_state). { 
          apply Valid_linear; try assumption. 
          - destruct Hp1. split; apply Rlt_le; assumption.
          - destruct Hp2. split; apply Rlt_le; assumption.
          - rewrite Hp_eq. apply Rle_refl. }
      assert (HPD': partial_dst_Prop (dom pd) (p1 * (mu pd01) + p2 * (mu pd02))%dist_state). {
        apply PD_linear; try assumption. 
        - destruct Hp1. apply Rlt_le. assumption.
        - destruct Hp2. apply Rlt_le. assumption. }
      pose (pd_tmp:= Build_partial_dist (dom pd) ((p1 * (mu pd01) + p2 * (mu pd02))%dist_state) HPD').
      assert (Heq: pd ≡ pd_tmp). { split; simpl; try apply dom_equiv_refl. assumption. }
      destruct pd02 as [dom02 mu02 HPD02]. destruct mu02 as [|(s02, p02) mu02']. 
      * simpl in Hmu. rewrite dst_add_0_r in Hmu. 
      simpl in Hdom02. simpl in Hsum1. rewrite <- Hsum1 in Hsum0.
      assert (Hmu_nil: mu pd = []). { 
        apply sum_probs0_implies_nil; try assumption.
        apply dst_equiv_implies_sum_probs_eq in Hmu; try assumption.
        - rewrite dst_sum_prob_coef_mult in Hmu. rewrite Hsum0 in Hmu. rewrite Rmult_0_r in Hmu. assumption.
        - apply Valid_mult_cofe; try assumption.
          destruct Hp1. split; apply Rlt_le; assumption. }
      unfold b_supp_classify in Hbclass. rewrite Hmu_nil in Hbclass. 
      discriminate Hbclass.
      * destruct Hsem02. destruct H0. simpl in H1. specialize (H1 s02).
      assert (Hin: is_in_supp s02 (supp_mu ((s02, p02) :: mu02')) = true) by apply in_supp_mu_cons_head.
      specialize (H1 Hin). destruct H1. 
      destruct (negb (evalB_st b s02)) eqn: Hs02; try contradiction.
      apply negb_true_iff in Hs02. 
      rewrite dst_equiv_implies_b_classify with (pd1:= pd_tmp) in Hbclass; try assumption.
      assert (Htmp: [[Pdeter (Dpred b)]] pd_tmp). { 
        apply bT_sem_iff. split; try assumption. 
        - unfold WF_bexp_with_pd. simpl. simpl in H0. simpl in Hdom02. 
        apply dom_subset_eq_compat_left with (Z:= (get_variables_in_bexp b)) in Hdom02; try assumption. 
        - right. assumption. }
      destruct Htmp as [Hem' Hcontra].
      specialize (Hcontra s02). 
      assert (Hin': is_in_supp s02 (supp_mu (mu pd_tmp)) = true).  {
        apply in_supp_iff_posi_prob; try assumption; try assumption.  
          pose (p':= (get_prob_in_dstate (p1 * mu pd01)%dist_state s02 + p2 * p02 + get_prob_in_dstate (p2 * mu02')%dist_state s02)%R).
          exists p'. simpl. destruct (Req_dec_T p2 0). 
          -- destruct Hp2 as [Hp_]. rewrite e in Hp_. apply Rlt_irrefl in Hp_. contradiction.
          -- rewrite get_prob_decom. rewrite dst_cons_eq_add.
          rewrite get_prob_decom. simpl. rewrite state_eq_refl. 
          rewrite Rplus_0_r. rewrite <- Rplus_assoc.
          split; try reflexivity. unfold p'.
          apply Valid_add_decom in Hvalid'. destruct Hvalid'. 
          simpl in H4.  destruct (Req_dec_T p2 0). 
          --- destruct Hp2 as [Hp_]. rewrite e in Hp_. apply Rlt_irrefl in Hp_. contradiction.
          --- rewrite dst_cons_eq_add in H4. apply Valid_add_decom in H4. destruct H4. 
          apply Rplus_lt_le_0_compat. 
          ++ apply Rplus_le_lt_0_compat. 
          ** apply dst_Valid_prob_0_1. assumption.
          ** destruct H4. destruct H6. destruct H6. assumption. 
          ++ apply dst_Valid_prob_0_1. assumption. }
      specialize (Hcontra Hin'). simpl in Hcontra. destruct Hcontra as [_ Hcontra].
      rewrite Hs02 in Hcontra. contradiction.
    + destruct Hsem as [Hcase2| Hcase3]. 
      * destruct Hcase2 as [pd01 H]. destruct H as [HWF01 H].
        destruct H as [Hpdeq01 H]. apply pd_equiv_sym in Hpdeq01.
        destruct H as [Hsub H]. 
        destruct H as [Hsem01 Hsum].
        apply pd_equiv_preserves_sem with (pd0:= pd01); try assumption.
        inversion HWD; subst. assumption.
      * destruct Hcase3 as [pd01 H]. destruct H as [HWF01 H].
        destruct H as [Hpdeq01 H]. apply pd_equiv_sym in Hpdeq01.
        destruct H as [Hsub H]. 
        destruct H as [Hsem01 Hsum]. destruct Hsem01 as [Hsem01 Hcontra].
        apply bF_sem_iff in Hcontra. destruct Hcontra as [_ Hcontra].
        apply dst_equiv_implies_b_classify with (b:= b) in Hpdeq01; try assumption.
        rewrite Hbclass in Hpdeq01. 
        rewrite <- Hpdeq01 in Hcontra. destruct Hcontra; discriminate.
Qed.

Lemma Oplus_implies_snd_under_All_false: 
  forall b pd phi0 phi1, 
  Valid_dist (mu pd) -> well_defined_Pf (phi0 ∧ Pdeter (Dpred b) ⊕ phi1 ∧ Pdeter (Dpred (~ b))) ->
  b_supp_classify b pd = All_False ->
  [[phi0 ∧ Pdeter (Dpred b) ⊕ phi1 ∧ Pdeter (Dpred (~ b))]] pd ->
  [[phi1 ∧ Pdeter (Dpred (~ b))]] pd.
Proof. 
  intros b pd phi0 phi1 Hvalid HWD Hbclass Hsem.
  destruct Hsem as [Hcase1 | Hsem]. 
    + destruct Hcase1 as [p1 H]. destruct H as [p2 H]. 
      destruct H as [Hp1 H]. destruct H as [Hp2 H]. destruct H as [Hp_eq H].
      destruct H as [pd01 H]. destruct H as [pd02 H].
      destruct H as [HWF01 H]. destruct H as [HWF02 H]. 
      destruct H as [Hdom01 H]. destruct H as [Hdom02 H].
      destruct H as [Hsem01 H]. destruct H as [Hsem02 H].
      destruct H as [Hsum0 H]. destruct H as [Hsum1 Hmu].
      assert (Hvalid': Valid_dist (p1 * mu pd01 + p2 * mu pd02)%dist_state). { 
          apply Valid_linear; try assumption. 
          - destruct Hp1. split; apply Rlt_le; assumption.
          - destruct Hp2. split; apply Rlt_le; assumption.
          - rewrite Hp_eq. apply Rle_refl. }
      assert (HPD': partial_dst_Prop (dom pd) (p1 * (mu pd01) + p2 * (mu pd02))%dist_state). {
        apply PD_linear; try assumption. 
        - destruct Hp1. apply Rlt_le. assumption.
        - destruct Hp2. apply Rlt_le. assumption. }
      pose (pd_tmp:= Build_partial_dist (dom pd) ((p1 * (mu pd01) + p2 * (mu pd02))%dist_state) HPD').
      assert (Heq: pd ≡ pd_tmp). { split; simpl; try apply dom_equiv_refl. assumption. }
      destruct pd01 as [dom01 mu01 HPD01]. destruct mu01 as [|(s02, p02) mu02']. 
      * simpl in Hmu. 
      simpl in Hdom01. simpl in Hsum0. rewrite <- Hsum0 in Hsum1.
      assert (Hmu_nil: mu pd = []). { 
        apply sum_probs0_implies_nil; try assumption.
        apply dst_equiv_implies_sum_probs_eq in Hmu; try assumption.
        rewrite dst_sum_prob_coef_mult in Hmu. rewrite Hsum1 in Hmu. rewrite Rmult_0_r in Hmu. assumption. }
      unfold b_supp_classify in Hbclass. rewrite Hmu_nil in Hbclass. 
      discriminate Hbclass.
      * destruct Hsem01. destruct H0. simpl in H1. specialize (H1 s02).
      assert (Hin: is_in_supp s02 (supp_mu ((s02, p02) :: mu02')) = true) by apply in_supp_mu_cons_head.
      specialize (H1 Hin). destruct H1. 
      destruct ((evalB_st b s02)) eqn: Hs02; try contradiction.
      rewrite dst_equiv_implies_b_classify with (pd1:= pd_tmp) in Hbclass; try assumption.
      assert (Htmp: [[Pdeter (Dpred (~b))]] pd_tmp). { 
        apply bF_sem_iff. split; try assumption. 
        - unfold WF_bexp_with_pd. simpl. simpl in H0. simpl in Hdom01. 
        apply dom_subset_eq_compat_left with (Z:= (get_variables_in_bexp b)) in Hdom01; try assumption.
        - right. assumption. }
      destruct Htmp as [Hem' Hcontra].
      specialize (Hcontra s02). 
      assert (Hin': is_in_supp s02 (supp_mu (mu pd_tmp)) = true).  {
        apply in_supp_iff_posi_prob; try assumption; try assumption.  
          pose (p':= ( p1 * p02 + get_prob_in_dstate (p1 * mu02')%dist_state s02 +  get_prob_in_dstate (p2 * (mu pd02))%dist_state s02)%R).
          exists p'. simpl. destruct (Req_dec_T p1 0). 
          -- destruct Hp1 as [Hp_]. rewrite e in Hp_. apply Rlt_irrefl in Hp_. contradiction.
          -- rewrite get_prob_decom. rewrite dst_cons_eq_add.
          rewrite get_prob_decom. simpl. rewrite state_eq_refl. 
          rewrite Rplus_0_r. 
          split; try reflexivity. unfold p'.
          apply Valid_add_decom in Hvalid'. destruct Hvalid'. 
          simpl in H3. destruct (Req_dec_T p1 0). 
          --- destruct Hp1 as [Hp_]. rewrite e in Hp_. apply Rlt_irrefl in Hp_. contradiction.
          --- rewrite dst_cons_eq_add in H3. apply Valid_add_decom in H3. destruct H3. 
          apply Rplus_lt_le_0_compat. 
          ++ apply Rplus_lt_le_0_compat. 
          ** destruct H3. destruct H6. destruct H6. assumption. 
          ** apply dst_Valid_prob_0_1. assumption.
          ++ apply dst_Valid_prob_0_1. assumption. }
      specialize (Hcontra Hin'). simpl in Hcontra. destruct Hcontra as [_ Hcontra].
      rewrite Hs02 in Hcontra. contradiction.
    + destruct Hsem as [Hcase2| Hcase3]. 
      * destruct Hcase2 as [pd01 H]. destruct H as [HWF01 H].
        destruct H as [Hpdeq01 H]. apply pd_equiv_sym in Hpdeq01.
        destruct H as [Hsub H]. 
        destruct H as [Hsem01 Hsum]. destruct Hsem01 as [Hsem01 Hcontra].
        apply bT_sem_iff in Hcontra. destruct Hcontra as [_ Hcontra].
        apply dst_equiv_implies_b_classify with (b:= b) in Hpdeq01; try assumption.
        rewrite Hbclass in Hpdeq01. 
        rewrite <- Hpdeq01 in Hcontra.
         destruct Hcontra; discriminate. 
      * destruct Hcase3 as [pd01 H]. destruct H as [HWF01 H].
        destruct H as [Hpdeq01 H]. apply pd_equiv_sym in Hpdeq01.
        destruct H as [Hsub H]. 
        destruct H as [Hsem01 Hsum]. 
        apply pd_equiv_preserves_sem with (pd0:= pd01); try assumption.
        inversion HWD; subst. assumption.
Qed.

Lemma bT_sem_implies_getb_refl: forall b pd,
  [[Pdeter (Dpred b)]] pd -> get_b_in_mu b (mu pd) = mu pd.
Proof. 
  intros. destruct H as [Hsub Hsem].
  destruct pd as [dom mu HPD].
  induction mu as [|(s,p) mu' Hmu ].
  - simpl. reflexivity.
  - simpl. simpl in Hsub. 
    assert (Hst: evalB_st b s = true). 
    { simpl in Hsem. specialize (Hsem s). 
      assert (Hin: is_in_supp s (supp_mu ((s,p) :: mu')) = true). {
        unfold supp_mu. simpl. 
        rewrite insert_st_pair_fst_eq_insert_st. 
        rewrite in_supp_insert_eq.
        rewrite state_eq_refl. 
        simpl. reflexivity. }
      specialize (Hsem Hin). destruct Hsem. 
      destruct (evalB_st b s); try reflexivity; try contradiction. }
    rewrite Hst. f_equal.
    inversion HPD; subst. 
    specialize (Hmu H3). simpl in Hmu.
    apply Hmu; try assumption.
    simpl in Hsem. simpl.
    intros. apply Hsem.
    apply in_supp_mu_cons_r; try assumption.
Qed.

Lemma bF_sem_implies_getnotb_refl: forall b pd, 
  [[Pdeter (Dpred (Bnot b))]] pd -> (get_notb_in_mu b (mu pd)) = mu pd.
Proof. 
  intros. destruct H as [Hsub Hsem].
  destruct pd as [dom mu HPD].
  induction mu as [|(s,p) mu' Hmu ].
  - simpl. reflexivity.
  - simpl. simpl in Hsub. 
    assert (Hst: evalB_st b s = false). {
      simpl in Hsem. specialize (Hsem s).
      assert (Hin: is_in_supp s (supp_mu ((s,p) :: mu')) = true). {
        unfold supp_mu. simpl. 
        rewrite insert_st_pair_fst_eq_insert_st. 
        rewrite in_supp_insert_eq.
        rewrite state_eq_refl. 
        simpl. reflexivity. }
      specialize (Hsem Hin). destruct Hsem. 
      destruct (evalB_st b s); try reflexivity; try contradiction. }
    rewrite Hst. simpl. apply app_inv_head_iff with (l:= [(s,p)]).
    inversion HPD; subst. 
    specialize (Hmu H3). simpl in Hmu.
    apply Hmu; try assumption.
    simpl in Hsem. simpl.
    intros. apply Hsem.
    apply in_supp_mu_cons_r; try assumption.
Qed.

Lemma Oplus_implies_under_Mixed: 
  forall b pd phi0 phi1, 
  Valid_dist (mu pd) -> well_defined_Pf (phi0 ∧ Pdeter (Dpred b) ⊕ phi1 ∧ Pdeter (Dpred (~ b))) ->
  b_supp_classify b pd = Mixed ->
  [[phi0 ∧ Pdeter (Dpred b) ⊕ phi1 ∧ Pdeter (Dpred (~ b))]] pd ->
  [[phi0 ∧ Pdeter (Dpred b)]] (extract_b_pd b pd) /\ [[phi1 ∧ Pdeter (Dpred (~ b))]] (extract_notb_pd b pd) .
Proof. 
  intros b pd phi0 phi1 Hvalid HWD Hbclass Hsem. 
  inversion HWD; subst. rename H1 into HWD1. rename H2 into HWD2.
  destruct Hsem as [Hcase1 | Hsem]. 
    + destruct Hcase1 as [p1 H]. destruct H as [p2 H]. 
      destruct H as [Hp1 H]. destruct H as [Hp2 H]. destruct H as [Hp_eq H].
      destruct H as [pd01 H]. destruct H as [pd02 H].
      destruct H as [HWF01 H]. destruct H as [HWF02 H]. 
      destruct H as [Hdom01 H]. destruct H as [Hdom02 H].
      destruct H as [Hsem01 H]. destruct H as [Hsem02 H].
      destruct H as [Hsum0 H]. destruct H as [Hsum1 Hmu].
      assert (Hvalid': Valid_dist (p1 * mu pd01 + p2 * mu pd02)%dist_state). { 
          apply Valid_linear; try assumption. 
          - destruct Hp1. split; apply Rlt_le; assumption.
          - destruct Hp2. split; apply Rlt_le; assumption.
          - rewrite Hp_eq. apply Rle_refl. }
      destruct Hsem01 as [Hsem0 Hsme01]. destruct Hsem02 as [Hsem1 Hsme02].
      destruct pd as [dom mu HPD]. destruct pd01 as [dom01 mu0_ex HPD0]. 
      destruct pd02 as [dom02 mu1_ex HPD1].
      simpl in HWF01. simpl in HWF02. simpl in Hdom01. simpl in Hdom02.
      simpl in Hsum0. simpl in Hsum1. simpl in Hmu. simpl in Hvalid'. 
      assert (Hb_eq: (get_b_in_mu b mu == get_b_in_mu b (p1 * mu0_ex + p2 * mu1_ex))%dist_state). { 
          apply Peq_implies_get_b_Peq; try assumption. }
      assert (Hnotb_eq: (get_notb_in_mu b mu == get_notb_in_mu b (p1 * mu0_ex + p2 * mu1_ex))%dist_state). { 
          apply Peq_implies_get_notb_Peq; try assumption. }
      assert (Hmu0_ex_b_eq: get_b_in_mu b mu0_ex = mu0_ex). { 
        apply bT_sem_implies_getb_refl with (pd:= Build_partial_dist dom01 mu0_ex HPD0). assumption. }
      assert (Hmu0_ex_notb_nil: get_notb_in_mu b mu0_ex = []). {
          rewrite <- Hmu0_ex_b_eq. apply get_notb_after_get_b. }
      assert (Hmu1_ex_notb: get_notb_in_mu b mu1_ex = mu1_ex). { 
        apply bF_sem_implies_getnotb_refl with (pd:= {| dom := dom02; mu := mu1_ex; all_partial := HPD1 |}). 
        assumption. }
      assert (Hmu1_ex_b_nil: get_b_in_mu b mu1_ex = []). {
          rewrite <- Hmu1_ex_notb. 
          apply get_b_after_get_notb. } 
      rewrite get_b_assoc in Hb_eq. repeat rewrite dst_get_b_coef_mult in Hb_eq.
      rewrite Hmu1_ex_b_nil in Hb_eq. simpl in Hb_eq. rewrite dst_add_0_r in Hb_eq.
      rewrite Hmu0_ex_b_eq in Hb_eq. 
      rewrite get_notb_assoc in Hnotb_eq. repeat rewrite dst_get_notb_coef_mult in Hnotb_eq.
      rewrite Hmu0_ex_notb_nil in Hnotb_eq. simpl in Hnotb_eq. rewrite Hmu1_ex_notb in Hnotb_eq. 
      split. 
      - assert (HPD0': partial_dst_Prop dom01 (p1 * mu0_ex)). { apply PD_mult_coef; try assumption. }
        pose (pd0':= Build_partial_dist dom01 (p1 * mu0_ex) HPD0').
        assert (Hequiv0: (extract_b_pd b {| dom := dom; mu := mu; all_partial := HPD |}) ≡ pd0'). {
          split; simpl; try assumption. apply dom_equiv_sym. assumption. }
        apply pd_equiv_preserves_sem with (pd0:= pd0'); try assumption.
        * simpl. apply Valid_add_decom in Hvalid'. destruct Hvalid'. assumption.
        * simpl. apply dst_Valid_get_b. assumption.
        * assert (Hsem': [[phi0 ∧ Pdeter (Dpred b)]] {| dom := dom01; mu := mu0_ex; all_partial := HPD0 |}). {
            split; try assumption. }
          apply sem_mult_cofe with (p:= p1) in Hsem'; try assumption. 
        ** assert (Hequiv0p: pd0' ≡ 
        {|
          dom := CoreDef.dom {| dom := dom01; mu := mu0_ex; all_partial := HPD0 |};
          mu := p1 * CoreDef.mu {| dom := dom01; mu := mu0_ex; all_partial := HPD0 |};
          all_partial := pd_mult_preserve_PD {| dom := dom01; mu := mu0_ex; all_partial := HPD0 |} p1
        |} ). {
          split; simpl; try apply dst_equiv_refl. apply dom_equiv_refl.  }
        apply pd_equiv_preserves_sem with (pd1:= pd0') (phi:= phi0 ∧ Pdeter (Dpred b)) in Hequiv0p; simpl; try assumption.
        -- apply Valid_mult_cofe; try assumption. destruct Hp1. split; apply Rlt_le; assumption.
        -- apply Valid_mult_cofe; try assumption. destruct Hp1. split; apply Rlt_le; assumption.
        ** destruct Hp1. apply Rlt_le; assumption.
        ** apply Valid_add_decom in Hvalid'. destruct Hvalid'. destruct H. assumption.
      - assert (HPD1': partial_dst_Prop dom02 (p2 * mu1_ex)). { apply PD_mult_coef; try assumption. }
        pose (pd1':= Build_partial_dist dom02 (p2 * mu1_ex) HPD1').
        assert (Hequiv1: (extract_notb_pd b {| dom := dom; mu := mu; all_partial := HPD |}) ≡ pd1'). {
          split; simpl; try assumption. apply dom_equiv_sym. assumption. }
        apply pd_equiv_preserves_sem with (pd0:= pd1'); try assumption.
        * simpl. apply Valid_add_decom in Hvalid'. destruct Hvalid'. assumption.
        * simpl. apply dst_Valid_get_notb. assumption.
        * assert (Hsem': [[phi1 ∧ Pdeter (Dpred (~b))]] {| dom := dom02; mu := mu1_ex; all_partial := HPD1 |}). {
            split; try assumption. }
          apply sem_mult_cofe with (p:= p2) in Hsem'; try assumption. 
        ** assert (Hequiv1p: pd1' ≡ 
        {|
          dom := CoreDef.dom {| dom := dom02; mu := mu1_ex; all_partial := HPD1 |};
          mu := p2 * CoreDef.mu {| dom := dom02; mu := mu1_ex; all_partial := HPD1 |};
          all_partial :=
            pd_mult_preserve_PD {| dom := dom02; mu := mu1_ex; all_partial := HPD1 |} p2
        |} ). {
          split; simpl; try apply dst_equiv_refl. apply dom_equiv_refl.  }
        apply pd_equiv_preserves_sem with (pd1:= pd1') (phi:= phi1 ∧ Pdeter (Dpred (~b))) in Hequiv1p; simpl; try assumption.
        -- apply Valid_mult_cofe; try assumption. destruct Hp2. split; apply Rlt_le; assumption.
        -- apply Valid_mult_cofe; try assumption. destruct Hp2. split; apply Rlt_le; assumption.
        ** destruct Hp2. apply Rlt_le; assumption.
        ** apply Valid_add_decom in Hvalid'. destruct Hvalid'. destruct H0. assumption.
    + destruct Hsem as [Hcase2| Hcase3]. 
      * destruct Hcase2 as [pd01 H]. destruct H as [HWF01 H].
        destruct H as [Hpdeq01 H]. apply pd_equiv_sym in Hpdeq01.
        destruct H as [Hsub H]. 
        destruct H as [Hsem01 Hsum]. destruct Hsem01 as [Hsem01 Hcontra].
        apply bT_sem_iff in Hcontra. destruct Hcontra as [_ Hcontra].
        apply dst_equiv_implies_b_classify with (b:= b) in Hpdeq01; try assumption.
        rewrite Hbclass in Hpdeq01. 
        rewrite <- Hpdeq01 in Hcontra. destruct Hcontra; discriminate.
      * destruct Hcase3 as [pd01 H]. destruct H as [HWF01 H].
        destruct H as [Hpdeq01 H]. apply pd_equiv_sym in Hpdeq01.
        destruct H as [Hsub H]. 
        destruct H as [Hsem01 Hsum]. destruct Hsem01 as [Hsem01 Hcontra].
        apply bF_sem_iff in Hcontra. destruct Hcontra as [_ Hcontra].
        apply dst_equiv_implies_b_classify with (b:= b) in Hpdeq01; try assumption.
        rewrite Hbclass in Hpdeq01. 
        rewrite <- Hpdeq01 in Hcontra. destruct Hcontra; discriminate.
Qed. 

Lemma Pplus_implies_fst_under_All_true: 
  forall b Bp pd phi0 phi1, 
  Valid_dist (mu pd) -> well_defined_Pf (phi0 ∧ Pdeter (Dpred b) ⊕[ Bp] phi1 ∧ Pdeter (Dpred (~ b)))%formula ->
  b_supp_classify b pd = All_True ->
  [[phi0 ∧ Pdeter (Dpred b) ⊕[ Bp] phi1 ∧ Pdeter (Dpred (~ b))]] pd ->
  [[phi0 ∧ Pdeter (Dpred b)]] pd /\ (Bp = 1).
Proof. 
  intros b Bp pd phi0 phi1 Hvalid HWD Hbclass Hsem.
  destruct Hsem as [Hcase1 | Hsem]. 
    + destruct Hcase1 as [Hp H]. 
      destruct H as [pd01 H]. destruct H as [pd02 H].
      destruct H as [HWF01 H]. destruct H as [HWF02 H]. 
      destruct H as [Hdom01 H]. destruct H as [Hdom02 H].
      destruct H as [Hsem01 H]. destruct H as [Hsem02 H].
      destruct H as [Hsum0 H]. destruct H as [Hsum1 Hmu].
      assert (Hvalid': Valid_dist (Bp * mu pd01 + (1 - Bp) * mu pd02)%dist_state). { 
          apply Valid_linear; try assumption. 
          - destruct Hp. split; apply Rlt_le; assumption.
          - apply Rp_1_minus_p_bounds. 
            destruct Hp. split; apply Rlt_le; assumption.
          - rewrite R_plus_sub_eq_1. apply Rle_refl. }
      assert (HPD': partial_dst_Prop (dom pd) (Bp * mu pd01 + (1 - Bp) * mu pd02)%dist_state). {
        apply PD_linear; try assumption. 
        - destruct Hp. apply Rlt_le; assumption.
        - apply Rp_1_minus_p_bounds. destruct Hp. split; apply Rlt_le; assumption. }
      pose (pd_tmp:= Build_partial_dist (dom pd) (Bp * mu pd01 + (1 - Bp) * mu pd02) HPD').
      assert (Heq: pd ≡ pd_tmp). { split; simpl; try apply dom_equiv_refl. assumption. }
      destruct pd02 as [dom02 mu02 HPD02]. destruct mu02 as [|(s02, p02) mu02']. 
      * simpl in Hmu. rewrite dst_add_0_r in Hmu. 
      simpl in Hdom02. simpl in Hsum1. rewrite <- Hsum1 in Hsum0.
      assert (Hmu_nil: mu pd = []). { 
        apply sum_probs0_implies_nil; try assumption.
        apply dst_equiv_implies_sum_probs_eq in Hmu; try assumption.
        - rewrite dst_sum_prob_coef_mult in Hmu. rewrite Hsum0 in Hmu. rewrite Rmult_0_r in Hmu. assumption.
        - apply Valid_mult_cofe; try assumption. destruct Hp. split; apply Rlt_le; assumption. }
      unfold b_supp_classify in Hbclass. rewrite Hmu_nil in Hbclass. 
      discriminate Hbclass.
      * destruct Hsem02. destruct H0. simpl in H1. specialize (H1 s02).
      assert (Hin: is_in_supp s02 (supp_mu ((s02, p02) :: mu02')) = true) by apply in_supp_mu_cons_head.
      specialize (H1 Hin). destruct H1. 
      destruct (negb (evalB_st b s02)) eqn: Hs02; try contradiction.
      apply negb_true_iff in Hs02. 
      rewrite dst_equiv_implies_b_classify with (pd1:= pd_tmp) in Hbclass; try assumption.
      assert (Htmp: [[Pdeter (Dpred b)]] pd_tmp). { 
        apply bT_sem_iff. split; try assumption. 
        - unfold WF_bexp_with_pd. simpl. simpl in H0. simpl in Hdom02. 
        apply dom_subset_eq_compat_left with (Z:= (get_variables_in_bexp b)) in Hdom02; try assumption. 
        - right. assumption. }
      destruct Htmp as [Hem' Hcontra].
      specialize (Hcontra s02). 
      assert (Hin': is_in_supp s02 (supp_mu (mu pd_tmp)) = true).  {
        apply in_supp_iff_posi_prob; try assumption; try assumption.  
          pose (p':= (get_prob_in_dstate (Bp * mu pd01)%dist_state s02 + (1 - Bp) * p02 + get_prob_in_dstate ((1 - Bp) * mu02')%dist_state s02)%R).
          exists p'. simpl. destruct (Req_dec_T (1 - Bp) 0). 
          -- apply Rp_lt1_minus_p_bounds in Hp. rewrite e in Hp. destruct Hp. apply Rlt_irrefl in H3. contradiction.
          -- rewrite get_prob_decom. rewrite dst_cons_eq_add.
          rewrite get_prob_decom. simpl. rewrite state_eq_refl. 
          rewrite Rplus_0_r. rewrite <- Rplus_assoc.
          split; try reflexivity. unfold p'.
          apply Valid_add_decom in Hvalid'. destruct Hvalid'. 
          simpl in H4.  destruct (Req_dec_T (1 - Bp) 0). 
          --- apply Rp_lt1_minus_p_bounds in Hp. rewrite e in Hp. destruct Hp. apply Rlt_irrefl in H5. contradiction.
          --- rewrite dst_cons_eq_add in H4. apply Valid_add_decom in H4. destruct H4. 
          apply Rplus_lt_le_0_compat. 
          ++ apply Rplus_le_lt_0_compat. 
          ** apply dst_Valid_prob_0_1. assumption.
          ** destruct H4. destruct H6. destruct H6. assumption. 
          ++ apply dst_Valid_prob_0_1. assumption. }
      specialize (Hcontra Hin'). simpl in Hcontra. destruct Hcontra as [_ Hcontra].
      rewrite Hs02 in Hcontra. contradiction.
    + destruct Hsem as [Hcase2| Hcase3]. 
      * destruct Hcase2 as [Hp1 H]. destruct H as [pd01 H]. destruct H as [HWF01 H].
        destruct H as [Hpdeq01 H]. apply pd_equiv_sym in Hpdeq01.
        destruct H as [Hsem01 Hsum]. split; try assumption.
        apply pd_equiv_preserves_sem with (pd0:= pd01); try assumption.
        inversion HWD; subst. assumption.
      * destruct Hcase3 as [Hp1 H]. destruct H as [pd01 H]. destruct H as [HWF01 H].
        destruct H as [Hpdeq01 H]. apply pd_equiv_sym in Hpdeq01.
        destruct H as [Hsem01 Hsum]. destruct Hsem01 as [Hsem01 Hcontra].
        apply bF_sem_iff in Hcontra. destruct Hcontra as [_ Hcontra].
        apply dst_equiv_implies_b_classify with (b:= b) in Hpdeq01; try assumption.
        rewrite Hbclass in Hpdeq01. 
        rewrite <- Hpdeq01 in Hcontra. destruct Hcontra; discriminate.
Qed.

Lemma Pplus_implies_snd_under_All_false: 
  forall b Bp pd phi0 phi1, 
  Valid_dist (mu pd) -> well_defined_Pf (phi0 ∧ Pdeter (Dpred b) ⊕[ Bp] phi1 ∧ Pdeter (Dpred (~ b))) ->
  b_supp_classify b pd = All_False ->
  [[phi0 ∧ Pdeter (Dpred b) ⊕[ Bp] phi1 ∧ Pdeter (Dpred (~ b))]] pd ->
  [[phi1 ∧ Pdeter (Dpred (~ b))]] pd /\ (Bp = 0).
Proof. 
  intros b Bp pd phi0 phi1 Hvalid HWD Hbclass Hsem.
  destruct Hsem as [Hcase1 | Hsem]. 
    + destruct Hcase1 as [Hp H]. 
      destruct H as [pd01 H]. destruct H as [pd02 H].
      destruct H as [HWF01 H]. destruct H as [HWF02 H]. 
      destruct H as [Hdom01 H]. destruct H as [Hdom02 H].
      destruct H as [Hsem01 H]. destruct H as [Hsem02 H].
      destruct H as [Hsum0 H]. destruct H as [Hsum1 Hmu].
      assert (Hvalid': Valid_dist (Bp * mu pd01 + (1 - Bp) * mu pd02)%dist_state). { 
          apply Valid_linear; try assumption. 
          - destruct Hp. split; apply Rlt_le; assumption.
          - apply Rp_1_minus_p_bounds. 
            destruct Hp. split; apply Rlt_le; assumption.
          - rewrite R_plus_sub_eq_1. apply Rle_refl. }
      assert (HPD': partial_dst_Prop (dom pd) (Bp * mu pd01 + (1 - Bp) * mu pd02)%dist_state). {
        apply PD_linear; try assumption. 
        - destruct Hp. apply Rlt_le; assumption.
        - apply Rp_1_minus_p_bounds. destruct Hp. split; apply Rlt_le; assumption. }
      pose (pd_tmp:= Build_partial_dist (dom pd) (Bp * mu pd01 + (1 - Bp) * mu pd02) HPD').
      assert (Heq: pd ≡ pd_tmp). { split; simpl; try apply dom_equiv_refl. assumption. }
      destruct pd01 as [dom01 mu01 HPD01]. destruct mu01 as [|(s02, p02) mu02']. 
      * simpl in Hmu. 
        simpl in Hdom01. simpl in Hsum0. rewrite <- Hsum0 in Hsum1.
        assert (Hmu_nil: mu pd = []). { 
        apply sum_probs0_implies_nil; try assumption.
        apply dst_equiv_implies_sum_probs_eq in Hmu; try assumption.
        rewrite dst_sum_prob_coef_mult in Hmu. rewrite Hsum1 in Hmu. rewrite Rmult_0_r in Hmu. assumption. }
        unfold b_supp_classify in Hbclass. rewrite Hmu_nil in Hbclass. 
        discriminate Hbclass.
      * destruct Hsem01. destruct H0. simpl in H1. specialize (H1 s02).
      assert (Hin: is_in_supp s02 (supp_mu ((s02, p02) :: mu02')) = true) by apply in_supp_mu_cons_head.
      specialize (H1 Hin). destruct H1. 
      destruct ((evalB_st b s02)) eqn: Hs02; try contradiction.
      rewrite dst_equiv_implies_b_classify with (pd1:= pd_tmp) in Hbclass; try assumption.
      assert (Htmp: [[Pdeter (Dpred (~b))]] pd_tmp). { 
        apply bF_sem_iff. split; try assumption. 
        - unfold WF_bexp_with_pd. simpl. simpl in H0. simpl in Hdom01. 
        apply dom_subset_eq_compat_left with (Z:= (get_variables_in_bexp b)) in Hdom01; try assumption.
        - right. assumption. }
      destruct Htmp as [Hem' Hcontra].
      specialize (Hcontra s02). 
      assert (Hin': is_in_supp s02 (supp_mu (mu pd_tmp)) = true).  {
        apply in_supp_iff_posi_prob; try assumption; try assumption.  
          pose (p':= (Bp * p02 + get_prob_in_dstate (Bp * mu02')%dist_state s02 +  get_prob_in_dstate ((1 - Bp) * (mu pd02))%dist_state s02)%R).
          exists p'. simpl. destruct (Req_dec_T Bp 0). 
          -- destruct Hp. rewrite e in H3. apply Rlt_irrefl in H3. contradiction.
          -- rewrite get_prob_decom. rewrite dst_cons_eq_add.
          rewrite get_prob_decom. simpl. rewrite state_eq_refl. 
          rewrite Rplus_0_r. 
          split; try reflexivity. unfold p'.
          apply Valid_add_decom in Hvalid'. destruct Hvalid'. 
          simpl in H3. destruct (Req_dec_T Bp 0). 
          --- destruct Hp. rewrite e in H5. apply Rlt_irrefl in H5. contradiction.
          --- rewrite dst_cons_eq_add in H3. apply Valid_add_decom in H3. destruct H3. 
          apply Rplus_lt_le_0_compat. 
          ++ apply Rplus_lt_le_0_compat. 
          ** destruct H3. destruct H6. destruct H6. assumption. 
          ** apply dst_Valid_prob_0_1. assumption.
          ++ apply dst_Valid_prob_0_1. assumption. }
      specialize (Hcontra Hin'). simpl in Hcontra. destruct Hcontra as [_ Hcontra].
      rewrite Hs02 in Hcontra. contradiction.
    + destruct Hsem as [Hcase2| Hcase3]. 
      * destruct Hcase2 as [Hp1 H]. destruct H as [pd01 H]. destruct H as [HWF01 H].
        destruct H as [Hpdeq01 H]. apply pd_equiv_sym in Hpdeq01.
        destruct H as [Hsem01 Hsum]. destruct Hsem01 as [Hsem01 Hcontra].
        apply bT_sem_iff in Hcontra. destruct Hcontra as [_ Hcontra].
        apply dst_equiv_implies_b_classify with (b:= b) in Hpdeq01; try assumption.
        rewrite Hbclass in Hpdeq01. 
        rewrite <- Hpdeq01 in Hcontra.
         destruct Hcontra; discriminate. 
      * destruct Hcase3 as [Hp0 H]. destruct H as [pd01 H]. destruct H as [HWF01 H].
        destruct H as [Hpdeq01 H]. apply pd_equiv_sym in Hpdeq01.
        destruct H as [Hsem01 Hsum]. split; try assumption. 
        apply pd_equiv_preserves_sem with (pd0:= pd01); try assumption.
        inversion HWD; subst. assumption.
Qed.

Lemma Pplus_implies_under_Mixed: 
  forall b Bp pd phi0 phi1, 
  Valid_dist (mu pd) -> well_defined_Pf (phi0 ∧ Pdeter (Dpred b) ⊕[ Bp] phi1 ∧ Pdeter (Dpred (~ b))) ->
  b_supp_classify b pd = Mixed ->
  [[phi0 ∧ Pdeter (Dpred b) ⊕[ Bp] phi1 ∧ Pdeter (Dpred (~ b))]] pd ->
  [[phi0 ∧ Pdeter (Dpred b)]] (extract_b_pd b pd) /\ [[phi1 ∧ Pdeter (Dpred (~ b))]] (extract_notb_pd b pd) /\ (0 < Bp <1).
Proof. 
  intros b Bp pd phi0 phi1 Hvalid HWD Hbclass Hsem. 
  inversion HWD; subst. 
  destruct Hsem as [Hcase1 | Hsem]. 
    + destruct Hcase1 as [Hp H]. 
      destruct H as [pd01 H]. destruct H as [pd02 H].
      destruct H as [HWF01 H]. destruct H as [HWF02 H]. 
      destruct H as [Hdom01 H]. destruct H as [Hdom02 H].
      destruct H as [Hsem01 H]. destruct H as [Hsem02 H].
      destruct H as [Hsum0 H]. destruct H as [Hsum1 Hmu].
      assert (Hvalid': Valid_dist (Bp * mu pd01 + (1 - Bp) * mu pd02)%dist_state). { 
          apply Valid_linear; try assumption. 
          - apply Rp_1_minus_p_bounds. 
            destruct Hp. split; apply Rlt_le; assumption.
          - rewrite R_plus_sub_eq_1. apply Rle_refl. }
      assert (HPD': partial_dst_Prop (dom pd) (Bp * mu pd01 + (1 - Bp) * mu pd02)%dist_state). {
        apply PD_linear; try assumption. 
        - destruct Hp. apply Rlt_le; assumption.
        - apply Rp_1_minus_p_bounds. destruct Hp. split; apply Rlt_le; assumption. }
      destruct Hsem01 as [Hsem0 Hsme01]. destruct Hsem02 as [Hsem1 Hsme02].
      destruct pd as [dom mu HPD]. destruct pd01 as [dom01 mu0_ex HPD0]. 
      destruct pd02 as [dom02 mu1_ex HPD1].
      simpl in HWF01. simpl in HWF02. simpl in Hdom01. simpl in Hdom02.
      simpl in Hsum0. simpl in Hsum1. simpl in Hmu. simpl in Hvalid'. 
      assert (Hb_eq: (get_b_in_mu b mu == get_b_in_mu b (Bp * mu0_ex + (1 - Bp) * mu1_ex))%dist_state). { 
          apply Peq_implies_get_b_Peq; try assumption. }
      assert (Hnotb_eq: (get_notb_in_mu b mu == get_notb_in_mu b (Bp * mu0_ex + (1 - Bp) * mu1_ex))%dist_state). { 
          apply Peq_implies_get_notb_Peq; try assumption. }
      assert (Hmu0_ex_b_eq: get_b_in_mu b mu0_ex = mu0_ex). { 
        apply bT_sem_implies_getb_refl with (pd:= Build_partial_dist dom01 mu0_ex HPD0). assumption. }
      assert (Hmu0_ex_notb_nil: get_notb_in_mu b mu0_ex = []). {
          rewrite <- Hmu0_ex_b_eq. apply get_notb_after_get_b. }
      assert (Hmu1_ex_notb: get_notb_in_mu b mu1_ex = mu1_ex). { 
        apply bF_sem_implies_getnotb_refl with (pd:= {| dom := dom02; mu := mu1_ex; all_partial := HPD1 |}). 
        assumption. }
      assert (Hmu1_ex_b_nil: get_b_in_mu b mu1_ex = []). {
          rewrite <- Hmu1_ex_notb. 
          apply get_b_after_get_notb. } 
      rewrite get_b_assoc in Hb_eq. repeat rewrite dst_get_b_coef_mult in Hb_eq.
      rewrite Hmu1_ex_b_nil in Hb_eq. simpl in Hb_eq. rewrite dst_add_0_r in Hb_eq.
      rewrite Hmu0_ex_b_eq in Hb_eq. 
      rewrite get_notb_assoc in Hnotb_eq. repeat rewrite dst_get_notb_coef_mult in Hnotb_eq.
      rewrite Hmu0_ex_notb_nil in Hnotb_eq. simpl in Hnotb_eq. rewrite Hmu1_ex_notb in Hnotb_eq. 
      split. 
      - assert (HPD0': partial_dst_Prop dom01 (Bp * mu0_ex)). { apply PD_mult_coef; try assumption. }
        pose (pd0':= Build_partial_dist dom01 (Bp * mu0_ex) HPD0').
        assert (Hequiv0: (extract_b_pd b {| dom := dom; mu := mu; all_partial := HPD |}) ≡ pd0'). {
          split; simpl; try assumption. apply dom_equiv_sym. assumption. }
        apply pd_equiv_preserves_sem with (pd0:= pd0'); try assumption.
        * simpl. apply Valid_add_decom in Hvalid'. destruct Hvalid'. assumption.
        * simpl. apply dst_Valid_get_b. assumption.
        * assert (Hsem': [[phi0 ∧ Pdeter (Dpred b)]] {| dom := dom01; mu := mu0_ex; all_partial := HPD0 |}). {
            split; try assumption. }
          apply sem_mult_cofe with (p:= Bp) in Hsem'; try assumption. 
        ** assert (Hequiv0p: pd0' ≡ 
        {|
          dom := CoreDef.dom {| dom := dom01; mu := mu0_ex; all_partial := HPD0 |};
          mu := Bp * CoreDef.mu {| dom := dom01; mu := mu0_ex; all_partial := HPD0 |};
          all_partial := pd_mult_preserve_PD {| dom := dom01; mu := mu0_ex; all_partial := HPD0 |} Bp
        |} ). {
          split; simpl; try apply dst_equiv_refl. apply dom_equiv_refl.  }
        apply pd_equiv_preserves_sem with (pd1:= pd0') (phi:= phi0 ∧ Pdeter (Dpred b)) in Hequiv0p; simpl; try assumption.
        -- apply Valid_mult_cofe; try assumption. 
        -- apply Valid_mult_cofe; try assumption. 
        ** destruct Hp. apply Rlt_le; assumption.
        ** apply Valid_add_decom in Hvalid'. destruct Hvalid'. destruct H. assumption.
      - assert (HPD1': partial_dst_Prop dom02 ((1 - Bp) * mu1_ex)). { apply PD_mult_coef; try assumption. }
        pose (pd1':= Build_partial_dist dom02 ((1 - Bp) * mu1_ex) HPD1').
        assert (Hequiv1: (extract_notb_pd b {| dom := dom; mu := mu; all_partial := HPD |}) ≡ pd1'). {
          split; simpl; try assumption. apply dom_equiv_sym. assumption. } 
        split; try assumption.
        apply pd_equiv_preserves_sem with (pd0:= pd1'); try assumption.
        * simpl. apply Valid_add_decom in Hvalid'. destruct Hvalid'. assumption.
        * simpl. apply dst_Valid_get_notb. assumption.
        * assert (Hsem': [[phi1 ∧ Pdeter (Dpred (~b))]] {| dom := dom02; mu := mu1_ex; all_partial := HPD1 |}). {
            split; try assumption. }
          apply sem_mult_cofe with (p:= (1 - Bp)) in Hsem'; try assumption. 
        ** assert (Hequiv1p: pd1' ≡ 
        {|
          dom := CoreDef.dom {| dom := dom02; mu := mu1_ex; all_partial := HPD1 |};
          mu := (1 - Bp) * CoreDef.mu {| dom := dom02; mu := mu1_ex; all_partial := HPD1 |};
          all_partial :=
            pd_mult_preserve_PD {| dom := dom02; mu := mu1_ex; all_partial := HPD1 |} (1 - Bp)
        |} ). {
          split; simpl; try apply dst_equiv_refl. apply dom_equiv_refl.  }
        apply pd_equiv_preserves_sem with (pd1:= pd1') (phi:= phi1 ∧ Pdeter (Dpred (~b))) in Hequiv1p; simpl; try assumption.
        -- apply Valid_mult_cofe; try assumption. apply Rp_1_minus_p_bounds. destruct Hp. split; apply Rlt_le; assumption.
        -- apply Valid_mult_cofe; try assumption. apply Rp_1_minus_p_bounds. destruct Hp. split; apply Rlt_le; assumption.
        ** apply Rp_1_minus_p_bounds. destruct Hp. split; apply Rlt_le; assumption.
        ** apply Valid_add_decom in Hvalid'. destruct Hvalid'. destruct H0. assumption.
    + destruct Hsem as [Hcase2| Hcase3]. 
      * destruct Hcase2 as [Hp1 H]. destruct H as [pd01 H]. destruct H as [HWF01 H].
        destruct H as [Hpdeq01 H]. apply pd_equiv_sym in Hpdeq01.
        destruct H as [Hsem01 Hsum]. destruct Hsem01 as [Hsem01 Hcontra].
        apply bT_sem_iff in Hcontra. destruct Hcontra as [_ Hcontra].
        apply dst_equiv_implies_b_classify with (b:= b) in Hpdeq01; try assumption.
        rewrite Hbclass in Hpdeq01. 
        rewrite <- Hpdeq01 in Hcontra. destruct Hcontra; discriminate.
      * destruct Hcase3 as [Hp0 H]. destruct H as [pd01 H]. destruct H as [HWF01 H].
        destruct H as [Hpdeq01 H]. apply pd_equiv_sym in Hpdeq01.
        destruct H as [Hsem01 Hsum]. destruct Hsem01 as [Hsem01 Hcontra].
        apply bF_sem_iff in Hcontra. destruct Hcontra as [_ Hcontra].
        apply dst_equiv_implies_b_classify with (b:= b) in Hpdeq01; try assumption.
        rewrite Hbclass in Hpdeq01. 
        rewrite <- Hpdeq01 in Hcontra. destruct Hcontra; discriminate.
Qed. 