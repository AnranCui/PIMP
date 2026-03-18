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

Require Import Library.UtilityQR.
Require Import Library.DistState.CoreDef.
Require Import Library.DistState.Domain.
Require Import Library.DistState.ValidDst.
Require Import Library.DistState.Support.
Require Import Library.DistState.Arithmetic.
Require Import Library.DistState.Combine.
Require Import Library.DistState.Restrict.

Open Scope list_scope.
Open Scope R_scope.
Open Scope dstate_scope.

Lemma res_bulid_helper_implies_Peq: forall ss ps mu X, (*Restrict 到域 X 后是单点分布（按 ss 聚合）*)
  (bulid_helper ss ps mu X) \| X == [(ss, ((get_prob_in_dstate (mu \| X) ss) * ps))%R].
Proof.
  intros ss ps mu X. generalize dependent X. generalize dependent ss.
  induction mu as [|(s, p) mu IH]; simpl; intros; try assumption.
  - rewrite Rmult_0_l. unfold dst_equiv. intros. simpl. 
    destruct (beq_state s ss) eqn: Hst; try reflexivity. rewrite Rplus_0_l. reflexivity.
  - destruct (beq_state ss (res_st_to_X s X)) eqn: Hst. 
    + simpl. apply dst_equiv_trans with 
              (mu1:= [(ss, (p * ps)%R)] + [(ss, ((get_prob_in_dstate (mu \| X) ss) * ps)%R)]).
      * rewrite dst_cons_eq_add. apply dst_add_preserves_equiv. 
      -- apply Peq_one_st. split; try apply Rmult_comm. 
      rewrite state_eq_sym. assumption.
      -- apply IH.
      * simpl. unfold dst_equiv. intros. simpl. 
        destruct (beq_state s0 ss) eqn: Hst0; try reflexivity.
        repeat rewrite Rplus_0_r. rewrite Rmult_plus_distr_r. reflexivity.
    + apply IH; try assumption.
Qed.

Lemma bulid_res_implies_Peq: forall mu_sub mu X,  (* Restrict 回 X 得到原来的 \mu_{\text{sub}}*)
  Valid_dist mu ->
  Valid_dist mu_sub ->
  is_supp_subset (supp_mu mu_sub) (supp_mu (mu \| X)) = true ->
  (bulid_dst_sub mu_sub mu X) \| X == mu_sub.
Proof.
  intros mu_sub mu X HWF HWFS Hsupp. generalize dependent X. generalize dependent mu.
  induction mu_sub as [|(ss, ps) mus' IH]; simpl; intros; try assumption.
  - apply dst_equiv_refl.
  - rewrite res_add_decom_eq. rewrite res_dst_to_X_mult_coef. 
  rewrite dst_cons_eq_add. apply dst_add_preserves_equiv.
    + assert (Htemp: is_in_supp ss (supp_mu (mu \| X)) = true). {
        apply in_supp_r_if_subset with (ls0:= supp_mu ((ss, ps) :: mus')); try assumption. 
        unfold supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st.
        rewrite in_supp_insert_eq. apply orb_true_iff. left. 
        apply state_eq_refl. }
    apply in_supp_iff_posi_prob in Htemp. 
    * destruct Htemp. destruct H. rewrite <- H0 in H. 
      apply dst_equiv_trans with (mu1:= / get_prob_in_dstate (mu \| X) ss * [(ss, ((get_prob_in_dstate (mu \| X) ss) * ps))%R] ).
      -- apply dst_mult_preserves_equiv. apply res_bulid_helper_implies_Peq.
      -- simpl. apply Rlt_gt in H. apply Rgt_not_eq in H. 
      destruct (Req_dec_T (/ get_prob_in_dstate (mu \| X) ss) 0) eqn: Hss. 
      ** apply Rinv_neq_0_compat in H.
      rewrite e in H. contradiction.
      ** rewrite <- Rmult_assoc. rewrite <- Rinv_l_sym; try assumption.
      apply Peq_one_st. split; try apply state_eq_refl. rewrite Rmult_1_l. reflexivity.
    * apply Valid_after_resX. assumption.
      + apply IH; try assumption.  
      -- apply Valid_dist_inv in HWFS. assumption.
      -- unfold supp_mu at 1 in Hsupp. simpl in Hsupp. 
      rewrite insert_st_pair_fst_eq_insert_st in Hsupp.
      unfold supp_mu in Hsupp. 
      apply supp_subset_insert_implies_subset in Hsupp; try assumption.
      ++ apply Sort_supp_if_WF_supp. 
      ++ apply Sort_supp_if_WF_supp.
Qed.

(*******************************************)
Lemma sum_probs_bulid_helper_le: forall ss ps mu X,  (*总质量不增*)
  prob_is_positive ps -> 
  Valid_dist mu ->
  sum_probs (bulid_helper ss ps mu X) <= sum_probs mu.
Proof.
  intros ss ps mu X Hps HV. induction mu as [|(s,p) mu' IH].
  - simpl. apply Rle_refl.
  - simpl. destruct (beq_state ss (res_st_to_X s X)) eqn: Hs.
    + simpl. apply Rplus_le_compat. 
      * rewrite <- Rmult_1_l with (r:= p) at 2. apply Rmult_le_compat_r.
      ** destruct HV. destruct H0. destruct H0. apply Rlt_le. assumption.
      ** destruct Hps. assumption.
      * apply IH. apply Valid_dist_inv in HV. assumption.
    + apply Rle_trans with (r2:= sum_probs mu'); try assumption. 
      * apply IH. apply Valid_dist_inv in HV. assumption.
      * rewrite <- Rplus_0_l at 1. apply Rplus_le_compat_r.
      destruct HV. destruct H0. destruct H0. apply Rlt_le. assumption.
Qed. 

Lemma Valid_after_bulid_helper: forall ss ps mu X, (*有效性保持*)
  Valid_dist mu -> 
  prob_is_positive ps -> 
  Valid_dist (bulid_helper ss ps mu X).
Proof.
  intros ss ps mu X HVD HP. induction mu as [|(s,p) mu' IH].
  - simpl. apply HVD. 
  - split. 
    + split. 
      * simpl. destruct (beq_state ss (res_st_to_X s X)) eqn: Hs.
      ** simpl. apply Rplus_le_le_0_compat. 
      -- destruct HVD. destruct H0. destruct H0. destruct HP.
      apply Rlt_le. apply Rmult_lt_0_compat; try assumption.
      -- apply IH. apply Valid_dist_inv in HVD. assumption.
      ** apply Valid_dist_inv in HVD. apply IH in HVD. destruct HVD. destruct H. assumption.
      * apply Rle_trans with (r2:= sum_probs ((s,p)::mu')); try assumption.
      ** apply sum_probs_bulid_helper_le; try assumption.
      ** destruct HVD. destruct H. assumption.
    + simpl. destruct (beq_state ss (res_st_to_X s X)) eqn: Hs.
      * simpl. split.
      ** apply Valid_dist_conj in HVD. destruct HVD. destruct H. destruct H1. destruct H1.
      destruct HP. split. 
      -- apply Rmult_lt_0_compat; try assumption.
      -- rewrite <- Rmult_1_l with (r:= 1). destruct H. simpl in H.
      apply Rmult_le_compat; try assumption; try apply Rlt_le; assumption.
      ** apply IH. apply Valid_dist_inv in HVD. assumption.
      * apply IH. apply Valid_dist_inv in HVD. assumption.
Qed.


Lemma bulid_nil: forall ss ps mu X,
  Valid_dist mu ->
  get_prob_in_dstate (mu \| X) ss = 0 -> 
  bulid_helper ss ps mu X = [].
Proof.
  intros ss ps mu X HV H. induction mu as [| (s,p) mu' IH]; simpl; intros; try reflexivity.
  simpl in *. destruct (beq_state ss (res_st_to_X s X)) eqn: Hs.
  - apply Valid_dist_conj in HV. destruct HV. destruct H0. destruct H2. destruct H2.
  apply Valid_after_resX with (X:= X) in H1. 
  apply dst_Valid_prob_0_1 with (s:= ss) in H1. destruct H1.
  rewrite <- H in H1. rewrite <- Rplus_0_l in H1. apply Rplus_le_reg_r in H1.
  apply Rle_not_lt in H1. unfold not in H1. apply H1 in H2. contradiction.
  - apply IH; try assumption. apply Valid_dist_inv in HV. assumption.
Qed.


Lemma sum_probs_bulid_helper_eq: forall ss ps mu X, (*点概率精确公式*)
  Valid_dist mu -> prob_is_positive ps -> 
  sum_probs (bulid_helper ss ps mu X) = ((get_prob_in_dstate (mu \| X) ss)*ps)%R.
Proof.
  intros ss ps mu X HWF Hpos. 
  destruct (Req_dec (get_prob_in_dstate (mu \| X) ss) 0) eqn: Hprob.
  { rewrite bulid_nil; simpl; try assumption.
    rewrite e. rewrite Rmult_0_l. reflexivity. }
  assert (Hmu: (bulid_helper ss ps mu X) \| X == 
                [(ss, ((get_prob_in_dstate (mu \| X) ss) * ps))%R]) by apply res_bulid_helper_implies_Peq.
  apply dst_equiv_implies_sum_probs_eq in Hmu; try assumption.
  - simpl in Hmu. rewrite Rplus_0_r in Hmu. rewrite <- Hmu.
    rewrite <- sum_eq_after_res. reflexivity.
  - apply Valid_after_resX. apply Valid_after_bulid_helper; try assumption.
  - apply Valid_after_resX with (X:= X) in HWF. 
    apply dst_Valid_prob_0_1 with (s:= ss) in HWF.
    destruct HWF. destruct Hpos. 
    assert (Hr: ((get_prob_in_dstate (mu \| X) ss) * ps <= 1)%R). {
      rewrite <- Rmult_1_l. 
      apply Rmult_le_compat; try assumption; try apply Rle_refl.
      apply Rlt_le. assumption. }
    assert (Hl: (0 <= (get_prob_in_dstate (mu \| X) ss) * ps)%R). {
      rewrite <- Rmult_0_l with (r:=0). 
      apply Rmult_le_compat; try assumption; try apply Rle_refl.
      apply Rlt_le. assumption. }
    split.
      * simpl. rewrite Rplus_0_r. split; try assumption.
      * split; simpl; try apply I. split; try assumption.
      destruct Hl; try assumption. apply Rlt_not_eq in H1.
      symmetry in H3. apply Rmult_integral in H3. destruct H3; subst.
      ** assert (Hcontra: get_prob_in_dstate (mu \| X) ss <> 0) by assumption.
      rewrite H3 in Hcontra. unfold not in Hcontra. exfalso. apply Hcontra. reflexivity.
      ** unfold not in H1. exfalso. apply H1. reflexivity.
Qed.

Lemma sum_probs_bulid: forall mu_sub mu X, (*总概率质量保持（build 不改变 sum_probs）*)
  Valid_dist mu_sub -> Valid_dist mu ->
  is_supp_subset (supp_mu mu_sub) (supp_mu (mu \| X)) = true ->
  sum_probs (bulid_dst_sub mu_sub mu X) = sum_probs mu_sub.
Proof. 
  intros mu_sub mu X HWFsub HWF Hsupp.
  generalize dependent mu. induction mu_sub as [|(ss,ps) mu_sub' IH]; intros.
  - simpl. reflexivity.
  - simpl. 
    assert (HW_copy: Valid_dist ((ss, ps) :: mu_sub')) by assumption.
    apply Valid_dist_conj in HWFsub. destruct HWFsub. 
    assert (Hnot: get_prob_in_dstate (mu \| X) ss <> 0). {
      unfold supp_mu at 1 in Hsupp. simpl in Hsupp.
      rewrite insert_st_pair_fst_eq_insert_st in Hsupp.
      apply supp_subset_insert_implies_subset_onest in Hsupp; try assumption.
      - apply in_supp_if_supp_subset_onest in Hsupp. apply in_supp_iff_posi_prob in Hsupp. 
        + destruct Hsupp. destruct H1. rewrite H2. apply Rgt_not_eq. assumption.
        + apply Valid_after_resX. assumption.
      - apply Sort_supp_if_WF_supp. 
      - apply Sort_supp_if_WF_supp. 
    }
    rewrite dst_sum_prob_decom. rewrite dst_sum_prob_coef_mult.
    rewrite sum_probs_bulid_helper_eq; try assumption.
    + rewrite <- Rmult_assoc. rewrite <- Rinv_l_sym; try assumption. 
      rewrite Rmult_1_l. f_equal. apply IH; try assumption. 
      apply supp_subset_trans with (ls1:= (supp_mu ((ss, ps) :: mu_sub'))); try assumption.
      * apply Sort_supp_if_WF_supp. 
      * apply Sort_supp_if_WF_supp. 
      * apply Sort_supp_if_WF_supp. 
      * apply supp_mu_subset_cons; try assumption.
    + destruct H. destruct H1. apply H1. 
Qed. 

Lemma supp_subset_bulid_helper: forall ss ps mu X,  (*支持集包含关系：helper 的支持属于原支持*)
  Valid_dist mu -> prob_is_positive ps ->
  is_supp_subset (supp_mu (bulid_helper ss ps mu X)) (supp_mu mu) = true.
Proof.
  intros ss ps mu X HWF Hpos. induction mu as [|(s,p) mu' IH].
  - simpl. reflexivity.
  - simpl. destruct (beq_state ss (res_st_to_X s X)) eqn: Hs. 
    + unfold supp_mu. simpl. repeat rewrite insert_st_pair_fst_eq_insert_st. 
    apply supp_subset_insert_compat; try assumption.
      * apply Sort_supp_if_WF_supp. 
      * apply Sort_supp_if_WF_supp.
      * apply IH. apply Valid_dist_conj in HWF. destruct HWF.  assumption.
    + assert (Htemp:is_supp_subset (supp_mu (bulid_helper ss ps mu' X)) (supp_mu mu') = true). { 
        apply Valid_dist_inv in HWF. apply IH in HWF. assumption. }
      apply supp_subset_trans with (ls1:= (supp_mu mu') ); try assumption.
      * apply Sort_supp_if_WF_supp. 
      * apply Sort_supp_if_WF_supp. 
      * apply Sort_supp_if_WF_supp. 
      * apply supp_mu_subset_cons. 
Qed.

Lemma WF_after_add: forall mu mu1 mu2,
  Valid_dist mu -> Valid_dist mu1 -> Valid_dist mu2 ->
  mu == mu1 + mu2 -> 
  (sum_probs mu = sum_probs mu1 + sum_probs mu2)%R ->
  Valid_dist (mu1 + mu2).
Proof.
  intros. split.
  - destruct H. rewrite dst_sum_prob_decom. rewrite <- H3. assumption.
  - destruct H0; destruct H1. apply dst_positive_decom. split; try assumption.
Qed.
Lemma posi_coef_two_lt: forall p0 p1 (mu:dist_state), 
  (p0 < p1)%R -> (0 < p0)%R -> 
  positive_probs (p1*mu)%dist_state -> 
  positive_probs (p0*mu)%dist_state.
Proof.
  intros p0 p1 mu Hp Hp0 Hmu.
  induction mu as [|(s,p) mu' IH]; simpl; try apply I.
  destruct (Req_dec_T p0 0 ) eqn: Hp00; simpl; try apply I.
  simpl in Hmu. destruct (Req_dec_T p1 0 ) eqn: Hp10.
  - rewrite e in Hp. 
    assert (Hcontra: 0 < 0). {
      apply Rlt_trans with (r2:= p0); try assumption. }
    apply Rlt_irrefl in Hcontra. contradiction.
  - destruct Hmu. apply IH in H0. split; try assumption.
    destruct H. 
    destruct (Rle_or_lt p 0) eqn: H'. 
    + destruct r. 
      * assert (Hcontra: (p1*p < p1*0)%R). {
          apply Rmult_lt_compat_l; try assumption.
          apply Rlt_trans with (r2:= p0); try assumption. }
        rewrite  Rmult_0_r in Hcontra. 
        apply Rlt_trans with (r1:= 0) in Hcontra; try assumption.
        apply Rlt_irrefl in Hcontra. contradiction.
      * rewrite e in H. rewrite  Rmult_0_r in H. 
        apply Rlt_irrefl in H. contradiction.
    + split. 
      * apply Rmult_lt_0_compat; try assumption.
      * apply Rle_trans with (r2:= (p1*p)%R); try assumption.
      apply Rmult_lt_compat_r with (r:= p) in Hp; try assumption.
      apply Rlt_le; assumption.
Qed.
Lemma posi_bulid_helper: forall ss ps mu X, 
  Valid_dist mu -> prob_is_positive ps ->
  positive_probs (/ get_prob_in_dstate (mu \| X) ss * bulid_helper ss ps mu X).
Proof.
  intros ss ps mu X HWF Hps. 
  induction mu as [|(s0, p0) mu' IH]; intros; try apply I.
  simpl in *. destruct (beq_state ss (res_st_to_X s0 X)) eqn: Hs.
  - simpl. 
    assert (Hp0: 0 < p0). { 
        apply Valid_dist_conj in HWF. destruct HWF.
        destruct H. destruct H1. destruct H1. assumption. }
    assert (Hgt0X: 0 <= get_prob_in_dstate (mu' \| X) ss). {
        apply Valid_dist_conj in HWF. destruct HWF.
        destruct H. destruct H1. destruct H1. 
        apply Valid_after_resX with (X:= X) in H0.
        apply dst_Valid_prob_0_1 with (s:= ss) in H0. 
        destruct H0. assumption. }
    assert (Hgt0: 0 < p0 + get_prob_in_dstate (mu' \| X) ss). {
        apply Valid_dist_conj in HWF. destruct HWF.
        destruct H. destruct H1. destruct H1. 
        apply Valid_after_resX with (X:= X) in H0.
        apply dst_Valid_prob_0_1 with (s:= ss) in H0. 
        destruct H0. apply Rplus_lt_le_0_compat; try assumption. }
    assert (Hprob: (p0 + get_prob_in_dstate (mu' \| X) ss <> 0)%R). { apply Rgt_not_eq. apply Hgt0. }
    destruct (Req_dec_T (/ (p0 + get_prob_in_dstate (mu' \| X) ss)) 0) eqn: Hp.
    + apply Rinv_neq_0_compat in Hprob. rewrite e in Hprob. contradiction.
    + simpl. split.
      * split. 
      ** apply Rmult_lt_0_compat.
      ++ apply Rinv_0_lt_compat. assumption. 
      ++ apply Valid_dist_conj in HWF. destruct HWF.
        destruct H. destruct H1. destruct H1. destruct Hps.
        apply Rmult_lt_0_compat; assumption.
      ** apply Rmult_le_reg_l with (r:= (p0 + get_prob_in_dstate (mu' \| X) ss)%R); try assumption.
      rewrite <- Rmult_assoc. rewrite Rinv_r; try assumption.
      rewrite Rmult_1_l. rewrite Rmult_1_r.
      apply Rle_trans with (r2:= (1*p0)%R).
      -- apply Valid_dist_conj in HWF. destruct HWF.
        destruct H. destruct H1. destruct H1. 
        destruct Hps. apply Rmult_le_compat_r; try assumption. apply Rlt_le; assumption.
      -- rewrite Rmult_1_l. rewrite <- Rplus_0_r at 1. apply Rplus_le_compat_l; try assumption.
      * destruct (Req_dec (get_prob_in_dstate (mu' \| X) ss) 0) eqn: Hprob'.
      ++ apply Valid_dist_conj in HWF. destruct HWF. 
        rewrite bulid_nil; try assumption.
        simpl. apply I.
      ++ apply Valid_dist_inv in HWF. apply IH in HWF.
      apply posi_coef_two_lt with (p0:= / (p0 + get_prob_in_dstate (mu' \| X) ss)) in HWF; try assumption.
      -- apply Rinv_lt_contravar.
      ** apply Rmult_lt_0_compat; try assumption. 
      destruct Hgt0X; try assumption. 
      assert (Hcontra: get_prob_in_dstate (mu' \| X) ss <> 0) by assumption.
      rewrite<- H in Hcontra. contradiction.
      ** rewrite <- Rplus_0_l at 1.
      apply Rplus_lt_compat_r. assumption.
      -- apply Rinv_0_lt_compat. assumption. 
  - apply IH. apply Valid_dist_inv in HWF. assumption.
Qed.
Lemma WF_dist_after_bulid_mu: forall mu_sub mu X, 
  Valid_dist mu_sub -> Valid_dist mu ->
  is_supp_subset (supp_mu mu_sub) (supp_mu (mu \| X)) = true ->
  Valid_dist (bulid_dst_sub mu_sub mu X).
Proof.
  intros mu_sub mu X HWFsub HWF Hsub. 
  induction mu_sub as [|(ss,ps) mu_sub' IH]; intros.
  - simpl. assumption.
  - assert (HWinv: Valid_dist mu_sub'). {apply Valid_dist_inv in HWFsub. assumption. }
    assert (HVinv: Sorted_supp (supp_mu mu_sub')). { apply Sort_supp_if_WF_supp. }
    assert (Hps: prob_is_positive ps). { destruct HWFsub. destruct H0. assumption. }
    assert (HVX: Valid_dist (mu \| X)). {apply Valid_after_resX. assumption. }
    assert (HSspX: Sorted_supp (supp_mu (mu \| X))). { apply Sort_supp_if_WF_supp.  }
    assert (HWFX: Valid_dist (mu \| X)). { apply Valid_after_resX. assumption. } 
    split. { 
      simpl. destruct (Req_dec (get_prob_in_dstate (mu \| X) ss) 0) eqn: Hprob.
      - rewrite bulid_nil; try assumption. 
        + simpl. apply IH; try assumption. 
        apply supp_mu_subset_conj_mu in Hsub; try assumption.
        destruct Hsub. assumption.
      - rewrite dst_sum_prob_decom. rewrite dst_sum_prob_coef_mult.
        rewrite sum_probs_bulid_helper_eq; try assumption.
        rewrite <- Rmult_assoc. 
        rewrite <- Rinv_l_sym with (r:= get_prob_in_dstate (mu \| X) ss); try assumption.
        rewrite Rmult_1_l.
        assert (HWF_copy: Valid_dist ((ss, ps) :: mu_sub')) by assumption. 
        destruct HWFsub. simpl in H. 
        rewrite sum_probs_bulid; try assumption. 
        apply supp_mu_subset_conj_mu in Hsub; try assumption.
        destruct Hsub. assumption. }
      simpl. apply dst_positive_decom. split.
          * apply posi_bulid_helper; try assumption.
          * apply IH; try assumption. 
          apply supp_mu_subset_conj_mu in Hsub; try assumption.
          destruct Hsub. assumption. 
Qed.

Lemma bulid_supp_subset: forall mu_sub mu X,  (*支持集包含关系：build 的支持属于原支持*)
  Valid_dist mu -> Valid_dist mu_sub ->
  is_supp_subset (supp_mu mu_sub) (supp_mu (mu \| X)) = true ->
  is_supp_subset (supp_mu (bulid_dst_sub mu_sub mu X)) (supp_mu mu) = true.
Proof.
  intros mu_sub mu X HWF HWFS Hsub. generalize dependent X. generalize dependent mu.
  induction mu_sub as [|(ss, ps) mus' IH]; intros; try assumption.
  - unfold supp_mu. simpl. apply supp_subset_nil_l.
  - assert (HWFmus': Valid_dist mus'). { 
      apply Valid_dist_inv in HWFS. assumption. }
    assert (HSsp: Sorted_supp (supp_mu mu)). {
        apply Sort_supp_if_WF_supp; try assumption. }
    assert (HSmus': Sorted_supp (supp_mu mus')). {
        apply Sort_supp_if_WF_supp. }
    assert (HS: Sorted_supp (supp_mu ((ss, ps) :: mus'))). {
        apply Sort_supp_if_WF_supp. }
    assert (HSX: Sorted_supp (supp_mu (mu \| X))). { 
        apply Sort_supp_if_WF_supp. }
    assert (Hsub': is_supp_subset (supp_mu mus') (supp_mu (mu \| X)) = true). { 
        apply supp_subset_trans with (ls1:= supp_mu ((ss, ps) :: mus')); try assumption.
        apply supp_mu_subset_cons. }
    destruct (Req_dec (get_prob_in_dstate (mu \| X) ss) 0) eqn: H'. 
      { assert (Htemp: bulid_helper ss ps mu X = []). { 
          apply bulid_nil; try assumption. }
        simpl. rewrite Htemp. simpl. 
        apply IH; try assumption. }
      assert (HWFbulid: Valid_dist (bulid_dst_sub ((ss, ps) :: mus') mu X)).
        { apply WF_dist_after_bulid_mu; try assumption. }
      simpl. simpl in HWFbulid.
      apply supp_mu_subset_add_l; try assumption.
      + split. 
      ++ rewrite <- supp_eq_mult_coef. 
      * apply supp_subset_bulid_helper; try assumption. 
      destruct HWFS. destruct H0. assumption.
      * apply Rinv_0_lt_compat. apply Valid_after_resX with(X:= X) in HWF.
      apply dst_Valid_prob_0_1 with (s:=ss) in HWF. 
      destruct HWF. destruct H; try assumption. 
      assert (Hcontra: get_prob_in_dstate (mu \| X) ss <> 0) by assumption.
      rewrite <- H in Hcontra. contradiction.
      ++ apply IH; try assumption. 
Qed.



Lemma bulid_helper_correct :
  forall ss ps mu X s,
    (ss == (res_st_to_X s X))%state ->
    get_prob_in_dstate (bulid_helper ss ps mu X) s =
    (ps * (get_prob_in_dstate mu s))%R.
Proof. 
  intros ss ps mu X s Hsupp. generalize dependent ss.
  induction mu as [|(s', p) mu' IH]; intros. 
  - simpl. rewrite Rmult_0_r. reflexivity.
  - simpl. destruct (beq_state s s') eqn: Hs. 
    + assert (H': beq_state ss (res_st_to_X s' X) = true). { 
        apply st_eq_implies_res_X_eq with (X:= X) in Hs. 
        apply state_eq_trans with (s1:= res_st_to_X s X); try assumption. }
    rewrite H'. simpl. rewrite Hs. rewrite Rmult_plus_distr_l. f_equal. 
    apply IH. assumption.
    + destruct (beq_state ss (res_st_to_X s' X)) eqn: H'. 
      * simpl. rewrite Hs. apply IH. assumption.
      * apply IH. assumption.
Qed.

Lemma get_probs_res_iff: forall mu s X,
  Valid_dist mu ->
  get_prob_in_dstate (mu \| X) (res_st_to_X s X) = 0 ->
    get_prob_in_dstate mu s = 0.
Proof.
  intros mu s X. intros HWF H. 
  induction mu as [|(s0, p0) mu' IH]; simpl; intros; try reflexivity.
  destruct (beq_state s s0) eqn: Hs.
    + apply st_eq_implies_res_X_eq with (X:= X) in Hs.
    simpl in H. rewrite Hs in H. 
    apply Valid_dist_conj in HWF. destruct HWF. destruct H0. 
    destruct H2. destruct H2.
    apply Valid_after_resX with (X:= X) in H1.
    apply dst_Valid_prob_0_1 with (s:= (res_st_to_X s X)) in H1. destruct H1.
    rewrite <- H in H1. rewrite <- Rplus_0_l in H1. apply Rplus_le_reg_r in H1.
    apply Rle_not_lt in H1. unfold not in H1. apply H1 in H2. contradiction.
    + simpl in *. destruct (beq_state (res_st_to_X s X) (res_st_to_X s0 X)) eqn: HsX.
      * apply Valid_dist_conj in HWF. destruct HWF. destruct H0. 
      destruct H2. destruct H2.
      apply Valid_after_resX with (X:= X) in H1.
      apply dst_Valid_prob_0_1 with (s:= (res_st_to_X s X)) in H1. destruct H1.
      rewrite <- H in H1. rewrite <- Rplus_0_l in H1. apply Rplus_le_reg_r in H1.
      apply Rle_not_lt in H1. unfold not in H1. apply H1 in H2. contradiction.
      * apply IH; try assumption. apply Valid_dist_inv in HWF. assumption.
Qed.

Lemma notinsupp: forall ss ps s mu X,
  res_st_to_X s X != ss -> 
  is_in_supp s (supp_mu (bulid_helper ss ps mu X)) = false.
Proof.
  intros ss ps s mu X H.
  induction mu as [|(s0, p0) mu' IH]; simpl; intros; try reflexivity.
  destruct (beq_state ss (res_st_to_X s0 X)) eqn: Hs; try assumption.
  unfold supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st.
  rewrite in_supp_insert_eq. apply orb_false_iff. split; try assumption.
  destruct (beq_state s s0) eqn: Hs0; try reflexivity.
  apply st_eq_implies_res_X_eq with (X:= X) in Hs0. 
  apply state_eq_compat_left with (s:= ss) in Hs0.
  rewrite Hs in Hs0. rewrite state_eq_sym in H.
  rewrite Hs0 in H. discriminate.
Qed.


Lemma res_bulid_Peq: forall mu_sub s mu X,  (*点概率闭式：按投影类做“条件化再加权”*)
  Valid_dist mu -> Valid_dist mu_sub ->
  is_supp_subset (supp_mu mu_sub) (supp_mu (mu \| X)) = true ->
  get_prob_in_dstate (bulid_dst_sub mu_sub mu X) s = 
  ((/get_prob_in_dstate (mu \| X) (res_st_to_X s X)) * 
      (get_prob_in_dstate mu_sub (res_st_to_X s X)) * (get_prob_in_dstate mu s))%R.
Proof.
  intros mu_sub s mu X HWF HWFsub Hsub. generalize dependent mu. 
  induction mu_sub as [|(ss0, ps0) mus' IH]; intros. 
  - simpl in *. rewrite Rmult_0_r. rewrite Rmult_0_l. reflexivity.
  - assert (HWFbulid: Valid_dist (bulid_dst_sub ((ss0, ps0) :: mus') mu X)). { 
      apply WF_dist_after_bulid_mu; try assumption. }
    assert (HSsub: Sorted_supp (supp_mu (bulid_dst_sub ((ss0, ps0) :: mus') mu X))). {
        apply Sort_supp_if_WF_supp. }
    assert (HSsp: Sorted_supp (supp_mu mu)). { apply Sort_supp_if_WF_supp. }
    assert (HWFX: Valid_dist (mu \| X)). { apply Valid_after_resX. assumption. }
    assert (HWF': Valid_dist mus'). { apply Valid_dist_inv in HWFsub. assumption. }
    assert (Hsubinv: is_supp_subset (supp_mu mus') (supp_mu (mu \| X)) = true). 
      { apply supp_mu_subset_conj_mu in Hsub; try assumption.
        destruct Hsub. assumption. }
    destruct (Req_dec (get_prob_in_dstate (mu \| X) (res_st_to_X s X)) 0) eqn: Hnot.
    + assert (Htemp: get_prob_in_dstate mu s = 0). { 
        apply get_probs_res_iff with (X:= X); try assumption. }
      assert (Htmp': get_prob_in_dstate (bulid_dst_sub ((ss0, ps0) :: mus') mu X) s = 0). {
        apply not_insupp_iff_probs_0 in Htemp; try assumption.
        apply not_in_supp_l_if_subset with (ls0:= supp_mu ((bulid_dst_sub ((ss0, ps0) :: mus') mu X))) in Htemp; try assumption.
          - apply not_insupp_iff_probs_0; try assumption. 
          - apply bulid_supp_subset; try assumption. }
      rewrite Htemp. rewrite Htmp'. rewrite Rmult_0_r. reflexivity.
    + simpl. destruct (beq_state (res_st_to_X s X) ss0) eqn: Hs.
      * rewrite get_prob_decom. rewrite get_prob_coef_mult. 
      rewrite state_eq_sym in Hs.
      rewrite bulid_helper_correct; try assumption.
      rewrite Rmult_plus_distr_l. rewrite Rmult_plus_distr_r. f_equal.
      ** apply st_eq_get_prob_compat with (mu:= mu\|X) in Hs. rewrite <- Hs. 
      rewrite <- Rmult_assoc. reflexivity.
      ** apply IH; try assumption. 
      * rewrite get_prob_decom. rewrite get_prob_coef_mult.
      assert (Htemp: get_prob_in_dstate (bulid_helper ss0 ps0 mu X) s = 0). { 
        apply not_insupp_iff_probs_0.
        - apply Valid_after_bulid_helper; try assumption. 
        destruct HWFsub. destruct H0. assumption.
        - apply notinsupp. assumption.  }
      rewrite Htemp. rewrite Rmult_0_r. rewrite Rplus_0_l. apply IH; try assumption.
Qed.

Lemma Peq_implies_res_bulid_Peq: forall mu mu1 X,  (*“build” 作为 \|X 的右逆（以及线性/可加性）*)
  Valid_dist mu -> Valid_dist mu1 ->
  mu1 == mu \| X -> 
  (bulid_dst_sub mu1 mu X) == mu.
Proof.
  intros mu mu1 X HWF HWF1 H. unfold dst_equiv. intros.
  assert (HWFX: Valid_dist (mu \| X)). { apply Valid_after_resX. assumption. }
  assert (Hsub: is_supp_subset (supp_mu mu1) (supp_mu (mu \| X)) = true). {
    apply dst_equiv_implies_beq_supp in H; try assumption. 
    apply supp_eq_implies_subset_conj in H. destruct H. assumption. }
  rewrite res_bulid_Peq; try assumption.
  specialize (H (res_st_to_X s X)). rewrite H. 
  destruct (Req_dec (get_prob_in_dstate (mu \| X) (res_st_to_X s X)) 0) eqn: Hnot.
  - assert (Htemp: get_prob_in_dstate mu s = 0). {
      apply get_probs_res_iff with (X:= X); try assumption. } 
    rewrite Htemp. rewrite Rmult_0_r. reflexivity.
  - rewrite <- Rinv_l_sym; try assumption. rewrite Rmult_1_l. reflexivity.
Qed.

Lemma res_bulid_add: forall mu mu1 mu2 X, (*加法分解：restriction 上的加法分解可 lift 回去相加得到原分布*)
  Valid_dist mu -> Valid_dist mu1 -> Valid_dist mu2 ->
  mu \| X == mu1 + mu2 -> 
  (sum_probs (mu \| X) = sum_probs mu1 + sum_probs mu2)%R ->
  mu == (bulid_dst_sub mu1 mu X) + (bulid_dst_sub mu2 mu X).
Proof.
  intros mu mu1 mu2 X. intros. unfold dst_equiv. intros.
  assert (Hsupp: is_supp_subset (supp_mu (mu1+mu2)) (supp_mu (mu \| X)) = true). { 
    apply dst_equiv_implies_beq_supp in H2; try assumption.
    - apply supp_eq_implies_subset_conj in H2. destruct H2. assumption. 
    - apply Valid_after_resX. assumption.
    - apply WF_after_add with (mu:= mu\|X); try assumption. 
      apply Valid_after_resX. assumption. }
  assert (HWFX: Valid_dist (mu \| X)). { apply Valid_after_resX. assumption. }
  assert (Hsub1: is_supp_subset (supp_mu mu1) (supp_mu (mu \| X)) = true). { 
    apply supp_mu_subset_decom_l in Hsupp; try assumption. 
    - destruct Hsupp. assumption.
    - apply Sort_supp_if_WF_supp. } 
  assert (Hsub2: is_supp_subset (supp_mu mu2) (supp_mu (mu \| X)) = true). { 
    apply supp_mu_subset_decom_l in Hsupp; try assumption. 
    - destruct Hsupp. assumption.
    - apply Sort_supp_if_WF_supp.  }
  rewrite get_prob_decom. repeat rewrite res_bulid_Peq; try assumption.
  rewrite <- Rmult_plus_distr_r. rewrite <- Rmult_plus_distr_l. 
  rewrite <- get_prob_decom.
  specialize (H2 (res_st_to_X s X)). rewrite <- H2. 
  destruct (Req_dec (get_prob_in_dstate (mu \| X) (res_st_to_X s X)) 0) eqn: Hnot.
  - assert (Htemp: get_prob_in_dstate mu s = 0). {
      apply get_probs_res_iff with (X:= X); try assumption. } 
  rewrite Htemp. rewrite Rmult_0_r. reflexivity.
  - rewrite <- Rinv_l_sym; try assumption. rewrite Rmult_1_l. reflexivity.
Qed.

Lemma res_bulid_linear: forall mu mu1 mu2 X p,  (*线性组合：restriction 上的凸组合可 lift 成全分布的凸组合*)
  0 < p < 1 -> Valid_dist mu -> Valid_dist mu1 -> Valid_dist mu2 ->
  mu \| X == p * mu1 + (1-p) * mu2 ->
  (sum_probs mu1 = sum_probs (mu \| X))%R ->
  (sum_probs mu2 = sum_probs (mu \| X))%R ->
  mu == p * (bulid_dst_sub mu1 mu X) + (1-p) * (bulid_dst_sub mu2 mu X).
Proof.
  intros mu mu1 mu2 X p Hp HWF HWF1 HWF2 Heq Hsum1 Hsum2. 
  unfold dst_equiv. intros.
  assert (Hpminus: 0< (1 - p) <1). { apply Rp_lt1_minus_p_bounds with (p:= p). assumption. }
  assert (HWFX: Valid_dist (mu \| X)). { apply Valid_after_resX; try assumption. }
  assert (HWFlinear: Valid_dist (p * mu1 + (1 - p) * mu2)). {
    - apply Valid_linear; try assumption. 
      + destruct Hp. split; try apply Rlt_le; assumption.
      + destruct Hpminus. split; try apply Rlt_le; assumption.
      + rewrite R_plus_sub_eq_1. apply Rle_refl.
  }
  assert (Hsupp_eq: beq_supp (supp_mu (mu \| X)) (supp_mu (p * mu1 + (1 - p) * mu2)) = true). {
      apply dst_equiv_implies_beq_supp in Heq; try assumption. }
  apply supp_eq_implies_subset_conj in Hsupp_eq. destruct Hsupp_eq.
  assert (Hsupp: is_supp_subset (supp_mu (mu1+mu2)) (supp_mu (mu \| X)) = true). { 
    apply dst_equiv_implies_beq_supp in Heq; try assumption.
    apply supp_eq_implies_subset_conj in Heq. destruct Heq. 
    rewrite <- supp_eq_linear in H0; try assumption. } 
  assert (Hsub1: is_supp_subset (supp_mu (p * mu1)) (supp_mu (mu \| X)) = true). {
    destruct Hp. 
    apply supp_mu_subset_decom_l in H0; try assumption. 
    - destruct H0. assumption.
    - apply Sort_supp_if_WF_supp. }
  assert (Hsub2: is_supp_subset (supp_mu ((1-p) * mu2)) (supp_mu (mu \| X)) = true). { 
    destruct Hpminus. destruct Hp. 
    apply supp_mu_subset_decom_l in H0; try assumption. 
    - destruct H0. assumption.
    - apply Sort_supp_if_WF_supp. }
  rewrite get_prob_decom. repeat rewrite get_prob_coef_mult.
  repeat rewrite res_bulid_Peq; try assumption.
  - rewrite <- Rmult_comm with (r1:= (get_prob_in_dstate mu1 (res_st_to_X s X))).
    rewrite Rmult_assoc with (r1:= get_prob_in_dstate mu1 (res_st_to_X s X)).
    rewrite <- Rmult_assoc with (r1:= p).
    rewrite <- Rmult_comm with (r1:= (get_prob_in_dstate mu2 (res_st_to_X s X))).
    rewrite Rmult_assoc with (r1:= get_prob_in_dstate mu2 (res_st_to_X s X)).
    rewrite <- Rmult_assoc with (r1:= (1-p)).
    rewrite <- Rmult_plus_distr_r. 
    specialize (Heq (res_st_to_X s X)). 
    rewrite get_prob_decom in Heq. 
    repeat rewrite get_prob_coef_mult in Heq.
    rewrite <- Heq. rewrite <- Rmult_assoc. 
    destruct (Req_dec (get_prob_in_dstate (mu \| X) (res_st_to_X s X)) 0) eqn: Hnot.
    + assert (Htemp: get_prob_in_dstate mu s = 0). {
        apply get_probs_res_iff with (X:= X); try assumption. } 
      rewrite Htemp. rewrite Rmult_0_r. reflexivity.
    + rewrite Rinv_r; try assumption. rewrite Rmult_1_l. reflexivity.
  - destruct Hpminus. rewrite <- supp_eq_mult_coef in Hsub2; try assumption.
  - destruct Hp. rewrite <- supp_eq_mult_coef in Hsub1; try assumption.
Qed.

Lemma res_bulid_linear2p: forall mu mu1 mu2 X p1 p2,
  0 < p1 < 1 -> 0 < p2 < 1 -> (p1 + p2)%R = 1 ->
  Valid_dist mu -> Valid_dist mu1 -> Valid_dist mu2 ->
  mu \| X == p1 * mu1 + p2 * mu2 ->
  (sum_probs mu1 = sum_probs (mu \| X))%R ->
  (sum_probs mu2 = sum_probs (mu \| X))%R ->
  mu == p1 * (bulid_dst_sub mu1 mu X) + p2 * (bulid_dst_sub mu2 mu X).
Proof.
  intros mu mu1 mu2 X p1 p2 Hp1 Hp2 Hsum. 
  intros. rewrite <- R_plus_sub_eq_1 with (p1:= p1) in Hsum.
  apply Rplus_eq_reg_l in Hsum. rewrite Hsum.
  apply res_bulid_linear; try assumption. 
  rewrite <- Hsum. assumption.
Qed.