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
Require Import Library.DistState.Arithmetic.

(*This file contains properties of valid_dist*)
Open Scope list_scope.
Open Scope dstate_scope.

Lemma positive_sum_ge_0 (A:Type): 
  forall (da: dist A), positive_probs da -> (0 <= sum_probs da)%R.
Proof.
  intros. induction da as [| (a0,p0) da' Hda'].
  - simpl. apply Rle_refl.
  - simpl in H. destruct H as [Hpos_p0 Hpos_da']. apply Hda' in Hpos_da'.
    unfold prob_is_positive in Hpos_p0. destruct Hpos_p0 as [Hpos_p0 Hle_p0].
    apply Rle_trans with (r2 := (p0 + 0)%R).
    * rewrite Rplus_0_r. apply Rlt_le. apply Hpos_p0.
    * simpl. apply Rplus_le_compat; try assumption. apply Rle_refl.
Qed.
Lemma posi_cons_sum_probs_gt_0 (A:Type): forall (s: A) p (d: dist A), 
  positive_probs ((s,p)::d) -> (0 < sum_probs ((s,p)::d))%R.
Proof.
  intros. inversion H. simpl. destruct H0. apply positive_sum_ge_0 in H1.
  apply Rplus_lt_le_0_compat; try assumption.
Qed.

Lemma dst_positive_decom: 
  forall (mu0 mu1: dist_state), 
    positive_probs mu0 /\ positive_probs mu1 <->
      positive_probs (mu0 + mu1)%dist_state.
Proof.
  split. {
  intros. generalize dependent mu1.
  induction mu0 as [|(s0, p0) mu0' Hmu0]; intros.
  - simpl. destruct H. apply H0.
  - simpl in *. destruct H. destruct H.
    split; try assumption. apply Hmu0. 
    split; try assumption. }
  { intros. generalize dependent mu1.
    induction mu0 as [|(s0, p0) mu0' Hmu0]; intros.
    - simpl in *. split; [apply I | apply H].
    - simpl in *.  destruct H as [H0 H1].
    specialize (Hmu0 mu1 H1). destruct Hmu0.
    split. 
      + split; try assumption.
      + assumption. 
  }
Qed.

Lemma dst_sum_prob_decom: forall (mu0 mu1: dist_state), 
  (sum_probs (mu0 + mu1)%dist_state = sum_probs mu0 + sum_probs mu1)%R.
Proof.
  intros. generalize dependent mu1.
  induction mu0 as [|(s,p) mu0' IHmu0]; intros; simpl.
  - rewrite Rplus_0_l. reflexivity.
  - rewrite Rplus_assoc. apply Rplus_eq_compat_l. apply IHmu0.
Qed.


Lemma Valid_dist_inv (A:Type): forall (a: A) (p: R) (da: dist A), 
  Valid_dist ((a,p) :: da) -> Valid_dist da.
Proof.
  intros a p da H. unfold Valid_dist in *.
  destruct H as [Hsum Hpos]. split.
  + simpl in Hsum. destruct Hsum as [Hsum_ge_0 Hsum_le_1].
    simpl in Hpos. destruct Hpos as [Hp Hpos_da]. split.
    * apply positive_sum_ge_0. exact Hpos_da. 
    * unfold prob_is_positive in Hp. destruct Hp.
      apply Rle_trans with (r2:= (0 + sum_probs da)%R).
      - rewrite Rplus_0_l. apply Rle_refl.
      - apply Rle_trans with (r2:= (p + sum_probs da)%R).
        -- apply Rplus_le_compat; [apply Rlt_le; assumption | apply Rle_refl]. 
        -- exact Hsum_le_1.
  + simpl in Hpos. destruct Hpos as [Hp Hpos_da]. exact Hpos_da.
Qed.

Lemma Valid_dist_nil (A: Type) : Valid_dist ([] : dist A). 
Proof.
  unfold Valid_dist. split. 
  - simpl. split. 
    + apply Rle_refl. + apply Rle_0_1.
  - unfold positive_probs. apply I. 
Qed.

Lemma Valid_dist_conj (A:Type): forall (s:A) (p: R) (d: dist A), 
  Valid_dist ((s,p):: d) ->
  Valid_dist [(s,p)] /\ (Valid_dist d).
Proof.
  intros. unfold Valid_dist in *. 
  destruct H. destruct H. destruct H0. split.
  - split. 
    + simpl. rewrite Rplus_0_r. 
    unfold prob_is_positive in H0. destruct H0. 
    split. * apply Rlt_le. assumption. * assumption.
    + simpl. split. * apply H0. * apply I.
  - split.  
    + split. * apply positive_sum_ge_0. assumption. 
      * simpl in H1. unfold prob_is_positive in H0. destruct H0. 
      apply Rle_trans with (r2:= (p + sum_probs d)%R).
      ** rewrite <- Rplus_0_l at 1. apply Rplus_le_compat. 
      *** apply Rlt_le. assumption. *** apply Rle_refl.
      ** apply H1.
    + assumption.
Qed.

Lemma Valid_add_decom: forall (mu0 mu1: dist_state),
  Valid_dist (mu0 + mu1)%dist_state -> 
  Valid_dist mu0 /\ Valid_dist mu1.
Proof.
  intros.
  unfold Valid_dist in *. destruct H.
  apply dst_positive_decom in H0. destruct H0 as [H0 H1].
  rewrite dst_sum_prob_decom in H. destruct H.
  split.
  - split; try assumption.
  apply positive_sum_ge_0 in H0.
  apply positive_sum_ge_0 in H1.
  split; try assumption.
  apply Rplus_le_reg_r with (sum_probs mu1).
  apply Rle_trans with 1%R; try assumption.
  rewrite <- Rplus_0_r with (r:=1%R) at 1.
  apply Rplus_le_compat_l.
  try assumption.
  - split; try assumption.
  apply positive_sum_ge_0 in H0.
  apply positive_sum_ge_0 in H1.
  split; try assumption.
  apply Rplus_le_reg_l with (sum_probs mu0).
  apply Rle_trans with 1%R; try assumption.
  rewrite <- Rplus_0_l with (r:=1%R) at 1.
  apply Rplus_le_compat_r.
  try assumption.
Qed.

Lemma dst_prob_le_sum : forall (mu:dist_state) (s:partial_st), 
  positive_probs mu -> (get_prob_in_dstate mu s <= sum_probs mu)%R.
Proof.
  intros. induction mu as [| (s1,p1) mu' Hmu'].
  - simpl. apply Rle_refl.
  - simpl in *. destruct H as [Hpos_p1 Hpos_mu'].
    unfold prob_is_positive in Hpos_p1. destruct Hpos_p1 as [Hpos_p1 Hle_p1].
    destruct (beq_state s s1) eqn: Hst1.
    + apply Rplus_le_compat_l. apply Hmu'. exact Hpos_mu'.
    + rewrite <- Rplus_0_l with (r:= (get_prob_in_dstate mu' s)). apply Rplus_le_compat.
      * apply Rlt_le. apply Hpos_p1.
      * apply Hmu'. exact Hpos_mu'.
Qed. 

Lemma dst_Valid_prob_0_1 (mu: dist_state): 
  Valid_dist mu -> forall s, (0 <= get_prob_in_dstate mu s <= 1)%R.
Proof. 
  intros Hvalid s. split.
  - induction mu as [|(s1,p1) mu1 Hmu1].
    + simpl. apply Rle_refl.
    + assert (Hvalid_copy: Valid_dist ((s1, p1) :: mu1)). { exact Hvalid. }
      apply Valid_dist_inv in Hvalid_copy. 
      unfold Valid_dist in Hvalid.
      destruct Hvalid as [Hsum Hpos]. destruct Hpos as [Hp Hpos_da]. 
      unfold prob_is_positive in Hp. destruct Hp as [Hp_gt Hp_le].
      simpl. destruct (beq_state s s1) eqn: Heq_st.
      * rewrite <- Rplus_0_l with (r:= 0%R). apply Rplus_le_compat.
        ** apply Rlt_le in Hp_gt. apply Hp_gt.
        ** apply Hmu1. apply Hvalid_copy.   
      * apply Hmu1. exact Hvalid_copy.
  - induction mu as [|(s1,p1) mu1 Hmu1].
    + simpl. apply Rle_0_1.
    + simpl. destruct (beq_state s s1) eqn: Heq_st.
      * unfold Valid_dist in Hvalid. destruct Hvalid as [Hsum Hpos].
        simpl in Hsum. destruct Hsum as [Hsum_ge Hsum_le]. 
        simpl in Hpos. destruct Hpos as [Hp Hpos_da].
        assert (Hsum_ge_prob: (get_prob_in_dstate mu1 s <= sum_probs mu1)%R). { 
          apply dst_prob_le_sum. apply Hpos_da. }
        apply Rplus_le_compat_l with (r:= p1) in Hsum_ge_prob. 
        apply Rle_trans with (r2:= (p1 + sum_probs mu1)%R).
        ** apply Hsum_ge_prob. ** apply Hsum_le.
      * apply Hmu1. apply Valid_dist_inv in Hvalid. apply Hvalid.
Qed.

Lemma dst_cons_valid_contra: forall mu s (p: R), 
  Valid_dist ((s, p) :: mu) -> (s, p) :: mu == [] -> False.
Proof.
  intros. inversion H; subst. 
  simpl in *. 
  unfold dst_equiv in H0. specialize (H0 s). 
  simpl in H0. rewrite state_eq_refl in H0. 
  destruct H2. unfold prob_is_positive in H2. destruct H2.
  apply Valid_dist_inv in H. apply dst_Valid_prob_0_1 with (s:= s) in H. destruct H.
  apply Rplus_le_compat_l with (r:= p) in H.
  rewrite H0 in H. rewrite Rplus_0_r in H.
  eapply Rle_not_lt in H. unfold not in H.
  apply H. apply H2.
Qed.



Lemma dst_eq_nil_iff: forall mu, 
  (Valid_dist mu /\ mu == []) <-> mu = []. (*emp_dst_eq*)
Proof. 
  intros.
  induction mu as [|(s1,p1) mu1' Hmu1]. 
  - split.
    + intros. reflexivity.
    + intro. split. * apply Valid_dist_nil. * apply dst_equiv_refl.
  - split.
    + intros. destruct H. exfalso.
      apply dst_cons_valid_contra with (mu:= mu1') (s:=s1) (p:= p1); assumption.
    + intro. discriminate H.
Qed.

Lemma dst_add_eq_nil_iff: forall (mu0 mu1: dist_state),
  (Valid_dist mu0 /\ Valid_dist mu1 /\ [] == (mu0 + mu1)%dist_state) <-> mu0 = [] /\ mu1 = [].
Proof.
  split. 
  - intros. destruct H. destruct H0.
    induction mu0 as [|(s0,p0) mu0' Hmu0]; induction mu1 as [|(s1,p1) mu1' Hmu1].
    + auto.
    + simpl in H1. exfalso. 
    apply dst_cons_valid_contra with (mu:= mu1') (s:= s1) (p:= p1); try assumption. 
    apply dst_equiv_sym. assumption.
    + rewrite dst_add_0_r in H1. exfalso. 
    apply dst_cons_valid_contra with (mu:= mu0') (s:= s0) (p:= p0); try assumption. 
    apply dst_equiv_sym. assumption.
    + exfalso. unfold dst_equiv in H1. simpl in H1. specialize (H1 s0). 
    rewrite state_eq_refl in H1.
    assert (Hget_p: (get_prob_in_dstate (mu0' + ((s1, p1) :: mu1'))%dist_state s0 =
    get_prob_in_dstate mu0' s0 + get_prob_in_dstate ((s1, p1) :: mu1') s0)%R). { apply get_prob_decom. }
    rewrite Hget_p in H1.
    assert (Hprob: (0 <= (get_prob_in_dstate mu0' s0 + get_prob_in_dstate ((s1, p1) :: mu1') s0)%R)%R). {
      rewrite <- Rplus_0_l with (r:= 0%R). apply Rplus_le_compat.
      * assert (H0': (0 <= get_prob_in_dstate mu0' s0 <=1)%R). { 
          apply dst_Valid_prob_0_1. apply Valid_dist_inv in H. assumption. }
        destruct H0'. assumption.
      * assert (H1': (0 <= get_prob_in_dstate ((s1, p1) :: mu1') s0 <=1)%R). { 
          apply dst_Valid_prob_0_1. assumption. }
        destruct H1'. assumption. }
    destruct H. destruct H2. unfold prob_is_positive in H2. destruct H2.
    assert (Hcontra: (0 + 0 <
      p0 + (get_prob_in_dstate mu0' s0 + get_prob_in_dstate ((s1, p1) :: mu1') s0))%R). {
        apply Rplus_lt_le_compat; assumption. }
    rewrite <- H1 in Hcontra. rewrite Rplus_0_l in Hcontra. 
    apply Rlt_irrefl in Hcontra. apply Hcontra. 
  - intros. destruct H. rewrite H. rewrite H0. 
    split; try apply Valid_dist_nil.
    split; try apply Valid_dist_nil.
    simpl. apply dst_equiv_refl. 
Qed.

Lemma sum_probs0_implies_nil: forall (mu : dist_state), 
  Valid_dist mu -> sum_probs mu = 0%R -> mu = [].
Proof.
  intros. induction mu as [|(s,p) mu' IH].
  - reflexivity.
  - simpl in *. destruct H. destruct H1. destruct H1. 
    apply positive_sum_ge_0 in H2. 
    assert (Hcontra: (0 < p + sum_probs mu')%R). {
      apply Rplus_lt_le_0_compat; assumption. }
    rewrite H0 in Hcontra. apply Rlt_irrefl in Hcontra. contradiction.
Qed.

(***************************************************************)
(*************************************************************)


Lemma dst_sum_prob_coef_mult: forall (mu:dist_state) (p:R), 
  ((sum_probs ((p * mu)%dist_state) = (p * (sum_probs mu))%R)%R).
Proof.
  intros.
  induction mu as [|(s0,p0) mu' IHmu]; intros; simpl.
  - rewrite Rmult_0_r. reflexivity.
  - destruct (Req_EM_T p 0) eqn: Hp.
    + simpl. rewrite e. rewrite Rmult_0_l. reflexivity.
    + simpl. rewrite IHmu. rewrite Rmult_plus_distr_l. reflexivity.
Qed.


Lemma dst_positive_mult_cofe: forall (mu:dist_state) (p: R),
  (0 < p <= 1)%R -> positive_probs mu -> 
  positive_probs ((p * mu)%dist_state).
Proof.
  intros. induction mu as [|(s,q) mu' Hmu].
  - simpl. apply I.
  - simpl in *. destruct (Req_EM_T p 0) eqn: Hp.
    + simpl. apply I.
    + simpl. destruct H0. unfold prob_is_positive in *. 
    destruct H. destruct H0. split.
      * split.
      ** apply Rmult_lt_0_compat; try assumption. 
      ** rewrite <- Rmult_1_l with (r:=1%R). 
      apply Rmult_le_compat; try (assumption); apply Rlt_le; assumption.
      * apply Hmu. assumption.
Qed. 


Lemma Valid_mult_cofe: forall (mu: dist_state) (p:R), 
  Valid_dist mu -> 
  (0 <= p <= 1)%R -> 
  Valid_dist ((p * mu)%dist_state). 
Proof.
  intros. destruct H0. induction mu as [|(s0,p0) mu'].
  - simpl. apply H.
  - simpl. destruct (Req_EM_T p 0) eqn: Hp.
    -- apply Valid_dist_nil.
    -- unfold Valid_dist in H. destruct H. simpl in H.
    destruct H. simpl in H2. destruct H2.
    unfold Valid_dist. simpl. split.
    + rewrite dst_sum_prob_coef_mult. rewrite <- Rmult_plus_distr_l. split. 
      * apply Rmult_le_pos; assumption.
      * rewrite <- Rmult_1_l with (r:=1%R). apply Rmult_le_compat; try assumption.
    + split.
      * unfold prob_is_positive in H2. destruct H2. unfold prob_is_positive. split.
      ** apply Rmult_lt_0_compat; try assumption.
        unfold not in n. destruct (Rle_lt_or_eq_dec 0 p) as [Hp1|Hp2].
        ++ assumption. ++ assumption.
        ++ exfalso. apply n. rewrite Hp2. reflexivity.
      ** rewrite <- Rmult_1_l with (r:=1%R). 
      apply Rmult_le_compat; try assumption.
      apply Rlt_le. assumption.
      * apply dst_positive_mult_cofe; try assumption. split; try assumption.
      destruct (Rle_lt_or_eq_dec 0 p) as [Hp1|Hp2].
        ++ assumption. ++ assumption.
        ++ exfalso. apply n. rewrite Hp2. reflexivity.
Qed.

Lemma Valid_linear: forall (mu0 mu1: dist_state) (p0 p1:R), 
  Valid_dist mu0 -> 
  Valid_dist mu1 ->   
  (0 <= p0 <= 1)%R -> (0 <= p1 <= 1)%R ->
  (p0 + p1 <= 1)%R ->
  Valid_dist ((p0 * mu0 + p1 * mu1)%dist_state).
Proof.
  intros mu0 mu1 p0 p1 Hvalid0 Hvalid1 Hp0 Hp1 Hadd. 
  generalize dependent mu1.
  induction mu0 as [|(s,p) mu0'].
  - intros. simpl. apply Valid_mult_cofe; try assumption.
  - intros. simpl. destruct (Req_EM_T p0 0) eqn: Hp0_b.
    -- simpl. apply Valid_mult_cofe; try assumption.
    -- unfold Valid_dist. simpl. split.
    + rewrite dst_sum_prob_decom with (mu0:= (p0 * mu0')) (mu1:= (p1 * mu1)).
      rewrite dst_sum_prob_coef_mult with (mu:= mu0').
      rewrite dst_sum_prob_coef_mult with (mu:= mu1). 
      rewrite <- Rplus_assoc. rewrite <- Rmult_plus_distr_l.
      unfold Valid_dist in Hvalid0. destruct Hvalid0 as [Hsum0 Hpos0]. simpl in Hsum0.
      unfold Valid_dist in Hvalid1. destruct Hvalid1 as [Hsum1 Hpos1].
      apply Rplus_mult_le_interval; try assumption.
    + apply Valid_dist_conj in Hvalid0. destruct Hvalid0 as [H1 H2]. split.
      * unfold Valid_dist in H1. destruct H1 as [Hsum0 Hpos0]. 
        simpl in Hpos0. destruct Hpos0 as [Hp HI]. unfold prob_is_positive in Hp. 
        unfold prob_is_positive. split.
        ** destruct Hp. destruct Hp0. apply Rmult_lt_0_compat; try assumption. 
        destruct (Rle_lt_or_eq_dec 0 p0) as [Hp01|Hp02]; try assumption.
        exfalso. apply n. rewrite Hp02. reflexivity.
        ** rewrite <- Rmult_1_l with (r:=1%R). 
        destruct Hp. destruct Hp0.
        apply Rmult_le_compat; try assumption. apply Rlt_le. assumption.
      * specialize (IHmu0' H2 mu1 Hvalid1). unfold Valid_dist in IHmu0'. 
      destruct IHmu0' as [Hsum1 Hpos1]. assumption.
Qed. 

Lemma Valid_mult_under_eq_prob: forall (mu:dist_state) (p: R), 
  Valid_dist mu ->
  (0 <= p)%R ->
  (0 <= sum_probs (p*mu)%dist_state <=1)%R ->
  Valid_dist (p * mu).
Proof.
  intros mu p Hvalid Hp Hsum_p.
  induction mu as [|(s,q) mu' IH].
  - simpl. apply Valid_dist_nil.
  - destruct (Req_dec_T p 0) eqn: Hp_eq; subst.
    + rewrite dst_mult_0_l. apply Valid_dist_nil.
    + simpl in *. rewrite Hp_eq. rewrite Hp_eq in Hsum_p.
    unfold Valid_dist. simpl in *.
    inversion Hp; subst.
      * apply Valid_dist_conj in Hvalid. destruct Hvalid.
      destruct H0. destruct H2. unfold prob_is_positive in H2. destruct H2.
      assert (Hpq0: (0 < p * q)%R). { apply Rmult_lt_0_compat; assumption. }
      assert (Hsum': (0 <= sum_probs (p * mu')%dist_state)%R). {
        destruct H1. destruct H1. rewrite dst_sum_prob_coef_mult. 
        apply Rmult_le_pos; try assumption. }
      split; try assumption.
      destruct Hsum_p. apply R_leq_1 in H6; try assumption. destruct H6.
      split.
      ** try unfold prob_is_positive. split; try assumption.
      ** apply IH; try assumption. split; try assumption.
      * unfold not in n. contradiction n. reflexivity.
Qed.


Lemma Valid_linear_under_eq_prob: forall (mu0 mu1: dist_state) (p0 p1: R), 
  Valid_dist mu0 -> Valid_dist mu1 -> 
  (0 <= p0)%R -> (0 <= p1)%R ->
  (0 <= (p0 * sum_probs mu0 + p1 * sum_probs mu1)%R <=1)%R ->
  Valid_dist (p0 * mu0 + p1 * mu1).
Proof.
  intros mu0 mu1 p0 p1 Hvalid0 Hvalid1 Hp0 Hp1 Hsum.
  generalize dependent mu1. induction mu0 as [|(s0,q0) mu0' IH].
  - intros. simpl in *. 
    rewrite Rmult_0_r in Hsum. rewrite Rplus_0_l in Hsum.
    apply Valid_mult_under_eq_prob; try assumption. 
    rewrite <- dst_sum_prob_coef_mult in Hsum.
    assumption.
  - intros. simpl in *. destruct (Req_dec_T p0 0) eqn: Hp0_eq; subst.
    + simpl in *. rewrite Rmult_0_l in Hsum. rewrite Rplus_0_l in Hsum. 
    apply Valid_mult_under_eq_prob; try assumption. 
    rewrite <- dst_sum_prob_coef_mult in Hsum.
    assumption.
    + unfold Valid_dist. simpl. rewrite Rmult_plus_distr_l in Hsum.
    split.
      * rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
      rewrite <- Rplus_assoc. assumption.
      * apply Valid_dist_conj in Hvalid0. destruct Hvalid0. destruct H. 
      unfold positive_probs in H1. destruct H1. destruct H1.
      inversion Hp0; subst.
      ** assert (Hpq0: (0 < p0 * q0)%R). { apply Rmult_lt_0_compat; assumption. }
      assert (Hsum0: (0 <= (p0 * sum_probs mu0'))%R). {
        apply Rmult_le_pos; try assumption. destruct H0. destruct H0. assumption. }
      assert (Hsum1: (0 <= (p1 * sum_probs mu1))%R). {
        destruct Hvalid1. destruct H5. apply Rmult_le_pos; try assumption. }
      assert (Hgt0: (0 < p0 * q0 + p0 * sum_probs mu0')%R). {
        rewrite <- Rplus_0_l at 1. apply Rplus_lt_le_compat; try assumption. }
      destruct Hsum.
      assert (Hsum_copy: (p0 * q0 + p0 * sum_probs mu0' + p1 * sum_probs mu1 <= 1)%R) by assumption.
      apply R_leq_1 in H6; try assumption.
      destruct H6. apply R_leq_1 in H6; try assumption.
      destruct H6. split.
      ++ unfold prob_is_positive. split; try assumption.
      ++ apply IH; try assumption.
      assert (Hge0: (0 <= p0 * sum_probs mu0' + p1 * sum_probs mu1)%R). { 
        apply Rplus_le_le_0_compat; try assumption. }
      split; try assumption.
      rewrite Rplus_assoc in Hsum_copy. 
      apply R_leq_1 in Hsum_copy; try assumption.
      destruct Hsum_copy. try assumption.
      ** unfold not in n. contradiction n. reflexivity.
Qed.


Lemma insert_positive: forall (mu:dist_state) (s:partial_st) (p:R),
  (0<= sum_probs ((s,p):: mu) <=1)%R ->
  positive_probs mu -> prob_is_positive p ->
  positive_probs (insert_st_pair s p mu).
Proof.
  intros mu s p Hsum Hmu Hp. induction mu as [|(s0,q0) mu' IH].
  - simpl. split; try assumption; try apply I.
  - simpl. destruct (beq_state s s0) eqn: Hs.
    + simpl. destruct Hmu. split; try assumption.
    unfold prob_is_positive in *. simpl in Hsum. rewrite <- Rplus_assoc in Hsum.
    destruct Hsum. destruct H. destruct Hp. split.
      * apply Rplus_lt_0_compat; assumption.
      * apply positive_sum_ge_0 in H0.
      apply Rplus_le_reg_r with (r:= sum_probs mu').
      apply Rle_trans with (r2:=1%R); try assumption.
      rewrite <- Rplus_0_r with (r:=1%R) at 1.
      apply Rplus_le_compat_l; try assumption.
    + destruct (ble_state s s0) eqn: Hle.
      * simpl. destruct Hmu. split; try assumption. split; try assumption.
      * simpl. destruct Hmu. split; try assumption. apply IH; try assumption.
      simpl. destruct Hp. destruct H. simpl in Hsum. rewrite <- Rplus_assoc in Hsum.
      rewrite Rplus_comm with (r1:= p) in Hsum. rewrite Rplus_assoc in Hsum. destruct Hsum.
      apply positive_sum_ge_0 in H0. split.
      ** apply Rplus_le_le_0_compat; try assumption. apply Rlt_le; try assumption.
      ** apply Rplus_le_reg_l with (r:= q0). 
      apply Rle_trans with (r2:=1%R); try assumption.
      rewrite <- Rplus_0_l with (r:=1%R) at 1.
      apply Rplus_le_compat_r; try assumption.
      apply Rlt_le; try assumption.
Qed.



(**********************************************************)
Open Scope Q_scope.
Open Scope dstate_scope.

Inductive Sorted_dst : dist_state -> Prop := 
  | sorted0 : Sorted_dst []
  | sorted1 : forall s p, Sorted_dst [(s, p)]
  | sorted2 : forall (s1 s2: partial_st) (p1 p2: R) (mu: dist_state),
                (* Valid_state s1 -> Valid_state s2 ->     *)
                (beq_state s1 s2 = false) /\ (ble_state s1 s2 = true) -> 
                Sorted_dst ((s2, p2) :: mu) ->
                Sorted_dst ((s1, p1) :: (s2, p2) :: mu).

Lemma Sorted_inv: forall (mu: dist_state) (s1: partial_st) (p1: R),
  Sorted_dst ((s1,p1) :: mu) -> Sorted_dst mu.
Proof.
  intros. inversion H; subst.
  + apply sorted0. + assumption.
Qed.

Lemma insert_st_pair_sorted : 
  forall s p mu, 
    Sorted_dst mu -> 
    Sorted_dst (insert_st_pair s p mu).
Proof.
  intros s p mu Hsorted. 
  induction Hsorted as [| s' p' | s2 s1 p2 p1 mu' [Hbeq Hcomp] IH].
  - simpl. apply sorted1. 
  - simpl. destruct (beq_state s s') eqn: Hst'; try constructor.
    destruct (ble_state s s') eqn: Hcomp; constructor.
    * split; assumption.
    * apply sorted1; try assumption.
    * rewrite state_eq_sym. split; try assumption.
      apply st_nle_iff in Hcomp. 
      destruct Hcomp. assumption.
    * apply sorted1. 
  - simpl in IHIH. destruct (beq_state s s1) eqn: Hst1.
    + simpl. assert (Hst2: beq_state s s2 = false). { 
        apply state_eq_compat_left with (s:= s2) in Hst1. 
        rewrite Hbeq in Hst1. 
        rewrite <- Hst1. apply state_eq_sym. }
      rewrite Hst2.
      assert (Hcomp2: ble_state s s2 = false). { 
        apply st_nle_iff. rewrite state_eq_sym in Hst2.
        split; try assumption. 
        apply st_eq_ble_compat_left with (s:= s2) in Hst1. 
        rewrite Hcomp in Hst1. apply Hst1; try assumption. }
      rewrite Hcomp2. rewrite Hst1. eapply sorted2; try assumption.
      split; try apply Hbeq. apply Hcomp.
    + destruct (ble_state s s1) eqn: Hcomp1.
      * unfold insert_st_pair. 
        destruct (beq_state s s2) eqn: Hst2.
      ** eapply sorted2; try assumption. split; assumption.
      ** destruct (ble_state s s2) eqn: Hcomp2.
      -- eapply sorted2; try assumption.
      ++ split; assumption.
      ++ eapply sorted2; try assumption. split; assumption.
      -- rewrite Hst1. rewrite Hcomp1. 
        eapply sorted2; try assumption. rewrite state_eq_sym in Hst2. 
        split; try apply Hst2. 
        apply st_nle_iff in Hcomp2. destruct Hcomp2. apply H0.
      * fold insert_st_pair in IHIH. unfold insert_st_pair.
        assert (Hcomp12: ble_state s1 s2 = false). { 
          apply st_nle_iff. split; assumption. }
        assert (Hcomp2: ble_state s s2 = false ). {
          apply st_nle_trans with (s1:= s1); try assumption. }
        rewrite Hcomp2. 
        apply st_nle_iff in Hcomp2. destruct Hcomp2.
        rewrite state_eq_sym in H. rewrite H. rewrite Hst1.
        rewrite Hcomp1. fold insert_st_pair.
        eapply sorted2; try assumption.
        split; assumption.
Qed.
                  
Lemma WF_dist_implies_sortdst_Sorted : forall mu, 
  Valid_dist mu -> Sorted_dst (sort_dst mu).
Proof.
  intros mu Hwf. 
  induction mu as [|(s1,p1) mu1 IHmu1].
  - simpl. apply sorted0.
  - simpl. apply Valid_dist_conj in Hwf. destruct Hwf as [Hwf1 Hwf2].
    assert (Hsorted: Sorted_dst (sort_dst mu1)). { apply IHmu1. assumption. }
    inversion Hsorted; subst.
    + simpl. apply sorted1; try assumption. 
    + simpl. destruct (beq_state s1 s) eqn: Heq_st.
      * apply sorted1; try assumption.
      * destruct (ble_state s1 s) eqn: Hcomp.
      ** apply sorted2; try assumption.
      -- split; assumption.
      -- apply sorted1; try assumption.
      ** apply sorted2; try assumption.
      -- split; try assumption.
      ++ rewrite state_eq_sym. apply Heq_st. 
      ++ apply st_nle_iff in Hcomp. destruct Hcomp. assumption.
      -- apply sorted1. 
    + rewrite H. 
      eapply insert_st_pair_sorted.
      apply IHmu1. assumption.
Qed.

Lemma Sorted_app_remove_l mu mu' : 
  Sorted_dst (mu + mu')%dist_state -> Sorted_dst mu'.
Proof.
  generalize dependent mu'.
  induction mu as [|(s,p) mu1 Hmu].
  - intros. simpl in H. assumption.
  - intros. simpl in *. destruct mu' as [|(s',p') mu'].
    + apply sorted0.
    + destruct mu1 as [|(s1,p1) mu2]. 
      * inversion H; subst. assumption.  
      * inversion H; subst.   
      apply Hmu; try assumption.
Qed.

Lemma Sorted_app_remove_r mu mu' : 
  Sorted_dst (mu + mu')%dist_state -> Sorted_dst mu.
Proof.
  generalize dependent mu'.
  induction mu as [|(s,p) mu1 Hmu].
  - intros. apply sorted0.
  - intros. simpl in *. destruct mu' as [|(s',p') mu'].
    + rewrite dst_add_0_r in H. apply H.
    + destruct mu1 as [|(s1,p1) mu2].
      * apply sorted1; try assumption.
      * simpl in *. inversion H; subst. 
        apply Sorted_inv in H. apply Hmu in H. 
        apply insert_st_pair_sorted with 
          (s:=s) (p:=p) (mu:= ((s1, p1) :: mu2)) in H; try assumption.
        simpl in H. destruct H2. 
        rewrite H0 in H. rewrite H1 in H. apply H.
Qed.

Lemma Sorted_remove_1 mu mu' s p : 
  Sorted_dst (mu + ((s,p)::mu'))%dist_state -> 
  Sorted_dst (mu + mu')%dist_state.
Proof.
  intros Hsort. induction mu as [|(s1,p1) mu1 Hmu1].
  - simpl in *. apply Sorted_inv in Hsort. apply Hsort.
  - destruct mu' as [|(s',p') mu''].
    + simpl. rewrite dst_add_0_r. apply Sorted_app_remove_r in Hsort. apply Hsort.
    + simpl in *. 
      assert (Hsort_copy : Sorted_dst ((s1, p1) :: mu1 + ((s, p) :: (s', p') :: mu''))%dist_state). { 
        exact Hsort. }
      apply Sorted_inv in Hsort. apply Hmu1 in Hsort.
      apply insert_st_pair_sorted with (s:=s1) (p:=p1) in Hsort.
      destruct mu1 as [|(s2,p2) mu3].
      * simpl in *. inversion Hsort_copy; subst. 
      inversion H5; subst.
      apply st_nle_iff in H1. apply st_nle_iff in H2.
      assert (Hle1': ble_state s' s1 = false). { 
        apply st_nle_trans with (s1:= s); try assumption. }
      apply st_nle_iff in Hle1'. destruct Hle1'.
      rewrite H in Hsort. rewrite H0 in Hsort. apply Hsort.
      * simpl in *. inversion Hsort_copy; subst. destruct H1.
      rewrite H in Hsort. rewrite H0 in Hsort. apply Hsort.
Qed.

Lemma insert_st_pair_fst_eq_insert_st: (*Very important simplified equation*)
  forall (mu: dist_state) (s: partial_st) (p: R), 
    map fst (insert_st_pair s p mu) = insert_st s (map fst mu).
Proof.
  intros mu s p. generalize dependent s. 
  induction mu as [|(s',q') mu1 Hmu]; intros.
  - simpl. reflexivity.
  - intros. simpl. destruct (beq_state s s') eqn: Hst.
    + simpl. reflexivity.
    + destruct (ble_state s s') eqn: Hcomp.
      * simpl. reflexivity.
      * simpl. rewrite Hmu. reflexivity.
Qed. 

Lemma In_insert_supp: forall s s1 (mu: dist_state), (*Validsupp*)
  In s (insert_st s1 (map fst mu)) -> s1 = s \/ In s (map fst mu).
Proof.
  intros s s1 mu H. generalize dependent s1. 
  induction mu as [|(s',q') mu1 Hmu]; intros s1 H0.
  - simpl in *. assumption.
  - simpl in *. destruct (beq_state s1 s') eqn: Hs1'. 
    + simpl in *. right. assumption.
    + destruct (ble_state s1 s') eqn: Hcomp. 
      * simpl in *. assumption.
      * simpl in *. inversion H0. 
      -- right. left. assumption.
      -- specialize (Hmu s1 H). inversion Hmu. 
      ++ left. assumption.
      ++ right. right. assumption.
Qed.

Lemma sum_probs_insert_pair_eq_cons: forall s p mu, 
  (sum_probs (insert_st_pair s p mu) = sum_probs ((s,p):: mu))%R.
Proof.
  intros. induction mu as [|(s1,p1) mu1 IH].
  - simpl. reflexivity.
  - simpl in *. destruct (beq_state s s1) eqn: Hst1.
    + simpl. rewrite Rplus_assoc. reflexivity.
    + destruct (ble_state s s1) eqn: Hcomp1.
      * simpl. reflexivity.
      * simpl. rewrite <- Rplus_assoc. 
        rewrite Rplus_comm with (r1:= p) (r2:= p1).
        rewrite Rplus_assoc. f_equal. apply IH.
Qed.
Lemma sum_probs_eq_sort: forall mu,
  (sum_probs mu = sum_probs (sort_dst mu))%R.
Proof.
  induction mu as [|(s1,p1) mu1 IH].
  - simpl. reflexivity.
  - simpl. rewrite sum_probs_insert_pair_eq_cons. simpl. rewrite IH. reflexivity.
Qed.

Lemma valid_implies_insert_pair: forall s p mu, 
  Valid_dist ((s,p) :: mu) -> Valid_dist (insert_st_pair s p mu).
Proof. 
  intros s p mu Hvalid. unfold Valid_dist in *.
  destruct Hvalid as [Hsum Hpos]. destruct Hsum as [Hsum_ge Hsum_le]. 
  simpl in Hpos. destruct Hpos as [Hp Hpos].
  induction mu as [|(s1,p1) mu1 IH].
  - simpl in *. rewrite Rplus_0_r in *. split.
    + split. * apply Hsum_ge. * apply Hsum_le.
    + split; assumption. 
  - simpl in *. destruct (beq_state s s1) eqn: Hst1.
    + split. 
      * split.
      ** simpl. rewrite Rplus_assoc. apply Hsum_ge.
      ** simpl. rewrite Rplus_assoc. apply Hsum_le.
      * simpl. destruct Hpos as [Hp1 Hpos]. 
      split; try apply Hpos.
      unfold prob_is_positive in *. 
      assert (Hsum_ge_0: (0 <= sum_probs mu1)%R). { apply positive_sum_ge_0. apply Hpos. }
      split.
      -- destruct Hp as [Hp_gt Hp_le]. destruct Hp1 as [Hp1_gt Hp1_le].
      apply Rplus_lt_0_compat; assumption.
      -- apply Rplus_le_reg_r with (r:= (sum_probs mu1)). 
      apply Rle_trans with (r2:=1%R).
      ++ rewrite Rplus_assoc. apply Hsum_le.
      ++ rewrite <- Rplus_0_r with (r:= 1%R) at 1. 
      apply Rplus_le_compat; [apply Rle_refl| apply Hsum_ge_0].
    + destruct (ble_state s s1) eqn: Hcomp1.
      * simpl. split; split; assumption. 
      * simpl. split.
      ** assert(Htemp: (sum_probs (insert_st_pair s p mu1) = sum_probs ((s, p) :: mu1))%R). { 
          apply sum_probs_insert_pair_eq_cons. }
      rewrite Htemp. simpl. rewrite <- Rplus_assoc. 
      rewrite Rplus_comm with (r1:=p1) (r2:=p).
      rewrite Rplus_assoc. split; [apply Hsum_ge| apply Hsum_le].
      ** destruct Hpos as [Hp1 Hpos1]. split; try apply Hp1.
      unfold prob_is_positive in Hp1. destruct Hp1 as [Hp1_gt Hp1_le].
      unfold prob_is_positive in Hp. destruct Hp as [Hp_gt Hp_le].
      apply IH; try assumption.
      ++ assert (Hsum_ge_0: (0 <= sum_probs mu1)%R). { apply positive_sum_ge_0. apply Hpos1. }
      rewrite <- Rplus_0_r with (r:= 0%R). 
      apply Rplus_le_compat; try assumption. 
      apply Rlt_le. apply Hp_gt. 
      ++ apply Rplus_le_reg_r with (r:= p1).  
      apply Rle_trans with (r2:= (p + (p1 + sum_probs mu1))%R).
      -- rewrite Rplus_assoc. apply Rplus_le_compat_l. rewrite Rplus_comm. apply Rle_refl.
      -- rewrite <- Rplus_0_r with (r:= (p + (p1 + sum_probs mu1))%R).
      apply Rplus_le_compat; try assumption. 
      apply Rlt_le. assumption.
Qed.

Lemma Valid_implies_sort_Valid: forall mu, 
  Valid_dist mu -> Valid_dist (sort_dst mu).
Proof.
  intros mu Hvalid.
  induction mu as [|(s1,p1) mu1 IH].
  - simpl. apply Valid_dist_nil.
  - simpl. remember (sort_dst mu1) as sort_mu1.
    destruct (sort_mu1) as [|(s',p') mu'].
    + simpl in *. unfold Valid_dist. unfold Valid_dist in Hvalid. 
      destruct Hvalid as [Hsum Hpos]. 
      simpl in Hpos. destruct Hpos as [Hp Hpos1]. split.
      * simpl. rewrite Rplus_0_r. 
      unfold prob_is_positive in Hp. 
      destruct Hp. split; try assumption.
      apply Rlt_le. apply H. 
      * simpl. split. ** apply Hp. ** apply I.
    + apply valid_implies_insert_pair. 
      assert (Hvalid_copy: Valid_dist ((s1, p1) :: mu1)). { exact Hvalid. }
      apply Valid_dist_inv in Hvalid_copy. apply IH in Hvalid_copy. 
      unfold Valid_dist in Hvalid. destruct Hvalid.
      unfold Valid_dist. split.
      * simpl in *.
        assert (Heq_sum1: (sum_probs mu1 = sum_probs (sort_dst mu1))%R). 
          { apply sum_probs_eq_sort. }
        rewrite <- Heqsort_mu1 in Heq_sum1. rewrite Heq_sum1 in H.
        simpl in H. apply H.
      * simpl in *. split.
        ** destruct H0. apply H0.
        ** unfold Valid_dist in Hvalid_copy. 
        destruct Hvalid_copy as [Hsum' Hpos'].
        simpl in Hpos'. apply Hpos'.
Qed.

(**************************************************************)
Lemma Sorted_nodup_inv mu s1 p1 : 
  Sorted_dst ((s1,p1) :: mu) -> (get_prob_in_dstate mu s1 = 0)%R.
Proof.
  intros Hsort. induction mu as [|(s',p') mu' Hmu].
  - simpl in *. reflexivity.
  - inversion Hsort; subst. destruct H1. 
    simpl. rewrite H. apply Hmu.
    apply Sorted_remove_1 with (mu:= [(s1,p1)]) (mu':= mu') (s:=s') (p:=p') in Hsort.
    simpl in Hsort.
    apply Hsort.
Qed.


Lemma Sort_Valid_Peq_implies_beq_True: forall mu1 mu2,
  Sorted_dst mu1 /\ Valid_dist mu1 ->
  Sorted_dst mu2 /\ Valid_dist mu2->
  mu1 == mu2 -> beq_dst mu1 mu2 = true.
Proof.
  intros mu1 mu2 [Hsorted1 Hvalid1] [Hsorted2 Hvalid2] Hpeq.
  generalize dependent mu2.
  induction mu1 as [|(s1, p1) mu1' IH1]. 
  - intros mu2 Hsorted2 Hvalid2 Heq_mu. 
    destruct mu2 as [|(s2, p2) mu2'].
    + simpl. reflexivity.
    + simpl in *. unfold dst_equiv in Heq_mu. 
      specialize (Heq_mu s2). simpl in Heq_mu. rewrite state_eq_refl in Heq_mu.  
      assert (Hp_ge_0: (0 <= get_prob_in_dstate mu2' s2)%R). { 
        apply dst_Valid_prob_0_1. apply Valid_dist_inv in Hvalid2. apply Hvalid2. }
      unfold Valid_dist in Hvalid2. simpl in Hvalid2. destruct Hvalid2. 
      destruct H0. unfold prob_is_positive in H0. destruct H0.  
      assert (Hp_lt_0: (0 + 0 < p2 + get_prob_in_dstate mu2' s2)%R). { 
        apply Rplus_lt_le_compat. - apply H0. - apply Hp_ge_0. }
      rewrite Rplus_0_l in Hp_lt_0. rewrite <- Heq_mu in Hp_lt_0. 
      apply Rlt_irrefl in Hp_lt_0. exfalso. assumption.
  - intros mu2 Hsorted2 Hvalid2 Heq_mu. destruct mu2 as [|(s2, p2) mu2'].
    + simpl in *. unfold dst_equiv in Heq_mu.
      specialize (Heq_mu s1). simpl in Heq_mu. rewrite state_eq_refl in Heq_mu.  
      assert (Hp_ge_0: (0 <= get_prob_in_dstate mu1' s1)%R). { 
        apply dst_Valid_prob_0_1. apply Valid_dist_inv in Hvalid1. apply Hvalid1. }
      unfold Valid_dist in Hvalid1. destruct Hvalid1. destruct H0. 
      unfold prob_is_positive in H0. destruct H0.  
      assert (Hp_lt_0: (0 + 0 < p1 + get_prob_in_dstate mu1' s1)%R). { 
        apply Rplus_lt_le_compat. - apply H0. - apply Hp_ge_0. }
      rewrite Heq_mu in Hp_lt_0. rewrite Rplus_0_l in Hp_lt_0.  
      apply Rlt_irrefl in Hp_lt_0. exfalso. assumption.
    + simpl in *. destruct (beq_state s1 s2) eqn: Hst.
      * simpl in *. destruct (Req_bool p1 p2) eqn: Hp.
      ** simpl in *. apply IH1; try assumption. 
      ++ apply Sorted_inv in Hsorted1. apply Hsorted1.
      ++ apply Valid_dist_inv in Hvalid1. apply Hvalid1.
      ++ apply Sorted_inv in Hsorted2. apply Hsorted2.
      ++ apply Valid_dist_inv in Hvalid2. apply Hvalid2.
      ++ unfold dst_equiv. intro s.
      unfold dst_equiv in Heq_mu. specialize (Heq_mu s). simpl in Heq_mu. 
      destruct (beq_state s s1) eqn: Hst1.
      -- assert (Hst2: beq_state s s2 = true). { 
        eapply state_eq_trans. - apply Hst1. - apply Hst. }
      rewrite Hst2 in Heq_mu. fold get_prob_in_dstate in Heq_mu.
      unfold Req_bool in Hp. destruct (Req_EM_T p1 p2) eqn: H12.
      --- rewrite e in Heq_mu. apply Rplus_eq_reg_l in Heq_mu. apply Heq_mu.
      --- discriminate Hp.
      -- assert (Hst2: beq_state s s2= false). { 
            apply state_eq_compat_left with (s:= s) in Hst.
            rewrite Hst1 in Hst. rewrite Hst. reflexivity. }
        rewrite Hst2 in Heq_mu. apply Heq_mu.
      ** simpl in *. unfold dst_equiv in Heq_mu. specialize (Heq_mu s2).
        simpl in Heq_mu. rewrite state_eq_refl in Heq_mu. 
        rewrite state_eq_sym in Hst. rewrite Hst in Heq_mu.
        assert (Hprob_1: (get_prob_in_dstate mu1' s1 = 0)%R). { 
          apply Sorted_nodup_inv with (p1:=p1). apply Hsorted1. }
        assert (Hprob_2: (get_prob_in_dstate mu2' s2 = 0)%R). { 
          apply Sorted_nodup_inv with (p1:=p2). apply Hsorted2. }
        assert (Hprob_eq: (get_prob_in_dstate mu1' s1 = get_prob_in_dstate mu1' s2)%R). { 
            apply st_eq_get_prob_compat. rewrite state_eq_sym. apply Hst. }
        rewrite Hprob_2 in Heq_mu. rewrite Hprob_eq in Hprob_1. rewrite Hprob_1 in Heq_mu.
        apply Rplus_eq_reg_r in Heq_mu. rewrite Heq_mu in Hp.  
        rewrite Req_bool_refl in Hp. discriminate Hp.
      * simpl in *. destruct (ble_state s1 s2) eqn: Hcomp.
        ** apply insert_st_pair_sorted with (s:=s1) (p:=p1) in Hsorted2.
          simpl in Hsorted2. rewrite Hst in Hsorted2. rewrite Hcomp in Hsorted2.
          apply Sorted_nodup_inv in Hsorted2. simpl in Hsorted2. 
          rewrite Hst in Hsorted2. 
          unfold dst_equiv in Heq_mu. specialize (Heq_mu s1). simpl in Heq_mu.
          rewrite state_eq_refl in Heq_mu. rewrite Hst in Heq_mu.
          rewrite Hsorted2 in Heq_mu. 
          assert (Hprob: (0<= get_prob_in_dstate mu1' s1 )%R). { 
            apply dst_Valid_prob_0_1. apply Valid_dist_inv in Hvalid1. apply Hvalid1. }
          unfold Valid_dist in Hvalid1. destruct Hvalid1 as [Hsum1 Hpos1].
          simpl in Hpos1. destruct Hpos1 as [Hp1 Hpos1']. 
          unfold prob_is_positive in Hp1. destruct Hp1 as [Hp_gt Hp_le].
          assert (Hplus: (0+0 < p1 + get_prob_in_dstate mu1' s1)%R). { 
            apply Rplus_lt_le_compat. - apply Hp_gt. - apply Hprob. }
          rewrite Heq_mu in Hplus. rewrite Rplus_0_l in Hplus.
          apply Rlt_irrefl in Hplus. exfalso. assumption. 
        ** apply insert_st_pair_sorted with (s:=s2) (p:=p2) in Hsorted1.
          simpl in Hsorted1. rewrite state_eq_sym in Hst. rewrite Hst in Hsorted1.
          assert (Hcomp21: ble_state s2 s1 = true). { 
            apply st_nle_iff in Hcomp. destruct Hcomp. apply H0. }
          rewrite Hcomp21 in Hsorted1.
          apply Sorted_nodup_inv in Hsorted1. simpl in Hsorted1. 
          rewrite Hst in Hsorted1. 
          unfold dst_equiv in Heq_mu. specialize (Heq_mu s2). simpl in Heq_mu.
          rewrite state_eq_refl in Heq_mu. rewrite Hst in Heq_mu.
          rewrite Hsorted1 in Heq_mu. 
          assert (Hprob: (0<= get_prob_in_dstate mu2' s2 )%R). { 
            apply dst_Valid_prob_0_1. apply Valid_dist_inv in Hvalid2. apply Hvalid2. }
          unfold Valid_dist in Hvalid2. destruct Hvalid2 as [Hsum2 Hpos2].
          simpl in Hpos2. destruct Hpos2 as [Hp2 Hpos2']. 
          unfold prob_is_positive in Hp2. destruct Hp2 as [Hp_gt Hp_le].
          assert (Hplus: (0+0 < p2 + get_prob_in_dstate mu2' s2)%R). { 
            apply Rplus_lt_le_compat. - apply Hp_gt. - apply Hprob. }
          rewrite <- Heq_mu in Hplus. rewrite Rplus_0_l in Hplus.
          apply Rlt_irrefl in Hplus. exfalso. assumption.
Qed.

Lemma insert_pair_equiv_cons: forall s p mu ,
  ((insert_st_pair s p mu) == ((s,p) :: mu))%dist_state.
Proof.
  intros. induction mu as [|(s1,p1) mu1 Hmu].
  - simpl. apply dst_equiv_refl.
  - simpl. destruct (beq_state s s1) eqn:Hst1.
    + rewrite dst_cons_eq_add with (mu:= mu1). rewrite dst_cons_eq_add with (mu:= mu1).
    rewrite dst_cons_eq_add with (mu:= ([(s1, p1)] + mu1)%dist_state).
    apply dst_equiv_trans with (mu1:= ([(s, p)] + [(s1, p1)] + mu1)%dist_state).
      * apply dst_add_preserves_equiv; try apply dst_equiv_refl.
      unfold dst_equiv. intros s'. simpl. destruct (beq_state s' s1) eqn:Hst1'.
      ** apply state_eq_compat_left with (s:= s') in Hst1. rewrite <- Hst1 in Hst1'.
      rewrite Hst1'. symmetry. rewrite Rplus_assoc. reflexivity.
      ** apply state_eq_compat_left with (s:= s') in Hst1. rewrite <- Hst1 in Hst1'.
      rewrite Hst1'. reflexivity.
      * apply dst_equiv_sym. rewrite dst_add_assoc_eq. apply dst_equiv_refl.
    + destruct (ble_state s s1) eqn:Hst1_lt.
      * apply dst_equiv_refl.
      * rewrite dst_cons_eq_add with (mu:= (insert_st_pair s p mu1)). 
      apply dst_equiv_trans with (mu1:= [(s1, p1)] + ((s, p) :: mu1)%dist_state).
      ** apply dst_add_preserves_equiv; [apply dst_equiv_refl | try apply Hmu].
      ** rewrite dst_cons_eq_add with (mu:= ((s1, p1) :: mu1)).
      repeat rewrite dst_cons_eq_add with (mu:= mu1). 
      rewrite <- dst_add_0_l with (mu:= [(s1,p1)]) at 1.
      rewrite <- dst_add_0_l with (mu:= [(s,p)]) at 2.
      apply dst_add_shuffle.
Qed.

Lemma dst_equiv_sort: forall mu, (mu == sort_dst mu)%dist_state.
Proof. 
  intros mu. induction mu as [|(s1,p1) mu' IH'].
  - simpl in *. apply dst_equiv_refl.
  - simpl. 
    assert (Hassump: (insert_st_pair s1 p1 (sort_dst mu') == (s1, p1) :: (sort_dst mu'))%dist_state) 
      by apply insert_pair_equiv_cons. 
    apply dst_equiv_sym. 
    apply dst_equiv_trans with (mu1:= (s1, p1) :: sort_dst mu'); try assumption.
    rewrite dst_cons_eq_add with (mu:= (sort_dst mu')). 
    rewrite dst_cons_eq_add with (mu:= mu').
    apply dst_add_preserves_equiv; try apply dst_equiv_refl.
    apply dst_equiv_sym. try apply IH'.
Qed.
Lemma dst_eq_implies_sum_probs_eq: forall mu0 mu1,
  beq_dst mu0 mu1 = true -> (sum_probs mu0 = sum_probs mu1)%R.
Proof.
  intros. generalize dependent mu1.
  induction mu0 as [|(s0,p0) mu0' IH]; destruct mu1 as [|(s1,p1) mu1'].
  - simpl. reflexivity.
  - simpl. discriminate.
  - simpl. discriminate.
  - simpl. intros. 
    apply andb_true_iff in H. destruct H.
    apply andb_true_iff in H. destruct H.
    unfold Req_bool in H1. destruct (Req_EM_T p0 p1) eqn: H01.
    + rewrite e. f_equal. apply IH. apply H0.
    + discriminate H1.
Qed.

Lemma dst_equiv_implies_sum_probs_eq: forall (mu0 mu1:dist_state), 
  Valid_dist mu0 -> Valid_dist mu1 ->
  mu0 == mu1 -> 
  (sum_probs mu0 = sum_probs mu1)%R.
Proof.
  intros. 
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
  assert (Hsum_sorted:(sum_probs mu0_sorted = sum_probs mu1_sorted)%R). { 
    apply dst_eq_implies_sum_probs_eq.
    apply Sort_Valid_Peq_implies_beq_True. 
    - split; try assumption. 
    - split; assumption.
    - apply dst_equiv_trans with (mu1:= mu0). {
      apply dst_equiv_sym. apply dst_equiv_sort. }
      apply dst_equiv_trans with (mu1:= mu1).
      + assumption.
      + apply dst_equiv_sort. } 
  assert (Hsum0: (sum_probs mu0 = sum_probs mu0_sorted)%R). { 
    apply sum_probs_eq_sort. }
  assert (Hsum1: (sum_probs mu1 = sum_probs mu1_sorted)%R). { 
    apply sum_probs_eq_sort. }
  rewrite Hsum0. rewrite Hsum1. apply Hsum_sorted.
Qed.

Lemma conti_sort_eq: forall mu, 
  Sorted_dst mu-> sort_dst mu = mu.
Proof.
  intros. induction mu as [|(s,p) mu' IH].
  - simpl. reflexivity.
  - simpl. inversion H; subst.
    + simpl. reflexivity.
    + simpl in *.
    apply IH in H4. rewrite H4. simpl. destruct H2; subst.
    rewrite H0. rewrite H1. reflexivity.
Qed.

Lemma Valid_add_comm: forall (mu mu0: dist_state), 
  Valid_dist (mu + mu0) -> Valid_dist (mu0 + mu).
Proof.
  intros. destruct H. apply dst_positive_decom in H0. destruct H0. 
  rewrite dst_sum_prob_decom in H. rewrite Rplus_comm in H. 
  rewrite <- dst_sum_prob_decom in H.
  split; try assumption. apply dst_positive_decom. split; assumption.
Qed.

Lemma Sort_mult_cofe: forall mu p,  
  Sorted_dst mu -> Sorted_dst (p * mu)%dist_state.
Proof. 
  intros. induction mu as [|(s,p') mu' IH]; simpl; try assumption. 
  destruct (Req_dec_T p 0) eqn: Heq; try apply sorted0.
  inversion H; subst. 
  - simpl. apply sorted1.
  - simpl. rewrite Heq. apply sorted2; try assumption.
    simpl in IH. rewrite Heq in IH. apply IH. assumption.
Qed.
