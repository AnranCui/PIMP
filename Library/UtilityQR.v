From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qround.
From Stdlib Require Import QArith.QArith_base.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import List.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ClassicalChoice.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lra.

Import ListNotations.
Set Default Goal Selector "!".

(***************This file contains some basic R operation properties********************************************)  

Open Scope R_scope.
Definition Req_bool (x y : R) : bool :=
  match Req_EM_T x y with
  | left _ => true
  | right _ => false
  end.
  
Lemma Req_bool_refl (x : R) : Req_bool x x = true.
Proof.
  unfold Req_bool. destruct (Req_EM_T x x).
  - reflexivity. - simpl in *. unfold not in n. exfalso. apply n. reflexivity.
Qed.
Lemma Req_bool_comm (x y : R) : Req_bool x y = Req_bool y x.
Proof.
  unfold Req_bool. destruct (Req_EM_T x y).
  - destruct (Req_EM_T y x).
    + reflexivity. + rewrite e in n. contradiction. 
  - destruct (Req_EM_T y x).
    + rewrite e in n. contradiction. + reflexivity. 
Qed.
Lemma Req_bool_trans (x y z : R) : Req_bool x y = true -> Req_bool y z = true -> Req_bool x z = true.
Proof.
  unfold Req_bool. 
  destruct (Req_EM_T x y); destruct (Req_EM_T y z); destruct (Req_EM_T x z); intros; try reflexivity; try discriminate.
  rewrite e in n. rewrite <- e0 in n. contradiction.
  Qed. 
Lemma Req_true_implies_equal: forall x y : R, 
  Req_bool x y = true <-> x = y.
Proof.
  split.
  - intros H. destruct (Req_EM_T x y) eqn: H0; try assumption.
  unfold Req_bool in *. rewrite H0 in H. inversion H.
  - intros H. unfold Req_bool in *. rewrite H. 
  destruct (Req_dec_T y y) eqn: H0; try reflexivity.
  contradiction.
Qed.
Lemma Req_bool_false_if_positive: forall p : R,
  (0 < p)%R -> Req_bool p 0 = false.
Proof.
  intros p Hps. unfold Req_bool. destruct (Req_EM_T p 0) eqn: Htemp.
  - rewrite e in Hps. apply Rlt_irrefl in Hps. contradiction.
  - reflexivity.
Qed.

Lemma Rmult_neq_0: forall (p0 p1: R), 
  Req_bool p0 0 = false -> Req_bool p1 0 = false -> 
  Req_bool (p0 * p1) 0 = false.
Proof.
  intros. unfold Req_bool in *.
  destruct (Req_EM_T p0 0) eqn: Hp0; try discriminate.
  destruct (Req_EM_T p1 0) eqn: Hp1; try discriminate.
  destruct (Req_EM_T (p0 * p1) 0) eqn: Hp0p1; try reflexivity.
  assert (He: (p0 * p1)%R = 0%R) by assumption.
  apply Rmult_integral in He. inversion He.
  - unfold not in n. exfalso. apply n. assumption.
  - unfold not in n0. exfalso. apply n0. assumption.
Qed.


Lemma R_plus_sub_eq_1: forall p1 : R, ((p1 + (1 - p1))%R = 1)%R.
Proof.
  intros p1. unfold Rminus. rewrite <- Rplus_comm. rewrite Rplus_assoc. 
  rewrite Rplus_opp_l. rewrite Rplus_0_r. reflexivity.
Qed. 

Lemma Rplus_1_minus_r p1 p2: (p1 + p2 = 1)%R -> (p1 = (1 - p2))%R.
Proof.
  intros. rewrite <- R_plus_sub_eq_1 with (p1:= p2) in H.
  rewrite Rplus_comm in H. apply Rplus_eq_reg_l in H.
  assumption. 
Qed.

Lemma Rplus_mult_le_interval: forall p0 p1 a b: R,
  (0 <= a <= 1)%R -> (0 <= b <= 1)%R ->
  (0 <= p0 <= 1)%R -> (0 <= p1 <= 1)%R ->
  (p0 + p1 <= 1)%R -> (0 <= (p0 * a + p1 * b) <= 1)%R.
Proof.
  intros p0 p1 a b Ha Hb Hp0 Hp1 Hsum.
  destruct Ha as [Ha1 Ha2]. destruct Hb as [Hb1 Hb2].
  destruct Hp0 as [Hp01 Hp02]. destruct Hp1 as [Hp11 Hp12].
  split.
  - rewrite <- Rplus_0_l with (r:= 0%R). apply Rplus_le_compat; apply Rmult_le_pos; try tauto.
  - apply Rle_trans with (r2:= (p0 * 1 + p1 * 1)%R).
    + apply Rplus_le_compat. 
      * apply Rmult_le_compat; try assumption. apply Rle_refl.
      * apply Rmult_le_compat; try assumption. apply Rle_refl.
    + repeat rewrite Rmult_1_r. assumption.
Qed.

Lemma R_01_decom3 : forall (p: R), 
  (0 <= p <= 1)%R <-> ((0 < p < 1)%R \/ (p = 1)%R \/ (p = 0)%R ).
Proof.
  split.
  { intros Hp.
    destruct Hp as [Hp1 Hp2].
    apply Rle_lt_or_eq_dec in Hp1. inversion Hp1.
    - apply Rle_lt_or_eq_dec in Hp2. inversion Hp2. 
      + left. split; assumption.
      + right. left. assumption.
    - right. right. rewrite H. reflexivity.
  }
  { intros H. destruct H as [Hcase1 | H].
    - destruct Hcase1. split; apply Rlt_le; assumption. 
    - destruct H as [Hcase2 | Hcase3].
      + rewrite Hcase2. split; try apply Rle_refl. apply Rle_0_1.
      + rewrite Hcase3. split; try apply Rle_refl. apply Rle_0_1.
  }
Qed.
Lemma R_01_split : forall (p: R), (0 <= p <= 1)%R <-> ((p = 0)%R \/ (0 < p <= 1)%R).
Proof.
  split.
  { intros Hp.
    destruct Hp as [Hp1 Hp2].
    apply Rle_lt_or_eq_dec in Hp1. inversion Hp1.
    - right. split; assumption.
    - left. rewrite H. reflexivity.
  }
  { intros H. inversion H.
    - rewrite H0. split. + apply Rle_refl. + apply Rle_0_1.
    - destruct H0. split.
      + apply Rlt_le. assumption.  + assumption.
  }
Qed.

Lemma Rbound_loss: forall (p: R), (0 < p < 1)%R -> (0 <= p <= 1)%R.
Proof.
 intros. destruct H. split; apply Rlt_le; assumption.
Qed.

Lemma Rp_1_minus_p_bounds: forall (p: R), (0 <= p <= 1)%R -> (0 <= 1 - p <= 1)%R.
Proof.
  intros. destruct H.
  split.
  - apply Rle_minus in H0. apply Ropp_le_cancel. rewrite Ropp_0. unfold Rminus in *. 
  rewrite Rplus_comm. rewrite Ropp_plus_distr. rewrite Ropp_involutive. apply H0.
  - apply Ropp_le_contravar in H.
    apply Rplus_le_compat_l with (r := 1%R) in H.
    unfold Rminus at 1. rewrite Ropp_0 in H. rewrite Rplus_0_r in H.
    apply H.
Qed.

Lemma Rp_lt1_minus_p_bounds: forall (p: R), (0 < p < 1)%R <-> (0 < 1 - p < 1)%R.
Proof.
  split. { 
    intros. destruct H. split.
    - apply Rlt_minus in H0. apply Ropp_lt_cancel. rewrite Ropp_0. unfold Rminus in *. 
    rewrite Rplus_comm. rewrite Ropp_plus_distr. rewrite Ropp_involutive. apply H0.
    - apply Ropp_lt_contravar in H.
    apply Rplus_lt_compat_l with (r := 1%R) in H.
    unfold Rminus at 1. rewrite Ropp_0 in H. rewrite Rplus_0_r in H.
    apply H. }
  intros. destruct H. 
  assert (Hp: 1 - (1 - p) = p). { field. }
  split. 
  - apply Rgt_minus in H0. rewrite Hp in H0. assumption.
  - apply Ropp_gt_contravar in H.
    apply Rplus_lt_compat_l with (r := 1%R) in H.
    rewrite Ropp_0 in H. rewrite Rplus_0_r in H.
    unfold Rminus in *. rewrite Hp in H.
    apply H.
Qed.

Lemma Rfrac_bound : forall a b : R,
  (0 <= a)%R ->
  (0 <= b)%R ->
  (0 <= a / (a + b) <= 1)%R.
Proof.
  intros a b Ha0 Hb0.
  inversion Ha0; inversion Hb0; subst; split. 
  - apply Rmult_le_pos; try assumption.
    apply Rlt_le. apply Rinv_0_lt_compat.
    apply Rplus_lt_0_compat; assumption. 
  - apply Rmult_le_reg_r with (r := (a + b)%R).
    + apply Rplus_lt_0_compat; assumption. 
    + rewrite Rdiv_def. rewrite Rmult_assoc. rewrite <- Rinv_l_sym.
      * rewrite Rmult_1_l. rewrite Rmult_1_r. rewrite <- Rplus_0_r with (r:= a) at 1.
      apply Rplus_le_compat_l. assumption.
      * apply Rplus_le_lt_0_neq_0; assumption.
  - rewrite Rplus_0_r with (r:= a). rewrite Rdiv_diag. 
    + apply Rle_0_1.
    + unfold not. intros. rewrite H0 in H. apply Rlt_irrefl in H. assumption.
  - rewrite Rplus_0_r with (r:= a). rewrite Rdiv_diag.
    + apply Rle_refl.
    + unfold not. intros. rewrite H0 in H. apply Rlt_irrefl in H. assumption.
  - rewrite Rplus_0_l. rewrite Rdiv_0_l. apply Rle_refl.
  - rewrite Rplus_0_l. rewrite Rdiv_0_l. apply Rle_0_1.
  - rewrite Rplus_0_l. rewrite Rdiv_0_l. apply Rle_refl.
  - rewrite Rplus_0_l. rewrite Rdiv_0_l. apply Rle_0_1.
Qed.

Lemma Rfrac_bound_neq0 : forall a b : R,
  (0 <= a <= 1)%R ->
  (0 <= b <= 1)%R ->
  (a <> 0)%R ->
  (0 < a / (a + b) <= 1)%R.
Proof.
  intros a b [Ha0 Ha1] [Hb0 Hb1] Ha.
  inversion Ha0; inversion Hb0; subst; split; try contradiction.
  - unfold Rdiv. apply Rmult_lt_0_compat; try assumption.
    apply Rinv_0_lt_compat.
    apply Rplus_lt_0_compat; assumption. 
  - apply Rmult_le_reg_r with (r := (a + b)%R).
    + apply Rplus_lt_0_compat; assumption. 
    + rewrite Rdiv_def. rewrite Rmult_assoc. rewrite <- Rinv_l_sym; try assumption.
      * rewrite Rmult_1_l. rewrite Rmult_1_r. rewrite <- Rplus_0_r with (r:= a) at 1.
        apply Rplus_le_compat_l. assumption.
      * apply Rplus_le_lt_0_neq_0; assumption.
  - rewrite Rplus_0_r with (r:= a). rewrite Rdiv_diag; try assumption. apply Rlt_0_1.
  - rewrite Rplus_0_r with (r:= a). rewrite Rdiv_diag; try assumption. apply Rle_refl.
Qed.

Lemma Rfrac_bound_lt1 : forall a b: R,
  (0 <= a <= 1)%R ->
  (0 <= b <= 1)%R ->
  (a <> 0)%R ->
  (b <> 0)%R ->
  (0 < a / (a + b) < 1)%R.
Proof.
  intros a b [Ha0 Ha1] [Hb0 Hb1] Ha Hb.
  inversion Ha0; inversion Hb0; subst; split; try contradiction.
  - unfold Rdiv. apply Rmult_lt_0_compat; try assumption.
    apply Rinv_0_lt_compat.
    apply Rplus_lt_0_compat; assumption. 
  - apply Rmult_lt_reg_r with (r := (a + b)%R).
    + apply Rplus_lt_0_compat; assumption. 
    + rewrite Rdiv_def. rewrite Rmult_assoc. rewrite <- Rinv_l_sym; try assumption.
      * rewrite Rmult_1_l. rewrite Rmult_1_r. rewrite <- Rplus_0_r with (r:= a) at 1.
        apply Rplus_lt_compat_l. assumption.
      * apply Rplus_le_lt_0_neq_0; assumption.
Qed.

Lemma Rfrac_bound_cofe_neq0 : forall a b p: R,
  (0 <= a <= 1)%R ->
  (0 <= b <= 1)%R ->
  0 < p <= 1 ->
  (a <> 0)%R ->
  (0 < a * p / (a + b) <= 1)%R.
Proof.
  intros a b p [Ha0 Ha1] [Hb0 Hb1] Hp Ha.
  destruct Hp. inversion Ha0; inversion Hb0; subst; split; try contradiction.
    - unfold Rdiv. apply Rmult_lt_0_compat; try assumption.
      + apply Rmult_lt_0_compat; try assumption.
      + apply Rinv_0_lt_compat.
      apply Rplus_lt_0_compat; assumption. 
    - apply Rmult_le_reg_r with (r := (a + b)%R).
      + apply Rplus_lt_0_compat; assumption. 
      + rewrite Rdiv_def. rewrite Rmult_assoc. rewrite <- Rinv_l_sym; try assumption.
        * rewrite Rmult_1_l. rewrite Rmult_1_r. rewrite <- Rplus_0_r with (r:= a * p) at 1.
          apply Rplus_le_compat.
        ** rewrite <- Rmult_1_r. apply Rmult_le_compat_l; try assumption.
        ** try apply Rlt_le; try assumption.
        * apply Rplus_le_lt_0_neq_0; assumption.
    - rewrite Rplus_0_r with (r:= a). unfold Rdiv. rewrite Rmult_assoc. rewrite Rmult_comm with (r1:= p). 
    rewrite <- Rmult_assoc. rewrite Rinv_r; try assumption. rewrite Rmult_1_l. assumption.
    - rewrite Rplus_0_r with (r:= a). unfold Rdiv. rewrite Rmult_assoc. rewrite Rmult_comm with (r1:= p). 
    rewrite <- Rmult_assoc. rewrite Rinv_r; try assumption. rewrite Rmult_1_l. assumption.
Qed.

Lemma Rp4_lt_1: forall p0 p1 p01 p11: R,
  (0 <= p0 <= 1)%R -> (0 <= p1 <= 1)%R -> 
  (p0 + p1 = 1)%R ->
  (0 < p01 < 1)%R -> (0 < p11 < 1)%R ->
  (0 < p0 * p01 + p1 * p11 < 1)%R.
Proof.
  intros p0 p1 p01 p11 H0 H1 Hsum H01 H11.
  destruct H0 as [H0_lower H0_upper].
  destruct H1 as [H1_lower H1_upper].
  destruct H01 as [H01_lower H01_upper].
  destruct H11 as [H11_lower H11_upper].
  split.
  { inversion H0_lower; inversion H1_lower.
  - apply Rplus_lt_0_compat; try apply Rmult_lt_0_compat; try assumption.
  - rewrite <- H0 in Hsum. rewrite <- Rplus_0_r in Hsum.
  apply Rplus_eq_reg_r in Hsum.
  rewrite Hsum. rewrite Rmult_1_l. 
  rewrite <- H0. rewrite Rmult_0_l. rewrite Rplus_0_r.
  try assumption.
  - rewrite <- H in Hsum. rewrite <- Rplus_0_l in Hsum.
  apply Rplus_eq_reg_l in Hsum.
  rewrite Hsum. rewrite Rmult_1_l. 
  rewrite <- H. rewrite Rmult_0_l. rewrite Rplus_0_l.
  try assumption.
  - rewrite <- H in Hsum. rewrite Rplus_0_l in Hsum.
  rewrite <- H0 in Hsum. symmetry in Hsum. 
  apply R1_neq_R0 in Hsum. contradiction.
  }
  { inversion H0_upper; inversion H1_upper.
  - rewrite <- Hsum. 
  rewrite <- Rmult_1_r with (r:= p0) at 2.
  rewrite <- Rmult_1_r with (r:= p1) at 2.
  apply Rplus_lt_compat.
    + inversion H0_lower; subst.
      * apply Rmult_lt_compat_l; try assumption.
      * rewrite Rplus_0_l in Hsum. rewrite Hsum in H0. 
      apply Rlt_irrefl in H0. contradiction.
    + inversion H1_lower; subst.
      * apply Rmult_lt_compat_l; try assumption.
      * rewrite Rplus_0_r in Hsum. rewrite Hsum in H. 
      apply Rlt_irrefl in H. contradiction.
  - rewrite H0 in Hsum. rewrite <- Rplus_0_l with (r:= 1%R) in Hsum at 2.
    apply Rplus_eq_reg_r in Hsum.
    rewrite Hsum. rewrite Rmult_0_l. rewrite Rplus_0_l.
    rewrite H0. rewrite Rmult_1_l. assumption.
  - rewrite H in Hsum. rewrite <- Rplus_0_r with (r:= 1%R) in Hsum at 2.
    apply Rplus_eq_reg_l in Hsum.
    rewrite Hsum. rewrite Rmult_0_l. rewrite Rplus_0_r.
    rewrite H. rewrite Rmult_1_l. assumption.
  - rewrite H in Hsum. rewrite <- Rplus_0_r with (r:= 1%R) in Hsum at 2.
    apply Rplus_eq_reg_l in Hsum.
    rewrite H0 in Hsum. 
    apply R1_neq_R0 in Hsum. contradiction.
  }
Qed.

Lemma Rdiv_ref: forall p0 p1 p01 p11 : R,
  (0 <= p0 <= 1)%R -> (0 <= p1 <= 1)%R ->
  (p0 + p1)%R = 1%R ->
  (0 < p01 < 1)%R -> (0 < p11 < 1)%R -> 
  ((p0 * p01 + p1 * p11) / (p0 * p01 + p1 * p11))%R = 1%R.
Proof.
  intros. destruct H as [Hp0_l Hp0_r]. destruct H0 as [Hp1_l Hp1_r].
  destruct H2 as [Hp01_l Hp01_r]. destruct H3 as [Hp11_l Hp11_r]. 
  apply Rdiv_diag. unfold not. intros Hsum.
  inversion Hp0_l; inversion Hp1_l; subst.
  - assert (Hcontra: (0 < (p0 * p01 + p1 * p11)%R)%R). {
    apply Rplus_lt_0_compat.
    - apply Rmult_lt_0_compat; try assumption.
    - apply Rmult_lt_0_compat; try assumption. }
    rewrite Hsum in Hcontra. apply Rlt_irrefl in Hcontra. assumption.
  - try rewrite Rmult_0_l in Hsum. try rewrite Rplus_0_r in *.
  rewrite H1 in Hsum. rewrite Rmult_1_l in Hsum. rewrite Hsum in Hp01_l. 
  apply Rlt_irrefl in Hp01_l. contradiction.
  - rewrite Rmult_0_l in Hsum. rewrite Rplus_0_l in *. 
  rewrite H1 in Hsum. rewrite Rmult_1_l in Hsum. rewrite Hsum in Hp11_l. 
  apply Rlt_irrefl in Hp11_l. contradiction.
  - try rewrite Rplus_0_r in H1. symmetry in H1. (* 反转 H 中的等式 *)
  apply R1_neq_R0 in H1. contradiction.
Qed.

Lemma R_leq_1 : forall a b : R, (*a_b_leq_1*)
  0 < a -> 0 <= b -> a + b <= 1 -> a <= 1 /\ b <= 1.
Proof.
  intros a b Ha Hb Hab.
  split.
  - (* 证明 a <= 1 *)
    apply Rplus_le_reg_r with b.
    apply Rle_trans with 1; try assumption.
    rewrite <- Rplus_0_r with (r:=1) at 1.
    apply Rplus_le_compat_l.
    assumption.
  - (* 证明 b <= 1 *)
    apply Rplus_le_reg_l with a.
    apply Rle_trans with 1; try assumption.
    rewrite <- Rplus_0_l with (r:=1) at 1.
    apply Rplus_le_compat_r.
    apply Rlt_le; assumption.
Qed.

Lemma Rplus_sub_lt_1 : forall a b : R,
  0 < a -> 0 < b -> a + b = 1 -> a < 1 /\ b < 1.
Proof.
  intros a b Ha Hb Hab.
  split.
  - rewrite <- Hab. rewrite <- Rplus_0_r with (r:= a) at 1.
    apply Rplus_gt_compat_l. assumption.
  - rewrite <- Hab. rewrite <- Rplus_0_l with (r:= b) at 1.
    apply Rplus_gt_compat_r. assumption.
Qed.


Lemma Rdiv_all_pos: forall  A B C p01 p11 : R,
  0 <= A -> 0 <= B -> 0 <= C -> 0 <= p01 -> 0 <= p11 ->
  0 <= C * p01 / (p01 * A + p11 * B).
Proof.
  intros. unfold Rdiv. apply Rmult_le_pos.
  - apply Rmult_le_pos; try assumption.
  - inversion H; subst.
    + inversion H0; subst.
      * inversion H2; subst.
      ** inversion H3; subst.
      ++ apply Rlt_le. apply Rinv_0_lt_compat. apply Rplus_lt_0_compat; apply Rmult_lt_0_compat; try assumption.
      ++ rewrite Rmult_0_l. rewrite Rplus_0_r. apply Rlt_le. apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; try assumption.
      ** inversion H3; subst.
      ++ rewrite Rmult_0_l. rewrite Rplus_0_l. apply Rlt_le. apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; try assumption.
      ++ repeat rewrite Rmult_0_l. rewrite Rplus_0_r. rewrite <- Rdiv_1_l. rewrite Rdiv_0_r. apply Rle_refl.
      * inversion H2; subst.
      ** inversion H3; subst.
      ++ rewrite Rmult_0_r. rewrite Rplus_0_r. apply Rlt_le. apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; try assumption.
      ++ rewrite Rmult_0_l. rewrite Rplus_0_r. 
      apply Rlt_le. apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; try assumption.
      ** rewrite Rmult_0_l. rewrite Rmult_0_r. rewrite Rplus_0_r. rewrite <- Rdiv_1_l. rewrite Rdiv_0_r. apply Rle_refl.
    + rewrite Rmult_0_r. rewrite Rplus_0_l. inversion H0; inversion H3; subst.
      * apply Rlt_le. apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; try assumption.
      * rewrite Rmult_0_l. rewrite <- Rdiv_1_l. rewrite Rdiv_0_r. apply Rle_refl.
      * rewrite Rmult_0_r. rewrite <- Rdiv_1_l. rewrite Rdiv_0_r. apply Rle_refl.
      * rewrite Rmult_0_l. rewrite <- Rdiv_1_l. rewrite Rdiv_0_r. apply Rle_refl.
Qed.

Lemma Rdiv_num_le_den: forall p0 p1 A B C,
  0 <= A <= 1 -> 0 <= B <= 1 -> C = A + B -> C <> 0 -> 0 < p0 <=1 -> 0 < p1 <=1 ->
  0 < (p0 * A + p1 * B) / C <= 1.
Proof.
  intros p0 p1 A B C. intros HA HB HC HC0 Hp0 Hp1.
  rewrite HC. apply R_01_split in HA. 
  inversion HA.
  - rewrite H. rewrite Rmult_0_r. repeat rewrite Rplus_0_l. 
    rewrite H in HC. rewrite Rplus_0_l in HC. rewrite HC in HC0. 
    destruct HB. destruct Hp1. inversion H0; try assumption.
    + split.
      * unfold Rdiv. apply Rmult_lt_0_compat.
      ** apply Rmult_lt_0_compat; try assumption.
      ** apply Rinv_0_lt_compat; try assumption.
      * unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_r; try assumption. 
        rewrite Rmult_1_r. assumption.
    + rewrite <- H4 in HC0. contradiction. 
  - destruct H. destruct Hp0. destruct Hp1.
    apply R_01_split in HB. inversion HB.
    + rewrite H5. rewrite Rmult_0_r. repeat rewrite Rplus_0_r.
      unfold Rdiv. split.
      * apply Rmult_lt_0_compat.
      ** apply Rmult_lt_0_compat; try assumption.
      ** apply Rinv_0_lt_compat; try assumption.
      * unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_r; try assumption.
      ** rewrite Rmult_1_r. assumption.
      ** rewrite H5 in HC. rewrite Rplus_0_r in HC. rewrite HC in HC0. assumption.
    + destruct H5. split.
      * unfold Rdiv. apply Rmult_lt_0_compat.
      ** apply Rplus_lt_0_compat; try apply Rmult_lt_0_compat; try assumption.
      ** apply Rinv_0_lt_compat; apply Rplus_lt_0_compat; try assumption.
      * unfold Rdiv. apply Rmult_le_reg_r with (r:= (A+B)).
      ** apply Rplus_lt_0_compat; try assumption.
      ** rewrite Rmult_assoc. rewrite <- Rmult_comm with (r1:= (A+B)).
      rewrite Rinv_r; try assumption.
      ++ rewrite Rmult_1_r. rewrite Rmult_plus_distr_l.
      apply Rplus_le_compat; apply Rmult_le_compat_r; try assumption; 
        try apply Rlt_le; try assumption.
      ++ rewrite <- HC. assumption.
Qed.

Lemma Rdiv_num_lt_den: forall p0 p1 A B C,
  0 <= A <= 1 -> 0 <= B <= 1 -> C = A + B -> C <> 0 -> 0 < p0 < 1 -> 0 < p1 < 1 ->
  0 < (p0 * A + p1 * B) / C < 1.
Proof.
  intros p0 p1 A B C. intros HA HB HC HC0 Hp0 Hp1.
  rewrite HC. apply R_01_split in HA. 
  inversion HA.
  - rewrite H. rewrite Rmult_0_r. repeat rewrite Rplus_0_l. 
    rewrite H in HC. rewrite Rplus_0_l in HC. rewrite HC in HC0. 
    destruct HB. destruct Hp1. inversion H0; try assumption.
    + split.
      * unfold Rdiv. apply Rmult_lt_0_compat.
      ** apply Rmult_lt_0_compat; try assumption.
      ** apply Rinv_0_lt_compat; try assumption.
      * unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_r; try assumption. 
        rewrite Rmult_1_r. assumption.
    + rewrite <- H4 in HC0. contradiction. 
  - destruct H. destruct Hp0. destruct Hp1.
    apply R_01_split in HB. inversion HB.
    + rewrite H5. rewrite Rmult_0_r. repeat rewrite Rplus_0_r.
      unfold Rdiv. split.
      * apply Rmult_lt_0_compat.
      ** apply Rmult_lt_0_compat; try assumption.
      ** apply Rinv_0_lt_compat; try assumption.
      * unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_r; try assumption.
      ** rewrite Rmult_1_r. assumption.
      ** rewrite H5 in HC. rewrite Rplus_0_r in HC. rewrite HC in HC0. assumption.
    + destruct H5. split.
      * unfold Rdiv. apply Rmult_lt_0_compat.
      ** apply Rplus_lt_0_compat; try apply Rmult_lt_0_compat; try assumption.
      ** apply Rinv_0_lt_compat; apply Rplus_lt_0_compat; try assumption.
      * unfold Rdiv. apply Rmult_lt_reg_r with (r:= (A+B)).
      ** apply Rplus_lt_0_compat; try assumption.
      ** rewrite Rmult_assoc. rewrite <- Rmult_comm with (r1:= (A+B)).
      rewrite Rinv_r; try assumption.
      ++ rewrite Rmult_1_r. rewrite Rmult_plus_distr_l.
      apply Rplus_lt_compat; apply Rmult_lt_compat_r; try assumption; 
        try apply Rlt_le; try assumption.
      ++ rewrite <- HC. assumption.
Qed.

Lemma Rdiv_num_lt_den2: forall p A B, 
  0 < p < 1 -> 0 < A -> 0 <= B -> A + B <> 0 ->
  0 < (p * A + B)/ (A + B) < 1.
Proof.
  intros p A B. intros Hp HA HB HC. 
  inversion HB.
  - split.
    + apply Rdiv_lt_0_compat; apply Rplus_lt_0_compat; try assumption.
    destruct Hp. apply Rmult_lt_0_compat; assumption.
    + rewrite <- Rinv_r with (r:= A + B); try assumption.
    unfold Rdiv. apply Rmult_lt_compat_r. 
      * apply Rinv_0_lt_compat. apply Rplus_lt_0_compat; try assumption.
      * apply Rplus_lt_compat_r. rewrite <- Rmult_1_l. destruct Hp.
      apply Rmult_lt_compat_r; try assumption.
  - rewrite <- H. repeat rewrite Rplus_0_r. 
    split. 
    + apply Rdiv_lt_0_compat; try assumption. 
    destruct Hp. apply Rmult_lt_0_compat; assumption.
    + rewrite <- Rinv_r with (r:= A); try assumption.
      * unfold Rdiv. apply Rmult_lt_compat_r. 
      ** apply Rinv_0_lt_compat. assumption.
      ** rewrite <- Rmult_1_l. destruct Hp.
        apply Rmult_lt_compat_r; try assumption.
      * unfold not. intros. rewrite H0 in HA. apply Rlt_irrefl in HA. contradiction.
Qed.

Lemma R_ge0_iff: forall p, 0 <= p /\ p <> 0 <-> 0 < p.
Proof.
  intros p. split.
  - intros. destruct H. inversion H; try assumption. rewrite H1 in H0. contradiction.
  - intros. split.
    + apply Rlt_le. assumption. + symmetry. apply Rlt_not_eq. assumption.
Qed.


Lemma Rdiv_pA_in_01: forall p A B, 
  0 < p < 1 -> 0 <= A -> 0 <= B -> 
  A <> 0 -> A + B <> 0 ->
  0 < p * A / (A + B) < 1.
Proof.
  intros p A B. intros Hp HA HB. intros.
  assert (HAgt0: 0 < A). {apply R_ge0_iff. split; assumption. }
  destruct HB; try assumption.
  - split. 
    + apply Rdiv_lt_0_compat; try assumption. 
      * destruct Hp. apply Rmult_lt_0_compat; assumption. 
      * apply Rplus_lt_0_compat; try assumption.
    + rewrite <- Rinv_r with (r:= A+B); try assumption.
      unfold Rdiv. apply Rmult_lt_compat_r. 
      * apply Rinv_0_lt_compat. apply Rplus_lt_0_compat; try assumption.
      * apply Rlt_trans with (r2:= A). 
      ** rewrite <- Rmult_1_l. destruct Hp.
      apply Rmult_lt_compat_r; try assumption.
      ** rewrite <- Rplus_0_r at 1. apply Rplus_lt_compat_l; assumption.
  - rewrite <- H1. rewrite Rplus_0_r. 
  split. 
    + apply Rdiv_lt_0_compat; try assumption. 
    destruct Hp. apply Rmult_lt_0_compat; assumption.
    + rewrite <- Rinv_r with (r:= A); try assumption.
    unfold Rdiv. apply Rmult_lt_compat_r. 
      * apply Rinv_0_lt_compat. assumption.
      * rewrite <- Rmult_1_l. destruct Hp.
      apply Rmult_lt_compat_r; try assumption.
Qed.

Lemma R_inte_help: forall p C, 0 < C -> 0 < p/C <= 1 -> 0 < p.
Proof.
  intros. destruct H0. unfold Rdiv in H0. apply Rinv_0_lt_compat in H.
  apply Rmult_lt_reg_r with (r:= /C); try assumption.
  rewrite Rmult_0_l. assumption.
Qed.

Lemma Rmult4_assoc: forall r s t u: R, (r * s * t * u) = (r * s * u * t).
Proof.
  intros. rewrite Rmult_assoc; rewrite Rmult_assoc.
  rewrite Rmult_assoc; rewrite Rmult_assoc.
  apply Rmult_eq_compat_l with (r:= r).
  apply Rmult_eq_compat_l with (r:= s).
  apply Rmult_comm.
Qed.

Lemma Rplus_gt0_linear: forall p0 p1 A B, 
  0 < p0 -> 0 < p1 -> 
  0 <= A -> 0 <= B ->
  0 < A + B ->
  0 < p0 * A + p1 * B.
Proof.
  intros p0 p1 A B. intros Hp0 Hp1 HA HB HC.
  destruct HA; destruct HB.
  - apply Rplus_lt_0_compat; apply Rmult_lt_0_compat; try assumption.
  - rewrite <- H0. rewrite Rmult_0_r. rewrite Rplus_0_r. apply Rmult_lt_0_compat; try assumption.
  - rewrite <- H. rewrite Rmult_0_r. rewrite Rplus_0_l. apply Rmult_lt_0_compat; try assumption.
  - rewrite <- H in HC. rewrite <- H0 in HC. rewrite Rplus_0_l in HC. 
  apply Rlt_irrefl in HC. contradiction.
Qed.

Lemma goal_eq (p : R) :
  p <> 1 ->
  2 * p * (1 - / 2) = (1 - p) * (2 * p / (2 - 2 * p)).
Proof.
  intro Hp.
  assert (Hden : 2 - 2 * p <> 0) by nra. 
  replace (1 - / 2) with (/2) by lra.
  assert (HL : 2 * p * (/2) = p) by lra.
  rewrite HL.
  replace (2 - 2 * p) with (2 * (1 - p)) by ring.
  assert (Hnp : 1 - p <> 0) by (intro H0; apply Hp; lra).
  unfold Rdiv. 
  field_simplify; auto.
Qed.

Lemma goal_eq_minus (p : R) :
  p <> 1 ->
  (1 - 2 * p) = (1 - p) * (1 - 2 * p / (2 - 2 * p)).
Proof.
  intro Hp. 
  assert (Hden : 2 - 2 * p <> 0) by nra. 
  replace (2 - 2 * p) with (2 * (1 - p)) by ring.
  apply (Rmult_eq_reg_r (2 - 2 * p)); try exact Hden.
  field_simplify; lra.
Qed.
