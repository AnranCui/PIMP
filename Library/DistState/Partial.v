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
Require Import Library.DistState.Support.
Require Import Library.DistState.ValidDst.
Require Import Library.DistState.Domain.
Require Import Library.DistState.Arithmetic.

Open Scope list_scope.
Open Scope R_scope.
Open Scope dstate_scope.

(*****************This file contains properties of "Partial" predicate constraints on partial ordered distribution states****************************************)

Lemma PD_inv: forall s p mu X, 
  partial_dst_Prop X ((s,p)::mu) -> partial_dst_Prop X mu.
Proof.
  intros. inversion H; subst. assumption.
Qed.

Lemma PD_decom: forall mu1 mu2 X, 
  partial_dst_Prop X (mu1 + mu2) <-> 
  partial_dst_Prop X mu1 /\ partial_dst_Prop X mu2.
Proof.
  intros. split. { 
  generalize dependent mu2. induction mu1 as [|(s, p) mu1' Hmu1]; intros.
  - simpl in *. split; try assumption. apply PD_nil.
  - simpl in *. inversion H; subst. 
    apply Hmu1 in H4. destruct H4. 
    split; try assumption.
    apply PD_cons; try assumption. }
  intros. generalize dependent mu2. 
  induction mu1 as [|(s, p) mu1' Hmu1]; intros.
  - simpl in *. destruct H; try assumption. 
  - destruct H. inversion H; subst. simpl. 
  apply PD_cons; try assumption. apply Hmu1; try assumption.
  split; try assumption.
Qed.

Lemma PD_mult_coef: forall mu X p, 
  partial_dst_Prop X mu -> partial_dst_Prop X (p * mu).
Proof.
  intros mu X p H. generalize dependent X. generalize dependent p. 
  induction mu as [|(s, p') mu' Hmu]; intros.
  - simpl in *. apply PD_nil.
  - simpl in *. destruct (Req_dec_T p 0) eqn: Hp. 
    + apply PD_nil.
    + inversion H; subst. apply PD_cons; try assumption. 
    apply Hmu; try assumption.
Qed.

Lemma pd_mult_preserve_PD: forall pd p, partial_dst_Prop (dom pd) (p * mu pd).
Proof.
  intros pd p. destruct pd. 
  apply PD_mult_coef; try assumption.
Qed.


Lemma Peq_dom_PD_Prop: forall mu dom X, 
  (X == dom)%domain -> 
    partial_dst_Prop dom mu ->
    partial_dst_Prop X mu .
Proof.
  intros mu dom X Heq HPD. generalize dependent X. 
  induction mu as [|(s, p) mu' Hmu]; intros.
  - apply PD_nil.
  - inversion HPD; subst. apply PD_cons; try assumption. 
    + apply dom_equiv_trans with (l1:= dom); try assumption.
    + apply Hmu; try assumption.
Qed.

Lemma dst_eq_implies_PD_X_eq: forall X mu0 mu1, 
  beq_dst mu0 mu1 = true -> 
  partial_dst_Prop X mu0 -> 
  partial_dst_Prop X mu1.
Proof.
  intros X mu0 mu1 Hmu HPD.
  generalize dependent mu1. generalize dependent X.
  induction mu0 as [|(s0, p0) mu0' Hmu]; destruct mu1 as [|(s1,p1) mu1']; intros; try assumption.
  - simpl in *. discriminate.
  - simpl in *. discriminate.
  - simpl in Hmu0. apply andb_true_iff in Hmu0. destruct Hmu0.
    apply andb_true_iff in H. destruct H. 
    apply PD_cons; try assumption.
    + inversion HPD; subst. 
      apply st_eq_implies_dom_equiv in H.
      apply dom_equiv_trans with (l1:= (return_domain s0)); try assumption.
    + apply Hmu; try assumption. 
    apply PD_inv in HPD; try assumption.
Qed.

Lemma insert_PD: forall s p X mu, 
  (X == return_domain s)%domain /\ 
  partial_dst_Prop X mu <->
  partial_dst_Prop X (insert_st_pair s p mu).
Proof.
  intros. split. 
  { generalize dependent X. 
    induction mu as [|(s', p') mu' Hmu]; intros; try assumption.
    - simpl. destruct H. apply PD_cons; try assumption.
    - simpl. destruct H. destruct (beq_state s s') eqn: Hs; try assumption. 
      + inversion H0; subst. apply PD_cons; try assumption.
      + destruct (ble_state s s') eqn: Hle; try assumption. 
        * inversion H0; subst. apply PD_cons; try assumption.
        * inversion H0; subst. apply PD_cons; try assumption.
          apply Hmu; split; try assumption. 
  }
    generalize dependent X. 
    induction mu as [|(s', p') mu' Hmu]; intros; try assumption.
    - simpl in H. inversion H; subst. split; try assumption.
    - simpl in H. destruct (beq_state s s') eqn: Hs; try assumption. 
      + inversion H; subst. split. 
        * apply st_eq_implies_dom_equiv in Hs.
        apply dom_equiv_trans with (l1:= (return_domain s')); try assumption.
        apply dom_equiv_sym. assumption.
        * apply PD_cons; try assumption.
      + destruct (ble_state s s') eqn: Hle; try assumption. 
        * inversion H; subst. split; try assumption. 
        * inversion H; subst. split; try assumption.
        ** apply Hmu; try assumption.
        ** apply PD_cons; try assumption.
          apply Hmu. try assumption.
Qed.

Lemma sort_PD_X_eq: forall X mu, 
  partial_dst_Prop X mu ->
  partial_dst_Prop X (sort_dst mu).
Proof.
  intros X mu.
  intros HPD.
  generalize dependent X.
  induction mu as [|(s, p) mu' Hmu]; intros; try assumption.
  inversion HPD; subst. simpl. 
  apply insert_PD; try assumption. split; try assumption.
  apply Hmu. assumption. 
Qed.

Lemma sort_PD_X_eq_implies: forall X mu, 
  partial_dst_Prop X (sort_dst mu) ->
  partial_dst_Prop X mu.
Proof.
  intros X mu.
  intros HPD.
  generalize dependent X. 
  induction mu as [|(s, p) mu' Hmu]; intros; try assumption.
  simpl in HPD. apply insert_PD in HPD. destruct HPD.
  apply PD_cons; try assumption.
  apply Hmu; try assumption. 
Qed.

Lemma dst_equiv_implies_PD_same_dom: forall X mu0 mu1, 
  Valid_dist mu0 -> Valid_dist mu1 ->
  (mu0 == mu1)%dist_state -> 
  partial_dst_Prop X mu0 -> 
  partial_dst_Prop X mu1.
Proof.
  intros X mu0 mu1 H0 H1 Hmu_Peq HPD. 
  pose (mu0_sorted := sort_dst mu0).
  pose (mu1_sorted := sort_dst mu1).
  assert (Hsorted0: Sorted_dst mu0_sorted). { apply WF_dist_implies_sortdst_Sorted. assumption. }
  assert (Hsorted1: Sorted_dst mu1_sorted). { apply WF_dist_implies_sortdst_Sorted. assumption. }
  assert (Hvalid0: Valid_dist mu0_sorted). { apply Valid_implies_sort_Valid. assumption. }
  assert (Hvalid1: Valid_dist mu1_sorted). { apply Valid_implies_sort_Valid. assumption. }
  assert (Hsort_trans: mu0_sorted == mu1_sorted). { 
    apply dst_equiv_trans with (mu1:= mu0).
    - apply dst_equiv_sym. apply dst_equiv_sort.
    - apply dst_equiv_trans with (mu1:= mu1); [assumption|apply dst_equiv_sort]. }
  assert (Htemp_beq: beq_dst mu0_sorted mu1_sorted = true). { 
    apply Sort_Valid_Peq_implies_beq_True; try split; try assumption. } 
  apply sort_PD_X_eq in HPD. 
  apply dst_eq_implies_PD_X_eq with (X:= X) in Htemp_beq; try assumption.
  apply sort_PD_X_eq_implies. assumption.
Qed.

Lemma dst_add_equiv_implies_PD_decom: forall mu mu0 mu1 X, 
  partial_dst_Prop X mu -> 
  Valid_dist mu -> Valid_dist mu0 -> Valid_dist mu1 ->
  mu == mu0 + mu1 -> 
  sum_probs mu = (sum_probs mu0 + sum_probs mu1)%R ->
  partial_dst_Prop X mu0 /\ partial_dst_Prop X mu1.
Proof.
  intros. apply dst_equiv_implies_PD_same_dom with (X:= X) in H3; try assumption. 
  - apply PD_decom in H3. assumption.
  - split. 
    + rewrite <- dst_mult_1_l with (mu:= mu0).
      rewrite <- dst_mult_1_l with (mu:= mu1).
      apply Valid_linear_under_eq_prob; try assumption; try apply Rle_0_1.
      repeat rewrite Rmult_1_l. rewrite <- H4.
      destruct H0. assumption.
    + destruct H1. destruct H2. apply dst_positive_decom. split; try assumption.
Qed.

Lemma PD_remove_coef: forall p X mu, 
  (0 < p)%R->
  partial_dst_Prop X (p * mu) ->
  partial_dst_Prop X mu.
Proof.
  intros p X mu Hp HPD.
  generalize dependent X. induction mu as [|(s, p') mu' Hmu]; intros; try assumption.
  simpl in HPD. destruct (Req_dec_T p 0) eqn: H. 
    + rewrite e in Hp. apply Rlt_irrefl in Hp. contradiction.
    + inversion HPD; subst. 
    apply PD_cons; try assumption.
    apply Hmu. try assumption.
Qed.

Lemma PD_decom_linear: forall mu mu0 mu1 p0 p1 X, 
  partial_dst_Prop X mu -> Valid_dist mu ->
  Valid_dist mu0 -> Valid_dist mu1 ->
  (0 < p0 <= 1)%R -> (0 < p1 <=1)%R -> 
  mu == p0 * mu0 + p1 * mu1 -> 
  sum_probs mu = (p0*sum_probs mu0 + p1*sum_probs mu1)%R ->
  partial_dst_Prop X mu0 /\ partial_dst_Prop X mu1.
Proof.
  intros.
  repeat rewrite <- dst_sum_prob_coef_mult in H6.
  apply dst_add_equiv_implies_PD_decom with (X:= X) in H5; try assumption.
  - destruct H5. destruct H3. destruct H4.
    apply PD_remove_coef in H5; try assumption.
    apply PD_remove_coef in H7; try assumption.
    split; try assumption.
  - apply Valid_mult_cofe; try assumption.
    destruct H3. split; try assumption. apply Rlt_le; assumption.
  - apply Valid_mult_cofe; try assumption.
    destruct H4. split; try assumption. apply Rlt_le; assumption.
Qed.

Lemma PD_linear: forall p0 p1 pd0 pd1 X, 
  (0 <= p0)%R -> (0 <= p1)%R -> 
  (dom pd0 == X)%domain -> (dom pd1 == X)%domain ->
  partial_dst_Prop X (p0 * (mu pd0) + p1 * (mu pd1)).
Proof.
  intros p0 p1 pd0 pd1 X Hp0 Hp1 Hdom0 Hdom1.
  apply PD_decom. split.
  - apply PD_mult_coef; try assumption. destruct pd0. simpl in *. 
    apply dom_equiv_sym in Hdom0.
    apply Peq_dom_PD_Prop with (mu:=mu) in Hdom0; try assumption.
  - apply PD_mult_coef; try assumption. destruct pd1. simpl in *. 
    apply dom_equiv_sym in Hdom1.
    apply Peq_dom_PD_Prop with (mu:=mu) in Hdom1; try assumption.
Qed.

(************************************************)
Lemma PD_bulid_one: forall s p mu X dom,
  partial_dst_Prop dom mu ->
  partial_dst_Prop dom (bulid_helper s p mu X).
Proof.
  intros s p mu X dom HPD. generalize dependent X. generalize dependent dom.
  induction mu as [|(s', p') mu' Hmu]; intros; try assumption.
  simpl. destruct (beq_state s (res_st_to_X s' X)) eqn: H'. 
    - inversion HPD; subst. apply PD_cons; try assumption.
    apply Hmu; try assumption.
    - apply Hmu; try assumption. inversion HPD; subst. try assumption.
Qed.

Lemma PD_bulid_proj: 
  forall pd_sub pd X, 
    partial_dst_Prop (dom pd) (bulid_dst_sub (mu pd_sub) (mu pd) X).
Proof.
  intros pd_sub pd X. 
  destruct pd_sub as [dom_sub mu_sub PD_sub].
  destruct pd as [dom mu PD].
  simpl in *. generalize dependent mu. generalize dependent X.
  induction mu_sub as [|(s', p') mu_sub' Hmu_sub]; intros; try assumption.
    + simpl. apply PD_nil.
    + simpl. apply PD_decom. split. 
      * apply PD_mult_coef. apply PD_bulid_one. try assumption.
      * apply Hmu_sub; try assumption. inversion PD_sub; subst. try assumption.
Qed.



(************Construct some special partial dist_state ***************************************)
Definition Sort_pd (pd : partial_dist) : partial_dist :=
  {| 
    dom := dom pd; 
    mu := sort_dst (mu pd);
    all_partial := sort_PD_X_eq (dom pd) (mu pd) (all_partial pd)
  |}.

Definition cofe_pd (pd : partial_dist) (p : R) : partial_dist :=
  {| 
    dom := dom pd; 
    mu := p * (mu pd);
    all_partial := PD_mult_coef (mu pd) (dom pd) p (all_partial pd)
  |}.

Lemma PD_add: forall pd1 pd2, 
  (pd1.(dom) == pd2.(dom))%domain -> 
  partial_dst_Prop (pd1.(dom)) (pd1.(mu) + pd2.(mu)).
Proof.
  intros pd1 pd2 Hdom. apply PD_decom. 
  destruct pd1. destruct pd2.
  split; try assumption.
  simpl in *. apply Peq_dom_PD_Prop with (mu:= mu0) in Hdom; try assumption.
Qed.

Definition pd_add (pd1 pd2: partial_dist) (Hdom: (pd1.(dom) == pd2.(dom))%domain) : partial_dist :=
  {|
    dom:= pd1.(dom) ;
    mu:= (pd1.(mu) + pd2.(mu))%dist_state ;
    all_partial:= PD_add pd1 pd2 Hdom
  |}.

(******************************************)
Lemma pd_sort_equiv: forall pd, Sort_pd pd ≡ pd. 
Proof. 
  intros pd. split; simpl; try apply dom_equiv_refl. 
  apply dst_equiv_sym. apply dst_equiv_sort. 
Qed.

(******************pd_equiv: reflexivity, symmetry, transitivity********************************)
Lemma pd_equiv_refl : forall pd, pd ≡ pd.
Proof.
  intros pd. destruct pd. 
  split; simpl; try apply dom_equiv_refl; apply dst_equiv_refl. 
Qed.

Lemma pd_equiv_sym: forall pd1 pd2, pd1 ≡ pd2 -> pd2 ≡ pd1.
Proof.
  intros pd1 pd2 Heq. destruct pd1. destruct pd2. destruct Heq. 
  split; simpl in *. 
  - try apply dom_equiv_sym; assumption. 
  - try apply dst_equiv_sym. assumption. 
Qed.

Lemma pd_equiv_trans: forall pd0 pd1 pd2,
  pd0 ≡ pd1 -> pd1 ≡ pd2 -> pd0 ≡ pd2.
Proof.
  intros. destruct pd0. destruct pd1. destruct pd2. 
  destruct H. destruct H0. 
  split; simpl in *. 
  - try apply dom_equiv_trans with (l1:= dom0); try assumption. 
  - try apply dst_equiv_trans with (mu1:= mu0); assumption. 
Qed.