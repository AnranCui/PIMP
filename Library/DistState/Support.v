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
Require Import Library.DistState.Arithmetic.

Open Scope list_scope.
Open Scope nat_scope.
Open Scope Q_scope.
Open Scope state_scope.

(** Support set ***********************************************************)
Lemma map_dst_decom: forall (mu0 mu1: dist_state ), 
  map fst (mu0 + mu1)%dist_state = (map fst mu0) ++ (map fst mu1).
Proof.
  intros mu0 mu1. generalize dependent mu1. 
  induction mu0 as [|(s,p) mu0' Hmu0]; intros mu1.
  - simpl. reflexivity.
  - simpl. f_equal. apply Hmu0.
Qed.

(***************in_supp ****************)
Lemma in_supp_beq_supp_compat: forall l0 l1 st,
  beq_supp l0 l1 = true -> 
  is_in_supp st l0 = is_in_supp st l1.
Proof.
  intros. generalize dependent l1.
  induction l0 as [|s0 l0' IH]; destruct l1 as [|s1 l1']; 
    intros; simpl in *; try reflexivity; try discriminate.
  apply andb_true_iff in H. destruct H.
  assert (Htest: beq_state st s0 = beq_state st s1). { 
    apply state_eq_compat_left. assumption. }
  destruct (beq_state st s1).
    + simpl. apply orb_true_iff. left. assumption.
    + simpl. rewrite Htest. simpl. apply IH. apply H0.
Qed. 

Lemma in_supp_st_eq_compat: forall s0 s1 ls, 
  beq_state s0 s1 = true ->
  is_in_supp s0 ls = is_in_supp s1 ls.
Proof.
  intros. generalize dependent s1. generalize dependent s0.
  induction ls as [|s' ls' IH]; intros.
  - simpl. reflexivity.
  - simpl. 
    destruct (beq_state s0 s') eqn:Hs0; 
      destruct (beq_state s1 s') eqn:Hs1; simpl; try reflexivity. 
      * assert (Hcontra: beq_state s1 s' = true).  
          { apply state_eq_trans with s0; try assumption. rewrite state_eq_sym. assumption. }
        rewrite Hs1 in Hcontra. discriminate Hcontra.
      * apply state_eq_compat_left with (s:= s') in H. rewrite state_eq_sym in Hs0. 
      rewrite state_eq_sym in Hs1. rewrite Hs0 in H. rewrite Hs1 in H. discriminate.
      * apply IH; try assumption.
Qed.

Lemma in_supp_insert_eq: forall (ls: supp) (s s': local_st), 
  is_in_supp s (insert_st s' ls) = beq_state s s' || is_in_supp s ls.
Proof.
  intros. destruct (is_in_supp s (insert_st s' ls)) eqn: Hbool.
  - induction ls as [|s0 supp0 Hsupp].
    + simpl in Hbool. apply orb_true_iff in Hbool. destruct Hbool.
      * simpl. rewrite H. simpl. reflexivity.
      * discriminate H.
    + simpl. simpl in Hsupp. destruct (beq_state s s') eqn: Heq.
      * simpl. reflexivity.
      * simpl. simpl in Hsupp. destruct (beq_state s s0) eqn: Heq0.
        ** simpl. reflexivity.
        ** simpl. simpl in Hbool. destruct (beq_state s' s0) eqn: Heq1. 
          ++ simpl in Hbool. apply orb_true_iff in Hbool. 
          rewrite Heq0 in Hbool. destruct Hbool; try discriminate.
          rewrite H. reflexivity.
          ++ destruct (ble_state s' s0) eqn: Hcomp.
            -- simpl in Hbool. apply orb_true_iff in Hbool. rewrite Heq in Hbool.
            destruct Hbool; try discriminate.
            apply orb_true_iff in H. rewrite Heq0 in H. 
            destruct H; try discriminate.
            rewrite H. reflexivity.
            -- simpl in Hbool. apply orb_true_iff in Hbool. rewrite Heq0 in Hbool. 
            destruct Hbool; try discriminate.
            apply Hsupp. assumption.
  - induction ls as [|s0 supp0 Hsupp].
    + simpl in Hbool. simpl. rewrite orb_false_r in Hbool. 
      rewrite Hbool. simpl. reflexivity.
    + simpl in *. destruct (beq_state s s') eqn: Heq.
      * simpl. destruct (beq_state s' s0) eqn: Heq1.
        -- simpl in Hbool. apply orb_false_iff in Hbool. destruct Hbool.
        apply state_eq_compat_left with (s:= s0) in Heq.
        rewrite state_eq_sym in H. rewrite Heq in H. 
        rewrite state_eq_sym in H. rewrite Heq1 in H. discriminate H.
        -- destruct (ble_state s' s0) eqn: Hcomp.
          ++ simpl in Hbool. apply orb_false_iff in Hbool. destruct Hbool. 
          rewrite Heq in H. discriminate H.
          ++ simpl in Hbool. apply orb_false_iff in Hbool. destruct Hbool.
          simpl in Hsupp. apply Hsupp. apply H0.
      * simpl. simpl in Hsupp. destruct (beq_state s' s0) eqn: Heq1.
        -- simpl in Hbool. rewrite Hbool. reflexivity.
        -- destruct (beq_state s s0) eqn: Heq0.
          ** simpl. destruct (ble_state s' s0) eqn: Hcomp.
          ++ simpl in Hbool. apply orb_false_iff in Hbool. destruct Hbool.
          apply orb_false_iff in H0. destruct H0. rewrite H0 in Heq0. discriminate Heq0.
          ++ simpl in Hbool. apply orb_false_iff in Hbool. destruct Hbool.
          rewrite H in Heq0. discriminate Heq0.
          ** simpl. destruct (ble_state s' s0) eqn: Hcomp.
          ++ simpl in Hbool. apply orb_false_iff in Hbool. destruct Hbool.
          apply orb_false_iff in H0. destruct H0. rewrite H1. reflexivity.
          ++ simpl in Hbool. apply orb_false_iff in Hbool. destruct Hbool.
          apply Hsupp. apply H0.
Qed.

Lemma not_insupp_iff_probs_0: forall s mu, 
  Valid_dist mu ->
  is_in_supp s (supp_mu mu) = false <->
    (get_prob_in_dstate mu s = 0)%R.
Proof.
  intros s mu HWF. split. {
    intros Hnot. 
    induction mu as [|(s0, p0) mu' IH]; simpl; intros; try reflexivity.
    unfold supp_mu in Hnot. simpl in Hnot. 
    rewrite insert_st_pair_fst_eq_insert_st in Hnot.
    rewrite in_supp_insert_eq in Hnot.
    apply orb_false_iff in Hnot. destruct Hnot. 
    rewrite H. apply IH; try assumption. 
    apply Valid_dist_inv in HWF. assumption. }
    intros. induction mu as [|(s0, p0) mu' IH]; simpl; intros; try reflexivity.
    unfold supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st.
    rewrite in_supp_insert_eq. apply orb_false_iff.
    simpl in *. destruct (beq_state s s0) eqn: Hs.
    - apply Valid_dist_conj in HWF. destruct HWF.
    destruct H0. destruct H2. destruct H2.
    apply dst_Valid_prob_0_1 with (s:= s) in H1. destruct H1.
    rewrite <- H in H1. rewrite <- Rplus_0_l in H1. apply Rplus_le_reg_r in H1.
    apply Rle_not_lt in H1. unfold not in H1. apply H1 in H2. contradiction.
    - split; try reflexivity. apply Valid_dist_inv in HWF. apply IH; try assumption.
Qed.

Lemma in_supp_iff_posi_prob: 
  forall mu s, Valid_dist mu ->
    is_in_supp s (supp_mu mu) = true <-> 
    (exists p: R, (0 < p)%R /\ (get_prob_in_dstate mu s = p)%R).
Proof.
  intros mu s Hvalid. split.
  - intro Hlist. induction mu as [|(s1,q1) mu1' Hmu1].
    + simpl in *. discriminate Hlist.
    + simpl in *. unfold supp_mu in Hlist. simpl in Hlist. 
    apply Valid_dist_conj in Hvalid. destruct Hvalid as [Hs1 Hvalid'].
    unfold Valid_dist in Hs1. destruct Hs1. 
    unfold positive_probs in H0. destruct H0.
    unfold prob_is_positive in H0. destruct H0 as [Hq1_gt_0 Hq1_le_1].
    destruct (beq_state s s1) eqn: Hst.
      * exists (q1 + get_prob_in_dstate mu1' s)%R. split; try reflexivity.
      assert (Hget_prob: (0 <= (get_prob_in_dstate mu1' s)%R <= 1)%R). { 
        apply dst_Valid_prob_0_1. apply Hvalid'. }
      destruct Hget_prob as [Hget_prob0 Hget_prob1].
      rewrite <- Rplus_0_r with (r:=0%R). apply Rplus_lt_le_compat; try assumption.
      * apply Req_bool_false_if_positive in Hq1_gt_0.
      rewrite insert_st_pair_fst_eq_insert_st in Hlist; try assumption.
      rewrite in_supp_insert_eq in Hlist. apply orb_true_iff in Hlist. 
      destruct Hlist as [ | ].
        ** rewrite Hst in H0. inversion H; discriminate.
        ** unfold supp_mu in Hmu1. specialize (Hmu1 Hvalid' H0).
        destruct Hmu1 as [q [Hq Hp]]. rewrite <- Rplus_0_l in Hp.
        exists q. rewrite Rplus_0_l in Hp. split; try assumption.
  - intro Hq. destruct Hq as [q [Hq Hprob]]. induction mu as [|(s1,q1) mu1' Hmu1].
    + simpl in Hprob. rewrite <- Hprob in Hq. apply Rlt_irrefl in Hq. contradiction.
    + unfold supp_mu. simpl.
    apply Valid_dist_conj in Hvalid. destruct Hvalid as [Hs1 Hvalid'].
    unfold Valid_dist in Hs1. destruct Hs1. 
    unfold positive_probs in H0. destruct H0.
    unfold prob_is_positive in H0. destruct H0 as [Hq1_gt_0 Hq1_le_1].
    apply Req_bool_false_if_positive in Hq1_gt_0.
    rewrite insert_st_pair_fst_eq_insert_st; try assumption. 
    rewrite in_supp_insert_eq.
    apply orb_true_iff. simpl in Hprob. 
    destruct (beq_state s s1) eqn: Hst.
    * left. reflexivity.
    * right. specialize (Hmu1 Hvalid' Hprob). unfold supp_mu in Hmu1. apply Hmu1.
Qed.

Lemma in_supp_mu_app_or:  
  forall mu mu0 mu1 st,
  Valid_dist mu ->
  Valid_dist mu0 ->
  Valid_dist mu1 -> 
  (mu == mu0 + mu1)%dist_state -> 
  is_in_supp st (supp_mu mu) = true -> 
  is_in_supp st (supp_mu mu0) = true \/ is_in_supp st (supp_mu mu1) = true.
Proof.
  intros mu mu0 mu1 st Hvalid Hvalid0 Hvalid1 Hmu_Peq Hinlist.
  apply in_supp_iff_posi_prob in Hinlist; try assumption.
  destruct Hinlist.
  unfold dst_equiv in Hmu_Peq. specialize (Hmu_Peq st).
  rewrite Hmu_Peq in H. 
  rewrite get_prob_decom in H.
  assert (Hvalid0_copy: Valid_dist mu0). { exact Hvalid0. }
  apply dst_Valid_prob_0_1 with (s:= st) in Hvalid0.
  destruct Hvalid0.
  apply Rle_lt_or_eq_dec in H0. inversion H0.
  - left. apply in_supp_iff_posi_prob; try assumption. 
    exists (x - (get_prob_in_dstate mu1 st))%R. destruct H.
    split.
    * unfold Rminus. rewrite <- H3. rewrite Rplus_assoc. 
    rewrite Rplus_opp_r. rewrite Rplus_0_r. assumption.
    * rewrite <- H3. ring.
  - right. rewrite<- H2 in H. rewrite Rplus_0_l in H. apply in_supp_iff_posi_prob; try assumption.
    exists x. assumption.
Qed.

Lemma in_supp_insert_st: forall ls s, is_in_supp s (insert_st s ls) = true.
Proof.
  intros. induction ls as [ |s' l' IH]. 
  - simpl. apply orb_true_iff. left. apply state_eq_refl.
  - simpl. destruct (beq_state s s') eqn: Hs. 
    + simpl. apply orb_true_iff. left. assumption.
    + destruct (ble_state s s') eqn: Hle.
      * simpl. apply orb_true_iff. left. apply state_eq_refl.
      * simpl. apply orb_true_iff. right. apply IH.
Qed.

Lemma in_supp_mu_cons_head: forall mu s p, 
  is_in_supp s (supp_mu ((s, p) :: mu)) = true.
Proof. 
  intros. unfold supp_mu. simpl. 
  rewrite insert_st_pair_fst_eq_insert_st. 
  apply in_supp_insert_st. 
Qed.

Lemma in_supp_mu_cons_r: forall mu st s p, 
    is_in_supp st (supp_mu mu) = true ->
      is_in_supp st (supp_mu ((s, p) :: mu)) = true.
Proof.
  intros mu st s p H. induction mu as [|(s', p') mu' IH]; intros.
  - simpl in H. discriminate H.
  - unfold supp_mu. simpl. simpl in H.
  rewrite insert_st_pair_fst_eq_insert_st; try assumption.
  rewrite in_supp_insert_eq. apply orb_true_iff. 
  right. assumption.
Qed.

(*Sortedsupp *)
Inductive Sorted_supp : supp -> Prop :=
  | sorted_nil : Sorted_supp []
  | sorted_single : forall s, Sorted_supp [s]
  | sorted_cons : forall s1 s2 l,
      beq_state s1 s2 = false /\ ble_state s1 s2 = true ->
      Sorted_supp (s2 :: l) ->
      Sorted_supp (s1 :: s2 :: l).

Lemma Sort_supp_inv: forall s ls, 
  Sorted_supp (s::ls) -> Sorted_supp ls.
Proof.
  intros. induction ls as [|s' l' IH]; intros.
  - apply sorted_nil.
  - inversion H; subst. assumption.
Qed.

Lemma Sort_supp_cons_le_inv: forall s1 s2 ls,
  (s1 <= s2)%state -> Sorted_supp (s2::ls) -> 
  Sorted_supp (s1::ls).
Proof.
  intros. induction ls as [|s' l' IH]; intros.
  - apply sorted_single. 
  - inversion H0; subst. 
    apply st_le_iff in H; try assumption.
    destruct H.
    + apply sorted_cons; try assumption.
    apply st_nle_iff. apply st_nle_iff in H3.
    apply st_eq_ble_compat_left with (s:= s') in H; try assumption.
    rewrite H. assumption.
    + apply sorted_cons; try assumption. 
    apply st_nle_iff. apply st_nle_iff in H3.
    apply st_nle_trans with (s1:= s2); assumption. 
Qed.


Lemma Sort_supp_cons_insert_st_preserve: forall s0 s ls, 
  (ble_state s s0 = false)%state ->
  Sorted_supp (s0::ls) ->
  Sorted_supp (s0 :: insert_st s ls).
Proof.
  intros s0 s ls. intros Hle HS. 
  generalize dependent s0.
  induction ls as [|s' l' IH]; intros.
  - simpl. apply sorted_cons; try apply sorted_single; try assumption.
    apply st_nle_iff. assumption.
  - simpl. destruct (beq_state s s') eqn: Hs.
    + apply sorted_cons; try assumption. 
      * apply st_nle_iff. 
      apply st_eq_ble_compat_right with (s:= s0) in Hs; try assumption. 
      rewrite Hle in Hs. rewrite Hs. reflexivity.
      * inversion HS; subst. assumption.
    + destruct (ble_state s s') eqn: Hle'; try discriminate.
      * apply sorted_cons; try assumption. 
      ** apply st_nle_iff. assumption.
      ** apply sorted_cons; try assumption. 
      -- split; try assumption.
      -- inversion HS; subst. assumption.
      * apply sorted_cons; try assumption. 
      ** inversion HS; subst. assumption. 
      ** apply IH; try assumption.
      -- inversion HS. assumption.
Qed.

Lemma Sort_supp_insert_st_preserve: forall s ls, 
  Sorted_supp ls ->
  Sorted_supp (insert_st s ls).
Proof.
  intros s ls HSls. induction ls as [|s' l' IH]; intros.
  - apply sorted_single. 
  - simpl. destruct (beq_state s s') eqn: Hs. 
    + assumption.
    + destruct (ble_state s s') eqn: Hle; try discriminate.
      * apply sorted_cons; try assumption.
      -- split; try assumption.
      * apply Sort_supp_cons_insert_st_preserve; try assumption. 
Qed.

Lemma Sort_supp_if_WF_supp: forall mu, 
  Sorted_supp (supp_mu mu).
Proof.
  intros. unfold supp_mu. 
  induction mu as [|(s, p) mu IH]; simpl; intros.
  - apply sorted_nil.
  - rewrite insert_st_pair_fst_eq_insert_st.
    apply Sort_supp_insert_st_preserve; try assumption.
Qed.

Lemma supp_subset_nil_l: forall ls, is_supp_subset [] ls = true.
Proof.
  intros ls. induction ls as [|s ls' IH].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
Lemma supp_subset_refl: forall ls, is_supp_subset ls ls = true.
Proof.
  intros ls. induction ls as [|s ls IH]; simpl; try reflexivity.
  rewrite state_eq_refl. assumption.
Qed.

Lemma supp_subset_st_if_beq_st: forall s0 s1 ls,
  beq_state s0 s1 = true ->
  is_supp_subset [s0] ls = true ->
  is_supp_subset [s1] ls = true.
Proof.
  intros s0 s1 ls Hsub0 Hsub1. induction ls as [|s ls']; simpl in *; try assumption.
  destruct (beq_state s0 s) eqn: Hs0.
  - assert (Hs1: beq_state s1 s = true). { 
      rewrite state_eq_sym in Hsub0. apply state_eq_trans with (s1:= s0); try assumption. }
    rewrite Hs1. apply supp_subset_nil_l.
  - destruct (ble_state s0 s) eqn: Hle0; try discriminate.
  assert (Hle1: ble_state s1 s = false). {  
    apply st_eq_ble_compat_right with (s:= s) in Hsub0; try assumption.
    - rewrite Hsub0 in Hle0. assumption. }
  rewrite Hle1. simpl. apply st_nle_iff in Hle1. destruct Hle1.
  rewrite state_eq_sym in H. rewrite H. apply IHls'; try assumption.
Qed.

Lemma supp_subset_cons_implies_head: forall s l ls, 
  is_supp_subset (s::l) ls = true -> 
  is_supp_subset [s] ls = true.
Proof.
  intros s l ls H. 
  generalize dependent l. generalize dependent s.
  induction ls as [|s' l' IH]; intros.
  - simpl in H. discriminate.
  - simpl in *. destruct (beq_state s s') eqn: Hs'. 
    + destruct l' as [|s0 l0]; simpl; try reflexivity.
    + destruct (ble_state s s') eqn: Hle'.
     * discriminate.
     * apply IH with (l:= l). assumption.
Qed.


Lemma supp_subset_false_if_nle_state_head: forall s s0 ls,
  Sorted_supp (s0::ls) -> 
  ble_state s0 s = false -> 
  is_supp_subset [s] ls = false.
Proof.
  intros s s0 ls HSort Hle. induction ls as [| s' ls' IH]; intros.
  - simpl. reflexivity.
  - simpl. inversion HSort; subst.
    apply st_nle_iff in H1. 
    apply st_nle_trans with (s0:= s') in Hle; try assumption.
    apply st_nle_iff in Hle. destruct Hle. 
    rewrite H. rewrite H0. reflexivity.
Qed.

(***********************************************************)
Lemma in_supp_if_supp_subset_onest: forall s ls,
  is_supp_subset [s] ls = true ->
  is_in_supp s ls = true.
Proof.
  intros. induction ls as [| s' ls' IH].
  - simpl in H. discriminate.
  - simpl in *. destruct (beq_state s s') eqn: Hs. 
    + simpl. reflexivity.
    + simpl. destruct (ble_state s s') eqn: Hle. 
      * discriminate.
      * apply IH. assumption.
Qed.

Lemma not_in_supp_if_supp_subset_false: forall s ls,
  Sorted_supp ls ->
  is_supp_subset [s] ls = false ->
  is_in_supp s ls = false.
Proof.
  intros s ls HSort. induction ls as [| s' ls' IH]; intros.
  - simpl. reflexivity.
  - simpl in *. apply orb_false_iff.
    destruct (beq_state s s') eqn: Hs. 
    + rewrite supp_subset_nil_l in H. discriminate.
    + split; try reflexivity. destruct (ble_state s s') eqn: Hle. 
      * apply IH; try assumption.
      ** apply Sort_supp_inv in HSort. assumption.
      ** apply supp_subset_false_if_nle_state_head with (s0:= s'); try assumption.
      apply st_nle_iff. split; try assumption.
      * apply IH; try assumption. apply Sort_supp_inv in HSort. assumption.
Qed.


(********************加 右加******************************************)
Lemma supp_subset_cons_r: forall s l ls, 
  Sorted_supp (s::l) ->
  is_supp_subset l ls = true ->
  is_supp_subset l (s::ls) = true.
Proof.
  intros s l ls HS H. generalize dependent l. generalize dependent s.
  induction ls as [|s' l' IH]; intros.
  - destruct l as [|s0 l0]; try reflexivity. simpl in *. discriminate.
  - destruct l as [|s0 l0]; try reflexivity. inversion HS; subst. 
    simpl in H. destruct (beq_state s0 s') eqn: Hs'. 
    + simpl. destruct H2. rewrite state_eq_sym in H0. rewrite H0.
      assert (Hle: ble_state s0 s = false). { 
        apply st_nle_iff. split; try assumption. rewrite state_eq_sym. assumption. }
      rewrite Hle. rewrite Hs'. assumption.
    + destruct ( ble_state s0 s') eqn: Hle'; try  discriminate.
      simpl. destruct H2. rewrite state_eq_sym in H0. rewrite H0. 
      assert (Hle: ble_state s0 s = false). { 
      apply st_nle_iff. split; try assumption. rewrite state_eq_sym. assumption. } 
      rewrite Hle. rewrite Hs'. rewrite Hle'. assumption.
Qed.

(********************减: 右减 左减******************************)
Lemma supp_subset_inv_r: forall s l ls,  (*重要*)
  Sorted_supp (s::l) ->
  is_supp_subset l (s::ls) = true ->
  is_supp_subset l ls = true.
Proof.
  intros s l ls HS H. generalize dependent ls. generalize dependent s.
  induction l as [|s' l' IH]; intros; destruct ls as [|s0 l0]; try reflexivity.
  - simpl in H. inversion HS; subst. 
    destruct H2. rewrite state_eq_sym in H0.
    rewrite H0 in H. destruct (ble_state s' s); discriminate.
  - simpl in H. inversion HS; subst. 
    destruct H2. rewrite state_eq_sym in H0.
    rewrite H0 in H. assert (Hle: ble_state s' s= false). {
      apply st_nle_iff. split; try assumption. rewrite state_eq_sym. assumption. }
    rewrite Hle in H. simpl. assumption.
Qed.
Lemma supp_subset_inv_l: forall s l ls,  (*重要*)
  Sorted_supp (s::l) ->
  Sorted_supp ls ->
  is_supp_subset (s::l) ls = true ->
  is_supp_subset l ls = true.
Proof.
  intros s l ls HS HLS H. generalize dependent l. generalize dependent s.
  induction ls as [|s' l' IH]; intros. 
  - destruct l as [|s0 l0]; try reflexivity. simpl in *. discriminate.
  - simpl in H. destruct (beq_state s s') eqn: Hs'. 
    + destruct l as [|s0 l0]; simpl; try reflexivity. 
      destruct (beq_state s0 s') eqn: Hs0'. 
      * apply Sort_supp_inv in HS. apply Sort_supp_inv in HLS. 
        apply IH with (s:= s0); try assumption. 
      * inversion HS; subst. 
      assert (Hle': ble_state s' s0= true). {
        apply st_eq_ble_compat_right with (s:= s0) in Hs'; try assumption. 
        destruct H2. rewrite Hs' in H1. assumption. }
      assert (Htemp: ble_state s0 s' = false). {
        apply st_nle_iff. split; try assumption. rewrite state_eq_sym. assumption. }
      rewrite Htemp. assumption.
    + destruct (ble_state s s') eqn: Hle; try discriminate. 
      apply Sort_supp_inv in HLS. 
      specialize (IH HLS s l HS H). 
      apply supp_subset_cons_r; try assumption. 
      apply Sort_supp_cons_le_inv with (s2:= s); try assumption.
      apply st_le_iff. right. assumption.
Qed.

(*合并*)
Lemma supp_subset_cons_l: forall s l ls, 
  Sorted_supp (s::l) -> 
  Sorted_supp ls -> 
  is_supp_subset l ls = true -> 
  is_supp_subset [s] ls = true ->
  is_supp_subset (s::l) ls = true.
Proof.
  intros s l ls. intros HS HSls H1 H2.
  generalize dependent l. generalize dependent s.
  induction ls as [|s' l' IH]; intros.
  - simpl in *. discriminate.
  - simpl in H2. simpl. destruct (beq_state s s') eqn: Hs'. 
    + destruct l as [|s0 l0]; simpl; try assumption. 
      destruct (beq_state s0 s') eqn: Hs0'. 
      * inversion HS; subst. destruct H3. 
      rewrite state_eq_sym in Hs0'.
      apply state_eq_trans with (s2:= s0) in Hs'; try assumption.
      rewrite Hs' in H. discriminate.
      * simpl in H1. rewrite Hs0' in H1. 
      destruct (ble_state s0 s') eqn: Hle'; try discriminate.
      apply Sort_supp_inv in HS. 
      apply Sort_supp_inv in HSls.
      apply IH; try assumption.
      -- apply supp_subset_cons_implies_head in H1; try assumption.
      -- apply supp_subset_inv_l in H1; try assumption.
    + destruct (ble_state s s') eqn: Hle'; try discriminate.
      apply IH; try assumption.
      * apply Sort_supp_inv in HSls. assumption.
      * apply supp_subset_inv_r in H1; try assumption.
      apply Sort_supp_cons_le_inv with (s2:= s); try assumption. 
      apply st_le_iff. right. assumption.
Qed.


(*subsetsupp支撑集的传递性*)
Lemma supp_subset_trans_onest: forall s ls0 ls1, 
  Sorted_supp ls0 -> Sorted_supp ls1 ->
  is_supp_subset [s] ls0 = true -> 
  is_supp_subset ls0 ls1 = true ->
  is_supp_subset [s] ls1 = true.
Proof.
  intros s ls0 ls1 HS0 HS1 Hsub0 Hsub1. generalize dependent ls1.
  induction ls0 as [|s0 ls0']; simpl in *; intros; try discriminate.
  destruct (beq_state s s0) eqn: Hs0.
  - apply supp_subset_st_if_beq_st with (s0:= s0); try assumption. 
    + rewrite state_eq_sym. assumption.
    + apply supp_subset_cons_implies_head in Hsub1. assumption.
  - destruct (ble_state s s0) eqn: Hle0; try discriminate.
  apply IHls0'; try assumption.
    + apply Sort_supp_inv in HS0. assumption.
    + apply supp_subset_inv_l in Hsub1; try assumption.
Qed.

Theorem supp_subset_trans: forall ls0 ls1 ls2, (*重要*)
  Sorted_supp ls0 -> Sorted_supp ls1 -> Sorted_supp ls2 ->
  is_supp_subset ls0 ls1 = true -> 
  is_supp_subset ls1 ls2 = true ->
  is_supp_subset ls0 ls2 = true.
Proof.
  intros ls0 ls1 ls2 HSl0 HSl1 HSl2. 
  generalize dependent ls2. generalize dependent ls1.
  induction ls0 as [|s0 ls0' IH]; simpl; intros.
  - apply supp_subset_nil_l.
  - destruct ls1 as [|s1 ls1']; destruct ls2 as [|s2 ls2']; simpl in *; 
      try assumption; try discriminate. 
    assert (HSl0': Sorted_supp ls0'). { apply Sort_supp_inv in HSl0. assumption. }
    assert (HSl1': Sorted_supp ls1'). { apply Sort_supp_inv in HSl1. assumption. }
    assert (HSl2': Sorted_supp ls2'). { apply Sort_supp_inv in HSl2. assumption. }
    destruct (beq_state s0 s1) eqn: Hs01.
    + destruct (beq_state s1 s2) eqn: Hs12.
      * assert (Hs02: beq_state s0 s2 = true). { 
          apply state_eq_trans with (s1:= s1); assumption. }
      rewrite Hs02. apply IH with (ls1:= ls1'); try assumption.
      * assert (Hs02: beq_state s0 s2 = false). { 
          apply state_eq_compat_left with (s:= s2) in Hs01; try assumption. 
          rewrite state_eq_sym. rewrite Hs01. rewrite state_eq_sym. assumption. }
      rewrite Hs02. destruct (ble_state s1 s2) eqn: Hle12; try discriminate.
      assert (Hle02: ble_state s0 s2 = false). { 
        apply st_eq_ble_compat_right with (s:= s2) in Hs01; try assumption.
        rewrite Hs01. assumption. }
      rewrite Hle02. apply supp_subset_cons_l; try assumption.
      ** apply IH with (ls1:= ls1'); try assumption. 
      apply supp_subset_inv_l in H0; try assumption.
      ** apply supp_subset_cons_implies_head in H0; try assumption. 
      apply supp_subset_st_if_beq_st with (s0:= s1); try assumption.
      rewrite state_eq_sym. assumption.
    + destruct (ble_state s0 s1) eqn: Hle01; try discriminate. 
      destruct (beq_state s1 s2) eqn: Hs12.
      * assert (Hs02: beq_state s0 s2 = false). { 
          apply state_eq_compat_left with (s:= s0) in Hs12; try assumption. 
          rewrite <- Hs12. assumption. }
        rewrite Hs02. assert (Hle02: ble_state s0 s2 = false). {
          apply st_eq_ble_compat_left with (s:= s0) in Hs12; try assumption.
          rewrite <- Hs12. assumption. }
        rewrite Hle02. apply supp_subset_cons_l; try assumption.
      ** apply IH with (ls1:= ls1'); try assumption. 
      apply supp_subset_inv_l in H; try assumption.
      ** apply supp_subset_cons_implies_head in H. 
      apply supp_subset_trans_onest with (ls0:= ls1'); try assumption.
      * destruct (ble_state s1 s2) eqn: Hle12; try discriminate.
        assert (Hle02: ble_state s0 s2 = false). { 
          apply st_nle_trans with (s1:= s1); try assumption. }
        rewrite Hle02. apply st_nle_iff in Hle02. destruct Hle02.
        rewrite state_eq_sym in H1. rewrite H1.
         apply supp_subset_cons_l; try assumption.
      ** apply IH with (ls1:= ls1'); try assumption.
      -- apply supp_subset_inv_l in H; try assumption.
      -- apply supp_subset_inv_l in H0; try assumption.
      ** apply supp_subset_inv_l in H0; try assumption.
      apply supp_subset_cons_implies_head in H; try assumption. 
      apply supp_subset_trans_onest with (ls0:= ls1'); try assumption.
Qed.

Lemma in_supp_r_if_subset: forall s ls0 ls1, 
  is_supp_subset ls0 ls1 = true -> 
  is_in_supp s ls0 = true ->
  is_in_supp s ls1 = true.
Proof.
  intros s ls0 ls1 H. generalize dependent ls0. generalize dependent s.
  induction ls1 as [|s1 ls1' IH]; destruct ls0 as [|s0 ls0']; simpl; intros; try discriminate.
  apply orb_true_iff in H0. destruct H0.
  - apply orb_true_iff. destruct (beq_state s0 s1) eqn: Hs.
    * left. apply state_eq_trans with (s1:= s0); assumption. 
    * destruct (ble_state s0 s1) eqn: Hle; try discriminate. 
    right. simpl in H. apply IH with (ls0:= (s0 :: ls0')); try assumption. 
    simpl. apply orb_true_iff. left. assumption.
  - apply orb_true_iff. destruct (beq_state s0 s1) eqn: Hs.
    * right. apply IH with (ls0:= ls0'); try assumption.
    * destruct (ble_state s0 s1) eqn: Hle; try discriminate. 
    right. apply IH with (ls0:= (s0 :: ls0')); try assumption. 
    simpl. apply orb_true_iff. right. assumption.
Qed.

Lemma not_in_supp_l_if_subset: forall s ls0 ls1, (*重要*)
  Sorted_supp ls0 -> Sorted_supp ls1 ->
  is_supp_subset ls0 ls1 = true -> 
  is_in_supp s ls1 = false ->
  is_in_supp s ls0 = false.
Proof.
  intros s ls0 ls1. intros HSls0 HSls1 Hsubset Hnot.
  generalize dependent ls0. generalize dependent s.
  induction ls1 as [|s1 ls1' IH]; destruct ls0 as [|s0 ls0']; 
    simpl; intros; try discriminate; try reflexivity.
  apply orb_false_iff. destruct (beq_state s0 s1) eqn: Hs.
    - split. 
      + simpl in Hnot. apply orb_false_iff in Hnot. destruct Hnot.
      apply state_eq_compat_left with (s:= s) in Hs. 
      rewrite H in Hs. assumption.
      + apply IH; try assumption.
        * apply Sort_supp_inv in HSls1. assumption.
        * simpl in Hnot. apply orb_false_iff in Hnot. destruct Hnot. assumption.
        * apply Sort_supp_inv in HSls0. assumption.
    - destruct (ble_state s0 s1) eqn: Hle; try discriminate.
      split.
      + simpl in *. apply orb_false_iff in Hnot. destruct Hnot.
        apply supp_subset_cons_implies_head in Hsubset. 
        apply in_supp_if_supp_subset_onest in Hsubset.
        destruct (beq_state s s0)eqn: Hcontra; try reflexivity.
        apply in_supp_st_eq_compat with (ls:= ls1') in Hcontra.
        rewrite Hsubset in Hcontra. rewrite H0 in Hcontra. discriminate.
      + apply IH; try assumption. 
        * apply Sort_supp_inv in HSls1. assumption.
        * simpl in Hnot. apply orb_false_iff in Hnot. destruct Hnot. assumption.
        * apply Sort_supp_inv in HSls0. assumption.
        * apply supp_subset_inv_l in Hsubset; try assumption.
        **apply Sort_supp_inv in HSls1. assumption.
Qed.


(*跟insert*)
Lemma supp_subset_insert_st: forall s ls, 
  is_supp_subset [s] (insert_st s ls) = true.
Proof.
  intros s ls. induction ls as [|s0 ls' IH].
  - simpl. rewrite state_eq_refl. reflexivity.
  - simpl. destruct (beq_state s s0) eqn: Hs. 
    + simpl. rewrite Hs. simpl. apply supp_subset_nil_l.
    + destruct (ble_state s s0) eqn: Hle.
      * simpl. rewrite state_eq_refl. reflexivity.
      * simpl. rewrite Hs. rewrite Hle. assumption.
Qed.
(******************跟insert相关的减 **************)
Lemma supp_subset_insert_implies_subset_onest: forall s l ls, 
  Sorted_supp l ->
  Sorted_supp ls ->
  is_supp_subset (insert_st s l) ls = true -> 
  is_supp_subset [s] ls = true.
Proof.
  intros s l ls HS HLS H.
  generalize dependent ls. generalize dependent s.
  induction l as [|s' l' IH]; intros. 
  - simpl in H. assumption.
  - simpl in *. destruct (beq_state s s') eqn: Hs'. 
      * apply supp_subset_cons_implies_head in H. rewrite state_eq_sym in Hs'. 
      apply supp_subset_st_if_beq_st with (ls:= ls) in Hs'; try assumption.
      * destruct (ble_state s s') eqn: Hle'.
        + apply supp_subset_cons_implies_head in H. assumption.
        + apply supp_subset_inv_l in H; try assumption.
        -- apply IH; try assumption. 
        ++ apply Sort_supp_inv in HS. assumption.
        -- apply Sort_supp_cons_insert_st_preserve; try assumption. 
Qed.  

Lemma supp_subset_insert_implies_subset: forall s l ls, 
  Sorted_supp l ->
  Sorted_supp ls ->
  is_supp_subset (insert_st s l) ls = true -> 
  is_supp_subset l ls = true.
Proof.
  intros s l ls HS HLS H. 
  generalize dependent ls. generalize dependent s.
  induction l as [|s' l' IH]; intros. 
  - destruct ls as [|s0 l0]; try reflexivity.
  - simpl in H. destruct (beq_state s s') eqn: Hs; try assumption. 
    destruct (ble_state s s') eqn: Hle; try discriminate.
    + apply supp_subset_inv_l with (s:= s); try assumption.
    apply sorted_cons; try assumption. 
      * split; try assumption.
    + destruct ls as [|s0 l0]; try reflexivity. 
      * simpl in *. discriminate.
      * simpl in H. simpl. destruct (beq_state s' s0) eqn: Hs'; try assumption.
      ** apply Sort_supp_inv in HLS. apply Sort_supp_inv in HS.
      apply IH with (s:= s); try assumption. 
      ** destruct (ble_state s' s0) eqn: Hle'.
      -- discriminate.
      -- apply supp_subset_cons_l; try assumption.
      ++ apply Sort_supp_inv in HLS. assumption.
      ++ assert (Htemp: Sorted_supp l'). { apply Sort_supp_inv in HS. assumption. }
      apply Sort_supp_inv in HLS. 
      specialize (IH Htemp s l0 HLS).
      apply supp_subset_inv_l in H; try assumption. 
      ---apply IH in H. assumption.
      ---apply Sort_supp_cons_insert_st_preserve; try assumption.
      ++ apply supp_subset_cons_implies_head in H. assumption.
Qed. 

(******************跟insert相关的加 **************)
Lemma supp_subset_implies_insert_onest: forall s0 s1 ls,
  is_supp_subset [s0] ls = true ->
  is_supp_subset [s0] (insert_st s1 ls) = true.
Proof.
  intros s0 s1 ls H. generalize dependent s1. 
  induction ls as [|s ls' IH]; intros.
  - simpl in *. discriminate.
  - simpl in *. destruct (beq_state s0 s) eqn: Hs0. 
    + destruct (beq_state s1 s) eqn: Hs1.
      * simpl. rewrite Hs0. apply supp_subset_nil_l.
      * destruct (ble_state s1 s) eqn: Hle1.
      ** simpl in *. assert (Hs01: beq_state s0 s1 = false). { 
          apply state_eq_compat_left with (s:= s1) in Hs0.
          rewrite <- Hs0 in Hs1. rewrite state_eq_sym. assumption. }  
      rewrite Hs01. rewrite Hs0. 
      assert (Hle01: ble_state s0 s1 = false). { 
          apply st_eq_ble_compat_left with (s:= s1) in Hs0. 
          - rewrite <- Hs0 in Hle1. apply st_nle_iff. split; try assumption.
          rewrite state_eq_sym. assumption. }
      rewrite Hle01. apply supp_subset_nil_l.
      ** simpl. rewrite Hs0. apply supp_subset_nil_l.
    + destruct (ble_state s0 s) eqn: Hle0; try discriminate.
    destruct (beq_state s1 s) eqn: Hs1.
      * simpl. rewrite Hs0. rewrite Hle0. assumption.
      * destruct (ble_state s1 s) eqn: Hle1.
      ** simpl in *. destruct (beq_state s0 s1) eqn: Hs01; try reflexivity.
      assert (Hle01: ble_state s0 s1 = false). { 
        apply st_nle_iff. split.
        - rewrite state_eq_sym. assumption.
        - apply st_le_trans with (s1:= s); try assumption. 
          + apply st_le_iff. right. assumption. }
      rewrite Hle01. rewrite Hs0. rewrite Hle0. assumption.
      ** simpl. rewrite Hs0. rewrite Hle0. apply IH; try assumption.
Qed.
Lemma supp_subset_implies_insert_right: forall s ls0 ls1,
  Sorted_supp ls0 -> 
  Sorted_supp ls1 -> 
  is_supp_subset ls0 ls1 = true ->
  is_supp_subset ls0 (insert_st s ls1) = true.
Proof.
  intros s ls0 ls1 HSl0 HSl1 H. generalize dependent ls1.
  induction ls0 as [|s0 ls0' IH]; simpl; intros.
  - simpl. apply supp_subset_nil_l.
  - destruct ls1 as [|s1 ls1']; simpl in H; try discriminate. 
    simpl. destruct (beq_state s0 s1) eqn: Hs01. 
    + destruct (beq_state s s1) eqn: Hs1.
      * simpl. rewrite Hs01. assumption.
      * destruct (ble_state s s1) eqn: Hle1.
      ** simpl. assert (Hs0: beq_state s0 s = false). {
            apply state_eq_compat_left with (s:= s) in Hs01.
            rewrite <- Hs01 in Hs1. rewrite state_eq_sym. assumption. }
        rewrite Hs0.
        assert (Hle0: ble_state s0 s = false). { 
          apply st_eq_ble_compat_left with (s:= s) in Hs01; try assumption.
          rewrite <- Hs01 in Hle1. apply st_nle_iff. split; try assumption.
          rewrite state_eq_sym. assumption. }
        rewrite Hle0. rewrite Hs01. assumption.
      ** simpl. rewrite Hs01. 
      apply Sort_supp_inv in HSl0. apply Sort_supp_inv in HSl1.
      apply IH; try assumption.
    + destruct (ble_state s0 s1) eqn: Hle01; try discriminate.
    destruct (beq_state s s1) eqn: Hs1.
      * simpl. rewrite Hs01. rewrite Hle01. assumption.
      * destruct (ble_state s s1) eqn: Hle1.
      ** simpl. apply st_le_iff in Hle1. destruct Hle1.
      ++ rewrite H0 in Hs1. discriminate.
      ++ assert (Hle0: ble_state s0 s = false). {
          apply st_nle_trans with (s1:= s1); try assumption. }
      rewrite Hle0. rewrite Hs01. rewrite Hle01. 
      apply st_nle_iff in Hle0. destruct Hle0. 
      rewrite state_eq_sym in H1. rewrite H1.
      assumption.
      ** simpl. rewrite Hs01. rewrite Hle01. 
      apply supp_subset_cons_l; try assumption.
      -- apply Sort_supp_inv in HSl1. apply Sort_supp_insert_st_preserve; try assumption. 
      -- apply IH; try assumption.
      ++ apply Sort_supp_inv in HSl0. assumption.
      ++ apply Sort_supp_inv in HSl1. assumption.
      ++ apply supp_subset_inv_l in H; try assumption.
      apply Sort_supp_inv in HSl1. assumption.  
      -- apply supp_subset_cons_implies_head in H. 
      apply supp_subset_implies_insert_onest; try assumption.
Qed.

Lemma supp_subset_insert_preserves: forall s l ls,
  Sorted_supp l ->
  Sorted_supp ls -> 
  is_supp_subset l ls = true -> 
  is_supp_subset [s] ls = true ->
  is_supp_subset (insert_st s l) ls = true.
Proof.
  intros s l ls. intros HSl HSls Hsubl Hsubs.
  generalize dependent ls. generalize dependent s.
  induction l as [|s0 l0 IH]; intros.
  - simpl in *. assumption.
  - simpl in *. destruct (beq_state s s0) eqn: Hs0. 
    + destruct ls as [|s' l']; simpl; try assumption. 
    + destruct (ble_state s s0) eqn: Hle0.
      * apply supp_subset_cons_l; try assumption.
      ** apply sorted_cons; try assumption. split; try assumption.
      * apply supp_subset_cons_l; try assumption.
      ** apply Sort_supp_cons_insert_st_preserve; try assumption.
      ** apply IH; try assumption.
      ++ apply Sort_supp_inv in HSl. assumption.
      ++ apply supp_subset_inv_l in Hsubl; try assumption. 
      ** apply supp_subset_cons_implies_head in Hsubl. assumption.
Qed.
      
Lemma supp_subset_insert_compat: forall s ls0 ls1,
  Sorted_supp ls0 -> 
  Sorted_supp ls1 -> 
  is_supp_subset ls0 ls1 = true ->
  is_supp_subset (insert_st s ls0) (insert_st s ls1) = true.
Proof.
  intros s ls0 ls1 HSls0 HSls1 H. generalize dependent ls1.
  induction ls0 as [|s0 ls0' IH]; destruct ls1 as [|s1 ls1']; intros.
  - simpl. rewrite state_eq_refl. reflexivity.
  - simpl in *. destruct (beq_state s s1) eqn: Hs. 
    + simpl. rewrite Hs. simpl. apply supp_subset_nil_l.
    + destruct (ble_state s s1) eqn: Hle. 
      * simpl. rewrite state_eq_refl. reflexivity.
      * simpl. rewrite Hs. rewrite Hle. simpl. 
      apply supp_subset_insert_st.
  - simpl in *. discriminate.
  - simpl in *. 
  assert (HSls0': Sorted_supp ls0'). { apply Sort_supp_inv in HSls0. assumption. }
  assert (HSls1': Sorted_supp ls1'). { apply Sort_supp_inv in HSls1. assumption. }
  destruct (beq_state s0 s1) eqn: Hs01. 
    + destruct (beq_state s s0) eqn: Hs0. 
      * assert (Hs1: beq_state s s1 = true). { 
          apply state_eq_trans with (s1:= s0); try assumption. }
      rewrite Hs1. simpl. rewrite Hs01. assumption.
      * assert (Hs1: beq_state s s1 = false). { 
          apply state_eq_compat_left with (s:= s) in Hs01.
          rewrite Hs01 in Hs0. assumption. }
      rewrite Hs1.
      destruct (ble_state s s0) eqn: Hle0. 
      ** assert (Hle1: ble_state s s1 = true). { 
          apply st_eq_ble_compat_left with (s:= s) in Hs01.
          - rewrite Hs01 in Hle0. assumption. }
      rewrite Hle1. simpl. 
      rewrite state_eq_refl. rewrite Hs01. assumption.
      ** assert (Hle1: ble_state s s1 = false). { 
          apply st_eq_ble_compat_left with (s:= s) in Hs01.
          - rewrite Hs01 in Hle0. assumption. }
      rewrite Hle1. simpl. rewrite Hs01. 
      apply IH; try assumption.
    + destruct (ble_state s0 s1) eqn: Hle01; try discriminate.
      destruct (beq_state s s0) eqn: Hs0. 
      * assert (Hs1: beq_state s s1 = false). { 
          apply state_eq_compat_left with (s:= s1) in Hs0.
          rewrite state_eq_sym in Hs0. rewrite Hs0.
          rewrite state_eq_sym. assumption. }
      rewrite Hs1. 
      assert(Hle1: ble_state s s1 = false). { 
        apply st_eq_ble_compat_left with (s:= s1) in Hs0; try assumption.
        apply st_nle_iff in Hle01. destruct Hle01.
        rewrite H1 in Hs0. apply st_nle_iff. split; try assumption.
        rewrite state_eq_sym. assumption. }
      rewrite Hle1. simpl. rewrite Hs01. rewrite Hle01. 
      apply supp_subset_cons_l; try assumption.
      -- apply Sort_supp_insert_st_preserve; try assumption.
      -- apply supp_subset_implies_insert_right; try assumption.
      apply supp_subset_inv_l in H; try assumption.
      -- apply supp_subset_implies_insert_onest; try assumption.
      apply supp_subset_cons_implies_head in H; try assumption.
      * destruct (ble_state s s0) eqn: Hle0. 
      ** destruct (beq_state s s1) eqn: Hs1.
      -- simpl. rewrite Hs1. assumption.
      -- destruct (ble_state s s1) eqn: Hle1.
      ++ simpl. rewrite state_eq_refl. rewrite Hs01. rewrite Hle01. assumption.
      ++ simpl. rewrite Hs1. rewrite Hle1. 
      apply supp_subset_implies_insert_right with (s:= s) in H; try assumption.
      apply supp_subset_cons_l; try assumption.
      +++ apply sorted_cons; try assumption. split; try assumption.
      +++ apply Sort_supp_insert_st_preserve; try assumption.
      +++ apply supp_subset_insert_st.
      ** destruct (beq_state s s1) eqn: Hs1.
      -- simpl. rewrite Hs01. rewrite Hle01.
      assert (Hcontra: ble_state s s1 = false). {
        apply st_nle_trans with (s1:= s0); try assumption. }
      apply st_nle_iff in Hcontra. destruct Hcontra. 
      rewrite state_eq_sym in H0.
      rewrite H0 in Hs1. discriminate.
      -- assert (Hle1: ble_state s s1 = false). {
          apply st_nle_trans with (s1:= s0); try assumption. }
        rewrite Hle1. simpl. rewrite Hs01. rewrite Hle01. 
        apply supp_subset_cons_l; try assumption.
      ++ apply Sort_supp_cons_insert_st_preserve; try assumption.
      ++ apply Sort_supp_insert_st_preserve; try assumption.
      ++ apply IH; try assumption. 
      apply supp_subset_inv_l in H; try assumption.
      ++ apply supp_subset_implies_insert_onest; try assumption.
      apply supp_subset_cons_implies_head in H; try assumption.
Qed.
(***支撑集关于 mu的性质*****)
Lemma supp_mu_subset_cons: forall s p mu, (*重要*)
  is_supp_subset (supp_mu mu) (supp_mu ((s,p)::mu)) = true.
Proof.
  intros s p mu. induction mu as [|(s0, p0) mu' IH]; simpl; try reflexivity.
  unfold supp_mu. simpl. repeat rewrite insert_st_pair_fst_eq_insert_st. 
  apply supp_subset_implies_insert_right; try assumption.
  - apply Sort_supp_insert_st_preserve; try assumption. 
    apply Sort_supp_if_WF_supp; try assumption.
  - apply Sort_supp_insert_st_preserve; try assumption. 
    apply Sort_supp_if_WF_supp; try assumption.
  - apply supp_subset_refl. 
Qed.

Lemma supp_mu_subset_decom_add_l: forall mu1 mu2, 
  is_supp_subset (supp_mu mu1) (supp_mu (mu1 + mu2)%dist_state) = true.
Proof.  
  intros mu1 mu2. generalize dependent mu2.
  induction mu1 as [|(s1, p1) mu1' IH1]; intros; simpl; try assumption.
  - apply supp_subset_nil_l. 
  - unfold supp_mu. simpl. repeat rewrite insert_st_pair_fst_eq_insert_st. 
  apply supp_subset_insert_compat. 
    + apply Sort_supp_if_WF_supp; try assumption.
    + apply Sort_supp_if_WF_supp; try assumption.
    + apply IH1.
Qed.

Lemma supp_mu_subset_decom_add_r: forall mu1 mu2, 
  is_supp_subset (supp_mu mu2) (supp_mu (mu1 + mu2)%dist_state) = true.
Proof.  
  intros mu1 mu2. generalize dependent mu2.
  induction mu1 as [|(s1, p1) mu1' IH1]; intros; simpl; try assumption.
  - apply supp_subset_refl. 
  - unfold supp_mu. simpl. repeat rewrite insert_st_pair_fst_eq_insert_st. 
    apply supp_subset_implies_insert_right. 
    + apply Sort_supp_if_WF_supp; try assumption.
    + apply Sort_supp_if_WF_supp; try assumption.
    + apply IH1.
Qed.


Lemma supp_mu_subset_conj_mu: forall s p mu mu', 
  is_supp_subset (supp_mu ((s,p)::mu)) (supp_mu mu') = true ->
  is_supp_subset [s] (supp_mu mu') = true /\ is_supp_subset (supp_mu mu) (supp_mu mu') = true.
Proof.
  intros s p mu mu'. intros Hsubset.
  assert (HVmu: Sorted_supp (supp_mu mu)). { apply Sort_supp_if_WF_supp.  }
  assert (HVspmu': Sorted_supp (supp_mu mu')). { apply Sort_supp_if_WF_supp. }
  unfold supp_mu in Hsubset. simpl in Hsubset.
  rewrite insert_st_pair_fst_eq_insert_st in Hsubset.
  split. 
  - apply supp_subset_insert_implies_subset_onest in Hsubset; try assumption. 
  - apply supp_subset_insert_implies_subset in Hsubset; try assumption.
Qed.

Lemma supp_mu_subset_sp_conj_mu: forall s p mu l, 
  Sorted_supp l -> 
  is_supp_subset (supp_mu ((s,p)::mu)) l = true ->
  is_supp_subset [s] l = true /\ is_supp_subset (supp_mu mu) l = true.
Proof.
  intros s p mu l. intros HSpl Hsubset.
  assert (HVmu: Sorted_supp (supp_mu mu)). { apply Sort_supp_if_WF_supp.  }
  unfold supp_mu in Hsubset. simpl in Hsubset.
  rewrite insert_st_pair_fst_eq_insert_st in Hsubset.
  split. 
  - apply supp_subset_insert_implies_subset_onest in Hsubset; try assumption. 
  - apply supp_subset_insert_implies_subset in Hsubset; try assumption.
Qed.

Lemma supp_mu_subset_add_l: forall mu1 mu2 l, 
  Sorted_supp l -> 
  is_supp_subset (supp_mu mu1) l = true /\ is_supp_subset (supp_mu mu2) l = true ->
  is_supp_subset (supp_mu (mu1 + mu2)%dist_state) l = true.
Proof.
  intros mu1 mu2 l HSl Hsub. 
  generalize dependent mu2. generalize dependent l.
  induction mu1 as [|(s1, p1) mu1' IH1]; intros; try assumption.
  - simpl in *. destruct Hsub. assumption.
  - simpl in *. destruct Hsub.
    apply supp_mu_subset_sp_conj_mu in H; try assumption.
    destruct H. 
    unfold supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st.
    assert (HS': Sorted_supp (map fst (sort_dst (mu1' + mu2)%dist_state))). {
      apply Sort_supp_if_WF_supp.  }
    apply supp_subset_insert_preserves; try assumption.
    apply IH1; try assumption. 
    * split; try assumption.
Qed.

Lemma supp_mu_subset_decom_l: forall mu1 mu2 l, 
  Sorted_supp l -> 
  is_supp_subset (supp_mu (mu1 + mu2)%dist_state) l = true ->
  is_supp_subset (supp_mu mu1) l = true /\ is_supp_subset (supp_mu mu2) l = true.
Proof.
  intros mu1 mu2 l HSl Hsub. 
  generalize dependent mu2. generalize dependent l.
  induction mu1 as [|(s1, p1) mu1' IH1]; intros; try assumption.
  - simpl in *. split; try assumption. apply supp_subset_nil_l.
  - simpl in *. 
    apply supp_mu_subset_sp_conj_mu in Hsub; try assumption.
    destruct Hsub. 
    apply IH1 in H0; try assumption.
    destruct H0. split; try assumption.
    unfold supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st.
    apply supp_subset_insert_preserves; try assumption.
    apply Sort_supp_if_WF_supp. 
Qed.


(*该beqsupp的性质了*)
Lemma supp_eq_implies_subset_conj: forall ls1 ls2,
  beq_supp ls1 ls2 = true ->
  is_supp_subset ls1 ls2 = true /\ is_supp_subset ls2 ls1 = true.
Proof.
  intros. split.
  - generalize dependent ls2. 
    induction ls1 as [|s1 ls1 IH1]; intros; try apply supp_subset_nil_l.
    destruct ls2 as [|s2 ls2].
    + simpl in H. discriminate.
    + simpl in H. apply andb_true_iff in H. destruct H.
    simpl. rewrite H. apply IH1. assumption.
  - generalize dependent ls1. 
    induction ls2 as [|s2 ls2 IH2]; intros; simpl in H; try apply supp_subset_nil_l.
    destruct ls1 as [|s1 ls1].
    + simpl in H. discriminate.
    + simpl in H. apply andb_true_iff in H. destruct H.
    simpl. rewrite state_eq_sym in H. 
    rewrite H. apply IH2. assumption.
Qed.

Lemma supp_eq_sorted: forall (mu: dist_state), 
  Valid_dist mu ->
  supp_mu mu = supp_mu (sort_dst mu).
Proof.
  intros. unfold supp_mu.
  assert (Hsort: Sorted_dst (sort_dst mu)). { 
    apply WF_dist_implies_sortdst_Sorted; try assumption. } 
  apply conti_sort_eq in Hsort. rewrite Hsort. reflexivity.
Qed.

Lemma supp_eq_insert_st_eq_preservs: forall (mu1 mu2: dist_state) (s1 s2: local_st), 
  let ls1:= supp_mu mu1 in
  let ls2:= supp_mu mu2 in
  beq_supp ls1 ls2 = true -> 
  beq_state s1 s2 = true ->
  beq_supp (insert_st s1 ls1) (insert_st s2 ls2) = true.
Proof.
  intros mu1 mu2 s1 s2. intros.
  generalize dependent ls2. 
  induction ls1 as [|s1' ls1' IH]; destruct ls2 as [|s2' ls2']; intros.
  - simpl. apply andb_true_iff. split; [assumption|reflexivity].
  - simpl in *. discriminate.
  - simpl in *. discriminate.
  - simpl in *. apply andb_true_iff in H. destruct H. 
    specialize (IH ls2' H1).
    destruct (beq_state s1 s1') eqn: Hs.
    + assert (Hs2: beq_state s2 s2' = true). { 
        apply state_eq_trans with (s1:= s1'); try assumption. 
        rewrite state_eq_sym. 
        apply state_eq_trans with (s1:= s1); try assumption.
        rewrite state_eq_sym. assumption. }
        rewrite Hs2. simpl. apply andb_true_iff. split; assumption.
    + assert (Hs2: beq_state s2 s2' = false). { 
        apply state_eq_compat_left with (s:= s1') in H0; try assumption. 
        apply state_eq_compat_left with (s:= s2) in H; try assumption.
        rewrite state_eq_sym in H0. rewrite Hs in H0.
        rewrite state_eq_sym in H0. rewrite <- H0 in H.
        rewrite H; reflexivity. }
      rewrite Hs2. 
      assert (Hst: beq_state s1 s2 = true) by assumption.
      assert (Hst': beq_state s1' s2' = true) by assumption.
      apply st_eq_ble_compat_left with (s:= s1) in H; try assumption.
      apply st_eq_ble_compat_right with (s:= s2') in H0; try assumption.
      { rewrite <- H in H0. destruct (ble_state s1 s1') eqn: Hle.
        * rewrite <- H0. simpl. apply andb_true_iff. split; try assumption.
        apply andb_true_iff. split; assumption. 
        * rewrite <- H0. simpl. apply andb_true_iff. split; try assumption.
      }
Qed.

Theorem dst_eq_implies_beq_supp: forall mu0 mu1,
  Valid_dist mu0 -> Valid_dist mu1 ->
  beq_dst mu0 mu1 = true -> 
  beq_supp (supp_mu mu0) (supp_mu mu1) =true.
Proof.
  intros mu0 mu1 Hvalid0 Hvalid1 H.
  generalize dependent mu1.
  induction mu0 as [|(s0,p0) mu0' IH]; destruct mu1 as [|(s1,p1) mu1']; intros.
  - simpl. reflexivity.
  - simpl. discriminate.
  - simpl. discriminate.
  - simpl in H. apply andb_true_iff in H. destruct H.
    apply andb_true_iff in H. destruct H.
    unfold supp_mu. simpl. apply Valid_dist_conj in Hvalid0. destruct Hvalid0.
    apply Valid_dist_conj in Hvalid1. destruct Hvalid1.
    specialize (IH H3 mu1' H5 H0).
    unfold supp_mu in IH.
    rewrite insert_st_pair_fst_eq_insert_st; try assumption.
    rewrite insert_st_pair_fst_eq_insert_st with (mu:= (sort_dst mu1')); try assumption.
    apply supp_eq_insert_st_eq_preservs; try assumption.
Qed.

Lemma dst_equiv_implies_beq_supp: 
  forall mu0 mu1, 
  Valid_dist mu0 -> Valid_dist mu1 ->
  (mu0 == mu1)%dist_state -> 
  beq_supp (supp_mu mu0) (supp_mu mu1) = true. 
Proof.
  intros. rewrite supp_eq_sorted; try assumption. 
  rewrite supp_eq_sorted with (mu:= mu1); try assumption. 
  pose (mu0_sorted := sort_dst mu0).
  pose (mu1_sorted := sort_dst mu1).
  assert (Hsorted0: Sorted_dst mu0_sorted). { apply WF_dist_implies_sortdst_Sorted. assumption. }
  assert (Hsorted1: Sorted_dst mu1_sorted). { apply WF_dist_implies_sortdst_Sorted. assumption. }
  assert (Hvalid0: Valid_dist mu0_sorted). { apply Valid_implies_sort_Valid. assumption. }
  assert (Hvalid1: Valid_dist mu1_sorted). { apply Valid_implies_sort_Valid. assumption. }
  assert (Hsort_trans: (mu0_sorted == mu1_sorted)%dist_state). { 
    apply dst_equiv_trans with (mu1:= mu0).
    - apply dst_equiv_sym. apply dst_equiv_sort.
    - apply dst_equiv_trans with (mu1:= mu1); [assumption|apply dst_equiv_sort]. }
  assert (Htemp_beq: beq_dst mu0_sorted mu1_sorted = true). { 
    apply Sort_Valid_Peq_implies_beq_True; try split; try assumption. }
  apply dst_eq_implies_beq_supp; try assumption.
Qed.

Theorem supp_eq_mult_coef: forall mu p, 
  (0 < p )%R ->
  supp_mu mu = supp_mu (p * mu)%dist_state .
Proof.
  intros. induction mu as [|(s,q) mu' IH]; simpl.
  - reflexivity.
  - destruct (Req_EM_T p 0) eqn: Hp; try discriminate.
    + rewrite e in H. apply Rlt_irrefl in H. contradiction.
    + unfold supp_mu. simpl. 
    rewrite insert_st_pair_fst_eq_insert_st; try assumption.
    rewrite insert_st_pair_fst_eq_insert_st; try assumption.
    unfold supp_mu in IH. rewrite IH. reflexivity.
Qed. 

Theorem supp_eq_linear: forall mu1 mu2 p,
  (0 < p < 1)%R ->
  supp_mu (mu1 + mu2)%dist_state = supp_mu (p * mu1 + (1 - p) * mu2)%dist_state.
Proof.
  intros. 
  assert (Hpminus: (0< (1 - p) <1)%R) . {
    apply Rp_lt1_minus_p_bounds with (p:= p). assumption. }
  generalize dependent p. generalize dependent mu2.
  induction mu1 as [|(s1,p1) mu1' IH]; intros.
  - simpl. destruct Hpminus. apply supp_eq_mult_coef; try assumption.
  - simpl. destruct (Req_dec_T p 0) eqn: Hp.
    + destruct H. rewrite e in H. apply Rlt_irrefl in H. contradiction.
    + simpl. unfold supp_mu. simpl. 
    repeat rewrite insert_st_pair_fst_eq_insert_st. 
    specialize (IH mu2 p H Hpminus). 
    unfold supp_mu in IH. rewrite IH.
    reflexivity.
Qed.

Lemma in_supp_return_domain_eq: forall pd st,
  is_in_supp st (supp_mu (mu pd)) = true ->
  (return_domain st == (dom pd))%domain.
Proof.
  intros. generalize dependent st. destruct pd. 
  induction mu as [|(s,p) mu1 Hmu]; intros; simpl in *; try discriminate.
  inversion all_partial; subst. 
  unfold supp_mu in H. simpl in H. 
  rewrite insert_st_pair_fst_eq_insert_st in H.
  rewrite in_supp_insert_eq in H. 
  apply orb_true_iff in H. destruct H.
  - apply st_eq_implies_dom_equiv in H. 
  apply dom_equiv_trans with (l1:= return_domain s); try assumption.
  apply dom_equiv_sym. assumption.
  - apply Hmu; try assumption.
Qed.

Lemma supp_insert_valid_contra: forall sp s, 
  insert_st s sp = [] -> False.
Proof.
  intros. destruct sp.
  - simpl in *. discriminate.
  - simpl in *. destruct (beq_state s l); destruct (ble_state s l); discriminate.
Qed.

Lemma insert_pair_contra: forall s p mu, 
  insert_st_pair s p mu = [] -> False.
Proof.
  intros. destruct mu as [|(s',p') mu']; simpl in *.
  - simpl in *. discriminate.
  - simpl in *. destruct (beq_state s s'); destruct (ble_state s s'); discriminate.
Qed.
