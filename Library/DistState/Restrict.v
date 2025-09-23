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
Require Import Library.DistState.Partial.
Open Scope list_scope.

(******************* The properties of restrict operations "\|" **********************************************)
Lemma res_st_nil_eq: forall s, res_st_to_X s [] = [].
Proof.
  intros. induction s as [|v s']; simpl; try destruct v; reflexivity.
Qed.

Lemma res_dst_nil_eq: forall X, [] \| X = [].
Proof.
  intros. induction X as [|x X' IH]; simpl; reflexivity.
Qed.

Lemma st_res_all_default: forall s X, 
  all_false X = true ->
  st_all_none (res_st_to_X s X) = true.
Proof.
  intros s X HX. generalize dependent X. induction s as [| v s' Hs]; intros.
  - simpl. reflexivity.
  - destruct v; destruct X as [| x' X']; simpl in *; try reflexivity.
    + apply andb_true_iff in HX. destruct HX. 
      apply negb_true_iff in H. rewrite H. simpl. apply Hs. assumption.
    + apply andb_true_iff in HX. destruct HX. apply Hs. assumption.
Qed.

Lemma st_conti_res_eq: forall s X0 X1,
  is_domain_subset X0 X1 = true ->
  beq_state (res_st_to_X s X0) (res_st_to_X (res_st_to_X s X1) X0) = true.
Proof.
  intros s X0 X1 Hsub. generalize dependent X1. generalize dependent X0.
  induction s as [| v s' Hs].
  - simpl. intros. reflexivity.
  - intros. 
    destruct v; destruct X0 as [| x0 X0']; destruct X1 as [| x1 X1']; simpl in *; try reflexivity.
    + destruct x1; simpl; reflexivity.
    + destruct x0; try discriminate. simpl in *. apply st_res_all_default. assumption.
    + destruct x0; destruct x1; simpl in *; try discriminate. 
      * destruct (q ?= q) eqn: H'. 
      -- apply Hs; try assumption.
      -- apply Qlt_alt in H'. apply Qlt_irrefl in H'. contradiction.
      -- apply Qgt_alt in H'. apply Qlt_irrefl in H'. contradiction.
      * apply Hs; try assumption.
      * apply Hs; try assumption.
    + apply andb_true_iff in Hsub. destruct Hsub. apply st_res_all_default. assumption.
    + destruct x0; destruct x1; simpl in *; try discriminate. 
      * apply Hs; try assumption.
      * apply Hs; try assumption.
      * apply Hs; try assumption.
Qed.

Lemma st_eq_res_to_dom: forall s, 
  let domain:= (return_domain s) in 
  beq_state (res_st_to_X s domain) s = true.
Proof.
  intros s X. induction s as [| v s' Hs].
  - simpl. reflexivity.
  - destruct v; simpl in *. 
    + destruct (q ?= q) eqn: H'. 
      * apply Hs.
      * apply Qlt_alt in H'. apply Qlt_irrefl in H'. contradiction.
      * apply Qgt_alt in H'. apply Qlt_irrefl in H'. contradiction.
    + apply Hs.
Qed.


Lemma all_default_res: forall s X, 
  st_all_none s = true ->
  st_all_none (res_st_to_X s X) = true.
Proof.
  intros s X HX. generalize dependent X. induction s as [| v s' Hs]; intros.
  - simpl. reflexivity.
  - simpl. destruct v; destruct X as [| x' X']; simpl in *; try reflexivity; try discriminate.
    apply Hs; try assumption.
Qed.

Lemma st_eq_res_to_eq_dom: forall s X Y, 
  (X == Y)%domain ->  
  beq_state (res_st_to_X s X) (res_st_to_X s Y) = true. 
Proof.
  intros. generalize dependent Y. generalize dependent X. 
  induction s as [| v s' Hs]; intros; simpl; try reflexivity.
  destruct v; destruct X as [|x X']; destruct Y as [|y Y']; simpl in *; try reflexivity.
  - apply dom_equiv_sym in H. apply all_false_iff_nil in H. simpl in H. 
    apply andb_true_iff in H. destruct H. apply negb_true_iff in H.
    rewrite H. simpl. apply st_res_all_default. assumption.
  - apply all_false_iff_nil in H. simpl in H. 
    apply andb_true_iff in H. destruct H. apply negb_true_iff in H.
    rewrite H. simpl. apply st_res_all_default. assumption.
  - apply dom_cons_equiv_iff in H. destruct H.
    destruct x; destruct y; try discriminate.
    + simpl. apply Hs in H0. destruct (q ?= q) eqn: H'. 
      * assumption.
      * apply Qlt_alt in H'. apply Qlt_irrefl in H'. contradiction.
      * apply Qgt_alt in H'. apply Qlt_irrefl in H'. contradiction.
    + simpl. apply Hs in H0. destruct (q ?= q) eqn: H'. 
      * assumption.
      * apply Qlt_alt in H'. apply Qlt_irrefl in H'. contradiction.
      * apply Qgt_alt in H'. apply Qlt_irrefl in H'. contradiction.
  - apply dom_equiv_sym in H. apply all_false_iff_nil in H. simpl in H. 
    apply andb_true_iff in H. destruct H. 
    apply st_res_all_default. assumption.
  - apply all_false_iff_nil in H. simpl in H. 
    apply andb_true_iff in H. destruct H. 
    apply st_res_all_default. assumption.
  - apply dom_cons_equiv_iff in H. destruct H.
    apply Hs in H0. assumption.
Qed.

Lemma st_eq_implies_res_X_eq: forall s0 s1 X, 
  beq_state s0 s1 = true ->
  beq_state (res_st_to_X s0 X) (res_st_to_X s1 X) = true.
Proof.
  intros. generalize dependent s1. generalize dependent s0.
  induction X as [|x0 X' IH]; destruct s0 as [| v0 s0']; destruct s1 as [| v1 s1']; 
    try destruct v0; try destruct v1; intros; simpl in *; try reflexivity; try discriminate.
  - apply all_default_res; try assumption.
  - apply all_default_res; try assumption. 
  - destruct x0. 
    + simpl. destruct (q ?= q0) eqn: H'; try discriminate.
      apply IH; try assumption.
    + simpl. destruct (q ?= q0) eqn: H'; try discriminate. 
      apply IH; try assumption.
  - apply IH. assumption.
Qed.

Lemma all_defalut_implies_all_false: forall s,
  st_all_none s = true -> 
  all_false (return_domain s) = true.
Proof.
  intros s H.
  induction s as [ |v s' IH]; intros.
  - simpl. reflexivity.
  - simpl in *. apply andb_true_iff in H. destruct H. 
    apply andb_true_iff. split; try assumption.
    + rewrite negb_involutive. assumption.
    + apply IH; try assumption.
Qed.

Lemma st_eq_implies_domain_eq: forall s0 s1,
  beq_state s0 s1 = true -> 
  (return_domain s0 == return_domain s1)%domain.
Proof.
  intros. generalize dependent s1.
  induction s0 as [|v0 s0' Hs0]; intros; simpl; 
    destruct s1 as [|v1 s1']; simpl.
  - apply dom_equiv_refl.
  - split; simpl in *; try reflexivity.
    apply andb_true_iff in H. destruct H. 
    apply andb_true_iff. split; try assumption. 
    + rewrite negb_involutive. assumption.
    + apply all_defalut_implies_all_false; try assumption.
  - split. 
    + simpl. rewrite st_eq_nil_iff_all_none in H. simpl in H.
    apply andb_true_iff in H. destruct H. 
    apply andb_true_iff. split; try assumption. 
      * rewrite negb_involutive. assumption.
      * apply all_defalut_implies_all_false; try assumption.
    + simpl. reflexivity.
  - simpl in *. destruct v0; destruct v1; simpl in *; try discriminate.
    + destruct (q ?= q0)eqn: H'; try discriminate. 
    apply dom_cons_equiv_iff. split; try reflexivity.
    apply Hs0. assumption.
    + apply dom_cons_equiv_iff. split; try reflexivity.
    apply Hs0. assumption. 
Qed.

Lemma res_dom_subst: forall s X,
  is_domain_subset (return_domain (res_st_to_X s X)) (return_domain s)= true.
Proof.
  intros s X. generalize dependent X. 
  induction s as [|v s' Hs]; intros.
  - simpl. reflexivity.
  - destruct v; destruct X; simpl; try reflexivity. 
    + destruct b; simpl; apply Hs. 
    + apply Hs.
Qed.

Lemma res_eq_union_l_res: forall s s' X, 
  is_domain_intersect (return_domain s) (return_domain s') = false ->
  is_domain_subset X (return_domain s) = true -> 
  (res_st_to_X s X == res_st_to_X (union_state s s') X)%state.
Proof.
  intros s s' X Hinter Hsub. generalize dependent X. generalize dependent s'.
  induction s as [| v s IH]; intros; try assumption.
  - simpl in Hsub. apply dom_subset_nil_iff in Hsub. 
    apply all_false_iff_nil in Hsub. 
    rewrite union_nil_left_eq. 
    apply st_res_all_default. assumption.
  - destruct s' as [| v' s']. 
    + rewrite union_nil_right_eq. apply state_eq_refl.
    + destruct v; destruct v'; destruct X as [| b X]; simpl in *; try discriminate; try reflexivity.
      * destruct b; simpl in *. 
      -- destruct (q ?= q) eqn: Hveq. 
      ++ apply IH; try assumption.
      ++ apply Qlt_alt in Hveq. apply Qlt_irrefl in Hveq. contradiction.
      ++ apply Qgt_alt in Hveq. apply Qlt_irrefl in Hveq. contradiction.
      -- apply IH; try assumption.
      * destruct b; simpl in *; try discriminate.
      apply IH; assumption.
      * destruct b; simpl in *; try discriminate. 
      apply IH; assumption.
Qed.

Lemma res_eq_union_r_res: forall s s' X, 
  is_domain_intersect (return_domain s) (return_domain s') = false ->
  is_domain_subset X (return_domain s) = true -> 
  (res_st_to_X s X == res_st_to_X (union_state s' s) X)%state.
Proof. 
  intros. apply state_eq_trans with (s1:= res_st_to_X (union_state s s') X).
  - apply res_eq_union_l_res; try assumption.
  - apply st_eq_implies_res_X_eq. apply union_state_comm.
Qed.

Lemma union_res_st_eq: forall s s' X X',
  is_domain_intersect (return_domain s) (return_domain s') = false ->
  is_domain_subset X (return_domain s) = true ->
  is_domain_subset X' (return_domain s') = true ->
  (union_state (res_st_to_X s X) (res_st_to_X s' X') ==
    res_st_to_X (union_state s s') (orb_domain X X'))%state.
Proof.
  intros s s' X X' Hinter Hsub Hsub'. 
  generalize dependent X'. generalize dependent X.
  generalize dependent s'. 
  induction s as [| v s IH]; intros; try assumption.
  - simpl in Hsub. apply dom_subset_nil_iff in Hsub. 
    repeat rewrite union_nil_left_eq. 
    apply all_false_iff_nil in Hsub. 
    apply all_false_orb_l with (l1:= X') in Hsub. 
    rewrite state_eq_sym. apply st_eq_res_to_eq_dom. assumption.
  - simpl in Hsub. destruct s' as [| v' s']. 
    + simpl in Hsub'. apply dom_subset_nil_iff in Hsub'.
      repeat rewrite union_nil_right_eq. 
      apply all_false_iff_nil in Hsub'. 
      apply all_false_orb_l with (l1:= X) in Hsub'. 
      rewrite orb_domain_comm. 
      rewrite state_eq_sym. apply st_eq_res_to_eq_dom. assumption.
    + destruct v; destruct v'; destruct X as [| b X]; destruct X' as [| b' X']; 
        try destruct b; try destruct b'; simpl in *; try discriminate; try reflexivity.
      * rewrite intersect_comm in Hinter. apply res_eq_union_r_res; try assumption.
      * destruct (q ?= q) eqn: Hv'eq.
        ++ apply res_eq_union_l_res; assumption. 
        ++ apply Qlt_alt in Hv'eq. apply Qlt_irrefl in Hv'eq. contradiction.
        ++ apply Qgt_alt in Hv'eq. apply Qlt_irrefl in Hv'eq. contradiction.
      * apply res_eq_union_l_res; assumption.
      * destruct (q ?= q) eqn: Hv'eq.
        ++ apply IH; assumption. 
        ++ apply Qlt_alt in Hv'eq. apply Qlt_irrefl in Hv'eq. contradiction.
        ++ apply Qgt_alt in Hv'eq. apply Qlt_irrefl in Hv'eq. contradiction.
      * apply IH; assumption. 
      * destruct (q ?= q) eqn: Hv'eq.
        ++ rewrite intersect_comm in Hinter. apply res_eq_union_r_res; assumption. 
        ++ apply Qlt_alt in Hv'eq. apply Qlt_irrefl in Hv'eq. contradiction.
        ++ apply Qgt_alt in Hv'eq. apply Qlt_irrefl in Hv'eq. contradiction.
      * rewrite intersect_comm in Hinter. apply res_eq_union_r_res; try assumption.
      * apply res_eq_union_l_res; try assumption.
      * destruct (q ?= q) eqn: Hv'eq.
        ++ apply IH; assumption. 
        ++ apply Qlt_alt in Hv'eq. apply Qlt_irrefl in Hv'eq. contradiction.
        ++ apply Qgt_alt in Hv'eq. apply Qlt_irrefl in Hv'eq. contradiction.
      * apply IH; assumption.
      * rewrite intersect_comm in Hinter. apply res_eq_union_r_res; try assumption.
      * apply res_eq_union_l_res; try assumption.
      * apply IH; assumption.
Qed.

Lemma res_union_state_doms: forall s s0, 
  is_domain_intersect (return_domain s) (return_domain s0) = false -> 
  (res_st_to_X (union_state s s0) (return_domain s) == s)%state.
Proof.
  intros s s0 H. generalize dependent s0.
  induction s as [|v s' IH]; intros.
  - rewrite union_nil_left_eq. simpl. rewrite res_st_nil_eq. apply state_eq_refl.
  - destruct s0 as [|v0 s0']; intros.
    + rewrite union_nil_right_eq. apply st_eq_res_to_dom.
    + destruct v; destruct v0; simpl in *; try discriminate. 
      * destruct (q ?= q) eqn: Hv'eq.
        ++ apply IH. assumption.
        ++ apply Qlt_alt in Hv'eq. apply Qlt_irrefl in Hv'eq. contradiction.
        ++ apply Qgt_alt in Hv'eq. apply Qlt_irrefl in Hv'eq. contradiction.
      * apply IH. assumption.
      * apply IH. assumption.
Qed.

(*******************partial dist_state *******************************************************)
Open Scope dstate_scope.
Lemma res_cons_decom_eq: forall s p mu X, 
  ((s,p) :: mu) \| X = (res_st_to_X s X,p) :: mu \| X.
Proof.
  intros s p mu X. simpl. reflexivity. 
Qed.

Lemma res_add_decom_eq: forall mu0 mu1 X, 
   (mu0 + mu1)%dist_state \| X = ((mu0 \| X) + (mu1 \| X))%dist_state.
Proof.
  intros mu0 mu1 X. generalize dependent X. generalize dependent mu1.
  induction mu0 as [| (s0,p0) mu0' Hmu0]; intros.
  - simpl. reflexivity.
  - simpl. f_equal. apply Hmu0.
Qed.

Lemma res_pd_to_dom_refl: forall pd, 
  pd.(mu) \| pd.(dom) == pd.(mu).
Proof.
  intros pd. destruct pd as [dom mu Hvalid].
  induction mu as [|(s,p) mu' IH]; intros.
  - simpl. apply dst_equiv_refl.
  - simpl. inversion Hvalid; subst.  
    rewrite dst_cons_eq_add. rewrite dst_cons_eq_add with (mu:= mu'). 
    apply dst_add_preserves_equiv.
    + apply Peq_one_st. split; try reflexivity.
      apply state_eq_trans with (s1:= (res_st_to_X s (return_domain s)));
      try apply st_eq_res_to_dom.
      apply st_eq_res_to_eq_dom; try assumption.
    + inversion Hvalid; subst. apply IH with (Hvalid:= H5).
Qed.

Theorem res_to_subset_equiv: forall mu X0 X1,
  is_domain_subset X0 X1 = true -> 
  mu \| X0 == (mu\| X1)\| X0.
Proof. 
  intros mu X0 X1 Hsubx1. 
  generalize dependent X1. generalize dependent X0.
  induction mu as [|(s, p) mu' Hmu].
  - simpl. intros. apply dst_equiv_refl.
  - intros. simpl.
    destruct X0 as [ | x0 X0']; destruct X1 as [ | x1 X1']; 
    simpl in *; try reflexivity. 
    + repeat rewrite res_st_nil_eq. rewrite dst_cons_eq_add. 
    rewrite dst_cons_eq_add with (mu:= (mu' \| []) \| []). 
    apply dst_add_preserves_equiv.
      * apply dst_equiv_refl.
      * apply Hmu. simpl. reflexivity.
    + repeat rewrite res_st_nil_eq. rewrite dst_cons_eq_add. 
    rewrite dst_cons_eq_add with (mu:= (mu' \| (x1 :: X1')) \| []). 
    apply dst_add_preserves_equiv.
      * apply dst_equiv_refl.
      * apply Hmu. simpl. reflexivity.
    + repeat rewrite res_st_nil_eq. simpl. 
    apply andb_true_iff in Hsubx1. destruct Hsubx1.
    rewrite dst_cons_eq_add. 
    rewrite dst_cons_eq_add with (mu:= (mu' \| []) \| (x0 :: X0')).
    apply dst_add_preserves_equiv.
      * apply Peq_one_st. split; try reflexivity. 
      destruct s as [|v s']; try reflexivity. 
      destruct v; simpl. 
      ** apply negb_true_iff in H. rewrite H. simpl. apply st_res_all_default. try assumption.
      ** apply st_res_all_default. try assumption.
      * apply Hmu. simpl. apply andb_true_iff. split; assumption.
    + rewrite dst_cons_eq_add. 
    rewrite dst_cons_eq_add with (mu:= (mu' \| (x1 :: X1')) \| (x0 :: X0')).
    apply dst_add_preserves_equiv.
      * apply Peq_one_st. split; try reflexivity.
      apply st_conti_res_eq; try assumption.
      * apply Hmu. simpl. assumption.
Qed. 

Lemma res_dst_to_X_mult_coef: forall mu p X, 
  (p * mu) \| X = p * (mu \| X).
Proof.
  intros mu p X.
  induction mu as [|(s, p') mu' Hmu]; intros.
  - simpl. reflexivity.
  - simpl. destruct (Req_dec_T p 0) eqn: Hp; try reflexivity.
  simpl. f_equal. assumption.
Qed.
(*************************************************************)
Lemma dst_eq_implies_res_X_eq: forall mu0 mu1 X,
  beq_dst mu0 mu1 = true ->
  beq_dst (mu0\| X) (mu1\| X) = true.
Proof.
  intros mu0 mu1 X Hmu. generalize dependent X. generalize dependent mu1.
  induction mu0 as [| (s0,p0) mu0' Hmu0]; destruct mu1 as [|(s1,p1) mu1']; intros.
  - simpl. reflexivity.
  - simpl in Hmu. discriminate.
  - simpl in Hmu. discriminate.
  - simpl in Hmu. apply andb_true_iff in Hmu. destruct Hmu. specialize (Hmu0 mu1' H0 X).
    apply andb_true_iff in H. destruct H. simpl. destruct X.
    + repeat rewrite res_st_nil_eq. simpl. 
    apply andb_true_iff. split; try assumption.
    + apply andb_true_iff. split; try assumption.
    apply andb_true_iff. split; try assumption.
    simpl.  apply st_eq_implies_res_X_eq; try assumption.
Qed. 

Lemma insert_st_res_Peq: forall mu s p X, 
  (insert_st_pair s p mu) \|X == insert_st_pair (res_st_to_X s X) p (mu\|X).
Proof. 
  intros. generalize dependent X.
  induction mu as [|(s', p') mu' Hmu]; destruct X; intros; try contradiction.
  - simpl. apply dst_equiv_refl.
  - simpl. apply dst_equiv_refl.
  - simpl. repeat rewrite res_st_nil_eq. simpl.  
    destruct (beq_state s s') eqn: Hst'.
    + simpl. repeat rewrite res_st_nil_eq. apply dst_equiv_refl.
    + destruct (ble_state s s') eqn: Hle'. 
      * simpl. repeat rewrite res_st_nil_eq. 
      rewrite dst_cons_eq_add. repeat rewrite dst_cons_eq_add with (mu:= mu' \| []).
      rewrite dst_add_assoc_eq. apply dst_add_preserves_equiv; try apply dst_equiv_refl.
      unfold dst_equiv. simpl. intros. destruct (beq_state s0 []) eqn: Hs0. 
      ** rewrite Rplus_assoc. reflexivity.
      ** reflexivity.
      * simpl. repeat rewrite res_st_nil_eq. 
      apply dst_equiv_trans with (mu1:= [([], p')] + ([([], p)] + mu' \| [])).
      ** rewrite dst_cons_eq_add. apply dst_add_inj_l. specialize Hmu with []. 
      rewrite res_st_nil_eq in Hmu. 
      apply dst_equiv_trans with (mu1:= insert_st_pair [] p (mu' \| [])); try assumption.
      rewrite <-dst_cons_eq_add. apply insert_pair_equiv_cons.
      ** rewrite dst_add_assoc_eq. rewrite dst_cons_eq_add with (mu:= mu' \| []).
      apply dst_add_inj_r. simpl. unfold dst_equiv. intros. simpl.
      destruct (beq_state s0 []) eqn: Hs0. 
      -- repeat rewrite Rplus_0_r. apply Rplus_comm.
      -- reflexivity.
  - simpl. destruct (beq_state s s') eqn: Hst'.
    + simpl. 
      assert (H1: beq_state (res_st_to_X s (b :: X)) (res_st_to_X s' (b :: X)) = true). { 
        apply st_eq_implies_res_X_eq. apply Hst'. }
      rewrite H1. simpl. apply dst_equiv_refl.
    + destruct (ble_state s s') eqn: Hle'. 
      * simpl. destruct (beq_state (res_st_to_X s (b :: X)) (res_st_to_X s' (b :: X))) eqn: Heq.
      ** unfold dst_equiv. intros. simpl. 
        destruct (beq_state s0 (res_st_to_X s (b :: X))) eqn: Heq0.
        ++ assert (Htrue: beq_state s0 (res_st_to_X s' (b :: X)) = true). { 
              apply state_eq_compat_left with (s:= s0) in Heq. rewrite Heq in Heq0. assumption. }
          rewrite Htrue. rewrite Rplus_assoc. reflexivity.
        ++ assert (Hfalse: beq_state s0 (res_st_to_X s' (b :: X)) = false). { 
              apply state_eq_compat_left with (s:= s0) in Heq. rewrite Heq in Heq0. assumption. }
        rewrite Hfalse. reflexivity.
      ** destruct (ble_state (res_st_to_X s (b :: X)) (res_st_to_X s' (b :: X))) eqn: Hle.
        ++ apply dst_equiv_refl.
        ++ rewrite dst_cons_eq_add. rewrite dst_cons_eq_add with (mu:= (mu' \| (b :: X))). 
          rewrite dst_cons_eq_add with (mu:= insert_st_pair (res_st_to_X s (b :: X)) p (mu' \| (b :: X))). 
          rewrite dst_add_assoc_eq.
          apply dst_equiv_trans with (mu1:= 
            [(res_st_to_X s' (b :: X), p')] + [(res_st_to_X s (b :: X), p)] + (mu' \| (b :: X))).
            -- apply dst_add_inj_r. apply dst_add_comm. 
            -- rewrite <- dst_add_assoc_eq. apply dst_add_inj_l. apply dst_equiv_sym.
              simpl. apply insert_pair_equiv_cons.
      * simpl. destruct (beq_state (res_st_to_X s (b :: X)) (res_st_to_X s' (b :: X))) eqn: Heq.
      ** rewrite dst_cons_eq_add. 
        apply dst_equiv_trans with (mu1:= [(res_st_to_X s' (b :: X), p')] + 
                                            insert_st_pair (res_st_to_X s (b :: X)) p (mu' \| (b :: X))).
        ++ apply dst_add_inj_l. apply Hmu. 
        ++ apply dst_equiv_trans with (mu1:= [(res_st_to_X s' (b :: X), p'%R)] + 
                                              ((res_st_to_X s (b :: X), p%R) :: mu' \| (b :: X))).
          -- apply dst_add_inj_l. apply insert_pair_equiv_cons. 
          -- rewrite dst_cons_eq_add with (mu:= mu'\|(b :: X)). 
            rewrite dst_cons_eq_add with (mu:= mu'\|(b :: X)).
            rewrite dst_add_assoc_eq. apply dst_add_inj_r. 
            unfold dst_equiv. intros. simpl. 
            destruct (beq_state s0 (res_st_to_X s' (b :: X))) eqn: Heq0.
            --- assert (Htrue: beq_state s0 (res_st_to_X s (b :: X)) = true). { 
                  apply state_eq_compat_left with (s:= s0) in Heq. rewrite <- Heq in Heq0. assumption. }
                rewrite Htrue. repeat rewrite Qplus_0_r. rewrite <- Rplus_assoc. f_equal. apply Rplus_comm. 
            --- assert (Hfalse: beq_state s0 (res_st_to_X s (b :: X)) = false). { 
                  apply state_eq_compat_left with (s:= s0) in Heq. rewrite <- Heq in Heq0. assumption. }
            rewrite Hfalse. reflexivity.
      ** destruct (ble_state (res_st_to_X s (b :: X)) (res_st_to_X s' (b :: X))) eqn: Hle.
        ++ rewrite dst_cons_eq_add. 
          rewrite dst_cons_eq_add with (mu:= (res_st_to_X s' (b :: X), p') :: mu' \| (b :: X)). 
          rewrite dst_cons_eq_add with (mu:= (mu' \| (b :: X))). 
          rewrite dst_add_assoc_eq.
          apply dst_equiv_trans with (mu1:= [(res_st_to_X s' (b :: X), p')] + 
                          [(res_st_to_X s (b :: X), p)] + (mu' \| (b :: X))).
          -- rewrite <- dst_add_assoc_eq. apply dst_add_inj_l. simpl. 
            apply dst_equiv_trans with (mu1:= insert_st_pair (res_st_to_X s (b :: X)) p (mu' \| (b :: X))).
            --- apply Hmu. 
            --- apply insert_pair_equiv_cons.
          -- apply dst_add_inj_r. unfold dst_equiv. intros. simpl. 
            destruct (beq_state s0 (res_st_to_X s' (b :: X))) eqn: Heq'; try reflexivity.
            destruct (beq_state s0 (res_st_to_X s (b :: X))) eqn: Heq0; try reflexivity.
            repeat rewrite Rplus_0_r. apply Rplus_comm.
        ++ rewrite dst_cons_eq_add. 
          rewrite dst_cons_eq_add with (mu:= (insert_st_pair (res_st_to_X s (b :: X)) p (mu' \| (b :: X)))).
          apply dst_add_inj_l. apply Hmu. 
Qed. 

Lemma mu_res_sort_Peq: forall mu X, 
  mu \| X == (sort_dst mu) \| X.
Proof. 
  intros. generalize dependent X.
  induction mu as [|(s, p) mu' Hmu].
  + intros. simpl. apply dst_equiv_refl.
  + intros. simpl. 
  apply dst_equiv_trans with (mu1:= insert_st_pair (res_st_to_X s X) p ((sort_dst mu') \| X)). 
    * apply dst_equiv_trans with (mu1:= ((res_st_to_X s X), p) :: ((sort_dst mu') \| X)).
    - apply dst_add_inj_l with (mu:= [(res_st_to_X s X, p)]). apply Hmu.
    - apply dst_equiv_sym. apply insert_pair_equiv_cons.
    * apply dst_equiv_sym. apply insert_st_res_Peq. 
Qed.

Lemma Peq_implies_res_eq: forall mu0 mu1 X, 
  Valid_dist mu0 -> Valid_dist mu1 ->
  mu0 == mu1 -> 
  mu0 \| X == mu1 \| X.
Proof.
  intros mu0 mu1 X H0 H1 Hmu_Peq. 
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
  assert (Htemp_implies: beq_dst (mu0_sorted \| X) (mu1_sorted \| X) = true). { 
    apply dst_eq_implies_res_X_eq. assumption. } 
  assert (Heq0: mu0 \| X  == mu0_sorted \| X). { apply mu_res_sort_Peq. }
  assert (Heq1: mu1 \| X  == mu1_sorted \| X). { apply mu_res_sort_Peq. }
  apply dst_equiv_trans with (mu1:= mu0_sorted \| X); try assumption.
  apply dst_equiv_trans with (mu1:= mu1_sorted \| X); try apply dst_equiv_sym in Heq1; try assumption. 
  apply dst_eq_implies_equiv in Htemp_implies.
  apply Htemp_implies.
Qed. 

(*********************Res preserves Valid. *******************************************)
Lemma sum_eq_after_res: forall mu X, 
  (sum_probs mu = sum_probs (mu \| X))%R.
Proof.
  intros mu X.
  induction mu as [|(s, p) mu' Hmu].
  - simpl. reflexivity.
  - simpl. rewrite Hmu. reflexivity.
Qed.

Lemma Valid_after_resX: forall mu X, 
  Valid_dist mu -> Valid_dist (mu \| X). 
Proof.
  intros mu X Hvalid. generalize dependent X.
  induction mu as [|(s, p) mu' Hmu]; intros.
  - simpl. assumption.
  - assert(H1: Valid_dist mu'). { 
      apply Valid_dist_conj in Hvalid. destruct Hvalid. assumption. }
    apply Hmu with (X) in H1. split. 
    + simpl. destruct Hvalid. simpl in *. 
    rewrite <- sum_eq_after_res. assumption.
    + simpl. destruct Hvalid. simpl in *. 
    destruct H0. split; try assumption.
    destruct H1. assumption.
Qed.
(*********************************************************)
Lemma res_dst_to_dom_trans: forall pd1 pd2 pd3, 
  Valid_dist (mu pd1) -> Valid_dist (mu pd2) -> Valid_dist (mu pd3) ->
  is_domain_subset (dom pd1) (dom pd2) = true ->
  is_domain_subset (dom pd2) (dom pd3) = true -> 
  (mu pd2) \| (dom pd1) == mu pd1 ->
  (mu pd3) \| (dom pd2) == mu pd2 ->
  (mu pd3) \| (dom pd1) == mu pd1.
Proof.
  intros pd1 pd2 pd3 Hwf1 Hwf2 Hwf3 Hsub1 Hsub2 Heq1 Heq2.
  apply dst_equiv_trans with (mu1:= (mu pd2 \| (dom pd1))); try assumption.
  apply dst_equiv_trans with (mu1:= ((mu pd3) \| (dom pd2) \| (dom pd1))); try assumption.
  - apply res_to_subset_equiv; try assumption.
  - apply Peq_implies_res_eq; try assumption. 
    apply Valid_after_resX; try assumption.
Qed.

Lemma beq_combine_onest_l_res_orb: forall s p X X' pd, 
  is_domain_intersect (return_domain s) pd.(dom) = false ->
  is_domain_subset X (return_domain s) = true ->
  is_domain_subset X' pd.(dom) = true ->
  beq_dst ([(res_st_to_X s X, p)] ⊗ pd.(mu) \| X') 
            (([(s, p)] ⊗ pd.(mu)) \| (orb_domain X X')) = true.
Proof.
  intros s p X X' pd Hinter Hsubs Hsubpd. destruct pd. 
  generalize dependent X'. generalize dependent X. 
  induction mu as [|(s',p') mu' Hmu]; intros; try assumption.
  - simpl. reflexivity.
  - simpl in Hsubpd. simpl in Hinter. 
    inversion all_partial; subst.
    unfold mu. 
    replace (((s', p') :: mu') \| X') with ((res_st_to_X s' X', p') :: mu' \| X') by reflexivity.
    repeat rewrite combine_onest_cons_distr_eq. repeat rewrite <- dst_cons_eq_add. 
    rewrite res_cons_decom_eq. unfold beq_dst. fold beq_dst. 
    apply andb_true_iff. split.
    + apply andb_true_iff; split; try apply Req_bool_refl.
    apply union_res_st_eq; try assumption. 
      * apply dom_eq_intersect_compat_left with (l:= (return_domain s)) in H1.
      rewrite Hinter in H1. rewrite H1. reflexivity. 
      * apply dom_subset_eq_compat_left with (Z:= X') in H1; try assumption.
    + apply Hmu with (all_partial:= H3); try assumption.
Qed.

Lemma combine_res_merge_equiv: forall pd0 pd1 X0 X1, 
  is_domain_intersect pd0.(dom) pd1.(dom) = false ->
  is_domain_subset X0 pd0.(dom) = true ->
  is_domain_subset X1 pd1.(dom) = true ->
  (((mu pd0) \| X0) ⊗ (pd1.(mu) \| X1)) == ((pd0.(mu) ⊗ pd1.(mu)) \| (orb_domain X0 X1)).
Proof.
  intros pd0 pd1 X0 X1 Hinter Hsub0 Hsub1. 
  destruct pd0 as [dom0 mu0 HPD0]. 
  generalize dependent pd1. generalize dependent X1.
  generalize dependent X0. 
  induction mu0 as [|(s, p) mu' Hmu]; intros; try assumption.
  - simpl. apply dst_equiv_refl.
  - simpl in Hinter. simpl in Hsub0. simpl in Hsub1. 
    inversion HPD0; subst.
    unfold mu. rewrite combine_cons_l_distr_eq.
    replace (((s, p) :: mu') \| X0) with ((res_st_to_X s X0, p) :: mu' \| X0) by reflexivity.
    rewrite combine_cons_l_distr_eq. rewrite res_add_decom_eq.
    apply dst_add_preserves_equiv; try assumption.
    + apply dst_eq_implies_equiv. 
    apply beq_combine_onest_l_res_orb with (pd:= pd1); try assumption.
      * apply dom_eq_intersect_compat_right with (l:=(dom pd1)) in H1.
      rewrite Hinter in H1. rewrite H1. reflexivity.
      * apply dom_subset_eq_compat_left with (Z:= X0) in H1; try assumption.
    + apply Hmu with (HPD0:= H3); try assumption. 
Qed.

Lemma res_sym_with_combine: forall mu mu0 X, 
  Valid_dist mu -> Valid_dist mu0 ->
  (mu ⊗ mu0) \| X == (mu0 ⊗ mu) \| X.
Proof.
  intros mu mu0 HV HV0 X. 
  apply Peq_implies_res_eq; try assumption.
  - apply Valid_after_combine; assumption.
  - apply Valid_after_combine; assumption.
  - apply combine_sym.
Qed.

Lemma res_comb_onest: forall s s0 p p0 mu dom dom0, 
  partial_dst_Prop dom0 ((s0,p0)::mu) -> 
  (dom == return_domain s)%domain ->
  is_domain_intersect dom dom0 = false -> 
  ([(s, p)] ⊗ ((s0,p0)::mu)) \| dom == [(s, (sum_probs ((s0,p0)::mu) * p)%R)].
Proof.
  intros s s0 p p0 mu dom dom0 HPD Hdom Hinter. 
  induction mu as [|(s', p') mu' Hmu]; intros.
  - simpl. inversion HPD; subst. 
    apply Peq_one_st. split.
    + apply state_eq_trans with (s1:= res_st_to_X (union_state s s0) (return_domain s)).
      * apply st_eq_res_to_eq_dom. assumption.
      * apply res_union_state_doms. 
      rewrite <- dom_eq_intersect_preserves_equiv with (l0:= dom) (l2:= dom0); assumption.
    + rewrite Rplus_0_r. apply Rmult_comm.
  - inversion HPD; subst. inversion H3; subst. 
    assert (HPD': partial_dst_Prop dom0 ((s0, p0) :: mu')). {
      apply PD_cons; assumption. }
    apply Hmu in HPD'. 
    rewrite combine_onest_cons_distr_eq in HPD'. 
    rewrite res_add_decom_eq in HPD'.
    repeat rewrite combine_onest_cons_distr_eq.
    repeat rewrite res_add_decom_eq. 
    apply dst_equiv_trans with (mu1:= [(union_state s s0, (p * p0)%R)] \| dom +
          (([(s, p)] ⊗ mu') \| dom + [(union_state s s', (p * p')%R)] \| dom)).
    + apply dst_add_inj_l. apply dst_add_comm.
    + rewrite dst_add_assoc_eq.
      apply dst_equiv_trans with (mu1:= [(s, (sum_probs ((s0, p0) :: mu') * p)%R)] + [(union_state s s', (p * p')%R)] \| dom).
      * apply dst_add_inj_r. assumption.
      * apply dst_equiv_trans with (mu1:= (s, ((p0 + sum_probs mu') * p)%R):: [(s, (p' * p)%R)]).
      ** simpl. rewrite dst_cons_eq_add. 
      assert (Hs: beq_state s (res_st_to_X (union_state s s') dom) = true). {
        rewrite state_eq_sym.
        apply state_eq_trans with (s1:= res_st_to_X (union_state s s') (return_domain s)).
        * apply st_eq_res_to_eq_dom. assumption.
        * apply res_union_state_doms. 
      rewrite <- dom_eq_intersect_preserves_equiv with (l0:= dom) (l2:= dom0); assumption.
      }
      unfold dst_equiv. intros. 
      simpl. destruct (beq_state s1 s) eqn: Hs1; try reflexivity.
      -- assert (Ht: beq_state s1 (res_st_to_X (union_state s s') dom)= true). {
            apply state_eq_trans with (s1:= s); assumption. }
      rewrite Ht. rewrite Rmult_comm with (r1:= p'). reflexivity.
      -- assert (Ht: beq_state s1 (res_st_to_X (union_state s s') dom)= false). {
            apply state_eq_compat_left with (s:= s1) in Hs; try assumption.
            rewrite Hs1 in Hs. rewrite <- Hs. reflexivity. }
      rewrite Ht. reflexivity.
      ** simpl. unfold dst_equiv. intros. 
        simpl. destruct (beq_state s1 s) eqn: Hs1; try reflexivity.
        repeat rewrite Rplus_0_r. rewrite <- Rmult_plus_distr_r. 
        apply Rmult_eq_compat_r. rewrite Rplus_assoc. rewrite Rplus_comm with (r1:= p'). reflexivity.
Qed.

Lemma res_comb_equiv: forall pd0 pd1, 
  Valid_dist pd1.(mu) ->
  is_domain_intersect pd0.(dom) pd1.(dom) = false -> 
  ((pd0.(mu) ⊗ pd1.(mu)) \| pd0.(dom)) == sum_probs (mu pd1) * pd0.(mu).
Proof.
  intros pd0 pd1 HWF1 Hinter. 
  destruct pd0 as [dom0 mu0 HPD0]. destruct pd1 as [dom1 mu1 HPD1]. 
  generalize dependent mu1. induction mu0 as [|(s0, p0) mu0 Hmu]; intros.
  - simpl. apply dst_equiv_refl.
  - unfold mu. unfold dom. simpl in Hmu. simpl in Hinter.
    rewrite combine_cons_l_distr_eq. repeat rewrite res_add_decom_eq. 
    inversion HPD0; subst.
    specialize (Hmu H3 mu1 HPD1 HWF1 Hinter). 
    apply dst_equiv_trans with (mu1:= ([(s0, p0)] ⊗ mu1) \| dom0 + sum_probs mu1 * mu0). 
    + apply dst_add_inj_l. assumption.
    + destruct mu1 as [|(s1, p1) mu1]; try assumption. 
      * simpl. destruct (Req_dec_T 0 0 ); try contradiction.
      rewrite dst_mult_0_l. apply dst_equiv_refl.
      * assert (Hsum: sum_probs ((s1, p1) :: mu1) <> 0). {
          simpl in *. unfold not. intros. 
          destruct HWF1. destruct H2. destruct H2. 
          apply positive_sum_ge_0 in H4. 
          assert (Hcontra: 0< p1 + sum_probs mu1). {
            apply Rplus_lt_le_0_compat; assumption. }
          rewrite H in Hcontra. apply Rlt_irrefl in Hcontra. assumption.
      }
      rewrite dst_cons_mult_distr; try assumption.
      rewrite dst_cons_eq_add with (s:= s0) (p:= (sum_probs ((s1, p1) :: mu1) * p0)%R).
      apply dst_add_inj_r.
      apply res_comb_onest with (dom0:= dom1); try assumption.
Qed. 

Lemma dst_res_nil_implies_nil: forall mu X, 
  (mu \| X) = [] -> mu = [].
Proof.
  intros mu X H.
  induction mu as [|(s, p) mu' Hmu]; intros; try reflexivity.
  simpl in *. discriminate H.
Qed.

Lemma WF_dst_res_X_nil: forall mu X, 
  Valid_dist mu -> 
  (mu \| X) == [] -> mu == [].
Proof.
  intros mu X HWF H.
  induction mu as [|(s, p) mu' Hmu]; intros; try assumption.
  simpl in H. apply dst_cons_valid_contra in H; try contradiction.
  assert (Hcopy: ((s, p) :: mu') \| X = (res_st_to_X s X, p) :: mu' \| X). { simpl. reflexivity. }
  rewrite <- Hcopy. apply Valid_after_resX. assumption.
Qed. 

(**************************************************************)
Lemma subst_implies_res_subst: forall s X0 X1,
  is_domain_subset X0 X1 = true -> 
  is_domain_subset (return_domain (res_st_to_X s X0)) 
              (return_domain (res_st_to_X s X1)) = true.
Proof.
  intros s X0 X1 H. generalize dependent X1. generalize dependent X0.
  induction s as [|v s' Hs]; intros.
  - simpl. reflexivity.
  - destruct v; destruct X0 as [|b0 X0']; destruct X1 as [|b1 X1']; 
      simpl in *; try reflexivity; try discriminate.
    * apply andb_true_iff in H. destruct H.
      apply negb_true_iff in H. rewrite H. simpl. 
      apply all_defalut_implies_all_false.
      apply st_res_all_default. assumption.
    * apply andb_true_iff in H. destruct H.
      destruct b0; destruct b1; try discriminate. 
      + simpl. apply Hs; try assumption.
      + simpl. apply Hs; try assumption.
      + simpl. apply Hs. try assumption.
    * apply andb_true_iff in H. destruct H.
      apply all_defalut_implies_all_false.
      apply st_res_all_default. assumption.
    * apply Hs. apply andb_true_iff in H. destruct H. assumption.
Qed.

Lemma supp_after_res: forall s mu V,
  is_in_supp s (supp_mu mu) = true ->
  is_in_supp (res_st_to_X s V) (supp_mu (mu\|V)) = true.
Proof.
  intros. generalize dependent V. generalize dependent s.
  induction mu as [|(s', p') mu' Hmu]; intros; try assumption.
  unfold supp_mu in H. simpl in H. 
  rewrite insert_st_pair_fst_eq_insert_st in H.
  rewrite in_supp_insert_eq in H. apply orb_true_iff in H.
  unfold supp_mu. simpl. 
  rewrite insert_st_pair_fst_eq_insert_st.
  rewrite in_supp_insert_eq. apply orb_true_iff.
  inversion H.
  - left. apply st_eq_implies_res_X_eq. assumption.
  - right. apply Hmu. apply H0.
Qed.
(****************************************)
Lemma PD_after_res: forall X dom mu, 
  is_domain_subset X dom = true ->
  partial_dst_Prop dom mu -> 
  partial_dst_Prop X (mu\|X).
Proof.
  intros X dom mu Hsub HPD. generalize dependent X.
  induction mu as [|(s, p) mu' Hmu]; intros; try assumption.
  - simpl. apply PD_nil; try assumption.
  - simpl. inversion HPD; subst. apply PD_cons; try assumption. 
    + apply dom_equiv_sym. apply res_dom_eq_iff_subset. 
    apply dom_subset_eq_compat_left with (Z:= X) in H1; try assumption.
    + apply Hmu; try assumption.
Qed.

Definition restrict_pd (pd : partial_dist) (X: domain) 
      (Hdom: is_domain_subset X (dom pd) = true) : partial_dist :=
  {| 
    dom := X; 
    mu := (mu pd) \| X;
    all_partial := PD_after_res X (dom pd) (mu pd) Hdom (all_partial pd)
  |}.

(***************************************************)
Definition independent (mu: dist_state) (X Y: domain) : Prop :=
  let mu_X := mu \| X in
  let mu_Y := mu \| Y in
  let mu_XY_indep := mu_X ⊗ mu_Y in
  (sum_probs mu) * (mu \| (X ∪ Y)) == mu_XY_indep.

Lemma dst_subst_implies_independent: 
  forall pd pd0 pd1 (Hdom: is_domain_intersect (dom pd0) (dom pd1) = false), 
    Valid_dist (mu pd) -> Valid_dist (mu pd0) -> Valid_dist (mu pd1) ->
    (combine_pd pd0 pd1 Hdom ⊑ pd) -> 
    independent (mu pd) (dom pd0) (dom pd1).
Proof.
  intros pd pd0 pd1 Hdom Hvalid Hvalid0 Hvalid1 Hpd.
  assert (Hv_res0: Valid_dist ((mu pd) \| (dom pd0))). { apply Valid_after_resX. assumption. }
  assert (Hv_res1: Valid_dist ((mu pd) \| (dom pd1))). { apply Valid_after_resX. assumption. }
  assert (Hv_res_orb: Valid_dist ((mu pd) \| (orb_domain (dom pd0) (dom pd1)))). { 
      apply Valid_after_resX. assumption. }
  assert (Hv_comb: Valid_dist (mu pd0 ⊗ mu pd1)). { apply Valid_after_combine; assumption. }
  unfold independent. destruct Hpd. simpl in *.
  assert (Hres0: (mu pd) \| (dom pd0) == sum_probs (mu pd1) * mu pd0). {
    apply Peq_implies_res_eq with (X:=(dom pd0)) in H0; try assumption.
    - apply dst_equiv_trans with (mu1:= ((mu pd) \| (orb_domain (dom pd0) (dom pd1))) \| (dom pd0)). 
      + apply res_to_subset_equiv. apply dom_subset_orb_snd_l_r.
      + apply dst_equiv_trans with (mu1:= (mu pd0 ⊗ mu pd1) \| (dom pd0)); try assumption.
        apply res_comb_equiv; try assumption. }
  assert (Hres1: (mu pd) \| (dom pd1) == sum_probs (mu pd0) * mu pd1). {
    apply Peq_implies_res_eq with (X:=(dom pd1)) in H0; try assumption.
    - apply dst_equiv_trans with (mu1:= ((mu pd) \| (orb_domain (dom pd0) (dom pd1))) \| (dom pd1)). 
      + apply res_to_subset_equiv. apply dom_subset_orb_snd_l_r.
      + apply dst_equiv_trans with (mu1:= (mu pd0 ⊗ mu pd1) \| (dom pd1)); try assumption.
        apply dst_equiv_trans with (mu1:= (mu pd1 ⊗ mu pd0) \| (dom pd1)); 
          try apply res_sym_with_combine; try assumption.
        apply res_comb_equiv; try assumption. rewrite intersect_comm. assumption. } 
  pose (p1:= sum_probs (mu pd1)). fold p1 in Hres0. 
  pose (p0:= sum_probs (mu pd0)). fold p0 in Hres1.
  assert (Hsum: (sum_probs (mu pd) = p0 * p1)%R). {
    apply dst_equiv_implies_sum_probs_eq in H0; try assumption. 
    rewrite sum_probs_combine_eq_mult in H0. fold p0 in H0. fold p1 in H0. 
    rewrite <- sum_eq_after_res in H0. assumption. }
  rewrite Hsum.
  apply dst_equiv_trans with (mu1:= (p1 * mu pd0) ⊗ (p0 * mu pd1)); try assumption.
  - rewrite combine_mult_r_assoc_eq. 
    rewrite combine_mult_l_assoc_eq. 
    rewrite dst_mult_assoc_eq. 
    apply dst_mult_preserves_equiv. assumption. 
  - apply dst_equiv_preserves_combine; try assumption.
    + destruct Hvalid1. apply Valid_mult_cofe; try assumption.
    + destruct Hvalid0. apply Valid_mult_cofe; try assumption. 
    + apply Peq_implies_res_eq with (X:= dom pd0) in H0. 
      * apply dst_equiv_trans with (mu2:= p1 * mu pd0) in H0; try apply res_comb_equiv; try assumption.
        apply dst_equiv_sym. 
        apply dst_equiv_trans with (mu1:= (mu pd \| (dom pd0 ∪ dom pd1)) \| dom pd0); try assumption. 
        apply res_to_subset_equiv. apply dom_subset_orb_snd_l_r.
      * apply Valid_after_resX. assumption.
      * apply Valid_after_combine; assumption.
    + apply Peq_implies_res_eq with (X:= dom pd1) in H0. 
      * apply dst_equiv_trans with (mu2:= (mu pd1 ⊗ mu pd0) \| dom pd1) in H0; try apply res_sym_with_combine; try assumption.
        rewrite intersect_comm in Hdom.
        apply dst_equiv_trans with (mu2:= p0 * mu pd1) in H0; try apply res_comb_equiv; try assumption.
        apply dst_equiv_sym. 
        apply dst_equiv_trans with (mu1:= (mu pd \| (dom pd0 ∪ dom pd1)) \| dom pd1); try assumption. 
        apply res_to_subset_equiv. apply dom_subset_orb_snd_l_r.
      * apply Valid_after_resX. assumption.
      * apply Valid_after_combine; assumption.
Qed.

Lemma independent_implies_combine_equiv: forall pd pd' (Hdom: (dom pd ∩∅ dom pd')%domain), 
  independent (mu (combine_pd pd pd' Hdom)) (dom pd) (dom pd') -> 
  Valid_dist (mu pd) -> Valid_dist (mu pd') ->
  (sum_probs (mu pd ⊗ mu pd') * (mu pd ⊗ mu pd') ==
   (sum_probs (mu pd') * mu pd) ⊗ (sum_probs (mu pd) * mu pd'))%dist_state.
Proof.
  intros.
  pose (Sten:= sum_probs (mu pd ⊗ mu pd')). fold Sten. 
  pose (Smu:= sum_probs (mu pd)). fold Smu.
  pose (Smu':= sum_probs (mu pd')). fold Smu'.
  assert (Hsumc: (Sten = Smu * Smu')%R). { unfold Sten, Smu, Smu'. apply sum_probs_combine_eq_mult. }
  unfold independent in *. simpl in H. fold Sten in H. 
  apply dst_equiv_trans with (mu0:= (Sten * (mu pd ⊗ mu pd'))%dist_state) in H;
  apply dst_equiv_trans with (mu2:= (((Smu' * mu pd) ⊗ (Smu * mu pd')))%dist_state) in H; try assumption.
  - apply dst_equiv_preserves_combine; try apply Valid_after_resX; try apply Valid_mult_cofe; try apply Valid_after_combine; try assumption.
    + destruct H1. assumption.
    + destruct H0. assumption.
    + apply res_comb_equiv; try assumption.
    + apply dst_equiv_trans with (mu1:= (mu pd' ⊗ mu pd) \| dom pd'). 
      * apply Peq_implies_res_eq; try apply Valid_after_combine; try assumption. apply combine_sym.
      * rewrite intersect_comm in Hdom. apply res_comb_equiv; try assumption.
  - apply dst_mult_preserves_equiv. apply dst_equiv_sym. 
    apply res_pd_to_dom_refl with (pd:= combine_pd pd pd' Hdom); try assumption.
  - apply dst_equiv_preserves_combine; try apply Valid_after_resX; try apply Valid_mult_cofe; try apply Valid_after_combine; try assumption.
    + destruct H1. assumption.
    + destruct H0. assumption.
    + apply res_comb_equiv; try assumption.
    + apply dst_equiv_trans with (mu1:= (mu pd' ⊗ mu pd) \| dom pd'). 
      * apply Peq_implies_res_eq; try apply Valid_after_combine; try assumption. apply combine_sym.
      * rewrite intersect_comm in Hdom. apply res_comb_equiv; try assumption.
Qed.

Lemma subst_preserves_independent: 
  forall pd dom0 dom1 X0 X1, 
    Valid_dist (mu pd) ->
    is_domain_subset X0 dom0 = true -> is_domain_subset X1 dom1 = true ->
    is_domain_intersect (dom0) (dom1) = false ->
    is_domain_subset dom0 pd.(dom) = true -> is_domain_subset dom1 pd.(dom) = true ->
    independent (mu pd) dom0 dom1 ->
    independent (mu pd) X0 X1.
Proof.
  intros pd dom0 dom1 X0 X1 HV Hdom0 Hdom1 Hinter Hsub0 Hsub1 Hpd.
  unfold independent in *.
  destruct pd as [dom' mu' HPD]. simpl in *.
  assert (Heq: sum_probs (mu' \| (orb_domain dom0 dom1)) = 
                sum_probs (mu' \| (orb_domain X0 X1))). {
                  repeat rewrite <- sum_eq_after_res. reflexivity. }
  pose(p:= sum_probs (mu')).
  fold p in Hpd. fold p. 
  pose (A:= (orb_domain dom0 dom1)).
  pose (B:= (orb_domain X0 X1)).
  fold B. fold A in Hpd.
  assert (Hsub: is_domain_subset B A = true). { apply dom_subset_orb_compat; assumption. }
  apply Peq_implies_res_eq with (X:= B) in Hpd; try assumption.
  - assert (Heq1: p * mu' \| B ==(p * mu' \| A) \| B). {
      rewrite res_dst_to_X_mult_coef.    
      apply dst_mult_preserves_equiv.
      apply res_to_subset_equiv. assumption. }
    apply dst_equiv_trans with (mu0:= (p * (mu' \| A)) \| B) in Hpd; try assumption;
    apply dst_equiv_trans with (mu1:= (p * (mu' \| B))); try assumption.
    * apply dst_mult_preserves_equiv. apply dst_equiv_sym. apply dst_equiv_refl. 
    * apply dst_equiv_trans with (mu1:= (p * mu' \| A) \| B); try assumption.
      apply dst_equiv_trans with (mu1:= (mu' \| dom0 ⊗ mu' \| dom1) \| B); try assumption.
      + pose (pd0':= Build_partial_dist (dom0) (mu' \| dom0) (PD_after_res dom0 dom' mu' Hsub0 HPD)).
      pose (pd1':= Build_partial_dist (dom1) (mu' \| dom1) (PD_after_res dom1 dom' mu' Hsub1 HPD)).
      assert (Htmp: (((pd0'.(mu)) \| X0) ⊗ ((pd1'.(mu)) \| X1) ==
                      ((pd0'.(mu)) ⊗ (pd1'.(mu))) \| (orb_domain X0 X1))%dist_state). {
        apply combine_res_merge_equiv with (pd0:= pd0') (pd1:= pd1'); try assumption. }
      simpl in Htmp. apply dst_equiv_sym. 
      apply dst_equiv_trans with (mu1:= (mu' \| dom0) \| X0 ⊗ (mu' \| dom1) \| X1); try assumption.
      apply dst_equiv_preserves_combine; try assumption. 
      ** apply Valid_after_resX; try assumption.
      ** apply Valid_after_resX; apply Valid_after_resX; try assumption.
      ** apply Valid_after_resX; try assumption.
      ** apply Valid_after_resX; apply Valid_after_resX; try assumption.
      ** apply res_to_subset_equiv. assumption.
      ** apply res_to_subset_equiv. assumption.
    * apply dst_equiv_sym. assumption.
  - apply Valid_mult_cofe; try apply Valid_after_resX; try assumption. destruct HV. try assumption.
  - apply Valid_after_combine; apply Valid_after_resX; try assumption.
Qed. 

(**********************pd_subst reflexivity******)  

Lemma relation_mu_refl : forall pd, pd ⊑ pd.
Proof.
  intros. unfold partial_dst_equiv. 
  split; try apply dom_subset_refl.
  apply res_pd_to_dom_refl.
Qed.
Lemma relation_mu_trans : forall pd1 pd2 pd3, 
  Valid_dist (mu pd1) -> Valid_dist (mu pd2) -> Valid_dist (mu pd3) ->
  pd1 ⊑ pd2 -> pd2 ⊑ pd3 -> pd1 ⊑ pd3.
Proof.
  intros pd1 pd2 pd3 Hwf1 Hwf2 Hwf3.
  intros [H1_sub H1_eq] [H2_sub H2_eq].
  split. 
  - apply dom_subset_trans with (pd2.(dom)); try assumption.
  - apply res_dst_to_dom_trans with (pd2:= pd2); try assumption.
Qed.

Lemma comb_pd_subst: 
  forall (pd1 pd2: partial_dist) (Hdom: is_domain_intersect (dom pd1) (dom pd2) = false), 
  Valid_dist (mu pd2) ->
  let p:= sum_probs (mu pd2) in
  (Build_partial_dist (dom pd1) (p * (mu pd1)) (pd_mult_preserve_PD pd1 p)) ⊑ (combine_pd pd1 pd2 Hdom).
Proof.
  intros pd1 pd2 Hdom. 
  split; simpl. 
  - apply dom_subset_orb_snd_l_r.
  - apply res_comb_equiv; try assumption. 
Qed.


Lemma subst_mu_mult_coef :
  forall (pd1 pd2 : partial_dist) (p : R)
         (Hle : pd1 ⊑ pd2)
         (H1 : partial_dst_Prop pd1.(dom) (p * pd1.(mu)))
         (H2 : partial_dst_Prop pd2.(dom) (p * pd2.(mu))),
    let pd1' := Build_partial_dist pd1.(dom) (p * pd1.(mu)) H1 in
    let pd2' := Build_partial_dist pd2.(dom) (p * pd2.(mu)) H2 in
    pd1' ⊑ pd2'.
Proof.
  intros pd1 pd2 p Hle H1 H2.
  destruct Hle. split; simpl; try assumption.
  rewrite res_dst_to_X_mult_coef. 
  apply dst_mult_preserves_equiv. assumption.
Qed.
