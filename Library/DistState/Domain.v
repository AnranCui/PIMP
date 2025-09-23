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
Require Import Library.DistState.CoreDef.
Open Scope list_scope.
Open Scope domain_scope.
(* This file contains properties of domain operation *)
(*uniou orb*)
Lemma orb_iff_nil: forall l l', 
  orb_domain l l' = [] <-> l = [] /\ l' = [].
Proof.
  split.
  - intros. destruct l as [| b l]; destruct l' as [| b' l']; split; try reflexivity.
    + simpl in H. inversion H.
    + simpl in H. inversion H.
    + simpl in H. inversion H.
    + simpl in H. inversion H.
  - intros. destruct H as [H1 H2]. rewrite H1. rewrite H2. simpl. reflexivity.
Qed.
  
Lemma orb_domain_nil_r: forall l, orb_domain l [] = l.
Proof.
  intros. induction l as [|h l' IH]; intros; simpl; reflexivity. 
Qed.

Lemma orb_domain_nil_l: forall l, orb_domain [] l = l.
Proof.
  intros. induction l as [|h l' IH]; intros; simpl; reflexivity. 
Qed.

Lemma orb_domain_refl: forall l, orb_domain l l = l.
Proof.
  intros. induction l as [|h l' IH]; intros; simpl.
  - reflexivity. - rewrite orb_diag. f_equal. apply IH.
Qed.
  
Lemma orb_domain_comm: forall (l l': domain), 
  orb_domain l l' = orb_domain l' l.
Proof.
  intros l l'. generalize dependent l'. 
  induction l as [|h l IH]; intros; simpl; destruct l' as [|h' l'].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity. 
  - simpl. specialize (IH l'). rewrite IH. f_equal. apply orb_comm.
Qed.
  
Lemma orb_domain_assoc: forall l0 l1 l2, 
  orb_domain l0 (orb_domain l1 l2) = orb_domain (orb_domain l0 l1) l2.
Proof.
  intros l0 l1 l2. generalize dependent l2. generalize dependent l1. 
  induction l0 as [|b0 l0' Hl0]; intros l1 l2; 
  destruct l1 as [|b1 l1']; destruct l2 as [|b2 l2'] .
  - simpl. reflexivity.
  - simpl. reflexivity. 
  - simpl. reflexivity. 
  - simpl. reflexivity. 
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. specialize (Hl0 l1' l2'). rewrite Hl0. f_equal. apply orb_assoc. 
Qed.



(*intersect*)
Lemma intersect_nil_r: forall l, is_domain_intersect l [] = false.
Proof.
  induction l as [ | s l']; intros.
  - simpl. reflexivity.
  - simpl in *. reflexivity.
Qed.

Lemma intersect_comm: forall l0 l1, 
  is_domain_intersect l0 l1 = is_domain_intersect l1 l0.
Proof.
  intros. generalize dependent l1. induction l0 as [| h0 l0' IH]; intros; simpl in *.
  - rewrite intersect_nil_r. reflexivity.
  - destruct l1 as [| h1 l1']; simpl in *; try reflexivity.
    rewrite andb_comm. destruct (h1&&h0); try reflexivity. 
    apply IH.
Qed.

Lemma intersect_orb_snd_left: forall l0 l1 l2,
  is_domain_intersect l0 (orb_domain l1 l2) = false -> 
  is_domain_intersect l0 l1 = false.
Proof.
  intros. generalize dependent l2. generalize dependent l1.
  induction l0 as [ | s0 l0' Hl0]; intros.
  - simpl. reflexivity.
  - destruct l1 as [ | s1 l1']; destruct l2 as [ | s2 l2']; intros.
    + simpl in *. reflexivity.
    + simpl in *. reflexivity.
    + simpl in *. assumption.
    + simpl in *. destruct (s0 && (s1 || s2)) eqn: Htest.
      * discriminate.
      * unfold andb in Htest. destruct s0; destruct s1; destruct s2; simpl in *; 
      try discriminate; try apply Hl0 with (l2:= l2'); try assumption.
Qed.

Lemma intersect_orb_fst_left: forall l0 l1 l2,
  is_domain_intersect (orb_domain l0 l1) l2 = false -> 
  is_domain_intersect l0 l2 = false.
Proof.
  intros. generalize dependent l2. generalize dependent l1.
  induction l0 as [ | s0 l0' Hl0]; intros.
  - simpl. reflexivity.
  - destruct l1 as [ | s1 l1']; destruct l2 as [ | s2 l2']; intros.
    + simpl in *. reflexivity.
    + simpl in *. assumption.
    + simpl in *. reflexivity.
    + simpl in *. destruct ((s0 || s1) && s2) eqn: Htest.
      * discriminate.
      * apply andb_false_iff in Htest. inversion Htest.
      ** apply orb_false_iff in H0. inversion H0.
      rewrite H1. simpl. apply Hl0 with (l1:= l1'); try assumption.
      ** rewrite H0. rewrite andb_false_r. apply Hl0 with (l1:= l1'); try assumption.
Qed.

Lemma intersect_orb_fst_right: forall l0 l1 l2,
  is_domain_intersect (orb_domain l0 l1) l2 = false -> 
  is_domain_intersect l1 l2 = false.
Proof.
  intros. generalize dependent l2. generalize dependent l0.
  induction l1 as [ | s0 l0' Hl0]; intros.
  - simpl. reflexivity.
  - destruct l0 as [ | s1 l1']; destruct l2 as [ | s2 l2']; intros.
    + simpl in *. reflexivity.
    + simpl in *. assumption.
    + simpl in *. reflexivity.
    + simpl in *. destruct ((s1 || s0) && s2) eqn: Htest.
      * discriminate.
      * apply andb_false_iff in Htest. inversion Htest.
      ** apply orb_false_iff in H0. inversion H0.
      ++ rewrite H2. simpl. apply Hl0 with (l0:= l1'); try assumption.
      ** rewrite H0. rewrite andb_false_r. apply Hl0 with (l0:= l1'); try assumption.
Qed.


Lemma intersect_orb_snd_conj: forall l0 l1 l2, 
  is_domain_intersect l0 (orb_domain l1 l2) = false -> 
  is_domain_intersect l0 l1 = false /\ is_domain_intersect l0 l2 = false.
Proof.
  intros. split.
  - apply intersect_orb_snd_left in H. assumption.
  - rewrite orb_domain_comm in H. apply intersect_orb_snd_left in H. assumption.
Qed.

Lemma intersect_orb_l_iff: forall l0 l1 l, 
  is_domain_intersect l0 l = false -> is_domain_intersect l1 l = false ->
  is_domain_intersect (orb_domain l0 l1) l = false.
Proof.
  intros. generalize dependent l. generalize dependent l1.
  induction l0 as [ | s0 l0' Hl0]; intros.
  - simpl. assumption.
  - destruct l1 as [ | s1 l1']; destruct l as [ | s l']; intros. 
    + simpl. reflexivity.
    + simpl in H. simpl. assumption.
    + simpl. reflexivity.
    + simpl. simpl in H. simpl in H0. 
      destruct s0; destruct s; destruct s1; simpl in H; simpl in H0; 
        simpl; try discriminate; try assumption; apply Hl0; try assumption.
Qed.

Lemma intersect_orb_r_iff: forall l0 l1 l2, 
  is_domain_intersect l0 l1 = false -> is_domain_intersect l0 l2 = false ->
  is_domain_intersect l0 (orb_domain l1 l2) = false.
Proof.
  intros. generalize dependent l1. generalize dependent l2.
  induction l0 as [ | s0 l0' Hl0]; intros.
  - simpl. assumption.
  - destruct l1 as [ | s1 l1']; destruct l2 as [ | s2 l2']; intros. 
    + simpl. reflexivity.
    + simpl in H. simpl. assumption.
    + simpl in *. assumption.
    + simpl. simpl in H. simpl in H0. 
      destruct s0; destruct s1; destruct s2; simpl in H; simpl in H0; 
        simpl; try discriminate; try assumption; apply Hl0; try assumption.
Qed.

Lemma all_false_implies_intersect_false: forall l l', 
  all_false l = true -> is_domain_intersect l' l = false.
Proof.
  intros. generalize dependent l'. 
  induction l as [|h t IH]; destruct l' as [|h' t']; 
    simpl in *; try reflexivity; try discriminate.
  apply andb_true_iff in H. destruct H.
  apply negb_true_iff in H. rewrite H. 
  rewrite andb_false_r. apply IH. assumption.
Qed.

Lemma intersect_subst_trans: forall l0 l1 l2, 
  is_domain_intersect l0 l2 = false ->
  is_domain_subset l1 l2 = true -> 
  is_domain_intersect l0 l1 = false.
Proof.
  intros. generalize dependent l2. generalize dependent l1. 
  induction l0 as [| b0 l0' Hl0]; intros.
  - simpl. reflexivity.
  - destruct l1 as [| b1 l1']; destruct l2 as [| b2 l2']; intros.
    + simpl in *. reflexivity.
    + simpl in *. reflexivity.
    + simpl in *. apply andb_true_iff in H0. destruct H0.
      apply negb_true_iff in H0. rewrite H0. rewrite andb_false_r. 
      apply all_false_implies_intersect_false. assumption.
    + simpl in *. apply andb_true_iff in H0. destruct H0.
      apply orb_true_iff in H0. destruct H0; subst.
      * apply negb_true_iff in H0. rewrite H0. rewrite andb_false_r.
      destruct b0; destruct b2; simpl in *; try discriminate. 
      ** apply Hl0 with (l2:= l2'); try assumption.
      ** apply Hl0 with (l2:= l2'); try assumption.
      ** apply Hl0 with (l2:= l2'); try assumption.
      * rewrite andb_true_r in H. destruct b0; try discriminate. 
      rewrite andb_false_l. apply Hl0 with (l2:= l2'); try assumption.
Qed.

(******subst***)

Lemma dom_subset_refl: forall l, is_domain_subset l l = true.
Proof.
  intros. induction l as [|h t IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. destruct h; reflexivity.
Qed.

Lemma all_false_implies_subset_bool: forall l l', 
  all_false l = true -> is_domain_subset l l' = true.
Proof.
  intros. generalize dependent l'. 
  induction l as [|h t IH]; destruct l' as [|h' t'].
  - simpl in *; reflexivity.
  - simpl in *; try reflexivity.
  - simpl in *; try assumption. 
  - simpl in *; try assumption. 
  apply andb_true_iff in H. destruct H.
  rewrite H. simpl. apply IH. assumption.
Qed.

Lemma all_false_implies_subst_all_false: forall l l', 
  all_false l' = true -> is_domain_subset l l' = true -> 
  all_false l = true.
Proof.
  intros. generalize dependent l'. 
  induction l as [|h t IH]; destruct l' as [|h' t']; intros.
  - simpl in *; try assumption.
  - simpl in *; try assumption.
  - simpl in *. destruct (negb h && all_false t)eqn: H'; try assumption; try discriminate.
  - simpl in *. apply andb_true_iff in H. destruct H. 
  apply andb_true_iff in H0. destruct H0. 
  apply andb_true_iff. 
  apply orb_true_iff in H0. inversion H0; subst.
    + split; try assumption. apply IH with (l':= t'); try assumption.
    + simpl in H. inversion H. 
Qed.

Lemma dom_subset_trans (l0 l1 l2: domain): 
  is_domain_subset l0 l1 = true -> is_domain_subset l1 l2 = true -> 
  is_domain_subset l0 l2 = true.
Proof.
  intros. generalize dependent l2. generalize dependent l1.
  induction l0 as [| b0 l0' Hl0].
  - intros. simpl. reflexivity.
  - intros l1 Hl1 l2 Hl2. destruct l1 as [| b1 l1'].
    + simpl in *. destruct l2 as [| b2 l2'].
      * assumption.
      * destruct (negb b0 && all_false l0') eqn: H'; try discriminate. 
      apply andb_true_iff in H'. destruct H'.
      apply andb_true_iff. split. 
      -- rewrite H. simpl. reflexivity.
      -- apply all_false_implies_subset_bool; try assumption.
    + simpl in *. destruct l2 as [| b2 l2']; simpl in *.
      * apply andb_true_iff in Hl1. destruct Hl1. 
      apply orb_true_iff in H. destruct H; subst. 
      ** rewrite H. simpl. 
      destruct (negb b1 && all_false l1') eqn: H'; try discriminate.
      apply andb_true_iff in H'. destruct H'.
      apply all_false_implies_subst_all_false in H0; try assumption.
      ** destruct (negb true && all_false l1') eqn: H'; try discriminate.
      * apply andb_true_iff in Hl1. destruct Hl1. 
      apply andb_true_iff in Hl2. destruct Hl2.
      apply andb_true_iff. split.
      -- apply orb_true_iff in H. destruct H.
      ++ rewrite H. simpl. reflexivity.
      ++ apply orb_true_iff in H1. destruct H1.
      ** rewrite H in H1. simpl in H1. discriminate.
      ** rewrite H1. apply orb_true_r. 
      -- apply Hl0 with (l1:= l1'); try assumption.
Qed.


Lemma dom_subset_orb_dom_r: forall l l0 l1,
  is_domain_subset l l0 = true -> is_domain_subset l (orb_domain l0 l1) = true.
Proof.
  intros. generalize dependent l1. generalize dependent l0.
  induction l as [| b l' Hl]; intros.
  - intros. simpl. reflexivity.
  - destruct l0; destruct l1; simpl in *; try discriminate; try assumption. 
    * destruct (negb b && all_false l') eqn : H'; try discriminate. 
      apply andb_true_iff in H'. destruct H'. 
      apply andb_true_iff. split.
      + rewrite H0. simpl. reflexivity.
      + apply all_false_implies_subset_bool. assumption.
    * apply andb_true_iff in H. destruct H. 
      apply orb_true_iff in H. inversion H; subst. 
      + rewrite H1. simpl. apply Hl. assumption.
      + simpl. rewrite orb_true_r. simpl. 
      apply Hl. assumption.
Qed.
Lemma dom_subset_orb_dom_l: forall l l0 l1,
  is_domain_subset l l1 = true -> is_domain_subset l (orb_domain l0 l1) = true.
Proof.
  intros. rewrite orb_domain_comm. apply dom_subset_orb_dom_r. assumption.
Qed.

Lemma dom_subset_orb_snd_l_r (l0 l1: domain):
  is_domain_subset l0 (orb_domain l0 l1) = true /\ is_domain_subset l1 (orb_domain l0 l1) = true.
Proof.
  split.
  { 
    generalize dependent l1. induction l0 as [| b0 l0' Hl0].
    - intros. simpl. reflexivity.
    - intros l1. destruct l1 as [| b1 l1'].
      + simpl in *. apply andb_true_iff. 
      split; try apply orb_negb_l. apply dom_subset_refl.
      + simpl in *. apply andb_true_iff. split.
        * rewrite orb_assoc. rewrite orb_negb_l. simpl. reflexivity.
        * apply Hl0. }
  { generalize dependent l0. induction l1 as [| b1 l1' Hl1].
    - intros. simpl. reflexivity.
    - intros l0. destruct l0 as [| b0 l0'].
      + simpl in *. apply andb_true_iff. 
      split; try apply orb_negb_l. apply dom_subset_refl.
      + simpl in *. apply andb_true_iff. split.
        * simpl. rewrite orb_comm with (b1:= b0). 
        rewrite orb_assoc. rewrite orb_negb_l. simpl. reflexivity.
        * apply Hl1. }
Qed.

Lemma all_false_orb: forall l l0, 
  all_false l0 = true -> all_false l = true -> 
  all_false (orb_domain l l0) = true.
Proof.
  intros. generalize dependent l0. induction l as [| b l' Hl]; intros.
  - simpl. assumption.
  - destruct l0 as [| b' l0'].
    + simpl in *. assumption.
    + simpl in *. apply andb_true_iff in H. destruct H.
    apply andb_true_iff in H0. destruct H0.
    apply andb_true_iff. rewrite negb_orb. 
    rewrite H0. rewrite H. simpl. 
    split; try reflexivity.
    apply Hl; try assumption.
Qed.

Lemma dom_subset_orb_fst_iff (l0 l1 X: domain): 
  is_domain_subset (orb_domain l0 l1) X = true <-> 
  is_domain_subset l0 X = true /\ is_domain_subset l1 X = true.
Proof.
  split.
  - split.
  { intros. generalize dependent X. generalize dependent l1.
    induction l0 as [| b0 l0' Hl0].
    - intros. simpl. reflexivity.
    - intros l1 X HX. 
    apply dom_subset_trans with (l1:= (orb_domain (b0 :: l0') l1)); try assumption.
    apply dom_subset_orb_snd_l_r. }
  { intros. generalize dependent X. generalize dependent l0.
    induction l1 as [| b1 l1' Hl1].
    - intros. simpl. reflexivity.
    - intros l0 X HX.
    apply dom_subset_trans with (l1:= (orb_domain l0 (b1 :: l1'))); try assumption.
    apply dom_subset_orb_snd_l_r. }
  - intros. destruct H. generalize dependent l1. generalize dependent X.
    induction l0 as [| b0 l0' Hl0]; intros.
    + simpl. assumption.
    + destruct l1 as [| b1 l1']. 
      * rewrite orb_domain_nil_r. assumption.
      * destruct X as [| bX X'].
      ** simpl in *. 
      destruct (negb b0 && all_false l0') eqn: H'; 
        destruct (negb b1 && all_false l1') eqn: H0'; try discriminate.
      apply andb_true_iff in H'. destruct H'. 
      apply andb_true_iff in H0'. destruct H0'. 
      rewrite negb_orb. rewrite H1. rewrite H3.
      rewrite all_false_orb; try assumption.
      ** simpl in *.
      apply andb_true_iff in H. destruct H. 
      apply andb_true_iff in H0. destruct H0.
      apply andb_true_iff. rewrite negb_orb.
      split. 
      -- apply orb_true_iff in H. apply orb_true_iff in H0.
      inversion H; inversion H0; subst.
      ++ rewrite H3. rewrite H4. simpl. reflexivity.
      ++ rewrite H3. simpl in *. apply orb_true_r.
      ++ rewrite H4. simpl in *. apply orb_true_r.
      ++ simpl. apply orb_true_r.
      -- apply Hl0; try assumption.
Qed.

Lemma dom_subset_orb_compat: forall l0 l1 X0 X1,  
  is_domain_subset l0 X0 = true -> is_domain_subset l1 X1 = true ->
  is_domain_subset (orb_domain l0 l1) (orb_domain X0 X1) = true.
Proof.
  intros. apply dom_subset_orb_fst_iff. split.
  - apply dom_subset_orb_dom_r. assumption. 
  - apply dom_subset_orb_dom_l. assumption. 
Qed.

Lemma dom_equiv_refl : forall l, l == l.
Proof.
  intros. induction l as [|h l' IH]; simpl.
  - split; simpl; reflexivity.  
  - destruct IH. split; simpl. 
    + apply andb_true_iff. split; try assumption. apply orb_negb_l.
    + apply andb_true_iff. split; try assumption. apply orb_negb_l.
Qed.

Lemma dom_equiv_sym: forall l0 l1, l0 == l1 -> l1 == l0.
Proof.
  intros. generalize dependent l1. induction l0 as [|h l0' IH]; simpl; intros.
  - destruct H. split; simpl; try assumption. 
  - destruct l1 as [ | h1 l1']. 
    + destruct H. split; simpl; try assumption. 
    + destruct H. split; simpl; try assumption. 
Qed.

Lemma dom_equiv_trans: forall l0 l1 l2, l0 == l1 -> l1 == l2 -> l0 == l2.
Proof.
  intros. destruct H. destruct H0. split; try assumption.
  - apply dom_subset_trans with (l1:= l1); try assumption.
  - apply dom_subset_trans with (l1:= l1); try assumption.
Qed.


Lemma all_false_iff_nil: forall l, all_false l = true <-> l == [].
Proof.
  split. { 
  intros. induction l as [|h l' IH]; simpl.
  - split; simpl; try assumption. 
  - simpl in *. apply andb_true_iff in H. destruct H. 
    apply negb_true_iff in H. rewrite H. split.
    + simpl. assumption.
    + simpl. reflexivity. }
  intros. induction l as [|h l' IH]; simpl.
  - reflexivity.
  - destruct H. simpl in *. assumption.
Qed.

Lemma dom_cons_nil_implies_tail_nil: forall h l, 
  h :: l == [] -> l == [].
Proof.
  intros. destruct H. simpl in *. 
  apply andb_true_iff in H. destruct H.
  apply all_false_iff_nil; try assumption.
Qed.

Lemma all_false_orb_l: forall l l1, all_false l = true -> orb_domain l l1 == l1.
Proof.
  intros. generalize dependent l1. induction l as [|b l' IH]; intros. 
  - simpl. apply dom_equiv_refl.
  - simpl in H. apply andb_true_iff in H. destruct H.
    destruct l1 as [|b1 l1']; simpl in *; try assumption. 
    + apply all_false_iff_nil. simpl. apply andb_true_iff. split; try assumption. 
    + apply negb_true_iff in H. rewrite H. simpl. 
      apply IH with (l1:= l1') in H0. destruct H0. split; simpl in *. 
      * apply andb_true_iff. split; try assumption. apply orb_negb_l.
      * apply andb_true_iff. split; try assumption. apply orb_negb_l.
Qed.

Lemma dom_eq_orb_compat_right: forall l0 l1 l2, 
  (l0 == l1)%domain -> 
  (orb_domain l0 l2 == orb_domain l1 l2)%domain.
Proof.
  intros l0 l1 l2 H. generalize dependent l2. generalize dependent l1.
  induction l0 as [|b0 l0' IH]; intros. 
  - simpl. apply dom_equiv_sym in H. apply all_false_iff_nil in H. 
    apply dom_equiv_sym. apply all_false_orb_l. assumption.
  - destruct l1 as [|b1 l1']; destruct l2 as [|b2 l2']; 
      simpl in *; try assumption. 
    + assert (H': l0' == []). { apply dom_cons_nil_implies_tail_nil in H. assumption. }
      specialize (IH [] H' l2'). destruct IH. destruct H. simpl in *.
      split; simpl. 
      * apply andb_true_iff. split; try assumption.
        apply andb_true_iff in H. destruct H.
        rewrite negb_orb. rewrite H. simpl. apply orb_negb_l.
      * apply andb_true_iff. split; try assumption.
        apply andb_true_iff in H. destruct H. 
        apply negb_true_iff in H. rewrite H. simpl. apply orb_negb_l.
    + destruct H. simpl in H. simpl in H0. 
      apply andb_true_iff in H. destruct H.
      apply andb_true_iff in H0. destruct H0.
      assert (H': l0' == l1'). { split; try assumption. }
      specialize (IH l1' H' l2'). destruct IH. 
      apply orb_true_iff in H. apply orb_true_iff in H0.
      split; simpl.
      * apply andb_true_iff. split; try assumption.
      destruct H; destruct H0; subst; try discriminate. 
      ** apply negb_true_iff in H0. rewrite H0. 
      apply negb_true_iff in H. rewrite H.
      simpl. apply orb_negb_l.
      ** simpl. reflexivity.
      * apply andb_true_iff. split; try assumption.
      destruct H; destruct H0; subst; try discriminate. 
      ** apply negb_true_iff in H0. rewrite H0. 
      apply negb_true_iff in H. rewrite H.
      simpl. apply orb_negb_l.
      ** simpl. reflexivity.
Qed.
Lemma dom_eq_orb_compat_left: forall l0 l1 l2, 
  (l0 == l1)%domain -> 
  (orb_domain l2 l0 == orb_domain l2 l1)%domain.
Proof.
  intros. apply dom_eq_orb_compat_right with (l2:= l2) in H; try assumption.
  rewrite orb_domain_comm in H. 
  apply dom_equiv_trans with (l1:= orb_domain l1 l2); try assumption.
  rewrite orb_domain_comm. apply dom_equiv_refl.
Qed.

Lemma dom_eq_orb_compat: forall l0 l1 l2 l3, 
  (l0 == l1)%domain -> 
  (l2 == l3)%domain -> 
  (orb_domain l0 l2 == orb_domain l1 l3)%domain.
Proof.
  intros. apply dom_equiv_trans with (l1:= l0 ∪ l3).
  - apply dom_eq_orb_compat_left. try assumption.
  - apply dom_eq_orb_compat_right; try assumption.
Qed.

Lemma dom_eq_intersect_compat_left: forall l0 l1 l,
  l0 == l1 -> 
  is_domain_intersect l l0 = is_domain_intersect l l1.
Proof.
  intros. 
  generalize dependent l1. generalize dependent l0. 
  induction l as [|h l' IH]; intros.
  - simpl in *. reflexivity.
  - simpl. destruct l0 as [ | h0 l0']; destruct l1 as [ | h1 l1']; 
    try discriminate; try reflexivity.
    + apply dom_equiv_sym in H. 
      assert( Hl1': l1' == []). { apply dom_cons_nil_implies_tail_nil in H. assumption. }
      specialize (IH l1' [] Hl1').  
      rewrite intersect_nil_r in IH. 
      destruct H. simpl in *. apply andb_true_iff in H. destruct H.
      apply negb_true_iff in H. rewrite H. 
      destruct (h && false) eqn: H'.
      * rewrite andb_false_r in H'. inversion H'.
      * rewrite IH. reflexivity.
    + apply dom_equiv_sym in H. 
      assert( Hl0': l0' == []). { 
        apply dom_equiv_sym in H.  
        apply dom_cons_nil_implies_tail_nil in H. assumption. }
      specialize (IH l0' [] Hl0').  
      rewrite intersect_nil_r in IH. 
      destruct H. simpl in *. apply andb_true_iff in H0. destruct H0.
      apply negb_true_iff in H0. rewrite H0. 
      destruct (h && false) eqn: H'.
      * rewrite andb_false_r in H'. inversion H'.
      * rewrite IH. reflexivity.
    + destruct h. 
      * repeat rewrite andb_true_l. 
      destruct H. simpl in H. simpl in H0. 
      apply andb_true_iff in H0. destruct H0.
      apply andb_true_iff in H. destruct H.
      destruct h0; destruct h1; try discriminate; try reflexivity.
      apply IH. split; try assumption.
      * repeat rewrite andb_false_l. 
      destruct H. simpl in H. simpl in H0. 
      apply andb_true_iff in H0. destruct H0.
      apply andb_true_iff in H. destruct H.
      destruct h0; destruct h1; try discriminate; try reflexivity;
      apply IH; split; try assumption.
Qed.

Lemma dom_eq_intersect_compat_right: forall l0 l1 l,
  l0 == l1 -> 
  is_domain_intersect l0 l= is_domain_intersect l1 l.
Proof.
  intros. rewrite intersect_comm. rewrite intersect_comm with (l1:= l). 
  apply dom_eq_intersect_compat_left; assumption.
Qed.

Lemma dom_eq_intersect_preserves_equiv: forall l0 l1 l2 l3,
  l0 == l1 -> l2 == l3 ->
  is_domain_intersect l0 l2 = is_domain_intersect l1 l3.
Proof.
  intros. 
  apply dom_eq_intersect_compat_left with (l:= l2) in H.
  apply dom_eq_intersect_compat_left with (l:= l1) in H0.
  rewrite intersect_comm in H. rewrite H. rewrite <- H0.
  apply intersect_comm.
Qed.

Lemma dom_eq_orb_dis_l: forall l0 l1 l, 
  (((l0 ∪ l1) ∪ l)%domain == ((l0 ∪ l) ∪ (l1 ∪ l))%domain).
Proof.
  intros. split.
  - apply dom_subset_orb_fst_iff. split. 
    + apply dom_subset_orb_fst_iff. split. 
      * apply dom_subset_trans with (l1:= l0 ∪ l1); try assumption. 
      ** apply dom_subset_orb_snd_l_r. 
      ** apply dom_subset_orb_compat; apply dom_subset_orb_snd_l_r.
      * apply dom_subset_trans with (l1:= l0 ∪ l1); try assumption. 
      ** apply dom_subset_orb_snd_l_r. 
      ** apply dom_subset_orb_compat; apply dom_subset_orb_snd_l_r.
    + apply dom_subset_trans with (l1:= l0 ∪ l); try assumption. 
      ** apply dom_subset_orb_snd_l_r. 
      ** apply dom_subset_orb_snd_l_r.
  - apply dom_subset_orb_fst_iff. split. 
    + apply dom_subset_orb_fst_iff. split. 
      * apply dom_subset_trans with (l1:= l0 ∪ l1); try assumption.
      ** apply dom_subset_orb_snd_l_r.
      ** apply dom_subset_orb_snd_l_r.
      * apply dom_subset_orb_snd_l_r.
    + apply dom_subset_orb_compat; try apply dom_subset_orb_snd_l_r.
      apply dom_subset_refl.
Qed.

Lemma dom_eq_orb_dis_r: forall l0 l1 l, 
  ((l ∪ (l0 ∪ l1))%domain == ((l ∪ l0) ∪ (l ∪ l1))%domain).
Proof.
  intros. apply dom_equiv_trans with (l1:= (l0 ∪ l1) ∪ l ). 
  - rewrite orb_domain_comm. apply dom_equiv_refl.
  - rewrite orb_domain_comm with (l':= l0). 
    rewrite orb_domain_comm with (l':= l1) (l:= l).
    apply dom_eq_orb_dis_l.
Qed.

(********************************************)

Lemma dom_subset_nil_iff: forall X, 
  is_domain_subset X [] = true <-> X == [].
Proof.
  split. { 
    induction X as [| b X IH]; intros.
    - simpl. apply dom_equiv_refl.
    - split; try assumption. simpl. reflexivity. }
    intros. destruct X. 
    - simpl. reflexivity.
    - destruct H. simpl in *. assumption.
Qed.

Lemma dom_subset_eq_compat_left: forall X Y Z, 
  X == Y -> is_domain_subset Z X = true -> is_domain_subset Z Y = true.
Proof.
  intros. 
  apply dom_subset_trans with (l1:= X); try assumption.
  destruct H. assumption.
Qed.

Lemma dom_subset_eq_compat_right: forall X Y Z, 
  X == Y -> is_domain_subset X Z = true -> is_domain_subset Y Z= true.
Proof.
  intros. 
  apply dom_subset_trans with (l1:= X); try assumption.
  destruct H. assumption.
Qed.

Lemma dom_subset_implies_orb_equiv X Y: 
    is_domain_subset X Y = true -> 
    (Y == orb_domain Y X)%domain.
Proof.
  intros H. generalize dependent Y. induction X; intros.
  - rewrite orb_domain_nil_r. apply dom_equiv_refl.
  - destruct Y as [|y Y']. 
    + simpl. apply dom_subset_nil_iff in H. apply dom_equiv_sym. assumption.
    + simpl in *. apply andb_true_iff in H. destruct H. 
      apply orb_true_iff in H. specialize (IHX Y' H0). destruct IHX.
      destruct H.
      * apply negb_true_iff in H. rewrite H. split; simpl. 
      ** rewrite orb_false_r. rewrite orb_negb_l. simpl. assumption.
      ** rewrite orb_false_r. rewrite orb_negb_l. simpl. assumption.
      * rewrite H. simpl. split; simpl; try assumption.
Qed.
(********************************************)
Lemma st_all_none_implies_all_false: forall s, 
  st_all_none s = true -> all_false (return_domain s) = true.
Proof.
  intros. induction s as [|v s' IH]; simpl.
  - split; simpl; try assumption. 
  - simpl in *. apply andb_true_iff in H. destruct H.
  apply IH in H0. apply andb_true_iff;split; try assumption. 
  rewrite negb_involutive. assumption.
Qed.

Lemma st_eq_implies_dom_equiv: forall s0 s1, 
  beq_state s0 s1 = true -> 
  return_domain s0 == return_domain s1.
Proof.
  intros. generalize dependent s1.
  induction s0 as [|v0 s0' IH]; intros; destruct s1 as [ | v1 s1']; simpl.
  - apply dom_equiv_refl.
  - simpl in *. apply andb_true_iff in H. destruct H.
  rewrite H. simpl. split; simpl; try reflexivity.
  apply st_all_none_implies_all_false; try assumption.
  - destruct v0; simpl in *; try discriminate. 
  split; simpl; try reflexivity.
  apply st_all_none_implies_all_false; assumption.
  - destruct v0; destruct v1; simpl in *; try discriminate. 
    * destruct (q ?= q0) eqn: H'; try discriminate.
  specialize (IH s1' H). destruct IH. split; simpl; assumption.
    * specialize (IH s1' H). destruct IH. split; simpl; try assumption.
Qed.



Lemma domain_orbT_contra: forall dom, 
  (dom ∪ [true])%domain = [] -> False.
Proof.
  intros. destruct dom.
  - simpl in *. discriminate.
  - simpl in *. rewrite orb_true_r in H. discriminate.
Qed.


Lemma orb_domain_elim_r: forall l l', 
  is_domain_subset l' l = true ->
  l == orb_domain l l'.
Proof. 
  intros. generalize dependent l'. induction l as [| b l IH]; intros.
  - simpl in *. apply dom_subset_nil_iff in H. apply dom_equiv_sym. assumption.
  - destruct l' as [|] . 
    + simpl in *. apply dom_equiv_refl.
    + simpl in *. apply andb_true_iff in H. destruct H. 
      apply IH in H0. destruct H0. split; simpl; try assumption.
      * apply andb_true_iff; split; try assumption. rewrite orb_assoc. rewrite orb_negb_l. simpl. reflexivity.
      * apply andb_true_iff; split; try assumption. rewrite negb_orb. 
      rewrite orb_andb_distrib_l. rewrite H. rewrite orb_negb_l. simpl. reflexivity.
Qed.

Open Scope domain_scope.
Lemma dom_cons_equiv_iff: forall X Y a b, 
  (a::X == b::Y) <-> (a = b /\ X == Y).
Proof.
  split. {
    intros. generalize dependent X. 
    induction Y as [| y Y' Hy]; intros; destruct X as [| x X'].
    - destruct H. simpl in *. split; try apply dom_equiv_refl.
      rewrite andb_true_r in H. rewrite andb_true_r in H0. 
      destruct a; destruct b; try reflexivity; try discriminate.
    - destruct H. simpl in *. rewrite andb_true_r in H0. 
      apply andb_true_iff in H. destruct H. 
      destruct a; destruct b; try reflexivity; try discriminate.
      + split; try reflexivity. apply all_false_iff_nil. simpl. assumption.
      + split; try reflexivity. apply all_false_iff_nil. simpl. assumption.
    - destruct H. simpl in *. apply andb_true_iff in H0. destruct H0.
      rewrite andb_true_r in H.  
      destruct a; destruct b; try reflexivity; try discriminate.
      + split; try reflexivity. apply dom_equiv_sym. apply all_false_iff_nil. simpl. assumption.
      + split; try reflexivity. apply dom_equiv_sym. apply all_false_iff_nil. simpl. assumption.
    - destruct H. simpl in *. apply andb_true_iff in H0. destruct H0.
      apply andb_true_iff in H. destruct H. apply andb_true_iff in H2. destruct H2.
      apply andb_true_iff in H1. destruct H1. 
      destruct a; destruct b; try reflexivity; try discriminate.
      + split; try reflexivity. split; simpl in *. 
        * rewrite H2. simpl. assumption.
        * rewrite H1. simpl. assumption.
      + split; try reflexivity. split; simpl in *. 
        * rewrite H2. simpl. assumption.
        * rewrite H1. simpl. assumption. }
  intros H. destruct H. generalize dependent Y. 
  induction X as [| x X' Hx]; destruct Y as [| y Y']; intros. 
  - rewrite H. apply dom_equiv_refl.
  - rewrite H. apply dom_equiv_sym in H0. apply all_false_iff_nil in H0.
    split; simpl in *. 
    + rewrite andb_true_r. apply orb_negb_l. 
    + rewrite orb_negb_l. rewrite H0. auto.
  - rewrite H. apply all_false_iff_nil in H0. 
    split; simpl in *.
    + rewrite orb_negb_l. rewrite H0. auto.
    + rewrite orb_negb_l. auto.
  - rewrite H. destruct H0. split; simpl in *. 
    + rewrite orb_negb_l. rewrite H0. auto.
    + rewrite orb_negb_l. rewrite H1. auto.
Qed.

Lemma res_dom_eq_iff_subset: forall s X, 
  is_domain_subset X  (return_domain s)= true <->
  (return_domain (res_st_to_X s X)) == X .
Proof.
  split. { 
    intros H. simpl. 
    generalize dependent X. induction s as [| v s' Hs]; intros.
    - simpl in *. apply dom_subset_nil_iff in H.
      apply dom_equiv_sym. assumption.
    - destruct v; destruct X as [| b X']; try destruct b; simpl in *; try apply dom_equiv_refl; try discriminate.
      + apply Hs in H. apply dom_cons_equiv_iff. split; try assumption. reflexivity.  
      + apply Hs in H. apply dom_cons_equiv_iff. split; try assumption. reflexivity.
      + apply Hs in H. apply dom_cons_equiv_iff. split; try assumption. reflexivity. }
  intros H. generalize dependent X. induction s as [| v s' Hs]; intros.
  - simpl in *. apply dom_subset_nil_iff. 
    apply dom_equiv_sym. assumption.
  - destruct X as [| b X']. 
    + simpl. reflexivity.
    + simpl in H. destruct v; destruct b; simpl in *; try assumption. 
      * apply Hs. apply dom_cons_equiv_iff in H. destruct H. assumption.
      * apply Hs. apply dom_cons_equiv_iff in H. destruct H. assumption.
      * apply dom_cons_equiv_iff in H. destruct H. discriminate.
      * apply Hs. apply dom_cons_equiv_iff in H. destruct H. assumption.
Qed.