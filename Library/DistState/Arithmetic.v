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
(*This file contains state size comparisons, and basic additive and multiplicative properties of state distributions.*)
Open Scope dstate_scope.
Lemma st_eq_nil_iff_all_none: forall s, beq_state s [] = st_all_none s. 
Proof.
  intro. induction s as [| v s IH]; try reflexivity. 
  destruct v; simpl; try reflexivity.
Qed.

Lemma st_eq_eq_all_none_compat: forall s0 s1, 
  beq_state s0 s1 = true -> st_all_none s0 = st_all_none s1.
Proof.
  intros s0 s1. intros H. generalize dependent s1.
  induction s0 as [| v0 s0 IH0]; intros s1 H; destruct s1 as [| v1 s1]; simpl in *; try reflexivity.
  - rewrite H. reflexivity.
  - destruct v0; assumption.
  - destruct v0; destruct v1; try discriminate.
    + destruct (Qcompare_spec q q0) as [Heq | Hlt | Hgt]; try discriminate H.
    rewrite andb_lazy_alt. destruct (is_none (Some q)) eqn: Hv0; try discriminate.
    unfold is_none in *. simpl. reflexivity.
    + unfold is_none in *. simpl. apply IH0; try assumption.
Qed.

Lemma default_eq_implies_st_eq: forall s0 s1, 
  st_all_none s0 = true -> st_all_none s1 = true -> beq_state s0 s1 = true.
Proof.
  intros s0 s1. intros H1 H2. generalize dependent s1.
  induction s0 as [| v0 s0 IH0]; intros s1 H2; destruct s1 as [| v1 s1]; simpl in *; 
    try assumption; destruct v0; try destruct v1; try discriminate.
  - unfold is_none in *. simpl in *. apply H1.
  - unfold is_none in *. simpl in *. apply IH0; try assumption.
Qed.
Lemma default_neq_implies_st_neq: forall s0 s1, 
  st_all_none s0 = true -> st_all_none s1 = false -> beq_state s0 s1 = false.
Proof.
  intros s0 s1. intros H1 H2. generalize dependent s1.
  induction s0 as [| v0 s0 IH0]; intros s1 H2; destruct s1 as [| v1 s1]; 
    simpl in *; try discriminate; try assumption; 
    destruct v0; try destruct v1; try discriminate; try reflexivity.
  unfold is_none in *. simpl in *. apply IH0; assumption.
Qed.
(*************************The property of state equality********************************************************************************************************)

Lemma state_eq_refl: forall st, beq_state st st = true. (*beq_st_refl*)
Proof.
  intro st. induction st as [| v s IH].
  - simpl. reflexivity.
  - simpl. destruct v; try assumption. destruct (q ?= q) eqn: H. 
    + apply IH.
    + apply Qlt_alt in H. exfalso. apply Qlt_irrefl in H. contradiction.
    + apply Qgt_alt in H. exfalso. apply Qlt_irrefl in H. contradiction.
Qed.

Lemma state_eq_sym: forall s0 s1, beq_state s0 s1 = beq_state s1 s0. (*beq_st_symm *)
Proof.
  intros s0 s1. generalize dependent s1.
  induction s0 as [| v0 s0 IH0]; intros s1; destruct s1 as [| v1 s1]; simpl; try reflexivity;
    try destruct v0; try destruct v1; try reflexivity.
  destruct (Qcompare_spec q q0) as [Heq | Hlt | Hgt].
  - rewrite Heq. destruct (q0 ?= q0) eqn: H1. 
    + apply IH0.
    + apply Qlt_alt in H1. exfalso. apply Qlt_irrefl in H1. contradiction.
    + apply Qgt_alt in H1. exfalso. apply Qlt_irrefl in H1. contradiction.
  - destruct (q0 ?= q) eqn: H1; try reflexivity.
    apply Qeq_alt in H1. rewrite H1 in Hlt. apply Qlt_irrefl in Hlt. contradiction.
  - destruct (q0 ?= q) eqn: H1; try reflexivity.
    apply Qeq_alt in H1. rewrite H1 in Hgt. apply Qlt_irrefl in Hgt. contradiction.
  - apply IH0.
Qed.

Lemma state_eq_trans: forall s0 s1 s2,  (*beq_st_trans *)
  beq_state s0 s1 = true -> beq_state s1 s2 = true -> 
  beq_state s0 s2 = true.
Proof.
  intros s0 s1 s2 H1 H2. 
  generalize dependent s1. generalize dependent s2. 
  induction s0 as [ | v0 l0 IH0].
  - intros s1 s2 H1 H2. destruct s1 as [| v1 l1]; destruct s2 as [| v2 l2]; 
      try simpl; try reflexivity.
    + simpl in H2. assumption.
    + simpl in *. apply andb_true_iff in H1 as [Hv1 Hl1]. 
      destruct v1; destruct v2 as [|]; simpl in*; try assumption; try discriminate.
      rewrite st_eq_eq_all_none_compat with (s1:= l2); try assumption. 
      rewrite state_eq_sym; try assumption.
  - intros s1 s2 H1 H2. destruct s1 as [| v1 l1]; destruct s2 as [| v2 l2]; simpl in *; try assumption.
    + destruct v0; destruct v2; simpl in *; try assumption; try discriminate. 
      rewrite st_eq_eq_all_none_compat with (s1:= l2); try assumption.
    + destruct v0; destruct v1; simpl in *; try assumption; try discriminate. 
      apply default_eq_implies_st_eq; try assumption.
    + destruct v0; destruct v1; destruct v2; simpl in *; try assumption; try discriminate.
      * destruct (q ?= q0) eqn: H'; destruct (q ?= q1) eqn: H0'; destruct (q1 ?= q0) eqn: H1'; 
        simpl in *; try discriminate.
      ** apply IH0 with (s1:= l2); try assumption.
      ** apply Qeq_alt in H0'. apply Qeq_alt in H1'. 
        apply Qlt_alt in H'. rewrite H0' in H'. rewrite H1' in H'.
        apply Qlt_irrefl in H'. contradiction.
      ** apply Qeq_alt in H0'. apply Qeq_alt in H1'. 
        apply Qgt_alt in H'. rewrite H0' in H'. rewrite H1' in H'.
        apply Qlt_irrefl in H'. contradiction.
      * apply IH0 with (s1:= l2); assumption.
Qed.

Lemma state_eq_compat_left: forall s0 s1 s, 
  beq_state s0 s1 = true -> beq_state s s0 = beq_state s s1.
Proof.
  intros s0 s1 s H. destruct (beq_state s s0) eqn: Htest.
  - symmetry.
    apply state_eq_trans with (s1:= s0); assumption.
  - generalize dependent s1. generalize dependent s0.
    induction s as [ | v l IH]; intros s0 H0 s1 H1.
    + simpl in *. rewrite <- H0. apply st_eq_eq_all_none_compat; try assumption.
    + destruct s1 as [| v1 l1]; destruct s0 as [| v0 l0]; try (discriminate).
      * simpl in *. rewrite H0. reflexivity.
      * simpl in *. 
      destruct v; destruct v0; simpl in *; try discriminate; try assumption.
      rewrite <- st_eq_nil_iff_all_none in H1.
      specialize (IH l0 H0 [] H1).  
      rewrite <- st_eq_nil_iff_all_none. assumption.
      * simpl in *. apply andb_true_iff in H1 as [Hv1 Hl1]. 
      destruct v; destruct v1; simpl in *; try discriminate; try assumption.
      apply IH with (s0:= []); simpl; try assumption.
      rewrite st_eq_nil_iff_all_none. assumption.
      * simpl in *. 
      destruct v; destruct v0; destruct v1; simpl in *; try discriminate; try assumption.
      ** destruct (q ?= q0) eqn: H0'; destruct (q0 ?= q1) eqn: H1'; try discriminate.
        -- apply Qeq_alt in H1'. rewrite <- H1'.   
        destruct (q ?= q0); try discriminate. 
        apply IH with (s0:= l0); try assumption.
        -- apply Qeq_alt in H1'. rewrite <- H1'.   
        destruct (q ?= q0); try discriminate. reflexivity.
        -- apply Qeq_alt in H1'. rewrite <- H1'.   
        destruct (q ?= q0); try discriminate. reflexivity.
      ** apply IH with (s0:= l0); try assumption. 
Qed.


(**********************The property of the state less than or greater than.******************************************************)
Lemma ble_state_nil_iff_all_none: forall s, ble_state s [] = st_all_none s.
Proof.
  intro. induction s as [| v s IH]; simpl; try reflexivity.
  destruct v; simpl in *; try assumption; try reflexivity.
Qed.

Lemma all_default_false_ble_state_nil_false: forall st,
  st_all_none st = false -> ble_state st [] = false.
Proof.
  intros. 
  induction st as [| v l]; intros; try (discriminate).
  simpl in *. destruct v; try assumption.
Qed.
Lemma all_default_ble_valid_state: forall s0 s1, 
  st_all_none s0 = true -> ble_state s0 s1 = true.
Proof.
  intros s0 s1 H. generalize dependent s1. 
  induction s0 as [ | v0 l0 IH]; intros s1; destruct s1 as [| v1 l1].
  - simpl in *. reflexivity.
  - simpl in *. reflexivity.
  - simpl in *. destruct v0; try assumption.
  - simpl in *. apply andb_true_iff in H. destruct H.
    destruct v0; destruct v1; simpl in *; try assumption; try discriminate.
    apply IH. assumption.
Qed.

Lemma st_nle_iff: forall s0 s1, 
  ble_state s1 s0 = false <-> 
  beq_state s0 s1 = false /\ ble_state s0 s1 = true.
Proof.
  intros s0 s1. split. 
  { 
    generalize dependent s1. induction s0 as [|v0 ns0 IH0].
    - intros s1 H. destruct s1 as [|v1 ns1]. 
      + simpl in *. discriminate. 
      + simpl in *. destruct v1; simpl in *. 
        * split; try assumption; try reflexivity.
        * split; try assumption; try reflexivity.
    - intros s1 H. destruct s1 as [|v1 ns1].
      + simpl in *. discriminate H.
      + destruct v0; destruct v1; simpl in *; try discriminate.
        * destruct (q0 ?= q) eqn: Heq10; try discriminate.
        ** apply Qeq_alt in Heq10. rewrite Heq10. 
        destruct (q ?= q) eqn: Heq01; try discriminate.
          -- apply IH0; try assumption.
          -- split; try reflexivity.
          -- apply Qgt_alt in Heq01. apply Qlt_irrefl in Heq01; contradiction.
        ** destruct (q ?= q0) eqn: Heq01; try discriminate.
          -- apply Qeq_alt in Heq01. rewrite Heq01 in Heq10. 
          apply Qgt_alt in Heq10. apply Qlt_irrefl in Heq10; contradiction.
          -- split; try reflexivity.
          -- apply Qgt_alt in Heq10. apply Qgt_alt in Heq01.
          assert (Hcontra: (q < q)%Q). { apply Qlt_trans with (y:= q0); eauto. } 
          apply Qlt_irrefl in Hcontra. contradiction.
        * split; try reflexivity.
        * apply IH0. assumption.
  }
  { 
    generalize dependent s1. induction s0 as [|v0 ns0 IH0].
    - intros s1 H. destruct H as [Hst Hcomp]. destruct s1 as [|v1 ns1]. 
      + simpl in *. discriminate.
      + destruct v1; simpl in *; try assumption.
    - intros s1 H. destruct H as [Hst Hcomp]. destruct s1 as [|v1 ns1]. 
      + simpl in *. rewrite Hst in Hcomp. discriminate Hcomp.
      + destruct v0; destruct v1; simpl in *; try discriminate; try reflexivity.
        -- simpl in *. destruct (q ?= q0) eqn: Heq01; try discriminate; try reflexivity. 
        * apply Qeq_alt in Heq01. rewrite Heq01. 
          destruct (q0 ?= q0) eqn: Heq11; try discriminate.
          ** apply Qeq_alt in Heq11. apply IH0; try assumption. split; try assumption.
          ** apply Qlt_alt in Heq11. apply Qlt_irrefl in Heq11; contradiction.
          ** apply Qgt_alt in Heq11. apply Qlt_irrefl in Heq11; contradiction.
        * destruct (q0 ?= q) eqn: Heq10; try discriminate. 
          ** apply Qeq_alt in Heq10. rewrite Heq10 in Heq01. 
          apply Qlt_alt in Heq01. apply Qlt_irrefl in Heq01; contradiction.
          ** apply Qlt_alt in Heq10. apply Qlt_alt in Heq01.
          assert (Hcontra: (q < q)%Q). { apply Qlt_trans with (y:= q0); eauto. }
          apply Qlt_irrefl in Hcontra; contradiction.
          ** reflexivity.
        -- apply IH0. split; assumption.
  }
Qed.

Lemma st_le_iff: forall s0 s1, 
  ble_state s0 s1 = true <-> 
  beq_state s0 s1 = true \/ ble_state s1 s0 = false.
Proof.
  intros s0 s1. split. 
  { 
    generalize dependent s1. induction s0 as [|v0 ns0 IH0].
    - intros s1 H. destruct s1 as [|v1 ns1]. 
      + simpl in *. left. reflexivity.
      + destruct v1; simpl in *; destruct (st_all_none ns1).
        * right. reflexivity.
        * right. reflexivity.
        * left. reflexivity.
        * right. reflexivity.
    - intros s1 H. destruct s1 as [|v1 ns1].
      + simpl in *. left. assumption.
      + destruct v0; destruct v1; simpl in *; try discriminate.
        * destruct (q ?= q0) eqn: Heq10; try discriminate. 
        -- destruct (q0 ?= q) eqn: Heq01; try discriminate.
        ** apply IH0; try assumption.
        ** apply Qeq_alt in Heq10. rewrite Heq10 in Heq01.  
          apply Qlt_alt in Heq01. apply Qlt_irrefl in Heq01; contradiction.
        ** apply Qeq_alt in Heq10. rewrite Heq10 in Heq01.
          apply Qgt_alt in Heq01. apply Qlt_irrefl in Heq01; contradiction.
        -- destruct (q0 ?= q) eqn: Heq01; try discriminate.
        ** apply Qeq_alt in Heq01. rewrite Heq01 in Heq10. 
        apply Qlt_alt in Heq10. apply Qlt_irrefl in Heq10; contradiction.
        ** apply Qlt_alt in Heq10. apply Qlt_alt in Heq01.
        assert (Hcontra: (q < q)%Q). { apply Qlt_trans with (y:= q0); eauto. } 
        apply Qlt_irrefl in Hcontra. contradiction.
        ** right. reflexivity.  
        * right. reflexivity.
        * apply IH0. assumption. }
  { 
    generalize dependent s1. induction s0 as [|v0 ns0 IH0].
    - intros s1 H. destruct H as [Hst| Hcomp]. 
      * destruct s1 as [|v1 ns1]. 
        + simpl in *. reflexivity.
        + simpl in *. reflexivity.
      * destruct s1 as [|v1 ns1]. 
        + simpl. reflexivity.
        + simpl in *. reflexivity.
    - intros s1 H. destruct H as [Hst | Hcomp]. 
    -- destruct s1 as [|v1 ns1]. 
      + simpl in *. assumption.
      + simpl in *. destruct v0; destruct v1; simpl in *; try discriminate.
      ++ destruct (q ?= q0) eqn: Heq01; try discriminate. apply IH0. left. assumption.
      ++ apply IH0. left. assumption.
    -- destruct s1 as [|v1 ns1]. 
      + simpl in *. discriminate.
      + destruct v0; destruct v1; simpl in *; try discriminate; try reflexivity. 
      ++ destruct (q ?= q0) eqn: Heq01; try discriminate; try reflexivity.
        * apply Qeq_alt in Heq01. rewrite Heq01 in Hcomp.  
          destruct (q0 ?= q0) eqn: Heq11; try discriminate.
          ** apply IH0; try assumption. right. assumption.
          ** apply Qgt_alt in Heq11. apply Qlt_irrefl in Heq11; contradiction.
        * destruct (q0 ?= q) eqn: Heq10; try discriminate. 
          ** apply Qeq_alt in Heq10. rewrite Heq10 in Heq01. 
          apply Qgt_alt in Heq01. apply Qlt_irrefl in Heq01; contradiction.
          ** apply Qgt_alt in Heq10. apply Qgt_alt in Heq01.
          assert (Hcontra: (q0 < q0)%Q). { apply Qlt_trans with (y:= q); eauto. }
          apply Qlt_irrefl in Hcontra; contradiction.
      ++ apply IH0. right. assumption.
  }
Qed.

Lemma st_le_default: forall s0 s1, 
  ble_state s0 s1 = true -> 
  st_all_none s1 = true -> 
  st_all_none s0 = true.
Proof.
  intros s0 s1 H H0. generalize dependent s1. 
  induction s0 as [ | v0 ns0 IH0]; intros s1 H H0; destruct s1 as [|v1 ns1].
  - simpl in *. assumption.
  - simpl in *. try assumption.
  - simpl in *. destruct v0; assumption.
  - destruct v0; destruct v1; simpl in *; try discriminate. 
  apply IH0 with (s1:= ns1); try assumption.
Qed.

Lemma st_le_trans: forall s0 s1 s2,
  ble_state s0 s1 = true -> 
  ble_state s1 s2 = true ->
  ble_state s0 s2 = true.
Proof.
  intros s0 s1 s2 H H0. 
  generalize dependent s1. generalize dependent s2.
  induction s0 as [| v l IH].
  - intros s1 s2 H H0. simpl in *. reflexivity.
  - intros s1 s2 H H0. 
    destruct s1 as [|v1 l1]; destruct s2 as [|v2 l2].
    + simpl in *. assumption.
    + destruct v; destruct v2; simpl in *; try discriminate.
      apply st_le_default with (s1:= l2); try assumption.
    + destruct v; destruct v1; simpl in *; try discriminate; try reflexivity.
      apply all_default_ble_valid_state; try assumption. 
    + destruct v; destruct v1; destruct v2; simpl in *; try discriminate; try reflexivity.
      * destruct (q ?= q1) eqn: Heq2; destruct (q1 ?= q0) eqn: Heq21; try discriminate.
      -- apply Qeq_alt in Heq2. rewrite Heq2.
        apply Qeq_alt in Heq21. rewrite Heq21. 
        destruct (q0 ?= q0) eqn: Heq11; try reflexivity. 
        ** apply Qeq_alt in Heq11. apply IH with (s1:= l2); try assumption. 
        ** apply Qgt_alt in Heq11. apply Qlt_irrefl in Heq11; contradiction.
      -- apply Qeq_alt in Heq2. apply Qlt_alt in Heq21. rewrite Heq2. 
        destruct (q1 ?= q0) eqn: Heq21'; try reflexivity.
        ** apply Qeq_alt in Heq21'. rewrite Heq21' in Heq21. 
        apply Qlt_irrefl in Heq21; contradiction.
        ** apply Qgt_alt in Heq21'. 
        assert (Hcontra: (q1 < q1)%Q). { apply Qlt_trans with (y:= q0); eauto. }
        apply Qlt_irrefl in Hcontra; contradiction.
      -- apply Qeq_alt in Heq21. apply Qgt_alt in Heq2. rewrite <- Heq21. 
        destruct (q ?= q1) eqn: Heq21'; try reflexivity.
        ** apply Qeq_alt in Heq21'. rewrite Heq21' in Heq2. apply Qgt_alt in Heq2.
        apply Qlt_irrefl in Heq2; contradiction.
        ** apply Qgt_alt in Heq21'. apply Qgt_alt in Heq2. 
        assert (Hcontra: (q < q)%Q). { apply Qlt_trans with (y:= q1); eauto. }
        apply Qlt_irrefl in Hcontra; contradiction.
      -- apply Qlt_alt in Heq2. apply Qlt_alt in Heq21. 
        destruct (q ?= q0) eqn: Heq21'; try reflexivity.
        ** apply Qeq_alt in Heq21'. rewrite Heq21' in Heq2. 
        assert (Hcontra: (q0 < q0)%Q). { apply Qlt_trans with (y:= q1); eauto. }
        apply Qlt_irrefl in Hcontra; contradiction.
        ** apply Qgt_alt in Heq21'.  
        assert (Hcontra: (q < q)%Q). { 
          apply Qlt_trans with (y:= q0); eauto. apply Qlt_trans with (y:= q1); eauto. }
        apply Qlt_irrefl in Hcontra; contradiction.
      * apply IH with (s1:= l2); try assumption.
Qed.

Lemma st_nle_trans: forall s0 s1 s2, 
  ble_state s0 s1 = false -> 
  ble_state s1 s2 = false ->
  ble_state s0 s2 = false.
Proof.
  intros s0 s1 s2 H H0. 
  generalize dependent s1. generalize dependent s2.
  induction s0 as [| v l IH].
  - intros s1 s2 H H0. simpl in *. discriminate H.
  - intros s1 s2 H H0. 
    destruct s1 as [|v1 l1]; destruct s2 as [|v2 l2]; try discriminate.
    + destruct v; destruct v2; simpl in *; try discriminate; try reflexivity.
      rewrite <- ble_state_nil_iff_all_none in H0. 
      specialize (IH [] l2 H H0). 
      rewrite <- ble_state_nil_iff_all_none. assumption.
    + destruct v; destruct v1; destruct v2; simpl in *; try discriminate; try reflexivity.
      * destruct (q ?= q1) eqn: Heq2; destruct (q1 ?= q0) eqn: Heq21; try discriminate; try reflexivity.
      -- apply Qeq_alt in Heq2. rewrite Heq2.
        apply Qeq_alt in Heq21. rewrite Heq21.
        destruct (q0 ?= q0) eqn: Heq11; try discriminate. 
        ** apply Qeq_alt in Heq11. apply IH with (s1:= l2); try assumption. 
        ** apply Qlt_alt in Heq11. apply Qlt_irrefl in Heq11; contradiction.
        ** apply Qgt_alt in Heq11. apply Qlt_irrefl in Heq11; contradiction.
      -- apply Qeq_alt in Heq2. apply Qgt_alt in Heq21. rewrite Heq2. 
        destruct (q1 ?= q0) eqn: Heq21'; try discriminate.
        ** apply Qeq_alt in Heq21'. rewrite Heq21' in Heq21. apply Qlt_irrefl in Heq21; contradiction.
        ** apply Qlt_alt in Heq21'. 
        assert (Hcontra: (q1 < q1)%Q). { apply Qlt_trans with (y:= q0); eauto. }
        apply Qlt_irrefl in Hcontra; contradiction.
        ** reflexivity.
      -- apply Qeq_alt in Heq21. apply Qgt_alt in Heq2. rewrite <- Heq21. 
        destruct (q ?= q1) eqn: Heq21'; try discriminate.
        ** apply Qeq_alt in Heq21'. rewrite Heq21' in Heq2. apply Qlt_irrefl in Heq2; contradiction.
        ** apply Qlt_alt in Heq21'. 
        assert (Hcontra: (q < q)%Q). { apply Qlt_trans with (y:= q1); eauto. }
        apply Qlt_irrefl in Hcontra; contradiction.
        ** reflexivity.
      -- apply Qgt_alt in Heq2. apply Qgt_alt in Heq21. 
        destruct (q ?= q0) eqn: Heq21'; try discriminate.
        ** apply Qeq_alt in Heq21'. rewrite Heq21' in Heq2. 
        assert (Hcontra: (q0 < q0)%Q). { apply Qlt_trans with (y:= q1); eauto. }
        apply Qlt_irrefl in Hcontra; contradiction.
        ** apply Qlt_alt in Heq21'.  
        assert (Hcontra: (q < q)%Q). { 
          apply Qlt_trans with (y:= q0); eauto. apply Qlt_trans with (y:= q1); eauto. }
        apply Qlt_irrefl in Hcontra; contradiction.
        ** reflexivity.
      * apply IH with (s1:= l2); try assumption.
Qed.

Lemma st_eq_ble_compat_left: forall s0 s1 s, 
  beq_state s0 s1 = true ->
  ble_state s s0 = ble_state s s1.
Proof.
  intros s0 s1 s Heq. generalize dependent s0. generalize dependent s1.
  induction s as [ | v l IH].
  - intros s1 s0 H. simpl in *. reflexivity.
  - intros s1 s0 H. destruct s1 as [| v1 l1]; destruct s0 as [| v0 l0].
    + simpl in *. reflexivity.
    + destruct v; destruct v0; simpl in *; try discriminate; try reflexivity. 
      specialize (IH [] l0). 
      repeat rewrite st_eq_nil_iff_all_none in IH.
      specialize (IH H). rewrite IH. simpl.
      apply ble_state_nil_iff_all_none.
    + destruct v; destruct v1; simpl in *; try discriminate; try reflexivity. 
      specialize (IH l1 []).
      repeat rewrite st_eq_nil_iff_all_none in IH.
      specialize (IH H). 
      rewrite ble_state_nil_iff_all_none in IH. apply IH.
    + destruct v; destruct v0; destruct v1; simpl in *; try discriminate; try reflexivity. 
    -- destruct (q ?= q0) eqn: Heq0; destruct (q ?= q1) eqn: Heq1; try reflexivity; try discriminate.
      * apply Qeq_alt in Heq0. apply Qeq_alt in Heq1. 
      rewrite <- Heq0 in H. rewrite <- Heq1 in H. 
      destruct (q ?= q) eqn: Heq; try discriminate.
      apply IH; try assumption.
      * apply Qeq_alt in Heq0. apply Qlt_alt in Heq1. 
      rewrite <- Heq0 in H. 
      destruct (q ?= q1) eqn: Heq; try discriminate.
      apply Qeq_alt in Heq. rewrite Heq in Heq1.
      apply Qlt_irrefl in Heq1; contradiction.
      * apply Qeq_alt in Heq0. apply Qgt_alt in Heq1. 
      rewrite <- Heq0 in H. 
      destruct (q ?= q1) eqn: Heq; try discriminate.
      apply Qeq_alt in Heq. rewrite Heq in Heq1.
      apply Qlt_irrefl in Heq1; contradiction.
      * apply Qeq_alt in Heq1. apply Qlt_alt in Heq0. 
      rewrite <- Heq1 in H. 
      destruct (q0 ?= q) eqn: Heq; try discriminate.
      apply Qeq_alt in Heq. rewrite Heq in Heq0.
      apply Qlt_irrefl in Heq0; contradiction.
      * apply Qgt_alt in Heq1. apply Qlt_alt in Heq0. 
      destruct (q0 ?= q1) eqn: Heq; try discriminate.
      apply Qeq_alt in Heq. rewrite Heq in Heq0.
      assert (Hcontra: (q1<q1)%Q). { apply Qlt_trans with (y:= q); eauto. }
      apply Qlt_irrefl in Hcontra; contradiction.
      * apply Qeq_alt in Heq1. apply Qgt_alt in Heq0. 
      rewrite <- Heq1 in H. 
      destruct (q0 ?= q) eqn: Heq; try discriminate.
      apply Qeq_alt in Heq. rewrite Heq in Heq0.
      apply Qlt_irrefl in Heq0; contradiction.
      * destruct (q0 ?= q1) eqn: Heq; try discriminate. 
      apply Qeq_alt in Heq. 
      apply Qlt_alt in Heq1. apply Qgt_alt in Heq0.
      rewrite Heq in Heq0. 
      assert (Hcontra: (q1 < q1)%Q). { apply Qlt_trans with (y:= q); eauto. }
      apply Qlt_irrefl in Hcontra; contradiction.
    -- apply IH. try assumption.
Qed.

Lemma st_eq_ble_compat_right: forall s0 s1 s, 
  beq_state s0 s1 = true ->
  ble_state s0 s = ble_state s1 s.
Proof. 
  intros s0 s1 s H. generalize dependent s. generalize dependent s1.
  induction s0 as [ | v0 l0 IH]; intros s1 H; destruct s1 as [| v1 l1]; intros s .
  - simpl in *. reflexivity. 
  - destruct v1; simpl in *; try discriminate. 
    destruct s as [| v l]; try assumption.
    + rewrite H. reflexivity.
    + destruct v; simpl in *; try reflexivity.
      rewrite all_default_ble_valid_state; try reflexivity; try assumption.
  - destruct v0; simpl in *; try discriminate. 
    destruct s as [| v l]; try assumption. 
    destruct v; simpl in *; try reflexivity.
    rewrite all_default_ble_valid_state; try reflexivity; try assumption.
  - destruct s as [| v l]; destruct v0; destruct v1; try destruct v; simpl in *; try discriminate; try reflexivity.
    + specialize (IH l1 H [] ). repeat rewrite ble_state_nil_iff_all_none in IH. assumption.
    + destruct (q ?= q0) eqn: Heq; try discriminate. 
      apply Qeq_alt in Heq. rewrite Heq. 
      destruct (q0 ?= q1); try reflexivity.
      apply IH; try assumption.
    + apply IH; try assumption.
Qed.



(*Reflexive, symmetric, and transitive properties of equiv distribution*********************************************************************)
(*******************************************************************)
Lemma dst_equiv_refl : forall mu, (mu == mu).
Proof. 
  unfold dst_equiv. 
  intros. split; try reflexivity.
Qed.
Lemma dst_equiv_sym : forall mu0 mu1, mu0 == mu1 -> mu1 == mu0.
Proof.
 unfold dst_equiv. intros. rewrite H. reflexivity. 
Qed.
Lemma dst_equiv_trans : forall mu0 mu1 mu2, 
  mu0 == mu1 -> mu1 == mu2 -> mu0 == mu2. 
Proof.
  unfold dst_equiv in *. intros. 
  rewrite H. rewrite H0. reflexivity.
Qed.

(*************************Properties of get_prob*******************************************************************************************)
Lemma st_eq_get_prob_compat: forall mu s0 s1, 
  beq_state s0 s1 = true ->
  (get_prob_in_dstate mu s0 = get_prob_in_dstate mu s1).
Proof.
  intros mu s0 s1 H.
  induction mu as [|(s,p) mu' Hmu].
  - simpl. reflexivity.
  - simpl. destruct (beq_state s0 s) eqn: Hst0.
    + assert (Hst1: beq_state s1 s = true). { 
        rewrite state_eq_sym in H. apply state_eq_trans with s0; assumption. }
    rewrite Hst1. rewrite Hmu. reflexivity.
    + assert (Hst1: beq_state s1 s = false). { 
        rewrite state_eq_sym. rewrite state_eq_compat_left with (s1:= s0). 
        - rewrite state_eq_sym in Hst0. assumption. 
        - rewrite state_eq_sym in H. assumption. }
    simpl. rewrite Hst1. rewrite Hmu. reflexivity.
Qed.

Lemma get_prob_decom: 
  forall mu mu' s, 
    (get_prob_in_dstate (mu + mu')%dist_state s) = 
    ((get_prob_in_dstate mu s) + (get_prob_in_dstate mu' s))%R.
Proof.
  intros mu mu' s.
  induction mu as [|sq mu1 H].
  - simpl. rewrite Rplus_0_l. reflexivity.
  - destruct sq as [s0 p0]. simpl. destruct (beq_state s s0) eqn:Heq. 
    + rewrite H. rewrite Rplus_assoc. reflexivity.
    + apply H.
Qed.

Lemma get_prob_coef_mult: forall mu s p, 
  get_prob_in_dstate ((p * mu)%dist_state) s = (p * (get_prob_in_dstate mu s))%R.
Proof.
  intros mu s p.
  induction mu as [|(s1,q1) mu1 H].
  - simpl. field.
  - simpl. destruct (Req_EM_T p 0) eqn:Hp.
    + simpl. rewrite e. field.
    + simpl. destruct (beq_state s s1) eqn: Heq_st.
      * rewrite Rmult_plus_distr_l. f_equal. apply H.
      * simpl. apply H.
Qed.

(*****************************Properties of add_mu***************************************************************************************)
Lemma dst_cons_eq_add : forall (mu:dist_state) s p, (s,p) :: mu = [(s,p)] + mu. 
Proof.
  intros. reflexivity.
Qed.

Lemma dst_add_0_l: forall mu :dist_state, [] + mu = mu.
Proof.
  intro. simpl. reflexivity.
Qed.
Lemma dst_add_0_r: forall mu :dist_state, mu + [] = mu.
Proof.
  intro mu. induction mu as [|sq mu' H].
  - simpl. reflexivity.
  - simpl. rewrite H. reflexivity.
Qed.

Lemma dst_add_assoc_eq : forall mu0 mu1 mu2: dist_state, mu0 + (mu1 + mu2) = (mu0 + mu1) + mu2.
Proof.
  intros.
  induction mu0 as [| [s p] x' IH]; simpl; intros.
  - reflexivity.
  - f_equal. apply IH.
Qed.

Lemma dst_add_comm: forall mu0 mu1, mu0 + mu1 == mu1 + mu0.
Proof.
  intros. generalize dependent mu1.
  induction mu0 as [| [s p] x' IH].
  - intros. simpl. rewrite dst_add_0_r. apply dst_equiv_refl.
  - intros. unfold dst_equiv. intros. simpl. 
    destruct (beq_state s0 s) eqn:Heq_st.
      + rewrite get_prob_decom; rewrite get_prob_decom. 
      rewrite <- Rplus_assoc. rewrite Rplus_comm. 
      f_equal. simpl. rewrite Heq_st. reflexivity.
      + rewrite get_prob_decom. rewrite get_prob_decom. 
      simpl. rewrite Heq_st. rewrite Rplus_comm.
      reflexivity.
Qed.

(************************Properties of mu_mult***************************************************************)  
Lemma dst_mult_0_l : forall (mu: dist_state), (0 * mu) = [].
Proof.
  intros mu. induction mu as [|sq mu' H].
  - simpl. reflexivity.
  - destruct sq. simpl. destruct (Req_EM_T 0 0) eqn: H0.
    + reflexivity. + contradiction.
Qed. 

Lemma dst_mult_1_l : forall (mu: dist_state), (1 * mu) = mu.
Proof.
  intros mu. induction mu as [|sq mu' H].
  - simpl. reflexivity.
  - destruct sq. simpl. destruct (Req_EM_T 1 0) eqn: H0.
  + exfalso. apply R1_neq_R0. assumption.
  + rewrite Rmult_1_l. f_equal. assumption.
Qed.

Lemma dst_mult_plus_distr_r_eq: forall (mu0 mu1: dist_state) p, 
  p * (mu0 + mu1) = (p * mu0) + (p * mu1).
Proof.
  intros. generalize dependent mu1. 
  induction mu0 as [|(s,q) mu0' IH].
  - simpl. intros. reflexivity.
  - intros. simpl. destruct (Req_EM_T p 0) eqn: Hp.
    + rewrite e. rewrite dst_mult_0_l. simpl. reflexivity.
    + simpl. f_equal. apply IH.
Qed.

Lemma dst_cons_mult_distr: forall (mu : dist_state) s1 p1 (p:R),
  p <> 0%R ->
  (p * ((s1, p1) :: mu)) = ((s1, (p * p1)%R) :: p * mu).
Proof.
  intros mu s1 p1 p H. simpl. destruct (Req_EM_T p 0).
  + rewrite e in H. contradiction.
  + reflexivity.
Qed.

Lemma dst_mult_assoc_eq: forall (p0 p1: R) (mu: dist_state), 
  p0 * (p1 * mu) = ((p0 * p1)%R) * mu.
Proof.
  intros p0 p1 mu.
  induction mu as [|(s,q) mu' H].
  - simpl. reflexivity.
  - rewrite dst_cons_eq_add. repeat rewrite dst_mult_plus_distr_r_eq. 
  simpl. destruct (Req_EM_T p1 0) eqn: Hp1; destruct (Req_EM_T p0 0) eqn: Hp0.
    + rewrite e. rewrite e0. simpl. destruct (Req_EM_T (0 * 0) 0) eqn: H0.
      * simpl. rewrite e1. repeat rewrite dst_mult_0_l. reflexivity.  
      * unfold not in n. exfalso. apply n. rewrite Rmult_0_l. reflexivity.
    + rewrite e. rewrite dst_mult_0_l. destruct (Req_EM_T (p0 * 0) 0) eqn: H0.
      * simpl. rewrite e0. rewrite dst_mult_0_l. reflexivity.
      * unfold not in n0. exfalso. apply n0. rewrite Rmult_0_r. reflexivity.
    + simpl. rewrite e. repeat rewrite Rmult_0_l. repeat rewrite dst_mult_0_l. reflexivity.
    + simpl. rewrite Hp0. destruct (Req_EM_T (p0 * p1) 0) eqn: H01.
      * assert (Hcontra: (p0 * p1)%R <> 0%R). { 
          apply Rmult_integral_contrapositive_currified; assumption. }
        rewrite e in Hcontra. contradiction.
      * rewrite H. f_equal. rewrite Rmult_assoc. reflexivity.
Qed.

Lemma dst_mult_comm_eq: 
  forall p0 p1 (mu: dist_state), (p0 * (p1 * mu)) = (p1 * (p0 * mu)).
Proof.
  intros p0 p1 mu.
  induction mu as [| [s q] mu' IH].
  - simpl. reflexivity.
  - rewrite dst_cons_eq_add. repeat rewrite dst_mult_plus_distr_r_eq. 
    rewrite IH. f_equal. simpl. 
    destruct (Req_EM_T p1 0) eqn: Hp1; destruct (Req_EM_T p0 0) eqn: Hp0.
    + simpl. reflexivity.
    + simpl. rewrite Hp1. reflexivity.
    + simpl. rewrite Hp0. reflexivity.
    + simpl. rewrite Hp1. rewrite Hp0.
    repeat rewrite <- Rmult_assoc.
    rewrite Rmult_comm with (r1:= p0). reflexivity.
Qed.


Lemma dst_mult_preserves_equiv: 
  forall p mu0 mu1, mu0 == mu1 -> p * mu0 == p * mu1.
Proof. 
  intros p mu1 mu2 H.
  unfold dst_equiv in *. intros.
  specialize (H s).
  rewrite get_prob_coef_mult.
  rewrite get_prob_coef_mult.
  rewrite H. reflexivity.
Qed.

Lemma dst_add_inj_r: forall mu0 mu1 mu, 
  mu0 + mu == mu1 + mu <-> mu0 == mu1.
Proof.
  intros mu0 mu1 mu. split.
  { 
    generalize dependent mu0. generalize dependent mu1.
    induction mu as [|(s,p) mu' IH].
    - intros. repeat rewrite dst_add_0_r in H. assumption.
    - intros. apply IH. unfold dst_equiv in *. 
      intros s0.          
      repeat rewrite get_prob_decom. f_equal.
      specialize (H s0).
      repeat rewrite get_prob_decom in H.
      apply Rplus_eq_reg_r in H. assumption.
  } 
  { 
    generalize dependent mu0. generalize dependent mu1.
    induction mu as [|(s,p) mu' IH].
    - intros. repeat rewrite dst_add_0_r. assumption.
    - intros. unfold dst_equiv. intros. 
      rewrite get_prob_decom with (mu:= mu0) (mu':= ((s, p) :: mu')).
      rewrite get_prob_decom with (mu:= mu1) (mu':= ((s, p) :: mu')).
      rewrite get_prob_decom with (mu:= [(s, p)]) (mu':= mu').
      apply Rplus_eq_compat_r. apply H. 
  }
Qed.

Lemma dst_add_inj_l: forall mu0 mu1 mu, 
  mu + mu0 == mu + mu1 <-> mu0 == mu1.
Proof.
  intros mu0 mu1 mu. split. { 
    generalize dependent mu0. generalize dependent mu1.
    induction mu as [|(s,p) mu' IH].
    - intros. repeat rewrite dst_add_0_l in H. assumption.
    - intros. apply IH.
      unfold dst_equiv. unfold dst_equiv in H. intros. 
      repeat rewrite get_prob_decom. f_equal.
      specialize (H s0).
      repeat rewrite get_prob_decom in H.
      apply Rplus_eq_reg_l in H. apply H. }
   
    generalize dependent mu0. generalize dependent mu1.
    induction mu as [|(s,p) mu' IH].
    - intros. simpl. apply H.
    - intros. simpl. unfold dst_equiv in H. 
      unfold dst_equiv. intros. 
      rewrite get_prob_decom with (mu:= [(s, p)]) (mu':= (mu' + mu0)).
      rewrite get_prob_decom with (mu:= [(s, p)]) (mu':= (mu' + mu1)).
      f_equal. apply IH; try assumption. 
Qed.


Lemma dst_add_preserves_equiv: 
  forall mu0 mu1 mu2 mu3,
    mu0 == mu1 -> mu2 == mu3 -> 
    mu0 + mu2 == mu1 + mu3.
Proof.
  unfold dst_equiv in *. intros.
  specialize (H s). specialize (H0 s).
  repeat rewrite get_prob_decom.
  rewrite H; try assumption. 
  rewrite H0; try assumption. reflexivity. 
Qed.

Lemma dst_add_shuffle: 
  forall mu0 mu1 mu2 mu3,
    (mu0 + mu1)+ (mu2 + mu3) == (mu0 + mu2) + (mu1 + mu3).
Proof.
  intros.
  apply dst_equiv_trans with (mu1:= mu0 + (mu1 + (mu2 + mu3))). {
    apply dst_equiv_sym. rewrite dst_add_assoc_eq. apply dst_equiv_refl. }
  apply dst_equiv_trans with (mu1:= mu0 + (mu2 + (mu1 + mu3))). { 
    apply dst_add_inj_l. apply dst_equiv_trans with (mu1:= (mu1 + mu2)+mu3). 
    - rewrite dst_add_assoc_eq. apply dst_equiv_refl.
    - apply dst_equiv_trans with (mu1:= mu2 + mu1 + mu3). 
      + apply dst_add_inj_r. apply dst_add_comm. 
      + apply dst_equiv_sym. rewrite dst_add_assoc_eq. apply dst_equiv_refl. }
    rewrite dst_add_assoc_eq. apply dst_equiv_refl.
Qed.

(************************************************************)
Lemma dst_equiv_nil_prob0: forall s, 
  [(s,0%R)] == [].
Proof.
  intros s. unfold dst_equiv. intros. simpl. 
  destruct (beq_state s0 s); try reflexivity.
  apply Rplus_0_l.
Qed.

Lemma Peq_one_st: forall s0 s1 p0 p1, 
  beq_state s0 s1 = true /\ (p0 = p1)%R -> 
  [(s0, p0)] == [(s1, p1)]. 
Proof.
  intros s0 s1 p0 p1 H. destruct H as [Hst Hp]. generalize dependent s1.
  induction s0 as [|v0 nv0 IH0]; intros s1; destruct s1 as [|v1 nv1]; intros.
  - unfold dst_equiv. simpl. intros. 
    destruct (beq_state s []); try reflexivity. 
    apply Rplus_eq_compat_r. assumption. 
  - simpl in Hst. apply andb_true_iff in Hst. destruct Hst. 
    unfold dst_equiv. intros. simpl. destruct (beq_state s []) eqn: Hs. 
    + rewrite st_eq_nil_iff_all_none in Hs. destruct s as [|v nv].
      * simpl in *. rewrite H. rewrite H0. simpl. rewrite Hp. reflexivity.
      * simpl in *. apply andb_true_iff in Hs. destruct Hs.
        destruct v; destruct v1; simpl in *; try discriminate.
        rewrite default_eq_implies_st_eq; try assumption. 
        rewrite Hp. reflexivity.
    + destruct s as [|v nv].
      * simpl in *. discriminate.
      * simpl in *. 
        destruct v; destruct v1; simpl in *; try discriminate; try reflexivity.
        rewrite state_eq_sym.
        rewrite default_neq_implies_st_neq; try assumption.
        reflexivity.
  - unfold dst_equiv. intros. 
    simpl. apply state_eq_compat_left with (s:= s) in Hst.
    rewrite Hst.  
    destruct (beq_state s []) eqn: Hs; try reflexivity.
    rewrite Hp. reflexivity.
  - unfold dst_equiv. intros. destruct s as [|v nv]. 
    + destruct v0; destruct v1; simpl in *; try reflexivity; try discriminate.  
      apply st_eq_eq_all_none_compat in Hst. rewrite Hst.
      rewrite Hp. reflexivity.
    + destruct v0; destruct v1; destruct v; simpl in *; try discriminate; try reflexivity.
      * destruct (q ?= q0) eqn: H'; try discriminate. apply Qeq_alt in H'. rewrite H'. 
        destruct (q1 ?= q0) eqn: H0; try reflexivity.
        apply state_eq_compat_left with (s:= nv) in Hst.
        rewrite Hst. destruct (beq_state nv nv1); try reflexivity.
        rewrite Hp. reflexivity.
      * apply state_eq_compat_left with (s:= nv) in Hst.
        rewrite Hst. destruct (beq_state nv nv1); try reflexivity.
        rewrite Hp. reflexivity.
Qed.

Lemma dst_eq_implies_equiv: forall mu0 mu1, 
  beq_dst mu0 mu1 = true -> mu0 == mu1.
Proof.
  intros. generalize dependent mu1.
  induction mu0 as [|(s0,p0) mu0' IH]; destruct mu1 as [|(s1,p1) mu1']; intros.
  - apply dst_equiv_refl.
  - simpl in H. discriminate.
  - simpl in H. discriminate.
  - simpl in H. apply andb_true_iff in H. destruct H. 
  apply andb_true_iff in H. destruct H.
  specialize (IH mu1' H0).
  rewrite dst_cons_eq_add. rewrite dst_cons_eq_add with (mu:= mu1'). 
  apply dst_add_preserves_equiv; try assumption.
  apply Peq_one_st. split; try assumption. 
  apply Req_true_implies_equal. assumption.
Qed.