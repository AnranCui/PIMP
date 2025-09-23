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
Require Import Library.PIMP.Syntax.

Open Scope list_scope.
Open Scope dstate_scope.


Fixpoint get (i:nat) (s:local_st) : Q :=  (*Use when updating*)
  match i, s with
  | 0%nat, Some v :: _  => v
  | S i' , _ :: s' => get i' s'
  | _    , _       => default_Q
  end.
Fixpoint update (s:local_st) (i:nat) (v:Q) : local_st :=
  match i, s with
  | 0%nat, a :: s' => Some v :: s'
  | 0%nat, []      => Some v :: []
  | S i' , a :: s' => a :: (update s' i' v)
  | S i' , []      => None :: (update [] i' v)    
  end.

(********aexp*)
Fixpoint evalA_st (a: aexp) (s: local_st) : Q := (** * Eval aexp under partial_state *)
  match a with
  | Aco n => n 
  | Ava x => get x s  
  | Apl a1 a2 => (evalA_st a1 s + evalA_st a2 s)
  | Amu a1 a2 => (evalA_st a1 s * evalA_st a2 s)
  | Asu a1 a2 => (evalA_st a1 s - evalA_st a2 s)
  end.
(***************bexp******************)
Fixpoint evalB_st (b : bexp) (s : local_st) : bool := (** * Eval bexp under partial_state *)
  match b with
  | Btrue => true
  | Bfalse => false
  | Band e1 e2 => andb (evalB_st e1 s) (evalB_st e2 s)
  | Bnot b => negb (evalB_st b s)
  | Beq a1 a2 => Qeq_bool (evalA_st a1 s) (evalA_st a2 s)
  | Ble a1 a2 => Qle_bool (evalA_st a1 s) (evalA_st a2 s) 
end.

(** Properties of [update].******************************************************************** *)

Theorem get_update_eq : forall n x st, get x (update st x n) = n. 
Proof. 
  intros n x.
  induction x as [| x' IH]; intros st.
  - destruct st as [| a s']; simpl; reflexivity.
  - destruct st as [| a s']; simpl; rewrite IH; reflexivity.
Qed.

Lemma get_default_nil: forall x, get x [] = default_Q. 
Proof. induction x; simpl; reflexivity. Qed.

Theorem update_neq : forall x1 x0 n st,
  Nat.eqb x0 x1 = false -> get x0 (update st x1 n) = get x0 st .
Proof.
  induction x1 as [| x1' IH1].
  - intros. destruct x0 as [| x0'].
    + simpl in H. discriminate H.
    + destruct st as [|a st']; simpl. 
      * induction x0'; simpl; reflexivity.
      * reflexivity.
  - intros. destruct x0 as [| x0'].
    + destruct st as [| a st']; simpl; reflexivity.
    + simpl in H. destruct st as [| a st'].
      * simpl. 
      assert (H'': get x0' [] = default_Q). { induction x0'; simpl; reflexivity. }
      rewrite <- H''. apply IH1. assumption.
      * simpl. apply IH1. assumption.
Qed.

Theorem conti_update: forall (v r : Q) (st : local_st) (x: nat), 
  (update (update st x v) x r) = update st x r. 
Proof.
  intros v r st x.
  generalize dependent x.
  induction st as [| hd tl IH]; intros x.
  - induction x as [|SX HSX].
    + simpl. reflexivity. 
    + simpl. rewrite <- HSX. reflexivity. 
  - induction x as [|SX HSX].
    + simpl. reflexivity. 
    + simpl. f_equal. apply IH.
Qed.
Lemma update_st_neq_nil: forall s x n, s <> [] -> update s n x <> [].
Proof.
  intros. generalize dependent x. generalize dependent n.
  induction s; intros; try contradiction. 
  destruct n.
  - simpl. unfold not. intros. inversion H0.
  - simpl. unfold not. intros. inversion H0.
Qed.

Lemma all_default_get_default: forall st i,
  st_all_none st = true -> (get i st == default_Q)%Q.
Proof.
  intros. generalize dependent i. 
  induction st as [| v l]; intros; destruct i; try destruct v; try (discriminate).
  - simpl in *. reflexivity.
  - simpl in *. reflexivity.
  - simpl in *. reflexivity.
  - simpl in *. apply IHl; try assumption.
Qed.
Lemma st_eq_implies_get_eq: forall st0 st1 x,
  (st0 == st1)%state -> (get x st0 == get x st1)%Q.
Proof.
  intros. generalize dependent st1. generalize dependent st0. 
  induction x as [| x' IH]; intros.
  - destruct st1 as [| v1 l1]; destruct st0 as [| v0 l0]; try destruct v0; try destruct v1;
      simpl in *; try (discriminate H); try reflexivity.
    destruct (q ?= q0) eqn: H0'; try discriminate.
      apply Qeq_alt in H0'. rewrite H0'. reflexivity.
  - destruct st1 as [| v1 l1]; destruct st0 as [| v0 l0]; try destruct v0; try destruct v1;
      simpl in *; try (discriminate H); try reflexivity.
    + apply all_default_get_default; try assumption.
    + symmetry. apply all_default_get_default; try assumption.
    + destruct (q ?= q0); try discriminate. apply IH. assumption.
    + apply IH. assumption.
Qed.

Theorem st_eq_implies_evalA: forall st1 st2 a,
  (st1 == st2)%state -> 
  (evalA_st a st1 == evalA_st a st2)%Q.
Proof.
  intros. induction a as [ | | | | ]; simpl in *.
  - reflexivity.
  - apply st_eq_implies_get_eq. apply H.
  - rewrite <- IHa1. rewrite <- IHa2. apply Qeq_refl.  
  - rewrite <- IHa1. rewrite <- IHa2.   apply Qeq_refl.  
  - rewrite <- IHa1. rewrite <- IHa2.  apply Qeq_refl.  
Qed.
Theorem st_eq_implies_evalB: forall st1 st2 b,
  (st1 == st2)%state -> 
  (evalB_st b st1 = evalB_st b st2).
Proof.
  intros. induction b as [ | | | | |]; simpl in *; try reflexivity.
  - rewrite IHb1. rewrite IHb2. reflexivity.
  - rewrite IHb. reflexivity.
  - assert (H1: ((evalA_st a st1) == (evalA_st a st2))%Q). { 
      apply st_eq_implies_evalA; assumption. }
    assert (H2: ((evalA_st a0 st1) == (evalA_st a0 st2))%Q). { 
      apply st_eq_implies_evalA; assumption. }
    rewrite H1. rewrite H2. reflexivity.
  - assert (H1: ((evalA_st a st1) == (evalA_st a st2))%Q). { 
      apply st_eq_implies_evalA; assumption. }
    assert (H2: ((evalA_st a0 st1) == (evalA_st a0 st2))%Q). { 
      apply st_eq_implies_evalA; assumption. }
    rewrite H1. rewrite H2. reflexivity.
Qed.
Theorem st_eq_implies_update_eq : forall st1 st2 x n1 n2, 
  (st1 == st2)%state -> (n1 == n2)%Q ->
  beq_state (update st1 x n1) (update st2 x n2) = true. 
Proof.
  intros. 
  generalize dependent st2. generalize dependent st1. 
  induction x as [|x' IHx]; intros.
  - destruct st1 as [ |v1 l1]; destruct st2 as [| v2 l2]; 
      try destruct v1; try destruct v2; simpl in *; try (discriminate).
    + simpl in *. rewrite H0. destruct (n2?=n2) eqn: H'; try reflexivity.
      * apply Qlt_alt in H'. apply Qlt_irrefl in H'. contradiction.
      * apply Qgt_alt in H'. apply Qlt_irrefl in H'. contradiction.
    + simpl in *. rewrite H0. destruct (n2?=n2) eqn: H'; try assumption.
      * apply Qlt_alt in H'. apply Qlt_irrefl in H'. contradiction.
      * apply Qgt_alt in H'. apply Qlt_irrefl in H'. contradiction.
    + simpl in *. rewrite H0. destruct (n2?=n2) eqn: H'; try simpl.
      * rewrite st_eq_nil_iff_all_none. assumption.
      * apply Qlt_alt in H'. apply Qlt_irrefl in H'. contradiction.
      * apply Qgt_alt in H'. apply Qlt_irrefl in H'. contradiction.
    + simpl in *. destruct (q ?= q0) eqn: H12; try discriminate. 
      rewrite H0. destruct (n2?=n2) eqn: H'; try assumption.
      * apply Qlt_alt in H'. apply Qlt_irrefl in H'. contradiction.
      * apply Qgt_alt in H'. apply Qlt_irrefl in H'. contradiction.
    + rewrite H0. destruct (n2?=n2) eqn: H'; try simpl; try assumption.
      * apply Qlt_alt in H'. apply Qlt_irrefl in H'. contradiction.
      * apply Qgt_alt in H'. apply Qlt_irrefl in H'. contradiction.
  - destruct st1 as [ |v1 l1]; destruct st2 as [| v2 l2]; 
      try destruct v1; try destruct v2; simpl in *; try (discriminate).
    + simpl. apply IHx. apply H.
    + simpl in *. apply IHx. apply H.
    + simpl in *. apply IHx. rewrite st_eq_nil_iff_all_none. assumption.
    + simpl in *. destruct (q ?= q0) eqn: H12; try discriminate.
      apply IHx. assumption.
    + apply IHx. assumption.
Qed.
Theorem st_eq_implies_update_a : forall st1 st2 x a, 
  (st1 == st2)%state -> 
  beq_state (update st1 x (evalA_st a st1)) (update st2 x (evalA_st a st2)) = true.
Proof.
  intros.
  assert (((evalA_st a st1) == (evalA_st a st2))%Q) by (apply st_eq_implies_evalA; assumption).
  apply st_eq_implies_update_eq; assumption.
Qed.

Lemma Qeq_get_under_res_st: forall s n,
  (get n s == get n (res_st_to_X s (singleton_bool_list n)))%Q.
Proof.
  intros. 
  generalize dependent s. induction n; intros.
  - simpl. destruct s as [|v s']; try destruct v; simpl in *; apply Qeq_refl.
  - simpl. destruct s as [|v s']; try destruct v; simpl in *; try apply Qeq_refl.
    + apply IHn.
    + apply IHn.
Qed.

Lemma evalB_Bnot_true_iff: forall b st, 
  evalB_st (~ b) st = true <-> evalB_st b st = false.
Proof. 
  split.
  - intros. simpl in *. rewrite negb_true_iff in H. assumption.
  - intros. simpl in *. rewrite negb_true_iff. assumption.
Qed.

Lemma evalB_Bnot_false_iff: forall b st, 
  evalB_st (~ b) st = false <-> evalB_st b st = true.
Proof. 
  split.
  - intros. simpl in *. rewrite negb_false_iff in H. assumption.
  - intros. simpl in *. rewrite negb_false_iff. assumption.
Qed.

Lemma evalB_Bnot_involutive: forall b st, 
  evalB_st (~ ~ b) st = (evalB_st b st).
Proof.
  intros b st. simpl. rewrite negb_involutive. reflexivity.
Qed. 

Lemma evalB_eq_implies_le_rev: forall a0 a1 st, 
  evalB_st (a0 = a1) st = true -> 
  evalB_st (a1 <= a0) st = true.
Proof.
  intros. simpl in *.  
  apply Qeq_bool_iff in H. rewrite H. 
  apply Qle_bool_iff. apply Qle_refl.
Qed.

Lemma evalB_eq_implies_le: forall a0 a1 st, 
  evalB_st (a0 = a1) st = true -> 
  evalB_st (a0 <= a1) st = true.
Proof.
  intros. simpl in *.  
  apply Qeq_bool_iff in H. rewrite H. 
  apply Qle_bool_iff. apply Qle_refl.
Qed.

Lemma evalB_not_le_iff_lt_rev: forall a0 a1 st, 
  evalB_st (~ (a0 <= a1)) st = evalB_st (a1 < a0) st.
Proof.
  intros a0 a1 st. simpl in *. reflexivity. 
Qed.

Lemma evalB_lt_implies_le: forall a0 a1 st, 
  evalB_st (a0 < a1) st = true ->
  evalB_st (a0 <= a1) st = true. 
Proof.
  intros. 
  rewrite <- evalB_not_le_iff_lt_rev in H. 
  apply evalB_Bnot_true_iff in H. 
  simpl in *. 
  destruct (Qcompare (evalA_st a1 st) (evalA_st a0 st)) eqn: Hcomp.
  - apply Qeq_alt in Hcomp. apply Qle_bool_iff. apply Qle_lteq. right. rewrite Hcomp. reflexivity. 
  - apply Qlt_alt in Hcomp. apply Qlt_leneq in Hcomp. destruct Hcomp. 
  apply Qle_bool_iff in H0. rewrite H in H0. discriminate.
  - apply Qgt_alt in Hcomp. apply Qle_bool_iff. apply Qlt_le_weak. assumption.
Qed.

Lemma evalBeq_implies_lt_compat_l: forall a0 a1 a2 st, 
  evalB_st (a0 = a1) st = true -> 
  evalB_st (a0 < a2) st = evalB_st (a1 < a2) st.
Proof.
  intros a0 a1 a2 st H. simpl in *. 
  apply Qeq_bool_iff in H. rewrite H. reflexivity.
Qed.

Lemma evalB_eq_trans: forall a0 a1 a2 st, 
  evalB_st (a0 = a1) st = true -> 
  evalB_st (a1 = a2) st = true -> 
  evalB_st (a0 = a2) st = true.
Proof.
  intros a0 a1 a2 st H0 H1. simpl in *. 
  apply Qeq_bool_iff in H0. rewrite H0. 
  apply Qeq_bool_iff in H1. rewrite H1. 
  apply Qeq_bool_refl. 
Qed.

Lemma evalB_sym: forall a0 a1 st, 
  evalB_st (a0 = a1) st = evalB_st (a1 = a0) st.
Proof.
  intros a0 a1 st. simpl in *. 
  apply Qeq_bool_comm. 
Qed.
(***********************************************)


Lemma evalA_more_less: forall s a l, 
  (evalA_st a (res_st_to_X s (orb_domain (get_variables_in_aexp a) l)) == evalA_st a s)%Q.
Proof.
  intros. generalize dependent l. generalize dependent s.
  induction a; intros.
  - simpl. apply Qeq_refl.
  - simpl. generalize dependent s. generalize dependent l. 
    induction n; intros.
    * simpl. destruct l; destruct s as [|v s']; try destruct v; simpl in *; try apply Qeq_refl.
    * destruct l.
      + rewrite orb_domain_nil_r. 
      rewrite <- Qeq_get_under_res_st. apply Qeq_refl.
      + destruct s as [|v s']; try destruct v; simpl in *; try apply Qeq_refl. 
      ** destruct b; simpl; apply IHn.
      ** apply IHn.
  - simpl. specialize (IHa1 s (orb_domain (get_variables_in_aexp a2) l)).
    rewrite orb_domain_assoc in IHa1. repeat rewrite IHa1.
    specialize (IHa2 s (orb_domain (get_variables_in_aexp a1) l)).
    rewrite orb_domain_assoc in IHa2. 
    rewrite orb_domain_comm with (l':= (get_variables_in_aexp a1)) in IHa2. 
    repeat rewrite IHa2. reflexivity.
  - simpl. specialize (IHa1 s (orb_domain (get_variables_in_aexp a2) l)).
    rewrite orb_domain_assoc in IHa1. repeat rewrite IHa1.  
    specialize (IHa2 s (orb_domain (get_variables_in_aexp a1) l)).
    rewrite orb_domain_assoc in IHa2. 
    rewrite orb_domain_comm with (l':= (get_variables_in_aexp a1)) in IHa2. 
    repeat rewrite IHa2. reflexivity.
  - simpl. specialize (IHa1 s (orb_domain (get_variables_in_aexp a2) l)).
  rewrite orb_domain_assoc in IHa1. repeat rewrite IHa1.  
  specialize (IHa2 s (orb_domain (get_variables_in_aexp a1) l)).
  rewrite orb_domain_assoc in IHa2. 
  rewrite orb_domain_comm with (l':= (get_variables_in_aexp a1)) in IHa2. 
  repeat rewrite IHa2. reflexivity.
Qed.
Lemma evalA_eq_res_st: forall s a, 
  (evalA_st a (res_st_to_X s (get_variables_in_aexp a)) == evalA_st a s)%Q.
Proof.
  intros. generalize dependent s. induction a; intros.
  - simpl. apply Qeq_refl.
  - simpl. rewrite <- Qeq_get_under_res_st. reflexivity.
  - simpl. rewrite evalA_more_less. rewrite orb_domain_comm at 1. rewrite evalA_more_less. reflexivity.
  - simpl. rewrite evalA_more_less. rewrite orb_domain_comm at 1. rewrite evalA_more_less. reflexivity. 
  - simpl. rewrite evalA_more_less. rewrite orb_domain_comm at 1. rewrite evalA_more_less. reflexivity. 
Qed. 

Lemma evalB_more_less: forall s b l,
  evalB_st b (res_st_to_X s (orb_domain (get_variables_in_bexp b) l)) = evalB_st b s.
Proof.
  intros. generalize dependent l. generalize dependent s.
  induction b.
  - intros. simpl. reflexivity.
  - intros. simpl in *. reflexivity.
  - intros. simpl in *. destruct l. 
    + rewrite orb_domain_nil_r. specialize (IHb1 s (get_variables_in_bexp b2)).
      rewrite IHb1. specialize (IHb2 s (get_variables_in_bexp b1)).
      rewrite orb_domain_comm in IHb2.
      rewrite IHb2. reflexivity.
    + rewrite <- orb_domain_assoc. specialize (IHb1 s (orb_domain (get_variables_in_bexp b2) (b :: l))).
      rewrite IHb1. rewrite orb_domain_assoc. 
      rewrite orb_domain_comm with (l:= (get_variables_in_bexp b1)).
      rewrite <- orb_domain_assoc. specialize (IHb2 s (orb_domain (get_variables_in_bexp b1) (b :: l))).
      rewrite IHb2. reflexivity.
  - intros. simpl. unfold negb in *. rewrite IHb. reflexivity.
  - intros. simpl. rewrite <- orb_domain_assoc. rewrite evalA_more_less.
    rewrite orb_domain_assoc. rewrite orb_domain_comm with (l':= (get_variables_in_aexp a0)).
    rewrite <- orb_domain_assoc. rewrite evalA_more_less. reflexivity.
  - intros. simpl. rewrite <- orb_domain_assoc. rewrite evalA_more_less.
    rewrite orb_domain_assoc. rewrite orb_domain_comm with (l':= (get_variables_in_aexp a0)).
    rewrite <- orb_domain_assoc. rewrite evalA_more_less. reflexivity.
Qed.

Lemma evalB_eq_res_st: forall s b,
  evalB_st b (res_st_to_X s (get_variables_in_bexp b)) = evalB_st b s.
Proof.
  intros. generalize dependent s. induction b; intros.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl in *. rewrite evalB_more_less. rewrite orb_domain_comm. rewrite evalB_more_less. reflexivity.
  - simpl in *. unfold negb. rewrite IHb. reflexivity.
  - simpl. rewrite evalA_more_less. rewrite orb_domain_comm. rewrite evalA_more_less. reflexivity.
  - simpl. rewrite evalA_more_less. rewrite orb_domain_comm. rewrite evalA_more_less. reflexivity.
Qed. 

Lemma all_false_sing_contra: forall n,
  all_false (singleton_bool_list n) = false.
Proof.
  intros. induction n; simpl; try reflexivity. 
  apply IHn. 
Qed.
Lemma sing_nil_contra: forall n, 
  (singleton_bool_list n == [])%domain -> False.
Proof.
  intros. induction n. 
  - simpl in H. destruct H. discriminate H.
  - simpl in *. apply IHn. destruct H. 
    simpl in H. rewrite all_false_sing_contra in H. discriminate H.
Qed.

Ltac solve_Qcompare_with tactic:=
  match goal with
  | [ Heq : (_ ?= _)%Q = Eq |- _ ] =>
      apply tactic
  | [ Hlt : (_ ?= _)%Q = Lt |- _ ] =>
      apply Qlt_alt in Hlt; apply Qlt_irrefl in Hlt; contradiction
  | [ Hgt : (_ ?= _)%Q = Gt |- _ ] =>
      apply Qgt_alt in Hgt; apply Qlt_irrefl in Hgt; contradiction
  end.

Lemma update_eq_res_st: forall s n q X, 
  is_domain_subset (singleton_bool_list n) X = true ->
  ((res_st_to_X (update s n q) X == update (res_st_to_X s X) n q)%state). 
Proof. 
  intros. 
  generalize dependent s. generalize dependent n. induction X; intros.
  - destruct n; simpl in H; try discriminate. 
  rewrite all_false_sing_contra in H. discriminate.
  - destruct n; simpl in H; try discriminate. 
    + rewrite andb_true_r in H. rewrite H. 
      destruct s as [|v s']; try destruct v; simpl in *; try apply state_eq_refl. 
      * destruct (q ?= q)%Q eqn: H'; try reflexivity.
      -- apply Qlt_alt in H'. apply Qlt_irrefl in H'. contradiction.
      -- apply Qgt_alt in H'. apply Qlt_irrefl in H'. contradiction.
      * destruct (q ?= q)%Q eqn: H'; solve_Qcompare_with state_eq_refl.
      * destruct (q ?= q)%Q eqn: H'; solve_Qcompare_with state_eq_refl.
    + simpl. destruct s as [|v s']; try destruct v; 
        simpl in *; try apply state_eq_refl; try apply IHX; try assumption.
      destruct a; simpl in *. 
      * apply IHX with (s:= s') in H. 
        destruct (q0 ?= q0)%Q eqn:Hq0; try assumption.
      -- apply Qlt_alt in Hq0. apply Qlt_irrefl in Hq0. contradiction.
      -- apply Qgt_alt in Hq0. apply Qlt_irrefl in Hq0. contradiction.
      * simpl. apply IHX; assumption.
Qed.  
Lemma update_subst_implies_dom_eq: forall s x q, 
  is_domain_subset (return_domain s) (return_domain (update s x q)) = true.
Proof. 
  intros. generalize dependent x. generalize dependent q. 
  induction s as [|v s' IH]; intros.
  - simpl. reflexivity.
  - simpl. destruct x; simpl. 
    + apply andb_true_iff. split.
      * rewrite negb_involutive. simpl.
      apply orb_true_iff. right. reflexivity.
      * apply dom_subset_refl.
    + apply andb_true_iff. split.
      * rewrite negb_involutive. apply orb_negb_r.
      * apply IH. 
Qed.

Lemma get_n_in_sing: forall n s,
  all_false (singleton_bool_list n) = true ->
  (default_Q == get n s)%Q.
Proof.
  intros. generalize dependent s. 
  induction n; destruct s; intros; try reflexivity.
  - simpl in H. discriminate.
  - simpl. apply IHn. assumption.
Qed.
Lemma get_n_sub: forall n V s,
  is_domain_subset (singleton_bool_list n) V = true -> 
  (get n (res_st_to_X s V) == get n s)%Q. 
Proof. 
  intros. generalize dependent s. generalize dependent V. 
  induction n; destruct s as [|v s']; try destruct v; destruct V; 
    simpl in *; intros; try reflexivity; try discriminate; try apply get_n_in_sing; try assumption.
  - simpl. apply andb_true_iff in H. destruct H. rewrite H. reflexivity.
  - destruct b; apply IHn with (V:= V); assumption.
  - apply IHn. assumption. 
Qed. 
Lemma evalA_st_preserve_bool : forall a s V,
    is_domain_subset (get_variables_in_aexp a) V = true ->
    (evalA_st a (res_st_to_X s (get_variables_in_aexp a)) == 
     evalA_st a (res_st_to_X s V))%Q.
Proof.
  intros. generalize dependent s. generalize dependent V. 
  induction a; intros; try reflexivity; try discriminate.
  - simpl in *. 
  rewrite <- Qeq_get_under_res_st.
  rewrite get_n_sub with (V:= V); try assumption. reflexivity.
  - simpl. rewrite evalA_more_less. rewrite orb_domain_comm. rewrite evalA_more_less.
  simpl in H. apply dom_subset_orb_fst_iff in H. destruct H.
  specialize (IHa1 V H s). rewrite evalA_eq_res_st in IHa1.
  specialize (IHa2 V H0 s). rewrite evalA_eq_res_st in IHa2.
  rewrite IHa1. rewrite IHa2. try reflexivity.
  - simpl in *. 
  rewrite evalA_more_less. rewrite orb_domain_comm. rewrite evalA_more_less.
  simpl in H. apply dom_subset_orb_fst_iff in H. destruct H.
  specialize (IHa1 V H s). rewrite evalA_eq_res_st in IHa1.
  specialize (IHa2 V H0 s). rewrite evalA_eq_res_st in IHa2.
  rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl in *. 
  rewrite evalA_more_less. rewrite orb_domain_comm. rewrite evalA_more_less.
  simpl in H. apply dom_subset_orb_fst_iff in H. destruct H.
  specialize (IHa1 V H s). rewrite evalA_eq_res_st in IHa1.
  specialize (IHa2 V H0 s). rewrite evalA_eq_res_st in IHa2.
  rewrite IHa1. rewrite IHa2. reflexivity.
Qed. 

Lemma evalB_st_preserve_bool : forall b s V,
    is_domain_subset (get_variables_in_bexp b) V = true ->
    evalB_st b (res_st_to_X s (get_variables_in_bexp b)) = 
    evalB_st b (res_st_to_X s V).
Proof.
  intros. generalize dependent s. generalize dependent V. 
  induction b; intros; try reflexivity; try discriminate.
  - simpl in *. 
    rewrite evalB_more_less. rewrite orb_domain_comm. rewrite evalB_more_less.
    apply dom_subset_orb_fst_iff in H. destruct H.
    specialize (IHb1 V H s).
    rewrite evalB_eq_res_st in IHb1. rewrite <- IHb1.
    specialize (IHb2 V H0 s).
    rewrite evalB_eq_res_st in IHb2. rewrite <- IHb2.
    reflexivity.
  - simpl in *. unfold negb.
    specialize (IHb V H s).
    rewrite IHb. reflexivity.
  - simpl. rewrite evalA_more_less. rewrite orb_domain_comm. rewrite evalA_more_less.
    simpl in H. apply dom_subset_orb_fst_iff in H. destruct H.
    repeat rewrite <- evalA_st_preserve_bool; try assumption.
    rewrite <- evalA_st_preserve_bool with (a:= a0); try assumption.
    repeat rewrite evalA_eq_res_st. reflexivity.
  - simpl. rewrite evalA_more_less. rewrite orb_domain_comm. rewrite evalA_more_less.
    simpl in H. apply dom_subset_orb_fst_iff in H. destruct H.
    repeat rewrite <- evalA_st_preserve_bool; try assumption.
    rewrite <- evalA_st_preserve_bool with (a:= a0); try assumption.
    repeat rewrite evalA_eq_res_st. reflexivity.
Qed. 

(********************************************)
Lemma supp_insert_all_none: forall s sp, 
  forallb (fun s : local_st => st_all_none s) (insert_st s sp) = 
    (st_all_none s && forallb (fun s : local_st => st_all_none s) sp)%bool.
Proof.
  intros s sp. induction sp as [|s0 sp' IH]; try reflexivity; intros.
  simpl in *. destruct (beq_state s s0) eqn: Hs.
  - simpl in *. apply st_eq_eq_all_none_compat in Hs. rewrite Hs. 
  rewrite andb_assoc. rewrite andb_diag. reflexivity.
  - destruct (ble_state s s0) eqn: Hle. 
    + simpl in *. reflexivity.
    + simpl in *. rewrite IH. rewrite andb_assoc. 
    rewrite andb_comm with (b2:= st_all_none s).
    rewrite andb_assoc. reflexivity.
Qed.
Lemma supp_sort_all_none: forall mu, 
  forallb (fun s0 : local_st => st_all_none s0) (map fst mu) = 
  forallb (fun s0 : local_st => st_all_none s0) (map fst (sort_dst mu)).
Proof.
  intros mu. induction mu as [|(s,p) mu' IH]; simpl; try reflexivity.
  rewrite insert_st_pair_fst_eq_insert_st. 
  rewrite supp_insert_all_none. rewrite IH. reflexivity.
Qed.

Lemma supp_insert_evalB: forall s sp b, 
  forallb (fun s : local_st => evalB_st b s) (insert_st s sp) =
  (evalB_st b s && forallb (fun s : local_st => evalB_st b s) sp)%bool.
Proof.
  intros s sp. induction sp as [|s0 sp' IH]; try reflexivity; intros.
  simpl in *. destruct (beq_state s s0) eqn: Hs.
  - simpl in *. apply st_eq_implies_evalB with (b:= b) in Hs. rewrite Hs. 
  rewrite andb_assoc. rewrite andb_diag. reflexivity.
  - destruct (ble_state s s0) eqn: Hle. 
    + simpl in *. reflexivity.
    + simpl in *. rewrite IH. rewrite andb_assoc. 
    rewrite andb_comm with (b2:= evalB_st b s).
    rewrite andb_assoc. reflexivity.
Qed.
Lemma supp_sort_evalB: forall mu b, 
  forallb (fun s0 : local_st => evalB_st b s0) (map fst mu) = 
  forallb (fun s0 : local_st => evalB_st b s0) (map fst (sort_dst mu)).
Proof.
  intros mu b. induction mu as [|(s,p) mu' IH]; simpl; try reflexivity.
  rewrite insert_st_pair_fst_eq_insert_st. 
  rewrite supp_insert_evalB. rewrite IH. reflexivity.
Qed.

Lemma supp_decom_r_evalB: forall mu0 mu1 b, 
  forallb (fun s : local_st => evalB_st b s) (supp_mu (mu0 + mu1)) = true -> 
  forallb (fun s : local_st => evalB_st b s) (supp_mu (mu0)) = true.
Proof.
  intros mu0 mu1 b Hb. generalize dependent mu1. 
  induction mu0 as [|(s,p) mu0' IH]; intros; try reflexivity.
  unfold supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st. rewrite supp_insert_evalB. 
  unfold supp_mu in Hb. simpl in Hb. rewrite insert_st_pair_fst_eq_insert_st in Hb. 
  rewrite supp_insert_evalB in Hb. apply andb_true_iff in Hb. destruct Hb.
  rewrite H. simpl. apply IH in H0; try assumption. 
Qed. 

Lemma supp_decom_l_evalB: forall mu0 mu1 b, 
  forallb (fun s : local_st => evalB_st b s) (supp_mu (mu0 + mu1)) = true -> 
  forallb (fun s : local_st => evalB_st b s) (supp_mu (mu1)) = true.
Proof.
  intros mu0 mu1 b Hb. 
  induction mu0 as [|(s,p) mu0' IH]; intros; try reflexivity.
  - simpl in Hb. assumption.
  - apply IH. unfold supp_mu in Hb. simpl in Hb. 
    rewrite insert_st_pair_fst_eq_insert_st in Hb. 
    rewrite supp_insert_evalB in Hb. apply andb_true_iff in Hb. 
    destruct Hb. try assumption. 
Qed. 

Lemma supp_insert_negbevalB: forall s sp b, 
  forallb (fun s : local_st => negb (evalB_st b s)) (insert_st s sp) =
  (negb (evalB_st b s) && forallb (fun s : local_st => negb (evalB_st b s)) sp)%bool.
Proof.
  intros s sp. induction sp as [|s0 sp' IH]; try reflexivity; intros.
  simpl in *. destruct (beq_state s s0) eqn: Hs.
  - simpl in *. apply st_eq_implies_evalB with (b:= b) in Hs. rewrite Hs. 
  rewrite andb_assoc. rewrite andb_diag. reflexivity.
  - destruct (ble_state s s0) eqn: Hle. 
    + simpl in *. reflexivity.
    + simpl in *. rewrite IH. rewrite andb_assoc. 
    rewrite andb_comm with (b2:= negb (evalB_st b s)).
    rewrite andb_assoc. reflexivity.
Qed.

Lemma supp_sort_negbevalB: forall mu b,
  forallb (fun s0 : local_st => negb (evalB_st b s0)) (map fst mu) = 
  forallb (fun s0 : local_st => negb (evalB_st b s0)) (map fst (sort_dst mu)).
Proof.
  intros mu b. induction mu as [|(s,p) mu' IH]; simpl; try reflexivity.
  rewrite insert_st_pair_fst_eq_insert_st. 
  rewrite supp_insert_negbevalB. rewrite IH. reflexivity.
Qed.

Lemma supp_decom_r_negbevalB: forall mu0 mu1 b, 
  forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu (mu0 + mu1)) = true -> 
  forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu (mu0)) = true.
Proof.
  intros mu0 mu1 b Hb. generalize dependent mu1. 
  induction mu0 as [|(s,p) mu0' IH]; intros; try reflexivity.
  unfold supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st. rewrite supp_insert_negbevalB. 
  unfold supp_mu in Hb. simpl in Hb. rewrite insert_st_pair_fst_eq_insert_st in Hb. 
  rewrite supp_insert_negbevalB in Hb. apply andb_true_iff in Hb. destruct Hb.
  rewrite H. simpl. apply IH in H0; try assumption. 
Qed. 

Lemma supp_decom_l_negbevalB: forall mu0 mu1 b, 
  forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu (mu0 + mu1)) = true -> 
  forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu (mu1)) = true.
Proof.
  intros mu0 mu1 b Hb. 
  induction mu0 as [|(s,p) mu0' IH]; intros; try reflexivity.
  - simpl in Hb. assumption.
  - apply IH. unfold supp_mu in Hb. simpl in Hb. 
    rewrite insert_st_pair_fst_eq_insert_st in Hb. 
    rewrite supp_insert_negbevalB in Hb. apply andb_true_iff in Hb. 
    destruct Hb. try assumption. 
Qed. 

Inductive b_classification : Type := 
  | All_nil
  | All_True  (* Indicates that b is always "true" under pd *)
  | All_False (* Indicates that b is always "false" under pd *)
  | Mixed. 

Definition b_supp_classify (b: bexp) (pd: partial_dist) : b_classification := 
  match (mu pd) with 
  | [] => All_nil 
  | _ => let states := supp_mu (mu pd) in
          match (forallb (fun s => evalB_st b s) states, (*Must be valid in WF_cexpw_ith_pd b pd*)
                  forallb (fun s => negb (evalB_st b s)) states) with
          | (true, _) => All_True
          | (_, true) => All_False
          | _ => Mixed
          end
  end.

Lemma pd_Nil_mu: forall b pd, b_supp_classify b pd = All_nil <-> mu pd = nil.
Proof.
  split. { 
    intros H. unfold b_supp_classify in *. destruct pd as [dom mu HPD]. 
    destruct mu; simpl in *; try reflexivity.
    destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu (p :: mu))); 
    destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu (p :: mu))); try discriminate. }
  intros. unfold b_supp_classify in *. rewrite H. reflexivity.
Qed.

Lemma dst_sort_b_classify: forall pd b, 
  Valid_dist (mu pd) -> 
  b_supp_classify b pd = b_supp_classify b (Sort_pd pd).
Proof. 
  intros pd b Hv. destruct pd as [dom mu HPD].
  unfold b_supp_classify. simpl in *. 
  rewrite <- supp_eq_sorted; try assumption.
  induction mu as [|(s,p) mu' IH]; simpl; try reflexivity.
  destruct (insert_st_pair s p (sort_dst mu')) eqn: Hincont.
  - apply insert_pair_contra in Hincont. contradiction.
  - inversion HPD; subst. apply Valid_dist_inv in Hv; subst.
    specialize (IH H3 Hv). unfold supp_mu. simpl.
    rewrite insert_st_pair_fst_eq_insert_st.
    rewrite supp_insert_evalB.
    rewrite supp_insert_negbevalB.
    destruct (evalB_st b s); simpl; try reflexivity.
Qed.
 
Lemma supp_equiv_implies_all_none_eq: forall sp0 sp1, 
  (sp0 == sp1)%supp ->
  forallb (fun s : local_st => st_all_none s) sp0 = forallb (fun s : local_st => st_all_none s) sp1.
Proof.
  intros sp0 sp1 H. generalize dependent sp1.
  induction sp0 as [|l0 sp0 IH]; destruct sp1 as [|l1 sp1]; try reflexivity; intros.
  - simpl in *. discriminate.
  - simpl in *. discriminate.
  - simpl in *. apply andb_true_iff in H. destruct H.
    apply IH in H0. rewrite H0. 
    apply st_eq_eq_all_none_compat in H. rewrite H. reflexivity.
Qed.

Lemma supp_equiv_implies_evalB_eq: forall sp0 sp1 b, 
  (sp0 == sp1)%supp ->
  forallb (fun s : local_st => evalB_st b s) sp0 = forallb (fun s : local_st => evalB_st b s) sp1.
Proof.
  intros sp0 sp1 b H. generalize dependent sp1.
  induction sp0 as [|l0 sp0 IH]; destruct sp1 as [|l1 sp1]; try reflexivity; intros.
  - simpl in *. discriminate.
  - simpl in *. discriminate.
  - simpl in *. apply andb_true_iff in H. destruct H.
    apply IH in H0. rewrite H0. 
    apply st_eq_implies_evalB with (b:= b) in H. rewrite H. reflexivity.
Qed.
Lemma supp_equiv_implies_negbevalB_eq: forall sp0 sp1 b, 
  (sp0 == sp1)%supp ->
  forallb (fun s : local_st => negb (evalB_st b s)) sp0 = 
    forallb (fun s : local_st => negb (evalB_st b s)) sp1.
Proof.
  intros sp0 sp1 b H. generalize dependent sp1.
  induction sp0 as [|l0 sp0 IH]; destruct sp1 as [|l1 sp1]; try reflexivity; intros.
  - simpl in *. discriminate.
  - simpl in *. discriminate.
  - simpl in *. apply andb_true_iff in H. destruct H.
    apply IH in H0. rewrite H0. 
    apply st_eq_implies_evalB with (b:= b) in H. rewrite H. reflexivity.
Qed.

Lemma dst_equiv_implies_b_classify: 
  forall pd0 pd1 b,  
  Valid_dist (mu pd0) -> Valid_dist (mu pd1) ->
  pd0 ≡ pd1 ->
  b_supp_classify b pd0 = b_supp_classify b pd1.
Proof.
  intros pd0 pd1 b Hv0 Hv1 Heq. 
  rewrite dst_sort_b_classify; try assumption.
  rewrite dst_sort_b_classify with (pd:= pd1); try assumption.
  destruct pd0 as [dom0 mu0 HPD0]. destruct pd1 as [dom1 mu1 HPD1].
  destruct Heq. simpl in *. 
  assert (Hsorted1: (mu0 == sort_dst mu0)%dist_state). { apply dst_equiv_sort. }
  assert (Hsorted2: (mu1 == sort_dst mu1)%dist_state). { apply dst_equiv_sort. }
  assert (Hsort_trans: (sort_dst mu0 == sort_dst mu1)%dist_state). { 
    eapply dst_equiv_trans. 
    - apply dst_equiv_sym in Hsorted1. apply Hsorted1.
    - eapply dst_equiv_trans. 
      + apply H0. + apply Hsorted2. }
  assert (Hvalid_sort1: Valid_dist (sort_dst mu0)). { apply Valid_implies_sort_Valid. assumption. }
  assert (Hvalid_sort2: Valid_dist (sort_dst mu1)). { apply Valid_implies_sort_Valid. assumption. }
  assert (Htemp_beq: beq_dst (sort_dst mu0) (sort_dst mu1) = true). { 
    apply Sort_Valid_Peq_implies_beq_True; try (assumption).
    - split; [apply WF_dist_implies_sortdst_Sorted; assumption| assumption].
    - split; [apply WF_dist_implies_sortdst_Sorted; assumption| assumption]. }
  apply dst_equiv_implies_beq_supp in H0; try assumption. 
  unfold b_supp_classify. simpl.
  repeat rewrite <- supp_eq_sorted; try assumption.
  rewrite supp_equiv_implies_evalB_eq with (sp1:= supp_mu mu1); try assumption.
  rewrite supp_equiv_implies_negbevalB_eq with (sp1:= supp_mu mu1); try assumption.
  destruct (sort_dst mu0); destruct (sort_dst mu1); simpl in *; try reflexivity.
  - destruct p. apply dst_equiv_sym in Hsort_trans. 
    apply dst_cons_valid_contra in Hsort_trans; try assumption. contradiction.
  - destruct p. 
    apply dst_cons_valid_contra in Hsort_trans; try assumption. contradiction.
Qed.

Lemma b_classify_mult_coef: forall pd p b, 
  0 < p -> 
  b_supp_classify b (cofe_pd pd p) = b_supp_classify b pd.
Proof.
  intros. unfold b_supp_classify. simpl. 
  rewrite <- supp_eq_mult_coef; try assumption.
  induction (mu pd) as [|(s0,p0) mu'].
  - simpl. reflexivity.
  - simpl. destruct (Req_dec_T p 0); try contradict. 
    + rewrite e in H. apply Rlt_irrefl in H. contradiction.
    + reflexivity.
Qed.

Lemma st_subst_evalBT: forall s b sp, 
  ([s] ⊆ sp)%supp -> forallb (fun s : local_st => evalB_st b s) sp = true ->
  evalB_st b s = true.
Proof.
  intros s b sp Hs Hsp. induction sp; simpl in *; try discriminate.  
  destruct (beq_state s a) eqn: Hst.
  - apply andb_true_iff in Hsp. destruct Hsp. 
    apply st_eq_implies_evalB with (b:= b) in Hst. rewrite Hst. assumption.
  - destruct (ble_state s a); try discriminate. 
    apply andb_true_iff in Hsp. destruct Hsp. 
    apply IHsp in Hs; try assumption.
Qed.

Lemma st_subst_negbevalBT: forall s b sp, 
  ([s] ⊆ sp)%supp -> forallb (fun s : local_st => negb (evalB_st b s)) sp = true ->
    negb (evalB_st b s) = true.
Proof.
  intros s b sp Hs Hsp. induction sp; simpl in *; try discriminate.  
  destruct (beq_state s a) eqn: Hst.
  - apply andb_true_iff in Hsp. destruct Hsp. 
    apply st_eq_implies_evalB with (b:= b) in Hst. rewrite Hst. assumption.
  - destruct (ble_state s a); try discriminate. 
    apply andb_true_iff in Hsp. destruct Hsp. 
    apply IHsp in Hs; try assumption.
Qed.


Lemma supp_subst_implies_evalBT_eq: forall sp0 sp1 b, 
  ((sp0) ⊆ sp1)%supp ->
  forallb (fun s : local_st => evalB_st b s) sp1 = true ->
  forallb (fun s : local_st => evalB_st b s) (sp0) = true.
Proof.
  intros sp0 sp1 b H. intros. generalize dependent sp0.
  induction sp1 as [|l1 sp1 IH]; destruct sp0 as [|l0 sp0]; 
    intros; try reflexivity; try contradiction; try discriminate.
  simpl in *. apply andb_true_iff in H0. destruct H0.
  destruct (beq_state l0 l1) eqn: Hst. 
    + apply IH in H; try assumption. 
      apply st_eq_implies_evalB with (b:= b) in Hst. rewrite Hst. rewrite H0. 
      simpl. assumption.
    + destruct (ble_state l0 l1); try discriminate.
      apply IH with (sp0:= l0 :: sp0) in H1; try assumption. 
Qed.

Lemma supp_subst_implies_negbevalBT_eq: forall sp0 sp1 b, 
  ((sp0) ⊆ sp1)%supp ->
  forallb (fun s : local_st => negb (evalB_st b s)) sp1 = true ->
  forallb (fun s : local_st => negb (evalB_st b s)) (sp0) = true.
Proof.
  intros sp0 sp1 b H. intros. generalize dependent sp0.
  induction sp1 as [|l1 sp1 IH]; destruct sp0 as [|l0 sp0]; 
    intros; try reflexivity; try contradiction; try discriminate.
  simpl in *. apply andb_true_iff in H0. destruct H0.
  destruct (beq_state l0 l1) eqn: Hst. 
    + apply IH in H; try assumption. 
      apply st_eq_implies_evalB with (b:= b) in Hst. rewrite Hst. rewrite H0. 
      simpl. assumption.
    + destruct (ble_state l0 l1); try discriminate.
      apply IH with (sp0:= l0 :: sp0) in H1; try assumption. 
Qed.

Lemma supp_insert_subst_implies_evalBT_eq: forall s0 sp0 sp1 b, 
  Sorted_supp sp0 -> Sorted_supp sp1 ->
  ((insert_st s0 sp0) ⊆ sp1)%supp ->
  forallb (fun s : local_st => evalB_st b s) sp1 = true ->
  evalB_st b s0 && forallb (fun s : local_st => evalB_st b s) sp0 = true.
Proof.
  intros s0 sp0 sp1 b HS0 HS1 H. intros. generalize dependent s0. generalize dependent sp0.
  induction sp1 as [|l1 sp1 IH]; destruct sp0 as [|l0 sp0]; 
    intros; try reflexivity; try contradiction; try discriminate.
  - simpl in H. destruct (beq_state s0 l0); destruct (ble_state s0 l0); try discriminate.
  - simpl in *. apply andb_true_iff in H0. destruct H0.
    rewrite andb_true_r. destruct (beq_state s0 l1) eqn: Hst. 
    + apply st_eq_implies_evalB with (b:= b) in Hst. rewrite Hst. assumption.
    + destruct (ble_state s0 l1); try discriminate. 
      simpl in *. apply st_subst_evalBT with (b:= b) in H; try assumption.
  - simpl. simpl in H0. apply andb_true_iff in H0. destruct H0.
    apply Sort_supp_inv in HS1.
    specialize (IH HS1 H1). simpl in H. destruct (beq_state s0 l0) eqn: Hst0. 
    + destruct (beq_state l0 l1) eqn: Hst1. 
      * apply st_eq_implies_evalB with (b:= b) in Hst0. rewrite Hst0. 
      apply st_eq_implies_evalB with (b:= b) in Hst1. rewrite Hst1. 
      rewrite H0. simpl.   
      apply supp_subst_implies_evalBT_eq with (b:= b) in H; try assumption.
      * destruct (ble_state l0 l1); try discriminate. 
      assert (HS': Sorted_supp (l0 :: sp0)) by assumption.
      apply Sort_supp_inv in HS0. specialize (IH sp0 HS0 l0). rewrite IH.
      ** rewrite andb_true_r. apply st_eq_implies_evalB with (b:= b) in Hst0. rewrite Hst0.
      apply supp_subst_implies_evalBT_eq with (b:= b) in H; try assumption.
      simpl in H. apply andb_true_iff in H. destruct H. assumption.
      ** apply supp_subset_insert_preserves; try assumption. 
      -- apply supp_subset_inv_l in H; try assumption. 
      -- apply supp_subset_cons_implies_head in H. assumption.
    + destruct (ble_state s0 l0) eqn: Hle0. 
      * destruct (beq_state s0 l1) eqn: Hst1. 
      ** apply st_eq_implies_evalB with (b:= b) in Hst1. rewrite Hst1. rewrite H0. simpl.
      apply supp_subst_implies_evalBT_eq with (b:= b) in H; try assumption.
      ** destruct (ble_state s0 l1) eqn: Hle1; try discriminate.  
      apply supp_subst_implies_evalBT_eq with (b:= b) in H; try assumption.
      * destruct (beq_state l0 l1) eqn: Hst1. 
      ** apply st_eq_implies_evalB with (b:= b) in Hst1. rewrite Hst1. rewrite H0. simpl.
      apply Sort_supp_inv in HS0. apply IH; try assumption.  
      ** destruct (ble_state l0 l1); try discriminate. 
      assert (Htmp1: ([l0] ⊆ sp1)%supp) by (apply supp_subset_cons_implies_head in H; assumption).
      assert (Htmp2: (insert_st s0 sp0 ⊆ sp1)%supp). { 
        apply supp_subset_inv_l in H; try assumption.
        apply Sort_supp_cons_insert_st_preserve; try assumption. }
      apply st_subst_evalBT with (b:= b) in Htmp1; try assumption. rewrite Htmp1. simpl.
      apply IH; try assumption. apply Sort_supp_inv in HS0. try assumption.
Qed. 



Lemma supp_insert_subst_implies_negbevalBT_eq: forall s0 sp0 sp1 b, 
  Sorted_supp sp0 -> Sorted_supp sp1 ->
  ((insert_st s0 sp0) ⊆ sp1)%supp ->
  forallb (fun s : local_st => negb (evalB_st b s)) sp1 = true ->
  (negb (evalB_st b s0)) && forallb (fun s : local_st => negb (evalB_st b s)) sp0 = true.
Proof.
  intros s0 sp0 sp1 b HS0 HS1 H. intros. generalize dependent s0. generalize dependent sp0.
  induction sp1 as [|l1 sp1 IH]; destruct sp0 as [|l0 sp0]; 
    intros; try reflexivity; try contradiction; try discriminate.
  - simpl in H. destruct (beq_state s0 l0); destruct (ble_state s0 l0); try discriminate.
  - simpl in *. apply andb_true_iff in H0. destruct H0.
    rewrite andb_true_r. destruct (beq_state s0 l1) eqn: Hst. 
    + apply st_eq_implies_evalB with (b:= b) in Hst. rewrite Hst. assumption.
    + destruct (ble_state s0 l1); try discriminate. 
      simpl in *. apply st_subst_negbevalBT with (b:= b) in H; try assumption.
  - simpl. simpl in H0. apply andb_true_iff in H0. destruct H0.
    apply Sort_supp_inv in HS1.
    specialize (IH HS1 H1). simpl in H. destruct (beq_state s0 l0) eqn: Hst0. 
    + destruct (beq_state l0 l1) eqn: Hst1. 
      * apply st_eq_implies_evalB with (b:= b) in Hst0. rewrite Hst0. 
      apply st_eq_implies_evalB with (b:= b) in Hst1. rewrite Hst1. 
      rewrite H0. simpl.   
      apply supp_subst_implies_negbevalBT_eq with (b:= b) in H; try assumption.
      * destruct (ble_state l0 l1); try discriminate. 
      assert (HS': Sorted_supp (l0 :: sp0)) by assumption.
      apply Sort_supp_inv in HS0. specialize (IH sp0 HS0 l0). rewrite IH.
      ** rewrite andb_true_r. apply st_eq_implies_evalB with (b:= b) in Hst0. rewrite Hst0.
      apply supp_subst_implies_negbevalBT_eq with (b:= b) in H; try assumption.
      simpl in H. apply andb_true_iff in H. destruct H. assumption.
      ** apply supp_subset_insert_preserves; try assumption. 
      -- apply supp_subset_inv_l in H; try assumption. 
      -- apply supp_subset_cons_implies_head in H. assumption.
    + destruct (ble_state s0 l0) eqn: Hle0. 
      * destruct (beq_state s0 l1) eqn: Hst1. 
      ** apply st_eq_implies_evalB with (b:= b) in Hst1. rewrite Hst1. rewrite H0. simpl.
      apply supp_subst_implies_negbevalBT_eq with (b:= b) in H; try assumption.
      ** destruct (ble_state s0 l1) eqn: Hle1; try discriminate.  
      apply supp_subst_implies_negbevalBT_eq with (b:= b) in H; try assumption.
      * destruct (beq_state l0 l1) eqn: Hst1. 
      ** apply st_eq_implies_evalB with (b:= b) in Hst1. rewrite Hst1. rewrite H0. simpl.
      apply Sort_supp_inv in HS0. apply IH; try assumption.  
      ** destruct (ble_state l0 l1); try discriminate. 
      assert (Htmp1: ([l0] ⊆ sp1)%supp) by (apply supp_subset_cons_implies_head in H; assumption).
      assert (Htmp2: (insert_st s0 sp0 ⊆ sp1)%supp). { 
        apply supp_subset_inv_l in H; try assumption.
        apply Sort_supp_cons_insert_st_preserve; try assumption. }
      apply st_subst_negbevalBT with (b:= b) in Htmp1; try assumption. rewrite Htmp1. simpl.
      apply IH; try assumption. apply Sort_supp_inv in HS0. try assumption.
Qed. 
Lemma supp_mu_subst_evalB: forall s0 p0 mu0 sp b, 
  Sorted_supp sp -> (supp_mu ((s0, p0) :: mu0) ⊆ sp)%supp ->
  forallb (fun s : local_st => (evalB_st b s)) sp = true ->
  forallb (fun s : local_st => (evalB_st b s)) (supp_mu ((s0, p0) :: mu0)) = true.
Proof.
  intros s0 p0 mu0 sp b HS Hsupp.  
  unfold supp_mu in Hsupp. simpl in Hsupp. 
  rewrite insert_st_pair_fst_eq_insert_st in Hsupp. 
  unfold supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st. rewrite supp_insert_evalB.
  apply supp_insert_subst_implies_evalBT_eq with (sp1:= sp); try assumption.
  apply Sort_supp_if_WF_supp. 
Qed. 

Lemma supp_mu_subst_negbevalB: forall s0 p0 mu0 sp b, 
  Sorted_supp sp -> (supp_mu ((s0, p0) :: mu0) ⊆ sp)%supp ->
  forallb (fun s : local_st => negb (evalB_st b s)) sp = true ->
  forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s0, p0) :: mu0)) = true.
Proof.
  intros s0 p0 mu0 sp b HS Hsupp.  
  unfold supp_mu in Hsupp. simpl in Hsupp. 
  rewrite insert_st_pair_fst_eq_insert_st in Hsupp. 
  unfold supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st. rewrite supp_insert_negbevalB.
  apply supp_insert_subst_implies_negbevalBT_eq with (sp1:= sp); try assumption.
  apply Sort_supp_if_WF_supp. 
Qed. 

Lemma bT_classify_subst: forall pd0 pd1 b, 
  (mu pd0) <> nil ->
  is_supp_subset (supp_mu (mu pd0)) (supp_mu (mu pd1)) = true -> 
  b_supp_classify b pd1 = All_True ->
  b_supp_classify b pd0 = All_True.
Proof.
  intros. rename H1 into Hb. unfold b_supp_classify in *. simpl. 
  destruct pd0 as [dom0 mu0 HPD0]. destruct pd1 as [dom1 mu1 HPD1]. simpl in *.
  destruct (mu0) as [|(s0,p0) mu0']; simpl in *; try contradiction. 
  destruct (mu1) as [|(s1,p1) mu1'].
  - unfold supp_mu in H0. simpl in H0. rewrite insert_st_pair_fst_eq_insert_st in H0.
    destruct (insert_st s0 (map fst (sort_dst mu0'))) eqn: Hcontra; try discriminate.
  - destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s1, p1) :: mu1'))) eqn: HT.
    + apply supp_mu_subst_evalB with (b:= b) in H0; try assumption; try apply Sort_supp_if_WF_supp.
    rewrite H0. reflexivity.
    + destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s1, p1) :: mu1'))) eqn: HF; try discriminate. 
Qed.

Lemma bF_classify_subst: forall pd0 pd1 b, 
  (mu pd0) <> nil ->
  is_supp_subset (supp_mu (mu pd0)) (supp_mu (mu pd1)) = true -> 
  b_supp_classify b pd1 = All_False ->
  b_supp_classify b pd0 = All_False.
Proof.
  intros. rename H1 into Hb. unfold b_supp_classify in *. simpl. 
  destruct pd0 as [dom0 mu0 HPD0]. destruct pd1 as [dom1 mu1 HPD1]. simpl in *.
  destruct (mu0) as [|(s0,p0) mu0']; simpl in *; try contradiction. 
  destruct (mu1) as [|(s1,p1) mu1'].
  - unfold supp_mu in H0. simpl in H0. rewrite insert_st_pair_fst_eq_insert_st in H0.
    destruct (insert_st s0 (map fst (sort_dst mu0'))) eqn: Hcontra; try discriminate.
  - destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s1, p1) :: mu1'))) eqn: HT; try discriminate.
    destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s1, p1) :: mu1'))) eqn: HF; try discriminate.
    apply supp_mu_subst_negbevalB with (b:= b) in H0; try assumption. 
    * rewrite H0. unfold supp_mu in H0. simpl in H0. rewrite insert_st_pair_fst_eq_insert_st in H0.
      rewrite supp_insert_negbevalB in H0. apply andb_true_iff in H0. destruct H0. 
      unfold supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st.
      rewrite supp_insert_evalB. apply negb_true_iff in H0. rewrite H0. simpl. reflexivity.
    * apply Sort_supp_if_WF_supp.
Qed.

Lemma bT_classify_decom_r: forall pd pd0 pd1 b, 
  Valid_dist (mu pd) -> Valid_dist (mu pd0 + mu pd1)%dist_state -> 
  mu pd == (mu pd0 + mu pd1)%dist_state -> (mu pd0) <> nil -> 
  (dom pd == dom pd0)%domain -> (dom pd == dom pd1)%domain -> 
  b_supp_classify b pd = All_True -> 
  b_supp_classify b pd0 = All_True.
Proof. 
  intros pd pd0 pd1 b Hv Hvl Hmu0 Hnil0 Hdom0 Hdom1 Hb. 
  apply bT_classify_subst with (pd0:= pd0) in Hb; try assumption.
  assert (Heq: (supp_mu (mu pd) == supp_mu (mu pd0 + mu pd1))%supp). {
    apply dst_equiv_implies_beq_supp; try assumption. }
  apply supp_eq_implies_subset_conj in Heq. destruct Heq.
  apply supp_subset_trans with (ls1:= supp_mu (mu pd0 + mu pd1)); 
    try apply Sort_supp_if_WF_supp; try assumption.
  assert (H': (supp_mu (mu pd0 + mu pd1) ⊆ supp_mu (mu pd0 + mu pd1))%supp) by apply supp_subset_refl.
  apply supp_mu_subset_decom_l in H'; try apply Sort_supp_if_WF_supp; try assumption.
  destruct H'. assumption.
Qed.
Lemma bF_classify_decom_r: forall pd pd0 pd1 b, 
  Valid_dist (mu pd) -> Valid_dist (mu pd0 + mu pd1)%dist_state -> 
  mu pd == (mu pd0 + mu pd1)%dist_state -> (mu pd0) <> nil -> 
  (dom pd == dom pd0)%domain -> (dom pd == dom pd1)%domain -> 
  b_supp_classify b pd = All_False -> 
  b_supp_classify b pd0 = All_False.
Proof. 
  intros pd pd0 pd1 b Hv Hvl Hmu0 Hnil0 Hdom0 Hdom1 Hb. 
  apply bF_classify_subst with (pd0:= pd0) in Hb; try assumption.
  assert (Heq: (supp_mu (mu pd) == supp_mu (mu pd0 + mu pd1))%supp). {
    apply dst_equiv_implies_beq_supp; try assumption. }
  apply supp_eq_implies_subset_conj in Heq. destruct Heq.
  apply supp_subset_trans with (ls1:= supp_mu (mu pd0 + mu pd1)); 
    try apply Sort_supp_if_WF_supp; try assumption.
  assert (H': (supp_mu (mu pd0 + mu pd1) ⊆ supp_mu (mu pd0 + mu pd1))%supp) by apply supp_subset_refl.
  apply supp_mu_subset_decom_l in H'; try apply Sort_supp_if_WF_supp; try assumption.
  destruct H'. assumption.
Qed.


Lemma evalB_contra: forall b s mu, 
  evalB_st b s = false -> 
  is_in_supp s (supp_mu mu) = true ->
  forallb (fun s0 : local_st => evalB_st b s0) (supp_mu mu) = false.
Proof.
  intros b s mu Hs Hsupp.
  induction mu as [|(s0,p0) mu' IH]; simpl in *; try discriminate.
  unfold supp_mu in Hsupp. simpl in Hsupp. 
  rewrite insert_st_pair_fst_eq_insert_st in Hsupp.
  rewrite in_supp_insert_eq in Hsupp. apply orb_true_iff in Hsupp. 
  destruct Hsupp.
  - unfold supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st.
    rewrite supp_insert_evalB. 
    apply st_eq_implies_evalB with (b:= b) in H. 
    rewrite <- H. rewrite Hs. simpl. reflexivity.
  - unfold supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st.
    rewrite supp_insert_evalB. 
    apply IH in H. unfold supp_mu in H.
    rewrite H. apply andb_false_r.
Qed.
