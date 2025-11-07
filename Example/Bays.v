From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qround.
From Stdlib Require Import QArith.QArith_base.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import List.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals Psatz.
From Stdlib Require Import Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ClassicalChoice.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lra.
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
Require Import Library.DistState.Partial.
Require Import Library.PIMP.Syntax.
Require Import Library.PIMP.EvalProps.
Require Import Library.PIMP.Semantics.
Require Import Library.Assertion.Asserts.
Require Import Library.Assertion.SemProp.
Require Import Rule.HoareLogic.

Open Scope state_scope.
Open Scope imp_scope.

Example XP := 0%nat.
Example XD := 1%nat.
Example XG := 2%nat.
Example XM := 3%nat.

Definition D_da := [(Aco 0, 6/10);(Aco 1, (1 - 6/10)%R)].
Lemma Dda_bounds : 0 < 6/10 < 1. Proof. lra. Qed.
Definition D_Vda : valid_dist_aexp := 
    exist _ D_da (valid_da_of_two (Aco 0) (Aco 1) (6/10) Dda_bounds).

Definition P_da := [(Aco 0, 7/10);(Aco 1, (1 - 7/10)%R)].
Lemma P_da_bounds : 0 < 7/10 < 1. Proof. lra. Qed.
Definition P_Vda : valid_dist_aexp := 
    exist _ P_da (valid_da_of_two (Aco 0) (Aco 1) (7/10) P_da_bounds).

Definition G_da_00 := [(Aco 0, 95/100);(Aco 1, (1 - 95/100)%R)].
Lemma Gda_00_bounds : 0 < 95/100 < 1. Proof. lra. Qed.
Definition G_Vda_00 : valid_dist_aexp := 
    exist _ G_da_00 (valid_da_of_two (Aco 0) (Aco 1) (95/100) Gda_00_bounds).

Definition G_da_11 := [(Aco 0, 5/100);(Aco 1, (1 - 5/100)%R)].
Lemma Gda_11_bounds : 0 < 5/100 < 1. Proof. lra. Qed.
Definition G_Vda_11 : valid_dist_aexp := 
    exist _ G_da_11 (valid_da_of_two (Aco 0) (Aco 1) (5/100) Gda_11_bounds).

Definition G_da_01 := [(Aco 0, 1/2);(Aco 1, (1 - 1/2)%R)].
Lemma Gda_01_bounds : 0 < 1/2 < 1. Proof. lra. Qed.
Definition G_Vda_01 : valid_dist_aexp := 
    exist _ G_da_01 (valid_da_of_two (Aco 0) (Aco 1) (1/2) Gda_01_bounds).

Definition G_da_10 := [(Aco 0, 6/10);(Aco 1, (1 - 6/10)%R)].
Lemma Gda_10_bounds : 0 < 6/10 < 1. Proof. lra. Qed.
Definition G_Vda_10 : valid_dist_aexp := 
    exist _ G_da_10 (valid_da_of_two (Aco 0) (Aco 1) (6/10) Gda_10_bounds).

Definition M_da_0 := [(Aco 0, 9/10);(Aco 1, (1 - 9/10)%R)].
Lemma Mda_0_bounds : 0 < 9/10 < 1. Proof. lra. Qed.
Definition M_Vda_0 : valid_dist_aexp := 
    exist _ M_da_0 (valid_da_of_two (Aco 0) (Aco 1) (9/10) Mda_0_bounds).

Definition M_da_1 := [(Aco 0, 3/10);(Aco 1, (1 - 3/10)%R)].
Lemma Mda_1_bounds : 0 < 3/10 < 1. Proof. lra. Qed.
Definition M_Vda_1 : valid_dist_aexp := 
    exist _ M_da_1 (valid_da_of_two (Aco 0) (Aco 1) (3/10) Mda_1_bounds).

Open Scope formula_scope.
Definition B_XD_0: bexp:= (Beq (Ava XD) (Aco 0%Q)).
Definition B_XP_0: bexp:= (Beq (Ava XP) (Aco 0%Q)).
Definition B_XD_1: bexp:= (Beq (Ava XD) (Aco 1%Q)).
Definition B_XP_1: bexp:= (Beq (Ava XP) (Aco 1%Q)).
Definition B_XG_0: bexp:= (Beq (Ava XG) (Aco 0%Q)).
Definition B_XG_1: bexp:= (Beq (Ava XG) (Aco 1%Q)).

Definition DA_XP: winstr:= (XP ::= Aco 0%Q).
Definition RA_XD: winstr:= (XD $= D_Vda).
Definition dist_XD := (Ava XD == Aco 0) ⊕[(6/10)] (Ava XD == Aco 1).
Definition RA_XP: winstr:= (XP $= P_Vda).
Definition dist_XP := (Ava XP == Aco 0) ⊕[7/10] (Ava XP == Aco 1).
Definition RA_XG00: winstr:= (XG $= G_Vda_00).
Definition dist_XG_00:= (Ava XG == Aco 0) ⊕[95/100] (Ava XG == Aco 1).
Definition RA_XG01: winstr:= (XG $= G_Vda_01).
Definition dist_XG_01:= (Ava XG == Aco 0) ⊕[1/2] (Ava XG == Aco 1).
Definition RA_XG10: winstr:= (XG $= G_Vda_10).
Definition dist_XG_10:= (Ava XG == Aco 0) ⊕[6/10] (Ava XG == Aco 1).
Definition RA_XG11: winstr:= (XG $= G_Vda_11).
Definition dist_XG_11:= (Ava XG == Aco 0) ⊕[5/100] (Ava XG == Aco 1).

Definition RA_XM0: winstr:= (XM $= M_Vda_0).
Definition dist_XM0:= (Ava XM == Aco 0) ⊕[9/10] (Ava XM == Aco 1).
Definition RA_XM1: winstr:= (XM $= M_Vda_1).
Definition dist_XM1:= (Ava XM == Aco 0) ⊕[3/10] (Ava XM == Aco 1).

Definition IF_D0_P:= If (B_XP_0) (RA_XG00) (RA_XG01).
Definition IF_D1_P:= If (B_XP_0) (RA_XG10) (RA_XG11).
Definition IF_D:= If B_XD_0 IF_D0_P IF_D1_P.

Definition IF_G:= If (B_XG_0)%imp (RA_XM0) (RA_XM1).
Definition body := RA_XD;; RA_XP;; IF_D;; IF_G.
Definition BN_Prog:= DA_XP;; While (B_XP_0) body.

Lemma RA_XG00_correct: {{[[⊤]]}} RA_XG00 {{[[dist_XG_00]]}}.
Proof. 
  apply hoare_consequence_pre with (P':= (
              ([[Pdeter (Dpred (Ava XG = Aco 0))]] [XG |-> Aco 0]) /\ 
              ([[Pdeter (Dpred (Ava XG = Aco 1))]] [XG |-> Aco 1]))%assertion). 
      * unfold RA_XG00. unfold G_Vda_00,G_da_00. apply hoare_Rasgn.
        apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try lra.
      * apply assert_trans with (R:= [[(Pdeter (Dpred Btrue)) ∧ ⊤]]); 
        try apply Conj_True; try apply WD_Pdeter; try apply WD_Dpred.
        split; try apply Pdeter_always_holds.
Qed.  
Lemma RA_XG01_correct: {{[[⊤]]}} RA_XG01 {{[[dist_XG_01]]}}.
Proof. 
  unfold RA_XG01. 
  apply hoare_consequence_pre with (P':= (
              ([[Pdeter (Dpred (Ava XG = Aco 0))]] [XG |-> Aco 0]) /\ 
              ([[Pdeter (Dpred (Ava XG = Aco 1))]] [XG |-> Aco 1]))%assertion). 
      * unfold G_Vda_01,G_da_01. apply hoare_Rasgn.
        apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try lra.
      * apply assert_trans with (R:= [[(Pdeter (Dpred Btrue)) ∧ ⊤]]); 
        try apply Conj_True; try apply WD_Pdeter; try apply WD_Dpred.
        split; try apply Pdeter_always_holds.
Qed.  
Lemma RA_XG10_correct: {{[[⊤]]}} RA_XG10 {{[[dist_XG_10]]}}.
Proof. 
  unfold RA_XG10. 
  apply hoare_consequence_pre with (P':= (
              ([[Pdeter (Dpred (Ava XG = Aco 0))]] [XG |-> Aco 0]) /\ 
              ([[Pdeter (Dpred (Ava XG = Aco 1))]] [XG |-> Aco 1]))%assertion). 
      * unfold G_Vda_10,G_da_10. apply hoare_Rasgn.
        apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try lra.
      * apply assert_trans with (R:= [[(Pdeter (Dpred Btrue)) ∧ ⊤]]); 
        try apply Conj_True; try apply WD_Pdeter; try apply WD_Dpred.
        split; try apply Pdeter_always_holds.
Qed.
Lemma RA_XG11_correct: {{[[⊤]]}} RA_XG11 {{[[dist_XG_11]]}}.
Proof. 
  unfold RA_XG11. 
  apply hoare_consequence_pre with (P':= (
              ([[Pdeter (Dpred (Ava XG = Aco 0))]] [XG |-> Aco 0]) /\ 
              ([[Pdeter (Dpred (Ava XG = Aco 1))]] [XG |-> Aco 1]))%assertion). 
      * unfold G_Vda_01,G_da_01. apply hoare_Rasgn.
        apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try lra.
      * apply assert_trans with (R:= [[(Pdeter (Dpred Btrue)) ∧ ⊤]]); 
        try apply Conj_True; try apply WD_Pdeter; try apply WD_Dpred.
        split; try apply Pdeter_always_holds.
Qed.

Definition dist_XG_with_dP_under_D0:= (dist_XG_00 ∧ (Ava XP == Aco 0)) ⊕[ 7 / 10] (dist_XG_01 ∧ (~ B_XP_0)).
Lemma IF_D0_P_correct: {{[[dist_XP]]}} 
               IF_D0_P {{[[dist_XG_with_dP_under_D0]]}}.
Proof. 
  unfold IF_D0_P. 
  apply hoare_consequence_pre with (P':= [[ (⊤ ∧ (Ava XP == Aco 0)) ⊕[ 7 / 10] (⊤ ∧ (~ B_XP_0))]]).
  - eapply hoare_cond.  
    + apply WD_Pplus; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred. lra. 
    + apply WD_Pplus; try apply WD_Pand; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try lra. 
    + unfold B_XP_0. apply hoare_Frame. 
      * apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred.
      * apply WD_Pand; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred. lra. 
      * simpl. reflexivity.
      * apply RA_XG00_correct.
    + unfold B_XP_0. apply hoare_Frame. 
      * apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred.
      * apply WD_Pand; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred. lra. 
      * simpl. reflexivity.
      * apply RA_XG01_correct. 
  - apply OCon_Pplus; try lra; try apply Conj_True; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred. 
    unfold assert_implies. intros. destruct H1. split. 
    + constructor; simpl; try reflexivity. intros. split; try reflexivity; try apply I.
    + split; try assumption. intros. apply H2 in H3. destruct H3. split; try assumption. 
      destruct (evalB_st (Ava XP = Aco 1) st) eqn: HXD; try contradiction.
      unfold B_XP_0. apply evalB_X_01 with (n:= 0%Q) in HXD; try lra. 
      * apply evalB_Bnot_true_iff in HXD. rewrite HXD. apply I.
      * try compute. reflexivity.
Qed. 

Definition dist_XG_with_dP_under_D1:= (dist_XG_10 ∧ (Ava XP == Aco 0)) ⊕[ 7 / 10] (dist_XG_11 ∧ (~ B_XP_0)).
Lemma IF_D1_P_correct: {{[[dist_XP]]}} 
               IF_D1_P {{[[dist_XG_with_dP_under_D1]]}}.
Proof. 
  unfold IF_D1_P. 
  apply hoare_consequence_pre with (P':= [[ (⊤ ∧ (Ava XP == Aco 0)) ⊕[ 7 / 10] (⊤ ∧ (~ B_XP_0))]]).
  - eapply hoare_cond. 
    + apply WD_Pplus; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred. lra. 
    + apply WD_Pplus; try apply WD_Pand; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; lra.
    + unfold B_XP_0. apply hoare_Frame. 
      * apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred.
      * apply WD_Pand; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred. lra. 
      * simpl. reflexivity.
      * apply RA_XG10_correct.
    + unfold RA_XG11. apply hoare_Frame. 
      * apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred.
      * apply WD_Pand; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred. lra. 
      * simpl. reflexivity.
      * apply RA_XG11_correct.
  - apply OCon_Pplus; try lra; try apply Conj_True; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred. 
    unfold assert_implies. intros. destruct H1. split. 
    + constructor; simpl; try reflexivity. intros. split; try reflexivity; try apply I.
    + split; try assumption. intros. apply H2 in H3. destruct H3. split; try assumption. 
      destruct (evalB_st (Ava XP = Aco 1) st) eqn: HXD; try contradiction.
      unfold B_XP_0. apply evalB_X_01 with (n:= 0%Q) in HXD; try lra. 
      * apply evalB_Bnot_true_iff in HXD. rewrite HXD. apply I.
      * try compute. reflexivity.
Qed. 

Lemma IF_D_correct: {{[[dist_XP ∧ (Ava XD == Aco 0) ⊕[ 6 / 10] dist_XP ∧ (~ B_XD_0)]]}}  
               IF_D {{[[(dist_XG_with_dP_under_D0 ∧ (Ava XD == Aco 0)) ⊕[ 6 / 10] 
                        (dist_XG_with_dP_under_D1 ∧ (~ B_XD_0))]]}}.
Proof. 
  unfold IF_D. eapply hoare_cond. 
  - apply WD_Pplus; try apply WD_Pplus; try apply WD_Pand; try apply WD_Odot;
      try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try lra. 
  - apply WD_Pplus; try apply WD_Pand; repeat try apply WD_Pplus; repeat try apply WD_Pand; 
      repeat try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try lra; simpl.
  - 
  apply hoare_Frame; try apply IF_D0_P_correct. 
    + apply WD_Pand; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred. lra.
    + apply WD_Pand; try unfold dist_XG_with_dP_under_D0; try apply WD_Pplus; try apply WD_Pand; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try lra; simpl.
    + simpl. reflexivity.
  - apply hoare_Frame; try apply IF_D1_P_correct. 
    + apply WD_Pand; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred. lra.
    + apply WD_Pand; try unfold dist_XG_with_dP_under_D0; try apply WD_Pplus; try apply WD_Pand; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try lra; simpl.
    + simpl. reflexivity.
Qed.
(************************************************************************)
Definition XD0P0 := (Ava XD == Aco 0) ∧ (Ava XP == Aco 0).
Definition XD0P1 := (Ava XD == Aco 0) ∧ (~ B_XP_0).
Definition XD1P0 := (~ B_XD_0) ∧ (Ava XP == Aco 0).
Definition XD1P1 := (~ B_XD_0) ∧ (~ B_XP_0).

Lemma After_D_implies_dG_with_DP: (*Take D and P and put them together*)
  [[(dist_XG_with_dP_under_D0 ∧ (Ava XD == Aco 0)) ⊕[ 6 / 10] (dist_XG_with_dP_under_D1 ∧ (~ B_XD_0))]] ->> 
  [[((dist_XG_00 ∧ XD0P0) ⊕[ 7 / 10] (dist_XG_01 ∧ XD0P1)) ⊕[ 6 / 10] 
    ((dist_XG_10 ∧ XD1P0) ⊕[ 7 / 10] (dist_XG_11 ∧ XD1P1))]].
Proof. 
  unfold assert_implies. intros. 
  destruct H1; try lra. destruct H1. destruct H2. destruct H2. intuition.
  left. split; try lra. exists x, x0. intuition. 
  - destruct H7. destruct H7; try lra. destruct H7. destruct H13 as [x00 H']. destruct H' as [x01 H']. intuition.
    destruct H18. destruct H19. 
    left. split; try lra. exists x00, x01. intuition. 
    + split; try assumption. split; try assumption. 
      apply df_add_sem_decom with (pd0:= x00) (pd1:= x01) (p1:= 7/10) in H11; intuition.
    + split; try assumption. split; try assumption. 
      apply df_add_sem_decom with (pd0:= x00) (pd1:= x01) (p1:= 7/10) in H11; intuition.
  - destruct H8. destruct H8; try lra. destruct H8. destruct H13 as [x00 H']. destruct H' as [x01 H']. intuition.
    destruct H18. destruct H19. 
    left. split; try lra. exists x00, x01. intuition. 
    + split; try assumption. split; try assumption.
      apply df_add_sem_decom with (pd0:= x00) (pd1:= x01) (p1:= 7/10) in H11; intuition.
    + split; try assumption. split; try assumption. 
      apply df_add_sem_decom with (pd0:= x00) (pd1:= x01) (p1:= 7/10) in H11; intuition. 
Qed.

Definition dist_D0dPG0 := XD0P0 ⊕[665/815] XD0P1.
Definition dist_D0dPG1 := XD0P0 ⊕[35/185] XD0P1.

Definition dist_D0dP_with_dG:= (dist_D0dPG0 ∧ (Ava XG == Aco 0)) ⊕[815/1000] (dist_D0dPG1 ∧ (~ B_XG_0)).
Lemma L_dist_XG_under_D_command: 
          [[((dist_XG_00 ∧ XD0P0) ⊕[ 7 / 10] (dist_XG_01 ∧ XD0P1))]] ->> [[dist_D0dP_with_dG]].
Proof. 
  unfold assert_implies. intros. destruct H1; try lra. 
  destruct H1. destruct H2 as [x0 H2]. destruct H2 as [x1 H2]. intuition.  
  destruct H7. destruct H8. destruct H7; destruct H8; try lra. 
  destruct H7. destruct H14 as [x00 H']. destruct H' as [x01 H']. intuition.  
  destruct H18 as [x10 H']. destruct H' as [x11 H']. intuition. 
  left. split; try lra. 
  assert (Hdom_0: (dom x00 == dom x10)%domain). {
    apply dom_equiv_trans with (l1:= dom x0); try assumption.
    apply dom_equiv_trans with (l1:= dom pd); try assumption.
    apply dom_equiv_sym.
    apply dom_equiv_trans with (l1:= dom x1); try assumption. }
  assert (Hdom_1: (dom x01 == dom x11)%domain). {
    apply dom_equiv_trans with (l1:= dom x0); try assumption.
    apply dom_equiv_trans with (l1:= dom pd); try assumption.
    apply dom_equiv_sym.
    apply dom_equiv_trans with (l1:= dom x1); try assumption. }
  pose (pd_tmp0:= pd_add (cofe_pd x00 (665/815)%R) (cofe_pd x10 (150/815)%R) Hdom_0).
  pose (pd_tmp1:= pd_add (cofe_pd x01 (35/185)%R) (cofe_pd x11 (150/185)%R) Hdom_1).
  exists pd_tmp0, pd_tmp1. 
  split. { simpl. apply Valid_linear; try assumption; lra. }
  split. { simpl. apply Valid_linear; try assumption; lra. }
  split. { simpl. apply dom_equiv_trans with (l1:= dom x0); try assumption. } 
  split. { simpl. apply dom_equiv_trans with (l1:= dom x0); try assumption. } 
  split. { split. 
    - left. split; try lra. exists x00, x10. intuition. 
      + simpl. apply dom_equiv_refl. 
      + simpl. apply dom_equiv_sym. assumption. 
      + destruct H11. split. 
        * apply df_add_sem_decom with (pd0:= x00) (pd1:= x01) (p1:= 95/100) in H11; intuition.
        * apply df_add_sem_decom with (pd0:= x00) (pd1:= x01) (p1:= 95/100) in H33; intuition.
      + destruct H13. split. 
        * apply df_add_sem_decom with (pd0:= x10) (pd1:= x11) (p1:= 1/2) in H13; intuition.
        * apply df_add_sem_decom with (pd0:= x10) (pd1:= x11) (p1:= 1/2) in H33; intuition.
      + simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H23. rewrite H9. rewrite H31. rewrite H10. rewrite <- Rmult_plus_distr_r. 
        rewrite <- Rmult_1_l at 1. apply Rmult_eq_compat_r. lra.
      + simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H23. rewrite H9. rewrite H31. rewrite H10. rewrite <- Rmult_plus_distr_r. 
        rewrite <- Rmult_1_l at 1. apply Rmult_eq_compat_r. lra. 
      + simpl. replace (1 - 665 / 815)%R with (150 / 815)%R by lra. apply dst_equiv_refl.
    - apply df_sem_linear_add with (pd0:= x00) (pd1:= x10) (p1:= (665 / 815)) (p2:= (150 / 815)); try assumption; try lra.  
      + apply Valid_linear; try assumption; lra.
      + simpl. apply dom_equiv_refl. 
      + simpl. apply dom_equiv_sym. assumption.
      + simpl. apply dst_equiv_refl. }
  split. { split. 
    - left. split; try lra. exists x01, x11. intuition. 
      + simpl. apply dom_equiv_refl. 
      + simpl. apply dom_equiv_sym. assumption. 
      + destruct H11. split. 
        * apply df_add_sem_decom with (pd0:= x00) (pd1:= x01) (p1:= 95/100) in H11; intuition.
        * apply df_add_sem_decom with (pd0:= x00) (pd1:= x01) (p1:= 95/100) in H33; intuition.
      + destruct H13. split. 
        * apply df_add_sem_decom with (pd0:= x10) (pd1:= x11) (p1:= 1/2) in H13; intuition.
        * apply df_add_sem_decom with (pd0:= x10) (pd1:= x11) (p1:= 1/2) in H33; intuition.
      + simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H24. rewrite H9. rewrite H32. rewrite H10. rewrite <- Rmult_plus_distr_r. 
        rewrite <- Rmult_1_l at 1. apply Rmult_eq_compat_r. lra.
      + simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H24. rewrite H9. rewrite H32. rewrite H10. rewrite <- Rmult_plus_distr_r. 
        rewrite <- Rmult_1_l at 1. apply Rmult_eq_compat_r. lra. 
      + simpl. replace (1 - 35 / 185)%R with (150 / 185)%R by lra. apply dst_equiv_refl.
    - apply df_sem_linear_add with (pd0:= x01) (pd1:= x11) (p1:= (35 / 185)) (p2:= (150 / 185)); try assumption; try lra.  
      + apply Valid_linear; try assumption; lra.
      + simpl. apply dom_equiv_refl. 
      + simpl. apply dom_equiv_sym. assumption.
      + simpl. apply dst_equiv_refl.
      + apply Pdeter_implie_not with (m:= 1%Q); try assumption. compute. reflexivity.
      + apply Pdeter_implie_not with (m:= 1%Q); try assumption. compute. reflexivity.
      }
  split. { simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
    rewrite H23. rewrite H9. rewrite H31. rewrite H10. rewrite <- Rmult_plus_distr_r. 
    rewrite <- Rmult_1_l. apply Rmult_eq_compat_r. lra. }
  split. { simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
    rewrite H24. rewrite H9. rewrite H32. rewrite H10. rewrite <- Rmult_plus_distr_r. 
    rewrite <- Rmult_1_l. apply Rmult_eq_compat_r. lra. }
  simpl. replace (1 - 815 / 1000)%R with (185 / 1000)%R by lra. 
  repeat rewrite dst_mult_plus_distr_r_eq. repeat rewrite dst_mult_assoc_eq.
  replace (815 / 1000 * (665 / 815))%R with (665 / 1000)%R by lra.
  replace (815 / 1000 * (150 / 815))%R with (150 / 1000)%R by lra.
  replace (185 / 1000 * (35 / 185))%R with (35 / 1000)%R by lra.
  replace (185 / 1000 * (150 / 185))%R with (150 / 1000)%R by lra.
  apply dst_equiv_trans with (mu1:= (665 / 1000 * mu x00 + 35 / 1000 * mu x01 + 
                                      (150 / 1000 * mu x10 + 150 / 1000 * mu x11))%dist_state);
  try apply dst_add_shuffle.
  apply dst_equiv_trans with (mu1:= (7 / 10 * mu x0 + (1 - 7 / 10) * mu x1)%dist_state); try assumption.
  apply dst_add_preserves_equiv. 
  - apply dst_equiv_trans with (mu1:= (7 / 10 * (95 / 100 * mu x00 + (1 - 95 / 100) * mu x01))%dist_state).
    + apply dst_mult_preserves_equiv. assumption.  
    + rewrite dst_mult_plus_distr_r_eq. apply dst_add_preserves_equiv; rewrite dst_mult_assoc_eq. 
      * replace (7 / 10 * (95 / 100))%R with (665 / 1000)%R by lra. try apply dst_equiv_refl.
      * replace (7 / 10 * (1 - 95 / 100))%R with (35 / 1000)%R by lra. try apply dst_equiv_refl.
  - apply dst_equiv_trans with (mu1:= ((1 - 7 / 10) * (1 / 2 * mu x10 + (1 - 1 / 2) * mu x11))%dist_state).
    + apply dst_mult_preserves_equiv. assumption.  
    + rewrite dst_mult_plus_distr_r_eq. apply dst_add_preserves_equiv; rewrite dst_mult_assoc_eq. 
      * replace ((1 - 7 / 10) * (1 / 2))%R with (150 / 1000)%R by lra. try apply dst_equiv_refl.
      * replace ((1 - 7 / 10) * (1 - 1 / 2))%R with (150 / 1000)%R by lra. try apply dst_equiv_refl. 
Qed. 

Definition dist_D1dPG0 := XD1P0 ⊕[420/435] XD1P1.
Definition dist_D1dPG1 := XD1P0 ⊕[280/565] XD1P1.

Definition dist_D1dP_with_dG:= (dist_D1dPG0 ∧ (Ava XG == Aco 0)) ⊕[435/1000] (dist_D1dPG1 ∧ (~ B_XG_0)).
Lemma R_dist_XG_under_D_command: 
          [[((dist_XG_10 ∧ XD1P0) ⊕[ 7 / 10] (dist_XG_11 ∧ XD1P1))]] ->> [[dist_D1dP_with_dG]].
Proof. 
  unfold assert_implies. intros. destruct H1; try contradiction; try lra.
  destruct H1. destruct H2 as [x0 H2]. destruct H2 as [x1 H2]. intuition.  
  destruct H7. destruct H7; try contradiction; try lra. 
  destruct H7. destruct H13 as [x00 H13]. destruct H13 as [x01 H13]. intuition.  
  destruct H8. destruct H8; try contradiction; try lra. 
  destruct H8. destruct H24 as [x10 H24]. destruct H24 as [x11 H24]. intuition. 
  left. split; try lra. 
  assert (Hdom_0: (dom x00 == dom x10)%domain). {
    apply dom_equiv_trans with (l1:= dom x0); try assumption.
    apply dom_equiv_trans with (l1:= dom pd); try assumption.
    apply dom_equiv_sym.
    apply dom_equiv_trans with (l1:= dom x1); try assumption. }
  assert (Hdom_1: (dom x01 == dom x11)%domain). {
    apply dom_equiv_trans with (l1:= dom x0); try assumption.
    apply dom_equiv_trans with (l1:= dom pd); try assumption.
    apply dom_equiv_sym.
    apply dom_equiv_trans with (l1:= dom x1); try assumption. }
  pose (pd_tmp0:= pd_add (cofe_pd x00 (420/435)%R) (cofe_pd x10 (15/435)%R) Hdom_0).
  pose (pd_tmp1:= pd_add (cofe_pd x01 (280/565)%R) (cofe_pd x11 (285/565)%R) Hdom_1).
  exists pd_tmp0, pd_tmp1. 
  split. { simpl. apply Valid_linear; try assumption; lra. }
  split. { simpl. apply Valid_linear; try assumption; lra. }
  split. { simpl. apply dom_equiv_trans with (l1:= dom x0); try assumption. } 
  split. { simpl. apply dom_equiv_trans with (l1:= dom x0); try assumption. } 
  split. { split. 
    - left. split; try lra.
      exists x00, x10. intuition. 
      + simpl. apply dom_equiv_refl. 
      + simpl. apply dom_equiv_sym. assumption. 
      + destruct H11. split. 
        * apply df_add_sem_decom with (pd0:= x00) (pd1:= x01) (p1:= 6/10) in H11; intuition.
        * apply df_add_sem_decom with (pd0:= x00) (pd1:= x01) (p1:= 6/10) in H33; intuition.
      + destruct H22. split.
        * apply df_add_sem_decom with (pd0:= x10) (pd1:= x11) (p1:= 5/100) in H22; intuition.
        * apply df_add_sem_decom with (pd0:= x10) (pd1:= x11) (p1:= 5/100) in H33; intuition.
      + simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H20. rewrite H9. rewrite H31. rewrite H10. rewrite <- Rmult_plus_distr_r. 
        rewrite <- Rmult_1_l at 1. apply Rmult_eq_compat_r. lra.
      + simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H20. rewrite H9. rewrite H31. rewrite H10. rewrite <- Rmult_plus_distr_r. 
        rewrite <- Rmult_1_l at 1. apply Rmult_eq_compat_r. lra. 
      + simpl. replace (1 - 420 / 435)%R with (15 / 435)%R by lra. apply dst_equiv_refl.
    - apply df_sem_linear_add with (pd0:= x00) (pd1:= x10) (p1:= (420 / 435)) (p2:= (15 / 435)); try assumption; try lra.  
      + apply Valid_linear; try assumption; lra.
      + simpl. apply dom_equiv_refl. 
      + simpl. apply dom_equiv_sym. assumption.
      + simpl. apply dst_equiv_refl. }
  split. { split. 
    - left. split; try lra. exists x01, x11. intuition. 
      + simpl. apply dom_equiv_refl. 
      + simpl. apply dom_equiv_sym. assumption. 
      + destruct H11. split. 
        * apply df_add_sem_decom with (pd0:= x00) (pd1:= x01) (p1:= 6/10) in H11; intuition.
        * apply df_add_sem_decom with (pd0:= x00) (pd1:= x01) (p1:= 6/10) in H33; intuition.
      + destruct H22. split.
        * apply df_add_sem_decom with (pd0:= x10) (pd1:= x11) (p1:= 5/100) in H22; intuition.
        * apply df_add_sem_decom with (pd0:= x10) (pd1:= x11) (p1:= 5/100) in H33; intuition.
      + simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H21. rewrite H9. rewrite H32. rewrite H10. rewrite <- Rmult_plus_distr_r. 
        rewrite <- Rmult_1_l at 1. apply Rmult_eq_compat_r. lra.
      + simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H21. rewrite H9. rewrite H32. rewrite H10. rewrite <- Rmult_plus_distr_r. 
        rewrite <- Rmult_1_l at 1. apply Rmult_eq_compat_r. lra. 
      + simpl. replace (1 - 280 / 565)%R with (285 / 565)%R by lra. apply dst_equiv_refl.
    - apply df_sem_linear_add with (pd0:= x01) (pd1:= x11) (p1:= (280 / 565)) (p2:= (285 / 565)); try assumption; try lra.  
      + apply Valid_linear; try assumption; lra.
      + simpl. apply dom_equiv_refl. 
      + simpl. apply dom_equiv_sym. assumption.
      + simpl. apply dst_equiv_refl.
      + apply Pdeter_implie_not with (m:= 1%Q); try assumption. compute. reflexivity. 
      + apply Pdeter_implie_not with (m:= 1%Q); try assumption. compute. reflexivity. }
  split. { simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
    rewrite H20. rewrite H9. rewrite H31. rewrite H10. rewrite <- Rmult_plus_distr_r. 
    rewrite <- Rmult_1_l. apply Rmult_eq_compat_r. lra. }
  split. { simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
    rewrite H21. rewrite H9. rewrite H32. rewrite H10. rewrite <- Rmult_plus_distr_r. 
    rewrite <- Rmult_1_l. apply Rmult_eq_compat_r. lra. }
  simpl. replace (1 - 435 / 1000)%R with (565 / 1000)%R by lra. 
  repeat rewrite dst_mult_plus_distr_r_eq. repeat rewrite dst_mult_assoc_eq.
  replace (435 / 1000 * (420 / 435))%R with (420 / 1000)%R by lra.
  replace (435 / 1000 * (15 / 435))%R with (15 / 1000)%R by lra.
  replace (565 / 1000 * (280 / 565))%R with (280 / 1000)%R by lra.
  replace (565 / 1000 * (285 / 565))%R with (285 / 1000)%R by lra.
  apply dst_equiv_trans with (mu1:= (420 / 1000 * mu x00 + 280 / 1000 * mu x01 + 
                                      (15 / 1000 * mu x10 + 285 / 1000 * mu x11))%dist_state);
  try apply dst_add_shuffle.
  apply dst_equiv_trans with (mu1:= (7 / 10 * mu x0 + (1 - 7 / 10) * mu x1)%dist_state); try assumption.
        apply dst_add_preserves_equiv. 
        * apply dst_equiv_trans with (mu1:= (7 / 10 * (6 / 10 * mu x00 + (1 - 6 / 10) * mu x01))%dist_state).
        ** apply dst_mult_preserves_equiv. assumption.  
        ** rewrite dst_mult_plus_distr_r_eq. apply dst_add_preserves_equiv; rewrite dst_mult_assoc_eq. 
        -- replace (7 / 10 * (6 / 10))%R with (420 / 1000)%R by lra. try apply dst_equiv_refl.
        -- replace (7 / 10 * (1 - 6 / 10))%R with (280 / 1000)%R by lra. try apply dst_equiv_refl.
        * apply dst_equiv_trans with (mu1:= ((1 - 7 / 10) * (5 / 100 * mu x10 + (1 - 5 / 100) * mu x11))%dist_state).
        ** apply dst_mult_preserves_equiv. assumption.  
        ** rewrite dst_mult_plus_distr_r_eq. apply dst_add_preserves_equiv; rewrite dst_mult_assoc_eq. 
        -- replace ((1 - 7 / 10) * (5 / 100))%R with (15 / 1000)%R by lra. try apply dst_equiv_refl.
        -- replace ((1 - 7 / 10) * (1 - 5 / 100))%R with (285 / 1000)%R by lra. try apply dst_equiv_refl. 
Qed. 

Lemma distG_under_DP_implies_distDP_with_dG: 
  [[((dist_XG_00 ∧ XD0P0) ⊕[ 7 / 10] (dist_XG_01 ∧ XD0P1)) ⊕[ 6 / 10] 
    ((dist_XG_10 ∧ XD1P0) ⊕[ 7 / 10] (dist_XG_11 ∧ XD1P1))]] ->>
  [[((dist_D0dPG0 ⊕[489/663] dist_D1dPG0) ∧ (Ava XG == Aco 0)) ⊕[ 663 / 1000] 
    ((dist_D0dPG1 ⊕[111/337] dist_D1dPG1) ∧ (~ B_XG_0))]].
Proof. 
  apply assert_trans with (R:= [[dist_D0dP_with_dG ⊕[ 6 / 10] dist_D1dP_with_dG]]).
  - apply OCon_Pplus; try lra; try apply L_dist_XG_under_D_command; try apply R_dist_XG_under_D_command.
  - unfold assert_implies. intros. destruct H1; try contradiction; try lra.
    destruct H1. destruct H2 as [x0 H2]. destruct H2 as [x1 H2]. intuition.  
    destruct H7; destruct H8; try contradiction; try lra.  
    destruct H7. destruct H11 as [x0dPG0 H']. destruct H' as [x0dPG1 H']. intuition.
    destruct H16 as [x1dPG0 H']. destruct H' as [x1dPG1 H']. intuition.
    destruct H19 as [dP1 Hx0dPG0]. destruct H20 as [dP2 Hx0dPG1]. 
    destruct H27 as [dP3 Hx1dPG0]. destruct H28 as [dP4 Hx1dPG1]. 
    left. split; try lra.
    assert (Hdom_0: (dom x0dPG0 == dom x1dPG0)%domain). {
      apply dom_equiv_trans with (l1:= dom x0); try assumption.
      apply dom_equiv_trans with (l1:= dom pd); try assumption.
      apply dom_equiv_sym.
      apply dom_equiv_trans with (l1:= dom x1); try assumption. }
    assert (Hdom_1: (dom x0dPG1 == dom x1dPG1)%domain). {
      apply dom_equiv_trans with (l1:= dom x0); try assumption.
      apply dom_equiv_trans with (l1:= dom pd); try assumption.
      apply dom_equiv_sym.
      apply dom_equiv_trans with (l1:= dom x1); try assumption. }
    pose (pd_tmp0:= pd_add (cofe_pd x0dPG0 (489 / 663)%R) (cofe_pd x1dPG0 (174 / 663)%R) Hdom_0).
    pose (pd_tmp1:= pd_add (cofe_pd x0dPG1 (111 / 337)%R) (cofe_pd x1dPG1 (226 / 337)%R) Hdom_1).
    exists pd_tmp0, pd_tmp1. 
    split. { simpl. apply Valid_linear; try assumption; try lra. }
    split. { simpl. apply Valid_linear; try assumption; try lra. }
    split. { simpl. apply dom_equiv_trans with (l1:= dom x0); try assumption. } 
    split. { simpl. apply dom_equiv_trans with (l1:= dom x0); try assumption. } 
    split. { split. 
      * left. split; try lra. 
        exists x0dPG0, x1dPG0. intuition. 
        + simpl. apply dom_equiv_refl.
        + simpl. apply dom_equiv_sym. assumption.
        + simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
          rewrite H21. rewrite H29. rewrite H9. rewrite H10. rewrite <- Rmult_plus_distr_r.
          rewrite <- Rmult_1_l at 1. apply Rmult_eq_compat_r. lra.
        + simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
          rewrite H21. rewrite H29. rewrite H9. rewrite H10. rewrite <- Rmult_plus_distr_r.
          rewrite <- Rmult_1_l at 1. apply Rmult_eq_compat_r. lra.
        + simpl. replace (1 - 489 / 663)%R with (174 / 663)%R by lra. apply dst_equiv_refl.
      * apply df_sem_linear_add with (pd0:= x0dPG0) (pd1:= x1dPG0) (p1:= (489 / 663)) (p2:= (174 / 663 )); try assumption; try lra. 
        + apply Valid_linear; try assumption; lra. 
        + simpl. apply dom_equiv_refl.
        + simpl. apply dom_equiv_sym. assumption.
        + simpl. apply dst_equiv_refl. }
    split. { split. 
      * left. split; try lra.
        exists x0dPG1, x1dPG1. intuition. 
        + simpl. apply dom_equiv_refl.
        + simpl. apply dom_equiv_sym. assumption.
        + simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
          rewrite H22. rewrite H30. rewrite H9. rewrite H10. rewrite <- Rmult_plus_distr_r.
          rewrite <- Rmult_1_l at 1. apply Rmult_eq_compat_r. lra.
        + simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
          rewrite H22. rewrite H30. rewrite H9. rewrite H10. rewrite <- Rmult_plus_distr_r.
          rewrite <- Rmult_1_l at 1. apply Rmult_eq_compat_r. lra.
        + simpl. replace (1 - 111 / 337)%R with (226 / 337)%R by lra. apply dst_equiv_refl.
      * apply df_sem_linear_add with (pd0:= x0dPG1) (pd1:= x1dPG1) (p1:= (111 / 337)) (p2:= (226 / 337)); try assumption; try lra. 
        -- apply Valid_linear; try assumption; lra.
        -- simpl. apply dom_equiv_refl.
        -- simpl. apply dom_equiv_sym. assumption.
        -- simpl. apply dst_equiv_refl.
    }
    split. { simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
      rewrite H21. rewrite H9. rewrite H29. rewrite H10. rewrite <- Rmult_plus_distr_r. 
      rewrite <- Rmult_1_l. apply Rmult_eq_compat_r. lra. }
    split. { simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
      rewrite H22. rewrite H30. rewrite H9. rewrite H10. rewrite <- Rmult_plus_distr_r. 
      rewrite <- Rmult_1_l. apply Rmult_eq_compat_r. lra. }
    simpl. replace (1 - 663 / 1000)%R with (337 / 1000)%R by lra. 
    repeat rewrite dst_mult_plus_distr_r_eq. repeat rewrite dst_mult_assoc_eq.
    replace (663 / 1000 * (489 / 663))%R with (489 / 1000)%R by lra.
    replace (663 / 1000 * (174 / 663))%R with (174 / 1000)%R by lra.
    replace (337 / 1000 * (111 / 337))%R with (111 / 1000)%R by lra.
    replace (337 / 1000 * (226 / 337))%R with (226 / 1000)%R by lra.
    apply dst_equiv_trans with (mu1:= (489 / 1000 * mu x0dPG0 + 111 / 1000 * mu x0dPG1 + (174 / 1000 * mu x1dPG0 + 226 / 1000 * mu x1dPG1))%dist_state);
      try apply dst_add_shuffle.
    apply dst_equiv_trans with (mu1:= (6 / 10 * mu x0 + (1 - 6 / 10) * mu x1)%dist_state); try assumption.
    apply dst_add_preserves_equiv. 
      + apply dst_equiv_trans with (mu1:= (6 /10 * (815 / 1000 * mu x0dPG0 + (1 - 815 / 1000) * mu x0dPG1))%dist_state); try assumption.
        * apply dst_mult_preserves_equiv. assumption.  
        * rewrite dst_mult_plus_distr_r_eq. apply dst_add_preserves_equiv; rewrite dst_mult_assoc_eq. 
        -- replace (6 / 10 * (815 / 1000))%R with (489 / 1000)%R by lra. try apply dst_equiv_refl.
        -- replace (6 / 10 * (1 - 815 / 1000))%R with (111 / 1000)%R by lra. try apply dst_equiv_refl.
      + apply dst_equiv_trans with (mu1:= ((1 - 6 / 10) * (435 / 1000 * mu x1dPG0 + (1 - 435 / 1000) * mu x1dPG1))%dist_state).
        * apply dst_mult_preserves_equiv. assumption.  
        * rewrite dst_mult_plus_distr_r_eq. apply dst_add_preserves_equiv; rewrite dst_mult_assoc_eq. 
        -- replace ((1 - 6 / 10) * (435 / 1000))%R with (174 / 1000)%R by lra. try apply dst_equiv_refl.
        -- replace ((1 - 6 / 10) * (1 - 435 / 1000))%R with (226 / 1000)%R by lra. try apply dst_equiv_refl. 
Qed.  
(****************************************************************************************)

Lemma RA_XM0_correct: {{ [[⊤]] }} RA_XM0 {{ [[dist_XM0]] }}.
Proof. 
  unfold RA_XM0. 
  apply hoare_consequence_pre with (P':= (
              ([[Pdeter (Dpred (Ava XM = Aco 0))]] [XM |-> Aco 0]) /\ 
              ([[Pdeter (Dpred (Ava XM = Aco 1))]] [XM |-> Aco 1]))%assertion). 
      * unfold M_Vda_0, M_da_0. apply hoare_Rasgn.
        apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try lra.
      * apply assert_trans with (R:= [[(Pdeter (Dpred Btrue)) ∧ ⊤]]); 
        try apply Conj_True; try apply WD_Pdeter; try apply WD_Dpred.
        split; try apply Pdeter_always_holds.
Qed.
Lemma RA_XM1_correct: {{ [[⊤]] }} RA_XM1 {{ [[dist_XM1]] }}.
Proof. 
  unfold RA_XM1. 
  apply hoare_consequence_pre with (P':= (
              ([[Pdeter (Dpred (Ava XM = Aco 0))]] [XM |-> Aco 0]) /\ 
              ([[Pdeter (Dpred (Ava XM = Aco 1))]] [XM |-> Aco 1]))%assertion). 
      * unfold M_Vda_1, M_da_1. apply hoare_Rasgn.
        apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try lra.
      * apply assert_trans with (R:= [[(Pdeter (Dpred Btrue)) ∧ ⊤]]); 
        try apply Conj_True; try apply WD_Pdeter; try apply WD_Dpred.
        split; try apply Pdeter_always_holds.
Qed.

Lemma IF_G_correct: 
  let phi1:= (dist_D0dPG0 ⊕[489/663] dist_D1dPG0) in 
  let phi2:= (dist_D0dPG1 ⊕[111/337] dist_D1dPG1) in
  {{[[ phi1 ∧ (Ava XG == Aco 0) ⊕[ 663 / 1000] phi2 ∧ (~ B_XG_0)]]}} IF_G 
  {{[[(phi1 ⊙ dist_XM0) ∧ (Ava XG == Aco 0) ⊕[ 663 / 1000] 
      (phi2 ⊙ dist_XM1) ∧ (~ B_XG_0)]]}}.
Proof. 
  eapply hoare_cond.
  - apply WD_Pplus; repeat apply WD_Pand; repeat try apply WD_Pplus; try apply WD_Pand; 
      try apply WD_Pdeter; try apply WD_Dpred; try lra.
  - apply WD_Pplus; try apply WD_Pand; try apply WD_Odot; repeat apply WD_Pplus; 
      try apply WD_Pand; try apply WD_Pand; try apply WD_Pplus; try apply WD_Pand; 
        try apply WD_Pdeter; try apply WD_Dpred; try lra.
    + simpl. 
      try destruct (Rle_lt_dec (489 / 663) 0); try contradiction; try lra;
      try destruct (Rle_lt_dec (420 / 435) 0); try contradiction; try lra;
      try destruct (Rle_lt_dec 1 (420 / 435)); try contradiction; try lra;
      try destruct (Rle_lt_dec 1 (489 / 663)); try contradiction; try lra; 
      try destruct (Rle_lt_dec (665 / 815) 0); try contradiction; try lra;
      try destruct (Rle_lt_dec 1 (665 / 815)); try contradiction; try lra;
      try destruct (Rle_lt_dec (9 / 10) 0); try contradiction; try lra;
      try destruct (Rle_lt_dec 1 (9 / 10)); try contradiction; try lra; simpl; try reflexivity.
    + simpl. 
      try destruct (Rle_lt_dec (111 / 337) 0); try contradiction; try lra;
      try destruct (Rle_lt_dec (280 / 565) 0); try contradiction; try lra.
      try destruct (Rle_lt_dec 1 (111 / 337)); try contradiction; try lra;
      try destruct (Rle_lt_dec (35 / 185) 0); try contradiction; try lra;
      try destruct (Rle_lt_dec 1 (35 / 185)); try contradiction; try lra.
      try destruct (Rle_lt_dec 1 (280 / 565)); try contradiction; try lra;
      try destruct (Rle_lt_dec (3 / 10) 0); try contradiction; try lra;
      try destruct (Rle_lt_dec 1 (3 / 10)); try contradiction; try lra; simpl; try reflexivity.
  - apply hoare_Frame; try reflexivity. 
    + apply WD_Pand; repeat apply WD_Pplus; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred; try lra.
    + apply WD_Pand; try apply WD_Odot; repeat apply WD_Pplus; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred; try lra. 
      simpl. try destruct (Rle_lt_dec (489 / 663) 0); try contradiction; try lra;
      try destruct (Rle_lt_dec (420 / 435) 0); try contradiction; try lra;
      try destruct (Rle_lt_dec 1 (420 / 435)); try contradiction; try lra;
      try destruct (Rle_lt_dec 1 (489 / 663)); try contradiction; try lra; 
      try destruct (Rle_lt_dec (665 / 815) 0); try contradiction; try lra;
      try destruct (Rle_lt_dec 1 (665 / 815)); try contradiction; try lra;
      try destruct (Rle_lt_dec (9 / 10) 0); try contradiction; try lra;
      try destruct (Rle_lt_dec 1 (9 / 10)); try contradiction; try lra; simpl; try reflexivity.
    + apply hoare_consequence_pre with (P':= [[(dist_D0dPG0 ⊕[ 489 / 663] dist_D1dPG0) ⊙ ⊤]]). 
      * apply hoare_consequence with (P':= [[⊤ ⊙ (dist_D0dPG0 ⊕[ 489 / 663] dist_D1dPG0)]])
          (Q':=[[dist_XM0 ⊙ (dist_D0dPG0 ⊕[ 489 / 663] dist_D1dPG0)]]); try apply OdotC. 
        apply hoare_OFrame; try reflexivity; try apply RA_XM0_correct; try apply NCF_RAssign.
        ** apply WD_Odot; repeat apply WD_Pplus; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred; try lra.
          simpl. reflexivity. 
        ** apply WD_Odot; repeat apply WD_Pplus; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred; try lra.
          simpl. try destruct (Rle_lt_dec (489 / 663) 0); try contradiction; try lra;
          try destruct (Rle_lt_dec (420 / 435) 0); try contradiction; try lra;
          try destruct (Rle_lt_dec 1 (420 / 435)); try contradiction; try lra;
          try destruct (Rle_lt_dec 1 (489 / 663)); try contradiction; try lra; 
          try destruct (Rle_lt_dec (665 / 815) 0); try contradiction; try lra;
          try destruct (Rle_lt_dec 1 (665 / 815)); try contradiction; try lra;
          try destruct (Rle_lt_dec (9 / 10) 0); try contradiction; try lra;
          try destruct (Rle_lt_dec 1 (9 / 10)); try contradiction; try lra; simpl; try reflexivity.
        ** simpl. try destruct (Rle_lt_dec (489 / 663) 0); try contradiction; try lra;
          try destruct (Rle_lt_dec (420 / 435) 0); try contradiction; try lra;
          try destruct (Rle_lt_dec 1 (420 / 435)); try contradiction; try lra;
          try destruct (Rle_lt_dec 1 (489 / 663)); try contradiction; try lra; 
          try destruct (Rle_lt_dec (665 / 815) 0); try contradiction; try lra;
          try destruct (Rle_lt_dec 1 (665 / 815)); try contradiction; try lra;
          try destruct (Rle_lt_dec (9 / 10) 0); try contradiction; try lra;
          try destruct (Rle_lt_dec 1 (9 / 10)); try contradiction; try lra; simpl; try reflexivity.
      * apply assert_trans with (R:= [[⊤ ⊙ (dist_D0dPG0 ⊕[ 489 / 663] dist_D1dPG0)]]); try apply OdotC. 
        try apply Odot_E. repeat apply WD_Pplus; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred; try lra.
  - apply hoare_Frame; try reflexivity. 
    + apply WD_Pand; repeat apply WD_Pplus; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred; try lra.
    + apply WD_Pand; try apply WD_Odot; repeat apply WD_Pplus; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred; try lra. 
      simpl. try destruct (Rle_lt_dec (111 / 337) 0); try contradiction; try lra;
      try destruct (Rle_lt_dec 1 (111 / 337)); try contradiction; try lra; 
      try destruct (Rle_lt_dec (35 / 185) 0); try contradiction; try lra;
      try destruct (Rle_lt_dec 1 (35 / 185)); try contradiction; try lra;
      try destruct (Rle_lt_dec (280 / 565) 0); try contradiction; try lra;
      try destruct (Rle_lt_dec 1 (280 / 565)); try contradiction; try lra;
      try destruct (Rle_lt_dec (3 / 10) 0); try contradiction; try lra;
      try destruct (Rle_lt_dec 1 (3 / 10)); try contradiction; try lra; simpl; try reflexivity.
    + apply hoare_consequence_pre with (P':= [[(dist_D0dPG1 ⊕[ 111 / 337] dist_D1dPG1) ⊙ ⊤]]). 
      * apply hoare_consequence with (P':= [[⊤ ⊙ (dist_D0dPG1 ⊕[ 111 / 337] dist_D1dPG1)]])
          (Q':=[[dist_XM1 ⊙ (dist_D0dPG1 ⊕[ 111 / 337] dist_D1dPG1)]]); try apply OdotC. 
        apply hoare_OFrame; try reflexivity; try apply RA_XM1_correct; try apply NCF_RAssign.
        ** apply WD_Odot; repeat apply WD_Pplus; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred; try lra.
          simpl. reflexivity. 
        ** apply WD_Odot; repeat apply WD_Pplus; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred; try lra.
          simpl. try destruct (Rle_lt_dec (111 / 337) 0); try contradiction; try lra;
          try destruct (Rle_lt_dec 1 (111 / 337)); try contradiction; try lra; 
          try destruct (Rle_lt_dec (35 / 185) 0); try contradiction; try lra;
          try destruct (Rle_lt_dec 1 (35 / 185)); try contradiction; try lra;
          try destruct (Rle_lt_dec (280 / 565) 0); try contradiction; try lra;
          try destruct (Rle_lt_dec 1 (280 / 565)); try contradiction; try lra;
          try destruct (Rle_lt_dec (3 / 10) 0); try contradiction; try lra;
          try destruct (Rle_lt_dec 1 (3 / 10)); try contradiction; try lra; simpl; try reflexivity.
        ** simpl. try destruct (Rle_lt_dec (111 / 337) 0); try contradiction; try lra;
          try destruct (Rle_lt_dec 1 (111 / 337)); try contradiction; try lra; 
          try destruct (Rle_lt_dec (35 / 185) 0); try contradiction; try lra;
          try destruct (Rle_lt_dec 1 (35 / 185)); try contradiction; try lra;
          try destruct (Rle_lt_dec (280 / 565) 0); try contradiction; try lra;
          try destruct (Rle_lt_dec 1 (280 / 565)); try contradiction; try lra;
          try destruct (Rle_lt_dec (3 / 10) 0); try contradiction; try lra;
          try destruct (Rle_lt_dec 1 (3 / 10)); try contradiction; try lra; simpl; try reflexivity.
      * apply assert_trans with (R:= [[⊤ ⊙ (dist_D0dPG1 ⊕[ 111 / 337] dist_D1dPG1)]]); try apply OdotC. 
        try apply Odot_E. repeat apply WD_Pplus; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred; try lra.
Qed. 

Lemma Body_correct: 
  let phi1:= (dist_D0dPG0 ⊕[489/663] dist_D1dPG0) in 
  let phi2:= (dist_D0dPG1 ⊕[111/337] dist_D1dPG1) in
  {{[[(Ava XP == Aco 0%Q)]]}} body 
  {{[[(phi1 ⊙ dist_XM0) ∧ (Ava XG == Aco 0) ⊕[ 663 / 1000] 
      (phi2 ⊙ dist_XM1) ∧ (~ B_XG_0)]]}}.
Proof.
  unfold body. 
  apply hoare_consequence_pre with (P':= (
              ([[Ava XD == Aco 0]] [XD |-> Aco 0]) /\ 
              ([[Ava XD == Aco 1]] [XD |-> Aco 1]))%assertion).
  - eapply hoare_seq with (Q:= ([[dist_XD]])); 
    try apply hoare_Rasgn; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try lra.
    eapply hoare_seq with (Q:= ([[dist_XD ⊙ dist_XP]])). 
    * apply hoare_consequence_pre with (P':= ([[dist_XP ∧ (Ava XD == Aco 0) ⊕[ 6 / 10] dist_XP ∧ (~ B_XD_0)]])).
      + apply hoare_seq with (Q:= ([[(dist_XG_with_dP_under_D0 ∧ (Ava XD == Aco 0)) ⊕[ 6 / 10] 
                        (dist_XG_with_dP_under_D1 ∧ (~ B_XD_0))]])); 
          try apply IF_D_correct.
        apply hoare_consequence_pre with 
          (P':=[[(dist_D0dPG0 ⊕[ 489 / 663] dist_D1dPG0) ∧ (Ava XG == Aco 0) ⊕[ 663 / 1000] 
                  (dist_D0dPG1 ⊕[ 111 / 337] dist_D1dPG1) ∧ (~ B_XG_0)]]);
          try apply IF_G_correct. 
        apply assert_trans with (R:= [[((dist_XG_00 ∧ XD0P0) ⊕[ 7 / 10] (dist_XG_01 ∧ XD0P1)) ⊕[ 6 / 10] 
                                        ((dist_XG_10 ∧ XD1P0) ⊕[ 7 / 10] (dist_XG_11 ∧ XD1P1))]]); 
          try apply After_D_implies_dG_with_DP; try apply distG_under_DP_implies_distDP_with_dG. 
      + apply assert_trans with (R:= [[((Ava XD == Aco 0) ⊙ dist_XP) ⊕[ 6 / 10] ((Ava XD == Aco 1) ⊙ dist_XP)]]).
        ++ apply OdotD_r; try assumption; try reflexivity; try lra.
          -- apply WD_Odot; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try reflexivity; simpl; try lra. 
            destruct (Rle_lt_dec (7 / 10) 0); destruct (Rle_lt_dec 1 (7 / 10)); 
            destruct (Rle_lt_dec (6 / 10) 0); destruct (Rle_lt_dec 1 (6 / 10)); simpl; try reflexivity.
          -- simpl. destruct (Rle_lt_dec (7 / 10) 0); destruct (Rle_lt_dec 1 (7 / 10)); try reflexivity.
          -- simpl. destruct (Rle_lt_dec (7 / 10) 0); destruct (Rle_lt_dec 1 (7 / 10)); try reflexivity.
        ++ apply OCon_Pplus; try lra. 
          -- apply assert_trans with (R:= [[dist_XP ⊙ (Ava XD == Aco 0)]]); try apply OdotC; try apply OdotO;
              try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try lra.
          -- apply assert_trans with (R:= [[dist_XP ⊙ (Ava XD == Aco 1)]]); try apply OdotC. 
              apply assert_trans with (R:= [[dist_XP ∧ (Ava XD == Aco 1)]]); try apply OdotO;
              try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try lra. 
              unfold assert_implies. intros. destruct H1. split; try assumption. 
              try apply Pdeter_implie_not with (m:= 1%Q); try assumption. compute; try reflexivity.
    * apply hoare_consequence_post with (Q':= [[((Ava XP == Aco 0) ⊕[ 7 / 10] (Ava XP == Aco 1)) ⊙ ((Ava XD == Aco 0) ⊕[ 6 / 10] (Ava XD == Aco 1))]]); 
          try apply OdotC.
      apply hoare_consequence_pre with (P':= [[⊤ ⊙ ((Ava XD == Aco 0) ⊕[ 6 / 10] (Ava XD == Aco 1)) ]]). 
        + eapply hoare_OFrame; intuition. 
        -- apply WD_Odot; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try reflexivity. lra.
        -- apply WD_Odot; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; simpl; try lra. 
          destruct (Rle_lt_dec (7 / 10) 0); destruct (Rle_lt_dec 1 (7 / 10)); destruct (Rle_lt_dec (6 / 10) 0); 
          destruct (Rle_lt_dec 1 (6 / 10)); simpl; try reflexivity.
        -- unfold RA_XP. constructor.
        -- simpl. destruct (Rle_lt_dec (6 / 10) 0); destruct (Rle_lt_dec 1 (6 / 10)); simpl; try reflexivity.
        -- apply hoare_consequence_pre with (P':= (
              ([[Pdeter (Dpred (Ava XP = Aco 0))]] [XP |-> Aco 0]) /\ 
              ([[Pdeter (Dpred (Ava XP = Aco 1))]] [XP |-> Aco 1]))%assertion).
          ++ apply hoare_Rasgn. apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred. lra.
          ++ unfold assert_implies. intros. split; try apply Pdeter_always_holds.
        + apply Odot_E. apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred. lra.
  - unfold assert_implies. intros. split; try apply Pdeter_always_holds. 
Qed. 
(*************************************************************************)
Definition L_ProbD_num0 := ((489/663)*(665/815))%R. (*equal to 399/663*)
Definition L_ProbD_num1 := ((174/663)*(420/435))%R. (*equal to 168/663*)
Definition L_dist_XD_under_XP0:= (Ava XD == Aco 0) ⊕[141455475/201015675] (Ava XD <> Aco 0). (*L_ProbD_num0/(L_ProbD_num0+L_ProbD_num1); equal to 399/567 *)
Definition L_dist_XD_under_XP1:= (Ava XD == Aco 0) ⊕[31907250/34034400] (Ava XD <> Aco 0). (*equal to 90/96*)


Lemma L_ProbP_eq: (L_ProbD_num0+L_ProbD_num1)%R = 201015675/235050075%R. (*equal to 567/663*)
Proof. unfold L_ProbD_num0, L_ProbD_num1. lra. Qed.

Lemma phi1_implies_One: 
  [[(dist_D0dPG0 ⊕[489/663] dist_D1dPG0)]] ->> 
  [[(Ava XP == Aco 0) ∧ L_dist_XD_under_XP0 ⊕[L_ProbD_num0 + L_ProbD_num1] 
    (Ava XP <> Aco 0) ∧ L_dist_XD_under_XP1]].
Proof. 
  unfold assert_implies. intros. destruct H1; try lra. destruct H1. 
  destruct H2 as [x0 H2]. destruct H2 as [x1 H2]. intuition.
  left. rewrite L_ProbP_eq. split; try lra. 
  destruct H7; try lra. destruct H7. destruct H11 as [D0P0 H']. destruct H' as [D0P1 H']. intuition.
  destruct H8; try lra. destruct H8. destruct H21 as [D1P0 H']. destruct H' as [D1P1 H']. intuition.
  destruct H17, H18, H27, H28.
  assert (Hdom_P0: (dom D0P0 == dom D1P0)%domain). { 
    apply dom_equiv_trans with (l1:= dom x0); try assumption. 
    apply dom_equiv_trans with (l1:= dom pd); try assumption. 
    apply dom_equiv_sym.
    apply dom_equiv_trans with (l1:= dom x1); try assumption. }
  assert (Hdom_P1: (dom D0P1 == dom D1P1)%domain). { 
    apply dom_equiv_trans with (l1:= dom x0); try assumption. 
    apply dom_equiv_trans with (l1:= dom pd); try assumption. 
    apply dom_equiv_sym.
    apply dom_equiv_trans with (l1:= dom x1); try assumption. }
  pose (pd_tmp0:= pd_add (cofe_pd D0P0 (141455475/201015675)) (cofe_pd D1P0 (59560200/201015675)) Hdom_P0).
  pose (pd_tmp1:= pd_add (cofe_pd D0P1 (31907250/34034400)) (cofe_pd D1P1 (2127150/34034400)) Hdom_P1).
  exists pd_tmp0, pd_tmp1. 
  split. { simpl. apply Valid_linear; try assumption; lra. }
  split. { simpl. apply Valid_linear; try assumption; lra. }
  split. { simpl. apply dom_equiv_trans with (l1:= dom x0); try assumption. }
  split. { simpl. apply dom_equiv_trans with (l1:= dom x0); try assumption. }
  split. { split. 
    - apply df_sem_linear_add with (pd0:= D0P0) (pd1:= D1P0) (p1:= (141455475/201015675)) (p2:= (59560200/201015675)); try assumption; try lra. 
      + apply Valid_linear; try assumption; lra.
      + simpl. apply dom_equiv_refl.
      + simpl. apply dom_equiv_sym. assumption.
      + simpl. apply dst_equiv_refl.
    - left; split; try lra. exists D0P0, D1P0. intuition.
      + simpl. apply dom_equiv_refl.
      + simpl. apply dom_equiv_sym. assumption.
      + simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H19. rewrite H29. rewrite H9. rewrite H10. 
        repeat rewrite <- Rmult_plus_distr_r. 
        replace (141455475 / 201015675 + 59560200 / 201015675)%R with (1)%R by lra. 
        rewrite Rmult_1_l. reflexivity.
      + simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H19. rewrite H29. rewrite H9. rewrite H10. 
        repeat rewrite <- Rmult_plus_distr_r. 
        replace (141455475 / 201015675 + 59560200 / 201015675)%R with (1)%R by lra.
        rewrite Rmult_1_l. reflexivity.
      + simpl. replace (1 - 141455475 / 201015675)%R with (59560200 / 201015675) by lra. apply dst_equiv_refl. }
  split. { split. 
    - apply df_sem_linear_add with (pd0:= D0P1) (pd1:= D1P1) (p1:= (31907250/34034400)) (p2:= (2127150/34034400)); try assumption; try lra. 
      + apply Valid_linear; try assumption; lra.
      + simpl. apply dom_equiv_refl.
      + simpl. apply dom_equiv_sym. assumption.
      + simpl. apply dst_equiv_refl.
    - left; split; try lra. exists D0P1, D1P1. intuition.
      + simpl. apply dom_equiv_refl.
      + simpl. apply dom_equiv_sym. assumption.
      + simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H20. rewrite H30. rewrite H9. rewrite H10. 
        repeat rewrite <- Rmult_plus_distr_r. 
        replace (31907250 / 34034400 + 2127150 / 34034400)%R with (1)%R by lra. 
        rewrite Rmult_1_l. reflexivity.
      + simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H20. rewrite H30. rewrite H9. rewrite H10. 
        repeat rewrite <- Rmult_plus_distr_r. 
        replace (31907250 / 34034400 + 2127150 / 34034400)%R with (1)%R by lra.
        rewrite Rmult_1_l. reflexivity.
      + simpl. replace (1 - 31907250 / 34034400)%R with (2127150 / 34034400) by lra. apply dst_equiv_refl. }
  split. { simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
    rewrite H19. rewrite H29. rewrite H9. rewrite H10. 
    repeat rewrite <- Rmult_plus_distr_r. 
    replace (141455475 / 201015675 + 59560200 / 201015675)%R with (1)%R by lra. 
    rewrite Rmult_1_l. reflexivity. }
  split. { simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
    rewrite H20. rewrite H30. rewrite H9. rewrite H10. 
    repeat rewrite <- Rmult_plus_distr_r. 
    replace (31907250 / 34034400 + 2127150 / 34034400)%R with (1)%R by lra. 
    rewrite Rmult_1_l. reflexivity. }
  simpl. repeat rewrite dst_mult_plus_distr_r_eq. repeat rewrite dst_mult_assoc_eq. 
  apply dst_equiv_trans with (mu1:= (489 / 663 * mu x0 + (1 - 489 / 663) * mu x1)%dist_state); try assumption.
  apply dst_equiv_trans with (mu1:= ((((201015675 / 235050075) * (141455475 / 201015675)) * mu D0P0) + 
    ((1 - 201015675 / 235050075) * (31907250 / 34034400)) * mu D0P1 + 
    ((201015675 / 235050075 * (59560200 / 201015675)) * mu D1P0 + ((1 - 201015675 / 235050075) * (2127150 / 34034400)) * mu D1P1))%dist_state);
    try apply dst_add_shuffle.
  apply dst_add_preserves_equiv. 
  - apply dst_equiv_trans with (mu1:= (489 / 663 * (665 / 815 * mu D0P0 + (1 - 665 / 815) * mu D0P1))%dist_state); try assumption.
    + apply dst_mult_preserves_equiv. assumption.  
    + rewrite dst_mult_plus_distr_r_eq. apply dst_add_preserves_equiv; rewrite dst_mult_assoc_eq. 
      * replace (201015675 / 235050075 * (141455475 / 201015675))%R with (489 / 663 * (665 / 815))%R by lra. try apply dst_equiv_refl.
      * replace ((1 - 201015675 / 235050075) * (31907250 / 34034400))%R with (489 / 663 * (1 - 665 / 815))%R by lra. try apply dst_equiv_refl.
  - apply dst_equiv_trans with (mu1:= (((1 - 489 / 663)) * (420 / 435 * mu D1P0 + (1 - 420 / 435) * mu D1P1))%dist_state).
    + apply dst_mult_preserves_equiv. assumption.  
    + rewrite dst_mult_plus_distr_r_eq. apply dst_add_preserves_equiv; rewrite dst_mult_assoc_eq. 
      * replace (201015675 / 235050075 * (59560200 / 201015675))%R with ((1 - 489 / 663) * (420 / 435))%R by lra. try apply dst_equiv_refl.
      * replace ((1 - 201015675 / 235050075) * (2127150 / 34034400))%R with ((1 - 489 / 663) * (1 - 420 / 435))%R by lra. try apply dst_equiv_refl. 
Qed.  

Definition R_ProbD_num0 := ((111/337)*(35/185))%R.  (*equal to 21/337*)
Definition R_ProbD_num1 := ((226/337)*(280/565))%R. (*equal to 112/337*)
Definition R_dist_XD_under_XP0:= (Ava XD == Aco 0) ⊕[2195025/13901825] (Ava XD <> Aco 0). (*R_ProbD_num0/(R_ProbD_num0+R_ProbD_num1) 21/133*)
Definition R_dist_XD_under_XP1:= (Ava XD == Aco 0) ⊕[9407250/21323100] (Ava XD <> Aco 0). (*equal to (111*150)/(185*204) *)
Lemma R_ProbP_eq: (R_ProbD_num0+R_ProbD_num1)%R = 13901825/35224925%R. (*equal to 133/337*)
Proof. unfold R_ProbD_num0, R_ProbD_num1. lra. Qed.

Lemma phi2_plus_implies_One: 
  [[(dist_D0dPG1 ⊕[111/337] dist_D1dPG1)]] ->> 
  [[(Ava XP == Aco 0) ∧ R_dist_XD_under_XP0 ⊕[R_ProbD_num0 + R_ProbD_num1] 
    (Ava XP <> Aco 0) ∧ R_dist_XD_under_XP1]].
Proof. 
  unfold assert_implies. intros. destruct H1; try lra. destruct H1. 
  destruct H2 as [x0 H2]. destruct H2 as [x1 H2]. intuition.
  left. rewrite R_ProbP_eq. split; try lra. 
  destruct H7; try lra. destruct H7. destruct H11 as [D0P0 H']. destruct H' as [D0P1 H']. intuition.
  destruct H8; try lra. destruct H8. destruct H21 as [D1P0 H']. destruct H' as [D1P1 H']. intuition.
  destruct H17, H18, H27, H28.
  assert (Hdom_P0: (dom D0P0 == dom D1P0)%domain). { 
    apply dom_equiv_trans with (l1:= dom x0); try assumption. 
    apply dom_equiv_trans with (l1:= dom pd); try assumption. 
    apply dom_equiv_sym.
    apply dom_equiv_trans with (l1:= dom x1); try assumption. }
  assert (Hdom_P1: (dom D0P1 == dom D1P1)%domain). { 
    apply dom_equiv_trans with (l1:= dom x0); try assumption. 
    apply dom_equiv_trans with (l1:= dom pd); try assumption. 
    apply dom_equiv_sym.
    apply dom_equiv_trans with (l1:= dom x1); try assumption. }
  pose (pd_tmp0:= pd_add (cofe_pd D0P0 (2195025/13901825)) (cofe_pd D1P0 (11706800/13901825)) Hdom_P0).
  pose (pd_tmp1:= pd_add (cofe_pd D0P1 (9407250/21323100)) (cofe_pd D1P1 (11915850/21323100)) Hdom_P1).
  exists pd_tmp0, pd_tmp1. 
  split. { simpl. apply Valid_linear; try assumption; lra. }
  split. { simpl. apply Valid_linear; try assumption; lra. }
  split. { simpl. apply dom_equiv_trans with (l1:= dom x0); try assumption. }
  split. { simpl. apply dom_equiv_trans with (l1:= dom x0); try assumption. }
  split. { split. 
    - apply df_sem_linear_add with (pd0:= D0P0) (pd1:= D1P0) (p1:= (2195025/13901825)) (p2:= (11706800/13901825)); try assumption; try lra. 
      + apply Valid_linear; try assumption; lra.
      + simpl. apply dom_equiv_refl.
      + simpl. apply dom_equiv_sym. assumption.
      + simpl. apply dst_equiv_refl.
    - left; split; try lra. exists D0P0, D1P0. intuition.
      + simpl. apply dom_equiv_refl.
      + simpl. apply dom_equiv_sym. assumption.
      + simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H19. rewrite H29. rewrite H9. rewrite H10. 
        repeat rewrite <- Rmult_plus_distr_r. 
        replace (2195025 / 13901825 + 11706800 / 13901825)%R with (1)%R by lra. 
        rewrite Rmult_1_l. reflexivity.
      + simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H19. rewrite H29. rewrite H9. rewrite H10. 
        repeat rewrite <- Rmult_plus_distr_r. 
        replace (2195025 / 13901825 + 11706800 / 13901825)%R with (1)%R by lra.
        rewrite Rmult_1_l. reflexivity.
      + simpl. replace (1 - 2195025 / 13901825)%R with (11706800 / 13901825) by lra. apply dst_equiv_refl. }
  split. { split. 
    - apply df_sem_linear_add with (pd0:= D0P1) (pd1:= D1P1) (p1:= (9407250 / 21323100)) (p2:= (11915850 / 21323100)); try assumption; try lra. 
      + apply Valid_linear; try assumption; lra.
      + simpl. apply dom_equiv_refl.
      + simpl. apply dom_equiv_sym. assumption.
      + simpl. apply dst_equiv_refl.
    - left; split; try lra. exists D0P1, D1P1. intuition.
      + simpl. apply dom_equiv_refl.
      + simpl. apply dom_equiv_sym. assumption.
      + simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H20. rewrite H30. rewrite H9. rewrite H10. 
        repeat rewrite <- Rmult_plus_distr_r. 
        replace (9407250 / 21323100 + 11915850 / 21323100)%R with (1)%R by lra. 
        rewrite Rmult_1_l. reflexivity.
      + simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H20. rewrite H30. rewrite H9. rewrite H10. 
        repeat rewrite <- Rmult_plus_distr_r. 
        replace (9407250 / 21323100 + 11915850 / 21323100)%R with (1)%R by lra.
        rewrite Rmult_1_l. reflexivity.
      + simpl. replace (1 - 9407250 / 21323100)%R with (11915850 / 21323100) by lra. apply dst_equiv_refl. }
  split. { simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
    rewrite H19. rewrite H29. rewrite H9. rewrite H10. 
    repeat rewrite <- Rmult_plus_distr_r. 
    replace (2195025 / 13901825 + 11706800 / 13901825)%R with (1)%R by lra. 
    rewrite Rmult_1_l. reflexivity. }
  split. { simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
    rewrite H20. rewrite H30. rewrite H9. rewrite H10. 
    repeat rewrite <- Rmult_plus_distr_r. 
    replace (9407250 / 21323100 + 11915850 / 21323100)%R with (1)%R by lra. 
    rewrite Rmult_1_l. reflexivity. }
  simpl. repeat rewrite dst_mult_plus_distr_r_eq. repeat rewrite dst_mult_assoc_eq. 
  apply dst_equiv_trans with (mu1:= (111 / 337 * mu x0 + (1 - 111 / 337) * mu x1)%dist_state); try assumption.
  apply dst_equiv_trans with (mu1:= ((13901825 / 35224925 * (2195025 / 13901825) * mu D0P0) + 
    (1 - 13901825 / 35224925) * (9407250 / 21323100) * mu D0P1 + 
    (13901825 / 35224925 * (11706800 / 13901825) * mu D1P0 + (1 - 13901825 / 35224925) * (11915850 / 21323100) * mu D1P1))%dist_state);
    try apply dst_add_shuffle.
  apply dst_add_preserves_equiv. 
  - apply dst_equiv_trans with (mu1:= (111 / 337 * (35 / 185 * mu D0P0 + (1 - 35 / 185) * mu D0P1))%dist_state); try assumption.
    + apply dst_mult_preserves_equiv. assumption.  
    + rewrite dst_mult_plus_distr_r_eq. apply dst_add_preserves_equiv; rewrite dst_mult_assoc_eq. 
      * replace (13901825 / 35224925 * (2195025 / 13901825))%R with (111 / 337 * (35 / 185))%R by lra. try apply dst_equiv_refl.
      * replace ((1 - 13901825 / 35224925) * (9407250 / 21323100))%R with (111 / 337 * (1 - 35 / 185))%R by lra. try apply dst_equiv_refl.
  - apply dst_equiv_trans with (mu1:= ((1 - 111 / 337) * (280 / 565 * mu D1P0 + (1 - 280 / 565) * mu D1P1))%dist_state).
    + apply dst_mult_preserves_equiv. assumption.  
    + rewrite dst_mult_plus_distr_r_eq. apply dst_add_preserves_equiv; rewrite dst_mult_assoc_eq. 
      * replace (13901825 / 35224925 * (11706800 / 13901825))%R with ((1 - 111 / 337) * (280 / 565))%R by lra. try apply dst_equiv_refl.
      * replace ((1 - 13901825 / 35224925) * (11915850 / 21323100))%R with ((1 - 111 / 337) * (1 - 280 / 565))%R by lra. try apply dst_equiv_refl. 
Qed.  

Definition dist_XG_under_XP0:= (Ava XG == Aco 0) ⊕[567/700] (Ava XG <> Aco 0).
Definition dist_XG_under_XP1:= (Ava XG == Aco 0) ⊕[663/1000] (Ava XG <> Aco 0).

Lemma After_Body_implies_one: 
  let phi1:= (dist_D0dPG0 ⊕[489/663] dist_D1dPG0) in 
  let phi2:= (dist_D0dPG1 ⊕[111/337] dist_D1dPG1) in
  [[(phi1 ⊙ dist_XM0) ∧ (Ava XG == Aco 0) ⊕[ 663 / 1000] 
      (phi2 ⊙ dist_XM1) ∧ (~ B_XG_0)]] ->> 
  [[((Ava XP == Aco 0) ∧ (L_dist_XD_under_XP0 ⊙ dist_XM0) ⊕[L_ProbD_num0 + L_ProbD_num1] 
    ((Ava XP <> Aco 0) ∧ (L_dist_XD_under_XP1 ⊙ dist_XM0))) ∧ (Ava XG == Aco 0) ⊕[ 663 / 1000] 
    ((Ava XP == Aco 0) ∧ (R_dist_XD_under_XP0 ⊙ dist_XM1) ⊕[R_ProbD_num0 + R_ProbD_num1] 
    ((Ava XP <> Aco 0) ∧ (R_dist_XD_under_XP1 ⊙ dist_XM1))) ∧ (~ B_XG_0)]].
Proof. 
  apply OCon_Pplus; try lra. 
  - unfold assert_implies. intros. destruct H1. split; try assumption. 
    destruct H1. destruct H1. destruct H1. intuition.
    assert (Hodot: [[((Ava XP == Aco 0) ∧ L_dist_XD_under_XP0 ⊕[ L_ProbD_num0 + L_ProbD_num1] 
                      (Ava XP <> Aco 0) ∧ (L_dist_XD_under_XP1)) ⊙ dist_XM0]] pd). {
                        destruct x0 as [dom0 mu0 HPD0]. 
                        destruct mu0 as [|(s0,p0) mu0'].
                        - simpl in H7. destruct H7 as [Hdom_comb Heq_comb]. 
                          simpl in Hdom_comb, Heq_comb. rewrite combine_nil_r_eq in Heq_comb. 
                          apply WF_dst_res_X_nil in Heq_comb; try assumption. 
                          assert (Hmu: mu pd = []). {
                            apply dst_eq_nil_iff. split; try assumption. }
                          assert (Heq: pd ≡ (pd_emp (dom pd))). { 
                            split; simpl; try apply dom_equiv_refl. rewrite Hmu.
                            try apply dst_equiv_refl.  }
                          apply pd_equiv_preserves_sem with (pd0:= pd_emp (dom pd)); 
                            try apply emp_dst_satisfies_phi; try assumption; 
                            try apply WD_Odot; try apply WD_Pplus; try apply WD_Pand; try apply WD_Pplus; try apply WD_Pdeter; 
                            try apply WD_Dpred; unfold L_ProbD_num0, L_ProbD_num1; try lra; simpl;  
                          destruct (Rle_lt_dec (489 / 663 * (665 / 815) + 174 / 663 * (420 / 435)) 0); try lra;
                          destruct (Rle_lt_dec 1 (489 / 663 * (665 / 815) + 174 / 663 * (420 / 435))); try lra; 
                          destruct (Rle_lt_dec (141455475 / 201015675) 0); try lra; 
                          destruct (Rle_lt_dec 1 (141455475 / 201015675)); try lra;
                          destruct (Rle_lt_dec (31907250 / 34034400) 0); try lra;
                          destruct (Rle_lt_dec 1 (31907250 / 34034400)); try lra;
                          destruct (Rle_lt_dec (9 / 10) 0); try lra;
                          destruct (Rle_lt_dec 1 (9 / 10)); try lra; try reflexivity.
                          apply satisfy_implies_dom_sub in H4; 
                          apply satisfy_implies_dom_sub in H5; try assumption. 
                          + simpl in H4. 
                            destruct (Rle_lt_dec (489 / 663) 0); try lra. 
                            destruct (Rle_lt_dec 1 (489 / 663)); try lra;
                            destruct (Rle_lt_dec (665 / 815) 0); try lra;
                            destruct (Rle_lt_dec 1 (665 / 815)); try lra.
                            destruct (Rle_lt_dec (420 / 435) 0); try lra;
                            destruct (Rle_lt_dec 1 (420 / 435)); try lra.
                            simpl in H5. 
                            destruct (Rle_lt_dec (9 / 10) 0); try lra;
                            destruct (Rle_lt_dec 1 (9 / 10)); try lra.
                            apply dom_subset_orb_fst_iff. split.
                            * apply dom_subset_trans with (l1:= (dom x ∪ dom0)%domain); try assumption. 
                              apply dom_subset_trans with (l1:= (dom x)%domain); try assumption.
                              apply dom_subset_orb_snd_l_r. 
                            * apply dom_subset_trans with (l1:= (dom x ∪ dom0)%domain); try assumption. 
                              apply dom_subset_trans with (l1:= (dom0)%domain); try assumption.
                              apply dom_subset_orb_snd_l_r.
                          + apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption. try lra. 
                          + repeat apply WD_Pplus; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra.
                          + repeat apply WD_Pplus; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra.
                        - pose (x0:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}). 
                          assert (H7_sortx: {|
                            dom := (dom (Sort_pd x) ∪ dom {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |})%domain;
                            mu := mu (Sort_pd x) ⊗ mu {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |};
                            all_partial :=
                              PD_combine_invar_mu (Sort_pd x) {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |} x1
                            |} ⊑ pd). { destruct H7. split; simpl; try assumption. simpl in H7. 
                            apply dst_equiv_trans with (mu1:= mu x ⊗ ((s0, p0) :: mu0')); try assumption.
                            apply combine_left_sort_equiv. }
                          exists x, x0, x1. intuition.
                          apply phi1_implies_One in H4; try assumption. 
                          apply comb_dst_inject_Z in H7_sortx; try assumption. 
                          * apply sort_inject_Z. assumption.
                          * apply Valid_implies_sort_Valid. assumption.
                          * apply WF_dist_implies_sortdst_Sorted. assumption. 
                      }
    apply OdotD_r in Hodot; unfold L_ProbD_num0, L_ProbD_num1; try lra; try assumption. 
    + unfold L_ProbD_num0, L_ProbD_num1 in *. destruct Hodot; try lra.  
      destruct H6. destruct H8. destruct H8. intuition. left. split; try lra.
      assert (Hinjx2: dst_inject_Z (mu x2)). {
        apply dst_implies_inject_Z in H18; try assumption.
        - apply dst_inject_Z_decom in H18. destruct H18. 
          apply dst_mult_inject_Z with (p:= /(489 / 663 * (665 / 815) + 174 / 663 * (420 / 435))) in H17.
          rewrite dst_mult_assoc_eq in H17.
          replace (/ (489 / 663 * (665 / 815) + 174 / 663 * (420 / 435)) *
            ((489 / 663 * (665 / 815) + 174 / 663 * (420 / 435))))%R with (1)%R in H17 by lra.
          rewrite <- dst_mult_1_l. assumption.
        - apply Valid_linear; try assumption; try lra. } 
      assert (Hinjx3: dst_inject_Z (mu x3)). {
        apply dst_implies_inject_Z in H18; try assumption.
        - apply dst_inject_Z_decom in H18. destruct H18. 
          apply dst_mult_inject_Z with (p:= /(1 - (489 / 663 * (665 / 815) + 174 / 663 * (420 / 435)))) in H18.
          rewrite dst_mult_assoc_eq in H18.
          replace (/ (1 - (489 / 663 * (665 / 815) + 174 / 663 * (420 / 435))) *
                (1 - (489 / 663 * (665 / 815) + 174 / 663 * (420 / 435))))%R with (1)%R in H18 by lra.
          rewrite <- dst_mult_1_l. assumption.
        - apply Valid_linear; try assumption; try lra. } 
      exists x2, x3. intuition.
      * apply OdotOC in H13; try assumption; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra. 
        destruct H13. split; try assumption. 
        apply OdotO in H13; try assumption; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra.
        destruct H13. try assumption. 
      * apply OdotOC in H14; try assumption; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra. 
        destruct H14. split; try assumption. 
        apply OdotO in H14; try assumption; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra.
        destruct H14. try assumption.
    + apply WD_Odot; try apply WD_Pplus; try apply WD_Pand; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra.
      simpl. 
      destruct (Rle_lt_dec (489 / 663 * (665 / 815) + 174 / 663 * (420 / 435)) 0); try lra;
      destruct (Rle_lt_dec 1 (489 / 663 * (665 / 815) + 174 / 663 * (420 / 435))); try lra;
      destruct (Rle_lt_dec (141455475 / 201015675) 0); try lra; 
      destruct (Rle_lt_dec 1 (141455475 / 201015675)); try lra;
      destruct (Rle_lt_dec (31907250 / 34034400) 0); try lra;
      destruct (Rle_lt_dec 1 (31907250 / 34034400)); try lra;
      destruct (Rle_lt_dec (9 / 10) 0); try lra;
      destruct (Rle_lt_dec 1 (9 / 10)); try lra; try reflexivity.
    + simpl. 
      destruct (Rle_lt_dec (141455475 / 201015675) 0); try lra; 
      destruct (Rle_lt_dec 1 (141455475 / 201015675)); try lra;
      destruct (Rle_lt_dec (9 / 10) 0); try lra;
      destruct (Rle_lt_dec 1 (9 / 10)); try lra; try reflexivity.
    + simpl. 
      destruct (Rle_lt_dec (31907250 / 34034400) 0); try lra;
      destruct (Rle_lt_dec 1 (31907250 / 34034400)); try lra;
      destruct (Rle_lt_dec (9 / 10) 0); try lra;
      destruct (Rle_lt_dec 1 (9 / 10)); try lra; try reflexivity.
  - unfold assert_implies. intros. destruct H1. split; try assumption. 
    destruct H1. destruct H1. destruct H1. intuition.
    assert (Hodot: [[((Ava XP == Aco 0) ∧ R_dist_XD_under_XP0 ⊕[ R_ProbD_num0 + R_ProbD_num1] 
                      (Ava XP <> Aco 0) ∧ (R_dist_XD_under_XP1)) ⊙ dist_XM1]] pd). {
                        destruct x0 as [dom0 mu0 HPD0]. 
                        destruct mu0 as [|(s0,p0) mu0'].
                        - simpl in H7. destruct H7 as [Hdom_comb Heq_comb]. 
                          simpl in Hdom_comb, Heq_comb. rewrite combine_nil_r_eq in Heq_comb. 
                          apply WF_dst_res_X_nil in Heq_comb; try assumption. 
                          assert (Hmu: mu pd = []). {
                            apply dst_eq_nil_iff. split; try assumption. }
                          assert (Heq: pd ≡ (pd_emp (dom pd))). { 
                            split; simpl; try apply dom_equiv_refl. rewrite Hmu.
                            try apply dst_equiv_refl.  }
                          apply pd_equiv_preserves_sem with (pd0:= pd_emp (dom pd)); 
                            try apply emp_dst_satisfies_phi; try assumption; 
                            try apply WD_Odot; try apply WD_Pplus; try apply WD_Pand; try apply WD_Pplus; try apply WD_Pdeter; 
                            try apply WD_Dpred; unfold R_ProbD_num0, R_ProbD_num1; try lra; simpl;
                          destruct (Rle_lt_dec (111 / 337 * (35 / 185) + 226 / 337 * (280 / 565)) 0); try lra;
                          destruct (Rle_lt_dec 1 (111 / 337 * (35 / 185) + 226 / 337 * (280 / 565))); try lra; 
                          destruct (Rle_lt_dec (9407250 / 21323100) 0); try lra; 
                          destruct (Rle_lt_dec 1 (9407250 / 21323100)); try lra;
                          destruct (Rle_lt_dec (2195025 / 13901825) 0); try lra;
                          destruct (Rle_lt_dec 1 (2195025 / 13901825)); try lra;
                          destruct (Rle_lt_dec (3 / 10) 0); try lra;
                          destruct (Rle_lt_dec 1 (3 / 10)); try lra; try reflexivity.
                          apply satisfy_implies_dom_sub in H4; 
                          apply satisfy_implies_dom_sub in H5; try assumption. 
                          + simpl in H4. 
                            destruct (Rle_lt_dec (111 / 337) 0); try lra. 
                            destruct (Rle_lt_dec 1 (111 / 337)); try lra;
                            destruct (Rle_lt_dec (280 / 565) 0); try lra;
                            destruct (Rle_lt_dec 1 (280 / 565)); try lra.
                            destruct (Rle_lt_dec (35 / 185) 0); try lra;
                            destruct (Rle_lt_dec 1 (35 / 185)); try lra.
                            simpl in H5. 
                            destruct (Rle_lt_dec (3 / 10) 0); try lra;
                            destruct (Rle_lt_dec 1 (3 / 10)); try lra.
                            apply dom_subset_orb_fst_iff. split.
                            * apply dom_subset_trans with (l1:= (dom x ∪ dom0)%domain); try assumption. 
                              apply dom_subset_trans with (l1:= (dom x)%domain); try assumption.
                              apply dom_subset_orb_snd_l_r. 
                            * apply dom_subset_trans with (l1:= (dom x ∪ dom0)%domain); try assumption. 
                              apply dom_subset_trans with (l1:= (dom0)%domain); try assumption.
                              apply dom_subset_orb_snd_l_r.
                          + apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption. try lra. 
                          + repeat apply WD_Pplus; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra.
                          + repeat apply WD_Pplus; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra.
                        - pose (x0:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}). 
                          assert (H7_sortx: {|
                            dom := (dom (Sort_pd x) ∪ dom {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |})%domain;
                            mu := mu (Sort_pd x) ⊗ mu {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |};
                            all_partial :=
                              PD_combine_invar_mu (Sort_pd x) {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |} x1
                            |} ⊑ pd). { destruct H7. split; simpl; try assumption. simpl in H7. 
                            apply dst_equiv_trans with (mu1:= mu x ⊗ ((s0, p0) :: mu0')); try assumption.
                            apply combine_left_sort_equiv. }
                          exists x, x0, x1. intuition.
                          apply phi2_plus_implies_One in H4; try assumption. 
                          apply comb_dst_inject_Z in H7_sortx; try assumption. 
                          * apply sort_inject_Z. assumption.
                          * apply Valid_implies_sort_Valid. assumption.
                          * apply WF_dist_implies_sortdst_Sorted. assumption. }
    apply OdotD_r in Hodot; unfold R_ProbD_num0, R_ProbD_num1; try lra; try assumption. 
    + unfold R_ProbD_num0, R_ProbD_num1 in *. destruct Hodot; try lra.  
      destruct H6. destruct H8. destruct H8. intuition. left. split; try lra.
      assert (Hinjx2: dst_inject_Z (mu x2)). {
        apply dst_implies_inject_Z in H18; try assumption.
        - apply dst_inject_Z_decom in H18. destruct H18. 
          apply dst_mult_inject_Z with (p:= /(111 / 337 * (35 / 185) + 226 / 337 * (280 / 565))) in H17.
          rewrite dst_mult_assoc_eq in H17.
          replace (/ (111 / 337 * (35 / 185) + 226 / 337 * (280 / 565)) *
            (111 / 337 * (35 / 185) + 226 / 337 * (280 / 565)))%R with (1)%R in H17 by lra.
          rewrite <- dst_mult_1_l. assumption.
        - apply Valid_linear; try assumption; try lra. } 
      assert (Hinjx3: dst_inject_Z (mu x3)). {
        apply dst_implies_inject_Z in H18; try assumption.
        - apply dst_inject_Z_decom in H18. destruct H18. 
          apply dst_mult_inject_Z with (p:= /(1 - (111 / 337 * (35 / 185) + 226 / 337 * (280 / 565)))) in H18.
          rewrite dst_mult_assoc_eq in H18.
          replace (/ (1 - (111 / 337 * (35 / 185) + 226 / 337 * (280 / 565))) *
            (1 - (111 / 337 * (35 / 185) + 226 / 337 * (280 / 565))))%R with (1)%R in H18 by lra.
          rewrite <- dst_mult_1_l. assumption.
        - apply Valid_linear; try assumption; try lra. } 
      exists x2, x3. intuition.
      * apply OdotOC in H13; try assumption; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra. 
        destruct H13. split; try assumption. 
        apply OdotO in H13; try assumption; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra.
        destruct H13. try assumption. 
      * apply OdotOC in H14; try assumption; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra. 
        destruct H14. split; try assumption. 
        apply OdotO in H14; try assumption; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra.
        destruct H14. try assumption.
    + apply WD_Odot; try apply WD_Pplus; try apply WD_Pand; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra.
      simpl. 
      destruct (Rle_lt_dec (111 / 337 * (35 / 185) + 226 / 337 * (280 / 565)) 0); try lra;
      destruct (Rle_lt_dec 1 (111 / 337 * (35 / 185) + 226 / 337 * (280 / 565))); try lra;
      destruct (Rle_lt_dec (9407250 / 21323100) 0); try lra; 
      destruct (Rle_lt_dec 1 (9407250 / 21323100)); try lra;
      destruct (Rle_lt_dec (2195025 / 13901825) 0); try lra;
      destruct (Rle_lt_dec 1 (2195025 / 13901825)); try lra;
      destruct (Rle_lt_dec (3 / 10) 0); try lra;
      destruct (Rle_lt_dec 1 (3 / 10)); try lra; try reflexivity.
    + simpl. 
      destruct (Rle_lt_dec (2195025 / 13901825) 0); try lra; 
      destruct (Rle_lt_dec 1 (2195025 / 13901825)); try lra;
      destruct (Rle_lt_dec (3 / 10) 0); try lra;
      destruct (Rle_lt_dec 1 (3 / 10)); try lra; try reflexivity.
    + simpl. 
      destruct (Rle_lt_dec (9407250 / 21323100) 0); try lra;
      destruct (Rle_lt_dec 1 (9407250 / 21323100)); try lra;
      destruct (Rle_lt_dec (3 / 10) 0); try lra;
      destruct (Rle_lt_dec 1 (3 / 10)); try lra; try reflexivity.
Qed.

Definition d1:= (L_dist_XD_under_XP0 ⊙ dist_XM0). 
Definition d1_distr_G := (L_dist_XD_under_XP0 ∧ (Ava XM == Aco 0)) ⊕[9/10] ((L_dist_XD_under_XP0 ∧ (Ava XM == Aco 1))) .
Definition d2:= (L_dist_XD_under_XP1 ⊙ dist_XM0).
Definition d2_distr_G := (L_dist_XD_under_XP1 ∧ (Ava XM == Aco 0)) ⊕[9/10] ((L_dist_XD_under_XP1 ∧ (Ava XM == Aco 1))) .
Definition d3:= (R_dist_XD_under_XP0 ⊙ dist_XM1).
Definition d3_distr_G := (R_dist_XD_under_XP0 ∧ (Ava XM == Aco 0)) ⊕[3/10] ((R_dist_XD_under_XP0 ∧ (Ava XM == Aco 1))) .
Definition d4:= (R_dist_XD_under_XP1 ⊙ dist_XM1).
Definition d4_distr_G := (R_dist_XD_under_XP1 ∧ (Ava XM == Aco 0)) ⊕[3/10] ((R_dist_XD_under_XP1 ∧ (Ava XM == Aco 1))) .

Definition F0:= (d1_distr_G ∧ (Ava XG == Aco 0)) ⊕[(663 / 1000)*(L_ProbD_num0 + L_ProbD_num1)*10/7] (d3_distr_G ∧ (~ B_XG_0)).
Definition F1:= (d2_distr_G ∧ (Ava XG == Aco 0)) ⊕[(663 / 1000)*(1- L_ProbD_num0 - L_ProbD_num1)*10/3] (d4_distr_G ∧ (~ B_XG_0)).

Lemma d1_implimes_distr_G : 
  [[d1]] ->> [[d1_distr_G]].
Proof. 
  unfold d1_distr_G, d1. 
  apply assert_trans with (R:= [[(L_dist_XD_under_XP0 ⊙ (Ava XM == Aco 0)) ⊕[ 9 / 10] (L_dist_XD_under_XP0 ⊙ (Ava XM == Aco 1))]]).
  - apply OdotD_l; try assumption; try lra. 
    + apply WD_Odot; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra. 
      simpl. 
      destruct (Rle_lt_dec (141455475 / 201015675) 0); try lra; 
      destruct (Rle_lt_dec 1 (141455475 / 201015675)); try lra; 
      destruct (Rle_lt_dec (9 / 10) 0); try lra; 
      destruct (Rle_lt_dec 1 (9 / 10)); try lra; try reflexivity.
    + simpl. destruct (Rle_lt_dec (141455475 / 201015675) 0); try lra; 
      destruct (Rle_lt_dec 1 (141455475 / 201015675)); try lra. simpl. reflexivity.
    + simpl. destruct (Rle_lt_dec (141455475 / 201015675) 0); try lra; 
      destruct (Rle_lt_dec 1 (141455475 / 201015675)); try lra. simpl. reflexivity.
  - apply OCon_Pplus; try assumption; try lra; try apply OdotO; 
      try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra.
Qed.

Lemma d2_implimes_distr_G : 
  [[d2]] ->> [[d2_distr_G]].
Proof. 
  unfold d2_distr_G, d2. 
  apply assert_trans with (R:= [[(L_dist_XD_under_XP1 ⊙ (Ava XM == Aco 0)) ⊕[ 9 / 10] (L_dist_XD_under_XP1 ⊙ (Ava XM == Aco 1))]]).
  - apply OdotD_l; try assumption; try lra. 
    + apply WD_Odot; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra. 
      simpl. 
      destruct (Rle_lt_dec (31907250 / 34034400) 0); try lra; 
      destruct (Rle_lt_dec 1 (31907250 / 34034400)); try lra; 
      destruct (Rle_lt_dec (9 / 10) 0); try lra; 
      destruct (Rle_lt_dec 1 (9 / 10)); try lra; try reflexivity.
    + simpl. destruct (Rle_lt_dec (31907250 / 34034400) 0); try lra; 
      destruct (Rle_lt_dec 1 (31907250 / 34034400)); try lra. simpl. reflexivity.
    + simpl. destruct (Rle_lt_dec (31907250 / 34034400) 0); try lra; 
      destruct (Rle_lt_dec 1 (31907250 / 34034400)); try lra. simpl. reflexivity.
  - apply OCon_Pplus; try assumption; try lra; try apply OdotO; 
      try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra.
Qed.

Lemma d3_implimes_distr_G : 
  [[d3]] ->> [[d3_distr_G]].
Proof. 
  unfold d3_distr_G, d3. 
  apply assert_trans with (R:= [[(R_dist_XD_under_XP0 ⊙ (Ava XM == Aco 0)) ⊕[ 3 / 10] (R_dist_XD_under_XP0 ⊙ (Ava XM == Aco 1))]]).
  - apply OdotD_l; try assumption; try lra. 
    + apply WD_Odot; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra. 
      simpl. 
      destruct (Rle_lt_dec (2195025 / 13901825) 0); try lra; 
      destruct (Rle_lt_dec 1 (2195025 / 13901825)); try lra; 
      destruct (Rle_lt_dec (3 / 10) 0); try lra; 
      destruct (Rle_lt_dec 1 (3 / 10)); try lra; try reflexivity.
    + simpl. destruct (Rle_lt_dec (2195025 / 13901825) 0); try lra; 
      destruct (Rle_lt_dec 1 (2195025 / 13901825)); try lra. simpl. reflexivity.
    + simpl. destruct (Rle_lt_dec (2195025 / 13901825) 0); try lra; 
      destruct (Rle_lt_dec 1 (2195025 / 13901825)); try lra. simpl. reflexivity.
  - apply OCon_Pplus; try assumption; try lra; try apply OdotO; 
      try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra.
Qed.

Lemma d4_implimes_distr_G : 
  [[d4]] ->> [[d4_distr_G]].
Proof. 
  unfold d4_distr_G, d4. 
  apply assert_trans with (R:= [[(R_dist_XD_under_XP1 ⊙ (Ava XM == Aco 0)) ⊕[ 3 / 10] (R_dist_XD_under_XP1 ⊙ (Ava XM == Aco 1))]]).
  - apply OdotD_l; try assumption; try lra. 
    + apply WD_Odot; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra. 
      simpl. 
      destruct (Rle_lt_dec (9407250 / 21323100) 0); try lra; 
      destruct (Rle_lt_dec 1 (9407250 / 21323100)); try lra; 
      destruct (Rle_lt_dec (3 / 10) 0); try lra; 
      destruct (Rle_lt_dec 1 (3 / 10)); try lra; try reflexivity.
    + simpl. destruct (Rle_lt_dec (9407250 / 21323100) 0); try lra; 
      destruct (Rle_lt_dec 1 (9407250 / 21323100)); try lra. simpl. reflexivity.
    + simpl. destruct (Rle_lt_dec (9407250 / 21323100) 0); try lra; 
      destruct (Rle_lt_dec 1 (9407250 / 21323100)); try lra. simpl. reflexivity.
  - apply OCon_Pplus; try assumption; try lra; try apply OdotO; 
      try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try lra.
Qed.


Lemma After_Body_implies_two: 
  [[((Ava XP == Aco 0) ∧ d1 ⊕[L_ProbD_num0 + L_ProbD_num1] 
    ((Ava XP <> Aco 0) ∧ d2)) ∧ (Ava XG == Aco 0) ⊕[ 663 / 1000] 
    ((Ava XP == Aco 0) ∧ d3 ⊕[R_ProbD_num0 + R_ProbD_num1] 
    ((Ava XP <> Aco 0) ∧ d4)) ∧ (~ B_XG_0)]] ->> 
  [[((Ava XP == Aco 0) ∧ F0) ⊕[7/10]
    ((Ava XP <> Aco 0) ∧ F1)]].
Proof. 
  apply assert_trans with (R:= 
  [[((Ava XP == Aco 0) ∧ (d1 ∧ (Ava XG == Aco 0)) ⊕[L_ProbD_num0 + L_ProbD_num1] 
    ((Ava XP <> Aco 0) ∧ (d2 ∧ (Ava XG == Aco 0))))  ⊕[ 663 / 1000] 
    ((Ava XP == Aco 0) ∧ (d3 ∧ (~ B_XG_0)) ⊕[R_ProbD_num0 + R_ProbD_num1] 
    ((Ava XP <> Aco 0) ∧ (d4 ∧ (~ B_XG_0))))]]).
  - apply OCon_Pplus; try lra.  
    + apply assert_trans with (R:= 
    [[((Ava XP == Aco 0) ∧ d1 ∧ (Ava XG == Aco 0) ⊕[ L_ProbD_num0 + L_ProbD_num1] 
       (Ava XP <> Aco 0) ∧ d2 ∧ (Ava XG == Aco 0))]]). 
      * apply Pplus_distr_PDeter. unfold L_ProbD_num0, L_ProbD_num1. lra. 
      * unfold L_ProbD_num0, L_ProbD_num1. apply OCon_Pplus; try lra. 
      ** unfold assert_implies. intros. destruct H1. destruct H1. split; try assumption. split; try assumption.
      ** unfold assert_implies. intros. destruct H1. destruct H1. split; try assumption. split; try assumption.
    + apply assert_trans with (R:= 
    [[((Ava XP == Aco 0) ∧ d3 ∧ (~ B_XG_0) ⊕[ R_ProbD_num0 + R_ProbD_num1] 
       (Ava XP <> Aco 0) ∧ d4 ∧ (~ B_XG_0))]]). 
      * apply Pplus_distr_PDeter. unfold R_ProbD_num0, R_ProbD_num1. lra. 
      * unfold R_ProbD_num0, R_ProbD_num1. apply OCon_Pplus; try lra. 
      ** unfold assert_implies. intros. destruct H1. destruct H1. split; try assumption. split; try assumption.
      ** unfold assert_implies. intros. destruct H1. destruct H1. split; try assumption. split; try assumption.
  - apply assert_trans with (R:= 
  [[((Ava XP == Aco 0) ∧ (d1_distr_G ∧ (Ava XG == Aco 0))
   ⊕[ L_ProbD_num0 + L_ProbD_num1] (Ava XP <> Aco 0)
                                   ∧ (d2_distr_G ∧ (Ava XG == Aco 0)))
  ⊕[ 663 / 1000] (Ava XP == Aco 0) ∧ (d3_distr_G ∧ (~ B_XG_0))
                 ⊕[ R_ProbD_num0 + R_ProbD_num1] 
                 (Ava XP <> Aco 0) ∧ (d4_distr_G ∧ (~ B_XG_0))]]).
    + apply OCon_Pplus; try lra. 
      * unfold L_ProbD_num0, L_ProbD_num1. apply OCon_Pplus; try lra. 
      ** unfold assert_implies. intros. destruct H1. destruct H2. 
        split; try assumption. split; try assumption. 
        apply d1_implimes_distr_G; intuition.
      ** unfold assert_implies. intros. destruct H1. destruct H2. 
        split; try assumption. split; try assumption. 
        apply d2_implimes_distr_G; intuition.
      * unfold R_ProbD_num0, R_ProbD_num1. apply OCon_Pplus; try lra. 
        ** unfold assert_implies. intros. destruct H1. destruct H2. 
          split; try assumption. split; try assumption. 
          apply d3_implimes_distr_G; intuition.
        ** unfold assert_implies. intros. destruct H1. destruct H2. 
          split; try assumption. split; try assumption. 
          apply d4_implimes_distr_G; intuition.
    + unfold assert_implies. intros. destruct H1; try lra. destruct H1. destruct H2. destruct H2. intuition. 
      unfold L_ProbD_num0, L_ProbD_num1, R_ProbD_num0, R_ProbD_num1 in *.
      destruct H7; destruct H8; try lra. destruct H7. destruct H11. destruct H11. intuition.
      destruct H16. destruct H16. intuition. destruct H19. destruct H27.
      left. split; try lra. 
      assert (Hdom_P0: (dom x1 == dom x3)%domain). { 
      apply dom_equiv_trans with (l1:= dom x); try assumption. 
      apply dom_equiv_trans with (l1:= dom pd); try assumption. 
      apply dom_equiv_sym.
      apply dom_equiv_trans with (l1:= dom x0); try assumption. }
      pose (pd_tmp0:= pd_add (cofe_pd x1 ((663 / 1000)*(L_ProbD_num0 + L_ProbD_num1)*10/7)) 
                              (cofe_pd x3 (1-(663 / 1000)*(L_ProbD_num0 + L_ProbD_num1)*10/7)) Hdom_P0).
      assert (Hdom_P1: (dom x2 == dom x4)%domain). { 
      apply dom_equiv_trans with (l1:= dom x); try assumption. 
      apply dom_equiv_trans with (l1:= dom pd); try assumption. 
      apply dom_equiv_sym.
      apply dom_equiv_trans with (l1:= dom x0); try assumption. }
      pose (pd_tmp1:= pd_add (cofe_pd x2 ((663 / 1000)*(1- L_ProbD_num0 - L_ProbD_num1)*10/3)) 
                            (cofe_pd x4 (1-(663 / 1000)*(1- L_ProbD_num0 - L_ProbD_num1)*10/3)) Hdom_P1).
      exists pd_tmp0, pd_tmp1. 
      assert (HV0: Valid_dist (mu pd_tmp0)). {
        simpl. unfold L_ProbD_num0, L_ProbD_num1. apply Valid_linear; try assumption; try lra. }
      assert (HV1: Valid_dist (mu pd_tmp1)). {
        simpl. unfold L_ProbD_num0, L_ProbD_num1. apply Valid_linear; try assumption; try lra. }
      intuition.
      * simpl. apply dom_equiv_trans with (l1:= dom x); try assumption. 
      * simpl. apply dom_equiv_trans with (l1:= dom x); try assumption. 
      * split. { 
          apply df_sem_linear_add with (pd0:= x1) (pd1:= x3) 
          (p1:= ((663 / 1000)*(L_ProbD_num0 + L_ProbD_num1)*10/7)) 
          (p2:= (1- ((663 / 1000)*(L_ProbD_num0 + L_ProbD_num1)*10/7))%R); try assumption;
          unfold L_ProbD_num0, L_ProbD_num1; try lra.
          - simpl. apply dom_equiv_refl.
          - simpl. apply dom_equiv_sym. assumption.
          - simpl. fold L_ProbD_num0. fold L_ProbD_num1. apply dst_equiv_refl. }
        unfold F0. left. unfold L_ProbD_num0, L_ProbD_num1; split; try lra. 
        fold L_ProbD_num0. fold L_ProbD_num1. exists x1, x3. intuition.
      ** simpl. apply dom_equiv_refl.
      ** simpl. apply dom_equiv_sym. assumption.
      ** simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H21. rewrite H29. rewrite H9. rewrite H10. 
        repeat rewrite <- Rmult_plus_distr_r. 
        replace ((663 / 1000 * (L_ProbD_num0 + L_ProbD_num1) * 10 / 7 +
          (1 - 663 / 1000 * (L_ProbD_num0 + L_ProbD_num1) * 10 / 7)))%R with (1)%R by lra. 
        rewrite Rmult_1_l. reflexivity.
      ** simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H21. rewrite H29. rewrite H9. rewrite H10. 
        repeat rewrite <- Rmult_plus_distr_r. 
        replace ((663 / 1000 * (L_ProbD_num0 + L_ProbD_num1) * 10 / 7 +
          (1 - 663 / 1000 * (L_ProbD_num0 + L_ProbD_num1) * 10 / 7)))%R with (1)%R by lra. 
        rewrite Rmult_1_l. reflexivity.
      ** simpl. apply dst_equiv_refl. 
    * destruct H20. destruct H28.
      split. { 
        apply df_sem_linear_add with (pd0:= x2) (pd1:= x4) 
        (p1:= (663 / 1000 * (1 - L_ProbD_num0 - L_ProbD_num1) * 10 / 3)) 
        (p2:= (1 - 663 / 1000 * (1 - L_ProbD_num0 - L_ProbD_num1) * 10 / 3)%R); try assumption;
        unfold L_ProbD_num0, L_ProbD_num1; try lra.
        - simpl. apply dom_equiv_refl.
        - simpl. apply dom_equiv_sym. assumption.
        - simpl. fold L_ProbD_num0. fold L_ProbD_num1. apply dst_equiv_refl. }
      unfold F0. left. unfold L_ProbD_num0, L_ProbD_num1; split; try lra. 
      fold L_ProbD_num0. fold L_ProbD_num1. exists x2, x4. intuition.
      ** simpl. apply dom_equiv_refl.
      ** simpl. apply dom_equiv_sym. assumption.
      ** simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H22. rewrite H30. rewrite H9. rewrite H10. 
        repeat rewrite <- Rmult_plus_distr_r. 
        replace ((663 / 1000 * (1 - L_ProbD_num0 - L_ProbD_num1) * 10 / 3 +
          (1 - 663 / 1000 * (1 - L_ProbD_num0 - L_ProbD_num1) * 10 / 3)))%R with (1)%R by lra. 
        rewrite Rmult_1_l. reflexivity.
      ** simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
        rewrite H22. rewrite H30. rewrite H9. rewrite H10. 
        repeat rewrite <- Rmult_plus_distr_r. 
        replace ((663 / 1000 * (1 - L_ProbD_num0 - L_ProbD_num1) * 10 / 3 +
          (1 - 663 / 1000 * (1 - L_ProbD_num0 - L_ProbD_num1) * 10 / 3)))%R with (1)%R by lra. 
        rewrite Rmult_1_l. reflexivity.
      ** simpl. apply dst_equiv_refl.
    * simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
      rewrite H21. rewrite H29. rewrite H9. rewrite H10. 
      repeat rewrite <- Rmult_plus_distr_r.  
      replace ((663 / 1000 * (L_ProbD_num0 + L_ProbD_num1) * 10 / 7 +
          (1 - 663 / 1000 * (L_ProbD_num0 + L_ProbD_num1) * 10 / 7)))%R with (1)%R by lra. 
      rewrite Rmult_1_l. reflexivity.
    * simpl. repeat rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
      rewrite H22. rewrite H30. rewrite H9. rewrite H10. 
      repeat rewrite <- Rmult_plus_distr_r. 
      replace ((663 / 1000 * (1 - L_ProbD_num0 - L_ProbD_num1) * 10 / 3 +
          (1 - 663 / 1000 * (1 - L_ProbD_num0 - L_ProbD_num1) * 10 / 3)))%R with (1)%R by lra. 
      rewrite Rmult_1_l. reflexivity.
    * simpl. repeat rewrite dst_mult_plus_distr_r_eq. repeat rewrite dst_mult_assoc_eq.
      apply dst_equiv_trans with (mu1:= (7 / 10 * (663 / 1000 * (L_ProbD_num0 + L_ProbD_num1) * 10 / 7) * mu x1 + 
        (1 - 7 / 10) * (663 / 1000 * (1 - L_ProbD_num0 - L_ProbD_num1) * 10 / 3) * mu x2 + 
        (7 / 10 * (1 - 663 / 1000 * (L_ProbD_num0 + L_ProbD_num1) * 10 / 7) * mu x3 + 
        (1 - 7 / 10) * (1 - 663 / 1000 * (1 - L_ProbD_num0 - L_ProbD_num1) * 10 / 3) * mu x4))%dist_state);
      try apply dst_add_shuffle.
      apply dst_equiv_trans with (mu1:= (663 / 1000 * mu x + (1 - 663 / 1000) * mu x0)%dist_state); try assumption.
      apply dst_add_preserves_equiv.
      ** apply dst_equiv_trans with (mu1:= (663 / 1000 * ((489 / 663 * (665 / 815) + 174 / 663 * (420 / 435)) * mu x1 +
          (1 - (489 / 663 * (665 / 815) + 174 / 663 * (420 / 435))) * mu x2))%dist_state). 
      -- apply dst_mult_preserves_equiv. assumption.
      -- rewrite dst_mult_plus_distr_r_eq. apply dst_add_preserves_equiv; rewrite dst_mult_assoc_eq. 
      ++ unfold L_ProbD_num0, L_ProbD_num1. 
        replace (7 / 10 * (663 / 1000 * (489 / 663 * (665 / 815) + 174 / 663 * (420 / 435)) * 10 / 7))%R with 
        (663 / 1000 * (489 / 663 * (665 / 815) + 174 / 663 * (420 / 435)))%R by lra. apply dst_equiv_refl.
      ++ unfold L_ProbD_num0, L_ProbD_num1. 
        replace ((1 - 7 / 10) * (663 / 1000 * (1 - 489 / 663 * (665 / 815) - 174 / 663 * (420 / 435)) * 10 / 3))%R with 
        (663 / 1000 * (1 - (489 / 663 * (665 / 815) + 174 / 663 * (420 / 435))))%R by lra. apply dst_equiv_refl.
      ** apply dst_equiv_trans with (mu1:= ((1 - 663 / 1000)* ((111 / 337 * (35 / 185) + 226 / 337 * (280 / 565)) * mu x3 +
          (1 - (111 / 337 * (35 / 185) + 226 / 337 * (280 / 565))) * mu x4))%dist_state). 
      ++ apply dst_mult_preserves_equiv. assumption.
      ++ rewrite dst_mult_plus_distr_r_eq. apply dst_add_preserves_equiv; rewrite dst_mult_assoc_eq. 
      -- unfold L_ProbD_num0, L_ProbD_num1. 
        replace (7 / 10 * (1 - 663 / 1000 * (489 / 663 * (665 / 815) + 174 / 663 * (420 / 435)) * 10 / 7))%R with 
        ((1 - 663 / 1000) * (111 / 337 * (35 / 185) + 226 / 337 * (280 / 565)))%R by lra. apply dst_equiv_refl.
      -- unfold L_ProbD_num0, L_ProbD_num1. 
        replace ((1 - 7 / 10) * (1 - 663 / 1000 * (1 - 489 / 663 * (665 / 815) - 174 / 663 * (420 / 435)) * 10 / 3))%R with 
        ((1 - 663 / 1000) * (1 - (111 / 337 * (35 / 185) + 226 / 337 * (280 / 565))))%R by lra. apply dst_equiv_refl.
Qed.


Definition INVARIANT: Pformula:= (⊤ ∧ (Ava XP == Aco 0)) ⊕ (F1 ∧ (~B_XP_0)).
Lemma invariant_implies: 
  [[((Ava XP == Aco 0) ∧ (L_dist_XD_under_XP0 ⊙ dist_XM0) 
                  ⊕[ L_ProbD_num0 + L_ProbD_num1] 
          (Ava XP <> Aco 0) ∧ (L_dist_XD_under_XP1 ⊙ dist_XM0)) ∧ (Ava XG == Aco 0) ⊕[ 663 / 1000] 
    ((Ava XP == Aco 0) ∧ (R_dist_XD_under_XP0 ⊙ dist_XM1)
                  ⊕[ R_ProbD_num0 + R_ProbD_num1] 
          (Ava XP <> Aco 0) ∧ (R_dist_XD_under_XP1 ⊙ dist_XM1)) ∧ (~ B_XG_0)]] ->>
[[INVARIANT]].
Proof. 
  unfold INVARIANT. 
  apply assert_trans with (R:= [[((Ava XP == Aco 0) ∧ d1 ⊕[L_ProbD_num0 + L_ProbD_num1] 
    ((Ava XP <> Aco 0) ∧ d2)) ∧ (Ava XG == Aco 0) ⊕[ 663 / 1000] 
    ((Ava XP == Aco 0) ∧ d3 ⊕[R_ProbD_num0 + R_ProbD_num1] 
    ((Ava XP <> Aco 0) ∧ d4)) ∧ (~ B_XG_0)]]). 
  - apply OCon_Pplus; try lra. 
    + unfold assert_implies. intros. destruct H1. split; try assumption.
    + unfold assert_implies. intros. destruct H1. split; try assumption.
  - apply assert_trans with (R:= [[((Ava XP == Aco 0) ∧ F0) ⊕[7/10] ((Ava XP <> Aco 0) ∧ F1)]]); 
      try apply After_Body_implies_two. 
    apply assert_trans with (R:= [[⊤ ∧ (Ava XP == Aco 0) ⊕[ 7 / 10] F1 ∧ (Ava XP <> Aco 0)]]). 
    + apply OCon_Pplus; try apply Pand_comm; try lra.  
      unfold assert_implies. intros. destruct H1. 
      split; try assumption. simpl. intuition. 
    + unfold assert_implies. intros. destruct H1; try discriminate; try lra. 
      destruct H1. destruct H2. destruct H2. intuition. left. 
      exists (7/10), (3/10). intuition; try lra. 
      exists x, x0. intuition. 
      replace (3 / 10) with (1 - 7 / 10)%R by lra. assumption.
Qed.
Lemma BN_Prog_correct :
  {{[[(Ava XD == Aco default_Q) ∧ (Ava XG == Aco default_Q) ∧ (Ava XM == Aco default_Q)]]}} BN_Prog 
  {{[[(Ava XP <> Aco 0%Q)]]}}.
Proof.
  unfold BN_Prog. 
  pose (PD:= (Ava XD == Aco default_Q)).
  pose (PG:= (Ava XG == Aco default_Q)).
  pose (PM:= (Ava XM == Aco default_Q)).
  pose (P0:= [[PD ∧ PG ∧ PM ∧ (Ava XP == Aco 0%Q)]]).
  apply hoare_seq with (Q:= P0). { 
    apply hoare_consequence with (P':= [[INVARIANT]]) (Q':= [[F1 ∧ (~B_XP_0)]]).
    - apply hoare_while with (phi0:= ⊤); try reflexivity. 
      + apply WD_Oplus; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred. 
        unfold F1, L_ProbD_num0, L_ProbD_num1. 
        apply WD_Pplus; repeat try apply WD_Pand; try apply WD_Pplus; try apply WD_Pand; try apply WD_Pplus;
        try apply WD_Pdeter; try apply WD_Dpred; try lra.
      + unfold F1. simpl. intuition.
      + apply hoare_consequence_pre with (P':= [[Pdeter (Dpred (Ava XP = Aco 0%Q))]]). 
        * apply hoare_consequence_post with (Q':= 
            [[((dist_D0dPG0 ⊕[489/663] dist_D1dPG0) ⊙ dist_XM0) ∧ (Ava XG == Aco 0) ⊕[ 663 / 1000] 
              ((dist_D0dPG1 ⊕[111/337] dist_D1dPG1) ⊙ dist_XM1) ∧ (~ B_XG_0)]]).
        ** apply Body_correct.
        ** 
        apply assert_trans with (R:= [[((Ava XP == Aco 0) ∧ (L_dist_XD_under_XP0 ⊙ dist_XM0) ⊕[L_ProbD_num0 + L_ProbD_num1] 
    ((Ava XP <> Aco 0) ∧ (L_dist_XD_under_XP1 ⊙ dist_XM0))) ∧ (Ava XG == Aco 0) ⊕[ 663 / 1000] 
    ((Ava XP == Aco 0) ∧ (R_dist_XD_under_XP0 ⊙ dist_XM1) ⊕[R_ProbD_num0 + R_ProbD_num1] 
    ((Ava XP <> Aco 0) ∧ (R_dist_XD_under_XP1 ⊙ dist_XM1))) ∧ (~ B_XG_0)]]). 
        -- apply After_Body_implies_one. 
        -- apply invariant_implies. 
        * apply Conj_True. apply WD_Pdeter. apply WD_Dpred.
    - unfold INVARIANT, P0. unfold assert_implies. intros. right. left. 
      exists pd. intuition. 
      + apply pd_equiv_refl. 
      + apply satisfy_implies_dom_sub in H1.  
        * simpl in H1. simpl.
        unfold L_ProbD_num0, L_ProbD_num1.
        destruct (Rle_lt_dec (663 / 1000 * (1 - 489 / 663 * (665 / 815) - 174 / 663 * (420 / 435)) * 10 / 3) 0);
        destruct (Rle_lt_dec 1 (663 / 1000 * (1 - 489 / 663 * (665 / 815) - 174 / 663 * (420 / 435)) * 10 / 3)); try lra.
        destruct (Rle_lt_dec (31907250 / 34034400)%R 0%R);
        destruct (Rle_lt_dec 1 (31907250 / 34034400)%R); 
        destruct (Rle_lt_dec (9 / 10) 0); 
        destruct (Rle_lt_dec 1 (9 / 10)); 
        destruct (Rle_lt_dec (9407250 / 21323100) 0%R); 
        destruct (Rle_lt_dec 1 (9407250 / 21323100)); 
        destruct (Rle_lt_dec (3 / 10) 0);  
        destruct (Rle_lt_dec 1 (3 / 10)); try lra. 
        simpl. try assumption. 
        * repeat apply WD_Pand; apply WD_Pdeter; apply WD_Dpred. 
      + destruct H1. split; try assumption. simpl. split; try reflexivity. intros. intuition.
    - unfold B_XP_0. apply Pand_elim_l.
  }
  apply hoare_consequence_pre with (P':= [[⊤ ∧ (PD ∧ PG ∧ PM)]]); 
  try apply hoare_consequence_post with (Q':= [[(Ava XP == Aco 0) ∧ (PD ∧ PG ∧ PM)]]).
  - apply hoare_Frame; try repeat apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred. 
    * simpl. reflexivity.
    * apply hoare_consequence_pre with (P':= [[Pdeter (Dpred (Ava XP = Aco 0))]] [XP |-> Aco 0]). 
      + apply hoare_Dasgn. 
      + unfold assert_implies. intros. apply Pdeter_always_holds.
  - apply Pand_comm.
  - apply Conj_True. repeat apply WD_Pand; apply WD_Pdeter; apply WD_Dpred.
Qed. 