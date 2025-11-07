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
From Stdlib Require Import Reals Psatz.
Open Scope imp_scope.

Example X := 0%nat.
Example N1:= 1%nat.
Definition da_01 := [(Aco 0, 1/2);(Aco 1, (1 - 1/2)%R)].
Lemma da_01_valid : positive_probs da_01 /\ sum_probs da_01 = 1%R.
Proof.
  split.
  - unfold positive_probs. simpl. unfold prob_is_positive. 
    split; try lra.
  - unfold da_01, sum_probs. rewrite Rplus_0_r. lra. 
Qed.
Lemma half_bounds : 0 < 1/2 < 1.
Proof. lra. Qed.
Definition Vda_01 : valid_dist_aexp := 
    exist _ da_01 (valid_da_of_two (Aco 0) (Aco 1) (1/2) half_bounds).

Definition DA_X: winstr:= (X ::= (Aco 0%Q)).
Definition RA_N: winstr:= (N1 $= Vda_01).
Definition DA_X_plus: winstr := (X ::= (Apl (Ava X) (Aco 1%Q))).
Definition B_X_5: bexp:= Bnot (Ble (Aco 5%Q) (Ava X)).
Definition B_N_1: bexp:= (Beq (Ava N1) ((Aco 1%Q))).
Definition IF1 := If B_N_1 (DA_X_plus) (Skip).
Definition body1 := RA_N;; IF1.
Definition Prog1:= DA_X;; While B_X_5 body1.


Open Scope formula_scope. 

Lemma Prog1_correct :
  {{ [[Pdeter (Dpred Btrue)]] }} Prog1 {{ [[Pdeter (Dpred (Ava X = Aco 5%Q))]] }}.
Proof.
  unfold Prog1. 
  pose (P0:= [[Pdeter (Dpred (Ava X = Aco 0%Q))]]).
  apply hoare_seq with (Q:= P0). 
  { unfold B_X_5. 
    pose (phiT:= Pdeter (Dpred Btrue)).
    pose (phi1:= Pdeter (Dpred (Ava X = Aco 5%Q))).
    pose (phi_inv:= (phiT ∧ Pdeter (Dpred B_X_5) ⊕ phi1 ∧ Pdeter (Dpred (~ B_X_5)))).
    assert (HWD_inv: well_defined_Pf phi_inv). { 
      apply WD_Oplus; apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred. }
    apply hoare_consequence_pre with (P':= [[phi_inv]]);
    try apply hoare_consequence_post with 
        (Q':= [[phi1 ∧ Pdeter (Dpred (~ B_X_5))]]).
    - apply hoare_while with (phi0:= phiT); try reflexivity; try assumption. 
      unfold body1. 
      apply hoare_consequence_pre with (P':= [[Pdeter (Dpred B_X_5)]]); 
              try apply Conj_True; try apply WD_Pdeter; try apply WD_Dpred.
      apply hoare_consequence_pre with (P':= [[phiT ⊙ (Pdeter (Dpred B_X_5))]]); 
                try apply Odot_E; try apply WD_Pdeter; try apply WD_Dpred.
      assert (Hp: (0 <= (1/2)%R <= 1)%R) by lra. 
      pose (phi_n := (Pdeter (Dpred (Ava (N1) = Aco 0%Q)) ⊕[1/2] 
                      Pdeter (Dpred (Ava (N1) = Aco 1%Q)))%formula).
      apply hoare_seq with (Q:= [[phi_n ⊙ (Pdeter (Dpred B_X_5))]]); 
              try apply hoare_OFrame; try assumption; try reflexivity. 
        * pose (pre_if:= (Pdeter (Dpred (Ava X < Aco 5)) ∧ Pdeter (Dpred (Ava N1 = Aco 1))) ⊕[ 1 / 2 ] 
                          Pdeter (Dpred (Ava X < Aco 5)) ∧ Pdeter (Dpred (Bnot (Ava N1 = Aco 1)))).
          pose (post_if:= (Pdeter (Dpred (Ava X < Aco 5)) ⊕ Pdeter (Dpred (Ava X = Aco 5))) ⊕[ 1 / 2 ] 
                            Pdeter (Dpred (Ava X < Aco 5))).                
          apply hoare_consequence_pre with (P':= [[pre_if]]);
          try apply hoare_consequence_post with (Q':= [[post_if]]).
          + apply hoare_cond. 
          ++ apply WD_Pplus; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred. assumption.
          ++ apply WD_Pplus; try apply WD_Oplus; try apply WD_Pdeter; try apply WD_Dpred. assumption.
          ++ unfold DA_X_plus, B_N_1. 
            apply hoare_consequence_pre with (P':= 
              [[Pdeter (Dpred (Ava X < Aco 5)) ⊕ Pdeter (Dpred (Ava X = Aco 5))]] [X |-> Ava X + Aco 1]).
            -- apply hoare_Dasgn.
            -- apply assert_trans with (R:= [[Pdeter (Dpred (Ava X < Aco 5))]]); try apply Pand_elim_r.
            unfold assert_implies. intros.
            assert (HWFa : WF_aexp_with_pd (Ava X + Aco 1) pd). {
              simpl. unfold WF_aexp_with_pd. 
              apply satisfy_implies_dom_sub in H1; try assumption.
              apply WD_Pdeter; apply WD_Dpred.
            }
            apply pf_sub_eq with (HWFa:= HWFa); try assumption.
            +++ apply WD_Oplus; apply WD_Pdeter; try apply WD_Dpred.
            +++ apply Conseq_DA; try assumption.
            ++ apply hoare_consequence_pre with (P':= [[Pdeter (Dpred (Ava X < Aco 5))]]); 
              try apply hoare_skip; try apply Pand_elim_r.
          + unfold phi_inv, post_if. 
            apply assert_trans with (R:= [[Pdeter (Dpred B_X_5) ⊕ phi1]]).
            ++ unfold assert_implies. intros pd H HZ H0. 
              apply Oplus in H0; try assumption.
              -- apply OplusC in H0; try assumption.
                apply OplusA in H0; try assumption.
                ** apply Oplus_elim_left in H0; try assumption; simpl; try apply I.
                apply WD_Oplus; apply WD_Pdeter; try apply WD_Dpred.
                ** apply WD_Oplus; try apply WD_Oplus; try apply WD_Pdeter; try apply WD_Dpred.
              -- apply satisfy_implies_dom_sub in H0; try assumption. 
                ** simpl. simpl in H0. 
                destruct (Rle_lt_dec (1 / 2) 0) eqn: Hl;
                destruct (Rle_lt_dec 1 (1 / 2)) eqn: Hr; simpl; try assumption.
                ** apply WD_Pplus; try apply WD_Oplus; try apply WD_Pdeter; try apply WD_Dpred. assumption.
              -- simpl. apply satisfy_implies_dom_sub in H0; try assumption. 
                *** simpl in H0. 
                destruct (Rle_lt_dec (1 / 2) 0) eqn: Hl;
                destruct (Rle_lt_dec 1 (1 / 2)) eqn: Hr; simpl; try assumption.
                *** apply WD_Pplus; try apply WD_Oplus; try apply WD_Pdeter; try apply WD_Dpred. assumption.
            ++ apply OCon_Oplus; try assumption; try reflexivity.
              -- apply Conj_True. apply WD_Pdeter; try apply WD_Dpred.
              -- unfold B_X_5, phi1. unfold assert_implies. intros pd H HZ H0. 
                split; try assumption. destruct H0. split; try assumption.
                intros. specialize (H1 st H2). destruct H1. split; try assumption.
                destruct (evalB_st (Ava X = Aco 5) st) eqn: Hst; try contradiction.
                rewrite evalB_Bnot_involutive. 
                apply evalB_eq_implies_le_rev in Hst.
                rewrite Hst. simpl. apply I.
          + apply assert_trans with (R:= [[(Pdeter (Dpred (Ava N1 = Aco 0)) ⊙ Pdeter (Dpred B_X_5))
                                ⊕[ 1/2 ] (Pdeter (Dpred (Ava N1 = Aco 1)) ⊙ Pdeter (Dpred B_X_5))]]).
            ++ apply OdotD_r; try assumption; try reflexivity.
            apply WD_Odot; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption.
            simpl. destruct (Rle_lt_dec (1 / 2) 0) eqn: Hl;
                destruct (Rle_lt_dec 1 (1 / 2)) eqn: Hr; simpl; try reflexivity.
            ++ apply assert_trans with (R:= [[
             (Pdeter (Dpred (Ava N1 = Aco 1)) ⊙ Pdeter (Dpred B_X_5)) ⊕[ 
              1 / 2 ] (Pdeter (Dpred (Ava N1 = Aco 0)) ⊙ Pdeter (Dpred B_X_5))
            ]]). 
            ** unfold assert_implies. intros. 
              apply PplusC with (p:= 1 / 2); try assumption.
              apply prob_convert; try assumption.
            ** apply OCon_Pplus; try assumption.
            *** apply assert_trans with (R:= [[Pdeter (Dpred (Ava N1 = Aco 1)) ∧ Pdeter (Dpred (Ava X < Aco 5))]]);
                try apply Pand_comm; try apply OdotO; try assumption; apply WD_Pdeter; try apply WD_Dpred.
            *** apply assert_trans with (R:= [[Pdeter (Dpred (Ava N1 = Aco 0)) ∧ Pdeter (Dpred (Ava X < Aco 5))]]);
                try apply OdotO; try assumption; try apply WD_Pdeter; try apply WD_Dpred.
                unfold assert_implies. intros pd H HZ H0. destruct H0. split; try assumption.
                destruct H0. split; try assumption.
                intros. specialize (H2 st H3). destruct H2. split; try assumption.
                destruct (evalB_st (Ava N1 = Aco 0) st) eqn: Hst; try contradiction.
                destruct (evalB_st (~ Ava N1 = Aco 1) st) eqn: Hst2; try apply I.
                rewrite evalB_Bnot_false_iff in Hst2.
                rewrite evalB_sym in Hst. 
                apply evalB_eq_trans with (a0:= (Aco 0)) in Hst2; try assumption.
                simpl in Hst2. apply Qeq_bool_iff in Hst2.
                symmetry in Hst2. 
                apply Q_apart_0_1 in Hst2. contradiction.
        * unfold phiT. apply WD_Odot; try apply WD_Pdeter; try apply WD_Dpred.
              simpl. reflexivity.
        * unfold phi_n. apply WD_Odot; try apply WD_Pdeter; try apply WD_Dpred.
          + try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption.
          + simpl. destruct (Rle_lt_dec (1 / 2) 0) eqn: Hl; simpl; try reflexivity.
            destruct (Rle_lt_dec 1 (1 / 2)) eqn: Hr; simpl; try reflexivity.
        * unfold RA_N. apply NCF_RAssign.
        * apply hoare_consequence_pre with (P':= (
              ([[Pdeter (Dpred (Ava N1 = Aco 0))]] [N1 |-> Aco 0]) /\ 
              ([[Pdeter (Dpred (Ava N1 = Aco 1))]] [N1 |-> Aco 1]))%assertion). 
          + unfold phi_n. unfold Vda_01, da_01. apply hoare_Rasgn.
                  apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try assumption.
          + apply assert_trans with (R:= [[(Pdeter (Dpred Btrue)) ∧ phiT]]); 
                  try apply Conj_True; try apply WD_Pdeter; try apply WD_Dpred.
                  split; try apply Pdeter_always_holds.  
    - unfold assert_implies. intros pd H HZ H0. destruct H0. try assumption. 
    - unfold phi_inv, P0. 
      apply assert_trans with (R:= [[phiT ∧ Pdeter (Dpred B_X_5)]]).
      + apply assert_trans with (R:= [[Pdeter (Dpred B_X_5)]]); try apply Conj_True; try apply WD_Pdeter; 
        try apply WD_Dpred; try assumption.
        unfold B_X_5. unfold assert_implies. 
        intros pd H HZ H0. destruct H0. split; try assumption.
        intros. specialize (H1 st H2). destruct H1. split; try assumption.
        destruct (evalB_st (Ava X = Aco 0) st) eqn: Hst; try contradiction.
        rewrite evalB_not_le_iff_lt_rev; try assumption.
        apply evalBeq_implies_lt_compat_l with (a2:= (Aco 5)) in Hst.
        rewrite Hst. simpl. apply I.
      + unfold assert_implies. intros. right. left. 
        exists pd. split; try assumption. 
        split; try apply pd_equiv_refl.
        split. { simpl. destruct H1. destruct H2. simpl in H2. assumption. }
        split; try assumption.
        reflexivity.
  }

  apply hoare_consequence_pre with (P':= P0 [X |-> (Aco 0)]). 
    + apply hoare_Dasgn. 
    + pose (P1:= [[Pdeter (Dpred (Ava X = Aco 0))]] [X |-> Aco 0]).
      apply assert_trans with (R:= P1). 
      * unfold assert_implies. intros. 
        unfold P1. apply Pdeter_always_holds.
      * unfold assert_implies. intros. 
      assert (HWFa: WF_aexp_with_pd (Aco 0) pd). { 
        unfold WF_aexp_with_pd. simpl. reflexivity. }
      assert (HWD: well_defined_Pf (Pdeter (Dpred (Ava X = Aco 0)))). {
        apply WD_Pdeter. apply WD_Dpred. }
      assert (Htmp: P0 (DAssn_under_pd X (Aco 0) pd HWFa)). {
        apply pf_sub_eq; try assumption. }
      apply pf_sub_eq in Htmp; try assumption.
Qed.