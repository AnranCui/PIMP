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
Require Import Library.DistState.Restrict.
Require Import Library.DistState.Bulid.
Require Import Library.DistState.Partial.
Require Import Library.PIMP.Syntax.
Require Import Library.PIMP.EvalProps.
Require Import Library.PIMP.Semantics.
Require Import Library.Assertion.Asserts.
Require Import Library.Assertion.SemProp.
From Stdlib Require Import micromega.Lra. 
Open Scope list_scope.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope state_scope.
Set Default Goal Selector "!".
(*This file contains all Hoare rules*)
(*Ensure that every variable in mu is assigned an integer value*)
Definition is_inject_Z (q : Q) : Prop :=
  exists z : Z, (q == inject_Z z)%Q.

Definition var_inject_Z (v : option Q) : Prop :=
  match v with
  | Some q => is_inject_Z q
  | None => True  
  end.
Definition state_inject_Z (s : local_st) : Prop :=
  Forall var_inject_Z s.

Fixpoint dst_inject_Z (mu : dist_state) : Prop := 
  match mu with
  | [] => True 
  | (s,p) :: mu' => (state_inject_Z s) /\ dst_inject_Z mu'
  end.

Fixpoint aexp_inject_Z (a: aexp) : Prop := 
  match a with
  | Aco q => is_inject_Z q
  | Ava x => True
  | Apl a1 a2 => (aexp_inject_Z a1) /\ (aexp_inject_Z a2)
  | Amu a1 a2 => (aexp_inject_Z a1) /\ (aexp_inject_Z a2)
  | Asu a1 a2 => (aexp_inject_Z a1) /\ (aexp_inject_Z a2)
  end.

Fixpoint distaexp_inject_Z (da: dist aexp) : Prop := 
  match da with 
  | [] => True 
  | (a,p) :: da' => (aexp_inject_Z a) /\ (distaexp_inject_Z da')
  end.

Fixpoint winstr_inject_Z (c : winstr) : Prop := 
  match c with
  | Skip => True 
  | DAssign x a => aexp_inject_Z a
  | RAssign x Vda => distaexp_inject_Z (proj1_sig Vda)
  | Seq c1 c2 => (winstr_inject_Z c1) /\ (winstr_inject_Z c2)
  | If b c1 c2 => (winstr_inject_Z c1) /\ (winstr_inject_Z c2)
  | While b c => (winstr_inject_Z c)
  end.
(********************Ensure that the mu decomposed by combine also satisfies integers************************************************)
Lemma res_st_inject_Z: forall s X, 
  state_inject_Z s -> state_inject_Z (res_st_to_X s X).
Proof. 
  intros s X H. generalize dependent X. induction s as [|v s' IH]; intros; try assumption. 
  unfold state_inject_Z in *. inversion H; subst. intuition. 
  simpl. destruct v; destruct X; try constructor; auto. 
  destruct b; constructor; auto; try apply I.
Qed.

Lemma res_dst_inject_Z: forall mu X, 
  dst_inject_Z mu -> dst_inject_Z (mu \| X).
Proof.
  intros mu X H. induction mu as [|(s,p) mu' IH]; try apply I. 
  destruct H. simpl. split.
  - apply res_st_inject_Z. assumption.
  - apply IH; try assumption.
Qed.

Lemma st_nil_inject_Z: forall s, s == [] -> state_inject_Z s.
Proof. 
  intros s H. unfold state_inject_Z in *. induction s as [|v s IH]; intros; try auto.
  simpl in *. destruct v; try discriminate.
  apply andb_true_iff in H. destruct H. 
  constructor; intuition. 
  - unfold var_inject_Z, is_inject_Z. apply I. 
  - apply IH. rewrite st_eq_nil_iff_all_none. assumption.
Qed.

Lemma st_eq_inject_Z: forall s s', 
  s == s' -> state_inject_Z s -> state_inject_Z s'. 
Proof. 
  intros s s' Heq H. generalize dependent s'. induction s as [|v s IH]; intros; destruct s' as [|v' s']; intuition.
  - apply st_nil_inject_Z. rewrite state_eq_sym. assumption.
  - unfold state_inject_Z. constructor. 
  - unfold state_inject_Z in *. inversion H; subst.
    destruct v; destruct v'; try auto; try discriminate.
    simpl in Heq. destruct ((q ?= q0)%Q) eqn: Hv; try discriminate.
    intuition. constructor; intuition. inversion H; subst. 
    apply Qeq_alt in Hv. unfold var_inject_Z in H5. destruct H5.
    unfold var_inject_Z, is_inject_Z. exists x. 
    rewrite <- Hv. assumption.
Qed.
Lemma dst_eq_inject_Z: forall mu mu', 
  beq_dst mu mu' = true -> dst_inject_Z mu -> dst_inject_Z mu'.
Proof. 
  intros mu mu' H H'. generalize dependent mu'. 
  induction mu as [|(s,p) mu IH]; intros; destruct mu' as [|(s',p') mu']; try assumption; try apply I. 
  - simpl in H. discriminate H. 
  - simpl in *. destruct H'. 
    apply andb_true_iff in H. destruct H. intuition. 
    apply andb_true_iff in H. destruct H. apply st_eq_inject_Z with (s:= s); try assumption.
Qed.

Lemma insert_inject_Z: forall s p mu, 
  (state_inject_Z s /\ dst_inject_Z mu) <-> dst_inject_Z (insert_st_pair s p mu).
Proof.
  split. 
  - intros [Hs Hmu]. induction mu as [|(s',p') mu' IH]; simpl; intuition.
    destruct (beq_state s s') eqn: Heq; try assumption.
    destruct (ble_state s s') eqn: Hle; constructor; simpl in *; intuition.
  - intros H. induction mu as [|(s',p') mu' IH]; simpl in *; try apply I; intuition. 
    + destruct (beq_state s s') eqn: Heq; try assumption. 
      * inversion H; subst. rewrite state_eq_sym in Heq. apply st_eq_inject_Z with (s:= s'); try assumption.
      * destruct (ble_state s s') eqn: Hle; try constructor; simpl in *; intuition.
    + destruct (beq_state s s') eqn: Heq; try assumption. 
      * inversion H; subst. assumption.
      * destruct (ble_state s s') eqn: Hle; try constructor; simpl in *; intuition.
    + destruct (beq_state s s') eqn: Heq; try assumption. 
      * inversion H; subst. assumption.
      * destruct (ble_state s s') eqn: Hle; try constructor; simpl in *; intuition.
Qed.

Lemma sort_inject_Z: forall mu, 
  dst_inject_Z mu <-> dst_inject_Z (sort_dst mu).
Proof.
  split. 
  - intros H. induction mu as [|(s,p) mu IH]; try apply I. simpl in *. destruct H. 
    apply insert_inject_Z; intuition.
  - intros. induction mu as [|(s,p) mu IH]; try apply I. simpl in *. 
    apply insert_inject_Z in H. destruct H. intuition.
Qed.

Lemma dst_implies_inject_Z: forall mu mu', 
  Valid_dist mu -> Valid_dist mu' -> 
  (mu == mu')%dist_state -> dst_inject_Z mu -> dst_inject_Z mu'.
Proof.
  intros mu0 mu1 HWD0 HWD1 Heq H. 
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
  apply sort_inject_Z. apply dst_eq_inject_Z in Htemp_beq; try assumption. 
  apply sort_inject_Z in H. apply H.
Qed. 

Lemma dst_mult_inject_Z: forall mu p, dst_inject_Z mu -> dst_inject_Z (p * mu)%dist_state.
Proof. 
  intros mu p H. induction mu as [|(s,p') mu IH]; try apply I.
  simpl. destruct (Req_dec_T p 0) eqn: Hp.
  - simpl. apply I.
  - simpl in *. intuition.
Qed. 

Lemma comb_dst_inject_Z: forall pd0 s1 p1 mu1 dom1 pd 
  (HPD1: partial_dst_Prop dom1 ((s1, p1) :: mu1)) (Hdom01: (dom pd0 ∩∅ dom1)%domain),
  Valid_dist (mu pd0) -> Sorted_dst (mu pd0) -> 
  Valid_dist ((s1,p1)::mu1) -> Valid_dist (mu pd) ->
  {|
    dom := (dom pd0 ∪ dom1)%domain;
    mu := mu pd0 ⊗ ((s1,p1)::mu1);
    all_partial := PD_combine_invar_mu pd0 
                      {| dom := dom1; mu := (s1, p1) :: mu1; all_partial := HPD1 |} Hdom01
  |} ⊑ pd -> 
  dst_inject_Z (mu pd) ->
  dst_inject_Z (mu pd0).
Proof. 
  intros pd0 s1 p1 mu1 dom1 pd HPD1 Hdom01 HV0 HS0 HV1 HV Hsub H. destruct Hsub. simpl in *. 
  apply Peq_implies_res_eq with (X:= dom pd0) in H1; try assumption.
  - apply dst_equiv_trans with (mu2:= (sum_probs ((s1, p1) :: mu1) * (mu pd0))%dist_state) in H1.
    * apply dst_equiv_trans with (mu0:= mu pd \| dom pd0) in H1; 
      try apply res_to_subset_equiv; try apply dom_subset_orb_snd_l_r.
      apply res_dst_inject_Z with (X:= dom pd0) in H. 
      assert (Heq: beq_dst (sort_dst (mu pd \| dom pd0)) (sum_probs ((s1, p1) :: mu1) * mu pd0)%dist_state = true). {
      apply Sort_Valid_Peq_implies_beq_True; intuition; 
        try apply Valid_implies_sort_Valid; try apply Valid_after_resX; try apply Valid_mult_cofe; try assumption.
      + apply WF_dist_implies_sortdst_Sorted; apply Valid_after_resX; try assumption.
      + apply Sort_mult_cofe; try assumption.
      + destruct HV1. assumption.
      + apply dst_equiv_trans with (mu1:= mu pd \| dom pd0); try assumption. 
        apply dst_equiv_sym. apply dst_equiv_sort. }
    apply dst_eq_inject_Z in Heq. 
    + simpl in Heq. apply dst_mult_inject_Z with (p:= 1/ (p1 + sum_probs mu1)) in Heq. 
      rewrite dst_mult_assoc_eq in Heq. unfold Rdiv in Heq. 
      rewrite Rmult_1_l in Heq.  
      rewrite <- Rinv_l_sym with (r:= p1+sum_probs mu1) in Heq. 
      ++ rewrite dst_mult_1_l in Heq. assumption.
      ++ intuition. destruct HV1. destruct H4. destruct H4. 
        apply positive_sum_ge_0 in H5. 
        apply Rplus_lt_le_compat with (r3:= 0) (r4:= sum_probs mu1)in H4; try assumption.
        rewrite Rplus_0_l in H4. rewrite H2 in H4. apply Rlt_irrefl in H4. contradiction.
    + apply sort_inject_Z in H; try assumption.
  * apply res_comb_equiv with (pd1:= {| dom := dom1; mu := (s1, p1) :: mu1; all_partial := HPD1 |}); try assumption.
  - apply Valid_after_resX. assumption.
  - apply Valid_after_combine; assumption.
Qed.

Lemma get_inject_Z: forall n s, 
  state_inject_Z s -> is_inject_Z (get n s).
Proof.
  intros. generalize dependent s. induction n; destruct s; simpl in *; intuition.
  - unfold is_inject_Z. exists (-99999)%Z. apply Qeq_refl.
  - destruct o; simpl. 
    + inversion H; subst. simpl in *. assumption.
    + unfold is_inject_Z. exists (-99999)%Z. apply Qeq_refl.
  - unfold is_inject_Z. exists (-99999)%Z. apply Qeq_refl.
  - apply IHn. inversion H; subst. intuition.
Qed.

Lemma st_evalA_inject_Z: forall a s, 
  aexp_inject_Z a -> state_inject_Z s -> 
  is_inject_Z (evalA_st a s).
Proof. 
  intros. generalize dependent s. induction a; intros; simpl in *; intuition; try constructor.
  - apply get_inject_Z. assumption.
  - unfold is_inject_Z. simpl. specialize (H s H0). destruct H. 
    specialize (H3 s H0). destruct H3. 
    exists (x+x0)%Z. rewrite H. rewrite H3. unfold inject_Z.  
    apply Qinv_plus_distr.
  - unfold is_inject_Z. simpl. specialize (H s H0). destruct H. 
    specialize (H3 s H0). destruct H3. 
    exists (x*x0)%Z. rewrite H. rewrite H3. unfold inject_Z. constructor.
  - unfold is_inject_Z. simpl. specialize (H s H0). destruct H. 
    specialize (H3 s H0). destruct H3. 
    exists (x-x0)%Z. rewrite H. rewrite H3. unfold inject_Z. apply Qinv_minus_distr.    
Qed.

Lemma update_inject_Z: forall n q s, 
  is_inject_Z q -> state_inject_Z s -> 
  state_inject_Z (update s n q).
Proof.
  intros. generalize dependent s. induction n; intros; destruct s; simpl; constructor; intuition; try apply I.
  - destruct o; inversion H0; subst; assumption.
  - simpl in *. apply IHn in H0. assumption.
  - unfold state_inject_Z in H0. inversion H0; subst. assumption.
  - unfold state_inject_Z in H0. inversion H0; subst. 
    apply IHn. assumption. 
Qed.

Lemma DA_inject_Z: forall a mu n, 
  aexp_inject_Z a -> dst_inject_Z mu -> 
  dst_inject_Z (DAssn_under_dstate mu n a).
Proof.
 intros. induction mu as [|(s,p) mu IH]; simpl in *; intuition. apply update_inject_Z; try assumption. 
 apply st_evalA_inject_Z; assumption.
Qed. 
Lemma dst_inject_Z_decom: forall mu mu', 
  dst_inject_Z (mu + mu')%dist_state ->
  dst_inject_Z mu /\ dst_inject_Z mu'.
Proof.
  intros. generalize dependent mu'. induction mu as [|(s,p) mu IH]; intros; simpl in *; intuition.
  - apply IH in H1. destruct H1. assumption.
  - apply IH in H1. destruct H1. assumption. 
Qed.

Lemma dst_inject_Z_add: forall mu mu', 
dst_inject_Z mu -> dst_inject_Z mu' ->
  dst_inject_Z (mu + mu')%dist_state.
Proof.
  intros. generalize dependent mu'. induction mu as [|(s,p) mu IH]; intros; simpl in *; intuition.
Qed.

Lemma dista_inject_Z: forall da s p n, 
  distaexp_inject_Z da -> state_inject_Z s -> 
  dst_inject_Z (update_st_with_da s p n da).
Proof.
  intros. generalize dependent s. induction da; intros; simpl in *; intuition.
  destruct a. simpl in *; intuition. 
  apply update_inject_Z; try assumption.
  apply st_evalA_inject_Z; intuition.
Qed.

Lemma RA_inject_Z: forall da mu n, 
  distaexp_inject_Z da -> dst_inject_Z mu -> 
  dst_inject_Z (RAssn_under_dstate mu n da).
Proof.
 intros. induction mu as [|(s,p) mu IH]; simpl in *; intuition. 
 apply dst_inject_Z_add. 
 - apply dista_inject_Z; intuition.
 - assumption.
Qed. 
Lemma getb_inject_Z: forall mu b, 
  dst_inject_Z mu -> dst_inject_Z (get_b_in_mu b mu).
Proof.
  intros. induction mu as [|(s,p) mu IH]; simpl in *; intuition.
  destruct (evalB_st b s); simpl; intuition.
Qed.
Lemma getnotb_inject_Z: forall mu b, 
  dst_inject_Z mu -> dst_inject_Z (get_notb_in_mu b mu).
Proof.
  intros. induction mu as [|(s,p) mu IH]; simpl in *; intuition.
  destruct (evalB_st b s); simpl; intuition.
Qed.

Lemma inject_Z_after_NS: forall c pd pd', 
  NS c pd pd' -> winstr_inject_Z c -> dst_inject_Z (mu pd) -> dst_inject_Z (mu pd').
Proof.
  intros c pd pd' HNS HWc HZ. generalize dependent pd; generalize dependent pd'.
  induction c; intros.
  - inversion HNS; subst. assumption.
  - inversion HNS; subst. simpl in *. apply DA_inject_Z; assumption.
  - inversion HNS; subst. simpl in *. apply RA_inject_Z; assumption.
  - inversion HNS; subst. simpl in *. destruct HWc. 
    apply IHc2 with (pd:= pd1); intuition.
    apply H4 with (pd:= pd); intuition.
  - simpl in HWc. inversion HNS; subst.
    + simpl. apply I.
    + apply IHc1 with (pd:= pd); intuition.
    + apply IHc2 with (pd:= pd); intuition.
    + rewrite H9. apply dst_inject_Z_add. 
      * apply IHc1 with (pd:= pd_b); intuition; simpl; apply getb_inject_Z; assumption.
      * apply IHc2 with (pd:= pd_notb); intuition; simpl; apply getnotb_inject_Z; assumption.
  - remember (While b c) as original_command eqn:Horig.
    induction HNS; try inversion Horig; subst. 
    + simpl. apply I.
    + apply IHHNS2; intuition. apply H4 with (pd:= pd); intuition. 
    + assumption.
    + rewrite H4. apply dst_inject_Z_add; intuition. 
      * apply H8; intuition. apply H7 with (pd:= pd_b); intuition. apply getb_inject_Z; assumption.
      * apply getnotb_inject_Z; assumption.
Qed.

(******************************************************)
Declare Scope hoare_spec_scope. 
Definition hoare_triple (P : PAssertion) (c : winstr) (Q : PAssertion) : Prop := (*The definition of Hoare triplets*)
  forall pd pd', 
  Valid_dist (mu pd) -> dst_inject_Z (mu pd) -> winstr_inject_Z c ->
  pd =[ c ]=> pd' -> 
  P pd -> Q pd'.
Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q) (at level 90, c at level 99) : hoare_spec_scope.
Definition assert_implies (P Q : PAssertion) : Prop := 
  forall pd, Valid_dist (mu pd) -> dst_inject_Z (mu pd) -> P pd -> Q pd.
Declare Scope hoare_spec_scope.
Open Scope hoare_spec_scope.
Notation "P ->> Q" := (assert_implies P Q)   (at level 80) : hoare_spec_scope.
Notation "P <<->> Q" := (P ->> Q /\ Q ->> P)    (at level 80) : hoare_spec_scope.
Declare Scope assertion_scope.
Bind Scope assertion_scope with PAssertion.
Bind Scope assertion_scope with DAssertion.
Delimit Scope assertion_scope with assertion.

Lemma assert_trans: forall P R Q, 
  P ->> R ->  R ->> Q -> P ->> Q.
Proof.
  intros. unfold assert_implies in *. intros. 
  apply H0; try assumption. apply H; assumption. 
Qed.
(**************Rules************************)
Theorem hoare_skip : forall P, {{P}} SKIP {{P}}.
Proof.
intros P mu mu' Hvalid HZ HZc Hhoare Himp. 
inversion Hhoare; subst. 
assumption.
Qed.
(**********************************)
(** *** Evaluation *)
Definition DAssertion_sub_Q (P:DAssertion) (X:nat) (r: Q) : DAssertion := 
  fun (st : local_st) => P (update st X r).  
Definition DAssertion_sub_aexp (P:DAssertion) (X:nat) (a: aexp) : DAssertion := 
  fun (st : local_st) => P (update st X (evalA_st a st)). 
Definition PAssertion_sub (P : PAssertion) (X : nat) (a : aexp) : PAssertion := 
  fun (pd : partial_dist) => 
    forall (HWFa : WF_aexp_with_pd a pd),
      P (DAssn_under_pd X a pd HWFa).
Notation "P [ X |-> a ]" := (PAssertion_sub P X a) (at level 10, X at next level).

Lemma pf_sub_eq: forall X a pf pd (HWFa : WF_aexp_with_pd a pd), 
  well_defined_Pf pf -> Valid_dist (mu pd) ->
  ([[pf]] [X |-> a] pd <-> [[pf]] (DAssn_under_pd X a pd HWFa)).
Proof.
  intros X a pf pd HWFa HWD HV.
  split.
  - intros. unfold PAssertion_sub in H. apply H.
  - intros. unfold PAssertion_sub. intros. 
    assert (Heq: (DAssn_under_pd X a pd HWFa0) ≡ (DAssn_under_pd X a pd HWFa)). {
      split; simpl. - apply dom_equiv_refl. - apply dst_equiv_refl. }
    apply pd_equiv_preserves_sem with (pd0:= DAssn_under_pd X a pd HWFa); 
      try assumption; simpl; apply Valid_after_DA; try assumption.
Qed.

Theorem hoare_Dasgn : forall Q X a, {{(Q [X |-> a])}} X ::= a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a mu mu' Hvalid HZ HZc HNS HQ.
  inversion HNS; subst.  
  apply HQ. 
Qed.
(**********************************)
Definition PAssertion_and (P1 P2: PAssertion): PAssertion := ((P1 /\ P2)%assertion).
Lemma valid_da_of_two: forall (a1 a2 : aexp) (p : R) (Hp : 0 < p < 1), 
  let da:= [(a1, p); (a2, 1 - p)] in
  positive_probs da /\ sum_probs da = 1%R.
Proof.
  intros a1 a2 p Hp da. 
  unfold positive_probs. simpl. split; try assumption.
  - split; unfold prob_is_positive; split; try apply I. 
    + destruct Hp; assumption. 
    + destruct Hp. apply Rlt_le. assumption. 
    + apply Rp_lt1_minus_p_bounds with (p:= p) in Hp. destruct Hp.
    split; try assumption. apply Rlt_le. assumption. 
  - rewrite Rplus_0_r. apply R_plus_sub_eq_1.
Qed.

Theorem hoare_Rasgn : 
  forall phi1 phi2 (X : nat) (a1 a2 : aexp) (p : R) (Hp : 0%R < p < 1%R),
  let Vda := exist _ [(a1, p); (a2, 1 - p)] 
                  (valid_da_of_two a1 a2 p Hp) in 
  well_defined_Pf (Pplus (p) phi1 phi2) ->  
    {{ ([[phi1]] [X |-> a1]) /\ ([[phi2]] [X |-> a2]) }}
        X $= Vda
    {{ [[Pplus (p) phi1 phi2]] }}.
Proof. 
  unfold hoare_triple.   
  intros phi1 phi2 X a1 a2 p Hp HWD pd pd' HV HZ HZc H Hsem.
  destruct Hsem. 
  inversion H; subst. simpl in *. 
  destruct HWFa as [HWFa1 HWFa]. 
  destruct HWFa as [HWFa2 HWFa]. 
  left. split; try assumption.
  inversion HWD; subst.
  pose (pd1:= DAssn_under_pd X a1 pd HWFa1).
  pose (pd2:= DAssn_under_pd X a2 pd HWFa2).
  exists pd1, pd2. 
  split. { simpl. apply Valid_after_DA. try assumption. }
  split. { simpl. apply Valid_after_DA. try assumption. }
  split. { simpl. apply dom_equiv_refl. }
  split. { simpl. apply dom_equiv_refl. }
  split. { apply pf_sub_eq; try assumption. }
  split. { apply pf_sub_eq; try assumption. }
  split. { simpl. rewrite RA_preserve_sum_prob. 
    - apply DA_preserve_sum_prob. - apply valid_da_of_two. assumption. }
  split. { simpl. rewrite RA_preserve_sum_prob. 
    - apply DA_preserve_sum_prob. - apply valid_da_of_two. assumption. }
  simpl. apply RA_DA_equiv.
Qed.
(**********************************)
Theorem hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1;; c2 {{R}}.
Proof.
  unfold hoare_triple.
  intros P Q R c1 c2 H1 H2 mu mu' Hvalid HZ HZc H12 HP.
  inversion H12; subst.
  apply H1 with (pd:= pd1); try assumption. 
  - apply Valid_forall_NS in H5; try assumption.
  - simpl in HZc. apply inject_Z_after_NS in H5; intuition.  
  - destruct HZc. assumption.
  - simpl in HZc. apply H2 with (pd:= mu); try intuition.
Qed.
(**********************************)
Theorem hoare_cond: forall phi1 phi2 phi1' phi2' c1 c2 Bp b, 
  well_defined_Pf (Pplus Bp (Pand phi1 (Pdeter (Dpred b))) (Pand phi2 (Pdeter (Dpred (Bnot b))))) ->
  well_defined_Pf (Pplus Bp phi1' phi2') ->
  {{[[Pand phi1 (Pdeter (Dpred b))]]}} c1 {{[[phi1']]}} -> 
  {{[[Pand phi2 (Pdeter (Dpred (Bnot b)))]]}} c2 {{[[phi2']]}} -> 
  {{[[Pplus Bp (Pand phi1 (Pdeter (Dpred b))) (Pand phi2 (Pdeter (Dpred (Bnot b))))]]}} 
    IF b THEN c1 ELSE c2 FI {{[[Pplus Bp phi1' phi2']]}}.
Proof.
  intros phi1 phi2 phi1' phi2' c1 c2 p b HWD_pre HWD_post Hc1 Hc2.
  unfold hoare_triple.
  intros pd pd' Hvalid HZ HZc HNS H. 
  destruct HZc as [HZc1 HZc2]. 
  inversion HNS; subst. 
  - apply emp_dst_satisfies_phi; try assumption. 
    inversion HWD_pre; subst. 
    destruct H9. destruct H0. destruct H10. destruct H2. 
    apply satisfy_implies_dom_sub in H; try assumption. simpl in H.
    apply pd_Nil_mu in H4. 
    simpl. destruct (Rle_lt_dec p 0). 
    + assert (HNSx0: NS c2 pd x0); try assumption.
      apply Hc2 in H9; try assumption. 
      assert (Hpd2: [[phi2 ∧ Pdeter (Dpred (~ b))]] pd ). { 
        apply pd_equiv_preserves_sem with (pd0:= pd_emp (dom pd)); try assumption.
        - apply Valid_dist_nil.
        - split; simpl; try apply dom_equiv_refl. rewrite H4. apply dst_equiv_refl.
        - apply emp_dst_satisfies_phi; try assumption. }
      specialize (H9 Hpd2). inversion HWD_post; subst. 
      apply satisfy_implies_dom_sub in H9; try assumption. 
      apply orbdom_after_NS in HNSx0. 
      apply dom_subset_trans with (l1:= dom x0); try assumption.
      apply dom_equiv_sym in HNSx0.
      apply dom_subset_eq_compat_right with (X:= (dom pd ∪ get_modvar_in_winstr c2)%domain); try assumption.
      apply dom_subset_orb_compat; try apply dom_subset_refl.
      apply dom_subset_orb_snd_l_r.
    + destruct (Rle_lt_dec 1 p). 
      * assert (HNSx: NS c1 pd x); try assumption.
        apply Hc1 in H1; try assumption. 
        assert (Hpd1: [[phi1 ∧ Pdeter (Dpred (b))]] pd ). { 
          apply pd_equiv_preserves_sem with (pd0:= pd_emp (dom pd)); try assumption.
          - apply Valid_dist_nil.
          - split; simpl; try apply dom_equiv_refl. rewrite H4. apply dst_equiv_refl.
          - apply emp_dst_satisfies_phi; try assumption. }
        specialize (H1 Hpd1). inversion HWD_post; subst. 
        apply satisfy_implies_dom_sub in H1; try assumption. 
        apply orbdom_after_NS in HNSx. 
        apply dom_subset_trans with (l1:= dom x); try assumption.
        apply dom_equiv_sym in HNSx.
        apply dom_subset_eq_compat_right with (X:= (dom pd ∪ get_modvar_in_winstr c1)%domain); try assumption.
        apply dom_subset_orb_compat; try apply dom_subset_refl.
        apply dom_subset_orb_snd_l_r.
      * assert (HNSx: NS c1 pd x); try assumption.
        apply Hc1 in H1; try assumption.
        assert (Hpd1: [[phi1 ∧ Pdeter (Dpred (b))]] pd ). { 
          apply pd_equiv_preserves_sem with (pd0:= pd_emp (dom pd)); try assumption.
          - apply Valid_dist_nil.
          - split; simpl; try apply dom_equiv_refl. rewrite H4. apply dst_equiv_refl.
          - apply emp_dst_satisfies_phi; try assumption. 
          simpl. apply dom_subset_orb_fst_iff in H. destruct H. assumption. }
        specialize (H1 Hpd1). inversion HWD_post; subst. 
        apply satisfy_implies_dom_sub in H1; try assumption. 
        apply orbdom_after_NS in HNSx. 
        assert (HNSx0: NS c2 pd x0); try assumption. 
        apply Hc2 in H9; try assumption. 
        assert (Hpd2: [[phi2 ∧ Pdeter (Dpred (~ b))]] pd ). { 
          apply pd_equiv_preserves_sem with (pd0:= pd_emp (dom pd)); try assumption.
          - apply Valid_dist_nil.
          - split; simpl; try apply dom_equiv_refl. rewrite H4. apply dst_equiv_refl.
          - apply emp_dst_satisfies_phi; try assumption. 
          simpl. apply dom_subset_orb_fst_iff in H. destruct H. assumption. }
        specialize (H9 Hpd2). inversion HWD_post; subst. 
        apply satisfy_implies_dom_sub in H9; try assumption. 
        apply orbdom_after_NS in HNSx0.
        apply dom_subset_trans with (l1:= ((dom x) ∪ (dom x0))%domain); try assumption. 
        ++ apply dom_subset_orb_compat; try assumption.
        ++ apply dom_subset_eq_compat_left with (X:= ((dom pd ∪ get_modvar_in_winstr c1) ∪ (dom pd ∪ get_modvar_in_winstr c2))%domain); try assumption.
        -- apply dom_equiv_sym. apply dom_eq_orb_dis_r.
        -- destruct HNSx. destruct HNSx0. apply dom_subset_orb_compat; try assumption.
  - destruct H. 
    + destruct H as [Hp_case1 H]. destruct H as [pd01 H]. destruct H as [pd02 H].
      destruct H as [HWF01 H]. destruct H as [HWF02 H]. 
      destruct H as [Hdom01 H]. destruct H as [Hdom02 H].
      destruct H as [Hsem01 H]. destruct H as [Hsem02 H].
      destruct H as [Hsum0 H]. destruct H as [Hsum1 Hmu].
      assert (Hvalid': Valid_dist (p * mu pd01 + (1 - p) * mu pd02)%dist_state). { 
          apply Valid_linear; try assumption. 
          - apply Rbound_loss. assumption.
          - apply Rp_1_minus_p_bounds with (p:= p). apply Rbound_loss. assumption.
          - rewrite R_plus_sub_eq_1. apply Rle_refl. }
      assert (HPD': partial_dst_Prop (dom pd) (p * mu pd01 + (1 - p) * mu pd02)%dist_state). {
        apply PD_linear; try assumption. 
        - destruct Hp_case1. apply Rlt_le. assumption.
        - apply Rp_1_minus_p_bounds. apply Rbound_loss. assumption. }
      pose (pd_tmp:= Build_partial_dist (dom pd) (p * mu pd01 + (1 - p) * mu pd02)%dist_state HPD').
      assert (Heq: pd ≡ pd_tmp). { split; simpl; try apply dom_equiv_refl. assumption. }
      destruct pd02 as [dom02 mu02 HPD02]. destruct mu02 as [|(s02, p02) mu02']. 
      * simpl in Hmu. rewrite dst_add_0_r in Hmu. 
      simpl in Hdom02. simpl in Hsum1. rewrite <- Hsum1 in Hsum0.
      assert (Hmu_nil: mu pd = []). { 
        apply sum_probs0_implies_nil; try assumption.
        apply dst_equiv_implies_sum_probs_eq in Hmu; try assumption.
        - rewrite dst_sum_prob_coef_mult in Hmu. rewrite Hsum0 in Hmu. rewrite Rmult_0_r in Hmu. assumption.
        - apply Valid_mult_cofe; try assumption. apply Rbound_loss. assumption. }
      unfold b_supp_classify in H4. rewrite Hmu_nil in H4. discriminate H4.
      * destruct Hsem02. destruct H0. simpl in H1. specialize (H1 s02).
      assert (Hin: is_in_supp s02 (supp_mu ((s02, p02) :: mu02')) = true) by apply in_supp_mu_cons_head.
      specialize (H1 Hin). destruct H1. 
      destruct (negb (evalB_st b s02)) eqn: Hs02; try contradiction.
      apply negb_true_iff in Hs02. 
      rewrite dst_equiv_implies_b_classify with (pd1:= pd_tmp) in H4; try assumption.
      assert (Htmp: [[Pdeter (Dpred b)]] pd_tmp). { 
        apply bT_sem_iff. split; try assumption.
        right. assumption. }
      destruct Htmp as [Hem' Hcontra].
      specialize (Hcontra s02). 
      assert (Hin': is_in_supp s02 (supp_mu (mu pd_tmp)) = true).  {
        apply in_supp_iff_posi_prob; try assumption; try assumption.  
          pose (p':= (get_prob_in_dstate (p * mu pd01)%dist_state s02 + (1-p) * p02 + get_prob_in_dstate ((1-p)*mu02')%dist_state s02)%R).
          exists p'. simpl. destruct (Req_dec_T (1 - p) 0). 
          -- apply Rp_lt1_minus_p_bounds with (p:= p) in Hp_case1. destruct Hp_case1 as [Hp_].
          rewrite e in Hp_. apply Rlt_irrefl in Hp_. contradiction.
          -- rewrite get_prob_decom. rewrite dst_cons_eq_add.
          rewrite get_prob_decom. simpl. rewrite state_eq_refl. 
          rewrite Rplus_0_r. rewrite <- Rplus_assoc.
          split; try reflexivity. unfold p'.
          apply Valid_add_decom in Hvalid'. destruct Hvalid'. 
          simpl in H7. destruct (Req_dec_T (1 - p) 0) eqn: Hpmins. 
          --- apply Rp_lt1_minus_p_bounds with (p:= p) in Hp_case1. destruct Hp_case1 as [Hp_].
          rewrite e in Hp_. apply Rlt_irrefl in Hp_. contradiction.
          --- simpl in H9. rewrite Hpmins in H9.  
          rewrite dst_cons_eq_add in H9. 
          apply Valid_add_decom in H9. destruct H9. 
          apply Rplus_lt_le_0_compat. 
          ++ apply Rplus_le_lt_0_compat. 
          ** apply dst_Valid_prob_0_1. assumption.
          ** destruct H9. destruct H13. destruct H13. assumption. 
          ++ apply dst_Valid_prob_0_1. assumption. }
      specialize (Hcontra Hin'). simpl in Hcontra. destruct Hcontra as [_ Hcontra].
      rewrite Hs02 in Hcontra. contradiction.
    + destruct H as [Hp_case2 | Hp_case3]. 
      * destruct Hp_case2 as [Hp' H]. destruct H. 
        destruct H as [Hvalidx H]. destruct H as [Heq H].
        destruct H as [Hsem1 Hsum].
        right. left. split; try assumption.
        exists pd'.
        assert (Hsem1_mu: [[phi1 ∧ Pdeter (Dpred b)]] pd). {
          apply pd_equiv_preserves_sem with (pd0:= x); try assumption. 
          - inversion HWD_pre; subst. try assumption. 
          - apply pd_equiv_sym. assumption. }  
        specialize (Hc1 pd pd' Hvalid HZ HZc1 H10 Hsem1_mu). 
        split. { apply Valid_forall_NS in H10; assumption. }
        split. { apply pd_equiv_refl. }
        split; try assumption. 
        reflexivity.
      * destruct Hp_case3 as [Hp' H]. destruct H. 
        destruct H as [Hvalidx H]. destruct H as [Heq H].
        destruct H as [Hsem2 Hsum]. destruct Hsem2 as [Hsem2 Hcontra].
        apply dst_equiv_implies_b_classify with (b:= b) in Heq; try assumption.
        rewrite <- Heq in H4.
        apply bF_sem_iff in Hcontra. destruct Hcontra as [_ Hcontra].
        rewrite H4 in Hcontra. 
         destruct Hcontra; discriminate.
  - destruct H. 
    + destruct H as [Hp_case1 H]. destruct H as [pd01 H]. destruct H as [pd02 H].
      destruct H as [HWF01 H]. destruct H as [HWF02 H]. 
      destruct H as [Hdom01 H]. destruct H as [Hdom02 H].
      destruct H as [Hsem01 H]. destruct H as [Hsem02 H]. 
      destruct H as [Hsum0 H]. destruct H as [Hsum1 Hmu].
      assert (Hvalid': Valid_dist (p * mu pd01 + (1 - p) * mu pd02)%dist_state). { 
          apply Valid_linear; try assumption. 
          - apply Rbound_loss. assumption.
          - apply Rp_1_minus_p_bounds. apply Rbound_loss. assumption.
          - rewrite R_plus_sub_eq_1. apply Rle_refl. }
      assert (HPD': partial_dst_Prop (dom pd) (p * mu pd01 + (1 - p) * mu pd02)%dist_state). {
        apply PD_linear; try assumption. 
        - apply Rbound_loss. assumption.
        - apply Rp_1_minus_p_bounds. apply Rbound_loss. assumption. }
      pose (pd_tmp:= Build_partial_dist (dom pd) (p * mu pd01 + (1 - p) * mu pd02)%dist_state HPD').
      assert (Heq: pd ≡ pd_tmp). { split; simpl; try apply dom_equiv_refl. assumption. }
      destruct pd01 as [dom01 mu01 HPD01]. destruct mu01 as [|(s02, p02) mu02']. 
      * simpl in Hmu. 
        simpl in Hdom01. simpl in Hsum0. rewrite <- Hsum0 in Hsum1.
        assert (Hmu_nil: mu pd = []). { 
          apply sum_probs0_implies_nil; try assumption.
          apply dst_equiv_implies_sum_probs_eq in Hmu; try assumption.
          rewrite dst_sum_prob_coef_mult in Hmu. rewrite Hsum1 in Hmu. rewrite Rmult_0_r in Hmu. assumption. }
        unfold b_supp_classify in H4. rewrite Hmu_nil in H4.
        simpl in H4. 
        discriminate H4.
      * destruct Hsem01. destruct H0. simpl in H1. specialize (H1 s02).
        assert (Hin: is_in_supp s02 (supp_mu ((s02, p02) :: mu02')) = true) by apply in_supp_mu_cons_head.
        specialize (H1 Hin). destruct H1. 
        destruct ((evalB_st b s02)) eqn: Hs02; try contradiction.
        rewrite dst_equiv_implies_b_classify with (pd1:= pd_tmp) in H4; try assumption.
        assert (Htmp: [[Pdeter (Dpred (~b))]] pd_tmp). { 
          apply bF_sem_iff. split; try assumption.
          right. assumption. }
        destruct Htmp as [Hem' Hcontra].
        specialize (Hcontra s02). 
        assert (Hin': is_in_supp s02 (supp_mu (mu pd_tmp)) = true).  {
          apply in_supp_iff_posi_prob; try assumption; try assumption.  
            pose (p':= ( p * p02 + get_prob_in_dstate (p * mu02')%dist_state s02 +  get_prob_in_dstate ((1-p)* (mu pd02))%dist_state s02)%R).
            exists p'. simpl. destruct (Req_dec_T p 0). 
            -- destruct Hp_case1 as [Hp_].
            rewrite e in Hp_. apply Rlt_irrefl in Hp_. contradiction.
            -- rewrite get_prob_decom. rewrite dst_cons_eq_add.
            rewrite get_prob_decom. simpl. rewrite state_eq_refl. 
            rewrite Rplus_0_r. 
            split; try reflexivity. unfold p'.
            apply Valid_add_decom in Hvalid'. destruct Hvalid'. 
            simpl in H8. destruct (Req_dec_T p 0) eqn: Hp0. 
            --- destruct Hp_case1 as [Hp_].
            rewrite e in Hp_. apply Rlt_irrefl in Hp_. contradiction.
            --- rewrite dst_cons_eq_add in H8. 
            apply Valid_add_decom in H8. destruct H8. 
            apply Rplus_lt_le_0_compat. 
            ++ apply Rplus_lt_le_0_compat. 
            ** destruct H8. destruct H13. destruct H13. assumption. 
            ** apply dst_Valid_prob_0_1. assumption.
            ++ apply dst_Valid_prob_0_1. assumption. }
        specialize (Hcontra Hin'). simpl in Hcontra. destruct Hcontra as [_ Hcontra].
        rewrite Hs02 in Hcontra. contradiction.
    + destruct H as [Hp_case2 | Hp_case3]. 
      * destruct Hp_case2 as [Hp' H]. destruct H. 
        destruct H as [Hvalidx H]. destruct H as [Heq H].
        destruct H as [Hsem1 Hsum]. 
        destruct Hsem1 as [Hsem1 Hcontra].
        apply dst_equiv_implies_b_classify with (b:= b) in Heq; try assumption.
        rewrite <- Heq in H4.
        apply bT_sem_iff in Hcontra. destruct Hcontra as [_ Hcontra].
        rewrite H4 in Hcontra.
        destruct Hcontra; discriminate.
      * destruct Hp_case3 as [Hp' H]. destruct H. 
        destruct H as [Hvalidx H]. destruct H as [Heq H].
        destruct H as [Hsem1 Hsum].
        right. right. split; try assumption.
        exists pd'.
        assert (Hsem2_mu: [[phi2 ∧ Pdeter (Dpred (~b))]] pd). {
            apply pd_equiv_preserves_sem with (pd0:= x); try assumption. 
            - inversion HWD_pre; subst. try assumption. 
            - apply pd_equiv_sym. assumption.
          }  
        specialize (Hc2 pd pd' Hvalid HZ HZc2 H10 Hsem2_mu). 
        split. { apply Valid_forall_NS in H10; assumption. }
        split. { apply pd_equiv_refl. }
        split; try assumption. 
        reflexivity.
  - destruct H. 
    + destruct H as [Hp_case1 H]. destruct H as [pd01 H]. destruct H as [pd02 H].
      destruct H as [HWF01 H]. destruct H as [HWF02 H]. 
      destruct H as [Hdom01 H]. destruct H as [Hdom02 H].
      destruct H as [Hsem01 H]. destruct H as [Hsem02 H].
      destruct H as [Hsum01 H]. destruct H as [Hsum02 Hmu]. 
      assert (Hvl: Valid_dist (p * mu pd01 + (1 - p) * mu pd02)%dist_state). {
        apply Valid_linear_under_eq_prob; try assumption. 
        - apply Rbound_loss. assumption.
        - apply Rp_1_minus_p_bounds. apply Rbound_loss. assumption.
        - rewrite Hsum01. rewrite Hsum02. 
        rewrite <- Rmult_plus_distr_r. rewrite R_plus_sub_eq_1. rewrite Rmult_1_l. 
        destruct Hvalid. assumption. }
      simpl. left. split; try assumption. 
      destruct pd01 as [dom01 mu01 HPD01]. destruct pd02 as [dom02 mu02 HPD02].
      destruct (mu01) as [|(s01, p01) mu01']; destruct (mu02) as [|(s02, p02) mu02'].
      { 
        simpl in Hmu. 
        assert (Hmu_nil: mu pd = []). { 
          apply sum_probs0_implies_nil; try assumption.
          apply dst_equiv_implies_sum_probs_eq in Hmu; try assumption. }
        unfold b_supp_classify in H4. rewrite Hmu_nil in H4.
        discriminate H4.
      }
      { 
        simpl in Hsum01. simpl in Hsum02. rewrite <- Hsum01 in Hsum02. 
        destruct HWF02 as [Hsum Hpos]. destruct Hpos. destruct H. 
        apply positive_sum_ge_0 in H0. 
        assert (Hcontra: (0 < (p02 + sum_probs mu02'))%R). {
          apply Rplus_lt_le_0_compat; try assumption. }
        rewrite Hsum02 in Hcontra. apply Rlt_irrefl in Hcontra. contradiction. }
      { 
        simpl in Hsum01. simpl in Hsum02. rewrite <- Hsum02 in Hsum01. 
        destruct HWF01 as [Hsum Hpos]. destruct Hpos. destruct H. 
        apply positive_sum_ge_0 in H0. 
        assert (Hcontra: (0 < (p01 + sum_probs mu01'))%R). {
          apply Rplus_lt_le_0_compat; try assumption. }
        rewrite Hsum01 in Hcontra. apply Rlt_irrefl in Hcontra. contradiction. }
      { 
        pose (pd01:= {| dom := dom01; mu := (s01, p01) :: mu01'; all_partial := HPD01 |}).
        pose (pd02:= {| dom := dom02; mu := (s02, p02) :: mu02'; all_partial := HPD02 |}).
        assert(Hmu_copy: (mu pd ==
   p * mu {| dom := dom01; mu := (s01, p01) :: mu01'; all_partial := HPD01 |} +
   (1 - p) * mu {| dom := dom02; mu := (s02, p02) :: mu02'; all_partial := HPD02 |})%dist_state) by assumption.
        apply linear_NS with (c:= If b c1 c2) (pd':= pd') in Hmu; try assumption.
        * destruct Hmu as [x1 H]. destruct H as [x2 H]. 
          destruct H as [HNSx1 H]. destruct H as [HNSx2 H].
          destruct H as [Hmu' H]. destruct H as [Hdom1' Hdom2'].
          exists x1, x2.
          assert (Hvalidx1: Valid_dist (mu x1)). { 
            eapply Valid_forall_NS; try assumption. 
            - apply HWF01. - apply HNSx1. }
          assert (Hvalidx2: Valid_dist (mu x2)). { 
            eapply Valid_forall_NS; try assumption. 
            - apply HWF02. - apply HNSx2. }
          split; try assumption. split; try assumption.
          split. { apply dom_equiv_sym. assumption. }
          split. { apply dom_equiv_sym. assumption. }
          assert (Htemp_x1: pd01 =[ c1 ]=> x1). {
            inversion HNSx1; subst; try assumption. 
            - apply pd_Nil_mu in H11. simpl in H11. discriminate.
            - destruct Hsem01 as [_ Hcontra]. 
            apply bT_sem_iff in Hcontra. destruct Hcontra as [_ Hcontra].
            rewrite H11 in Hcontra. 
            destruct Hcontra; try discriminate. (*H16 Hsem01: contradiction*) 
            - destruct Hsem01 as [_ Hcontra]. 
            apply bT_sem_iff in Hcontra. destruct Hcontra as [_ Hcontra].
            rewrite H11 in Hcontra. destruct Hcontra; try discriminate. }
          split. { unfold hoare_triple in Hc1. apply Hc1 with (pd:= pd01); try assumption.
            apply dst_implies_inject_Z in Hmu_copy; try assumption. 
            apply dst_inject_Z_decom in Hmu_copy. destruct Hmu_copy.
            apply dst_mult_inject_Z with (p:= / p) in H. 
            rewrite dst_mult_assoc_eq in H. rewrite <- Rinv_l_sym in H. 
            - rewrite dst_mult_1_l in H. assumption.
            - unfold not. intros. destruct Hp_case1 as [Hpgt0 Hplt1].
            rewrite H1 in Hpgt0. apply Rlt_irrefl in Hpgt0. contradiction.
          }
          assert (Htemp_x2: pd02 =[ c2 ]=> x2). {
            inversion HNSx2; subst; try assumption.
            - apply pd_Nil_mu in H11. simpl in H11. discriminate.
            - destruct Hsem02 as [_ Hcontra]. 
            apply bF_sem_iff in Hcontra. destruct Hcontra as [_ Hcontra].
            rewrite H11 in Hcontra. destruct Hcontra; try discriminate. 
            - destruct Hsem02 as [_ Hcontra]. 
            apply bF_sem_iff in Hcontra. destruct Hcontra as [_ Hcontra].
            rewrite H11 in Hcontra. destruct Hcontra; discriminate. }
          split. { unfold hoare_triple in Hc2. apply Hc2 with (pd:= pd02); try assumption.
            apply dst_implies_inject_Z in Hmu_copy; try assumption. 
            apply dst_inject_Z_decom in Hmu_copy. destruct Hmu_copy.
            apply dst_mult_inject_Z with (p:= / (1- p)) in H0. 
            rewrite dst_mult_assoc_eq in H0. rewrite <- Rinv_l_sym in H0. 
            - rewrite dst_mult_1_l in H0. assumption.
            - unfold not. intros. apply Rp_lt1_minus_p_bounds in Hp_case1. 
              destruct Hp_case1 as [Hpgt0 Hplt1].
              rewrite H1 in Hpgt0. apply Rlt_irrefl in Hpgt0. contradiction.
            }
          split. { 
            apply NS_preserve_sum_eq in Htemp_x1; try assumption.
            apply NS_preserve_sum_eq in Htemp_x2; try assumption.
            apply NS_preserve_sum_eq in HNS; try assumption.
            rewrite <- Htemp_x1. simpl. simpl in Hsum01. rewrite Hsum01. rewrite HNS. reflexivity. } 
          split. { 
            apply NS_preserve_sum_eq in Htemp_x1; try assumption.
            apply NS_preserve_sum_eq in Htemp_x2; try assumption.
            apply NS_preserve_sum_eq in HNS; try assumption.
            rewrite <- Htemp_x2. simpl. simpl in Hsum02. rewrite Hsum02. rewrite HNS. reflexivity. }
          assumption.
      * apply dom_equiv_sym in Hdom01. apply dom_equiv_sym in Hdom02. split; try assumption. }
    + destruct H as [Hp_case2 | Hp_case3]. 
      * destruct Hp_case2 as [Hp' H]. destruct H. 
        destruct H as [Hvalidx H]. destruct H as [Heq H].
        destruct H as [Hsem1 Hsum]. destruct Hsem1 as [Hsem1 Hcontra].
        apply dst_equiv_implies_b_classify with (b:= b) in Heq; try assumption.
        rewrite <- Heq in H4.
        apply bT_sem_iff in Hcontra. destruct Hcontra as [_ Hcontra].
        rewrite H4 in Hcontra. destruct Hcontra; discriminate.
      * destruct Hp_case3 as [Hp' H]. destruct H. 
        destruct H as [Hvalidx H]. destruct H as [Heq H].
        destruct H as [Hsem2 Hsum]. destruct Hsem2 as [Hsem2 Hcontra].
        apply dst_equiv_implies_b_classify with (b:= b) in Heq; try assumption.
        rewrite <- Heq in H4.
        apply bF_sem_iff in Hcontra. destruct Hcontra as [_ Hcontra].
        rewrite H4 in Hcontra. destruct Hcontra; discriminate.
Qed.
(**********************************)
Theorem hoare_while: forall phi0 phi1 phi c b,
  phi = (Oplus (Pand phi0 (Pdeter (Dpred b))) (Pand phi1 (Pdeter (Dpred (Bnot b))))) -> 
  well_defined_Pf phi -> exclude_odot phi1 ->
  {{[[Pand phi0 (Pdeter (Dpred b))]]}} c {{[[phi]]}} -> 
  {{[[phi]]}} While b c {{[[Pand phi1 (Pdeter (Dpred (Bnot b)))]]}}.
Proof. 
  intros phi0 phi1 phi c b Hphi HWD HWX Hc.
  intros pd pd' Hvalid HZ HZc Hw H.
  assert(Hw_copy: pd =[ WHILE b DO c END ]=> pd') by assumption.
  remember (While b c) as original_command eqn:Horig.
  rewrite Hphi in Hc. rewrite Hphi in H.
  induction Hw; try inversion Horig; subst. 
  - apply emp_dst_satisfies_phi. 
    + inversion HWD; subst. assumption.
    + simpl. apply satisfy_implies_dom_sub in H; try assumption. 
    simpl in H. apply dom_subset_orb_fst_iff in H. destruct H. 
    apply dom_subset_trans with (l1:= dom pd); try assumption. 
    apply dom_subset_orb_snd_l_r. 
  - assert (Hv1: Valid_dist (mu pd1)). { apply Valid_forall_NS in Hw1; try assumption. }
    assert (Hv': Valid_dist (mu pd')). { apply Valid_forall_NS in Hw2; try assumption. }
    assert (Hsem1: [[phi0 ∧ Pdeter (Dpred b)]] pd). { 
      apply Oplus_implies_fst_under_All_true in H; try assumption. }
    specialize (Hc pd pd1 Hvalid HZ HZc Hw1 Hsem1). 
    apply IHHw2; try assumption. apply inject_Z_after_NS in Hw1; try assumption.
  - apply Oplus_implies_snd_under_All_false in H; try assumption.
  - assert (Hvb: Valid_dist (mu pd_b)). { simpl. apply dst_Valid_get_b. assumption. }
    assert (Hvnotb: Valid_dist (mu pd_notb)). { simpl. apply dst_Valid_get_notb. assumption. }
    assert (Hv0: Valid_dist (mu pd0)). { apply Valid_forall_NS in Hw1; try assumption. }
    assert (Hv1: Valid_dist (mu pd1)). { apply Valid_forall_NS in Hw2; try assumption. }
    assert (Hv': Valid_dist (mu pd')). { apply Valid_forall_NS in Hw_copy; try assumption. }
    apply phi_sem_add with (pd0:= pd1) (pd1:= pd_notb); try assumption.
    + apply dom_sub_modvar_preserves_domeq in Hw_copy; simpl; try assumption.
      apply dom_sub_modvar_preserves_domeq in Hw1; simpl; try assumption.
      apply dom_sub_modvar_preserves_domeq in Hw2; simpl; try assumption.
      * simpl in Hw1. apply dom_equiv_trans with (l1:= dom pd); try assumption.
      apply dom_equiv_sym.
      apply dom_equiv_trans with (l1:= dom pd0); try assumption.
      * simpl in Hw1. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
    + simpl. 
    apply dom_equiv_sym. apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption.
    apply orbdom_after_NS in Hw2. simpl in Hw2.
    apply dom_equiv_trans with (l1:= (dom pd0 ∪ get_modvar_in_winstr c)%domain); try assumption.
    apply orbdom_after_NS in Hw1. simpl in Hw1. 
    apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr c) in Hw1.
    apply dom_equiv_trans with (l1:= ((dom pd ∪ get_modvar_in_winstr c) ∪ get_modvar_in_winstr c)%domain); try assumption.
    rewrite <- orb_domain_assoc. rewrite orb_domain_refl.
    apply orb_domain_elim_r in H4. apply dom_equiv_sym. assumption. 
    + rewrite H5. apply dst_equiv_refl.
    + rewrite H5. rewrite dst_sum_prob_decom. reflexivity.
    + inversion HWD; subst. assumption.
    + simpl. split; try assumption. apply I.
    + apply IHHw2; try assumption; intuition. 
      * apply inject_Z_after_NS in Hw1; intuition. apply getb_inject_Z. assumption.
      * specialize (Hc pd_b pd0 Hvb). apply Hc; intuition. 
      ** apply getb_inject_Z. assumption.
      ** apply Oplus_implies_under_Mixed in H; try assumption. 
      destruct H. assumption.
    + apply Oplus_implies_under_Mixed in H; try assumption. 
      destruct H. assumption.
Qed. 
(********************************)
Theorem hoare_consequence_pre : forall (P P' Q : PAssertion) c,
  {{P'}} c {{Q}} ->
   P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple. intros.
  apply (H pd pd'); try assumption.
  apply H0; assumption.
Qed.
  
Theorem hoare_consequence_post : forall (P Q Q' : PAssertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros mu mu' Hvalid HZ HZc Hmu HP. 
  apply Himp; try assumption.
  - apply Valid_forall_NS in Hmu; try assumption.
  - apply inject_Z_after_NS in Hmu; intuition.
  - apply (Hhoare mu mu'); assumption.
Qed.

Theorem hoare_consequence : forall (P P' Q Q' : PAssertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P'); try assumption.
  apply hoare_consequence_post with (Q' := Q'); assumption.
Qed.
(********************************)
Theorem hoare_conj: forall P1 Q1 P2 Q2 c, 
  {{P1}} c {{Q1}} -> {{P2}} c {{Q2}} -> 
  {{P1 /\ P2}} c {{Q1 /\ Q2}}.
Proof.
  unfold hoare_triple, PAssertion_and.
  intros. destruct H5. split.
  - apply H with pd; assumption.
  - apply H0 with pd; assumption.
Qed.

(******************The following is the auxiliary theorem of Oframe **************)
Lemma res_update_nil_default: forall n V q, 
  is_domain_intersect V (singleton_bool_list n) = false ->
  st_all_none (res_st_to_X (update ([])%state n q) V) = true.
Proof.
  intros n V q HNS. generalize dependent V. 
  induction n as [|n0 Hn]; intros.
  - simpl. destruct V as [|x V']; simpl; try reflexivity.
    destruct x; simpl in *; try discriminate.
    reflexivity.
  - destruct V as [|x V']; simpl; try reflexivity.
    destruct x; simpl in *; try discriminate.
    + apply Hn; try assumption.
    + apply Hn; try assumption.
Qed.

Lemma res_intersect_update_eq: forall s V n q, 
  is_domain_intersect V (singleton_bool_list n) = false ->
  (res_st_to_X s V == res_st_to_X (update s n q) V).
Proof.
  intros s V n q HNS. generalize dependent V. generalize dependent n. 
  induction s as [|v s']; intros.
  - simpl. destruct V as [|x V']. 
    * rewrite res_st_nil_eq. simpl. reflexivity.
    * destruct n as [|n0]. 
      + simpl in *. rewrite andb_true_r in HNS. 
      destruct x; try discriminate. simpl. reflexivity.
      + simpl in *. destruct x; simpl in *; try discriminate.
      ** apply res_update_nil_default. assumption.
      ** apply res_update_nil_default. assumption.
  - simpl. generalize dependent V. induction n as [|n0 Hn]; intros.
    + simpl. destruct V as [|x V'].
      * destruct v; apply state_eq_refl.
      * destruct x; try discriminate. destruct v; apply state_eq_refl.
    + destruct V as [|x V'].
      * simpl. destruct v; reflexivity.
      * simpl. simpl in HNS. destruct x.
      ** simpl in HNS. apply IHs' in HNS. 
      unfold beq_state. fold beq_state.
      destruct v; simpl in *; try assumption.
      ++ destruct ((q0 ?= q0)%Q) eqn: Hv.
      -- assumption.
      -- apply Qlt_irrefl in Hv. contradiction.
      -- apply Qgt_alt in Hv. apply Qlt_irrefl in Hv. contradiction.
      ** simpl in HNS. apply IHs' in HNS. 
      unfold beq_state. fold beq_state. 
      destruct v; simpl in *; try assumption.
Qed.

Lemma DA_NS_res_intersect_dom: forall pd n a V (HWFa: WF_aexp_with_pd a pd),
  Valid_dist (mu pd) -> 
  is_domain_intersect V (singleton_bool_list n) = false -> 
  pd =[ n ::= a ]=> (DAssn_under_pd n a pd HWFa)-> 
  ((mu pd) \| V == (mu (DAssn_under_pd n a pd HWFa)) \| V)%dist_state.
Proof.
  intros pd n a V HWFa HWF Hdom HNS. destruct pd as [dom mu HPD]. simpl in *.
  induction mu as [|(s,p) mu' IH].
  - simpl. apply dst_equiv_refl.
  - simpl. rewrite dst_cons_eq_add. 
  rewrite dst_cons_eq_add with (s:= res_st_to_X (update s n (evalA_st a s)) V).
  apply dst_add_preserves_equiv.
    + apply Peq_one_st. split; try reflexivity. apply res_intersect_update_eq. assumption.
    + apply Valid_dist_inv in HWF; subst. inversion HPD; subst.
    assert (HWFa_inv: WF_aexp_with_pd a {| dom := dom; mu := mu'; all_partial := H3 |}). {
        apply WF_aexp_inv with (s:=s) (p:=p) (HPDs:= HPD). assumption. }
    apply IH with (HPD:= H3) (HWFa:= HWFa_inv); try assumption. apply NS_DAssign.
Qed.

Lemma res_intersect_update_da: forall s p V n da, 
  is_domain_intersect V (singleton_bool_list n) = false ->
  ([(res_st_to_X s V, ((sum_probs da)*p)%R)] == (update_st_with_da s p n da) \| V)%dist_state.
Proof. 
  intros s p V n da Hdom. generalize dependent s. 
  induction da as [|(a,pa) da']; intros.
  - simpl. rewrite Rmult_0_l. unfold dst_equiv. intros. simpl. 
    destruct (beq_state s0 (res_st_to_X s V)) eqn: Hs0; try reflexivity.
    apply Rplus_0_l. 
  - simpl. rewrite dst_cons_eq_add with (mu:= (update_st_with_da s p n da') \| V).
    apply dst_equiv_trans with (mu1:= ([(res_st_to_X s V, (pa * p)%R)] + 
                                        [(res_st_to_X s V, (sum_probs da' * p)%R)])%dist_state).
    + unfold dst_equiv. intros. simpl. destruct (beq_state s0 (res_st_to_X s V)); try reflexivity.
      repeat rewrite Rplus_0_r. apply Rmult_plus_distr_r.
    + apply dst_add_preserves_equiv. 
      * apply Peq_one_st. split; try reflexivity. apply res_intersect_update_eq. assumption.
      * apply IHda'.
Qed.  

Lemma RA_NS_res_intersect_dom: forall pd pd' n da V,
  Valid_dist (mu pd) -> 
  is_domain_intersect V (singleton_bool_list n) = false -> 
  pd =[ n $= da ]=> pd' ->
  (mu pd \| V == mu pd' \| V)%dist_state.
Proof.
  intros pd pd' n da V HWF Hdom HNS. 
  inversion HNS; subst. destruct pd as [dom mu HPD]. simpl in *.
  generalize dependent da.
  induction mu as [|(s,p) mu' IH]; intros.
  - destruct da. simpl. apply dst_equiv_refl.
  - destruct da as [da Hda]. simpl. 
    rewrite dst_cons_eq_add. 
    rewrite res_add_decom_eq.
    apply dst_add_preserves_equiv.
      * destruct Hda. rewrite <- Rmult_1_l with (r:= p) at 1. 
        rewrite <- e. apply res_intersect_update_da. assumption.
      * apply Valid_dist_inv in HWF; subst. inversion HPD; subst.  
        specialize (IH H3 HWF (exist (fun da : dist aexp => positive_probs da /\ sum_probs da = 1) da Hda)).
        simpl in IH. simpl in HWFa.
        assert (HWFa_inv: WF_distaexp_with_pd da {| dom := dom; mu := mu'; all_partial := H3 |}). {
          apply WF_distaexp_inv with (s:=s) (p:=p) (HPDs:= HPD). assumption. }
        apply IH with (HWFa:= HWFa_inv); try assumption. apply NS_RAssign.
Qed.

Lemma NS_res_intersect_dom: forall pd pd' c V, 
  Valid_dist (mu pd) -> Valid_dist (mu pd') -> 
  is_domain_intersect V (get_modvar_in_winstr c) = false ->
  pd =[ c ]=> pd' -> 
  (mu pd \| V == mu pd' \| V)%dist_state.
Proof.
  intros pd pd' c V HWF HWF' Hdom HNS.  
  generalize dependent pd'. generalize dependent pd.
  induction c; intros. 
  - inversion HNS; subst. apply dst_equiv_refl.
  - inversion HNS; subst. apply DA_NS_res_intersect_dom; try assumption.
  - apply RA_NS_res_intersect_dom with (n:= n) (da:= v); try assumption.
  - inversion HNS; subst.
    simpl in Hdom. apply intersect_orb_snd_conj in Hdom. destruct Hdom. 
    apply dst_equiv_trans with (mu1:= (mu pd1 \| V)).
    + apply IHc1; try assumption. apply Valid_forall_NS in H3; try assumption.
    + apply IHc2; try assumption. apply Valid_forall_NS in H3; try assumption.
  - simpl in Hdom. apply intersect_orb_snd_conj in Hdom. destruct Hdom. 
    inversion HNS; subst.
    + simpl in *. apply pd_Nil_mu in H5. rewrite H5. simpl. apply dst_equiv_refl.
    + apply IHc1; try assumption. 
    + apply IHc2; try assumption. 
    + apply dst_equiv_trans with (mu1:= ((mu pd_b + mu pd_notb)%dist_state \| V)).
    ++ apply Peq_implies_res_eq; try assumption.
      * apply WF_dist_b_notb; try assumption.
      * apply dst_equiv_sym. apply mu_div_by_bool.
    ++ rewrite H11. repeat rewrite res_add_decom_eq. apply dst_add_preserves_equiv.
      * apply IHc1; try assumption. 
      ** apply dst_Valid_get_b. assumption.
      ** apply Valid_forall_NS in H9; try assumption. 
      apply dst_Valid_get_b. assumption.
      * apply IHc2; try assumption. 
      ** apply dst_Valid_get_notb. assumption.
      ** apply Valid_forall_NS in H10; try assumption. 
      apply dst_Valid_get_notb. assumption. 
  - remember (While b c) as cw eqn:Heqcw. 
    induction HNS; inversion Heqcw; subst; clear Heqcw.
    ++ simpl in *. apply pd_Nil_mu in H0. rewrite H0. simpl. apply dst_equiv_refl.
    ++ apply dst_equiv_trans with (mu1:= (mu pd1) \| V). 
    ** apply IHc; try assumption. apply Valid_forall_NS in HNS1; try assumption.
    ** apply IHHNS2; try assumption; try reflexivity. 
    apply Valid_forall_NS in HNS1; try assumption.
    ++ apply dst_equiv_refl.
    ++ apply dst_equiv_trans with (mu1:= ((mu pd_b + mu pd_notb)%dist_state \| V)).
    + apply Peq_implies_res_eq; try assumption.
      * apply WF_dist_b_notb; try assumption.
      * apply dst_equiv_sym. apply mu_div_by_bool.
    + rewrite H4. repeat rewrite res_add_decom_eq. 
      apply dst_add_preserves_equiv; try apply dst_equiv_refl.
      apply dst_equiv_trans with (mu1:= (mu pd0 \| V)). 
      * apply IHc; try assumption. 
      -- apply dst_Valid_get_b. assumption.
      -- apply Valid_forall_NS in HNS1; try assumption. apply dst_Valid_get_b. assumption.
      * apply IHHNS2; try assumption; try reflexivity.
      -- apply Valid_forall_NS in HNS1; try assumption. apply dst_Valid_get_b. assumption.
      -- apply Valid_forall_NS in HNS2; try assumption. 
      apply Valid_forall_NS in HNS1; try assumption. 
      apply dst_Valid_get_b. assumption.
Qed.  

Lemma intersect_preserves_satisfy: forall pd pd' c phi, 
  Valid_dist (mu pd) -> well_defined_Pf phi ->
  pd =[ c ]=> pd' ->
  is_domain_intersect (get_var_in_Pformular phi) (get_modvar_in_winstr c) = false ->
  [[phi]] pd ->
  [[phi]] pd'.
Proof.
  intros pd pd' c phi HWF HWD HNS Hdom Hphi. 
  assert (Hsub: is_domain_subset (get_var_in_Pformular phi) (dom pd) = true). {
        apply satisfy_implies_dom_sub in Hphi; assumption. }
  assert (HNS_res: ((mu pd)\| (get_var_in_Pformular phi) == (mu pd') \| (get_var_in_Pformular phi))%dist_state). {
    apply NS_res_intersect_dom with (c:= c); try assumption. 
    apply Valid_forall_NS in HNS; try assumption. }
  apply sem_satisfies_project_implies_V with (V:= get_var_in_Pformular phi) (HV:= Hsub) in Hphi; 
    try assumption; try apply dom_subset_refl.
  assert (HEF': Valid_dist (mu pd')). { apply Valid_forall_NS in HNS; try assumption. }
  assert (Hsub': is_domain_subset (get_var_in_Pformular phi) (dom pd') = true). { 
    apply subset_NS in HNS; try assumption.
    apply dom_subset_trans with (l1:= (dom pd)); try assumption. }
  assert (Heq: 
  {|
      dom := get_var_in_Pformular phi;
      mu := (mu pd') \| (get_var_in_Pformular phi);
      all_partial := PD_after_res (get_var_in_Pformular phi) (dom pd') (mu pd') Hsub' (all_partial pd')
  |} ≡
  {|
      dom := get_var_in_Pformular phi;
      mu := (mu pd) \| (get_var_in_Pformular phi);
      all_partial := PD_after_res (get_var_in_Pformular phi) (dom pd) (mu pd) Hsub (all_partial pd)
  |} 
  ).
  - split; simpl; try apply dom_equiv_refl.
    apply dst_equiv_sym. apply HNS_res.
  - apply pd_equiv_preserves_sem with (phi:= phi) in Heq; try assumption. 
    + apply sem_resV_implies_pd in Heq; try assumption. apply dom_subset_refl.
    + simpl. apply Valid_after_resX. try assumption.
    + simpl. apply Valid_after_resX. apply Valid_forall_NS in HNS; try assumption. 
Qed. 

Lemma NS_intersect_preserves: forall pd pd' c V,
  (get_variables_in_winstr c ∩∅ V)%domain -> 
  pd =[ c ]=> pd' -> (dom pd ∩∅ V)%domain ->
  (dom pd' ∩∅ V)%domain.
Proof. 
  intros pd pd' c V Hvar HNS Hdom. 
  generalize dependent pd'. generalize dependent pd. induction c; intros.
  - inversion HNS; subst. assumption.
  - inversion HNS; subst. simpl in *. apply intersect_orb_fst_left in Hvar. 
    apply intersect_orb_l_iff; try assumption.
  - inversion HNS; subst. destruct v. simpl in *. apply intersect_orb_fst_left in Hvar.
    apply intersect_orb_l_iff; try assumption.
  - inversion HNS; subst. simpl in *. apply IHc2 with (pd:= pd1); try assumption. 
    + apply intersect_orb_fst_right in Hvar. assumption.
    + apply intersect_orb_fst_left in Hvar. apply IHc1 with (pd:= pd); try assumption.
  - inversion HNS; subst; simpl in *. 
    + apply intersect_orb_fst_right in Hvar. 
      apply intersect_orb_l_iff; try assumption.
      rewrite intersect_comm. rewrite intersect_comm in Hvar.
      apply intersect_subst_trans with (l2:= (get_variables_in_winstr c1 ∪ get_variables_in_winstr c2)%domain); try assumption.
      apply dom_subset_orb_compat; try apply Win_mod_sub_var.
    + apply IHc1 with (pd:= pd); try assumption.
      apply intersect_orb_fst_right in Hvar. apply intersect_orb_fst_left in Hvar.
      try assumption.
    + apply IHc2 with (pd:= pd); try assumption.
      apply intersect_orb_fst_right in Hvar. apply intersect_orb_fst_right in Hvar.
      try assumption.
    + rewrite dom_eq_intersect_compat_right with (l1:= dom pd1); try assumption.
      apply IHc1 with (pd:= pd_b); try assumption. 
      apply intersect_orb_fst_right in Hvar. apply intersect_orb_fst_left in Hvar.
      try assumption.
  - remember (While b c) as cw eqn:Heqcw. 
    induction HNS; inversion Heqcw; subst; clear Heqcw.
    + simpl in *. apply intersect_orb_fst_right in Hvar. 
      apply intersect_orb_l_iff; try assumption. 
      rewrite intersect_comm. rewrite intersect_comm in Hvar.
      apply intersect_subst_trans with (l2:= get_variables_in_winstr c); 
        try assumption; try apply Win_mod_sub_var.
    + apply IHHNS2; try assumption; try reflexivity.
      apply IHc with (pd:= pd); try assumption.
      simpl in *. apply intersect_orb_fst_right in Hvar. assumption. 
    + assumption.
    + rewrite dom_eq_intersect_compat_right with (l1:= dom pd1); try assumption.
      apply IHHNS2; try assumption; try reflexivity.
      apply IHc with (pd:= pd_b); try assumption.
      simpl in Hvar. apply intersect_orb_fst_right in Hvar. assumption. 
Qed.

Lemma RA_sub_WF_distaexp : forall x pd, 
  (get_variables_in_dist_aexp x ⊆ dom pd)%domain -> 
  WF_distaexp_with_pd x pd.
Proof.
  intros x pd H. generalize dependent pd.
  induction x; intros; simpl; try apply I.
  destruct a. simpl in *. destruct x.
  - simpl. split; try apply I. unfold WF_aexp_with_pd. assumption.
  - apply dom_subset_orb_fst_iff in H. destruct H. 
    apply IHx in H0. split; try assumption. 
Qed.

Lemma Pd_nil_sub_implies_WD: forall pd c, 
  ((get_readvar_in_winstr c) ⊆ dom pd)%domain ->
  mu pd = [] ->
  well_defined_winstr_with_pd c pd.
Proof.
  intros pd c Hdom Hnil. induction c; intros.
  - simpl. apply I. 
  - simpl in *. assumption.
  - simpl in *. destruct v. apply RA_sub_WF_distaexp. assumption.
  - simpl in *. apply dom_subset_orb_fst_iff in Hdom. destruct Hdom.
    apply IHc1. assumption.
  - simpl in *. apply dom_subset_orb_fst_iff in Hdom. destruct Hdom.
    split; try assumption. unfold b_supp_classify. rewrite Hnil. apply I.
  - simpl in *. apply dom_subset_orb_fst_iff in Hdom. destruct Hdom.
    split; try assumption. unfold b_supp_classify. rewrite Hnil. apply I.
Qed.


Lemma NS_pd_exists: forall c pd, 
  mu pd = [] -> well_defined_winstr_with_pd c pd -> 
  ((get_readvar_in_winstr c) ⊆ dom pd)%domain ->
  exists pd', pd_emp (dom pd ∪ get_modvar_in_winstr c)%domain ≡ pd' /\ pd =[ c ]=> pd'.
Proof.
  intros c pd Hnil Hwd Hsub. generalize dependent pd. induction c; intros.
  - exists pd. split; try apply NS_Skip. split; simpl.
    + rewrite orb_domain_nil_r. try apply dom_equiv_refl.
    + rewrite Hnil. apply dst_equiv_refl.
  - simpl in *. exists (DAssn_under_pd n a pd Hwd). split; try apply NS_DAssign; try assumption.
    split; simpl; try apply dom_equiv_refl.
    rewrite Hnil. apply dst_equiv_refl.
  - simpl in *. 
    assert (HWFa: WF_distaexp_with_pd (proj1_sig v) pd). { destruct v. simpl in *. assumption. } 
    exists (RAssn_under_pd n v pd HWFa). split; try apply NS_RAssign; try assumption.
    split; simpl; try apply dom_equiv_refl.
    rewrite Hnil. apply dst_equiv_refl.
  - simpl in *. apply dom_subset_orb_fst_iff in Hsub. destruct Hsub. 
    apply IHc1 in Hwd; try assumption. 
    destruct Hwd. destruct H1.
    assert (Hv: Valid_dist (mu pd)). { rewrite Hnil. apply Valid_dist_nil. }
    assert (Hvx: Valid_dist (mu x)). { apply Valid_forall_NS in H2; try assumption. }
    assert (Hwd2x: well_defined_winstr_with_pd c2 x). {
      apply pd_equiv_preserves_WD_win with (c:= c2) in H1; try assumption.
        - apply Valid_dist_nil.
        - apply Pd_nil_sub_implies_WD; try reflexivity. simpl. 
          apply dom_subset_trans with (l1:= (dom pd)); try assumption.
          apply dom_subset_orb_snd_l_r. }
    assert (Hxnil: mu x = []). {
      apply dst_eq_nil_iff. split; try assumption.
      destruct H1. simpl in *. apply dst_equiv_sym. assumption. }
    assert (Hdomc2x: (get_readvar_in_winstr c2 ⊆ dom x)%domain). {
      apply dom_subset_trans with (l1:= (dom pd)); try assumption.
      apply subset_NS in H2; try assumption. }
    apply IHc2 in Hwd2x; try assumption.
    destruct Hwd2x. destruct H3. exists x0. split; try assumption.
    * destruct H3. simpl in *. split; simpl; try assumption.
      apply dom_equiv_trans with (l1:= (dom x ∪ get_modvar_in_winstr c2)%domain); try assumption.
      rewrite orb_domain_assoc. apply dom_eq_orb_compat_right; try apply dom_subset_refl.
      apply dom_equiv_sym. apply orbdom_after_NS in H2; try assumption.
    * eapply NS_Seq; try assumption.
      + apply Pd_nil_sub_implies_WD; try reflexivity; try assumption. 
      + apply Pd_nil_sub_implies_WD with (pd:= x); try reflexivity; try assumption.
      + apply H2.
      + assumption.
  - exists (pd_emp (dom pd ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI))%domain). 
    split; try apply pd_equiv_refl. 
    assert (HWD1: well_defined_winstr_with_pd c1 pd). {
      apply Pd_nil_sub_implies_WD; try reflexivity; try assumption. 
      simpl in Hsub. apply dom_subset_orb_fst_iff in Hsub. destruct Hsub.
      apply dom_subset_orb_fst_iff in H0. destruct H0. assumption.
    }
    assert (HWD2: well_defined_winstr_with_pd c2 pd). {
      apply Pd_nil_sub_implies_WD; try reflexivity; try assumption. 
      simpl in Hsub. apply dom_subset_orb_fst_iff in Hsub. destruct Hsub.
      apply dom_subset_orb_fst_iff in H0. destruct H0. assumption.
    }
    eapply NS_IF_Nil; try assumption.
    + destruct Hwd; assumption.
    + apply pd_Nil_mu. assumption.
    + apply IHc1; try assumption. simpl in Hsub. apply dom_subset_orb_fst_iff in Hsub. destruct Hsub.
      apply dom_subset_orb_fst_iff in H0. destruct H0. assumption.
    + apply IHc2; try assumption. simpl in Hsub. apply dom_subset_orb_fst_iff in Hsub. destruct Hsub.
      apply dom_subset_orb_fst_iff in H0. destruct H0. assumption.
  - exists (pd_emp (dom pd ∪ get_modvar_in_winstr (WHILE b DO c END))%domain). 
    split; try apply pd_equiv_refl. 
    eapply NS_While_Nil; try assumption.
    + destruct Hwd; assumption.
    + apply pd_Nil_mu. assumption.
Qed.

Inductive NoControlFlow : winstr -> Prop :=
  | NCF_Skip : NoControlFlow Skip
  | NCF_DAssign : forall x a, NoControlFlow (DAssign x a)
  | NCF_RAssign : forall x d, NoControlFlow (RAssign x d)
  | NCF_Seq : forall c1 c2,
      NoControlFlow c1 -> NoControlFlow c2 ->
      NoControlFlow (Seq c1 c2).

 Lemma Pd_Iden_implies_WD: forall pd c, 
  NoControlFlow c ->
  ((get_readvar_in_winstr c) = nil)%domain ->
  well_defined_winstr_with_pd c pd.
Proof.
  intros pd c HNC Hdom. induction c; intros; inversion HNC; simpl in *.
  - simpl. apply I. 
  - simpl in *. unfold WF_aexp_with_pd. rewrite Hdom. simpl. reflexivity.
  - simpl in *. destruct v. apply RA_sub_WF_distaexp. rewrite Hdom. simpl. reflexivity.
  - simpl in *. apply orb_iff_nil in Hdom. destruct Hdom.
    apply IHc1; try assumption. 
Qed. 

Lemma PD_Iden: partial_dst_Prop nil Identify_mu.
Proof. 
  apply PD_cons; try apply PD_nil. simpl. apply dom_equiv_refl.
Qed.
Definition Identify_pd : partial_dist := 
                  {| dom := nil;
                     mu := Identify_mu;
                     all_partial := PD_Iden
                  |}.

Lemma NS_Identify: forall c pd, 
  NoControlFlow c ->
  well_defined_winstr_with_pd c pd ->
  get_readvar_in_winstr c = nil ->
  (exists pd', pd =[ c ]=> pd').
Proof. 
  intros c pd HNC HWD Hread. generalize dependent pd. 
  induction c; intros; inversion HNC; subst; simpl in *.
  - exists pd. apply NS_Skip.
  - simpl in HWD. exists (DAssn_under_pd n a pd HWD). apply NS_DAssign; try assumption.
  - simpl in HWD. 
    assert (HWFa: WF_distaexp_with_pd (proj1_sig v) pd). { destruct v. simpl in *. assumption. } 
    exists (RAssn_under_pd n v pd HWFa). try apply NS_RAssign; try assumption.
  - simpl in *. apply orb_iff_nil in Hread. destruct Hread as [Hread1 Hread2].
    apply IHc1 with (pd:= pd) in Hread1; try assumption. destruct Hread1.
    assert (HWD2: well_defined_winstr_with_pd c2 x). { 
      apply Pd_Iden_implies_WD; try assumption. }
    apply IHc2 with (pd:= x) in Hread2; try assumption. 
    destruct Hread2. exists x0. eapply NS_Seq; try assumption.
    * apply HWD2.
    * assumption.
    * assumption.
Qed.

Lemma update_orb_n_eq: forall s X n q, 
  update (res_st_to_X s (X ∪ singleton_bool_list n)%domain) n q = update (res_st_to_X s X) n q.
Proof.
  intros. 
  generalize dependent X. generalize dependent q. generalize dependent n.
  induction s as [|v s' IH]; intros.
  - simpl. reflexivity.
  - destruct X. 
    + simpl. destruct v; simpl. 
      * destruct (singleton_bool_list n) eqn: Hn; try reflexivity.
      unfold singleton_bool_list in Hn. destruct n; try discriminate Hn.
      ** inversion Hn; subst. simpl. rewrite res_st_nil_eq. reflexivity.
      ** inversion Hn; subst. simpl. f_equal. fold singleton_bool_list. 
      specialize (IH n q nil). simpl in IH. rewrite res_st_nil_eq in IH. assumption.
      * destruct (singleton_bool_list n) eqn: Hn; try reflexivity.
      unfold singleton_bool_list in Hn. destruct n; try discriminate Hn.
      ** inversion Hn; subst. simpl. rewrite res_st_nil_eq. reflexivity.
      ** inversion Hn; subst. simpl. f_equal. fold singleton_bool_list. 
      specialize (IH n q nil). simpl in IH. rewrite res_st_nil_eq in IH. assumption.
    + simpl. destruct v; simpl. 
      * destruct (singleton_bool_list n) eqn: Hn; try reflexivity.
      unfold singleton_bool_list in Hn. destruct n; try discriminate Hn.
      ** inversion Hn; subst. rewrite orb_true_r. simpl. 
        destruct b.
        -- rewrite orb_domain_nil_r. reflexivity.
        -- rewrite orb_domain_nil_r. reflexivity.
      ** inversion Hn; subst. rewrite orb_false_r. simpl. 
        destruct b.
        -- f_equal. fold singleton_bool_list. apply IH.
        -- f_equal. fold singleton_bool_list. apply IH.
      * destruct (singleton_bool_list n) eqn: Hn; try reflexivity.
      unfold singleton_bool_list in Hn. destruct n; try discriminate Hn.
      ** inversion Hn; subst. rewrite orb_domain_nil_r. simpl. reflexivity.
      ** inversion Hn; subst. simpl. f_equal. fold singleton_bool_list. apply IH. 
Qed. 

Lemma update_res_preserves: forall s n a X, 
  (get_variables_in_aexp a ⊆ X)%domain ->
  (res_st_to_X (update s n (evalA_st a s)) (X ∪ singleton_bool_list n)%domain ==
  update (res_st_to_X s X) n (evalA_st a (res_st_to_X s X)))%state.
Proof.
  intros s n a X Ha. 
  apply state_eq_trans with (s1:= update (res_st_to_X s (X ∪ singleton_bool_list n)%domain) n (evalA_st a s)).
  - apply update_eq_res_st. apply dom_subset_orb_snd_l_r.
  - rewrite update_orb_n_eq. apply st_eq_implies_update_eq.
    + apply state_eq_refl.
    + apply evalA_st_preserve_bool with (s:= s) in Ha.
      rewrite <- evalA_eq_res_st. assumption.
Qed.

Lemma DA_res_preserves: forall mu n a X, 
  (get_variables_in_aexp a ⊆ X)%domain ->
  (DAssn_under_dstate mu n a \| (X ∪ singleton_bool_list n)%domain ==
  DAssn_under_dstate (mu \| X) n a)%dist_state.
Proof.
  intros mu n a X Ha. induction mu as [|(s,p) mu' IH]; simpl; try apply dst_equiv_refl.
  rewrite dst_cons_eq_add. 
  rewrite dst_cons_eq_add with (mu:= DAssn_under_dstate (mu' \| X) n a).
  apply dst_add_preserves_equiv; try assumption. 
  apply Peq_one_st. split; try reflexivity.
  apply update_res_preserves. assumption.
Qed.

Lemma updateda_res_preserves: forall s p n da X, 
  (get_variables_in_dist_aexp da ⊆ X)%domain ->
  (update_st_with_da s p n da \| (X ∪ singleton_bool_list n)%domain ==
 update_st_with_da (res_st_to_X s X) p n da)%dist_state.
Proof.
  intros s p n da X Ha. generalize dependent s. generalize dependent n.
  induction da as [|(a1,p1) da' IH]; intros; try apply dst_equiv_refl.
  simpl. rewrite dst_cons_eq_add. rewrite dst_cons_eq_add with (mu:= update_st_with_da (res_st_to_X s X) p n da').
  apply dst_add_preserves_equiv; try assumption.
  - apply Peq_one_st. split; try reflexivity. 
    apply update_res_preserves. 
    apply dom_subset_trans with (l1:= get_variables_in_dist_aexp ((a1, p1) :: da')); try assumption. 
    simpl. destruct da'; simpl; try apply dom_subset_refl. apply dom_subset_orb_snd_l_r. 
  - apply IH. apply dom_subset_trans with (l1:= get_variables_in_dist_aexp ((a1, p1) :: da')); try assumption. 
    simpl. destruct da'; simpl; try reflexivity. apply dom_subset_orb_snd_l_r. 
Qed.


Lemma RA_res_preserves: forall mu n da X, 
  (get_variables_in_dist_aexp da ⊆ X)%domain ->
  (RAssn_under_dstate mu n da \| (X ∪ singleton_bool_list n)%domain ==
  RAssn_under_dstate (mu \| X) n da)%dist_state.
Proof.
  intros mu n da X Ha. induction mu as [|(s,p) mu' IH]; simpl; try apply dst_equiv_refl.
  rewrite res_add_decom_eq.
  apply dst_add_preserves_equiv; try assumption. 
  apply updateda_res_preserves. assumption.
Qed.


Lemma update_union_preserves: forall s s' n q, 
  (singleton_bool_list n ∩∅ (return_domain s'))%domain -> 
  ((return_domain s) ∩∅ (return_domain s'))%domain ->
  update (union_state s s') n q = union_state (update s n q) s'.
Proof.
  intros s s' n q H Hdom. generalize dependent s'. generalize dependent n. 
  induction s as [|v s IH]; intros. 
  - simpl. generalize dependent n. induction s' as [|v' s' IH]; intros. 
    + rewrite union_nil_right_eq. reflexivity.
    + simpl in *. destruct n; destruct v'; simpl in H; try discriminate; try reflexivity.
      * simpl in *. f_equal. apply IH; try reflexivity. assumption.
      * simpl in *. f_equal. apply IH; try reflexivity. assumption.
  - destruct s' as [|v' s']. 
    + simpl. destruct v; simpl. 
      * rewrite union_nil_right_eq. reflexivity.
      * rewrite union_nil_right_eq. reflexivity.
    + destruct n eqn: Hn; destruct v; destruct v'; simpl in *; try discriminate; try reflexivity.
      * f_equal. apply IH; try assumption.
      * f_equal. apply IH; try assumption.
      * f_equal. apply IH; try assumption.
Qed.

Lemma get_intersect_compat: forall s n, 
  (singleton_bool_list n ∩∅ return_domain s)%domain ->
  (get n s == default_Q)%Q.
Proof.
  intros s n Hdom. generalize dependent n. induction s as [|v s IH]; intros. 
  - simpl. rewrite get_default_nil. apply Qeq_refl. 
  - simpl in *. destruct n; destruct v; simpl in *; try discriminate; try reflexivity.
    * apply IH; try reflexivity. assumption.
    * apply IH; try reflexivity. assumption.
Qed.

Ltac simplify_and_solve_orb Hdom IHa1 IHa2 :=
  simpl; 
  rewrite IHa1; try rewrite IHa2; try apply Qeq_refl;
  try (simpl in Hdom; apply intersect_orb_fst_right in Hdom; assumption);
  try (simpl in Hdom; apply intersect_orb_fst_left in Hdom; assumption).

Lemma evalA_union_intersect: forall s s' a, 
  ((get_variables_in_aexp a) ∩∅ (return_domain s'))%domain -> 
  ((return_domain s) ∩∅ (return_domain s'))%domain -> 
  (evalA_st a (union_state s s') == evalA_st a s)%Q.
Proof.
  intros s s' a Hdom Hs. generalize dependent s'. generalize dependent s.
  induction a; intros; try (simplify_and_solve_orb Hdom IHa1 IHa2).
  - simpl. apply Qeq_refl.
  - simpl in *. generalize dependent s'. generalize dependent n. induction s as [|v s IH]; intros. 
    + simpl. rewrite get_default_nil. apply get_intersect_compat. assumption.
    + destruct v; destruct s' as [|v' s']; simpl; try apply Qeq_refl. 
      * destruct v'; simpl in *; try discriminate. 
        destruct n; simpl; try apply Qeq_refl.
        apply IH; try assumption.
      * destruct v'; destruct n; simpl in *; try discriminate; try apply Qeq_refl.
        ** apply IH; try assumption.
        ** apply IH; try assumption.
Qed.    
      
Lemma DA_onest_independent: forall s p pd_inde n a, 
  ((singleton_bool_list n ∪ get_variables_in_aexp a) ∩∅ dom pd_inde)%domain ->
  (return_domain s ∩∅ dom pd_inde)%domain ->
  (DAssn_under_dstate ([(s, p)] ⊗ (mu pd_inde)) n a == (DAssn_under_dstate ((s, p)::nil) n a) ⊗ (mu pd_inde))%dist_state.
Proof. 
  intros s p pd_inde n a Hdom Hinter. destruct pd_inde as [dom mu HPD]. 
  induction mu as [|(s',p') mu' IH]; try apply dst_equiv_refl. 
  unfold mu in *. rewrite combine_onest_cons_distr_eq. rewrite DAss_add_dec_eq. 
  apply dst_equiv_trans with (mu1:= (DAssn_under_dstate ((s, p)::nil) n a ⊗ [(s', p')] + DAssn_under_dstate ((s, p)::nil) n a ⊗ mu')%dist_state).
  - apply dst_add_preserves_equiv; try assumption. 
    + simpl. apply Peq_one_st. split; try reflexivity. simpl in Hdom. 
      inversion HPD; subst.
      rewrite update_union_preserves; try assumption. 
      * apply union_state_eq_compat_r. 
        apply st_eq_implies_update_eq; try apply state_eq_refl.
        apply evalA_union_intersect.
      ** apply intersect_orb_fst_right in Hdom.  rewrite <- dom_eq_intersect_compat_left with (l0:= dom); try assumption.
      ** rewrite <- dom_eq_intersect_compat_left with (l0:= dom); try assumption.
      * apply intersect_orb_fst_left in Hdom. rewrite <- dom_eq_intersect_compat_left with (l0:= dom); try assumption.
      * rewrite <- dom_eq_intersect_compat_left with (l0:= dom); try assumption.
    + inversion HPD; subst. apply IH with (HPD:= H3); simpl in *; try assumption.
  - apply dst_equiv_sym. apply combine_cons_r_distr.  
Qed. 

Lemma DA_independent: forall pd pd_inde n a, 
  ((singleton_bool_list n ∪ get_variables_in_aexp a) ∩∅ dom pd_inde)%domain -> 
  (dom pd ∩∅ dom pd_inde)%domain -> 
  (DAssn_under_dstate (mu pd ⊗ mu pd_inde) n a == DAssn_under_dstate (mu pd) n a ⊗ mu pd_inde)%dist_state.
Proof. 
  intros pd pd_inde n a Hdom HX. 
  destruct pd as [dom mu HPD].
  simpl in *. induction mu as [|(s,p) mu' IH]; try apply dst_equiv_refl. 
  rewrite combine_cons_l_distr_eq. rewrite DAss_add_dec_eq. 
  rewrite dst_cons_eq_add with (mu:= mu'). rewrite DAss_add_dec_eq. 
  rewrite combine_add_distr_l_eq. apply dst_add_preserves_equiv; try assumption. 
  - apply DA_onest_independent; try assumption. inversion HPD; subst. 
    rewrite <- dom_eq_intersect_compat_right with (l0:= dom); try assumption.
  - apply IH. inversion HPD; subst. assumption.
Qed.

Lemma updateda_union_preserves: forall s s' p p' n da, 
  ((singleton_bool_list n ∪ get_variables_in_dist_aexp da) ∩∅ (return_domain s'))%domain -> 
  ((return_domain s) ∩∅ (return_domain s'))%domain ->
  (update_st_with_da (union_state s s') (p * p') n da == update_st_with_da s p n da ⊗ [(s', p')])%dist_state.
Proof. 
  intros. generalize dependent s'. generalize dependent s. generalize dependent n. 
  induction da; intros; try apply dst_equiv_refl.
  destruct a. simpl. rewrite dst_cons_eq_add. 
  rewrite dst_cons_eq_add with (mu:= update_st_with_da s p n da ⊗ [(s', p')]).
  apply dst_add_preserves_equiv. 
  - apply Peq_one_st. split; try rewrite Rmult_assoc; try reflexivity.
    rewrite update_union_preserves; try assumption.
    + apply union_state_eq_compat_r. 
      apply st_eq_implies_update_eq; try apply state_eq_refl.
      apply evalA_union_intersect; try assumption. 
      apply intersect_orb_fst_right in H. 
      rewrite intersect_comm. rewrite intersect_comm in H. 
      apply intersect_subst_trans with (l2:= get_variables_in_dist_aexp ((a, r) :: da)); try assumption. 
      simpl. destruct da; try apply dom_subset_refl. apply dom_subset_orb_snd_l_r.
    + apply intersect_orb_fst_left in H. assumption.
  - apply IHda; try assumption. apply intersect_orb_l_iff. 
    + apply intersect_orb_fst_left in H. assumption.
    + apply intersect_orb_fst_right in H. 
      rewrite intersect_comm. rewrite intersect_comm in H. 
      apply intersect_subst_trans with (l2:= get_variables_in_dist_aexp ((a, r) :: da)); try assumption. 
      simpl. destruct da; try apply reflexivity. apply dom_subset_orb_snd_l_r.
Qed.

Lemma RA_onest_independent: forall s p pd_inde n da, 
  ((singleton_bool_list n ∪ get_variables_in_dist_aexp da) ∩∅ dom pd_inde)%domain ->
  (return_domain s ∩∅ dom pd_inde)%domain ->
  (RAssn_under_dstate ([(s, p)] ⊗ (mu pd_inde)) n da == RAssn_under_dstate ((s, p)::nil) n da ⊗ (mu pd_inde))%dist_state.
Proof. 
  intros s p pd_inde n da Hdom Hinter. destruct pd_inde as [dom mu HPD]. 
  induction mu as [|(s',p') mu' IH]. 
  { simpl; rewrite combine_nil_r_eq. try apply dst_equiv_refl. }   
  unfold mu in *. rewrite combine_onest_cons_distr_eq. rewrite RAss_add_dec_eq. 
  apply dst_equiv_trans with (mu1:= (RAssn_under_dstate ((s, p)::nil) n da ⊗ [(s', p')] + RAssn_under_dstate ((s, p)::nil) n da ⊗ mu')%dist_state).
  - apply dst_add_preserves_equiv; try assumption. 
    + simpl. repeat rewrite dst_add_0_r. simpl in Hdom. 
      inversion HPD; subst. 
      apply updateda_union_preserves; try assumption.
      * rewrite <- dom_eq_intersect_compat_left with (l0:= dom); try assumption.
      * rewrite <- dom_eq_intersect_compat_left with (l0:= dom); try assumption.
    + inversion HPD; subst. apply IH with (HPD:= H3); simpl in *; try assumption.
  - apply dst_equiv_sym. apply combine_cons_r_distr.  
Qed. 
Lemma RA_independent: forall pd pd_inde n da, 
  ((singleton_bool_list n ∪ get_variables_in_dist_aexp da) ∩∅ dom pd_inde)%domain -> 
  (dom pd ∩∅ dom pd_inde)%domain -> 
  (RAssn_under_dstate (mu pd ⊗ mu pd_inde) n da == RAssn_under_dstate (mu pd) n da ⊗ mu pd_inde)%dist_state.
Proof. 
  intros pd pd_inde n da Hdom HX. 
  destruct pd as [dom mu HPD].
  simpl in *. induction mu as [|(s,p) mu' IH]; try apply dst_equiv_refl. 
  rewrite combine_cons_l_distr_eq. rewrite RAss_add_dec_eq. 
  rewrite dst_cons_eq_add with (mu:= mu'). rewrite RAss_add_dec_eq. 
  rewrite combine_add_distr_l_eq. apply dst_add_preserves_equiv; try assumption. 
  - apply RA_onest_independent; try assumption. inversion HPD; subst. 
    rewrite <- dom_eq_intersect_compat_right with (l0:= dom); try assumption. 
  - apply IH. inversion HPD; subst. assumption.
Qed.

Lemma WF_da_comb_preserves: forall pd pd_inde da (Hdom: (dom pd ∩∅ dom pd_inde)%domain),
  let PD_comb:= combine_pd pd pd_inde Hdom : partial_dist in 
  WF_distaexp_with_pd da pd -> 
  WF_distaexp_with_pd da PD_comb.
Proof.
  intros. induction da; intros.
  - simpl. apply I.
  - destruct a. simpl in *. destruct H. 
    apply IHda in H0. split; try assumption. 
    unfold WF_aexp_with_pd in *. simpl in *. 
    apply dom_subset_trans with (l1:= dom pd); try assumption.
    apply dom_subset_orb_snd_l_r.
Qed.

Lemma readc_independent_preserved_by_NS :
  forall pd pd' pd0 pd0' pd_inde c 
        (Hdom: is_domain_intersect (dom pd0) (dom pd_inde) = false)
        (Hdom': is_domain_intersect (dom pd0') (dom pd_inde) = false), 
    Valid_dist (mu pd) -> Valid_dist (mu pd_inde) -> Valid_dist (mu pd0) ->
    is_domain_intersect (get_variables_in_winstr c) (dom pd_inde) = false ->
    NoControlFlow c -> get_readvar_in_winstr c = nil ->
    pd0 =[ c ]=> pd0' -> 
    pd =[ c ]=> pd' -> 
    (combine_pd pd0 pd_inde Hdom) ⊑ pd ->
    (combine_pd pd0' pd_inde Hdom') ⊑ pd'.
Proof.
  intros pd pd' pd0 pd0' pd_inde c 
    Hdom Hdom' HV HVin HV0 Hdomc HNC Hreadc Hsem0 Hsem1 Hsub.
  generalize dependent pd0'. generalize dependent pd0. 
  generalize dependent pd'. generalize dependent pd. generalize dependent pd_inde.
  induction c; intros; inversion HNC; subst; simpl in *.
  - inversion Hsem0; inversion Hsem1; subst. assumption.
  - inversion Hsem0; inversion Hsem1; subst. destruct Hsub. simpl in *. 
    split; simpl.
    + apply dom_subset_eq_compat_right with (X:= ((dom pd0 ∪ dom pd_inde) ∪ singleton_bool_list n)%domain).
      * repeat rewrite <- orb_domain_assoc. apply dom_eq_orb_compat_left. 
        rewrite orb_domain_comm. apply dom_equiv_refl.
      * apply dom_subset_orb_compat; try apply dom_subset_refl. assumption.
    + apply DA_step_deter with (n:= n) (a:= a) in H0; 
        try apply Valid_after_combine; try apply Valid_after_resX; try assumption.
      apply Peq_implies_res_eq with (X:= ((dom pd0 ∪ singleton_bool_list n) ∪ dom pd_inde)%domain) in H0; 
        try apply Valid_after_DA; try apply Valid_after_combine; try apply Valid_after_resX; try assumption.
      apply dst_equiv_trans with (mu1:= 
        (DAssn_under_dstate (mu pd \| (dom pd0 ∪ dom pd_inde)%domain) n a \| ((dom pd0 ∪ singleton_bool_list n) ∪ dom pd_inde)%domain)).
      * assert (Hdom_eq: ((dom pd0 ∪ singleton_bool_list n) ∪ dom pd_inde)%domain = ((dom pd0 ∪ dom pd_inde) ∪ singleton_bool_list n)%domain). {
          rewrite <- orb_domain_assoc. 
          rewrite (orb_domain_comm (singleton_bool_list n) (dom pd_inde)).
          rewrite <- orb_domain_assoc. reflexivity. }
        rewrite Hdom_eq. 
        pose (X:= (dom pd0 ∪ dom pd_inde)%domain). fold X.
        assert (Heq: (DAssn_under_dstate (mu pd) n a \| (X ∪ singleton_bool_list n)%domain == 
                      DAssn_under_dstate (mu pd \| X) n a)%dist_state). {
          destruct pd. simpl in *. apply DA_res_preserves.
          unfold WF_aexp_with_pd in HWFa. 
          apply dom_subset_trans with (l1:= CoreDef.dom pd0); try assumption.
          apply dom_subset_orb_snd_l_r. }
        apply dst_equiv_trans with (mu1:=  DAssn_under_dstate (mu pd \| X) n a); try assumption.
        apply dst_equiv_sym.
        assert (HWFa_res: WF_aexp_with_pd a (restrict_pd pd X H)). {
          unfold WF_aexp_with_pd. simpl. rewrite Hreadc. simpl. reflexivity. } 
        pose (pd_res:= (DAssn_under_pd n a (restrict_pd pd X H) HWFa_res)).
        apply res_pd_to_dom_refl with (pd:= pd_res); try assumption.
      * apply dst_equiv_trans with (mu1:= DAssn_under_dstate (mu pd0 ⊗ mu pd_inde) n a \|
                                            ((dom pd0 ∪ singleton_bool_list n) ∪ dom pd_inde)%domain); try assumption. 
        apply dst_equiv_trans with (mu1:= (DAssn_under_dstate (mu pd0 ⊗ mu pd_inde) n a)). 
      ** 
      pose (PD_comb:= (combine_pd pd0 pd_inde Hdom)).
      assert (HWD_comb: WF_aexp_with_pd a PD_comb). { 
        unfold WF_aexp_with_pd. simpl. 
        apply dom_subset_trans with (l1:= dom pd0); try assumption. 
        apply dom_subset_orb_snd_l_r. }
      pose (PD:= DAssn_under_pd n a PD_comb HWD_comb). 
      rewrite <- orb_domain_assoc. rewrite orb_domain_comm with (l':= dom pd_inde). 
      rewrite orb_domain_assoc. 
      apply res_pd_to_dom_refl with (pd:= PD).
      ** apply DA_independent; try assumption.
  - inversion Hsem0; inversion Hsem1; subst. destruct Hsub. simpl in *. 
    split; simpl.
    + apply dom_subset_eq_compat_right with (X:= ((dom pd0 ∪ dom pd_inde) ∪ singleton_bool_list n)%domain).
      * repeat rewrite <- orb_domain_assoc. apply dom_eq_orb_compat_left. 
        rewrite orb_domain_comm. apply dom_equiv_refl.
      * apply dom_subset_orb_compat; try apply dom_subset_refl. assumption.
    + pose (X:= (dom pd0 ∪ dom pd_inde)%domain). 
      assert (HWFa_res: WF_distaexp_with_pd (proj1_sig v) (restrict_pd pd X H)). {
        destruct v. simpl in *. apply RA_sub_WF_distaexp. rewrite Hreadc. 
        simpl. reflexivity. } 
      pose (pd_res:= (RAssn_under_pd n v (restrict_pd pd X H) HWFa_res)).
      pose (PD_comb:= (combine_pd pd0 pd_inde Hdom)).
      assert (HWD_comb: WF_distaexp_with_pd (proj1_sig v) PD_comb). { 
        destruct v. simpl in *. apply WF_da_comb_preserves. assumption. }
      pose (PD:= RAssn_under_pd n v PD_comb HWD_comb).
      destruct v as [da Hda]. simpl in *.
      apply RA_step_deter with (x:= n) (da:= da) in H0; 
        try apply Valid_after_combine; try apply Valid_after_resX; try assumption.     
      apply Peq_implies_res_eq with (X:= ((dom pd0 ∪ singleton_bool_list n) ∪ dom pd_inde)%domain) in H0; 
        try apply Valid_after_RA; try apply Valid_after_combine; try apply Valid_after_resX; try assumption;
        try split; destruct Hda; try rewrite e; try split; try apply Rle_refl; try apply Rle_0_1; try assumption. 
      apply dst_equiv_trans with (mu1:= 
        (RAssn_under_dstate (mu pd \| (dom pd0 ∪ dom pd_inde)%domain) n da \| ((dom pd0 ∪ singleton_bool_list n) ∪ dom pd_inde)%domain)).
      * assert (Hdom_eq: ((dom pd0 ∪ singleton_bool_list n) ∪ dom pd_inde)%domain = ((dom pd0 ∪ dom pd_inde) ∪ singleton_bool_list n)%domain). {
          rewrite <- orb_domain_assoc. 
          rewrite (orb_domain_comm (singleton_bool_list n) (dom pd_inde)).
          rewrite <- orb_domain_assoc. reflexivity. }
        rewrite Hdom_eq. fold X.
        assert (Heq: (RAssn_under_dstate (mu pd) n da \| (X ∪ singleton_bool_list n)%domain == 
                      RAssn_under_dstate (mu pd \| X) n da)%dist_state). {
          destruct pd. simpl in *. apply RA_res_preserves. rewrite Hreadc. simpl. reflexivity. }
        apply dst_equiv_trans with (mu1:=  RAssn_under_dstate (mu pd \| X) n da); try assumption.
        apply dst_equiv_sym. 
        apply res_pd_to_dom_refl with (pd:= pd_res); try assumption.
      * apply dst_equiv_trans with (mu1:= RAssn_under_dstate (mu pd0 ⊗ mu pd_inde) n da \|
                                            ((dom pd0 ∪ singleton_bool_list n) ∪ dom pd_inde)%domain); try assumption. 
        apply dst_equiv_trans with (mu1:= (RAssn_under_dstate (mu pd0 ⊗ mu pd_inde) n da)). 
      ** rewrite <- orb_domain_assoc. rewrite orb_domain_comm with (l':= dom pd_inde). 
      rewrite orb_domain_assoc. apply res_pd_to_dom_refl with (pd:= PD).
      ** apply RA_independent; try assumption.
  - inversion Hsem0; inversion Hsem1; subst. 
    assert (Hdomc1: (get_variables_in_winstr c1 ∩∅ dom pd_inde)%domain). { 
      simpl in Hdomc. apply intersect_orb_fst_left in Hdomc; try assumption. }
    assert (Hdomc2: (get_variables_in_winstr c2 ∩∅ dom pd_inde)%domain). { 
      simpl in Hdomc. apply intersect_orb_fst_right in Hdomc; try assumption. }
    assert (Hdom2: (dom pd2 ∩∅ dom pd_inde)%domain). { apply NS_intersect_preserves with (V:= dom pd_inde) in H5; try assumption. }
    assert (Hdom5: (dom pd0' ∩∅ dom pd_inde)%domain). { apply NS_intersect_preserves with (V:= dom pd_inde) in H8; try assumption. }
    assert (HV5: Valid_dist (mu pd5)). { apply Valid_forall_NS in H13; try assumption. }
    assert (HV2: Valid_dist (mu pd2)). { apply Valid_forall_NS in H5; try assumption. }
    assert (HV': Valid_dist (mu pd')). { apply Valid_forall_NS in H16; try assumption. }
    inversion HNC; subst. apply orb_iff_nil in Hreadc. destruct Hreadc as [Hreadc1 Hreadc2].
    specialize (IHc1 H6 Hreadc1 pd_inde HVin Hdomc1 pd HV pd5 H13 pd0 Hdom HV0 Hsub pd2 Hdom2 H5).
    specialize (IHc2 H7 Hreadc2 pd_inde HVin Hdomc2 pd5 HV5 pd' H16 pd2 Hdom2 HV2 IHc1 pd0' Hdom5 H8).
    assumption.
Qed.

Lemma readc_local_execution_exists : 
  forall c (pd pd' pd_inde pd0: partial_dist)
      (Hdom: is_domain_intersect (dom pd0)%domain (dom pd_inde) = false)
      (Hdomc: is_domain_intersect (get_variables_in_winstr c) (dom pd_inde) = false),
    NoControlFlow c -> get_readvar_in_winstr c = nil ->
    pd =[ c ]=> pd' -> 
    Valid_dist (mu pd) -> Valid_dist (mu pd') -> Valid_dist (mu pd_inde) -> Valid_dist (mu pd0) ->
    combine_pd pd0 pd_inde Hdom ⊑ pd ->
    (exists pd_tmp (HNS0: pd0 =[ c ]=> pd_tmp),
      combine_pd pd_tmp pd_inde 
        (NS_intersect_preserves pd0 pd_tmp c (dom pd_inde) Hdomc HNS0 Hdom) ⊑ pd').
Proof. 
  intros c pd pd' pd_inde pd0 Hdom Hdomc HNC Hreadc HNS Hv Hv' Hv_inde Hv0 Hsub. 
  generalize dependent pd. generalize dependent pd'. 
  generalize dependent pd_inde. generalize dependent pd0.
  induction c; intros; inversion HNC; subst; simpl in *.
  - inversion HNS; subst. 
    assert (HNS0: pd0 =[ SKIP ]=> pd0) by apply NS_Skip. 
    exists pd0, HNS0. destruct Hsub; simpl in *. 
    split; simpl; try assumption. 
  - inversion HNS; subst. simpl in *.
    pose (c:= (DAssign n a)).
    assert (HWF_a0: WF_aexp_with_pd a pd0). {
      unfold WF_aexp_with_pd. rewrite Hreadc. simpl. reflexivity. }
    assert (HNS0 : pd0 =[ n ::= a ]=> DAssn_under_pd n a pd0 HWF_a0). { apply NS_DAssign; try assumption. }
    exists (DAssn_under_pd n a pd0 HWF_a0), HNS0.
    apply readc_independent_preserved_by_NS with (pd:= pd) (pd0:= pd0) (c:= DAssign n a) (Hdom:= Hdom); try assumption.
  - inversion HNS; subst. 
    assert (HWFa0: WF_distaexp_with_pd (proj1_sig v) pd0). { 
      destruct v. simpl in *. apply RA_sub_WF_distaexp. rewrite Hreadc. simpl. reflexivity. } 
    assert (HNS0: pd0 =[ n $= v ]=> RAssn_under_pd n v pd0 HWFa0). { apply NS_RAssign; try assumption. }
    exists (RAssn_under_pd n v pd0 HWFa0), HNS0.
    apply readc_independent_preserved_by_NS with (pd:= pd) (pd0:= pd0) (c:= RAssign n v) (Hdom:= Hdom); try assumption.
  - inversion HNS; subst. 
    simpl in Hdomc. 
    assert (Hc1: get_readvar_in_winstr c1 = []). {
      apply orb_iff_nil in Hreadc. destruct Hreadc. assumption. }
    assert (Hc2: get_readvar_in_winstr c2 = []). {
      apply orb_iff_nil in Hreadc. destruct Hreadc. assumption. }
    assert (Hdomc1: is_domain_intersect (get_variables_in_winstr c1) (dom pd_inde) = false). {
      apply intersect_orb_fst_left in Hdomc; try assumption. }
    assert (Hdomc2: is_domain_intersect (get_variables_in_winstr c2) (dom pd_inde) = false). {
      apply intersect_orb_fst_right in Hdomc; try assumption. }
    assert (Hreadc10: (get_readvar_in_winstr c1 ⊆ dom pd0)%domain). {
      apply orb_iff_nil in Hreadc. destruct Hreadc. rewrite H. simpl. reflexivity. }
    assert (Hreadc20: (get_readvar_in_winstr c2 ⊆ dom pd0)%domain). {
      apply orb_iff_nil in Hreadc. destruct Hreadc. rewrite H0. simpl. reflexivity. }
    assert (HV2: Valid_dist (mu pd2)). { apply Valid_forall_NS in H5; try assumption. }
    apply IHc1 with (pd0:= pd0) (pd_inde:= pd_inde) (Hdom:= Hdom) (Hdomc:= Hdomc1)in H5; try assumption.
    destruct H5 as [pd_tmp Hsem1]. destruct Hsem1 as [HNS_tmp Hcomb].
    assert (HNS_T: pd0 =[ c1 ]=> pd_tmp) by assumption.
    apply NS_intersect_preserves with (V:= dom pd_inde) in HNS_T; try assumption.
    assert (HVtmp: Valid_dist (mu pd_tmp)). { apply Valid_forall_NS with (c:= c1) (pd:= pd0); try assumption. }
    apply IHc2 with (pd0:= pd_tmp) (pd_inde:= pd_inde) (Hdom:= HNS_T) (Hdomc:= Hdomc2) in H8; try assumption.
    destruct H8 as [pd_tmp' Hsem2]. destruct Hsem2 as [HNS_tmp' Hcomb'].
    assert (HNS0 : pd0 =[ c1;; c2 ]=> pd_tmp'). { 
        eapply NS_Seq; try assumption. 
        - apply NS_implies_WD_win with (pd':= pd_tmp). assumption.
        - apply NS_implies_WD_win with (pd:= pd_tmp) (pd':= pd_tmp'); try assumption. 
        - apply HNS_tmp.
        - assumption. }
    exists pd_tmp', HNS0. destruct Hcomb'; split; try assumption.
Qed.

Lemma hoare_OFrame_True: forall (phi0 phi1 phi2: Pformula) c, (*Important*)
  well_defined_Pf (phi0 ⊙ phi2) -> well_defined_Pf (phi1 ⊙ phi2) -> 
  NoControlFlow c ->
  is_domain_intersect (get_variables_in_winstr c) (get_var_in_Pformular phi2) = false ->
  get_readvar_in_winstr c = nil ->
  {{[[phi0]]}} c {{[[phi1]]}} -> 
  {{[[phi0 ⊙ phi2]]}} c {{[[phi1 ⊙ phi2]]}}.
Proof.
  intros phi0 phi1 phi2 c HWD0 HWD1 HNC Hdom Hreadc H. 
  assert (Hreadc_copy: get_readvar_in_winstr c = nil) by assumption.
  unfold hoare_triple in *. intros pd pd' HWF HZ HZc HNS Hsem.  
  assert (HWF': Valid_dist (mu pd')). { apply Valid_forall_NS in HNS; try assumption. }
  assert (Hsem': well_defined_Pf phi0 /\ well_defined_Pf phi2 /\ 
                    Valid_dist (mu pd) /\  
                    [[phi0]] pd /\ [[phi2]] pd /\
                      (independent (pd.(mu)) (get_var_in_Pformular phi0) (get_var_in_Pformular phi2)) /\
              is_domain_intersect (get_var_in_Pformular phi0) (get_var_in_Pformular phi2) = false).
      { apply odot_satisfies_iff. split; try assumption. split; try assumption. }
  destruct Hsem as [pd0 Hsem]. destruct Hsem as [pd2 Hsem]. 
  destruct Hsem as [Hdom02 Hsem].  
  destruct Hsem as [Hv0 Hsem]. destruct Hsem as [Hv2 Hsem]. 
  destruct Hsem as [Hsem0 Hsem]. destruct Hsem as [Hsem2 Hsub].
  assert (HWDc0: well_defined_winstr_with_pd c pd0). {
    apply Pd_Iden_implies_WD; try assumption. }
  apply NS_Identify with (pd:= pd0) in Hreadc; try assumption.
  destruct Hreadc as [pd_tmp HNS_tmp].
  simpl in Hsub. inversion HWD0; inversion HWD1; subst. 
  assert (Heq0: Sort_pd pd0 ≡ pd0) by apply pd_sort_equiv.
  assert (HVsort: Valid_dist (mu (Sort_pd pd0))). { 
     try apply Valid_implies_sort_Valid; try assumption. }
  assert (HWDc0_sort: well_defined_winstr_with_pd c (Sort_pd pd0)). {
    apply pd_equiv_sym in Heq0.
    apply pd_equiv_preserves_WD_win with (pd:= pd0); try assumption. }
  assert (Hsem0_sort: [[phi0]] (Sort_pd pd0)). { 
      apply pd_equiv_preserves_sem with (pd0:= pd0); try apply Valid_implies_sort_Valid; try assumption. }
  apply pd_equiv_sym in Heq0. 
  apply step_deterministic with (c:= c) (pd0':= pd_tmp) in Heq0; try apply Valid_implies_sort_Valid; try assumption. 
  destruct Heq0 as [pd_tmp_sort HNS_sort]. destruct HNS_sort as [Heq_sort HNS_sort].

  pose (V0:= get_var_in_Pformular phi0). pose (V2:= get_var_in_Pformular phi2). 
  pose (V1:= get_var_in_Pformular phi1).
  assert (HdomV0: (V0 ⊆ dom pd0)%domain). { apply satisfy_implies_dom_sub in Hsem0; try assumption. }
  assert (HdomV2: (V2 ⊆ dom pd2)%domain). { apply satisfy_implies_dom_sub in Hsem2; try assumption. }
  pose (pd2':= restrict_pd pd2 V2 HdomV2).
  assert (HWF2': Valid_dist (mu pd2')). { apply Valid_after_resX; try assumption. }
  assert (Hdom02': (dom pd0 ∩∅ V2)%domain). { apply intersect_subst_trans with (l2:= dom pd2); try assumption. }
  assert (HNS_copy: pd =[ c ]=> pd') by assumption.
  assert (HsubV2: 
    {| dom := (dom (Sort_pd pd0) ∪ V2)%domain;
       mu := mu (Sort_pd pd0) ⊗ (mu pd2 \| V2);
       all_partial := PD_combine_invar_mu (Sort_pd pd0) pd2' Hdom02'
    |} ⊑ pd). { 
      apply relation_mu_trans with (pd2:= {| dom := (dom (Sort_pd pd0) ∪ dom pd2)%domain; mu := mu (Sort_pd pd0) ⊗ mu pd2; 
                                             all_partial := PD_combine_invar_mu (Sort_pd pd0) pd2 Hdom02 |}); try assumption.
          - apply Valid_after_combine; try assumption; try apply Valid_after_resX; try assumption.
          - apply Valid_after_combine; try assumption.
          - split; simpl.
            + apply dom_subset_orb_compat; try apply dom_subset_refl; try assumption.
            + apply dst_equiv_sym. 
              apply dst_equiv_trans with (mu1:= (mu (Sort_pd pd0) \| (dom (Sort_pd pd0))) ⊗ (mu pd2 \| V2)).
              * apply dst_equiv_implies_combine_compat_r; try apply Valid_after_resX; try assumption.
              apply dst_equiv_sym. apply res_pd_to_dom_refl.
              * apply combine_res_merge_equiv; try assumption. try apply dom_subset_refl.
          - destruct Hsub. split; simpl; try assumption. 
            simpl in H1. apply dst_equiv_trans with (mu1:= mu pd0 ⊗ mu pd2); try assumption. 
            apply combine_left_sort_equiv.
           }

  destruct pd2 as [dom2 mu2 HPD2]. 
  destruct mu2 as [|(s2,p2) mu2']. {
    simpl in Hsub. destruct Hsub as [Hdom_comb Heq_comb]. 
    simpl in Hdom_comb, Heq_comb. rewrite combine_nil_r_eq in Heq_comb. 
    apply WF_dst_res_X_nil in Heq_comb; try assumption. 
    assert (Hmu: mu pd = []). {
      apply dst_eq_nil_iff. split; try assumption. }
    assert (Hmu': mu pd' = []). {
      apply NS_mu_implies_nil in HNS_copy; try assumption. }
    apply pd_equiv_preserves_sem with (pd0:= pd_emp (dom pd')); try assumption. 
    - split; simpl; [apply dom_equiv_refl| rewrite Hmu'; apply dst_equiv_refl] .
    - apply emp_dst_satisfies_phi; try assumption. simpl.
      apply H in HNS; try assumption.
      + apply dom_subset_orb_fst_iff. split. 
        * apply satisfy_implies_dom_sub; try assumption.
        * apply dom_subset_trans with (l1:= dom2); try assumption.
          apply dom_subset_orb_fst_iff in Hdom_comb. destruct Hdom_comb. 
          apply dom_subset_trans with (l1:= dom pd); try assumption.
          apply subset_NS with (c:=c); try assumption.
      + intuition. 
  }
  apply readc_local_execution_exists with (pd_inde:= pd2') (pd0:= (Sort_pd pd0)) (Hdom:= Hdom02') (Hdomc:= Hdom) in HNS; try assumption.
  destruct HNS. destruct H0. 
  assert (Hsort0_copy: Sort_pd pd0 =[ c ]=> x) by assumption. 
  assert (Hz0: dst_inject_Z (mu (Sort_pd pd0))). { 
    apply comb_dst_inject_Z in HsubV2; try assumption. 
    apply WF_dist_implies_sortdst_Sorted. assumption. }
  specialize (H (Sort_pd pd0) x HVsort Hz0 HZc x0 Hsem0_sort).
  assert (Hvar : (dom x ∩∅ V2)%domain). { apply NS_intersect_preserves with (V:= V2) in Hsort0_copy; try assumption. }
  exists x, pd2', Hvar. 
  split. { try apply Valid_forall_NS in Hsort0_copy; try assumption. }
  split; try apply Valid_after_resX; try assumption.
  split; try assumption. 
  split. { apply sem_satisfies_project_iff with (Hdom:= HdomV2) in Hsem2; try assumption. }
  apply readc_independent_preserved_by_NS with (pd:= pd) (pd0:= Sort_pd pd0)
      (c:= c) (Hdom:= Hdom02'); try assumption.
Qed.
(*************************)
Lemma hoare_Frame: forall (phi0 phi1 phi2: Pformula) c, 
  well_defined_Pf (phi0 ∧ phi2) -> well_defined_Pf (phi1 ∧ phi2) -> 
  is_domain_intersect (get_modvar_in_winstr c) (get_var_in_Pformular phi2) = false ->
  {{[[phi0]]}} c {{[[phi1]]}} -> 
  {{[[phi0 ∧ phi2]]}} c {{[[phi1 ∧ phi2]]}}.
Proof. 
  intros phi0 phi1 phi2 c HWD0 HWD1 Hdom H. 
  unfold hoare_triple in *. intros. destruct H4.
  specialize (H pd pd' H0 H1 H2); intuition. split; try assumption. 
  inversion HWD0; subst.
  apply intersect_preserves_satisfy with (phi:= phi2) in H3; intuition.
  rewrite intersect_comm. assumption.
Qed.
(*************************)
Lemma hoare_sum: forall p phi1 phi1' phi2 phi2' c, 
  well_defined_Pf (phi1 ⊕[p] phi2) -> well_defined_Pf (phi1' ⊕[p] phi2') ->
  {{[[phi1]]}} c {{[[phi1']]}} -> {{[[phi2]]}} c {{[[phi2']]}} -> 
  {{[[phi1 ⊕[p] phi2]]}} c {{[[phi1' ⊕[p] phi2']]}}.
Proof. 
  intros p phi1 phi1' phi2 phi2' c HWD0 HWD1 H1 H2. 
  unfold hoare_triple in *. intros. destruct H5.
  - destruct H5. destruct H6. destruct H6. intuition.
    left. intuition.
    assert (Hlinear: (mu pd == p * mu x + (1 - p) * mu x0)%dist_state) by assumption.
    assert (HV_linear: Valid_dist (p * mu x + (1 - p) * mu x0)%dist_state). {
      apply Valid_linear; try assumption. 
      + apply Rbound_loss. split; assumption.
      + apply Rp_1_minus_p_bounds. apply Rbound_loss. split; assumption.
      + rewrite R_plus_sub_eq_1. apply Rle_refl.  }
    assert (HZ: dst_inject_Z (mu x)). {
      apply dst_implies_inject_Z in H16; try assumption.
      apply dst_inject_Z_decom in H16. intuition. 
      apply dst_mult_inject_Z with (p:= / (p)) in H15. 
      rewrite dst_mult_assoc_eq in H15. rewrite <- Rinv_l_sym in H15. 
      + rewrite dst_mult_1_l in H15. assumption.
      + unfold not. intros. rewrite H16 in H7. apply Rlt_irrefl in H7. contradiction. }
    assert (HZ0: dst_inject_Z (mu x0)). {
      apply dst_implies_inject_Z in H16; try assumption.
      apply dst_inject_Z_decom in H16. intuition. 
      apply dst_mult_inject_Z with (p:= / (1- p)) in H17. 
      rewrite dst_mult_assoc_eq in H17. rewrite <- Rinv_l_sym in H17. 
      + rewrite dst_mult_1_l in H17. assumption.
      + unfold not. intros. 
        assert (Htmp: 0 < p < 1). { split; intuition. }
        apply Rp_lt1_minus_p_bounds in Htmp. destruct Htmp as [Hpgt0 Hplt1].
        rewrite H16 in Hpgt0. apply Rlt_irrefl in Hpgt0. contradiction. }
    apply linear_NS with (c:= c) (pd':= pd') in H16; intuition; try apply dom_equiv_sym; try assumption.
    destruct H16 as [x' H']. destruct H' as [x0' H']. intuition.
    assert (HVx': Valid_dist (mu x')). { 
      apply Valid_forall_NS with (c:=c) (pd:= x); try assumption. }
    assert (HVx0': Valid_dist (mu x0')). { 
      apply Valid_forall_NS with (c:=c) (pd:= x0); try assumption. }
    assert (Hx: x =[ c ]=> x') by assumption.
    assert (Hx0: x0 =[ c ]=> x0') by assumption.
    apply H1 in H15; apply H2 in H17; try assumption.   
    exists x', x0'. intuition; try apply dom_equiv_sym; try assumption.
    * rewrite <- NS_preserve_sum_eq with (c:=c) (pd:= x); try assumption.
      rewrite <- NS_preserve_sum_eq with (c:=c) (pd:= pd) (pd':= pd'); try assumption.
    * rewrite <- NS_preserve_sum_eq with (c:=c) (pd:= x0); try assumption.
      rewrite <- NS_preserve_sum_eq with (c:=c) (pd:= pd) (pd':= pd'); try assumption.
  - destruct H5. 
    + destruct H5. destruct H6. intuition. right. left. intuition. exists pd'. intuition. 
      * apply Valid_forall_NS with (c:=c) (pd:= pd); try assumption.
      * apply pd_equiv_refl.
      * apply H1 with (pd:= pd); intuition. apply pd_equiv_sym in H6.
        apply pd_equiv_preserves_sem with (phi:= phi1) in H6; intuition. 
        inversion HWD0; subst. assumption.
    + destruct H5. destruct H6. intuition. right. right. intuition. exists pd'. intuition.
      * apply Valid_forall_NS with (c:=c) (pd:= pd); try assumption.
      * apply pd_equiv_refl.
      * apply H2 with (pd:= pd); intuition. apply pd_equiv_sym in H6.
        apply pd_equiv_preserves_sem with (phi:= phi2) in H6; intuition. 
        inversion HWD0; subst. assumption.
Qed.
(*************************)
Theorem hoare_exists: forall x df c phi, 
  well_defined_Df (Dexist x df) -> well_defined_Pf phi -> exclude_odot phi ->
  (get_var_in_Pformular phi ⊆ get_var_in_Dformular df)%domain ->
  (forall r, {{[[(Pdeter df)]] [x |-> (Aco r)]}} c {{[[phi]]}}) -> 
  {{[[Pdeter (Dexist x df)]]}} c {{[[phi]]}}.
Proof.
  intros x df c phi WD_df WD_phi HEX Hsub Hall.
  unfold hoare_triple in *. intros. generalize dependent pd'.
  destruct pd as [dom mu HPD]. induction mu as [|(s,p) mu' IH]; intros.
  - apply NS_pd_implies_nil in H2. destruct H2. 
    apply pd_equiv_preserves_sem with (pd0:= (pd_emp (dom ∪ get_modvar_in_winstr c)%domain)); intuition.
    + rewrite H2. apply Valid_dist_nil.
    + split; simpl; try assumption. rewrite H2. apply dst_equiv_refl.
    + apply emp_dst_satisfies_phi; intuition. 
      apply satisfy_implies_dom_sub in H3; intuition.
      * simpl in H3. 
        apply dom_subset_trans with (l1:= get_var_in_Dformular df); try assumption.
        apply dom_subset_trans with (l1:= dom); try assumption. 
        apply dom_subset_orb_snd_l_r.
      * apply WD_Pdeter. assumption. 
  - inversion HPD; subst. 
    assert (HPD0: partial_dst_Prop dom [(s,p)]). {
      assert (H': partial_dst_Prop dom ((s,p)::mu')) by assumption.
      rewrite dst_cons_eq_add in H'. apply PD_decom in H'. destruct H'. assumption.
    }
    pose (pd0:= {| dom := dom; mu := [(s, p)]; all_partial := HPD0|}).
    pose (pd1:= {| dom := dom; mu := mu'; all_partial := H8|}).
    assert (Hv0: Valid_dist (mu pd0)). { apply Valid_dist_conj in H. intuition. }
    assert (Hv1: Valid_dist (mu pd1)). { apply Valid_dist_conj in H. intuition. }
    assert (Hv': Valid_dist (mu pd')). { apply Valid_forall_NS in H2; intuition. }
    assert (Hsum': sum_probs (mu {| dom := dom; mu := (s, p) :: mu'; all_partial := HPD |}) =
        sum_probs (mu pd') ).
      { apply NS_preserve_sum_eq in H2; intuition. }
    apply add_NS with (pd0:= pd0) (pd1:= pd1) in H2; intuition; 
      try apply dom_equiv_refl; try apply dst_equiv_refl.
    + destruct H2. destruct H2. intuition. 
      apply phi_sem_add with (phi:= phi) in H5; intuition.
      * apply Valid_forall_NS in H4; intuition.
      * apply Valid_forall_NS in H2; intuition.
      * apply dom_equiv_sym. assumption.
      * apply dom_equiv_sym. assumption.
      * apply NS_preserve_sum_eq in H4; intuition. 
        apply NS_preserve_sum_eq in H2; intuition.
        rewrite <- Hsum'. rewrite <- H2. rewrite <- H4. simpl. rewrite Rplus_0_r. reflexivity.
      * destruct H3. 
        assert(H': is_in_supp s (supp_mu (mu {| dom := dom; mu := (s, p) :: mu'; all_partial := HPD |})) =
  true). { simpl. apply in_supp_mu_cons_head. }
        specialize (H9 s H'). destruct H9. destruct H11. 
        apply Hall with (r:= x2) (pd:= pd0); intuition. 
        ** simpl in H0. simpl. intuition.
        ** simpl. split; intuition. 
        -- simpl. apply dom_subset_trans with (l1:= return_domain s); intuition. 
          apply dom_subset_eq_compat_right with (X:= dom); intuition.
          apply dom_subset_orb_snd_l_r.
        -- simpl in H12. apply orb_true_iff in H12. destruct H12; try discriminate. 
          rewrite state_eq_sym in H12.
          apply st_eq_implies_df_sem with (df:= df) in H12; try assumption.
    * apply IH with (HPD:= H8); try assumption; intuition. 
      ** simpl in H0. simpl. intuition.
      ** apply df_sem_conj_mu in H3; intuition.
Qed.
(******************************)
Theorem hoare_post_true : forall (P Q : PAssertion) c, (*PT *)
  (forall mu, Q mu) -> {{P}} c {{Q}}.
Proof. 
  unfold hoare_triple. 
  intros P Q c H. intros.
  apply H.
Qed.
Theorem hoare_pre_false : forall (P Q : PAssertion) c, 
  (forall mu, ~(P mu)) -> {{P}} c {{Q}}.
Proof.
  unfold hoare_triple. 
  intros P Q c H. intros.
  unfold not in H. 
  exfalso. apply H with pd. assumption.
Qed.
(******************************)
Lemma Pdeter_always_holds pd X n:
  ([[Pdeter (Dpred (Ava X = Aco n))]] [X |-> Aco n]) pd.
Proof.
  split. 
  - unfold WF_aexp_with_pd in HWFa. simpl in *.
    rewrite orb_domain_nil_r. apply dom_subset_orb_snd_l_r.
  - intros. destruct pd as [dom mu HPD]. simpl in H. 
    generalize dependent X. generalize dependent n.
    induction mu as [|(s,p) mu' IH]; intros. 
    + simpl in H. discriminate.
    + simpl in H. unfold supp_mu in H. simpl in H. 
      rewrite insert_st_pair_fst_eq_insert_st in H. 
      rewrite in_supp_insert_eq in H. apply orb_true_iff in H. destruct H.
      * rewrite state_eq_sym in H.
        apply st_eq_implies_df_sem with (df:= (Dpred (Ava X = Aco n))) in H; 
          try assumption.
        simpl. rewrite orb_domain_nil_r. split.
      ** rewrite dom_subset_eq_compat_left with (X:= (return_domain s ∪ singleton_bool_list X)%domain); 
        try reflexivity; try apply update_domain. 
        apply dom_subset_orb_snd_l_r.
      ** assert (Heq: get X (update s X n) = n) by apply get_update_eq. 
        rewrite Heq. rewrite Qeq_bool_refl. apply I.
      * inversion HPD; subst.
      apply IH with (HPD:= H4); try assumption.
Qed.

Lemma Valid_Iden: Valid_dist Identify_mu.
Proof.
  unfold Valid_dist. split. 
  - simpl. rewrite Rplus_0_r. split; try apply Rle_refl. apply Rle_0_1.
  - simpl. split; try apply I. split; try apply Rle_refl. apply Rlt_0_1.
Qed.

Lemma Odot_E phi: 
  well_defined_Pf phi ->
  [[phi]] <<->> [[(Pdeter (Dpred Btrue)) ⊙ phi]].
Proof.
  split. { 
    unfold assert_implies in *. intros. 
    assert (HWD: well_defined_Pf ((Pdeter (Dpred Btrue)) ⊙ phi)). { 
      apply WD_Odot; try apply WD_Pdeter; try apply WD_Dpred; try assumption.
      split; try assumption. }
    assert (Hdom_I: partial_dst_Prop nil Identify_mu). { 
      apply PD_cons; try apply PD_nil. simpl. apply dom_equiv_refl. }
    pose (pd1:= Build_partial_dist nil Identify_mu Hdom_I).
    exists pd1, pd. 
    assert (Htmp: is_domain_intersect ([]) (dom pd) = false). {
      simpl. reflexivity. } 
    exists Htmp. 
    split. { simpl. apply Valid_Iden. }
    split; try assumption. 
    split. { simpl. split; try reflexivity. intros. split; try reflexivity. }
    split; try assumption.
    split. 
    - simpl; try apply dom_subset_refl. 
    - apply dst_equiv_trans with (mu1:= (mu pd)). 
      + simpl. apply res_pd_to_dom_refl.
      + simpl. induction (mu pd); simpl; try apply dst_equiv_refl. 
        destruct a. simpl. rewrite dst_cons_eq_add. 
        rewrite dst_cons_eq_add with (p:= (1*r)%R).
        apply dst_add_preserves_equiv.
        * apply Peq_one_st. split; try apply state_eq_refl.
        rewrite Rmult_1_l. reflexivity.
        * apply IHd.  
          ** apply Valid_dist_inv in H0. assumption.
          ** inversion H1. assumption. 
  }
  unfold assert_implies in *. intros pd H0 HZ H1. 
  destruct H1. destruct H1. destruct H1. 
  destruct H1. destruct H2. destruct H3.
  destruct H4. simpl in H5. destruct H5. simpl in *.
  assert (HV : is_domain_subset (dom x0) (dom pd) = true). {
    apply dom_subset_orb_fst_iff in H5. destruct H5. assumption. }
  apply sem_resV_implies_pd with (V:= (dom x0)) (HV:= HV); try assumption.
  - apply satisfy_implies_dom_sub; try assumption.
  - apply dst_equiv_sym in H6.
    apply dst_equiv_trans with (mu0:= mu x0 ⊗ mu x) in H6; try apply combine_sym.
    apply dst_equiv_sym in H6. 
    apply Peq_implies_res_eq with (X:= (dom x0)) in H6. 
    + apply dst_equiv_trans with (mu0:= (mu pd) \| (dom x0)) in H6. 
      * apply dst_equiv_sym in H6.  
      apply dst_equiv_trans with (mu0:= (sum_probs (mu x) * (mu x0))%dist_state) in H6. 
      ** apply sem_mult_cofe with (p:= (sum_probs (mu x))) in H4; try assumption. 
      --
      assert (Heq: {|
        dom := dom x0;
        mu := (mu pd) \| (dom x0);
        all_partial := PD_after_res (dom x0) (dom pd) (mu pd) HV (all_partial pd)
      |} ≡ {|
          dom := dom x0;
          mu := (sum_probs (mu x) * mu x0)%dist_state;
          all_partial := pd_mult_preserve_PD x0 (sum_probs (mu x))
        |}). { 
        split; simpl; try apply dom_equiv_refl. apply dst_equiv_sym. assumption. }
      apply pd_equiv_preserves_sem with (pd0:= {|
        dom := dom x0;
        mu := (sum_probs (mu x) * mu x0)%dist_state;
        all_partial := pd_mult_preserve_PD x0 (sum_probs (mu x))
      |}); try assumption.
        ++ simpl. apply Valid_mult_cofe; try assumption. destruct H1. assumption.
        ++ simpl. apply Valid_after_resX. assumption.
      -- destruct H1. destruct H1. assumption.
      -- rewrite dst_sum_prob_coef_mult. destruct H1. destruct H1. destruct H2. destruct H2. 
        split. 
        ++ rewrite <- Rmult_0_l with (r:= 0). apply Rmult_le_compat; try apply Rle_refl; try assumption.
        ++ rewrite <- Rmult_1_l with (r:= 1). apply Rmult_le_compat; try apply Rle_refl; try assumption.
      ** apply dst_equiv_sym. apply res_comb_equiv; try assumption. 
        rewrite intersect_comm. assumption.
      * apply res_to_subset_equiv. apply dom_subset_orb_snd_l_r.
    + apply Valid_after_resX. try assumption.
    + apply Valid_after_combine; assumption.
Qed.
(*************************)  
Lemma OdotD_r: forall p phi0 phi1 phi (Hp: 0<= p <= 1), 
  well_defined_Pf ((phi0 ⊕[ p ] phi1) ⊙ phi) -> 
  is_domain_intersect (get_var_in_Pformular phi0) (get_var_in_Pformular phi) = false ->
  is_domain_intersect (get_var_in_Pformular phi1) (get_var_in_Pformular phi) = false ->
  [[(phi0 ⊕[ p ] phi1) ⊙ phi]] ->> 
  [[((phi0 ⊙ phi) ⊕[ p ] (phi1 ⊙ phi))]].
Proof.
  intros p phi0 phi1 phi Hp HWD. intros Hinsec0 Hinsec1.
  intros pd HV HZ Hsem.
  destruct Hsem as [pd1 H]. destruct H as [pd2 H].
  destruct H as [Hvar H].
  destruct H as [HWF1 H]. destruct H as [HWF2 H]. 
  destruct H as [Hsem' H]. destruct H as [Hsem Hsub].
  destruct Hsub as [Hsub Heq_sub]. simpl in Hsub. simpl in Heq_sub.
  destruct Hsem' as [H_case1| Hsem']. 
  - destruct H_case1 as [Hp_case1 H]. 
    destruct H as [pd00 H]. destruct H as [pd01 H].
    destruct H as [HWF00 H]. destruct H as [HWF01 H].
    destruct H as [Hdom00 H]. destruct H as [Hdom01 H].
    destruct H as [Hsem00 H]. destruct H as [Hsem01 H].
    destruct H as [Hsum00 H]. destruct H as [Hsum01 Heq].
    inversion HWD; subst. inversion H1; subst. simpl in H3. 
    destruct (Rle_lt_dec p 0) eqn: Hl; destruct (Rle_lt_dec 1 p) eqn: Hr. 
    -- destruct Hp_case1 as [H H0]; apply Rlt_not_le in H; apply Rlt_not_le in H0; try contradiction.
    -- destruct Hp_case1 as [H H0]; apply Rlt_not_le in H; apply Rlt_not_le in H0; try contradiction.
    -- destruct Hp_case1 as [H H0]; apply Rlt_not_le in H; apply Rlt_not_le in H0; try contradiction.
    -- 
    pose (X:= ((get_var_in_Pformular phi0 ∪ get_var_in_Pformular phi1) ∪ get_var_in_Pformular phi)%domain).
    assert (Hvar0_pd00: is_domain_subset (get_var_in_Pformular phi0) (dom pd00) = true). {
      apply satisfy_implies_dom_sub in Hsem00; try assumption. }
    assert (Hvar1_pd00: is_domain_subset (get_var_in_Pformular phi1) (dom pd01) = true). {
      apply satisfy_implies_dom_sub in Hsem01; try assumption. } 
    assert (Hdom0001: (dom pd00 == dom pd01)%domain). {
      apply dom_equiv_sym in Hdom01.
      apply dom_equiv_trans with (l1:= (dom pd1)); try assumption. }
    assert (Hvar_pd2: is_domain_subset (get_var_in_Pformular phi) (dom pd2) = true). {
      apply satisfy_implies_dom_sub; try assumption. } 
    assert (HX: is_domain_subset X (dom pd) = true). {
      unfold X. 
      apply dom_subset_trans with (l1:= (dom pd1 ∪ dom pd2)%domain); try assumption.
      apply dom_subset_orb_compat; try assumption.
      apply dom_subset_orb_fst_iff. 
      apply dom_subset_eq_compat_left with (Y:= (dom pd1)) in Hvar0_pd00; try assumption.
      apply dom_subset_eq_compat_left with (Y:= (dom pd1)) in Hvar1_pd00; try assumption.
      split; try assumption. }
    apply sem_resV_implies_pd with (V:= X) (HV:= HX); try assumption. 
      + apply WD_Pplus; try apply WD_Odot; try assumption. 
      + simpl. rewrite Hl. rewrite Hr. unfold X. apply dom_eq_orb_dis_l. 
      + left. split; try assumption. 
        assert (Hvar0: is_domain_intersect (dom pd00) (dom pd2) = false). {
          apply dom_eq_intersect_compat_right with (l:= (dom pd2)) in Hdom00.
          rewrite Hdom00. assumption.  }
        assert (Hvar1: is_domain_intersect (dom pd01) (dom pd2) = false). {
          apply dom_eq_intersect_compat_right with (l:= (dom pd2)) in Hdom01.
          rewrite Hdom01. assumption.  }  
        assert (Hdom0: is_domain_subset X (dom (combine_pd pd00 pd2 Hvar0)) = true). {
          simpl. apply dom_subset_eq_compat_right with 
              (X:= (((get_var_in_Pformular phi0) ∪ (get_var_in_Pformular phi1)) ∪ get_var_in_Pformular phi)%domain).
          - unfold X. apply dom_equiv_refl. 
          - apply dom_subset_orb_compat; try assumption. 
            apply dom_subset_orb_fst_iff. split; try assumption.
            apply dom_subset_eq_compat_left with (X:= (dom pd01)); try assumption.
            apply dom_equiv_sym. assumption. }
        assert (Hdom1: is_domain_subset X (dom (combine_pd pd01 pd2 Hvar1)) = true). {
          simpl. apply dom_subset_eq_compat_right with 
              (X:= (((get_var_in_Pformular phi0) ∪ (get_var_in_Pformular phi1)) ∪ get_var_in_Pformular phi)%domain).
          - unfold X. apply dom_equiv_refl. 
          - apply dom_subset_orb_compat; try assumption. 
            apply dom_subset_orb_fst_iff. split; try assumption.
            apply dom_subset_eq_compat_left with (X:= (dom pd00)); try assumption. }
        exists (restrict_pd (combine_pd pd00 pd2 Hvar0) X Hdom0), 
                (restrict_pd (combine_pd pd01 pd2 Hvar1) X Hdom1).
        split; try apply Valid_after_resX; try assumption; try apply Valid_after_combine; try assumption.
        split; try apply Valid_after_resX; try assumption; try apply Valid_after_combine; try assumption.
        split. { simpl. apply dom_equiv_refl. }
        split. { simpl. apply dom_equiv_refl. }
        split. { simpl. 
          pose (X1:= (get_var_in_Pformular phi0 ∪ get_var_in_Pformular phi1)%domain).
          assert (HdomX1: is_domain_subset X1 (dom pd00) = true). { 
            apply dom_subset_orb_fst_iff. split; try assumption. 
            apply dom_subset_eq_compat_left with (X:= (dom pd01)); try assumption.
            apply dom_equiv_sym. assumption. }
          exists (restrict_pd pd00 X1 HdomX1), 
                  (restrict_pd pd2 (get_var_in_Pformular phi) Hvar_pd2), H3.
          split; try apply Valid_after_resX; try assumption. 
          split; try apply Valid_after_resX; try assumption. 
          split. { apply sem_satisfies_project_implies_V; try assumption. apply dom_subset_orb_snd_l_r. }
          split. { apply sem_satisfies_project_implies_V; try assumption. apply dom_subset_refl. }
          split; simpl; try apply dom_subset_refl.
          pose (X2:= get_var_in_Pformular phi). fold X2.
          apply dst_equiv_sym in Heq_sub. 
          apply dst_equiv_trans with (mu0:= (p * mu pd00 + (1 - p) * mu pd01)%dist_state ⊗ mu pd2) in Heq_sub. 
          - apply dst_equiv_trans with (mu1:= (mu pd00 ⊗ mu pd2) \| (X1 ∪ X2)%domain); try assumption.
            + apply dst_equiv_sym. apply res_to_subset_equiv. apply dom_subset_refl.
            + apply dst_equiv_sym. apply combine_res_merge_equiv; try assumption.
          - apply dst_equiv_sym. apply dst_equiv_preserves_combine; try assumption; try apply dst_equiv_refl.
            apply Valid_linear; try assumption.
            + apply Rp_1_minus_p_bounds; assumption.
            + rewrite R_plus_sub_eq_1. apply Rle_refl. }
        split. { simpl.
          pose (X1:= (get_var_in_Pformular phi0 ∪ get_var_in_Pformular phi1)%domain).
          assert (HdomX1: is_domain_subset X1 (dom pd01) = true). { 
            apply dom_subset_orb_fst_iff. split; try assumption. 
            apply dom_subset_eq_compat_left with (X:= (dom pd00)); try assumption. }
          exists (restrict_pd pd01 X1 HdomX1), 
                  (restrict_pd pd2 (get_var_in_Pformular phi) Hvar_pd2), H3.
          split; try apply Valid_after_resX; try assumption. 
          split; try apply Valid_after_resX; try assumption. 
          split. { apply sem_satisfies_project_implies_V; try assumption. apply dom_subset_orb_snd_l_r. }
          split. { apply sem_satisfies_project_implies_V; try assumption. apply dom_subset_refl. }
          split; simpl; try apply dom_subset_refl.
          pose (X2:= get_var_in_Pformular phi). fold X2.
          apply dst_equiv_sym in Heq_sub. 
          apply dst_equiv_trans with (mu0:= (p * mu pd00 + (1 - p) * mu pd01)%dist_state ⊗ mu pd2) in Heq_sub. 
          - apply dst_equiv_trans with (mu1:= (mu pd01 ⊗ mu pd2) \| (X1 ∪ X2)%domain); try assumption.
            + apply dst_equiv_sym. apply res_to_subset_equiv. apply dom_subset_refl.
            + apply dst_equiv_sym. apply combine_res_merge_equiv; try assumption.
          - apply dst_equiv_sym. apply dst_equiv_preserves_combine; try assumption; try apply dst_equiv_refl.
            apply Valid_linear; try assumption.
            + apply Rp_1_minus_p_bounds; assumption.
            + rewrite R_plus_sub_eq_1. apply Rle_refl. }
        simpl. 
        repeat rewrite <- sum_eq_after_res. repeat rewrite sum_probs_combine_eq_mult.
        rewrite Hsum00. rewrite Hsum01.
        split. {  
          apply dst_equiv_implies_sum_probs_eq in Heq_sub; try apply Valid_after_combine; try apply Valid_after_resX; try assumption.
          repeat rewrite <- sum_eq_after_res in Heq_sub. rewrite sum_probs_combine_eq_mult in Heq_sub.
          rewrite Heq_sub. reflexivity. }
        split. {  
          apply dst_equiv_implies_sum_probs_eq in Heq_sub; try apply Valid_after_combine; try apply Valid_after_resX; try assumption.
          repeat rewrite <- sum_eq_after_res in Heq_sub. rewrite sum_probs_combine_eq_mult in Heq_sub.
          rewrite Heq_sub. reflexivity. }
        simpl in Hdom0. simpl in Hdom1.
        apply Peq_implies_res_eq with (X:= X) in Heq_sub; try apply Valid_after_resX; try apply Valid_after_combine; try assumption.
        apply dst_equiv_trans with (mu0:= (mu pd \| X)) in Heq_sub; try apply res_to_subset_equiv.
        * apply dst_equiv_trans with (mu1:= ((mu pd1 ⊗ mu pd2) \| X)); try assumption.
          repeat rewrite <- res_dst_to_X_mult_coef. 
          rewrite <- res_add_decom_eq. 
          apply Peq_implies_res_eq; try apply Valid_after_combine; try assumption.
          ** apply Valid_linear; try assumption; try apply Valid_after_combine; try assumption.
          *** apply Rp_1_minus_p_bounds; assumption.
          *** rewrite R_plus_sub_eq_1. apply Rle_refl.
          ** repeat rewrite <- combine_mult_l_assoc_eq.
          rewrite <- combine_add_distr_l_eq. 
          apply dst_equiv_implies_combine_compat_r; try assumption.
          apply Valid_linear; try assumption; try apply Valid_after_combine; try assumption.
          *** apply Rp_1_minus_p_bounds; assumption.
          *** rewrite R_plus_sub_eq_1. apply Rle_refl.
        * apply dom_subset_eq_compat_left with (X:= (dom pd00 ∪ dom pd2)%domain); try assumption.
        apply dom_eq_orb_compat_right. assumption.
  - destruct Hsem' as [H |H]. 
    + destruct H as [Hp_case2 H]. destruct H. 
      destruct H as [HWFx H]. destruct H as [Heq H].
      destruct H as [Hsem0 Hsumx]. destruct Heq as [Hdom_eq Hmu_eq]. 
      inversion HWD; subst. inversion H1; subst. simpl in H3. 
      destruct (Rle_lt_dec 1 0) eqn: Hl; destruct (Rle_lt_dec 1 1) eqn: Hr.
      -- assert (Hcontra: (1 <= 0)%R) by assumption.
        apply Rle_not_lt in Hcontra. unfold not in Hcontra. 
        contradict Hcontra. apply Rlt_0_1.
      -- assert (Hcontra: (1 <= 0)%R) by assumption.
        apply Rle_not_lt in Hcontra. unfold not in Hcontra. 
        contradict Hcontra. apply Rlt_0_1.
      -- 
      pose (X:= ((get_var_in_Pformular phi0 ∪ get_var_in_Pformular phi))%domain).
      assert (Hvar0_pdx: is_domain_subset (get_var_in_Pformular phi0) (dom x) = true). {
      apply satisfy_implies_dom_sub in Hsem0; try assumption. }
      assert (Hvar_pd2: is_domain_subset (get_var_in_Pformular phi) (dom pd2) = true). {
        apply satisfy_implies_dom_sub; try assumption. } 
      assert (HX: is_domain_subset X (dom pd) = true). { 
        unfold X. 
        apply dom_subset_trans with (l1:= (dom pd1 ∪ dom pd2)%domain); try assumption.
        apply dom_subset_orb_compat; try assumption. 
        apply dom_subset_eq_compat_left with (X:= (dom x)); try assumption. }     
      apply sem_resV_implies_pd with (V:= X) (HV:= HX); try assumption.
      * apply WD_Pplus; try apply WD_Odot; try assumption.
      * simpl. rewrite Hl. rewrite Hr. apply dom_subset_refl.
      * right. left. split; try reflexivity. 
        assert (Hvar0: is_domain_intersect (dom x) (dom pd2) = false). {
          apply dom_eq_intersect_compat_right with (l:= (dom pd2)) in Hdom_eq.
          rewrite Hdom_eq. assumption.  }
        assert (Hdom0: is_domain_subset X (dom (combine_pd x pd2 Hvar0)) = true). {
          simpl. apply dom_subset_orb_compat; try assumption. } 
        exists (restrict_pd (combine_pd x pd2 Hvar0) X Hdom0).
        split; try apply Valid_after_resX; try assumption; try apply Valid_after_combine; try assumption.
        split. { split; simpl; try apply dom_equiv_refl. 
          apply Peq_implies_res_eq with (X:= X) in Heq_sub; try apply Valid_after_resX; try apply Valid_after_combine; try assumption.
          apply dst_equiv_trans with (mu0:= (mu pd \| X)) in Heq_sub; try apply res_to_subset_equiv.
          * apply dst_equiv_sym. apply dst_equiv_sym in Hmu_eq. 
          apply dst_equiv_trans with (mu1:= ((mu pd1 ⊗ mu pd2) \| X)%dist_state); try assumption.
          apply Peq_implies_res_eq; try apply Valid_after_combine; try assumption. 
          apply dst_equiv_implies_combine_compat_r; try assumption.
          * apply dom_subset_orb_compat; try assumption. 
          apply dom_subset_eq_compat_left with (X:= (dom x)); try assumption. }
        split. { simpl. 
          exists (restrict_pd x (get_var_in_Pformular phi0) Hvar0_pdx),
                  (restrict_pd pd2 (get_var_in_Pformular phi) Hvar_pd2), H3.
          split; try apply Valid_after_resX; try assumption. 
          split; try apply Valid_after_resX; try assumption. 
          split. { apply sem_satisfies_project_implies_V; try assumption. apply dom_subset_refl. }
          split. { apply sem_satisfies_project_implies_V; try assumption. apply dom_subset_refl. }
          split; simpl; try apply dom_subset_refl.
          fold X.
          apply dst_equiv_sym in Heq_sub. 
          apply dst_equiv_trans with (mu1:= (mu x ⊗ mu pd2) \| X); try assumption.
            + apply dst_equiv_sym. apply res_to_subset_equiv. apply dom_subset_refl.
            + apply dst_equiv_sym. apply combine_res_merge_equiv; try assumption. }
        simpl. 
        repeat rewrite <- sum_eq_after_res. repeat rewrite sum_probs_combine_eq_mult.
        rewrite Hsumx. 
        apply dst_equiv_implies_sum_probs_eq in Heq_sub; try apply Valid_after_combine; try apply Valid_after_resX; try assumption.
        repeat rewrite <- sum_eq_after_res in Heq_sub. rewrite sum_probs_combine_eq_mult in Heq_sub.
        rewrite Heq_sub. reflexivity. 
      -- assert (Hcontra: (1 < 1)%R) by assumption. apply Rlt_irrefl in Hcontra. contradiction.
    + destruct H as [Hp_case2 H]. destruct H. 
      destruct H as [HWFx H]. destruct H as [Heq H].
      destruct H as [Hsem0 Hsumx]. destruct Heq as [Hdom_eq Hmu_eq]. 
      inversion HWD; subst. inversion H1; subst. simpl in H3. 
      destruct (Rle_lt_dec 1 0) eqn: Hl; destruct (Rle_lt_dec 0 0) eqn: Hr.
      -- assert (Hcontra: (1 <= 0)%R) by assumption.
        apply Rle_not_lt in Hcontra. unfold not in Hcontra. 
        contradict Hcontra. apply Rlt_0_1.
      -- assert (Hcontra: (1 <= 0)%R) by assumption.
        apply Rle_not_lt in Hcontra. unfold not in Hcontra. 
        contradict Hcontra. apply Rlt_0_1.
      -- 
      pose (X:= ((get_var_in_Pformular phi1 ∪ get_var_in_Pformular phi))%domain).
      assert (Hvar0_pdx: is_domain_subset (get_var_in_Pformular phi1) (dom x) = true). {
      apply satisfy_implies_dom_sub in Hsem0; try assumption. }
      assert (Hvar_pd2: is_domain_subset (get_var_in_Pformular phi) (dom pd2) = true). {
        apply satisfy_implies_dom_sub; try assumption. } 
      assert (HX: is_domain_subset X (dom pd) = true). { 
        unfold X. 
        apply dom_subset_trans with (l1:= (dom pd1 ∪ dom pd2)%domain); try assumption.
        apply dom_subset_orb_compat; try assumption. 
        apply dom_subset_eq_compat_left with (X:= (dom x)); try assumption. }     
      apply sem_resV_implies_pd with (V:= X) (HV:= HX); try assumption.
      * apply WD_Pplus; try apply WD_Odot; try assumption.
      * simpl. rewrite Hl. rewrite Hr. apply dom_subset_refl.
      * right. right. split; try reflexivity. 
        assert (Hvar0: is_domain_intersect (dom x) (dom pd2) = false). {
          apply dom_eq_intersect_compat_right with (l:= (dom pd2)) in Hdom_eq.
          rewrite Hdom_eq. assumption.  }
        assert (Hdom0: is_domain_subset X (dom (combine_pd x pd2 Hvar0)) = true). {
          simpl. apply dom_subset_orb_compat; try assumption. } 
        exists (restrict_pd (combine_pd x pd2 Hvar0) X Hdom0).
        split; try apply Valid_after_resX; try assumption; try apply Valid_after_combine; try assumption.
        split. { split; simpl; try apply dom_equiv_refl. 
          apply Peq_implies_res_eq with (X:= X) in Heq_sub; try apply Valid_after_resX; try apply Valid_after_combine; try assumption.
          apply dst_equiv_trans with (mu0:= (mu pd \| X)) in Heq_sub; try apply res_to_subset_equiv.
          * apply dst_equiv_sym. apply dst_equiv_sym in Hmu_eq. 
          apply dst_equiv_trans with (mu1:= ((mu pd1 ⊗ mu pd2) \| X)%dist_state); try assumption.
          apply Peq_implies_res_eq; try apply Valid_after_combine; try assumption. 
          apply dst_equiv_implies_combine_compat_r; try assumption.
          * apply dom_subset_orb_compat; try assumption. 
          apply dom_subset_eq_compat_left with (X:= (dom x)); try assumption. }
        split. { simpl. 
          exists (restrict_pd x (get_var_in_Pformular phi1) Hvar0_pdx),
                  (restrict_pd pd2 (get_var_in_Pformular phi) Hvar_pd2), H3.
          split; try apply Valid_after_resX; try assumption. 
          split; try apply Valid_after_resX; try assumption. 
          split. { apply sem_satisfies_project_implies_V; try assumption. apply dom_subset_refl. }
          split. { apply sem_satisfies_project_implies_V; try assumption. apply dom_subset_refl. }
          split; simpl; try apply dom_subset_refl.
          fold X.
          apply dst_equiv_sym in Heq_sub. 
          apply dst_equiv_trans with (mu1:= (mu x ⊗ mu pd2) \| X); try assumption.
            + apply dst_equiv_sym. apply res_to_subset_equiv. apply dom_subset_refl.
            + apply dst_equiv_sym. apply combine_res_merge_equiv; try assumption. }
        simpl. 
        repeat rewrite <- sum_eq_after_res. repeat rewrite sum_probs_combine_eq_mult.
        rewrite Hsumx. 
        apply dst_equiv_implies_sum_probs_eq in Heq_sub; try apply Valid_after_combine; try apply Valid_after_resX; try assumption.
        repeat rewrite <- sum_eq_after_res in Heq_sub. rewrite sum_probs_combine_eq_mult in Heq_sub.
        rewrite Heq_sub. reflexivity. 
      -- assert (Hcontra: (0 < 0)%R) by assumption. apply Rlt_irrefl in Hcontra. contradiction.
Qed.

Lemma OdotD_l: forall p phi0 phi1 phi (Hp: 0<= p <= 1), 
  well_defined_Pf (phi ⊙ (phi0 ⊕[ p ] phi1)) -> 
  is_domain_intersect (get_var_in_Pformular phi) (get_var_in_Pformular phi0) = false ->
  is_domain_intersect (get_var_in_Pformular phi) (get_var_in_Pformular phi1) = false ->
  [[phi ⊙ (phi0 ⊕[ p ] phi1)]] ->> 
  [[((phi ⊙ phi0) ⊕[ p ] (phi ⊙ phi1))]].
Proof.
  intros p phi0 phi1 phi Hp HWD. intros Hinsec0 Hinsec1.
  intros pd HV HZ Hsem.
  destruct Hsem as [pd2 H]. destruct H as [pd1 H].
  destruct H as [Hvar H].
  destruct H as [HWF2 H]. destruct H as [HWF1 H]. 
  destruct H as [Hsem H]. destruct H as [Hsem' Hsub].
  destruct Hsub as [Hsub Heq_sub]. simpl in Hsub. simpl in Heq_sub.
  destruct Hsem' as [H_case1| Hsem']. 
  - destruct H_case1 as [Hp_case1 H]. 
    destruct H as [pd00 H]. destruct H as [pd01 H].
    destruct H as [HWF00 H]. destruct H as [HWF01 H].
    destruct H as [Hdom00 H]. destruct H as [Hdom01 H].
    destruct H as [Hsem00 H]. destruct H as [Hsem01 H].
    destruct H as [Hsum00 H]. destruct H as [Hsum01 Heq].
    inversion HWD; subst. inversion H2; subst. simpl in H3. 
    destruct (Rle_lt_dec p 0) eqn: Hl; destruct (Rle_lt_dec 1 p) eqn: Hr. 
    -- destruct Hp_case1 as [H H0]; apply Rlt_not_le in H; apply Rlt_not_le in H0; try contradiction.
    -- destruct Hp_case1 as [H H0]; apply Rlt_not_le in H; apply Rlt_not_le in H0; try contradiction.
    -- destruct Hp_case1 as [H H0]; apply Rlt_not_le in H; apply Rlt_not_le in H0; try contradiction.
    -- assert (Hsub_sym: is_domain_subset (dom pd1 ∪ dom pd2)%domain (dom pd) = true). {
        apply dom_subset_orb_fst_iff in Hsub. destruct Hsub. 
        apply dom_subset_orb_fst_iff. split; try assumption. }
      pose (X:= (get_var_in_Pformular phi ∪ (get_var_in_Pformular phi0 ∪ get_var_in_Pformular phi1) )%domain).
      assert (Hvar0_pd00: is_domain_subset (get_var_in_Pformular phi0) (dom pd00) = true). {
        apply satisfy_implies_dom_sub in Hsem00; try assumption. }
      assert (Hvar1_pd00: is_domain_subset (get_var_in_Pformular phi1) (dom pd01) = true). {
        apply satisfy_implies_dom_sub in Hsem01; try assumption. } 
      assert (Hdom0001: (dom pd00 == dom pd01)%domain). {
        apply dom_equiv_sym in Hdom01.
        apply dom_equiv_trans with (l1:= (dom pd1)); try assumption. }
      assert (Hvar_pd2: is_domain_subset (get_var_in_Pformular phi) (dom pd2) = true). {
        apply satisfy_implies_dom_sub; try assumption. } 
      assert (HX: is_domain_subset X (dom pd) = true). {
        unfold X. rewrite orb_domain_comm.
        apply dom_subset_trans with (l1:= (dom pd1 ∪ dom pd2)%domain); try assumption.
        apply dom_subset_orb_compat; try assumption.
        apply dom_subset_orb_fst_iff. 
        apply dom_subset_eq_compat_left with (Y:= (dom pd1)) in Hvar0_pd00; try assumption.
        apply dom_subset_eq_compat_left with (Y:= (dom pd1)) in Hvar1_pd00; try assumption.
        split; try assumption. }
      apply sem_resV_implies_pd with (V:= X) (HV:= HX); try assumption. 
      + apply WD_Pplus; try apply WD_Odot; try assumption. 
      + simpl. rewrite Hl. rewrite Hr. unfold X. 
        apply dom_eq_orb_dis_r. 
      + left. split; try assumption. 
        assert (Hvar0: is_domain_intersect (dom pd00) (dom pd2) = false). {
          apply dom_eq_intersect_compat_right with (l:= (dom pd2)) in Hdom00.
          rewrite Hdom00. rewrite intersect_comm.
          assumption.  }
        assert (Hvar1: is_domain_intersect (dom pd01) (dom pd2) = false). {
          apply dom_eq_intersect_compat_right with (l:= (dom pd2)) in Hdom01.
          rewrite Hdom01. rewrite intersect_comm. assumption.  }  
        assert (Hdom0: is_domain_subset X (dom (combine_pd pd00 pd2 Hvar0)) = true). {
          simpl. apply dom_subset_eq_compat_right with 
              (X:= (((get_var_in_Pformular phi0) ∪ (get_var_in_Pformular phi1)) ∪ get_var_in_Pformular phi)%domain).
          - unfold X. rewrite orb_domain_comm. apply dom_equiv_refl.
          - apply dom_subset_orb_compat; try assumption. 
            apply dom_subset_orb_fst_iff. split; try assumption.
            apply dom_subset_eq_compat_left with (X:= (dom pd01)); try assumption.
            apply dom_equiv_sym. assumption. }
        assert (Hdom1: is_domain_subset X (dom (combine_pd pd01 pd2 Hvar1)) = true). {
          simpl. apply dom_subset_eq_compat_right with 
              (X:= (((get_var_in_Pformular phi0) ∪ (get_var_in_Pformular phi1)) ∪ get_var_in_Pformular phi)%domain).
          - unfold X. rewrite orb_domain_comm. apply dom_equiv_refl. 
          - apply dom_subset_orb_compat; try assumption. 
            apply dom_subset_orb_fst_iff. split; try assumption.
            apply dom_subset_eq_compat_left with (X:= (dom pd00)); try assumption. }
        exists (restrict_pd (combine_pd pd00 pd2 Hvar0) X Hdom0), 
                (restrict_pd (combine_pd pd01 pd2 Hvar1) X Hdom1).
        split; try apply Valid_after_resX; try assumption; try apply Valid_after_combine; try assumption.
        split; try apply Valid_after_resX; try assumption; try apply Valid_after_combine; try assumption.
        split. { simpl. apply dom_equiv_refl. }
        split. { simpl. apply dom_equiv_refl. }
        split. { simpl. 
          pose (X1:= (get_var_in_Pformular phi0 ∪ get_var_in_Pformular phi1)%domain).
          assert (HdomX1: is_domain_subset X1 (dom pd00) = true). { 
            apply dom_subset_orb_fst_iff. split; try assumption. 
            apply dom_subset_eq_compat_left with (X:= (dom pd01)); try assumption.
            apply dom_equiv_sym. assumption. }
          exists (restrict_pd pd2 (get_var_in_Pformular phi) Hvar_pd2), (restrict_pd pd00 X1 HdomX1), 
                   H3.
          split; try apply Valid_after_resX; try assumption. 
          split; try apply Valid_after_resX; try assumption. 
          split. { apply sem_satisfies_project_implies_V; try assumption. apply dom_subset_refl. }
          split. { apply sem_satisfies_project_implies_V; try assumption. apply dom_subset_orb_snd_l_r. }
          split; simpl; try apply dom_subset_refl.
          pose (X2:= get_var_in_Pformular phi). fold X2.
          apply dst_equiv_sym in Heq_sub. 
          apply dst_equiv_trans with (mu0:= (p * mu pd00 + (1 - p) * mu pd01)%dist_state ⊗ mu pd2) in Heq_sub. 
          - apply dst_equiv_trans with (mu1:= (mu pd00 ⊗ mu pd2) \| (X1 ∪ X2)%domain); try assumption.
            + apply dst_equiv_sym. rewrite orb_domain_comm. apply res_to_subset_equiv. apply dom_subset_refl.
            + apply dst_equiv_trans with (mu1:= (mu pd00) \| X1 ⊗ (mu pd2) \| X2); try assumption.
              * apply dst_equiv_sym. apply combine_res_merge_equiv; try assumption.
              * apply combine_sym.
          - apply dst_equiv_trans with (mu1:=mu pd1 ⊗ mu pd2); try assumption.
            + apply dst_equiv_preserves_combine; try assumption; try apply dst_equiv_refl. 
              * apply Valid_linear; try assumption.
              ** apply Rp_1_minus_p_bounds; assumption.
              ** rewrite R_plus_sub_eq_1. apply Rle_refl.
              * apply dst_equiv_sym. assumption.
            + apply combine_sym.  }
        split. { simpl.
          pose (X1:= (get_var_in_Pformular phi0 ∪ get_var_in_Pformular phi1)%domain).
          assert (HdomX1: is_domain_subset X1 (dom pd01) = true). { 
            apply dom_subset_orb_fst_iff. split; try assumption. 
            apply dom_subset_eq_compat_left with (X:= (dom pd00)); try assumption. }
          exists (restrict_pd pd2 (get_var_in_Pformular phi) Hvar_pd2), (restrict_pd pd01 X1 HdomX1), H3.
          split; try apply Valid_after_resX; try assumption. 
          split; try apply Valid_after_resX; try assumption. 
          split. { apply sem_satisfies_project_implies_V; try assumption. apply dom_subset_refl. }
          split. { apply sem_satisfies_project_implies_V; try assumption. apply dom_subset_orb_snd_l_r. }
          split; simpl; try apply dom_subset_refl.
          pose (X2:= get_var_in_Pformular phi). fold X2.
          apply dst_equiv_sym in Heq_sub. 
          apply dst_equiv_trans with (mu0:= (p * mu pd00 + (1 - p) * mu pd01)%dist_state ⊗ mu pd2) in Heq_sub. 
          - apply dst_equiv_trans with (mu1:= (mu pd01 ⊗ mu pd2) \| (X1 ∪ X2)%domain); try assumption.
            + apply dst_equiv_sym. rewrite orb_domain_comm. apply res_to_subset_equiv. apply dom_subset_refl.
            + apply dst_equiv_trans with (mu1:=(mu pd01) \| X1 ⊗ (mu pd2) \| X2); try apply combine_sym.
              apply dst_equiv_sym. apply combine_res_merge_equiv; try assumption.
          - apply dst_equiv_trans with (mu1:=mu pd1 ⊗ mu pd2); try apply combine_sym.
            apply dst_equiv_sym. apply dst_equiv_preserves_combine; try assumption; try apply dst_equiv_refl.
            apply Valid_linear; try assumption.
            + apply Rp_1_minus_p_bounds; assumption.
            + rewrite R_plus_sub_eq_1. apply Rle_refl. }
        simpl. 
        repeat rewrite <- sum_eq_after_res. repeat rewrite sum_probs_combine_eq_mult.
        rewrite Hsum00. rewrite Hsum01.
        split. {  
          apply dst_equiv_implies_sum_probs_eq in Heq_sub; try apply Valid_after_combine; try apply Valid_after_resX; try assumption.
          repeat rewrite <- sum_eq_after_res in Heq_sub. rewrite sum_probs_combine_eq_mult in Heq_sub.
          rewrite Heq_sub. apply Rmult_comm. }
        split. {  
          apply dst_equiv_implies_sum_probs_eq in Heq_sub; try apply Valid_after_combine; try apply Valid_after_resX; try assumption.
          repeat rewrite <- sum_eq_after_res in Heq_sub. rewrite sum_probs_combine_eq_mult in Heq_sub.
          rewrite Heq_sub. apply Rmult_comm. }
        simpl in Hdom0. simpl in Hdom1.
        apply Peq_implies_res_eq with (X:= X) in Heq_sub; try apply Valid_after_resX; try apply Valid_after_combine; try assumption.
        apply dst_equiv_trans with (mu0:= (mu pd \| X)) in Heq_sub; try apply res_to_subset_equiv.
        * apply dst_equiv_trans with (mu1:= ((mu pd1 ⊗ mu pd2) \| X)); try assumption.
          ++ apply dst_equiv_trans with (mu1:= (mu pd2 ⊗ mu pd1) \| X); try assumption.
          apply Peq_implies_res_eq; try apply Valid_after_combine; try assumption.
          apply combine_sym.
          ++
          repeat rewrite <- res_dst_to_X_mult_coef. 
          rewrite <- res_add_decom_eq. 
          apply Peq_implies_res_eq; try apply Valid_after_combine; try assumption.
          ** apply Valid_linear; try assumption; try apply Valid_after_combine; try assumption.
          *** apply Rp_1_minus_p_bounds; assumption.
          *** rewrite R_plus_sub_eq_1. apply Rle_refl.
          ** repeat rewrite <- combine_mult_l_assoc_eq.
          rewrite <- combine_add_distr_l_eq. 
          apply dst_equiv_implies_combine_compat_r; try assumption.
          apply Valid_linear; try assumption; try apply Valid_after_combine; try assumption.
          *** apply Rp_1_minus_p_bounds; assumption.
          *** rewrite R_plus_sub_eq_1. apply Rle_refl.
        * apply dom_subset_eq_compat_left with (X:= (dom pd00 ∪ dom pd2)%domain); try assumption.
        rewrite <- orb_domain_comm.
        apply dom_eq_orb_compat_left. assumption.
  - destruct Hsem' as [H |H]. 
    + destruct H as [Hp_case2 H]. destruct H. 
      destruct H as [HWFx H]. destruct H as [Heq H].
      destruct H as [Hsem0 Hsumx]. destruct Heq as [Hdom_eq Hmu_eq]. 
      inversion HWD; subst. inversion H2; subst. simpl in H3. 
      destruct (Rle_lt_dec 1 0) eqn: Hl; destruct (Rle_lt_dec 1 1) eqn: Hr.
      -- assert (Hcontra: (1 <= 0)%R) by assumption.
        apply Rle_not_lt in Hcontra. unfold not in Hcontra. 
        contradict Hcontra. apply Rlt_0_1.
      -- assert (Hcontra: (1 <= 0)%R) by assumption.
        apply Rle_not_lt in Hcontra. unfold not in Hcontra. 
        contradict Hcontra. apply Rlt_0_1.
      --
      pose (X:= ((get_var_in_Pformular phi ∪ get_var_in_Pformular phi0))%domain).
      assert (Hvar0_pdx: is_domain_subset (get_var_in_Pformular phi0) (dom x) = true). {
      apply satisfy_implies_dom_sub in Hsem0; try assumption. }
      assert (Hvar_pd2: is_domain_subset (get_var_in_Pformular phi) (dom pd2) = true). {
        apply satisfy_implies_dom_sub; try assumption. } 
      assert (HX: is_domain_subset X (dom pd) = true). { 
        unfold X. 
        apply dom_subset_trans with (l1:= (dom pd2 ∪ dom pd1)%domain); try assumption.
        apply dom_subset_orb_compat; try assumption. 
        apply dom_subset_eq_compat_left with (X:= (dom x)); try assumption. }     
      apply sem_resV_implies_pd with (V:= X) (HV:= HX); try assumption.
      * apply WD_Pplus; try apply WD_Odot; try assumption.
      * simpl. rewrite Hl. rewrite Hr. apply dom_subset_refl.
      * right. left. split; try reflexivity. 
        assert (Hvar0: is_domain_intersect (dom x) (dom pd2) = false). {
          apply dom_eq_intersect_compat_right with (l:= (dom pd2)) in Hdom_eq.
          rewrite Hdom_eq. rewrite intersect_comm. assumption.  }
        assert (Hdom0: is_domain_subset X (dom (combine_pd x pd2 Hvar0)) = true). {
          simpl. rewrite orb_domain_comm. apply dom_subset_orb_compat; try assumption. } 
        exists (restrict_pd (combine_pd x pd2 Hvar0) X Hdom0).
        split; try apply Valid_after_resX; try assumption; try apply Valid_after_combine; try assumption.
        split. { split; simpl; try apply dom_equiv_refl. 
          apply Peq_implies_res_eq with (X:= X) in Heq_sub; try apply Valid_after_resX; try apply Valid_after_combine; try assumption.
          apply dst_equiv_trans with (mu0:= (mu pd \| X)) in Heq_sub; try apply res_to_subset_equiv.
          * apply dst_equiv_sym. apply dst_equiv_sym in Hmu_eq. 
          apply dst_equiv_trans with (mu1:= ((mu pd2 ⊗ mu pd1) \| X)%dist_state); try assumption.
          apply Peq_implies_res_eq; try apply Valid_after_combine; try assumption.
          apply dst_equiv_trans with (mu1:= mu pd2 ⊗ mu x); try apply combine_sym.
          apply dst_equiv_implies_combine_compat_l; try assumption.
          * apply dom_subset_orb_compat; try assumption. 
          apply dom_subset_eq_compat_left with (X:= (dom x)); try assumption. }
        split. { simpl. 
          exists (restrict_pd pd2 (get_var_in_Pformular phi) Hvar_pd2), (restrict_pd x (get_var_in_Pformular phi0) Hvar0_pdx), H3.
          split; try apply Valid_after_resX; try assumption. 
          split; try apply Valid_after_resX; try assumption. 
          split. { apply sem_satisfies_project_implies_V; try assumption. apply dom_subset_refl. }
          split. { apply sem_satisfies_project_implies_V; try assumption. apply dom_subset_refl. }
          split; simpl; try apply dom_subset_refl.
          fold X.
          apply dst_equiv_sym in Heq_sub. 
          apply dst_equiv_trans with (mu1:= (mu x ⊗ mu pd2) \| X); try assumption.
            + apply dst_equiv_sym. apply res_to_subset_equiv. apply dom_subset_refl.
            + apply dst_equiv_trans with 
                (mu1:=(mu x) \| (get_var_in_Pformular phi0) ⊗ (mu pd2) \| (get_var_in_Pformular phi)); 
                  try apply combine_sym.
              unfold X. rewrite orb_domain_comm.
              apply dst_equiv_sym. apply combine_res_merge_equiv; try assumption. }
        simpl. 
        repeat rewrite <- sum_eq_after_res. repeat rewrite sum_probs_combine_eq_mult.
        rewrite Hsumx. 
        apply dst_equiv_implies_sum_probs_eq in Heq_sub; try apply Valid_after_combine; try apply Valid_after_resX; try assumption.
        repeat rewrite <- sum_eq_after_res in Heq_sub. rewrite sum_probs_combine_eq_mult in Heq_sub.
        rewrite Heq_sub. apply Rmult_comm. 
      -- assert (Hcontra: (1 < 1)%R) by assumption. apply Rlt_irrefl in Hcontra. contradiction.
    + destruct H as [Hp_case2 H]. destruct H. 
      destruct H as [HWFx H]. destruct H as [Heq H].
      destruct H as [Hsem0 Hsumx]. destruct Heq as [Hdom_eq Hmu_eq]. 
      inversion HWD; subst. inversion H2; subst. simpl in H3. 
      destruct (Rle_lt_dec 1 0) eqn: Hl; destruct (Rle_lt_dec 0 0) eqn: Hr.
      -- assert (Hcontra: (1 <= 0)%R) by assumption.
        apply Rle_not_lt in Hcontra. unfold not in Hcontra. 
        contradict Hcontra. apply Rlt_0_1.
      -- assert (Hcontra: (1 <= 0)%R) by assumption.
        apply Rle_not_lt in Hcontra. unfold not in Hcontra. 
        contradict Hcontra. apply Rlt_0_1.
      -- 
      pose (X:= ((get_var_in_Pformular phi ∪ get_var_in_Pformular phi1))%domain).
      assert (Hvar0_pdx: is_domain_subset (get_var_in_Pformular phi1) (dom x) = true). {
      apply satisfy_implies_dom_sub in Hsem0; try assumption. }
      assert (Hvar_pd2: is_domain_subset (get_var_in_Pformular phi) (dom pd2) = true). {
        apply satisfy_implies_dom_sub; try assumption. } 
      assert (HX: is_domain_subset X (dom pd) = true). { 
        unfold X. 
        apply dom_subset_trans with (l1:= (dom pd2 ∪ dom pd1)%domain); try assumption.
        apply dom_subset_orb_compat; try assumption. 
        apply dom_subset_eq_compat_left with (X:= (dom x)); try assumption. }     
      apply sem_resV_implies_pd with (V:= X) (HV:= HX); try assumption.
      * apply WD_Pplus; try apply WD_Odot; try assumption.
      * simpl. rewrite Hl. rewrite Hr. apply dom_subset_refl.
      * right. right. split; try reflexivity. 
        assert (Hvar0: is_domain_intersect (dom x) (dom pd2) = false). {
          apply dom_eq_intersect_compat_right with (l:= (dom pd2)) in Hdom_eq.
          rewrite Hdom_eq. rewrite intersect_comm. assumption.  }
        assert (Hdom0: is_domain_subset X (dom (combine_pd x pd2 Hvar0)) = true). {
          simpl. rewrite orb_domain_comm. apply dom_subset_orb_compat; try assumption. } 
        exists (restrict_pd (combine_pd x pd2 Hvar0) X Hdom0).
        split; try apply Valid_after_resX; try assumption; try apply Valid_after_combine; try assumption.
        split. { split; simpl; try apply dom_equiv_refl. 
          apply Peq_implies_res_eq with (X:= X) in Heq_sub; try apply Valid_after_resX; try apply Valid_after_combine; try assumption.
          apply dst_equiv_trans with (mu0:= (mu pd \| X)) in Heq_sub; try apply res_to_subset_equiv.
          * apply dst_equiv_sym. apply dst_equiv_sym in Hmu_eq. 
          apply dst_equiv_trans with (mu1:= ((mu pd2 ⊗ mu pd1) \| X)%dist_state); try assumption.
          apply Peq_implies_res_eq; try apply Valid_after_combine; try assumption.
          apply dst_equiv_trans with (mu1:= mu pd2 ⊗ mu x); try apply combine_sym.
          apply dst_equiv_implies_combine_compat_l; try assumption.
          * apply dom_subset_orb_compat; try assumption. 
          apply dom_subset_eq_compat_left with (X:= (dom x)); try assumption. }
        split. { simpl. 
          exists (restrict_pd pd2 (get_var_in_Pformular phi) Hvar_pd2), (restrict_pd x (get_var_in_Pformular phi1) Hvar0_pdx),H3.
          split; try apply Valid_after_resX; try assumption. 
          split; try apply Valid_after_resX; try assumption. 
          split. { apply sem_satisfies_project_implies_V; try assumption. apply dom_subset_refl. }
          split. { apply sem_satisfies_project_implies_V; try assumption. apply dom_subset_refl. }
          split; simpl; try apply dom_subset_refl.
          fold X.
          apply dst_equiv_sym in Heq_sub. 
          apply dst_equiv_trans with (mu1:= (mu x ⊗ mu pd2) \| X); try assumption.
            + apply dst_equiv_sym. apply res_to_subset_equiv. apply dom_subset_refl.
            + apply dst_equiv_trans with (mu1:= (mu x) \| (get_var_in_Pformular phi1) ⊗ (mu pd2) \| (get_var_in_Pformular phi));
              try apply combine_sym.
              unfold X. rewrite orb_domain_comm.
              apply dst_equiv_sym. 
            apply combine_res_merge_equiv; try assumption. }
        simpl. 
        repeat rewrite <- sum_eq_after_res. repeat rewrite sum_probs_combine_eq_mult.
        rewrite Hsumx. 
        apply dst_equiv_implies_sum_probs_eq in Heq_sub; try apply Valid_after_combine; try apply Valid_after_resX; try assumption.
        repeat rewrite <- sum_eq_after_res in Heq_sub. rewrite sum_probs_combine_eq_mult in Heq_sub.
        rewrite Heq_sub. apply Rmult_comm. 
      -- assert (Hcontra: (0 < 0)%R) by assumption. apply Rlt_irrefl in Hcontra. contradiction.
Qed.
(************************************)
Lemma OdotC: forall phi1 phi2, 
  [[phi1 ⊙ phi2]] <<->> [[phi2 ⊙ phi1]].
Proof.
  intros phi1 phi2. split.
  - unfold assert_implies. intros. destruct H1. destruct H1. destruct H1. intuition. 
    simpl. exists x0, x. 
    assert(Hvar : (dom x0 ∩∅ dom x)%domain). { rewrite intersect_comm. assumption. }
    exists Hvar. intuition. destruct H6. split; simpl in *. 
    + rewrite orb_domain_comm. assumption.
    + rewrite orb_domain_comm. 
      apply dst_equiv_trans with (mu1:= (mu x ⊗ mu x0)%dist_state); try assumption.
      apply combine_sym.
  - unfold assert_implies. intros. destruct H1. destruct H1. destruct H1. intuition. 
    simpl. exists x0, x. 
    assert(Hvar : (dom x0 ∩∅ dom x)%domain). { rewrite intersect_comm. assumption. }
    exists Hvar. intuition. destruct H6. split; simpl in *. 
    + rewrite orb_domain_comm. assumption.
    + rewrite orb_domain_comm. 
      apply dst_equiv_trans with (mu1:= (mu x ⊗ mu x0)%dist_state); try assumption.
      apply combine_sym.
Qed.
(***************************)
Lemma OdotA: forall phi1 phi2 phi3, 
  well_defined_Pf ((phi1 ⊙ phi2) ⊙ phi3) ->
  [[(phi1 ⊙ phi2) ⊙ phi3]] <<->> [[phi1 ⊙ (phi2 ⊙ phi3)]].
Proof.
  intros phi1 phi2 phi3 HWD. split.
  - unfold assert_implies. intros. 
    destruct H1 as [x H1]. destruct H1 as [x3 H1]. destruct H1 as [Hdom' H1]. intuition.
    destruct H3 as [x1 H3]. destruct H3 as [x2 H3]. destruct H3 as [Hdom H3]. intuition.
    inversion HWD; subst. inversion H12; subst. simpl in H14. 
    pose (V1:= get_var_in_Pformular phi1). pose (V2:= get_var_in_Pformular phi2). 
    pose (V3:= get_var_in_Pformular phi3).
    assert (HsubV2: (V2 ⊆ dom x2)%domain). { apply satisfy_implies_dom_sub; try assumption. }
    assert (HsubV3: (V3 ⊆ dom x3)%domain). { apply satisfy_implies_dom_sub; try assumption. }
    assert (Hinter23: (get_var_in_Pformular phi2 ∩∅ get_var_in_Pformular phi3)%domain). { 
      apply intersect_orb_fst_right in H14. assumption. }
    pose (x23:= 
    {| dom := (V2 ∪ V3)%domain;
      mu := mu (restrict_pd x2 V2 HsubV2) ⊗ mu (restrict_pd x3 V3 HsubV3);
      all_partial := PD_combine_invar_mu (restrict_pd x2 V2 HsubV2) (restrict_pd x3 V3 HsubV3) Hinter23
    |}).
    assert (HsubV1: (V1 ⊆ dom x1)%domain). { apply satisfy_implies_dom_sub; try assumption. }
    assert (Hinter: (V1 ∩∅ (V2 ∪ V3))%domain). { 
      apply intersect_orb_r_iff; try assumption.
      apply intersect_orb_fst_left in H14. assumption. }
    exists (restrict_pd x1 V1 HsubV1), x23, Hinter. intuition.
    + apply Valid_after_resX. assumption. 
    + apply Valid_after_combine; apply Valid_after_resX; intuition.
    + apply sem_satisfies_project_iff; try assumption.
    + exists (restrict_pd x2 V2 HsubV2), (restrict_pd x3 V3 HsubV3), Hinter23. intuition. 
      * apply Valid_after_resX. assumption.
      * apply Valid_after_resX. assumption.
      * apply sem_satisfies_project_iff; try assumption.
      * apply sem_satisfies_project_iff; try assumption.
      * simpl. apply relation_mu_refl.
    + simpl. apply relation_mu_trans with (pd2:= {|
          dom := (dom x ∪ dom x3)%domain;
          mu := mu x ⊗ mu x3;
          all_partial := PD_combine_invar_mu x x3 Hdom'
        |}); try repeat apply Valid_after_combine; try apply Valid_after_resX; try assumption.
      simpl. split; simpl. 
      * rewrite orb_domain_assoc. apply dom_subset_orb_compat; try assumption.
        destruct H10. simpl in H9. apply dom_subset_trans with (l1:= (dom x1 ∪ dom x2)%domain); try assumption.
        apply dom_subset_orb_compat; try assumption.
      * destruct H10. simpl in H10. 
        apply Peq_implies_res_eq with (X:= (V1 ∪ V2)%domain) in H10; try apply Valid_after_resX; try apply Valid_after_combine; try assumption.
        apply dst_equiv_trans with (mu0:= mu x \| (V1 ∪ V2)%domain) in H10; 
        try apply res_to_subset_equiv; try apply dom_subset_orb_compat; try assumption.
        apply dst_equiv_sym in H10.
        apply dst_equiv_trans with (mu0:= (mu x1 \| V1) ⊗ (mu x2 \| V2)%domain) in H10; 
        try apply combine_res_merge_equiv; try assumption.
        rewrite orb_domain_assoc. 
        apply dst_equiv_trans with (mu1:= (mu x \| (V1 ∪ V2)%domain) ⊗ (mu x3 \| V3)).
        ** apply dst_equiv_sym. apply combine_res_merge_equiv; try assumption. 
          simpl in H9. apply dom_subset_trans with (l1:= (dom x1 ∪ dom x2)%domain); try assumption.
          apply dom_subset_orb_compat; try assumption.
        ** apply dst_equiv_trans with (mu1:= (mu x1 \| V1 ⊗ mu x2 \| V2) ⊗ mu x3 \| V3). 
        -- apply dst_equiv_sym. apply dst_equiv_implies_combine_compat_r; 
          try apply Valid_after_combine; try apply Valid_after_resX; try assumption.
        -- apply dst_equiv_sym. 
          apply combine_assoc with (X0:= V1) (X1:= V2) (X2:= V3); try apply Valid_after_resX; try assumption.
          ++ apply PD_after_res with (dom:= dom x1); try assumption. destruct x1. simpl. assumption.
          ++ apply PD_after_res with (dom:= dom x2); try assumption. destruct x2. simpl. assumption.
          ++ apply PD_after_res with (dom:= dom x3); try assumption. destruct x3. simpl. assumption.
          ++ apply intersect_orb_fst_left in H14. assumption.
  - unfold assert_implies. intros. destruct H1 as [x1 H1]. destruct H1 as [x23 H1]. 
    destruct H1 as [Hdom H1]. intuition. 
    destruct H4 as [x2 H4]. destruct H4 as [x3 H4]. destruct H4 as [Hdom' H4]. intuition.
    inversion HWD; subst. inversion H12; subst. simpl in H14. 
    pose (V1:= get_var_in_Pformular phi1). pose (V2:= get_var_in_Pformular phi2). 
    pose (V3:= get_var_in_Pformular phi3).
    assert (HsubV1: (V1 ⊆ dom x1)%domain). { apply satisfy_implies_dom_sub; try assumption. }
    assert (HsubV2: (V2 ⊆ dom x2)%domain). { apply satisfy_implies_dom_sub; try assumption. }
    assert (HsubV3: (V3 ⊆ dom x3)%domain). { apply satisfy_implies_dom_sub; try assumption. }
    assert (Hinter23: (get_var_in_Pformular phi1 ∩∅ get_var_in_Pformular phi2)%domain). { 
      apply intersect_orb_fst_right in H14. assumption. }
    pose (x12:= 
    {| dom := (V1 ∪ V2)%domain;
      mu := mu (restrict_pd x1 V1 HsubV1) ⊗ mu (restrict_pd x2 V2 HsubV2);
      all_partial := PD_combine_invar_mu (restrict_pd x1 V1 HsubV1) (restrict_pd x2 V2 HsubV2) Hinter23
    |}).
    assert (Hinter: ((V1 ∪ V2) ∩∅ V3)%domain). { 
      apply intersect_orb_l_iff; try assumption.
      - apply intersect_orb_fst_left in H14. assumption.
      - apply intersect_orb_fst_right in H14. assumption. }
    exists x12, (restrict_pd x3 V3 HsubV3), Hinter. intuition.
    + apply Valid_after_combine; apply Valid_after_resX; intuition.
    + apply Valid_after_resX; intuition.
    + exists (restrict_pd x1 V1 HsubV1), (restrict_pd x2 V2 HsubV2), Hinter23. intuition. 
      * apply Valid_after_resX. assumption.
      * apply Valid_after_resX. assumption.
      * apply sem_satisfies_project_iff; try assumption.
      * apply sem_satisfies_project_iff; try assumption.
      * simpl. apply relation_mu_refl.
    + apply sem_satisfies_project_iff; try assumption.
    + simpl. apply relation_mu_trans with (pd2:= {|
    dom := (dom x1 ∪ dom x23)%domain;
    mu := mu x1 ⊗ mu x23;
    all_partial := PD_combine_invar_mu x1 x23 Hdom
  |}); try repeat apply Valid_after_combine; try apply Valid_after_resX; try assumption.
      simpl. split; simpl. 
      * rewrite <- orb_domain_assoc. apply dom_subset_orb_compat; try assumption.
        destruct H10. simpl in H9. apply dom_subset_trans with (l1:= (dom x2 ∪ dom x3)%domain); try assumption.
        apply dom_subset_orb_compat; try assumption.
      * destruct H10. simpl in H10. 
        apply Peq_implies_res_eq with (X:= (V2 ∪ V3)%domain) in H10; try apply Valid_after_resX; try apply Valid_after_combine; try assumption.
        apply dst_equiv_trans with (mu0:= mu x23 \| (V2 ∪ V3)%domain) in H10; 
        try apply res_to_subset_equiv; try apply dom_subset_orb_compat; try assumption.
        apply dst_equiv_sym in H10.
        apply dst_equiv_trans with (mu0:= (mu x2 \| V2) ⊗ (mu x3 \| V3)%domain) in H10; 
        try apply combine_res_merge_equiv; try assumption.
        rewrite <- orb_domain_assoc. 
        apply dst_equiv_trans with (mu1:= (mu x1 \| V1) ⊗ (mu x23 \| (V2 ∪ V3)%domain)).
        ** apply dst_equiv_sym. apply combine_res_merge_equiv; try assumption. 
          simpl in H9. apply dom_subset_trans with (l1:= (dom x2 ∪ dom x3)%domain); try assumption.
          apply dom_subset_orb_compat; try assumption.
        ** apply dst_equiv_trans with (mu1:= mu x1 \| V1 ⊗ (mu x2 \| V2 ⊗ mu x3 \| V3)). 
        -- apply dst_equiv_sym. apply dst_equiv_implies_combine_compat_l; 
          try apply Valid_after_combine; try apply Valid_after_resX; try assumption.
        -- apply combine_assoc with (X0:= V1) (X1:= V2) (X2:= V3); try apply Valid_after_resX; try assumption.
          ++ apply PD_after_res with (dom:= dom x1); try assumption. destruct x1. simpl. assumption.
          ++ apply PD_after_res with (dom:= dom x2); try assumption. destruct x2. simpl. assumption.
          ++ apply PD_after_res with (dom:= dom x3); try assumption. destruct x3. simpl. assumption.
          ++ apply intersect_orb_fst_left in H14. assumption.
          ++ apply intersect_orb_fst_right in H14. assumption.
Qed.
(***************************************)
Lemma OdotO phi1 phi2: 
  well_defined_Pf phi1 ->
  well_defined_Pf phi2 ->
  [[phi1 ⊙ phi2]] ->> [[phi1 ∧ phi2]].
Proof.
  unfold assert_implies in *. intros H H0 pd H1 HZ H2. 
  destruct H2. destruct H2. destruct H2.
  destruct H2. destruct H3. destruct H4. 
  destruct H5. simpl in H6. 
  apply sem_preserve_subst_pd with ( pd:= 
  {|
    dom := (dom x ∪ dom x0)%domain;
    mu := mu x ⊗ mu x0;
    all_partial := PD_combine_invar_mu x x0 x1
  |} ); try assumption. 
  - apply Valid_after_combine; assumption.
  - apply WD_Pand; assumption.
  - simpl. 
    apply satisfy_implies_dom_sub in H4; try assumption.
    apply satisfy_implies_dom_sub in H5; try assumption.
    apply dom_subset_orb_compat; assumption.
  - split. 
    + pose (p1:= sum_probs (mu x0)).
      apply sem_preserve_subst_pd with 
        (pd:= (Build_partial_dist (dom x) (p1 * (mu x))%dist_state (pd_mult_preserve_PD x p1))); try assumption. 
      * apply Valid_mult_cofe; try assumption. destruct H3. assumption.
      * simpl. apply Valid_after_combine; assumption.
      * simpl. apply satisfy_implies_dom_sub in H4; try assumption.
      * apply comb_pd_subst. assumption.
      * apply sem_mult_cofe; try assumption. 
      ** destruct H3. destruct H3. assumption.
      ** rewrite dst_sum_prob_coef_mult; try assumption.
      destruct H3. destruct H3. destruct H2. destruct H2. 
      split. 
      ++ rewrite <- Rmult_0_l with (r:= 0). apply Rmult_le_compat; try apply Rle_refl; try assumption.
      ++ rewrite <- Rmult_1_l with (r:= 1). apply Rmult_le_compat; try apply Rle_refl; try assumption.
    + pose (p1:= sum_probs (mu x)).
      apply sem_preserve_subst_pd with 
        (pd:= (Build_partial_dist (dom x0) (p1 * (mu x0))%dist_state (pd_mult_preserve_PD x0 p1))); try assumption. 
      * apply Valid_mult_cofe; try assumption. destruct H2. assumption.
      * simpl. apply Valid_after_combine; assumption.
      * simpl. apply satisfy_implies_dom_sub in H5; try assumption.
      * split; simpl. 
      ** apply dom_subset_orb_snd_l_r.
      ** apply dst_equiv_trans with (mu1:= (mu x0 ⊗ mu x) \| (dom x0)). 
      -- apply Peq_implies_res_eq; try apply Valid_after_combine; try assumption. 
      apply combine_sym. 
      -- apply res_comb_equiv; try assumption. 
      rewrite intersect_comm. assumption.
      * apply sem_mult_cofe; try assumption. 
      ** destruct H2. destruct H2. assumption.
      ** rewrite dst_sum_prob_coef_mult; try assumption.
      destruct H3. destruct H3. destruct H2. destruct H2. 
      split. 
      ++ rewrite <- Rmult_0_l with (r:= 0). apply Rmult_le_compat; try apply Rle_refl; try assumption.
      ++ rewrite <- Rmult_1_l with (r:= 1). apply Rmult_le_compat; try apply Rle_refl; try assumption.
Qed.
(***************************************)
Lemma OdotOC: forall phi1 phi2 phi3, 
  well_defined_Pf phi1 -> well_defined_Pf phi2 -> well_defined_Pf phi3 ->
  [[(phi1 ∧ phi2) ⊙ phi3]] ->> [[(phi1 ⊙ phi3) ∧ (phi2 ⊙ phi3)]].
Proof. 
  unfold assert_implies. intros. destruct H4. destruct H4. destruct H4. intuition.
  destruct H6. split.
  - exists x, x0, x1. intuition; split; try assumption.
  - exists x, x0, x1. intuition; split; try assumption.
Qed.
(***************************************)
Lemma OplusC: forall phi0 phi1, 
  [[phi0 ⊕ phi1]] <<->> [[phi1 ⊕ phi0]].
Proof.
  split. 
  - intros. unfold assert_implies in *. intros pd HV HZ Hsem.
    destruct Hsem as [Hcase1 | Hsem]. 
    + destruct Hcase1 as [p1 H]. destruct H as [p2 H].
      destruct H as [Hp1 H]. destruct H as [Hp2 H]. destruct H as [Hp_eq H].
      destruct H as [pd1 H]. destruct H as [pd2 H]. 
      destruct H as [HWF1 H]. destruct H as [HWF2 H].
      destruct H as [Hdom1 H]. destruct H as [Hdom2 H]. 
      destruct H as [Hsem0 H]. destruct H as [Hsem1 H].
      destruct H as [Hsum1 H]. destruct H as [Hsum2 Heq].
      simpl. left. exists p2, p1. intuition.
      * try rewrite Rplus_comm; try assumption.
      * exists pd2, pd1. intuition.
      apply dst_equiv_trans with (mu1:= (p1 * mu pd1 + p2 * mu pd2)%dist_state); try assumption.
      apply dst_add_comm.
    + destruct Hsem as [Hcase2| Hcase3]. 
      * destruct Hcase2 as [pd1 H].
        destruct H as [HWF1 H]. 
        destruct H as [Hpdeq1 H]. destruct H as [Hdom H].
        destruct H as [Hsem0 Hsum]. 
        simpl. right. right. exists pd1.
        intuition.
      * destruct Hcase3 as [pd2 H].
        destruct H as [HWF2 H]. 
        destruct H as [Hpdeq2 H]. destruct H as [Hdom H].
        destruct H as [Hsem0 Hsum]. 
        simpl. right. left. exists pd2.
        intuition.
  - intros. unfold assert_implies in *. intros pd HV HZ Hsem.
    destruct Hsem as [Hcase1 | Hsem]. 
    + destruct Hcase1 as [p1 H]. destruct H as [p2 H].
      destruct H as [Hp1 H]. destruct H as [Hp2 H]. destruct H as [Hp_eq H].
      destruct H as [pd1 H]. destruct H as [pd2 H]. 
      destruct H as [HWF1 H]. destruct H as [HWF2 H].
      destruct H as [Hdom1 H]. destruct H as [Hdom2 H]. 
      destruct H as [Hsem0 H]. destruct H as [Hsem1 H].
      destruct H as [Hsum1 H]. destruct H as [Hsum2 Heq].
      simpl. left. exists p2, p1. intuition.
      * try rewrite Rplus_comm; try assumption.
      * exists pd2, pd1. intuition.
      apply dst_equiv_trans with (mu1:= (p1 * mu pd1 + p2 * mu pd2)%dist_state); try assumption.
      apply dst_add_comm.
    + destruct Hsem as [Hcase2| Hcase3]. 
      * destruct Hcase2 as [pd1 H].
        destruct H as [HWF1 H]. 
        destruct H as [Hpdeq1 H]. destruct H as [Hdom H].
        destruct H as [Hsem0 Hsum]. 
        simpl. right. right. exists pd1.
        intuition.
      * destruct Hcase3 as [pd2 H].
        destruct H as [HWF2 H]. 
        destruct H as [Hpdeq2 H]. destruct H as [Hdom H].
        destruct H as [Hsem0 Hsum]. 
        simpl. right. left. exists pd2.
        intuition.
Qed.
Lemma PplusC: forall pd phi0 phi1 p (Hp: 0 <= p <= 1), 
  [[phi0 ⊕[ p ] phi1]] pd <-> [[phi1 ⊕[ (1-p)] phi0]] pd.
Proof.
  split. 
  - intros. destruct H as [Hcase1 | Hsem]. 
    + destruct Hcase1 as [Hp1 H]. 
      destruct H as [pd1 H]. destruct H as [pd2 H]. 
      destruct H as [HWF1 H]. destruct H as [HWF2 H].
      destruct H as [Hdom1 H]. destruct H as [Hdom2 H]. 
      destruct H as [Hsem0 H]. destruct H as [Hsem1 H].
      destruct H as [Hsum1 H]. destruct H as [Hsum2 Heq].
      simpl. left. 
      split. { apply Rp_lt1_minus_p_bounds with (p:= p). assumption. }
      exists pd2, pd1. intuition.
      apply dst_equiv_trans with (mu1:= (p * mu pd1 + (1 - p) * mu pd2)%dist_state); try assumption.
      assert (HP: (1 - (1 - p) = p)). { field. }
      rewrite HP. apply dst_add_comm.
    + destruct Hsem as [Hcase2| Hcase3]. 
      * destruct Hcase2 as [Hp2 H]. 
        destruct H as [pd1 H].
        destruct H as [HWF1 H]. 
        destruct H as [Hpdeq1 H]. 
        destruct H as [Hsem0 Hsum]. 
        simpl. right. right. 
        split. { rewrite Hp2. field. }
        exists pd1.
        intuition.
      * destruct Hcase3 as [Hp3 H]. 
        destruct H as [pd2 H].
        destruct H as [HWF2 H]. 
        destruct H as [Hpdeq2 H]. 
        destruct H as [Hsem0 Hsum]. 
        simpl. right. left. 
        split. { rewrite Hp3. field. }
        exists pd2.
        intuition.
  - intros. 
    destruct H as [Hcase1 | Hsem]. 
    + destruct Hcase1 as [Hp1 H]. 
      destruct H as [pd1 H]. destruct H as [pd2 H]. 
      destruct H as [HWF1 H]. destruct H as [HWF2 H].
      destruct H as [Hdom1 H]. destruct H as [Hdom2 H]. 
      destruct H as [Hsem0 H]. destruct H as [Hsem1 H].
      destruct H as [Hsum1 H]. destruct H as [Hsum2 Heq].
      simpl. left. 
      split. { apply Rp_lt1_minus_p_bounds with (p:= p). try assumption. } 
      exists pd2, pd1. intuition. 
      replace (1 - (1 - p)) with p in Heq by field.
      apply dst_equiv_trans with (mu1:= ((1-p) * mu pd1 + p * mu pd2)%dist_state); try assumption.
      apply dst_add_comm.
    + destruct Hsem as [Hcase2| Hcase3]. 
      * destruct Hcase2 as [Hp1 H]. 
        destruct H as [pd1 H].
        destruct H as [HWF1 H]. 
        destruct H as [Hpdeq1 H]. 
        destruct H as [Hsem0 Hsum]. 
        simpl. right. right. 
        split. { unfold Rminus in Hp1. rewrite <- Rplus_0_r in Hp1. 
          apply Rplus_eq_reg_l in Hp1. 
          apply Ropp_eq_0_compat in Hp1. 
          rewrite Ropp_involutive in Hp1. assumption. }
        exists pd1.
        intuition.
      * destruct Hcase3 as [Hp1 H]. 
        destruct H as [pd2 H].
        destruct H as [HWF2 H]. 
        destruct H as [Hpdeq2 H]. 
        destruct H as [Hsem0 Hsum]. 
        simpl. right. left. 
        split. { 
          apply Rplus_eq_compat_r with (r:= p) in Hp1.   
          unfold Rminus in Hp1. rewrite Rplus_assoc in Hp1. 
          rewrite Rplus_opp_l in Hp1. 
          rewrite Rplus_0_l in Hp1. rewrite Rplus_0_r in Hp1.
          symmetry. assumption. }
        exists pd2.
        intuition.
Qed.
(**************************************************)
Lemma OplusA: forall phi0 phi1 phi2, 
  well_defined_Pf (phi0 ⊕ (phi1 ⊕ phi2)) ->
  [[phi0 ⊕ (phi1 ⊕ phi2)]] <<->> [[(phi0 ⊕ phi1) ⊕ phi2]].
Proof.  
  intros phi0 phi1 phi2 HWD. 
  split. 
  - intros. unfold assert_implies in *. intros pd HV HZ Hsem.
    destruct Hsem as [Hcase1 | Hsem]. 
    + destruct Hcase1 as [p1 H]. destruct H as [p2 H].
      destruct H as [Hp1 H]. destruct H as [Hp2 H]. destruct H as [Hp_eq H].
      destruct H as [pd1 H]. destruct H as [pd2 H]. 
      destruct H as [HWF1 H]. destruct H as [HWF2 H].
      destruct H as [Hdom1 H]. destruct H as [Hdom2 H]. 
      destruct H as [Hsem0 H]. destruct H as [Hsem1 H].
      destruct H as [Hsum1 H]. destruct H as [Hsum2 Heq]. 
      destruct Hsem1 as [Hsem11 | Hsem12]. 
      * destruct Hsem11 as [p3 H]. destruct H as [p4 H]. 
        destruct H as [Hp3 H]. destruct H as [Hp4 H]. 
        destruct H as [Hp_eq' H].
        destruct H as [pd3 H]. destruct H as [pd4 H]. 
        destruct H as [HWF3 H]. destruct H as [HWF4 H].
        destruct H as [Hdom3 H]. destruct H as [Hdom4 H]. 
        destruct H as [Hsem3 H]. destruct H as [Hsem4 H].
        destruct H as [Hsum3 H]. destruct H as [Hsum4 Heq'].
        left. exists (1 - p2*p4)%R, (p2*p4)%R. 
        assert (Hp24: 0 < (p2*p4)%R < 1). {
          destruct Hp2; destruct Hp4.
          split; try apply Rmult_lt_0_compat; try assumption.
          rewrite <- Rmult_1_l. apply Rmult_gt_0_lt_compat; try assumption.
          apply Rlt_0_1. } 
        assert (Hp24_1: 0 < (1 - p2*p4)%R < 1). {
          apply Rp_lt1_minus_p_bounds with (p:= p2 * p4). assumption. } 
        intuition.
        { try rewrite Rplus_comm; try apply R_plus_sub_eq_1. }
        pose (p1':= (p1 / (1 - p2 * p4))%R).
        pose (p2':= (p2*p3 / (1 - p2 * p4))%R).
        assert (Hp1': (0 < p1')%R). { 
          unfold p1'. unfold Rdiv. apply Rmult_lt_0_compat; try assumption.
          apply Rinv_0_lt_compat. assumption. }
        assert (Hp2': (0 < p2')%R). { 
          unfold p2'. unfold Rdiv. apply Rmult_lt_0_compat.
          - apply Rmult_lt_0_compat; assumption. 
          - apply Rinv_0_lt_compat. assumption. }
        assert (Hsum12': (p1' + p2')%R = 1). { 
          unfold p1', p2'. rewrite Rplus_comm. unfold Rdiv. 
          rewrite <- Rmult_plus_distr_r.
          apply Rplus_1_minus_r in Hp_eq'.
          rewrite Hp_eq'. 
          rewrite Rmult_minus_distr_l.
          unfold Rminus. 
          rewrite Rplus_assoc. rewrite <- Rplus_comm with (r1:= p1).
          rewrite <- Rplus_assoc.
          rewrite <- Rplus_comm with (r1:= p1). rewrite Rmult_1_r.
          rewrite Hp_eq. apply Rinv_r.
          apply Rgt_not_eq. assumption. }
        apply dom_equiv_trans with (l0:= dom pd3) in Hdom2; try assumption.
        assert (Hp1'_le: (0 <= p1')%R) by (apply Rlt_le; assumption).
        assert (Hp2'_le: (0 <= p2')%R) by (apply Rlt_le; assumption).
        pose (pd0:= Build_partial_dist (dom pd)
                    (p1' * mu pd1 + p2' * mu pd3)%dist_state
                    (PD_linear p1' p2' pd1 pd3 (dom pd) Hp1'_le Hp2'_le Hdom1 Hdom2)).
        exists pd0, pd4.
        split. { simpl. apply Valid_linear_under_eq_prob; try assumption. 
          rewrite Hsum1. rewrite Hsum3. rewrite Hsum2. 
          rewrite <- Rmult_plus_distr_r. rewrite Hsum12'.
          rewrite Rmult_1_l. destruct HV. assumption. }
        split; try assumption.
        split. { simpl. apply dom_equiv_refl. }
        split. { simpl. 
          apply dom_equiv_trans with (l1:= (dom pd2)); try assumption.
          apply dom_equiv_sym.
          apply dom_equiv_trans with (l1:= (dom pd3)); try assumption.
          apply dom_equiv_sym; assumption. }
        split. { left. exists p1', p2'. intuition. 
          - apply Rplus_sub_lt_1 in Hsum12'; destruct Hsum12'; assumption. 
          - apply Rplus_sub_lt_1 in Hsum12'; destruct Hsum12'; assumption.
          - exists pd1, pd3.  intuition. 
            * simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
            rewrite Hsum3. rewrite Hsum2. rewrite Hsum1.
            rewrite <- Rmult_plus_distr_r. rewrite Hsum12'. rewrite Rmult_1_l. reflexivity.
            * simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
            rewrite Hsum3. rewrite Hsum2. rewrite Hsum1.
            rewrite <- Rmult_plus_distr_r. rewrite Hsum12'. rewrite Rmult_1_l. reflexivity.
            * simpl. apply dst_equiv_refl. }
          split; try assumption.
          split. { simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
            rewrite Hsum3. rewrite Hsum2. rewrite Hsum1.
            rewrite <- Rmult_plus_distr_r. rewrite Hsum12'. rewrite Rmult_1_l. reflexivity. }
            simpl.
          split. { rewrite Hsum4. assumption. } 
          apply dst_equiv_trans with (mu1:= (p1 * mu pd1 + p2 * mu pd2)%dist_state); try assumption.
          apply dst_equiv_trans with (mu1:= (p1 * mu pd1 + p2 * (p3 * mu pd3 + p4 * mu pd4)%dist_state)%dist_state).
          ** apply dst_add_inj_l. apply dst_mult_preserves_equiv. assumption.
          ** rewrite dst_mult_plus_distr_r_eq. rewrite dst_add_assoc_eq. 
          rewrite dst_mult_plus_distr_r_eq with (p:= (1 - p2 * p4)%R). 
          apply dst_add_preserves_equiv.
          -- repeat rewrite dst_mult_assoc_eq. unfold p1', p2'. unfold Rdiv.  
             rewrite <- Rmult_assoc. rewrite <- Rmult_assoc with (r1:= (1 - p2 * p4)%R). 
             repeat rewrite Rinv_r_simpl_m; try apply dst_equiv_refl; try apply Rgt_not_eq; assumption. 
          -- rewrite dst_mult_assoc_eq. apply dst_equiv_refl.
      * destruct Hsem12 as [H|H]. 
      ** destruct H as [pd3 H]. destruct H as [HWF3 H]. 
        destruct H as [Heq_pd H]. destruct H as [Hsub2 H]. 
        destruct H as [Hsem3 Hsum3]. 
        right. left. exists pd. intuition.
        -- apply pd_equiv_refl.
        -- apply dom_subset_eq_compat_left with (X:= dom pd2); try assumption.
        -- left. exists p1,p2. intuition.
          exists pd1, pd2. intuition. 
          apply pd_equiv_sym in Heq_pd.
          apply pd_equiv_preserves_sem with (pd0:= pd3); try assumption. 
          inversion HWD; subst. inversion H6; subst. assumption.
      ** destruct H as [pd3 H]. destruct H as [HWF3 H]. 
        destruct H as [Heq_pd H]. destruct H as [Hsub2 H]. 
        destruct H as [Hsem3 Hsum3]. 
        left. exists p1,p2. intuition.
        exists pd1, pd3. intuition. 
        -- destruct Heq_pd. apply dom_equiv_trans with (l1:= dom pd2); try assumption.
        -- right. left. exists pd1. intuition. 
        ++ apply pd_equiv_refl.
        ++ apply dom_subset_eq_compat_left with (X:= dom pd2); try assumption.
        apply dom_equiv_sym in Hdom1.
        apply dom_equiv_trans with (l1:= dom pd); try assumption.
        -- rewrite Hsum3. assumption.
        -- destruct Heq_pd. 
        apply dst_equiv_trans with (mu1:= (p1 * mu pd1 + p2 * mu pd2)%dist_state); try assumption.
        apply dst_add_inj_l. apply dst_mult_preserves_equiv. 
        apply dst_equiv_sym. assumption.
    + destruct Hsem as [Hcase2| Hcase3]. 
      * destruct Hcase2 as [pd1 H]. destruct H as [HWF1 H]. 
        destruct H as [Hpdeq1 H]. destruct H as [Hdom H].
        destruct H as [Hsem0 Hsum]. 
        right. left. exists pd1.
        intuition. 
        ** simpl in Hdom. apply dom_subset_orb_fst_iff in Hdom. destruct Hdom. assumption.  
        ** right. left. exists pd1. intuition. 
        -- apply pd_equiv_refl. 
        -- simpl in Hdom. apply dom_subset_orb_fst_iff in Hdom. destruct Hdom. 
          destruct Hpdeq1. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
          apply dom_equiv_sym. assumption.
      * destruct Hcase3 as [pd2 H].
        destruct H as [HWF2 H]. 
        destruct H as [Hpdeq2 H]. destruct H as [Hdom H].
        destruct H as [Hsem0 Hsum].   
        destruct Hsem0 as [Hsem11 | Hsem12]. 
        ** destruct Hsem11 as [p3 H]. destruct H as [p4 H]. 
          destruct H as [Hp3 H]. destruct H as [Hp4 H]. 
          destruct H as [Hp_eq' H].
          destruct H as [pd3 H]. destruct H as [pd4 H]. 
          destruct H as [HWF3 H]. destruct H as [HWF4 H].
          destruct H as [Hdom3 H]. destruct H as [Hdom4 H]. 
          destruct H as [Hsem3 H]. destruct H as [Hsem4 H].
          destruct H as [Hsum3 H]. destruct H as [Hsum4 Heq'].
          left. exists p3, p4. intuition.
          exists pd3, pd4. destruct Hpdeq2. intuition.
          -- apply dom_equiv_trans with (l1:= dom pd2); try assumption.
          -- apply dom_equiv_trans with (l1:= dom pd2); try assumption.
          -- right. right. exists pd3. intuition. 
            ++ apply pd_equiv_refl.
            ++ apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. 
            apply dom_equiv_sym. apply dom_equiv_trans with (l1:= dom pd2); try assumption.
          -- rewrite Hsum3. assumption.
          -- rewrite Hsum4. assumption.
          -- apply dst_equiv_trans with (mu1:= mu pd2); try assumption.
            apply dst_equiv_sym. assumption.
        ** destruct Hsem12 as [H|H].
          -- destruct H as [pd3 H]. destruct H as [HWF3 H]. 
            destruct H as [Hpdeq3 H]. destruct H as [Hdom3 H].
            destruct H as [Hsem3 Hsum3]. 
            right. left. exists pd3.
            intuition.
            ++ apply pd_equiv_trans with (pd1:= pd2); try assumption.
            ++ destruct Hpdeq2. apply dom_subset_eq_compat_left with (X:= dom pd2); try assumption.
            ++ right. right. exists pd3. intuition.
            +++ apply pd_equiv_refl.
            +++ apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. 
            destruct Hpdeq2. destruct Hpdeq3. 
            apply dom_equiv_sym. apply dom_equiv_trans with (l1:= dom pd2); try assumption.
            ++ rewrite Hsum3. destruct Hpdeq2. apply dst_equiv_implies_sum_probs_eq; assumption.
          -- destruct H as [pd3 H]. destruct H as [HWF3 H]. 
            destruct H as [Hpdeq3 H]. destruct H as [Hdom3 H].
            destruct H as [Hsem3 Hsum3]. right. right.
            exists pd3. intuition. 
            ++ apply pd_equiv_trans with (pd1:= pd2); try assumption.
            ++ simpl. apply dom_subset_orb_fst_iff. split; try assumption.
            destruct Hpdeq2. apply dom_subset_eq_compat_left with (X:= dom pd2); try assumption.
            ++ rewrite Hsum3. assumption.
  - intros. unfold assert_implies in *. intros pd HV HZ Hsem.
    destruct Hsem as [Hcase1 | Hsem]. 
    + destruct Hcase1 as [p1 H]. destruct H as [p2 H].
      destruct H as [Hp1 H]. destruct H as [Hp2 H]. destruct H as [Hp_eq H].
      destruct H as [pd1 H]. destruct H as [pd2 H]. 
      destruct H as [HWF1 H]. destruct H as [HWF2 H].
      destruct H as [Hdom1 H]. destruct H as [Hdom2 H]. 
      destruct H as [Hsem0 H]. destruct H as [Hsem1 H].
      destruct H as [Hsum1 H]. destruct H as [Hsum2 Heq]. 
      destruct Hsem0 as [Hsem11 | Hsem12]. 
      * destruct Hsem11 as [p3 H]. destruct H as [p4 H]. 
        destruct H as [Hp3 H]. destruct H as [Hp4 H]. 
        destruct H as [Hp_eq' H].
        destruct H as [pd3 H]. destruct H as [pd4 H]. 
        destruct H as [HWF3 H]. destruct H as [HWF4 H].
        destruct H as [Hdom3 H]. destruct H as [Hdom4 H]. 
        destruct H as [Hsem3 H]. destruct H as [Hsem4 H].
        destruct H as [Hsum3 H]. destruct H as [Hsum4 Heq'].
        left. exists (p1*p3)%R, (1 - p1*p3)%R. 
        assert (Hp24: 0 < (p1*p3)%R < 1). {
          destruct Hp1; destruct Hp3.
          split; try apply Rmult_lt_0_compat; try assumption.
          rewrite <- Rmult_1_l. apply Rmult_gt_0_lt_compat; try assumption.
          apply Rlt_0_1. } 
        assert (Hp24_1: 0 < (1 - p1*p3)%R < 1). {
          apply Rp_lt1_minus_p_bounds with (p:= p1 * p3). assumption. } 
        split; try assumption. 
        split; try assumption. 
        split. { try apply R_plus_sub_eq_1. }
        pose (p1':= (p1*p4 / (1 - p1 * p3))%R).
        pose (p2':= (p2 / (1 - p1 * p3))%R).
        intuition.
        assert (Hp1': (0 < p1')%R). { 
          unfold p1'. unfold Rdiv. apply Rmult_lt_0_compat; try assumption.
          - apply Rmult_lt_0_compat; try assumption. 
          - apply Rinv_0_lt_compat. assumption. }
        assert (Hp2': (0 < p2')%R). { 
          unfold p2'. unfold Rdiv. apply Rmult_lt_0_compat; try assumption.
          apply Rinv_0_lt_compat. assumption. }
        assert (Hsum12': (p1' + p2')%R = 1). { 
          unfold p1', p2'. rewrite Rplus_comm. unfold Rdiv. 
          rewrite <- Rmult_plus_distr_r. 
          rewrite Rplus_comm in Hp_eq'.
          apply Rplus_1_minus_r in Hp_eq'.
          rewrite Hp_eq'. 
          rewrite Rmult_minus_distr_l.
          unfold Rminus. 
          rewrite <- Rplus_assoc. rewrite Rmult_1_r.
          rewrite <- Rplus_comm with (r1:= p1).
          rewrite Hp_eq. apply Rinv_r.
          apply Rgt_not_eq. assumption. }
        assert (Hp1'_le: (0 <= p1')%R) by (apply Rlt_le; assumption).
        assert (Hp2'_le: (0 <= p2')%R) by (apply Rlt_le; assumption).
        apply dom_equiv_trans with (l0:= dom pd4) in Hdom1; try assumption.
        pose (pd0:= Build_partial_dist (dom pd)
                    (p1' * mu pd4 + p2' * mu pd2)%dist_state
                    (PD_linear p1' p2' pd4 pd2 (dom pd) Hp1'_le Hp2'_le Hdom1 Hdom2)).
        exists pd3, pd0.
        split; try assumption.
        split. { simpl. apply Valid_linear_under_eq_prob; try assumption. 
          rewrite Hsum2. rewrite Hsum4. rewrite Hsum1. 
          rewrite <- Rmult_plus_distr_r. rewrite Hsum12'.
          rewrite Rmult_1_l. destruct HV. assumption. }
        split. { simpl. 
          apply dom_equiv_trans with (l1:= (dom pd1)); try assumption.
          apply dom_equiv_sym. 
          apply dom_equiv_trans with (l1:= (dom pd4)); try assumption.
          apply dom_equiv_sym; assumption. }
        split. { simpl. apply dom_equiv_refl. } 
        split; try assumption.
        split. { left. exists p1', p2'. intuition. 
          - apply Rplus_sub_lt_1 in Hsum12'; destruct Hsum12'; assumption. 
          - apply Rplus_sub_lt_1 in Hsum12'; destruct Hsum12'; assumption.
          - exists pd4, pd2. intuition; simpl. 
            * rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
            rewrite Hsum2. rewrite Hsum4. rewrite Hsum1.
            rewrite <- Rmult_plus_distr_r. rewrite Hsum12'. rewrite Rmult_1_l. reflexivity.
            * simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
            rewrite Hsum2. rewrite Hsum4. rewrite Hsum1. 
            rewrite <- Rmult_plus_distr_r. rewrite Hsum12'. rewrite Rmult_1_l. reflexivity.
            * simpl. apply dst_equiv_refl. }
          split. { rewrite <- Hsum1. assumption. }
          split. { simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
            rewrite Hsum4. rewrite Hsum2. rewrite Hsum1.
            rewrite <- Rmult_plus_distr_r. rewrite Hsum12'. rewrite Rmult_1_l. reflexivity. }
          simpl.
          apply dst_equiv_trans with (mu1:= (p1 * mu pd1 + p2 * mu pd2)%dist_state); try assumption.
          apply dst_equiv_trans with (mu1:= (p1 * (p3 * mu pd3 + p4 * mu pd4)%dist_state + p2 * mu pd2) %dist_state).
          ** apply dst_add_inj_r. apply dst_mult_preserves_equiv. assumption.
          ** rewrite dst_mult_plus_distr_r_eq. rewrite <- dst_add_assoc_eq. 
          rewrite dst_mult_plus_distr_r_eq with (p:= (1 - p1 * p3)%R). 
          apply dst_add_preserves_equiv.
          -- rewrite dst_mult_assoc_eq. apply dst_equiv_refl.   
          -- repeat rewrite dst_mult_assoc_eq. 
          unfold p1', p2'. unfold Rdiv.
          rewrite <- Rmult_assoc. rewrite <- Rmult_assoc with (r2:= p2).  
          repeat rewrite Rinv_r_simpl_m; try apply dst_equiv_refl; try apply Rgt_not_eq; assumption. 
      * destruct Hsem12 as [H|H].
        ** destruct H as [pd3 H]. destruct H as [HWF3 H]. 
          destruct H as [Heq_pd H]. destruct H as [Hsub2 H]. 
          destruct H as [Hsem3 Hsum3].
          left. exists p1,p2. intuition.
          exists pd3, pd2. intuition.
          -- destruct Heq_pd. apply dom_equiv_trans with (l1:= dom pd1); try assumption.
          -- right. right. exists pd2. intuition.
            ++ apply pd_equiv_refl.
            ++ apply dom_subset_eq_compat_left with (X:= dom pd1); try assumption. 
              apply dom_equiv_sym in Hdom2. 
              apply dom_equiv_trans with (l1:= (dom pd)); try assumption.
          -- rewrite Hsum3. assumption.
          -- destruct Heq_pd. 
            apply dst_equiv_trans with (mu1:= (p1 * mu pd1 + p2 * mu pd2)%dist_state); try assumption.
            apply dst_add_inj_r. apply dst_mult_preserves_equiv.
            apply dst_equiv_sym. assumption.
        ** destruct H as [pd3 H]. destruct H as [HWF3 H].
          destruct H as [Heq_pd H]. destruct H as [Hsub2 H]. 
          destruct H as [Hsem3 Hsum3]. 
          right. right. 
          destruct Hp1 as [Hp1_l Hp1_r]. destruct Hp2 as [Hp2_l Hp2_r].
          assert (H1_le: (0 <= p1)%R) by (apply Rlt_le; assumption).
          assert (H2_le: (0 <= p2)%R) by (apply Rlt_le; assumption).
          pose (pd':= Build_partial_dist (dom pd)
                    (p1 * mu pd1 + p2 * mu pd2)%dist_state
                    (PD_linear p1 p2 pd1 pd2 (dom pd) H1_le H2_le Hdom1 Hdom2)).
          exists pd'. intuition.
          -- apply Valid_linear_under_eq_prob; try assumption.
             rewrite Hsum1. rewrite Hsum2. 
             rewrite <- Rmult_plus_distr_r. rewrite Hp_eq.
             rewrite Rmult_1_l. destruct HV. assumption.
          -- apply dst_equiv_sym in Heq. split; simpl; try assumption; apply dom_equiv_refl.
          -- apply dom_subset_eq_compat_left with (X:= dom pd1); try assumption.
          -- left. exists p1, p2. intuition.
            exists pd1, pd2. intuition; simpl.
            ++ apply pd_equiv_sym in Heq_pd.
            apply pd_equiv_preserves_sem with (pd0:= pd3); try assumption.
            inversion HWD; subst. inversion H2; subst. assumption.
            ++ rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
            rewrite Hsum1. rewrite Hsum2.
            rewrite <- Rmult_plus_distr_r. rewrite Hp_eq. rewrite Rmult_1_l. reflexivity.
            ++ rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
            rewrite Hsum1. rewrite Hsum2.
            rewrite <- Rmult_plus_distr_r. rewrite Hp_eq. rewrite Rmult_1_l. reflexivity.
            ++ apply dst_equiv_refl.
          -- simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
            rewrite Hsum1. rewrite Hsum2.
            rewrite <- Rmult_plus_distr_r. rewrite Hp_eq. rewrite Rmult_1_l. reflexivity.
    + destruct Hsem as [Hcase2| Hcase3]. 
      * destruct Hcase2 as [pd1 H]. destruct H as [HWF1 H].
        destruct H as [Hpdeq1 H]. destruct H as [Hdom H].
        destruct H as [Hsem0 Hsum]. destruct Hsem0 as [H | Hsem02].
        ** destruct H as [p3 H]. destruct H as [p4 H]. 
          destruct H as [Hp3 H]. destruct H as [Hp4 H]. 
          destruct H as [Hp_eq' H].
          destruct H as [pd3 H]. destruct H as [pd4 H]. 
          destruct H as [HWF3 H]. destruct H as [HWF4 H].
          destruct H as [Hdom3 H]. destruct H as [Hdom4 H]. 
          destruct H as [Hsem3 H]. destruct H as [Hsem4 H].
          destruct H as [Hsum3 H]. destruct H as [Hsum4 Heq'].
          left. exists p3, p4. intuition.
          exists pd3, pd4. destruct Hpdeq1. intuition.
          -- apply dom_equiv_trans with (l1:= dom pd1); try assumption.
          -- apply dom_equiv_trans with (l1:= dom pd1); try assumption.
          -- right. left. exists pd4. intuition. 
            ++ apply pd_equiv_refl.
            ++ apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. 
            apply dom_equiv_sym. apply dom_equiv_trans with (l1:= dom pd1); try assumption.
          -- rewrite Hsum3. assumption.
          -- rewrite Hsum4. assumption.
          -- apply dst_equiv_trans with (mu1:= mu pd1); try assumption.
            apply dst_equiv_sym. assumption.
        ** destruct Hsem02 as [H|H]. 
          -- destruct H as [pd3 H]. destruct H as [HWF3 H].
            destruct H as [Hpdeq3 H]. destruct H as [Hdom3 H].
            destruct H as [Hsem3 Hsum3].
            right. left. exists pd3. intuition.
            ++ apply pd_equiv_trans with (pd1:= pd1); try assumption.
            ++ simpl. apply dom_subset_orb_fst_iff. split; try assumption.
            destruct Hpdeq1. apply dom_subset_eq_compat_left with (X:= dom pd1); try assumption.
            ++ rewrite Hsum3. assumption.
          -- destruct H as [pd3 H]. destruct H as [HWF3 H].
            destruct H as [Hpdeq3 H]. destruct H as [Hdom3 H].
            destruct H as [Hsem3 Hsum3]. right. right. 
            exists pd3. intuition.
            ++ apply pd_equiv_trans with (pd1:= pd1); try assumption.
            ++ simpl. destruct Hpdeq1. 
            apply dom_subset_eq_compat_left with (X:= dom pd1); try assumption.
            ++ right. left. exists pd3. intuition.
            +++ apply pd_equiv_refl.
            +++ apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
            destruct Hpdeq1. destruct Hpdeq3.
            apply dom_equiv_sym.
            apply dom_equiv_trans with (l1:= dom pd1); try assumption. 
            ++ rewrite Hsum3. assumption.
      * destruct Hcase3 as [pd2 H]. destruct H as [HWF2 H].
        destruct H as [Hpdeq2 H]. destruct H as [Hdom H].
        destruct H as [Hsem0 Hsum]. 
        right. right. exists pd2. intuition.
        ** simpl in Hdom. apply dom_subset_orb_fst_iff in Hdom. destruct Hdom. assumption.
        ** right. right. exists pd2. intuition. 
          ++ apply pd_equiv_refl.
          ++ simpl in Hdom. apply dom_subset_orb_fst_iff in Hdom. destruct Hdom.
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
          apply dom_equiv_sym. destruct Hpdeq2. assumption.
Qed.
(***************************************************)
Lemma Oplus: forall phi0 phi1 p (Hp: 0 <= p <= 1), 
  (forall pd : partial_dist, 
    is_domain_subset (get_var_in_Pformular phi0) (dom pd) = true ->
    is_domain_subset (get_var_in_Pformular phi1) (dom pd) = true ->
    Valid_dist (mu pd) -> [[phi0 ⊕[ p] phi1]] pd -> [[phi0 ⊕ phi1]] pd).
Proof.
  intros phi0 phi1 p Hp. intros pd Hsub0 Hsub1 HV Hsem.
  destruct Hsem as [Hcase1 | Hsem]. 
  - destruct Hcase1 as [Hp1 H]. destruct H as [pd1 H].
    destruct H as [pd2 H]. destruct H as [HWF1 H]. destruct H as [HWF2 H].
    destruct H as [Hdom1 H]. destruct H as [Hdom2 H]. 
    destruct H as [Hsem0 H]. destruct H as [Hsem1 H].
    destruct H as [Hsum1 H]. destruct H as [Hsum2 Heq].
    simpl. left. exists p, (1-p)%R. 
    split; try assumption. 
    split. { try apply Rp_lt1_minus_p_bounds with (p:= p). assumption. }
    split; try apply R_plus_sub_eq_1.
    exists pd1, pd2. intuition.
  - destruct Hsem as [Hcase2| Hcase3]. 
    + destruct Hcase2 as [Hp2 H]. destruct H as [pd1 H].
      destruct H as [HWF1 H]. 
      destruct H as [Hpdeq1 H]. 
      destruct H as [Hsem0 Hsum]. 
      simpl. right. left. exists pd1.
      split; try assumption.
      split; try assumption. 
      split. { assumption. }
      split; try assumption.
    + destruct Hcase3 as [Hp3 H]. destruct H as [pd2 H].
      destruct H as [HWF2 H]. 
      destruct H as [Hpdeq2 H]. 
      destruct H as [Hsem0 Hsum]. 
      simpl. right. right. exists pd2.
      split; try assumption.
      split; try assumption.
      split. { assumption. }
      split; try assumption.
Qed.
(***************************************************)
Lemma OCon_Oplus: forall phi0 phi0' phi1 phi1', 
  [[phi0]] ->> [[phi0']] -> 
  [[phi1]] ->> [[phi1']] ->
  is_domain_subset (get_var_in_Pformular phi0') (get_var_in_Pformular phi0) = true ->
  is_domain_subset (get_var_in_Pformular phi1') (get_var_in_Pformular phi1) = true ->
  [[phi0 ⊕ phi1]] ->> [[phi0' ⊕ phi1']].
Proof.
  intros phi0 phi0' phi1 phi1' HP0 HP1 Hsub0 Hsub1. 
  unfold assert_implies in *. intros pd HV HZ Hsem.
  destruct Hsem as [Hcase1 | Hsem]. 
  - destruct Hcase1 as [p1 H]. destruct H as [p2 H]. 
    destruct H as [Hp1 H]. destruct H as [Hp2 H]. destruct H as [Hp_eq H].
    destruct H as [pd01 H]. destruct H as [pd02 H].
    destruct H as [HWF01 H]. destruct H as [HWF02 H]. 
    destruct H as [Hdom01 H]. destruct H as [Hdom02 H].
    destruct H as [Hsem01 H]. destruct H as [Hsem02 H].
    simpl. left. exists p1, p2.
    split; try assumption.
    split; try assumption.
    split; try assumption.
    exists pd01, pd02. 
    split; try assumption.
    split; try assumption.
    split; try assumption.
    split; try assumption.
    split. { try apply HP0; try assumption. 
      destruct H as [Hsum01 H]. destruct H as [Hsum02 Hmu]. 
      apply dst_implies_inject_Z in Hmu; intuition. 
      - apply dst_inject_Z_decom in Hmu. destruct Hmu.
        apply dst_mult_inject_Z with (p:= / p1) in H3. 
        rewrite dst_mult_assoc_eq in H3. rewrite <- Rinv_l_sym in H3. 
        + rewrite dst_mult_1_l in H3. assumption.
        + unfold not. intros. rewrite H5 in H. apply Rlt_irrefl in H. contradiction.
      - apply Valid_linear_under_eq_prob; try assumption. 
        + apply Rlt_le. assumption.
        + apply Rlt_le. assumption.
        + rewrite Hsum01, Hsum02. rewrite <- Rmult_plus_distr_r. rewrite Hp_eq. rewrite Rmult_1_l. destruct HV. assumption. }
    split. { try apply HP1; try assumption. 
      destruct H as [Hsum01 H]. destruct H as [Hsum02 Hmu]. 
      apply dst_implies_inject_Z in Hmu; intuition. 
      - apply dst_inject_Z_decom in Hmu. destruct Hmu.
        apply dst_mult_inject_Z with (p:= / p2) in H4. 
        rewrite dst_mult_assoc_eq in H4. rewrite <- Rinv_l_sym in H4. 
        + rewrite dst_mult_1_l in H4. assumption.
        + unfold not. intros. rewrite H5 in H1. apply Rlt_irrefl in H1. contradiction.
      - apply Valid_linear_under_eq_prob; try assumption. 
        + apply Rlt_le. assumption.
        + apply Rlt_le. assumption.
        + rewrite Hsum01, Hsum02. rewrite <- Rmult_plus_distr_r. rewrite Hp_eq. rewrite Rmult_1_l. destruct HV. assumption. }
    assumption.
  - destruct Hsem as [Hcase2| Hcase3].
    + destruct Hcase2 as [pd01 H]. destruct H as [HWF01 H]. 
      destruct H as [Hpdeq01 H]. 
      destruct H as [Hsub H]. 
      destruct H as [Hsem01 Hsum]. 
      simpl. right. left. exists pd01.
      split; try assumption.
      split; try assumption.
      split. { apply dom_subset_trans with (l1:= (get_var_in_Pformular phi1)); assumption. }
      split; try assumption. 
      apply HP0; try assumption. 
      destruct Hpdeq01. apply dst_equiv_sym in H0. 
      apply dst_implies_inject_Z in H0; intuition.
    + destruct Hcase3 as [pd02 H]. destruct H as [HWF02 H]. 
      destruct H as [Hpdeq02 H]. 
      destruct H as [Hsub H]. 
      destruct H as [Hsem02 Hsum]. 
      simpl. right. right. exists pd02.
      split; try assumption.
      split; try assumption.
      split. { apply dom_subset_trans with (get_var_in_Pformular phi0); assumption. }
      split; try assumption.
      apply HP1; try assumption.
      destruct Hpdeq02. apply dst_equiv_sym in H0. 
      apply dst_implies_inject_Z in H0; intuition.
Qed.

Lemma OCon_Pplus: forall p (Hp: 0 <= p <= 1) phi0 phi0' phi1 phi1', 
  [[phi0]] ->> [[phi0']] -> 
  [[phi1]] ->> [[phi1']] ->
  [[phi0 ⊕[ p ] phi1]] ->> [[phi0' ⊕[ p ] phi1']].
Proof.
  intros p Hp phi0 phi0' phi1 phi1' HP0 HP1.
  unfold assert_implies in *. intros pd HV HZ Hsem.
  destruct Hsem as [Hcase1 | Hsem]. 
  - destruct Hcase1 as [Hp1 H]. 
    destruct H as [pd01 H]. destruct H as [pd02 H].
    destruct H as [HWF01 H]. destruct H as [HWF02 H]. 
    destruct H as [Hdom01 H]. destruct H as [Hdom02 H].
    destruct H as [Hsem01 H]. destruct H as [Hsem02 H].
    destruct H as [Hsum01 H]. destruct H as [Hsum02 Heq].
    simpl. left. split; try assumption.
    exists pd01, pd02. 
    split; try assumption.
    split; try assumption.
    split; try assumption.
    split; try assumption.
    split. { try apply HP0; try assumption.
      assert (Hp_minus: 0 < 1 - p < 1). { apply Rp_lt1_minus_p_bounds in Hp1. assumption. }
      apply dst_implies_inject_Z in Heq; try assumption. 
      - apply dst_inject_Z_decom in Heq. destruct Heq.
        apply dst_mult_inject_Z with (p:= / p) in H.
        rewrite dst_mult_assoc_eq in H. rewrite <- Rinv_l_sym in H. 
        + rewrite dst_mult_1_l in H. assumption.
        + unfold not. intros. destruct Hp1. rewrite H1 in H2. apply Rlt_irrefl in H2. contradiction.
      - apply Valid_linear_under_eq_prob; try assumption. 
        + apply Rlt_le. intuition.
        + apply Rlt_le. intuition.
        + rewrite Hsum01, Hsum02. rewrite <- Rmult_plus_distr_r. rewrite R_plus_sub_eq_1. rewrite Rmult_1_l. destruct HV. assumption. }
    split. { try apply HP1; try assumption. 
      assert (Hp_minus: 0 < 1 - p < 1). { apply Rp_lt1_minus_p_bounds in Hp1. assumption. }
      apply dst_implies_inject_Z in Heq; try assumption. 
      - apply dst_inject_Z_decom in Heq. destruct Heq.
        apply dst_mult_inject_Z with (p:= / (1 -p)) in H0.
        rewrite dst_mult_assoc_eq in H0. rewrite <- Rinv_l_sym in H0. 
        + rewrite dst_mult_1_l in H0. assumption.
        + unfold not. intros. destruct Hp_minus. rewrite H1 in H2. apply Rlt_irrefl in H2. contradiction.
      - apply Valid_linear_under_eq_prob; try assumption. 
        + apply Rlt_le. intuition.
        + apply Rlt_le. intuition.
        + rewrite Hsum01, Hsum02. rewrite <- Rmult_plus_distr_r. rewrite R_plus_sub_eq_1. rewrite Rmult_1_l. destruct HV. assumption. }
    split; try assumption.
    split; try assumption.
  - destruct Hsem as [Hcase2| Hcase3].
    + destruct Hcase2 as [Hp2 H]. 
      destruct H as [pd01 H]. destruct H as [HWF01 H]. 
      destruct H as [Hpdeq01 H]. 
      destruct H as [Hsem01 Hsum]. 
      simpl. right. left. 
      split; try assumption. 
      exists pd01.
      split; try assumption.
      split; try assumption.
      split; try apply HP0; try assumption. 
      destruct Hpdeq01. apply dst_equiv_sym in H0. 
      apply dst_implies_inject_Z in H0; intuition.
    + destruct Hcase3 as [Hp3 H]. 
      destruct H as [pd02 H]. destruct H as [HWF02 H]. 
      destruct H as [Hpdeq02 H]. 
      destruct H as [Hsem02 Hsum]. 
      simpl. right. right.
      split; try assumption.
      exists pd02.
      split; try assumption.
      split; try assumption.
      split; try apply HP1; try assumption.
      destruct Hpdeq02. apply dst_equiv_sym in H0. 
      apply dst_implies_inject_Z in H0; intuition.
Qed. 
(***************************************************)
Lemma Conj_True phi: 
  well_defined_Pf phi ->
  [[phi]] <<->> [[(Pdeter (Dpred Btrue)) ∧ phi]].
Proof.
  split. { 
    unfold assert_implies in *. intros. 
    assert (HWD: well_defined_Pf ((Pdeter (Dpred Btrue)) ∧ phi)). { 
      apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred; try assumption. }
    split; try assumption. 
    split; simpl; try reflexivity. intros. split; try reflexivity. }
  unfold assert_implies in *. intros. 
  destruct H2. assumption.
Qed.

Lemma Pand_comm phi0 phi1: 
  [[phi0 ∧ phi1]] <<->> [[phi1 ∧ phi0]].
Proof.
  unfold assert_implies in *. split; intros; destruct H1; split; try assumption.
Qed.

Lemma Pand_elim_r phi0 phi1:
  [[phi0 ∧ phi1]] ->> ([[phi0]]).
Proof.
  unfold assert_implies in *. intros. destruct H1. assumption.
Qed.

Lemma Pand_elim_l phi0 phi1:
  [[phi0 ∧ phi1]] ->> ([[phi1]]).
Proof.
  unfold assert_implies in *. intros. destruct H1. assumption.
Qed.

(***************************************************)
Lemma Oplus_same: forall phi, 
  well_defined_Pf phi -> exclude_odot phi ->
  [[(phi ⊕ phi)]] ->> [[phi]].
Proof.
  intros phi HWD HEX.
  unfold assert_implies. intros pd HV HZ Hsem.
  destruct Hsem as [Hcase1 | Hsem].
  - destruct Hcase1 as [p1 H]. destruct H as [p2 H].
    destruct H as [Hp1 H]. destruct H as [Hp2 H]. destruct H as [Hp_eq H].  
    destruct H as [pd1 H]. destruct H as [pd2 H].
    destruct H as [HWF1 H]. destruct H as [HWF2 H].
    destruct H as [Hdom1 H]. destruct H as [Hdom2 H].   
    destruct H as [Hsem0 H]. destruct H as [Hsem1 H].
    destruct H as [Hsum1 H]. destruct H as [Hsum2 Heq].
    assert (Hp1_ge0: (0 <= p1)%R) by (apply Rlt_le; destruct Hp1; assumption).
    assert (Hp2_ge0: (0 <= p2)%R) by (apply Rlt_le; destruct Hp2; assumption).
    assert (Hsum2p: (0 <= sum_probs (p2 * mu pd2)%dist_state <= 1)%R). {
      apply Valid_mult_cofe with (p:= p2) in HWF2; try assumption.
      - destruct HWF2. assumption.
      - apply Rbound_loss in Hp2. assumption. }
    assert (Hsum1p: (0 <= sum_probs (p1 * mu pd1)%dist_state <= 1)%R). { 
      apply Valid_mult_cofe with (p:= p1) in HWF1; try assumption.
      - destruct HWF1. assumption.
      - apply Rbound_loss in Hp1. assumption. }
    apply sem_mult_cofe with (p:= p1) in Hsem0; 
    apply sem_mult_cofe with (p:= p2) in Hsem1; try assumption.
    apply phi_sem_add with (pd0:= {|
      dom := dom pd1;
      mu := (p1 * mu pd1)%dist_state;
      all_partial := pd_mult_preserve_PD pd1 p1 |}) 
      (pd1:= {|
      dom := dom pd2;
      mu := (p2 * mu pd2)%dist_state;
      all_partial := pd_mult_preserve_PD pd2 p2 |}); 
        try assumption; try apply Valid_mult_cofe; try assumption; simpl.
    + destruct Hp1. split; apply Rlt_le; try assumption.
    + destruct Hp2. split; apply Rlt_le; try assumption.
    + apply dst_equiv_implies_sum_probs_eq in Heq; try assumption.
      * rewrite dst_sum_prob_decom in Heq. assumption.
      * apply Rbound_loss in Hp1. apply Rbound_loss in Hp2.
      apply Valid_linear; try assumption. rewrite Hp_eq. apply Rle_refl. 
  - destruct Hsem as [Hcase2| Hcase3]. 
    * destruct Hcase2 as [pd1 H]. destruct H as [HWF1 H].
      destruct H as [Hpdeq1 H]. destruct H as [Hdom H].
      destruct H as [Hsem1 Hsum]. 
      apply pd_equiv_preserves_sem with (pd0:= pd1); try assumption. 
      apply pd_equiv_sym. assumption. 
    * destruct Hcase3 as [pd1 H]. destruct H as [HWF1 H].
      destruct H as [Hpdeq1 H]. destruct H as [Hdom H].
      destruct H as [Hsem1 Hsum]. 
      apply pd_equiv_preserves_sem with (pd0:= pd1); try assumption. 
      apply pd_equiv_sym. assumption. 
Qed.

Lemma Oplus_elim_left: forall phi0 phi1, 
  well_defined_Pf (phi0 ⊕ phi1) -> exclude_odot phi0 ->
  [[(phi0 ⊕ phi0) ⊕ phi1]] ->> [[(phi0 ⊕ phi1)]].
Proof.
  intros phi0 phi1 HWD HEX.
  unfold assert_implies. intros pd HV HZ Hsem.
  destruct Hsem as [Hcase1 | Hsem].
  - destruct Hcase1 as [p1 H]. destruct H as [p2 H].
    destruct H as [Hp1 H]. destruct H as [Hp2 H]. destruct H as [Hp_eq H].
    destruct H as [pd1 H]. destruct H as [pd2 H]. 
    destruct H as [HWF1 H]. destruct H as [HWF2 H].
    destruct H as [Hdom1 H]. destruct H as [Hdom2 H]. 
    destruct H as [Hsem0 H]. destruct H as [Hsem1 H].
    destruct H as [Hsum1 H]. destruct H as [Hsum2 Heq]. 
    apply Oplus_same in Hsem0; try assumption.
    + left. exists p1, p2. intuition.
      exists pd1, pd2. intuition; simpl.
    + inversion HWD; subst. assumption.
    + apply dst_implies_inject_Z in Heq; try assumption. 
      * apply dst_inject_Z_decom in Heq. destruct Heq.
        apply dst_mult_inject_Z with (p:= / p1) in H. 
        rewrite dst_mult_assoc_eq in H. rewrite <- Rinv_l_sym in H. 
        -- rewrite dst_mult_1_l in H. assumption.
        -- unfold not. intros. destruct Hp1 as [Hpgt0 Hplt1].
          rewrite H1 in Hpgt0. apply Rlt_irrefl in Hpgt0. contradiction.
      * apply Valid_linear; try assumption. 
        -- apply Rbound_loss. assumption.
        -- apply Rbound_loss. assumption. 
        -- rewrite Hp_eq. apply Rle_refl.
  - destruct Hsem as [Hcase2 | Hcase3].
    + destruct Hcase2 as [pd1 H]. destruct H as [HWF1 H].
      destruct H as [Hpdeq1 H]. destruct H as [Hdom H].
      destruct H as [Hsem0 Hsum].
      right. left. exists pd1. intuition. 
      apply Oplus_same; try assumption.
      * inversion HWD; subst. assumption.
      * destruct Hpdeq1. apply dst_equiv_sym in H0. apply dst_implies_inject_Z in H0; intuition.
    + destruct Hcase3 as [pd2 H]. destruct H as [HWF2 H].
      destruct H as [Hpdeq2 H]. destruct H as [Hdom H].
      destruct H as [Hsem0 Hsum]. 
      right. right. exists pd2. intuition.
      simpl in Hdom. apply dom_subset_orb_fst_iff in Hdom. 
      destruct Hdom. assumption.
Qed.

(***************************************************)
Lemma prob_convert : forall (Hp: 0 <= 1 / 2 <= 1) A B pd,
    [[A ⊕[ 1/2 ] B]] pd -> 
    [[A ⊕[ (1 - 1/2)%R ] B]] pd.
Proof.
    intros. destruct H. 
    - destruct H as [Hp_case1 H]. destruct H. destruct H.
    left. split. 
      + apply Rp_lt1_minus_p_bounds with (p:= 1 / 2). assumption.
      + exists x, x0. intuition. 
        replace (1 - 1/2)%R with (1/2)%R; try assumption. lra.
    - destruct H as [H | H]. 
      + right. left. 
      replace (1 - 1/2)%R with (1/2)%R by lra. assumption.
      + right. right. 
      replace (1 - 1/2)%R with (1/2)%R by lra. assumption.
Qed.

Lemma pre_implies_post :
  forall x n: Z, 
  let X := inject_Z x in 
  let N := inject_Z n in 
  (X < N)%Q -> ( X + 1%Q < N)%Q \/ ((X + 1)%Q == N)%Q.
Proof. 
  intros x n X N H.  
  unfold X, N in *. rewrite <- Zlt_Qlt in H.
  replace (1)%Q with (inject_Z 1); try reflexivity.
  rewrite <- inject_Z_plus. 
  rewrite <- Zlt_Qlt. rewrite inject_Z_injective.
  destruct (Z.eq_dec (x + 1) n) as [Heq | Hneq].
  - right; assumption.
  - left. assert (x + 1 <= n)%Z by lia. lia.
Qed.

Lemma Conseq_DA: forall X (N: Z) pd (HWFa: WF_aexp_with_pd (Ava X + Aco 1) pd),
  Valid_dist (mu pd) -> dst_inject_Z (mu pd) ->
  [[Pdeter (Dpred (Ava X < Aco (inject_Z N)))]] pd -> 
  [[Pdeter (Dpred (Ava X < Aco (inject_Z N))) ⊕ Pdeter (Dpred (Ava X = Aco (inject_Z N)))]]
  (DAssn_under_pd X (Ava X + Aco 1) pd HWFa).
Proof.
  intros X N pd HWFa HV HZ H.
  destruct pd as [dom mu HPD].
  induction mu as [|(s,p) mu' IH].
  - right. left. exists (DAssn_under_pd X (Ava X + Aco 1)
      {| dom := dom; mu := []; all_partial := HPD |} HWFa).
    intuition. 
    + simpl. apply pd_equiv_refl.
    + simpl. rewrite orb_domain_nil_r. apply dom_subset_orb_snd_l_r.
    + apply pf_sub_eq; try assumption. 
      * apply WD_Pdeter. apply WD_Dpred.
      * destruct H. split; try assumption. simpl. apply dom_subset_orb_snd_l_r.
  - inversion HPD; subst. inversion HWFa.
    assert (HPD0: partial_dst_Prop dom [(update s X (get X s + 1),p)]). { 
      apply PD_cons; try apply PD_nil. 
      rewrite orb_domain_nil_r in H1. 
      apply dom_equiv_trans with (l1:= (return_domain s ∪ singleton_bool_list X)%domain); try apply update_domain.
      apply dom_equiv_trans with (l1:= return_domain s); try assumption.
      apply orb_domain_elim_r; try assumption. 
      apply dom_subset_eq_compat_left with (X:= dom); try assumption.  }
    pose (pd0:= {| dom := dom; mu := [(update s X (get X s + 1),p)]; all_partial := HPD0 |}).
    assert (HWFa': WF_aexp_with_pd (Ava X + Aco 1) {| dom := dom; mu := mu'; all_partial := H4 |}). {
      unfold WF_aexp_with_pd. simpl. try assumption. }
    pose (pd1:= (DAssn_under_pd X (Ava X + Aco 1)
       {| dom := dom; mu := mu'; all_partial := H4 |} HWFa')).
    apply phi_sem_add with (pd0:= pd0) (pd1:= pd1); try assumption.
    + apply Valid_after_DA; try assumption.
    + apply Valid_dist_conj in HV. destruct HV. assumption.
    + apply Valid_after_DA; try assumption. apply Valid_dist_conj in HV. destruct HV. assumption.
    + simpl. rewrite orb_domain_nil_r in H1. apply orb_domain_elim_r; try assumption.
    + simpl. apply dom_equiv_refl.
    + simpl. apply dst_equiv_refl.
    + simpl. rewrite Rplus_0_r. f_equal.
    + apply WD_Oplus; try apply WD_Pdeter; try apply WD_Dpred.
    + simpl. split; apply I.
    + inversion HPD; subst. 
      assert (HPDs: partial_dst_Prop dom [(s, p)]). { apply PD_cons; try apply PD_nil. assumption. }
      assert (Hsem: [[Pdeter (Dpred (Ava X < Aco (inject_Z N)))]] {| dom := dom; mu := [(s, p)]; all_partial := HPDs |}). {
        destruct H as [Hdom Hsem]. split; try assumption.
        simpl in *. intros. apply orb_true_iff in H. 
        destruct H; try discriminate.
        specialize (Hsem st). apply Hsem. 
        unfold supp_mu. simpl. 
        rewrite insert_st_pair_fst_eq_insert_st.
        rewrite in_supp_insert_eq.
        apply orb_true_iff. left. assumption. }  
      destruct Hsem. simpl in H3. specialize (H3 s). destruct H3.
        * rewrite state_eq_refl. simpl. reflexivity.
        * destruct (negb (Qle_bool (inject_Z N) (get X s))) eqn: HNX; try contradiction. 
          destruct (Qcompare (inject_Z N) (get X s)) eqn: Hcomp.
        ** apply Qeq_alt in Hcomp. rewrite <- Hcomp in HNX. 
          rewrite negb_true_iff in HNX.  
          assert (Hcontra: Qle_bool (inject_Z N) (inject_Z N) = true).
            { rewrite Qle_bool_iff. apply Qle_refl. }
          rewrite HNX in Hcontra. discriminate.
        ** apply Qlt_alt in Hcomp.  
          assert (Hcontra: Qle_bool (inject_Z N) (get X s) = true).
            { rewrite Qle_bool_iff. apply Qlt_le_weak. assumption. }
          rewrite negb_true_iff in HNX. 
          rewrite HNX in Hcontra. discriminate.
        ** apply Qgt_alt in Hcomp. simpl in HZ. destruct HZ.
          apply get_inject_Z with (n:= X) in H8.
          destruct H8. rewrite H8 in Hcomp.
          apply pre_implies_post in Hcomp. destruct Hcomp. 
          -- right. left. exists pd0. intuition. 
            ++ simpl. apply Valid_dist_conj in HV. destruct HV. 
              destruct H11. simpl in H11. simpl in H13.
              split; simpl; try assumption.
            ++ apply pd_equiv_refl.
            ++ split; try assumption. intros. simpl in H11. rewrite orb_true_iff in H11. 
              destruct H11; try discriminate. 
              split; try assumption. 
            *** simpl. rewrite orb_domain_nil_r in H1.
            apply st_eq_implies_dom_equiv in H11. apply dom_equiv_sym in H11.
            apply dom_subset_eq_compat_left with (X := return_domain (update s X (get X s + 1))); try assumption.
            apply dom_subset_trans with (l1:= return_domain s); try assumption.
            apply update_subst_implies_dom_eq.
            *** simpl. rewrite H8 in HNX. 
            assert (HstX: ((get X st) == inject_Z x + 1)%Q). {
               rewrite st_eq_implies_get_eq with (st1:= (update s X (get X s + 1))%state); try assumption.
               rewrite get_update_eq. rewrite H8. reflexivity. }
            rewrite <- HstX in H10. 
            destruct (negb (Qle_bool (inject_Z N) (get X st))) eqn: HXN'; try apply I.
            rewrite negb_false_iff in HXN'. apply Qle_bool_iff in HXN'. 
            assert (Hcontra: (inject_Z N < inject_Z N)%Q). { apply Qle_lt_trans with (y:= get X st); assumption. }
            apply Qlt_irrefl in Hcontra. contradiction.
          -- right. right. exists pd0. intuition. 
            ++ simpl. apply Valid_dist_conj in HV. destruct HV. 
              destruct H11. simpl in H11. simpl in H13.
              split; simpl; try assumption.
            ++ apply pd_equiv_refl.
            ++ split; try assumption. intros. simpl in H11. rewrite orb_true_iff in H11. 
              destruct H11; try discriminate. 
              split; try assumption. 
            *** simpl. rewrite orb_domain_nil_r. 
              apply st_eq_implies_dom_equiv in H11. apply dom_equiv_sym in H11.
              apply dom_subset_eq_compat_left with (X := return_domain (update s X (get X s + 1))); try assumption.
              apply dom_subset_trans with (l1:= return_domain s); try assumption.
              apply update_subst_implies_dom_eq.
            *** simpl. 
            assert (HstX: ((get X st) == inject_Z x + 1)%Q). {
               rewrite st_eq_implies_get_eq with (st1:= (update s X (get X s + 1))%state); try assumption.
               rewrite get_update_eq. rewrite H8. reflexivity. }
            rewrite H10 in HstX. apply Qeq_bool_iff in HstX. rewrite HstX. 
            try apply I.
    + apply IH; try assumption. 
      * apply Valid_dist_conj in HV. destruct HV. assumption.
      * destruct HZ. simpl. assumption.
      * apply df_sem_conj_mu in H; try assumption. 
        apply PD_cons; try assumption. apply PD_nil.
Qed. 

Lemma Psum_implies: forall X Y m n o p, 
  [[((Ava X == Aco m) ∧ (Ava Y == Aco n)) ⊕[p] ((Ava X == Aco m) ∧ (Ava Y == Aco o))]] ->>
  [[(Ava X == Aco m) ∧ ((Ava Y == Aco n) ⊕[p] (Ava Y == Aco o))]].
Proof.
  unfold assert_implies. intros. destruct H1.
  - destruct H1. destruct H2 as [x H2]. destruct H2 as [y H2]. intuition. 
    destruct H7. destruct H8. split. 
    + assert (Hdom: (dom x == dom y)%domain). {
      apply dom_equiv_sym in H6.
      apply dom_equiv_trans with (l1:= dom pd); try assumption. }
      pose (pd_tmp:= pd_add (cofe_pd x (p)%R) (cofe_pd y (1-p))%R Hdom).
      assert (HV_tmp: Valid_dist (mu pd_tmp)). {
        simpl. apply Valid_linear_under_eq_prob; try assumption; try lra. rewrite H9. rewrite H10.
        rewrite <- Rmult_plus_distr_r. rewrite R_plus_sub_eq_1. rewrite Rmult_1_l.
        destruct H. assumption.
      }
      assert (HV_px: Valid_dist (mu (cofe_pd x (p)%R))). {
        simpl. apply Valid_mult_cofe; try assumption; try lra. }
      assert (HV_py: Valid_dist (mu (cofe_pd y (1-p)%R))). {
        simpl. apply Valid_mult_cofe; try assumption; try lra. }
      apply pd_equiv_preserves_sem with (pd0:= pd_tmp); intuition.
      * apply WD_Pdeter. apply WD_Dpred.
      * split; try assumption. simpl. apply dom_equiv_sym. assumption.
      * apply df_sem_add with (pd0:= (cofe_pd x (p)%R)) (pd1:= (cofe_pd y (1-p))%R); try assumption. 
      ** simpl. apply dom_equiv_refl.
      ** simpl. apply dom_equiv_sym. assumption.
      ** simpl. apply dst_equiv_refl.
      ** apply sem_mult_cofe with (p:= p) in H7; try assumption; try lra.
        -- apply WD_Pdeter. apply WD_Dpred.
        -- destruct HV_px. assumption.
      ** apply sem_mult_cofe with (p:= (1-p)%R) in H8; try assumption; try lra.
        -- apply WD_Pdeter. apply WD_Dpred.
        -- destruct HV_py. assumption.
    + left. split; intuition. 
      exists x, y. intuition.
  - destruct H1. 
    + destruct H1. destruct H2 as [x H2]. intuition. destruct H4. split.
      * apply pd_equiv_sym in H2. apply pd_equiv_preserves_sem with (phi:= (Ava X == Aco m)%formula) in H2; try assumption. 
        apply WD_Pdeter. apply WD_Dpred.
      * right. left. intuition. exists x. intuition.
    + destruct H1. destruct H2 as [y H2]. intuition. destruct H4. split. 
      * apply pd_equiv_sym in H2. apply pd_equiv_preserves_sem with (phi:= (Ava X == Aco m)%formula) in H2; try assumption. 
        apply WD_Pdeter. apply WD_Dpred.
      * right. right. intuition. exists y. intuition.
Qed.

Lemma evalB_X_01: forall st X m n, 
  Qeq_bool m n = false ->
  evalB_st (Ava X = Aco m) st = true -> 
  evalB_st (Ava X = Aco n) st = false.
Proof.
  intros. generalize dependent st. simpl in *. 
  induction X; intros; destruct st as [|v s'].
  - simpl in *. apply Qeq_bool_iff in H0. rewrite H0. assumption.
  - simpl in *. destruct v. 
    + apply Qeq_bool_iff in H0. rewrite H0. assumption.
    + apply Qeq_bool_iff in H0. rewrite H0. assumption.
  - simpl in *. apply Qeq_bool_iff in H0. rewrite H0. assumption.
  - simpl in *. apply IHX. assumption.
Qed.

Lemma Pdeter_implie_not: forall X m n pd, 
  Qeq_bool m n = false ->
  [[(Ava X == Aco m)]] pd -> [[(Ava X <> Aco n)]] pd.
Proof. 
  intros. destruct H0. split; try assumption. 
  intros. apply H1 in H2. destruct H2. simpl in H2. split; try assumption. 
  destruct (evalB_st (Ava X = Aco m) st) eqn: HXD; try contradiction.
  apply evalB_X_01 with (n:= n) in HXD; try lra; try assumption.
  apply evalB_Bnot_true_iff in HXD. rewrite HXD. apply I.
Qed.

Lemma Odot_conj_Pdeter: forall phi1 phi2, 
  well_defined_Pf phi1 -> well_defined_Pf phi2 ->
  [[phi1 ⊙ phi2]] ->> [[(phi1 ⊙ phi2) ∧ phi1]].
Proof. 
  unfold assert_implies. intros. split; try assumption. 
  apply OdotO in H3; intuition. destruct H3. assumption. 
Qed.

Lemma Pplus_distr_PDeter: forall phi1 phi2 p df, 
  0 < p < 1 ->
  [[(phi1 ⊕[p] phi2) ∧ (Pdeter df)]] ->> [[phi1 ∧ (Pdeter df) ⊕[p] phi2 ∧ (Pdeter df)]].
Proof. 
  unfold assert_implies. intros. destruct H2. destruct H2; try lra. destruct H2.
  destruct H4 as [x0 H']. destruct H' as [x1 H']. intuition.  
  left. split; try lra. exists x0, x1. intuition; split; try assumption.
  - apply df_add_sem_decom with (df:= df) in H15; intuition.
  - apply df_add_sem_decom with (df:= df) in H15; intuition. 
Qed.