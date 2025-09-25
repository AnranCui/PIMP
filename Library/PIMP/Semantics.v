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
Require Import Library.DistState.Partial.
Require Import Library.PIMP.Syntax.
Require Import Library.PIMP.EvalProps.

Open Scope list_scope.
Open Scope dstate_scope.

(************** Update status distribution based on commands ******************)
Fixpoint DAssn_under_dstate (mu : dist_state) (x: nat) (a: aexp) : dist_state := (*Calculation of assignment:=*)
  match mu with 
  | [] => [] (*Ensure that the probability remains unchanged after execution*)
  | (s,p) :: mu' => (update s x (evalA_st a s), p) :: DAssn_under_dstate mu' x a 
  end.

Fixpoint update_st_with_da (s : local_st) (p: R) (x: nat) (d_A: dist aexp) : dist_state := 
  match d_A with
  | [] => []
  | (a0, d0) :: lap => (update s x (evalA_st a0 s), (d0*p)%R) :: update_st_with_da s p x lap
  end.
Fixpoint RAssn_under_dstate (mu : dist_state) (x : nat) (d_A : dist aexp) : dist_state :=
  match mu with
  | [] => []
  | (s0, p0) :: mu' => update_st_with_da s0 p0 x d_A + RAssn_under_dstate mu' x d_A
  end.

Fixpoint get_b_in_mu (b: bexp) (mu: dist_state): dist_state := 
  match mu with 
  |[]=>[]
  |(s,p) :: ns => if (evalB_st b s) then (s,p) :: get_b_in_mu b ns  
                  else get_b_in_mu b ns 
  end.
Fixpoint get_notb_in_mu (b: bexp) (mu:dist_state) : dist_state := 
  match mu with 
  |[]=>[]
  |(s,p) :: ns => if negb (evalB_st b s) then (s,p) :: get_notb_in_mu b ns 
                  else get_notb_in_mu b ns 
  end.

Lemma get_b_preserves_PD : 
  forall (b : bexp) pd,
    partial_dst_Prop (dom pd) (get_b_in_mu b (mu pd)).
Proof.
  intros b pd. destruct pd. simpl.
  induction all_partial.
  - simpl. constructor.
  - simpl. destruct (evalB_st b s).
    + constructor; assumption.
    + assumption.
Qed.
Definition extract_b_pd (b : bexp) (pd : partial_dist) : partial_dist :=
  let mu' := get_b_in_mu b (mu pd) in
  {| 
    dom := dom pd; 
    mu := mu';
    all_partial := get_b_preserves_PD b pd
  |}.
Lemma get_notb_preserves_PD : 
  forall (b : bexp) pd,
    partial_dst_Prop (dom pd) (get_notb_in_mu b (mu pd)).
Proof.
  intros b pd. destruct pd. simpl.
  induction all_partial.
  - simpl. constructor.
  - simpl. destruct (evalB_st b s).
    + assumption.
    + constructor; assumption.
Qed.
Definition extract_notb_pd (b : bexp) (pd : partial_dist) : partial_dist :=
  let mu' := get_notb_in_mu b (mu pd) in
  {| 
    dom := dom pd; 
    mu := mu';
    all_partial := get_notb_preserves_PD b pd
  |}.
(****************************************************************************)

Definition WF_aexp_with_pd a pd:= 
  is_domain_subset (get_variables_in_aexp a) (dom pd) = true.
Definition WF_bexp_with_pd b pd:= 
  is_domain_subset (get_variables_in_bexp b) (dom pd) = true.

Lemma update_domain: forall s x q, 
  (orb_domain (return_domain s) (singleton_bool_list x) == return_domain (update s x q))%domain.
Proof.
  intros s x q. generalize dependent x.
  induction s as [|v s' IH]; intros.
  - simpl. induction x. 
    + simpl. apply dom_equiv_refl.
    + simpl in *. apply dom_cons_equiv_iff. split; try assumption. reflexivity. 
  - induction x.
    + simpl. rewrite orb_true_r. rewrite orb_domain_nil_r. apply dom_equiv_refl.
    + simpl. rewrite orb_false_r. apply dom_cons_equiv_iff. split; try reflexivity. apply IH.
Qed.
Lemma WF_aexp_inv: forall a s p mu dom (HPDs: partial_dst_Prop dom ((s, p) :: mu)) 
                      (HPD: partial_dst_Prop dom mu), 
  WF_aexp_with_pd a {| dom := dom; mu := (s, p) :: mu; all_partial := HPDs |} -> 
  WF_aexp_with_pd a {| dom := dom; mu := mu; all_partial := HPD |}.
Proof.
  intros a s p mu HWFa. induction mu as [|(s0,p0) mu' IHmu]; intros. 
  - unfold WF_aexp_with_pd in *. intros. simpl in *. assumption.
  - unfold WF_aexp_with_pd in *. intros. simpl in *. assumption.
Qed. 

Lemma WF_aexp_mult_coef: forall a p pd, 
  WF_aexp_with_pd a pd <-> WF_aexp_with_pd a (cofe_pd pd p).
Proof.
  split. - intros HWFa. destruct pd. unfold WF_aexp_with_pd in *. simpl in *. assumption.
  - intros HWFa. destruct pd. unfold WF_aexp_with_pd in *. simpl in *. assumption. 
Qed.
Lemma PD_DA: forall x a pd, 
  WF_aexp_with_pd a pd ->
  partial_dst_Prop (orb_domain (dom pd) (singleton_bool_list x)) (DAssn_under_dstate (mu pd) x a).
Proof.
  intros x a pd HWFa. 
  destruct pd. simpl in *. 
  induction mu as [|(s, p) mu' IHmu].
  - simpl in *. constructor.
  - simpl. inversion all_partial; subst. constructor. 
    + apply dom_equiv_trans with (l1:= (orb_domain (return_domain s) (singleton_bool_list x))). 
      * apply dom_eq_orb_compat_right. assumption.
      * apply update_domain. 
    + apply IHmu with H3. apply WF_aexp_inv with (HPD:= H3) in HWFa. assumption.
Qed.

Definition DAssn_under_pd (x : nat) (a : aexp) (pd : partial_dist) 
                  (HV: WF_aexp_with_pd a pd): partial_dist := 
  {| 
    dom := (orb_domain (dom pd) (singleton_bool_list x)); 
    mu := DAssn_under_dstate (mu pd) x a;
    all_partial := PD_DA x a pd HV
  |}.

Fixpoint WF_distaexp_with_pd (da : dist aexp) (pd : partial_dist) : Prop := 
  match da with 
  | [] => True 
  | (a, pa) :: da' => WF_aexp_with_pd a pd /\ WF_distaexp_with_pd da' pd
  end.

Lemma WF_distaexp_inv: forall s p mu dom da (HPDs: partial_dst_Prop dom ((s, p) :: mu)) 
                      (HPD: partial_dst_Prop dom mu),
  WF_distaexp_with_pd da {| dom := dom; mu := (s, p) :: mu; all_partial := HPDs |} ->
  WF_distaexp_with_pd da {| dom := dom; mu := mu; all_partial := HPD |}.
Proof.
  intros s p mu dom da HWF HPDs HPD. induction da as [|(a, pa) da' IHda].
  - simpl. constructor.
  - simpl in *. inversion HWF; subst. destruct HPD.
    split.
    + apply WF_aexp_inv with (HPD:= HPDs) in H. assumption.
    + apply IHda. assumption.
Qed.

Lemma WF_distaexp_conj: forall s p mu dom da (HPDs: partial_dst_Prop dom ((s, p) :: mu)) 
                      (Hdom: partial_dst_Prop dom [(s,p)])
                      (HPD: partial_dst_Prop dom mu),
  WF_distaexp_with_pd da {| dom := dom; mu := (s, p) :: mu; all_partial := HPDs |} ->
    WF_distaexp_with_pd da {| dom := dom; mu := [(s, p)]; all_partial := Hdom |} /\ 
      WF_distaexp_with_pd da {| dom := dom; mu := mu; all_partial := HPD |}.
Proof.
  intros s p mu dom da HPDs Hdom HPD HWF. split.
  - induction da as [|(a, pa) da' IHda].
    + simpl. constructor.
    + simpl in *. destruct HWF. split.
      * unfold WF_aexp_with_pd in *. simpl in *. assumption.
      * apply IHda. assumption.
  - apply WF_distaexp_inv with (HPD:= HPD) in HWF. assumption.
Qed.

Lemma WF_distaexp_mult_coef: forall da p pd,
  ( WF_distaexp_with_pd da pd) <-> WF_distaexp_with_pd da (cofe_pd pd p).
Proof.
  split; intros HWFa; unfold WF_distaexp_with_pd in *; induction da; try apply I;
  destruct a; destruct HWFa; split; try apply WF_aexp_mult_coef; try assumption; apply IHda; assumption.
Qed.

Lemma PD_update_da_domain: forall s p dom x da (Hdom: partial_dst_Prop dom [(s,p)]), 
  WF_distaexp_with_pd da {| dom := dom; mu := [(s, p)]; all_partial := Hdom |} ->
  partial_dst_Prop ((return_domain s) ∪ (singleton_bool_list x)) (update_st_with_da s p x da).
Proof.
  intros s p dom x da Hdom HWF. induction da as [|(a, pa) da' IHda]. 
  - simpl. apply PD_nil.
  - simpl. apply PD_cons; try assumption. 
    + apply update_domain. 
    + apply IHda. destruct HWF. assumption.
Qed.

Lemma PD_RA: forall x da pd,
  WF_distaexp_with_pd da pd ->
  partial_dst_Prop ((dom pd) ∪ (singleton_bool_list x)) (RAssn_under_dstate (mu pd) x da).
Proof. 
  intros x a pd HWFa. destruct pd. simpl in *.
  induction mu as [|(s,p) mu' IH].
  - simpl. constructor.
  - simpl. inversion all_partial; subst. 
    assert (Hdom:  partial_dst_Prop dom [(s,p)]). { constructor; try assumption. constructor. }
    apply PD_decom. split. 
    + apply Peq_dom_PD_Prop with (dom:= orb_domain (return_domain s) (singleton_bool_list x)); try assumption.
      * apply dom_eq_orb_compat_right. assumption.
      * apply WF_distaexp_conj with (Hdom:= Hdom) (HPD:= H3) in HWFa. destruct HWFa. 
        eapply PD_update_da_domain. apply H.
    + eapply IH. apply WF_distaexp_conj with (Hdom:= Hdom) (HPD:= H3) in HWFa. 
      destruct HWFa. apply H0.
Qed. 

Definition RAssn_under_pd (x : nat) (Vda : valid_dist_aexp) (pd : partial_dist) 
                  (HV : WF_distaexp_with_pd (proj1_sig Vda) pd)
                 : partial_dist :=
  {| 
    dom := (orb_domain (dom pd) (singleton_bool_list x)); 
    mu := RAssn_under_dstate (mu pd) x (proj1_sig Vda);
    all_partial := PD_RA x (proj1_sig Vda) pd HV
  |}.
  
(***************************************************************)
Fixpoint well_defined_winstr_with_pd (i: winstr) (pd: partial_dist):= 
  match i with 
  | Skip   => True
  | DAssign n aexp => WF_aexp_with_pd aexp pd
  | RAssign n Vda  => (let '(exist _ d_A _) := Vda in WF_distaexp_with_pd d_A pd)
  | Seq i1 i2      => well_defined_winstr_with_pd i1 pd 
  | If bexp i1 i2 => WF_bexp_with_pd bexp pd /\ 
                    match b_supp_classify bexp pd with 
                      | All_nil => True
                      | All_True => well_defined_winstr_with_pd i1 pd /\ 
                                    ((get_modvar_in_winstr i2) ⊆ ((dom pd) ∪ (get_modvar_in_winstr i1)))
                      | All_False => well_defined_winstr_with_pd i2 pd /\ 
                                    ((get_modvar_in_winstr i1) ⊆ ((dom pd) ∪ (get_modvar_in_winstr i2))) 
                      | Mixed => well_defined_winstr_with_pd i1 (extract_b_pd bexp pd) /\ 
                                 well_defined_winstr_with_pd i2 (extract_notb_pd bexp pd) /\
                                  (((get_modvar_in_winstr i1) == (get_modvar_in_winstr i2))%domain \/ (*New variables*)
                                    ((get_modvar_in_winstr i1) ⊆ pd.(dom) /\ (get_modvar_in_winstr i2) ⊆ pd.(dom)))
                    end 
  | While bexp i1 =>  WF_bexp_with_pd bexp pd /\ 
                    match b_supp_classify bexp pd with 
                      | All_nil => True 
                      | All_True => well_defined_winstr_with_pd i1 pd 
                      | All_False => (get_modvar_in_winstr i1) ⊆ (dom pd)
                      | Mixed => 
                        well_defined_winstr_with_pd i1 (extract_b_pd bexp pd) /\ 
                        (get_modvar_in_winstr i1) ⊆ (dom pd) 
                    end 
  end. 

Inductive NS: winstr -> partial_dist -> partial_dist -> Prop :=
  | NS_Skip   : forall pd, NS SKIP pd pd
  | NS_DAssign: forall x a pd (HWFa: WF_aexp_with_pd a pd), 
                      NS (x ::= a) pd (DAssn_under_pd x a pd HWFa)
  | NS_RAssign: forall x (Vda: valid_dist_aexp) pd 
                        (HWFa: WF_distaexp_with_pd (proj1_sig Vda) pd),
                      NS (x $= Vda) pd (RAssn_under_pd x Vda pd HWFa)
  | NS_Seq    : forall {i1 i2 pd pd1 pd2}, 
                      well_defined_winstr_with_pd i1 pd -> well_defined_winstr_with_pd i2 pd1 ->
                      NS i1 pd pd1 -> NS i2 pd1 pd2 -> NS (Seq i1 i2) pd pd2
  | NS_IF_Nil: forall {b i1 i2 pd}, 
                      WF_bexp_with_pd b pd -> b_supp_classify b pd = All_nil ->
                      well_defined_winstr_with_pd i1 pd ->  well_defined_winstr_with_pd i2 pd ->
                      (exists pd1_tmp, (pd_emp ((dom pd) ∪ (get_modvar_in_winstr i1))%domain) ≡ pd1_tmp /\ (*Ensure that NS_Skip can execute and meet the existence constraints of step_deterministic*)
                                        NS i1 pd pd1_tmp) ->
                      (exists pd2_tmp, (pd_emp ((dom pd) ∪ (get_modvar_in_winstr i2))%domain) ≡ pd2_tmp /\  
                                        NS i2 pd pd2_tmp) ->
                      NS (If b i1 i2) pd (pd_emp ((dom pd) ∪ (get_modvar_in_winstr (If b i1 i2)))%domain)
  | NS_IF_All_True: forall {b i1 i2 pd pd'}, 
                      WF_bexp_with_pd b pd -> b_supp_classify b pd = All_True ->
                      well_defined_winstr_with_pd i1 pd -> well_defined_winstr_with_pd i2 (pd_emp (dom pd)) -> 
                      ((get_modvar_in_winstr i2) ⊆ ((dom pd) ∪ (get_modvar_in_winstr i1))) ->
                      NS i1 pd pd' -> 
                      (exists pd2_tmp, (pd_emp ((dom pd) ∪ (get_modvar_in_winstr i2))%domain) ≡ pd2_tmp /\  
                                        NS i2 (pd_emp (dom pd)) pd2_tmp) ->
                      NS (If b i1 i2) pd pd'
  | NS_IF_All_False: forall {b i1 i2 pd pd'}, 
                      WF_bexp_with_pd b pd -> b_supp_classify b pd = All_False ->
                      well_defined_winstr_with_pd i1 (pd_emp (dom pd)) -> well_defined_winstr_with_pd i2 pd ->
                      ((get_modvar_in_winstr i1) ⊆ ((dom pd) ∪ (get_modvar_in_winstr i2))) ->
                      NS i2 pd pd' -> 
                      (exists pd1_tmp, (pd_emp ((dom pd) ∪ (get_modvar_in_winstr i1))%domain) ≡ pd1_tmp /\ 
                                        NS i1 (pd_emp (dom pd)) pd1_tmp) ->
                      NS (If b i1 i2) pd pd'
  | NS_IF_Mixed: forall {b i1 i2 pd pd1 pd2 pd'},
                      WF_bexp_with_pd b pd -> b_supp_classify b pd = Mixed ->
                      let pd_b := extract_b_pd b pd in
                      let pd_notb := extract_notb_pd b pd in
                        well_defined_winstr_with_pd i1 pd_b ->
                        well_defined_winstr_with_pd i2 pd_notb ->
                        (((get_modvar_in_winstr i1) == (get_modvar_in_winstr i2))%domain \/ 
                          ((get_modvar_in_winstr i1) ⊆ pd.(dom) /\ (get_modvar_in_winstr i2) ⊆ pd.(dom))) ->
                        NS i1 pd_b pd1 -> NS i2 pd_notb pd2 ->
                        mu pd' = mu pd1 + mu pd2 ->
                        (dom pd' == dom pd1)%domain ->
                        (dom pd' == dom pd2)%domain ->
                        NS (If b i1 i2) pd pd'
  | NS_While_Nil: forall {b i pd}, 
                      WF_bexp_with_pd b pd ->
                      b_supp_classify b pd = All_nil ->
                      NS (While b i) pd (pd_emp ((dom pd) ∪ (get_modvar_in_winstr (While b i)))%domain)                      
  | NS_While_All_True: forall {b i pd pd1 pd'}, 
                      WF_bexp_with_pd b pd -> b_supp_classify b pd = All_True ->
                      well_defined_winstr_with_pd i pd ->
                      well_defined_winstr_with_pd (While b i) pd1 ->
                      NS i pd pd1 -> NS (While b i) pd1 pd' ->
                      NS (While b i) pd pd'
  | NS_While_All_False: forall {b i pd}, 
                      WF_bexp_with_pd b pd -> b_supp_classify b pd = All_False ->
                      (get_modvar_in_winstr i) ⊆ (dom pd) ->
                      NS (While b i) pd pd 
  | NS_While_Mixed  :  forall {b i pd pd0 pd1 pd'},   
                      WF_bexp_with_pd b pd -> b_supp_classify b pd = Mixed ->
                      let pd_b := extract_b_pd b pd in
                      let pd_notb := extract_notb_pd b pd in
                      well_defined_winstr_with_pd i pd_b ->
                      well_defined_winstr_with_pd (While b i) pd0 ->
                      (get_modvar_in_winstr i) ⊆ (dom pd) ->
                      NS i pd_b pd0 -> NS (While b i) pd0 pd1 ->
                      mu pd' = mu pd1 + mu pd_notb -> 
                      (dom pd' == dom pd1)%domain ->
                      NS (While b i) pd pd'.

Notation "mu '=[' c ']=>' mu' " := (NS c mu mu') (at level 40).

Lemma NS_implies_WD_win: forall c pd pd', 
  NS c pd pd' -> well_defined_winstr_with_pd c pd.
Proof.
  intros c pd pd' H. 
  generalize dependent pd'. generalize dependent pd. induction c; intros.
  - simpl. apply I. 
  - inversion H; subst. simpl in *. assumption.
  - inversion H; subst. simpl in *. destruct v. simpl in *. assumption.
  - inversion H; subst. simpl in *. assumption. 
  - inversion H; subst. 
    + split; try assumption. rewrite H4. apply I.
    + split; try assumption. rewrite H4. split; try assumption.
    + split; try assumption. rewrite H4. split; try assumption.
    + split; try assumption. rewrite H4. intuition. 
  - inversion H; subst. 
    + simpl in *. split; try assumption. rewrite H5. apply I.
    + split; try assumption. rewrite H3. try assumption.
    + split; try assumption. rewrite H3. try assumption.
    + split; try assumption. rewrite H3. split; try assumption.
Qed.
(********************************)
Lemma sort_beq_after_DA: forall mu1 mu2 x a,
  beq_dst mu1 mu2 = true -> 
  DAssn_under_dstate mu1 x a == DAssn_under_dstate mu2 x a.
Proof.
  intros. 
  generalize dependent mu2. induction mu1 as [|(s1,p1) mu10 Hmu1].
  - intros. destruct mu2 as [|(s2,p2) mu20].
    + simpl in *. apply dst_equiv_refl.
    + simpl in *. discriminate H.
  - intros. destruct mu2 as [|(s2,p2) mu20].
    + simpl in H. discriminate H.
    + simpl in *. rewrite <- andb_assoc in H. apply andb_true_iff in H.
      destruct H. apply andb_true_iff in H0. destruct H0.
      rewrite dst_cons_eq_add. rewrite dst_cons_eq_add with (mu:= DAssn_under_dstate mu20 x a).
      apply dst_add_preserves_equiv.
      * apply Peq_one_st. split; try apply Req_true_implies_equal; try assumption.
      apply st_eq_implies_update_a; try assumption.
      * apply Hmu1. apply H1.
Qed.

Lemma insert_DA_Peq: forall mu s1 p1 x a, 
  DAssn_under_dstate ((s1,p1)::mu) x a == 
  DAssn_under_dstate (insert_st_pair s1 p1 mu) x a.
Proof.
  intros. induction mu as [|(s2,p2) mu1 Hmu1].
  - simpl in *. apply dst_equiv_refl.
  - simpl in *. destruct (beq_state s1 s2) eqn: Hst12.
    + simpl in *. unfold dst_equiv. intros.
      rewrite get_prob_decom with (mu:= [(update s1 x (evalA_st a s1), p1);(update s2 x (evalA_st a s2), p2)]) (mu':= DAssn_under_dstate mu1 x a).
      rewrite get_prob_decom with (mu:= [(update s2 x (evalA_st a s2), (p1+p2)%R)]) (mu':= DAssn_under_dstate mu1 x a).
      simpl. destruct (beq_state s (update s1 x (evalA_st a s1))) eqn: Hst_temp1.
      * assert (Hst_temp2: beq_state s (update s2 x (evalA_st a s2))=true). {
          eapply state_eq_trans. - apply Hst_temp1. - apply st_eq_implies_update_a. apply Hst12. }
        rewrite Hst_temp2. f_equal. rewrite Rplus_assoc. reflexivity.
      * assert (Hst_temp2: beq_state s (update s2 x (evalA_st a s2))=false). {
          assert (Htemp: beq_state (update s1 x (evalA_st a s1)) (update s2 x (evalA_st a s2)) = true) by (apply st_eq_implies_update_a; apply Hst12).
          apply state_eq_compat_left with (s:= s) in Htemp. rewrite Htemp in Hst_temp1. apply Hst_temp1. }
        rewrite Hst_temp2. rewrite Rplus_0_l. reflexivity.
    + destruct (ble_state s1 s2) eqn: Hcomp12.
      * simpl in *. apply dst_equiv_refl.
      * simpl in *. unfold dst_equiv in *. intros.
        specialize (Hmu1 s).
        rewrite get_prob_decom with (mu:= [(update s2 x (evalA_st a s2), p2)]) (mu':= DAssn_under_dstate (insert_st_pair s1 p1 mu1) x a).
        rewrite <- Hmu1.
        rewrite get_prob_decom with (mu:= [(update s1 x (evalA_st a s1), p1)]) (mu':= DAssn_under_dstate mu1 x a).
        rewrite get_prob_decom with (mu:= [(update s1 x (evalA_st a s1), p1);(update s2 x (evalA_st a s2), p2)]) (mu':= DAssn_under_dstate mu1 x a).
        rewrite get_prob_decom with (mu:= [(update s1 x (evalA_st a s1), p1)]) (mu':= [(update s2 x (evalA_st a s2), p2)]).
        rewrite <- Rplus_assoc. f_equal.
        apply Rplus_comm. 
Qed.
(**********************************)
Lemma DAss_add_dec_eq: forall x a mu0 mu1, 
  (DAssn_under_dstate (mu0 + mu1) x a) = 
    (DAssn_under_dstate mu0 x a + DAssn_under_dstate mu1 x a).
Proof.
  intros. generalize dependent mu1. 
  induction mu0 as [|(s0,p0) mu0'].
  - intros. simpl. reflexivity.
  - intros. simpl. f_equal. apply IHmu0'. 
Qed.

Theorem DAss_equiv_mult : forall mu p X a, 
  DAssn_under_dstate (p * mu) X a == p * DAssn_under_dstate mu X a.
Proof.
  intros.
  induction mu as [|(s,q) mu' Hmu].
  - simpl. apply dst_equiv_refl.
  - simpl. destruct (Req_EM_T p 0) eqn: Hp.
    + simpl. apply dst_equiv_refl.
    + unfold dst_equiv in Hmu. unfold dst_equiv; intro.
    rewrite get_prob_decom with (mu:= [(update s X (evalA_st a s), (p * q)%R)]) (mu':= DAssn_under_dstate (p * mu')%dist_state X a). 
    rewrite get_prob_decom with (mu:= [(update s X (evalA_st a s), (p * q)%R)]) (mu':= (p * DAssn_under_dstate mu' X a)). 
    f_equal. apply Hmu.
Qed.

Theorem DAss_eq_mult : forall mu p X a, 
  DAssn_under_dstate (p * mu) X a = p * DAssn_under_dstate mu X a.
Proof.
  intros. 
  induction mu as [|(s,q) mu' Hmu]; simpl.
  - reflexivity.
  - destruct (Req_EM_T p 0) eqn: Hp; simpl.
    + reflexivity.
    + rewrite Hmu. reflexivity.
Qed.

Theorem DAss_equiv_under_addAndmult: forall p0 p1 mu0 mu1 X a, 
  DAssn_under_dstate (p0 * mu0 + p1 * mu1) X a == p0 * (DAssn_under_dstate mu0 X a) + p1 * (DAssn_under_dstate mu1 X a) .
Proof.
  intros p0 p1 mu0 mu1 X a.
  generalize dependent mu1. 
  induction mu0 as [|(s,q) mu0' Hmu0].
  - simpl. intro. apply DAss_equiv_mult.
  - intros. simpl. destruct (Req_EM_T p0 0) eqn: Hp0; simpl.
    + apply DAss_equiv_mult.
    + unfold dst_equiv; intros.
    rewrite get_prob_decom with (mu:= [(update s X (evalA_st a s), (p0 * q)%R)]) (mu':= DAssn_under_dstate (p0 * mu0' + p1 * mu1)%dist_state X a). 
    rewrite get_prob_decom with (mu:= [(update s X (evalA_st a s), (p0 * q)%R)]) (mu':= (p0 * DAssn_under_dstate mu0' X a + p1 * DAssn_under_dstate mu1 X a)). 
    f_equal. unfold dst_equiv in Hmu0. apply Hmu0.
Qed.

Theorem DAss_eq_under_addAndmult: forall p0 p1 mu0 mu1 X a, 
  DAssn_under_dstate (p0 * mu0 + p1 * mu1) X a = p0 * (DAssn_under_dstate mu0 X a) + p1 * (DAssn_under_dstate mu1 X a) .
Proof.
  intros p0 p1 mu0 mu1 X a.
  generalize dependent mu1. 
  induction mu0 as [|(s,q) mu0' Hmu0].
  - intro. simpl. apply DAss_eq_mult.
  - intro. simpl. destruct (Req_EM_T p0 0) eqn: Hp0; simpl.
    + apply DAss_eq_mult.
    + apply app_inv_head_iff with (l:= [(update s X (evalA_st a s), (p0 * q)%R)]). apply Hmu0.
Qed. 
Lemma DA_preserve_sum_prob : forall mu a x, sum_probs (DAssn_under_dstate mu x a)%dist_state = sum_probs mu.
Proof.
  intros. induction mu as [|(s,q) mu' Hmu].
  - simpl. reflexivity.
  - simpl. rewrite Hmu. reflexivity.
Qed.
(*****************************************************************************************************)
Lemma RA_nil_dst: forall da x, RAssn_under_dstate [] x da = [].
Proof.
  intros. induction da as [|(a,pa) d_A' Hda].
  - simpl. reflexivity.
  - simpl. apply Hda. 
Qed.
Lemma RA_nil_da: forall da x, RAssn_under_dstate da x [] = [].
Proof.
  intros. induction da as [|(a,pa) d_A' Hda].
  - simpl. reflexivity.
  - simpl. apply Hda. 
Qed.

Lemma RAss_add_dec_eq: forall x da mu0 mu1, (RAssn_under_dstate (mu0 + mu1) x da) = 
  (RAssn_under_dstate mu0 x da + RAssn_under_dstate mu1 x da).
Proof.
  intros. generalize dependent mu1. 
  induction mu0 as [|(s0,p0) mu0'].
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite <- dst_add_assoc_eq. f_equal. apply IHmu0'. 
Qed.

Lemma update_st_RAssn_eq: forall s p q X da,
  p <> 0%R ->
  update_st_with_da s (p * q) X da = p * update_st_with_da s q X da .
Proof.
  intros. induction da as [|(a,pa) da'].
  - simpl. reflexivity.
  - simpl. destruct (Req_dec_T p 0) eqn: Hp.
    + unfold not in H. rewrite e in H. contradiction.
    + assert (Heq: (pa * (p * q))%R = (p * (pa * q))%R). { 
      rewrite Rmult_comm. rewrite Rmult_assoc. f_equal. apply Rmult_comm. }
    rewrite Heq. f_equal.
    apply IHda'.
Qed.

Theorem RAss_eq_mult : forall mu p X da, 
  RAssn_under_dstate (p * mu) X da = p * RAssn_under_dstate mu X da.
Proof.
  intros.
  induction mu as [|(s,q) mu' Hmu]; simpl.
  - reflexivity.
  - intros. destruct (Req_EM_T p 0) eqn: Hp; simpl.
    + rewrite e. rewrite dst_mult_0_l. reflexivity.
    + rewrite dst_mult_plus_distr_r_eq. rewrite Hmu. f_equal.
      destruct da as [|(a0, pa) da'].
      * simpl. reflexivity.
      * simpl in *. rewrite Hp. rewrite update_st_RAssn_eq; try assumption.
      f_equal. assert (Heq: (pa * (p * q))%R = (p * (pa * q))%R). { 
        rewrite Rmult_comm. rewrite Rmult_assoc. f_equal. apply Rmult_comm. }
      rewrite Heq. f_equal.
Qed.

Lemma RAss_equiv_under_addAndmult: forall p0 p1 d_A mu0 mu1 X ,
  RAssn_under_dstate (p0 * mu0 + p1 * mu1) X d_A = 
  p0 * (RAssn_under_dstate mu0 X d_A) + p1 * (RAssn_under_dstate mu1 X d_A) .
Proof.
  intros. 
  generalize dependent mu1. generalize dependent d_A.
  induction mu0 as [|(s0,r0) mu0'].
  - intros. simpl. apply RAss_eq_mult.
  - intros. simpl. destruct (Req_EM_T p0 0) eqn: Hp; simpl.
    + rewrite e. rewrite dst_mult_0_l. simpl. apply RAss_eq_mult.
    + rewrite dst_mult_plus_distr_r_eq. rewrite <- dst_add_assoc_eq. 
    rewrite update_st_RAssn_eq; try assumption.
    f_equal. apply IHmu0'. 
Qed.

Lemma sum_eq_update: forall s p x d_A, 
  sum_probs (update_st_with_da s p x d_A) = (p * sum_probs d_A)%R.
Proof.
  intros.
  induction d_A as [|(a0,p0) d' IHd].
  - simpl. rewrite Rmult_0_r. reflexivity.
  - simpl. rewrite Rmult_plus_distr_l. rewrite Rmult_comm with (r1:= p0).
  f_equal. apply IHd.
Qed.
Lemma sum_probs_RA_eq_DA_cofe: forall mu x d_A, 
  sum_probs (RAssn_under_dstate mu x d_A) = ((sum_probs d_A) * (sum_probs mu))%R.
Proof.
  intros. generalize dependent d_A. induction mu as [|(s0,p0) mu' IH].
  - simpl. intro. rewrite Rmult_0_r. reflexivity.
  - simpl. intros. rewrite dst_sum_prob_decom. rewrite Rmult_plus_distr_l.
  rewrite Rmult_comm with (r2:= p0). f_equal. 
    + apply sum_eq_update.
    + apply IH. 
Qed.

Lemma sum_ge0_mult_p: forall {A: Type} p mu, 
  (0 <= @sum_probs A mu)%R -> (0 < p)%R -> (0 <= p * @sum_probs A mu)%R.
Proof.
  intros. apply Rmult_le_pos; try assumption. apply Rlt_le. assumption. 
Qed.

Lemma sum_ge0_RA: forall mu d_A x,
  Valid_dist d_A -> (0 <= sum_probs mu)%R -> 
  (0 <= sum_probs (RAssn_under_dstate mu x d_A))%R.
Proof.
  intros. rewrite sum_probs_RA_eq_DA_cofe. 
  destruct H. destruct H. apply Rmult_le_pos; try assumption.
Qed.
Lemma sum_le_RA: forall x mu d_A,
  Valid_dist d_A ->
  (0 <= sum_probs mu)%R ->
  (sum_probs (RAssn_under_dstate mu x d_A) <= sum_probs mu)%R.
Proof.
  intros. rewrite sum_probs_RA_eq_DA_cofe. destruct H. destruct H. 
  rewrite <- Rmult_1_l with (r:= (sum_probs mu)) at 2.
  apply Rmult_le_compat_r ; try assumption.
Qed.

Lemma sum_le_after_RA: forall x mu d_A,
  (0 <= sum_probs mu)%R -> positive_probs mu ->
  Valid_dist d_A ->
  (sum_probs (RAssn_under_dstate mu x d_A) <= sum_probs mu)%R.
Proof.
  intros. generalize dependent d_A.
  induction mu as [|(s,p) mu' Hmu].
  - simpl. intros. apply Rle_refl.
  - intros. simpl.
  rewrite dst_sum_prob_decom. rewrite sum_eq_update; try assumption.
  apply Rplus_le_compat.
    * rewrite <- Rmult_1_r with (r:= p) at 2. 
      simpl in H. destruct H0. unfold prob_is_positive in H0. destruct H0.
      apply Rmult_le_compat ; try assumption.
      ** apply Rlt_le. assumption.
      ** apply positive_sum_ge_0. 
      destruct H1. assumption.
      ** apply Rle_refl.
      ** destruct H1. destruct H1. assumption.
    * destruct H0. apply Hmu; try assumption. 
      apply positive_sum_ge_0. assumption.
Qed.
Lemma pos_onest_after_RA: forall x s p d_A,
  prob_is_positive p -> Valid_dist d_A ->
  positive_probs (update_st_with_da s p x d_A).
Proof.
  intros. induction d_A as [|(a0,pa) d' IHd].
  - simpl. apply I.
  - simpl. split.
    + destruct H. destruct H0. destruct H2. destruct H2. split.
      * apply Rmult_lt_0_compat; try assumption.
      * rewrite <- Rmult_1_l with (r:= 1%R). apply Rmult_le_compat; try assumption.
      ** apply Rlt_le; try assumption.
      ** apply Rlt_le. assumption.
    + apply IHd. apply Valid_dist_inv in H0. assumption.
Qed.
Lemma pos_after_RA: forall x mu d_A,
  positive_probs mu -> Valid_dist d_A -> 
  positive_probs (RAssn_under_dstate mu x d_A).
Proof.
  intros. generalize dependent d_A.
  induction mu as [|(s,p) mu' Hmu].
  - simpl. intros. apply I.
  - intros. simpl. apply dst_positive_decom. split.
    + destruct H. apply pos_onest_after_RA; assumption.
    + destruct H. apply Hmu; try assumption. 
Qed.

Open Scope R_scope.
Lemma update_st_sum_eq: forall s p x (da: dist aexp), 
  sum_probs (update_st_with_da s p x da) = (sum_probs da) * p.
Proof.
  intros. induction da as [|(a0,p0) da' IH].
  - simpl. rewrite Rmult_0_l. reflexivity.
  - simpl. rewrite IH. rewrite <- Rmult_plus_distr_r. reflexivity.
Qed.
Lemma RA_preserve_sum_prob : forall mu da x, 
  sum_probs da = 1 ->
  sum_probs (RAssn_under_dstate mu x da)%dist_state = sum_probs mu.
Proof.
  intros. induction mu as [|(s,q) mu' Hmu].
  - simpl. reflexivity.
  - simpl. rewrite dst_sum_prob_decom. rewrite Hmu. f_equal. 
  rewrite update_st_sum_eq. rewrite H. rewrite Rmult_1_l. reflexivity.
Qed.
Lemma Valid_after_DA: forall mu x a,
  Valid_dist mu -> Valid_dist (DAssn_under_dstate mu x a).
Proof.
  intros mu x a Hvalid. inversion Hvalid. 
  induction mu as [|(s,p) mu' IH].
  - simpl. apply Valid_dist_nil.
  - unfold Valid_dist. simpl in *. 
    destruct H0 as [Hp Hpos]. split.
    + assert (Hsum: sum_probs mu' = sum_probs (DAssn_under_dstate mu' x a)). { 
        symmetry. apply DA_preserve_sum_prob. }
      rewrite <- Hsum. apply H.
    + split; try (assumption).
      apply Valid_dist_inv in Hvalid. specialize (IH Hvalid).
      destruct Hvalid as [Hsum' Hpos']. specialize (IH Hsum' Hpos').
      inversion IH. apply IH.
Qed.

Lemma valid_mu_sum_le_after_RA: forall x mu d_A,
  Valid_dist d_A ->
  Valid_dist mu ->
  (sum_probs (RAssn_under_dstate mu x d_A) <= sum_probs mu)%R.
Proof.
  intros. generalize dependent d_A.
  induction mu as [|(s,p) mu' Hmu].
  - simpl. intros. apply Rle_refl.
  - intros. simpl.
  apply Valid_dist_conj in H0. destruct H0. destruct H0. destruct H0. simpl in H0. rewrite Rplus_0_r in H0.
  destruct H2. unfold prob_is_positive in H2.
  rewrite dst_sum_prob_decom. rewrite sum_eq_update; try assumption.
  apply Rplus_le_compat.
    * rewrite <- Rmult_1_r with (r:= p) at 2. destruct H. destruct H.
      apply Rmult_le_compat ; try assumption.
      apply Rle_refl.
    * apply Hmu; try assumption. 
Qed.
Lemma Valid_RA_one_st: forall s0 p0 da x, 
  Valid_dist [(s0, p0)] -> Valid_dist da -> 
  positive_probs (update_st_with_da s0 p0 x da).
Proof.
  intros. induction da as [|(a0,r0) da' IH].
  - simpl. apply I.
  - simpl. apply Valid_dist_conj in H0. destruct H0. split.
    + destruct H. unfold positive_probs in H2. destruct H2. 
    unfold prob_is_positive in H2. destruct H2.
    destruct H0. unfold positive_probs in H5. destruct H5.
    unfold prob_is_positive in H5. destruct H5. 
    unfold prob_is_positive. split.
      * apply Rmult_lt_0_compat; try assumption.
      * rewrite <- Rmult_1_r. apply Rmult_le_compat; 
          try assumption; [apply Rlt_le; assumption|apply Rlt_le; assumption].
    + apply IH. assumption.  
Qed.
Lemma Valid_after_RA: forall x mu d_A,
  Valid_dist d_A -> Valid_dist mu ->
  Valid_dist (RAssn_under_dstate mu x d_A).
Proof.
  intros x mu da Hvalid_da Hvalid_mu.
  unfold Valid_dist. split.
  - split. 
    + rewrite sum_probs_RA_eq_DA_cofe. destruct Hvalid_da. destruct H. 
    destruct Hvalid_mu. destruct H2. apply Rmult_le_pos; assumption.
    + apply Rle_trans with (r2:= sum_probs mu). { apply valid_mu_sum_le_after_RA; try assumption. }
    destruct Hvalid_mu as [Hsum_mu Hpos_mu]. destruct Hsum_mu. assumption.
  - induction mu as [|(s0,p0) mu' IH].
    + simpl. apply I.
    + simpl. apply Valid_dist_conj in Hvalid_mu. destruct Hvalid_mu. 
      apply dst_positive_decom. split.
      * apply Valid_RA_one_st; assumption.
      * apply IH. assumption.
Qed. 


Lemma mu_Sorted_DA_Peq: forall mu x a, 
  DAssn_under_dstate mu x a == DAssn_under_dstate (sort_dst mu) x a.
Proof. 
  intros. induction mu as [|(s1,p1) mu1 Hmu1]; simpl in *.
  - apply dst_equiv_refl.
  - assert (Htemp: DAssn_under_dstate ((s1,p1) :: (sort_dst mu1)) x a == 
              DAssn_under_dstate (insert_st_pair s1 p1 (sort_dst mu1)) x a) 
                by (apply insert_DA_Peq; assumption).
    apply dst_equiv_trans with (mu1:= DAssn_under_dstate ((s1, p1) :: sort_dst mu1) x a).
    + simpl. unfold dst_equiv. intros. 
      rewrite get_prob_decom with (mu:= [(update s1 x (evalA_st a s1), p1)]) 
                                  (mu':= DAssn_under_dstate mu1 x a).
      rewrite get_prob_decom with (mu:= [(update s1 x (evalA_st a s1), p1)]) 
                                  (mu':= DAssn_under_dstate (sort_dst mu1) x a).
      f_equal. unfold dst_equiv in Hmu1. 
      apply Hmu1; try assumption; apply NS_DAssign.
    + assumption.
Qed.

Theorem DA_step_deter: forall mu0 mu1 n a, 
  Valid_dist mu0 -> Valid_dist mu1 -> mu0 == mu1 ->
  DAssn_under_dstate mu0 n a == DAssn_under_dstate mu1 n a.
Proof. 
  intros mu0 mu1 x a Hvalid1 Hvalid2 Heq_mu.
  assert (Hsorted1: mu0 == sort_dst mu0). { apply dst_equiv_sort. }
  assert (Hsorted2: mu1 == sort_dst mu1). { apply dst_equiv_sort. }
  assert (Hsort_trans: sort_dst mu0 == sort_dst mu1). { 
    eapply dst_equiv_trans. 
    - apply dst_equiv_sym in Hsorted1. apply Hsorted1.
    - eapply dst_equiv_trans. 
      + apply Heq_mu. + apply Hsorted2. }
  assert (Hvalid_sort1: Valid_dist (sort_dst mu0)). { apply Valid_implies_sort_Valid. assumption. }
  assert (Hvalid_sort2: Valid_dist (sort_dst mu1)). { apply Valid_implies_sort_Valid. assumption. }
  assert (Htemp_beq: beq_dst (sort_dst mu0) (sort_dst mu1) = true). { 
    apply Sort_Valid_Peq_implies_beq_True; try (assumption).
    - split; [apply WF_dist_implies_sortdst_Sorted; assumption| assumption].
    - split; [apply WF_dist_implies_sortdst_Sorted; assumption| assumption]. }
  assert (H1: DAssn_under_dstate mu0 x a == DAssn_under_dstate (sort_dst mu0) x a). { 
    apply mu_Sorted_DA_Peq. }
  assert (H2: DAssn_under_dstate mu1 x a == DAssn_under_dstate (sort_dst mu1) x a). {
    apply mu_Sorted_DA_Peq. }
  eapply dst_equiv_trans.
  - apply H1.
  - eapply dst_equiv_trans.
    + apply sort_beq_after_DA. apply Htemp_beq.
    + apply dst_equiv_sym. apply H2.
Qed. 
(****************************************************************************************************)
Open Scope dstate_scope.

Lemma insert_pair_equiv_cons: forall s1 p1 s2 x Vda, 
  beq_state s1 s2 = true ->
  update_st_with_da s1 p1 x Vda == update_st_with_da s2 p1 x Vda.
Proof.
  intros. generalize dependent s2. generalize s1. 
  induction Vda as [|(a,p) da']; intros; simpl.
  - apply dst_equiv_refl.
  - rewrite dst_cons_eq_add. rewrite dst_cons_eq_add with (mu:= update_st_with_da s2 p1 x da'). 
    apply dst_add_preserves_equiv.
    + apply Peq_one_st. split.
      * assert (Heq: ((evalA_st a s0) == (evalA_st a s2))%Q).
      ** apply st_eq_implies_evalA. assumption.
      ** apply st_eq_implies_update_eq; try assumption.
      * reflexivity.
    + apply IHda'. assumption.
Qed.
Lemma update_st_pair_decpm_prob: forall s p1 p2 x Vda,
  (update_st_with_da s p1 x Vda + update_st_with_da s p2 x Vda ==
  update_st_with_da s (p1 + p2) x Vda)%dist_state.
Proof.
  intros. induction Vda as [|(a,p) da']; intros; simpl; try apply dst_equiv_refl.
  rewrite dst_cons_eq_add. 
  rewrite dst_cons_eq_add with (mu:= update_st_with_da s p2 x da').
  rewrite dst_add_assoc_eq.
  apply dst_equiv_trans with (mu1:= ([(update s x (evalA_st a s), (p * p1)%R)] + 
                                    [(update s x (evalA_st a s), (p * p2)%R)] +
                                  (update_st_with_da s p1 x da' + update_st_with_da s p2 x da'))%dist_state).
  - apply dst_add_shuffle.
  - rewrite dst_cons_eq_add with (mu:= update_st_with_da s (p1 + p2) x da'). 
    apply dst_add_preserves_equiv; try apply dst_equiv_refl.
    + unfold dst_equiv. intros. simpl. 
    destruct (beq_state s0 (update s x (evalA_st a s))); try reflexivity.
    repeat rewrite Rplus_0_r. rewrite Rmult_plus_distr_l. reflexivity.
    + apply IHda'.
Qed.

Lemma insert_RA_Peq: forall s1 p1 mu x Vda, 
  RAssn_under_dstate ((s1,p1)::mu) x Vda == 
  RAssn_under_dstate (insert_st_pair s1 p1 mu) x Vda.
Proof.
  intros. induction mu as [|(s2,p2) mu1 Hmu1].
  - simpl in *. apply dst_equiv_refl.
  - simpl in *. destruct (beq_state s1 s2) eqn: Hst12.
    + simpl in *. rewrite dst_add_assoc_eq. 
    apply dst_add_preserves_equiv; try apply dst_equiv_refl.
    apply dst_equiv_trans with 
      (mu1:= (update_st_with_da s2 p1 x Vda + update_st_with_da s2 p2 x Vda)%dist_state).
      { apply dst_add_preserves_equiv; try apply dst_equiv_refl. 
        apply insert_pair_equiv_cons; try assumption. }
    apply update_st_pair_decpm_prob.
    + destruct (ble_state s1 s2) eqn: Hle.
      * simpl. apply dst_equiv_refl.
      * simpl. rewrite dst_add_assoc_eq.
      apply dst_equiv_trans with 
        (mu1:= (update_st_with_da s2 p2 x Vda + update_st_with_da s1 p1 x Vda +
              RAssn_under_dstate mu1 x Vda)%dist_state).
      ** apply dst_add_inj_r. apply dst_add_comm.
      ** rewrite <- dst_add_assoc_eq. apply dst_add_inj_l. apply Hmu1.
Qed.

Lemma mu_sort_RA_Peq: forall mu x Vda, 
  RAssn_under_dstate mu x Vda == RAssn_under_dstate (sort_dst mu) x Vda.
Proof.
  intros. generalize dependent Vda.
  induction mu as [|(s,p) mu' IH]; intros.
  - simpl. apply dst_equiv_refl.
  - simpl. apply dst_equiv_trans with (mu1:= RAssn_under_dstate ((s,p)::(sort_dst mu')) x Vda).
    + simpl. apply dst_add_inj_l. apply IH.
    + apply insert_RA_Peq.
Qed.
Lemma sort_beq_after_RA: forall mu1 mu2 x a,
  beq_dst mu1 mu2 = true -> 
  RAssn_under_dstate mu1 x a == RAssn_under_dstate mu2 x a.
Proof.
  intros. 
  generalize dependent mu2. induction mu1 as [|(s1,p1) mu10 Hmu1].
  - intros. destruct mu2 as [|(s2,p2) mu20].
    + simpl in *. apply dst_equiv_refl.
    + simpl in *. discriminate H.
  - intros. destruct mu2 as [|(s2,p2) mu20].
    + simpl in H. discriminate H.
    + simpl in *. rewrite <- andb_assoc in H. apply andb_true_iff in H.
      destruct H. apply andb_true_iff in H0. destruct H0.
      apply dst_add_preserves_equiv.
      * unfold Req_bool in H0. destruct (Req_dec_T p1 p2); try discriminate.
      rewrite e.
      apply insert_pair_equiv_cons with (x:=x) (p1:= p2) (Vda:= a)in H; try assumption.
      * apply Hmu1. apply H1.
Qed.

Theorem RA_step_deter: forall mu0 mu1 x da, 
  Valid_dist mu0 -> Valid_dist mu1 -> mu0 == mu1 ->
  (RAssn_under_dstate mu0 x da == RAssn_under_dstate mu1 x da) .
Proof.
  intros mu0 mu1 x Vda H0 H1 Hmu.
  pose (mu0_sorted := sort_dst mu0).
  pose (mu1_sorted := sort_dst mu1).
  assert (Hsorted0: Sorted_dst mu0_sorted). { apply WF_dist_implies_sortdst_Sorted. assumption. }
  assert (Hsorted1: Sorted_dst mu1_sorted). { apply WF_dist_implies_sortdst_Sorted. assumption. }
  assert (Hvalid0: Valid_dist mu0_sorted). { apply Valid_implies_sort_Valid. assumption. }
  assert (Hvalid1: Valid_dist mu1_sorted). { apply Valid_implies_sort_Valid. assumption. }
  assert (Hbeq: beq_dst mu0_sorted mu1_sorted = true). { 
    apply Sort_Valid_Peq_implies_beq_True.
    - split; try assumption.
    - split; try assumption.
    - apply dst_equiv_trans with (mu1:= mu0).
      + apply dst_equiv_sym. apply dst_equiv_sort.
      + apply dst_equiv_trans with (mu1:= mu1); [assumption|apply dst_equiv_sort]. }
  apply dst_equiv_trans with (mu1:= RAssn_under_dstate mu0_sorted x Vda).
  + apply mu_sort_RA_Peq.
  + apply dst_equiv_trans with (mu1:= RAssn_under_dstate mu1_sorted x Vda).
    * apply sort_beq_after_RA. assumption.
    * apply dst_equiv_sym. apply mu_sort_RA_Peq.
Qed.

Lemma RA_DA_equiv: forall mu a1 a2 p1 p2 X, 
  (RAssn_under_dstate mu X [(a1, p1); (a2, p2)] ==
  p1 * DAssn_under_dstate mu X a1 + p2 * DAssn_under_dstate mu X a2)%dist_state.
Proof. 
  intros. induction mu as [|(s,q) mu' Hmu]. 
  - simpl. apply dst_equiv_refl.
  - simpl. destruct (Req_dec_T p1 0); destruct (Req_dec_T p2 0). 
    + simpl. rewrite e. rewrite e0. rewrite Rmult_0_l. 
    rewrite e in Hmu. rewrite e0 in Hmu. 
    repeat rewrite dst_mult_0_l in Hmu. simpl in Hmu. 
    rewrite dst_cons_eq_add.
    rewrite dst_cons_eq_add with (s:= (update s X (evalA_st a2 s))).
    apply dst_equiv_trans with (mu1:= [] +[]). 
      * apply dst_add_preserves_equiv; try apply dst_equiv_nil_prob0. 
      rewrite <- dst_add_0_r.
      apply dst_add_preserves_equiv; try apply dst_equiv_nil_prob0.
      assumption.
      * apply dst_equiv_refl. 
    + simpl. rewrite e. rewrite Rmult_0_l.
    rewrite dst_cons_eq_add. rewrite <- dst_add_0_l.
    apply dst_add_preserves_equiv; try apply dst_equiv_nil_prob0.  
    rewrite dst_cons_eq_add. 
    rewrite dst_cons_eq_add with (mu:= p2 * DAssn_under_dstate mu' X a2).
    apply dst_add_inj_l. rewrite e in Hmu.
    rewrite dst_mult_0_l in Hmu. simpl in Hmu. assumption.
    + simpl. rewrite e. rewrite Rmult_0_l. rewrite dst_add_0_r.
    rewrite dst_cons_eq_add. 
    rewrite dst_cons_eq_add with (mu:= p1 * DAssn_under_dstate mu' X a1).
    apply dst_add_inj_l. rewrite dst_cons_eq_add. 
    rewrite <- dst_add_0_l.
    apply dst_add_preserves_equiv; try apply dst_equiv_nil_prob0. 
    rewrite e in Hmu. rewrite dst_mult_0_l in Hmu. 
    rewrite dst_add_0_r in Hmu. assumption.
    + simpl in *. 
    rewrite dst_cons_eq_add. 
    rewrite dst_cons_eq_add with (s:= update s X (evalA_st a2 s)).
    rewrite dst_add_assoc_eq. 
    apply dst_equiv_trans with (mu1:= 
      [(update s X (evalA_st a1 s), (p1 * q)%R)] + [(update s X (evalA_st a2 s), (p2 * q)%R)] + (p1 * DAssn_under_dstate mu' X a1 + p2 * DAssn_under_dstate mu' X a2)).
      * apply dst_add_inj_l. apply Hmu.
      * rewrite dst_cons_eq_add with (mu := p2 * DAssn_under_dstate mu' X a2).
        rewrite dst_cons_eq_add with (mu := p1 * DAssn_under_dstate mu' X a1 + ([(update s X (evalA_st a2 s), (p2 * q)%R)] + p2 * DAssn_under_dstate mu' X a2)).
        rewrite dst_add_assoc_eq with (mu2:= ([(update s X (evalA_st a2 s), (p2 * q)%R)] + p2 * DAssn_under_dstate mu' X a2)).   
        apply dst_add_shuffle. 
Qed.

(***************getb getnotb**************)

Open Scope dstate_scope.

Theorem get_b_assoc: forall b mu1 mu2, 
  get_b_in_mu b (mu1 + mu2) = (get_b_in_mu b mu1) + (get_b_in_mu b mu2) .
Proof.
  intros.
  generalize dependent mu2.
  induction mu1 as [|(s,q) mu1' Hmu1].
  - simpl. intro. reflexivity.
  - simpl in *. intros. destruct (evalB_st b s) eqn: Heq.
    + simpl. apply app_inv_head_iff with (l:= [(s, q)]). apply Hmu1.
    + apply Hmu1.
Qed.
Theorem get_notb_assoc: forall b mu1 mu2, 
  get_notb_in_mu b (mu1 + mu2) = (get_notb_in_mu b mu1) + (get_notb_in_mu b mu2) .
Proof.
  intros.
  generalize dependent mu2.
  induction mu1 as [|(s,q) mu1' Hmu1].
  - simpl. intro. reflexivity.
  - simpl in *. intros. destruct (evalB_st b s) eqn: Heq.
    + simpl. apply app_inv_head_iff with (l:= [(s, q)]). f_equal. apply Hmu1.
    + simpl. f_equal. apply Hmu1.
Qed.

Theorem mu_div_by_bool : forall mu b, 
  (get_b_in_mu b mu) + (get_notb_in_mu b mu) == mu.
Proof.
  intros. induction mu as [|(s,q) mu' Hmu].
  - simpl. unfold dst_equiv; intros. reflexivity.
  - simpl. destruct (evalB_st b s) eqn: Hb.
    + simpl. unfold dst_equiv; intros. 
      rewrite get_prob_decom with (mu:= [(s, q)]) (mu':= (get_b_in_mu b mu' + get_notb_in_mu b mu')%dist_state). 
      rewrite get_prob_decom with (mu:= [(s, q)]) (mu':= mu').
      f_equal. unfold dst_equiv in Hmu. apply Hmu.
    + simpl. unfold dst_equiv; intros.
      rewrite get_prob_decom. 
      rewrite get_prob_decom with (mu:= [(s, q)]) (mu':= (get_notb_in_mu b mu')%dist_state).
      rewrite get_prob_decom with (mu:= [(s, q)]) (mu':= mu'). 
      rewrite Rplus_comm. rewrite Rplus_assoc. f_equal.
      rewrite Rplus_comm.  
      unfold dst_equiv in Hmu.
      rewrite <- get_prob_decom. 
      apply Hmu.
Qed.

Lemma insert_getb: forall mu b s p, 
  get_b_in_mu b ((s,p)::mu) == get_b_in_mu b (insert_st_pair s p mu).
Proof.
  intros. generalize dependent s.
  induction mu as [|(s',p') mu' Hmu'].
  - simpl. intros. apply dst_equiv_refl.
  - intros. simpl. destruct (beq_state s s') eqn: Hst.
    + destruct (evalB_st b s) eqn: Hb.
      * assert (Hsb': evalB_st b s' = true). { 
        apply st_eq_implies_evalB with (b:= b) in Hst. rewrite <- Hst. assumption. }
      rewrite Hsb'. simpl. rewrite Hsb'.
      rewrite dst_cons_eq_add. 
      rewrite dst_cons_eq_add with (mu:= get_b_in_mu b mu').
      rewrite dst_add_assoc_eq.
      rewrite dst_cons_eq_add with (mu:= get_b_in_mu b mu').
      apply dst_add_preserves_equiv; try apply dst_equiv_refl.
      unfold dst_equiv. intros. simpl. 
      destruct (beq_state s0 s) eqn: Hst0.
      ** assert (Hst0': beq_state s0 s' = true). {
        apply state_eq_trans with (s1:= s); try assumption. }
        rewrite Hst0'. rewrite Rplus_assoc. reflexivity.
      ** apply state_eq_compat_left with (s:= s0) in Hst. rewrite Hst in Hst0.
      rewrite Hst0. reflexivity.
      * assert (Hsb': evalB_st b s' = false). { 
          apply st_eq_implies_evalB with (b:= b) in Hst. rewrite <- Hst. assumption. }
      rewrite Hsb'. simpl. rewrite Hsb'. apply dst_equiv_refl.
    + destruct (ble_state s s') eqn: Hle.
      * destruct (evalB_st b s) eqn: Hbs; destruct (evalB_st b s') eqn: Hbs'; 
      simpl; rewrite Hbs; rewrite Hbs'; apply dst_equiv_refl.
      * simpl. destruct (evalB_st b s) eqn: Hbs; destruct (evalB_st b s') eqn: Hbs'. 
      ** apply dst_equiv_trans with (mu1:= (s', p') :: (s, p) :: get_b_in_mu b mu').
      ++ rewrite dst_cons_eq_add. 
      rewrite dst_cons_eq_add with (mu:= get_b_in_mu b mu').
      rewrite dst_add_assoc_eq. 
      rewrite dst_cons_eq_add with (mu:= (s, p) :: get_b_in_mu b mu'). 
      rewrite dst_cons_eq_add with (mu:= get_b_in_mu b mu').
      rewrite dst_add_assoc_eq. 
      apply dst_add_preserves_equiv; try apply dst_equiv_refl.
      apply dst_add_comm.
      ++ rewrite dst_cons_eq_add. 
      rewrite dst_cons_eq_add with (mu:= get_b_in_mu b (insert_st_pair s p mu')).
      apply dst_add_preserves_equiv; try apply dst_equiv_refl.
      specialize (Hmu' s). simpl in Hmu'. rewrite Hbs in Hmu'.
      apply Hmu'.
      ** specialize (Hmu' s). simpl in Hmu'. rewrite Hbs in Hmu'.
      apply Hmu'.
      ** specialize (Hmu' s). simpl in Hmu'. rewrite Hbs in Hmu'.
      rewrite dst_cons_eq_add. 
      rewrite dst_cons_eq_add with (mu:= get_b_in_mu b (insert_st_pair s p mu')).
      apply dst_add_preserves_equiv; try apply dst_equiv_refl.
      apply Hmu'.
      ** specialize (Hmu' s). simpl in Hmu'. rewrite Hbs in Hmu'.
      apply Hmu'.     
Qed.
Lemma insert_getnotb: forall mu b s p, 
  get_notb_in_mu b ((s,p)::mu) == get_notb_in_mu b (insert_st_pair s p mu).
Proof.
  intros. generalize dependent s.
  induction mu as [|(s',p') mu' Hmu'].
  - simpl. intros. apply dst_equiv_refl.
  - intros. simpl. destruct (beq_state s s') eqn: Hst.
    + destruct (evalB_st b s) eqn: Hb.
      * assert (Hsb': evalB_st b s' = true). { 
        apply st_eq_implies_evalB with (b:= b) in Hst. rewrite <- Hst. assumption. }
        rewrite Hsb'. simpl. rewrite Hsb'. simpl. apply dst_equiv_refl.
      * simpl. assert (Hsb': evalB_st b s' = false). { 
          apply st_eq_implies_evalB with (b:= b) in Hst. rewrite <- Hst. assumption. }
        rewrite Hsb'. simpl. 
      rewrite dst_cons_eq_add. 
      rewrite dst_cons_eq_add with (mu:= get_notb_in_mu b mu').
      rewrite dst_add_assoc_eq.
      rewrite dst_cons_eq_add with (mu:= get_notb_in_mu b mu').
      apply dst_add_preserves_equiv; try apply dst_equiv_refl.
      unfold dst_equiv. intros. simpl. 
      destruct (beq_state s0 s) eqn: Hst0.
      ** assert (Hst0': beq_state s0 s' = true). {
        apply state_eq_trans with (s1:= s); try assumption. }
        rewrite Hst0'. rewrite Rplus_assoc. reflexivity.
      ** apply state_eq_compat_left with (s:= s0) in Hst. rewrite Hst in Hst0.
      rewrite Hst0. reflexivity.
    + destruct (ble_state s s') eqn: Hle.
      * destruct (evalB_st b s) eqn: Hbs; destruct (evalB_st b s') eqn: Hbs'; 
      simpl; rewrite Hbs; rewrite Hbs'; apply dst_equiv_refl.
      * simpl. destruct (evalB_st b s) eqn: Hbs; destruct (evalB_st b s') eqn: Hbs'; simpl in *. 
      ** specialize (Hmu' s). rewrite Hbs in Hmu'. simpl in Hmu'. apply Hmu'. 
      ** specialize (Hmu' s). rewrite Hbs in Hmu'. simpl in Hmu'. 
        rewrite dst_cons_eq_add.  
        rewrite dst_cons_eq_add with (mu:= get_notb_in_mu b (insert_st_pair s p mu')).
        apply dst_add_preserves_equiv; try apply dst_equiv_refl.
        apply Hmu'.
      ** specialize (Hmu' s). rewrite Hbs in Hmu'. simpl in Hmu'. apply Hmu'.
      ** specialize (Hmu' s). rewrite Hbs in Hmu'. simpl in Hmu'. 
        apply dst_equiv_trans with (mu1:= (s', p') :: (s, p) :: get_notb_in_mu b mu').
        ++ rewrite dst_cons_eq_add. 
        rewrite dst_cons_eq_add with (mu:= get_notb_in_mu b mu').
        rewrite dst_add_assoc_eq. 
        rewrite dst_cons_eq_add with (mu:= (s, p) :: get_notb_in_mu b mu'). 
        rewrite dst_cons_eq_add with (mu:= get_notb_in_mu b mu').
        rewrite dst_add_assoc_eq. 
        apply dst_add_preserves_equiv; try apply dst_equiv_refl.
        apply dst_add_comm.
        ++ rewrite dst_cons_eq_add. 
        rewrite dst_cons_eq_add with (mu:= get_notb_in_mu b (insert_st_pair s p mu')).
        apply dst_add_preserves_equiv; try apply dst_equiv_refl. 
        apply Hmu'.
Qed.

Lemma dst_eq_getb_sorted: forall b mu, 
  Valid_dist mu ->
    get_b_in_mu b mu == (get_b_in_mu b (sort_dst mu)).
Proof.
  intros. induction mu as [|(s,p) mu' Hmu].
  - simpl. apply dst_equiv_refl.
  - unfold sort_dst. fold sort_dst. 
    apply dst_equiv_trans with (mu1:= get_b_in_mu b ((s,p)::(sort_dst mu'))).
    + rewrite dst_cons_eq_add. rewrite dst_cons_eq_add with (mu:= sort_dst mu'). repeat rewrite get_b_assoc.
    apply dst_add_preserves_equiv; try apply dst_equiv_refl. apply Hmu.
    apply Valid_dist_inv in H. assumption.
    + apply insert_getb.
Qed. 
Lemma dst_eq_get_b_eq: forall b mu1 mu2, 
  beq_dst mu1 mu2 = true ->
    beq_dst (get_b_in_mu b mu1) (get_b_in_mu b mu2) = true.
Proof.
  intros. generalize dependent mu2.
  induction mu1 as [|(s1,p1) mu1' Hmu1]; destruct mu2 as [|(s2,p2) mu2']. 
    + intros. simpl. reflexivity.
    + intros. simpl. simpl in H. discriminate.
    + intros. simpl. simpl in H. discriminate.
    + intros. simpl. simpl in H. apply andb_true_iff in H.
    destruct H. apply andb_true_iff in H. destruct H.
    destruct (evalB_st b s1) eqn: Hsb.
    * assert (Hsb': evalB_st b s2 = true). { 
        apply st_eq_implies_evalB with (b:= b) in H. rewrite <- H. assumption. }
    rewrite Hsb'. simpl. apply andb_true_iff. split.
    ** apply andb_true_iff. split; assumption.
    ** apply Hmu1. assumption.
    * assert (Hsb': evalB_st b s2 = false). { 
        apply st_eq_implies_evalB with (b:= b) in H. rewrite <- H. assumption. }
    rewrite Hsb'. simpl. apply Hmu1. assumption.
Qed.

Theorem Peq_implies_get_b_Peq: forall mu0 mu1 b, 
  Valid_dist mu0 -> Valid_dist mu1 -> 
  mu0 == mu1 ->
  (get_b_in_mu b mu0) == (get_b_in_mu b mu1). 
Proof.
  intros.
  pose (mu0_sorted := sort_dst mu0).
  pose (mu1_sorted := sort_dst mu1).
  assert (Hsorted0: Sorted_dst mu0_sorted). { apply WF_dist_implies_sortdst_Sorted. assumption. }
  assert (Hsorted1: Sorted_dst mu1_sorted). { apply WF_dist_implies_sortdst_Sorted. assumption. }
  assert (Hvalid0: Valid_dist mu0_sorted). { apply Valid_implies_sort_Valid. assumption. }
  assert (Hvalid1: Valid_dist mu1_sorted). { apply Valid_implies_sort_Valid. assumption. }
  assert (Hbeq: beq_dst mu0_sorted mu1_sorted = true). { 
    apply Sort_Valid_Peq_implies_beq_True.
    - split; try assumption.
    - split; try assumption.
    - apply dst_equiv_trans with (mu1:= mu0).
      + apply dst_equiv_sym. apply dst_equiv_sort.
      + apply dst_equiv_trans with (mu1:= mu1); [assumption|apply dst_equiv_sort]. }
  apply dst_equiv_trans with (mu1:= (get_b_in_mu b (sort_dst mu0))).
  - apply dst_eq_getb_sorted. assumption.
  - apply dst_equiv_trans with (mu1:= (get_b_in_mu b (sort_dst mu1))).
  + fold mu0_sorted. fold mu1_sorted. 
    apply dst_eq_get_b_eq with (b:= b) in Hbeq.
    apply dst_eq_implies_equiv. assumption.
  + apply dst_equiv_sym. apply dst_eq_getb_sorted. assumption.
Qed.

Lemma dst_eq_getnotb_sorted: forall b mu, 
  Valid_dist mu ->
    get_notb_in_mu b mu ==  (get_notb_in_mu b (sort_dst mu)).
Proof.
  intros. induction mu as [|(s,p) mu' Hmu].
  - simpl. apply dst_equiv_refl.
  - unfold sort_dst. fold sort_dst. 
    apply dst_equiv_trans with (mu1:= get_notb_in_mu b ((s,p)::(sort_dst mu'))).
    + rewrite dst_cons_eq_add. rewrite dst_cons_eq_add with (mu:= sort_dst mu'). repeat rewrite get_notb_assoc.
    apply dst_add_preserves_equiv; try apply dst_equiv_refl. apply Hmu.
    apply Valid_dist_inv in H. assumption.
    + apply insert_getnotb.
Qed.

Lemma dst_eq_get_notb_eq: forall b mu1 mu2, 
  beq_dst mu1 mu2 = true ->
    beq_dst (get_notb_in_mu b mu1) (get_notb_in_mu b mu2) = true.
Proof.
  intros. generalize dependent mu2.
  induction mu1 as [|(s1,p1) mu1' Hmu1]; destruct mu2 as [|(s2,p2) mu2']. 
    + intros. simpl. reflexivity.
    + intros. simpl. simpl in H. discriminate.
    + intros. simpl. simpl in H. discriminate.
    + intros. simpl. simpl in H. apply andb_true_iff in H.
    destruct H. apply andb_true_iff in H. destruct H.
    destruct (evalB_st b s1) eqn: Hsb.
    * assert (Hsb': evalB_st b s2 = true). { 
        apply st_eq_implies_evalB with (b:= b) in H. rewrite <- H. assumption. }
      rewrite Hsb'. simpl. apply Hmu1. assumption.
    * assert (Hsb': evalB_st b s2 = false). { 
        apply st_eq_implies_evalB with (b:= b) in H. rewrite <- H. assumption. }
      rewrite Hsb'. simpl. apply andb_true_iff. split.
    ** apply andb_true_iff. split; assumption.
    ** apply Hmu1. assumption.
Qed.

Theorem Peq_implies_get_notb_Peq: forall mu0 mu1 b, 
  Valid_dist mu0 -> Valid_dist mu1 ->
  mu0 == mu1 ->
  (get_notb_in_mu b mu0) == (get_notb_in_mu b mu1). 
Proof.
  intros.
  pose (mu0_sorted := sort_dst mu0).
  pose (mu1_sorted := sort_dst mu1).
  assert (Hsorted0: Sorted_dst mu0_sorted). { apply WF_dist_implies_sortdst_Sorted. assumption. }
  assert (Hsorted1: Sorted_dst mu1_sorted). { apply WF_dist_implies_sortdst_Sorted. assumption. }
  assert (Hvalid0: Valid_dist mu0_sorted). { apply Valid_implies_sort_Valid. assumption. }
  assert (Hvalid1: Valid_dist mu1_sorted). { apply Valid_implies_sort_Valid. assumption. }
  assert (Hbeq: beq_dst mu0_sorted mu1_sorted = true). { 
    apply Sort_Valid_Peq_implies_beq_True.
    - split; try assumption.
    - split; try assumption.
    - apply dst_equiv_trans with (mu1:= mu0).
      + apply dst_equiv_sym. apply dst_equiv_sort.
      + apply dst_equiv_trans with (mu1:= mu1); [assumption|apply dst_equiv_sort]. }
  apply dst_equiv_trans with (mu1:= (get_notb_in_mu b (sort_dst mu0))).
  - apply dst_eq_getnotb_sorted. assumption.
  - apply dst_equiv_trans with (mu1:= (get_notb_in_mu b (sort_dst mu1))).
  + fold mu0_sorted. fold mu1_sorted. 
    apply dst_eq_get_notb_eq with (b:= b) in Hbeq.
    apply dst_eq_implies_equiv. assumption.
  + apply dst_equiv_sym. apply dst_eq_getnotb_sorted. assumption.
Qed.

Lemma pd_eq_preserves_get_b: forall pd0 pd1 b, 
  Valid_dist (mu pd0) -> Valid_dist (mu pd1) ->
    pd0 ≡ pd1 -> extract_b_pd b pd0 ≡ extract_b_pd b pd1.
Proof.
  intros. destruct H1. split; simpl; try assumption. 
  apply Peq_implies_get_b_Peq; try assumption.
Qed.
Lemma pd_eq_preserves_get_notb: forall pd0 pd1 b, 
  Valid_dist (mu pd0) -> Valid_dist (mu pd1) ->
    pd0 ≡ pd1 -> extract_notb_pd b pd0 ≡ extract_notb_pd b pd1.
Proof.
  intros. destruct H1. split; simpl; try assumption. 
  apply Peq_implies_get_notb_Peq; try assumption.
Qed.

Lemma bT_supp_implies_getb_eq: forall b pd, 
  Valid_dist (mu pd) ->
  b_supp_classify b pd = All_True ->
  extract_b_pd b pd ≡ pd.
Proof.
  intros. split; simpl; try apply dom_equiv_refl. unfold b_supp_classify in H0.
  destruct pd. induction mu as [|(s,p) mu' IH].
  - simpl in *. discriminate.
  - simpl in *. 
    destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s, p) :: mu'))) eqn: Hb.
    + unfold supp_mu in Hb. simpl in Hb. rewrite insert_st_pair_fst_eq_insert_st in Hb. 
      rewrite supp_insert_evalB in Hb. apply andb_true_iff in Hb. destruct Hb.
      rewrite H1. inversion all_partial; subst. apply Valid_dist_inv in H.
      specialize (IH H7 H). rewrite dst_cons_eq_add. 
      rewrite dst_cons_eq_add with (mu:= mu'). apply dst_add_inj_l.
      destruct mu'; try apply dst_equiv_refl.
      apply IH. unfold supp_mu. rewrite H2. reflexivity.
    + destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s, p) :: mu'))); try discriminate.
Qed.

Lemma bF_supp_implies_getnotb_eq: forall b pd,
  Valid_dist (mu pd) ->
  b_supp_classify b pd = All_False ->
  extract_notb_pd b pd ≡ pd.
Proof.
  intros. split; simpl; try apply dom_equiv_refl. unfold b_supp_classify in H0.
  destruct pd. induction mu as [|(s,p) mu' IH].
  - simpl in *. discriminate.
  - simpl in *. 
    destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s, p) :: mu'))) eqn: HbT; try discriminate.
    destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s, p) :: mu'))) eqn: HbF; try discriminate.
    unfold supp_mu in HbF. simpl in HbF. rewrite insert_st_pair_fst_eq_insert_st in HbF. 
    rewrite supp_insert_negbevalB in HbF. apply andb_true_iff in HbF. destruct HbF.
    rewrite H1. inversion all_partial; subst. apply Valid_dist_inv in H.
    specialize (IH H7 H). rewrite dst_cons_eq_add. 
    rewrite dst_cons_eq_add with (mu:= mu'). apply dst_add_inj_l.
    destruct mu' as [|(s',p') mu']; try apply dst_equiv_refl.
    apply IH. unfold supp_mu. rewrite H2. 
    destruct (forallb (fun s0 : local_st => evalB_st b s0) (map fst (sort_dst ((s', p') :: mu')))) eqn: Hcontra; try reflexivity.
    unfold supp_mu in Hcontra. simpl in Hcontra. rewrite insert_st_pair_fst_eq_insert_st in Hcontra. 
    rewrite supp_insert_evalB in Hcontra. apply andb_true_iff in Hcontra. destruct Hcontra.
    simpl in H2. rewrite insert_st_pair_fst_eq_insert_st in H2. 
    repeat rewrite supp_insert_negbevalB in H2. 
    apply negb_false_iff in H3. rewrite H3 in H2. simpl in H2. discriminate.
Qed.

Lemma forallb_getb_eq: forall b mu, 
  forallb (fun s : local_st => evalB_st b s) (map fst mu) = true -> 
  get_b_in_mu b mu = mu.
Proof.
  intros. induction mu as [|(s,q) mu' Hmu].
  - simpl. reflexivity.
  - simpl. simpl in H. apply andb_true_iff in H. destruct H. rewrite H. f_equal. apply Hmu. assumption.
Qed.
Lemma forallb_getnotb_eq: forall b mu, 
  forallb (fun s : local_st => negb (evalB_st b s)) (map fst mu) = true -> 
  get_notb_in_mu b mu = mu.
Proof.
  intros. induction mu as [|(s,q) mu' Hmu].
  - simpl. reflexivity.
  - simpl. simpl in H. apply andb_true_iff in H. destruct H. rewrite H. f_equal. apply Hmu. assumption.
Qed.

Theorem dst_get_b_coef_mult: forall mu p b, get_b_in_mu b (p * mu) = p * (get_b_in_mu b mu).
Proof.
  intros. induction mu as [|(s,q) mu' Hmu].
  - simpl. reflexivity.
  - simpl. destruct (evalB_st b s) eqn: Hs.
    + simpl. destruct (Req_dec_T p 0) eqn: Hp.
      * simpl. reflexivity.
      * simpl. rewrite Hs. f_equal. apply Hmu.
    + destruct (Req_dec_T p 0) eqn: Hp.
      * simpl. rewrite e. rewrite dst_mult_0_l. reflexivity.
      * simpl. rewrite Hs. apply Hmu.
Qed.

Theorem dst_get_notb_coef_mult: forall mu p b, 
  get_notb_in_mu b (p * mu) = p * (get_notb_in_mu b mu).
Proof.
  intros. induction mu as [|(s,q) mu' Hmu].
  - simpl. reflexivity.
  - simpl. destruct (evalB_st b s) eqn: Hs.
    + destruct (Req_dec_T p 0) eqn: Hp.
      * simpl. rewrite e. rewrite dst_mult_0_l. reflexivity.
      * simpl. rewrite Hs. apply Hmu.
    + simpl. destruct (Req_dec_T p 0) eqn: Hp.
      * simpl. reflexivity.
      * simpl. rewrite Hs. simpl. f_equal. apply Hmu.
Qed.

Lemma conti_get_b_eq: forall b mu, 
  let mu1:= get_b_in_mu b mu: dist_state in 
  mu1 = get_b_in_mu b mu1.
Proof. 
  intros. 
  induction mu as [|(s,p) mu' Hmu ].
  - simpl. reflexivity.
  - unfold get_b_in_mu in mu1. destruct (evalB_st b s) eqn: Hs.
    + simpl in *. rewrite Hs. unfold get_b_in_mu in *. simpl in *. 
      rewrite <- Hmu. reflexivity.
    + apply Hmu.
Qed.

Lemma get_notb_after_get_b: forall b mu, 
  let mu1:= get_b_in_mu b mu: dist_state in 
  get_notb_in_mu b mu1 = [].
Proof.
  intros. 
  induction mu as [|(s,p) mu' Hmu ].
  - simpl. reflexivity.
  - simpl in mu1. destruct (evalB_st b s) eqn: Hs. 
    + simpl in *. rewrite Hs. simpl. apply Hmu.
    + apply Hmu.
Qed.

Lemma get_b_after_get_notb: forall b mu, 
  let mu1:= get_notb_in_mu b mu: dist_state in 
  get_b_in_mu b mu1 = [].
Proof.
  intros. 
  induction mu as [|(s,p) mu' Hmu ].
  - simpl. reflexivity.
  - simpl in mu1. destruct (evalB_st b s) eqn: Hs. 
    + apply Hmu.
    + simpl in *. rewrite Hs. apply Hmu.
Qed.
Lemma munotb_eq_mu_implies_mub_eq_empty: forall mu b, 
  mu = get_notb_in_mu b mu ->
  get_b_in_mu b mu = []. 
Proof.
  intros. rewrite H. apply get_b_after_get_notb.
Qed.

Lemma mub_eq_mu_implies_mub_eq_empty: forall mu b, 
  mu = get_b_in_mu b mu ->
  get_notb_in_mu b mu = [].
Proof. 
  intros. rewrite H. apply get_notb_after_get_b.
Qed.

Lemma bT_getnotb_nil: forall b pd,
  b_supp_classify b pd = All_True -> 
  mu (extract_notb_pd b pd) = [].
Proof.
  intros. destruct pd. unfold b_supp_classify in H. simpl in *. 
  apply mub_eq_mu_implies_mub_eq_empty.
  destruct mu as [|(s,p) mu']; try reflexivity.
  destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s, p) :: mu'))) eqn: HT; 
  destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s, p) :: mu'))); try discriminate.
  - simpl. unfold supp_mu in HT. simpl in HT. rewrite insert_st_pair_fst_eq_insert_st in HT.
  rewrite supp_insert_evalB in HT. apply andb_true_iff in HT. destruct HT.
  rewrite H0. f_equal. rewrite forallb_getb_eq; try reflexivity. 
  rewrite supp_sort_evalB. apply H1. 
  - simpl. unfold supp_mu in HT. simpl in HT. rewrite insert_st_pair_fst_eq_insert_st in HT.
  rewrite supp_insert_evalB in HT. apply andb_true_iff in HT. destruct HT.
  rewrite H0. f_equal. rewrite forallb_getb_eq; try reflexivity. 
  rewrite supp_sort_evalB. apply H1. 
Qed.
Lemma bF_getnotb_nil: forall b pd,
  b_supp_classify b pd = All_False -> 
  mu (extract_b_pd b pd) = [].
Proof.
  intros. destruct pd. unfold b_supp_classify in H. simpl in *. 
  apply munotb_eq_mu_implies_mub_eq_empty.
  destruct mu as [|(s,p) mu']; try reflexivity.
  destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s, p) :: mu'))) eqn: HF; 
  destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s, p) :: mu'))) eqn: HT; try discriminate.
  simpl. unfold supp_mu in HT. simpl in HT. rewrite insert_st_pair_fst_eq_insert_st in HT.
  rewrite supp_insert_negbevalB in HT. apply andb_true_iff in HT. destruct HT.
  rewrite H0. f_equal. rewrite forallb_getnotb_eq; try reflexivity. 
  rewrite supp_sort_negbevalB. apply H1. 
Qed.


(*****************************************************************************************************)
Open Scope R_scope.

Lemma positive_mu_by_b: forall mu b, positive_probs mu -> 
  let mu_b:= get_b_in_mu b mu in
  let mu_notb:= get_notb_in_mu b mu in
  positive_probs mu_b /\ positive_probs mu_notb.
Proof.
  intros. split.
  - induction mu as [|(s,p) mu' IH]. 
    + simpl in *. apply I.
    + simpl in *. destruct (evalB_st b s).
      * simpl in *. destruct H. split; try assumption. apply IH. assumption.
      * simpl in *. destruct H. apply IH. assumption.
  - induction mu as [|(s,p) mu' IH]. 
    + simpl in *. apply I.
    + simpl in *. destruct (evalB_st b s).
      * simpl in *. destruct H. apply IH. assumption.
      * simpl in *. destruct H. split; try assumption. apply IH. assumption.
Qed.

Lemma sum_prob_get_notb_ge0: forall mu b,
  (0 <= sum_probs mu)%R -> positive_probs mu -> 
  (0 <= (sum_probs (get_notb_in_mu b mu)))%R.
Proof.
  intros. induction mu as [|(s,p) mu' IH].
  - simpl. apply Rle_refl.
  - simpl. destruct H0. destruct H0. destruct (evalB_st b s).
  + simpl. apply IH; try assumption. apply positive_sum_ge_0. assumption.
  + simpl. apply Rplus_le_le_0_compat.
  * apply Rlt_le. assumption.
  * apply IH; try assumption. apply positive_sum_ge_0. assumption.
Qed. 

Lemma sum_prob_get_b_ge0: forall mu b,
  (0 <= sum_probs mu)%R -> positive_probs mu -> 
  (0 <= sum_probs (get_b_in_mu b mu))%R.
Proof.
  intros. induction mu as [|(s,p) mu' IH].
  - simpl. apply Rle_refl.
  - simpl. destruct H0. destruct H0. destruct (evalB_st b s).
  + simpl. apply Rplus_le_le_0_compat.
  * apply Rlt_le. assumption.
  * apply IH; try assumption. apply positive_sum_ge_0. assumption.
  + apply IH; try assumption. apply positive_sum_ge_0. assumption.
Qed. 

Lemma sum_prob_get_b_le: forall mu b,
  Valid_dist mu ->
  ((sum_probs (get_b_in_mu b mu)) <= (sum_probs mu))%R.
Proof.
  intros. induction mu as [|(s,p) mu' IH].
  - simpl. apply Rle_refl.
  - simpl. destruct (evalB_st b s).
    + simpl. apply Rplus_le_compat_l. apply IH. apply Valid_dist_inv in H. apply H.
    + rewrite <- Rplus_0_l at 1. apply Rplus_le_compat. 
      * destruct H. simpl in H0. destruct H0. 
      unfold prob_is_positive in H0. destruct H0. apply Rlt_le. assumption.
      * apply IH. apply Valid_dist_inv in H. apply H.
Qed. 
Lemma sum_prob_get_notb_le: forall mu b,
  Valid_dist mu ->
  ((sum_probs (get_notb_in_mu b mu)) <= (sum_probs mu))%R.
Proof.
  intros. induction mu as [|(s,p) mu' IH].
  - simpl. apply Rle_refl.
  - simpl. destruct (evalB_st b s).
    + simpl. rewrite <- Rplus_0_l at 1. apply Rplus_le_compat. 
      * destruct H. simpl in H0. 
      destruct H0. unfold prob_is_positive in H0. destruct H0.
      apply Rlt_le. apply H0.
      * apply IH. apply Valid_dist_inv in H. apply H.
    + simpl. apply Rplus_le_compat.
      * apply Rle_refl.
      * apply IH. apply Valid_dist_inv in H. apply H.
Qed. 
Theorem dst_Valid_get_b: forall mu b, 
  Valid_dist mu -> 
  Valid_dist (get_b_in_mu b mu).
Proof.
  intros.
  assert (Hvalid_copy: Valid_dist mu) by assumption.
  unfold Valid_dist.
  destruct H. destruct H. split.
  - split. 
  + induction mu as [|(s,p) mu' IH].
    * simpl. apply Rle_refl.
    * simpl. assert (Htemp: (0 <= sum_probs (get_b_in_mu b mu'))%R). {
      apply Valid_dist_inv in Hvalid_copy. apply IH. 
      * destruct Hvalid_copy. destruct H2. assumption.
      * destruct Hvalid_copy. destruct H2. assumption.
      * destruct Hvalid_copy. assumption.
      * assumption. }
    destruct (evalB_st b s); try assumption.
    simpl. apply Rplus_le_le_0_compat; try assumption.
    destruct H0. unfold prob_is_positive in H0. destruct H0. apply Rlt_le. assumption.
  + apply Rle_trans with (r2:= sum_probs mu). * apply sum_prob_get_b_le. apply Hvalid_copy.
    * apply H1.
  - induction mu as [|(s,p) mu' IH].
  + simpl. apply I.
  + simpl. apply Valid_dist_inv in Hvalid_copy. 
    assert (Hvalid_copy': Valid_dist mu') by assumption.
    destruct Hvalid_copy. destruct H2.
    destruct (evalB_st b s).
    * simpl. simpl in H0. destruct H0. split; try assumption. 
    apply IH; try assumption.
    * apply IH; try assumption. 
Qed.


Theorem dst_Valid_get_notb: forall mu b, 
  Valid_dist mu -> 
  Valid_dist (get_notb_in_mu b mu).
Proof.
  intros.
  assert (Hvalid_copy: Valid_dist mu) by assumption.
  unfold Valid_dist.
  destruct H. destruct H. split.
  - split. 
  + induction mu as [|(s,p) mu' IH].
    * simpl. apply Rle_refl.
    * simpl. assert (Htemp: (0 <= sum_probs (get_notb_in_mu b mu'))%R). {
      apply Valid_dist_inv in Hvalid_copy. apply IH. 
      * destruct Hvalid_copy. destruct H2. assumption.
      * destruct Hvalid_copy. destruct H2. assumption.
      * destruct Hvalid_copy. assumption.
      * assumption. }
      destruct (evalB_st b s); try assumption.
      simpl. apply Rplus_le_le_0_compat; try assumption.
      destruct H0. unfold prob_is_positive in H0. destruct H0. apply Rlt_le. assumption.
  + apply Rle_trans with (r2:= sum_probs mu). * apply sum_prob_get_notb_le. apply Hvalid_copy.
    * apply H1.
  - induction mu as [|(s,p) mu' IH].
  + simpl. apply I.
  + simpl. apply Valid_dist_inv in Hvalid_copy. 
    assert (Hvalid_copy': Valid_dist mu') by assumption.
    destruct Hvalid_copy. destruct H2.
    destruct (evalB_st b s).
    * apply IH; try assumption. 
    * simpl. simpl in H0. destruct H0. split; try assumption. 
    apply IH; try assumption.
Qed.

Lemma dst_sum_decom_by_b: forall mu b, 
  (0 <= sum_probs mu)%R -> positive_probs mu ->
  let mu_b:= get_b_in_mu b mu in
  let mu_notb:= get_notb_in_mu b mu in
  (sum_probs mu = sum_probs mu_b + sum_probs mu_notb)%R.
Proof.
  intros. induction mu as [|(s,p) mu' IH].
  - simpl. rewrite Rplus_0_l. reflexivity.
  - simpl in *. destruct (evalB_st b s).
    + simpl in *. rewrite Rplus_assoc. f_equal. destruct H0.
    apply IH; try assumption.
    apply positive_sum_ge_0. assumption.
    + simpl in *. rewrite <- Rplus_assoc. rewrite Rplus_comm with (r1:=sum_probs mu_b).
    rewrite Rplus_assoc. f_equal. destruct H0.
    apply IH; try assumption.
    apply positive_sum_ge_0. assumption.
Qed.

Lemma WF_dist_b_notb: forall mu b, 
  let mu_b:= get_b_in_mu b mu : dist_state in 
  let mu_notb:= get_notb_in_mu b mu : dist_state in
  Valid_dist mu -> Valid_dist (mu_b + mu_notb)%dist_state.
Proof. 
  intros. rewrite <- dst_mult_1_l with (mu:= mu_b).
  rewrite <- dst_mult_1_l with (mu:= mu_notb).
  apply Valid_linear_under_eq_prob; try assumption.
  - apply dst_Valid_get_b; try assumption.
  - apply dst_Valid_get_notb; try assumption.
  - apply Rle_0_1.
  - apply Rle_0_1.
  - repeat rewrite Rmult_1_l. unfold mu_b. unfold mu_notb.
    rewrite <- dst_sum_decom_by_b with (b:= b); try assumption.
    + destruct H. assumption.
    + destruct H. destruct H. assumption.
    + destruct H. destruct H. assumption.
Qed. 

Lemma Valid_da (da: dist aexp) : 
  positive_probs da /\ sum_probs da = 1%R -> Valid_dist da.
Proof. 
  intros. destruct H. split; try assumption. rewrite H0. 
  split; [apply Rle_0_1|apply Rle_refl].
Qed.


Lemma NS_preserve_positive_probs: forall c pd pd', 
  positive_probs (mu pd) -> NS c pd pd' -> 
  positive_probs (mu pd').
Proof.
  intros c pd pd' Hpos HNS. induction HNS; subst; try assumption.
  - destruct pd as [dom mu HPD]. simpl in *.
    induction mu as [|(s,p) mu0' IH]; simpl; try apply I. 
    destruct Hpos. split; try assumption. 
    inversion HPD; subst. 
    apply IH with (HPD:= H5); try assumption.
  - destruct Vda as [da Hda]. 
    assert (Htemp: Valid_dist da). { apply Valid_da. assumption. }
    apply pos_after_RA; assumption.
  - apply IHHNS2. apply IHHNS1. assumption.
  - simpl. apply I.
  - apply IHHNS. assumption.
  - apply IHHNS. assumption.
  - rewrite H4. apply dst_positive_decom. split.
    + apply IHHNS1. apply positive_mu_by_b; assumption.  
    + apply IHHNS2. apply positive_mu_by_b; assumption. 
  - simpl. apply I.
  - apply IHHNS2. apply IHHNS1. assumption.
  - rewrite H4. apply dst_positive_decom. split.
    + apply IHHNS2. apply IHHNS1. apply positive_mu_by_b; assumption. 
    + apply positive_mu_by_b; assumption. 
Qed. 

Lemma NS_preserve_sum_ge0: forall c pd pd', 
  0 <= sum_probs (mu pd) -> positive_probs (mu pd) -> 
  NS c pd pd' -> 0 <= sum_probs (mu pd').
Proof.
  intros. induction H1; subst; simpl; try assumption; try apply Rle_refl.
  - rewrite DA_preserve_sum_prob. assumption.
  - destruct Vda. apply sum_ge0_RA; try assumption. apply Valid_da. assumption.
  - apply IHNS2. 
    + apply IHNS1; try assumption.
    + apply NS_preserve_positive_probs with (c:= i1) (pd:= pd); try assumption.
  - apply IHNS; try assumption.
  - apply IHNS; try assumption.
  - rewrite H6. rewrite dst_sum_prob_decom. apply Rplus_le_le_0_compat.
    + apply IHNS1. 
      * apply positive_sum_ge_0. apply positive_mu_by_b; assumption. 
      * apply positive_mu_by_b; assumption. 
    + apply IHNS2.
      * apply positive_sum_ge_0. apply positive_mu_by_b; assumption. 
      * apply positive_mu_by_b; assumption.
  - apply IHNS2; try assumption. 
    + apply IHNS1; try assumption.
    + apply NS_preserve_positive_probs in H1_; assumption.
  - rewrite H6. rewrite dst_sum_prob_decom. apply Rplus_le_le_0_compat.
    + apply IHNS2. 
      * apply positive_sum_ge_0. 
      apply NS_preserve_positive_probs with (c:= i) (pd:= pd_b); try assumption.
      apply positive_mu_by_b; assumption. 
      * apply NS_preserve_positive_probs with (c:= i) (pd:= pd_b); try assumption. 
      apply positive_mu_by_b; assumption. 
  + apply sum_prob_get_notb_ge0; assumption.
Qed. 

Lemma NS_preserves_sum_probs_upper_bound: forall c pd pd', 
  0 <= sum_probs (mu pd) -> 
  positive_probs (mu pd) -> 
  NS c pd pd' -> 
  (sum_probs (mu pd') <= sum_probs (mu pd))%R.
Proof. 
  intros. induction H1; subst; intros; try apply Rle_refl; try assumption.
  - simpl. rewrite DA_preserve_sum_prob. apply Rle_refl.
  - destruct Vda. apply sum_le_after_RA; try assumption. apply Valid_da. assumption. 
  - apply Rle_trans with (r2:= (sum_probs (mu pd1))).
    + apply IHNS2; try assumption.
      * apply NS_preserve_sum_ge0 with (c:= i1) (pd:= pd); try assumption.
      * apply NS_preserve_positive_probs with (c:= i1) (pd:= pd); try assumption. 
    + apply IHNS1; try assumption.
  - simpl. apply IHNS; try assumption. 
  - apply IHNS; try assumption.
  - rewrite H6. rewrite dst_sum_prob_decom. 
    assert (Hsum_dec: sum_probs (mu pd) = sum_probs (mu pd_b) + sum_probs (mu pd_notb)). { 
      apply dst_sum_decom_by_b; try assumption. }
    rewrite Hsum_dec. apply Rplus_le_compat.
    + apply IHNS1; try assumption.
      * apply sum_prob_get_b_ge0; assumption.
      * apply positive_mu_by_b; assumption. 
    + apply IHNS2; try assumption.
    * apply sum_prob_get_notb_ge0; assumption.
    * apply positive_mu_by_b; assumption. 
  - apply Rle_trans with (r2:= (sum_probs (mu pd1))). 
    + apply IHNS2; try assumption. 
      * apply NS_preserve_sum_ge0 with (c:= i) (pd:= pd); try assumption.
      * apply NS_preserve_positive_probs with (c:= i) (pd:= pd); try assumption.
    + apply IHNS1; try assumption.
  - rewrite H6. rewrite dst_sum_prob_decom. 
    assert (Hsum_dec: sum_probs (mu pd) = sum_probs (mu pd_b) + sum_probs (mu pd_notb)). { 
      apply dst_sum_decom_by_b; try assumption. }
    rewrite Hsum_dec. apply Rplus_le_compat; try apply Rle_refl.
    + apply Rle_trans with (r2:= sum_probs (mu pd0)).
      * apply IHNS2; try assumption.
      ** apply NS_preserve_sum_ge0 with (c:= i) (pd:= pd_b); try assumption.
      ++ apply sum_prob_get_b_ge0; assumption.
      ++ apply positive_mu_by_b; assumption. 
      ** apply NS_preserve_positive_probs with (c:= i) (pd:= pd_b); try assumption.
        apply positive_mu_by_b; assumption.
      * apply IHNS1; try assumption.
      ++ apply sum_prob_get_b_ge0; assumption.
      ++ apply positive_mu_by_b; assumption.
Qed. 

Lemma Valid_forall_NS: forall c pd pd', 
  Valid_dist (mu pd) -> NS c pd pd' -> 
  Valid_dist (mu pd').
Proof.
  intros. 
  induction H0; try assumption; try apply Valid_dist_nil.
  - apply Valid_after_DA. assumption.
  - destruct Vda. apply Valid_after_RA; try assumption. apply Valid_da. assumption. 
  - apply IHNS2; try assumption. apply IHNS1; assumption.
  - apply IHNS; try assumption.
  - apply IHNS; try assumption.
  - rewrite H5. unfold Valid_dist. destruct H. destruct H. split.
    + split. 
      * rewrite <- H5. apply NS_preserve_sum_ge0 with (c:= If b i1 i2) (pd:= pd); try assumption. 
        eapply NS_IF_Mixed; try assumption.
      ** apply H0_. ** apply H0_0. ** assumption. ** assumption. ** assumption.
      * apply Rle_trans with (r2:= sum_probs (mu pd)). 
      ** rewrite <- H5. apply NS_preserves_sum_probs_upper_bound with (c:= If b i1 i2); try assumption. 
        eapply NS_IF_Mixed; try assumption.
      ++ apply H0_. ++ apply H0_0. ++ assumption. ++ assumption. ++ assumption.
      ** assumption.
    + rewrite <- H5. apply NS_preserve_positive_probs with (c:= If b i1 i2) (pd:= pd); try assumption.
      eapply NS_IF_Mixed; try assumption.
      ** apply H0_. ** apply H0_0. ** assumption. ** assumption. ** assumption.
  - apply IHNS2; try assumption. apply IHNS1; assumption.
  - rewrite H5. unfold Valid_dist. destruct H. destruct H. split.
    + split. 
      * rewrite dst_sum_prob_decom. apply Rplus_le_le_0_compat.
      ** apply NS_preserve_sum_ge0 with (c:= While b i) (pd:= pd0); try assumption.
      ++ apply NS_preserve_sum_ge0 with (c:= i) (pd:= pd_b); try assumption.
      -- apply sum_prob_get_b_ge0; try assumption. 
      -- apply positive_mu_by_b; try assumption.
      ++ apply NS_preserve_positive_probs with (c:= i) (pd:= pd_b); try assumption. 
      apply positive_mu_by_b; try assumption.
      ** apply sum_prob_get_notb_ge0; try assumption. 
      * apply Rle_trans with (r2:= sum_probs (mu pd)); try assumption.
      ** assert (Hsum_dec: sum_probs (mu pd) = sum_probs (mu pd_b) + sum_probs (mu pd_notb)). { 
            apply dst_sum_decom_by_b; try assumption. }
      rewrite Hsum_dec. rewrite dst_sum_prob_decom. apply Rplus_le_compat_r.
      apply Rle_trans with (r2:= sum_probs (mu pd0)).
      ++ apply NS_preserves_sum_probs_upper_bound with (c:= While b i); try assumption.
      -- apply NS_preserve_sum_ge0 with (c:= i) (pd:= pd_b); try assumption.
      --- apply sum_prob_get_b_ge0; try assumption. 
      --- apply positive_mu_by_b; try assumption.
      -- apply NS_preserve_positive_probs with (c:= i) (pd:= pd_b); try assumption.
      apply positive_mu_by_b; try assumption.
      ++ apply NS_preserves_sum_probs_upper_bound with (c:= i); try assumption.
      +++ apply sum_prob_get_b_ge0; try assumption. 
      +++ apply positive_mu_by_b; try assumption.
    + apply dst_positive_decom. split.
      * apply NS_preserve_positive_probs with (c:= While b i) (pd:= pd0); try assumption.
      apply NS_preserve_positive_probs with (c:= i) (pd:= pd_b); try assumption. 
      apply positive_mu_by_b; try assumption.
      * apply positive_mu_by_b; try assumption.
Qed. 

Lemma NS_preserve_sum_eq: forall c pd pd', 
  Valid_dist (mu pd) -> NS c pd pd' -> 
  sum_probs (mu pd) = sum_probs (mu pd').
Proof.
  intros c mu mu' Hvalid HNS. induction HNS; try reflexivity; try apply IHHNS; try assumption.
  - destruct pd. simpl. rewrite DA_preserve_sum_prob. reflexivity.
  - destruct pd. simpl. destruct Vda. destruct a. rewrite RA_preserve_sum_prob; try reflexivity. try assumption. 
  - apply Valid_forall_NS in HNS1; try assumption. 
    apply IHHNS1 in Hvalid. 
    rewrite Hvalid. apply IHHNS2. assumption.
  - simpl. apply pd_Nil_mu in H0. rewrite H0. simpl. reflexivity.
  - rewrite H4. rewrite dst_sum_decom_by_b with (b:= b). 
    + rewrite dst_sum_prob_decom. 
      destruct pd as [dom mu HPD]; destruct pd' as [dom' mu' HPD']; simpl in *.
      rewrite IHHNS1.
      * f_equal. apply IHHNS2. apply dst_Valid_get_notb. assumption.
      * apply dst_Valid_get_b. assumption.
    + destruct Hvalid as [Hsum Hpos]. destruct Hsum. assumption.
    + destruct Hvalid. assumption.
  - simpl. apply pd_Nil_mu in H0. rewrite H0. simpl. reflexivity. 
  - rewrite <- IHHNS2. 
    + apply IHHNS1; try assumption. 
    + apply Valid_forall_NS in HNS1; assumption.
  - rewrite H4. rewrite dst_sum_decom_by_b with (b:= b).
    + rewrite dst_sum_prob_decom. 
      destruct pd as [dom mu HPD]; destruct pd' as [dom' mu' HPD']; simpl in *.
      f_equal. rewrite IHHNS1.
      * apply IHHNS2. apply Valid_forall_NS in HNS1; try assumption. 
        apply dst_Valid_get_b. assumption.
      * apply dst_Valid_get_b. assumption.
    + destruct Hvalid as [Hsum Hpos]. destruct Hsum. assumption.
    + destruct Hvalid. assumption.
Qed. 

Lemma dom_equiv_preserves_WF_aexp: forall a pd pd', 
  (dom pd == dom pd')%domain ->
  WF_aexp_with_pd a pd ->
  WF_aexp_with_pd a pd'.
Proof.
  intros. unfold WF_aexp_with_pd in *. 
  apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
Qed.
Lemma dom_equiv_preserves_WF_distaexp: forall da pd pd', 
  (dom pd == dom pd')%domain ->
  WF_distaexp_with_pd da pd -> WF_distaexp_with_pd da pd'.
Proof.
  intros. induction da; try assumption.
  simpl. destruct a. simpl in H0. destruct H0. 
  split; try assumption.
  - apply dom_equiv_preserves_WF_aexp with (pd:= pd); try assumption.
  - apply IHda. assumption.
Qed.

Lemma dom_equiv_preserves_WF_bexp: forall b pd pd', 
  (dom pd == dom pd')%domain ->
  WF_bexp_with_pd b pd ->
  WF_bexp_with_pd b pd'.
Proof.
  intros. unfold WF_bexp_with_pd in *. 
  apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
Qed.

Lemma pd_equiv_preserves_WD_win: forall c pd pd', 
  Valid_dist (mu pd) -> Valid_dist (mu pd') ->
  pd ≡ pd' -> 
  well_defined_winstr_with_pd c pd ->
  well_defined_winstr_with_pd c pd'.
Proof.
  intros c pd pd'. intros Hv Hv' Heq HWD. 
  generalize dependent pd'. generalize dependent pd.
  induction c; intros; try apply I; try assumption.
  - destruct Heq. apply dom_equiv_preserves_WF_aexp with (pd:= pd); try assumption.
  - destruct Heq. destruct v. simpl in *. 
    apply dom_equiv_preserves_WF_distaexp with (pd:= pd); try assumption.
  - simpl. apply IHc1 with (pd:= pd); try assumption.
  - inversion HWD; subst. split.
    + destruct Heq. apply dom_equiv_preserves_WF_bexp with (pd:= pd); assumption.
    + rewrite <- dst_equiv_implies_b_classify with (pd0:= pd); try assumption.
      destruct (b_supp_classify b pd); try apply I. 
      * destruct H0. split. 
      ++ apply IHc1 with (pd:= pd); assumption.
      ++ apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c1 ); try assumption.
        apply dom_eq_orb_compat_right. destruct Heq. assumption.
      * destruct H0. split. 
      ++ apply IHc2 with (pd:= pd); assumption.
      ++ apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c2 ); try assumption.
        apply dom_eq_orb_compat_right. destruct Heq. assumption.
      * destruct H0. destruct H1. 
        split. 
        -- apply IHc1 with (pd:= (extract_b_pd b pd)); try apply dst_Valid_get_b; try assumption. 
          apply pd_eq_preserves_get_b; try assumption.
        -- split. 
          ** apply IHc2 with (pd:= (extract_notb_pd b pd)); try apply dst_Valid_get_notb; try assumption. 
          apply pd_eq_preserves_get_notb; try assumption.
          ** destruct H2. 
            ++ left; try assumption.
            ++ destruct H2. right. destruct Heq. 
              split; apply dom_subset_eq_compat_left with (X:= dom pd ); try assumption.
  - inversion HWD; subst. split. 
    + destruct Heq. apply dom_equiv_preserves_WF_bexp with (pd:= pd); assumption.
    + rewrite <- dst_equiv_implies_b_classify with (pd0:= pd); try assumption.
      destruct (b_supp_classify b pd); try apply I.
      * apply IHc with (pd:= pd); assumption.
      * destruct Heq. apply dom_subset_eq_compat_left with (X:= dom pd ); try assumption.
      * destruct H0. split. 
      ** apply IHc with (pd:= (extract_b_pd b pd)); try apply dst_Valid_get_b; try assumption.
        apply pd_eq_preserves_get_b; try assumption.
      ** destruct Heq. apply dom_subset_eq_compat_left with (X:= dom pd ); try assumption.
Qed.


Lemma pd_decom_r_preserves_WD_win: forall c pd pd0 pd1, 
  Valid_dist (mu pd) -> Valid_dist (mu pd0) -> Valid_dist (mu pd1) ->
  Valid_dist (mu pd0 + mu pd1)%dist_state ->
  (mu pd == mu pd0 + mu pd1)%dist_state ->
  (dom pd == dom pd0)%domain /\ (dom pd == dom pd1)%domain -> 
  well_defined_winstr_with_pd c pd -> 
  well_defined_winstr_with_pd c pd0. 
Proof.
  intros c pd pd0 pd1. intros Hv Hv0 Hv1 Hvadd Heq Hdom HWD. 
  generalize dependent pd1. generalize dependent pd0. generalize dependent pd.
  induction c; intros; try apply I; try assumption.
  - simpl in *. destruct Hdom. apply dom_equiv_preserves_WF_aexp with (pd:= pd); try assumption.
  - simpl in *. destruct Hdom. destruct v. 
    apply dom_equiv_preserves_WF_distaexp with (pd:= pd); try assumption.
  - simpl. simpl in HWD. apply IHc1 in Heq; try assumption.
  - destruct Hdom. inversion HWD; subst. split.
    + apply dom_equiv_preserves_WF_bexp with (pd:= pd); assumption.
    + unfold b_supp_classify. 
      destruct pd0 as [dom0 mu0 HPD0]. simpl in *.
      destruct (mu0) as [|(s0,p0) mu0']; try apply I. 
      destruct (b_supp_classify b pd) eqn: Hb.
      * apply pd_Nil_mu in Hb. rewrite Hb in Heq. 
      apply dst_equiv_sym in Heq. apply dst_cons_valid_contra in Heq; try assumption; contradiction.
      * pose (pd0:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
        assert (Htmp: forallb (fun s : local_st => evalB_st b s) (supp_mu ((s0, p0) :: mu0')) = true). { 
          apply bT_classify_decom_r with (b:= b) (pd0:= pd0) in Heq; try assumption.
          - unfold b_supp_classify in Heq. simpl in Heq. 
          destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s0, p0) :: mu0'))); try reflexivity.
          destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s0, p0) :: mu0'))); try discriminate.
          - simpl. unfold not. intros. discriminate. }
        rewrite Htmp. destruct H2. 
        specialize (IHc1 pd Hv H2 pd0 Hv0 pd1 Hv1 Hvadd Heq). split.
      ** apply IHc1. split; try assumption.
      ** apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c1 ); try assumption.
        apply dom_eq_orb_compat_right. assumption.
      * pose (pd0:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
        assert (Htmp: forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s0, p0) :: mu0')) = true). { 
          apply bF_classify_decom_r with (b:= b) (pd0:= pd0) in Heq; try assumption.
          - unfold b_supp_classify in Heq. simpl in Heq. 
          destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s0, p0) :: mu0'))); try discriminate.
          destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s0, p0) :: mu0'))); try discriminate.
          reflexivity.
          - simpl. unfold not. intros. discriminate. }
        rewrite Htmp. destruct H2. 
        specialize (IHc2 pd Hv H2 pd0 Hv0 pd1 Hv1 Hvadd Heq). 
        assert (Hymp: forallb (fun s : local_st => evalB_st b s) (supp_mu ((s0, p0) :: mu0')) = false). {
          unfold supp_mu in Htmp. simpl in Htmp. rewrite insert_st_pair_fst_eq_insert_st in Htmp. 
          rewrite supp_insert_negbevalB in Htmp. apply andb_true_iff in Htmp. destruct Htmp. 
          unfold supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st. 
          rewrite supp_insert_evalB. apply negb_true_iff in H4. rewrite H4. simpl. reflexivity. } 
        rewrite Hymp. split.
      ** apply IHc2. split; try assumption.
      ** apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c2 ); try assumption.
        apply dom_eq_orb_compat_right. assumption.
      * destruct H2. destruct H3.
        assert (Hb_eq: get_b_in_mu b (mu pd) == get_b_in_mu b ((((s0, p0) :: mu0') + mu pd1)%dist_state)). {
          apply Peq_implies_get_b_Peq with (b:= b) in Heq; try assumption. }
        assert (Hnotb_eq: get_notb_in_mu b (mu pd) == get_notb_in_mu b ((((s0, p0) :: mu0') + mu pd1)%dist_state)). {
          apply Peq_implies_get_notb_Peq with (b:= b) in Heq; try assumption. }
        destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s0, p0) :: mu0'))) eqn: HbT. 
        { split. 
          - apply IHc1 with (pd:= (extract_b_pd b pd)) (pd1:= (extract_b_pd b pd1)); try apply dst_Valid_get_b; try assumption. 
            + simpl. rewrite dst_cons_eq_add. rewrite dst_add_assoc_eq. rewrite <- dst_cons_eq_add. 
              rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq. 
              apply Valid_linear_under_eq_prob; try apply dst_Valid_get_b; try assumption; try apply Rle_0_1.
              repeat rewrite Rmult_1_l. split. 
              * destruct Hv0. destruct H5. 
                apply dst_Valid_get_b with (b:= b) in Hv1. destruct Hv1. destruct H8.
                apply Rplus_le_le_0_compat; assumption.
              * apply Rle_trans with (r2:= sum_probs (((s0, p0) :: mu0') + (mu pd1))%dist_state). 
                ++ rewrite dst_sum_prob_decom. apply Rplus_le_compat_l. apply sum_prob_get_b_le. assumption.
                ++ destruct Hvadd. destruct H5. assumption.
            + simpl. 
              assert (Haddb: (get_b_in_mu b (((s0, p0) :: mu0') + mu pd1) == 
                  (((s0, p0) :: mu0') + get_b_in_mu b (mu pd1)))%dist_state). {
                  rewrite get_b_assoc. apply dst_add_inj_r. simpl. 
                  unfold supp_mu in HbT. simpl in HbT. rewrite insert_st_pair_fst_eq_insert_st in HbT.
                  rewrite supp_insert_evalB in HbT. apply andb_true_iff in HbT. destruct HbT.
                  rewrite H5. rewrite dst_cons_eq_add. rewrite dst_cons_eq_add with (mu:= mu0').
                  apply dst_add_inj_l. 
                  apply dst_equiv_trans with (mu1:= get_b_in_mu b (sort_dst mu0')); (try apply dst_eq_getb_sorted; try assumption).
                  - apply Valid_dist_inv in Hv0. assumption.
                  - apply forallb_getb_eq in H6. rewrite H6. apply dst_equiv_sym. apply dst_equiv_sort. }
              apply dst_equiv_trans with (mu1:= get_b_in_mu b (((s0, p0) :: mu0') + mu pd1)%dist_state); try assumption.
            + simpl. split; try assumption.
          - destruct H4. 
            + destruct H4. apply dom_subset_orb_dom_l. assumption. 
            + destruct H4. 
              apply dom_subset_eq_compat_left with (Z:= get_modvar_in_winstr c2) in H; try assumption.
              apply dom_subset_orb_dom_r. assumption. }
        destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s0, p0) :: mu0'))) eqn: HbF. 
        { split.
          - apply IHc2 with (pd:= (extract_notb_pd b pd)) (pd1:= (extract_notb_pd b pd1)); try apply dst_Valid_get_notb; try assumption.
            + simpl. rewrite dst_cons_eq_add. rewrite dst_add_assoc_eq. rewrite <- dst_cons_eq_add. 
              rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq. 
              apply Valid_linear_under_eq_prob; try apply dst_Valid_get_notb; try assumption; try apply Rle_0_1.
              repeat rewrite Rmult_1_l. split. 
              * destruct Hv0. destruct H5. 
                apply dst_Valid_get_notb with (b:= b) in Hv1. destruct Hv1. destruct H8.
                apply Rplus_le_le_0_compat; assumption.
              * apply Rle_trans with (r2:= sum_probs (((s0, p0) :: mu0') + (mu pd1))%dist_state). 
                ++ rewrite dst_sum_prob_decom. apply Rplus_le_compat_l. 
                  apply sum_prob_get_notb_le. assumption.
                ++ destruct Hvadd. destruct H5. assumption.
            + simpl. 
              assert (Haddnotb: (get_notb_in_mu b (((s0, p0) :: mu0') + mu pd1) == 
                (((s0, p0) :: mu0') + get_notb_in_mu b (mu pd1)))%dist_state). {
                  rewrite get_notb_assoc. apply dst_add_inj_r. simpl. 
                  unfold supp_mu in HbF. simpl in HbF. rewrite insert_st_pair_fst_eq_insert_st in HbF.
                  rewrite supp_insert_negbevalB in HbF. apply andb_true_iff in HbF. destruct HbF.
                  rewrite H5. rewrite dst_cons_eq_add. rewrite dst_cons_eq_add with (mu:= mu0').
                  apply dst_add_inj_l. 
                  apply dst_equiv_trans with (mu1:= get_notb_in_mu b (sort_dst mu0')); (try apply dst_eq_getnotb_sorted; try assumption).
                  - apply Valid_dist_inv in Hv0. assumption.
                  - apply forallb_getnotb_eq in H6. rewrite H6. apply dst_equiv_sym. apply dst_equiv_sort. }
              apply dst_equiv_trans with (mu1:= get_notb_in_mu b (((s0, p0) :: mu0') + mu pd1)%dist_state); try assumption.
            + simpl. split; try assumption.
          - destruct H4. 
            + destruct H4. apply dom_subset_orb_dom_l. assumption. 
            + destruct H4. 
              apply dom_subset_eq_compat_left with (Z:= get_modvar_in_winstr c1) in H; try assumption.
              apply dom_subset_orb_dom_r. assumption. }
        split.
        ** apply IHc1 with (pd:= (extract_b_pd b pd)) (pd1:= (extract_b_pd b pd1)); try apply dst_Valid_get_b; try assumption.
          -- rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq. 
            apply Valid_linear_under_eq_prob; try apply dst_Valid_get_b; try assumption; try apply Rle_0_1.
            repeat rewrite Rmult_1_l. split. 
            ++ apply dst_Valid_get_b with (b:= b) in Hv1. destruct Hv1. destruct H5.
               apply dst_Valid_get_b with (b:= b) in Hv0. destruct Hv0. destruct H8.
                apply Rplus_le_le_0_compat; assumption.
            ++ apply Rle_trans with (r2:= sum_probs (((s0, p0) :: mu0') + (mu pd1))%dist_state). 
              +++ rewrite dst_sum_prob_decom. 
                apply Rplus_le_compat; apply sum_prob_get_b_le; assumption.
              +++ destruct Hvadd. destruct H5. assumption.
          -- rewrite get_b_assoc in Hb_eq. simpl in Hb_eq. simpl. assumption. 
          -- simpl. split; try assumption.
        ** split.
          -- apply IHc2 with (pd:= (extract_notb_pd b pd)) (pd1:= (extract_notb_pd b pd1)); try apply dst_Valid_get_notb; try assumption.
            ++ rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq. 
              apply Valid_linear_under_eq_prob; try apply dst_Valid_get_notb; try assumption; try apply Rle_0_1.
              repeat rewrite Rmult_1_l. split. 
              +++ apply dst_Valid_get_notb with (b:= b) in Hv1. destruct Hv1. destruct H5.
                  apply dst_Valid_get_notb with (b:= b) in Hv0. destruct Hv0. destruct H8.
                  apply Rplus_le_le_0_compat; assumption.
              +++ apply Rle_trans with (r2:= sum_probs (((s0, p0) :: mu0') + (mu pd1))%dist_state). 
                --- rewrite dst_sum_prob_decom. 
                    apply Rplus_le_compat; apply sum_prob_get_notb_le; assumption.
                --- destruct Hvadd. destruct H5. assumption.
            ++ rewrite get_notb_assoc in Hnotb_eq. simpl in Hnotb_eq. simpl. assumption. 
            ++ simpl. split; try assumption.
          -- destruct H4. 
            ++ left. assumption.
            ++ right. destruct H4. split; apply dom_subset_eq_compat_left with (X:= dom pd ); try assumption.
  - destruct Hdom. inversion HWD; subst. split.
    + apply dom_equiv_preserves_WF_bexp with (pd:= pd); assumption.
    + unfold b_supp_classify. 
      destruct pd0 as [dom0 mu0 HPD0]. simpl in *.
      destruct (mu0) as [|(s0,p0) mu0']; try apply I. 
      destruct (b_supp_classify b pd) eqn: Hb.
      * apply pd_Nil_mu in Hb. rewrite Hb in Heq. 
      apply dst_equiv_sym in Heq. apply dst_cons_valid_contra in Heq; try assumption; contradiction.
      * pose (pd0:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
        assert (Htmp: forallb (fun s : local_st => evalB_st b s) (supp_mu ((s0, p0) :: mu0')) = true). { 
          apply bT_classify_decom_r with (b:= b) (pd0:= pd0) in Heq; try assumption.
          - unfold b_supp_classify in Heq. simpl in Heq. 
          destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s0, p0) :: mu0'))); try reflexivity.
          destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s0, p0) :: mu0'))); try discriminate.
          - simpl. unfold not. intros. discriminate. }
        rewrite Htmp. 
        specialize (IHc pd Hv H2 pd0 Hv0 pd1 Hv1 Hvadd Heq). 
      ** apply IHc. split; try assumption.
      * pose (pd0:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
        assert (Htmp: forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s0, p0) :: mu0')) = true). { 
          apply bF_classify_decom_r with (b:= b) (pd0:= pd0) in Heq; try assumption.
          - unfold b_supp_classify in Heq. simpl in Heq. 
          destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s0, p0) :: mu0'))); try discriminate.
          destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s0, p0) :: mu0'))); try discriminate.
          reflexivity.
          - simpl. unfold not. intros. discriminate. }
        rewrite Htmp.  
        assert (Hymp: forallb (fun s : local_st => evalB_st b s) (supp_mu ((s0, p0) :: mu0')) = false). {
          unfold supp_mu in Htmp. simpl in Htmp. rewrite insert_st_pair_fst_eq_insert_st in Htmp. 
          rewrite supp_insert_negbevalB in Htmp. apply andb_true_iff in Htmp. destruct Htmp. 
          unfold supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st. 
          rewrite supp_insert_evalB. apply negb_true_iff in H3. rewrite H3. simpl. reflexivity. } 
        rewrite Hymp. 
        apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
      * destruct H2. 
        assert (Hb_eq: get_b_in_mu b (mu pd) == get_b_in_mu b ((((s0, p0) :: mu0') + mu pd1)%dist_state)). {
          apply Peq_implies_get_b_Peq with (b:= b) in Heq; try assumption. }
        assert (Hnotb_eq: get_notb_in_mu b (mu pd) == get_notb_in_mu b ((((s0, p0) :: mu0') + mu pd1)%dist_state)). {
          apply Peq_implies_get_notb_Peq with (b:= b) in Heq; try assumption. }
        destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s0, p0) :: mu0'))) eqn: HbT. 
        { apply IHc with (pd:= (extract_b_pd b pd)) (pd1:= (extract_b_pd b pd1)); try apply dst_Valid_get_b; try assumption. 
          + simpl. rewrite dst_cons_eq_add. rewrite dst_add_assoc_eq. rewrite <- dst_cons_eq_add. 
            rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq. 
            apply Valid_linear_under_eq_prob; try apply dst_Valid_get_b; try assumption; try apply Rle_0_1.
            repeat rewrite Rmult_1_l. split. 
            * destruct Hv0. destruct H4. 
              apply dst_Valid_get_b with (b:= b) in Hv1. destruct Hv1. destruct H7.
              apply Rplus_le_le_0_compat; assumption.
            * apply Rle_trans with (r2:= sum_probs (((s0, p0) :: mu0') + (mu pd1))%dist_state). 
              - rewrite dst_sum_prob_decom. apply Rplus_le_compat_l. apply sum_prob_get_b_le. assumption.
              - destruct Hvadd. destruct H4. assumption.
          + simpl. 
            assert (Haddb: (get_b_in_mu b (((s0, p0) :: mu0') + mu pd1) == 
                  (((s0, p0) :: mu0') + get_b_in_mu b (mu pd1)))%dist_state). {
                  rewrite get_b_assoc. apply dst_add_inj_r. simpl. 
                  unfold supp_mu in HbT. simpl in HbT. rewrite insert_st_pair_fst_eq_insert_st in HbT.
                  rewrite supp_insert_evalB in HbT. apply andb_true_iff in HbT. destruct HbT.
                  rewrite H4. rewrite dst_cons_eq_add. rewrite dst_cons_eq_add with (mu:= mu0').
                  apply dst_add_inj_l. 
                  apply dst_equiv_trans with (mu1:= get_b_in_mu b (sort_dst mu0')); (try apply dst_eq_getb_sorted; try assumption).
                  - apply Valid_dist_inv in Hv0. assumption.
                  - apply forallb_getb_eq in H5. rewrite H5. apply dst_equiv_sym. apply dst_equiv_sort. }
            apply dst_equiv_trans with (mu1:= get_b_in_mu b (((s0, p0) :: mu0') + mu pd1)%dist_state); try assumption.
          + simpl. split; try assumption. }
        destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s0, p0) :: mu0'))) eqn: HbF. 
        { apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
        split.
        ** apply IHc with (pd:= (extract_b_pd b pd)) (pd1:= (extract_b_pd b pd1)); try apply dst_Valid_get_b; try assumption.
          -- rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq. 
            apply Valid_linear_under_eq_prob; try apply dst_Valid_get_b; try assumption; try apply Rle_0_1.
            repeat rewrite Rmult_1_l. split. 
            ++ apply dst_Valid_get_b with (b:= b) in Hv1. destruct Hv1. destruct H4.
               apply dst_Valid_get_b with (b:= b) in Hv0. destruct Hv0. destruct H7.
               apply Rplus_le_le_0_compat; assumption.
            ++ apply Rle_trans with (r2:= sum_probs (((s0, p0) :: mu0') + (mu pd1))%dist_state). 
              +++ rewrite dst_sum_prob_decom. 
                apply Rplus_le_compat; apply sum_prob_get_b_le; assumption.
              +++ destruct Hvadd. destruct H4. assumption.
          -- rewrite get_b_assoc in Hb_eq. simpl in Hb_eq. simpl. assumption. 
          -- simpl. split; try assumption.
        ** apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.  
Qed.

Lemma pd_decom_l_preserves_WD_win: forall c pd pd0 pd1, 
  Valid_dist (mu pd) -> Valid_dist (mu pd0) -> Valid_dist (mu pd1) ->
  Valid_dist (mu pd0 + mu pd1)%dist_state ->
  (mu pd == mu pd0 + mu pd1)%dist_state ->
  (dom pd == dom pd0)%domain /\ (dom pd == dom pd1)%domain -> 
  well_defined_winstr_with_pd c pd -> 
  well_defined_winstr_with_pd c pd1.
Proof.
  intros c pd pd0 pd1. intros Hv Hv0 Hv1 Hvadd Heq Hdom HWD. 
  apply dst_equiv_trans with (mu0:= mu pd) (mu2:= (mu pd1 + mu pd0)%dist_state) in Heq; try apply dst_add_comm; try apply dst_equiv_refl.
  apply pd_decom_r_preserves_WD_win with (c:= c) in Heq; try assumption; intuition.
  rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq. 
  apply Valid_linear_under_eq_prob; try assumption; try apply Rle_0_1.
  repeat rewrite Rmult_1_l. rewrite Rplus_comm. rewrite <- dst_sum_prob_decom.
  destruct Hvadd. assumption. 
Qed.

Lemma pd_mult_coef_dom_r_preserves_WD_win: forall c pd p, 
  Valid_dist (mu pd) -> 0 < p < 1 ->
  well_defined_winstr_with_pd c pd <->
  well_defined_winstr_with_pd c (cofe_pd pd p).
Proof.
  split. {
  intros HWD. rename H into Hv. destruct H0 as [Hp0 Hp1]. generalize dependent pd.
  induction c; simpl; intros; try apply I.
  - apply WF_aexp_mult_coef; try assumption.
  - destruct v. apply WF_distaexp_mult_coef; try assumption.
  - apply IHc1; try assumption.
  - inversion HWD; subst. split; try assumption.
    rewrite b_classify_mult_coef; try assumption.
    destruct (b_supp_classify b pd); try assumption.
    + destruct H0. split; try assumption. apply IHc1; assumption.
    + destruct H0. split; try assumption. apply IHc2; assumption.
    + destruct H0. destruct H1. 
      assert (Hvb: Valid_dist (get_b_in_mu b (mu pd))). { apply dst_Valid_get_b; assumption. }
      assert (Hvbnot: Valid_dist (get_notb_in_mu b (mu pd))). { apply dst_Valid_get_notb; assumption. }
      split; try assumption. 
      * apply pd_equiv_preserves_WD_win with (pd:= (cofe_pd (extract_b_pd b pd) p)).
      ** try apply Valid_mult_under_eq_prob; simpl; try apply dst_Valid_get_b; try apply Rlt_le; try assumption.
        destruct Hvb. destruct H3. rewrite dst_sum_prob_coef_mult. split.
        -- apply Rmult_le_pos; try assumption. apply Rlt_le. assumption. 
        -- apply Rle_trans with (r2:= sum_probs (get_b_in_mu b (mu pd))%dist_state); try assumption. 
        rewrite <- Rmult_1_l. apply Rmult_le_compat_r; try assumption. apply Rlt_le. assumption. 
      ** simpl. try apply Valid_mult_under_eq_prob; simpl; try apply dst_Valid_get_b; try apply Rlt_le; try assumption.
        apply Valid_mult_under_eq_prob; simpl; try apply dst_Valid_get_b; try apply Rlt_le; try assumption.
        destruct Hv. destruct H3. rewrite dst_sum_prob_coef_mult. split.
        -- apply Rmult_le_pos; try assumption. apply Rlt_le. assumption. 
        -- apply Rle_trans with (r2:= sum_probs ((mu pd))%dist_state); try assumption. 
        rewrite <- Rmult_1_l. apply Rmult_le_compat_r; try assumption. apply Rlt_le. assumption. 
      ** split; simpl; try apply dom_equiv_refl. rewrite dst_get_b_coef_mult. apply dst_equiv_refl.
      ** apply IHc1; try assumption. 
      * split. {
        apply pd_equiv_preserves_WD_win with (pd:= (cofe_pd (extract_notb_pd b pd) p)).
      ** try apply Valid_mult_under_eq_prob; simpl; try apply dst_Valid_get_notb; try apply Rlt_le; try assumption.
        destruct Hvbnot. destruct H3. rewrite dst_sum_prob_coef_mult. split.
        -- apply Rmult_le_pos; try assumption. apply Rlt_le. assumption. 
        -- apply Rle_trans with (r2:= sum_probs (get_notb_in_mu b (mu pd))%dist_state); try assumption. 
        rewrite <- Rmult_1_l. apply Rmult_le_compat_r; try assumption. apply Rlt_le. assumption. 
      ** simpl. try apply Valid_mult_under_eq_prob; simpl; try apply dst_Valid_get_notb; try apply Rlt_le; try assumption.
        apply Valid_mult_under_eq_prob; simpl; try apply dst_Valid_get_b; try apply Rlt_le; try assumption.
        destruct Hv. destruct H3. rewrite dst_sum_prob_coef_mult. split.
        -- apply Rmult_le_pos; try assumption. apply Rlt_le. assumption. 
        -- apply Rle_trans with (r2:= sum_probs ((mu pd))%dist_state); try assumption. 
        rewrite <- Rmult_1_l. apply Rmult_le_compat_r; try assumption. apply Rlt_le. assumption. 
      ** split; simpl; try apply dom_equiv_refl. rewrite dst_get_notb_coef_mult. apply dst_equiv_refl.
      ** apply IHc2; try assumption. 
      }
      assumption.
  - inversion HWD; subst. split; try assumption.
    rewrite b_classify_mult_coef; try assumption.
    destruct (b_supp_classify b pd); try assumption.
    + apply IHc; assumption.
    + destruct H0. split; try assumption. 
      assert (Hvb: Valid_dist (get_b_in_mu b (mu pd))). { apply dst_Valid_get_b; assumption. }
      assert (Hvbnot: Valid_dist (get_notb_in_mu b (mu pd))). { apply dst_Valid_get_notb; assumption. }
      apply pd_equiv_preserves_WD_win with (pd:= (cofe_pd (extract_b_pd b pd) p)).
      * try apply Valid_mult_under_eq_prob; simpl; try apply dst_Valid_get_b; try apply Rlt_le; try assumption.
        destruct Hvb. destruct H2. rewrite dst_sum_prob_coef_mult. split.
        -- apply Rmult_le_pos; try assumption. apply Rlt_le. assumption. 
        -- apply Rle_trans with (r2:= sum_probs (get_b_in_mu b (mu pd))%dist_state); try assumption. 
        rewrite <- Rmult_1_l. apply Rmult_le_compat_r; try assumption. apply Rlt_le. assumption. 
      * simpl. try apply Valid_mult_under_eq_prob; simpl; try apply dst_Valid_get_b; try apply Rlt_le; try assumption.
        apply Valid_mult_under_eq_prob; simpl; try apply dst_Valid_get_b; try apply Rlt_le; try assumption.
        destruct Hv. destruct H2. rewrite dst_sum_prob_coef_mult. split.
        -- apply Rmult_le_pos; try assumption. apply Rlt_le. assumption. 
        -- apply Rle_trans with (r2:= sum_probs ((mu pd))%dist_state); try assumption. 
        rewrite <- Rmult_1_l. apply Rmult_le_compat_r; try assumption. apply Rlt_le. assumption. 
      * split; simpl; try apply dom_equiv_refl. rewrite dst_get_b_coef_mult. apply dst_equiv_refl.
      * apply IHc; assumption. }
  intros HWD. rename H into Hv. destruct H0 as [Hp0 Hp1]. generalize dependent pd.
  induction c; simpl; intros; try apply I.
  - apply WF_aexp_mult_coef in HWD; try assumption.
  - destruct v. apply WF_distaexp_mult_coef in HWD; try assumption.
  - apply IHc1; try assumption.
  - inversion HWD; subst. split; try assumption.
    rewrite b_classify_mult_coef in H0; try assumption.
    destruct (b_supp_classify b pd); try assumption.
    + destruct H0. split; try assumption. apply IHc1; assumption.
    + destruct H0. split; try assumption. apply IHc2; assumption.
    + destruct H0. destruct H1. 
      assert (Hvb: Valid_dist (get_b_in_mu b (mu pd))). { apply dst_Valid_get_b; assumption. }
      assert (Hvbnot: Valid_dist (get_notb_in_mu b (mu pd))). { apply dst_Valid_get_notb; assumption. }
      split; try assumption. 
      * apply IHc1; try assumption.
      apply pd_equiv_preserves_WD_win with (pd:= (extract_b_pd b (cofe_pd pd p))); try assumption.
      ** try apply Valid_mult_under_eq_prob; simpl; try apply dst_Valid_get_b; try apply Rlt_le; try assumption.
        try apply Valid_mult_under_eq_prob; simpl; try apply Rlt_le; try assumption.
        destruct Hv. destruct H3. rewrite dst_sum_prob_coef_mult. split.
        -- apply Rmult_le_pos; try assumption. apply Rlt_le. assumption. 
        -- apply Rle_trans with (r2:= sum_probs (mu pd)%dist_state); try assumption. 
        rewrite <- Rmult_1_l. apply Rmult_le_compat_r; try assumption. apply Rlt_le. assumption. 
      ** simpl. try apply Valid_mult_under_eq_prob; simpl; try apply dst_Valid_get_b; try apply Rlt_le; try assumption.
        apply Valid_mult_under_eq_prob; simpl; try apply dst_Valid_get_b; try apply Rlt_le; try assumption.
        destruct Hvb. destruct H3. rewrite dst_sum_prob_coef_mult. split.
        -- apply Rmult_le_pos; try assumption. apply Rlt_le. assumption. 
        -- apply Rle_trans with (r2:= sum_probs (get_b_in_mu b (mu pd))%dist_state); try assumption. 
        rewrite <- Rmult_1_l. apply Rmult_le_compat_r; try assumption. apply Rlt_le. assumption. 
      ** split; simpl; try apply dom_equiv_refl. rewrite dst_get_b_coef_mult. apply dst_equiv_refl.
      * split. {
        apply IHc2; try assumption. 
        apply pd_equiv_preserves_WD_win with (pd:= (extract_notb_pd b (cofe_pd pd p))); try assumption.
      ** try apply Valid_mult_under_eq_prob; simpl; try apply dst_Valid_get_notb; try apply Rlt_le; try assumption.
        try apply Valid_mult_under_eq_prob; simpl; try apply Rlt_le; try assumption.
        destruct Hv. destruct H3. rewrite dst_sum_prob_coef_mult. split.
        -- apply Rmult_le_pos; try assumption. apply Rlt_le. assumption. 
        -- apply Rle_trans with (r2:= sum_probs ((mu pd))%dist_state); try assumption. 
        rewrite <- Rmult_1_l. apply Rmult_le_compat_r; try assumption. apply Rlt_le. assumption. 
      ** simpl. try apply Valid_mult_under_eq_prob; simpl; try apply dst_Valid_get_notb; try apply Rlt_le; try assumption.
        apply Valid_mult_under_eq_prob; simpl; try apply dst_Valid_get_b; try apply Rlt_le; try assumption.
        destruct Hvbnot. destruct H3. rewrite dst_sum_prob_coef_mult. split.
        -- apply Rmult_le_pos; try assumption. apply Rlt_le. assumption. 
        -- apply Rle_trans with (r2:= sum_probs ((get_notb_in_mu b (mu pd)))%dist_state); try assumption. 
        rewrite <- Rmult_1_l. apply Rmult_le_compat_r; try assumption. apply Rlt_le. assumption. 
      ** split; simpl; try apply dom_equiv_refl. rewrite dst_get_notb_coef_mult. apply dst_equiv_refl.
      }
      assumption.
  - inversion HWD; subst. split; try assumption.
    rewrite b_classify_mult_coef in H0; try assumption.
    destruct (b_supp_classify b pd); try assumption.
    + apply IHc; assumption.
    + destruct H0. split; try assumption. 
      assert (Hvb: Valid_dist (get_b_in_mu b (mu pd))). { apply dst_Valid_get_b; assumption. }
      assert (Hvbnot: Valid_dist (get_notb_in_mu b (mu pd))). { apply dst_Valid_get_notb; assumption. }
      apply IHc; try assumption.
      apply pd_equiv_preserves_WD_win with (pd:= (extract_b_pd b (cofe_pd pd p))); try assumption.
      * try apply Valid_mult_under_eq_prob; simpl; try apply dst_Valid_get_b; try apply Rlt_le; try assumption.
        try apply Valid_mult_under_eq_prob; simpl; try apply dst_Valid_get_b; try apply Rlt_le; try assumption.
        destruct Hv. destruct H2. rewrite dst_sum_prob_coef_mult. split.
        -- apply Rmult_le_pos; try assumption. apply Rlt_le. assumption. 
        -- apply Rle_trans with (r2:= sum_probs ((mu pd))%dist_state); try assumption. 
        rewrite <- Rmult_1_l. apply Rmult_le_compat_r; try assumption. apply Rlt_le. assumption. 
      * simpl. try apply Valid_mult_under_eq_prob; simpl; try apply dst_Valid_get_b; try apply Rlt_le; try assumption.
        apply Valid_mult_under_eq_prob; simpl; try apply dst_Valid_get_b; try apply Rlt_le; try assumption.
        destruct Hvb. destruct H2. rewrite dst_sum_prob_coef_mult. split.
        -- apply Rmult_le_pos; try assumption. apply Rlt_le. assumption. 
        -- apply Rle_trans with (r2:= sum_probs ((get_b_in_mu b (mu pd)))%dist_state); try assumption. 
        rewrite <- Rmult_1_l. apply Rmult_le_compat_r; try assumption. apply Rlt_le. assumption. 
      * split; simpl; try apply dom_equiv_refl. rewrite dst_get_b_coef_mult. apply dst_equiv_refl.
Qed.

Lemma pd_linear_decom_r_preserve_WD_win: forall c pd pd0 pd1 p, 
  0 < p < 1 ->
  Valid_dist (mu pd) -> Valid_dist (mu pd0) -> Valid_dist (mu pd1) ->
  Valid_dist (p * mu pd0 + (1 - p) * mu pd1)%dist_state ->
  mu pd == (p * mu pd0 + (1 - p) * mu pd1)%dist_state ->
  (dom pd == dom pd0)%domain /\ (dom pd == dom pd1)%domain -> 
  well_defined_winstr_with_pd c pd -> 
  well_defined_winstr_with_pd c pd0.
Proof.
  intros c pd pd0 pd1 p Hp Hpd Hpd0 Hpd1 Hpd0p Hpd0p' Hdom HWD.
  destruct Hdom. 
  assert (Hdom': (dom (cofe_pd (pd0) p) == dom (cofe_pd (pd1) (1-p)))%domain). {
    simpl. apply dom_equiv_sym in H. apply dom_equiv_trans with (l1:= dom pd); assumption. }
  apply pd_equiv_preserves_WD_win with (pd':= pd_add (cofe_pd (pd0) p) (cofe_pd (pd1) (1-p)) Hdom') in HWD; try assumption.
  - apply pd_decom_r_preserves_WD_win with (pd0:=(cofe_pd pd0 p)) (pd1:= (cofe_pd pd1 (1-p))) in HWD; try assumption.
    + apply pd_mult_coef_dom_r_preserves_WD_win in HWD; try assumption.
    + simpl. apply Valid_mult_cofe; try assumption. apply Rbound_loss. assumption.
    + simpl. apply Valid_mult_cofe; try assumption. apply Rbound_loss. apply Rp_lt1_minus_p_bounds with (p:= p). assumption.
    + simpl. apply dst_equiv_refl.
    + simpl. split; try assumption. apply dom_equiv_refl.
  - split; simpl; try assumption. 
Qed.

Lemma pd_linear_decom_l_preserve_WD_win: forall c pd pd0 pd1 p, 
  0 < p < 1 ->
  Valid_dist (mu pd) -> Valid_dist (mu pd0) -> Valid_dist (mu pd1) ->
  Valid_dist (p * mu pd0 + (1 - p) * mu pd1)%dist_state ->
  mu pd == (p * mu pd0 + (1 - p) * mu pd1)%dist_state ->
  (dom pd == dom pd0)%domain /\ (dom pd == dom pd1)%domain -> 
  well_defined_winstr_with_pd c pd -> 
  well_defined_winstr_with_pd c pd1.
Proof.
  intros c pd pd0 pd1 p Hp Hpd Hpd0 Hpd1 Hpd0p Hadd Hdom HWD.
  assert (Hp1: (1- (1 - p)) = p). { field. }
  apply dst_equiv_trans with (mu2:= ((1 - p) * mu pd1 + (1- (1 - p)) * mu pd0)%dist_state) in Hadd. 
  - apply pd_linear_decom_r_preserve_WD_win with (c:= c) in Hadd; try assumption.
    + apply Rp_lt1_minus_p_bounds with (p:= p). assumption.
    + apply Valid_linear; try assumption. 
      * apply Rp_1_minus_p_bounds. apply Rbound_loss. assumption.
      * apply Rbound_loss. rewrite Hp1. assumption.
      * rewrite Hp1. unfold Rminus. rewrite Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_r. apply Rle_refl.
    + destruct Hdom. split; try assumption.
  - rewrite Hp1. apply dst_add_comm.
Qed.

Lemma bMixed_implies_neq_nil: forall b pd,
  b_supp_classify b pd = Mixed -> 
  get_b_in_mu b (mu pd) <> [] /\ get_notb_in_mu b (mu pd) <> [].
Proof.
  intros b pd H. destruct pd as [dom mu HPD]. 
  unfold b_supp_classify in H.
  induction mu as [|(s,p) mu' IH]; simpl in *; try discriminate.
  unfold supp_mu in H. simpl in H. rewrite insert_st_pair_fst_eq_insert_st in H.
  rewrite supp_insert_evalB in H. rewrite supp_insert_negbevalB in H.
  destruct (evalB_st b s && forallb (fun s : local_st => evalB_st b s) (map fst (sort_dst mu'))) eqn: HT; try discriminate.
  destruct (negb (evalB_st b s) && forallb (fun s : local_st => negb (evalB_st b s)) (map fst (sort_dst mu'))) eqn: HF; try discriminate.
  destruct mu' as [|(s',p') mu'].
    + simpl in *. destruct (evalB_st b s); try discriminate.
    + simpl in *. 
      rewrite insert_st_pair_fst_eq_insert_st in HT. rewrite supp_insert_evalB in HT. 
      rewrite insert_st_pair_fst_eq_insert_st in HF. rewrite supp_insert_negbevalB in HF.
      destruct ( evalB_st b s) eqn: Hs; destruct (evalB_st b s') eqn: Hs'; simpl in *.
      * split. 
      ** unfold not. intros. discriminate H0.
      ** inversion HPD; subst. apply IH; try assumption.
      unfold supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st. 
      rewrite supp_insert_evalB. rewrite supp_insert_negbevalB. 
      rewrite Hs'. simpl. rewrite HT. reflexivity.
      * unfold not. split; intros; discriminate H0.
      * unfold not. split; intros; discriminate H0.
      * split. 
      ** inversion HPD; subst. apply IH; try assumption. 
      unfold supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st. 
      rewrite supp_insert_evalB. rewrite supp_insert_negbevalB. 
      rewrite Hs'. simpl. rewrite HF. reflexivity.
      ** unfold not. intros. discriminate H0.
Qed.


(*******************************)
Lemma orbdom_after_NS: forall i pd pd', 
  NS i pd pd' -> (dom pd' == (dom pd) ∪ (get_modvar_in_winstr i))%domain.
Proof.
  intros. rename H into HNS.
  generalize dependent pd'. generalize dependent pd. 
  induction i; intros.
  - inversion HNS; subst. simpl in *. rewrite orb_domain_nil_r. apply dom_equiv_refl.
  - inversion HNS; subst. simpl in *. apply dom_equiv_refl.
  - inversion HNS; subst. simpl in *. apply dom_equiv_refl.
  - inversion HNS; subst. simpl in *.
    apply IHi1 in H3. apply IHi2 in H6. 
    apply dom_equiv_trans with (l1:= (dom pd1 ∪ get_modvar_in_winstr i2)%domain); try assumption. 
    rewrite orb_domain_assoc. apply dom_eq_orb_compat_right. assumption.
  - inversion HNS; subst; simpl in *; try apply dom_equiv_refl. 
    + apply IHi1 in H9. 
      apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr i1)%domain); try assumption.
      rewrite orb_domain_assoc. apply orb_domain_elim_r. assumption.
    + apply IHi2 in H9. 
      apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr i2)%domain); try assumption.
      rewrite orb_domain_comm with (l:= get_modvar_in_winstr i1). 
      rewrite orb_domain_assoc. apply orb_domain_elim_r. assumption.
    + apply IHi1 in H7. apply IHi2 in H8. simpl in *. 
      apply dom_equiv_trans with (l1:= dom pd1); try assumption.
      apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr i1)%domain); try assumption.
      destruct H6. 
      * apply dom_eq_orb_compat_left. apply orb_domain_elim_r. destruct H. assumption.
      * destruct H. apply dom_equiv_trans with (l1:= dom pd); try assumption. 
      ** apply dom_equiv_sym. apply orb_domain_elim_r. assumption.
      ** apply orb_domain_elim_r; apply dom_subset_orb_fst_iff; split; assumption.
  - remember (While b i) as original_command eqn:Horig.
    induction HNS; try inversion Horig; subst; intros; try apply dom_equiv_refl.
    + apply IHi in HNS1. apply IHHNS2 in Horig. 
      simpl in *. 
      apply dom_equiv_trans with (l1:= (dom pd1 ∪ get_modvar_in_winstr i)%domain); try assumption.
      apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr i ∪ get_modvar_in_winstr i)%domain); try assumption.
      * apply dom_eq_orb_compat_right. assumption.
      * apply dom_equiv_sym. apply orb_domain_elim_r. apply dom_subset_orb_snd_l_r.
    + simpl in *. apply orb_domain_elim_r. assumption.
    + simpl in *. apply IHi in HNS1. apply IHHNS2 in Horig. 
      apply dom_equiv_trans with (l1:= dom pd1); try assumption.
      apply dom_equiv_trans with (l1:= (dom pd0 ∪ get_modvar_in_winstr i)%domain); try assumption.
      simpl in *. apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr i) in HNS1. 
      apply dom_equiv_trans with (l1:= ((dom pd ∪ get_modvar_in_winstr i) ∪ get_modvar_in_winstr i)%domain); try assumption.
      apply dom_equiv_sym. apply orb_domain_elim_r. apply dom_subset_orb_snd_l_r.
Qed.

Lemma dom_sub_modvar_preserves_domeq: forall c pd pd',
  is_domain_subset (get_modvar_in_winstr c) (dom pd) = true ->
  pd =[ c ]=> pd' ->  
  (dom pd == dom pd')%domain.
Proof.
  intros c pd pd' Hsub HNS. generalize dependent pd'. generalize dependent pd.
  induction c; intros.
  - inversion HNS; subst. simpl in *. apply dom_equiv_refl. 
  - inversion HNS; subst. simpl in *. apply orb_domain_elim_r. assumption.
  - inversion HNS; subst. simpl in *. apply dom_subset_implies_orb_equiv. assumption.
  - inversion HNS; subst. simpl in *. apply dom_subset_orb_fst_iff in Hsub. destruct Hsub.
    specialize (IHc1 pd H pd1 H3). 
    apply dom_subset_eq_compat_left with (Y:= dom pd1) in H0; try assumption.
    specialize (IHc2 pd1 H0 pd' H6). 
    apply dom_equiv_trans with (l1:= dom pd1); try assumption.
  - simpl in *. apply dom_subset_orb_fst_iff in Hsub. destruct Hsub.
    inversion HNS; subst.
    + simpl in *. apply orb_domain_elim_r. apply dom_subset_orb_fst_iff. split; try assumption.
    + apply IHc1; try assumption.
    + apply IHc2; try assumption.
    + specialize (IHc1 pd_b). simpl in IHc1. 
      specialize (IHc1 H pd1 H9). 
      specialize (IHc2 pd_notb). simpl in IHc2. 
      specialize (IHc2 H0 pd2 H10). 
      apply dom_equiv_trans with (l1:= dom pd1); try assumption.
      apply dom_equiv_trans with (l1:= orb_domain (dom pd1) (get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI))); try assumption.
      * apply dom_subset_implies_orb_equiv. simpl. apply dom_subset_orb_fst_iff. 
        assert (IHc1_copy:  (dom pd == dom pd1)%domain). { assumption. }
        apply dom_subset_eq_compat_left with (Z:= (get_modvar_in_winstr c1)) in IHc1; try assumption.
        apply dom_subset_eq_compat_left with (Z:= (get_modvar_in_winstr c2)) in IHc2; try assumption.
        apply dom_subset_eq_compat_left with (Z:= (get_modvar_in_winstr c2)) in IHc1_copy; try assumption.
        split; try assumption.
      * simpl in *. apply dom_equiv_sym in H14.
        apply dom_equiv_trans with (l1:= dom pd1); try assumption. 
        apply dom_equiv_sym.
        apply orb_domain_elim_r. 
        apply dom_subset_orb_fst_iff. 
        split; apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
  - simpl in *. remember (While b c) as cw eqn:Heqcw. 
    induction HNS; inversion Heqcw; subst; clear Heqcw; try apply dom_equiv_refl.
    + simpl in *. apply orb_domain_elim_r. assumption. 
    + specialize (IHc pd Hsub pd1 HNS1). 
      apply dom_equiv_trans with (l1:= dom pd1); try assumption.
      apply IHHNS2; try assumption; try reflexivity.
      apply dom_subset_eq_compat_left with (X:= (dom pd)); try assumption.
    + simpl in *. specialize (IHc pd_b). simpl in IHc. 
      specialize (IHc Hsub pd0 HNS1).
      apply dom_equiv_sym. 
      apply dom_equiv_trans with (l1:= dom pd1); try assumption.
      apply dom_equiv_sym. 
      apply dom_equiv_trans with (l1:= dom pd0); try assumption.
      apply IHHNS2; try reflexivity.
      apply dom_subset_eq_compat_left with (X:= (dom pd)); try assumption.
Qed.

Lemma subset_NS: forall pd pd' c, 
  Valid_dist (mu pd) -> Valid_dist (mu pd') -> 
  pd =[ c ]=> pd' -> is_domain_subset (dom pd) (dom pd') = true.
Proof. 
  intros pd pd' c HWF HWF' HNS. generalize dependent pd'. generalize dependent pd.
  induction c; intros. 
  - inversion HNS; subst. apply dom_subset_refl.
  - inversion HNS; subst. simpl in *. apply dom_subset_orb_dom_r. apply dom_subset_refl.
  - inversion HNS; subst. simpl in *. apply dom_subset_orb_dom_r. apply dom_subset_refl.
  - inversion HNS; subst. apply IHc2 in H6; try assumption. 
    + apply IHc1 in H3; try assumption. 
      * apply dom_subset_trans with (l1:= dom pd1); assumption.
      * apply Valid_forall_NS in H3; assumption.
    + apply Valid_forall_NS in H3; assumption.
  - inversion HNS; subst.
    + simpl in *. apply dom_subset_orb_dom_r. apply dom_subset_refl.
    + apply IHc1; try assumption.
    + apply IHc2; try assumption.
    + assert (HWFb: Valid_dist (mu pd_b)). { apply dst_Valid_get_b. assumption. }
      assert (HWFnb: Valid_dist (mu pd_notb)). { apply dst_Valid_get_notb. assumption. }
      assert (HWF1: Valid_dist (mu pd1)). { apply Valid_forall_NS in H7; try assumption. }
      assert (HWF2: Valid_dist (mu pd2)). { apply Valid_forall_NS in H8; try assumption. }
      specialize (IHc1 pd_b HWFb pd1 HWF1 H7). specialize (IHc2 pd_notb HWFnb pd2 HWF2 H8).
      simpl in *. apply dom_subset_trans with (l1:= dom pd1); try assumption.
      apply dom_equiv_sym in H12. 
      apply dom_subset_eq_compat_left with (Z:= (dom pd1)) in H12; try assumption.
      apply dom_subset_refl.
  - remember (While b c) as cw eqn:Heqcw. 
    induction HNS; inversion Heqcw; subst; clear Heqcw.
    + simpl in *. apply dom_subset_orb_dom_r. apply dom_subset_refl.
    + assert (HWF1: Valid_dist (mu pd1)). { apply Valid_forall_NS in HNS1; assumption. }
      apply dom_subset_trans with (l1:= (dom pd1)). 
      * apply IHc; try assumption. 
      * apply IHHNS2; try assumption. reflexivity.
    + apply dom_subset_refl.
    + simpl in *. 
      assert (HWFb: Valid_dist (mu pd_b)). { apply dst_Valid_get_b. assumption. }
      assert (HWFnb: Valid_dist (mu pd_notb)). { apply dst_Valid_get_notb. assumption. }
      assert (HWF0: Valid_dist (mu pd0)). { apply Valid_forall_NS in HNS1; assumption. }
      assert (HWF1: Valid_dist (mu pd1)). { apply Valid_forall_NS in HNS2; assumption. }
      specialize (IHc pd_b HWFb pd0 HWF0 HNS1). simpl in *.
      apply dom_subset_trans with (l1:= (dom pd0)); try assumption. 
      apply dom_equiv_sym in H5.
      apply dom_subset_eq_compat_left with (X:= (dom pd1)); try assumption. 
      apply IHHNS2; try assumption. reflexivity.
Qed. 


Lemma NS_pd_implies_nil: forall c dom0 ( pd': partial_dist) (HPD0: partial_dst_Prop dom0 []), 
  NS c {| dom := dom0; mu := []; all_partial := HPD0 |} pd' -> 
  (mu pd') = nil /\ ((dom pd') == orb_domain dom0 (get_modvar_in_winstr c))%domain.
Proof. 
  intros c dom0 pd' Hdom0 HNS. split. {
    generalize dependent pd'. generalize dependent dom0.
    induction c as [| | | | |]; intros.
    - inversion HNS; subst. simpl. reflexivity.
    - inversion HNS; subst; simpl in *. reflexivity.
    - inversion HNS; subst; simpl in *. reflexivity.
    - inversion HNS; subst; simpl in *. 
      apply IHc1 in H3; try assumption.
      destruct pd1. simpl in *. subst.
      apply IHc2 in H6. assumption.
    - inversion HNS; subst; simpl in *; try reflexivity. 
      + apply IHc1 in H9; try assumption.
      + apply IHc2 in H9; try assumption.
      + unfold b_supp_classify in H3. simpl in H3. discriminate.
    - inversion HNS; subst; simpl in *; try reflexivity. 
      + unfold b_supp_classify in H2. simpl in H2. discriminate.
      + unfold b_supp_classify in H2. simpl in H2. discriminate. }
  apply orbdom_after_NS in HNS; try assumption.
Qed.  
Lemma NS_mu_implies_nil: forall c (pd pd': partial_dist), 
  NS c pd pd' -> mu pd = nil ->
  (mu pd') = nil.
Proof. 
  intros c pd pd' HNS Hnil. 
  generalize dependent pd'. generalize dependent pd.
  induction c as [| | | | |]; intros.
  - inversion HNS; subst; try assumption; try reflexivity.
  - inversion HNS; subst; try assumption; try reflexivity. 
    simpl in *. rewrite Hnil. simpl. reflexivity.
  - inversion HNS; subst; try assumption; try reflexivity. 
    simpl in *. rewrite Hnil. simpl. reflexivity.
  - inversion HNS; subst; try assumption; try reflexivity.
    apply IHc1 in H3; try assumption.
    apply IHc2 in H6; assumption.
  - inversion HNS; subst; try assumption; try reflexivity. 
    + apply IHc1 in H9; try assumption.
    + apply IHc2 in H9; try assumption.
    + apply IHc1 in H7; try assumption; apply IHc2 in H8; try assumption; simpl. 
      * rewrite H9. rewrite H7. rewrite H8. reflexivity.
      * rewrite Hnil. simpl. reflexivity.
      * rewrite Hnil. simpl. reflexivity.
      * rewrite Hnil. simpl. reflexivity.
  - remember (While b c) as original_command eqn:Horig.
    induction HNS; try inversion Horig; subst; intros.
    + simpl. reflexivity.
    + apply IHHNS2; try reflexivity. apply IHc with (pd:= pd); try assumption.
    + assumption.
    + rewrite H4. simpl. rewrite Hnil. simpl. rewrite dst_add_0_r.
      apply IHHNS2; try reflexivity. apply IHc with (pd:= pd_b); try assumption.
      simpl. rewrite Hnil. simpl. reflexivity.  
Qed. 

Lemma step_deterministic : forall c pd0 pd1 pd0',
  Valid_dist (mu pd0) -> Valid_dist (mu pd1) ->
  well_defined_winstr_with_pd c pd0 -> well_defined_winstr_with_pd c pd1 ->
  pd0 ≡ pd1 ->
  NS c pd0 pd0' ->
  (exists pd1', pd0' ≡ pd1' /\ NS c pd1 pd1').
Proof.
  intros c pd0 pd1 pd0' Hvalid0 Hvalid1 HWD0 HWD1 Hmu HNS.
  generalize dependent pd0'. generalize dependent pd0. generalize dependent pd1.
  induction c; intros.
  - inversion HNS; intros; subst. exists pd1. split; try assumption. apply NS_Skip.
  - inversion HNS; intros; subst. 
    assert (HWFa1: WF_aexp_with_pd a pd1). { 
      destruct Hmu. apply dom_equiv_preserves_WF_aexp with (pd:= pd0); try assumption. }
    exists (DAssn_under_pd n a pd1 HWFa1). split.
    * destruct Hmu. split; simpl. 
      + apply dom_eq_orb_compat_right. assumption. 
      + apply DA_step_deter; try assumption.
    * apply NS_DAssign.
  - inversion HNS; intros; subst.
    assert (HWFa1: WF_distaexp_with_pd (proj1_sig v) pd1). { 
      destruct Hmu. apply dom_equiv_preserves_WF_distaexp with (pd:= pd0); try assumption. }
    exists (RAssn_under_pd n v pd1 HWFa1). split.
    * destruct Hmu. split; simpl. 
      + apply dom_eq_orb_compat_right. assumption. 
      + apply RA_step_deter; try assumption.
    * apply NS_RAssign.
  - inversion HNS; intros; subst.
    assert (Hmu': pd0 ≡ pd1) by assumption.
    assert (HWFc1: well_defined_winstr_with_pd c1 pd1). { 
      destruct Hmu. apply pd_equiv_preserves_WD_win with (pd:= pd0); try assumption. }
    apply IHc1 with (pd0':= pd2) in Hmu; try assumption. destruct Hmu. destruct H.
    assert (Hvx: Valid_dist (mu x)). { apply Valid_forall_NS with (c:= c1) (pd:= pd1); try assumption. }
    assert (Hv2: Valid_dist (mu pd2)). { apply Valid_forall_NS with (c:= c1) (pd:= pd0); try assumption. }
    assert (H': pd2 ≡ x) by assumption. 
    apply IHc2 with (pd0':= pd0') in H; try assumption.
    + destruct H. destruct H. exists x0. split; try assumption. 
      eapply NS_Seq; try assumption. 
      * apply pd_equiv_preserves_WD_win with (pd:= pd2); try assumption. 
      ** apply Hvx.
      ** apply H'.
      * assumption. 
      * assumption. 
    + apply pd_equiv_preserves_WD_win with (pd:= pd2); try assumption. 
  - inversion HNS; intros; subst.
    * assert (HWFc1: well_defined_winstr_with_pd c1 pd1). { 
        apply pd_equiv_preserves_WD_win with (pd:= pd0); try assumption. }
      assert (HWFc2: well_defined_winstr_with_pd c2 pd1). { 
        apply pd_equiv_preserves_WD_win with (pd:= pd0); try assumption. }
      exists ((pd_emp (dom pd1 ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI)))). split.
      + destruct Hmu. split; try apply dst_equiv_refl. simpl.
        apply dom_eq_orb_compat_right. assumption.
      + apply NS_IF_Nil; try assumption. 
        ++ destruct Hmu. apply dom_equiv_preserves_WF_bexp with (pd:= pd0); try assumption.
        ++ rewrite dst_equiv_implies_b_classify with (pd1:= pd1) in H3; try assumption.
        ++ destruct H8. destruct H. 
          apply IHc1 with (pd1:= pd1) in H0; try assumption. 
          destruct H0. destruct H0. exists x0. split; try assumption. 
          apply pd_equiv_trans with (pd1:= x); try assumption. 
          apply pd_equiv_trans with (pd1:= pd_emp (dom pd0 ∪ get_modvar_in_winstr c1)); try assumption.
          split; simpl; try apply dst_equiv_refl.
          destruct Hmu. apply dom_eq_orb_compat_right. 
          apply dom_equiv_sym. assumption.
        ++ destruct H9. destruct H. 
          apply IHc2 with (pd1:= pd1) in H0; try assumption. 
          destruct H0. destruct H0. exists x0. split; try assumption. 
          apply pd_equiv_trans with (pd1:= x); try assumption. 
          apply pd_equiv_trans with (pd1:= pd_emp (dom pd0 ∪ get_modvar_in_winstr c2)); try assumption.
          split; simpl; try apply dst_equiv_refl.
          destruct Hmu. apply dom_eq_orb_compat_right. 
          apply dom_equiv_sym. assumption.
    * assert (Hmu': pd0 ≡ pd1) by assumption.
      rewrite dst_equiv_implies_b_classify with (pd1:= pd1) in H3; try assumption.
      assert (HWFc1: well_defined_winstr_with_pd c1 pd1). { 
        destruct Hmu. apply pd_equiv_preserves_WD_win with (pd:= pd0); try assumption. }
      assert (HWFc2: well_defined_winstr_with_pd c2 (pd_emp (dom pd1))). { 
        destruct Hmu. apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd0))); try assumption.
        - apply Valid_dist_nil. 
        - apply Valid_dist_nil.
        - split; simpl; try assumption. apply dst_equiv_refl. }
      apply IHc1 with (pd0':= pd0') in Hmu; try assumption. destruct Hmu. destruct H.
      exists x. split; try assumption. apply NS_IF_All_True; try assumption. 
      + destruct Hmu'. apply dom_equiv_preserves_WF_bexp with (pd:= pd0); try assumption.
      + apply dom_subset_eq_compat_left with (X:= dom pd0 ∪ get_modvar_in_winstr c1); try assumption. 
        apply dom_eq_orb_compat_right. destruct Hmu'. assumption.
      + destruct H10. destruct H1. 
        apply IHc2 with (pd1:= (pd_emp (dom pd1))) in H7; try assumption.
        ++ destruct H7. destruct H7. exists x1. split; try assumption. 
          apply NS_pd_implies_nil in H8. destruct H8.
          split; simpl.
          ** apply dom_equiv_sym. assumption.
          ** rewrite H8. apply dst_equiv_refl.
        ++ apply Valid_dist_nil.
        ++ apply Valid_dist_nil.
        ++ destruct Hmu'. split; simpl; try assumption; try apply dst_equiv_refl.
    * assert (Hmu': pd0 ≡ pd1) by assumption.
      rewrite dst_equiv_implies_b_classify with (pd1:= pd1) in H3; try assumption.
      assert (HWFc1: well_defined_winstr_with_pd c1 (pd_emp (dom pd1))). { 
        destruct Hmu. apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd0))); try assumption.
        - apply Valid_dist_nil.
        - apply Valid_dist_nil.
        - split; simpl; try assumption. apply dst_equiv_refl. }
      assert (HWFc2: well_defined_winstr_with_pd c2 pd1). { 
        destruct Hmu. apply pd_equiv_preserves_WD_win with (pd:= pd0); try assumption. }
      apply IHc2 with (pd0':= pd0') in Hmu; try assumption. destruct Hmu. destruct H. 
      exists x. split; try assumption. apply NS_IF_All_False; try assumption. 
      + destruct Hmu'. apply dom_equiv_preserves_WF_bexp with (pd:= pd0); try assumption.
      + apply dom_subset_eq_compat_left with (X:= dom pd0 ∪ get_modvar_in_winstr c2); try assumption. 
        apply dom_eq_orb_compat_right. destruct Hmu'. assumption.
      + destruct H10. destruct H1. apply IHc1 with (pd1:= (pd_emp (dom pd1))) in H7; try assumption. 
        ++ destruct H7. destruct H7. exists x1. split; try assumption. 
          apply pd_equiv_trans with (pd1:= x0); try assumption.
          apply pd_equiv_trans with (pd1:= pd_emp (dom pd0 ∪ get_modvar_in_winstr c1)); try assumption.
          split; simpl; try apply dst_equiv_refl.
          destruct Hmu'. apply dom_eq_orb_compat_right. apply dom_equiv_sym. assumption.
        ++ apply Valid_dist_nil.
        ++ apply Valid_dist_nil.
        ++ destruct Hmu'. split; simpl; try assumption; try apply dst_equiv_refl.
    * assert (Heq1: pd_b ≡ extract_b_pd b pd1). { apply pd_eq_preserves_get_b; try assumption. }
      assert (Heq2: pd_notb ≡ extract_notb_pd b pd1). { apply pd_eq_preserves_get_notb; try assumption. }
      assert (HWD21: well_defined_winstr_with_pd c2 (extract_notb_pd b pd1)). { 
        apply pd_equiv_preserves_WD_win with (pd:= (extract_notb_pd b pd0)); 
          try apply dst_Valid_get_notb; try assumption. }
      assert (HWD11: well_defined_winstr_with_pd c1 (extract_b_pd b pd1)). { 
        apply pd_equiv_preserves_WD_win with (pd:= (extract_b_pd b pd0)); 
          try apply dst_Valid_get_b; try assumption. }
      apply IHc1 with (pd0':= pd2) in Heq1; apply IHc2 with (pd0':= pd3) in Heq2; try assumption;
        try apply dst_Valid_get_b; try apply dst_Valid_get_notb; try assumption. 
      destruct Heq1. destruct H. destruct Heq2. destruct H1. 
      assert (Hdom': (dom x == dom x0)%domain). { simpl. 
        destruct H. destruct H1. 
        apply dom_equiv_trans with (l1:= dom pd3); try assumption.
        apply dom_equiv_sym in H.
        apply dom_equiv_trans with (l1:= dom pd2); try assumption.
        apply orbdom_after_NS in H7, H8.  
        apply dom_equiv_trans with (l1:= (dom pd_b ∪ get_modvar_in_winstr c1)%domain); try assumption.
        apply dom_equiv_sym in H8.
        apply dom_equiv_trans with (l1:= (dom pd_notb ∪ get_modvar_in_winstr c2)%domain); try assumption.
        simpl. destruct H6.
        - apply dom_eq_orb_compat_left. assumption.
        - destruct H6. apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H15. 
          apply dom_equiv_sym in H6. 
          apply dom_equiv_trans with (l1:= (dom pd0)%domain); try assumption. }
      exists (pd_add x x0 Hdom'). split; try assumption. 
      + split; simpl; try assumption. 
      ** apply orbdom_after_NS in HNS. simpl in HNS. apply orbdom_after_NS in H0. simpl in H0. 
        apply dom_equiv_trans with (l1:= (dom pd0 ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2))%domain); try assumption.
        apply dom_equiv_sym in H0.
        apply dom_equiv_trans with (l1:= (dom pd1 ∪ get_modvar_in_winstr c1)%domain); try assumption.
        destruct H6. 
        -- destruct H6.
        apply orb_domain_elim_r in H11. 
        apply dom_equiv_trans with (l1:= dom pd1 ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2)); try assumption.
        ++ apply dom_eq_orb_compat_right. destruct Hmu. assumption.
        ++ apply dom_eq_orb_compat_left. apply dom_equiv_sym. assumption.
        -- destruct H6. destruct Hmu.  
        apply dom_equiv_trans with (l1:= dom pd0); try assumption.
        ++ apply dom_equiv_sym. apply orb_domain_elim_r. apply dom_subset_orb_fst_iff. split; try assumption.
        ++ apply orb_domain_elim_r in H6. 
        apply dom_equiv_trans with (l1:= (dom pd0 ∪ get_modvar_in_winstr c1)%domain); try assumption.
        apply dom_eq_orb_compat_right. assumption. 
      ** rewrite H9.
        destruct H. destruct H1. apply dst_add_preserves_equiv; try assumption.
      + rewrite dst_equiv_implies_b_classify with (pd1:= pd1) in H3; try assumption.
        eapply NS_IF_Mixed; try assumption. 
      ** destruct Hmu. apply dom_equiv_preserves_WF_bexp with (pd:= pd0); try assumption.
      ** destruct H6. -- try left; try assumption. -- right. destruct H6. destruct Hmu. 
          split; apply dom_subset_eq_compat_left with (X:= dom pd0); try assumption.
      ** apply H0.
      ** apply H10.
      ** simpl. reflexivity.
      ** simpl. apply dom_equiv_refl.
      ** simpl. assumption.
  - generalize dependent pd1. 
    remember (While b c) as original_command eqn:Horig.
    induction HNS; try inversion Horig; subst; intros.
    + exists ((pd_emp (dom pd1 ∪ get_modvar_in_winstr (WHILE b DO c END)))). split.
      * destruct Hmu. split; try apply dst_equiv_refl. simpl.
        apply dom_eq_orb_compat_right. assumption.
      * apply NS_While_Nil.
      ** destruct Hmu. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
      ** rewrite dst_equiv_implies_b_classify with (pd1:= pd1) in H0; try assumption.
    + assert (HV1: Valid_dist (mu pd1)). { apply Valid_forall_NS with (c:= c) (pd:= pd) ; try assumption. }
      assert (HV': Valid_dist (mu pd')). { apply Valid_forall_NS with (c:= While b c) (pd:= pd1) ; try assumption. }
      assert (Hmu': pd ≡ pd0) by assumption.
      rewrite dst_equiv_implies_b_classify with (pd1:= pd0) in H0; try assumption.
      apply IHc with (pd0':= pd1) in Hmu; try assumption. 
      * destruct Hmu. destruct H3. 
        assert (H3': pd1 ≡ x) by assumption.
        assert (HVx: Valid_dist (mu x)). { apply Valid_forall_NS with (c:= c) (pd:= pd0) ; try assumption. }
        apply IHHNS2 in H3; try assumption.
        ** destruct H3. destruct H3. exists x0. split; try assumption. 
          eapply NS_While_All_True; try assumption.
          -- apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption. destruct Hmu'. assumption.
          -- apply pd_equiv_preserves_WD_win with (pd:= pd); try assumption. 
          -- apply pd_equiv_preserves_WD_win with (pd:= pd1) (pd':= x); try assumption.
          -- apply H4.
          -- assumption.
        ** apply pd_equiv_preserves_WD_win with (pd:= pd1) (pd':= x); try assumption.
      * destruct HWD1. rewrite H0 in H4. assumption.
    + rewrite dst_equiv_implies_b_classify with (pd1:= pd1) in H0; try assumption. 
      exists pd1. split; try assumption. 
      apply NS_While_All_False; try assumption. 
      * destruct Hmu. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
      * destruct Hmu. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
    + rewrite dst_equiv_implies_b_classify with (pd1:= pd2) in H0; try assumption. 
      assert (Heq': (extract_b_pd b pd) ≡ (extract_b_pd b pd2)). { apply pd_eq_preserves_get_b; assumption. }
      assert (H1': well_defined_winstr_with_pd c (extract_b_pd b pd2)). { 
        apply pd_equiv_preserves_WD_win with (pd:= (extract_b_pd b pd)); try apply dst_Valid_get_b; try assumption. }
      assert (Hv0: Valid_dist (mu pd0)). { apply Valid_forall_NS in HNS1; try assumption. apply dst_Valid_get_b; assumption. } 
      apply IHc with (pd0':= pd0) in Heq'; try assumption.
      * destruct Heq'. destruct H6. 
        assert (H6': pd0 ≡ x) by assumption. 
        assert (HVx: Valid_dist (mu x)). { apply Valid_forall_NS in H7; try assumption. apply dst_Valid_get_b; assumption. }
        apply IHHNS2 in H6; try assumption. 
        ** destruct H6. destruct H6. 
          assert (Hdom10: (dom pd1 == dom pd0)%domain). {
            destruct H6. apply dom_equiv_sym in H6.
            apply orbdom_after_NS in HNS1, HNS2. simpl in HNS1. simpl in HNS2. 
            apply dom_equiv_trans with (l1:= (dom pd0 ∪ get_modvar_in_winstr c)%domain); try assumption. 
            apply dom_equiv_sym. apply orb_domain_elim_r. 
            apply dom_equiv_sym in HNS1.
            apply dom_subset_eq_compat_left with (X:= (dom pd ∪ get_modvar_in_winstr c)%domain); try assumption.
            apply dom_subset_orb_snd_l_r. } 
          assert (Hdom0: (dom pd0 == dom pd)%domain). {
            destruct H6. apply dom_equiv_sym in H6.
            apply orbdom_after_NS in HNS1, HNS2. simpl in HNS1. simpl in HNS2. 
            apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c)%domain); try assumption. 
            apply dom_equiv_sym. apply orb_domain_elim_r. assumption. }  
          assert (Htmp: (dom x0 == dom (extract_notb_pd b pd))%domain). {
            simpl. destruct H6. apply dom_equiv_sym in H6.
            apply orbdom_after_NS in HNS1, HNS2. simpl in HNS1. simpl in HNS2. 
            apply dom_equiv_trans with (l1:= dom pd1); try assumption.
            apply dom_equiv_trans with (l1:= dom pd0); try assumption. }
          assert (H': (dom x0 == dom (extract_notb_pd b pd2))%domain). {
            simpl. destruct Hmu. apply dom_equiv_trans with (l1:= dom pd); try assumption. }
          pose (pdx:= pd_add x0 (extract_notb_pd b pd2) H').
          exists pdx. split; try apply pd_equiv_refl. 
          -- split; simpl; try assumption.
            ++ apply dom_equiv_sym. simpl in H'. 
            apply dom_equiv_trans with (l1:= dom pd); try assumption. 
            apply dom_equiv_sym in H5. 
            apply dom_equiv_trans with (l1:= dom pd1); try assumption. 
            apply dom_equiv_sym. 
            apply dom_equiv_trans with (l1:= dom pd0); try assumption. 
            ++ rewrite H4. simpl. destruct H6. destruct Hmu.
            apply dst_add_preserves_equiv; try assumption.
            apply Peq_implies_get_notb_Peq; try assumption.
          -- eapply NS_While_Mixed; try assumption. 
            ++ destruct Hmu. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
            ++ apply pd_equiv_preserves_WD_win with (pd:= pd0) (pd':= x); try assumption.
            ++ destruct Hmu. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. 
            ++ apply H7.
            ++ apply H8.
            ++ simpl. reflexivity.
            ++ simpl. apply dom_equiv_refl. 
        ** apply pd_equiv_preserves_WD_win with (pd:= pd0); try assumption.
      * apply dst_Valid_get_b; assumption.
      * apply dst_Valid_get_b; assumption.
Qed. 

Lemma add_NS: forall c (pd0 pd1 pd pd': partial_dist),
  Valid_dist (mu pd0) -> Valid_dist (mu pd1) -> Valid_dist (mu pd) -> 
  Valid_dist (mu pd0 + mu pd1)%dist_state -> NS c pd pd' ->
  mu pd == (mu pd0 + mu pd1)%dist_state -> 
  ((dom pd) == (dom pd0))%domain /\ ((dom pd) == (dom pd1))%domain ->
    (exists pd0' pd1', NS c pd0 pd0' /\ NS c pd1 pd1' /\
      mu pd' == ((mu pd0') + (mu pd1'))%dist_state /\
      ((dom pd') == (dom pd0'))%domain /\ ((dom pd') == (dom pd1'))%domain).
Proof. 
  intros c pd0 pd1 pd pd' Hvalid0 Hvalid1 Hvalid Hvl HNS Hadd Hdom.
  generalize dependent pd'. generalize dependent pd.
  generalize dependent pd1. generalize dependent pd0. 
  induction c as [| | | | |]; intros. 
  - inversion HNS; subst. exists pd0, pd1. 
    split; try apply NS_Skip. 
    split; try apply NS_Skip. 
    split; assumption.
  - inversion HNS; subst; simpl in *. 
    destruct Hdom. 
    assert (HWFa0: WF_aexp_with_pd a pd0). {
      apply dom_equiv_preserves_WF_aexp with (pd:= pd); try assumption. }
    assert (HWFa1: WF_aexp_with_pd a pd1). {
      apply dom_equiv_preserves_WF_aexp with (pd:= pd); try assumption. }
    exists (DAssn_under_pd n a pd0 HWFa0), (DAssn_under_pd n a pd1 HWFa1).
    split; try apply NS_DAssign. 
    split; try apply NS_DAssign.
    simpl in *. rewrite <- dst_mult_1_l with (mu:= DAssn_under_dstate (mu pd0) n a).
    rewrite <- dst_mult_1_l with (mu:= DAssn_under_dstate (mu pd1) n a).
    rewrite <- DAss_eq_under_addAndmult. 
    split. { repeat rewrite dst_mult_1_l. apply DA_step_deter; try assumption. }
    split; apply dom_eq_orb_compat_right; assumption.
  - inversion HNS; subst. destruct Hdom. 
    assert (HWFa0': WF_distaexp_with_pd (proj1_sig v) pd0). {
     apply dom_equiv_preserves_WF_distaexp with (pd:= pd); try assumption. }
    assert (HWFa1': WF_distaexp_with_pd (proj1_sig v) pd1). {
      apply dom_equiv_preserves_WF_distaexp with (pd:= pd); try assumption. }
    exists (RAssn_under_pd n v pd0 HWFa0'), (RAssn_under_pd n v pd1 HWFa1').
    split; try apply NS_RAssign. 
    split; try apply NS_RAssign. simpl. 
    rewrite <- dst_mult_1_l with (mu:= RAssn_under_dstate (mu pd0) n (proj1_sig v)).
    rewrite <- dst_mult_1_l with (mu:= RAssn_under_dstate (mu pd1) n (proj1_sig v)).
    rewrite <- RAss_equiv_under_addAndmult.
    split. 
    + repeat rewrite dst_mult_1_l. apply RA_step_deter with (x:=n) (da:=(proj1_sig v)) in Hadd; try assumption.
    + split; apply dom_eq_orb_compat_right; try assumption.
  - inversion HNS; subst. 
    specialize IHc1 with (pd0:= pd0) (pd1:= pd1) (pd:= pd) (pd':= pd3); try assumption.
    specialize (IHc1 Hvalid0  Hvalid1 Hvl  Hvalid Hadd Hdom H3).
    destruct IHc1 as [mu01 Htemp]. destruct Htemp as [mu11 Htemp]. 
    destruct Htemp as [HNSmu0 Htemp]. destruct Htemp as [HNSmu1 Hmu3].
    destruct Hmu3 as [Hmu3 Hdom3].
    assert (Hmu3': mu pd3 == (mu mu01 + mu mu11)%dist_state) by assumption.
    assert (Hv01: Valid_dist (mu mu01)). {apply Valid_forall_NS in HNSmu0; assumption. }
    assert (Hv11: Valid_dist (mu mu11)). {apply Valid_forall_NS in HNSmu1; assumption. }
    assert (Hv3: Valid_dist (mu pd3)). {apply Valid_forall_NS in H3; assumption. }
    assert (Hv': Valid_dist (mu pd')). {apply Valid_forall_NS in H6; assumption. }
    assert (Hvmu: Valid_dist (mu mu01 + mu mu11)%dist_state). {
      rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq.
      apply Valid_linear_under_eq_prob; try assumption; try lra. 
      rewrite <- Rmult_plus_distr_l. rewrite Rmult_1_l. 
      apply NS_preserve_sum_eq in HNSmu0; try assumption. rewrite <- HNSmu0.
      apply NS_preserve_sum_eq in HNSmu1; try assumption. rewrite <- HNSmu1.
      rewrite <- dst_sum_prob_decom. destruct Hvl. assumption. } 
    apply IHc2 with (pd0:= mu01) (pd1:= mu11) (pd:= pd3) (pd':= pd') in Hmu3; try assumption.
    destruct Hmu3 as [mu02 Htemp]. destruct Htemp as [mu12 Htemp]. 
    destruct Htemp as [HNSmu02 Htemp]. destruct Htemp as [HNSmu12 Hmu2].
    destruct Hmu2 as [ Hmu2 Hdom2].
    exists (mu02), (mu12). split.
    * eapply NS_Seq; try assumption. 
      ** destruct Hdom3. 
      apply pd_decom_r_preserves_WD_win with (c:= c1) in Hadd; try assumption. 
      ** apply pd_decom_r_preserves_WD_win with (c:= c2) in Hmu3'; try assumption. apply Hmu3'.
      ** apply HNSmu0. 
      ** apply HNSmu02.
    * split. 
      ** eapply NS_Seq; try assumption.
      -- destruct Hdom3. 
        apply dst_equiv_trans with (mu2:= (mu pd1 + mu pd0)%dist_state) in Hadd; try apply dst_add_comm. 
        apply pd_decom_r_preserves_WD_win with (c:= c1) in Hadd; try assumption.
        +++ rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq.
        apply Valid_linear_under_eq_prob; try assumption; try lra. 
        rewrite <- Rmult_plus_distr_l. rewrite Rmult_1_l. rewrite Rplus_comm. 
        rewrite <- dst_sum_prob_decom. destruct Hvl. assumption. 
        +++ destruct Hdom. split; try assumption. 
      -- apply dst_equiv_trans with (mu2:= (mu mu11 + mu mu01)%dist_state) in Hmu3'. 
        ++ apply pd_decom_r_preserves_WD_win with (c:= c2) in Hmu3'; try assumption.
        +++ apply Hmu3'.
        +++ rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq.
        apply Valid_linear_under_eq_prob; try assumption; try lra. 
        rewrite <- Rmult_plus_distr_l. rewrite Rmult_1_l. rewrite Rplus_comm. 
        rewrite <- dst_sum_prob_decom. destruct Hvmu. assumption. 
        +++ destruct Hdom3. split; try assumption.
        ++ apply dst_add_comm.
      -- apply HNSmu1. 
      -- apply HNSmu12.
      ** split; try assumption.
  - destruct pd0 as [dom0 mu0 HPD0]. destruct pd1 as [dom1 mu1 HPD1].
    destruct mu0 as [|(s0,p0) mu0']; destruct mu1 as [|(s1,p1) mu1'].
    { assert (Hmu: mu pd = []). { apply dst_eq_nil_iff. split; try assumption.  }
      inversion HNS; subst.
      - assert (HWD10: well_defined_winstr_with_pd c1 {| dom := dom0; mu := []; all_partial := HPD0 |}). 
        { apply pd_decom_r_preserves_WD_win with (c:= c1) in Hadd; try assumption. }
        assert (HWD20: well_defined_winstr_with_pd c2 {| dom := dom0; mu := []; all_partial := HPD0 |}). 
        { apply pd_decom_r_preserves_WD_win with (c:= c2) in Hadd; try assumption. }
        assert (HWD11: well_defined_winstr_with_pd c1 {| dom := dom1; mu := []; all_partial := HPD1 |}). 
        { 
          apply dst_equiv_trans with (mu0:= mu pd) (mu2:= (mu {| dom := dom1; mu := []; all_partial := HPD1 |} +
            mu {| dom := dom0; mu := []; all_partial := HPD0 |})%dist_state) in Hadd; try apply dst_add_comm; try apply dst_equiv_refl.
          apply pd_decom_r_preserves_WD_win with (c:= c1) in Hadd; try assumption. destruct Hdom. split; try assumption.  }
        assert (HWD21: well_defined_winstr_with_pd c2 {| dom := dom1; mu := []; all_partial := HPD1 |}). 
        { apply pd_decom_l_preserves_WD_win with (c:= c2) in Hadd; try assumption. }
        unfold b_supp_classify in H3. rewrite Hmu in H3. 
        exists (pd_emp (dom0 ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI))), 
          (pd_emp (dom1 ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI))).  
        split. { 
          apply (@NS_IF_Nil b c1 c2 {| dom := dom0; mu := []; all_partial := HPD0 |}); try assumption.
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - destruct H8. destruct H. apply IHc1 with (pd':= x) in Hadd; try assumption. 
            destruct Hadd. destruct H1. destruct H1. exists x0. split; try assumption.
            split; simpl. 
            + apply orbdom_after_NS in H1. simpl in H1. apply dom_equiv_sym. assumption.
            + apply NS_pd_implies_nil in H1. destruct H1. rewrite H1. apply dst_equiv_refl.
          - destruct H9. destruct H. apply IHc2 with (pd':= x) in Hadd; try assumption. 
            destruct Hadd. destruct H1. destruct H1. exists x0. split; try assumption.
            split; simpl. 
            + apply orbdom_after_NS in H1. simpl in H1. apply dom_equiv_sym. assumption.
            + apply NS_pd_implies_nil in H1. destruct H1. rewrite H1. apply dst_equiv_refl. }
        split. { 
          apply (@NS_IF_Nil b c1 c2 {| dom := dom1; mu := []; all_partial := HPD1 |}); try assumption.
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - destruct H8. destruct H. apply IHc1 with (pd':= x) in Hadd; try assumption. 
            destruct Hadd. destruct H1. destruct H1. destruct H6. exists x1. split; try assumption.
            split; simpl. 
            + apply orbdom_after_NS in H6. simpl in H6. apply dom_equiv_sym. assumption.
            + apply NS_pd_implies_nil in H6. destruct H6. rewrite H6. apply dst_equiv_refl.
          - destruct H9. destruct H. apply IHc2 with (pd':= x) in Hadd; try assumption. 
            destruct Hadd. destruct H1. destruct H1. destruct H6. exists x1. split; try assumption.
            split; simpl. 
            + apply orbdom_after_NS in H6. simpl in H6. apply dom_equiv_sym. assumption.
            + apply NS_pd_implies_nil in H6. destruct H6. rewrite H6. apply dst_equiv_refl. }
        simpl. split; try apply dst_equiv_refl. destruct Hdom. 
        split; apply dom_eq_orb_compat_right; assumption.
      - unfold b_supp_classify in H3. rewrite Hmu in H3. discriminate.
      - unfold b_supp_classify in H3. rewrite Hmu in H3. discriminate.
      - unfold b_supp_classify in H3. rewrite Hmu in H3. discriminate.
    } 
    {
      inversion HNS; subst. 
      - rewrite dst_add_0_l in Hadd. apply pd_Nil_mu in H3. rewrite H3 in Hadd.
        apply dst_equiv_sym in Hadd.
        simpl in Hadd. 
        apply dst_cons_valid_contra in Hadd; try assumption; try contradiction. 
      - assert (HWD10: well_defined_winstr_with_pd c1 {| dom := dom0; mu := []; all_partial := HPD0 |}). 
          { apply pd_decom_r_preserves_WD_win with (c:= c1) in Hadd; try assumption. }
        assert (HWD20: well_defined_winstr_with_pd c2 {| dom := dom0; mu := []; all_partial := HPD0 |}). 
          { apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption.
          destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.  }
        assert (HWD11: well_defined_winstr_with_pd c1 {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}). 
          { apply pd_decom_l_preserves_WD_win with (c:= c1) in Hadd; try assumption. } 
        assert (HWD21: well_defined_winstr_with_pd c2 (pd_emp (dom {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}))). 
          { apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption.
          destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl. }
        assert (HNS1: NS c1 pd pd'); try assumption.
        apply IHc1 with (pd0:= {| dom := dom0; mu := []; all_partial := HPD0 |}) 
                        (pd1:= {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}) in H9; try assumption.
        destruct H9. destruct H. destruct H. destruct H0.
        apply NS_pd_implies_nil in H. destruct H as [Hmux Hdomx]. rewrite Hmux in H1. simpl in H1. 
        exists (pd_emp (dom0 ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI))), x0. 
        split. { 
          apply (@NS_IF_Nil b c1 c2 {| dom := dom0; mu := []; all_partial := HPD0 |}); try assumption.
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - unfold b_supp_classify. simpl. reflexivity.
          - apply IHc1 with (pd':= pd') in Hadd; try assumption. 
            destruct Hadd. destruct H. destruct H. exists x1. split; try assumption.
            split; simpl. 
            + apply orbdom_after_NS in H. simpl in H. apply dom_equiv_sym. assumption.
            + apply NS_pd_implies_nil in H. destruct H. rewrite H. apply dst_equiv_refl.
          - destruct H10. destruct H. 
            apply step_deterministic with (pd1:= {| dom := dom0; mu := []; all_partial := HPD0 |}) in H7; try assumption.
            + destruct H7. destruct H7. exists x2. split; try assumption. split; simpl.
              ++ apply orbdom_after_NS in H8. simpl in H8. apply dom_equiv_sym. assumption.
              ++ apply NS_pd_implies_nil in H8. destruct H8. rewrite H8. apply dst_equiv_refl. 
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
          }
        split. { 
          apply NS_IF_All_True; try assumption. 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - rewrite dst_equiv_implies_b_classify with (pd1:= pd); try assumption.
            apply pd_equiv_sym. 
            destruct Hdom. split; simpl; try assumption.
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c1); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          - destruct H10. destruct H. 
            apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}))) in H7; try assumption.
            + destruct H7. destruct H7. exists x2. split; try assumption. split; simpl. 
              ++ apply orbdom_after_NS in H8. simpl in H8. apply dom_equiv_sym. assumption.
              ++ apply NS_pd_implies_nil in H8. destruct H8. rewrite H8. apply dst_equiv_refl.
            + split; simpl; try apply dst_equiv_refl. destruct Hdom. assumption.
           }
        split. { rewrite dst_add_0_l. simpl. destruct H1. assumption. }
        destruct H1. destruct H1.
        split; simpl; try assumption. 
        apply dom_equiv_trans with (l1:= dom x); try assumption.
        apply dom_equiv_trans with (l1:= (dom0 ∪ get_modvar_in_winstr c1)%domain); try assumption.
        apply dom_equiv_trans with (l1:= dom0 ∪ get_modvar_in_winstr c1); try apply dom_equiv_refl.
        rewrite orb_domain_assoc. apply orb_domain_elim_r.
        destruct Hdom. simpl in H6.
        apply dom_subset_eq_compat_left with (X := dom pd ∪ get_modvar_in_winstr c1); try assumption.
        apply dom_eq_orb_compat_right. assumption.
      - assert (HNS2: NS c2 pd pd'); try assumption.
        apply IHc2 with (pd0:= {| dom := dom0; mu := []; all_partial := HPD0 |}) 
                        (pd1:= {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}) in H9; try assumption.
        destruct H9. destruct H. destruct H. destruct H0.
        apply NS_pd_implies_nil in H. destruct H as [Hmux Hdomx]. rewrite Hmux in H1. simpl in H1. 
        exists (pd_emp (dom0 ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI))), x0. 
        split. { apply (@NS_IF_Nil b c1 c2 {| dom := dom0; mu := []; all_partial := HPD0 |}). 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - unfold b_supp_classify. simpl. reflexivity.
          - apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
            split; simpl; try apply dst_equiv_refl. destruct Hdom. assumption.
          - apply pd_decom_r_preserves_WD_win with (c:= c2) in Hadd; try assumption.
          - destruct H10. destruct H. 
            apply step_deterministic with (pd1:= ({| dom := dom0; mu := []; all_partial := HPD0 |})) in H7; try assumption.
            + destruct H7. destruct H7. exists x2. split; try assumption. split; simpl. 
              ++ apply orbdom_after_NS in H8. simpl in H8. apply dom_equiv_sym. assumption.
              ++ apply NS_pd_implies_nil in H8. destruct H8. rewrite H8. apply dst_equiv_refl.
            + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption.
              split; simpl; try apply dst_equiv_refl. destruct Hdom. assumption.
            + split; simpl; try apply dst_equiv_refl. destruct Hdom. assumption.
          - apply IHc2 with (pd':= pd') in Hadd; try assumption. 
            destruct Hadd. destruct H. destruct H. exists x1. split; try assumption. split; simpl.
            + apply orbdom_after_NS in H. simpl in H. apply dom_equiv_sym. assumption.
            + apply NS_pd_implies_nil in H. destruct H. rewrite H. apply dst_equiv_refl.
          }
        split. { apply NS_IF_All_False; try assumption. 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - rewrite dst_equiv_implies_b_classify with (pd1:= pd); try assumption.
            apply pd_equiv_sym. destruct Hdom. split; simpl; try assumption.
          - apply pd_equiv_preserves_WD_win with (pd:= pd_emp (dom pd)); try assumption. 
            destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
          - apply pd_decom_l_preserves_WD_win with (c:=c2) in Hadd; try assumption.  
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c2); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          - destruct H10. destruct H. 
            apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}))) in H7; try assumption.
            + destruct H7. destruct H7. exists x2. split; try assumption. split; simpl. 
              ++ apply orbdom_after_NS in H8. simpl in H8. apply dom_equiv_sym. assumption.
              ++ apply NS_pd_implies_nil in H8. destruct H8. rewrite H8. apply dst_equiv_refl.
            + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption.
              split; simpl; try apply dst_equiv_refl. destruct Hdom. assumption.
            + split; simpl; try apply dst_equiv_refl. destruct Hdom. assumption.
           }
        split. { rewrite dst_add_0_l. simpl. destruct H1. assumption. }
        destruct H1. destruct H1.
        split; simpl; try assumption. 
        apply dom_equiv_trans with (l1:= dom x); try assumption.
        apply dom_equiv_trans with (l1:= (dom0 ∪ get_modvar_in_winstr c2)%domain); try assumption.
        apply dom_equiv_trans with (l1:= dom0 ∪ get_modvar_in_winstr c2); try apply dom_equiv_refl.
        rewrite orb_domain_comm with (l:= get_modvar_in_winstr c1). 
        rewrite orb_domain_assoc. apply orb_domain_elim_r.
        destruct Hdom. simpl in H6.
        apply dom_subset_eq_compat_left with (X := dom pd ∪ get_modvar_in_winstr c2); try assumption.
        apply dom_eq_orb_compat_right. assumption.
      - rewrite dst_add_0_l in Hadd.
        assert (Heq': pd ≡ {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}). {
          destruct Hdom. split; simpl; try assumption. }
        pose(pd1_ori := {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}).
        assert (HVb1: Valid_dist (mu (extract_b_pd b pd1_ori))). { apply dst_Valid_get_b; assumption. }
        assert (HVnb1: Valid_dist (mu (extract_notb_pd b pd1_ori))). { apply dst_Valid_get_notb; assumption. }
        assert (HVb: Valid_dist (mu pd_b)). { apply dst_Valid_get_b; assumption. }
        assert (HVnb: Valid_dist (mu pd_notb)).  { apply dst_Valid_get_notb; assumption. }
        assert (Hb_eq: mu pd_b == (mu {| dom := dom0; mu := []; all_partial := HPD0 |} +
                                  mu (extract_b_pd b pd1_ori))%dist_state). {  
                        rewrite dst_add_0_l. 
                        apply Peq_implies_get_b_Peq with (b:= b) in Hadd; try assumption. }
        assert (Hnotb_eq: mu pd_notb == (mu {| dom := dom0; mu := []; all_partial := HPD0 |} +
                                        mu (extract_notb_pd b pd1_ori))%dist_state). {
                        rewrite dst_add_0_l. 
                        apply Peq_implies_get_notb_Peq with (b:= b) in Hadd; try assumption. }
        apply IHc1 with (pd0:= {| dom := dom0; mu := []; all_partial := HPD0 |}) 
                        (pd1:= extract_b_pd b pd1_ori) in H7; try assumption; 
        apply IHc2 with (pd0:= {| dom := dom0; mu := []; all_partial := HPD0 |}) 
                        (pd1:= extract_notb_pd b pd1_ori) in H8; try assumption.
        + destruct H8. destruct H. destruct H. destruct H0. destruct H1.
          destruct H7. destruct H7. destruct H7. destruct H10. destruct H11.
          assert (Htmp: (dom x0 == dom x2)%domain). { destruct H8. destruct H14.
            apply orbdom_after_NS in H10. apply orbdom_after_NS in H0. 
            apply dom_equiv_trans with (l1:= (dom (extract_notb_pd b pd1_ori) ∪ get_modvar_in_winstr c2)%domain); try assumption.
            apply dom_equiv_sym.
            apply dom_equiv_trans with (l1:= (dom (extract_b_pd b pd1_ori) ∪ get_modvar_in_winstr c1)%domain); try assumption.
            simpl. destruct H6.
            - apply dom_eq_orb_compat_left. assumption.
            - destruct H6. destruct Hdom. simpl in H16. 
              apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c2); try assumption.
              + apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c1); try assumption. 
                * apply dom_eq_orb_compat_right. apply dom_equiv_sym. assumption.
                * apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H17.
                apply dom_equiv_sym in H6. apply dom_equiv_trans with (l1:= dom pd); try assumption.
              + apply dom_eq_orb_compat_right. assumption. }
          assert (Hdom02: (dom x2 == dom x0)%domain). { apply dom_equiv_sym. assumption. }
          exists (pd_emp (dom0 ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI))), (pd_add x2 x0 (Hdom02)). 
          split. { apply (@NS_IF_Nil b c1 c2 {| dom := dom0; mu := []; all_partial := HPD0 |}). 
            - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
            - unfold b_supp_classify. simpl. reflexivity.
            - apply pd_decom_r_preserves_WD_win with (c:= c1) in Hb_eq; try assumption. 
            - apply pd_decom_r_preserves_WD_win with (c:= c2) in Hnotb_eq; try assumption.
            - exists x1. split; try assumption. split; simpl. 
              + apply orbdom_after_NS in H7. apply dom_equiv_sym. assumption.
              + apply NS_pd_implies_nil in H7. destruct H7. rewrite H7. apply dst_equiv_refl.
            - exists x. split; try assumption. split; simpl. 
              + apply orbdom_after_NS in H. apply dom_equiv_sym. assumption.
              + apply NS_pd_implies_nil in H. destruct H. rewrite H. apply dst_equiv_refl. }
          split. { eapply NS_IF_Mixed; try assumption.
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption. 
              - apply dst_equiv_implies_b_classify with (b:= b) in Heq'; try assumption. 
                rewrite H3 in Heq'. symmetry in Heq'. assumption.  
              - apply pd_equiv_preserves_WD_win with (pd:= pd_b); try assumption. split.
                + destruct Hdom. try assumption.
                +  try apply dst_Valid_get_b; try assumption.
              - apply pd_equiv_preserves_WD_win with (pd:= pd_notb); try assumption.
                destruct Hdom. split; simpl; try assumption.
              - destruct H6. 
                + left. assumption.
                + destruct H6. right. simpl. destruct Hdom. 
                  split; apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply H10.
              - apply H0.
              - simpl. reflexivity.
              - simpl. apply dom_equiv_refl.
              - simpl. assumption. }
          split. { simpl. 
              apply NS_pd_implies_nil in H7. destruct H7. rewrite H7 in H11. simpl in H11.
              apply NS_pd_implies_nil in H. destruct H. rewrite H in H1. simpl in H1.
              rewrite H9.
              apply dst_add_preserves_equiv; try assumption. }
          simpl. split; try assumption.
          * apply orbdom_after_NS in HNS. simpl in HNS. 
            apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI)); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          * destruct H8. apply orbdom_after_NS in HNS. simpl in HNS.  
            apply dom_equiv_trans with (l1:= (dom pd ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2))%domain); try assumption.
            apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym in H10.
            apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c1)%domain); try assumption.
            destruct Hdom. simpl in H16. 
            apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c1); try assumption.
              ** destruct H6. 
                -- apply dom_eq_orb_compat_left. apply dom_equiv_sym.
                apply orb_domain_elim_r. destruct H6. assumption.
                -- destruct H6. apply dom_equiv_trans with (l1:= 
                    (dom pd ∪ get_modvar_in_winstr c1) ∪ (dom pd ∪ get_modvar_in_winstr c2)); try apply dom_eq_orb_dis_r.
                apply dom_equiv_sym. apply orb_domain_elim_r. 
                apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H18. 
                apply dom_equiv_trans with (l1:= dom pd); try assumption.
                apply dom_equiv_sym. assumption.
              ** apply dom_eq_orb_compat_right. assumption. 
    }
    {
      assert (HVl: Valid_dist
                (mu {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |} +
                mu {| dom := dom1; mu := []; all_partial := HPD1 |})%dist_state). {
          simpl. rewrite dst_add_0_r. assumption. }
      inversion HNS; subst. 
      - rewrite dst_add_0_r in Hadd. apply pd_Nil_mu in H3. rewrite H3 in Hadd.
        apply dst_equiv_sym in Hadd.
        simpl in Hadd. 
        apply dst_cons_valid_contra in Hadd; try assumption; try contradiction. 
      - assert (Heq': pd ≡ {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}). {
          destruct Hdom. rewrite dst_add_0_r in Hadd. split; simpl; try assumption. }
        assert (HNS1: NS c1 pd pd') by assumption.
        apply IHc1 with (pd1:= {| dom := dom1; mu := []; all_partial := HPD1 |}) 
                        (pd0:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}) in H9; try assumption.
        rewrite dst_add_0_r in Hvl.         
        destruct H9. destruct H. destruct H. destruct H0.
        apply NS_pd_implies_nil in H0. destruct H0 as [Hmux0 Hdomx0]. 
        rewrite Hmux0 in H1. simpl in H1. rewrite dst_add_0_r in H1. 
        exists x, (pd_emp (dom1 ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI))). 
        split. { apply NS_IF_All_True; try assumption. 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - rewrite dst_equiv_implies_b_classify with (pd1:= pd); try assumption.
            apply pd_equiv_sym. 
            destruct Hdom. rewrite dst_add_0_r in Hadd. split; simpl; try assumption. 
          - apply pd_equiv_preserves_WD_win with (pd:= pd); try assumption.
          - apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
            destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c1); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          - destruct H10. destruct H0. 
            apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}))) in H7; try assumption.
            + destruct H7. destruct H7. exists x2. split; try assumption. 
              split; simpl.
              * apply orbdom_after_NS in H8; try assumption. simpl in H8. apply dom_equiv_sym. assumption.
              * apply NS_pd_implies_nil in H8; try assumption. destruct H8. rewrite H8. apply dst_equiv_refl.
            + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
              destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
           }
        split. { apply (@NS_IF_Nil b c1 c2 {| dom := dom1; mu := []; all_partial := HPD1 |}). 
            - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
            - unfold b_supp_classify. simpl. reflexivity.
            - apply pd_decom_l_preserves_WD_win with (c:= c1) in Hadd; try assumption. 
            - apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
              destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
            - apply IHc1 with (pd':= pd') in Hadd; try assumption.
              destruct Hadd. destruct H0. destruct H0. destruct H7. 
              exists x2. split; try assumption. split; simpl. 
              + apply orbdom_after_NS in H7; try assumption. simpl in H7. apply dom_equiv_sym. assumption.
              + apply NS_pd_implies_nil in H7; try assumption. destruct H7. rewrite H7. apply dst_equiv_refl.
            - destruct H10. destruct H0. 
              apply step_deterministic with (pd1:= {| dom := dom1; mu := []; all_partial := HPD1 |}) in H7; try assumption.
              + destruct H7. destruct H7. exists x2. split; try assumption. split; simpl. 
                * apply orbdom_after_NS in H8; try assumption. simpl in H8. apply dom_equiv_sym. assumption.
                * apply NS_pd_implies_nil in H8; try assumption. destruct H8. rewrite H8. apply dst_equiv_refl.
              + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
                destruct Hdom. split; simpl; try apply dst_equiv_refl. assumption.
              + destruct Hdom. split; simpl; try apply dst_equiv_refl. assumption.
            }
        split. { rewrite dst_add_0_r. simpl. destruct H1. assumption. }
        destruct H1. destruct H1.
        split; simpl; try assumption. 
        apply dom_equiv_trans with (l1:= dom x0); try assumption.
        apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c1)%domain); try assumption.
        apply dom_equiv_trans with (l1:= dom1 ∪ get_modvar_in_winstr c1); try apply dom_equiv_refl.
        rewrite orb_domain_assoc. apply orb_domain_elim_r.
        destruct Hdom. simpl in H6.
        apply dom_subset_eq_compat_left with (X := dom pd ∪ get_modvar_in_winstr c1); try assumption.
        apply dom_eq_orb_compat_right. assumption.
      - assert (Heq': pd ≡ {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}). {
          destruct Hdom. rewrite dst_add_0_r in Hadd. split; simpl; try assumption. }
        assert (HNS2: NS c2 pd pd') by assumption.
        apply IHc2 with (pd1:= {| dom := dom1; mu := []; all_partial := HPD1 |}) 
                        (pd0:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}) in H9; try assumption.
        destruct H9. destruct H. destruct H. destruct H0.
        rewrite dst_add_0_r in Hvl.
        apply NS_pd_implies_nil in H0. destruct H0 as [Hmux0 Hdomx0]. rewrite Hmux0 in H1. simpl in H1.
        rewrite dst_add_0_r in H1.
        exists x, (pd_emp (dom1 ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI))). 
        split. { apply NS_IF_All_False; try assumption. 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - rewrite dst_equiv_implies_b_classify with (pd1:= pd); try assumption.
            apply pd_equiv_sym. destruct Hdom.
            rewrite dst_add_0_r in Hadd. split; simpl; try assumption. 
          - apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
            destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
          - apply pd_decom_r_preserves_WD_win with (c:= c2) in Hadd; try assumption.
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c2); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          - destruct H10. destruct H0. 
            apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}))) in H7; try assumption.
            + destruct H7. destruct H7. exists x2. split; try assumption. split; simpl.
              * apply orbdom_after_NS in H8; try assumption. simpl in H8. apply dom_equiv_sym. assumption.
              * apply NS_pd_implies_nil in H8; try assumption. destruct H8. rewrite H8. apply dst_equiv_refl.
            + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
              destruct Hdom. split; simpl; try apply dst_equiv_refl. assumption.
            + destruct Hdom. split; simpl; try apply dst_equiv_refl. assumption.
           }
        split. { apply (@NS_IF_Nil b c1 c2 {| dom := dom1; mu := []; all_partial := HPD1 |}).
            - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
            - unfold b_supp_classify. simpl. reflexivity.
            - apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
              destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
            - apply pd_decom_l_preserves_WD_win with (c:= c2) in Hadd; try assumption.
            - destruct H10. destruct H0. 
              apply step_deterministic with (pd1:= {| dom := dom1; mu := []; all_partial := HPD1 |}) in H7; try assumption.
              + destruct H7. destruct H7. exists x2. split; try assumption. split; simpl.
                * apply orbdom_after_NS in H8; try assumption. simpl in H8. apply dom_equiv_sym. assumption.
                * apply NS_pd_implies_nil in H8; try assumption. destruct H8. rewrite H8. apply dst_equiv_refl.
              + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
                destruct Hdom. split; simpl; try apply dst_equiv_refl. assumption.
              + destruct Hdom. split; simpl; try apply dst_equiv_refl. assumption.
            - apply IHc2 with (pd':= pd') in Hadd; try assumption. 
              destruct Hadd. destruct H0. destruct H0. destruct H7.
              exists x2. split; try assumption. split; simpl. 
              + apply orbdom_after_NS in H7; try assumption. simpl in H7. apply dom_equiv_sym. assumption.
              + apply NS_pd_implies_nil in H7; try assumption. destruct H7. rewrite H7. apply dst_equiv_refl.
             }
        split. { rewrite dst_add_0_r. simpl. destruct H1. assumption. }
        destruct H1. destruct H1.
        split; simpl; try assumption. 
        apply dom_equiv_trans with (l1:= dom x0); try assumption.
        apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c2)%domain); try assumption.
        apply dom_equiv_trans with (l1:= dom1 ∪ get_modvar_in_winstr c2); try apply dom_equiv_refl.
        rewrite orb_domain_comm with (l:= get_modvar_in_winstr c1). 
        rewrite orb_domain_assoc. apply orb_domain_elim_r.
        destruct Hdom. simpl in H6.
        apply dom_subset_eq_compat_left with (X := dom pd ∪ get_modvar_in_winstr c2); try assumption.
        apply dom_eq_orb_compat_right. assumption.
      - assert (Heq': pd ≡ {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}). {
          destruct Hdom. rewrite dst_add_0_r in Hadd. split; simpl; try assumption. }
        pose(pd1_ori := {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
        assert (HVb1: Valid_dist (mu (extract_b_pd b pd1_ori))). { apply dst_Valid_get_b; assumption. }
        assert (HVnb1: Valid_dist (mu (extract_notb_pd b pd1_ori))). { apply dst_Valid_get_notb; assumption. }
        assert (HVb: Valid_dist (mu pd_b)). { apply dst_Valid_get_b; assumption. }
        assert (HVnb: Valid_dist (mu pd_notb)).  { apply dst_Valid_get_notb; assumption. }
        rewrite dst_add_0_r in Hadd. rewrite dst_add_0_r in Hvl.
        assert (Hb_eq: mu pd_b == (mu (extract_b_pd b pd1_ori)  +
                                   mu {| dom := dom1; mu := []; all_partial := HPD1 |})%dist_state). {  
                        rewrite dst_add_0_r. 
                        apply Peq_implies_get_b_Peq with (b:= b) in Hadd; try assumption. }
        assert (Hnotb_eq: mu pd_notb == (mu (extract_notb_pd b pd1_ori)  +
                                         mu {| dom := dom1; mu := []; all_partial := HPD1 |})%dist_state). {
                        rewrite dst_add_0_r. 
                        apply Peq_implies_get_notb_Peq with (b:= b) in Hadd; try assumption. }
        apply IHc1 with (pd1:= {| dom := dom1; mu := []; all_partial := HPD1 |}) 
                        (pd0:= extract_b_pd b pd1_ori) in H7; try assumption; 
        apply IHc2 with (pd1:= {| dom := dom1; mu := []; all_partial := HPD1 |}) 
                        (pd0:= extract_notb_pd b pd1_ori) in H8; try assumption.
        + destruct H8. destruct H. destruct H. destruct H0. destruct H1.
          destruct H7. destruct H7. destruct H7. destruct H10. destruct H11.
          assert (Hdom02: (dom x1 == dom x)%domain). { destruct H8. destruct H14.
            apply orbdom_after_NS in H7. apply orbdom_after_NS in H. 
            apply dom_equiv_trans with (l1:= (dom (extract_b_pd b pd1_ori) ∪ get_modvar_in_winstr c1)%domain); try assumption.
            apply dom_equiv_sym.
            apply dom_equiv_trans with (l1:= (dom (extract_notb_pd b pd1_ori) ∪ get_modvar_in_winstr c2)%domain); try assumption.
            simpl. destruct H6.
            - apply dom_eq_orb_compat_left. apply dom_equiv_sym. assumption.
            - destruct H6. destruct Hdom. simpl in H17. 
              apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c2); try assumption.
              + apply dom_eq_orb_compat_right. apply dom_equiv_sym. assumption.
              + apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c1); try assumption. 
                * apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H17.
                  apply dom_equiv_sym in H17. apply dom_equiv_trans with (l1:= dom pd); try assumption.
                * apply dom_eq_orb_compat_right. assumption. }
          exists (pd_add x1 x (Hdom02)), (pd_emp (dom1 ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI))). 
          split. { eapply NS_IF_Mixed; try assumption.
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption. 
              - apply dst_equiv_implies_b_classify with (b:= b) in Heq'; try assumption. 
                rewrite H3 in Heq'. symmetry in Heq'. assumption. 
              - apply pd_equiv_preserves_WD_win with (pd:= pd_b); try assumption.
                destruct Hdom. rewrite dst_add_0_r in Hb_eq. split; simpl; try assumption.
              - apply pd_equiv_preserves_WD_win with (pd:= pd_notb); try assumption.
                destruct Hdom. rewrite dst_add_0_r in Hnotb_eq. split; simpl; try assumption.
              - destruct H6. 
                + left. assumption.
                + destruct H6. right. simpl. destruct Hdom. 
                  split; apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply H7.
              - apply H.
              - simpl. reflexivity.
              - simpl. apply dom_equiv_refl.
              - simpl. assumption. }
          split. { apply (@NS_IF_Nil b c1 c2 {| dom := dom1; mu := []; all_partial := HPD1 |}).
            - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
            - unfold b_supp_classify. simpl. reflexivity.
            - apply pd_decom_l_preserves_WD_win with (c:= c1) in Hb_eq; try assumption. 
              rewrite dst_add_0_r. assumption.
            - apply pd_decom_l_preserves_WD_win with (c:= c2) in Hnotb_eq; try assumption.
              rewrite dst_add_0_r. try assumption. 
            - exists x2. split; try assumption. split; simpl. 
              + apply orbdom_after_NS in H10. apply dom_equiv_sym. assumption.
              + apply NS_pd_implies_nil in H10. destruct H10. rewrite H10. apply dst_equiv_refl.
            - exists x0. split; try assumption. split; simpl. 
              + apply orbdom_after_NS in H0. apply dom_equiv_sym. assumption.
              + apply NS_pd_implies_nil in H0. destruct H0. rewrite H0. apply dst_equiv_refl. }
          split. { simpl. rewrite H9.
              apply NS_pd_implies_nil in H10. destruct H10. rewrite H10 in H11. rewrite dst_add_0_r in H11.
              apply NS_pd_implies_nil in H0. destruct H0. rewrite H0 in H1. rewrite dst_add_0_r in H1.
              rewrite dst_add_0_r. 
              apply dst_add_preserves_equiv; assumption. }
          simpl. split; try assumption.
          * destruct H14. apply orbdom_after_NS in HNS. simpl in HNS.  
            apply orbdom_after_NS in H7. simpl in H7. apply dom_equiv_sym in H7.
            apply dom_equiv_trans with (l1:= (dom pd ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2))%domain); try assumption.
            apply dom_equiv_trans with (l1:= (dom0 ∪ get_modvar_in_winstr c1)%domain); try assumption.
            destruct Hdom. 
            apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c1); try assumption.
              ** destruct H6. 
                -- apply dom_eq_orb_compat_left. apply dom_equiv_sym.
                apply orb_domain_elim_r. destruct H6. assumption.
                -- destruct H6. apply dom_equiv_trans with (l1:= 
                    (dom pd ∪ get_modvar_in_winstr c1) ∪ (dom pd ∪ get_modvar_in_winstr c2)); try apply dom_eq_orb_dis_r.
                apply dom_equiv_sym. 
                apply orb_domain_elim_r. apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H18. 
                apply dom_equiv_trans with (l1:= dom pd); try assumption.
                apply dom_equiv_sym. assumption.
              ** apply dom_eq_orb_compat_right. assumption. 
          * apply orbdom_after_NS in HNS. simpl in HNS. 
            apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI)); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
        + rewrite dst_add_0_r. try assumption. 
        + rewrite dst_add_0_r. try assumption. 
        + rewrite dst_add_0_r. try assumption. 
    }
    { 
      pose (pd0:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
      pose (pd1:= {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}).
      assert (Hadd_sym: mu pd == (mu pd1 + mu pd0)%dist_state). {
        apply dst_equiv_trans with (mu1:= (mu {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |} +
                     mu {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |})%dist_state); try assumption.
        apply dst_add_comm. }
      assert (HVl_sym: Valid_dist (mu pd1 + mu pd0)%dist_state). {
        rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq.
          apply Valid_linear_under_eq_prob; try assumption; try apply Valid_mult_cofe; try assumption; try apply Rle_0_1.
         rewrite Rplus_comm. repeat rewrite Rmult_1_l. rewrite <- dst_sum_prob_decom.
          destruct Hvl. assumption. }
      inversion HNS; subst.
      - apply pd_Nil_mu in H3. rewrite H3 in Hadd. apply dst_equiv_sym in Hadd. 
        simpl in Hadd. 
        + apply dst_cons_valid_contra in Hadd; try assumption; try contradiction. 
      - apply IHc1 with (pd0:= pd0) (pd1:= pd1) in H9; try assumption.
        destruct H9. destruct H. destruct H. destruct H0. destruct H1.
        exists x, x0.
        split. { apply NS_IF_All_True; try assumption. 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply bT_classify_decom_r with (pd0:= pd0) (pd1:= pd1) in H3; try assumption.
              * unfold not. intros. discriminate.
              * simpl. destruct Hdom. assumption.
              * simpl. destruct Hdom. assumption.
          - apply pd_decom_r_preserves_WD_win with (pd0:= pd0) (pd1:= pd1) in H4; try assumption.
          - apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
            + apply Valid_dist_nil.
            + apply Valid_dist_nil.
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl. 
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c1); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          - destruct H10. destruct H8. 
            apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}))) in H9; try assumption.
            + destruct H9. destruct H9. exists x2. split; try assumption. split; simpl.
              * apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym. assumption.
              * apply NS_mu_implies_nil in H10; try reflexivity. rewrite H10. apply dst_equiv_refl.
            + apply Valid_dist_nil.
            + apply Valid_dist_nil.
            + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
              * apply Valid_dist_nil.
              * apply Valid_dist_nil.
              * destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
           }
        split. {
          apply NS_IF_All_True; try assumption. 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply bT_classify_decom_r with (pd0:= pd1) (pd1:= pd0) in H3; try assumption.
              * simpl. unfold not. intros. discriminate.
              * simpl. destruct Hdom. assumption.
              * simpl. destruct Hdom. assumption.
          - apply pd_decom_r_preserves_WD_win with (pd0:= pd1) (pd1:= pd0) in H4; try assumption.
            simpl in Hdom. destruct Hdom. split; assumption.
          - apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
            + apply Valid_dist_nil.
            + apply Valid_dist_nil.
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c1); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          - destruct H10. destruct H8. 
            apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}))) in H9; try assumption.
            + destruct H9. destruct H9. exists x2. split; try assumption. split; simpl. 
              * apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym. assumption.
              * apply NS_mu_implies_nil in H10; try reflexivity. rewrite H10. apply dst_equiv_refl.
            + apply Valid_dist_nil.
            + apply Valid_dist_nil.
            + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
              * apply Valid_dist_nil.
              * apply Valid_dist_nil.
              * destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
          }
        split; try assumption.
      - apply IHc2 with (pd0:= pd0) (pd1:= pd1) in H9; try assumption.
        destruct H9. destruct H. destruct H. destruct H0. destruct H1.
        exists x, x0.
        split. { apply NS_IF_All_False; try assumption. 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply bF_classify_decom_r with (pd0:= pd0) (pd1:=pd1) in H3; try assumption.
              * simpl. unfold not. intros. discriminate.
              * simpl. destruct Hdom. assumption.
              * simpl. destruct Hdom. assumption.
          - apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
            + apply Valid_dist_nil.
            + apply Valid_dist_nil.
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
          - apply pd_decom_r_preserves_WD_win with (pd0:= pd0) (pd1:= pd1) in H5; try assumption.
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c2); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          - destruct H10. destruct H8.
            apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}))) in H9; try assumption.
            + destruct H9. destruct H9. exists x2. split; try assumption. split; simpl. 
              * apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym. assumption.
              * apply NS_mu_implies_nil in H10; try reflexivity. rewrite H10. apply dst_equiv_refl.
            + apply Valid_dist_nil.
            + apply Valid_dist_nil.
            + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
              * apply Valid_dist_nil.
              * apply Valid_dist_nil.
              * destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
           }
        split. { apply NS_IF_All_False; try assumption. 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply bF_classify_decom_r with (pd0:= pd1) (pd1:= pd0) in H3; try assumption.
              * simpl. unfold not. intros. discriminate.
              * simpl. destruct Hdom. assumption.
              * simpl. destruct Hdom. assumption.
          - apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
            + apply Valid_dist_nil.
            + apply Valid_dist_nil.
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
          - apply pd_decom_r_preserves_WD_win with (pd0:= pd1) (pd1:= pd0) in H5; try assumption.
            simpl. simpl in Hdom. destruct Hdom. split; assumption.
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c2); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          - destruct H10. destruct H8.
            apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}))) in H9; try assumption.
            + destruct H9. destruct H9. exists x2. split; try assumption. split; simpl. 
              * apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym. assumption.
              * apply NS_mu_implies_nil in H10; try reflexivity. rewrite H10. apply dst_equiv_refl.
            + apply Valid_dist_nil.
            + apply Valid_dist_nil.
            + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
              * apply Valid_dist_nil.
              * apply Valid_dist_nil.
              * destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl. }
        split; try assumption.
      - specialize IHc1 with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (pd:= pd_b) (pd':= pd3); try assumption.
        assert (Hvalid_mub0: Valid_dist (get_b_in_mu b (mu pd0))). { apply dst_Valid_get_b; assumption. }
        assert (Hvalid_mub1: Valid_dist (get_b_in_mu b (mu pd1))). { apply dst_Valid_get_b; assumption. }
        assert (Hvalid_mub: Valid_dist (mu pd_b)). { apply dst_Valid_get_b; assumption. }
        assert (Hvlb': Valid_dist (mu (extract_b_pd b pd0) + mu (extract_b_pd b pd1))%dist_state). {
          rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq.
          apply Valid_linear_under_eq_prob; try assumption; try lra. 
          rewrite <- Rmult_plus_distr_l. rewrite Rmult_1_l. 
          destruct Hvl. rewrite dst_sum_prob_decom in H.
          split. 
          - rewrite <- Rplus_0_r with (r:= 0). destruct Hvalid_mub0; destruct Hvalid_mub1. apply Rplus_le_compat; intuition.
          - destruct H. apply Rle_trans with (r2:= sum_probs (mu {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}) +
              sum_probs (mu {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |})); try assumption.
            apply Rplus_le_compat; try apply sum_prob_get_b_le; try assumption.
          }
        assert (Hvalid_munb0: Valid_dist (get_notb_in_mu b (mu pd0))). { apply dst_Valid_get_notb; assumption. }
        assert (Hvalid_munb1: Valid_dist (get_notb_in_mu b (mu pd1))). { apply dst_Valid_get_notb; assumption. }
        assert (Hvalid_munb: Valid_dist (mu pd_notb)). { apply dst_Valid_get_notb; assumption. }
        assert (Hvlnotb': Valid_dist (mu (extract_notb_pd b pd0) + mu (extract_notb_pd b pd1))%dist_state). { 
          rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq.
          apply Valid_linear_under_eq_prob; try assumption; try lra. 
          rewrite <- Rmult_plus_distr_l. rewrite Rmult_1_l. 
          destruct Hvl. rewrite dst_sum_prob_decom in H.
          split. 
          - rewrite <- Rplus_0_r with (r:= 0). destruct Hvalid_munb0; destruct Hvalid_munb1. apply Rplus_le_compat; intuition.
          - destruct H. apply Rle_trans with (r2:= sum_probs (mu {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}) +
              sum_probs (mu {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |})); try assumption.
            apply Rplus_le_compat; try apply sum_prob_get_notb_le; try assumption. }
        assert (Hmub: (mu pd_b == get_b_in_mu b (mu pd0) + get_b_in_mu b (mu pd1))%dist_state). { 
          repeat rewrite <- dst_get_b_coef_mult. rewrite <- get_b_assoc.
          apply Peq_implies_get_b_Peq; try assumption. }
        specialize (IHc1 Hvalid_mub0 Hvalid_mub1 Hvlb' Hvalid_mub Hmub).
        apply IHc1 in H7; try assumption.
        destruct H7 as [mu01 Htemp]. destruct Htemp as [mu11 Htemp]. 
        destruct Htemp as [HNSmu0 Htemp]. destruct Htemp as [HNSmu1 Hmu1]. 
        destruct Hmu1 as [Hmu1 Hdom1].
        specialize IHc2 with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (pd:= pd_notb) (pd':= pd4); try assumption.
        assert (Hmunb: (mu pd_notb == get_notb_in_mu b (mu pd0) + get_notb_in_mu b (mu pd1))%dist_state). { 
          repeat rewrite <- dst_get_notb_coef_mult. rewrite <- get_notb_assoc.
          apply Peq_implies_get_notb_Peq; try assumption. } 
        apply IHc2 in H8; try assumption.
        destruct H8 as [mu02 Htemp]. destruct Htemp as [mu12 Htemp]. 
        destruct Htemp as [HNSmu01 Htemp]. destruct Htemp as [HNSmu11 Hmu2].
        destruct Hmu2 as [Hmu2 Hdom2].

        destruct (b_supp_classify b {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}) eqn: HB0. {
            unfold b_supp_classify in HB0. simpl in HB0. 
            destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s0, p0) :: mu0')));
            destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s0, p0) :: mu0'))); try discriminate. }
        { destruct (b_supp_classify b {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}) eqn: HB1.
          - unfold b_supp_classify in HB1. simpl in HB1. 
            destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s1, p1) :: mu1')));
            destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s1, p1) :: mu1'))); try discriminate.
          - assert (Heq0: (extract_b_pd b pd0) ≡ pd0). { apply bT_supp_implies_getb_eq; try assumption. }
            assert (Heq1: (extract_b_pd b pd1) ≡ pd1). { apply bT_supp_implies_getb_eq; try assumption. }
            assert (HWDb11: well_defined_winstr_with_pd c1 (extract_b_pd b pd1)). { 
              apply pd_decom_l_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) in H4; try assumption. }
            assert (HWDb10: well_defined_winstr_with_pd c1 (extract_b_pd b pd0)). { 
              apply pd_decom_r_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1))in H4; try assumption. } 
            assert (HWD11: well_defined_winstr_with_pd c1 pd1). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd1) in HWDb11; try assumption. }
            assert (HWD10: well_defined_winstr_with_pd c1 pd0). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd0) in HWDb10; try assumption. }
            apply step_deterministic with (pd1:= pd0) in HNSmu0; try assumption; 
            apply step_deterministic with (pd1:= pd1) in HNSmu1; try assumption.
            destruct HNSmu0 as [mu01' Htemp0]. destruct Htemp0. 
            destruct HNSmu1 as [mu11' Htemp1]. destruct Htemp1.
              exists mu01', mu11'. 
              split. { apply NS_IF_All_True; try assumption. 
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - apply pd_decom_r_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1))in H5; try assumption.
                  apply pd_equiv_preserves_WD_win with (pd:= (extract_notb_pd b pd0)) ; try assumption.
                  + apply Valid_dist_nil.
                  + simpl. apply bT_getnotb_nil in HB0. simpl in HB0. split; simpl; try apply dom_equiv_refl.
                  rewrite HB0. apply dst_equiv_refl.
                - simpl. destruct H6. 
                  + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom0) in H8. assumption.
                  + destruct H6. 
                    apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c1)%domain) .
                    * apply dom_subset_orb_dom_r. assumption.
                    * apply dom_subset_orb_compat; try apply dom_subset_refl.
                    destruct Hdom. destruct H10. assumption.
                - apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}))) in HNSmu01; try assumption. 
                  + destruct HNSmu01. destruct H8. exists x. split; try assumption. 
                    split; simpl; try assumption. 
                    * apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym. assumption.
                    * apply NS_pd_implies_nil in H10. destruct H10. rewrite H10. apply dst_equiv_refl.
                  + apply Valid_dist_nil.
                  + apply pd_decom_r_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption.
                  + apply pd_decom_r_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption.
                    apply pd_equiv_preserves_WD_win with (pd:= (extract_notb_pd b pd0)) ; try assumption.
                    * apply Valid_dist_nil.
                    * simpl. apply bT_getnotb_nil in HB0. simpl in HB0. split; simpl; try apply dom_equiv_refl. 
                    rewrite HB0. apply dst_equiv_refl.
                  + apply bT_getnotb_nil in HB0. simpl in HB0. split; simpl; try apply dom_equiv_refl. 
                    rewrite HB0. apply dst_equiv_refl.
                 }
              split. { apply NS_IF_All_True; try assumption.
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - apply pd_decom_l_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption.
                  apply pd_equiv_preserves_WD_win with (pd:= (extract_notb_pd b pd1)); try assumption.
                  + apply Valid_dist_nil.
                  + simpl. apply bT_getnotb_nil in HB1. simpl in HB1. split; simpl; try apply dom_equiv_refl.
                  rewrite HB1. apply dst_equiv_refl.
                - simpl. destruct H6. 
                  + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom1) in H8. assumption.
                  + destruct H6. 
                    apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c1)%domain) .
                    * apply dom_subset_orb_dom_r. assumption.
                    * apply dom_subset_orb_compat; try apply dom_subset_refl.
                    destruct Hdom. destruct H11. assumption.
                - apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}))) in HNSmu11; try assumption. 
                  + destruct HNSmu11. destruct H8. exists x. split; try assumption. 
                    split; simpl; try assumption. 
                    * apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym. assumption.
                    * apply NS_pd_implies_nil in H10. destruct H10. rewrite H10. apply dst_equiv_refl.
                  + apply Valid_dist_nil.
                  + apply pd_decom_l_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption.
                  + apply pd_decom_l_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption.
                    apply pd_equiv_preserves_WD_win with (pd:= (extract_notb_pd b pd1)) ; try assumption.
                    * apply Valid_dist_nil.
                    * simpl. apply bT_getnotb_nil in HB1. simpl in HB1. split; simpl; try apply dom_equiv_refl. 
                    rewrite HB1. apply dst_equiv_refl.
                  + apply bT_getnotb_nil in HB1. simpl in HB1. split; simpl; try apply dom_equiv_refl. 
                    rewrite HB1. apply dst_equiv_refl.
                }
              split; simpl; try assumption. { 
                rewrite H9.
                apply dst_equiv_trans with (mu1:= ((mu mu01 + mu mu11) + (mu mu02 + mu mu12))%dist_state).
                - apply dst_add_preserves_equiv; try assumption.
                - apply bT_getnotb_nil in HB0. 
                  apply NS_mu_implies_nil in HNSmu01; try assumption. rewrite HNSmu01.
                  apply bT_getnotb_nil in HB1. 
                  apply NS_mu_implies_nil in HNSmu11; try assumption. rewrite HNSmu11.
                  simpl. rewrite dst_add_0_r. destruct H. destruct H1.
                  apply dst_add_preserves_equiv; try apply dst_mult_preserves_equiv; assumption. }
              simpl. split; try assumption. 
              * apply dom_equiv_trans with (l1:= dom pd3); try assumption.  
                destruct Hdom1. apply dom_equiv_trans with (l1:= dom mu01); try assumption.
                destruct H. assumption.
              * apply dom_equiv_trans with (l1:= dom pd3); try assumption.  
                destruct Hdom1. apply dom_equiv_trans with (l1:= dom mu11); try assumption.
                destruct H1. assumption.
          - assert (Heq0: (extract_b_pd b pd0) ≡ pd0). { apply bT_supp_implies_getb_eq; try assumption. }
            assert (Heq1: (extract_notb_pd b pd1) ≡ pd1). { apply bF_supp_implies_getnotb_eq; try assumption.  }
            assert (HWDb11: well_defined_winstr_with_pd c2 (extract_notb_pd b pd1)). { 
              apply pd_decom_l_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption. }
            assert (HWDb10: well_defined_winstr_with_pd c1 (extract_b_pd b pd0)). { 
              apply pd_decom_r_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) in H4; try assumption. } 
            assert (HWD11: well_defined_winstr_with_pd c2 pd1). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd1) in HWDb11; try assumption. }
            assert (HWD10: well_defined_winstr_with_pd c1 pd0). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd0) in HWDb10; try assumption. }
            apply step_deterministic with (pd1:= pd0) in HNSmu0; try assumption; 
            apply step_deterministic with (pd1:= pd1) in HNSmu11; try assumption.
            destruct HNSmu0 as [mu01' Htemp0]. destruct Htemp0. 
            destruct HNSmu11 as [mu12' Htemp1]. destruct Htemp1.
            exists mu01', mu12'. 
              split. { apply NS_IF_All_True; try assumption. 
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - apply pd_decom_r_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption.
                  apply pd_equiv_preserves_WD_win with (pd:= (extract_notb_pd b pd0)) ; try assumption.
                  + apply Valid_dist_nil.
                  + simpl. apply bT_getnotb_nil in HB0. simpl in HB0. split; simpl; try apply dom_equiv_refl.
                  rewrite HB0. apply dst_equiv_refl.
                - simpl. destruct H6. 
                  + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom0) in H8. assumption.
                  + destruct H6. 
                    apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c1)%domain) .
                    * apply dom_subset_orb_dom_r. assumption.
                    * apply dom_subset_orb_compat; try apply dom_subset_refl.
                    destruct Hdom. destruct H10. assumption.
                - apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}))) in HNSmu01; try assumption. 
                  + destruct HNSmu01. destruct H8. exists x. split; try assumption. 
                    split; simpl; try assumption. 
                    * apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym. assumption.
                    * apply NS_pd_implies_nil in H10. destruct H10. rewrite H10. apply dst_equiv_refl.
                  + apply Valid_dist_nil.
                  + apply pd_decom_r_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption.
                  + apply pd_decom_r_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption.
                    apply pd_equiv_preserves_WD_win with (pd:= (extract_notb_pd b pd0)) ; try assumption.
                    * apply Valid_dist_nil.
                    * simpl. apply bT_getnotb_nil in HB0. simpl in HB0. split; simpl; try apply dom_equiv_refl. 
                    rewrite HB0. apply dst_equiv_refl.
                  + apply bT_getnotb_nil in HB0. simpl in HB0. split; simpl; try apply dom_equiv_refl. 
                    rewrite HB0. apply dst_equiv_refl. }
              split. { apply NS_IF_All_False; try assumption.
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - apply pd_decom_l_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) in H4; try assumption.
                  apply pd_equiv_preserves_WD_win with (pd:= (extract_b_pd b pd1)) ; try assumption.
                    * apply Valid_dist_nil.
                    * simpl. apply bF_getnotb_nil in HB1. simpl in HB1. split; simpl; try apply dom_equiv_refl. 
                    rewrite HB1. apply dst_equiv_refl.
                - simpl. destruct H6. 
                  + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom1) in H6. assumption.
                  + destruct H6. 
                    apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c2)%domain) .
                    * apply dom_subset_orb_dom_r. assumption.
                    * apply dom_subset_orb_compat; try apply dom_subset_refl.
                    destruct Hdom. destruct H11. assumption.
                - apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}))) in HNSmu1; try assumption.
                  + destruct HNSmu1. destruct H8. exists x. split; try assumption. 
                    simpl. split; simpl; try assumption. 
                    * apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym. assumption.
                    * apply NS_pd_implies_nil in H10. destruct H10. rewrite H10. apply dst_equiv_refl.
                  + apply Valid_dist_nil.
                  + apply pd_decom_l_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) in H4; try assumption.
                  + apply pd_decom_l_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) in H4; try assumption.
                    apply pd_equiv_preserves_WD_win with (pd:= (extract_b_pd b pd1)) ; try assumption.
                    * apply Valid_dist_nil.
                    * simpl. apply bF_getnotb_nil in HB1. simpl in HB1. split; simpl; try apply dom_equiv_refl. 
                    rewrite HB1. apply dst_equiv_refl.
                  + apply bF_getnotb_nil in HB1. simpl in HB1. split; simpl; try apply dom_equiv_refl. 
                    rewrite HB1. apply dst_equiv_refl.
                }
              split; simpl; try assumption. { 
                rewrite H9.
                apply dst_equiv_trans with (mu1:= ((mu mu01 + mu mu11) + (mu mu02 + mu mu12))%dist_state).
                - apply dst_add_preserves_equiv; try assumption.
                - apply bT_getnotb_nil in HB0. 
                  apply NS_mu_implies_nil in HNSmu01; try assumption. rewrite HNSmu01.
                  apply bF_getnotb_nil in HB1. 
                  apply NS_mu_implies_nil in HNSmu1; try assumption. rewrite HNSmu1.
                  simpl. rewrite dst_add_0_r. destruct H. destruct H1.
                  apply dst_add_preserves_equiv; try apply dst_mult_preserves_equiv; assumption.
                }
              simpl. split; try assumption. 
              * apply dom_equiv_trans with (l1:= dom pd3); try assumption.  
                destruct Hdom1. apply dom_equiv_trans with (l1:= dom mu01); try assumption.
                destruct H. assumption.
              * apply orbdom_after_NS in HNS. simpl in HNS.
                apply dom_equiv_trans with (l1:= (dom pd ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2))%domain); try assumption.
                apply orbdom_after_NS in H7. simpl in H7. apply dom_equiv_sym in H7.
                apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c2)%domain); try assumption.
                apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c2)%domain) .
              ** destruct H6. 
                -- apply dom_eq_orb_compat_left. rewrite orb_domain_comm. apply dom_equiv_sym.
                apply orb_domain_elim_r. destruct H6. assumption.
                -- destruct H6. apply dom_equiv_trans with (l1:= 
                    (dom pd ∪ get_modvar_in_winstr c1) ∪ (dom pd ∪ get_modvar_in_winstr c2)); try apply dom_eq_orb_dis_r.
                apply dom_equiv_sym. rewrite orb_domain_comm with (l:= (dom pd ∪ get_modvar_in_winstr c1) ). 
                apply orb_domain_elim_r. apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H8. 
                apply dom_equiv_trans with (l1:= dom pd); try assumption.
                apply dom_equiv_sym. assumption.
              ** destruct Hdom. apply dom_eq_orb_compat_right. assumption. 
          - assert (Heq0: (extract_b_pd b pd0) ≡ pd0). { apply bT_supp_implies_getb_eq; try assumption. }
            assert (Heqn0: (extract_notb_pd b pd0) ≡ pd_emp (dom pd0)). { 
              apply bT_getnotb_nil in HB0. simpl in HB0. split; simpl; try apply dom_equiv_refl.
              rewrite HB0. apply dst_equiv_refl.  }
            assert (HWDnb21: well_defined_winstr_with_pd c2 (extract_notb_pd b pd1)). { 
              apply pd_decom_l_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption. }
            assert (HWDb10: well_defined_winstr_with_pd c1 (extract_b_pd b pd0)). { 
              apply pd_decom_r_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) in H4; try assumption. } 
            assert (HWDb11: well_defined_winstr_with_pd c1 (extract_b_pd b pd1)). { 
               apply pd_decom_l_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) in H4; try assumption. } 
            assert (HWDnb20: well_defined_winstr_with_pd c2 (extract_notb_pd b pd0)). { 
              apply pd_decom_r_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption. }
            assert (HWD20: well_defined_winstr_with_pd c2
                        (pd_emp (dom {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}))). {
                apply pd_equiv_preserves_WD_win with (pd:= (extract_notb_pd b pd0)); try assumption.
                apply Valid_dist_nil. }
            assert (HWD10: well_defined_winstr_with_pd c1 pd0). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd0) in HWDb10; try assumption. }
            apply step_deterministic with (pd1:= pd0) in HNSmu0; try assumption; 
            apply step_deterministic with (pd1:= (extract_b_pd b pd1)) in HNSmu1; try assumption;
            apply step_deterministic with (pd1:= (extract_notb_pd b pd1)) in HNSmu11; try assumption; try apply pd_equiv_refl.
            destruct HNSmu0 as [mu01' Htemp0]. destruct Htemp0. 
            destruct HNSmu11 as [mu12' Htemp1]. destruct Htemp1.
            destruct HNSmu1 as [mu11' Htemp2]. destruct Htemp2.
            assert (Hdom02: (dom mu11' == dom mu12')%domain). { 
              apply orbdom_after_NS in H7. apply orbdom_after_NS in H10. 
              apply dom_equiv_trans with (l1:= (dom (extract_b_pd b pd1) ∪ get_modvar_in_winstr c1)%domain); try assumption.
              apply dom_equiv_sym.
              apply dom_equiv_trans with (l1:= (dom (extract_notb_pd b pd1) ∪ get_modvar_in_winstr c2)%domain); try assumption.
              simpl. destruct H6.
              - apply dom_eq_orb_compat_left. apply dom_equiv_sym. assumption.
              - destruct H6. destruct Hdom. simpl in H14. 
                apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c2); try assumption.
                + apply dom_eq_orb_compat_right. apply dom_equiv_sym. assumption.
                + apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c1); try assumption. 
                  * apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H11.
                    apply dom_equiv_sym in H11. apply dom_equiv_trans with (l1:= dom pd); try assumption.
                  * apply dom_eq_orb_compat_right. assumption. }
            exists mu01', (pd_add mu11' mu12' (Hdom02)). 
            split. { apply NS_IF_All_True; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - simpl. destruct H6. 
                + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom0) in H11. assumption.
                + destruct H6. 
                  apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c1)%domain) .
                  * apply dom_subset_orb_dom_r. assumption.
                  * apply dom_subset_orb_compat; try apply dom_subset_refl.
                  destruct Hdom. destruct H14. assumption.
              - apply step_deterministic with (pd1:= pd_emp (dom pd0)) in HNSmu01; try assumption; try apply Valid_dist_nil.
                destruct HNSmu01. destruct H11. exists x. split; try assumption. 
                split; simpl. 
                * apply orbdom_after_NS in H14. apply dom_equiv_sym. assumption.
                * apply NS_pd_implies_nil in H14. destruct H14. rewrite H14. apply dst_equiv_refl. }
            split. { eapply NS_IF_Mixed; try assumption.
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - simpl. destruct H6. 
                + left. assumption.
                + right. destruct H6. destruct Hdom. 
                split; apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply H10.
              - apply H7.
              - simpl. reflexivity.
              - simpl. apply dom_equiv_refl.
              - simpl. assumption. }
            split; simpl; try assumption. { 
              rewrite H9.
              apply dst_equiv_trans with (mu1:= ((mu mu01 + mu mu11) + (mu mu02 + mu mu12))%dist_state).
              - apply dst_add_preserves_equiv; try assumption.
              - apply bT_getnotb_nil in HB0. 
                apply NS_mu_implies_nil in HNSmu01; try assumption. rewrite HNSmu01. simpl. 
                rewrite dst_add_assoc_eq. 
                destruct H. destruct H1. destruct H8.
                apply dst_add_preserves_equiv; try apply dst_add_preserves_equiv; try try apply dst_mult_preserves_equiv; try assumption.
              }
            simpl. split; try assumption. 
            * apply dom_equiv_trans with (l1:= dom pd3); try assumption.  
              destruct Hdom1. apply dom_equiv_trans with (l1:= dom mu01); try assumption.
              destruct H. assumption.
            * apply orbdom_after_NS in HNS. simpl in HNS.
              apply dom_equiv_trans with (l1:= (dom pd ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2))%domain); try assumption.
              apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym in H10.
              apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c1)%domain); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c1)%domain) .
              ** destruct H6. 
                -- apply dom_eq_orb_compat_left. apply dom_equiv_sym.
                apply orb_domain_elim_r. destruct H6. assumption.
                -- destruct H6. apply dom_equiv_trans with (l1:= 
                    (dom pd ∪ get_modvar_in_winstr c1) ∪ (dom pd ∪ get_modvar_in_winstr c2)); try apply dom_eq_orb_dis_r.
                apply dom_equiv_sym. 
                apply orb_domain_elim_r. apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H11. 
                apply dom_equiv_trans with (l1:= dom pd); try assumption.
                apply dom_equiv_sym. assumption.
              ** destruct Hdom. apply dom_eq_orb_compat_right. assumption. 
        }
        { destruct (b_supp_classify b {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}) eqn: HB1.
          - unfold b_supp_classify in HB1. simpl in HB1. 
            destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s1, p1) :: mu1')));
            destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s1, p1) :: mu1'))); try discriminate.
          - assert (Heq0: (extract_notb_pd b pd0) ≡ pd0). { apply bF_supp_implies_getnotb_eq; try assumption.  }
            assert (Heq1: (extract_b_pd b pd1) ≡ pd1). { apply bT_supp_implies_getb_eq; try assumption. }
            assert (Heqb0: extract_b_pd b pd0 ≡ pd_emp (dom pd0)). { 
              apply bF_getnotb_nil in HB0; try assumption. 
              split; simpl; try apply dom_equiv_refl.
              simpl in HB0. rewrite HB0. apply dst_equiv_refl.  }
            assert (Heqb1: extract_notb_pd b pd1 ≡ pd_emp (dom pd1)). { 
              apply bT_getnotb_nil in HB1; try assumption. 
              split; simpl; try apply dom_equiv_refl.
              simpl in HB1. rewrite HB1. apply dst_equiv_refl.  }
            assert (HWDb11: well_defined_winstr_with_pd c1 (extract_b_pd b pd1)). { 
              apply pd_decom_l_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) in H4; try assumption. }
            assert (HWDb10: well_defined_winstr_with_pd c1 (extract_b_pd b pd0)). { 
              apply pd_decom_r_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) in H4; try assumption. } 
            assert (HWD1: well_defined_winstr_with_pd c1 (pd_emp (dom0))). { 
              apply pd_equiv_preserves_WD_win with (pd:= extract_b_pd b pd0); try assumption.
              apply Valid_dist_nil. }
            assert (HWD11: well_defined_winstr_with_pd c1 pd1). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd1) in HWDb11; try assumption. }
            assert (HWDnb20: well_defined_winstr_with_pd c2 (extract_notb_pd b pd0)). {
              apply pd_decom_r_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption. }
            assert (HWD2: well_defined_winstr_with_pd c2 (pd_emp (dom1))). {
              apply pd_decom_l_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption.
              apply pd_equiv_preserves_WD_win with (pd:= extract_notb_pd b pd1); try assumption.
              apply Valid_dist_nil. }
            assert (HWDnb21: well_defined_winstr_with_pd c2 (extract_notb_pd b pd1)). {
              apply pd_equiv_preserves_WD_win with (pd:= pd_emp (dom pd1)); try assumption.
              - apply Valid_dist_nil.
              - apply pd_equiv_sym. assumption.  }
            assert (HWD20: well_defined_winstr_with_pd c2 pd0). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd0) in HWDnb20; try assumption. }
            apply step_deterministic with (pd1:= pd0) in HNSmu01; try assumption; 
            apply step_deterministic with (pd1:= pd1) in HNSmu1; try assumption.
            destruct HNSmu01 as [mu02' Htemp0]. destruct Htemp0. 
            destruct HNSmu1 as [mu11' Htemp1]. destruct Htemp1.
            exists mu02', mu11'. 
            split. { apply NS_IF_All_False; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - simpl. destruct H6. 
                + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom0) in H6. assumption.
                + destruct H6. 
                  apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c2)%domain) .
                  * apply dom_subset_orb_dom_r. assumption.
                  * apply dom_subset_orb_compat; try apply dom_subset_refl.
                  destruct Hdom. destruct H10. assumption.
              - apply step_deterministic with (pd1:= pd_emp (dom pd0)) in HNSmu0; try assumption; try apply Valid_dist_nil.
                destruct HNSmu0. destruct H8. exists x. split; try assumption.
                apply NS_pd_implies_nil in H10. destruct H10. apply dom_equiv_sym in H11.
                split; simpl; try assumption. rewrite H10. apply dst_equiv_refl. }
            split. { apply NS_IF_All_True; try assumption.
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - simpl. destruct H6. 
                + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom1) in H8. assumption.
                + destruct H6. 
                  apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c1)%domain) .
                  * apply dom_subset_orb_dom_r. assumption.
                  * apply dom_subset_orb_compat; try apply dom_subset_refl.
                  destruct Hdom. destruct H11. assumption.
              - apply step_deterministic with (pd1:= pd_emp (dom pd1)) in HNSmu11; try assumption; try apply Valid_dist_nil.
                destruct HNSmu11. destruct H8. exists x. split; try assumption.
                apply NS_pd_implies_nil in H10. destruct H10. apply dom_equiv_sym in H11.
                split; simpl; try assumption. rewrite H10. apply dst_equiv_refl. 
                }
            split; simpl; try assumption. { 
              rewrite H9.
              apply dst_equiv_trans with (mu1:= ((mu mu01 + mu mu11) + (mu mu02 + mu mu12))%dist_state).
              - apply dst_add_preserves_equiv; try assumption.
              - apply bF_getnotb_nil in HB0. 
                apply NS_mu_implies_nil in HNSmu0; try assumption. rewrite HNSmu0.
                apply bT_getnotb_nil in HB1. 
                apply NS_mu_implies_nil in HNSmu11; try assumption. rewrite HNSmu11.
                simpl. rewrite dst_add_0_r. destruct H. destruct H1.
                apply dst_equiv_trans with (mu1:= (mu mu02 + mu mu11)%dist_state); try apply dst_add_comm.
                apply dst_add_preserves_equiv; try apply dst_mult_preserves_equiv; assumption. }
            simpl. split; try assumption. 
            * apply dom_equiv_trans with (l1:= dom pd4); try assumption.
              destruct Hdom2. destruct H. 
              apply dom_equiv_trans with (l1:= dom mu02); try assumption.
            * apply dom_equiv_trans with (l1:= dom pd3); try assumption.   
              destruct Hdom1. apply dom_equiv_trans with (l1:= dom mu11); try assumption.
              destruct H1. assumption.
          - assert (Heq0: (extract_notb_pd b pd0) ≡ pd0). { apply bF_supp_implies_getnotb_eq; try assumption.  }
            assert (Heq1: (extract_notb_pd b pd1) ≡ pd1). { apply bF_supp_implies_getnotb_eq; try assumption.  }
            assert (Heqb0: extract_b_pd b pd0 ≡ pd_emp (dom pd0)). { 
              apply bF_getnotb_nil in HB0; try assumption.
              split; simpl; try apply dom_equiv_refl.
              simpl in HB0. rewrite HB0. apply dst_equiv_refl.  }
            assert (Heqb1: extract_b_pd b pd1 ≡ pd_emp (dom pd1)). { 
              apply bF_getnotb_nil in HB1; try assumption.
              split; simpl; try apply dom_equiv_refl.
              simpl in HB1. rewrite HB1. apply dst_equiv_refl.  }
            assert (HWDb21: well_defined_winstr_with_pd c2 (extract_notb_pd b pd1)). { 
              apply pd_decom_l_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption. }
            assert (HWDb20: well_defined_winstr_with_pd c2 (extract_notb_pd b pd0)). { 
              apply pd_decom_r_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption. } 
            assert (HWD21: well_defined_winstr_with_pd c2 pd1). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd1) in HWDb21; try assumption. }
            assert (HWD20: well_defined_winstr_with_pd c2 pd0). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd0) in HWDb20; try assumption. }
            assert (HWDb10: well_defined_winstr_with_pd c1 (extract_b_pd b pd0)). {
              apply pd_decom_r_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) in H4; try assumption. } 
            assert (HWDb11: well_defined_winstr_with_pd c1 (extract_b_pd b pd1)). {
              apply pd_decom_l_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) in H4; try assumption. } 
            assert (HWD10nil: well_defined_winstr_with_pd c1 (pd_emp (dom0))). { 
              apply pd_equiv_preserves_WD_win with (pd:= extract_b_pd b pd0); try assumption.
              apply Valid_dist_nil. }
            assert (HWD11nil: well_defined_winstr_with_pd c1 (pd_emp (dom1))). { 
              apply pd_equiv_preserves_WD_win with (pd:= extract_b_pd b pd1); try assumption.
              apply Valid_dist_nil. }
            apply step_deterministic with (pd1:= pd0) in HNSmu01; try assumption; 
            apply step_deterministic with (pd1:= pd1) in HNSmu11; try assumption.
            destruct HNSmu01 as [mu02' Htemp0]. destruct Htemp0. 
            destruct HNSmu11 as [mu12' Htemp1]. destruct Htemp1.
            exists mu02', mu12'. 
              split. { apply NS_IF_All_False; try assumption. 
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - simpl. destruct H6. 
                  + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom0) in H6. assumption.
                  + destruct H6. 
                    apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c2)%domain) .
                    * apply dom_subset_orb_dom_r. assumption.
                    * apply dom_subset_orb_compat; try apply dom_subset_refl.
                    destruct Hdom. destruct H10. assumption.
                - apply step_deterministic with (pd1:= pd_emp (dom pd0)) in HNSmu0; try assumption; try apply Valid_dist_nil.
                  destruct HNSmu0. destruct H8. exists x. split; try assumption.
                  apply NS_pd_implies_nil in H10. destruct H10. apply dom_equiv_sym in H11.
                  split; simpl; try assumption. rewrite H10. apply dst_equiv_refl.  }
              split. { apply NS_IF_All_False; try assumption.
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - simpl. destruct H6. 
                  + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom1) in H6. assumption.
                  + destruct H6. 
                    apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c2)%domain) .
                    * apply dom_subset_orb_dom_r. assumption.
                    * apply dom_subset_orb_compat; try apply dom_subset_refl.
                    destruct Hdom. destruct H11. assumption.
                - apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}))) in HNSmu1; try assumption.
                  + destruct HNSmu1. destruct H8. exists x. split; try assumption. 
                    simpl. split; simpl; try assumption. 
                    * apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym. assumption.
                    * apply NS_pd_implies_nil in H10. destruct H10. rewrite H10. apply dst_equiv_refl.
                  + apply Valid_dist_nil. }
              split; simpl; try assumption. { 
                rewrite H9.
                apply dst_equiv_trans with (mu1:= ((mu mu01 + mu mu11) + (mu mu02 + mu mu12))%dist_state).
                - apply dst_add_preserves_equiv; try assumption.
                - apply bF_getnotb_nil in HB0. 
                  apply NS_mu_implies_nil in HNSmu0; try assumption. rewrite HNSmu0.
                  apply bF_getnotb_nil in HB1. 
                  apply NS_mu_implies_nil in HNSmu1; try assumption. rewrite HNSmu1.
                  simpl. destruct H. destruct H1.
                  apply dst_add_preserves_equiv; try apply dst_mult_preserves_equiv; assumption.
                }
              simpl. split; try assumption. 
              * apply dom_equiv_trans with (l1:= dom pd4); try assumption.  
                destruct Hdom2. apply dom_equiv_trans with (l1:= dom mu02); try assumption.
                destruct H. assumption.
              * apply orbdom_after_NS in HNS. simpl in HNS.
                apply dom_equiv_trans with (l1:= (dom pd ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2))%domain); try assumption.
                apply orbdom_after_NS in H7. simpl in H7. apply dom_equiv_sym in H7.
                apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c2)%domain); try assumption.
                apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c2)%domain) .
              ** destruct H6. 
                -- apply dom_eq_orb_compat_left. rewrite orb_domain_comm. apply dom_equiv_sym.
                apply orb_domain_elim_r. destruct H6. assumption.
                -- destruct H6. apply dom_equiv_trans with (l1:= 
                    (dom pd ∪ get_modvar_in_winstr c1) ∪ (dom pd ∪ get_modvar_in_winstr c2)); try apply dom_eq_orb_dis_r.
                apply dom_equiv_sym. rewrite orb_domain_comm with (l:= (dom pd ∪ get_modvar_in_winstr c1) ). 
                apply orb_domain_elim_r. apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H8. 
                apply dom_equiv_trans with (l1:= dom pd); try assumption.
                apply dom_equiv_sym. assumption.
              ** destruct Hdom. apply dom_eq_orb_compat_right. assumption. 
          - assert (Heq0: (extract_notb_pd b pd0) ≡ pd0). { apply bF_supp_implies_getnotb_eq; try assumption. }
            assert (Heqb0: extract_b_pd b pd0 ≡ pd_emp (dom pd0)). { 
              apply bF_getnotb_nil in HB0; try assumption. 
              split; simpl; try apply dom_equiv_refl.
              simpl in HB0. rewrite HB0. apply dst_equiv_refl.  }

            assert (HWDb21: well_defined_winstr_with_pd c2 (extract_notb_pd b pd1)). { 
              apply pd_decom_l_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption. }
            assert (HWDb10: well_defined_winstr_with_pd c1 (extract_b_pd b pd0)). { 
              apply pd_decom_r_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) in H4; try assumption. } 
            assert (HWD11: well_defined_winstr_with_pd c1 (extract_b_pd b pd1)). { 
               apply pd_decom_l_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) in H4; try assumption. } 
            assert (HWDnb20: well_defined_winstr_with_pd c2 (extract_notb_pd b pd0)). {
              apply pd_decom_r_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption. }
            assert (HWD20: well_defined_winstr_with_pd c2 pd0). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd0) in HWDnb20; try assumption. } 
            assert (HWD10nil: well_defined_winstr_with_pd c1 (pd_emp (dom0))). { 
              apply pd_equiv_preserves_WD_win with (pd:= extract_b_pd b pd0); try assumption.
              apply Valid_dist_nil. }

            apply step_deterministic with (pd1:= pd0) in HNSmu01; try assumption; 
            apply step_deterministic with (pd1:= (extract_b_pd b pd1)) in HNSmu1; try assumption;
            apply step_deterministic with (pd1:= (extract_notb_pd b pd1)) in HNSmu11; try assumption; try apply pd_equiv_refl.
            destruct HNSmu01 as [mu02' Htemp0]. destruct Htemp0. 
            destruct HNSmu11 as [mu12' Htemp1]. destruct Htemp1.
            destruct HNSmu1 as [mu11' Htemp2]. destruct Htemp2.
            assert (Hdom02: (dom mu11' == dom mu12')%domain). {
              destruct Hdom1. destruct Hdom2. 
              destruct H8. destruct H1.
              apply dom_equiv_trans with (l1:= (dom mu12)); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd4)); try assumption.
              apply dom_equiv_sym. 
              apply dom_equiv_trans with (l1:= (dom mu11)); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd3)); try assumption.
              apply dom_equiv_sym in H13.
              apply dom_equiv_trans with (l1:= (dom pd')); try assumption. }
            exists mu02', (pd_add mu11' mu12' (Hdom02)). 
              split. { apply NS_IF_All_False; try assumption. 
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - simpl. destruct H6. 
                  + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom0) in H6. assumption.
                  + destruct H6. 
                    apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c2)%domain) .
                    * apply dom_subset_orb_dom_r. assumption.
                    * apply dom_subset_orb_compat; try apply dom_subset_refl.
                    destruct Hdom. destruct H14. assumption.
                - apply step_deterministic with (pd1:= pd_emp (dom pd0)) in HNSmu0; try assumption; try apply Valid_dist_nil.
                  destruct HNSmu0. destruct H11. exists x. split; try assumption.
                  apply NS_pd_implies_nil in H14. destruct H14. apply dom_equiv_sym in H15.
                  split; simpl; try assumption. rewrite H14. apply dst_equiv_refl.  }
              split. { eapply NS_IF_Mixed; try assumption.
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - simpl. destruct H6. 
                  + left. assumption.
                  + right. destruct H6. destruct Hdom. 
                  split; apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
                - apply H10.
                - apply H7.
                - simpl. reflexivity.
                - simpl. apply dom_equiv_refl.
                - simpl. assumption. }
              split; simpl; try assumption. { 
                rewrite H9.
                apply dst_equiv_trans with (mu1:= ((mu mu01 + mu mu11) + (mu mu02 + mu mu12))%dist_state).
                - apply dst_add_preserves_equiv; try assumption.
                - apply bF_getnotb_nil in HB0. 
                  apply NS_mu_implies_nil in HNSmu0; try assumption. rewrite HNSmu0. simpl.
                  apply dst_equiv_trans with (mu1:= (mu mu02 + (mu mu11 + mu mu12))%dist_state).
                  + 
                  rewrite dst_add_assoc_eq. rewrite dst_add_assoc_eq with (mu0:= (mu mu02)%dist_state).
                  apply dst_add_inj_r. apply dst_add_comm.
                  + destruct H. destruct H1. destruct H8. repeat rewrite dst_mult_plus_distr_r_eq. 
                  apply dst_add_preserves_equiv; try apply dst_add_preserves_equiv; try try apply dst_mult_preserves_equiv; try assumption.
                }
              simpl. split; try assumption. 
              * apply dom_equiv_trans with (l1:= dom pd4); try assumption.  
                destruct Hdom2. apply dom_equiv_trans with (l1:= dom mu02); try assumption.
                destruct H. assumption.
              * apply orbdom_after_NS in HNS. simpl in HNS.
                apply dom_equiv_trans with (l1:= (dom pd ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2))%domain); try assumption.
                apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym in H10.
                apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c1)%domain); try assumption.
                apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c1)%domain) .
              ** destruct H6. 
                -- apply dom_eq_orb_compat_left. apply dom_equiv_sym.
                apply orb_domain_elim_r. destruct H6. assumption.
                -- destruct H6. apply dom_equiv_trans with (l1:= 
                    (dom pd ∪ get_modvar_in_winstr c1) ∪ (dom pd ∪ get_modvar_in_winstr c2)); try apply dom_eq_orb_dis_r.
                apply dom_equiv_sym. 
                apply orb_domain_elim_r. apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H11. 
                apply dom_equiv_trans with (l1:= dom pd); try assumption.
                apply dom_equiv_sym. assumption.
              ** destruct Hdom. apply dom_eq_orb_compat_right. assumption. 
        }
        { destruct (b_supp_classify b {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}) eqn: HB1.
          - unfold b_supp_classify in HB1. simpl in HB1. 
            destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s1, p1) :: mu1')));
            destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s1, p1) :: mu1'))); try discriminate.
          - assert (Heqb1: (extract_b_pd b pd1) ≡ pd1). { apply bT_supp_implies_getb_eq; try assumption. }
            assert (Heqnb1: (extract_notb_pd b pd1) ≡ pd_emp (dom pd1)). { 
              apply bT_getnotb_nil in HB1; try assumption.
              split; simpl; try apply dom_equiv_refl.
              simpl in HB1. rewrite HB1. apply dst_equiv_refl. }
            assert (HWDb20: well_defined_winstr_with_pd c2 (extract_notb_pd b pd0)). { 
              apply pd_decom_r_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption. }
            assert (HWDb21: well_defined_winstr_with_pd c2 (extract_notb_pd b pd1)). { 
              apply pd_decom_l_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption. }
            assert (HWDb10: well_defined_winstr_with_pd c1 (extract_b_pd b pd0)). { 
              apply pd_decom_r_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) in H4; try assumption. } 
            assert (HWDb11: well_defined_winstr_with_pd c1 (extract_b_pd b pd1)). { 
               apply pd_decom_l_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) in H4; try assumption. } 
            assert (HWD11: well_defined_winstr_with_pd c1 pd1). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd1) in HWDb11; try assumption. }
            assert (HWD21nil: well_defined_winstr_with_pd c2 (pd_emp (dom pd1))). {
              apply pd_equiv_preserves_WD_win with (pd:= (extract_notb_pd b pd1)); try assumption. 
              apply Valid_dist_nil. }
            apply step_deterministic with (pd1:= pd1) in HNSmu1; try assumption; 
            apply step_deterministic with (pd1:= (extract_b_pd b pd0)) in HNSmu0; try assumption;
            apply step_deterministic with (pd1:= (extract_notb_pd b pd0)) in HNSmu01; try assumption; try apply pd_equiv_refl.
            destruct HNSmu0 as [mu01' Htemp0]. destruct Htemp0. 
            destruct HNSmu1 as [mu11' Htemp2]. destruct Htemp2.
            destruct HNSmu01 as [mu02' Htemp1]. destruct Htemp1.
            assert (Hdom02: (dom mu01' == dom mu02')%domain). { 
              apply orbdom_after_NS in H0. apply orbdom_after_NS in H10. 
              apply dom_equiv_trans with (l1:= (dom (extract_b_pd b pd0) ∪ get_modvar_in_winstr c1)%domain); try assumption.
              apply dom_equiv_sym.
              apply dom_equiv_trans with (l1:= (dom (extract_notb_pd b pd0) ∪ get_modvar_in_winstr c2)%domain); try assumption.
              simpl. destruct H6.
              - apply dom_eq_orb_compat_left. apply dom_equiv_sym. assumption.
              - destruct H6. destruct Hdom. simpl in H14. 
                apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c2); try assumption.
                + apply dom_eq_orb_compat_right. apply dom_equiv_sym. assumption.
                + apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c1); try assumption. 
                  * apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H11.
                    apply dom_equiv_sym in H11. apply dom_equiv_trans with (l1:= dom pd); try assumption.
                  * apply dom_eq_orb_compat_right. assumption. }
            exists (pd_add mu01' mu02' (Hdom02)), mu11'. 
            split. { eapply NS_IF_Mixed; try assumption.
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - simpl. destruct H6. 
                  + left. assumption.
                  + right. destruct H6. destruct Hdom. 
                  split; apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
                - apply H0.
                - apply H10.
                - simpl. reflexivity.
                - simpl. apply dom_equiv_refl.
                - simpl. assumption. }
            split. { apply NS_IF_All_True; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - simpl. destruct H6. 
                + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom1) in H11. assumption.
                + destruct H6. 
                  apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c1)%domain) .
                  * apply dom_subset_orb_dom_r. assumption.
                  * apply dom_subset_orb_compat; try apply dom_subset_refl.
                  destruct Hdom. destruct H15. assumption.
              - apply step_deterministic with (pd1:= pd_emp (dom pd1)) in HNSmu11; try assumption; try apply Valid_dist_nil.
                destruct HNSmu11. destruct H11. exists x. split; try assumption.
                apply NS_pd_implies_nil in H14. destruct H14. apply dom_equiv_sym in H15.
                split; simpl; try assumption. rewrite H14. apply dst_equiv_refl.  }
            split; simpl; try assumption. { 
              rewrite H9.
              apply dst_equiv_trans with (mu1:= ((mu mu01 + mu mu11) + (mu mu02 + mu mu12))%dist_state).
              - apply dst_add_preserves_equiv; try assumption.
              - apply bT_getnotb_nil in HB1. 
                apply NS_mu_implies_nil in HNSmu11; try assumption. rewrite HNSmu11. rewrite dst_add_0_r. 
                repeat rewrite <- dst_add_assoc_eq. 
                apply dst_add_preserves_equiv.
                + destruct H. try apply dst_add_preserves_equiv; try try apply dst_mult_preserves_equiv; try assumption.
                + destruct H1. destruct H8.
                  apply dst_equiv_trans with (mu1:= (mu mu02 + mu mu11)%dist_state); try apply dst_add_comm.
                  apply dst_add_preserves_equiv; try apply dst_add_preserves_equiv; try try apply dst_mult_preserves_equiv; try assumption.
              }
            simpl. split; try assumption. 
            * apply dom_equiv_trans with (l1:= dom pd3); try assumption.  
              destruct Hdom1. apply dom_equiv_trans with (l1:= dom mu01); try assumption.
              destruct H. assumption.
            * apply orbdom_after_NS in HNS. simpl in HNS.
              apply dom_equiv_trans with (l1:= (dom pd ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2))%domain); try assumption.
              apply orbdom_after_NS in H7. simpl in H7. apply dom_equiv_sym in H7.
              apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c1)%domain); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c1)%domain) .
            ** destruct H6. 
              -- apply dom_eq_orb_compat_left. apply dom_equiv_sym.
              apply orb_domain_elim_r. destruct H6. assumption.
              -- destruct H6. apply dom_equiv_trans with (l1:= 
                  (dom pd ∪ get_modvar_in_winstr c1) ∪ (dom pd ∪ get_modvar_in_winstr c2)); try apply dom_eq_orb_dis_r.
              apply dom_equiv_sym. 
              apply orb_domain_elim_r. apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H11. 
              apply dom_equiv_trans with (l1:= dom pd); try assumption.
              apply dom_equiv_sym. assumption.
            ** destruct Hdom. apply dom_eq_orb_compat_right. assumption.
          - assert (Heqnb1: (extract_notb_pd b pd1) ≡ pd1). { apply bF_supp_implies_getnotb_eq; try assumption.  }
            assert (Heqb1: (extract_b_pd b pd1) ≡ pd_emp (dom pd1)). { apply bF_getnotb_nil in HB1. 
              split; simpl; try apply dom_equiv_refl. 
              simpl in HB1. rewrite HB1. apply dst_equiv_refl. }
            assert (HWDnb21: well_defined_winstr_with_pd c2 (extract_notb_pd b pd1)). { 
              apply pd_decom_l_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption. }
            assert (HWDb10: well_defined_winstr_with_pd c1 (extract_b_pd b pd0)). { 
              apply pd_decom_r_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) in H4; try assumption. } 
            assert (HWDb11: well_defined_winstr_with_pd c1 (extract_b_pd b pd1)). { 
               apply pd_decom_l_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) in H4; try assumption. } 
            assert (HWD11nil: well_defined_winstr_with_pd c1 (pd_emp (dom pd1))). {
              apply pd_equiv_preserves_WD_win with (pd:= (extract_b_pd b pd1)); try assumption. apply Valid_dist_nil. }
            assert (HWDnb20: well_defined_winstr_with_pd c2 (extract_notb_pd b pd0)). {
              apply pd_decom_r_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption. }
            assert (HWD11: well_defined_winstr_with_pd c2 pd1). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd1) in HWDnb21; try assumption. } 
            apply step_deterministic with (pd1:= pd1) in HNSmu11; try assumption; 
            apply step_deterministic with (pd1:= (extract_b_pd b pd0)) in HNSmu0; try assumption;
            apply step_deterministic with (pd1:= (extract_notb_pd b pd0)) in HNSmu01; try assumption; try apply pd_equiv_refl.
            destruct HNSmu01 as [mu02' Htemp0]. destruct Htemp0. 
            destruct HNSmu11 as [mu12' Htemp1]. destruct Htemp1.
            destruct HNSmu0 as [mu01' Htemp2]. destruct Htemp2.
            assert (Hdom02: (dom mu01' == dom mu02')%domain). {
              destruct Hdom1. destruct Hdom2. 
              destruct H8. destruct H.
              apply dom_equiv_trans with (l1:= (dom mu02)); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd4)); try assumption.
              apply dom_equiv_sym. 
              apply dom_equiv_trans with (l1:= (dom mu01)); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd3)); try assumption.
              apply dom_equiv_sym in H13.
              apply dom_equiv_trans with (l1:= (dom pd')); try assumption. }
            exists (pd_add mu01' mu02' (Hdom02)), mu12'. 
            split. { eapply NS_IF_Mixed; try assumption.
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - simpl. destruct H6. 
                + left. assumption.
                + right. destruct H6. destruct Hdom. 
                split; apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply H10.
              - apply H0.
              - simpl. reflexivity.
              - simpl. apply dom_equiv_refl.
              - simpl. assumption. }
            split. { apply NS_IF_All_False; try assumption. 
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - simpl. destruct H6. 
                  + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom1) in H6. assumption.
                  + destruct H6. 
                    apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c2)%domain) .
                    * apply dom_subset_orb_dom_r. assumption.
                    * apply dom_subset_orb_compat; try apply dom_subset_refl.
                    destruct Hdom. destruct H15. assumption.
                - apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}))) in HNSmu1; try assumption.
                  + destruct HNSmu1. destruct H11. exists x. split; try assumption. 
                    simpl. split; simpl; try assumption. 
                    * apply orbdom_after_NS in H14. simpl in H14. apply dom_equiv_sym. assumption.
                    * apply NS_pd_implies_nil in H14. destruct H14. rewrite H14. apply dst_equiv_refl.
                  + apply Valid_dist_nil. }
            split; simpl; try assumption. { 
                rewrite H9.
                apply dst_equiv_trans with (mu1:= ((mu mu01 + mu mu11) + (mu mu02 + mu mu12))%dist_state).
                - apply dst_add_preserves_equiv; try assumption.
                - apply bF_getnotb_nil in HB1. 
                  apply NS_mu_implies_nil in HNSmu1; try assumption. rewrite HNSmu1. rewrite dst_add_0_r.
                  destruct H. destruct H1. destruct H8. rewrite dst_add_assoc_eq.
                  apply dst_add_preserves_equiv; try apply dst_add_preserves_equiv; try try apply dst_mult_preserves_equiv; try assumption.
                }
            simpl. split; try assumption. 
              * apply dom_equiv_trans with (l1:= dom pd3); try assumption.  
                destruct Hdom1. apply dom_equiv_trans with (l1:= dom mu01); try assumption.
                destruct H8. assumption.
              * apply orbdom_after_NS in HNS. simpl in HNS.
                apply dom_equiv_trans with (l1:= (dom pd ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2))%domain); try assumption.
                apply orbdom_after_NS in H7. simpl in H7. apply dom_equiv_sym in H7.
                apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c2)%domain); try assumption.
                apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c2)%domain) .
              ** destruct H6. 
                -- apply dom_eq_orb_compat_left. rewrite orb_domain_comm. apply dom_equiv_sym.
                apply orb_domain_elim_r. destruct H6. assumption.
                -- destruct H6. apply dom_equiv_trans with (l1:= 
                    (dom pd ∪ get_modvar_in_winstr c1) ∪ (dom pd ∪ get_modvar_in_winstr c2)); try apply dom_eq_orb_dis_r.
                apply dom_equiv_sym.  rewrite orb_domain_comm with (l:= (dom pd ∪ get_modvar_in_winstr c1)).
                apply orb_domain_elim_r. apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H11. 
                apply dom_equiv_trans with (l1:= dom pd); try assumption.
                apply dom_equiv_sym. assumption.
              ** destruct Hdom. apply dom_eq_orb_compat_right. assumption.
          - assert (HWDnb21: well_defined_winstr_with_pd c2 (extract_notb_pd b pd1)). { 
              apply pd_decom_l_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption. }
            assert (HWDb10: well_defined_winstr_with_pd c1 (extract_b_pd b pd0)). { 
              apply pd_decom_r_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) in H4; try assumption. } 
            assert (HWDb11: well_defined_winstr_with_pd c1 (extract_b_pd b pd1)). { 
               apply pd_decom_l_preserves_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) in H4; try assumption. } 
            assert (HWDnb20: well_defined_winstr_with_pd c2 (extract_notb_pd b pd0)). {
              apply pd_decom_r_preserves_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) in H5; try assumption. }
            apply step_deterministic with (pd1:= (extract_b_pd b pd1)) in HNSmu1; try assumption; 
            apply step_deterministic with (pd1:= (extract_notb_pd b pd1)) in HNSmu11; try assumption; 
            apply step_deterministic with (pd1:= (extract_b_pd b pd0)) in HNSmu0; try assumption;
            apply step_deterministic with (pd1:= (extract_notb_pd b pd0)) in HNSmu01; try assumption; try apply pd_equiv_refl.
            destruct HNSmu01 as [mu02' Htemp0]. destruct Htemp0. 
            destruct HNSmu11 as [mu12' Htemp1]. destruct Htemp1.
            destruct HNSmu0 as [mu01' Htemp2]. destruct Htemp2.
            destruct HNSmu1 as [mu11' Htemp2]. destruct Htemp2.
            assert (Hdom02: (dom mu01' == dom mu02')%domain). {
              destruct Hdom1. destruct Hdom2. 
              destruct H8. destruct H.
              apply dom_equiv_trans with (l1:= (dom mu02)); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd4)); try assumption.
              apply dom_equiv_sym. 
              apply dom_equiv_trans with (l1:= (dom mu01)); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd3)); try assumption.
              apply dom_equiv_sym in H13.
              apply dom_equiv_trans with (l1:= (dom pd')); try assumption. }
            assert (Hdom12: (dom mu11' == dom mu12')%domain). {
              destruct Hdom1. destruct Hdom2. 
              destruct H8. destruct H1.
              apply dom_equiv_trans with (l1:= (dom mu12)); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd4)); try assumption.
              apply dom_equiv_sym. destruct H11.
              apply dom_equiv_trans with (l1:= (dom mu11)); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd3)); try assumption.
              apply dom_equiv_sym in H13.
              apply dom_equiv_trans with (l1:= (dom pd')); try assumption. }
            exists (pd_add mu01' mu02' (Hdom02)), (pd_add mu11' mu12' (Hdom12)). 
            split. { eapply NS_IF_Mixed; try assumption.
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - simpl. destruct H6. 
                + left. assumption.
                + right. destruct H6. destruct Hdom. 
                split; apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply H10.
              - apply H0.
              - simpl. reflexivity.
              - simpl. apply dom_equiv_refl.
              - simpl. assumption. }
            split. { eapply NS_IF_Mixed; try assumption.
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - simpl. destruct H6. 
                  + left. assumption.
                  + right. destruct H6. destruct Hdom. 
                  split; apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
                - apply H14.
                - apply H7.
                - simpl. reflexivity.
                - simpl. apply dom_equiv_refl.
                - simpl. assumption. }
            split; simpl; try assumption. { 
                rewrite H9.
                apply dst_equiv_trans with (mu1:= ((mu mu01 + mu mu11) + (mu mu02 + mu mu12))%dist_state).
                - apply dst_add_preserves_equiv; try assumption.
                - rewrite dst_add_assoc_eq. 
                  rewrite dst_add_assoc_eq.   
                  destruct H. destruct H1. destruct H8. destruct H11.
                  apply dst_add_preserves_equiv; try assumption. 
                  rewrite <- dst_add_assoc_eq. rewrite <- dst_add_assoc_eq. 
                  try apply dst_add_preserves_equiv; try try apply dst_mult_preserves_equiv; try assumption.
                  apply dst_equiv_trans with (mu1:= (mu mu02 + mu mu11)%dist_state); try apply dst_add_comm.
                  try apply dst_add_preserves_equiv; try try apply dst_mult_preserves_equiv; try assumption.
                }
            simpl. split; try assumption. 
              * apply dom_equiv_trans with (l1:= dom pd3); try assumption.  
                destruct Hdom1. apply dom_equiv_trans with (l1:= dom mu01); try assumption.
                destruct H8. assumption.
              * apply orbdom_after_NS in HNS. simpl in HNS.
                apply dom_equiv_trans with (l1:= (dom pd ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2))%domain); try assumption.
                apply orbdom_after_NS in H14. simpl in H14. apply dom_equiv_sym in H14.
                apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c1)%domain); try assumption.
                apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c1)%domain) .
              ** destruct H6. 
                -- apply dom_eq_orb_compat_left. apply dom_equiv_sym.
                apply orb_domain_elim_r. destruct H6. assumption.
                -- destruct H6. apply dom_equiv_trans with (l1:= 
                    (dom pd ∪ get_modvar_in_winstr c1) ∪ (dom pd ∪ get_modvar_in_winstr c2)); try apply dom_eq_orb_dis_r.
                apply dom_equiv_sym. 
                apply orb_domain_elim_r. apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H15. 
                apply dom_equiv_trans with (l1:= dom pd); try assumption.
                apply dom_equiv_sym. assumption.
              ** destruct Hdom. apply dom_eq_orb_compat_right. assumption.
        }
    }
  - assert (Hdom': (dom pd' == (orb_domain (dom pd) (get_modvar_in_winstr (While b c))))%domain) by 
      (apply orbdom_after_NS; try assumption).
    remember (While b c) as original_command eqn:Horig.
    generalize dependent pd1. generalize dependent pd0. 
    induction HNS; try inversion Horig; subst; intros.
    { 
      destruct pd0 as [dom0 mu0 HPD0]. destruct pd1 as [dom2 mu2 HPD2].
      destruct mu0 as [|(s0,p0) mu0']; destruct mu2 as [|(s2,p2) mu2'].
      - simpl in *.
        assert (Hmu_nil: mu pd = []). { apply dst_eq_nil_iff; split; try assumption. }
        exists (pd_emp (orb_domain (dom0) (get_modvar_in_winstr (While b c)))), 
                (pd_emp (orb_domain (dom2) (get_modvar_in_winstr c))).
        split. { apply (@NS_While_Nil b c {| dom := dom0; mu := []; all_partial := HPD0 |}). 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - unfold b_supp_classify. simpl. reflexivity.  }
        split. { apply (@NS_While_Nil b c {| dom := dom2; mu := []; all_partial := HPD2 |}).
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption. 
          - unfold b_supp_classify. simpl. reflexivity.  }
        simpl. split; try apply dst_equiv_refl.
        destruct Hdom. 
        apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr c) in H1. 
        apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr c) in H2. 
        split; try apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c)%domain); try assumption.
      - apply pd_Nil_mu in H0. 
        rewrite H0 in Hadd. rewrite dst_add_0_l in Hadd. simpl in Hadd.  
        + apply dst_equiv_sym in Hadd. 
          apply dst_cons_valid_contra in Hadd; try assumption; try contradiction.
      - apply pd_Nil_mu in H0. 
        rewrite H0 in Hadd. rewrite dst_add_0_r in Hadd. simpl in Hadd.  
        + apply dst_equiv_sym in Hadd. 
          apply dst_cons_valid_contra in Hadd; try assumption; try contradiction.
      - apply pd_Nil_mu in H0. 
        rewrite H0 in Hadd. simpl in Hadd.  
        + apply dst_equiv_sym in Hadd. 
          apply dst_cons_valid_contra in Hadd; try assumption; try contradiction.
    }
    {
      destruct pd0 as [dom0 mu0 HPD0]. destruct pd2 as [dom2 mu2 HPD2].
      destruct mu0 as [|(s0,p0) mu0']; destruct mu2 as [|(s2,p2) mu2'].
      - simpl in *. 
        assert (Hmu_nil: mu pd = []). { apply dst_eq_nil_iff; split; try assumption. }
        apply NS_mu_implies_nil in HNS1; try assumption.
        apply NS_mu_implies_nil in HNS2; try assumption.
        exists (pd_emp (orb_domain (dom0) (get_modvar_in_winstr (While b c)))), 
                (pd_emp (orb_domain (dom2) (get_modvar_in_winstr c))).
        split. { apply (@NS_While_Nil b c {| dom := dom0; mu := []; all_partial := HPD0 |}). 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - unfold b_supp_classify. simpl. reflexivity.  }
        split. { apply (@NS_While_Nil b c {| dom := dom2; mu := []; all_partial := HPD2 |}).
            - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
            - unfold b_supp_classify. simpl. reflexivity.  }
        simpl. rewrite HNS2. split; try apply dst_equiv_refl.
        destruct Hdom. 
        apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr c) in H3. 
        apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr c) in H4. 
        split; try apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c)%domain); try assumption.
      - pose (pd2_ori:= {| dom := dom2; mu := (s2, p2) :: mu2'; all_partial := HPD2 |}).
        assert (Heq': pd ≡ pd2_ori). {
          destruct Hdom. rewrite dst_add_0_l in Hadd. split; simpl; try assumption. }
        assert (Hb: b_supp_classify b pd2_ori = All_True). {
          rewrite dst_add_0_l in Hadd. 
          apply dst_equiv_implies_b_classify with (b:= b) in Heq'; try assumption. 
          rewrite H0 in Heq'. symmetry in Heq'. assumption. } 
        apply IHc with (pd':= pd1) in Hadd; try assumption. 
        destruct Hadd as [x Hx]. destruct Hx as [x0 Hx0]. 
        destruct Hx0 as [HNSx Hx0]. destruct Hx0 as [HNSx0 Hmu].
        destruct Hmu as [Hmu Hdomx].
        assert (Hvx: Valid_dist (mu x)). { apply Valid_forall_NS in HNSx; try assumption. }
        assert (Hvx0: Valid_dist (mu x0)). { apply Valid_forall_NS in HNSx0; try assumption. } 
        assert (HVl: Valid_dist (mu x + mu x0)%dist_state). {
          rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq.
          apply Valid_linear_under_eq_prob; try assumption; try lra. 
          rewrite <- Rmult_plus_distr_l. rewrite Rmult_1_l.
          apply NS_preserve_sum_eq in HNSx; try assumption.
          apply NS_preserve_sum_eq in HNSx0; try assumption.
          rewrite <- HNSx. rewrite <- HNSx0. simpl. rewrite Rplus_0_l.
          destruct Hvl. simpl in H3. assumption. }
        assert (Hv1: Valid_dist (mu pd1)). { apply Valid_forall_NS in HNS1; try assumption. }
        assert (Hdom1': (dom pd' == dom pd1 ∪ get_modvar_in_winstr (WHILE b DO c END))%domain). {
          apply orbdom_after_NS; try assumption. }
        assert (HWDx0c: well_defined_winstr_with_pd (WHILE b DO c END) x0). { 
          
          apply pd_decom_l_preserves_WD_win with (c:= While b c) in Hmu; try assumption. }
        apply IHHNS2 in Hmu; try assumption.
        destruct Hmu as [x' Hx]. destruct Hx as [x0' Hx0]. 
        destruct Hx0 as [HNSx' Hx0]. destruct Hx0 as [HNSx0' Hmu].
        destruct Hmu as [Heq Hdomx'].
        exists (pd_emp (orb_domain (dom0) (get_modvar_in_winstr (While b c)))), x0'.
        split. { apply (@NS_While_Nil b c {| dom := dom0; mu := []; all_partial := HPD0 |}). 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - unfold b_supp_classify. simpl. reflexivity. }
        split. { eapply NS_While_All_True; try assumption.
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply pd_equiv_preserves_WD_win with (pd:= pd); try assumption.
          - apply HWDx0c.
          - apply HNSx0.
          - assumption. }
        simpl. apply NS_pd_implies_nil in HNSx. destruct HNSx. split.
        + apply NS_mu_implies_nil in HNSx'; try assumption. rewrite HNSx' in Heq. simpl in Heq. assumption.
        + destruct Hdomx'. split; try assumption. 
          apply dom_equiv_trans with (l1:= dom x'); try assumption.
          apply orbdom_after_NS in HNSx'. simpl in HNSx'.
          apply dom_equiv_trans with (l1:= (dom x ∪ get_modvar_in_winstr c)%domain); try assumption.
          apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr c) in H4. 
          apply dom_equiv_trans with (l1:= ((dom0 ∪ get_modvar_in_winstr c) ∪ get_modvar_in_winstr c)%domain); try assumption.
          apply dom_equiv_sym. apply orb_domain_elim_r. apply dom_subset_orb_snd_l_r. 
      - pose (pd0_ori:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
        assert (Heq': pd ≡ pd0_ori). {
          destruct Hdom. rewrite dst_add_0_r in Hadd. split; simpl; try assumption. }
        assert (Hb: b_supp_classify b pd0_ori = All_True). {
          rewrite dst_add_0_r in Hadd. 
          apply dst_equiv_implies_b_classify with (b:= b) in Heq'; try assumption. 
          rewrite H0 in Heq'. symmetry in Heq'. assumption. } 
        apply IHc with (pd':= pd1) in Hadd; try assumption. 
        destruct Hadd as [x Hx]. destruct Hx as [x0 Hx0]. 
        destruct Hx0 as [HNSx Hx0]. destruct Hx0 as [HNSx0 Hmu].
        destruct Hmu as [Hmu Hdomx].
        assert (Hvx: Valid_dist (mu x)). { apply Valid_forall_NS in HNSx; try assumption. }
        assert (Hvx0: Valid_dist (mu x0)). { apply Valid_forall_NS in HNSx0; try assumption. } 
        assert (HVl: Valid_dist (mu x + mu x0)%dist_state). {
          rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq.
          apply Valid_linear_under_eq_prob; try assumption; try lra. 
          rewrite <- Rmult_plus_distr_l. rewrite Rmult_1_l.
          apply NS_preserve_sum_eq in HNSx; try assumption.
          apply NS_preserve_sum_eq in HNSx0; try assumption.
          rewrite <- HNSx. rewrite <- HNSx0. simpl. rewrite Rplus_0_r.
          destruct Hvl. simpl in H3. rewrite dst_add_0_r in H3.
          assumption. }
        assert (Hv1: Valid_dist (mu pd1)). { apply Valid_forall_NS in HNS1; try assumption. }
        assert (Hdom1': (dom pd' == dom pd1 ∪ get_modvar_in_winstr (WHILE b DO c END))%domain). {
          apply orbdom_after_NS; try assumption. }
        assert (HWDxc: well_defined_winstr_with_pd (WHILE b DO c END) x). { 
          apply pd_decom_r_preserves_WD_win with (c:= While b c) in Hmu; try assumption. }
        apply IHHNS2 in Hmu; try assumption.
        destruct Hmu as [x' Hx]. destruct Hx as [x0' Hx0]. 
        destruct Hx0 as [HNSx' Hx0]. destruct Hx0 as [HNSx0' Hmu].
        destruct Hmu as [Heq Hdomx'].
        exists x', (pd_emp (orb_domain (dom2) (get_modvar_in_winstr (While b c)))).
        split. { eapply NS_While_All_True; try assumption.
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply pd_equiv_preserves_WD_win with (pd:= pd); try assumption.
          - apply HWDxc.
          - apply HNSx.
          - assumption. }
        split. { apply (@NS_While_Nil b c {| dom := dom2; mu := []; all_partial := HPD2 |}). 
            - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
            - unfold b_supp_classify. simpl. reflexivity. }
        simpl. apply NS_pd_implies_nil in HNSx0. destruct HNSx0. split.
        + apply NS_mu_implies_nil in HNSx0'; try assumption. rewrite HNSx0' in Heq. simpl in Heq. assumption.
        + destruct Hdomx'. split; try assumption. 
          apply dom_equiv_trans with (l1:= dom x0'); try assumption.
          apply orbdom_after_NS in HNSx0'. simpl in HNSx0'.
          apply dom_equiv_trans with (l1:= (dom x0 ∪ get_modvar_in_winstr c)%domain); try assumption.
          apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr c) in H4. 
          apply dom_equiv_trans with (l1:= ((dom2 ∪ get_modvar_in_winstr c) ∪ get_modvar_in_winstr c)%domain); try assumption.
          apply dom_equiv_sym. apply orb_domain_elim_r. apply dom_subset_orb_snd_l_r. 
      - pose (pd0_ori:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
        pose (pd2_ori:= {| dom := dom2; mu := (s2, p2) :: mu2'; all_partial := HPD2 |}).
        assert (HWD0c: well_defined_winstr_with_pd c pd0_ori). { 
          apply pd_decom_r_preserves_WD_win with (c:= c) in Hadd; try assumption. }
        assert (HWD2c: well_defined_winstr_with_pd c pd2_ori). { 
          apply pd_decom_l_preserves_WD_win with (c:= c) in Hadd; try assumption. }
        assert (Hb0: b_supp_classify b pd0_ori = All_True). { 
          apply bT_classify_decom_r with (b:= b) (pd0:= pd0_ori) (pd1:= pd2_ori) in H0; simpl; try assumption.
          - unfold not. intros. discriminate.
          - destruct Hdom. simpl in H3. assumption. 
          - destruct Hdom. simpl in H3. assumption. }
        assert (Hb2: b_supp_classify b pd2_ori = All_True). { 
          destruct Hdom.  
          apply bT_classify_decom_r with (b:= b) (pd0:= pd2_ori) (pd1:= pd0_ori) in H0; try assumption.
          - apply Valid_add_comm. assumption.
          - apply dst_equiv_trans with (mu1:= ( mu {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |} +
              mu {| dom := dom2; mu := (s2, p2) :: mu2'; all_partial := HPD2 |})%dist_state); try assumption.
            apply dst_add_comm.
          - simpl. 
            + unfold not. intros. discriminate. 
         }
        apply IHc with (pd':= pd1) in Hadd; try assumption. 
        destruct Hadd as [x Hx]. destruct Hx as [x0 Hx0]. 
        destruct Hx0 as [HNSx Hx0]. destruct Hx0 as [HNSx0 Hmu].
        destruct Hmu as [Hmu Hdomx].
        assert (Hvx: Valid_dist (mu x)). { apply Valid_forall_NS in HNSx; try assumption. }
        assert (Hvx0: Valid_dist (mu x0)). { apply Valid_forall_NS in HNSx0; try assumption. } 
        assert (HVl: Valid_dist (mu x + mu x0)%dist_state). {
          rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq.
          apply Valid_linear_under_eq_prob; try assumption; try lra. 
          rewrite <- Rmult_plus_distr_l. rewrite Rmult_1_l.
          apply NS_preserve_sum_eq in HNSx; try assumption.
          apply NS_preserve_sum_eq in HNSx0; try assumption.
          rewrite <- HNSx. rewrite <- HNSx0. simpl. 
          destruct Hvl. simpl in H3. 
          rewrite dst_sum_prob_decom in H3. simpl in H3. rewrite Rplus_assoc. assumption. } 
        assert (Hv1: Valid_dist (mu pd1)). { apply Valid_forall_NS in HNS1; try assumption. }
        assert (Hdom1': (dom pd' == dom pd1 ∪ get_modvar_in_winstr (WHILE b DO c END))%domain). {
          apply orbdom_after_NS; try assumption. }
        assert (HWDxc: well_defined_winstr_with_pd (WHILE b DO c END) x). { 
          apply pd_decom_r_preserves_WD_win with (c:= While b c) in Hmu; try assumption. }
        assert (HWDx0c: well_defined_winstr_with_pd (WHILE b DO c END) x0). { 
          apply pd_decom_l_preserves_WD_win with (c:= While b c) in Hmu; try assumption. }
        apply IHHNS2 in Hmu; try assumption.
        destruct Hmu as [x' Hx]. destruct Hx as [x0' Hx0]. 
        destruct Hx0 as [HNSx' Hx0]. destruct Hx0 as [HNSx0' Hmu].
        destruct Hmu as [Heq Hdomx'].
        exists x', x0'.
        split. { eapply NS_While_All_True; try assumption.
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply HWDxc.
          - apply HNSx.
          - assumption. }
        split. { eapply NS_While_All_True; try assumption.
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply HWDx0c.
          - apply HNSx0.
          - assumption. }
        simpl. split; try assumption.
    }
    {
      destruct pd0 as [dom0 mu0 HPD0]. destruct pd1 as [dom2 mu2 HPD2].
      destruct mu0 as [|(s0,p0) mu0']; destruct mu2 as [|(s2,p2) mu2'].
      - simpl in *. 
        assert (Hmu_nil: mu pd = []). { apply dst_eq_nil_iff; split; try assumption. }
        unfold b_supp_classify in H0. rewrite Hmu_nil in H0. simpl. discriminate. 
      - pose (pd2_ori:= {| dom := dom2; mu := (s2, p2) :: mu2'; all_partial := HPD2 |}).
        destruct Hdom. 
        assert (Heq': pd ≡ pd2_ori  ). {
          rewrite dst_add_0_l in Hadd. split; simpl; try assumption. }
        assert (Hb: b_supp_classify b pd2_ori = All_False). {
          rewrite dst_add_0_l in Hadd. 
          apply dst_equiv_implies_b_classify with (b:= b) in Heq'; try assumption. 
          rewrite H0 in Heq'. symmetry in Heq'. assumption. }
        exists (pd_emp (orb_domain (dom0) (get_modvar_in_winstr (While b c)))), pd2_ori.
        split. { apply (@NS_While_Nil b c {| dom := dom0; mu := []; all_partial := HPD0 |}). 
          - apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - unfold b_supp_classify. simpl. reflexivity. }
        split. { eapply NS_While_All_False; try assumption.
          - apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
        rewrite dst_add_0_l. split; try assumption. simpl. 
        split; try assumption. 
        apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr (WHILE b DO c END))%domain); try assumption.
            apply dom_eq_orb_compat_right. assumption.
      - pose (pd0_ori:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
        destruct Hdom. 
        assert (Heq': pd ≡ pd0_ori). {
          rewrite dst_add_0_r in Hadd. split; simpl; try assumption. }
        assert (Hb: b_supp_classify b pd0_ori = All_False). {
          rewrite dst_add_0_r in Hadd. 
          apply dst_equiv_implies_b_classify with (b:= b) in Heq'; try assumption. 
          rewrite H0 in Heq'. symmetry in Heq'. assumption. } 
        exists pd0_ori, (pd_emp (orb_domain (dom2) (get_modvar_in_winstr (While b c)))).
        split. { eapply NS_While_All_False; try assumption.
          - apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
        split. { apply (@NS_While_Nil b c {| dom := dom2; mu := []; all_partial := HPD2 |}).
            - apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
            - unfold b_supp_classify. simpl. reflexivity. }
        rewrite dst_add_0_r. rewrite dst_add_0_r in Hadd. split; try assumption. simpl. 
        split; try assumption. 
        apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr (WHILE b DO c END))%domain); try assumption.
            apply dom_eq_orb_compat_right. assumption.
      - pose (pd0_ori:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
        pose (pd2_ori:= {| dom := dom2; mu := (s2, p2) :: mu2'; all_partial := HPD2 |}).
        assert (Hb0: b_supp_classify b pd0_ori = All_False). { 
          destruct Hdom.  
          apply bF_classify_decom_r with (b:= b) (pd0:= ( pd0_ori )) (pd1:= ( pd2_ori  )) in H0; try assumption.
          simpl. unfold not. intros. discriminate. }
        assert (Hb: b_supp_classify b pd2_ori = All_False). {
          destruct Hdom.  
          apply bF_classify_decom_r with (b:= b) (pd0:= pd2_ori ) (pd1:= pd0_ori ) in H0; try assumption.
          - apply Valid_add_comm. assumption.
          - apply dst_equiv_trans with (mu1:= (  mu {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |} +
                mu {| dom := dom2; mu := (s2, p2) :: mu2'; all_partial := HPD2 |})%dist_state); try assumption.
            apply dst_add_comm.
          - simpl. 
            + unfold not. intros. discriminate.  }
        destruct Hdom.
        exists pd0_ori, pd2_ori.
        split. { eapply NS_While_All_False; try assumption.
          - apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. } 
        split. { eapply NS_While_All_False; try assumption.
          - apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. } 
        simpl. split; try assumption. split; try assumption.
    }
    {
      destruct pd2 as [dom0 mu0 HPD0]. destruct pd3 as [dom2 mu2 HPD2].
      destruct mu0 as [|(s0,p0) mu0']; destruct mu2 as [|(s2,p2) mu2'].
      - simpl in *. 
        assert (Hmu_nil: mu pd = []). { apply dst_eq_nil_iff; split; try assumption. }
        unfold b_supp_classify in H0. rewrite Hmu_nil in H0. simpl. discriminate. 
      - pose (pd2_ori:= {| dom := dom2; mu := (s2, p2) :: mu2'; all_partial := HPD2 |}).
        assert (Heq': pd ≡ pd2_ori  ). {
          destruct Hdom. rewrite dst_add_0_l in Hadd. split; simpl; try assumption. }
        assert (Hb_pdeq: pd_b ≡ extract_b_pd b ( pd2_ori  )). {
          apply pd_eq_preserves_get_b with (b:= b); try assumption. } 
        assert (Hnb_pdeq: pd_notb ≡ extract_notb_pd b ( pd2_ori  )). {
          apply pd_eq_preserves_get_notb with (b:= b); try assumption. } 
        assert (Hb: b_supp_classify b pd2_ori = Mixed). {
          rewrite dst_add_0_l in Hadd. 
          apply dst_equiv_implies_b_classify with (b:= b) in Heq'; try assumption. 
          rewrite H0 in Heq'. symmetry in Heq'. assumption. }
        assert (HVb1: Valid_dist (mu (extract_b_pd b pd2_ori))). { apply dst_Valid_get_b; assumption. }
        assert (HVbp1: Valid_dist (mu {| dom := dom0; mu := []; all_partial := HPD0 |} + 
            mu (extract_b_pd b pd2_ori))%dist_state). {
              rewrite dst_add_0_l. assumption. }
        assert (HVnb1: Valid_dist (mu (extract_notb_pd b pd2_ori))). { apply dst_Valid_get_notb; assumption. }
        assert (HVb: Valid_dist (mu pd_b)). { apply dst_Valid_get_b; assumption. }
        assert (HVnb: Valid_dist (mu pd_notb)).  { apply dst_Valid_get_notb; assumption. }
        assert (Hb_eq: mu pd_b == (  mu {| dom := dom0; mu := []; all_partial := HPD0 |} +
                                   mu (extract_b_pd b pd2_ori))%dist_state). {  
                        rewrite dst_add_0_l. rewrite dst_add_0_l in Hadd.
                        apply Peq_implies_get_b_Peq with (b:= b) in Hadd; try assumption. }
        assert (Hnotb_eq:  mu pd_notb == (  mu {| dom := dom0; mu := []; all_partial := HPD0 |} +
                                  mu (extract_notb_pd b pd2_ori))%dist_state). {
                        rewrite dst_add_0_l. rewrite dst_add_0_l in Hadd.
                        apply Peq_implies_get_notb_Peq with (b:= b) in Hadd; try assumption. }
        assert (HWDb2: well_defined_winstr_with_pd c (extract_b_pd b pd2_ori)). { 
          apply pd_decom_l_preserves_WD_win with (c:= c) in Hb_eq; try assumption. }
        apply IHc with (pd':= pd0) in Hb_eq; try assumption. 
        destruct Hb_eq as [x Hx]. destruct Hx as [x0 Hx0]. 
        destruct Hx0 as [HNSx Hx0]. destruct Hx0 as [HNSx0 Hmu].
        destruct Hmu as [Hmu Hdomx].
        assert (Hvx: Valid_dist (mu x)). { apply Valid_forall_NS in HNSx; try assumption. }
        assert (Hvx0: Valid_dist (mu x0)). { apply Valid_forall_NS in HNSx0; try assumption. } 
        assert (HVl: Valid_dist (mu x +  mu x0)%dist_state). { 
          rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq.
          apply Valid_linear_under_eq_prob; try assumption; try lra. 
          rewrite <- Rmult_plus_distr_l. rewrite Rmult_1_l.
          apply NS_preserve_sum_eq in HNSx; try assumption.
          apply NS_preserve_sum_eq in HNSx0; try assumption.
          rewrite <- HNSx. rewrite <- HNSx0. rewrite Rplus_0_l.
          destruct HVb1. assumption. }
        assert (Hv1: Valid_dist (mu pd0)). { apply Valid_forall_NS in HNS1; try assumption. }
        assert (HWDx: well_defined_winstr_with_pd (WHILE b DO c END) x0). { 
          apply pd_decom_l_preserves_WD_win with (c:= (While b c)) in Hmu; try assumption. }
        assert (Hdom1': (dom pd1 == dom pd0 ∪ get_modvar_in_winstr (WHILE b DO c END))%domain). { 
          apply orbdom_after_NS; try assumption. }
        apply IHHNS2 in Hmu; try assumption.
        destruct Hmu as [x' Hx]. destruct Hx as [x0' Hx0]. 
        destruct Hx0 as [HNSx' Hx0]. destruct Hx0 as [HNSx0' Hmu].
        destruct Hmu as [Heq Hdomx'].
        assert (Hdomx2: (dom x0' == dom pd2_ori)%domain). { 
          apply orbdom_after_NS in HNSx0; try assumption.
          apply orbdom_after_NS in HNSx0'; try assumption.
          apply dom_equiv_trans with (l1:= (dom x0 ∪ get_modvar_in_winstr (WHILE b DO c END))%domain); try assumption.
          apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr (WHILE b DO c END)) in HNSx0; try assumption.
          simpl in HNSx0. simpl.
          apply dom_equiv_trans with (l1:= ((dom2 ∪ get_modvar_in_winstr c) ∪ get_modvar_in_winstr c)%domain); try assumption.
          rewrite <- orb_domain_assoc. rewrite orb_domain_refl.
          apply dom_equiv_sym. apply orb_domain_elim_r.
          destruct Hdom. 
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
        exists (pd_emp (orb_domain (dom0) (get_modvar_in_winstr (While b c)))), 
                (pd_add x0' (extract_notb_pd b pd2_ori) (Hdomx2)).
        split. { apply (@NS_While_Nil b c {| dom := dom0; mu := []; all_partial := HPD0 |}). 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - unfold b_supp_classify. simpl. reflexivity. }
        split. { eapply NS_While_Mixed; try assumption.
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply HWDx.
          - simpl. destruct Hdom. 
            apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
          - apply HNSx0.
          - apply HNSx0'.
          - simpl. reflexivity.
          - simpl. apply dom_equiv_refl. }
        split. { rewrite dst_add_0_l. rewrite H4. unfold pd_add.
          simpl.
          apply dst_add_preserves_equiv; try assumption.
          apply NS_pd_implies_nil in HNSx. destruct HNSx. 
          apply NS_mu_implies_nil in HNSx'; try assumption. 
          rewrite HNSx' in Heq. simpl in Heq. assumption. } 
        simpl. split; try assumption.
          + simpl in Hdom'. 
            apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c)%domain); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          + destruct Hdomx'. 
            apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
      - pose (pd0_ori:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
        assert (Hv0p: Valid_dist (mu ( pd0_ori ))). { try apply Valid_mult_cofe; try assumption. }
        assert (Heq': pd ≡  pd0_ori ). {
          destruct Hdom. rewrite dst_add_0_r in Hadd. split; simpl; try assumption. }
        assert (Hb_pdeq: pd_b ≡ extract_b_pd b ( pd0_ori )). {
          apply pd_eq_preserves_get_b with (b:= b); try assumption. } 
        assert (Hnb_pdeq: pd_notb ≡ extract_notb_pd b ( pd0_ori )). {
          apply pd_eq_preserves_get_notb with (b:= b); try assumption. } 
        assert (Hb: b_supp_classify b pd0_ori = Mixed). {
          rewrite dst_add_0_r in Hadd. 
          apply dst_equiv_implies_b_classify with (b:= b) in Heq'; try assumption. 
          rewrite H0 in Heq'. symmetry in Heq'. assumption. }
        assert (HVb1: Valid_dist (mu (extract_b_pd b pd0_ori))). { apply dst_Valid_get_b; assumption. }
        assert (HVbp1:Valid_dist (  mu (extract_b_pd b pd0_ori) + 
                                  mu {| dom := dom2; mu := []; all_partial := HPD2 |})%dist_state). {
          rewrite dst_add_0_r. try apply Valid_mult_cofe; try assumption.  }
        assert (HVnb1: Valid_dist (mu (extract_notb_pd b pd0_ori))). { apply dst_Valid_get_notb; assumption. }
        assert (HVb: Valid_dist (mu pd_b)). { apply dst_Valid_get_b; assumption. }
        assert (HVnb: Valid_dist (mu pd_notb)).  { apply dst_Valid_get_notb; assumption. }
        assert (Hb_eq: mu pd_b == (  mu (extract_b_pd b pd0_ori) +
                                    mu {| dom := dom2; mu := []; all_partial := HPD2 |})%dist_state). {  
                        rewrite dst_add_0_r. rewrite dst_add_0_r in Hadd.
                        apply Peq_implies_get_b_Peq with (b:= b) in Hadd; try assumption. }
        assert (Hnotb_eq:  mu pd_notb == (  mu (extract_notb_pd b pd0_ori) +
                                    mu {| dom := dom2; mu := []; all_partial := HPD2 |})%dist_state). {
                        rewrite dst_add_0_r. rewrite dst_add_0_r in Hadd.
                        apply Peq_implies_get_notb_Peq with (b:= b) in Hadd; try assumption. }
        assert (HWDb2: well_defined_winstr_with_pd c (extract_b_pd b pd0_ori)). { 
          apply pd_decom_r_preserves_WD_win with (c:= c) in Hb_eq; try assumption. }
        apply IHc with (pd':= pd0) in Hb_eq; try assumption. 
        destruct Hb_eq as [x Hx]. destruct Hx as [x0 Hx0]. 
        destruct Hx0 as [HNSx Hx0]. destruct Hx0 as [HNSx0 Hmu].
        destruct Hmu as [Hmu Hdomx].
        assert (Hvx: Valid_dist (mu x)). { apply Valid_forall_NS in HNSx; try assumption. }
        assert (Hvx0: Valid_dist (mu x0)). { apply Valid_forall_NS in HNSx0; try assumption. } 
        assert (HVl: Valid_dist (mu x + mu x0)%dist_state). { 
          rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq.
          apply Valid_linear_under_eq_prob; try assumption; try lra. 
          rewrite <- Rmult_plus_distr_l. rewrite Rmult_1_l.
          apply NS_preserve_sum_eq in HNSx; try assumption.
          apply NS_preserve_sum_eq in HNSx0; try assumption.
          rewrite <- HNSx. rewrite <- HNSx0. rewrite Rplus_0_r.
          destruct HVb1. assumption.
         }
        assert (Hv1: Valid_dist (mu pd0)). { apply Valid_forall_NS in HNS1; try assumption. }
        assert (HWDx: well_defined_winstr_with_pd (WHILE b DO c END) x). { 
          apply pd_decom_r_preserves_WD_win with (c:= (While b c)) in Hmu; try assumption. }
        assert (Hdom1': (dom pd1 == dom pd0 ∪ get_modvar_in_winstr (WHILE b DO c END))%domain). { 
          apply orbdom_after_NS; try assumption. }
        apply IHHNS2 in Hmu; try assumption.
        destruct Hmu as [x' Hx]. destruct Hx as [x0' Hx0]. 
        destruct Hx0 as [HNSx' Hx0]. destruct Hx0 as [HNSx0' Hmu].
        destruct Hmu as [Heq Hdomx'].
        assert (Hdomx2: (dom x' == dom pd0_ori)%domain). { 
          apply orbdom_after_NS in HNSx; try assumption.
          apply orbdom_after_NS in HNSx'; try assumption.
          apply dom_equiv_trans with (l1:= (dom x ∪ get_modvar_in_winstr (WHILE b DO c END))%domain); try assumption.
          apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr (WHILE b DO c END)) in HNSx; try assumption.
          simpl in HNSx. simpl.
          apply dom_equiv_trans with (l1:= ((dom0 ∪ get_modvar_in_winstr c) ∪ get_modvar_in_winstr c)%domain); try assumption.
          rewrite <- orb_domain_assoc. rewrite orb_domain_refl.
          apply dom_equiv_sym. apply orb_domain_elim_r.
          destruct Hdom. 
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
        exists (pd_add x' (extract_notb_pd b pd0_ori) (Hdomx2)),  
                (pd_emp (orb_domain (dom2) (get_modvar_in_winstr (While b c)))).
        split. { eapply NS_While_Mixed; try assumption.
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply HWDx.
          - simpl. destruct Hdom. 
            apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
          - apply HNSx.
          - apply HNSx'.
          - simpl. reflexivity.
          - simpl. apply dom_equiv_refl. }
        split. { apply (@NS_While_Nil b c {| dom := dom2; mu := []; all_partial := HPD2 |}). 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - unfold b_supp_classify. simpl. reflexivity. }
        split. { rewrite dst_add_0_r. rewrite H4. unfold pd_add.
          simpl.  
          rewrite dst_add_0_r in Hnotb_eq.
          apply dst_add_preserves_equiv; try assumption.
          apply NS_pd_implies_nil in HNSx0. destruct HNSx0. 
          apply NS_mu_implies_nil in HNSx0'; try assumption. 
          rewrite HNSx0' in Heq. rewrite dst_add_0_r in Heq. assumption. } 
        simpl. split; try assumption.
          + destruct Hdomx'. 
            apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption.
          + simpl in Hdom'. 
            apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c)%domain); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
      - pose (pd0_ori:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
        pose (pd2_ori:= {| dom := dom2; mu := (s2, p2) :: mu2'; all_partial := HPD2 |}).
        assert (HVb: Valid_dist (mu pd_b)). { apply dst_Valid_get_b; assumption. }
        assert (HVnb: Valid_dist (mu pd_notb)).  { apply dst_Valid_get_notb; assumption. }
        assert (HVb0: Valid_dist (mu (extract_b_pd b pd0_ori))). { apply dst_Valid_get_b; assumption. }
        assert (HVb1: Valid_dist (mu (extract_b_pd b pd2_ori))). { apply dst_Valid_get_b; assumption. }
        assert (HVnb0: Valid_dist (mu (extract_notb_pd b pd0_ori))). { apply dst_Valid_get_notb; assumption. }
        assert (HVnb1: Valid_dist (mu (extract_notb_pd b pd2_ori))). { apply dst_Valid_get_notb; assumption. }
        assert (HVbp1:Valid_dist (mu (extract_b_pd b pd0_ori) + 
                                  mu (extract_b_pd b pd2_ori))%dist_state). { 
          rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq.
          apply Valid_linear_under_eq_prob; try assumption; try lra. 
          rewrite <- Rmult_plus_distr_l. rewrite Rmult_1_l.
          destruct Hvl. rewrite dst_sum_prob_decom in H6.
          split. 
          - rewrite <- Rplus_0_r with (r:= 0). destruct HVb0; destruct HVb1. apply Rplus_le_compat; intuition.
          - destruct H6. 
            apply Rle_trans with (r2:= sum_probs (mu pd0_ori) + sum_probs (mu pd2_ori)); try assumption.
            apply Rplus_le_compat; try apply sum_prob_get_b_le; try assumption. }
        assert (HVnbp1:Valid_dist (mu (extract_notb_pd b pd0_ori) + 
                                   mu (extract_notb_pd b pd2_ori))%dist_state). { 
          rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq.
          apply Valid_linear_under_eq_prob; try assumption; try lra. 
          rewrite <- Rmult_plus_distr_l. rewrite Rmult_1_l.
          destruct Hvl. rewrite dst_sum_prob_decom in H6.
          split. 
          - rewrite <- Rplus_0_r with (r:= 0). destruct HVnb0; destruct HVnb1. apply Rplus_le_compat; intuition.
          - destruct H6. 
            apply Rle_trans with (r2:= sum_probs (mu pd0_ori) + sum_probs (mu pd2_ori)); try assumption.
            apply Rplus_le_compat; try apply sum_prob_get_notb_le; try assumption.
                                    }
        assert (Hmub: (mu pd_b ==   get_b_in_mu b (mu pd0_ori) + get_b_in_mu b (mu pd2_ori))%dist_state). { 
          apply Peq_implies_get_b_Peq with (b:= b) in Hadd; try assumption.
          rewrite <- get_b_assoc. assumption. }
        assert (Hmunb: (mu pd_notb ==   get_notb_in_mu b (mu pd0_ori) +   get_notb_in_mu b (mu pd2_ori))%dist_state). { 
          repeat rewrite <- dst_get_notb_coef_mult. rewrite <- get_notb_assoc.
          apply Peq_implies_get_notb_Peq; try assumption. }
        specialize (IHc (extract_b_pd b pd0_ori) HVb0 (extract_b_pd b pd2_ori) HVb1 HVbp1 pd_b HVb Hmub Hdom).
        specialize (IHc pd0 HNS1). destruct IHc. destruct H6. 
        destruct H6 as [HNSx Hx]. destruct Hx as [HNSx0 Hmu0]. destruct Hmu0 as [Hmu0 Hdom0].
        assert (Hvx: Valid_dist (mu x)). { apply Valid_forall_NS in HNSx; try assumption. }
        assert (Hvx0: Valid_dist (mu x0)). { apply Valid_forall_NS in HNSx0; try assumption. } 
        assert (HVl: Valid_dist (mu x + mu x0)%dist_state). { 
          rewrite <- dst_mult_1_l. rewrite dst_mult_plus_distr_r_eq.
          apply Valid_linear_under_eq_prob; try assumption; try lra. 
          rewrite <- Rmult_plus_distr_l. rewrite Rmult_1_l.
          apply NS_preserve_sum_eq in HNSx; try assumption.
          apply NS_preserve_sum_eq in HNSx0; try assumption.
          rewrite <- HNSx. rewrite <- HNSx0. 
          rewrite <- dst_sum_prob_decom. destruct HVbp1. assumption. } 
        assert (Hv1: Valid_dist (mu pd0)). { apply Valid_forall_NS in HNS1; try assumption. }
        assert (HWDx: well_defined_winstr_with_pd (WHILE b DO c END) x). { 
          apply pd_decom_r_preserves_WD_win with (c:= (While b c)) in Hmu0; try assumption. }
        assert (HWDx0: well_defined_winstr_with_pd (WHILE b DO c END) x0). { 
          apply pd_decom_l_preserves_WD_win with (c:= (While b c)) in Hmu0; try assumption. } 
        assert (HWD0b: well_defined_winstr_with_pd c (extract_b_pd b pd0_ori)). { 
              apply pd_decom_r_preserves_WD_win with (c:= c)  
                (pd0:= (extract_b_pd b pd0_ori)) (pd1:= (extract_b_pd b pd2_ori)) 
                  in Hmub; try assumption. }
        assert (HWD2b: well_defined_winstr_with_pd c (extract_b_pd b pd2_ori)). { 
              apply pd_decom_l_preserves_WD_win with (c:= c)  
                (pd0:= (extract_b_pd b pd0_ori)) (pd1:= (extract_b_pd b pd2_ori)) 
                  in Hmub; try assumption. }
        assert (Hdom1': (dom pd1 == dom pd0 ∪ get_modvar_in_winstr (WHILE b DO c END))%domain). { 
          apply orbdom_after_NS; try assumption. }
        apply IHHNS2 in Hmu0; try assumption.
        destruct Hmu0 as [x' Hx]. destruct Hx as [x0' Hx0]. 
        destruct Hx0 as [HNSx' Hx0]. destruct Hx0 as [HNSx0' Hmu].
        destruct Hmu as [Heq Hdomx'].
        assert (Hdomx0: (dom x' == dom pd0_ori)%domain). { 
          apply orbdom_after_NS in HNSx; try assumption.
          apply orbdom_after_NS in HNSx'; try assumption.
          apply dom_equiv_trans with (l1:= (dom x ∪ get_modvar_in_winstr (WHILE b DO c END))%domain); try assumption.
          apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr (WHILE b DO c END)) in HNSx; try assumption.
          simpl in HNSx. simpl.
          apply dom_equiv_trans with (l1:= ((dom0 ∪ get_modvar_in_winstr c) ∪ get_modvar_in_winstr c)%domain); try assumption.
          rewrite <- orb_domain_assoc. rewrite orb_domain_refl.
          apply dom_equiv_sym. apply orb_domain_elim_r.
          destruct Hdom. 
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
        assert (Hdomx2: (dom x0' == dom pd2_ori)%domain). { 
          apply orbdom_after_NS in HNSx0; try assumption.
          apply orbdom_after_NS in HNSx0'; try assumption.
          apply dom_equiv_trans with (l1:= (dom x0 ∪ get_modvar_in_winstr (WHILE b DO c END))%domain); try assumption.
          apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr (WHILE b DO c END)) in HNSx0; try assumption.
          simpl in HNSx0. simpl.
          apply dom_equiv_trans with (l1:= ((dom2 ∪ get_modvar_in_winstr c) ∪ get_modvar_in_winstr c)%domain); try assumption.
          rewrite <- orb_domain_assoc. rewrite orb_domain_refl.
          apply dom_equiv_sym. apply orb_domain_elim_r.
          destruct Hdom. 
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
        
        destruct (b_supp_classify b pd0_ori) eqn: HB0. {
            unfold b_supp_classify in HB0. simpl in HB0. 
            destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s0, p0) :: mu0')));
            destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s0, p0) :: mu0'))); try discriminate. }
        {
          destruct (b_supp_classify b pd2_ori) eqn: HB2.
          - unfold b_supp_classify in HB2. simpl in HB2. 
            destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s2, p2) :: mu2')));
            destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s2, p2) :: mu2'))); try discriminate.
          - apply bMixed_implies_neq_nil in H0. destruct H0 as [Hb Hnotb]. 
            apply bT_getnotb_nil in HB0. apply bT_getnotb_nil in HB2. 
            simpl in HB0, HB2. simpl in Hmunb.  
            rewrite HB0, HB2 in Hmunb. simpl in Hmunb.
            assert (get_notb_in_mu b (mu pd) = []). { apply dst_eq_nil_iff; split; assumption. }
            rewrite H0 in Hnotb. contradiction.
          - assert (Hpd0: extract_b_pd b pd0_ori ≡ pd0_ori). { apply bT_supp_implies_getb_eq in HB0; try assumption. }
            assert (HWD0: well_defined_winstr_with_pd c pd0_ori). {
              apply pd_equiv_preserves_WD_win with (pd:= extract_b_pd b pd0_ori); try assumption. }
            apply step_deterministic with (c:= c) (pd1:= pd0_ori) in HNSx; try assumption. 
            destruct HNSx as [pd0' HNS0']. destruct HNS0' as [Heqx0 HNS0'].
            assert (Hv0': Valid_dist (mu pd0')). { apply Valid_forall_NS in HNS0'; try assumption. }
            assert (Hpd2: extract_notb_pd b pd2_ori ≡ pd2_ori). { apply bF_supp_implies_getnotb_eq in HB2; try assumption. }
            assert (HWD0': well_defined_winstr_with_pd (WHILE b DO c END) pd0'). {
              apply pd_equiv_preserves_WD_win with (pd:= x); try assumption. }
            apply step_deterministic with (c:= While b c) (pd1:= pd0') in HNSx'; try assumption. 
            destruct HNSx' as [pd1' HNS1']. destruct HNS1' as [Heqx1 HNS1'].
            exists pd1', pd2_ori. 
            split. { eapply NS_While_All_True; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWD0'.
              - apply HNS0'.
              - assumption. }
            split. { apply NS_While_All_False; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - destruct Hdom. simpl. simpl in H7. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
            split. { 
              rewrite H4.
              apply dst_add_preserves_equiv. 
              - apply bF_getnotb_nil in HB2. 
                apply NS_mu_implies_nil in HNSx0; try assumption. 
                apply NS_mu_implies_nil in HNSx0'; try assumption. simpl in Heq. 
                rewrite HNSx0' in Heq. rewrite dst_add_0_r in Heq. 
                apply dst_equiv_trans with (mu1:= (  mu x')%dist_state); try assumption.
                destruct Heqx1.
                try try apply dst_mult_preserves_equiv; try assumption.
              - apply bT_getnotb_nil in HB0. simpl in HB0. 
                simpl in Hmunb. rewrite HB0 in Hmunb. rewrite dst_add_0_l in Hmunb.
                apply dst_equiv_trans with (mu1:= (  (if negb (evalB_st b s2) then (s2, p2) :: get_notb_in_mu b mu2' else get_notb_in_mu b mu2'))%dist_state); try assumption.
                destruct Hpd2. try try apply dst_mult_preserves_equiv; try assumption. }
            split; try assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x')%domain); try assumption.
              destruct Heqx1. assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x0')%domain); try assumption.
          - assert (Hpd0: extract_b_pd b pd0_ori ≡ pd0_ori). { apply bT_supp_implies_getb_eq in HB0; try assumption. }
            assert (HWD0: well_defined_winstr_with_pd c pd0_ori). {
              apply pd_equiv_preserves_WD_win with (pd:= extract_b_pd b pd0_ori); try assumption. }
            apply step_deterministic with (c:= c) (pd1:= pd0_ori) in HNSx; try assumption. 
            destruct HNSx as [pd0' HNS0']. destruct HNS0' as [Heqx0 HNS0'].
            assert (Hv0': Valid_dist (mu pd0')). { apply Valid_forall_NS in HNS0'; try assumption. }
            assert (HWD0': well_defined_winstr_with_pd (WHILE b DO c END) pd0'). {
              apply pd_equiv_preserves_WD_win with (pd:= x); try assumption. }
            apply step_deterministic with (c:= While b c) (pd1:= pd0') in HNSx'; try assumption. 
            destruct HNSx' as [pd1' HNS1']. destruct HNS1' as [Heqx1 HNS1'].
            exists pd1', (pd_add x0' (extract_notb_pd b pd2_ori) (Hdomx2)). 
            split. { eapply NS_While_All_True; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWD0'.
              - apply HNS0'.
              - assumption. }
            split. { eapply NS_While_Mixed; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWDx0.
              - destruct Hdom. simpl. simpl in H7. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply HNSx0.
              - apply HNSx0'.
              - simpl. reflexivity.
              - simpl. apply dom_equiv_refl. }
            split. { 
              rewrite H4. 
              apply dst_equiv_trans with (mu1:= ((  mu x' +   mu x0') + mu pd_notb)%dist_state).
              - apply dst_add_inj_r. assumption.
              - rewrite <- dst_add_assoc_eq.  
                apply dst_add_preserves_equiv.
                + destruct Heqx1. try try apply dst_mult_preserves_equiv; try assumption.
                + simpl.  apply dst_add_inj_l. 
                  apply bT_getnotb_nil in HB0. simpl in HB0. 
                  simpl in Hmunb. rewrite HB0 in Hmunb. rewrite dst_add_0_l in Hmunb. assumption. }
            simpl. split; try assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x')%domain); try assumption.
              destruct Heqx1. assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x0')%domain); try assumption.
              apply dom_equiv_refl.
        }
        {
          destruct (b_supp_classify b pd2_ori) eqn: HB2.
          - unfold b_supp_classify in HB2. simpl in HB2. 
            destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s2, p2) :: mu2')));
            destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s2, p2) :: mu2'))); try discriminate.
          - assert (Hpd2: extract_b_pd b pd2_ori ≡ pd2_ori). { apply bT_supp_implies_getb_eq in HB2; try assumption. }
            assert (HWD2: well_defined_winstr_with_pd c pd2_ori). {
              apply pd_equiv_preserves_WD_win with (pd:= extract_b_pd b pd2_ori); try assumption. }
            apply step_deterministic with (c:= c) (pd1:= pd2_ori) in HNSx0; try assumption. 
            destruct HNSx0 as [pd2' HNS2']. destruct HNS2' as [Heqx2 HNS2'].
            assert (Hv2': Valid_dist (mu pd2')). { apply Valid_forall_NS in HNS2'; try assumption. }
            assert (Hpd0: extract_notb_pd b pd0_ori ≡ pd0_ori). { apply bF_supp_implies_getnotb_eq in HB0; try assumption. }
            assert (HWD2': well_defined_winstr_with_pd (WHILE b DO c END) pd2'). {
              apply pd_equiv_preserves_WD_win with (pd:= x0); try assumption. }
            apply step_deterministic with (c:= While b c) (pd1:= pd2') in HNSx0'; try assumption. 
            destruct HNSx0' as [pd3' HNS3']. destruct HNS3' as [Heqx3 HNS3'].
            exists pd0_ori, pd3'. 
            split. { apply NS_While_All_False; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - destruct Hdom. simpl. simpl in H7. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
            split. { eapply NS_While_All_True; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWD2'.
              - apply HNS2'.
              - assumption. }
            split. { 
              rewrite H4. apply dst_equiv_trans with (mu1:= (mu pd_notb + mu pd1)%dist_state); try apply dst_add_comm.
              apply dst_add_preserves_equiv. 
              - apply bT_getnotb_nil in HB2. simpl in HB2. 
                simpl in Hmunb. rewrite HB2 in Hmunb. rewrite dst_add_0_r in Hmunb.
                apply dst_equiv_trans with (mu1:= (  (if negb (evalB_st b s0) then (s0, p0) :: get_notb_in_mu b mu0' else get_notb_in_mu b mu0'))%dist_state); try assumption.
                destruct Hpd0. try try apply dst_mult_preserves_equiv; try assumption.
              - apply bF_getnotb_nil in HB0. 
                apply NS_mu_implies_nil in HNSx; try assumption. 
                apply NS_mu_implies_nil in HNSx'; try assumption. simpl in Heq. 
                rewrite HNSx' in Heq. rewrite dst_add_0_l in Heq. 
                apply dst_equiv_trans with (mu1:= (  mu x0')%dist_state); try assumption.
                destruct Heqx3.
                try apply dst_mult_preserves_equiv; try assumption.
               }
            split; try assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x')%domain); try assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x0')%domain); try assumption.
              destruct Heqx3. assumption.
          - apply bMixed_implies_neq_nil in H0. destruct H0 as [Hb Hnotb]. 
            apply bF_getnotb_nil in HB0. apply bF_getnotb_nil in HB2. 
            simpl in HB0, HB2. simpl in Hmub.  
            rewrite HB0, HB2 in Hmub. simpl in Hmub.
            assert (get_b_in_mu b (mu pd) = []). { apply dst_eq_nil_iff; split; assumption. }
            rewrite H0 in Hb. contradiction.
          - assert (Hpd0: extract_notb_pd b pd0_ori ≡ pd0_ori). { apply bF_supp_implies_getnotb_eq in HB0; try assumption. }
            exists pd0_ori, (pd_add x0' (extract_notb_pd b pd2_ori) (Hdomx2)). 
            split. { eapply NS_While_All_False; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - simpl. destruct Hdom. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
            split. { eapply NS_While_Mixed; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWDx0.
              - destruct Hdom. simpl. simpl in H7. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply HNSx0.
              - apply HNSx0'.
              - simpl. reflexivity.
              - simpl. apply dom_equiv_refl. }
            split. { 
              rewrite H4. 
              apply dst_equiv_trans with (mu1:= ((  mu x' +   mu x0') + mu pd_notb)%dist_state).
              - apply dst_add_inj_r. assumption. 
              - apply bF_getnotb_nil in HB0. 
                apply NS_mu_implies_nil in HNSx; try assumption. 
                apply NS_mu_implies_nil in HNSx'; try assumption. 
                rewrite HNSx'. rewrite dst_add_0_l.
                apply dst_equiv_trans with (mu1:= (  mu x0' + (  get_notb_in_mu b (mu pd0_ori) +   get_notb_in_mu b (mu pd2_ori))%dist_state)%dist_state); try assumption.
                + apply dst_add_inj_l. assumption.
                + apply dst_equiv_trans with (mu1:= (  get_notb_in_mu b (mu pd0_ori) + (  mu x0' +   get_notb_in_mu b (mu pd2_ori)))%dist_state).
                  * repeat rewrite dst_add_assoc_eq. apply dst_add_inj_r. apply dst_add_comm.
                  * apply dst_add_preserves_equiv. 
                  ** destruct Hpd0. try apply dst_mult_preserves_equiv; try assumption.
                  ** simpl.  apply dst_equiv_refl. }
            simpl. split; try assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x')%domain); try assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x0')%domain); try assumption.
              apply dom_equiv_refl.
        }
        { 
          destruct (b_supp_classify b pd2_ori) eqn: HB2.
          - unfold b_supp_classify in HB2. simpl in HB2. 
            destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s2, p2) :: mu2')));
            destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s2, p2) :: mu2'))); try discriminate.
          - assert (Hpd2: extract_b_pd b pd2_ori ≡ pd2_ori). { apply bT_supp_implies_getb_eq in HB2; try assumption. }
            assert (HWD0: well_defined_winstr_with_pd c pd2_ori). {
              apply pd_equiv_preserves_WD_win with (pd:= extract_b_pd b pd2_ori); try assumption. }
            apply step_deterministic with (c:= c) (pd1:= pd2_ori) in HNSx0; try assumption. 
            destruct HNSx0 as [pd2' HNS2']. destruct HNS2' as [Heqx2 HNS2'].
            assert (Hv2': Valid_dist (mu pd2')). { apply Valid_forall_NS in HNS2'; try assumption. }
            assert (HWD2': well_defined_winstr_with_pd (WHILE b DO c END) pd2'). {
              apply pd_equiv_preserves_WD_win with (pd:= x0); try assumption. }
            apply step_deterministic with (c:= While b c) (pd1:= pd2') in HNSx0'; try assumption. 
            destruct HNSx0' as [pd3' HNS3']. destruct HNS3' as [Heqx3 HNS3'].
            exists (pd_add x' (extract_notb_pd b pd0_ori) (Hdomx0)), pd3'. 
            split. { eapply NS_While_Mixed; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWDx.
              - destruct Hdom. simpl. simpl in H7. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply HNSx.
              - apply HNSx'.
              - simpl. reflexivity.
              - simpl. apply dom_equiv_refl. }
            split. { eapply NS_While_All_True; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWD2'.
              - apply HNS2'.
              - assumption. }
            split. { 
              rewrite H4. 
              apply dst_equiv_trans with (mu1:= ((  mu x' +   mu x0') + mu pd_notb)%dist_state).
              - apply dst_add_inj_r. assumption. 
              - simpl.
                repeat rewrite <- dst_add_assoc_eq.  
                apply dst_add_inj_l. 
                apply dst_equiv_trans with (mu1:= (get_notb_in_mu b (mu pd) +   mu x0')%dist_state).
                + apply dst_add_comm.
                + apply dst_add_preserves_equiv.
                  * apply bT_getnotb_nil in HB2. simpl in HB2. 
                  simpl in Hmunb. rewrite HB2 in Hmunb. rewrite dst_add_0_r in Hmunb. assumption. 
                  * destruct Heqx3. try apply dst_mult_preserves_equiv; try assumption. }
            simpl. split; try assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x')%domain); try assumption.
              apply dom_equiv_refl.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x0')%domain); try assumption.
              destruct Heqx3. assumption.
          - assert (Hpd2: extract_notb_pd b pd2_ori ≡ pd2_ori). { apply bF_supp_implies_getnotb_eq in HB2; try assumption. }
            exists (pd_add x' (extract_notb_pd b pd0_ori) (Hdomx0)), pd2_ori. 
            split. { eapply NS_While_Mixed; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWDx.
              - destruct Hdom. simpl. simpl in H7. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply HNSx.
              - apply HNSx'.
              - simpl. reflexivity.
              - simpl. apply dom_equiv_refl. }
            split. { eapply NS_While_All_False; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - simpl. destruct Hdom. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
            split. { 
              rewrite H4. 
              apply dst_equiv_trans with (mu1:= ((  mu x' +   mu x0') + mu pd_notb)%dist_state).
              - apply dst_add_inj_r. assumption. 
              - apply bF_getnotb_nil in HB2.
                apply NS_mu_implies_nil in HNSx0; try assumption. 
                apply NS_mu_implies_nil in HNSx0'; try assumption. 
                rewrite HNSx0'. rewrite dst_add_0_r. simpl. 
                rewrite <- dst_add_assoc_eq. apply dst_add_inj_l.
                apply dst_equiv_trans with (mu1:= ((  get_notb_in_mu b (mu pd0_ori) +   get_notb_in_mu b (mu pd2_ori))%dist_state)); try assumption.
                apply dst_add_inj_l. destruct Hpd2. try assumption. }
            simpl. split; try assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x')%domain); try assumption.
              apply dom_equiv_refl.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x0')%domain); try assumption.
          - exists (pd_add x' (extract_notb_pd b pd0_ori) (Hdomx0)).
            exists (pd_add x0' (extract_notb_pd b pd2_ori) (Hdomx2)).
            split. { eapply NS_While_Mixed; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWDx.
              - simpl. destruct Hdom. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply HNSx.
              - apply HNSx'.
              - simpl. reflexivity.
              - apply dom_equiv_refl. }
            split. { eapply NS_While_Mixed; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWDx0.
              - simpl. destruct Hdom. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply HNSx0.
              - apply HNSx0'.
              - simpl. reflexivity.
              - apply dom_equiv_refl. }
            split. {
              rewrite H4. 
              apply dst_equiv_trans with (mu1:= ((  mu x' +   mu x0') + mu pd_notb)%dist_state).
              - apply dst_add_inj_r. assumption. 
              - simpl.  repeat rewrite <- dst_add_assoc_eq. apply dst_add_inj_l. 
                apply dst_equiv_trans with (mu1:= (  mu x0' + 
                (  (if negb (evalB_st b s0) then (s0, p0) :: get_notb_in_mu b mu0' else get_notb_in_mu b mu0') + 
                  (if negb (evalB_st b s2) then (s2, p2) :: get_notb_in_mu b mu2' else get_notb_in_mu b mu2')))%dist_state).
                + apply dst_add_inj_l. assumption.
                + repeat rewrite dst_add_assoc_eq. apply dst_add_inj_r. 
                apply dst_add_comm. }
            simpl. split; try assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption.
              destruct Hdomx'. assumption.
        }      
    }
Qed.

Lemma linear_NS: forall c (pd0 pd1 pd pd': partial_dist) (p: R), 
  Valid_dist (mu pd0) -> Valid_dist (mu pd1) -> Valid_dist (mu pd) -> 
  Valid_dist ((p * (mu pd0) + (1-p) * (mu pd1))%dist_state) ->
  (0 < p < 1)%R -> NS c pd pd' ->
  (mu pd) == (p * (mu pd0) + (1-p) * (mu pd1))%dist_state -> 
  ((dom pd) == (dom pd0))%domain /\ ((dom pd) == (dom pd1))%domain ->
    (exists pd0' pd1', NS c pd0 pd0' /\ NS c pd1 pd1' /\
      mu pd' == (p * (mu pd0') + (1-p) * (mu pd1'))%dist_state /\
      ((dom pd') == (dom pd0'))%domain /\ ((dom pd') == (dom pd1'))%domain).
Proof. 
  intros c pd0 pd1 pd pd' p Hvalid0 Hvalid1 Hvalid Hvl Hp HNS Hadd Hdom.
  generalize dependent pd'. generalize dependent pd.
  generalize dependent pd1. generalize dependent pd0. 
  induction c as [| | | | |]; intros. 
  - inversion HNS; subst. exists pd0, pd1. 
    split; try apply NS_Skip. 
    split; try apply NS_Skip. 
    split; assumption.
  - inversion HNS; subst; simpl in *. 
    destruct Hdom. 
    assert (HWFa0: WF_aexp_with_pd a pd0). {
      apply dom_equiv_preserves_WF_aexp with (pd:= pd); try assumption. }
    assert (HWFa1: WF_aexp_with_pd a pd1). {
      apply dom_equiv_preserves_WF_aexp with (pd:= pd); try assumption. }
    exists (DAssn_under_pd n a pd0 HWFa0), (DAssn_under_pd n a pd1 HWFa1).
    split; try apply NS_DAssign. 
    split; try apply NS_DAssign.
    simpl in *. rewrite <- DAss_eq_under_addAndmult. 
    assert (HPDp: partial_dst_Prop (dom pd) (p * mu pd0 + (1 - p) * mu pd1)%dist_state). {
      apply PD_linear; try assumption.
      - destruct Hp. apply Rlt_le. assumption.  
      - apply Rp_lt1_minus_p_bounds with (p:= p) in Hp. destruct Hp. apply Rlt_le. assumption.
      - apply dom_equiv_sym. assumption.
      - apply dom_equiv_sym. assumption. }
    split. { apply DA_step_deter; try assumption. }
    split; apply dom_eq_orb_compat_right; assumption.
  - inversion HNS; subst. destruct Hdom. 
    assert (HWFa0': WF_distaexp_with_pd (proj1_sig v) pd0). {
     apply dom_equiv_preserves_WF_distaexp with (pd:= pd); try assumption. }
    assert (HWFa1': WF_distaexp_with_pd (proj1_sig v) pd1). {
      apply dom_equiv_preserves_WF_distaexp with (pd:= pd); try assumption. }
    exists (RAssn_under_pd n v pd0 HWFa0'), (RAssn_under_pd n v pd1 HWFa1').
    split; try apply NS_RAssign. 
    split; try apply NS_RAssign. simpl. 
    rewrite <- RAss_equiv_under_addAndmult.
    split. 
    + apply RA_step_deter with (x:=n) (da:=(proj1_sig v)) in Hadd; try assumption.
    + split; apply dom_eq_orb_compat_right; try assumption.
  - inversion HNS; subst. 
    specialize IHc1 with (pd0:= pd0) (pd1:= pd1) (pd:= pd) (pd':= pd3); try assumption.
    specialize (IHc1 Hvalid0  Hvalid1 Hvl  Hvalid Hadd Hdom H3).
    destruct IHc1 as [mu01 Htemp]. destruct Htemp as [mu11 Htemp]. 
    destruct Htemp as [HNSmu0 Htemp]. destruct Htemp as [HNSmu1 Hmu3].
    destruct Hmu3 as [Hmu3 Hdom3].
    assert (Hmu3': mu pd3 == (p * mu mu01 + (1 - p) * mu mu11)%dist_state) by assumption.
    assert (Hv01: Valid_dist (mu mu01)). {apply Valid_forall_NS in HNSmu0; assumption. }
    assert (Hv11: Valid_dist (mu mu11)). {apply Valid_forall_NS in HNSmu1; assumption. }
    assert (Hv3: Valid_dist (mu pd3)). {apply Valid_forall_NS in H3; assumption. }
    assert (Hv': Valid_dist (mu pd')). {apply Valid_forall_NS in H6; assumption. }
    assert (Hvmu: Valid_dist (p * mu mu01 + (1 - p) * mu mu11)%dist_state). {
      apply Valid_linear; try assumption. 
          ++ apply Rbound_loss. assumption.
          ++ apply Rp_1_minus_p_bounds. apply Rbound_loss. assumption.
          ++ rewrite R_plus_sub_eq_1. apply Rle_refl. }
    apply IHc2 with (pd0:= mu01) (pd1:= mu11) (pd:= pd3) (pd':= pd') in Hmu3; try assumption.
    + destruct Hmu3 as [mu02 Htemp]. destruct Htemp as [mu12 Htemp]. 
      destruct Htemp as [HNSmu02 Htemp]. destruct Htemp as [HNSmu12 Hmu2].
      destruct Hmu2 as [ Hmu2 Hdom2].
      exists (mu02), (mu12). split.
      * eapply NS_Seq; try assumption. 
      ** destruct Hdom3. 
        apply pd_linear_decom_r_preserve_WD_win with (c:= c1) in Hadd; try assumption. 
      ** apply pd_linear_decom_r_preserve_WD_win with (c:= c2) in Hmu3'; try assumption.
         apply Hmu3'.
      ** apply HNSmu0. 
      ** apply HNSmu02.
      * split. 
      ** assert (Hp1: (1- (1 - p)) = p). { field. }
      eapply NS_Seq; try assumption.
      -- destruct Hdom3. 
        apply dst_equiv_trans with (mu2:= ((1 - p) * mu pd1 + (1- (1 - p)) * mu pd0)%dist_state) in Hadd. 
        ++ apply pd_linear_decom_r_preserve_WD_win with (c:= c1) in Hadd; try assumption.
        +++ apply Rp_lt1_minus_p_bounds with (p:= p). assumption.
        +++ apply Valid_linear; try assumption. 
          *** apply Rp_1_minus_p_bounds. apply Rbound_loss. assumption.
          *** apply Rbound_loss. rewrite Hp1. assumption.
          *** rewrite Hp1. unfold Rminus. rewrite Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_r. apply Rle_refl.
        +++ destruct Hdom. split; try assumption. 
        ++ rewrite Hp1. apply dst_add_comm.
      -- apply dst_equiv_trans with (mu2:= ((1 - p) * mu mu11 + (1- (1 - p)) * mu mu01)%dist_state) in Hmu3'. 
        ++ apply pd_linear_decom_r_preserve_WD_win with (c:= c2) in Hmu3'; try assumption.
        +++ apply Hmu3'.
        +++ apply Rp_lt1_minus_p_bounds with (p:= p). assumption.
        +++ apply Valid_linear; try assumption. 
          *** apply Rp_1_minus_p_bounds. apply Rbound_loss. assumption.
          *** rewrite Hp1. apply Rbound_loss. assumption.
          *** rewrite R_plus_sub_eq_1. apply Rle_refl.
        +++ destruct Hdom3. split; try assumption.
        ++ rewrite Hp1. apply dst_add_comm.
      -- apply HNSmu1. 
      -- apply HNSmu12.
      ** split; try assumption.
  - assert (HV_linear: Valid_dist (p * mu pd0 + (1 - p) * mu pd1)%dist_state). { 
      apply Valid_linear; try assumption. 
      - apply Rbound_loss. assumption. 
      - apply Rp_1_minus_p_bounds. apply Rbound_loss. assumption. 
      - rewrite R_plus_sub_eq_1. apply Rle_refl. }
    assert (HPD_linear: partial_dst_Prop (dom pd) ((p * mu pd0 + (1 - p) * mu pd1)%dist_state)). {
      destruct Hdom. apply PD_linear; try assumption.
      - destruct Hp. apply Rlt_le. assumption. 
      - apply Rp_lt1_minus_p_bounds with (p:= p) in Hp. destruct Hp. apply Rlt_le. assumption.
      - apply dom_equiv_sym. assumption.
      - apply dom_equiv_sym. assumption. } 
    destruct pd0 as [dom0 mu0 HPD0]. destruct pd1 as [dom1 mu1 HPD1].
    destruct mu0 as [|(s0,p0) mu0']; destruct mu1 as [|(s1,p1) mu1'].
    { assert (Hmu: mu pd = []). { apply dst_eq_nil_iff. split; try assumption.  }
      inversion HNS; subst.
      - assert (HWD10: well_defined_winstr_with_pd c1 {| dom := dom0; mu := []; all_partial := HPD0 |}). 
        { apply pd_linear_decom_r_preserve_WD_win with (c:= c1) in Hadd; try assumption. }
        assert (HWD20: well_defined_winstr_with_pd c2 {| dom := dom0; mu := []; all_partial := HPD0 |}). 
        { apply pd_linear_decom_r_preserve_WD_win with (c:= c2) in Hadd; try assumption. }
        assert (HWD11: well_defined_winstr_with_pd c1 {| dom := dom1; mu := []; all_partial := HPD1 |}). 
        { apply pd_linear_decom_l_preserve_WD_win with (c:= c1) in Hadd; try assumption. }
        assert (HWD21: well_defined_winstr_with_pd c2 {| dom := dom1; mu := []; all_partial := HPD1 |}). 
        { apply pd_linear_decom_l_preserve_WD_win with (c:= c2) in Hadd; try assumption. }
        unfold b_supp_classify in H3. rewrite Hmu in H3. 
        exists (pd_emp (dom0 ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI))), 
          (pd_emp (dom1 ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI))).  
        split. { 
          apply (@NS_IF_Nil b c1 c2 {| dom := dom0; mu := []; all_partial := HPD0 |}); try assumption.
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - destruct H8. destruct H. apply IHc1 with (pd':= x) in Hadd; try assumption. 
            destruct Hadd. destruct H1. destruct H1. exists x0. split; try assumption.
            split; simpl. 
            + apply orbdom_after_NS in H1. simpl in H1. apply dom_equiv_sym. assumption.
            + apply NS_pd_implies_nil in H1. destruct H1. rewrite H1. apply dst_equiv_refl.
          - destruct H9. destruct H. apply IHc2 with (pd':= x) in Hadd; try assumption. 
            destruct Hadd. destruct H1. destruct H1. exists x0. split; try assumption.
            split; simpl. 
            + apply orbdom_after_NS in H1. simpl in H1. apply dom_equiv_sym. assumption.
            + apply NS_pd_implies_nil in H1. destruct H1. rewrite H1. apply dst_equiv_refl. }
        split. { 
          apply (@NS_IF_Nil b c1 c2 {| dom := dom1; mu := []; all_partial := HPD1 |}); try assumption.
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - destruct H8. destruct H. apply IHc1 with (pd':= x) in Hadd; try assumption. 
            destruct Hadd. destruct H1. destruct H1. destruct H6. exists x1. split; try assumption.
            split; simpl. 
            + apply orbdom_after_NS in H6. simpl in H6. apply dom_equiv_sym. assumption.
            + apply NS_pd_implies_nil in H6. destruct H6. rewrite H6. apply dst_equiv_refl.
          - destruct H9. destruct H. apply IHc2 with (pd':= x) in Hadd; try assumption. 
            destruct Hadd. destruct H1. destruct H1. destruct H6. exists x1. split; try assumption.
            split; simpl. 
            + apply orbdom_after_NS in H6. simpl in H6. apply dom_equiv_sym. assumption.
            + apply NS_pd_implies_nil in H6. destruct H6. rewrite H6. apply dst_equiv_refl. }
        simpl. split; try apply dst_equiv_refl. destruct Hdom. 
        split; apply dom_eq_orb_compat_right; assumption.
      - unfold b_supp_classify in H3. rewrite Hmu in H3. discriminate.
      - unfold b_supp_classify in H3. rewrite Hmu in H3. discriminate.
      - unfold b_supp_classify in H3. rewrite Hmu in H3. discriminate.
    } 
    {
      inversion HNS; subst. 
      - rewrite dst_add_0_l in Hadd. apply pd_Nil_mu in H3. rewrite H3 in Hadd.
        apply dst_equiv_sym in Hadd.
        simpl in Hadd. 
        assert (HVl: Valid_dist ((1 - p) * mu {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |})%dist_state). {
          apply Valid_mult_cofe; try assumption. apply Rp_lt1_minus_p_bounds with (p:= p) in Hp. apply Rbound_loss. assumption. }
        destruct (Req_dec_T (1 - p) 0) eqn: Hp1.
        + apply Rp_lt1_minus_p_bounds with (p:= p) in Hp. destruct Hp. rewrite e in H. apply Rlt_irrefl in H. contradiction.
        + apply dst_cons_valid_contra in Hadd; try assumption; try contradiction. 
          simpl in Hvl. rewrite Hp1 in Hvl. assumption.
      - assert (HWD10: well_defined_winstr_with_pd c1 {| dom := dom0; mu := []; all_partial := HPD0 |}). 
          { apply pd_linear_decom_r_preserve_WD_win with (c:= c1) in Hadd; try assumption. }
        assert (HWD20: well_defined_winstr_with_pd c2 {| dom := dom0; mu := []; all_partial := HPD0 |}). 
          { apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption.
          destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.  }
        assert (HWD11: well_defined_winstr_with_pd c1 {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}). 
          { apply pd_linear_decom_l_preserve_WD_win with (c:= c1) in Hadd; try assumption. } 
        assert (HWD21: well_defined_winstr_with_pd c2 (pd_emp (dom {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}))). 
          { apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption.
          destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl. }
        assert (Heq': pd ≡ cofe_pd {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |} (1 - p)). {
          destruct Hdom. split; simpl; try assumption. }
        assert (Hpmius: 0 <1- p < 1 ). { apply Rp_lt1_minus_p_bounds with (p:= p) in Hp. assumption. } 
        assert (HNS1: NS c1 pd pd'); try assumption.
        apply IHc1 with (pd0:= {| dom := dom0; mu := []; all_partial := HPD0 |}) 
                        (pd1:= {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}) in H9; try assumption.
        destruct H9. destruct H. destruct H. destruct H0.
        apply NS_pd_implies_nil in H. destruct H as [Hmux Hdomx]. rewrite Hmux in H1. simpl in H1. 
        exists (pd_emp (dom0 ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI))), x0. 
        split. { 
          apply (@NS_IF_Nil b c1 c2 {| dom := dom0; mu := []; all_partial := HPD0 |}); try assumption.
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - unfold b_supp_classify. simpl. reflexivity.
          - apply IHc1 with (pd':= pd') in Hadd; try assumption. 
            destruct Hadd. destruct H. destruct H. exists x1. split; try assumption.
            split; simpl. 
            + apply orbdom_after_NS in H. simpl in H. apply dom_equiv_sym. assumption.
            + apply NS_pd_implies_nil in H. destruct H. rewrite H. apply dst_equiv_refl.
          - destruct H10. destruct H. 
            apply step_deterministic with (pd1:= {| dom := dom0; mu := []; all_partial := HPD0 |}) in H7; try assumption.
            + destruct H7. destruct H7. exists x2. split; try assumption. split; simpl.
              ++ apply orbdom_after_NS in H8. simpl in H8. apply dom_equiv_sym. assumption.
              ++ apply NS_pd_implies_nil in H8. destruct H8. rewrite H8. apply dst_equiv_refl. 
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
          }
        split. { 
          apply NS_IF_All_True; try assumption. 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - rewrite <- b_classify_mult_coef with (p:= 1-p). 
            + rewrite dst_equiv_implies_b_classify with (pd1:= pd); try assumption.
              apply pd_equiv_sym. 
              destruct Hdom. split; simpl; try assumption.
            + apply Rp_lt1_minus_p_bounds with (p:= p) in Hp. destruct Hp. assumption.
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c1); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          - destruct H10. destruct H. 
            apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}))) in H7; try assumption.
            + destruct H7. destruct H7. exists x2. split; try assumption. split; simpl. 
              ++ apply orbdom_after_NS in H8. simpl in H8. apply dom_equiv_sym. assumption.
              ++ apply NS_pd_implies_nil in H8. destruct H8. rewrite H8. apply dst_equiv_refl.
            + split; simpl; try apply dst_equiv_refl. destruct Hdom. assumption.
           }
        split. { rewrite dst_add_0_l. simpl. destruct H1. assumption. }
        destruct H1. destruct H1.
        split; simpl; try assumption. 
        apply dom_equiv_trans with (l1:= dom x); try assumption.
        apply dom_equiv_trans with (l1:= (dom0 ∪ get_modvar_in_winstr c1)%domain); try assumption.
        apply dom_equiv_trans with (l1:= dom0 ∪ get_modvar_in_winstr c1); try apply dom_equiv_refl.
        rewrite orb_domain_assoc. apply orb_domain_elim_r.
        destruct Hdom. simpl in H6.
        apply dom_subset_eq_compat_left with (X := dom pd ∪ get_modvar_in_winstr c1); try assumption.
        apply dom_eq_orb_compat_right. assumption.
      - assert (Heq': pd ≡ cofe_pd {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |} (1 - p)). {
          destruct Hdom. split; simpl; try assumption. }
        assert (Hpmius: 0 <1- p < 1 ). { apply Rp_lt1_minus_p_bounds with (p:= p) in Hp. assumption. }
        assert (HNS2: NS c2 pd pd'); try assumption.
        apply IHc2 with (pd0:= {| dom := dom0; mu := []; all_partial := HPD0 |}) 
                        (pd1:= {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}) in H9; try assumption.
        destruct H9. destruct H. destruct H. destruct H0.
        apply NS_pd_implies_nil in H. destruct H as [Hmux Hdomx]. rewrite Hmux in H1. simpl in H1. 
        exists (pd_emp (dom0 ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI))), x0. 
        split. { apply (@NS_IF_Nil b c1 c2 {| dom := dom0; mu := []; all_partial := HPD0 |}). 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - unfold b_supp_classify. simpl. reflexivity.
          - apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
            split; simpl; try apply dst_equiv_refl. destruct Hdom. assumption.
          - apply pd_linear_decom_r_preserve_WD_win with (c:= c2) in Hadd; try assumption.
          - destruct H10. destruct H. 
            apply step_deterministic with (pd1:= ({| dom := dom0; mu := []; all_partial := HPD0 |})) in H7; try assumption.
            + destruct H7. destruct H7. exists x2. split; try assumption. split; simpl. 
              ++ apply orbdom_after_NS in H8. simpl in H8. apply dom_equiv_sym. assumption.
              ++ apply NS_pd_implies_nil in H8. destruct H8. rewrite H8. apply dst_equiv_refl.
            + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption.
              split; simpl; try apply dst_equiv_refl. destruct Hdom. assumption.
            + split; simpl; try apply dst_equiv_refl. destruct Hdom. assumption.
          - apply IHc2 with (pd':= pd') in Hadd; try assumption. 
            destruct Hadd. destruct H. destruct H. exists x1. split; try assumption. split; simpl.
            + apply orbdom_after_NS in H. simpl in H. apply dom_equiv_sym. assumption.
            + apply NS_pd_implies_nil in H. destruct H. rewrite H. apply dst_equiv_refl.
          }
        split. { apply NS_IF_All_False; try assumption. 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - rewrite <- b_classify_mult_coef with (p:= 1-p). 
            + rewrite dst_equiv_implies_b_classify with (pd1:= pd); try assumption.
              apply pd_equiv_sym. 
              destruct Hdom. split; simpl; try assumption.
            + apply Rp_lt1_minus_p_bounds with (p:= p) in Hp. destruct Hp. assumption.
          - apply pd_equiv_preserves_WD_win with (pd:= pd_emp (dom pd)); try assumption. 
            destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
          - apply pd_mult_coef_dom_r_preserves_WD_win with (p:= (1-p)); try assumption.  
            apply pd_equiv_preserves_WD_win with (pd:= pd); try assumption.
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c2); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          - destruct H10. destruct H. 
            apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}))) in H7; try assumption.
            + destruct H7. destruct H7. exists x2. split; try assumption. split; simpl. 
              ++ apply orbdom_after_NS in H8. simpl in H8. apply dom_equiv_sym. assumption.
              ++ apply NS_pd_implies_nil in H8. destruct H8. rewrite H8. apply dst_equiv_refl.
            + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption.
              split; simpl; try apply dst_equiv_refl. destruct Hdom. assumption.
            + split; simpl; try apply dst_equiv_refl. destruct Hdom. assumption.
           }
        split. { rewrite dst_add_0_l. simpl. destruct H1. assumption. }
        destruct H1. destruct H1.
        split; simpl; try assumption. 
        apply dom_equiv_trans with (l1:= dom x); try assumption.
        apply dom_equiv_trans with (l1:= (dom0 ∪ get_modvar_in_winstr c2)%domain); try assumption.
        apply dom_equiv_trans with (l1:= dom0 ∪ get_modvar_in_winstr c2); try apply dom_equiv_refl.
        rewrite orb_domain_comm with (l:= get_modvar_in_winstr c1). 
        rewrite orb_domain_assoc. apply orb_domain_elim_r.
        destruct Hdom. simpl in H6.
        apply dom_subset_eq_compat_left with (X := dom pd ∪ get_modvar_in_winstr c2); try assumption.
        apply dom_eq_orb_compat_right. assumption.
      - rewrite dst_add_0_l in Hadd.
        assert (Heq': pd ≡ cofe_pd {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |} (1 - p)). {
          destruct Hdom. split; simpl; try assumption. }
        assert (Hpmius: 0 <1- p < 1 ). { apply Rp_lt1_minus_p_bounds with (p:= p) in Hp. assumption. } 
        pose(pd1_ori := {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}).
        assert (HVb1: Valid_dist (mu (extract_b_pd b pd1_ori))). { apply dst_Valid_get_b; assumption. }
        assert (HVnb1: Valid_dist (mu (extract_notb_pd b pd1_ori))). { apply dst_Valid_get_notb; assumption. }
        assert (HVb: Valid_dist (mu pd_b)). { apply dst_Valid_get_b; assumption. }
        assert (HVnb: Valid_dist (mu pd_notb)).  { apply dst_Valid_get_notb; assumption. }
        assert (Hb_eq: mu pd_b == (p * mu {| dom := dom0; mu := []; all_partial := HPD0 |} +
                                  (1 - p) * mu (extract_b_pd b pd1_ori))%dist_state). {  
                        rewrite dst_add_0_l. 
                        apply Peq_implies_get_b_Peq with (b:= b) in Hadd; try assumption.
                        rewrite dst_get_b_coef_mult in Hadd.
                        simpl. simpl in Hadd. assumption. }
        assert (Hnotb_eq: mu pd_notb == (p * mu {| dom := dom0; mu := []; all_partial := HPD0 |} +
                                        (1 - p) * mu (extract_notb_pd b pd1_ori))%dist_state). {
                        rewrite dst_add_0_l. 
                        apply Peq_implies_get_notb_Peq with (b:= b) in Hadd; try assumption.
                        rewrite dst_get_notb_coef_mult in Hadd.
                        simpl. simpl in Hadd. assumption. }
        apply IHc1 with (pd0:= {| dom := dom0; mu := []; all_partial := HPD0 |}) 
                        (pd1:= extract_b_pd b pd1_ori) in H7; try assumption; 
        apply IHc2 with (pd0:= {| dom := dom0; mu := []; all_partial := HPD0 |}) 
                        (pd1:= extract_notb_pd b pd1_ori) in H8; try assumption.
        + destruct H8. destruct H. destruct H. destruct H0. destruct H1.
          destruct H7. destruct H7. destruct H7. destruct H10. destruct H11.
          assert (Htmp: (dom x0 == dom x2)%domain). { destruct H8. destruct H14.
            apply orbdom_after_NS in H10. apply orbdom_after_NS in H0. 
            apply dom_equiv_trans with (l1:= (dom (extract_notb_pd b pd1_ori) ∪ get_modvar_in_winstr c2)%domain); try assumption.
            apply dom_equiv_sym.
            apply dom_equiv_trans with (l1:= (dom (extract_b_pd b pd1_ori) ∪ get_modvar_in_winstr c1)%domain); try assumption.
            simpl. destruct H6.
            - apply dom_eq_orb_compat_left. assumption.
            - destruct H6. destruct Hdom. simpl in H16. 
              apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c2); try assumption.
              + apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c1); try assumption. 
                * apply dom_eq_orb_compat_right. apply dom_equiv_sym. assumption.
                * apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H17.
                apply dom_equiv_sym in H6. apply dom_equiv_trans with (l1:= dom pd); try assumption.
              + apply dom_eq_orb_compat_right. assumption. }
          assert (Hdom02: (dom x2 == dom x0)%domain). { apply dom_equiv_sym. assumption. }
          exists (pd_emp (dom0 ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI))), (pd_add x2 x0 (Hdom02)). 
          split. { apply (@NS_IF_Nil b c1 c2 {| dom := dom0; mu := []; all_partial := HPD0 |}). 
            - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
            - unfold b_supp_classify. simpl. reflexivity.
            - apply pd_linear_decom_r_preserve_WD_win with (c:= c1) in Hb_eq; try assumption. 
              rewrite dst_add_0_l. apply Valid_mult_cofe; try assumption. 
              apply Rbound_loss. assumption.
            - apply pd_linear_decom_r_preserve_WD_win with (c:= c2) in Hnotb_eq; try assumption.
              rewrite dst_add_0_l. apply Valid_mult_cofe; try assumption. 
              apply Rbound_loss. assumption.
            - exists x1. split; try assumption. split; simpl. 
              + apply orbdom_after_NS in H7. apply dom_equiv_sym. assumption.
              + apply NS_pd_implies_nil in H7. destruct H7. rewrite H7. apply dst_equiv_refl.
            - exists x. split; try assumption. split; simpl. 
              + apply orbdom_after_NS in H. apply dom_equiv_sym. assumption.
              + apply NS_pd_implies_nil in H. destruct H. rewrite H. apply dst_equiv_refl. }
          split. { eapply NS_IF_Mixed; try assumption.
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption. 
              - apply dst_equiv_implies_b_classify with (b:= b) in Heq'; try assumption. 
                rewrite H3 in Heq'. symmetry in Heq'. destruct Hpmius. 
                rewrite b_classify_mult_coef in Heq'; try assumption.
              - apply pd_mult_coef_dom_r_preserves_WD_win with (p:= (1-p)); try assumption.
                apply pd_equiv_preserves_WD_win with (pd:= pd_b); try assumption.
                + apply Valid_mult_cofe; try apply dst_Valid_get_b; try assumption.
                  apply Rbound_loss. assumption.
                + destruct Hdom. split; simpl; try assumption.
              - apply pd_mult_coef_dom_r_preserves_WD_win with (p:= (1-p)); try assumption.
                apply pd_equiv_preserves_WD_win with (pd:= pd_notb); try assumption.
                + apply Valid_mult_cofe; try apply dst_Valid_get_notb; try assumption.
                  apply Rbound_loss. assumption.
                + destruct Hdom. split; simpl; try assumption.
              - destruct H6. 
                + left. assumption.
                + destruct H6. right. simpl. destruct Hdom. 
                  split; apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply H10.
              - apply H0.
              - simpl. reflexivity.
              - simpl. apply dom_equiv_refl.
              - simpl. assumption. }
          split. { simpl. 
              apply NS_pd_implies_nil in H7. destruct H7. rewrite H7 in H11. simpl in H11.
              apply NS_pd_implies_nil in H. destruct H. rewrite H in H1. simpl in H1.
              rewrite dst_mult_plus_distr_r_eq. rewrite H9.
              apply dst_add_preserves_equiv; try assumption. }
          simpl. split; try assumption.
          * apply orbdom_after_NS in HNS. simpl in HNS. 
            apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI)); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          * destruct H8. apply orbdom_after_NS in HNS. simpl in HNS.  
            apply dom_equiv_trans with (l1:= (dom pd ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2))%domain); try assumption.
            apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym in H10.
            apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c1)%domain); try assumption.
            destruct Hdom. simpl in H16. 
            apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c1); try assumption.
              ** destruct H6. 
                -- apply dom_eq_orb_compat_left. apply dom_equiv_sym.
                apply orb_domain_elim_r. destruct H6. assumption.
                -- destruct H6. apply dom_equiv_trans with (l1:= 
                    (dom pd ∪ get_modvar_in_winstr c1) ∪ (dom pd ∪ get_modvar_in_winstr c2)); try apply dom_eq_orb_dis_r.
                apply dom_equiv_sym. apply orb_domain_elim_r. 
                apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H18. 
                apply dom_equiv_trans with (l1:= dom pd); try assumption.
                apply dom_equiv_sym. assumption.
              ** apply dom_eq_orb_compat_right. assumption. 
        + rewrite dst_add_0_l. apply Valid_mult_cofe; try assumption. apply Rbound_loss. assumption.
        + rewrite dst_add_0_l. apply Valid_mult_cofe; try assumption. apply Rbound_loss. assumption.
        + rewrite dst_add_0_l. apply Valid_mult_cofe; try assumption. apply Rbound_loss. assumption.
    }
    {
      inversion HNS; subst. 
      - rewrite dst_add_0_r in Hadd. apply pd_Nil_mu in H3. rewrite H3 in Hadd.
        apply dst_equiv_sym in Hadd.
        simpl in Hadd. 
        assert (HVl: Valid_dist (p * mu {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |})%dist_state). {
          apply Valid_mult_cofe; try assumption. apply Rbound_loss. assumption. }
        destruct (Req_dec_T p 0) eqn: Hp1.
        + destruct Hp. rewrite e in H. apply Rlt_irrefl in H. contradiction.
        + apply dst_cons_valid_contra in Hadd; try assumption; try contradiction. 
          simpl in Hvl. rewrite Hp1 in Hvl. rewrite dst_add_0_r in Hvl. assumption.
      - assert (Heq': pd ≡ cofe_pd {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |} p). {
          destruct Hdom. rewrite dst_add_0_r in Hadd. split; simpl; try assumption. }
        assert (Hpmius: 0 <1- p < 1 ). { apply Rp_lt1_minus_p_bounds with (p:= p) in Hp. assumption. } 
        assert (HNS1: NS c1 pd pd') by assumption.
        apply IHc1 with (pd1:= {| dom := dom1; mu := []; all_partial := HPD1 |}) 
                        (pd0:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}) in H9; try assumption.
        rewrite dst_add_0_r in Hvl.         
        destruct H9. destruct H. destruct H. destruct H0.
        apply NS_pd_implies_nil in H0. destruct H0 as [Hmux0 Hdomx0]. 
        rewrite Hmux0 in H1. simpl in H1. rewrite dst_add_0_r in H1. 
        exists x, (pd_emp (dom1 ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI))). 
        split. { apply NS_IF_All_True; try assumption. 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - rewrite <- b_classify_mult_coef with (p:= p). 
            + rewrite dst_equiv_implies_b_classify with (pd1:= pd); try assumption.
              apply pd_equiv_sym. 
              destruct Hdom. rewrite dst_add_0_r in Hadd. split; simpl; try assumption. 
            + destruct Hp. assumption.
          - apply pd_mult_coef_dom_r_preserves_WD_win with (p:= p); try assumption.  
            apply pd_equiv_preserves_WD_win with (pd:= pd); try assumption.
          - apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
            destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c1); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          - destruct H10. destruct H0. 
            apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}))) in H7; try assumption.
            + destruct H7. destruct H7. exists x2. split; try assumption. 
              split; simpl.
              * apply orbdom_after_NS in H8; try assumption. simpl in H8. apply dom_equiv_sym. assumption.
              * apply NS_pd_implies_nil in H8; try assumption. destruct H8. rewrite H8. apply dst_equiv_refl.
            + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
              destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
           }
        split. { apply (@NS_IF_Nil b c1 c2 {| dom := dom1; mu := []; all_partial := HPD1 |}). 
            - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
            - unfold b_supp_classify. simpl. reflexivity.
            - apply pd_linear_decom_l_preserve_WD_win with (c:= c1) in Hadd; try assumption. 
            - apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
              destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
            - apply IHc1 with (pd':= pd') in Hadd; try assumption. 
              destruct Hadd. destruct H0. destruct H0. destruct H7. 
              exists x2. split; try assumption. split; simpl. 
              + apply orbdom_after_NS in H7; try assumption. simpl in H7. apply dom_equiv_sym. assumption.
              + apply NS_pd_implies_nil in H7; try assumption. destruct H7. rewrite H7. apply dst_equiv_refl.
            - destruct H10. destruct H0. 
              apply step_deterministic with (pd1:= {| dom := dom1; mu := []; all_partial := HPD1 |}) in H7; try assumption.
              + destruct H7. destruct H7. exists x2. split; try assumption. split; simpl. 
                * apply orbdom_after_NS in H8; try assumption. simpl in H8. apply dom_equiv_sym. assumption.
                * apply NS_pd_implies_nil in H8; try assumption. destruct H8. rewrite H8. apply dst_equiv_refl.
              + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
                destruct Hdom. split; simpl; try apply dst_equiv_refl. assumption.
              + destruct Hdom. split; simpl; try apply dst_equiv_refl. assumption.
            }
        split. { rewrite dst_add_0_r. simpl. destruct H1. assumption. }
        destruct H1. destruct H1.
        split; simpl; try assumption. 
        apply dom_equiv_trans with (l1:= dom x0); try assumption.
        apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c1)%domain); try assumption.
        apply dom_equiv_trans with (l1:= dom1 ∪ get_modvar_in_winstr c1); try apply dom_equiv_refl.
        rewrite orb_domain_assoc. apply orb_domain_elim_r.
        destruct Hdom. simpl in H6.
        apply dom_subset_eq_compat_left with (X := dom pd ∪ get_modvar_in_winstr c1); try assumption.
        apply dom_eq_orb_compat_right. assumption.
      - assert (Heq': pd ≡ cofe_pd {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |} p). {
          destruct Hdom. rewrite dst_add_0_r in Hadd. split; simpl; try assumption. }
        assert (Hpmius: 0 <1- p < 1 ). { apply Rp_lt1_minus_p_bounds with (p:= p) in Hp. assumption. } 
        assert (HNS2: NS c2 pd pd') by assumption.
        apply IHc2 with (pd1:= {| dom := dom1; mu := []; all_partial := HPD1 |}) 
                        (pd0:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}) in H9; try assumption.
        destruct H9. destruct H. destruct H. destruct H0.
        rewrite dst_add_0_r in Hvl.
        apply NS_pd_implies_nil in H0. destruct H0 as [Hmux0 Hdomx0]. rewrite Hmux0 in H1. simpl in H1.
        rewrite dst_add_0_r in H1.
        exists x, (pd_emp (dom1 ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI))). 
        split. { apply NS_IF_All_False; try assumption. 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - rewrite <- b_classify_mult_coef with (p:= p). 
            + rewrite dst_equiv_implies_b_classify with (pd1:= pd); try assumption.
              apply pd_equiv_sym. destruct Hdom.
              rewrite dst_add_0_r in Hadd. split; simpl; try assumption. 
            + destruct Hp. assumption.
          - apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
            destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
          - apply pd_linear_decom_r_preserve_WD_win with (c:= c2) in Hadd; try assumption.
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c2); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          - destruct H10. destruct H0. 
            apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}))) in H7; try assumption.
            + destruct H7. destruct H7. exists x2. split; try assumption. split; simpl.
              * apply orbdom_after_NS in H8; try assumption. simpl in H8. apply dom_equiv_sym. assumption.
              * apply NS_pd_implies_nil in H8; try assumption. destruct H8. rewrite H8. apply dst_equiv_refl.
            + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
              destruct Hdom. split; simpl; try apply dst_equiv_refl. assumption.
            + destruct Hdom. split; simpl; try apply dst_equiv_refl. assumption.
           }
        split. { apply (@NS_IF_Nil b c1 c2 {| dom := dom1; mu := []; all_partial := HPD1 |}).
            - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
            - unfold b_supp_classify. simpl. reflexivity.
            - apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
              destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
            - apply pd_linear_decom_l_preserve_WD_win with (c:= c2) in Hadd; try assumption.
            - destruct H10. destruct H0. 
              apply step_deterministic with (pd1:= {| dom := dom1; mu := []; all_partial := HPD1 |}) in H7; try assumption.
              + destruct H7. destruct H7. exists x2. split; try assumption. split; simpl.
                * apply orbdom_after_NS in H8; try assumption. simpl in H8. apply dom_equiv_sym. assumption.
                * apply NS_pd_implies_nil in H8; try assumption. destruct H8. rewrite H8. apply dst_equiv_refl.
              + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
                destruct Hdom. split; simpl; try apply dst_equiv_refl. assumption.
              + destruct Hdom. split; simpl; try apply dst_equiv_refl. assumption.
            - apply IHc2 with (pd':= pd') in Hadd; try assumption. 
              destruct Hadd. destruct H0. destruct H0. destruct H7.
              exists x2. split; try assumption. split; simpl. 
              + apply orbdom_after_NS in H7; try assumption. simpl in H7. apply dom_equiv_sym. assumption.
              + apply NS_pd_implies_nil in H7; try assumption. destruct H7. rewrite H7. apply dst_equiv_refl.
             }
        split. { rewrite dst_add_0_r. simpl. destruct H1. assumption. }
        destruct H1. destruct H1.
        split; simpl; try assumption. 
        apply dom_equiv_trans with (l1:= dom x0); try assumption.
        apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c2)%domain); try assumption.
        apply dom_equiv_trans with (l1:= dom1 ∪ get_modvar_in_winstr c2); try apply dom_equiv_refl.
        rewrite orb_domain_comm with (l:= get_modvar_in_winstr c1). 
        rewrite orb_domain_assoc. apply orb_domain_elim_r.
        destruct Hdom. simpl in H6.
        apply dom_subset_eq_compat_left with (X := dom pd ∪ get_modvar_in_winstr c2); try assumption.
        apply dom_eq_orb_compat_right. assumption.
      - assert (Heq': pd ≡ cofe_pd {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |} p). {
          destruct Hdom. rewrite dst_add_0_r in Hadd. split; simpl; try assumption. }
        assert (Hpmius: 0 <1- p < 1 ). { apply Rp_lt1_minus_p_bounds with (p:= p) in Hp. assumption. } 
        pose(pd1_ori := {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
        assert (HVb1: Valid_dist (mu (extract_b_pd b pd1_ori))). { apply dst_Valid_get_b; assumption. }
        assert (HVnb1: Valid_dist (mu (extract_notb_pd b pd1_ori))). { apply dst_Valid_get_notb; assumption. }
        assert (HVb: Valid_dist (mu pd_b)). { apply dst_Valid_get_b; assumption. }
        assert (HVnb: Valid_dist (mu pd_notb)).  { apply dst_Valid_get_notb; assumption. }
        rewrite dst_add_0_r in Hadd. rewrite dst_add_0_r in Hvl.
        assert (Hb_eq: mu pd_b == (p * mu (extract_b_pd b pd1_ori)  +
                                  (1 - p) * mu {| dom := dom1; mu := []; all_partial := HPD1 |})%dist_state). {  
                        rewrite dst_add_0_r. 
                        apply Peq_implies_get_b_Peq with (b:= b) in Hadd; try assumption.
                        rewrite dst_get_b_coef_mult in Hadd.
                        simpl. simpl in Hadd. assumption. }
        assert (Hnotb_eq: mu pd_notb == (p * mu (extract_notb_pd b pd1_ori)  +
                                  (1 - p) * mu {| dom := dom1; mu := []; all_partial := HPD1 |})%dist_state). {
                        rewrite dst_add_0_r. 
                        apply Peq_implies_get_notb_Peq with (b:= b) in Hadd; try assumption.
                        rewrite dst_get_notb_coef_mult in Hadd.
                        simpl. simpl in Hadd. assumption. }
        apply IHc1 with (pd1:= {| dom := dom1; mu := []; all_partial := HPD1 |}) 
                        (pd0:= extract_b_pd b pd1_ori) in H7; try assumption; 
        apply IHc2 with (pd1:= {| dom := dom1; mu := []; all_partial := HPD1 |}) 
                        (pd0:= extract_notb_pd b pd1_ori) in H8; try assumption.
        + destruct H8. destruct H. destruct H. destruct H0. destruct H1.
          destruct H7. destruct H7. destruct H7. destruct H10. destruct H11.
          assert (Hdom02: (dom x1 == dom x)%domain). { destruct H8. destruct H14.
            apply orbdom_after_NS in H7. apply orbdom_after_NS in H. 
            apply dom_equiv_trans with (l1:= (dom (extract_b_pd b pd1_ori) ∪ get_modvar_in_winstr c1)%domain); try assumption.
            apply dom_equiv_sym.
            apply dom_equiv_trans with (l1:= (dom (extract_notb_pd b pd1_ori) ∪ get_modvar_in_winstr c2)%domain); try assumption.
            simpl. destruct H6.
            - apply dom_eq_orb_compat_left. apply dom_equiv_sym. assumption.
            - destruct H6. destruct Hdom. simpl in H17. 
              apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c2); try assumption.
              + apply dom_eq_orb_compat_right. apply dom_equiv_sym. assumption.
              + apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c1); try assumption. 
                * apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H17.
                  apply dom_equiv_sym in H17. apply dom_equiv_trans with (l1:= dom pd); try assumption.
                * apply dom_eq_orb_compat_right. assumption. }
          exists (pd_add x1 x (Hdom02)), (pd_emp (dom1 ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI))). 
          split. { eapply NS_IF_Mixed; try assumption.
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption. 
              - apply dst_equiv_implies_b_classify with (b:= b) in Heq'; try assumption. 
                rewrite H3 in Heq'. symmetry in Heq'. destruct Hp. 
                rewrite b_classify_mult_coef in Heq'; try assumption.
              - apply pd_mult_coef_dom_r_preserves_WD_win with (p:= p); try assumption.
                apply pd_equiv_preserves_WD_win with (pd:= pd_b); try assumption.
                + apply Valid_mult_cofe; try apply dst_Valid_get_b; try assumption.
                  apply Rbound_loss. assumption.
                + destruct Hdom. rewrite dst_add_0_r in Hb_eq. split; simpl; try assumption.
              - apply pd_mult_coef_dom_r_preserves_WD_win with (p:= p); try assumption.
                apply pd_equiv_preserves_WD_win with (pd:= pd_notb); try assumption.
                + apply Valid_mult_cofe; try apply dst_Valid_get_notb; try assumption.
                  apply Rbound_loss. assumption.
                + destruct Hdom. rewrite dst_add_0_r in Hnotb_eq. split; simpl; try assumption.
              - destruct H6. 
                + left. assumption.
                + destruct H6. right. simpl. destruct Hdom. 
                  split; apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply H7.
              - apply H.
              - simpl. reflexivity.
              - simpl. apply dom_equiv_refl.
              - simpl. assumption. }
          split. { apply (@NS_IF_Nil b c1 c2 {| dom := dom1; mu := []; all_partial := HPD1 |}).
            - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
            - unfold b_supp_classify. simpl. reflexivity.
            - apply pd_linear_decom_l_preserve_WD_win with (c:= c1) in Hb_eq; try assumption. 
              rewrite dst_add_0_r. apply Valid_mult_cofe; try assumption. 
              apply Rbound_loss. assumption.
            - apply pd_linear_decom_l_preserve_WD_win with (c:= c2) in Hnotb_eq; try assumption.
              rewrite dst_add_0_r. apply Valid_mult_cofe; try assumption. 
              apply Rbound_loss. assumption.
            - exists x2. split; try assumption. split; simpl. 
              + apply orbdom_after_NS in H10. apply dom_equiv_sym. assumption.
              + apply NS_pd_implies_nil in H10. destruct H10. rewrite H10. apply dst_equiv_refl.
            - exists x0. split; try assumption. split; simpl. 
              + apply orbdom_after_NS in H0. apply dom_equiv_sym. assumption.
              + apply NS_pd_implies_nil in H0. destruct H0. rewrite H0. apply dst_equiv_refl. }
          split. { simpl. rewrite H9.
              apply NS_pd_implies_nil in H10. destruct H10. rewrite H10 in H11. rewrite dst_add_0_r in H11.
              apply NS_pd_implies_nil in H0. destruct H0. rewrite H0 in H1. rewrite dst_add_0_r in H1.
              rewrite dst_mult_plus_distr_r_eq. rewrite dst_add_0_r. 
              apply dst_add_preserves_equiv; assumption. }
          simpl. split; try assumption.
          * destruct H14. apply orbdom_after_NS in HNS. simpl in HNS.  
            apply orbdom_after_NS in H7. simpl in H7. apply dom_equiv_sym in H7.
            apply dom_equiv_trans with (l1:= (dom pd ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2))%domain); try assumption.
            apply dom_equiv_trans with (l1:= (dom0 ∪ get_modvar_in_winstr c1)%domain); try assumption.
            destruct Hdom. 
            apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c1); try assumption.
              ** destruct H6. 
                -- apply dom_eq_orb_compat_left. apply dom_equiv_sym.
                apply orb_domain_elim_r. destruct H6. assumption.
                -- destruct H6. apply dom_equiv_trans with (l1:= 
                    (dom pd ∪ get_modvar_in_winstr c1) ∪ (dom pd ∪ get_modvar_in_winstr c2)); try apply dom_eq_orb_dis_r.
                apply dom_equiv_sym. 
                apply orb_domain_elim_r. apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H18. 
                apply dom_equiv_trans with (l1:= dom pd); try assumption.
                apply dom_equiv_sym. assumption.
              ** apply dom_eq_orb_compat_right. assumption. 
          * apply orbdom_after_NS in HNS. simpl in HNS. 
            apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr (IF b THEN c1 ELSE c2 FI)); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
        + rewrite dst_add_0_r. apply Valid_mult_cofe; try assumption. apply Rbound_loss. assumption.
        + rewrite dst_add_0_r. apply Valid_mult_cofe; try assumption. apply Rbound_loss. assumption.
        + rewrite dst_add_0_r. apply Valid_mult_cofe; try assumption. apply Rbound_loss. assumption.
    }
    { 
      assert (Hpmius: 0 < 1- p < 1 ). { apply Rp_lt1_minus_p_bounds with (p:= p) in Hp. assumption. } 
      assert (Hprefl: (1- (1 - p)) = p). { field. }
      pose (pd0:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
      pose (pd1:= {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}).
      assert (Hadd_sym: mu pd == (mu (cofe_pd pd1 (1 - p)) + mu (cofe_pd pd0 (1 - (1 - p))))%dist_state). {
        rewrite Hprefl. 
        apply dst_equiv_trans with (mu1:= (p * mu {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |} +
                    (1 - p) * mu {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |})%dist_state); try assumption.
        apply dst_add_comm. }
      assert (HVl_sym: Valid_dist (mu (cofe_pd pd1 (1 - p)) + mu (cofe_pd pd0 (1 - (1 - p))))%dist_state). {
          apply Valid_linear_under_eq_prob; try assumption; try apply Valid_mult_cofe; try assumption; try apply Rle_0_1.
              * apply Rp_1_minus_p_bounds. apply Rbound_loss. assumption.
              * rewrite Hprefl. apply Rbound_loss. assumption.
              * rewrite Hprefl. repeat rewrite Rmult_1_l. rewrite Rplus_comm. 
                 repeat rewrite <- dst_sum_prob_coef_mult. rewrite <- dst_sum_prob_decom.
                destruct Hvl. assumption. }
      inversion HNS; subst.
      - apply pd_Nil_mu in H3. rewrite H3 in Hadd. apply dst_equiv_sym in Hadd. 
        simpl in Hadd. destruct (Req_dec_T p 0) eqn: Hp1.
        + destruct Hp. rewrite e in H. apply Rlt_irrefl in H. contradiction.
        + apply dst_cons_valid_contra in Hadd; try assumption; try contradiction. 
          simpl in Hvl. rewrite Hp1 in Hvl. destruct ( Req_dec_T (1 - p) 0) eqn: Hp2. 
          * apply Rp_lt1_minus_p_bounds with (p:= p) in Hp. destruct Hp. rewrite e in H. apply Rlt_irrefl in H. contradiction.
          * assumption.
      - apply IHc1 with (pd0:= pd0) (pd1:= pd1) in H9; try assumption.
        destruct H9. destruct H. destruct H. destruct H0. destruct H1.
        exists x, x0.
        split. { apply NS_IF_All_True; try assumption. 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - rewrite <- b_classify_mult_coef with (p:= p). 
            + apply bT_classify_decom_r with (pd0:= cofe_pd pd0 p) (pd1:= cofe_pd pd1 (1-p)) in H3; try assumption.
              * simpl. destruct (Req_dec_T p 0). 
              ** destruct Hp as [Hp_gt0 Hp_lt1]. rewrite e in Hp_gt0. apply Rlt_irrefl in Hp_gt0. contradiction.
              ** unfold not. intros. discriminate.
              * simpl. destruct Hdom. assumption.
              * simpl. destruct Hdom. assumption.
            + destruct Hp. assumption.
          - apply pd_linear_decom_r_preserve_WD_win with (p:= p) (pd0:= pd0) (pd1:= pd1) in H4; try assumption.
          - apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
            + apply Valid_dist_nil.
            + apply Valid_dist_nil.
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl. 
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c1); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          - destruct H10. destruct H8. 
            apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}))) in H9; try assumption.
            + destruct H9. destruct H9. exists x2. split; try assumption. split; simpl.
              * apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym. assumption.
              * apply NS_mu_implies_nil in H10; try reflexivity. rewrite H10. apply dst_equiv_refl.
            + apply Valid_dist_nil.
            + apply Valid_dist_nil.
            + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
              * apply Valid_dist_nil.
              * apply Valid_dist_nil.
              * destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
           }
        split. {
          apply NS_IF_All_True; try assumption. 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - rewrite <- b_classify_mult_coef with (p:= 1-p). 
            + apply bT_classify_decom_r with (pd0:= cofe_pd pd1 (1 - p)) (pd1:= cofe_pd pd0 (1- (1 - p))) in H3; try assumption.
              * simpl. destruct (Req_dec_T p 0). 
              ** destruct Hp as [Hp_gt0 Hp_lt1]. rewrite e in Hp_gt0. apply Rlt_irrefl in Hp_gt0. contradiction.
              ** unfold not. intros. destruct (Req_dec_T (1 - p) 0). 
                -- destruct Hpmius as [Hp_gt0 Hp_lt1]. rewrite e in Hp_gt0. apply Rlt_irrefl in Hp_gt0. contradiction.
                -- discriminate.
              * simpl. destruct Hdom. assumption.
              * simpl. destruct Hdom. assumption.
            + destruct Hpmius. assumption.
          - apply pd_decom_r_preserves_WD_win with (pd0:= cofe_pd pd1 (1 - p)) (pd1:= cofe_pd pd0 (1- (1 - p))) in H4; try assumption.
            + apply pd_mult_coef_dom_r_preserves_WD_win in H4; try assumption. 
            + apply Valid_mult_cofe; try assumption. apply Rp_1_minus_p_bounds. apply Rbound_loss. assumption.
            + apply Valid_mult_cofe; try assumption. rewrite Hprefl. apply Rbound_loss. assumption.
            + simpl. simpl in Hdom. destruct Hdom. split; assumption.
          - apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
            + apply Valid_dist_nil.
            + apply Valid_dist_nil.
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c1); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          - destruct H10. destruct H8. 
            apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}))) in H9; try assumption.
            + destruct H9. destruct H9. exists x2. split; try assumption. split; simpl. 
              * apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym. assumption.
              * apply NS_mu_implies_nil in H10; try reflexivity. rewrite H10. apply dst_equiv_refl.
            + apply Valid_dist_nil.
            + apply Valid_dist_nil.
            + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
              * apply Valid_dist_nil.
              * apply Valid_dist_nil.
              * destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
          }
        split; try assumption.
      - apply IHc2 with (pd0:= pd0) (pd1:= pd1) in H9; try assumption.
        destruct H9. destruct H. destruct H. destruct H0. destruct H1.
        exists x, x0.
        split. { apply NS_IF_All_False; try assumption. 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - rewrite <- b_classify_mult_coef with (p:= p). 
            + apply bF_classify_decom_r with (pd0:= cofe_pd pd0 p) (pd1:= cofe_pd pd1 (1-p)) in H3; try assumption.
              * simpl. destruct (Req_dec_T p 0). 
              ** destruct Hp as [Hp_gt0 Hp_lt1]. rewrite e in Hp_gt0. apply Rlt_irrefl in Hp_gt0. contradiction.
              ** unfold not. intros. discriminate.
              * simpl. destruct Hdom. assumption.
              * simpl. destruct Hdom. assumption.
            + destruct Hp. assumption.
          - apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
            + apply Valid_dist_nil.
            + apply Valid_dist_nil.
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
          - apply pd_linear_decom_r_preserve_WD_win with (p:= p) (pd0:= pd0) (pd1:= pd1) in H5; try assumption.
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c2); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          - destruct H10. destruct H8.
            apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}))) in H9; try assumption.
            + destruct H9. destruct H9. exists x2. split; try assumption. split; simpl. 
              * apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym. assumption.
              * apply NS_mu_implies_nil in H10; try reflexivity. rewrite H10. apply dst_equiv_refl.
            + apply Valid_dist_nil.
            + apply Valid_dist_nil.
            + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
              * apply Valid_dist_nil.
              * apply Valid_dist_nil.
              * destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
           }
        split. { apply NS_IF_All_False; try assumption. 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - rewrite <- b_classify_mult_coef with (p:= 1-p). 
            + apply bF_classify_decom_r with (pd0:= cofe_pd pd1 (1 - p)) (pd1:= cofe_pd pd0 (1- (1 - p))) in H3; try assumption.
              * simpl. destruct (Req_dec_T p 0). 
              ** destruct Hp as [Hp_gt0 Hp_lt1]. rewrite e in Hp_gt0. apply Rlt_irrefl in Hp_gt0. contradiction.
              ** unfold not. intros. destruct (Req_dec_T (1 - p) 0). 
                -- destruct Hpmius as [Hp_gt0 Hp_lt1]. rewrite e in Hp_gt0. apply Rlt_irrefl in Hp_gt0. contradiction. 
                -- discriminate.
              * simpl. destruct Hdom. assumption.
              * simpl. destruct Hdom. assumption.
            + destruct Hpmius. assumption.
          - apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
            + apply Valid_dist_nil.
            + apply Valid_dist_nil.
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
          - apply pd_decom_r_preserves_WD_win with (pd0:= cofe_pd pd1 (1 - p)) (pd1:= cofe_pd pd0 (1- (1 - p))) in H5; try assumption.
            + apply pd_mult_coef_dom_r_preserves_WD_win in H5; try assumption. 
            + apply Valid_mult_cofe; try assumption. apply Rp_1_minus_p_bounds. apply Rbound_loss. assumption.
            + apply Valid_mult_cofe; try assumption. rewrite Hprefl. apply Rbound_loss. assumption.
            + simpl. simpl in Hdom. destruct Hdom. split; assumption.
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd ∪ get_modvar_in_winstr c2); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          - destruct H10. destruct H8.
            apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}))) in H9; try assumption.
            + destruct H9. destruct H9. exists x2. split; try assumption. split; simpl. 
              * apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym. assumption.
              * apply NS_mu_implies_nil in H10; try reflexivity. rewrite H10. apply dst_equiv_refl.
            + apply Valid_dist_nil.
            + apply Valid_dist_nil.
            + apply pd_equiv_preserves_WD_win with (pd:= (pd_emp (dom pd))); try assumption. 
              * apply Valid_dist_nil.
              * apply Valid_dist_nil.
              * destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl.
            + destruct Hdom. split; simpl; try assumption. apply dst_equiv_refl. }
        split; try assumption.
      - specialize IHc1 with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (pd:= pd_b) (pd':= pd3); try assumption.
        assert (Hvalid_mub0: Valid_dist (get_b_in_mu b (mu pd0))). { apply dst_Valid_get_b; assumption. }
        assert (Hvalid_mub1: Valid_dist (get_b_in_mu b (mu pd1))). { apply dst_Valid_get_b; assumption. }
        assert (Hvalid_mub: Valid_dist (mu pd_b)). { apply dst_Valid_get_b; assumption. }
        assert (Hvlb': Valid_dist (p * mu (extract_b_pd b pd0) + (1 - p) * mu (extract_b_pd b pd1))%dist_state). {
          apply Valid_linear; try assumption. 
          - apply Rbound_loss. assumption.
          - apply Rbound_loss. apply Rp_lt1_minus_p_bounds with (p:= p). assumption.
          - rewrite R_plus_sub_eq_1. apply Rle_refl. }
        assert (Hvlnotb': Valid_dist (p * mu (extract_notb_pd b pd0) + (1 - p) * mu (extract_notb_pd b pd1))%dist_state). { 
          apply Valid_linear; try assumption.
          - apply dst_Valid_get_notb; assumption.
          - apply dst_Valid_get_notb; assumption.
          - apply Rbound_loss. assumption.
          - apply Rbound_loss. apply Rp_lt1_minus_p_bounds with (p:= p). assumption.
          - rewrite R_plus_sub_eq_1. apply Rle_refl. }
        assert (Hmub: (mu pd_b == p * get_b_in_mu b (mu pd0) + (1 - p) * get_b_in_mu b (mu pd1))%dist_state). { 
          repeat rewrite <- dst_get_b_coef_mult. rewrite <- get_b_assoc.
          apply Peq_implies_get_b_Peq; try assumption. }
        specialize (IHc1 Hvalid_mub0 Hvalid_mub1 Hvlb' Hvalid_mub Hmub).
        apply IHc1 in H7; try assumption.
        destruct H7 as [mu01 Htemp]. destruct Htemp as [mu11 Htemp]. 
        destruct Htemp as [HNSmu0 Htemp]. destruct Htemp as [HNSmu1 Hmu1]. 
        destruct Hmu1 as [Hmu1 Hdom1].
        specialize IHc2 with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (pd:= pd_notb) (pd':= pd4); try assumption.
        assert (Hvalid_munb0: Valid_dist (get_notb_in_mu b (mu pd0))). { apply dst_Valid_get_notb; assumption. }
        assert (Hvalid_munb1: Valid_dist (get_notb_in_mu b (mu pd1))). { apply dst_Valid_get_notb; assumption. }
        assert (Hvalid_munb: Valid_dist (mu pd_notb)). { apply dst_Valid_get_notb; assumption. }
        assert (Hmunb: (mu pd_notb == p * get_notb_in_mu b (mu pd0) + (1 - p) * get_notb_in_mu b (mu pd1))%dist_state). { 
          repeat rewrite <- dst_get_notb_coef_mult. rewrite <- get_notb_assoc.
          apply Peq_implies_get_notb_Peq; try assumption. } 
        apply IHc2 in H8; try assumption.
        destruct H8 as [mu02 Htemp]. destruct Htemp as [mu12 Htemp]. 
        destruct Htemp as [HNSmu01 Htemp]. destruct Htemp as [HNSmu11 Hmu2].
        destruct Hmu2 as [Hmu2 Hdom2].

        destruct (b_supp_classify b {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}) eqn: HB0. {
            unfold b_supp_classify in HB0. simpl in HB0. 
            destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s0, p0) :: mu0')));
            destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s0, p0) :: mu0'))); try discriminate. }
        { destruct (b_supp_classify b {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}) eqn: HB1.
          - unfold b_supp_classify in HB1. simpl in HB1. 
            destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s1, p1) :: mu1')));
            destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s1, p1) :: mu1'))); try discriminate.
          - assert (Heq0: (extract_b_pd b pd0) ≡ pd0). { apply bT_supp_implies_getb_eq; try assumption. }
            assert (Heq1: (extract_b_pd b pd1) ≡ pd1). { apply bT_supp_implies_getb_eq; try assumption. }
            assert (HWDb11: well_defined_winstr_with_pd c1 (extract_b_pd b pd1)). { 
              apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption. }
            assert (HWDb10: well_defined_winstr_with_pd c1 (extract_b_pd b pd0)). { 
              apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption. } 
            assert (HWD11: well_defined_winstr_with_pd c1 pd1). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd1) in HWDb11; try assumption. }
            assert (HWD10: well_defined_winstr_with_pd c1 pd0). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd0) in HWDb10; try assumption. }
            apply step_deterministic with (pd1:= pd0) in HNSmu0; try assumption; 
            apply step_deterministic with (pd1:= pd1) in HNSmu1; try assumption.
            destruct HNSmu0 as [mu01' Htemp0]. destruct Htemp0. 
            destruct HNSmu1 as [mu11' Htemp1]. destruct Htemp1.
              exists mu01', mu11'. 
              split. { apply NS_IF_All_True; try assumption. 
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption.
                  apply pd_equiv_preserves_WD_win with (pd:= (extract_notb_pd b pd0)) ; try assumption.
                  + apply Valid_dist_nil.
                  + simpl. apply bT_getnotb_nil in HB0. simpl in HB0. split; simpl; try apply dom_equiv_refl.
                  rewrite HB0. apply dst_equiv_refl.
                - simpl. destruct H6. 
                  + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom0) in H8. assumption.
                  + destruct H6. 
                    apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c1)%domain) .
                    * apply dom_subset_orb_dom_r. assumption.
                    * apply dom_subset_orb_compat; try apply dom_subset_refl.
                    destruct Hdom. destruct H10. assumption.
                - apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}))) in HNSmu01; try assumption. 
                  + destruct HNSmu01. destruct H8. exists x. split; try assumption. 
                    split; simpl; try assumption. 
                    * apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym. assumption.
                    * apply NS_pd_implies_nil in H10. destruct H10. rewrite H10. apply dst_equiv_refl.
                  + apply Valid_dist_nil.
                  + apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption.
                  + apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption.
                    apply pd_equiv_preserves_WD_win with (pd:= (extract_notb_pd b pd0)) ; try assumption.
                    * apply Valid_dist_nil.
                    * simpl. apply bT_getnotb_nil in HB0. simpl in HB0. split; simpl; try apply dom_equiv_refl. 
                    rewrite HB0. apply dst_equiv_refl.
                  + apply bT_getnotb_nil in HB0. simpl in HB0. split; simpl; try apply dom_equiv_refl. 
                    rewrite HB0. apply dst_equiv_refl.
                 }
              split. { apply NS_IF_All_True; try assumption.
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption.
                  apply pd_equiv_preserves_WD_win with (pd:= (extract_notb_pd b pd1)); try assumption.
                  + apply Valid_dist_nil.
                  + simpl. apply bT_getnotb_nil in HB1. simpl in HB1. split; simpl; try apply dom_equiv_refl.
                  rewrite HB1. apply dst_equiv_refl.
                - simpl. destruct H6. 
                  + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom1) in H8. assumption.
                  + destruct H6. 
                    apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c1)%domain) .
                    * apply dom_subset_orb_dom_r. assumption.
                    * apply dom_subset_orb_compat; try apply dom_subset_refl.
                    destruct Hdom. destruct H11. assumption.
                - apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}))) in HNSmu11; try assumption. 
                  + destruct HNSmu11. destruct H8. exists x. split; try assumption. 
                    split; simpl; try assumption. 
                    * apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym. assumption.
                    * apply NS_pd_implies_nil in H10. destruct H10. rewrite H10. apply dst_equiv_refl.
                  + apply Valid_dist_nil.
                  + apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption.
                  + apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption.
                    apply pd_equiv_preserves_WD_win with (pd:= (extract_notb_pd b pd1)) ; try assumption.
                    * apply Valid_dist_nil.
                    * simpl. apply bT_getnotb_nil in HB1. simpl in HB1. split; simpl; try apply dom_equiv_refl. 
                    rewrite HB1. apply dst_equiv_refl.
                  + apply bT_getnotb_nil in HB1. simpl in HB1. split; simpl; try apply dom_equiv_refl. 
                    rewrite HB1. apply dst_equiv_refl.
                }
              split; simpl; try assumption. { 
                rewrite H9.
                apply dst_equiv_trans with (mu1:= ((p * mu mu01 + (1 - p) * mu mu11) + (p * mu mu02 + (1 - p) * mu mu12))%dist_state).
                - apply dst_add_preserves_equiv; try assumption.
                - apply bT_getnotb_nil in HB0. 
                  apply NS_mu_implies_nil in HNSmu01; try assumption. rewrite HNSmu01.
                  apply bT_getnotb_nil in HB1. 
                  apply NS_mu_implies_nil in HNSmu11; try assumption. rewrite HNSmu11.
                  simpl. rewrite dst_add_0_r. destruct H. destruct H1.
                  apply dst_add_preserves_equiv; try apply dst_mult_preserves_equiv; assumption. }
              simpl. split; try assumption. 
              * apply dom_equiv_trans with (l1:= dom pd3); try assumption.  
                destruct Hdom1. apply dom_equiv_trans with (l1:= dom mu01); try assumption.
                destruct H. assumption.
              * apply dom_equiv_trans with (l1:= dom pd3); try assumption.  
                destruct Hdom1. apply dom_equiv_trans with (l1:= dom mu11); try assumption.
                destruct H1. assumption.
          - assert (Heq0: (extract_b_pd b pd0) ≡ pd0). { apply bT_supp_implies_getb_eq; try assumption. }
            assert (Heq1: (extract_notb_pd b pd1) ≡ pd1). { apply bF_supp_implies_getnotb_eq; try assumption.  }
            assert (HWDb11: well_defined_winstr_with_pd c2 (extract_notb_pd b pd1)). { 
              apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption. }
            assert (HWDb10: well_defined_winstr_with_pd c1 (extract_b_pd b pd0)). { 
              apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption. } 
            assert (HWD11: well_defined_winstr_with_pd c2 pd1). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd1) in HWDb11; try assumption. }
            assert (HWD10: well_defined_winstr_with_pd c1 pd0). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd0) in HWDb10; try assumption. }
            apply step_deterministic with (pd1:= pd0) in HNSmu0; try assumption; 
            apply step_deterministic with (pd1:= pd1) in HNSmu11; try assumption.
            destruct HNSmu0 as [mu01' Htemp0]. destruct Htemp0. 
            destruct HNSmu11 as [mu12' Htemp1]. destruct Htemp1.
            exists mu01', mu12'. 
              split. { apply NS_IF_All_True; try assumption. 
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption.
                  apply pd_equiv_preserves_WD_win with (pd:= (extract_notb_pd b pd0)) ; try assumption.
                  + apply Valid_dist_nil.
                  + simpl. apply bT_getnotb_nil in HB0. simpl in HB0. split; simpl; try apply dom_equiv_refl.
                  rewrite HB0. apply dst_equiv_refl.
                - simpl. destruct H6. 
                  + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom0) in H8. assumption.
                  + destruct H6. 
                    apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c1)%domain) .
                    * apply dom_subset_orb_dom_r. assumption.
                    * apply dom_subset_orb_compat; try apply dom_subset_refl.
                    destruct Hdom. destruct H10. assumption.
                - apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}))) in HNSmu01; try assumption. 
                  + destruct HNSmu01. destruct H8. exists x. split; try assumption. 
                    split; simpl; try assumption. 
                    * apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym. assumption.
                    * apply NS_pd_implies_nil in H10. destruct H10. rewrite H10. apply dst_equiv_refl.
                  + apply Valid_dist_nil.
                  + apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption.
                  + apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption.
                    apply pd_equiv_preserves_WD_win with (pd:= (extract_notb_pd b pd0)) ; try assumption.
                    * apply Valid_dist_nil.
                    * simpl. apply bT_getnotb_nil in HB0. simpl in HB0. split; simpl; try apply dom_equiv_refl. 
                    rewrite HB0. apply dst_equiv_refl.
                  + apply bT_getnotb_nil in HB0. simpl in HB0. split; simpl; try apply dom_equiv_refl. 
                    rewrite HB0. apply dst_equiv_refl. }
              split. { apply NS_IF_All_False; try assumption.
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption.
                  apply pd_equiv_preserves_WD_win with (pd:= (extract_b_pd b pd1)) ; try assumption.
                    * apply Valid_dist_nil.
                    * simpl. apply bF_getnotb_nil in HB1. simpl in HB1. split; simpl; try apply dom_equiv_refl. 
                    rewrite HB1. apply dst_equiv_refl.
                - simpl. destruct H6. 
                  + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom1) in H6. assumption.
                  + destruct H6. 
                    apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c2)%domain) .
                    * apply dom_subset_orb_dom_r. assumption.
                    * apply dom_subset_orb_compat; try apply dom_subset_refl.
                    destruct Hdom. destruct H11. assumption.
                - apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}))) in HNSmu1; try assumption.
                  + destruct HNSmu1. destruct H8. exists x. split; try assumption. 
                    simpl. split; simpl; try assumption. 
                    * apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym. assumption.
                    * apply NS_pd_implies_nil in H10. destruct H10. rewrite H10. apply dst_equiv_refl.
                  + apply Valid_dist_nil.
                  + apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption.
                  + apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption.
                    apply pd_equiv_preserves_WD_win with (pd:= (extract_b_pd b pd1)) ; try assumption.
                    * apply Valid_dist_nil.
                    * simpl. apply bF_getnotb_nil in HB1. simpl in HB1. split; simpl; try apply dom_equiv_refl. 
                    rewrite HB1. apply dst_equiv_refl.
                  + apply bF_getnotb_nil in HB1. simpl in HB1. split; simpl; try apply dom_equiv_refl. 
                    rewrite HB1. apply dst_equiv_refl.
                }
              split; simpl; try assumption. { 
                rewrite H9.
                apply dst_equiv_trans with (mu1:= ((p * mu mu01 + (1 - p) * mu mu11) + (p * mu mu02 + (1 - p) * mu mu12))%dist_state).
                - apply dst_add_preserves_equiv; try assumption.
                - apply bT_getnotb_nil in HB0. 
                  apply NS_mu_implies_nil in HNSmu01; try assumption. rewrite HNSmu01.
                  apply bF_getnotb_nil in HB1. 
                  apply NS_mu_implies_nil in HNSmu1; try assumption. rewrite HNSmu1.
                  simpl. rewrite dst_add_0_r. destruct H. destruct H1.
                  apply dst_add_preserves_equiv; try apply dst_mult_preserves_equiv; assumption.
                }
              simpl. split; try assumption. 
              * apply dom_equiv_trans with (l1:= dom pd3); try assumption.  
                destruct Hdom1. apply dom_equiv_trans with (l1:= dom mu01); try assumption.
                destruct H. assumption.
              * apply orbdom_after_NS in HNS. simpl in HNS.
                apply dom_equiv_trans with (l1:= (dom pd ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2))%domain); try assumption.
                apply orbdom_after_NS in H7. simpl in H7. apply dom_equiv_sym in H7.
                apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c2)%domain); try assumption.
                apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c2)%domain) .
              ** destruct H6. 
                -- apply dom_eq_orb_compat_left. rewrite orb_domain_comm. apply dom_equiv_sym.
                apply orb_domain_elim_r. destruct H6. assumption.
                -- destruct H6. apply dom_equiv_trans with (l1:= 
                    (dom pd ∪ get_modvar_in_winstr c1) ∪ (dom pd ∪ get_modvar_in_winstr c2)); try apply dom_eq_orb_dis_r.
                apply dom_equiv_sym. rewrite orb_domain_comm with (l:= (dom pd ∪ get_modvar_in_winstr c1) ). 
                apply orb_domain_elim_r. apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H8. 
                apply dom_equiv_trans with (l1:= dom pd); try assumption.
                apply dom_equiv_sym. assumption.
              ** destruct Hdom. apply dom_eq_orb_compat_right. assumption. 
          - assert (Heq0: (extract_b_pd b pd0) ≡ pd0). { apply bT_supp_implies_getb_eq; try assumption. }
            assert (Heqn0: (extract_notb_pd b pd0) ≡ pd_emp (dom pd0)). { 
              apply bT_getnotb_nil in HB0. simpl in HB0. split; simpl; try apply dom_equiv_refl.
              rewrite HB0. apply dst_equiv_refl.  }
            assert (HWDnb21: well_defined_winstr_with_pd c2 (extract_notb_pd b pd1)). { 
              apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption. }
            assert (HWDb10: well_defined_winstr_with_pd c1 (extract_b_pd b pd0)). { 
              apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption. } 
            assert (HWDb11: well_defined_winstr_with_pd c1 (extract_b_pd b pd1)). { 
               apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption. } 
            assert (HWDnb20: well_defined_winstr_with_pd c2 (extract_notb_pd b pd0)). { 
              apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption. }
            assert (HWD20: well_defined_winstr_with_pd c2
                        (pd_emp (dom {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}))). {
                apply pd_equiv_preserves_WD_win with (pd:= (extract_notb_pd b pd0)); try assumption.
                apply Valid_dist_nil. }
            assert (HWD10: well_defined_winstr_with_pd c1 pd0). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd0) in HWDb10; try assumption. }
            apply step_deterministic with (pd1:= pd0) in HNSmu0; try assumption; 
            apply step_deterministic with (pd1:= (extract_b_pd b pd1)) in HNSmu1; try assumption;
            apply step_deterministic with (pd1:= (extract_notb_pd b pd1)) in HNSmu11; try assumption; try apply pd_equiv_refl.
            destruct HNSmu0 as [mu01' Htemp0]. destruct Htemp0. 
            destruct HNSmu11 as [mu12' Htemp1]. destruct Htemp1.
            destruct HNSmu1 as [mu11' Htemp2]. destruct Htemp2.
            assert (Hdom02: (dom mu11' == dom mu12')%domain). { 
              apply orbdom_after_NS in H7. apply orbdom_after_NS in H10. 
              apply dom_equiv_trans with (l1:= (dom (extract_b_pd b pd1) ∪ get_modvar_in_winstr c1)%domain); try assumption.
              apply dom_equiv_sym.
              apply dom_equiv_trans with (l1:= (dom (extract_notb_pd b pd1) ∪ get_modvar_in_winstr c2)%domain); try assumption.
              simpl. destruct H6.
              - apply dom_eq_orb_compat_left. apply dom_equiv_sym. assumption.
              - destruct H6. destruct Hdom. simpl in H14. 
                apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c2); try assumption.
                + apply dom_eq_orb_compat_right. apply dom_equiv_sym. assumption.
                + apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c1); try assumption. 
                  * apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H11.
                    apply dom_equiv_sym in H11. apply dom_equiv_trans with (l1:= dom pd); try assumption.
                  * apply dom_eq_orb_compat_right. assumption. }
            exists mu01', (pd_add mu11' mu12' (Hdom02)). 
            split. { apply NS_IF_All_True; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - simpl. destruct H6. 
                + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom0) in H11. assumption.
                + destruct H6. 
                  apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c1)%domain) .
                  * apply dom_subset_orb_dom_r. assumption.
                  * apply dom_subset_orb_compat; try apply dom_subset_refl.
                  destruct Hdom. destruct H14. assumption.
              - apply step_deterministic with (pd1:= pd_emp (dom pd0)) in HNSmu01; try assumption; try apply Valid_dist_nil.
                destruct HNSmu01. destruct H11. exists x. split; try assumption. 
                split; simpl. 
                * apply orbdom_after_NS in H14. apply dom_equiv_sym. assumption.
                * apply NS_pd_implies_nil in H14. destruct H14. rewrite H14. apply dst_equiv_refl. }
            split. { eapply NS_IF_Mixed; try assumption.
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - simpl. destruct H6. 
                + left. assumption.
                + right. destruct H6. destruct Hdom. 
                split; apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply H10.
              - apply H7.
              - simpl. reflexivity.
              - simpl. apply dom_equiv_refl.
              - simpl. assumption. }
            split; simpl; try assumption. { 
              rewrite H9.
              apply dst_equiv_trans with (mu1:= ((p * mu mu01 + (1 - p) * mu mu11) + (p * mu mu02 + (1 - p) * mu mu12))%dist_state).
              - apply dst_add_preserves_equiv; try assumption.
              - apply bT_getnotb_nil in HB0. 
                apply NS_mu_implies_nil in HNSmu01; try assumption. rewrite HNSmu01. simpl. 
                rewrite dst_mult_plus_distr_r_eq. rewrite dst_add_assoc_eq. 
                destruct H. destruct H1. destruct H8.
                apply dst_add_preserves_equiv; try apply dst_add_preserves_equiv; try try apply dst_mult_preserves_equiv; try assumption.
              }
            simpl. split; try assumption. 
            * apply dom_equiv_trans with (l1:= dom pd3); try assumption.  
              destruct Hdom1. apply dom_equiv_trans with (l1:= dom mu01); try assumption.
              destruct H. assumption.
            * apply orbdom_after_NS in HNS. simpl in HNS.
              apply dom_equiv_trans with (l1:= (dom pd ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2))%domain); try assumption.
              apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym in H10.
              apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c1)%domain); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c1)%domain) .
              ** destruct H6. 
                -- apply dom_eq_orb_compat_left. apply dom_equiv_sym.
                apply orb_domain_elim_r. destruct H6. assumption.
                -- destruct H6. apply dom_equiv_trans with (l1:= 
                    (dom pd ∪ get_modvar_in_winstr c1) ∪ (dom pd ∪ get_modvar_in_winstr c2)); try apply dom_eq_orb_dis_r.
                apply dom_equiv_sym. 
                apply orb_domain_elim_r. apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H11. 
                apply dom_equiv_trans with (l1:= dom pd); try assumption.
                apply dom_equiv_sym. assumption.
              ** destruct Hdom. apply dom_eq_orb_compat_right. assumption. 
        }
        { destruct (b_supp_classify b {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}) eqn: HB1.
          - unfold b_supp_classify in HB1. simpl in HB1. 
            destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s1, p1) :: mu1')));
            destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s1, p1) :: mu1'))); try discriminate.
          - assert (Heq0: (extract_notb_pd b pd0) ≡ pd0). { apply bF_supp_implies_getnotb_eq; try assumption.  }
            assert (Heq1: (extract_b_pd b pd1) ≡ pd1). { apply bT_supp_implies_getb_eq; try assumption. }
            assert (Heqb0: extract_b_pd b pd0 ≡ pd_emp (dom pd0)). { 
              apply bF_getnotb_nil in HB0; try assumption. 
              split; simpl; try apply dom_equiv_refl.
              simpl in HB0. rewrite HB0. apply dst_equiv_refl.  }
            assert (Heqb1: extract_notb_pd b pd1 ≡ pd_emp (dom pd1)). { 
              apply bT_getnotb_nil in HB1; try assumption. 
              split; simpl; try apply dom_equiv_refl.
              simpl in HB1. rewrite HB1. apply dst_equiv_refl.  }
            assert (HWDb11: well_defined_winstr_with_pd c1 (extract_b_pd b pd1)). { 
              apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption. }
            assert (HWDb10: well_defined_winstr_with_pd c1 (extract_b_pd b pd0)). { 
              apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption. } 
            assert (HWD1: well_defined_winstr_with_pd c1 (pd_emp (dom0))). { 
              apply pd_equiv_preserves_WD_win with (pd:= extract_b_pd b pd0); try assumption.
              apply Valid_dist_nil. }
            assert (HWD11: well_defined_winstr_with_pd c1 pd1). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd1) in HWDb11; try assumption. }
            assert (HWDnb20: well_defined_winstr_with_pd c2 (extract_notb_pd b pd0)). {
              apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption. }
            assert (HWD2: well_defined_winstr_with_pd c2 (pd_emp (dom1))). {
              apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption.
              apply pd_equiv_preserves_WD_win with (pd:= extract_notb_pd b pd1); try assumption.
              apply Valid_dist_nil. }
            assert (HWDnb21: well_defined_winstr_with_pd c2 (extract_notb_pd b pd1)). {
              apply pd_equiv_preserves_WD_win with (pd:= pd_emp (dom pd1)); try assumption.
              - apply Valid_dist_nil.
              - apply pd_equiv_sym. assumption.  }
            assert (HWD20: well_defined_winstr_with_pd c2 pd0). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd0) in HWDnb20; try assumption. }
            apply step_deterministic with (pd1:= pd0) in HNSmu01; try assumption; 
            apply step_deterministic with (pd1:= pd1) in HNSmu1; try assumption.
            destruct HNSmu01 as [mu02' Htemp0]. destruct Htemp0. 
            destruct HNSmu1 as [mu11' Htemp1]. destruct Htemp1.
            exists mu02', mu11'. 
            split. { apply NS_IF_All_False; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - simpl. destruct H6. 
                + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom0) in H6. assumption.
                + destruct H6. 
                  apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c2)%domain) .
                  * apply dom_subset_orb_dom_r. assumption.
                  * apply dom_subset_orb_compat; try apply dom_subset_refl.
                  destruct Hdom. destruct H10. assumption.
              - apply step_deterministic with (pd1:= pd_emp (dom pd0)) in HNSmu0; try assumption; try apply Valid_dist_nil.
                destruct HNSmu0. destruct H8. exists x. split; try assumption.
                apply NS_pd_implies_nil in H10. destruct H10. apply dom_equiv_sym in H11.
                split; simpl; try assumption. rewrite H10. apply dst_equiv_refl. }
            split. { apply NS_IF_All_True; try assumption.
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - simpl. destruct H6. 
                + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom1) in H8. assumption.
                + destruct H6. 
                  apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c1)%domain) .
                  * apply dom_subset_orb_dom_r. assumption.
                  * apply dom_subset_orb_compat; try apply dom_subset_refl.
                  destruct Hdom. destruct H11. assumption.
              - apply step_deterministic with (pd1:= pd_emp (dom pd1)) in HNSmu11; try assumption; try apply Valid_dist_nil.
                destruct HNSmu11. destruct H8. exists x. split; try assumption.
                apply NS_pd_implies_nil in H10. destruct H10. apply dom_equiv_sym in H11.
                split; simpl; try assumption. rewrite H10. apply dst_equiv_refl. 
                }
            split; simpl; try assumption. { 
              rewrite H9.
              apply dst_equiv_trans with (mu1:= ((p * mu mu01 + (1 - p) * mu mu11) + (p * mu mu02 + (1 - p) * mu mu12))%dist_state).
              - apply dst_add_preserves_equiv; try assumption.
              - apply bF_getnotb_nil in HB0. 
                apply NS_mu_implies_nil in HNSmu0; try assumption. rewrite HNSmu0.
                apply bT_getnotb_nil in HB1. 
                apply NS_mu_implies_nil in HNSmu11; try assumption. rewrite HNSmu11.
                simpl. rewrite dst_add_0_r. destruct H. destruct H1.
                apply dst_equiv_trans with (mu1:= (p * mu mu02 + (1 - p) * mu mu11)%dist_state); try apply dst_add_comm.
                apply dst_add_preserves_equiv; try apply dst_mult_preserves_equiv; assumption. }
            simpl. split; try assumption. 
            * apply dom_equiv_trans with (l1:= dom pd4); try assumption.
              destruct Hdom2. destruct H. 
              apply dom_equiv_trans with (l1:= dom mu02); try assumption.
            * apply dom_equiv_trans with (l1:= dom pd3); try assumption.   
              destruct Hdom1. apply dom_equiv_trans with (l1:= dom mu11); try assumption.
              destruct H1. assumption.
          - assert (Heq0: (extract_notb_pd b pd0) ≡ pd0). { apply bF_supp_implies_getnotb_eq; try assumption.  }
            assert (Heq1: (extract_notb_pd b pd1) ≡ pd1). { apply bF_supp_implies_getnotb_eq; try assumption.  }
            assert (Heqb0: extract_b_pd b pd0 ≡ pd_emp (dom pd0)). { 
              apply bF_getnotb_nil in HB0; try assumption.
              split; simpl; try apply dom_equiv_refl.
              simpl in HB0. rewrite HB0. apply dst_equiv_refl.  }
            assert (Heqb1: extract_b_pd b pd1 ≡ pd_emp (dom pd1)). { 
              apply bF_getnotb_nil in HB1; try assumption.
              split; simpl; try apply dom_equiv_refl.
              simpl in HB1. rewrite HB1. apply dst_equiv_refl.  }
            assert (HWDb21: well_defined_winstr_with_pd c2 (extract_notb_pd b pd1)). { 
              apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption. }
            assert (HWDb20: well_defined_winstr_with_pd c2 (extract_notb_pd b pd0)). { 
              apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption. } 
            assert (HWD21: well_defined_winstr_with_pd c2 pd1). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd1) in HWDb21; try assumption. }
            assert (HWD20: well_defined_winstr_with_pd c2 pd0). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd0) in HWDb20; try assumption. }
            assert (HWDb10: well_defined_winstr_with_pd c1 (extract_b_pd b pd0)). {
              apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption. } 
            assert (HWDb11: well_defined_winstr_with_pd c1 (extract_b_pd b pd1)). {
              apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption. } 
            assert (HWD10nil: well_defined_winstr_with_pd c1 (pd_emp (dom0))). { 
              apply pd_equiv_preserves_WD_win with (pd:= extract_b_pd b pd0); try assumption.
              apply Valid_dist_nil. }
            assert (HWD11nil: well_defined_winstr_with_pd c1 (pd_emp (dom1))). { 
              apply pd_equiv_preserves_WD_win with (pd:= extract_b_pd b pd1); try assumption.
              apply Valid_dist_nil. }
            apply step_deterministic with (pd1:= pd0) in HNSmu01; try assumption; 
            apply step_deterministic with (pd1:= pd1) in HNSmu11; try assumption.
            destruct HNSmu01 as [mu02' Htemp0]. destruct Htemp0. 
            destruct HNSmu11 as [mu12' Htemp1]. destruct Htemp1.
            exists mu02', mu12'. 
              split. { apply NS_IF_All_False; try assumption. 
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - simpl. destruct H6. 
                  + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom0) in H6. assumption.
                  + destruct H6. 
                    apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c2)%domain) .
                    * apply dom_subset_orb_dom_r. assumption.
                    * apply dom_subset_orb_compat; try apply dom_subset_refl.
                    destruct Hdom. destruct H10. assumption.
                - apply step_deterministic with (pd1:= pd_emp (dom pd0)) in HNSmu0; try assumption; try apply Valid_dist_nil.
                  destruct HNSmu0. destruct H8. exists x. split; try assumption.
                  apply NS_pd_implies_nil in H10. destruct H10. apply dom_equiv_sym in H11.
                  split; simpl; try assumption. rewrite H10. apply dst_equiv_refl.  }
              split. { apply NS_IF_All_False; try assumption.
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - simpl. destruct H6. 
                  + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom1) in H6. assumption.
                  + destruct H6. 
                    apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c2)%domain) .
                    * apply dom_subset_orb_dom_r. assumption.
                    * apply dom_subset_orb_compat; try apply dom_subset_refl.
                    destruct Hdom. destruct H11. assumption.
                - apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}))) in HNSmu1; try assumption.
                  + destruct HNSmu1. destruct H8. exists x. split; try assumption. 
                    simpl. split; simpl; try assumption. 
                    * apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym. assumption.
                    * apply NS_pd_implies_nil in H10. destruct H10. rewrite H10. apply dst_equiv_refl.
                  + apply Valid_dist_nil. }
              split; simpl; try assumption. { 
                rewrite H9.
                apply dst_equiv_trans with (mu1:= ((p * mu mu01 + (1 - p) * mu mu11) + (p * mu mu02 + (1 - p) * mu mu12))%dist_state).
                - apply dst_add_preserves_equiv; try assumption.
                - apply bF_getnotb_nil in HB0. 
                  apply NS_mu_implies_nil in HNSmu0; try assumption. rewrite HNSmu0.
                  apply bF_getnotb_nil in HB1. 
                  apply NS_mu_implies_nil in HNSmu1; try assumption. rewrite HNSmu1.
                  simpl. destruct H. destruct H1.
                  apply dst_add_preserves_equiv; try apply dst_mult_preserves_equiv; assumption.
                }
              simpl. split; try assumption. 
              * apply dom_equiv_trans with (l1:= dom pd4); try assumption.  
                destruct Hdom2. apply dom_equiv_trans with (l1:= dom mu02); try assumption.
                destruct H. assumption.
              * apply orbdom_after_NS in HNS. simpl in HNS.
                apply dom_equiv_trans with (l1:= (dom pd ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2))%domain); try assumption.
                apply orbdom_after_NS in H7. simpl in H7. apply dom_equiv_sym in H7.
                apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c2)%domain); try assumption.
                apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c2)%domain) .
              ** destruct H6. 
                -- apply dom_eq_orb_compat_left. rewrite orb_domain_comm. apply dom_equiv_sym.
                apply orb_domain_elim_r. destruct H6. assumption.
                -- destruct H6. apply dom_equiv_trans with (l1:= 
                    (dom pd ∪ get_modvar_in_winstr c1) ∪ (dom pd ∪ get_modvar_in_winstr c2)); try apply dom_eq_orb_dis_r.
                apply dom_equiv_sym. rewrite orb_domain_comm with (l:= (dom pd ∪ get_modvar_in_winstr c1) ). 
                apply orb_domain_elim_r. apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H8. 
                apply dom_equiv_trans with (l1:= dom pd); try assumption.
                apply dom_equiv_sym. assumption.
              ** destruct Hdom. apply dom_eq_orb_compat_right. assumption. 
          - assert (Heq0: (extract_notb_pd b pd0) ≡ pd0). { apply bF_supp_implies_getnotb_eq; try assumption. }
            assert (Heqb0: extract_b_pd b pd0 ≡ pd_emp (dom pd0)). { 
              apply bF_getnotb_nil in HB0; try assumption. 
              split; simpl; try apply dom_equiv_refl.
              simpl in HB0. rewrite HB0. apply dst_equiv_refl.  }

            assert (HWDb21: well_defined_winstr_with_pd c2 (extract_notb_pd b pd1)). { 
              apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption. }
            assert (HWDb10: well_defined_winstr_with_pd c1 (extract_b_pd b pd0)). { 
              apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption. } 
            assert (HWD11: well_defined_winstr_with_pd c1 (extract_b_pd b pd1)). { 
               apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption. } 
            assert (HWDnb20: well_defined_winstr_with_pd c2 (extract_notb_pd b pd0)). {
              apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption. }
            assert (HWD20: well_defined_winstr_with_pd c2 pd0). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd0) in HWDnb20; try assumption. } 
            assert (HWD10nil: well_defined_winstr_with_pd c1 (pd_emp (dom0))). { 
              apply pd_equiv_preserves_WD_win with (pd:= extract_b_pd b pd0); try assumption.
              apply Valid_dist_nil. }

            apply step_deterministic with (pd1:= pd0) in HNSmu01; try assumption; 
            apply step_deterministic with (pd1:= (extract_b_pd b pd1)) in HNSmu1; try assumption;
            apply step_deterministic with (pd1:= (extract_notb_pd b pd1)) in HNSmu11; try assumption; try apply pd_equiv_refl.
            destruct HNSmu01 as [mu02' Htemp0]. destruct Htemp0. 
            destruct HNSmu11 as [mu12' Htemp1]. destruct Htemp1.
            destruct HNSmu1 as [mu11' Htemp2]. destruct Htemp2.
            assert (Hdom02: (dom mu11' == dom mu12')%domain). {
              destruct Hdom1. destruct Hdom2. 
              destruct H8. destruct H1.
              apply dom_equiv_trans with (l1:= (dom mu12)); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd4)); try assumption.
              apply dom_equiv_sym. 
              apply dom_equiv_trans with (l1:= (dom mu11)); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd3)); try assumption.
              apply dom_equiv_sym in H13.
              apply dom_equiv_trans with (l1:= (dom pd')); try assumption. }
            exists mu02', (pd_add mu11' mu12' (Hdom02)). 
              split. { apply NS_IF_All_False; try assumption. 
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - simpl. destruct H6. 
                  + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom0) in H6. assumption.
                  + destruct H6. 
                    apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c2)%domain) .
                    * apply dom_subset_orb_dom_r. assumption.
                    * apply dom_subset_orb_compat; try apply dom_subset_refl.
                    destruct Hdom. destruct H14. assumption.
                - apply step_deterministic with (pd1:= pd_emp (dom pd0)) in HNSmu0; try assumption; try apply Valid_dist_nil.
                  destruct HNSmu0. destruct H11. exists x. split; try assumption.
                  apply NS_pd_implies_nil in H14. destruct H14. apply dom_equiv_sym in H15.
                  split; simpl; try assumption. rewrite H14. apply dst_equiv_refl.  }
              split. { eapply NS_IF_Mixed; try assumption.
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - simpl. destruct H6. 
                  + left. assumption.
                  + right. destruct H6. destruct Hdom. 
                  split; apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
                - apply H10.
                - apply H7.
                - simpl. reflexivity.
                - simpl. apply dom_equiv_refl.
                - simpl. assumption. }
              split; simpl; try assumption. { 
                rewrite H9.
                apply dst_equiv_trans with (mu1:= ((p * mu mu01 + (1 - p) * mu mu11) + (p * mu mu02 + (1 - p) * mu mu12))%dist_state).
                - apply dst_add_preserves_equiv; try assumption.
                - apply bF_getnotb_nil in HB0. 
                  apply NS_mu_implies_nil in HNSmu0; try assumption. rewrite HNSmu0. simpl.
                  apply dst_equiv_trans with (mu1:= (p * mu mu02 + (1 - p) * (mu mu11 + mu mu12))%dist_state).
                  + rewrite dst_mult_plus_distr_r_eq.  
                  rewrite dst_add_assoc_eq. rewrite dst_add_assoc_eq with (mu0:= (p * mu mu02)%dist_state).
                  apply dst_add_inj_r. apply dst_add_comm.
                  + destruct H. destruct H1. destruct H8. repeat rewrite dst_mult_plus_distr_r_eq. 
                  apply dst_add_preserves_equiv; try apply dst_add_preserves_equiv; try try apply dst_mult_preserves_equiv; try assumption.
                }
              simpl. split; try assumption. 
              * apply dom_equiv_trans with (l1:= dom pd4); try assumption.  
                destruct Hdom2. apply dom_equiv_trans with (l1:= dom mu02); try assumption.
                destruct H. assumption.
              * apply orbdom_after_NS in HNS. simpl in HNS.
                apply dom_equiv_trans with (l1:= (dom pd ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2))%domain); try assumption.
                apply orbdom_after_NS in H10. simpl in H10. apply dom_equiv_sym in H10.
                apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c1)%domain); try assumption.
                apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c1)%domain) .
              ** destruct H6. 
                -- apply dom_eq_orb_compat_left. apply dom_equiv_sym.
                apply orb_domain_elim_r. destruct H6. assumption.
                -- destruct H6. apply dom_equiv_trans with (l1:= 
                    (dom pd ∪ get_modvar_in_winstr c1) ∪ (dom pd ∪ get_modvar_in_winstr c2)); try apply dom_eq_orb_dis_r.
                apply dom_equiv_sym. 
                apply orb_domain_elim_r. apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H11. 
                apply dom_equiv_trans with (l1:= dom pd); try assumption.
                apply dom_equiv_sym. assumption.
              ** destruct Hdom. apply dom_eq_orb_compat_right. assumption. 
        }
        { destruct (b_supp_classify b {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}) eqn: HB1.
          - unfold b_supp_classify in HB1. simpl in HB1. 
            destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s1, p1) :: mu1')));
            destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s1, p1) :: mu1'))); try discriminate.
          - assert (Heqb1: (extract_b_pd b pd1) ≡ pd1). { apply bT_supp_implies_getb_eq; try assumption. }
            assert (Heqnb1: (extract_notb_pd b pd1) ≡ pd_emp (dom pd1)). { 
              apply bT_getnotb_nil in HB1; try assumption.
              split; simpl; try apply dom_equiv_refl.
              simpl in HB1. rewrite HB1. apply dst_equiv_refl. }
            assert (HWDb20: well_defined_winstr_with_pd c2 (extract_notb_pd b pd0)). { 
              apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption. }
            assert (HWDb21: well_defined_winstr_with_pd c2 (extract_notb_pd b pd1)). { 
              apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption. }
            assert (HWDb10: well_defined_winstr_with_pd c1 (extract_b_pd b pd0)). { 
              apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption. } 
            assert (HWDb11: well_defined_winstr_with_pd c1 (extract_b_pd b pd1)). { 
               apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption. } 
            assert (HWD11: well_defined_winstr_with_pd c1 pd1). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd1) in HWDb11; try assumption. }
            assert (HWD21nil: well_defined_winstr_with_pd c2 (pd_emp (dom pd1))). {
              apply pd_equiv_preserves_WD_win with (pd:= (extract_notb_pd b pd1)); try assumption. 
              apply Valid_dist_nil. }
            apply step_deterministic with (pd1:= pd1) in HNSmu1; try assumption; 
            apply step_deterministic with (pd1:= (extract_b_pd b pd0)) in HNSmu0; try assumption;
            apply step_deterministic with (pd1:= (extract_notb_pd b pd0)) in HNSmu01; try assumption; try apply pd_equiv_refl.
            destruct HNSmu0 as [mu01' Htemp0]. destruct Htemp0. 
            destruct HNSmu1 as [mu11' Htemp2]. destruct Htemp2.
            destruct HNSmu01 as [mu02' Htemp1]. destruct Htemp1.
            assert (Hdom02: (dom mu01' == dom mu02')%domain). { 
              apply orbdom_after_NS in H0. apply orbdom_after_NS in H10. 
              apply dom_equiv_trans with (l1:= (dom (extract_b_pd b pd0) ∪ get_modvar_in_winstr c1)%domain); try assumption.
              apply dom_equiv_sym.
              apply dom_equiv_trans with (l1:= (dom (extract_notb_pd b pd0) ∪ get_modvar_in_winstr c2)%domain); try assumption.
              simpl. destruct H6.
              - apply dom_eq_orb_compat_left. apply dom_equiv_sym. assumption.
              - destruct H6. destruct Hdom. simpl in H14. 
                apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c2); try assumption.
                + apply dom_eq_orb_compat_right. apply dom_equiv_sym. assumption.
                + apply dom_equiv_trans with (l1:= dom pd ∪ get_modvar_in_winstr c1); try assumption. 
                  * apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H11.
                    apply dom_equiv_sym in H11. apply dom_equiv_trans with (l1:= dom pd); try assumption.
                  * apply dom_eq_orb_compat_right. assumption. }
            exists (pd_add mu01' mu02' (Hdom02)), mu11'. 
            split. { eapply NS_IF_Mixed; try assumption.
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - simpl. destruct H6. 
                  + left. assumption.
                  + right. destruct H6. destruct Hdom. 
                  split; apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
                - apply H0.
                - apply H10.
                - simpl. reflexivity.
                - simpl. apply dom_equiv_refl.
                - simpl. assumption. }
            split. { apply NS_IF_All_True; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - simpl. destruct H6. 
                + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom1) in H11. assumption.
                + destruct H6. 
                  apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c1)%domain) .
                  * apply dom_subset_orb_dom_r. assumption.
                  * apply dom_subset_orb_compat; try apply dom_subset_refl.
                  destruct Hdom. destruct H15. assumption.
              - apply step_deterministic with (pd1:= pd_emp (dom pd1)) in HNSmu11; try assumption; try apply Valid_dist_nil.
                destruct HNSmu11. destruct H11. exists x. split; try assumption.
                apply NS_pd_implies_nil in H14. destruct H14. apply dom_equiv_sym in H15.
                split; simpl; try assumption. rewrite H14. apply dst_equiv_refl.  }
            split; simpl; try assumption. { 
              rewrite H9.
              apply dst_equiv_trans with (mu1:= ((p * mu mu01 + (1 - p) * mu mu11) + (p * mu mu02 + (1 - p) * mu mu12))%dist_state).
              - apply dst_add_preserves_equiv; try assumption.
              - apply bT_getnotb_nil in HB1. 
                apply NS_mu_implies_nil in HNSmu11; try assumption. rewrite HNSmu11. rewrite dst_add_0_r. 
                rewrite dst_mult_plus_distr_r_eq. repeat rewrite <- dst_add_assoc_eq. 
                apply dst_add_preserves_equiv.
                + destruct H. try apply dst_add_preserves_equiv; try try apply dst_mult_preserves_equiv; try assumption.
                + destruct H1. destruct H8.
                  apply dst_equiv_trans with (mu1:= (p * mu mu02 + (1 - p) * mu mu11)%dist_state); try apply dst_add_comm.
                  apply dst_add_preserves_equiv; try apply dst_add_preserves_equiv; try try apply dst_mult_preserves_equiv; try assumption.
              }
            simpl. split; try assumption. 
            * apply dom_equiv_trans with (l1:= dom pd3); try assumption.  
              destruct Hdom1. apply dom_equiv_trans with (l1:= dom mu01); try assumption.
              destruct H. assumption.
            * apply orbdom_after_NS in HNS. simpl in HNS.
              apply dom_equiv_trans with (l1:= (dom pd ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2))%domain); try assumption.
              apply orbdom_after_NS in H7. simpl in H7. apply dom_equiv_sym in H7.
              apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c1)%domain); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c1)%domain) .
            ** destruct H6. 
              -- apply dom_eq_orb_compat_left. apply dom_equiv_sym.
              apply orb_domain_elim_r. destruct H6. assumption.
              -- destruct H6. apply dom_equiv_trans with (l1:= 
                  (dom pd ∪ get_modvar_in_winstr c1) ∪ (dom pd ∪ get_modvar_in_winstr c2)); try apply dom_eq_orb_dis_r.
              apply dom_equiv_sym. 
              apply orb_domain_elim_r. apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H11. 
              apply dom_equiv_trans with (l1:= dom pd); try assumption.
              apply dom_equiv_sym. assumption.
            ** destruct Hdom. apply dom_eq_orb_compat_right. assumption.
          - assert (Heqnb1: (extract_notb_pd b pd1) ≡ pd1). { apply bF_supp_implies_getnotb_eq; try assumption.  }
            assert (Heqb1: (extract_b_pd b pd1) ≡ pd_emp (dom pd1)). { apply bF_getnotb_nil in HB1. 
              split; simpl; try apply dom_equiv_refl. 
              simpl in HB1. rewrite HB1. apply dst_equiv_refl. }
            assert (HWDnb21: well_defined_winstr_with_pd c2 (extract_notb_pd b pd1)). { 
              apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption. }
            assert (HWDb10: well_defined_winstr_with_pd c1 (extract_b_pd b pd0)). { 
              apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption. } 
            assert (HWDb11: well_defined_winstr_with_pd c1 (extract_b_pd b pd1)). { 
               apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption. } 
            assert (HWD11nil: well_defined_winstr_with_pd c1 (pd_emp (dom pd1))). {
              apply pd_equiv_preserves_WD_win with (pd:= (extract_b_pd b pd1)); try assumption. apply Valid_dist_nil. }
            assert (HWDnb20: well_defined_winstr_with_pd c2 (extract_notb_pd b pd0)). {
              apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption. }
            assert (HWD11: well_defined_winstr_with_pd c2 pd1). { 
              apply pd_equiv_preserves_WD_win with (pd':= pd1) in HWDnb21; try assumption. } 
            apply step_deterministic with (pd1:= pd1) in HNSmu11; try assumption; 
            apply step_deterministic with (pd1:= (extract_b_pd b pd0)) in HNSmu0; try assumption;
            apply step_deterministic with (pd1:= (extract_notb_pd b pd0)) in HNSmu01; try assumption; try apply pd_equiv_refl.
            destruct HNSmu01 as [mu02' Htemp0]. destruct Htemp0. 
            destruct HNSmu11 as [mu12' Htemp1]. destruct Htemp1.
            destruct HNSmu0 as [mu01' Htemp2]. destruct Htemp2.
            assert (Hdom02: (dom mu01' == dom mu02')%domain). {
              destruct Hdom1. destruct Hdom2. 
              destruct H8. destruct H.
              apply dom_equiv_trans with (l1:= (dom mu02)); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd4)); try assumption.
              apply dom_equiv_sym. 
              apply dom_equiv_trans with (l1:= (dom mu01)); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd3)); try assumption.
              apply dom_equiv_sym in H13.
              apply dom_equiv_trans with (l1:= (dom pd')); try assumption. }
            exists (pd_add mu01' mu02' (Hdom02)), mu12'. 
            split. { eapply NS_IF_Mixed; try assumption.
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - simpl. destruct H6. 
                + left. assumption.
                + right. destruct H6. destruct Hdom. 
                split; apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply H10.
              - apply H0.
              - simpl. reflexivity.
              - simpl. apply dom_equiv_refl.
              - simpl. assumption. }
            split. { apply NS_IF_All_False; try assumption. 
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - simpl. destruct H6. 
                  + destruct H6. apply dom_subset_orb_dom_l with (l0:= dom1) in H6. assumption.
                  + destruct H6. 
                    apply dom_subset_trans with (l1:= (dom pd∪ get_modvar_in_winstr c2)%domain) .
                    * apply dom_subset_orb_dom_r. assumption.
                    * apply dom_subset_orb_compat; try apply dom_subset_refl.
                    destruct Hdom. destruct H15. assumption.
                - apply step_deterministic with (pd1:= (pd_emp (dom {| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}))) in HNSmu1; try assumption.
                  + destruct HNSmu1. destruct H11. exists x. split; try assumption. 
                    simpl. split; simpl; try assumption. 
                    * apply orbdom_after_NS in H14. simpl in H14. apply dom_equiv_sym. assumption.
                    * apply NS_pd_implies_nil in H14. destruct H14. rewrite H14. apply dst_equiv_refl.
                  + apply Valid_dist_nil. }
            split; simpl; try assumption. { 
                rewrite H9.
                apply dst_equiv_trans with (mu1:= ((p * mu mu01 + (1 - p) * mu mu11) + (p * mu mu02 + (1 - p) * mu mu12))%dist_state).
                - apply dst_add_preserves_equiv; try assumption.
                - apply bF_getnotb_nil in HB1. 
                  apply NS_mu_implies_nil in HNSmu1; try assumption. rewrite HNSmu1. rewrite dst_add_0_r.
                  rewrite dst_mult_plus_distr_r_eq. 
                  destruct H. destruct H1. destruct H8. rewrite dst_add_assoc_eq.
                  apply dst_add_preserves_equiv; try apply dst_add_preserves_equiv; try try apply dst_mult_preserves_equiv; try assumption.
                }
            simpl. split; try assumption. 
              * apply dom_equiv_trans with (l1:= dom pd3); try assumption.  
                destruct Hdom1. apply dom_equiv_trans with (l1:= dom mu01); try assumption.
                destruct H8. assumption.
              * apply orbdom_after_NS in HNS. simpl in HNS.
                apply dom_equiv_trans with (l1:= (dom pd ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2))%domain); try assumption.
                apply orbdom_after_NS in H7. simpl in H7. apply dom_equiv_sym in H7.
                apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c2)%domain); try assumption.
                apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c2)%domain) .
              ** destruct H6. 
                -- apply dom_eq_orb_compat_left. rewrite orb_domain_comm. apply dom_equiv_sym.
                apply orb_domain_elim_r. destruct H6. assumption.
                -- destruct H6. apply dom_equiv_trans with (l1:= 
                    (dom pd ∪ get_modvar_in_winstr c1) ∪ (dom pd ∪ get_modvar_in_winstr c2)); try apply dom_eq_orb_dis_r.
                apply dom_equiv_sym.  rewrite orb_domain_comm with (l:= (dom pd ∪ get_modvar_in_winstr c1)).
                apply orb_domain_elim_r. apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H11. 
                apply dom_equiv_trans with (l1:= dom pd); try assumption.
                apply dom_equiv_sym. assumption.
              ** destruct Hdom. apply dom_eq_orb_compat_right. assumption.
          - assert (HWDnb21: well_defined_winstr_with_pd c2 (extract_notb_pd b pd1)). { 
              apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption. }
            assert (HWDb10: well_defined_winstr_with_pd c1 (extract_b_pd b pd0)). { 
              apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption. } 
            assert (HWDb11: well_defined_winstr_with_pd c1 (extract_b_pd b pd1)). { 
               apply pd_linear_decom_l_preserve_WD_win with (pd0:= (extract_b_pd b pd0)) (pd1:= (extract_b_pd b pd1)) (p:= p) in H4; try assumption. } 
            assert (HWDnb20: well_defined_winstr_with_pd c2 (extract_notb_pd b pd0)). {
              apply pd_linear_decom_r_preserve_WD_win with (pd0:= (extract_notb_pd b pd0)) (pd1:= (extract_notb_pd b pd1)) (p:= p) in H5; try assumption. }
            apply step_deterministic with (pd1:= (extract_b_pd b pd1)) in HNSmu1; try assumption; 
            apply step_deterministic with (pd1:= (extract_notb_pd b pd1)) in HNSmu11; try assumption; 
            apply step_deterministic with (pd1:= (extract_b_pd b pd0)) in HNSmu0; try assumption;
            apply step_deterministic with (pd1:= (extract_notb_pd b pd0)) in HNSmu01; try assumption; try apply pd_equiv_refl.
            destruct HNSmu01 as [mu02' Htemp0]. destruct Htemp0. 
            destruct HNSmu11 as [mu12' Htemp1]. destruct Htemp1.
            destruct HNSmu0 as [mu01' Htemp2]. destruct Htemp2.
            destruct HNSmu1 as [mu11' Htemp2]. destruct Htemp2.
            assert (Hdom02: (dom mu01' == dom mu02')%domain). {
              destruct Hdom1. destruct Hdom2. 
              destruct H8. destruct H.
              apply dom_equiv_trans with (l1:= (dom mu02)); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd4)); try assumption.
              apply dom_equiv_sym. 
              apply dom_equiv_trans with (l1:= (dom mu01)); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd3)); try assumption.
              apply dom_equiv_sym in H13.
              apply dom_equiv_trans with (l1:= (dom pd')); try assumption. }
            assert (Hdom12: (dom mu11' == dom mu12')%domain). {
              destruct Hdom1. destruct Hdom2. 
              destruct H8. destruct H1.
              apply dom_equiv_trans with (l1:= (dom mu12)); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd4)); try assumption.
              apply dom_equiv_sym. destruct H11.
              apply dom_equiv_trans with (l1:= (dom mu11)); try assumption.
              apply dom_equiv_trans with (l1:= (dom pd3)); try assumption.
              apply dom_equiv_sym in H13.
              apply dom_equiv_trans with (l1:= (dom pd')); try assumption. }
            exists (pd_add mu01' mu02' (Hdom02)), (pd_add mu11' mu12' (Hdom12)). 
            split. { eapply NS_IF_Mixed; try assumption.
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - simpl. destruct H6. 
                + left. assumption.
                + right. destruct H6. destruct Hdom. 
                split; apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply H10.
              - apply H0.
              - simpl. reflexivity.
              - simpl. apply dom_equiv_refl.
              - simpl. assumption. }
            split. { eapply NS_IF_Mixed; try assumption.
                - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
                - simpl. destruct H6. 
                  + left. assumption.
                  + right. destruct H6. destruct Hdom. 
                  split; apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
                - apply H14.
                - apply H7.
                - simpl. reflexivity.
                - simpl. apply dom_equiv_refl.
                - simpl. assumption. }
            split; simpl; try assumption. { 
                rewrite H9.
                apply dst_equiv_trans with (mu1:= ((p * mu mu01 + (1 - p) * mu mu11) + (p * mu mu02 + (1 - p) * mu mu12))%dist_state).
                - apply dst_add_preserves_equiv; try assumption.
                - rewrite dst_add_assoc_eq. rewrite dst_mult_plus_distr_r_eq with (p:= 1-p).
                  rewrite dst_add_assoc_eq.  
                  destruct H. destruct H1. destruct H8. destruct H11.
                  apply dst_add_preserves_equiv. 
                  + rewrite <- dst_add_assoc_eq. rewrite dst_mult_plus_distr_r_eq with (p:= p).
                    rewrite <- dst_add_assoc_eq. 
                    try apply dst_add_preserves_equiv; try try apply dst_mult_preserves_equiv; try assumption.
                    apply dst_equiv_trans with (mu1:= (p * mu mu02 + (1 - p) * mu mu11)%dist_state); try apply dst_add_comm.
                    try apply dst_add_preserves_equiv; try try apply dst_mult_preserves_equiv; try assumption.
                  + try apply dst_add_preserves_equiv; try try apply dst_mult_preserves_equiv; try assumption.
                }
            simpl. split; try assumption. 
              * apply dom_equiv_trans with (l1:= dom pd3); try assumption.  
                destruct Hdom1. apply dom_equiv_trans with (l1:= dom mu01); try assumption.
                destruct H8. assumption.
              * apply orbdom_after_NS in HNS. simpl in HNS.
                apply dom_equiv_trans with (l1:= (dom pd ∪ (get_modvar_in_winstr c1 ∪ get_modvar_in_winstr c2))%domain); try assumption.
                apply orbdom_after_NS in H14. simpl in H14. apply dom_equiv_sym in H14.
                apply dom_equiv_trans with (l1:= (dom1 ∪ get_modvar_in_winstr c1)%domain); try assumption.
                apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c1)%domain) .
              ** destruct H6. 
                -- apply dom_eq_orb_compat_left. apply dom_equiv_sym.
                apply orb_domain_elim_r. destruct H6. assumption.
                -- destruct H6. apply dom_equiv_trans with (l1:= 
                    (dom pd ∪ get_modvar_in_winstr c1) ∪ (dom pd ∪ get_modvar_in_winstr c2)); try apply dom_eq_orb_dis_r.
                apply dom_equiv_sym. 
                apply orb_domain_elim_r. apply orb_domain_elim_r in H6. apply orb_domain_elim_r in H15. 
                apply dom_equiv_trans with (l1:= dom pd); try assumption.
                apply dom_equiv_sym. assumption.
              ** destruct Hdom. apply dom_eq_orb_compat_right. assumption.
        }
    }
  - assert (Hdom': (dom pd' == (orb_domain (dom pd) (get_modvar_in_winstr (While b c))))%domain) by 
      (apply orbdom_after_NS; try assumption).
    remember (While b c) as original_command eqn:Horig.
    generalize dependent pd1. generalize dependent pd0. 
    induction HNS; try inversion Horig; subst; intros.
    { 
      destruct pd0 as [dom0 mu0 HPD0]. destruct pd1 as [dom2 mu2 HPD2].
      destruct mu0 as [|(s0,p0) mu0']; destruct mu2 as [|(s2,p2) mu2'].
      - simpl in *.
        assert (Hmu_nil: mu pd = []). { apply dst_eq_nil_iff; split; try assumption. }
        exists (pd_emp (orb_domain (dom0) (get_modvar_in_winstr (While b c)))), 
                (pd_emp (orb_domain (dom2) (get_modvar_in_winstr c))).
        split. { apply (@NS_While_Nil b c {| dom := dom0; mu := []; all_partial := HPD0 |}). 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - unfold b_supp_classify. simpl. reflexivity.  }
        split. { apply (@NS_While_Nil b c {| dom := dom2; mu := []; all_partial := HPD2 |}).
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption. 
          - unfold b_supp_classify. simpl. reflexivity.  }
        simpl. split; try apply dst_equiv_refl.
        destruct Hdom. 
        apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr c) in H1. 
        apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr c) in H2. 
        split; try apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c)%domain); try assumption.
      - apply pd_Nil_mu in H0. 
        rewrite H0 in Hadd. rewrite dst_add_0_l in Hadd. simpl in Hadd.  
        assert (Hvp: Valid_dist (mu (cofe_pd {| dom := dom2; mu := (s2, p2) :: mu2'; all_partial := HPD2 |} (1-p)))). {
          apply Valid_mult_cofe; try assumption.
          apply Rp_1_minus_p_bounds. apply Rbound_loss. assumption. }
        destruct (Req_dec_T (1 - p) 0) eqn: Hp1.
        + apply Rp_lt1_minus_p_bounds with (p:= p) in Hp. destruct Hp as [Hp1l Hp1r]. 
          rewrite e in Hp1l. apply Rlt_irrefl in Hp1l. contradiction.
        + apply dst_equiv_sym in Hadd. 
          apply dst_cons_valid_contra in Hadd; try assumption; try contradiction.
          simpl in Hvp. rewrite Hp1 in Hvp. assumption. 
      - apply pd_Nil_mu in H0. 
        rewrite H0 in Hadd. rewrite dst_add_0_r in Hadd. simpl in Hadd.  
        assert (Hvp: Valid_dist (mu (cofe_pd {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |} (p)))). {
          apply Valid_mult_cofe; try assumption.
          apply Rbound_loss. assumption. }
        destruct (Req_dec_T (p) 0) eqn: Hp1.
        + destruct Hp as [Hp1l Hp1r]. 
          rewrite e in Hp1l. apply Rlt_irrefl in Hp1l. contradiction.
        + apply dst_equiv_sym in Hadd. 
          apply dst_cons_valid_contra in Hadd; try assumption; try contradiction.
          simpl in Hvp. rewrite Hp1 in Hvp. assumption.
      - apply pd_Nil_mu in H0. 
        rewrite H0 in Hadd. simpl in Hadd.  
        destruct (Req_dec_T (p) 0) eqn: Hp1.
        + destruct Hp as [Hp1l Hp1r]. 
          rewrite e in Hp1l. apply Rlt_irrefl in Hp1l. contradiction.
        + apply dst_equiv_sym in Hadd. 
          apply dst_cons_valid_contra in Hadd; try assumption; try contradiction.
          simpl in Hvl. rewrite Hp1 in Hvl. assumption.
    }
    {
      destruct pd0 as [dom0 mu0 HPD0]. destruct pd2 as [dom2 mu2 HPD2].
      destruct mu0 as [|(s0,p0) mu0']; destruct mu2 as [|(s2,p2) mu2'].
      - simpl in *. 
        assert (Hmu_nil: mu pd = []). { apply dst_eq_nil_iff; split; try assumption. }
        apply NS_mu_implies_nil in HNS1; try assumption.
        apply NS_mu_implies_nil in HNS2; try assumption.
        exists (pd_emp (orb_domain (dom0) (get_modvar_in_winstr (While b c)))), 
                (pd_emp (orb_domain (dom2) (get_modvar_in_winstr c))).
        split. { apply (@NS_While_Nil b c {| dom := dom0; mu := []; all_partial := HPD0 |}). 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - unfold b_supp_classify. simpl. reflexivity.  }
        split. { apply (@NS_While_Nil b c {| dom := dom2; mu := []; all_partial := HPD2 |}).
            - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
            - unfold b_supp_classify. simpl. reflexivity.  }
        simpl. rewrite HNS2. split; try apply dst_equiv_refl.
        destruct Hdom. 
        apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr c) in H3. 
        apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr c) in H4. 
        split; try apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c)%domain); try assumption.
      - pose (pd2_ori:= {| dom := dom2; mu := (s2, p2) :: mu2'; all_partial := HPD2 |}).
        assert (Hpmius: 0 < (1-p) < 1). { apply Rp_lt1_minus_p_bounds with (p:= p). assumption. }
        assert (Heq': pd ≡ cofe_pd pd2_ori (1-p)). {
          destruct Hdom. rewrite dst_add_0_l in Hadd. split; simpl; try assumption. }
        assert (Hb: b_supp_classify b pd2_ori = All_True). {
          rewrite dst_add_0_l in Hadd. 
          apply dst_equiv_implies_b_classify with (b:= b) in Heq'; try assumption. 
          rewrite H0 in Heq'. symmetry in Heq'. destruct Hpmius. 
          rewrite b_classify_mult_coef in Heq'; try assumption. }
        apply IHc with (pd':= pd1) in Hadd; try assumption. 
        destruct Hadd as [x Hx]. destruct Hx as [x0 Hx0]. 
        destruct Hx0 as [HNSx Hx0]. destruct Hx0 as [HNSx0 Hmu].
        destruct Hmu as [Hmu Hdomx].
        assert (Hvx: Valid_dist (mu x)). { apply Valid_forall_NS in HNSx; try assumption. }
        assert (Hvx0: Valid_dist (mu x0)). { apply Valid_forall_NS in HNSx0; try assumption. } 
        assert (HVl: Valid_dist (p * mu x + (1 - p) * mu x0)%dist_state). {
          apply Valid_linear; try assumption. 
          - apply Rbound_loss. assumption.
          - apply Rbound_loss. apply Rp_lt1_minus_p_bounds with (p:= p). assumption.
          - rewrite R_plus_sub_eq_1. apply Rle_refl.  }
        assert (Hv1: Valid_dist (mu pd1)). { apply Valid_forall_NS in HNS1; try assumption. }
        assert (Hdom1': (dom pd' == dom pd1 ∪ get_modvar_in_winstr (WHILE b DO c END))%domain). {
          apply orbdom_after_NS; try assumption. }
        assert (HWDx0c: well_defined_winstr_with_pd (WHILE b DO c END) x0). { 
          apply pd_linear_decom_l_preserve_WD_win with (c:= While b c) in Hmu; try assumption. }
        apply IHHNS2 in Hmu; try assumption.
        destruct Hmu as [x' Hx]. destruct Hx as [x0' Hx0]. 
        destruct Hx0 as [HNSx' Hx0]. destruct Hx0 as [HNSx0' Hmu].
        destruct Hmu as [Heq Hdomx'].
        exists (pd_emp (orb_domain (dom0) (get_modvar_in_winstr (While b c)))), x0'.
        split. { apply (@NS_While_Nil b c {| dom := dom0; mu := []; all_partial := HPD0 |}). 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - unfold b_supp_classify. simpl. reflexivity. }
        split. { eapply NS_While_All_True; try assumption.
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply pd_mult_coef_dom_r_preserves_WD_win with (p:= (1-p)); try assumption.
            apply pd_equiv_preserves_WD_win with (pd:= pd); try assumption.
          - apply HWDx0c.
          - apply HNSx0.
          - assumption. }
        simpl. apply NS_pd_implies_nil in HNSx. destruct HNSx. split.
        + apply NS_mu_implies_nil in HNSx'; try assumption. rewrite HNSx' in Heq. simpl in Heq. assumption.
        + destruct Hdomx'. split; try assumption. 
          apply dom_equiv_trans with (l1:= dom x'); try assumption.
          apply orbdom_after_NS in HNSx'. simpl in HNSx'.
          apply dom_equiv_trans with (l1:= (dom x ∪ get_modvar_in_winstr c)%domain); try assumption.
          apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr c) in H4. 
          apply dom_equiv_trans with (l1:= ((dom0 ∪ get_modvar_in_winstr c) ∪ get_modvar_in_winstr c)%domain); try assumption.
          apply dom_equiv_sym. apply orb_domain_elim_r. apply dom_subset_orb_snd_l_r. 
      - pose (pd0_ori:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
        assert (Hpmius: 0 < (1-p) < 1). { apply Rp_lt1_minus_p_bounds with (p:= p). assumption. }
        assert (Heq': pd ≡ cofe_pd pd0_ori p). {
          destruct Hdom. rewrite dst_add_0_r in Hadd. split; simpl; try assumption. }
        assert (Hvp: Valid_dist (mu (cofe_pd pd0_ori p))). {
          apply Valid_mult_cofe; try assumption. apply Rbound_loss. assumption. }
        assert (Hb: b_supp_classify b pd0_ori = All_True). {
          rewrite dst_add_0_r in Hadd. 
          apply dst_equiv_implies_b_classify with (b:= b) in Heq'; try assumption. 
          rewrite H0 in Heq'. symmetry in Heq'. destruct Hp. 
          rewrite b_classify_mult_coef in Heq'; try assumption. }
        apply IHc with (pd':= pd1) in Hadd; try assumption. 
        destruct Hadd as [x Hx]. destruct Hx as [x0 Hx0]. 
        destruct Hx0 as [HNSx Hx0]. destruct Hx0 as [HNSx0 Hmu].
        destruct Hmu as [Hmu Hdomx].
        assert (Hvx: Valid_dist (mu x)). { apply Valid_forall_NS in HNSx; try assumption. }
        assert (Hvx0: Valid_dist (mu x0)). { apply Valid_forall_NS in HNSx0; try assumption. } 
        assert (HVl: Valid_dist (p * mu x + (1 - p) * mu x0)%dist_state). {
          apply Valid_linear; try assumption. 
          - apply Rbound_loss. assumption.
          - apply Rbound_loss. apply Rp_lt1_minus_p_bounds with (p:= p). assumption.
          - rewrite R_plus_sub_eq_1. apply Rle_refl.  }
        assert (Hv1: Valid_dist (mu pd1)). { apply Valid_forall_NS in HNS1; try assumption. }
        assert (Hdom1': (dom pd' == dom pd1 ∪ get_modvar_in_winstr (WHILE b DO c END))%domain). {
          apply orbdom_after_NS; try assumption. }
        assert (HWDxc: well_defined_winstr_with_pd (WHILE b DO c END) x). { 
          apply pd_linear_decom_r_preserve_WD_win with (c:= While b c) in Hmu; try assumption. }
        apply IHHNS2 in Hmu; try assumption.
        destruct Hmu as [x' Hx]. destruct Hx as [x0' Hx0]. 
        destruct Hx0 as [HNSx' Hx0]. destruct Hx0 as [HNSx0' Hmu].
        destruct Hmu as [Heq Hdomx'].
        exists x', (pd_emp (orb_domain (dom2) (get_modvar_in_winstr (While b c)))).
        split. { eapply NS_While_All_True; try assumption.
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply pd_mult_coef_dom_r_preserves_WD_win with (p:= p); try assumption.
            apply pd_equiv_preserves_WD_win with (pd:= pd); try assumption.
          - apply HWDxc.
          - apply HNSx.
          - assumption. }
        split. { apply (@NS_While_Nil b c {| dom := dom2; mu := []; all_partial := HPD2 |}). 
            - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
            - unfold b_supp_classify. simpl. reflexivity. }
        simpl. apply NS_pd_implies_nil in HNSx0. destruct HNSx0. split.
        + apply NS_mu_implies_nil in HNSx0'; try assumption. rewrite HNSx0' in Heq. simpl in Heq. assumption.
        + destruct Hdomx'. split; try assumption. 
          apply dom_equiv_trans with (l1:= dom x0'); try assumption.
          apply orbdom_after_NS in HNSx0'. simpl in HNSx0'.
          apply dom_equiv_trans with (l1:= (dom x0 ∪ get_modvar_in_winstr c)%domain); try assumption.
          apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr c) in H4. 
          apply dom_equiv_trans with (l1:= ((dom2 ∪ get_modvar_in_winstr c) ∪ get_modvar_in_winstr c)%domain); try assumption.
          apply dom_equiv_sym. apply orb_domain_elim_r. apply dom_subset_orb_snd_l_r. 
      - pose (pd0_ori:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
        pose (pd2_ori:= {| dom := dom2; mu := (s2, p2) :: mu2'; all_partial := HPD2 |}).
        assert (HWD0c: well_defined_winstr_with_pd c pd0_ori). { 
          apply pd_linear_decom_r_preserve_WD_win with (c:= c) in Hadd; try assumption. }
        assert (HWD2c: well_defined_winstr_with_pd c pd2_ori). { 
          apply pd_linear_decom_l_preserve_WD_win with (c:= c) in Hadd; try assumption. }
        assert (Hpmius: 0 < (1-p) < 1). { apply Rp_lt1_minus_p_bounds with (p:= p). assumption. }
        assert (Hp1: (1- (1 - p)) = p). { field. }
        assert (Hv0p: Valid_dist (mu (cofe_pd pd0_ori p))). {
          apply Valid_mult_cofe; try assumption. apply Rbound_loss. assumption. }
        assert (Hv2p: Valid_dist (mu (cofe_pd pd2_ori (1-p)))). {
          apply Valid_mult_cofe; try assumption. apply Rbound_loss. assumption. }
        assert (Hb0: b_supp_classify b pd0_ori = All_True). { 
          destruct Hp.
          rewrite <- b_classify_mult_coef with (p:= p); try assumption. destruct Hdom.  
          apply bT_classify_decom_r with (b:= b) (pd0:= (cofe_pd pd0_ori p)) (pd1:= (cofe_pd pd2_ori (1-p))) in H0; try assumption.
          simpl. destruct (Req_dec_T p 0) eqn: Hp.
          + rewrite e in H3. apply Rlt_irrefl in H3. contradiction.
          + unfold not. intros. discriminate. }
        assert (Hb2: b_supp_classify b pd2_ori = All_True). { 
          destruct Hp. destruct Hpmius.
          rewrite <- b_classify_mult_coef with (p:= (1-p)); try assumption. destruct Hdom.  
          apply bT_classify_decom_r with (b:= b) (pd0:= cofe_pd pd2_ori (1 - p)) (pd1:= cofe_pd pd0_ori (1- (1 - p))) in H0; try assumption.
          - rewrite Hp1. apply Valid_add_comm. assumption.
          - apply dst_equiv_trans with (mu1:= (p * mu {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |} +
              (1 - p) * mu {| dom := dom2; mu := (s2, p2) :: mu2'; all_partial := HPD2 |})%dist_state); try assumption.
            rewrite Hp1. simpl. apply dst_add_comm.
          - simpl. destruct (Req_dec_T (1-p) 0) eqn: Hp.
            + rewrite e in H5. apply Rlt_irrefl in H5. contradiction.
            + unfold not. intros. discriminate. 
         }
        apply IHc with (pd':= pd1) in Hadd; try assumption. 
        destruct Hadd as [x Hx]. destruct Hx as [x0 Hx0]. 
        destruct Hx0 as [HNSx Hx0]. destruct Hx0 as [HNSx0 Hmu].
        destruct Hmu as [Hmu Hdomx].
        assert (Hvx: Valid_dist (mu x)). { apply Valid_forall_NS in HNSx; try assumption. }
        assert (Hvx0: Valid_dist (mu x0)). { apply Valid_forall_NS in HNSx0; try assumption. } 
        assert (HVl: Valid_dist (p * mu x + (1 - p) * mu x0)%dist_state). {
          apply Valid_linear; try assumption. 
          - apply Rbound_loss. assumption.
          - apply Rbound_loss. apply Rp_lt1_minus_p_bounds with (p:= p). assumption.
          - rewrite R_plus_sub_eq_1. apply Rle_refl.  }
        assert (Hv1: Valid_dist (mu pd1)). { apply Valid_forall_NS in HNS1; try assumption. }
        assert (Hdom1': (dom pd' == dom pd1 ∪ get_modvar_in_winstr (WHILE b DO c END))%domain). {
          apply orbdom_after_NS; try assumption. }
        assert (HWDxc: well_defined_winstr_with_pd (WHILE b DO c END) x). { 
          apply pd_linear_decom_r_preserve_WD_win with (c:= While b c) in Hmu; try assumption. }
        assert (HWDx0c: well_defined_winstr_with_pd (WHILE b DO c END) x0). { 
          apply pd_linear_decom_l_preserve_WD_win with (c:= While b c) in Hmu; try assumption. }
        apply IHHNS2 in Hmu; try assumption.
        destruct Hmu as [x' Hx]. destruct Hx as [x0' Hx0]. 
        destruct Hx0 as [HNSx' Hx0]. destruct Hx0 as [HNSx0' Hmu].
        destruct Hmu as [Heq Hdomx'].
        exists x', x0'.
        split. { eapply NS_While_All_True; try assumption.
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply HWDxc.
          - apply HNSx.
          - assumption. }
        split. { eapply NS_While_All_True; try assumption.
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply HWDx0c.
          - apply HNSx0.
          - assumption. }
        simpl. split; try assumption.
    }
    {
      destruct pd0 as [dom0 mu0 HPD0]. destruct pd1 as [dom2 mu2 HPD2].
      destruct mu0 as [|(s0,p0) mu0']; destruct mu2 as [|(s2,p2) mu2'].
      - simpl in *. 
        assert (Hmu_nil: mu pd = []). { apply dst_eq_nil_iff; split; try assumption. }
        unfold b_supp_classify in H0. rewrite Hmu_nil in H0. simpl. discriminate. 
      - pose (pd2_ori:= {| dom := dom2; mu := (s2, p2) :: mu2'; all_partial := HPD2 |}).
        assert (Hpmius: 0 < (1-p) < 1). { apply Rp_lt1_minus_p_bounds with (p:= p). assumption. }
        destruct Hdom. 
        assert (Heq': pd ≡ cofe_pd pd2_ori (1-p)). {
          rewrite dst_add_0_l in Hadd. split; simpl; try assumption. }
        assert (Hb: b_supp_classify b pd2_ori = All_False). {
          rewrite dst_add_0_l in Hadd. 
          apply dst_equiv_implies_b_classify with (b:= b) in Heq'; try assumption. 
          rewrite H0 in Heq'. symmetry in Heq'. destruct Hpmius. 
          rewrite b_classify_mult_coef in Heq'; try assumption. }
        exists (pd_emp (orb_domain (dom0) (get_modvar_in_winstr (While b c)))), pd2_ori.
        split. { apply (@NS_While_Nil b c {| dom := dom0; mu := []; all_partial := HPD0 |}). 
          - apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - unfold b_supp_classify. simpl. reflexivity. }
        split. { eapply NS_While_All_False; try assumption.
          - apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
        rewrite dst_add_0_l. split; try assumption. simpl. 
        split; try assumption. 
        apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr (WHILE b DO c END))%domain); try assumption.
            apply dom_eq_orb_compat_right. assumption.
      - pose (pd0_ori:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
        destruct Hdom. 
        assert (Heq': pd ≡ cofe_pd pd0_ori p). {
          rewrite dst_add_0_r in Hadd. split; simpl; try assumption. }
        assert (Hvp: Valid_dist (mu (cofe_pd pd0_ori p))). {
          apply Valid_mult_cofe; try assumption. apply Rbound_loss. assumption. }
        assert (Hb: b_supp_classify b pd0_ori = All_False). {
          rewrite dst_add_0_r in Hadd. 
          apply dst_equiv_implies_b_classify with (b:= b) in Heq'; try assumption. 
          rewrite H0 in Heq'. symmetry in Heq'. destruct Hp. 
          rewrite b_classify_mult_coef in Heq'; try assumption. }
        exists pd0_ori, (pd_emp (orb_domain (dom2) (get_modvar_in_winstr (While b c)))).
        split. { eapply NS_While_All_False; try assumption.
          - apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - simpl. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
        split. { apply (@NS_While_Nil b c {| dom := dom2; mu := []; all_partial := HPD2 |}).
            - apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
            - unfold b_supp_classify. simpl. reflexivity. }
        rewrite dst_add_0_r. rewrite dst_add_0_r in Hadd. split; try assumption. simpl. 
        split; try assumption. 
        apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr (WHILE b DO c END))%domain); try assumption.
            apply dom_eq_orb_compat_right. assumption.
      - pose (pd0_ori:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
        pose (pd2_ori:= {| dom := dom2; mu := (s2, p2) :: mu2'; all_partial := HPD2 |}).
        assert (Hpmius: 0 < (1-p) < 1). { apply Rp_lt1_minus_p_bounds with (p:= p). assumption. }
        assert (Hb0: b_supp_classify b pd0_ori = All_False). { 
          destruct Hp.
          rewrite <- b_classify_mult_coef with (p:= p); try assumption. destruct Hdom.  
          apply bF_classify_decom_r with (b:= b) (pd0:= (cofe_pd pd0_ori p)) (pd1:= (cofe_pd pd2_ori (1-p))) in H0; try assumption.
          simpl. destruct (Req_dec_T p 0) eqn: Hp.
          + rewrite e in H2. apply Rlt_irrefl in H2. contradiction.
          + unfold not. intros. discriminate. }
        assert (Hb: b_supp_classify b pd2_ori = All_False). {
          destruct Hp. destruct Hpmius.
          rewrite <- b_classify_mult_coef with (p:= (1-p)); try assumption. destruct Hdom.  
          assert (Hp1: (1- (1 - p)) = p). { field. }
          apply bF_classify_decom_r with (b:= b) (pd0:= cofe_pd pd2_ori (1 - p)) (pd1:= cofe_pd pd0_ori (1- (1 - p))) in H0; try assumption.
          - rewrite Hp1. apply Valid_add_comm. assumption.
          - apply dst_equiv_trans with (mu1:= (p * mu {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |} +
              (1 - p) * mu {| dom := dom2; mu := (s2, p2) :: mu2'; all_partial := HPD2 |})%dist_state); try assumption.
            rewrite Hp1. simpl. apply dst_add_comm.
          - simpl. destruct (Req_dec_T (1-p) 0) eqn: Hp.
            + rewrite e in H4. apply Rlt_irrefl in H4. contradiction.
            + unfold not. intros. discriminate.  }
        destruct Hdom.
        exists pd0_ori, pd2_ori.
        split. { eapply NS_While_All_False; try assumption.
          - apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. } 
        split. { eapply NS_While_All_False; try assumption.
          - apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. } 
        simpl. split; try assumption. split; try assumption.
    }
    {
      destruct pd2 as [dom0 mu0 HPD0]. destruct pd3 as [dom2 mu2 HPD2].
      destruct mu0 as [|(s0,p0) mu0']; destruct mu2 as [|(s2,p2) mu2'].
      - simpl in *. 
        assert (Hmu_nil: mu pd = []). { apply dst_eq_nil_iff; split; try assumption. }
        unfold b_supp_classify in H0. rewrite Hmu_nil in H0. simpl. discriminate. 
      - pose (pd2_ori:= {| dom := dom2; mu := (s2, p2) :: mu2'; all_partial := HPD2 |}).
        assert (Hpmius: 0 < (1-p) < 1). { apply Rp_lt1_minus_p_bounds with (p:= p). assumption. }
        assert (Heq': pd ≡ cofe_pd pd2_ori (1-p)). {
          destruct Hdom. rewrite dst_add_0_l in Hadd. split; simpl; try assumption. }
        assert (Hb_pdeq: pd_b ≡ extract_b_pd b (cofe_pd pd2_ori (1-p))). {
          apply pd_eq_preserves_get_b with (b:= b); try assumption. } 
        assert (Hnb_pdeq: pd_notb ≡ extract_notb_pd b (cofe_pd pd2_ori (1-p))). {
          apply pd_eq_preserves_get_notb with (b:= b); try assumption. } 
        assert (Hb: b_supp_classify b pd2_ori = Mixed). {
          rewrite dst_add_0_l in Hadd. 
          apply dst_equiv_implies_b_classify with (b:= b) in Heq'; try assumption. 
          rewrite H0 in Heq'. symmetry in Heq'. destruct Hpmius. 
          rewrite b_classify_mult_coef in Heq'; try assumption. }
        assert (HVb1: Valid_dist (mu (extract_b_pd b pd2_ori))). { apply dst_Valid_get_b; assumption. }
        assert (HVbp1: Valid_dist (p * mu {| dom := dom0; mu := []; all_partial := HPD0 |} + (1 - p) * mu (extract_b_pd b pd2_ori))%dist_state). {
          apply Valid_mult_cofe; try assumption. apply Rbound_loss. assumption. }
        assert (HVnb1: Valid_dist (mu (extract_notb_pd b pd2_ori))). { apply dst_Valid_get_notb; assumption. }
        assert (HVb: Valid_dist (mu pd_b)). { apply dst_Valid_get_b; assumption. }
        assert (HVnb: Valid_dist (mu pd_notb)).  { apply dst_Valid_get_notb; assumption. }
        assert (Hb_eq: mu pd_b == (p * mu {| dom := dom0; mu := []; all_partial := HPD0 |} +
                                  (1 - p) * mu (extract_b_pd b pd2_ori))%dist_state). {  
                        rewrite dst_add_0_l. rewrite dst_add_0_l in Hadd.
                        apply Peq_implies_get_b_Peq with (b:= b) in Hadd; try assumption.
                        rewrite dst_get_b_coef_mult in Hadd.
                        simpl. simpl in Hadd. assumption. }
        assert (Hnotb_eq:  mu pd_notb == (p * mu {| dom := dom0; mu := []; all_partial := HPD0 |} +
                                  (1 - p) * mu (extract_notb_pd b pd2_ori))%dist_state). {
                        rewrite dst_add_0_l. rewrite dst_add_0_l in Hadd.
                        apply Peq_implies_get_notb_Peq with (b:= b) in Hadd; try assumption.
                        rewrite dst_get_notb_coef_mult in Hadd.
                        simpl. simpl in Hadd. assumption. }
        assert (HWDb2: well_defined_winstr_with_pd c (extract_b_pd b pd2_ori)). { 
          apply pd_linear_decom_l_preserve_WD_win with (c:= c) in Hb_eq; try assumption. }
        apply IHc with (pd':= pd0) in Hb_eq; try assumption. 
        destruct Hb_eq as [x Hx]. destruct Hx as [x0 Hx0]. 
        destruct Hx0 as [HNSx Hx0]. destruct Hx0 as [HNSx0 Hmu].
        destruct Hmu as [Hmu Hdomx].
        assert (Hvx: Valid_dist (mu x)). { apply Valid_forall_NS in HNSx; try assumption. }
        assert (Hvx0: Valid_dist (mu x0)). { apply Valid_forall_NS in HNSx0; try assumption. } 
        assert (HVl: Valid_dist (p * mu x + (1 - p) * mu x0)%dist_state). {
          apply Valid_linear; try assumption. 
          - apply Rbound_loss. assumption.
          - apply Rbound_loss. apply Rp_lt1_minus_p_bounds with (p:= p). assumption.
          - rewrite R_plus_sub_eq_1. apply Rle_refl.  }
        assert (Hv1: Valid_dist (mu pd0)). { apply Valid_forall_NS in HNS1; try assumption. }
        assert (HWDx: well_defined_winstr_with_pd (WHILE b DO c END) x0). { 
          apply pd_linear_decom_l_preserve_WD_win with (c:= (While b c)) in Hmu; try assumption. }
        assert (Hdom1': (dom pd1 == dom pd0 ∪ get_modvar_in_winstr (WHILE b DO c END))%domain). { 
          apply orbdom_after_NS; try assumption. }
        apply IHHNS2 in Hmu; try assumption.
        destruct Hmu as [x' Hx]. destruct Hx as [x0' Hx0]. 
        destruct Hx0 as [HNSx' Hx0]. destruct Hx0 as [HNSx0' Hmu].
        destruct Hmu as [Heq Hdomx'].
        assert (Hdomx2: (dom x0' == dom pd2_ori)%domain). { 
          apply orbdom_after_NS in HNSx0; try assumption.
          apply orbdom_after_NS in HNSx0'; try assumption.
          apply dom_equiv_trans with (l1:= (dom x0 ∪ get_modvar_in_winstr (WHILE b DO c END))%domain); try assumption.
          apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr (WHILE b DO c END)) in HNSx0; try assumption.
          simpl in HNSx0. simpl.
          apply dom_equiv_trans with (l1:= ((dom2 ∪ get_modvar_in_winstr c) ∪ get_modvar_in_winstr c)%domain); try assumption.
          rewrite <- orb_domain_assoc. rewrite orb_domain_refl.
          apply dom_equiv_sym. apply orb_domain_elim_r.
          destruct Hdom. 
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
        exists (pd_emp (orb_domain (dom0) (get_modvar_in_winstr (While b c)))), 
                (pd_add x0' (extract_notb_pd b pd2_ori) (Hdomx2)).
        split. { apply (@NS_While_Nil b c {| dom := dom0; mu := []; all_partial := HPD0 |}). 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - unfold b_supp_classify. simpl. reflexivity. }
        split. { eapply NS_While_Mixed; try assumption.
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply HWDx.
          - simpl. destruct Hdom. 
            apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
          - apply HNSx0.
          - apply HNSx0'.
          - simpl. reflexivity.
          - simpl. apply dom_equiv_refl. }
        split. { rewrite dst_add_0_l. rewrite H4. unfold pd_add.
          simpl. rewrite dst_mult_plus_distr_r_eq. 
          apply dst_add_preserves_equiv; try assumption.
          apply NS_pd_implies_nil in HNSx. destruct HNSx. 
          apply NS_mu_implies_nil in HNSx'; try assumption. 
          rewrite HNSx' in Heq. simpl in Heq. assumption. } 
        simpl. split; try assumption.
          + simpl in Hdom'. 
            apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c)%domain); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
          + destruct Hdomx'. 
            apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
      - pose (pd0_ori:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
        assert (Hv0p: Valid_dist (mu (cofe_pd pd0_ori p))). { apply Valid_mult_cofe; try assumption. apply Rbound_loss; assumption. }
        assert (Heq': pd ≡ cofe_pd pd0_ori p). {
          destruct Hdom. rewrite dst_add_0_r in Hadd. split; simpl; try assumption. }
        assert (Hb_pdeq: pd_b ≡ extract_b_pd b (cofe_pd pd0_ori p)). {
          apply pd_eq_preserves_get_b with (b:= b); try assumption. } 
        assert (Hnb_pdeq: pd_notb ≡ extract_notb_pd b (cofe_pd pd0_ori p)). {
          apply pd_eq_preserves_get_notb with (b:= b); try assumption. } 
        assert (Hb: b_supp_classify b pd0_ori = Mixed). {
          rewrite dst_add_0_r in Hadd. 
          apply dst_equiv_implies_b_classify with (b:= b) in Heq'; try assumption. 
          rewrite H0 in Heq'. symmetry in Heq'. destruct Hp. 
          rewrite b_classify_mult_coef in Heq'; try assumption. }
        assert (HVb1: Valid_dist (mu (extract_b_pd b pd0_ori))). { apply dst_Valid_get_b; assumption. }
        assert (HVbp1:Valid_dist (p * mu (extract_b_pd b pd0_ori) + 
                                  (1 - p) * mu {| dom := dom2; mu := []; all_partial := HPD2 |})%dist_state). {
          rewrite dst_add_0_r. apply Valid_mult_cofe; try assumption. apply Rbound_loss. assumption. }
        assert (HVnb1: Valid_dist (mu (extract_notb_pd b pd0_ori))). { apply dst_Valid_get_notb; assumption. }
        assert (HVb: Valid_dist (mu pd_b)). { apply dst_Valid_get_b; assumption. }
        assert (HVnb: Valid_dist (mu pd_notb)).  { apply dst_Valid_get_notb; assumption. }
        assert (Hb_eq: mu pd_b == (p * mu (extract_b_pd b pd0_ori) +
                                  (1 - p) * mu {| dom := dom2; mu := []; all_partial := HPD2 |})%dist_state). {  
                        rewrite dst_add_0_r. rewrite dst_add_0_r in Hadd.
                        apply Peq_implies_get_b_Peq with (b:= b) in Hadd; try assumption.
                        rewrite dst_get_b_coef_mult in Hadd.
                        simpl. simpl in Hadd. assumption. }
        assert (Hnotb_eq:  mu pd_notb == (p * mu (extract_notb_pd b pd0_ori) +
                                  (1 - p) * mu {| dom := dom2; mu := []; all_partial := HPD2 |})%dist_state). {
                        rewrite dst_add_0_r. rewrite dst_add_0_r in Hadd.
                        apply Peq_implies_get_notb_Peq with (b:= b) in Hadd; try assumption.
                        rewrite dst_get_notb_coef_mult in Hadd.
                        simpl. simpl in Hadd. assumption. }
        assert (HWDb2: well_defined_winstr_with_pd c (extract_b_pd b pd0_ori)). { 
          apply pd_linear_decom_r_preserve_WD_win with (c:= c) in Hb_eq; try assumption. }
        apply IHc with (pd':= pd0) in Hb_eq; try assumption. 
        destruct Hb_eq as [x Hx]. destruct Hx as [x0 Hx0]. 
        destruct Hx0 as [HNSx Hx0]. destruct Hx0 as [HNSx0 Hmu].
        destruct Hmu as [Hmu Hdomx].
        assert (Hvx: Valid_dist (mu x)). { apply Valid_forall_NS in HNSx; try assumption. }
        assert (Hvx0: Valid_dist (mu x0)). { apply Valid_forall_NS in HNSx0; try assumption. } 
        assert (HVl: Valid_dist (p * mu x + (1 - p) * mu x0)%dist_state). {
          apply Valid_linear; try assumption. 
          - apply Rbound_loss. assumption.
          - apply Rbound_loss. apply Rp_lt1_minus_p_bounds with (p:= p). assumption.
          - rewrite R_plus_sub_eq_1. apply Rle_refl.  }
        assert (Hv1: Valid_dist (mu pd0)). { apply Valid_forall_NS in HNS1; try assumption. }
        assert (HWDx: well_defined_winstr_with_pd (WHILE b DO c END) x). { 
          apply pd_linear_decom_r_preserve_WD_win with (c:= (While b c)) in Hmu; try assumption. }
        assert (Hdom1': (dom pd1 == dom pd0 ∪ get_modvar_in_winstr (WHILE b DO c END))%domain). { 
          apply orbdom_after_NS; try assumption. }
        apply IHHNS2 in Hmu; try assumption.
        destruct Hmu as [x' Hx]. destruct Hx as [x0' Hx0]. 
        destruct Hx0 as [HNSx' Hx0]. destruct Hx0 as [HNSx0' Hmu].
        destruct Hmu as [Heq Hdomx'].
        assert (Hdomx2: (dom x' == dom pd0_ori)%domain). { 
          apply orbdom_after_NS in HNSx; try assumption.
          apply orbdom_after_NS in HNSx'; try assumption.
          apply dom_equiv_trans with (l1:= (dom x ∪ get_modvar_in_winstr (WHILE b DO c END))%domain); try assumption.
          apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr (WHILE b DO c END)) in HNSx; try assumption.
          simpl in HNSx. simpl.
          apply dom_equiv_trans with (l1:= ((dom0 ∪ get_modvar_in_winstr c) ∪ get_modvar_in_winstr c)%domain); try assumption.
          rewrite <- orb_domain_assoc. rewrite orb_domain_refl.
          apply dom_equiv_sym. apply orb_domain_elim_r.
          destruct Hdom. 
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
        exists (pd_add x' (extract_notb_pd b pd0_ori) (Hdomx2)),  
                (pd_emp (orb_domain (dom2) (get_modvar_in_winstr (While b c)))).
        split. { eapply NS_While_Mixed; try assumption.
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - apply HWDx.
          - simpl. destruct Hdom. 
            apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
          - apply HNSx.
          - apply HNSx'.
          - simpl. reflexivity.
          - simpl. apply dom_equiv_refl. }
        split. { apply (@NS_While_Nil b c {| dom := dom2; mu := []; all_partial := HPD2 |}). 
          - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
          - unfold b_supp_classify. simpl. reflexivity. }
        split. { rewrite dst_add_0_r. rewrite H4. unfold pd_add.
          simpl. rewrite dst_mult_plus_distr_r_eq. 
          rewrite dst_add_0_r in Hnotb_eq.
          apply dst_add_preserves_equiv; try assumption.
          apply NS_pd_implies_nil in HNSx0. destruct HNSx0. 
          apply NS_mu_implies_nil in HNSx0'; try assumption. 
          rewrite HNSx0' in Heq. rewrite dst_add_0_r in Heq. assumption. } 
        simpl. split; try assumption.
          + destruct Hdomx'. 
            apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption.
          + simpl in Hdom'. 
            apply dom_equiv_trans with (l1:= (dom pd ∪ get_modvar_in_winstr c)%domain); try assumption.
            apply dom_eq_orb_compat_right. destruct Hdom. assumption.
      - assert (Hpmius: 0 < (1-p) < 1). { apply Rp_lt1_minus_p_bounds with (p:= p). assumption. }
        pose (pd0_ori:= {| dom := dom0; mu := (s0, p0) :: mu0'; all_partial := HPD0 |}).
        pose (pd2_ori:= {| dom := dom2; mu := (s2, p2) :: mu2'; all_partial := HPD2 |}).
        assert (HVb: Valid_dist (mu pd_b)). { apply dst_Valid_get_b; assumption. }
        assert (HVnb: Valid_dist (mu pd_notb)).  { apply dst_Valid_get_notb; assumption. }
        assert (HVb0: Valid_dist (mu (extract_b_pd b pd0_ori))). { apply dst_Valid_get_b; assumption. }
        assert (HVb1: Valid_dist (mu (extract_b_pd b pd2_ori))). { apply dst_Valid_get_b; assumption. }
        assert (HVnb0: Valid_dist (mu (extract_notb_pd b pd0_ori))). { apply dst_Valid_get_notb; assumption. }
        assert (HVnb1: Valid_dist (mu (extract_notb_pd b pd2_ori))). { apply dst_Valid_get_notb; assumption. }
        assert (HVbp1:Valid_dist (p * mu (extract_b_pd b pd0_ori) + 
                                  (1 - p) * mu (extract_b_pd b pd2_ori))%dist_state). {
          apply Valid_linear; try assumption. 
          - apply Rbound_loss. assumption.
          - apply Rbound_loss. assumption.
          - rewrite R_plus_sub_eq_1. apply Rle_refl. }
        assert (HVnbp1:Valid_dist (p * mu (extract_notb_pd b pd0_ori) + 
                                  (1 - p) * mu (extract_notb_pd b pd2_ori))%dist_state). {
          apply Valid_linear; try assumption. 
          - apply Rbound_loss. assumption.
          - apply Rbound_loss. assumption.
          - rewrite R_plus_sub_eq_1. apply Rle_refl. }
        assert (Hmub: (mu pd_b == p * get_b_in_mu b (mu pd0_ori) + (1 - p) * get_b_in_mu b (mu pd2_ori))%dist_state). { 
          repeat rewrite <- dst_get_b_coef_mult. rewrite <- get_b_assoc.
          apply Peq_implies_get_b_Peq; try assumption. }
        assert (Hmunb: (mu pd_notb == p * get_notb_in_mu b (mu pd0_ori) + (1 - p) * get_notb_in_mu b (mu pd2_ori))%dist_state). { 
          repeat rewrite <- dst_get_notb_coef_mult. rewrite <- get_notb_assoc.
          apply Peq_implies_get_notb_Peq; try assumption. }
        specialize (IHc (extract_b_pd b pd0_ori) HVb0 (extract_b_pd b pd2_ori) HVb1 HVbp1 pd_b HVb Hmub Hdom).
        specialize (IHc pd0 HNS1). destruct IHc. destruct H6. 
        destruct H6 as [HNSx Hx]. destruct Hx as [HNSx0 Hmu0]. destruct Hmu0 as [Hmu0 Hdom0].
        assert (Hvx: Valid_dist (mu x)). { apply Valid_forall_NS in HNSx; try assumption. }
        assert (Hvx0: Valid_dist (mu x0)). { apply Valid_forall_NS in HNSx0; try assumption. } 
        assert (HVl: Valid_dist (p * mu x + (1 - p) * mu x0)%dist_state). {
          apply Valid_linear; try assumption. 
          - apply Rbound_loss. assumption.
          - apply Rbound_loss. apply Rp_lt1_minus_p_bounds with (p:= p). assumption.
          - rewrite R_plus_sub_eq_1. apply Rle_refl.  }
        assert (Hv1: Valid_dist (mu pd0)). { apply Valid_forall_NS in HNS1; try assumption. }
        assert (HWDx: well_defined_winstr_with_pd (WHILE b DO c END) x). { 
          apply pd_linear_decom_r_preserve_WD_win with (c:= (While b c)) in Hmu0; try assumption. }
        assert (HWDx0: well_defined_winstr_with_pd (WHILE b DO c END) x0). { 
          apply pd_linear_decom_l_preserve_WD_win with (c:= (While b c)) in Hmu0; try assumption. } 
        assert (HWD0b: well_defined_winstr_with_pd c (extract_b_pd b pd0_ori)). { 
              apply pd_linear_decom_r_preserve_WD_win with (c:= c)  
                (pd0:= (extract_b_pd b pd0_ori)) (pd1:= (extract_b_pd b pd2_ori)) 
                  in Hmub; try assumption. }
        assert (HWD2b: well_defined_winstr_with_pd c (extract_b_pd b pd2_ori)). { 
              apply pd_linear_decom_l_preserve_WD_win with (c:= c)  
                (pd0:= (extract_b_pd b pd0_ori)) (pd1:= (extract_b_pd b pd2_ori)) 
                  in Hmub; try assumption. }
        assert (Hdom1': (dom pd1 == dom pd0 ∪ get_modvar_in_winstr (WHILE b DO c END))%domain). { 
          apply orbdom_after_NS; try assumption. }
        apply IHHNS2 in Hmu0; try assumption.
        destruct Hmu0 as [x' Hx]. destruct Hx as [x0' Hx0]. 
        destruct Hx0 as [HNSx' Hx0]. destruct Hx0 as [HNSx0' Hmu].
        destruct Hmu as [Heq Hdomx'].
        assert (Hdomx0: (dom x' == dom pd0_ori)%domain). { 
          apply orbdom_after_NS in HNSx; try assumption.
          apply orbdom_after_NS in HNSx'; try assumption.
          apply dom_equiv_trans with (l1:= (dom x ∪ get_modvar_in_winstr (WHILE b DO c END))%domain); try assumption.
          apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr (WHILE b DO c END)) in HNSx; try assumption.
          simpl in HNSx. simpl.
          apply dom_equiv_trans with (l1:= ((dom0 ∪ get_modvar_in_winstr c) ∪ get_modvar_in_winstr c)%domain); try assumption.
          rewrite <- orb_domain_assoc. rewrite orb_domain_refl.
          apply dom_equiv_sym. apply orb_domain_elim_r.
          destruct Hdom. 
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
        assert (Hdomx2: (dom x0' == dom pd2_ori)%domain). { 
          apply orbdom_after_NS in HNSx0; try assumption.
          apply orbdom_after_NS in HNSx0'; try assumption.
          apply dom_equiv_trans with (l1:= (dom x0 ∪ get_modvar_in_winstr (WHILE b DO c END))%domain); try assumption.
          apply dom_eq_orb_compat_right with (l2:= get_modvar_in_winstr (WHILE b DO c END)) in HNSx0; try assumption.
          simpl in HNSx0. simpl.
          apply dom_equiv_trans with (l1:= ((dom2 ∪ get_modvar_in_winstr c) ∪ get_modvar_in_winstr c)%domain); try assumption.
          rewrite <- orb_domain_assoc. rewrite orb_domain_refl.
          apply dom_equiv_sym. apply orb_domain_elim_r.
          destruct Hdom. 
          apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
        
        destruct (b_supp_classify b pd0_ori) eqn: HB0. {
            unfold b_supp_classify in HB0. simpl in HB0. 
            destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s0, p0) :: mu0')));
            destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s0, p0) :: mu0'))); try discriminate. }
        {
          destruct (b_supp_classify b pd2_ori) eqn: HB2.
          - unfold b_supp_classify in HB2. simpl in HB2. 
            destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s2, p2) :: mu2')));
            destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s2, p2) :: mu2'))); try discriminate.
          - apply bMixed_implies_neq_nil in H0. destruct H0 as [Hb Hnotb]. 
            apply bT_getnotb_nil in HB0. apply bT_getnotb_nil in HB2. 
            simpl in HB0, HB2. simpl in Hmunb.  
            rewrite HB0, HB2 in Hmunb. simpl in Hmunb.
            assert (get_notb_in_mu b (mu pd) = []). { apply dst_eq_nil_iff; split; assumption. }
            rewrite H0 in Hnotb. contradiction.
          - assert (Hpd0: extract_b_pd b pd0_ori ≡ pd0_ori). { apply bT_supp_implies_getb_eq in HB0; try assumption. }
            assert (HWD0: well_defined_winstr_with_pd c pd0_ori). {
              apply pd_equiv_preserves_WD_win with (pd:= extract_b_pd b pd0_ori); try assumption. }
            apply step_deterministic with (c:= c) (pd1:= pd0_ori) in HNSx; try assumption. 
            destruct HNSx as [pd0' HNS0']. destruct HNS0' as [Heqx0 HNS0'].
            assert (Hv0': Valid_dist (mu pd0')). { apply Valid_forall_NS in HNS0'; try assumption. }
            assert (Hpd2: extract_notb_pd b pd2_ori ≡ pd2_ori). { apply bF_supp_implies_getnotb_eq in HB2; try assumption. }
            assert (HWD0': well_defined_winstr_with_pd (WHILE b DO c END) pd0'). {
              apply pd_equiv_preserves_WD_win with (pd:= x); try assumption. }
            apply step_deterministic with (c:= While b c) (pd1:= pd0') in HNSx'; try assumption. 
            destruct HNSx' as [pd1' HNS1']. destruct HNS1' as [Heqx1 HNS1'].
            exists pd1', pd2_ori. 
            split. { eapply NS_While_All_True; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWD0'.
              - apply HNS0'.
              - assumption. }
            split. { apply NS_While_All_False; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - destruct Hdom. simpl. simpl in H7. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
            split. { 
              rewrite H4.
              apply dst_add_preserves_equiv. 
              - apply bF_getnotb_nil in HB2. 
                apply NS_mu_implies_nil in HNSx0; try assumption. 
                apply NS_mu_implies_nil in HNSx0'; try assumption. simpl in Heq. 
                rewrite HNSx0' in Heq. rewrite dst_add_0_r in Heq. 
                apply dst_equiv_trans with (mu1:= (p * mu x')%dist_state); try assumption.
                destruct Heqx1.
                try apply dst_mult_preserves_equiv; try assumption.
              - apply bT_getnotb_nil in HB0. simpl in HB0. 
                simpl in Hmunb. rewrite HB0 in Hmunb. rewrite dst_add_0_l in Hmunb.
                apply dst_equiv_trans with (mu1:= ((1 - p) * (if negb (evalB_st b s2) then (s2, p2) :: get_notb_in_mu b mu2' else get_notb_in_mu b mu2'))%dist_state); try assumption.
                destruct Hpd2. try apply dst_mult_preserves_equiv; try assumption. }
            split; try assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x')%domain); try assumption.
              destruct Heqx1. assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x0')%domain); try assumption.
          - assert (Hpd0: extract_b_pd b pd0_ori ≡ pd0_ori). { apply bT_supp_implies_getb_eq in HB0; try assumption. }
            assert (HWD0: well_defined_winstr_with_pd c pd0_ori). {
              apply pd_equiv_preserves_WD_win with (pd:= extract_b_pd b pd0_ori); try assumption. }
            apply step_deterministic with (c:= c) (pd1:= pd0_ori) in HNSx; try assumption. 
            destruct HNSx as [pd0' HNS0']. destruct HNS0' as [Heqx0 HNS0'].
            assert (Hv0': Valid_dist (mu pd0')). { apply Valid_forall_NS in HNS0'; try assumption. }
            assert (HWD0': well_defined_winstr_with_pd (WHILE b DO c END) pd0'). {
              apply pd_equiv_preserves_WD_win with (pd:= x); try assumption. }
            apply step_deterministic with (c:= While b c) (pd1:= pd0') in HNSx'; try assumption. 
            destruct HNSx' as [pd1' HNS1']. destruct HNS1' as [Heqx1 HNS1'].
            exists pd1', (pd_add x0' (extract_notb_pd b pd2_ori) (Hdomx2)). 
            split. { eapply NS_While_All_True; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWD0'.
              - apply HNS0'.
              - assumption. }
            split. { eapply NS_While_Mixed; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWDx0.
              - destruct Hdom. simpl. simpl in H7. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply HNSx0.
              - apply HNSx0'.
              - simpl. reflexivity.
              - simpl. apply dom_equiv_refl. }
            split. { 
              rewrite H4. 
              apply dst_equiv_trans with (mu1:= ((p * mu x' + (1 - p) * mu x0') + mu pd_notb)%dist_state).
              - apply dst_add_inj_r. assumption.
              - rewrite <- dst_add_assoc_eq.  
                apply dst_add_preserves_equiv.
                + destruct Heqx1. try apply dst_mult_preserves_equiv; try assumption.
                + simpl. rewrite dst_mult_plus_distr_r_eq. apply dst_add_inj_l. 
                  apply bT_getnotb_nil in HB0. simpl in HB0. 
                  simpl in Hmunb. rewrite HB0 in Hmunb. rewrite dst_add_0_l in Hmunb. assumption. }
            simpl. split; try assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x')%domain); try assumption.
              destruct Heqx1. assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x0')%domain); try assumption.
              apply dom_equiv_refl.
        }
        {
          destruct (b_supp_classify b pd2_ori) eqn: HB2.
          - unfold b_supp_classify in HB2. simpl in HB2. 
            destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s2, p2) :: mu2')));
            destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s2, p2) :: mu2'))); try discriminate.
          - assert (Hpd2: extract_b_pd b pd2_ori ≡ pd2_ori). { apply bT_supp_implies_getb_eq in HB2; try assumption. }
            assert (HWD2: well_defined_winstr_with_pd c pd2_ori). {
              apply pd_equiv_preserves_WD_win with (pd:= extract_b_pd b pd2_ori); try assumption. }
            apply step_deterministic with (c:= c) (pd1:= pd2_ori) in HNSx0; try assumption. 
            destruct HNSx0 as [pd2' HNS2']. destruct HNS2' as [Heqx2 HNS2'].
            assert (Hv2': Valid_dist (mu pd2')). { apply Valid_forall_NS in HNS2'; try assumption. }
            assert (Hpd0: extract_notb_pd b pd0_ori ≡ pd0_ori). { apply bF_supp_implies_getnotb_eq in HB0; try assumption. }
            assert (HWD2': well_defined_winstr_with_pd (WHILE b DO c END) pd2'). {
              apply pd_equiv_preserves_WD_win with (pd:= x0); try assumption. }
            apply step_deterministic with (c:= While b c) (pd1:= pd2') in HNSx0'; try assumption. 
            destruct HNSx0' as [pd3' HNS3']. destruct HNS3' as [Heqx3 HNS3'].
            exists pd0_ori, pd3'. 
            split. { apply NS_While_All_False; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - destruct Hdom. simpl. simpl in H7. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
            split. { eapply NS_While_All_True; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWD2'.
              - apply HNS2'.
              - assumption. }
            split. { 
              rewrite H4. apply dst_equiv_trans with (mu1:= (mu pd_notb + mu pd1)%dist_state); try apply dst_add_comm.
              apply dst_add_preserves_equiv. 
              - apply bT_getnotb_nil in HB2. simpl in HB2. 
                simpl in Hmunb. rewrite HB2 in Hmunb. rewrite dst_add_0_r in Hmunb.
                apply dst_equiv_trans with (mu1:= (p * (if negb (evalB_st b s0) then (s0, p0) :: get_notb_in_mu b mu0' else get_notb_in_mu b mu0'))%dist_state); try assumption.
                destruct Hpd0. try apply dst_mult_preserves_equiv; try assumption.
              - apply bF_getnotb_nil in HB0. 
                apply NS_mu_implies_nil in HNSx; try assumption. 
                apply NS_mu_implies_nil in HNSx'; try assumption. simpl in Heq. 
                rewrite HNSx' in Heq. rewrite dst_add_0_l in Heq. 
                apply dst_equiv_trans with (mu1:= ((1 - p) * mu x0')%dist_state); try assumption.
                destruct Heqx3.
                try apply dst_mult_preserves_equiv; try assumption.
               }
            split; try assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x')%domain); try assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x0')%domain); try assumption.
              destruct Heqx3. assumption.
          - apply bMixed_implies_neq_nil in H0. destruct H0 as [Hb Hnotb]. 
            apply bF_getnotb_nil in HB0. apply bF_getnotb_nil in HB2. 
            simpl in HB0, HB2. simpl in Hmub.  
            rewrite HB0, HB2 in Hmub. simpl in Hmub.
            assert (get_b_in_mu b (mu pd) = []). { apply dst_eq_nil_iff; split; assumption. }
            rewrite H0 in Hb. contradiction.
          - assert (Hpd0: extract_notb_pd b pd0_ori ≡ pd0_ori). { apply bF_supp_implies_getnotb_eq in HB0; try assumption. }
            exists pd0_ori, (pd_add x0' (extract_notb_pd b pd2_ori) (Hdomx2)). 
            split. { eapply NS_While_All_False; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - simpl. destruct Hdom. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
            split. { eapply NS_While_Mixed; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWDx0.
              - destruct Hdom. simpl. simpl in H7. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply HNSx0.
              - apply HNSx0'.
              - simpl. reflexivity.
              - simpl. apply dom_equiv_refl. }
            split. { 
              rewrite H4. 
              apply dst_equiv_trans with (mu1:= ((p * mu x' + (1 - p) * mu x0') + mu pd_notb)%dist_state).
              - apply dst_add_inj_r. assumption. 
              - apply bF_getnotb_nil in HB0. 
                apply NS_mu_implies_nil in HNSx; try assumption. 
                apply NS_mu_implies_nil in HNSx'; try assumption. 
                rewrite HNSx'. rewrite dst_add_0_l.
                apply dst_equiv_trans with (mu1:= ((1 - p) * mu x0' + (p * get_notb_in_mu b (mu pd0_ori) + (1 - p) * get_notb_in_mu b (mu pd2_ori))%dist_state)%dist_state); try assumption.
                + apply dst_add_inj_l. assumption.
                + apply dst_equiv_trans with (mu1:= (p * get_notb_in_mu b (mu pd0_ori) + ((1 - p) * mu x0' + (1 - p) * get_notb_in_mu b (mu pd2_ori)))%dist_state).
                  * repeat rewrite dst_add_assoc_eq. apply dst_add_inj_r. apply dst_add_comm.
                  * apply dst_add_preserves_equiv. 
                  ** destruct Hpd0. try apply dst_mult_preserves_equiv; try assumption.
                  ** simpl. rewrite dst_mult_plus_distr_r_eq. apply dst_equiv_refl. }
            simpl. split; try assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x')%domain); try assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x0')%domain); try assumption.
              apply dom_equiv_refl.
        }
        { 
          destruct (b_supp_classify b pd2_ori) eqn: HB2.
          - unfold b_supp_classify in HB2. simpl in HB2. 
            destruct (forallb (fun s : local_st => evalB_st b s) (supp_mu ((s2, p2) :: mu2')));
            destruct (forallb (fun s : local_st => negb (evalB_st b s)) (supp_mu ((s2, p2) :: mu2'))); try discriminate.
          - assert (Hpd2: extract_b_pd b pd2_ori ≡ pd2_ori). { apply bT_supp_implies_getb_eq in HB2; try assumption. }
            assert (HWD0: well_defined_winstr_with_pd c pd2_ori). {
              apply pd_equiv_preserves_WD_win with (pd:= extract_b_pd b pd2_ori); try assumption. }
            apply step_deterministic with (c:= c) (pd1:= pd2_ori) in HNSx0; try assumption. 
            destruct HNSx0 as [pd2' HNS2']. destruct HNS2' as [Heqx2 HNS2'].
            assert (Hv2': Valid_dist (mu pd2')). { apply Valid_forall_NS in HNS2'; try assumption. }
            assert (HWD2': well_defined_winstr_with_pd (WHILE b DO c END) pd2'). {
              apply pd_equiv_preserves_WD_win with (pd:= x0); try assumption. }
            apply step_deterministic with (c:= While b c) (pd1:= pd2') in HNSx0'; try assumption. 
            destruct HNSx0' as [pd3' HNS3']. destruct HNS3' as [Heqx3 HNS3'].
            exists (pd_add x' (extract_notb_pd b pd0_ori) (Hdomx0)), pd3'. 
            split. { eapply NS_While_Mixed; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWDx.
              - destruct Hdom. simpl. simpl in H7. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply HNSx.
              - apply HNSx'.
              - simpl. reflexivity.
              - simpl. apply dom_equiv_refl. }
            split. { eapply NS_While_All_True; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWD2'.
              - apply HNS2'.
              - assumption. }
            split. { 
              rewrite H4. 
              apply dst_equiv_trans with (mu1:= ((p * mu x' + (1 - p) * mu x0') + mu pd_notb)%dist_state).
              - apply dst_add_inj_r. assumption. 
              - simpl. rewrite dst_mult_plus_distr_r_eq.
                repeat rewrite <- dst_add_assoc_eq.  
                apply dst_add_inj_l. 
                apply dst_equiv_trans with (mu1:= (get_notb_in_mu b (mu pd) + (1 - p) * mu x0')%dist_state).
                + apply dst_add_comm.
                + apply dst_add_preserves_equiv.
                  * apply bT_getnotb_nil in HB2. simpl in HB2. 
                  simpl in Hmunb. rewrite HB2 in Hmunb. rewrite dst_add_0_r in Hmunb. assumption. 
                  * destruct Heqx3. try apply dst_mult_preserves_equiv; try assumption. }
            simpl. split; try assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x')%domain); try assumption.
              apply dom_equiv_refl.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x0')%domain); try assumption.
              destruct Heqx3. assumption.
          - assert (Hpd2: extract_notb_pd b pd2_ori ≡ pd2_ori). { apply bF_supp_implies_getnotb_eq in HB2; try assumption. }
            exists (pd_add x' (extract_notb_pd b pd0_ori) (Hdomx0)), pd2_ori. 
            split. { eapply NS_While_Mixed; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWDx.
              - destruct Hdom. simpl. simpl in H7. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply HNSx.
              - apply HNSx'.
              - simpl. reflexivity.
              - simpl. apply dom_equiv_refl. }
            split. { eapply NS_While_All_False; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - simpl. destruct Hdom. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption. }
            split. { 
              rewrite H4. 
              apply dst_equiv_trans with (mu1:= ((p * mu x' + (1 - p) * mu x0') + mu pd_notb)%dist_state).
              - apply dst_add_inj_r. assumption. 
              - apply bF_getnotb_nil in HB2.
                apply NS_mu_implies_nil in HNSx0; try assumption. 
                apply NS_mu_implies_nil in HNSx0'; try assumption. 
                rewrite HNSx0'. rewrite dst_add_0_r. simpl. rewrite dst_mult_plus_distr_r_eq.
                rewrite <- dst_add_assoc_eq. apply dst_add_inj_l.
                apply dst_equiv_trans with (mu1:= ((p * get_notb_in_mu b (mu pd0_ori) + (1 - p) * get_notb_in_mu b (mu pd2_ori))%dist_state)); try assumption.
                apply dst_add_inj_l. destruct Hpd2. 
                apply dst_mult_preserves_equiv with (p:= (1-p)) in H7; try assumption. }
            simpl. split; try assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x')%domain); try assumption.
              apply dom_equiv_refl.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. apply dom_equiv_trans with (l1:= (dom x0')%domain); try assumption.
          - exists (pd_add x' (extract_notb_pd b pd0_ori) (Hdomx0)).
            exists (pd_add x0' (extract_notb_pd b pd2_ori) (Hdomx2)).
            split. { eapply NS_While_Mixed; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWDx.
              - simpl. destruct Hdom. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply HNSx.
              - apply HNSx'.
              - simpl. reflexivity.
              - apply dom_equiv_refl. }
            split. { eapply NS_While_Mixed; try assumption. 
              - destruct Hdom. apply dom_equiv_preserves_WF_bexp with (pd:= pd); try assumption.
              - apply HWDx0.
              - simpl. destruct Hdom. apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
              - apply HNSx0.
              - apply HNSx0'.
              - simpl. reflexivity.
              - apply dom_equiv_refl. }
            split. {
              rewrite H4. 
              apply dst_equiv_trans with (mu1:= ((p * mu x' + (1 - p) * mu x0') + mu pd_notb)%dist_state).
              - apply dst_add_inj_r. assumption. 
              - simpl. rewrite dst_mult_plus_distr_r_eq. repeat rewrite <- dst_add_assoc_eq. apply dst_add_inj_l. 
                rewrite dst_mult_plus_distr_r_eq. 
                apply dst_equiv_trans with (mu1:= ((1 - p) * mu x0' + 
                (p * (if negb (evalB_st b s0) then (s0, p0) :: get_notb_in_mu b mu0' else get_notb_in_mu b mu0') + 
                (1 - p) * (if negb (evalB_st b s2) then (s2, p2) :: get_notb_in_mu b mu2' else get_notb_in_mu b mu2')))%dist_state).
                + apply dst_add_inj_l. assumption.
                + repeat rewrite dst_add_assoc_eq. apply dst_add_inj_r. 
                apply dst_add_comm. }
            simpl. split; try assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption. 
              destruct Hdomx'. assumption.
            + apply dom_equiv_trans with (l1:= (dom pd1)%domain); try assumption.
              destruct Hdomx'. assumption.
        }      
    }
Qed. 



Close Scope imp_scope.

(*************************************************************)

Close Scope dstate_scope.
Close Scope Q_scope.
Close Scope domain_scope.
Close Scope supp_scope.
Open Scope state_scope.
 