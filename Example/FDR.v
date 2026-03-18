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
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import setoid_ring.Ring.
From Stdlib Require Import ZArith Ring.
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
Open Scope domain_scope.


Lemma inv_INR_S_length_range :
  forall k : nat, (0 <= (/ INR (S k)) <= 1)%R.
Proof.
  intro k.
  split.
  - apply Rlt_le. apply Rinv_0_lt_compat. 
    assert (Hpos : (0 <= INR k)%R) by apply pos_INR. 
    apply lt_0_INR. lia.
  - rewrite <- Rinv_1. apply Rinv_le_contravar; try lra.
    replace 1 with (INR 1). 
    + apply le_INR. lia.
    + simpl. reflexivity.
Qed.

Lemma inv_INR_S_length_gt_0_and_lt_1: 
  forall {A: Type} (f: A) (fs: list A),
  (0 < / INR (S (length (f :: fs))) < 1)%R. 
Proof. 
  split. 
  * apply Rinv_0_lt_compat. apply lt_0_INR. simpl. lia.
  * rewrite <- Rinv_1. apply Rinv_lt_contravar. 
    + rewrite Rmult_1_l. try apply lt_0_INR; simpl. apply Nat.lt_0_succ.
    + change 1 with (INR 1). apply lt_INR. simpl. lia. 
Qed.

(*Syntax newly added*)
Fixpoint unif_sugar (fs:list Pformula) : Pformula :=
  match fs with
  | [] => Pdeter (Dpred Bfalse)
  | [f] => f
  | f :: fs' =>
      let n := S (length fs') in (f) ⊕[ (/ INR n)%R ] (unif_sugar fs')
  end.
Fixpoint well_defined_pf_list (l : list Pformula) : Prop := 
  match l with 
  | [] => True 
  | f1 :: l' => well_defined_Pf f1 /\ well_defined_pf_list l'  
  end. 

Lemma WD_unif_sugar :
  forall fs,
    fs <> [] ->
    Forall well_defined_Pf fs ->
    well_defined_Pf (unif_sugar fs).
Proof.
  intros fs Hne Hall.
  induction fs as [|f fs IH]; [contradiction|].
  inversion Hall as [|? ? Hwd_f Hwd_fs]; subst.
  destruct fs as [|f' fs'].
  - cbn [unif_sugar]. exact Hwd_f.
  - cbn [unif_sugar]. apply WD_Pplus. 
    + apply inv_INR_S_length_range.
    + inversion Hall. subst. exact H1.
    + apply IH; auto. intuition. inversion H.
Qed.

Lemma WD_list_unif_sugar: forall fs, 
  well_defined_pf_list fs -> well_defined_Pf (unif_sugar fs).
Proof.
  intros fs. induction fs as [|f1 fs' IH]; intros.
  - simpl in *. apply WD_Pdeter. apply WD_Dpred.
  - destruct fs' as [|f2 fs']. 
    + simpl in *. intuition.
    + cbn [unif_sugar]. cbn [unif_sugar] in IH.
      inversion H; subst. apply WD_Pplus; try assumption. 
      * apply inv_INR_S_length_range.
      * apply IH. assumption.
Qed.

(********************************)

(*returns the list of rational numbers corresponding to the integers from [m] to [m + n - 1].*)
Definition rangeQ (m n:nat) : list Q :=
  map (fun k => inject_Z (Z.of_nat k)) (seq m n). 
  

Definition pf_C_uniform (C m n : nat) : list Pformula :=
  map (fun i => (C == Aco i)%formula) (rangeQ m n). (*A series of formulas for c = i*)

Definition pf_C_minus_n_uniform (C m o: nat) (n: Q) : list Pformula := 
  map (fun i => (C - Aco n == Aco i - Aco n)%formula) (rangeQ m o). (*A series of formulas for  c - n == i - n*)

Definition pf_C_eq_minus_n_uniform (C m o: nat) n: list Pformula := 
  map (fun i => (C == Aco i - Aco n)%formula) (rangeQ m o). (*A series of formulas for c == i - n*)

(* *********Assertion depend by the value of var *)
Definition Unif_Depend_by (V : nat) (mkfs : nat -> list Pformula) : PAssertion := (*PAssertions that depend on the value of V *)
  fun pd =>
    exists nv : nat, (nv > 0)%nat /\ 
      (forall st,
         is_in_supp st (supp_mu pd.(mu)) = true ->
         (evalA_st V st == inject_Z (Z.of_nat nv))%Q) /\
      well_defined_pf_list (mkfs nv) /\ 
      [[ unif_sugar (mkfs nv) ]] pd. 

Definition C_unif_depend_to_0v (C V : nat) : PAssertion := (*c is uniformly distributed on [0, v-1].*)
  Unif_Depend_by V (fun Nv => pf_C_uniform C 0 Nv).

Definition C_unif_depend_to_0v2 (C V: nat) : PAssertion := (*c is uniformly distributed on [0, v/2).*)
  fun pd =>
    exists nv : nat, (nv >= 2)%nat /\ Nat.Even nv /\
      (forall st,
         is_in_supp st (supp_mu pd.(mu)) = true ->
         (evalA_st V st == inject_Z (Z.of_nat nv))%Q) /\
      [[ unif_sugar (pf_C_uniform C 0 (nv/2)%nat)]] pd.

Definition C_unif_depend_to_nv (C V n : nat) : PAssertion :=
  fun pd =>
    exists nv : nat,
      (nv > n)%nat /\
      (forall st,
         is_in_supp st (supp_mu pd.(mu)) = true ->
         (evalA_st V st == inject_Z (Z.of_nat nv))%Q) /\
      [[ unif_sugar (pf_C_uniform C n (nv - n)) ]] pd.

Definition C_unif_depend_to_nvn1 (C V n : nat) : PAssertion := (*c is uniformly distributed on [n,v+n-1]*)
  fun pd =>
    exists nv : nat,
      (nv > 0)%nat /\
      (forall st,
         is_in_supp st (supp_mu pd.(mu)) = true ->
         (evalA_st V st == inject_Z (Z.of_nat nv))%Q) /\
      [[ unif_sugar (pf_C_uniform C n nv)]] pd.


Definition mkfs_outer (C BIT v : nat) (d_i: nat -> nat -> Q -> Pformula): list Pformula :=
  map (fun i => d_i C BIT i) (rangeQ 0 (Nat.div2 v)).
Definition Unif_Depend_and (V C BIT : nat) (d_i: nat -> nat -> Q -> Pformula) : PAssertion := (*Important*)
  fun pd =>
    exists nv : nat,
      (2 <= nv)%nat /\  Nat.Even nv /\                     
      (forall st,
         is_in_supp st (supp_mu pd.(mu)) = true ->
         (evalA_st V st == inject_Z (Z.of_nat nv))%Q) /\
      [[ unif_sugar (mkfs_outer C BIT nv d_i) ]] pd.

  (* d_i \;=\; (c=i \wedge bit=0)\;\oplus_{1/2}\; (c=i \wedge bit=1) *)
Definition c_i_and_bit (C BIT : nat) (i : Q) : Pformula :=
  ((C == Aco i)%formula ∧ (BIT == Aco 0)%formula) ⊕[ (/ 2)%R ]
  ((C == Aco i)%formula ∧ (BIT == Aco 1)%formula).
Definition mult_c_i_and_bit (C BIT : nat) (i : Q) : Pformula :=
  ((2%Q * C + BIT == 2%Q * Aco i + BIT)%formula ∧ (BIT == Aco 0)%formula) ⊕[ (/ 2)%R ]
  ((2%Q * C + BIT == 2%Q * Aco i + BIT)%formula ∧ (BIT == Aco 1)%formula).  
Definition c2_i_and_bit (C BIT : nat) (i : Q) : Pformula :=
  ((C == 2%Q * Aco i + BIT)%formula ∧ (BIT == Aco 0)%formula) ⊕[ (/ 2)%R ]
  ((C == 2%Q * Aco i + BIT)%formula ∧ (BIT == Aco 1)%formula).  

Definition C_unif_and_bit_to_0v2 (C BIT V : nat) : PAssertion := 
  Unif_Depend_and V C BIT c_i_and_bit.
Definition mult_C_unif_and_bit_to_0v2 (C BIT V : nat) : PAssertion := 
  Unif_Depend_and V C BIT mult_c_i_and_bit.
Definition C2_unif_and_bit_to_0v2 (C BIT V : nat) : PAssertion := 
  Unif_Depend_and V C BIT c2_i_and_bit.

Definition c2_i (C : nat) (i : Q) : Pformula :=
  (C == 2%Q * Aco i)%formula ⊕[ (/ 2)%R ]
  (C == 2%Q * Aco i + Aco 1%Q)%formula .

Definition mkfs_plus (C v : nat) : list Pformula :=
  map (fun i => c2_i C i) (rangeQ 0 (Nat.div2 v)).

Definition Unif_Depend_plus (V C : nat) : PAssertion :=
  fun pd =>
    exists nv : nat,
      (2 <= nv)%nat /\                         
      (forall st,
         is_in_supp st (supp_mu pd.(mu)) = true ->
         (evalA_st V st == inject_Z (Z.of_nat nv))%Q) /\
      [[ unif_sugar (mkfs_plus C nv) ]] pd.

Definition Dirac_v (V: nat): PAssertion :=
  fun pd => singleton_bool_list V ⊆ pd.(dom) /\ 
            exists a, (forall st, is_in_supp st (supp_mu pd.(mu)) = true ->
                                  (evalA_st V st == a)%Q).


Definition assert_Oplus (P1 P2 : PAssertion) : PAssertion := 
  fun pd => 
    (exists p1 p2, (0 < p1 < 1)%R /\ (0 < p2 < 1)%R /\ ((p1 + p2)%R = 1%R) /\
          (exists pd1 pd2, 
            (Valid_dist pd1.(mu) /\ Valid_dist pd2.(mu) /\ 
            (pd1.(dom) == pd.(dom))%domain /\ (pd2.(dom) == pd.(dom))%domain /\
            (P1 pd1) /\ (P2 pd2) /\ 
            (sum_probs pd1.(mu)%R = sum_probs pd.(mu)%R) /\ 
            (sum_probs pd2.(mu)%R = sum_probs pd.(mu)%R) /\
            (pd.(mu) == (p1 * pd1.(mu)) + p2 * pd2.(mu))%dist_state))) 
    \/ (P1 pd)
    \/ (P2 pd).

Definition assert_Odot (P1 P2 : PAssertion) : PAssertion := 
  fun pd => (exists pd1 pd2 (Hvar: is_domain_intersect pd1.(dom) pd2.(dom) = false),
                    Valid_dist pd1.(mu) /\ Valid_dist pd2.(mu) /\  
                    (P1 pd1) /\ (P2 pd2) /\ 
                    (let pd0:= Build_partial_dist (orb_domain pd1.(dom) pd2.(dom)) 
                                                    (pd1.(mu) ⊗ pd2.(mu)) (PD_combine_invar_mu pd1 pd2 Hvar) in
                      pd0 ⊑ pd)).

  
Inductive GoodAssertion : PAssertion -> Prop :=
  | GA_pf : forall f : Pformula, well_defined_Pf f -> GoodAssertion (pf_sem f)
  | GA_Dirac: forall V, GoodAssertion (Dirac_v V)
  | GA_unif_depend : forall V mkfs, GoodAssertion (Unif_Depend_by V mkfs)
  | GA_Unif_Depend_n: forall C V n, GoodAssertion (C_unif_depend_to_nv C V n)
  | GA_and :
      forall P Q,
        GoodAssertion P ->
        GoodAssertion Q ->
        GoodAssertion (fun pd => P pd /\ Q pd)
  | GA_oplus :
      forall P Q,
        GoodAssertion P ->
        GoodAssertion Q ->
        GoodAssertion (assert_Oplus P Q).


Lemma well_defined_pf_list_map
  (A : Type) (f : A -> Pformula) (l : list A) :
  (forall x, well_defined_Pf (f x)) ->
  well_defined_pf_list (map f l).
Proof.
  intro Hf.
  induction l as [| x l IH].
  - simpl. exact I.
  - simpl. split.
    + apply Hf.
    + exact IH.
Qed.

Lemma WD_list_C_uniform: forall C M N, 
  well_defined_pf_list (pf_C_uniform C M N).
Proof.
  intros. unfold pf_C_uniform. unfold rangeQ. 
  apply well_defined_pf_list_map.
  intros. apply WD_Pdeter. apply WD_Dpred. 
Qed.

(*******************************************************************************)
Lemma assert_oplus_sym: forall P1 P2 pd, 
  assert_Oplus P1 P2 pd -> assert_Oplus P2 P1 pd.
Proof. 
  intros. unfold assert_Oplus. destruct H as [H1 | H].
  - destruct H1 as (p1 & p2 & H1p1 & H1p2 & H1p3 & pd1 & pd2 & H). 
    left. exists p2, p1. intuition. 
    + rewrite <- H1p3. apply Rplus_comm.
    + exists pd2, pd1. intuition. 
      apply dst_equiv_trans with (mu1:= (p1 * mu pd1 + p2 * mu pd2)%dist_state); try assumption.
      apply dst_add_comm.
  - destruct H as [H2 | H3]. 
    + right. intuition.
    + right. intuition.
Qed.

Lemma assert_oplus_and_comm: forall P1 P2 P3 P4 pd, 
  assert_Oplus (P1/\P2) (P3/\P4) pd -> assert_Oplus (P2/\P1) (P4/\P3) pd.
Proof. 
  intros. unfold assert_Oplus. destruct H as [H1 | H].
  - destruct H1 as (p1 & p2 & H1p1 & H1p2 & H1p3 & pd1 & pd2 & H). 
    left. exists p1, p2. intuition. 
    exists pd1, pd2. intuition. 
  - destruct H as [H2 | H3]. 
    + right. intuition.
    + right. intuition.
Qed.


Lemma Forallb_neg_inver: forall b s p mu',
  forallb (fun s0 : partial_st => negb (evalB_st b s0)) (supp_mu ((s, p) :: mu')) = true -> 
  forallb (fun s0 : partial_st => evalB_st b s0) (supp_mu ((s, p) :: mu')) = false.
Proof.
  intros. unfold supp_mu in *. simpl in *. rewrite insert_st_pair_fst_eq_insert_st in *.
  rewrite supp_insert_evalB. rewrite supp_insert_negbevalB in H. 
  apply andb_true_iff in H. destruct H as [Hhead Htail].
  apply andb_false_iff. apply negb_true_iff in Hhead. 
  left. assumption.
Qed.

Lemma dst_mult_eq_nil: forall pd p, 
  (0 < p)%R -> 
  (p * (mu pd))%dist_state = [] -> mu pd = [].
Proof. 
  intros pd p Hp H. destruct (mu pd) as [| (s, p') mu']; simpl in *.
  - reflexivity.
  - exfalso. destruct (Req_dec_T p 0) eqn: Hcontra.
    + rewrite e in Hp. lra.
    + inversion H.
Qed.

Lemma AssertOplus_under_All_true:  (*Important*)
  forall b pd phi0 phi1, 
  Valid_dist (mu pd) -> 
  b_supp_classify b pd = All_True ->
  assert_Oplus (phi0 /\ [[Pdeter (Dpred b)]]) (phi1 /\ [[~ b]]) pd ->
  phi0 pd.
Proof. 
  intros b pd phi0 phi1 Hvalid Hb H. destruct H as [Hcase1 | H].
  - destruct Hcase1 as (p1 & p2 & Hp1 & Hp2 & Hp_sum & pd1 & pd2 & Hrest). 
    destruct Hrest as (Hv1 & Hv2 & Hdom1 & Hdom2 & Hsem1 & Hsem2 & Hsum1 & Hsum2 & Hmu).
    destruct Hsem1 as [Hsem1 Hb1]. destruct Hsem2 as [Hsem2 Hnb2]. 
    pose (pd1':= cofe_pd pd1 p1). pose (pd2':= cofe_pd pd2 p2).
    apply bT_classify_decom_r with ( pd0:= pd2') (pd1:= pd1') in Hb; try assumption.
    + unfold pd2' in Hb. rewrite b_classify_mult_coef in Hb; try lra.
      apply bF_sem_iff in Hnb2. destruct Hnb2. destruct H0. 
      * rewrite Hb in H0. inversion H0.
      * rewrite Hb in H0. inversion H0.
    + simpl. apply Valid_linear; try assumption; try lra.
    + simpl. apply dst_equiv_trans with (mu1:= (p1 * mu pd1 + p2 * mu pd2)%dist_state); try assumption.
      apply dst_add_comm.
    + simpl. unfold not. intros Hcontra. apply dst_mult_eq_nil in Hcontra; try lra.
      rewrite Hcontra in Hsum2. simpl in Hsum2. symmetry in Hsum2. 
      assert (Hmu_pd: mu pd = []); try assumption. { apply sum_probs0_implies_nil; try assumption. }
      unfold b_supp_classify in Hb. rewrite Hmu_pd in Hb. simpl in Hb. inversion Hb.
    + simpl. apply dom_equiv_sym. assumption.
    + simpl. apply dom_equiv_sym. assumption.
  - destruct H as [Hcase2 | Hcase3].
    + destruct Hcase2. try assumption. 
    + destruct Hcase3. apply bT_sem_iff in H0. destruct H0. 
      destruct H1.
      * destruct pd as [dom mu HPD]. 
        destruct mu as [| (s, p) mu']; simpl in *. 
        ** unfold b_supp_classify in Hb. simpl in *. inversion Hb.
        ** unfold b_supp_classify in H1. simpl in *. 
        destruct (forallb (fun s : partial_st => negb (evalB_st b s)) (supp_mu ((s, p) :: mu'))); 
        inversion H1. 
        destruct (forallb (fun s : partial_st => negb (negb (evalB_st b s))) (supp_mu ((s, p) :: mu'))); inversion H1.
      * destruct pd as [dom mu HPD]. 
        destruct mu as [| (s, p) mu']; simpl in *.
        ** unfold b_supp_classify in Hb. simpl in *. inversion Hb.
        ** unfold b_supp_classify in H1, Hb. simpl in *.
        destruct (forallb (fun s : partial_st => negb (evalB_st b s)) (supp_mu ((s, p) :: mu'))) eqn: Hn.
        -- assert (Hcontra: forallb (fun s : partial_st => evalB_st b s) (supp_mu ((s, p) :: mu')) = false). { 
           apply Forallb_neg_inver; try assumption. }
        rewrite Hcontra in Hb. inversion Hb.
        -- destruct (forallb (fun s : partial_st => negb (negb (evalB_st b s))) (supp_mu ((s, p) :: mu'))); try inversion H1.
Qed.

Lemma AssertOplus_under_All_false:   (*Important*)
  forall b pd phi0 phi1, 
  Valid_dist (mu pd) -> 
  b_supp_classify b pd = All_False ->
  assert_Oplus (phi0 /\ [[Pdeter (Dpred b)]]) (phi1 /\ [[~ b]]) pd ->
  phi1 pd.
Proof. 
  intros b pd phi0 phi1 Hvalid Hb H. destruct H as [Hcase1 | H].
  - destruct Hcase1 as (p1 & p2 & Hp1 & Hp2 & Hp_sum & pd1 & pd2 & Hrest). 
    destruct Hrest as (Hv1 & Hv2 & Hdom1 & Hdom2 & Hsem1 & Hsem2 & Hsum1 & Hsum2 & Hmu).
    destruct Hsem1 as [Hsem1 Hb1]. destruct Hsem2 as [Hsem2 Hnb2]. 
    pose (pd1':= cofe_pd pd1 p1). pose (pd2':= cofe_pd pd2 p2).
    apply bF_classify_decom_r with ( pd0:= pd1') (pd1:= pd2') in Hb; try assumption.
    + unfold pd1' in Hb. rewrite b_classify_mult_coef in Hb; try lra. 
      apply bT_sem_iff in Hb1. destruct Hb1. destruct H0. 
      * rewrite Hb in H0. inversion H0.
      * rewrite Hb in H0. inversion H0.
    + simpl. apply Valid_linear; try assumption; try lra.
    + simpl. unfold not. intros Hcontra. apply dst_mult_eq_nil in Hcontra; try lra.
      rewrite Hcontra in Hsum1. simpl in Hsum1. symmetry in Hsum1. 
      assert (Hmu_pd: mu pd = []); try assumption. { apply sum_probs0_implies_nil; try assumption. }
      unfold b_supp_classify in Hb. rewrite Hmu_pd in Hb. simpl in Hb. inversion Hb.
    + simpl. apply dom_equiv_sym. assumption.
    + simpl. apply dom_equiv_sym. assumption.
  - destruct H as [Hcase2 | Hcase3].
    + destruct Hcase2. apply bT_sem_iff in H0. destruct H0. 
      destruct H1.
      * rewrite H1 in Hb. inversion Hb.
      * rewrite H1 in Hb. inversion Hb.
    + destruct Hcase3. apply bF_sem_iff in H0. destruct H0. destruct H1.
      * rewrite H1 in Hb. inversion Hb.
      * assumption.
Qed.

Lemma pd_equiv_preserves_Dirac: forall V pd0 pd1,
  Valid_dist (mu pd0) -> Valid_dist (mu pd1) ->
  pd1 ≡ pd0 -> Dirac_v V pd0 -> 
  Dirac_v V pd1.
Proof.
  intros V pd0 pd1 HV0 HV1 Heq H. 
  destruct H as [Hdom (q & H)]. destruct Heq as [Hdomeq Hmueq]. 
  split.
  - apply dom_equiv_sym in Hdomeq.
    apply dom_subset_eq_compat_left with (X:= dom pd0); try assumption.
  - exists q. intros. apply H. 
    apply in_supp_iff_posi_prob in H0; intuition. destruct H0 as [p Hprob].
    apply in_supp_iff_posi_prob; intuition. exists p; intuition.
    specialize (Hmueq st). rewrite <- Hmueq. intuition.
Qed.

Lemma pd_decom_Dirac_right: forall V pd0 pd1 pd, 
  Valid_dist (mu pd0 + mu pd1)%dist_state ->
  Valid_dist (mu pd) ->
  (dom pd == dom pd1)% domain ->
  (mu pd == mu pd0 + mu pd1)%dist_state ->
  Dirac_v V pd ->
  Dirac_v V pd1.
Proof. 
  intros V pd0 pd1 pd HVsum HV Hdom Hsum H. 
  destruct H as [Hsub (q & H)]. split.
  - apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
  - exists q. intros. apply H. 
    apply dst_equiv_implies_beq_supp in Hsum; auto. 
    apply in_supp_beq_supp_compat with (st:= st) in Hsum.
    rewrite Hsum. 
    apply in_supp_r_if_subset with (ls0:= (supp_mu (mu pd1))); auto.
    apply supp_mu_subset_decom_add_r.
Qed.

Lemma pd_equiv_preserves_unif_sugar: forall fs pd0 pd1,   (*Important*)
  Valid_dist (mu pd0) -> Valid_dist (mu pd1) ->
  pd1 ≡ pd0 -> well_defined_Pf (unif_sugar fs) ->
  [[unif_sugar fs]] pd0 ->
  [[unif_sugar fs]] pd1.
Proof.
  intros fs pd0 pd1 HV0 HV1 Heq HWD H. induction fs as [|f1 fs' IH].
  - simpl in *. 
    unfold unif_sugar. split; try reflexivity. intros.
    destruct H. apply H1 with st. destruct Heq as [Hdomeq Hmueq]. 
    apply in_supp_iff_posi_prob in H0; intuition. destruct H0 as [p Hprob].
    apply in_supp_iff_posi_prob; intuition. exists p; intuition.
    specialize (Hmueq st). rewrite <- Hmueq. intuition.
  - destruct fs' as [|f2 fs']. 
    + simpl in H. simpl. 
      apply pd_equiv_preserves_sem with (pd0:= pd0); intuition.
    + cbn [unif_sugar]. cbn [unif_sugar] in H. 
      apply pd_equiv_preserves_sem with (pd0:= pd0); intuition.
Qed.

Lemma pd_equiv_preserves_Unif_Depend_by: forall V mkfs pd0 pd1,  (*Important*)
  Valid_dist (mu pd0) -> Valid_dist (mu pd1) ->
  pd1 ≡ pd0 -> Unif_Depend_by V mkfs pd0 -> 
  Unif_Depend_by V mkfs pd1.
Proof.
  intros V mkfs pd0 pd1 HV0 HV1 Heq H. 
  destruct H as [N (HN & H)]. destruct H as (H & HWD & Hsem).
  unfold Unif_Depend_by. exists N. intuition.
  - destruct Heq as [Hdomeq Hmueq]. 
    apply H. apply in_supp_iff_posi_prob in H0; intuition. 
    destruct H0 as [p Hprob].
    apply in_supp_iff_posi_prob; intuition. exists p; intuition.
    specialize (Hmueq st). rewrite <- Hmueq. intuition.
  - apply pd_equiv_preserves_unif_sugar with (pd0:= pd0); intuition. 
    apply WD_list_unif_sugar. assumption.
Qed.

Lemma WD_in_pf_C_uniform_MN : forall (f : Pformula) C M N, 
  (N > 0)%nat -> In f (pf_C_uniform C M N) -> 
  well_defined_Pf f.
Proof. 
  intros f C M N _ Hin.
  unfold pf_C_uniform in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [i (Hf &HiIn)].
  subst f. apply WD_Pdeter. apply WD_Dpred.
Qed.

Lemma WD_Unif_MN: forall C M N, 
  (N > 0)%nat ->
  well_defined_Pf (unif_sugar (pf_C_uniform C M N)). 
Proof.
  intros. apply WD_unif_sugar. 
  - induction N as [| N' IH]. 
    + exfalso; lia.
    + unfold pf_C_uniform, unif_sugar. simpl. intuition. inversion H0.
  - apply Forall_forall. intros. 
    apply WD_in_pf_C_uniform_MN with (C:= C) (M:= M) (N:= N); try assumption.
Qed. 

Lemma exclude_unif_sugar :
  forall fs,
    fs <> [] ->
    Forall exclude_odot fs ->
    exclude_odot (unif_sugar fs).
Proof.
  intros fs Hne Hall.
  induction fs as [|f fs IH]; [contradiction|].
  inversion Hall as [|? ? Hwd_f Hwd_fs]; subst.
  destruct fs as [|f' fs'].
  - cbn [unif_sugar]. exact Hwd_f.
  - cbn [unif_sugar]. cbn [exclude_odot]. intuition. 
    apply IH; auto. intuition. inversion H.
Qed.

Lemma exclude_Unif_MN : forall C M N, 
  (N > 0)%nat ->
  exclude_odot (unif_sugar (pf_C_uniform C M N)).
Proof.
  intros. apply exclude_unif_sugar.
  - induction N as [| N' IH]. 
    + exfalso; lia.
    + unfold pf_C_uniform, unif_sugar. simpl. intuition. inversion H0.
  - apply Forall_forall. intros. 
    unfold pf_C_uniform in H0.
    apply in_map_iff in H0.
    destruct H0 as [i (Hf &HiIn)]. rewrite <- Hf.
    unfold exclude_odot. intuition.
Qed.

Lemma pd_equiv_preserves_unif_depend_nv: forall C V n pd0 pd1, (*Important*)
  Valid_dist (mu pd0) -> Valid_dist (mu pd1) ->
  pd1 ≡ pd0 -> C_unif_depend_to_nv C V n pd0 -> 
  C_unif_depend_to_nv C V n pd1.
Proof.
  intros C V n pd0 pd1 HV0 HV1 Heq H. 
  destruct H as [N (HN & H)]. destruct H as (H & Hsem).
  unfold C_unif_depend_to_nv. exists N. intuition.
  - destruct Heq as [Hdomeq Hmueq]. 
    apply H. apply in_supp_iff_posi_prob in H0; intuition. 
    destruct H0 as [p Hprob].
    apply in_supp_iff_posi_prob; intuition. exists p; intuition.
    specialize (Hmueq st). rewrite <- Hmueq. intuition.
  - apply pd_equiv_preserves_unif_sugar with (pd0:= pd0); intuition. 
    apply WD_Unif_MN. lia.
Qed.

Lemma Asser_pd_equiv_implies_sem:  (*Important*)
  forall pd0 pd1 P, 
  Valid_dist (mu pd0) ->  Valid_dist (mu pd1) -> 
  GoodAssertion P -> 
  pd1 ≡ pd0 -> P pd0 -> P pd1.
Proof.
  intros pd0 pd1 P Hvalid0 Hvalid1 HG0 Heq Hsem.
  generalize dependent pd1. generalize dependent pd0.
  induction HG0; intros. 
  - apply pd_equiv_preserves_sem with (pd0:= pd0); intuition. 
  - apply pd_equiv_preserves_Dirac with (pd0:= pd0); intuition.
  - apply pd_equiv_preserves_Unif_Depend_by with (pd0:= pd0); intuition.
  - apply pd_equiv_preserves_unif_depend_nv with (pd0:= pd0); intuition.
  - destruct Hsem as [HP HQ]. 
    apply IHHG0_1 with (pd1:= pd1) in HP; intuition. 
    apply IHHG0_2 with (pd1:= pd1) in HQ; intuition. 
  - destruct Hsem as [Hcase1 | Hsem]. 
    + destruct Hcase1 as [p1 H]. destruct H as [p2 H]. 
      destruct H as [Hp1 H]. destruct H as [Hp2 H]. destruct H as [Hp_eq H].
      destruct H as [pd01 H]. destruct H as [pd02 H].
      destruct H as [HWF01 H]. destruct H as [HWF02 H].
      destruct H as [Hdom01 H]. destruct H as [Hdom02 H].
      destruct H as [Hsem01 H]. destruct H as [Hsem02 H].
      destruct H as [Hsum0 H]. destruct H as [Hsum1 Hmu].
      apply IHHG0_1 with (pd1:= pd01) in Hsem01; intuition; try apply pd_equiv_refl.
      apply IHHG0_2 with (pd1:= pd02) in Hsem02; intuition; try apply pd_equiv_refl.
      left. exists p1. exists p2. split; intuition.
      exists pd01, pd02. 
      destruct Heq as [Hdomeq Hmueq]. apply dom_equiv_sym in Hdomeq. 
      apply dst_equiv_sym in Hmueq.
      intuition. 
      * apply dom_equiv_trans with (l1:= dom pd0); intuition.
      * apply dom_equiv_trans with (l1:= dom pd0); intuition.
      * rewrite Hsum0. apply dst_equiv_implies_sum_probs_eq; intuition.
      * rewrite Hsum1. apply dst_equiv_implies_sum_probs_eq; intuition.
      * apply dst_equiv_trans with (mu1:= mu pd0); intuition.
        apply dst_equiv_sym. assumption.
    + destruct Hsem as [HsemP | HsemQ].
      * right. left. apply IHHG0_1 with pd0; intuition.
      * right. right. apply IHHG0_2 with pd0; intuition.
Qed.

Lemma pd_mult_cofe_Dirac: forall V pd p,   (*Important*)
  Valid_dist (mu pd) -> (0 < p)%R ->
  Dirac_v V pd -> 
  Dirac_v V {| dom := dom pd; 
               mu := (p * mu pd)%dist_state; 
               all_partial := pd_mult_preserve_PD pd p |}.
Proof.
  intros V pd p HV Hp H. 
  destruct H as [Hdom (q & H)]. 
  split.
  - simpl. intuition.
  - exists q. intros. apply H. simpl in H0. 
    rewrite <- supp_eq_mult_coef in H0; intuition.
Qed.


Lemma pd_mult_cofe_unif_sugar: forall fs pd p,  (*Important*)
  Valid_dist (mu pd) -> 
  (0 < p)%R -> 0 <= sum_probs (p * (mu pd))%dist_state <= 1-> 
  well_defined_Pf (unif_sugar fs) ->
  [[unif_sugar fs]] pd ->
  [[unif_sugar fs]] (Build_partial_dist (dom pd) 
                                        (p * (mu pd))%dist_state 
                                        (pd_mult_preserve_PD pd p)).
Proof.
  intros fs pd p HV Hp Hsum HWD H. induction fs as [|f1 fs' IH].
  - simpl in *.  split; try reflexivity. intros.
    destruct H. apply H1 with st. 
    rewrite <- supp_eq_mult_coef in H0; intuition. 
  - destruct fs' as [|f2 fs']. 
    + simpl in H. simpl. apply sem_mult_cofe; auto. lra.
    + cbn [unif_sugar]. cbn [unif_sugar] in H. 
      apply sem_mult_cofe; auto. lra.
Qed.

Lemma pd_mult_cofe_Unif_Depend:   (*Important*)
  forall pd V mkfs p,  
    (0 < p)%R -> 
    Valid_dist (mu pd) ->
    0 <= sum_probs (p * (mu pd))%dist_state <= 1-> 
    Unif_Depend_by V mkfs pd ->
    Unif_Depend_by V mkfs (Build_partial_dist (dom pd) (p * (mu pd))%dist_state (pd_mult_preserve_PD pd p)).
Proof.
  intros pd V mkfs p H0 Hvalid Hsum Hsem. unfold Unif_Depend_by in *.
  destruct Hsem as [N (HN & H)]. destruct H as (H & (HWD & Hsem)).
  exists N. intuition.
  - apply H. simpl in H3. 
    rewrite <- supp_eq_mult_coef in H3; intuition.
  - apply pd_mult_cofe_unif_sugar; intuition.
    apply WD_list_unif_sugar. intuition.
Qed.

Lemma pd_mult_cofe_unif_depend_to_nv: (*Important*)
  forall pd C V p n,  
    (0 < p)%R -> 
    Valid_dist (mu pd) ->
    0 <= sum_probs (p * (mu pd))%dist_state <= 1-> 
    C_unif_depend_to_nv C V n pd ->
    C_unif_depend_to_nv C V n (Build_partial_dist (dom pd) (p * (mu pd))%dist_state (pd_mult_preserve_PD pd p)).
Proof.
  intros pd C V p n Hp Hvalid Hsum Hsem. unfold C_unif_depend_to_nv in *.
  destruct Hsem as [N (HN & H)]. destruct H as (H & Hsem).
  exists N. intuition.
  - apply H. simpl in H2. 
    rewrite <- supp_eq_mult_coef in H2; intuition.
  - apply pd_mult_cofe_unif_sugar; intuition.
    apply WD_Unif_MN. lia.
Qed.

Lemma Asser_pd_sem_mult_cofe:  (*Important*)
  forall pd P p,  
    (0 < p)%R -> GoodAssertion P -> 
    Valid_dist (mu pd) ->
    (0 <= sum_probs (p * (mu pd))%dist_state <= 1)%R -> 
    P pd ->
    P (Build_partial_dist (dom pd) (p * (mu pd))%dist_state (pd_mult_preserve_PD pd p)). 
Proof. 
  intros pd P p Hp HG Hvalid Hsum Hsem.
  generalize dependent pd. induction HG; intros. 
  - apply sem_mult_cofe; auto. lra. 
  - apply pd_mult_cofe_Dirac; intuition. 
  - apply pd_mult_cofe_Unif_Depend; intuition.
  - apply pd_mult_cofe_unif_depend_to_nv; intuition.
  - destruct Hsem as [HP HQ]. split. 
    + apply IHHG1; intuition. 
    + apply IHHG2; intuition. 
  - destruct Hsem as [Hcase1 | Hsem]. 
    + destruct Hcase1 as [p1 H]. destruct H as [p2 H]. 
      destruct H as [Hp1 H]. destruct H as [Hp2 H]. destruct H as [Hp_eq H].
      destruct H as [pd1 H]. destruct H as [pd2 H].
      destruct H as [HWF1 H]. destruct H as [HWF2 H].
      destruct H as [Hdom1 H]. destruct H as [Hdom2 H].
      destruct H as [Hsem1 H]. destruct H as [Hsem2 H].
      destruct H as [Hsum1 H]. destruct H as [Hsum2 Hmu].
      left. exists p1. exists p2. split; auto. split; auto. split; auto.
      pose (pd1':= {| dom := dom pd1; mu := (p * mu pd1)%dist_state;
                        all_partial := pd_mult_preserve_PD pd1 p |}).
      pose (pd2':= {| dom := dom pd2; mu := (p * mu pd2)%dist_state;
                        all_partial := pd_mult_preserve_PD pd2 p |}).
      assert (Hsum1_p: (0 <= sum_probs (p * (mu pd1))%dist_state <= 1)%R). { 
            rewrite dst_sum_prob_coef_mult.
            rewrite dst_sum_prob_coef_mult in Hsum. 
            rewrite <- Hsum1 in Hsum. assumption. }
      assert (Hsum2_p: (0 <= sum_probs (p * (mu pd2))%dist_state <= 1)%R). { 
            rewrite dst_sum_prob_coef_mult.
            rewrite dst_sum_prob_coef_mult in Hsum. 
            rewrite <- Hsum2 in Hsum. assumption. }
      exists pd1', pd2'; intuition.
      * try apply Valid_mult_under_eq_prob; auto. lra.
      * try apply Valid_mult_under_eq_prob; auto. lra.
      * apply IHHG1 in Hsem1; intuition; try apply pd_equiv_refl.
      * apply IHHG2 in Hsem2; intuition; try apply pd_equiv_refl.
      * simpl. repeat rewrite dst_sum_prob_coef_mult. rewrite Hsum1. auto.
      * simpl. repeat rewrite dst_sum_prob_coef_mult. rewrite Hsum2. auto.
      * simpl. rewrite dst_mult_comm_eq. rewrite dst_mult_comm_eq with (mu:= mu pd2).
        rewrite <- dst_mult_plus_distr_r_eq. apply dst_mult_preserves_equiv. 
        try assumption.
    + destruct Hsem as [HsemP | HsemQ].
      * right. left. apply IHHG1; intuition.
      * right. right. apply IHHG2; intuition.
Qed. 

Lemma AssertOplus_under_Mixed: (*Important*)
  forall b pd phi0 phi1, 
  Valid_dist (mu pd) -> 
  b_supp_classify b pd = Mixed -> 
  GoodAssertion phi0 -> well_defined_Pf phi1 -> well_defined_Pf (Pdeter (Dpred b)) -> 
  assert_Oplus (phi0 /\ [[Pdeter (Dpred b)]]) ([[phi1]] /\ [[~ b]]) pd ->
  phi0 (extract_b_pd b pd) /\ [[Pdeter (Dpred b)]] (extract_b_pd b pd) /\ 
  [[phi1]] (extract_notb_pd b pd) /\ [[Pdeter (Dpred (~ b))]] (extract_notb_pd b pd) .
Proof. 
  intros b pd phi0 phi1 Hvalid Hb HG0 HWD1 HWDb Hsem. 
  destruct Hsem as [Hcase1 | Hsem].
  - destruct Hcase1 as [p1 H]. destruct H as [p2 H]. 
    destruct H as [Hp1 H]. destruct H as [Hp2 H]. destruct H as [Hp_eq H].
    destruct H as [pd01 H]. destruct H as [pd02 H].
    destruct H as [HWF01 H]. destruct H as [HWF02 H]. 
    destruct H as [Hdom01 H]. destruct H as [Hdom02 H].
    destruct H as [Hsem01 H]. destruct H as [Hsem02 H].
    destruct H as [Hsum0 H]. destruct H as [Hsum1 Hmu].
    assert (Hvalid': Valid_dist (p1 * mu pd01 + p2 * mu pd02)%dist_state). { 
        apply Valid_linear; try assumption. 
        - destruct Hp1. split; apply Rlt_le; assumption.
        - destruct Hp2. split; apply Rlt_le; assumption.
        - rewrite Hp_eq. apply Rle_refl. }
    destruct Hsem01 as [Hsem0 Hsme01]. destruct Hsem02 as [Hsem1 Hsme02].
    destruct pd as [dom mu HPD]. destruct pd01 as [dom01 mu0_ex HPD0]. 
    destruct pd02 as [dom02 mu1_ex HPD1].
    simpl in HWF01. simpl in HWF02. simpl in Hdom01. simpl in Hdom02.
    simpl in Hsum0. simpl in Hsum1. simpl in Hmu. simpl in Hvalid'. 
    assert (Hb_eq: (get_b_in_mu b mu == get_b_in_mu b (p1 * mu0_ex + p2 * mu1_ex))%dist_state). { 
        apply Peq_implies_get_b_Peq; try assumption. }
    assert (Hnotb_eq: (get_notb_in_mu b mu == get_notb_in_mu b (p1 * mu0_ex + p2 * mu1_ex))%dist_state). { 
        apply Peq_implies_get_notb_Peq; try assumption. }
    assert (Hmu0_ex_b_eq: get_b_in_mu b mu0_ex = mu0_ex). { 
      apply bT_sem_implies_getb_refl with (pd:= Build_partial_dist dom01 mu0_ex HPD0). assumption. }
    assert (Hmu0_ex_notb_nil: get_notb_in_mu b mu0_ex = []). {
        rewrite <- Hmu0_ex_b_eq. apply get_notb_after_get_b. }
    assert (Hmu1_ex_notb: get_notb_in_mu b mu1_ex = mu1_ex). { 
      apply bF_sem_implies_getnotb_refl with (pd:= {| dom := dom02; mu := mu1_ex; all_partial := HPD1 |}). 
      assumption. }
    assert (Hmu1_ex_b_nil: get_b_in_mu b mu1_ex = []). {
          rewrite <- Hmu1_ex_notb. 
          apply get_b_after_get_notb. } 
    rewrite get_b_assoc in Hb_eq. repeat rewrite dst_get_b_coef_mult in Hb_eq.
    rewrite Hmu1_ex_b_nil in Hb_eq. simpl in Hb_eq. 
    rewrite dst_add_0_r in Hb_eq. rewrite Hmu0_ex_b_eq in Hb_eq. 
    rewrite get_notb_assoc in Hnotb_eq. repeat rewrite dst_get_notb_coef_mult in Hnotb_eq.
    rewrite Hmu0_ex_notb_nil in Hnotb_eq. simpl in Hnotb_eq. 
    rewrite Hmu1_ex_notb in Hnotb_eq. 
    assert (HPD0': partial_dst_Prop dom01 (p1 * mu0_ex)%dist_state). { 
      apply PD_mult_coef; try assumption. }
    pose (pd0':= {|
          dom := CoreDef.dom {| dom := dom01; mu := mu0_ex; all_partial := HPD0 |};
          mu := (p1 * CoreDef.mu {| dom := dom01; mu := mu0_ex; all_partial := HPD0 |})%dist_state;
          all_partial :=
            pd_mult_preserve_PD {| dom := dom01; mu := mu0_ex; all_partial := HPD0 |} p1
        |}).
    assert (Hequiv0: (extract_b_pd b {| dom := dom; mu := mu; all_partial := HPD |}) ≡ pd0'). {
        split; simpl; try assumption. apply dom_equiv_sym. assumption. } 
    assert (HPD1': partial_dst_Prop dom02 (p2 * mu1_ex)%dist_state). { apply PD_mult_coef; try assumption. }
    pose (pd1':= {|
          dom := CoreDef.dom {| dom := dom02; mu := mu1_ex; all_partial := HPD1 |};
          mu := (p2 * CoreDef.mu {| dom := dom02; mu := mu1_ex; all_partial := HPD1 |})%dist_state;
          all_partial :=
            pd_mult_preserve_PD {| dom := dom02; mu := mu1_ex; all_partial := HPD1 |} p2
        |}).
    assert (Hequiv1: (extract_notb_pd b {| dom := dom; mu := mu; all_partial := HPD |}) ≡ pd1'). {
          split; simpl; try assumption. apply dom_equiv_sym. assumption. }
    split.
    + apply Asser_pd_equiv_implies_sem with (pd0:= pd0'); try assumption.
      * simpl. apply Valid_add_decom in Hvalid'. destruct Hvalid'. assumption.
      * simpl. apply dst_Valid_get_b. assumption.
      * apply Asser_pd_sem_mult_cofe; intuition; simpl.
      ** repeat rewrite dst_sum_prob_coef_mult. destruct HWF01 as [H1' H2']. destruct H1'. 
        apply Rmult_le_pos; try assumption. lra.
      ** repeat rewrite dst_sum_prob_coef_mult. destruct HWF01 as [H1' H2']. destruct H1'. 
        rewrite <- Rmult_1_r with (r:= 1%R). apply Rmult_le_compat; auto; lra.
    + intuition.
      * apply pd_equiv_preserves_sem with (pd0:= pd0'); try assumption.
      ** simpl. apply Valid_add_decom in Hvalid'. destruct Hvalid'. assumption.
      ** simpl. apply dst_Valid_get_b. assumption.
      ** apply sem_mult_cofe with (p:= p1) in Hsme01; try assumption; try lra.
        apply Valid_add_decom in Hvalid'. destruct Hvalid' as [H' H'']. 
        simpl. destruct H'. assumption. 
      * apply pd_equiv_preserves_sem with (pd0:= pd1'); try assumption.
      ** simpl. apply Valid_add_decom in Hvalid'. destruct Hvalid'. assumption.
      ** simpl. apply dst_Valid_get_notb. assumption.
      ** apply sem_mult_cofe with (p:= p2) in Hsem1; try assumption; try lra.
        simpl. apply Valid_add_decom in Hvalid'. 
        destruct Hvalid' as [H' H'']. destruct H''. assumption.
      * apply pd_equiv_preserves_sem with (pd0:= pd1'); try assumption.
      ** simpl. apply Valid_add_decom in Hvalid'. destruct Hvalid'. assumption.
      ** simpl. apply dst_Valid_get_notb. assumption.
      ** try apply WD_Pdeter; try apply WD_Dpred.
      ** apply sem_mult_cofe with (p:= p2) in Hsme02; 
          try assumption; try lra; try apply WD_Pdeter; try apply WD_Dpred.
        simpl. apply Valid_add_decom in Hvalid'. 
        destruct Hvalid' as [H' H'']. destruct H''. assumption. 
  - destruct Hsem as [Hcase2| Hcase3]. 
    * destruct Hcase2 as [Hphi0 Hcontra]. 
      apply bT_sem_iff in Hcontra. destruct Hcontra as [_ Hcontra].
      rewrite Hb in Hcontra. destruct Hcontra; discriminate.
    * destruct Hcase3 as [Hphi1 Hcontra].
      apply bF_sem_iff in Hcontra. destruct Hcontra as [_ Hcontra].
      rewrite Hb in Hcontra. destruct Hcontra; discriminate.
Qed. 

(********************************)

Lemma hoare_while_sem : forall (P0 phi: PAssertion) phi1 (b : bexp) (c : winstr),  (*Important*)
  well_defined_Pf (Pdeter (Dpred b)) -> 
  well_defined_Pf phi1 -> exclude_odot phi1 -> 
  (get_var_in_Pformular phi1 ⊆ get_modvar_in_winstr c)%domain ->
  GoodAssertion P0 ->
  phi = assert_Oplus (P0 /\ [[(Pdeter (Dpred b))]]) ([[phi1]] /\ [[~ b]]) ->
  {{ P0 /\ [[(Pdeter (Dpred b))]] }} c {{ phi }} ->
  {{ phi }} (While b c) {{ ([[phi1]] /\ [[~ b]])}}.
Proof.
  intros P0 phi phi1 b c HWb HWD1 HEX Hphi1 HGP0 Hphi Hc.
  intros pd pd' Hvalid HZ HZc Hw H.
  assert(Hw_copy: pd =[ WHILE b DO c OD ]=> pd') by assumption.
  remember (While b c) as original_command eqn:Horig.
  rewrite Hphi in Hc. rewrite Hphi in H.
  induction Hw; try inversion Horig; subst. 
  - split; try apply emp_dst_satisfies_phi; intuition. 
    + apply dom_subset_orb_dom_l. assumption.
    + apply WD_Pdeter. apply WD_Dpred.
    + simpl. unfold WF_bexp_with_pd in H0. apply dom_subset_orb_dom_r. assumption.
  - assert (Hv1: Valid_dist (mu pd1)). { apply Valid_forall_NS in Hw1; try assumption. }
    assert (Hv': Valid_dist (mu pd')). { apply Valid_forall_NS in Hw2; try assumption. }
    apply IHHw2; try assumption.
    + apply inject_Z_after_NS in Hw1; try assumption.
    + apply AssertOplus_under_All_true in H; try assumption. (*According to: Hw1 Hc*)
      assert (Hsem1: (P0 /\ [[Pdeter (Dpred b)]])%assertion pd). { 
        split; try assumption. 
        apply bT_sem_iff. intuition. }
      * specialize (Hc pd pd1 Hvalid HZ HZc Hw1 Hsem1). assumption. 
  - apply AssertOplus_under_All_false in H; intuition. 
    apply bF_sem_iff. intuition.
  - assert (Hvb: Valid_dist (mu pd_b)). { simpl. apply dst_Valid_get_b. assumption. }
    assert (Hvnotb: Valid_dist (mu pd_notb)). { simpl. apply dst_Valid_get_notb. assumption. }
    assert (Hv0: Valid_dist (mu pd0)). { apply Valid_forall_NS in Hw1; try assumption. }
    assert (Hv1: Valid_dist (mu pd1)). { apply Valid_forall_NS in Hw2; try assumption. }
    assert (Hv': Valid_dist (mu pd')). { apply Valid_forall_NS in Hw_copy; try assumption. }
    split.
    { apply phi_sem_add with (pd0:= pd1) (pd1:= pd_notb); try assumption.
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
      + apply IHHw2; try assumption; intuition. 
        * apply inject_Z_after_NS in Hw1; intuition. apply getb_inject_Z. assumption.
        * specialize (Hc pd_b pd0 Hvb). apply Hc; intuition. 
        ** apply getb_inject_Z. assumption.
        ** apply AssertOplus_under_Mixed in H; try assumption; intuition.
        ** apply AssertOplus_under_Mixed in H; try assumption; intuition.
      + apply AssertOplus_under_Mixed in H; try assumption; intuition.
    }
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
    + apply WD_Pdeter. apply WD_Dpred.
    + simpl. apply I.
    + apply IHHw2; try assumption; intuition. 
      * apply inject_Z_after_NS in Hw1; intuition. apply getb_inject_Z. assumption.
      * specialize (Hc pd_b pd0 Hvb). apply Hc; intuition. 
      ** apply getb_inject_Z. assumption.
      ** apply AssertOplus_under_Mixed in H; try assumption; intuition.
      ** apply AssertOplus_under_Mixed in H; try assumption; intuition.
    + apply AssertOplus_under_Mixed in H; try assumption; intuition.
Qed.


(********************************)
Lemma notb_NIL: forall b pd, 
  b_supp_classify (~ b) pd = All_nil -> pd.(mu) = nil.
Proof. 
  intros b pd Hb. unfold b_supp_classify in Hb. 
  destruct pd as [dom_ mu_ HPD]. 
  destruct mu_ as [|].
  - simpl in *. reflexivity.
  - destruct p. simpl in *. 
    destruct (forallb (fun s : partial_st => negb (evalB_st b s))
      (supp_mu ((p, r) :: mu_))); try discriminate. 
    destruct (forallb (fun s : partial_st => negb (negb (evalB_st b s)))
      (supp_mu ((p, r) :: mu_))); try discriminate.
Qed.

Lemma Unif_emp: forall C V pd X, 
  singleton_bool_list C ⊆ dom pd ->
  is_domain_subset (dom pd) X = true -> mu pd = [] -> 
  C_unif_depend_to_0v C V (pd_emp X).
Proof. 
  intros C V pd X H Hdom Hmu. destruct pd as [dom_ mu_ HPD].
  unfold C_unif_depend_to_0v, Unif_Depend_by in *. exists 1%nat.
  split; try lia. split; try assumption.
  - intros. simpl in H0. inversion H0.
  - split.
    * simpl. intuition. apply WD_Pdeter. apply WD_Dpred.
    * apply emp_dst_satisfies_phi; try assumption. 
      + simpl. apply WD_Pdeter. apply WD_Dpred.
      + simpl. rewrite orb_domain_nil_r. 
        apply dom_subset_trans with (l1:= dom_); try assumption. 
Qed.


Lemma Dirac_implies_Left: forall (V:nat) (r bn:Q) ls, 
  (forall st : partial_st, is_in_supp st ls = true -> (get V st == r)%Q)->
  (r < bn)%Q ->
  forallb (fun s0 : partial_st => negb (negb (negb (Qle_bool bn (get V s0))))) ls = true.
Proof. 
  intros V r bn ls H Hlt. induction ls as [| s ls' IH].
  - simpl. reflexivity.
  - simpl in *. apply andb_true_iff. split. 
    + rewrite negb_involutive, negb_true_iff. 
      specialize (H s). rewrite state_eq_refl in H. simpl in H. intuition. 
      rewrite H0. destruct (Qle_bool bn r) eqn:Hb; [| reflexivity].
      exfalso. apply (Qlt_irrefl r).
      apply (Qlt_le_trans r bn r); [exact Hlt|].
      apply (proj1 (Qle_bool_iff bn r)).
      exact Hb.
    + apply IH; try assumption. intros. apply H. 
      rewrite H0. rewrite orb_true_r. reflexivity.
Qed. 

Lemma Dirac_implies_Right: forall (V:nat) (r bn:Q) ls, 
  (forall st : partial_st, is_in_supp st ls = true -> (get V st == r)%Q)->
  (bn <= r)%Q ->
  forallb (fun s : partial_st => (evalB_st (~ V < bn) s)) ls = true.
Proof. 
  intros V r bn ls H Hlt. induction ls as [| s ls' IH].
  - simpl. reflexivity.
  - simpl in *. apply andb_true_iff. split. 
    + try rewrite negb_true_iff, negb_false_iff. 
      specialize (H s). rewrite state_eq_refl in H. simpl in H. intuition. 
      rewrite H0. apply Qle_bool_iff. intuition.
    + apply IH; try assumption. intros. 
      apply H. rewrite H0. rewrite orb_true_r. reflexivity.
Qed. 


Lemma Dirac_contra_Mixed: forall V pd (bn:Q), 
  Dirac_v V pd -> 
  b_supp_classify (~ V < bn) pd <> Mixed. 
Proof.
  intros V pd bn HD. 
  destruct pd as [dom_ mu_ HPD]. unfold Dirac_v in HD. destruct HD as [HdomV (r & HD)].
  destruct (Qlt_le_dec r bn) as [Hlt | Hge].
  - induction mu_ as [| (s, p) mu' IH].
    + simpl in *. intuition. inversion H.
    + unfold b_supp_classify. simpl in HD. 
      apply Dirac_implies_Left with (bn:=bn) in HD; try assumption.
      simpl. rewrite HD. intuition. 
      destruct (forallb (fun s0 : partial_st => (negb (negb (Qle_bool bn (get V s0))))) 
                        (supp_mu ((s, p) :: mu'))) eqn:Hcontra; intuition; inversion H. 
  - induction mu_ as [| (s, p) mu' IH].
    + simpl in *. intuition. inversion H.
    + unfold b_supp_classify. simpl in HD.
      apply Dirac_implies_Right with (bn:=bn) in HD; try assumption.
      simpl. simpl in HD. rewrite HD. intuition. inversion H.
Qed.


Lemma rangeQ_0_S : forall n, rangeQ 0 (S n) = 0%Q :: rangeQ 1 n.
Proof. 
  intros. induction n as [| n' IH]. 
  - unfold rangeQ. simpl. reflexivity. 
  - unfold rangeQ. simpl. f_equal. 
Qed.

Lemma get_var_unif_sugar_singleton :
  forall fs C,
    fs <> [] ->
    (forall f, In f fs ->
       get_var_in_Pformular f = singleton_bool_list C) ->
    get_var_in_Pformular (unif_sugar fs) = singleton_bool_list C.
Proof.
  induction fs as [| f fs IH]; intros C Hne Hall.
  - contradiction. 
  - destruct fs as [|f' fs'].
    + simpl. apply Hall. simpl. auto.
    + unfold unif_sugar. fold unif_sugar. 
      unfold get_var_in_Pformular. fold get_var_in_Pformular. 
      assert (H: (0 < / INR (S (length (f' :: fs'))) < 1)%R) 
        by apply inv_INR_S_length_gt_0_and_lt_1.
      destruct H as [Ha_pos Ha_lt1]. 
      set (a := / INR (S (length (f' :: fs')))).
      destruct (Rle_lt_dec a 0) as [Ha_le0 | Ha_gt0].
      * exfalso. exact (Rlt_not_le _ _ Ha_pos Ha_le0).
      * destruct (Rle_lt_dec 1 a) as [Ha_le1 | Ha_gt1].
      ** apply Hall. simpl. auto.
      ** unfold unif_sugar in IH. 
        fold unif_sugar in IH. rewrite IH with (C:= C); auto.
      -- specialize (Hall f). rewrite Hall. 
      ++ rewrite orb_domain_refl. auto.
      ++ simpl. auto.
      -- intuition. inversion H.
      -- intros. apply Hall. simpl. simpl in H. auto.
Qed.

Lemma var_in_pf_C_uniform_eq_C : forall (f : Pformula) C M N, 
  (N > 0)%nat -> In f (pf_C_uniform C M N) -> 
  get_var_in_Pformular f = singleton_bool_list C.
Proof. 
  intros f C M N _ Hin.
  unfold pf_C_uniform in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [i (Hf &HiIn)].
  subst f. simpl. 
  rewrite orb_domain_nil_r. reflexivity.
Qed.

Lemma get_var_in_unif_MN: forall C M N, 
  (N > 0)%nat ->
  (get_var_in_Pformular (unif_sugar (pf_C_uniform C M N)))%domain = 
    (singleton_bool_list C)%domain.
Proof. 
  intros C M N Hlen. apply get_var_unif_sugar_singleton. 
  - induction N as [| N' IH].
    + simpl in *. inversion Hlen. 
    + unfold pf_C_uniform. simpl. intuition. inversion H.
  - intros. apply var_in_pf_C_uniform_eq_C with (N:= N) (M:= M); try assumption.
Qed.


Lemma dom_subset_unif_0V: forall V C pd, 
  C_unif_depend_to_0v C V pd -> (singleton_bool_list C ⊆ dom pd)%domain.
Proof.
  intros V C pd H. destruct H as [N (HN & (HWD & H))]. destruct H as [Hn H]. 
  apply satisfy_implies_dom_sub in H; try assumption.
  - rewrite <- get_var_in_unif_MN with (N:= N) (M:= 0%nat); try assumption.
  - apply WD_Unif_MN. assumption.
Qed.

Lemma dom_subset_unif_nV: forall V C n pd, 
  C_unif_depend_to_nv C V n pd -> 
  (singleton_bool_list C ⊆ dom pd)%domain.
Proof.
  intros V C n pd H. 
  destruct H as [N (HN & H)]. destruct H as [Hn H].
  apply satisfy_implies_dom_sub in H; simpl in H; try assumption.
  - rewrite <- get_var_in_unif_MN with (N:= (N-n)%nat) (M:= n); try assumption; try lia. 
  - apply WD_Unif_MN. lia.
Qed.


Lemma forallb_negb_true_implies_forallb_false_if_nonempty 
  (b : bexp) (l : list partial_st): 
  forallb (fun s => negb (evalB_st b s)) l = true ->
  l <> [] ->
  forallb (fun s => evalB_st b s) l = false.
Proof.
  intros Hneg Hne.
  destruct l as [|x xs].
  - exfalso. apply Hne. reflexivity.
  - simpl.
    assert (Hxneg : negb (evalB_st b x) = true).
    { 
      apply (proj1 (forallb_forall (fun s => negb (evalB_st b s)) (x :: xs))) 
        with (x:= x) in Hneg; auto.
      simpl. auto.
    }
    apply negb_true_iff in Hxneg.
    rewrite Hxneg. simpl. reflexivity.
Qed.

Lemma forallb_two_negb_true_implies_forallb_false_if_nonempty 
  (b : bexp) (l : list partial_st): 
  forallb (fun s => negb (negb (evalB_st b s))) l = true ->
  l <> [] ->
  forallb (fun s => evalB_st b s) l = true.
Proof.
  intros Hneg _.
  apply (proj2 (forallb_forall (fun s => evalB_st b s) l)).
  intros x Hinx.
  assert ( Hx : negb (negb (evalB_st b x)) = true). { 
    apply (proj1 (forallb_forall (fun s => negb (negb (evalB_st b s))) l)) with (x:= x) in Hneg; auto.
  }
  now rewrite negb_involutive in Hx.
Qed. 

Lemma supp_classify_neg_true_false: forall b pd,
  b_supp_classify (~ b) pd = All_True -> 
  b_supp_classify b pd = All_False.
Proof.
  intros. destruct pd as [dom mu HPD]. 
  induction mu as [|(s,p) mu' IH].
  - unfold b_supp_classify in H. simpl in *. inversion H.
  - unfold b_supp_classify in H. simpl in *. 
    unfold b_supp_classify. simpl. 
    destruct (forallb (fun s : partial_st => negb (evalB_st b s)) (supp_mu ((s, p) :: mu'))) eqn: Hnb.
    + set (l := supp_mu ((s, p) :: mu')) in *. 
      apply forallb_negb_true_implies_forallb_false_if_nonempty with (l:= l) in Hnb; try assumption.
      * rewrite Hnb. auto.
      * unfold l, supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st. 
        intuition. apply supp_insert_valid_contra in H0. auto.
    + destruct (forallb (fun s : partial_st => negb (negb (evalB_st b s))) (supp_mu ((s, p) :: mu'))); inversion H.
Qed.

Lemma supp_classify_neg_false_true: forall b pd,
  b_supp_classify (~ b) pd = All_False -> 
  b_supp_classify b pd = All_True.
Proof.
  intros. destruct pd as [dom mu HPD]. 
  induction mu as [|(s,p) mu' IH].
  - unfold b_supp_classify in H. simpl in *. inversion H.
  - unfold b_supp_classify in H. simpl in *. 
    unfold b_supp_classify. simpl. 
    set (l := supp_mu ((s, p) :: mu')) in *. 
    destruct (forallb (fun s : partial_st => negb (evalB_st b s)) l) eqn: Hnb; try inversion H.
    destruct (forallb (fun s : partial_st => negb (negb (evalB_st b s))) l) eqn: Hnnb; try inversion H.
    apply forallb_two_negb_true_implies_forallb_false_if_nonempty with (l:= l) in Hnnb; try assumption.
      * rewrite Hnnb. auto.
      * unfold l, supp_mu. simpl. rewrite insert_st_pair_fst_eq_insert_st. 
        intuition. apply supp_insert_valid_contra in H0. auto.
Qed.

Lemma andb_sem_conj: forall b1 b2 pd, 
  [[b1 && b2]] pd <-> [[Pdeter (Dpred b1)]] pd /\ [[Pdeter (Dpred b2)]] pd.
Proof.
  intros b1 b2 pd. split. 
  { intros H. destruct H. simpl in H. apply dom_subset_orb_fst_iff in H.
    split. 
    + split; intuition. apply H0 in H. destruct H as [Hb1 Hb2]. split. 
      * simpl in Hb1. apply dom_subset_orb_fst_iff in Hb1. intuition.
      * destruct (evalB_st (b1 && b2) st) eqn: Hb; try contradiction.
        simpl in Hb. apply andb_true_iff in Hb. intuition. rewrite H. auto.
    + split; intuition. apply H0 in H. destruct H as [Hb1 Hb2]. split.
      * simpl in Hb1. apply dom_subset_orb_fst_iff in Hb1. intuition.
      * destruct (evalB_st (b1 && b2) st) eqn: Hb; try contradiction.
        simpl in Hb. apply andb_true_iff in Hb. intuition. rewrite H3. auto. }
  intros H. destruct H as [Hb1 Hb2]. split.
  - apply dst_satisfy_df_implies_dom in Hb1, Hb2. simpl in *. 
    apply dom_subset_orb_fst_iff; intuition. 
  - intros. destruct Hb1, Hb2. specialize (H1 st H). specialize (H3 st H).
    destruct H1, H3. 
    destruct (evalB_st b1 st) eqn: Hb1; 
    destruct (evalB_st b2 st) eqn: Hb2; try contradiction.
    split.
    + simpl. apply dom_subset_orb_fst_iff; intuition.
    + simpl. rewrite Hb1, Hb2. auto.  
Qed.

Lemma Dirac_pd_emp: forall V X,  
  singleton_bool_list V ⊆ X -> 
  Dirac_v V (pd_emp X).
Proof.
  intros V X H. split; intuition. exists default_Q. 
  intros. simpl in H0. inversion H0.
Qed.

Lemma hoare_cond_sem: forall (V C bn: nat) b' (c1 c2 : winstr), (*Important rule*)
  let b:= (V < inject_Z (Z.of_nat bn))%imp in
  {{(([[Pdeter (Dpred b)]] /\ (C_unif_depend_to_0v C V))%assertion /\ (Dirac_v V))%assertion}} 
    c1 {{(([[Pdeter (Dpred b)]] /\ (C_unif_depend_to_0v C V))%assertion/\ (Dirac_v V))%assertion}} -> 
  {{(([[(~b) && b']] /\ (C_unif_depend_to_nv C V bn))%assertion /\ (Dirac_v V))%assertion}} 
    c2 {{(([[Pdeter (Dpred b)]] /\ (C_unif_depend_to_0v C V))%assertion/\ (Dirac_v V))%assertion}} -> 
  {{(assert_Oplus ([[Pdeter (Dpred b)]] /\ (C_unif_depend_to_0v C V)) 
                  ([[(~b) && b']] /\ (C_unif_depend_to_nv C V bn))) 
    /\ (Dirac_v V)}} IF (~b) THEN c2 ELSE c1 FI 
  {{(([[Pdeter (Dpred b)]] /\ (C_unif_depend_to_0v C V))%assertion /\ (Dirac_v V))%assertion}}.
Proof. 
  intros V C bn b' c1 c2 b Hc1 Hc2. 
  intros pd pd' Hvalid HZ HZc HNC (Hoplus & HDV).
  inversion HNC; subst.
  - split. 
    + split. 
      { 
        apply emp_dst_satisfies_phi; simpl; try assumption; 
        try apply WD_Pdeter; try apply WD_Dpred.
        destruct HDV as [HdomV HDV].
        apply dom_subset_trans with (l1:= dom pd); try assumption.
        apply dom_subset_orb_snd_l_r.
      } 
      simpl. inversion HZc as [HZc1 HZc2]; subst.
      destruct Hoplus as [Hcase1 | Hcase2].
      { destruct Hcase1 as (p1 & p2 & Hp1 & Hp2 & Hp_sum & pd1 & pd2 & Hrest). 
        destruct Hrest as (Hv1 & Hv2 & Hdom1 & Hdom2 & Hsem1 & Hsem2 & Hsum1 & Hsum2 & Hmu). 
        assert (Hmu_nil: (mu pd1)= [] /\ (mu pd2) = []). { 
            apply notb_NIL in H3. rewrite H3 in Hsum1, Hsum2. 
            simpl in Hsum1, Hsum2.
            apply sum_probs0_implies_nil in Hsum1, Hsum2; try assumption.
            split; try assumption. }
        destruct Hmu_nil as [Hmu1 Hmu2].
        destruct Hsem1 as [Hsem1b Hsem1]. 
        apply dom_subset_unif_0V in Hsem1.
        apply Unif_emp with (pd:= pd1); intuition.
        apply dom_equiv_sym in Hdom1.
        apply dom_subset_eq_compat_right with (X:= dom pd); try assumption.
        apply dom_subset_orb_snd_l_r. 
      }
      destruct Hcase2 as [Hcase2| Hcase3]. 
      * destruct Hcase2 as [pd1 Hsem1]. 
        apply dom_subset_unif_0V in Hsem1.
        apply Unif_emp with (pd:= pd); intuition.
      ** apply dom_subset_orb_snd_l_r. 
      ** apply notb_NIL in H3. exact H3.
      * destruct Hcase3 as [pd1 Hsem1]. 
        apply dom_subset_unif_nV in Hsem1.
        apply Unif_emp with (pd:= pd); intuition.
      ** apply dom_subset_orb_snd_l_r. 
      ** apply notb_NIL in H3. exact H3.
    + apply Dirac_pd_emp. 
      apply dom_subset_trans with (l1:= dom pd); try assumption.
      apply dom_subset_orb_snd_l_r.
  - apply supp_classify_neg_true_false in H3.
    apply assert_oplus_and_comm in Hoplus.
    specialize (Hc2 pd pd'). inversion HZc; subst.
    assert (Hoplus': assert_Oplus (C_unif_depend_to_0v C V /\ [[Pdeter (Dpred b)]])
                                  ((C_unif_depend_to_nv C V bn /\ [[Pdeter (Dpred b')]])%assertion /\ [[~b]]) pd). {
                    destruct Hoplus.
                    - destruct H1 as (p1 & p2 & H'). intuition.
                      destruct H14 as (pd1 & pd2 & H'). intuition.
                      apply andb_sem_conj in H23.
                      left. exists p1, p2. intuition. exists pd1, pd2. intuition.
                    - right. intuition. right. apply andb_sem_conj in H8. intuition. }
    * apply Hc2; intuition.
      + apply AssertOplus_under_All_false in Hoplus'; intuition. 
        apply andb_sem_conj; intuition. apply bF_sem_iff; intuition.
      + apply AssertOplus_under_All_false in Hoplus'; intuition.
  - apply supp_classify_neg_false_true in H3.
    apply assert_oplus_and_comm in Hoplus.
    specialize (Hc1 pd pd'). inversion HZc; subst. 
    assert (Hoplus': assert_Oplus (C_unif_depend_to_0v C V /\ [[Pdeter (Dpred b)]])
                                  ((C_unif_depend_to_nv C V bn /\ [[Pdeter (Dpred b')]])%assertion 
                      /\ [[~b]]) pd). {
                    destruct Hoplus.
                    - destruct H1 as (p1 & p2 & H'). intuition.
                      destruct H14 as (pd1 & pd2 & H'). intuition.
                      apply andb_sem_conj in H23.
                      left. exists p1, p2. intuition. 
                      exists pd1, pd2. intuition.
                    - right. intuition. right. apply andb_sem_conj in H8. intuition. }
    * apply Hc1; intuition.
      + apply AssertOplus_under_All_true in Hoplus'; intuition. 
        apply bT_sem_iff; intuition.
      + apply AssertOplus_under_All_true in Hoplus'; intuition.
  - unfold b in H3. rename H3 into Hcontra. 
    apply Dirac_contra_Mixed with (bn:= inject_Z (Z.of_nat bn)) in HDV; try assumption. 
    rewrite Hcontra in HDV. contradiction.
Qed.


Lemma hoare_Frame_sem: forall (phi : Pformula) c (P Q: PAssertion), (*Important rule*)
  well_defined_Pf phi -> 
  is_domain_intersect (get_modvar_in_winstr c) (get_var_in_Pformular phi) = false ->
  {{P}} c {{Q}} -> 
  {{([[phi]] /\ P)%assertion}} c {{([[phi]] /\ Q)%assertion}}.
Proof. 
  intros phi c P Q HWD Hdom H. 
  unfold hoare_triple in *. intros. destruct H4.
  specialize (H pd pd' H0 H1 H2); intuition. 
  apply intersect_preserves_satisfy with (phi:= phi) in H3; intuition.
  rewrite intersect_comm. assumption.
Qed.

Section FastDice.

  Parameter N : nat.  

  Hypothesis HN : (inject_Z (Z.of_nat N) > 1)%Q.  (* Assume N is greater than 0 *)
  Definition weight1 : R := 1 / IZR (Z.of_nat N).
  Definition weight2 : R := (1 - weight1)/ (IZR (Z.of_nat N) - 1).

  Example Bit:= 0%nat.
  Example V := 1%nat.
  Example C:= 2%nat.
  Definition Bit_01 := [(Aco 0, /2);(Aco 1, (1 - /2)%R)].  
  Lemma half_bounds : 0 < /2 < 1.
    Proof. lra. Qed.
  Definition Vbit_01 : valid_dist_aexp := 
    exist _ Bit_01 (valid_da_of_two (Aco 0) (Aco 1) (/2) half_bounds).

  Definition DA_V: winstr:= (V ::= 1%Q).
  Definition DA_C: winstr:= (C ::= 0%Q).
  Definition RA_Bit: winstr:= (Bit $= Vbit_01).
  Definition DA_V_minus: winstr := (V ::= (V - inject_Z (Z.of_nat N))%imp).
  Definition DA_C_minus: winstr := (C ::= (C- inject_Z (Z.of_nat N))%imp).
  Definition DA_V_mult: winstr := (V ::= (2%Q * V)%imp).
  Definition DA_C_mult: winstr := (C ::= (2%Q * C + Bit)%imp).
  
  Definition B_VN: bexp:= (V < inject_Z (Z.of_nat N))%imp.
  Definition B_VR: bexp:= (~ B_VN) && (V < (2%Q * inject_Z (Z.of_nat N))%imp)%imp.
  Definition B_CN: bexp:= (C >= inject_Z (Z.of_nat N))%imp.
  Definition guard := (B_VN || ( (~B_VN) && B_CN) )%imp.
  Definition IF_VN := If (~ B_VN) (DA_V_minus;; DA_C_minus) (Skip). 
  Definition While_body := IF_VN;; DA_V_mult;; RA_Bit;; DA_C_mult.
  Definition FDR:= DA_V;; DA_C;; While guard While_body. 
  
  Definition phi1:= unif_sugar (pf_C_uniform C 0 N).
  Definition phi0_L: PAssertion := [[Pdeter (Dpred B_VN)]] /\ C_unif_depend_to_0v C V. 
  Definition phi0_R: PAssertion := [[Pdeter (Dpred (B_VR && B_CN))]] /\ C_unif_depend_to_nv C V N.
  Definition phi0:= ((assert_Oplus phi0_L phi0_R) /\ (Dirac_v V))%assertion.
  Definition invariant:= assert_Oplus (phi0 /\ [[Pdeter (Dpred guard)]])%assertion 
                                      ([[phi1]] /\ [[~guard]])%assertion.

  Definition dist_bit : Pformula := (Bit == Aco 0) ⊕[ (/ 2)%R ] (Bit == Aco 1).          

  Lemma EVAL_V: forall st V,  
    evalB_st (V = 1%Q) st = true -> evalB_st (V < inject_Z (Z.of_nat N)) st = true.
  Proof.
    intros. simpl in *. rewrite negb_true_iff. apply Qeq_bool_iff in H. rewrite H. 
    destruct (Qle_bool (inject_Z (Z.of_nat N)) 1) eqn: HNX; try reflexivity.
    destruct (Qcompare (inject_Z (Z.of_nat N)) 1) eqn: Hcomp.
    * apply Qeq_alt in Hcomp. rewrite <- Hcomp in HN. apply Qlt_irrefl in HN. contradiction.
    * apply Qlt_alt in Hcomp. 
      assert (Hcontra: (1 < 1)%Q). { apply Qlt_trans with (y:= inject_Z (Z.of_nat N)); try assumption. }
      apply Qlt_irrefl in Hcontra. contradiction.
    * apply Qgt_alt in Hcomp. apply Qle_bool_iff in HNX. 
      assert (Hcontra: (1 < 1)%Q). { apply Qlt_le_trans with (y:= inject_Z (Z.of_nat N)); try assumption. }
      apply Qlt_irrefl in Hcontra. contradiction.
  Qed.  
  Lemma EVAL_B_implies_A: forall st V (q:Q), 
    evalB_st (V = q) st = true -> (evalA_st V st == q)%Q.
  Proof. 
    intros. simpl in *. apply Qeq_bool_iff in H. rewrite H. reflexivity.
  Qed.
  Lemma Pdeter_implies_and: forall (b b': bexp) pd, [[(b && b')]] pd -> [[Pdeter (Dpred b)]] pd. 
  Proof.
    intros. destruct H. split. 
    - simpl in H. apply dom_subset_orb_fst_iff in H. intuition.
    - intros. apply H0 in H1. destruct H1. split; intuition.
      + simpl in H1. apply dom_subset_orb_fst_iff in H1. intuition.
      + simpl in H2. destruct ((evalB_st b st && evalB_st b' st)%bool) eqn: Hband; try contradiction.
        apply andb_true_iff in Hband. destruct Hband; try assumption. rewrite H3. trivial.
  Qed.

  Lemma Pdeter_mult_cofe : forall a1 a2 (p:Q) pd, 
    (p > 0)%Q -> 
    [[a1 < a2]] pd -> [[p * a1 < p * a2]] pd.
  Proof. 
    intros. destruct H0. split; intuition.
    apply H1 in H2. destruct H2.
    split; simpl in *; try assumption. 
    set (a1' := evalA_st a1 st) in *; set (a2' := evalA_st a2 st) in *.
    destruct (negb (Qle_bool a2' a1')) eqn : Hnegb; try contradiction.
    apply negb_true_iff in Hnegb.
    assert (Hnotle : ~ (a2' <= a1')%Q).
    { intro Hle.
      apply (proj2 (Qle_bool_iff a2' a1')) in Hle.
      congruence.
    }
    assert (Hlt : (a1' < a2')%Q).
    { apply Qnot_le_lt. exact Hnotle. }
    assert (Hlt_mul : (p * a1' < p * a2')%Q).
    { apply (Qmult_lt_l a1' a2' p); assumption. }
    assert (Hnotle_mul : ~ (p * a2' <= p * a1')%Q).
    { apply Qlt_not_le. exact Hlt_mul. }
    destruct (Qle_bool (p * a2') (p * a1')) eqn:Hb.
    - exfalso.
      apply (proj1 (Qle_bool_iff (p * a2') (p * a1'))) in Hb.
      exact (Hnotle_mul Hb).
    - reflexivity.
  Qed.

  Lemma mult2_eval_implies: forall st V (q:Q), 
    evalB_st (V < Aco (2 * q)%Q) st = true -> (evalB_st (V - q < q) st = true) .
  Proof. 
    intros. simpl in *. apply negb_true_iff in H. rewrite negb_true_iff.
    destruct (Qle_bool q (evalA_st V0 st - q)) eqn:Hb; [| reflexivity ].
    assert (Hle : (q <= evalA_st V0 st - q)%Q).
    { apply (proj1 (Qle_bool_iff q (evalA_st V0 st - q))).
      exact Hb.
    }
    assert (Hle_add : (q + q <= (evalA_st V0 st - q) + q)%Q).
    { apply Qplus_le_l with (z:= q) (x:= q) (y:= (evalA_st V0 st - q)%Q). exact Hle. }
    assert (H2le : (2 * q <= evalA_st V0 st)%Q).
    { 
      setoid_replace (q + q)%Q with (2 * q)%Q in Hle_add by ring.
      setoid_replace ((evalA_st V0 st - q) + q)%Q with (evalA_st V0 st)%Q in Hle_add by ring.
      exact Hle_add. }
    assert (Hb2 : Qle_bool (2 * q) (evalA_st V0 st) = true).
    { apply (proj2 (Qle_bool_iff (2 * q) (evalA_st V0 st))).
      exact H2le.
    }
    congruence.
  Qed.
  
  Lemma in_supp_DAssn_under_dstate_inv : forall st mu C e,
  is_in_supp st (supp_mu (DAssn_under_dstate mu C e)) = true ->
  exists st0,
    is_in_supp st0 (supp_mu mu) = true /\
    (st == update st0 C (evalA_st e st0))%state.
  Proof.
    intros. induction mu as [|(s,p) mu'].
    - simpl in *. inversion H.
    - simpl in H. unfold supp_mu in H. simpl in H.
      rewrite insert_st_pair_fst_eq_insert_st in H.
      rewrite in_supp_insert_eq in H. 
      apply orb_true_iff in H. destruct H.
      + exists s. intuition. apply in_supp_mu_cons_head.
      + apply IHmu' in H. destruct H as [st0 (H0 & H1)]. 
        exists st0; intuition. apply in_supp_mu_cons_r. auto.
  Qed.

  Lemma eval_eq_after_assign_shift : forall (i:Q) (C N: nat) pd (HWFa : WF_aexp_with_pd (C - inject_Z (Z.of_nat N)) pd),
  [[(C == Aco (i + inject_Z (Z.of_nat N)))%formula ]] pd ->
  [[(C == Aco i)%formula ]] (DAssn_under_pd C (C - inject_Z (Z.of_nat N)) pd HWFa).
  Proof.
    intros. destruct H. simpl in H. split; intuition.
    - simpl. apply dom_subset_trans with (l1:= dom pd); try assumption. 
      apply dom_subset_orb_dom_r. apply dom_subset_refl.
    - apply in_supp_DAssn_under_dstate_inv in H1. 
      destruct H1 as [st0 (Hin & Heq)].
      apply H0 in Hin. destruct Hin. simpl in H1. split.
      + simpl. apply st_eq_implies_dom_equiv in Heq. simpl in Heq.
        assert (Htmp: (return_domain st0) ⊆ 
                      (return_domain (update st0 C0 (get C0 st0 - inject_Z (Z.of_nat N0))))) 
                      by apply update_subst_implies_dom_eq.
        apply dom_equiv_sym in Heq.
        apply dom_subset_eq_compat_left with (X:= return_domain (update st0 C0 (get C0 st0 - inject_Z (Z.of_nat N0)))); try assumption.
        apply dom_subset_trans with (l1:= return_domain st0); try assumption.
      + simpl in H2. simpl.
        destruct (Qeq_bool (get C0 st0) (i + inject_Z (Z.of_nat N0))) eqn:Hb; try contradiction.
        apply Qeq_bool_iff in Hb. simpl in Heq. 
        apply Qplus_inj_r with (z:= (- inject_Z (Z.of_nat N0))%Q) in Hb.
        rewrite <- Qplus_assoc in Hb. rewrite Qplus_opp_r in Hb. 
        rewrite Qplus_0_r in Hb. apply Qeq_sym in Hb.
        assert (Htemp: (update st0 C0 i == update st0 C0 (get C0 st0 - inject_Z (Z.of_nat N0)))%state). {
          simpl. apply st_eq_implies_update_eq; auto. apply state_eq_refl.
        }
        assert (H': (update st0 C0 i == st)%state). {
        rewrite state_eq_sym in Heq.
        apply state_eq_trans with (s2:= st) in Htemp; try assumption. }
        apply st_eq_implies_get_eq with (x:= C0) in Htemp. simpl in Htemp.
        apply st_eq_implies_get_eq with (x:= C0) in H'. simpl in H'.
        assert(Hi: ((get C0 st) == i)%Q). {
          rewrite <- H'. rewrite Htemp. rewrite get_update_eq. rewrite Hb. 
          reflexivity.
        }
        apply Qeq_bool_iff in Hi. rewrite Hi. apply I.
  Qed.

  Lemma unif_sugar_after_assign_shift_index: 
  forall (C N NV : nat) len pd (HWFa : WF_aexp_with_pd (C - inject_Z (Z.of_nat N)) pd),
    Valid_dist (mu pd) ->
    [[unif_sugar (map (fun i : Q => (C == (i + inject_Z (Z.of_nat N))%Q)%formula) len)]] pd ->
    [[unif_sugar (map (fun i : Q => (C == i)%formula) len)]] (DAssn_under_pd C (C - inject_Z (Z.of_nat N)) pd HWFa).
  Proof.
    intros C N NV len pd HWFa HValid H. generalize dependent pd.
    induction len as [|i1 len]; intros.
    - cbn [map] in *. cbn [unif_sugar] in *. destruct H. 
      split; intuition. apply in_supp_DAssn_under_dstate_inv in H1. 
      destruct H1 as [st0 (Hin & Heq)].
      apply H0 in Hin. destruct Hin. split; simpl; auto.
    - destruct len as [|i2 len']. 
      + cbn [map] in *. cbn [unif_sugar] in *. 
        apply eval_eq_after_assign_shift. assumption.
      + cbn [map] in *. destruct H as [Hcase1 | H].
        * left. destruct Hcase1 as (Hp & pd1 & pd2 & Hrest). 
          destruct Hrest as (Hv1 & Hv2 & Hdom1 & Hdom2 & Hsem1 & Hsem2 & Hsum1 & Hsum2 & Hmu).
          set (l1:= length ((C == (i2 + inject_Z (Z.of_nat N))%Q)%formula
                      :: map (fun i : Q => (C == (i + inject_Z (Z.of_nat N))%Q)%formula) len')) in *.
          set (l2:= length ((C == i2)%formula
                      :: map (fun i : Q => (C == i)%formula) len')) in *.
          assert (Hl : l1 = l2). { unfold l1, l2. simpl. now rewrite !List.length_map. }
          split. 
          ** rewrite Hl in Hp. exact Hp.
          ** assert (HWFa1: WF_aexp_with_pd (C - inject_Z (Z.of_nat N)) pd1). { 
              apply dom_equiv_preserves_WF_aexp with (pd:= pd); intuition.
              apply dom_equiv_sym in Hdom1. assumption. }
            assert (HWFa2: WF_aexp_with_pd (C - inject_Z (Z.of_nat N)) pd2). { 
            apply dom_equiv_preserves_WF_aexp with (pd:= pd); intuition.
              apply dom_equiv_sym in Hdom2. assumption.
           }
            pose (pd1':= (DAssn_under_pd C (C - inject_Z (Z.of_nat N)) pd1 HWFa1)).
            pose (pd2':= (DAssn_under_pd C (C - inject_Z (Z.of_nat N)) pd2 HWFa2)).
            exists pd1', pd2'. intuition.
            ++ simpl. apply Valid_after_DA. assumption.
            ++ simpl. apply Valid_after_DA. assumption.
            ++ simpl. apply dom_eq_orb_compat_right. assumption.
            ++ simpl. apply dom_eq_orb_compat_right. assumption.
            ++ apply eval_eq_after_assign_shift. assumption.
            ++ apply IHlen; try assumption.
            ++ simpl. repeat rewrite DA_preserve_sum_prob. assumption.
            ++ simpl. repeat rewrite DA_preserve_sum_prob. assumption.
            ++ rewrite <- Hl. 
              apply DA_step_deter with (n:= C) 
                                       (a:= C - inject_Z (Z.of_nat N)) in Hmu; intuition.
              -- apply dst_equiv_trans with (mu1:= (DAssn_under_dstate (/ INR (S l1) * mu pd1 + 
                    (1 - / INR (S l1)) * mu pd2) C (C - inject_Z (Z.of_nat N)))%dist_state); try assumption.
                rewrite DAss_eq_under_addAndmult. apply dst_add_preserves_equiv.
              --- apply dst_equiv_refl.
              --- apply dst_equiv_refl.
             -- apply Valid_linear; try assumption; try lra.
        * destruct H as [Hcase2 | Hcase3].
        ** right. left. destruct Hcase2 as [Hp (pd1 & Hrest)]. 
        split.
        -- set (l1:= length ((C == (i2 + inject_Z (Z.of_nat N))%Q)%formula
                      :: map (fun i : Q => (C == (i + inject_Z (Z.of_nat N))%Q)%formula) len')) in *.
          set (l2:= length ((C == i2)%formula
                      :: map (fun i : Q => (C == i)%formula) len')) in *.
          assert (Hl : l1 = l2). { unfold l1, l2. simpl. now rewrite !List.length_map. }
          rewrite <- Hl. auto.
        -- assert (HWFa1: WF_aexp_with_pd (C - inject_Z (Z.of_nat N)) pd1). { 
            apply dom_equiv_preserves_WF_aexp with (pd:= pd); intuition.
            destruct H1 as [Hdom1 Hmu1].
            apply dom_equiv_sym in Hdom1. assumption.
          }
          pose (pd1':= (DAssn_under_pd C (C - inject_Z (Z.of_nat N)) pd1 HWFa1)).
          exists pd1'. intuition.
          ++ simpl. apply Valid_after_DA. assumption.
          ++ destruct H1 as [Hdom1 Hmu1]. split. 
          +++ simpl. apply dom_eq_orb_compat_right. assumption.
          +++ apply DA_step_deter; intuition.
          ++ apply eval_eq_after_assign_shift. assumption.
          ++ simpl. repeat rewrite DA_preserve_sum_prob. assumption.
        ** right. right. destruct Hcase3 as [Hp (pd2 & Hrest)]. 
        split.
        -- set (l1:= length ((C == (i2 + inject_Z (Z.of_nat N))%Q)%formula
                      :: map (fun i : Q => (C == (i + inject_Z (Z.of_nat N))%Q)%formula) len')) in *.
          set (l2:= length ((C == i2)%formula
                      :: map (fun i : Q => (C == i)%formula) len')) in *.
          assert (Hl : l1 = l2). { unfold l1, l2. simpl. now rewrite !List.length_map. }
          rewrite <- Hl. auto.
        -- assert (HWFa2: WF_aexp_with_pd (C - inject_Z (Z.of_nat N)) pd2). { 
            apply dom_equiv_preserves_WF_aexp with (pd:= pd); intuition.
            destruct H1 as [Hdom1 Hmu1].
            apply dom_equiv_sym in Hdom1. assumption. }
          pose (pd2':= (DAssn_under_pd C (C - inject_Z (Z.of_nat N)) pd2 HWFa2)).
          exists pd2'. intuition.
          ++ simpl. apply Valid_after_DA. assumption.
          ++ destruct H1 as [Hdom1 Hmu1]. split. 
          +++ simpl. apply dom_eq_orb_compat_right. assumption.
          +++ apply DA_step_deter; intuition.
          ++ apply IHlen; assumption.
          ++ simpl. repeat rewrite DA_preserve_sum_prob. assumption.
  Qed.

  Lemma seq_succ_start :
    forall (start len : nat),
      seq (S start) len = map S (seq start len).
  Proof.
    intros start len; revert start.
    induction len as [|len IH]; intro start.
    - simpl. reflexivity.
    - simpl.                      (* seq start (S len) = start :: seq (S start) len *)
      rewrite IH.                 (* seq (S (S start)) len = map S (seq (S start) len) *)
      reflexivity.
  Qed.

  Lemma rangeQ_shift : forall (N NV C:nat) ,
    map (fun i : Q => (C == (i + inject_Z (Z.of_nat N))%Q)%formula) (rangeQ 0 NV) = 
    map (fun i : Q => (C == i)%formula) (rangeQ N NV).
  Proof.
    intros. unfold rangeQ. 
    rewrite !map_map. revert N0.
    induction NV; intros.
    - simpl. auto.
    - simpl. f_equal. 
      + rewrite <- inject_Z_plus. rewrite Z.add_0_l. reflexivity.
      + rewrite seq_succ_start. rewrite map_map. 
        eapply eq_trans with (y:= map (fun x : nat =>
                                          (C0 == (inject_Z (Z.of_nat x) + inject_Z (Z.of_nat (S N0)))%Q)%formula) (seq 0 NV)).
        * apply map_ext; intro x. 
          rewrite !Nat2Z.inj_succ. repeat rewrite <- inject_Z_plus. 
          repeat rewrite Z.add_succ_l.
          repeat rewrite Z.add_succ_r. auto.
        * apply IHNV. 
  Qed.

  Lemma text: forall (N NV C: nat),
    unif_sugar (map (fun i : Q => (C == i)%formula) (rangeQ N NV)) =
    unif_sugar (map (fun i : Q => (C == (i + inject_Z (Z.of_nat N))%Q)%formula) (rangeQ 0 NV)).
  Proof.
    intros. rewrite <- rangeQ_shift. auto.
  Qed.


  Lemma uniform_after_assign_shift: forall (C N NV : nat) pd (HWFa :  WF_aexp_with_pd (C - inject_Z (Z.of_nat N)) pd),
    Valid_dist (mu pd) ->
    [[unif_sugar (pf_C_uniform C N NV)]] pd ->
    [[unif_sugar (pf_C_uniform C 0 NV)]]
    (DAssn_under_pd C (C - inject_Z (Z.of_nat N)) pd HWFa).
  Proof.
    intros C N NV pd HWFa HV H. 
    unfold pf_C_uniform in *. rewrite (text N NV) in H.
    apply unif_sugar_after_assign_shift_index with (len:= (rangeQ 0 NV)); try assumption.
  Qed.

  Lemma testV: forall (V: nat) (N: Q) pd (HWFa: WF_aexp_with_pd (V - N) pd), 
    [[V - Aco N < Aco N]] pd -> 
    [[V < Aco N]] (DAssn_under_pd V (V - Aco N) pd HWFa).
  Proof.
    intros V N pd HWFa H. destruct H. split.
    - simpl. simpl in H. rewrite orb_domain_nil_r in H. 
      apply dom_subset_trans with (l1:= dom pd); try assumption.
      apply dom_subset_orb_snd_l_r. 
    - intros. apply in_supp_DAssn_under_dstate_inv in H1. 
      destruct H1 as [st0 (Hin0 & Heq)]. apply H0 in Hin0.
      destruct Hin0. split.
      + simpl. simpl in H1. rewrite orb_domain_nil_r in H1.
        apply dom_subset_trans with (l1:= return_domain st0); try assumption.
        apply st_eq_implies_dom_equiv in Heq. 
        apply dom_equiv_sym in Heq.
        apply dom_subset_eq_compat_left with 
          (X:= return_domain (update st0 V (evalA_st (V - N) st0))); try assumption.
        apply update_subst_implies_dom_eq.
      + destruct (evalB_st (V - N < N) st0) eqn: Hb; try contradiction.
        simpl in Hb. simpl. simpl in Heq.
        apply st_eq_implies_get_eq with (x:= V) in Heq.
        rewrite get_update_eq in Heq. 
        destruct (negb (Qle_bool N (get V st))) eqn: Hcontra; try auto.
        apply negb_false_iff in Hcontra. 
        rewrite Heq in Hcontra. rewrite Hcontra in Hb. inversion Hb.
  Qed.

  Lemma testVmult: forall (V: nat) (p N: Q) pd (HWFa: WF_aexp_with_pd (p * V) pd), 
    [[V < Aco N]] pd -> 
    (0 < p)%Q ->
    [[V < p * Aco N]] (DAssn_under_pd V (p * V) pd HWFa).
  Proof.
    intros V p N pd HWFa H Hp. destruct H. split.
    - simpl. simpl in H. 
      apply dom_subset_trans with (l1:= dom pd); try assumption.
      apply dom_subset_orb_snd_l_r. 
    - intros. apply in_supp_DAssn_under_dstate_inv in H1. 
      destruct H1 as [st0 (Hin0 & Heq)]. apply H0 in Hin0.
      destruct Hin0. split.
      + simpl. simpl in H1. 
        apply dom_subset_trans with (l1:= return_domain st0); try assumption.
        apply st_eq_implies_dom_equiv in Heq. 
        apply dom_equiv_sym in Heq.
        apply dom_subset_eq_compat_left with 
          (X:= return_domain (update st0 V (evalA_st (p * V) st0))); try assumption.
        apply update_subst_implies_dom_eq.
      + destruct (evalB_st (V < N) st0) eqn: Hb; try contradiction.
        simpl in Hb. simpl. simpl in Heq.
        apply st_eq_implies_get_eq with (x:= V) in Heq.
        rewrite get_update_eq in Heq. 
        destruct (negb (Qle_bool (p * N) (get V st))) eqn: Hcontra; try auto.
        apply negb_false_iff in Hcontra. 
        rewrite Heq in Hcontra. apply Qle_bool_iff in Hcontra.
        apply (proj1 (Qmult_le_l N (get V st0) p Hp)); try assumption. 
        apply Qgt_alt. rewrite negb_true_iff in Hb. 
        apply Qnot_le_lt. intuition. 
        apply (proj2 (Qle_bool_iff N (get V st0))) in H3.
        rewrite H3 in Hb. inversion Hb.
  Qed.

  Lemma in_supp_res_inv : forall st mu X,
    is_in_supp st (supp_mu (mu \| X)) = true ->
    exists st0,
      is_in_supp st0 (supp_mu mu) = true /\
      (res_st_to_X st0 X == st)%state.
  Proof.
    intros. induction mu as [|(s,p) mu'].
    - simpl in *. inversion H.
    - simpl in H. unfold supp_mu in H. simpl in H.
      rewrite insert_st_pair_fst_eq_insert_st in H.
      rewrite in_supp_insert_eq in H. 
      apply orb_true_iff in H. destruct H.
      + exists s. intuition. 
        * apply in_supp_mu_cons_head.
        * rewrite state_eq_sym. intuition.
      + apply IHmu' in H. destruct H as [st0 (H0 & H1)]. 
        exists st0; intuition. apply in_supp_mu_cons_r. auto.
  Qed.

  Lemma sing_subset_nil_contra: forall X, 
    singleton_bool_list X ⊆ nil -> False.
  Proof.
    intros X H. destruct X as [|x]; try inversion H.
    induction x. 
    - simpl in H1. inversion H1.
    - simpl in *. apply IHx; try assumption.
  Qed.


  Lemma get_res_st_to_X: forall st X V,  
    (singleton_bool_list V ⊆ X)%domain -> 
    (get V (res_st_to_X st X) == get V st)%Q.
  Proof. 
    intros st X V. generalize dependent V. generalize dependent X. 
    induction st as [|q st']; intros.
    - simpl. reflexivity.
    - destruct X as [|x1 X']. 
      + destruct V0. 
        * simpl in H. inversion H.
        * apply sing_subset_nil_contra in H. contradiction.
      + destruct V0. 
        * simpl. destruct q; try reflexivity. 
          destruct x1; try reflexivity. 
          simpl in H. inversion H.
        * simpl in H. destruct q; try reflexivity. 
        ** simpl. destruct x1; intuition.
        ** simpl. apply IHst'; try assumption.
  Qed. 

  Lemma combine_Identify_pd: forall pd, 
    (mu pd == mu Identify_pd ⊗ mu pd)%dist_state.
  Proof.
    intros pd. destruct pd as [dom mu HPD]. cbn.
    rewrite app_nil_r. induction mu as [|(s,p) mu'].
    - apply dst_equiv_refl.
    - rewrite dst_cons_eq_add. 
      rewrite dst_cons_eq_add with (mu:= ((fix combine_op_helper (mu2 : dist_state) : dist_state :=
        match mu2 with
        | [] => []
        | (s2, p2) :: nl2 => (s2, (1 * p2)%R) :: combine_op_helper nl2
        end) mu')%dist_state).
      apply dst_add_preserves_equiv.
      + rewrite Rmult_1_l. apply dst_equiv_refl.
      + apply IHmu'. inversion HPD; subst. intuition.
  Qed.

  Lemma Pand_conj phi0 phi1: 
  [[phi0 ∧ phi1]] <<->> ([[phi0]] /\ [[phi1]]).
  Proof.
    intros. 
    unfold assert_implies in *. split; intros; destruct H1; split; try assumption.
  Qed.

  Lemma eval_eq_after_assign_shift_with_Bit : 
    forall (i:Q) (C Bit: nat) pd (HWFa : WF_aexp_with_pd (2%Q * C + Bit) pd), 
      (Bit =? C) = false ->
      [[(C == Aco i)%formula ]] pd ->
      [[(C == 2%Q * i + Bit)%formula ]] (DAssn_under_pd C (2%Q * C + Bit) pd HWFa).
  Proof.
    intros i C Bit pd HWFa HNeq H. destruct H. simpl in H. split; intuition.
    - simpl. apply dom_subset_trans with (l1:= dom pd); try assumption.
      apply dom_subset_orb_dom_r. apply dom_subset_refl.
    - apply in_supp_DAssn_under_dstate_inv in H1. 
      destruct H1 as [st0 (Hin & Heq)].
      assert (Hst0: (return_domain st0 == dom pd)%domain) by (apply in_supp_return_domain_eq in Hin; assumption).
      apply H0 in Hin. destruct Hin. simpl in H1. split.
      + simpl. apply dom_subset_orb_fst_iff. intuition. 
        * apply dom_equiv_sym in Hst0.
          apply dom_subset_eq_compat_left with (Y:= return_domain st0) in H; try assumption.
          apply st_eq_implies_dom_equiv in Heq. 
          assert (Htmp: (return_domain st0) ⊆ 
                      (return_domain (update st0 C (evalA_st (2%Q * C + Bit) st0)))) 
                      by apply update_subst_implies_dom_eq.
          apply dom_equiv_sym in Heq.
          apply dom_subset_eq_compat_left with (X:= 
              return_domain (update st0 C (evalA_st (2%Q * C + Bit) st0))); try assumption.
          apply dom_subset_trans with (l1:= return_domain st0); try assumption.
          apply dom_subset_orb_fst_iff in H. intuition.
        * unfold WF_aexp_with_pd in HWFa.  
          apply dom_equiv_sym in Hst0.
          apply dom_subset_eq_compat_left with (Y:= return_domain st0) in HWFa; try assumption.
          apply st_eq_implies_dom_equiv in Heq. 
          assert (Htmp: (return_domain st0) ⊆ 
                      (return_domain (update st0 C (evalA_st (2%Q * C + Bit) st0)))) 
                      by apply update_subst_implies_dom_eq.
          apply dom_equiv_sym in Heq.
          apply dom_subset_eq_compat_left with (X:= return_domain (update st0 C (evalA_st (2%Q * C + Bit) st0))); try assumption.
          apply dom_subset_trans with (l1:= return_domain st0); try assumption.
          cbn [get_variables_in_aexp] in HWFa. rewrite orb_domain_nil_l in HWFa.
          apply dom_subset_orb_fst_iff in HWFa. intuition.
      + simpl in H2. cbn [evalB_st]. cbn [evalA_st] in *. 
        destruct (Qeq_bool (get C st0) i) eqn:Hb; try contradiction.
        apply Qeq_bool_iff in Hb. 
        assert (Heq' : (st == update st0 C (2 * (get C st0) + get Bit st0))%state) by auto.
        apply st_eq_implies_get_eq with (x:= C) in Heq. 
        rewrite get_update_eq in Heq.
        apply st_eq_implies_get_eq with (x:= Bit) in Heq'. 
        rewrite update_neq in Heq'; auto. 
        rewrite <- Heq' in Heq. rewrite Hb in Heq.  
        apply Qeq_bool_iff in Heq.   
        rewrite Heq. apply I.
  Qed.


  Lemma eq_after_assign_i_shift_with_Bit : 
    forall (i:Q) (C Bit: nat) pd (HWFa : WF_aexp_with_pd (2%Q * i + Bit) pd), 
      (Bit =? C) = false ->
      [[(C == Aco i)%formula ]] pd ->
      [[(C == 2%Q * i + Bit)%formula ]] (DAssn_under_pd C (2%Q * i + Bit) pd HWFa).
  Proof.
    intros i C Bit pd HWFa HNeq H. destruct H. simpl in H. split; intuition.
    - simpl. apply dom_subset_trans with (l1:= dom pd); try assumption.
      + unfold WF_aexp_with_pd in HWFa. apply dom_subset_orb_fst_iff. 
        apply dom_subset_orb_fst_iff in H. intuition.  
      + apply dom_subset_orb_dom_r. apply dom_subset_refl.
    - apply in_supp_DAssn_under_dstate_inv in H1. 
      destruct H1 as [st0 (Hin & Heq)].
      assert (Hst0: (return_domain st0 == dom pd)%domain) by (apply in_supp_return_domain_eq in Hin; assumption).
      apply H0 in Hin. destruct Hin. simpl in H1. split.
      + simpl. apply dom_subset_orb_fst_iff. intuition. 
        * apply dom_equiv_sym in Hst0.
          apply dom_subset_eq_compat_left with (Y:= return_domain st0) in H; try assumption.
          apply st_eq_implies_dom_equiv in Heq. 
          assert (Htmp: (return_domain st0) ⊆ 
                      (return_domain (update st0 C (evalA_st (2%Q * i + Bit) st0)))) 
                      by apply update_subst_implies_dom_eq.
          apply dom_equiv_sym in Heq.
          apply dom_subset_eq_compat_left with (X:= return_domain (update st0 C (evalA_st (2%Q * i + Bit) st0))); try assumption.
          apply dom_subset_trans with (l1:= return_domain st0); try assumption.
          apply dom_subset_orb_fst_iff in H. intuition.
        * unfold WF_aexp_with_pd in HWFa.  
          apply dom_equiv_sym in Hst0.
          apply dom_subset_eq_compat_left with (Y:= return_domain st0) in HWFa; try assumption.
          apply st_eq_implies_dom_equiv in Heq. 
          assert (Htmp: (return_domain st0) ⊆ 
                      (return_domain (update st0 C (evalA_st (2%Q * i + Bit) st0)))) 
                      by apply update_subst_implies_dom_eq.
          apply dom_equiv_sym in Heq.
          apply dom_subset_eq_compat_left with (X:= return_domain (update st0 C (evalA_st (2%Q * i + Bit) st0))); try assumption.
          apply dom_subset_trans with (l1:= return_domain st0); try assumption.
      + simpl in H2. cbn [evalB_st]. cbn [evalA_st] in *. 
        destruct (Qeq_bool (get C st0) i) eqn:Hb; try contradiction.
        apply Qeq_bool_iff in Hb. 
        assert (Heq' : (st == update st0 C (2 * i + get Bit st0))%state) by auto.
        apply st_eq_implies_get_eq with (x:= C) in Heq. 
        rewrite get_update_eq in Heq.
        apply st_eq_implies_get_eq with (x:= Bit) in Heq'. 
        rewrite update_neq in Heq'; auto. 
        rewrite <- Heq' in Heq. 
        apply Qeq_bool_iff in Heq. rewrite Heq. apply I.
  Qed.

  Lemma update_C_preserves_bit : 
    forall (a:aexp) (q: Q) (C BIT: nat) pd (HWFa : WF_aexp_with_pd a pd), 
      (BIT =? C) = false ->
      [[(BIT == q)%formula ]] pd ->
      [[(BIT == q)%formula ]] (DAssn_under_pd C a pd HWFa).
  Proof.
    intros a q C BIT pd HWFa HNeg H. destruct H. simpl in H. split; intuition.
    - simpl. apply dom_subset_trans with (l1:= dom pd); try assumption.
      apply dom_subset_orb_dom_r. apply dom_subset_refl.
    - apply in_supp_DAssn_under_dstate_inv in H1. 
      destruct H1 as [st0 (Hin & Heq)].
      assert (Hst0: (return_domain st0 == dom pd)%domain) by (apply in_supp_return_domain_eq in Hin; assumption).
      apply H0 in Hin. destruct Hin. simpl in H1. split.
      + simpl. apply dom_equiv_sym in Hst0.
        apply dom_subset_eq_compat_left with (Y:= return_domain st0) in H; try assumption.
        apply st_eq_implies_dom_equiv in Heq. 
          assert (Htmp: (return_domain st0) ⊆ 
                      (return_domain (update st0 C (evalA_st a st0)))) 
                      by apply update_subst_implies_dom_eq.
        apply dom_equiv_sym in Heq.
        apply dom_subset_eq_compat_left with (X:= 
              return_domain (update st0 C (evalA_st a st0))); try assumption.
        apply dom_subset_trans with (l1:= return_domain st0); try assumption.
      + simpl in H2. cbn [evalB_st]. cbn [evalA_st] in *. 
        destruct (Qeq_bool (get BIT st0) q) eqn:Hb; try contradiction.
        apply Qeq_bool_iff in Hb. 
        assert (Heq' : (st == update st0 C (evalA_st a st0))%state) by auto.
        apply st_eq_implies_get_eq with (x:= BIT) in Heq. 
        rewrite update_neq in Heq; auto. 
        apply st_eq_implies_get_eq with (x:= BIT) in Heq'. 
        rewrite update_neq in Heq'; auto. 
        rewrite Hb in Heq.  
        apply Qeq_bool_iff in Heq.   
        rewrite Heq. apply I.
  Qed.

  Lemma eval_eq_after_assign : forall (i:Q) (C Bit: nat) pd (HWFa : WF_aexp_with_pd (2%Q * C + Bit) pd),
    Valid_dist (mu pd) -> (Bit =? C) = false ->
    [[c_i_and_bit C Bit i]] pd ->
    [[c2_i_and_bit C Bit i]] (DAssn_under_pd C (2%Q * C + Bit) pd HWFa).
  Proof.
    intros i C Bit pd. 
    unfold c_i_and_bit, c2_i_and_bit in *. 
    intros HWFa HValid HNeq H. destruct H as [Hcase1 | H].
    - left. intuition. 
      destruct H0 as (pd1 & pd2 & HValid1 & Hvalid2 & Hdom1 & Hdom2 & Hsem1 & Hsem2 & Hsum1 & Hsum2 & Hmu).

      assert (HWFa1: WF_aexp_with_pd (2%Q * C + Bit) pd1). { 
            apply dom_equiv_preserves_WF_aexp with (pd:= pd); intuition.
            apply dom_equiv_sym in Hdom1. assumption.
          }
      pose (pd1':= (DAssn_under_pd C (2%Q * C + Bit) pd1 HWFa1)).
      assert (HWFa2: WF_aexp_with_pd (2%Q * C + Bit) pd2). { 
            apply dom_equiv_preserves_WF_aexp with (pd:= pd); intuition.
            apply dom_equiv_sym in Hdom2. assumption.
          }
      pose (pd2':= (DAssn_under_pd C (2%Q * C + Bit) pd2 HWFa2)).

      exists pd1', pd2'. intuition.
      + simpl. apply Valid_after_DA. auto.
      + simpl. apply Valid_after_DA. auto.
      + simpl. apply dom_eq_orb_compat_right. assumption.
      + simpl. apply dom_eq_orb_compat_right. assumption.
      + destruct Hsem1. split.
        * unfold pd1'. eapply eval_eq_after_assign_shift_with_Bit; auto.
        * apply update_C_preserves_bit; auto.
      + destruct Hsem2. split.
        * unfold pd2'. eapply eval_eq_after_assign_shift_with_Bit; auto.
        * apply update_C_preserves_bit; auto.
      + simpl. repeat rewrite DA_preserve_sum_prob. assumption.
      + simpl. repeat rewrite DA_preserve_sum_prob. assumption. 
      + simpl. apply DA_step_deter with (n:= C) 
                                        (a:= (2%Q * C + Bit)) in Hmu; intuition.
        -- apply dst_equiv_trans with (mu1:= (DAssn_under_dstate (/ 2 * mu pd1 + (1 - / 2) * mu pd2) C
                                              (2%Q * C + Bit))%dist_state); try assumption.
          rewrite DAss_eq_under_addAndmult. apply dst_add_preserves_equiv.
        --- apply dst_equiv_refl.
        --- apply dst_equiv_refl.
        -- apply Valid_linear; try assumption; try lra.
    - destruct H as [Hcase2 | Hcase3].
      * right. left. 
        destruct Hcase2 as [Hp (pd1 & Hrest)]. 
        split; try lra.
      * right. right. destruct Hcase3 as [Hp (pd2 & Hrest)]. 
        split; try lra.
  Qed.

  Lemma unif_sugar_after_assign_shift_aexp: 
  forall (C N NV Bit: nat) len pd (HWFa : WF_aexp_with_pd (2%Q * C + Bit) pd),
    Valid_dist (mu pd) -> (Bit =? C) = false ->
    [[unif_sugar (map (fun i : Q => c_i_and_bit C Bit i) len)]] pd ->
    [[unif_sugar (map (fun i : Q => c2_i_and_bit C Bit i) len)]] (DAssn_under_pd C (2%Q * C + Bit) pd HWFa).
  Proof.
    intros C N NV Bit len pd HWFa HValid HNeg H. 
    (* unfold c_i_and_bit, c2_i_and_bit in *. *)
    generalize dependent pd.
    induction len as [|i1 len]; intros.
    - cbn [map] in *. cbn [unif_sugar] in *. destruct H. 
      split; intuition. apply in_supp_DAssn_under_dstate_inv in H1. 
      destruct H1 as [st0 (Hin & Heq)].
      apply H0 in Hin. destruct Hin. split; simpl; auto.
    - destruct len as [|i2 len']. 
      + cbn [map] in *. cbn [unif_sugar] in *. 
        apply eval_eq_after_assign; try assumption.
      + cbn [map] in *. destruct H as [Hcase1 | H].
        * left. destruct Hcase1 as (Hp & pd1 & pd2 & Hrest). 
          destruct Hrest as (Hv1 & Hv2 & Hdom1 & Hdom2 & Hsem1 & Hsem2 & Hsum1 & Hsum2 & Hmu).
          set (l1:= length (c_i_and_bit C Bit i2
                      :: map (fun i : Q => c_i_and_bit C Bit i) len')) in *.
          set (l2:= length (c2_i_and_bit C Bit i2
                      :: map (fun i : Q => c2_i_and_bit C Bit i) len')) in *.
          assert (Hl : l1 = l2). { unfold l1, l2. simpl. now rewrite !List.length_map. }
          split. 
          ** rewrite Hl in Hp. exact Hp.
          ** assert (HWFa1: WF_aexp_with_pd (2%Q * C + Bit) pd1). { 
              apply dom_equiv_preserves_WF_aexp with (pd:= pd); intuition.
              apply dom_equiv_sym in Hdom1. assumption. }
            assert (HWFa2: WF_aexp_with_pd (2%Q * C + Bit) pd2). { 
            apply dom_equiv_preserves_WF_aexp with (pd:= pd); intuition.
              apply dom_equiv_sym in Hdom2. assumption.
           }
            pose (pd1':= (DAssn_under_pd C (2%Q * C + Bit) pd1 HWFa1)).
            pose (pd2':= (DAssn_under_pd C (2%Q * C + Bit) pd2 HWFa2)).
            exists pd1', pd2'. intuition.
            ++ simpl. apply Valid_after_DA. assumption.
            ++ simpl. apply Valid_after_DA. assumption.
            ++ simpl. apply dom_eq_orb_compat_right. assumption.
            ++ simpl. apply dom_eq_orb_compat_right. assumption.
            ++ apply eval_eq_after_assign; assumption.
            ++ apply IHlen; try assumption.
            ++ simpl. repeat rewrite DA_preserve_sum_prob. assumption.
            ++ simpl. repeat rewrite DA_preserve_sum_prob. assumption.
            ++ rewrite <- Hl. 
              apply DA_step_deter with (n:= C) 
                                       (a:= (2%Q * C + Bit)) in Hmu; intuition.
              -- apply dst_equiv_trans with (mu1:= (DAssn_under_dstate (/ INR (S l1) * mu pd1 + 
                    (1 - / INR (S l1)) * mu pd2) C (2%Q * C + Bit))%dist_state); try assumption.
                rewrite DAss_eq_under_addAndmult. apply dst_add_preserves_equiv.
              --- apply dst_equiv_refl.
              --- apply dst_equiv_refl.
             -- apply Valid_linear; try assumption; try lra.
        * destruct H as [Hcase2 | Hcase3].
        ** right. left. destruct Hcase2 as [Hp (pd1 & Hrest)]. 
        split.
        -- set (l1:= length (c_i_and_bit C Bit i2
                      :: map (fun i : Q => c_i_and_bit C Bit i) len')) in *.
          set (l2:= length (c2_i_and_bit C Bit i2
                      :: map (fun i : Q => c2_i_and_bit C Bit i) len')) in *.
          assert (Hl : l1 = l2). { unfold l1, l2. simpl. now rewrite !List.length_map. }
          rewrite <- Hl. auto.
        -- assert (HWFa1: WF_aexp_with_pd (2%Q * C + Bit) pd1). { 
            apply dom_equiv_preserves_WF_aexp with (pd:= pd); intuition.
            destruct H1 as [Hdom1 Hmu1].
            apply dom_equiv_sym in Hdom1. assumption.
          }
          pose (pd1':= (DAssn_under_pd C (2%Q * C + Bit) pd1 HWFa1)).
          exists pd1'. intuition.
          ++ simpl. apply Valid_after_DA. assumption.
          ++ destruct H1 as [Hdom1 Hmu1]. split. 
          +++ simpl. apply dom_eq_orb_compat_right. assumption.
          +++ apply DA_step_deter; intuition.
          ++ apply eval_eq_after_assign; assumption.
          ++ simpl. repeat rewrite DA_preserve_sum_prob. assumption.
        ** right. right. destruct Hcase3 as [Hp (pd2 & Hrest)]. 
        split.
        --set (l1:= length (c_i_and_bit C Bit i2
                      :: map (fun i : Q => c_i_and_bit C Bit i) len')) in *.
          set (l2:= length (c2_i_and_bit C Bit i2
                      :: map (fun i : Q => c2_i_and_bit C Bit i) len')) in *.
          assert (Hl : l1 = l2). { unfold l1, l2. simpl. now rewrite !List.length_map. }
          rewrite <- Hl. auto.
        -- assert (HWFa2: WF_aexp_with_pd (2%Q * C + Bit) pd2). { 
            apply dom_equiv_preserves_WF_aexp with (pd:= pd); intuition.
            destruct H1 as [Hdom1 Hmu1].
            apply dom_equiv_sym in Hdom1. assumption. }
          pose (pd2':= (DAssn_under_pd C (2%Q * C + Bit) pd2 HWFa2)).
          exists pd2'. intuition.
          ++ simpl. apply Valid_after_DA. assumption.
          ++ destruct H1 as [Hdom1 Hmu1]. split. 
          +++ simpl. apply dom_eq_orb_compat_right. assumption.
          +++ apply DA_step_deter; intuition.
          ++ apply IHlen; assumption.
          ++ simpl. repeat rewrite DA_preserve_sum_prob. assumption.
  Qed. 

  Lemma df_sem_minus: 
    forall pd0 pd1 pd df, 
      Valid_dist (mu pd0) -> Valid_dist (mu pd1) -> Valid_dist (mu pd) ->
      (dom pd0 == dom pd)%domain -> (dom pd1 == dom pd)%domain -> 
      (mu pd == mu pd0 + mu pd1)%dist_state ->  
      Valid_dist (mu pd0 + mu pd1)%dist_state ->
      [[Pdeter df]] pd ->
      [[Pdeter df]] pd1.
  Proof.
    intros pd0 pd1 pd df HWF0 HWF1 HWF Hdom0 Hdom1 Hmu HValid Hsem.
    destruct pd0 as [dom0 mu0 HPD0]. destruct pd1 as [dom1 mu1 HPD1]. destruct pd as [dom mu HPD].
    simpl in *. destruct Hsem as [Hsub Hsem]. split.
    - apply dom_subset_eq_compat_left with (X:= (dom)); try assumption.
      apply dom_equiv_sym. auto.
    - intros. 
      assert (Hsupp: (supp_mu mu == supp_mu (mu0 + mu1)%dist_state)%supp). { 
        apply dst_equiv_implies_beq_supp; intuition. }   
      apply in_supp_r_if_subset with (ls1:= supp_mu mu) in H.
      + apply Hsem; intuition.
      + apply supp_eq_implies_subset_conj in Hsupp. destruct Hsupp.
        apply supp_subset_trans with (ls1:= supp_mu (mu0 + mu1)%dist_state); 
          try apply Sort_supp_if_WF_supp; intuition.
        apply supp_mu_subset_decom_add_r. 
  Qed.

  Lemma unif_sugar_conj: forall df lf pd C,
    Valid_dist (mu pd) -> well_defined_Pf (Pdeter df) ->
    [[unif_sugar (map (fun i : Q => (C == i)%formula) lf) ∧ (Pdeter df)]] pd -> 
    [[unif_sugar (map (fun i : Q => (C == i) ∧ (Pdeter df)) lf)]] pd.
  Proof.
    intros df lf pd C. intros HValid HWD.
    generalize dependent pd. induction lf as [| f1 lf' IHlf]; intros.
    - simpl in *. intuition.
    - destruct lf' as [| f2 lf']. 
      + unfold unif_sugar; cbn in *. intuition.
      + destruct H as [Hsugar Hdf]. destruct Hsugar. 
        * left. destruct H as [Hp H]. destruct H. destruct H.
          rewrite length_map in *.
          set (l := / INR (S (length (f2 :: lf')))) in *.
          split; try lra.
          exists x, x0. intuition. 
          -- split; intuition. 
            assert (Hdom: dom x == dom x0). { apply dom_equiv_sym in H4. apply dom_equiv_trans with (l1:= dom pd); intuition. }
            assert (Heq: (pd_add (cofe_pd x l) (cofe_pd x0 (1-l)) Hdom) ≡ pd).
            ++ split; simpl; intuition. apply dst_equiv_sym. auto.
            ++ apply pd_equiv_preserves_sem with (phi:= Pdeter df) in Heq; intuition.
            ** apply df_sem_decom in Heq; intuition.
            ** simpl. apply Valid_linear; auto with *. lra.
          -- apply IHlf; intuition. split; intuition.
            assert (Hdom: dom x == dom x0). { apply dom_equiv_sym in H4. apply dom_equiv_trans with (l1:= dom pd); intuition. }
            assert (Heq: (pd_add (cofe_pd x l) (cofe_pd x0 (1-l)) Hdom) ≡ pd).
            ++ split; simpl; intuition. apply dst_equiv_sym. auto.
            ++ apply pd_equiv_preserves_sem with (phi:= Pdeter df) in Heq; intuition.
            ** apply df_sem_decom in Heq; intuition.
            ** simpl. apply Valid_linear; auto with *. lra.
        * destruct H as [H | H].
        ** right. left. intuition. 
        -- rewrite !length_map. rewrite !length_map in H0. auto.
        -- destruct H1. exists x. intuition. split; intuition.
          apply pd_equiv_preserves_sem with (pd0:= pd); intuition.
        ** right. right. intuition. 
        -- rewrite !length_map. rewrite !length_map in H0. auto.
        -- destruct H1. exists x. intuition. apply IHlf; intuition.
          split; intuition.
          apply pd_equiv_preserves_sem with (pd0:= pd); intuition.
  Qed.

  Lemma unif_sugar_merge: forall pd C Bit len, 
    Valid_dist (mu pd) -> dst_inject_Z (mu pd) ->
    [[unif_sugar (map (fun i : Q => (C == i) ∧ (Bit == 0%Q)) len)
    ⊕[ / 2] unif_sugar (map (fun i : Q => (C == i) ∧ (Bit == 1%Q)) len)]] pd -> 
    [[unif_sugar (map (fun i : Q => (C == i) ∧ (Bit == 0%Q) ⊕[ / 2] (C == i) ∧ (Bit == 1%Q)) len)]] pd.
  Proof.
    intros pd C Bit len HV HZ H. generalize dependent pd. 
    induction len as [| n1 len' IHlen]; intros.
    - cbn [map] in *. cbn [unif_sugar] in *. apply Pplus_same in H; intuition.
      + apply WD_Pplus; try apply WD_Pdeter, WD_Dpred. lra.
      + simpl. auto.
    - destruct len' as [| n2 len']. 
      + cbn [map] in *. cbn [unif_sugar] in *. intuition.
      + cbn [map] in H. destruct H. 
      * destruct H. destruct H0. destruct H0. intuition.
        cbn [map]. left. 
        set (l:= / INR
            (S
            (length
            ((C == n2) ∧ (Bit == 0%Q) ⊕[ / 2] (C == n2) ∧ (Bit == 1%Q)
            :: map (fun i : Q => (C == i) ∧ (Bit == 0%Q) ⊕[ / 2] (C == i) ∧ (Bit == 1%Q)) len')))) in *.
        split; try apply inv_INR_S_length_gt_0_and_lt_1.
        destruct H5.
        ** set (l0:= / INR (S (length ((C == n2) ∧ (Bit == 0%Q) :: map (fun i : Q => (C == i) ∧ (Bit == 0%Q)) len')))) in *.
        
        destruct H6. 
        -- set (l1:= / INR (S (length ((C == n2) ∧ (Bit == 1%Q) :: map (fun i : Q => (C == i) ∧ (Bit == 1%Q)) len')))) in *.
          destruct H6. 
          destruct H5, H6. destruct H11 as (pd01 & pd02 & Hsem0).
          destruct H9 as (pd11 & pd12 & Hsem1).
          intuition.
          assert (Hl0: l = l0). {unfold l, l0.  cbn.
                  rewrite !length_map. reflexivity. }
          assert (Hl1: l = l1). {unfold l, l1.  cbn.
                  rewrite !length_map. reflexivity. }
          assert (Hdom1': (dom (cofe_pd pd01 (/ 2)) == dom (cofe_pd pd11 (1-/ 2)))%domain). {
            simpl. apply dom_equiv_sym in H18.
            apply dom_equiv_trans with (l1:= dom x); intuition.
            apply dom_equiv_trans with (l1:= dom pd); intuition.
            apply dom_equiv_sym in H17.
            apply dom_equiv_trans with (l1:= dom x0); intuition.
            apply dom_equiv_sym in H4; intuition.
          }
          pose (pd1':= pd_add (cofe_pd pd01 (/ 2)) (cofe_pd pd11 (1-/ 2)) Hdom1').
          assert (HV1': Valid_dist (mu pd1')). { apply Valid_linear; auto with *. lra. }
          assert (Hdom2': (dom (cofe_pd pd02 (/ 2)) == dom (cofe_pd pd12 (1-/ 2)))%domain). {
            simpl. apply dom_equiv_sym in H19.
            apply dom_equiv_trans with (l1:= dom x); intuition.
            apply dom_equiv_trans with (l1:= dom pd); intuition.
            apply dom_equiv_sym in H17.
            apply dom_equiv_trans with (l1:= dom x0); intuition.
            apply dom_equiv_sym in H4; intuition.
          }
          pose (pd2':= pd_add (cofe_pd pd02 (/ 2)) (cofe_pd pd12 (1-/ 2)) Hdom2').
          assert (HV2': Valid_dist (mu pd2')). { apply Valid_linear; auto with *. lra. }

          exists pd1', pd2'. intuition.
          ++ simpl. apply dom_equiv_trans with (l1:= dom x); intuition.
          ++ simpl. apply dom_equiv_trans with (l1:= dom x); intuition.
          ++ left. intuition.  exists pd01, pd11. intuition; simpl; try apply dom_equiv_refl.
          +++ simpl in Hdom1'. apply dom_equiv_sym. auto.
          +++ rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
            rewrite H24, H25, H7, H8. lra.
          +++ rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult. 
            rewrite H24, H25, H7, H8. lra.
          +++ apply dst_equiv_refl.
          ++ apply IHlen; intuition.
          +++ simpl. apply dst_inject_Z_add; apply dst_mult_inject_Z.
          *** apply dst_implies_inject_Z in H10; intuition.
          --- apply dst_inject_Z_decom in H10. 
              apply dst_implies_inject_Z in H29, H30; intuition.
          ---- apply dst_inject_Z_decom in H29. destruct H29.
              apply dst_mult_inject_Z with (p:= (/(1 - l0))%R) in H29. 
              rewrite dst_mult_assoc_eq in H29.
              rewrite <- Rinv_l_sym in H29; try lra. rewrite <- dst_mult_1_l. intuition.
          ---- apply Valid_linear; auto; try lra.
          ---- apply dst_mult_inject_Z with (p:= 2%R) in H31. 
              rewrite dst_mult_assoc_eq in H31.
              replace (2 * (1 - / 2))%R with (1 : R) in H31 by (field; nra).
              rewrite <- dst_mult_1_l. intuition.
          ---- apply Valid_linear; auto; try lra.
          ---- apply dst_mult_inject_Z with (p:= 2%R) in H28. 
              rewrite dst_mult_assoc_eq in H28.
              replace (2 * / 2)%R with (1 : R) in H28 by (field; nra).
              rewrite <- dst_mult_1_l. intuition.
          --- apply Valid_linear; auto; try lra.
          *** apply dst_implies_inject_Z in H10; intuition.
          --- apply dst_inject_Z_decom in H10. 
              apply dst_implies_inject_Z in H29, H30; intuition.
          ---- apply dst_inject_Z_decom in H30. destruct H30.
              apply dst_mult_inject_Z with (p:= (/(1 - l1))%R) in H30. 
              rewrite dst_mult_assoc_eq in H30.
              rewrite <- Rinv_l_sym in H30; try lra. rewrite <- dst_mult_1_l. intuition.
          ---- apply Valid_linear; auto; try lra.
          ---- apply dst_mult_inject_Z with (p:= 2%R) in H31. 
              rewrite dst_mult_assoc_eq in H31.
              replace (2 * (1 - / 2))%R with (1 : R) in H31 by (field; nra).
              rewrite <- dst_mult_1_l. intuition.
          ---- apply Valid_linear; auto; try lra.
          ---- apply dst_mult_inject_Z with (p:= 2%R) in H28. 
              rewrite dst_mult_assoc_eq in H28.
              replace (2 * / 2)%R with (1 : R) in H28 by (field; nra).
              rewrite <- dst_mult_1_l. intuition.
          --- apply Valid_linear; auto; try lra.
          +++ cbn [map]. left. intuition. 
            exists pd02, pd12. intuition; simpl; try apply dom_equiv_refl.
            *** simpl in Hdom2'. apply dom_equiv_sym. auto.
            *** rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
              rewrite H26, H27, H7, H8. lra.
            *** rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
            rewrite H26, H27, H7, H8. lra.
            *** apply dst_equiv_refl.
          ++ simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
            rewrite H24, H25, H7, H8. lra.
          ++ simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
            rewrite H26, H27, H7, H8. lra.
          ++ apply dst_equiv_trans with (mu1:= (/ 2 * mu x + (1 - / 2) * mu x0)%dist_state); auto.
            simpl. repeat rewrite dst_mult_plus_distr_r_eq. 
            apply dst_equiv_trans with (mu1:= (l * (/ 2 * mu pd01) + (1 - l) * (/ 2 * mu pd02) + 
                              (l * ((1 - / 2) * mu pd11) + (1 - l) * ((1 - / 2) * mu pd12)))%dist_state); 
                              try apply dst_add_shuffle.
            apply dst_add_preserves_equiv; try assumption.
            +++ rewrite Hl0. rewrite dst_mult_comm_eq.
              rewrite dst_mult_comm_eq with (mu:= mu pd02).
              apply dst_mult_preserves_equiv with (p:= /2) in H29.
              apply dst_equiv_trans with (mu1:= (/ 2 * (l0 * mu pd01 + (1 - l0) * mu pd02))%dist_state); try assumption.
              rewrite dst_mult_plus_distr_r_eq. apply dst_equiv_refl.
            +++ rewrite Hl1. rewrite dst_mult_comm_eq.
              rewrite dst_mult_comm_eq with (mu:= mu pd12).
              apply dst_mult_preserves_equiv with (p:= /2) in H30.
              replace (1 - / 2)%R with (/ 2 : R) by nra.
              apply dst_equiv_trans with (mu1:= (/ 2 * (l1 * mu pd11 + (1 - l1) * mu pd12))%dist_state); try assumption.
              rewrite dst_mult_plus_distr_r_eq. apply dst_equiv_refl.
        -- assert (Hcontra: 0 < / INR (S (length ((C == n2) ∧ (Bit == 1%Q) :: map (fun i : Q => (C == i) ∧ (Bit == 1%Q)) len'))) < 1) by apply inv_INR_S_length_gt_0_and_lt_1.
          destruct H6; destruct H6; exfalso; rewrite H6 in Hcontra; lra.
        ** assert (Hcontra: 0 < / INR (S (length ((C == n2) ∧ (Bit == 0%Q) :: map (fun i : Q => (C == i) ∧ (Bit == 0%Q)) len'))) < 1) by apply inv_INR_S_length_gt_0_and_lt_1.
          destruct H5; destruct H5; exfalso; rewrite H5 in Hcontra; lra.
      * destruct H; destruct H; exfalso; nra.
  Qed.
  

  Lemma assert_Odot_implies: 
    assert_Odot [[dist_bit]] ([[V < 2%Q * inject_Z (Z.of_nat N)]] /\ C_unif_depend_to_0v2 C V) ->>
    ([[V < 2%Q * inject_Z (Z.of_nat N)]] /\ C_unif_and_bit_to_0v2 C Bit V).
  Proof.
    unfold assert_implies. intros. destruct H1 as (pd1 & pd2 & Hvar & Hsem).
    destruct Hsem as (HV1 & HV2 & Hsem1 & (Hsem2 & Hsem3) & Hcomb).
    assert (HVcomb: Valid_dist (mu pd1 ⊗ mu pd2)). { apply Valid_after_combine; intuition. }
    assert (HWD: well_defined_Pf (V < 2%Q * inject_Z (Z.of_nat N))). { 
      apply WD_Pdeter; apply WD_Dpred. }
    assert (Hsubdom: get_var_in_Pformular (V < 2%Q * inject_Z (Z.of_nat N)) ⊆ dom pd2). { 
      apply dst_satisfy_df_implies_dom in Hsem2. auto. }
    split.
    - apply sem_preserve_subst_pd with (phi:= 
        (V < 2%Q * inject_Z (Z.of_nat N))%formula) in Hcomb; intuition.
      + apply dst_satisfy_df_implies_dom in Hsem2. 
        apply dom_subset_trans with (l1:= dom pd2); try assumption.
        simpl. apply dom_subset_orb_dom_l. apply dom_subset_refl.
      + assert (HV : dom pd2 ⊆ dom pd1 ∪ dom pd2). { 
          apply dom_subset_orb_dom_l. apply dom_subset_refl. }
        apply df_sem_resV_implies_pd with (V:= dom pd2) (HV:= HV); try assumption.
        pose (p:= sum_probs (mu pd1)). 
        apply sem_mult_cofe with (p:= p) in Hsem2; try assumption.
        * assert (Heq: {| dom := dom pd2;
                          mu := mu {| dom := dom pd1 ∪ dom pd2; mu := mu pd1 ⊗ mu pd2; all_partial := PD_combine_invar_mu pd1 pd2 Hvar |} \|
                          dom pd2;
                          all_partial :=
                          PD_after_res (dom pd2) (dom {|
                          dom := dom pd1 ∪ dom pd2; mu := mu pd1 ⊗ mu pd2;
                          all_partial := PD_combine_invar_mu pd1 pd2 Hvar
                          |})
                          (mu {| dom := dom pd1 ∪ dom pd2; mu := mu pd1 ⊗ mu pd2; all_partial := PD_combine_invar_mu pd1 pd2 Hvar |}) HV
                          (all_partial {| dom := dom pd1 ∪ dom pd2; mu := mu pd1 ⊗ mu pd2; all_partial := PD_combine_invar_mu pd1 pd2 Hvar
                          |})
                        |} ≡ {| dom := dom pd2; mu := (p * mu pd2)%dist_state; all_partial := pd_mult_preserve_PD pd2 p |} ). { 
            split; simpl; try apply dom_equiv_refl.
            apply dst_equiv_trans with (mu1:= (mu pd2 ⊗ mu pd1) \| dom pd2).
            - apply res_sym_with_combine; intuition.
            - apply res_comb_equiv; intuition. rewrite intersect_comm. auto.
          }
          apply pd_equiv_preserves_sem with (pd0:= {| dom := dom pd2; mu := (p * mu pd2)%dist_state; all_partial := pd_mult_preserve_PD pd2 p |}); intuition.
          -- simpl. apply Valid_mult_cofe; try assumption. destruct HV1. auto.
          -- apply Valid_after_resX. apply Valid_after_combine; intuition.
        * destruct HV1. destruct H1. auto.
        * rewrite dst_sum_prob_coef_mult. destruct HV2. destruct HV1. intuition.
        ** apply Rmult_le_pos; assumption.
        ** replace 1 with (1 * 1)%R by ring. 
            apply Rmult_le_compat; try lra; try auto.
    - unfold C_unif_depend_to_0v2 in Hsem3. 
      unfold C_unif_and_bit_to_0v2, Unif_Depend_and, c_i_and_bit.
      destruct Hsem3 as (NV & HNV & Heven & Hin & Hsem).
      exists NV. intuition.
      + destruct pd1 as [dom1 mu1 HPD1]. destruct mu1 as [|(s1,p1) mu1']. 
        {
          simpl in Hcomb. 
          assert (Hpd: (mu pd = [])). {
            destruct Hcomb. simpl in H2, H3.
            apply WF_dst_res_X_nil in H3; try assumption. 
            apply dst_eq_nil_iff. split; try assumption. }
          rewrite Hpd in H1. simpl in H1. inversion H1.
        }
        pose (pd1:={| dom := dom1; mu := (s1, p1) :: mu1'; all_partial := HPD1 |}).
        pose (p:= sum_probs (mu pd1)). 
        assert (Heq: ((mu pd) \| dom pd2 == p * mu pd2)%dist_state). {
          destruct Hcomb. simpl in H2, H3.
          apply Peq_implies_res_eq with (X:= dom pd2) in H3; try apply Valid_after_resX; intuition.
          apply dst_equiv_trans with (mu0:= (mu pd) \| dom pd2) in H3;
            try apply res_to_subset_equiv; try apply dom_subset_orb_dom_l; try apply dom_equiv_refl.
          apply dst_equiv_trans with (mu1:= (mu pd1 ⊗ mu pd2) \| dom pd2); intuition.
          apply dst_equiv_trans with (mu1:= (mu pd2 ⊗ mu pd1) \| dom pd2).
          - apply res_sym_with_combine; intuition.
          - apply res_comb_equiv; intuition. rewrite intersect_comm. auto.
        }
         apply dst_equiv_implies_beq_supp in Heq; intuition.
         * rewrite <- supp_eq_mult_coef in Heq; intuition. 
         ** apply supp_after_res with (V:= dom pd2) in H1.
          rewrite in_supp_beq_supp_compat with (l1:= supp_mu (mu pd2)) in H1; auto.
          specialize (Hin (res_st_to_X st (dom pd2)) H1). 
          rewrite <- Hin. rewrite <- evalA_eq_res_st. 
          rewrite <- evalA_eq_res_st with (s:= (res_st_to_X st (dom pd2))).
          apply st_eq_implies_evalA.
          apply st_conti_res_eq. 
          apply dst_satisfy_df_implies_dom in Hsem2. 
          intuition.
          ** unfold p. destruct HV1. simpl in H2. 
            simpl. simpl in H3. destruct H3. unfold prob_is_positive in H3.
            destruct H3. destruct H2. rewrite <- Rplus_0_l with (r:= 0).
            apply Rplus_lt_le_compat; auto.
            apply positive_sum_ge_0; auto. 
          * apply Valid_after_resX; intuition.
          * destruct HV1. apply Valid_mult_cofe; intuition.

      + unfold mkfs_outer. 
        assert (Htmp: [[(unif_sugar (pf_C_uniform C 0 (NV / 2))) ⊙ dist_bit]] pd). {
          exists pd2, pd1; intuition. 
          assert (Hvar0: dom pd2 ∩∅ dom pd1) by (rewrite intersect_comm; auto).
          exists Hvar0. intuition.
          apply relation_mu_trans with (pd2:= {|
            dom := dom pd1 ∪ dom pd2;
            mu := mu pd1 ⊗ mu pd2;
            all_partial := PD_combine_invar_mu pd1 pd2 Hvar
            |}); intuition.
          - simpl. apply Valid_after_combine; intuition.
          - split; simpl. 
            + rewrite orb_domain_comm. apply dom_subset_refl.
            + set (pd':= {|dom := dom pd1 ∪ dom pd2;
                              mu := mu pd1 ⊗ mu pd2;
                              all_partial := PD_combine_invar_mu pd1 pd2 Hvar
                              |}) in *.
              assert (Htmp: (pd'.(mu) \| (pd'.(dom)) == pd'.(mu))%dist_state) by 
                apply res_pd_to_dom_refl. 
              simpl in Htmp. rewrite orb_domain_comm.
              apply dst_equiv_trans with (mu1:= (mu pd1 ⊗ mu pd2)); try assumption.
              apply combine_sym. 
        }
        assert (HWD_sugar: well_defined_Pf (unif_sugar (pf_C_uniform C 0 (NV / 2)))). {
          apply WD_Unif_MN. apply (Nat.div_str_pos NV 2). lia.
        }
        assert (HWD_bit0: well_defined_Pf (Bit == 0%Q)). { 
          apply WD_Pdeter. apply WD_Dpred. 
        }
        assert (HWD_bit1: well_defined_Pf (Bit == 1%Q)). { 
          apply WD_Pdeter. apply WD_Dpred. 
        }
        assert (Hvar_unif: get_var_in_Pformular
                              (unif_sugar (pf_C_uniform C 0 (NV / 2))) ∩∅ get_var_in_Pformular
                              ((Bit == 0%Q) ⊕[ / 2] (Bit == 1%Q))). {
          simpl. rewrite get_var_in_unif_MN; try lia.
          - destruct (Rle_lt_dec (/ 2) 0) as [Hlt | Hgt]; auto.
            destruct (Rle_lt_dec 1 (/ 2)) as [Hlt' | Hgt']; auto.
          - replace (fst (Nat.divmod NV 1 0 1)) with (NV / 2)%nat by (unfold Nat.div; simpl; reflexivity).
            apply (Nat.div_str_pos NV 2). lia.
        }
        assert (HWD_sugar_bit: well_defined_Pf (unif_sugar (pf_C_uniform C 0 (NV / 2))
                                            ⊙ ((Bit == 0%Q) ⊕[ / 2] (Bit == 1%Q)))). {
          apply WD_Odot; try apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try lra; try assumption.
        }
        unfold dist_bit in Htmp.
        apply OdotD_l in Htmp; try lra; try assumption; intuition.
        * apply OCon_Pplus with (phi0':= unif_sugar (map (fun i : Q => (C == i) ∧ (Bit == 0%Q)) (rangeQ 0 (Nat.div2 NV))))
                                (phi1':= unif_sugar (map (fun i : Q => (C == i) ∧ (Bit == 1%Q)) (rangeQ 0 (Nat.div2 NV)))) in Htmp; 
                                try lra; try assumption.
          ** unfold pf_C_uniform in Htmp. apply unif_sugar_merge; auto.
          ** unfold assert_implies. intros.
            apply OdotO in H3; intuition.  
            unfold pf_C_uniform in H3.
            eapply unif_sugar_conj; intuition. 
            replace (NV / 2)%nat with (Nat.div2 NV) in H3
               by (rewrite Nat.div2_div; reflexivity).
            auto.
          ** unfold assert_implies. intros.
            apply OdotO in H3; intuition.  
            unfold pf_C_uniform in H3.
            eapply unif_sugar_conj; intuition. 
            replace (NV / 2)%nat with (Nat.div2 NV) in H3
               by (rewrite Nat.div2_div; reflexivity).
            auto.

        * simpl. rewrite get_var_in_unif_MN; try lia; auto. 
          replace (fst (Nat.divmod NV 1 0 1)) with (NV / 2)%nat by (unfold Nat.div; simpl; reflexivity).
          apply (Nat.div_str_pos NV 2). lia.
        * simpl. rewrite get_var_in_unif_MN; try lia; auto.
          replace (fst (Nat.divmod NV 1 0 1)) with (NV / 2)%nat by (unfold Nat.div; simpl; reflexivity).
          apply (Nat.div_str_pos NV 2). lia.
  Qed.

  Lemma test_sub: forall len pd, 
    [[unif_sugar 
      (map (fun i : Q => 
        (C == 2%Q * i + Bit) ∧ (Bit == 0%Q) ⊕[ / 2] (C == 2%Q * i + Bit) ∧ (Bit == 1%Q)) 
          len)]] pd ->  
    [[unif_sugar 
      (map (fun i : Q => 
        (C == 2%Q * i + 0%Q) ⊕[ / 2] (C == 2%Q * i + 1%Q)) 
          len)]] pd.
  Proof. 
    intros. generalize dependent pd. induction len as [|f1 len']; intros.
    - cbn [map] in *. intuition.
    - destruct len' as [|f2 len]. 
      + cbn [map] in *. cbn [unif_sugar] in *. destruct H. 
        * destruct H. destruct H0. destruct H0. left. intuition. 
          exists x,x0. intuition.
          ** destruct H5. destruct H5. split; intuition.
          -- cbn [get_var_in_Dformular get_variables_in_bexp get_variables_in_aexp] in *. 
            rewrite orb_domain_nil_r in *. rewrite orb_domain_nil_l in H5. 
            apply dom_subset_trans with (l1:= singleton_bool_list C ∪ singleton_bool_list Bit); auto.
          -- split; intuition.
          ++ cbn [get_var_in_Dformular get_variables_in_bexp get_variables_in_aexp] in *. 
            rewrite orb_domain_nil_r in *. rewrite orb_domain_nil_l in H5.
            apply in_supp_return_domain_eq in H12. apply dom_equiv_sym in H12.
            apply dom_subset_eq_compat_left with (X:= dom x); try assumption. 
            apply dom_subset_trans with (l1:= singleton_bool_list C ∪ singleton_bool_list Bit); auto.
          ++ assert (Hin : is_in_supp st (supp_mu (mu x)) = true) by assumption.
            apply H11 in H12. destruct H12. 
            destruct (evalB_st (C = 2%Q * f1 + Bit) st) eqn: HB; try contradiction.
            destruct H9.
            apply H14 in Hin. destruct Hin.
            destruct (evalB_st (Bit = 0%Q) st) eqn : HB1; try contradiction.
            cbn [evalB_st evalA_st] in *. 
            apply Qeq_bool_iff in HB, HB1. rewrite HB1 in HB.
            apply Qeq_bool_iff in HB. rewrite HB. auto.
          ** destruct H6. destruct H6. split; intuition.
          -- cbn [get_var_in_Dformular get_variables_in_bexp get_variables_in_aexp] in *. 
            rewrite orb_domain_nil_r in *. rewrite orb_domain_nil_l in H6. 
            apply dom_subset_trans with (l1:= singleton_bool_list C ∪ singleton_bool_list Bit); auto.
          -- split; intuition.
          ++ cbn [get_var_in_Dformular get_variables_in_bexp get_variables_in_aexp] in *. 
            rewrite orb_domain_nil_r in *. rewrite orb_domain_nil_l in H6.
            apply in_supp_return_domain_eq in H12. apply dom_equiv_sym in H12.
            apply dom_subset_eq_compat_left with (X:= dom x0); try assumption. 
            apply dom_subset_trans with (l1:= singleton_bool_list C ∪ singleton_bool_list Bit); auto.
          ++ assert (Hin : is_in_supp st (supp_mu (mu x0)) = true) by assumption.
            apply H11 in H12. destruct H12. 
            destruct (evalB_st (C = 2%Q * f1 + Bit) st) eqn: HB; try contradiction.
            destruct H9.
            apply H14 in Hin. destruct Hin.
            destruct (evalB_st (Bit = 1%Q) st) eqn : HB1; try contradiction.
            cbn [evalB_st evalA_st] in *. 
            apply Qeq_bool_iff in HB, HB1. rewrite HB1 in HB.
            apply Qeq_bool_iff in HB. rewrite HB. auto.
        * destruct H; destruct H; exfalso; nra.
      + destruct H. 
        * set (p:= (/ INR (S (length (map (fun i : Q => (C == 2%Q * i + Bit) ∧ (Bit == 0%Q) ⊕[ / 2] 
                                                        (C == 2%Q * i + Bit) ∧ (Bit == 1%Q)) (f2 :: len)))))%R) in *.
          assert (Hp: (0 < p < 1)%R) by (apply inv_INR_S_length_gt_0_and_lt_1).
          destruct H. destruct H0. destruct H0. left. split.
          ** apply inv_INR_S_length_gt_0_and_lt_1.
          ** exists x, x0. intuition.
          -- destruct H7. 
          ++ destruct H7. destruct H11. destruct H11. intuition. 
            left. intuition. exists x1, x2. intuition. 
            { destruct H17. destruct H17. split; intuition.
              - cbn [get_var_in_Dformular get_variables_in_bexp get_variables_in_aexp] in *. 
                rewrite orb_domain_nil_r in *. rewrite orb_domain_nil_l in H17. 
                apply dom_subset_trans with (l1:= singleton_bool_list C ∪ singleton_bool_list Bit); auto.
              - split; intuition.
                + cbn [get_var_in_Dformular get_variables_in_bexp get_variables_in_aexp] in *. 
                  rewrite orb_domain_nil_r in *. rewrite orb_domain_nil_l in H17.
                  apply in_supp_return_domain_eq in H24. apply dom_equiv_sym in H24.
                  apply dom_subset_eq_compat_left with (X:= dom x1); try assumption. 
                  apply dom_subset_trans with (l1:= singleton_bool_list C ∪ singleton_bool_list Bit); auto.
                + assert (Hin : is_in_supp st (supp_mu (mu x1)) = true) by assumption.
                  apply H23 in H24. destruct H24. 
                  destruct (evalB_st (C = 2%Q * f1 + Bit) st) eqn: HB; try contradiction.
                  destruct H21.
                  apply H26 in Hin. destruct Hin.
                  destruct (evalB_st (Bit = 0%Q) st) eqn : HB1; try contradiction.
                  cbn [evalB_st evalA_st] in *. 
                  apply Qeq_bool_iff in HB, HB1. rewrite HB1 in HB.
                  apply Qeq_bool_iff in HB. rewrite HB. auto. 
            }
            { destruct H18. destruct H18. split; intuition.
              - cbn [get_var_in_Dformular get_variables_in_bexp get_variables_in_aexp] in *. 
                rewrite orb_domain_nil_r in *. rewrite orb_domain_nil_l in H18. 
                apply dom_subset_trans with (l1:= singleton_bool_list C ∪ singleton_bool_list Bit); auto.
              - split; intuition.
                + cbn [get_var_in_Dformular get_variables_in_bexp get_variables_in_aexp] in *. 
                  rewrite orb_domain_nil_r in *. rewrite orb_domain_nil_l in H18.
                  apply in_supp_return_domain_eq in H24. apply dom_equiv_sym in H24.
                  apply dom_subset_eq_compat_left with (X:= dom x2); try assumption. 
                  apply dom_subset_trans with (l1:= singleton_bool_list C ∪ singleton_bool_list Bit); auto.
                + assert (Hin : is_in_supp st (supp_mu (mu x2)) = true) by assumption.
                  apply H23 in H24. destruct H24. 
                  destruct (evalB_st (C = 2%Q * f1 + Bit) st) eqn: HB; try contradiction.
                  destruct H21.
                  apply H26 in Hin. destruct Hin.
                  destruct (evalB_st (Bit = 1%Q) st) eqn : HB1; try contradiction.
                  cbn [evalB_st evalA_st] in *. 
                  apply Qeq_bool_iff in HB, HB1. rewrite HB1 in HB.
                  apply Qeq_bool_iff in HB. rewrite HB. auto. 
            }
          ++ destruct H7; destruct H7; exfalso; nra.
          -- cbn. rewrite !length_map. unfold p in H12. 
            rewrite !length_map in H12. simpl in H12. auto. 
        * set (p:= (/ INR (S (length (map (fun i : Q => (C == 2%Q * i + Bit) ∧ (Bit == 0%Q) ⊕[ / 2] 
                                                        (C == 2%Q * i + Bit) ∧ (Bit == 1%Q)) (f2 :: len)))))%R) in *.
          assert (Hp: (0 < p < 1)%R) by (apply inv_INR_S_length_gt_0_and_lt_1).
          destruct H; destruct H; exfalso; rewrite H in Hp; lra.
  Qed.

  Lemma length_flat_map_pair
  (fe fo : Q -> Pformula) (l : list Q) :
  length (flat_map (fun i : Q => [fe i; fo i]) l) = (2 * length l)%nat.
  Proof.
    induction l as [|a l IH]; simpl.
    - lia.
    -  simpl. rewrite IH. simpl. lia.
  Qed.


  Lemma unif_sugar_map_pair_flatten :
  forall pd (L:list Q) (fe fo : Q -> Pformula),
    [[unif_sugar (map (fun i => fe i ⊕[ /2 ] fo i) L)]] pd ->
    [[unif_sugar (flat_map (fun i => [fe i; fo i]) L)]] pd.
  Proof.
    intros. generalize dependent pd. induction L as [|f1 L]; intros.
    - cbn [map] in *. intuition.
    - destruct L as [|f2 L']. 
      + cbn [map] in *. cbn [unif_sugar] in *. destruct H. 
        * destruct H. destruct H0. destruct H0. left. intuition. 
          exists x,x0. intuition.
        * destruct H; destruct H; exfalso; nra. 
      + cbn [map] in *. destruct H.
        * destruct H. 
          set (p:= / INR (S (length (fe f2 ⊕[ / 2] fo f2 :: map (fun i : Q => fe i ⊕[ / 2] fo i) L')))) in *.
          destruct H0. destruct H0. left.
          set (p':= / INR (S (length ([fo f1] ++ flat_map (fun i : Q => [fe i; fo i]) (f2 :: L'))))) in *.
          split.
          ** apply inv_INR_S_length_gt_0_and_lt_1.
          ** intuition. destruct H5. 
          -- destruct H5. destruct H9. destruct H9. intuition. 
            assert (Hdom: (dom x2 == dom x0)%domain). { 
              apply dom_equiv_trans with (l1:= dom x); intuition.
              apply dom_equiv_trans with (l1:= dom pd); intuition.
              apply dom_equiv_sym in H4. auto.
            }
            
            set (p'':= / INR (S (length ([] ++ flat_map (fun i : Q => [fe i; fo i]) (f2 :: L'))))) in *.
            set (p_tmp:= p / (2-p)).
            assert (Hdom2': (dom (cofe_pd x2 p_tmp) == dom (cofe_pd x0 (1- p_tmp)))%domain). { simpl. auto. }

            pose (pd':= pd_add (cofe_pd x2 p_tmp) (cofe_pd x0 (1 - p_tmp)) Hdom2').
            assert (Hp: (p = (2 * p')%R)). { 
              unfold p, p'. cbn [flat_map].
              rewrite !length_app. cbn [length].
              rewrite length_map. 
              rewrite length_flat_map_pair. 
              set (m := length L').
              replace (S (S m)) with (2 + m)%nat by lia.
              replace (S (1 + (2 + 2 * m))) with (2 * (2 + m))%nat by lia.
              rewrite mult_INR. 
              assert (Hnz : INR (2 + m) <> 0).
              { apply not_0_INR. lia. }
              rewrite Rinv_mult; try lra; try exact Hnz.
              ring_simplify. rewrite Rmult_comm. rewrite <- Rmult_assoc.
              rewrite Rmult_comm with (r2:= 2). simpl.
              replace (2 * / (1 + 1))%R with 1 by lra. rewrite Rmult_1_l. auto.
            }

            assert (Hptmp: 0 <= p_tmp <= 1). { unfold p_tmp.
              assert (Hden_pos : (0 < 2 - p)%R) by lra.
              split.
              - apply Rlt_le. apply Rdiv_lt_0_compat; lra.
              - apply Rlt_le.
                apply (Rmult_lt_reg_r (2 - p)); [exact Hden_pos |].
                field_simplify; try lra.
            }
            assert (Htmp_eq: p_tmp = p''). { 
              unfold p_tmp, p'', p. cbn [flat_map]. 
              set (n := length L').
              assert (Hlen_rhs : length ([] ++ [fe f2; fo f2] ++ flat_map (fun i : Q => [fe i; fo i]) L')
                                  = (2%nat * n + 2%nat)%nat). {
                          subst n. cbn. (* [] ++ ... -> ... *)
                          rewrite length_flat_map_pair. lia.
              }
              assert (Hlen_lhs : S (length (fe f2 ⊕[ / 2] fo f2 :: map (fun i : Q => fe i ⊕[ / 2] fo i) L'))
                                = S (S n)).
                { subst n. cbn. rewrite length_map. reflexivity. } 
              rewrite Hlen_lhs. rewrite Hlen_rhs. 
              set (a := INR (S (S n))).
              assert (Ha : a <> 0). { subst a. apply not_0_INR. lia. }
              subst a. field_simplify. 
              - assert (Hden : INR (S (2 * n + 2)%nat) = (2 * INR (S (S n)) - 1)%R).
                  {
                    rewrite !S_INR.   
                    rewrite plus_INR.                    (* INR (2*n + 2) -> INR (2*n) + INR 2 *)
                    rewrite mult_INR.                    (* INR (2*n) -> INR 2 * INR n *)
                    simpl INR.
                    ring.
                  }
                rewrite Hden. auto.
              - rewrite !S_INR.  rewrite plus_INR. rewrite mult_INR. 
                assert (Hpos : (0 < (INR 2 * INR n + INR 2 + 1)%R)%R).
                {
                  assert (Hn : (0%R <= INR n)%R) by apply pos_INR. 
                  simpl INR.
                  lra.
                }
                lra.
              - split; auto. rewrite !S_INR. simpl INR. 
                assert (Hpos : (0 < (2 * (INR n + 1 + 1) - 1)%R)%R).
                {
                  assert (Hn : (0 <= INR n)%R) by apply pos_INR.
                  lra.
                }
                lra.
              }
    
            exists x1, pd'. intuition.
            ++ simpl. apply Valid_linear; auto. 
              +++ apply Rp_1_minus_p_bounds. auto.
              +++ rewrite R_plus_sub_eq_1. lra.
            ++ simpl. apply dom_equiv_trans with (l1:= dom x); intuition.
            ++ simpl. apply dom_equiv_trans with (l1:= dom x); intuition.
            ++ left. fold p''. split. 
              *** apply inv_INR_S_length_gt_0_and_lt_1.
              *** exists x2, x0. intuition;try apply dom_equiv_refl.
              --- simpl. apply dom_equiv_trans with (l1:= dom pd); intuition.
                apply dom_equiv_sym in H3. apply dom_equiv_sym in H14. 
                apply dom_equiv_trans with (l1:= dom x); intuition.
              --- simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
                  rewrite H8, H18, H7. lra. 
              --- simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
                  rewrite H8, H18, H7. lra. 
              --- simpl. rewrite Htmp_eq. apply dst_equiv_refl.
            ++ simpl. rewrite H17. auto. 
            ++ simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
                rewrite H8, H18, H7. lra. 
            ++ simpl. apply dst_equiv_trans with (mu1:= (p * mu x + (1 - p) * mu x0)%dist_state); try auto.
              apply dst_mult_preserves_equiv with (p:= p) in H20.
              apply dst_equiv_trans with (mu1:= (p * (/ 2 * mu x1 + (1 - / 2) * mu x2) + (1 - p) * mu x0)%dist_state).
              +++ apply dst_add_inj_r. auto.
              +++ rewrite dst_mult_plus_distr_r_eq. rewrite dst_mult_plus_distr_r_eq with (p:= (1 - p')%R).
                rewrite dst_add_assoc_eq.
                apply dst_add_preserves_equiv.
                --- unfold p_tmp. rewrite Hp. 
                    rewrite dst_mult_assoc_eq. apply dst_add_preserves_equiv.
                    *** rewrite Rmult_assoc. rewrite Rmult_comm with (r1:= p'). rewrite <- Rmult_assoc. 
                      rewrite <- Rinv_r_sym; try lra. rewrite Rmult_1_l. apply dst_equiv_refl.
                    *** repeat rewrite dst_mult_assoc_eq. rewrite goal_eq; try lra. apply dst_equiv_refl.
                --- unfold p_tmp. rewrite Hp. rewrite dst_mult_assoc_eq. 
                  rewrite goal_eq_minus; try lra. apply dst_equiv_refl.
            -- destruct H; destruct H; exfalso; nra.
          * assert (Hcontra1: 0 < / INR (S (length (fe f2 ⊕[ / 2] fo f2 :: map (fun i : Q => fe i ⊕[ / 2] fo i) L'))) < 1) by apply inv_INR_S_length_gt_0_and_lt_1.
            assert (Hcontra2: 0 < / INR (S (length (fe f2 ⊕[ / 2] fo f2 :: map (fun i : Q => fe i ⊕[ / 2] fo i) L'))) < 1) by apply inv_INR_S_length_gt_0_and_lt_1.
            destruct H; destruct H; exfalso; lra.
  Qed.

  Lemma rangeQ_even_odd_flat :
  forall n,
    Nat.even n = true ->
     List.Forall2 Qeq
      (List.flat_map
        (fun i : Q => (2%Q*i+0)%Q :: (2%Q*i+1)%Q :: nil)
        (rangeQ 0 (Nat.div2 n)))
      (rangeQ 0 n).
  Proof.
    intros n He. 
    apply Nat.even_spec in He.
    destruct He as [k Hk]. subst n.
    rewrite Nat.div2_double. 
    induction k as [|k IH]; intros.
    - simpl. unfold rangeQ. cbn. auto.
    - unfold rangeQ in *. 
      rewrite seq_S.
      simpl Nat.add. rewrite map_app.
      rewrite flat_map_app.
      replace (2 * S k)%nat with (2 * k + 2) %nat by lia.
      rewrite seq_app by lia.
      simpl.
      rewrite map_app.
      eapply Forall2_app.
      + exact IH.
      + simpl. constructor; try constructor; try constructor.
        * ring_simplify. change (2%Q) with (inject_Z 2%Z).
          rewrite <- inject_Z_mult. change 2%Z with (Z.of_nat 2).  
          rewrite <- Nat2Z.inj_mul. 
          reflexivity.
        * ring_simplify. change (2%Q) with (inject_Z 2%Z).
          rewrite <- inject_Z_mult. change 2%Z with (Z.of_nat 2).  
          rewrite <- Nat2Z.inj_mul. 
          replace (k + (k + 0))%nat with (2*k)%nat by lia.
          rewrite Zpos_P_of_succ_nat.
          change (1%Q) with (inject_Z 1%Z).
          rewrite <- inject_Z_plus. reflexivity.
  Qed.

  Lemma atom_eq_Qeq :
  forall (C:nat) x y,
    Qeq x y ->
    (forall pd, [[(C == x)%formula]] pd <-> [[(C == y)%formula]] pd).
  Proof.
    intros C x y Hq. split.
    - intros H. destruct H. split; intuition. 
      apply H0 in H1. destruct H1.
      split; intuition. destruct (evalB_st (C = x) st) eqn: HB; try contradiction.
      cbn in HB. rewrite Hq in HB.
      cbn. rewrite HB. auto.
    - intros H. destruct H. split; intuition. 
      apply H0 in H1. destruct H1.
      split; intuition. destruct (evalB_st (C = y) st) eqn: HB; try contradiction.
      cbn in HB. rewrite <- Hq in HB.
      cbn. rewrite HB. auto.
  Qed.

  Lemma unif_sugar_ext_Forall2 :
  forall Fs Gs,
    Forall2 (fun f g => forall pd, [[f]] pd <-> [[g]] pd) Fs Gs ->
    forall pd, [[unif_sugar Fs]] pd -> [[unif_sugar Gs]] pd.
  Proof.
    intros fs gs Hfg. induction Hfg; intros pd Hsem; auto.
    destruct Hfg.
    - simpl in *. apply H. auto.
    - destruct Hsem.
      * destruct H1. destruct H2 as (pd0 & pd1 & H2). intuition.
        left. split; try apply inv_INR_S_length_gt_0_and_lt_1.
        exists pd0, pd1. intuition.
        + apply H. auto.
        + pose proof (Forall2_length Hfg) as Hlen.
          assert (Heq: / INR (S (length (x0 :: l))) = 
                       / INR (S (length (y0 :: l')))).  {
            simpl. rewrite <- Hlen. reflexivity. }
          rewrite <- Heq. auto.
      * assert (Hcontra: 0 < / INR (S (length (x0 :: l))) < 1) by apply inv_INR_S_length_gt_0_and_lt_1.
        destruct H1; destruct H1; exfalso; rewrite H1 in Hcontra; lra.
  Qed. 
  
  Lemma Forall2_map_pointwise_sem :
    forall (A : Type) (F : A -> Pformula) (R : A -> A -> Prop),
      (forall x y, R x y -> forall pd, [[F x]] pd <-> [[F y]] pd) ->
      forall l1 l2,
        Forall2 R l1 l2 ->
        Forall2 (fun f g => forall pd, [[f]] pd <-> [[g]] pd)
                (map F l1) (map F l2).
  Proof.
    intros A F R Hrel l1 l2 H.
    induction H; simpl.
    - constructor.
    - constructor.
      + apply Hrel; assumption.
      + assumption.
  Qed.

  Lemma map_flat_map
    (A B C : Type) (f : B -> C) (g : A -> list B) :
    forall l : list A,
      flat_map (fun x => map f (g x)) l =
      map f (flat_map g l).
  Proof.
    induction l as [|x xs IH]; cbn.
    - reflexivity.
    - rewrite map_app.
      rewrite IH.
      reflexivity.
  Qed.

  Lemma length_flat_map_eq: forall len C,
  length
    (flat_map (fun i : Q =>
      [(C == 2%Q * i + 0%Q)%formula; (C == 2%Q * i + 1%Q)%formula]) len)
  =
  length
    (flat_map (fun x : Q =>
      [(C == (2 * x + 0)%Q)%formula; (C == (2 * x + 1)%Q)%formula]) len).
  Proof.
    induction len as [|t ts IH]; cbn; auto.
  Qed.

  Lemma seq_even_flat_map len pd C:
    [[unif_sugar (flat_map (fun i : Q => [(C == 2%Q * i + 0%Q)%formula; 
                                          (C == 2%Q * i + 1%Q)%formula]) len)]] pd -> 
    [[unif_sugar (flat_map (fun x : Q => [(C == (2 * x + 0)%Q)%formula; 
                                          (C == (2 * x + 1)%Q)%formula]) len)]] pd.
  Proof.
    intros. generalize dependent pd. induction len as [|f1 len']; intros.
    - cbn [flat_map] in *. auto.
    - destruct len' as [|f2 len].
      + cbn [flat_map] in *. auto.
      + cbn [flat_map] in *. 
        set (a := (C == 2%Q * f1 + 0%Q)%formula) in *.
        set (b := (C == 2%Q * f1 + 1%Q)%formula) in *.
        set (L2 := [(C == 2%Q * f2 + 0%Q)%formula; (C == 2%Q * f2 + 1%Q)%formula]) in *.
        set (L3 := flat_map (fun i : Q =>
              [(C == 2%Q * i + 0%Q)%formula; (C == 2%Q * i + 1%Q)%formula]) len) in *.
        change ([[unif_sugar (a :: [b] ++ L2 ++ L3)]] pd) in H. 

        set (a' := (C == (2 * f1 + 0)%Q)%formula) in *.
        set (b' := (C == (2 * f1 + 1)%Q)%formula) in *.
        set (L2' := [(C == (2 * f2 + 0)%Q)%formula; (C == (2 * f2 + 1)%Q)%formula]) in *.
        set (L3' := flat_map (fun x : Q => 
              [(C == (2 * x + 0)%Q)%formula; (C == (2 * x + 1)%Q)%formula])len) in *.
        destruct H.
        * destruct H. destruct H0. destruct H0. intuition.
          left. split; try apply inv_INR_S_length_gt_0_and_lt_1.
          exists x, x0. intuition.
          ** destruct H6. 
          -- destruct H6. destruct H9. destruct H9. left. 
            split; try apply inv_INR_S_length_gt_0_and_lt_1. 
            exists x1, x2. intuition.
            assert (Heq: / INR (S (length ([] ++ L2 ++ L3))) = 
                        / INR (S (length ([] ++ L2' ++ L3')))).  {
                          cbn. f_equal. repeat rewrite length_app. cbn.
                          unfold L3, L3'.
                          rewrite length_flat_map_eq. auto.
                        }
            rewrite <- Heq. auto.
          -- assert (Hcontra: 0 < / INR (S (length ([] ++ L2 ++ L3))) < 1) by apply inv_INR_S_length_gt_0_and_lt_1.
            destruct H6; destruct H6; exfalso; rewrite H6 in Hcontra; lra.
          ** assert (Heq: / INR (S (length ([b] ++ L2 ++ L3))) = 
                        / INR (S (length ([b'] ++ L2' ++ L3')))).  {
                          cbn. f_equal. 
                          unfold L3, L3'.
                          rewrite length_flat_map_eq. auto.
                        }
            rewrite <- Heq. auto.
        * assert (Hcontra: 0 < / INR (S (length ([b] ++ L2 ++ L3))) < 1) by apply inv_INR_S_length_gt_0_and_lt_1.
          destruct H; destruct H; exfalso; rewrite H in Hcontra; lra.
  Qed. 


  Lemma unif_sugar_even_odd: forall pd n (C: nat), 
    Nat.even n = true ->
    [[unif_sugar (map (fun i : Q => (C == 2%Q * i + 0%Q) ⊕[ / 2] 
                                    (C == 2%Q * i + 1%Q)) (rangeQ 0 (Nat.div2 n)))]] pd ->
    [[unif_sugar (map (fun i : Q => (C == i)%formula) (rangeQ 0 n))]] pd.
  Proof.
    intros pd n C Heven H. 
    eapply (unif_sugar_map_pair_flatten pd (rangeQ 0 (Nat.div2 n))
          (fun i => (C == 2%Q*i + 0%Q)%formula)
          (fun i => (C == 2%Q*i + 1%Q)%formula)) in H.
    assert (Hmap :
    [[unif_sugar
      (map (fun i:Q => (C == i)%formula)
           (flat_map (fun i:Q => (2%Q*i+0)%Q :: (2%Q*i+1)%Q :: nil)
                     (rangeQ 0 (Nat.div2 n))))]] pd). {
    rewrite <- (map_flat_map
                  Q Q Pformula
                  (fun i => (C == i)%formula)
                  (fun i => (2%Q*i+0)%Q :: (2%Q*i+1)%Q :: nil)
                  (rangeQ 0 (Nat.div2 n))).
    cbn in H |- *. apply seq_even_flat_map. auto.
    }

    assert (Hf :
      Forall2
        (fun f g => forall pd0, [[f]] pd0 <-> [[g]] pd0)
        (map (fun i => (C == Aco i)%formula)
             ((flat_map (fun i : Q => [(2 * i + 0)%Q; (2 * i + 1)%Q]) (rangeQ 0 (Nat.div2 n)))))
        (map (fun i => (C == Aco i)%formula) (rangeQ 0 n))).
    { 
      set (F := fun i : Q => (C == Aco i)%formula) in *.
      set (L := flat_map (fun i : Q => [(2 * i + 0)%Q; (2 * i + 1)%Q])
                    (rangeQ 0 (Nat.div2 n))) in *.
      set (R := rangeQ 0 n) in *.
      assert (HQR : Forall2 Qeq L R). {
        apply rangeQ_even_odd_flat. auto. }
      apply Forall2_map_pointwise_sem with (R := Qeq).
      - intros x y Hxy pd0.
        apply atom_eq_Qeq; exact Hxy.
      - exact HQR.
    }
    eapply (unif_sugar_ext_Forall2 _ _ Hf pd).
    exact Hmap.
  Qed.

  Lemma split_lt_2n_nat : forall (v : nat) (n: Q) pd,
    [[v < 2%Q * n]] pd -> (Dirac_v v) pd ->
    [[v < Aco n]] pd \/ [[(~ v < Aco n) && (v < 2%Q * n)]] pd.
  Proof.
    intros v n pd Hv Hd. destruct pd as [dom mu HPD].
    destruct Hv, Hd. destruct H2. simpl in H, H0, H1, H2.
    destruct (Qlt_le_dec x n) as [Hlt | Hge].
    - left. split; simpl; intuition; specialize (H0 st H3); destruct H0; auto. 
      specialize (H2 st H3). rewrite <- H2 in Hlt. 
      destruct (negb (Qle_bool n (get v st))) eqn: HB; auto.
      rewrite negb_false_iff in HB. 
      apply Qle_bool_iff in HB.
      apply Qlt_not_le in Hlt.
      contradiction.
    - right. split; simpl; intuition. 
      + rewrite orb_domain_refl. auto.
      + rewrite orb_domain_refl. specialize (H0 st H3); destruct H0; auto.
      + specialize (H2 st H3). specialize (H0 st H3); destruct H0.
        destruct (negb (Qle_bool (2 * n) (get v st))) eqn: HB; try contradiction.
        rewrite negb_true_iff in HB. cbv [andb].
        destruct (negb (negb (Qle_bool n (get v st)))) eqn: Hb; auto.
        rewrite negb_false_iff, negb_true_iff in Hb.
        apply Qle_bool_iff in Hge. rewrite <- H2 in Hge.
        rewrite Hge in Hb.
        discriminate.
  Qed.


  Lemma in_supp_update_da_inv : forall st s0 p0 C da,
    is_in_supp st (supp_mu (update_st_with_da s0 p0 C da)) = true ->
    exists a d, In (a,d) da /\ 
      (st == update s0 C (evalA_st a s0))%state.
  Proof.
    intros. induction da as [|(a0,d0) da' IH].
    - simpl in *. inversion H.
    - simpl in H. unfold supp_mu in H. simpl in H.
      rewrite insert_st_pair_fst_eq_insert_st in H.
      rewrite in_supp_insert_eq in H. 
      apply orb_true_iff in H. destruct H.
      + exists a0, d0. split; try auto.  
        left. auto.
      + apply IH in H. destruct H as (a & (d & (H0 & H1))). 
        exists a, d; try auto. split; try auto. 
        right. auto.
  Qed.

  Lemma get_RA_supp: forall (V B: nat) x0 da mu,
  Valid_dist mu -> Valid_dist (RAssn_under_dstate mu B da) -> Valid_dist da -> 
  Nat.eqb V B = false ->
  (forall st : partial_st, 
    is_in_supp st (supp_mu mu) = true ->
      (get V st == x0)%Q) -> 
    forall s, is_in_supp s (supp_mu (RAssn_under_dstate mu B da)) = true -> 
    (get V s == x0)%Q.
  Proof.
    intros V B x0 da mu HV HV' HVda HVB H0 s Hin. 
    induction mu as [|(s0,p0) mu' IH].
    - simpl in Hin. inversion Hin.
    - simpl in *. 
      apply in_supp_mu_app_or with (mu0:= update_st_with_da s0 p0 B da) 
        (mu1:= RAssn_under_dstate mu' B da) in Hin; intuition.
      + apply in_supp_update_da_inv in H. destruct H as (a & d & HIN & Hs).
        apply st_eq_implies_get_eq with (x:= V) in Hs. rewrite Hs.
        rewrite update_neq; try auto.
        apply H0. apply in_supp_mu_cons_head.
      + apply IH; auto. 
        * apply Valid_dist_inv in HV. auto.
        * apply Valid_dist_inv in HV. apply Valid_after_RA; auto.
        * intros. apply H0; auto. apply in_supp_mu_cons_r. auto.
      + apply Valid_add_decom in HV'. destruct HV'. auto.
      + apply Valid_dist_inv in HV. apply Valid_after_RA; auto.
      + apply dst_equiv_refl.
  Qed.

  Lemma Dirac_RA_neq: forall (V B: nat) pd (Vda : valid_dist_aexp)
    (HWFa : WF_distaexp_with_pd (proj1_sig Vda) pd), 
    Nat.eqb V B = false ->
    Valid_dist (mu pd) ->
    Dirac_v V pd ->
    Dirac_v V (RAssn_under_pd B Vda pd HWFa).
  Proof.
    intros V B pd Vda HWFa HVB HV Hd. destruct Hd. split.
    - apply dom_subset_trans with (l1:= dom pd); auto. 
      simpl in *. apply dom_subset_orb_dom_r. apply dom_subset_refl.
    - destruct H0. exists x. intros. simpl in *.
      eapply get_RA_supp in H1; auto.
      + auto.
      + destruct Vda. apply Valid_after_RA; auto. simpl. 
        destruct a. split; try auto. rewrite e. lra.
      + destruct Vda. simpl. destruct a. split; try auto. rewrite e. lra.
      + auto. 
  Qed.

  Lemma evalB_lt_with_N: forall s (V: nat) q x,
    evalB_st (V < Aco q) s = false -> 
    (get V s == x)%Q -> 
    (q <= x)%Q.
  Proof.
    intros s V q x H H0. rewrite <- evalB_not_le_iff_lt_rev in H.
    unfold evalB_st in H. rewrite negb_false_iff in H.
    apply Qle_bool_iff in H. cbn [evalA_st] in H.
    rewrite H0 in H. auto.
  Qed.

  Lemma sat_unif_sugar_split :
  forall l1 l2 pd, 
    Valid_dist (mu pd) ->
    [[unif_sugar (l1 ++ l2)]] pd ->
    [[(unif_sugar l1)
       ⊕[ INR (length l1) / INR (length (l1 ++ l2)) ]
       (unif_sugar l2)]] pd.
  Proof.
    intros l1 l2 pd HV H. 
    set (p_num:= INR (length l1)) in *.
    set (p_den:= INR (length (l1 ++ l2))) in *.
    generalize dependent l2. generalize dependent pd.
    induction l1 as [|a0 l1' IH]; intros.
    - simpl in H. cbn [unif_sugar]. right. right. split. 
      + simpl. rewrite Rdiv_0_l. auto.
      + exists pd. intuition. apply pd_equiv_refl.
    - destruct l1' as [|a1 l1']; destruct l2 as [|b0 l2']. 
      + simpl in H. cbn [unif_sugar]. right. left. split.
        * unfold p_num, p_den. simpl. rewrite Rdiv_1_l. lra.
        * exists pd. intuition. apply pd_equiv_refl.
      + destruct H. 
        * destruct H. destruct H0 as (pd0 & pd1 & H0). 
          left. intuition. 
          -- apply Rdiv_lt_0_compat; apply lt_0_INR; simpl; try lia. 
          -- apply (Rmult_lt_reg_r p_den).
            ++ unfold p_den. change (0 < INR (S (S (length l2'))))%R.
              apply lt_0_INR. lia.
            ++ field_simplify.
              ** apply lt_INR. simpl. lia.
              ** apply not_0_INR; simpl; lia.
          -- exists pd0, pd1. intuition. 
            change ([] ++ b0 :: l2') with (b0 :: l2') in H10. 
            assert (Heq: ((/ INR (S (length (b0 :: l2'))))%R = (p_num / p_den)%R)). {
              unfold p_num, p_den. simpl. lra. }
            rewrite <- Heq. auto.
        * assert (Hcontra: 0 < / INR (S (length ([] ++ b0 :: l2'))) < 1) by apply inv_INR_S_length_gt_0_and_lt_1. 
          destruct H; destruct H; rewrite H in Hcontra; lra.
      + destruct H. 
        * destruct H. destruct H0 as (pd0 & pd1 & H0). 
          right. left. split.
          ++ unfold p_num, p_den. rewrite app_nil_r. field.
            apply not_0_INR. simpl. lia.
          ++ exists pd. intuition; try apply pd_equiv_refl. 
            rewrite app_nil_r in *. left. 
            split; try apply inv_INR_S_length_gt_0_and_lt_1.
            exists pd0, pd1. intuition.
        * assert (Hcontra: 0 < / INR (S (length ((a1 :: l1') ++ []))) < 1) by apply inv_INR_S_length_gt_0_and_lt_1. 
          destruct H; destruct H; rewrite H in Hcontra; lra.
      + destruct H. 
        * set (p1:= / INR (S (length ((a1 :: l1') ++ b0 :: l2')))) in *. 
          destruct H. destruct H0 as (pd0 & pd1 & H0). 
          left. 
          assert (Htmp: 0 < p_num / p_den < 1). {
            unfold p_num, p_den. rewrite length_app. rewrite plus_INR.
            set (A := INR (length (a0 :: a1 :: l1'))).
            set (B := INR (length (b0 :: l2'))). 
            assert (HA : (0 < A)%R).
            {
              unfold A.
              apply lt_0_INR. simpl.
              lia.
            }
            assert (HB : (0 < B)%R).
            {
              unfold B.
              apply lt_0_INR. simpl.
              lia.
            }
            split.
            -- apply Rdiv_lt_0_compat.
              ++ exact HA.
              ++ lra.
            -- apply (Rmult_lt_reg_r (A + B)).
              ++ lra.
              ++ field_simplify; lra.
          } 
          split; auto. 
          destruct H0. destruct H1. destruct H2.
          destruct H3. destruct H4. destruct H5.
          destruct H6. destruct H7. 
           apply IH in H5; auto. destruct H5.
          -- destruct H5. 
            set (p2:= INR (length (a1 :: l1')) / INR (length ((a1 :: l1') ++ b0 :: l2'))) in *.
            destruct H9 as (pd2 & pd3 & H11). intuition. 
            assert (Heq: (dom (cofe_pd pd0 (/ p_num)) == dom (cofe_pd pd2 (1 - / p_num)))%domain). {
              simpl. apply dom_equiv_trans with (l1:= dom pd); auto.
              apply dom_equiv_sym.
              apply dom_equiv_trans with (l1:= dom pd1); auto.
            }
            pose (pd':= pd_add (cofe_pd pd0 (/ p_num)) (cofe_pd pd2 (1 - / p_num)) Heq).
            exists pd', pd3. intuition.
            ++ assert (Hpnum: 0 <= / p_num <= 1). {
                unfold p_num. split.
                - apply Rlt_le. apply Rinv_0_lt_compat. apply lt_0_INR. simpl. lia.
                - apply (Rmult_le_reg_r (INR (length (a0 :: a1 :: l1')))).
                  + apply lt_0_INR. simpl. lia.
                  + field_simplify.
                    * replace (length (a0 :: a1 :: l1')) with (S (S (length l1'))) by reflexivity.
                      rewrite S_INR. rewrite S_INR. 
                      assert (H' : (0 <= INR (length l1'))%R) by apply pos_INR.
                      nra.  
                    * apply not_0_INR. simpl. lia.
              }
              apply Valid_linear; try auto.
              ** apply Rp_1_minus_p_bounds. auto. 
              ** rewrite R_plus_sub_eq_1. lra.
            ++ apply dom_equiv_trans with (l1:= dom pd1); auto.
            ++ left. split; try apply inv_INR_S_length_gt_0_and_lt_1. 
              exists pd0, pd2. intuition.
              +++ simpl. apply dom_equiv_refl.
              +++ simpl. apply dom_equiv_trans with (l1:= dom pd1); auto.
                apply dom_equiv_sym in H2.
                apply dom_equiv_trans with (l1:= dom pd); auto.
              +++ simpl. rewrite dst_sum_prob_decom. 
                repeat rewrite dst_sum_prob_coef_mult. 
                rewrite H19, H6, H7. lra. 
              +++ simpl. rewrite dst_sum_prob_decom. 
                repeat rewrite dst_sum_prob_coef_mult.
                rewrite H19, H6, H7. lra.
              +++ replace (INR (S (length (a1 :: l1')))) with p_num. 
                --- simpl. apply dst_equiv_refl.
                --- unfold p_num. simpl. reflexivity.
            ++ simpl. rewrite dst_sum_prob_decom. 
              repeat rewrite dst_sum_prob_coef_mult. 
              rewrite H19, H6, H7. lra.
            ++ simpl. rewrite H20. lra.
            ++ simpl. rewrite dst_mult_plus_distr_r_eq.
              rewrite dst_mult_assoc_eq. 
              assert (p1 = / p_den). { 
                unfold p1, p_den. 
                change ((a0 :: a1 :: l1') ++ b0 :: l2') with (a0 :: ((a1 :: l1') ++ b0 :: l2')).
                simpl.
                reflexivity.
              }
              set (A:= INR (length ((a1 :: l1')))) in *.
              set (B:= INR (length ((b0 :: l2')))) in *. 
              assert (Hpnum : p_num = (A + 1)%R). {
                unfold p_num, A. simpl. reflexivity.
              }
              assert (Hp1 : p1 = /(A + 1 + B)%R). {
                unfold p1, A , B. 
                repeat rewrite length_app. rewrite S_INR. 
                rewrite plus_INR. rewrite Rplus_assoc. rewrite Rplus_comm with (r2:= 1). 
                rewrite Rplus_assoc. 
                simpl. reflexivity.
              }
              assert (Hp2 : p2 = A /(A + B)%R). {
                unfold p2, A , B. 
                repeat rewrite length_app. 
                rewrite plus_INR. 
                simpl. reflexivity.
              }
              assert (HAaB: (A + B)%R <> 0). {
                unfold A, B. rewrite <- plus_INR.
                apply not_0_INR. simpl. lia.
              }
              assert (HA1B: (A + 1 + B)%R <> 0). {
                unfold A, B. rewrite <- Rplus_comm with (r1:= 1).
                replace 1%R with (INR 1%nat) by reflexivity. 
                repeat rewrite <- plus_INR.
                apply not_0_INR. simpl. lia.
              }
              assert (HA10: (A + 1)%R <> 0). {
                unfold A. replace 1%R with (INR 1%nat) by reflexivity. 
                repeat rewrite <- plus_INR.
                apply not_0_INR. simpl. lia.
              }
              replace (p_num / p_den * / p_num)%R with p1.
              ** apply dst_equiv_trans with (mu1:= (p1 * mu pd0 + (1 - p1) * mu pd1)%dist_state); auto. 
                rewrite <- dst_add_assoc_eq. 
                apply dst_add_inj_l.  
                apply dst_equiv_trans with (mu1:= ((1 - p1) * (p2 * mu pd2 + (1 - p2) * mu pd3))%dist_state).
                *** apply dst_mult_preserves_equiv. auto.
                *** rewrite dst_mult_plus_distr_r_eq. 
                    apply dst_add_preserves_equiv.
                    --- repeat rewrite dst_mult_assoc_eq. 
                      replace ((1 - p1) * p2)%R with (p_num / p_den * (1 - / p_num))%R; try apply dst_equiv_refl.
                      unfold Rdiv. rewrite <- H21.
                      rewrite Rmult_comm. rewrite <- Rmult_assoc.
                      rewrite Hpnum, Hp1.
                      replace (1 - / (A + 1))%R with (A / (A + 1))%R.
                      +++ unfold Rdiv at 1. rewrite Rmult_assoc with (r1:= A).
                          rewrite Rinv_l; try lra.
                          replace (1 - / (A + 1 + B))%R with ((A + B) / (A + 1 + B))%R.
                        ++++ rewrite Hp2. field. split; assumption.
                        ++++ field. assumption.
                      +++ field. assumption.
                    --- rewrite dst_mult_assoc_eq.  
                      replace ((1 - p1) * (1 - p2))%R with (1 - p_num / p_den)%R; try apply dst_equiv_refl.
                      unfold Rdiv. rewrite <- H21.
                      (* rewrite Rmult_comm. rewrite <- Rmult_assoc. *)
                      rewrite Hpnum, Hp1.
                      replace (1 - (A + 1) * / (A + 1 + B))%R with (B / (A + 1 + B))%R.
                      +++ replace (1 - / (A + 1 + B))%R with ((A + B) / (A + 1 + B))%R.
                        ++++ rewrite Hp2. field. split; assumption.
                        ++++ field. assumption.
                      +++ field. assumption.
              ** unfold Rdiv. rewrite Rmult_comm. rewrite <- Rmult_assoc. 
                rewrite Rinv_l; try rewrite Hpnum; auto.
                rewrite H21. rewrite Rmult_1_l. reflexivity.
          -- assert (Hcontra: 0 < INR (length (a1 :: l1')) / INR (length ((a1 :: l1') ++ b0 :: l2')) < 1). {
              rewrite length_app. rewrite plus_INR.
              set (A := INR (length (a1 :: l1'))).
              set (B := INR (length (b0 :: l2'))). 
              assert (HA : (0 < A)%R).
              {
                unfold A.
                apply lt_0_INR. simpl.
                lia.
              }
              assert (HB : (0 < B)%R).
              {
                unfold B.
                apply lt_0_INR. simpl.
                lia.
              }
              split.
              -- apply Rdiv_lt_0_compat.
                ++ exact HA.
                ++ lra.
              -- apply (Rmult_lt_reg_r (A + B)).
                ++ lra.
                ++ field_simplify; lra.
              }
          destruct H5; destruct H5; rewrite H5 in Hcontra; lra.
        * assert (Hcontra: 0 < / INR (S (length ((a1 :: l1') ++ b0 :: l2'))) < 1) by apply inv_INR_S_length_gt_0_and_lt_1. 
          destruct H; destruct H; rewrite H in Hcontra; lra.
          
  Qed.

  Lemma pf_C_uniform_split :
    forall C0 X0 X1,
      (X0 <= X1)%nat ->
      pf_C_uniform C0 0 X1 =
      pf_C_uniform C0 0 X0 ++ pf_C_uniform C0 X0 (X1 - X0).
  Proof.
    intros C0 X0 X1 HX.
    unfold pf_C_uniform, rangeQ.
    replace (seq 0 X1) with (seq 0 (X0 + (X1 - X0))) by (f_equal; lia).
    rewrite seq_app.
    simpl.
    repeat rewrite map_app.
    f_equal.
  Qed.

  Lemma length_pf_C_uniform :
    forall C0 s k, length (pf_C_uniform C0 s k) = k.
  Proof.
    intros C0 s k. generalize dependent s.
    unfold pf_C_uniform.
    induction k as [|k IH]; try auto.
    intros. simpl. unfold rangeQ in IH.
    rewrite IH. auto.
  Qed.



  Lemma decom_C_unif_0v_to_oplus: forall (C V: nat) pd,
    Valid_dist (mu pd) ->
    C_unif_depend_to_0v C V pd -> 
    [[~ (V < inject_Z (Z.of_nat N))]] pd -> 
    assert_Oplus [[unif_sugar (pf_C_uniform C 0 N)]] (C_unif_depend_to_nv C V N) pd.
  Proof. 
    intros C0 V0 pd HValid. intros.
    unfold C_unif_depend_to_0v, Unif_Depend_by in H. 
    destruct H. intuition. 
    assert (HN1: (1 < N)%nat). {
      assert (Hz : (1 < Z.of_nat N)%Z).
        {
          rewrite Zlt_Qlt.
          exact HN.
        }
        lia.
    } 
    destruct pd as [dom mu HPD]. destruct mu as [|(s',p') mu'].
    + right. left. 
      apply pd_equiv_preserves_sem with (pd0:= pd_emp dom); 
        intuition; try apply Valid_dist_nil.
      * apply WD_Unif_MN. lia. 
      * split; simpl; try apply dom_equiv_refl; try apply dst_equiv_refl.
      * apply emp_dst_satisfies_phi; auto. 
        - apply WD_Unif_MN. lia. 
        - rewrite get_var_in_unif_MN; try lia.
          apply satisfy_implies_dom_sub in H4; auto. 
        ++ simpl in H4. rewrite get_var_in_unif_MN in H4; auto.
        ++ apply WD_Unif_MN. auto. 
    + set (pd':= {| dom := dom; mu := (s', p') :: mu'; all_partial := HPD|}) in *.
      destruct (Nat.eq_dec N x) as [Heq | Hneq].
      {
        right. left. rewrite Heq. auto. 
      }

      left. exists (INR N / INR x)%R, (INR (x-N) / INR x)%R.
      assert (HNx: (N <= x)%nat). { 
        destruct H0. unfold df_sem in H3.
        assert (Hin': is_in_supp s' (supp_mu (mu pd')) = true). {
          simpl. apply in_supp_mu_cons_head.
        }
        specialize (H3 s' Hin'). destruct H3.
        cbn [get_variables_in_bexp] in H3. 
        cbn [evalB_st] in H5.

        specialize (H s' Hin'). cbn [evalA_st] in H.
        destruct (negb (evalB_st (V0 < inject_Z (Z.of_nat N)) s')) eqn: HB; try contradiction.
        rewrite negb_true_iff in HB.
        apply evalB_lt_with_N with (q:= inject_Z (Z.of_nat N)) in H; auto.
        apply Nat2Z.inj_le. rewrite Zle_Qle. auto.
      }
      assert (HxR: (N < x)%nat) by lia.
      intuition.
      * apply Rdiv_lt_0_compat; apply lt_0_INR; lia.
      * apply (Rmult_lt_reg_r (INR x)). 
        - apply lt_0_INR. lia.
        - field_simplify.
        ++ apply lt_INR. auto.
        ++ apply not_0_INR. lia.
      * rewrite minus_INR; auto. 
        apply (Rmult_lt_reg_r (INR x)). 
        - apply lt_0_INR. lia.
        - field_simplify.
        ++ rewrite <- minus_INR; auto. apply lt_0_INR. lia.
        ++ apply not_0_INR. lia.
      * apply (Rmult_lt_reg_r (INR x)). 
        ** apply lt_0_INR. lia.
        ** field_simplify.
          ++ apply lt_INR. lia.
          ++ apply not_0_INR. lia.
      * rewrite minus_INR by lia. field. apply not_0_INR. lia.
      * rewrite pf_C_uniform_split with (X0:= N) in H4; auto.
        apply sat_unif_sugar_split in H4; auto.
        -- set (padd:= INR (length (pf_C_uniform C0 0 N)) /
                    INR (length (pf_C_uniform C0 0 N ++ pf_C_uniform C0 N (x - N)))) in *.
            assert (Hcontra: 0 < padd < 1). { 
                unfold padd. rewrite length_app.
                rewrite plus_INR.
                repeat rewrite length_pf_C_uniform. 
                rewrite <- plus_INR. 
                replace (INR (N + (x - N))) with (INR x) by (f_equal; lia).
                assert (HNnat : (0 < N)%nat) by lia.
                assert (HxposR : (0 < INR x)%R).
                {
                  apply lt_0_INR.
                  exact H1.
                }
                split.
                - apply Rdiv_lt_0_compat.
                  + apply lt_0_INR.
                    exact HNnat.
                  + exact HxposR.
                - apply (Rmult_lt_reg_r (INR x)).
                  + exact HxposR.
                  + field_simplify.
                    * apply lt_INR.
                    exact HxR.
                    * apply not_0_INR. lia.
              }
            destruct H4.  
            ++ destruct H3. destruct H4. destruct H4. exists x0, x1. intuition.
            ** unfold C_unif_depend_to_nv. exists x. intuition.
              apply H.
              apply dst_equiv_implies_beq_supp in H16; intuition.
              --- rewrite <- supp_eq_linear in H16; auto. 
                  apply in_supp_beq_supp_compat with (st:= st) in H16; auto.
                  rewrite H16. 
                  apply in_supp_r_if_subset with (ls1:= supp_mu (mu x0 + mu x1)%dist_state) in H15; auto.
                  apply supp_mu_subset_decom_add_r.
              --- apply Valid_linear; auto; try lra.
      
            ** assert (Heq: padd = INR N / INR x). {
                unfold padd. rewrite length_app.
                rewrite plus_INR.
                repeat rewrite length_pf_C_uniform. 
                rewrite <- plus_INR. 
                replace (INR (N + (x - N))) with (INR x) by (f_equal; lia).
                reflexivity.
              }
              assert (Heq1 : @eq R (Rminus 1%R padd) (Rdiv (INR (x - N)) (INR x))). {
                unfold padd. rewrite length_app.
                rewrite plus_INR.
                repeat rewrite length_pf_C_uniform. 
                rewrite <- plus_INR. 
                replace (INR (N + (x - N))) with (INR x) by (f_equal; lia).
                replace (1 - INR N / INR x)%R with ((INR x - INR N) / INR x)%R.
                - rewrite <- minus_INR; auto.
                - field. apply not_0_INR. lia.
              }
              rewrite <- Heq. rewrite <- Heq1. auto.
            ++ 
              destruct H3; destruct H3; rewrite H3 in Hcontra; exfalso; lra.
  Qed.

  Lemma pf_C_uniform_cons :
  forall C m n,
    pf_C_uniform C m (S n) =
    (C == Aco (inject_Z (Z.of_nat m)))%formula
      :: pf_C_uniform C (S m) n.
  Proof. 
    unfold pf_C_uniform. induction n; simpl; auto.
  Qed.

  Lemma unif_sugar_pf_C_uniform_support :
  forall C m n pd st,
    Valid_dist (mu pd) ->
    [[ unif_sugar (pf_C_uniform C m n) ]] pd ->
    is_in_supp st (supp_mu pd.(mu)) = true ->
    exists i,
      In i (rangeQ m n) /\
      df_sem (Dpred (Beq C (Aco i))) st.
  Proof. 
    intros C0 m n pd st HV. intros. generalize dependent pd. generalize dependent m.
    induction n; intros.
    - cbn in H. destruct H. apply H1 in H0. inversion H0. contradiction.
    - destruct n as [|n']. 
      + destruct H. intuition. exists (inject_Z (Z.of_nat m)). intuition. 
        simpl. auto.
      + rewrite pf_C_uniform_cons in H. destruct H. 
        * set (p:= / INR (S (length (pf_C_uniform C0 (S m) (S n'))))) in *. 
          destruct H. destruct H1. destruct H1. intuition.
          assert (Hpminus: (0 < 1 - p < 1)%R) by (rewrite <- Rp_lt1_minus_p_bounds; auto).
          apply in_supp_mu_app_or with (st:= st) in H11; auto.
          -- destruct H11. 
            ++ rewrite <- supp_eq_mult_coef with (p:= p) in H10; auto.  
              destruct H6. exists (inject_Z (Z.of_nat m)). intuition. 
              simpl. auto.
            ++ rewrite <- supp_eq_mult_coef in H10; intuition.
              apply IHn in H7; auto. destruct H7. 
              exists x1. intuition. simpl. simpl in H13. auto.
          -- apply Valid_mult_cofe; try assumption. lra. 
          -- apply Valid_mult_cofe; try assumption. lra. 
        * assert (Hcontra: 0 < / INR (S (length (pf_C_uniform C0 (S m) (S n')))) < 1) by apply inv_INR_S_length_gt_0_and_lt_1. 
          destruct H; destruct H; rewrite H in Hcontra; exfalso; lra.  
  Qed.
    
  Lemma in_rangeQ_0N_lt :
  forall i N,
    In i (rangeQ 0 N) ->
    (i < inject_Z (Z.of_nat N))%Q.
  Proof.
    intros i N Hin.
    unfold rangeQ in Hin.
    apply in_map_iff in Hin.
    destruct Hin as (k & [Hik Hk]).
    subst i.
    apply in_seq in Hk.
    destruct Hk as [_ Hklt]. 
    rewrite <- Zlt_Qlt.
    apply Nat2Z.inj_lt.
    exact Hklt.
  Qed.
    
  Lemma unif_pf_C_uniform_lt :
  forall C N pd, 
    (N > 0)%nat ->
    Valid_dist (mu pd) ->
    [[ unif_sugar (pf_C_uniform C 0 N) ]] pd ->
    [[ C < inject_Z (Z.of_nat N) ]] pd.
  Proof. 
    intros C0 N0 pd HN0 HValid Hunif. split.
    - simpl. 
      apply satisfy_implies_dom_sub in Hunif; try assumption.
      + rewrite <- get_var_in_unif_MN with (N:= N0) (M:= 0%nat); try assumption.
      + apply WD_Unif_MN. auto.
    - intros st Hsupp. 
      destruct (unif_sugar_pf_C_uniform_support C0 0 N0 pd st HValid Hunif Hsupp)
        as (i & [Hin_range Hdf]).
      assert (HiLt : (i < inject_Z (Z.of_nat N0))%Q).
      { apply in_rangeQ_0N_lt. exact Hin_range. }
      destruct Hdf. simpl in H. rewrite orb_domain_nil_r in H.
      split; simpl; auto.  
      destruct (evalB_st (C0 = i) st) eqn: HB; try contradiction.
      cbn [evalB_st] in HB. cbn [evalA_st] in *. 
      apply Qeq_bool_iff in HB. rewrite <- HB in HiLt. 
      destruct ((Qle_bool (inject_Z (Z.of_nat N0)) (get C0 st))) eqn: Hcontra ; try auto.
      simpl. 
      apply Qle_bool_iff in Hcontra. 
      assert ((inject_Z (Z.of_nat N0) < inject_Z (Z.of_nat N0))%Q) as Hbad.
      {
        eapply Qle_lt_trans; eauto.
      }
      now apply Qlt_irrefl in Hbad.
  Qed.

  Lemma from_Q_ineq_to_nat_sub1_pos (N : nat) :
    (1 < inject_Z (Z.of_nat N))%Q ->
    (N - 1 > 0)%nat.
  Proof.
    intro HNminus.
    change (inject_Z 1 < inject_Z (Z.of_nat N))%Q in HNminus.
    rewrite <- (Zlt_Qlt 1 (Z.of_nat N)) in HNminus.
    lia.
  Qed.

  Lemma PDeter_lt_le_inv: forall (X: nat) (q: Q) pd, 
    Valid_dist (mu pd) -> 
    [[X < q]] pd <-> [[~ X >= q]] pd.
  Proof. 
    intros. split; intros; destruct H0; split; simpl in *; auto; intros; intuition.
    - apply in_supp_return_domain_eq in H2. 
      apply dom_equiv_sym in H2.
      apply dom_subset_eq_compat_left with (X:= dom pd); auto.
    - apply H1 in H2. intuition. 
      destruct (negb (Qle_bool q (get X st))) eqn: HB; try auto.
    - apply in_supp_return_domain_eq in H2. 
      apply dom_equiv_sym in H2.
      apply dom_subset_eq_compat_left with (X:= dom pd); auto.
    - apply H1 in H2. intuition. 
      destruct (negb (Qle_bool q (get X st))) eqn: HB; try auto.
  Qed.

  Lemma in_rangeQ_MN_ge :
  forall i M N, 
    In i (rangeQ M N) ->
    (i >= inject_Z (Z.of_nat M))%Q.
  Proof.
    intros i M N Hin.
    unfold rangeQ in Hin.
    apply in_map_iff in Hin.
    destruct Hin as (k & [Hik Hk]).
    subst i.
    apply in_seq in Hk.
    destruct Hk as [HMle Hklt]. 
    rewrite <- Zle_Qle.
    apply Nat2Z.inj_le. 
    exact HMle.
  Qed.

  Lemma unif_pf_C_uniform_ge :
  forall C m n pd, 
    (n > 0)%nat ->
    Valid_dist (mu pd) ->
    [[ unif_sugar (pf_C_uniform C m n) ]] pd ->
    [[ Pdeter (Dpred (C >= inject_Z (Z.of_nat m))) ]] pd.
  Proof. 
    intros C0 m n pd HN0 HValid Hunif. split.
    - simpl. 
      apply satisfy_implies_dom_sub in Hunif; try assumption.
      + rewrite <- get_var_in_unif_MN with (N:= n) (M:= m); try assumption.
      + apply WD_Unif_MN. auto.
    - intros st Hsupp. 
      destruct (unif_sugar_pf_C_uniform_support C0 m n pd st HValid Hunif Hsupp)
        as (i & [Hin_range Hdf]).
      assert (HiGe : (i >= inject_Z (Z.of_nat m))%Q).
      { apply in_rangeQ_MN_ge with (N:= n). exact Hin_range. }
      destruct Hdf. simpl in H. rewrite orb_domain_nil_r in H.
      split; simpl; auto.  
      destruct (evalB_st (C0 = i) st) eqn: HB; try contradiction.
      cbn [evalB_st] in HB. cbn [evalA_st] in *. 
      apply Qeq_bool_iff in HB. rewrite <- HB in HiGe. 
      destruct ((Qle_bool (inject_Z (Z.of_nat m)) (get C0 st))) eqn: Hcontra ; try auto.
      simpl. 
      apply Qle_bool_iff in HiGe. 
      rewrite HiGe in Hcontra. inversion Hcontra.
  Qed.


  Lemma unif_depend_pf_C_uniform_ge:
  forall C N pd, 
    (N > 0)%nat ->
    Valid_dist (mu pd) ->
    C_unif_depend_to_nv C V N pd ->
    [[Pdeter (Dpred (C >= inject_Z (Z.of_nat N)))]] pd.
  Proof. 
    intros C0 N0 pd HN0 HValid Hunif. destruct Hunif. intuition. 
    rename H2 into Hunif.
    assert (HWD: singleton_bool_list C0 ⊆ dom pd). {
      apply satisfy_implies_dom_sub in Hunif; try assumption.
      + rewrite get_var_in_unif_MN in Hunif; try assumption. lia.
      + apply WD_Unif_MN. lia. 
    }
    split.
    - simpl. auto. 
    - intros st Hsupp. 
      destruct (unif_sugar_pf_C_uniform_support C0 N0 (x-N0) pd st HValid Hunif Hsupp)
        as (i & [Hin_range Hdf]).
      assert (HiLt : (i >= inject_Z (Z.of_nat N0))%Q).
      { apply in_rangeQ_MN_ge with (N:= (x-N0)%nat). exact Hin_range. }
      destruct Hdf. 
      split; simpl; auto.  
      + apply in_supp_return_domain_eq in Hsupp. 
        apply dom_equiv_sym in Hsupp.
        apply dom_subset_eq_compat_left with (X:= dom pd); auto.
      +  destruct (evalB_st (C0 = i) st) eqn: HB; try contradiction.
        cbn [evalB_st] in HB. cbn [evalA_st] in *. 
        apply Qeq_bool_iff in HB. rewrite <- HB in HiLt. 
        destruct ((Qle_bool (inject_Z (Z.of_nat N0)) (get C0 st))) eqn: Hcontra ; try auto.
        simpl. 
        apply Qle_bool_iff in HiLt. 
        rewrite HiLt in Hcontra. inversion Hcontra.
  Qed.

  Lemma PDeter_or_add: forall b1 b2 pd1 pd2 (Hdom: (dom pd1 == dom pd2)%domain), 
  let pd:= (pd_add pd1 pd2 Hdom) in 
    Valid_dist (mu pd1) ->
    Valid_dist (mu pd2) -> 
    Valid_dist (mu pd) ->
    [[Pdeter (Dpred b1)]] pd1 ->
    [[Pdeter (Dpred b2)]] pd2 ->
    [[Pdeter (Dpred (b1 || b2))]] pd.
  Proof.
    intros b1 b2 pd1 pd2 Hdom pd Hv1 Hv2 Hv Hsat1 Hsat2.
    simpl in *.
    destruct Hsat1 as [Hdom1 Hsem1].
    destruct Hsat2 as [Hdom2 Hsem2].
    assert (Hdomsub: get_variables_in_bexp b1 ∪ get_variables_in_bexp b2 ⊆ dom pd1). {
      apply dom_subset_orb_fst_iff; intuition. 
      apply dom_subset_eq_compat_left with (X:= dom pd2); auto.
      apply dom_equiv_sym. auto.
    }
    split; auto.
    intros st Hsupp. 
    apply in_supp_mu_app_or with (mu0:= mu pd1) (mu1:= mu pd2) in Hsupp; auto;
        try apply dst_equiv_refl.
    split.
      + destruct Hsupp as [Hs1 | Hs2]. 
        * apply in_supp_return_domain_eq in Hs1. 
          apply dom_equiv_sym in Hs1. 
          apply dom_subset_eq_compat_left with (X:= dom pd1); auto.
        * apply in_supp_return_domain_eq in Hs2. 
          apply dom_equiv_sym in Hs2. 
          apply dom_subset_eq_compat_left with (X:= dom pd2); auto. 
          apply dom_subset_eq_compat_left with (X:= dom pd1); auto.
      + destruct Hsupp as [Hs1 | Hs2].
        * destruct (Hsem1 _ Hs1) as [_ Hb1].
          destruct (evalB_st b1 st) eqn:E1; simpl in Hb1; try contradiction.
          simpl. trivial.
        * destruct (Hsem2 _ Hs2) as [_ Hb2].
          destruct (evalB_st b2 st) eqn:E2; simpl in Hb2; try contradiction.
          destruct (evalB_st b1 st); simpl; trivial.
  Qed.

  Lemma Dirac_subset_supp_preserve: forall pd pd' X, 
    (supp_mu (mu pd') ⊆ supp_mu (mu pd))%supp ->
    (dom pd == dom pd')%domain ->
    Dirac_v X pd -> 
    Dirac_v X pd'.
  Proof. 
    intros pd pd' X Hsupp Hdom Hdir. destruct Hdir. destruct H0. 
    split. 
    - apply dom_subset_eq_compat_left with (X:= dom pd); auto.
    - exists x. intuition. apply H0. 
      apply in_supp_r_if_subset with (ls0:= supp_mu (mu pd')); auto.  
  Qed.

  Lemma Pdeter_L_implies_or: forall b b' pd, 
    [[Pdeter (Dpred b)]] pd -> 
    is_domain_subset (get_variables_in_bexp b') (dom pd) = true ->
    [[Pdeter (Dpred (b || b'))]] pd.
  Proof.
    intros. destruct H. split.
    - simpl. apply dom_subset_orb_fst_iff; intuition.
    - intros. split; try assumption.
      + simpl. simpl in H. apply in_supp_return_domain_eq in H2. apply dom_equiv_sym in H2.
        apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
        apply dom_subset_orb_fst_iff; intuition.
      + apply H1 in H2. destruct H2. 
        simpl. destruct (evalB_st b st) eqn: Hb; try contradiction. simpl. apply I.
  Qed.

   Lemma Pdeter_R_implies_or: forall b b' pd, 
    [[Pdeter (Dpred b')]] pd -> 
    is_domain_subset (get_variables_in_bexp b) (dom pd) = true ->
    [[Pdeter (Dpred (b || b'))]] pd.
  Proof.
    intros. destruct H. split.
    - simpl. apply dom_subset_orb_fst_iff; intuition.
    - intros. split; try assumption.
      + simpl. simpl in H. apply in_supp_return_domain_eq in H2. apply dom_equiv_sym in H2.
        apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
        apply dom_subset_orb_fst_iff; intuition.
      + apply H1 in H2. destruct H2. 
        simpl. destruct (evalB_st b' st) eqn: Hb; try contradiction. simpl.
        destruct (negb (negb (evalB_st b st) && false)) eqn: HB; try apply I.
        rewrite negb_false_iff in HB. 
        rewrite andb_false_r in HB. inversion HB.
  Qed. 

  Lemma Pde_morgan_and: forall b1 b2 pd, 
    Valid_dist (mu pd) ->
    [[Pdeter (Dpred ((~b1) && (~b2)))]] pd -> 
    [[~ (b1 || b2)]] pd.
  Proof.
    intros b1 b2 pd Hv Hsat. 
    assert (H: get_variables_in_bexp b1 ∪ get_variables_in_bexp b2 ⊆ dom pd). {
      apply dst_satisfy_df_implies_dom in Hsat. simpl in Hsat.
      auto.
    }
    apply andb_sem_conj in Hsat. 
    split; auto. 
    intros. split.
    - simpl. 
      apply in_supp_return_domain_eq in H0. 
      apply dom_equiv_sym in H0.
      apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
    - simpl. 
      destruct Hsat. destruct H1. 
      specialize (H3 st H0) . destruct H3. simpl in H4. 
      destruct (negb (evalB_st b1 st)) eqn: Hb1; try contradiction.
      destruct H2. 
      specialize (H5 st H0) . destruct H5. simpl in H6. 
      destruct (negb (evalB_st b2 st)) eqn: Hb2; try contradiction.
      simpl. auto.
  Qed.

  Lemma Pde_morgan_or: forall b1 b2 pd, 
    Valid_dist (mu pd) ->
    [[Pdeter (Dpred ((~b1) || (~b2)))]] pd -> 
    [[~ (b1 && b2)]] pd.
  Proof.
    intros b1 b2 pd Hv Hsat. 
    assert (H: get_variables_in_bexp b1 ∪ get_variables_in_bexp b2 ⊆ dom pd). {
      apply dst_satisfy_df_implies_dom in Hsat. simpl in Hsat.
      auto.
    }
    destruct Hsat. simpl in H0. 
    split; auto. intros. split.
    - simpl. 
      apply in_supp_return_domain_eq in H2. 
      apply dom_equiv_sym in H2.
      apply dom_subset_eq_compat_left with (X:= dom pd); try assumption.
    - simpl. 
      specialize (H1 st H2) . destruct H1. simpl in H3. 
      destruct (evalB_st b1 st) eqn: Hb1; 
      destruct (evalB_st b2 st) eqn: Hb2; try contradiction; simpl; auto.
  Qed.

  Lemma not_guard_sem: forall pd,  
    Valid_dist (mu pd) ->
    [[(~ B_VN) && (~ B_CN)]] pd ->
    [[~ guard]] pd.
  Proof. 
    intros pd HV H. unfold guard. 
    apply Pde_morgan_and in H; auto. 
    destruct H. split.
    - simpl. simpl in H. auto.
    - intros. apply H0 in H1. destruct H1. split. 
      + simpl. simpl in H1. auto.
      + destruct (evalB_st (~ B_VN || B_CN) st) eqn: HB; try contradiction. 
        cbn [evalB_st] in HB. rewrite negb_true_iff in HB. 
        destruct (evalB_st (~ B_VN || (~ B_VN) && B_CN) st) eqn: HB'; try auto.
        cbn [evalB_st] in HB'. rewrite negb_false_iff in HB'. 
        unfold Bor in HB, HB'. rewrite evalB_Bnot_false_iff in HB. 
        cbn [evalB_st] in HB, HB'. apply andb_true_iff in HB.
        rewrite negb_true_iff in HB'. destruct HB.
        rewrite H3 in HB'. 
        rewrite negb_true_iff in H4. rewrite H4 in HB'. 
        simpl in HB'. inversion HB'.
  Qed.

  Lemma body_correct : 
    {{ phi0 /\ [[Pdeter (Dpred guard)]] }} While_body {{ invariant }}.
  Proof.
    unfold While_body. 
    assert (HN0: (0 < N)%nat). { apply from_Q_ineq_to_nat_sub1_pos in HN. lia. }
    apply hoare_consequence_pre with (P':= phi0).
    { 
      apply hoare_seq with (Q:= (phi0_L /\ (Dirac_v V))%assertion). 
      - unfold phi0_R, DA_V_mult, B_VR. unfold phi0_L, B_VN. 
        apply hoare_seq with (Q:= (([[V < Aco 2 * inject_Z (Z.of_nat N)]] 
                                    /\ C_unif_depend_to_0v2 C V)%assertion 
                                    /\ (Dirac_v V))%assertion ).
        + apply hoare_seq with (Q:= 
            (assert_Odot [[dist_bit]] 
                         ([[V < 2%Q * inject_Z (Z.of_nat N)]] /\ C_unif_depend_to_0v2 C V) 
              /\ (Dirac_v V))%assertion).
          * apply hoare_consequence with 
            (P':= (([[V < Aco 2 * inject_Z (Z.of_nat N)]] /\ C_unif_and_bit_to_0v2 C Bit V)%assertion 
                    /\ (Dirac_v V))%assertion) 
            (Q':= (([[V < Aco 2 * inject_Z (Z.of_nat N)]] /\ C2_unif_and_bit_to_0v2 C Bit V)%assertion 
                    /\ (Dirac_v V))%assertion).
          ** apply hoare_conj.
            { 
              apply hoare_Frame_sem; intuition. 
              - apply WD_Pdeter; apply WD_Dpred.
              - unfold DA_C_mult. unfold hoare_triple. intros. 
                inversion H2; subst. 
                destruct H3 as [NV (HNV & Heven & (Hin & Hsem))].
                unfold C2_unif_and_bit_to_0v2. exists NV. intuition.
                + apply in_supp_DAssn_under_dstate_inv in H3. 
                  destruct H3 as [st0 (Hin0 & Heq)].
                  specialize Hin with st0. apply Hin in Hin0. 
                  apply st_eq_implies_get_eq with (x:= V) in Heq.
                  cbn [evalA_st] in *. rewrite Heq. 
                  rewrite update_neq; try assumption. 
                  simpl. auto. 
                + unfold mkfs_outer in *. unfold c_i_and_bit, c2_i_and_bit in *. 
                  apply unif_sugar_after_assign_shift_aexp; try assumption. 
                  simpl. auto. 
            }
            unfold hoare_triple. intros. destruct H3. split; auto.
            -- apply dom_subset_trans with (l1:= dom pd); auto. 
              apply subset_NS in H2; intuition.
              apply Valid_forall_NS in H2; auto.
            -- destruct H4. exists x. intros. inversion H2; subst.
              apply in_supp_DAssn_under_dstate_inv in H5. destruct H5. 
              destruct H5. apply H4 in H5. cbn [evalA_st] in *. 
              apply st_eq_implies_get_eq with (x:= V) in H6. rewrite H6.
              rewrite update_neq; try assumption. simpl. auto.
          ** unfold assert_implies. intros. destruct H1. split; auto.
            apply assert_Odot_implies; intuition.
          ** unfold invariant. 
            apply assert_trans with (R:= (([[V < 2%Q * inject_Z (Z.of_nat N)]] /\ 
                                            C_unif_depend_to_0v C V)%assertion /\ (Dirac_v V))%assertion).
            -- unfold assert_implies. intros. intuition. 
              unfold C2_unif_and_bit_to_0v2,Unif_Depend_and, mkfs_outer,c2_i_and_bit in H3. 
              unfold C_unif_depend_to_0v,Unif_Depend_by.
              destruct H4 as [NV (HNV & Heven & (Hin & Hsem))]. 
              exists NV. split; try lia. split; try assumption. 
              split; try apply WD_list_C_uniform. 
              apply test_sub in Hsem.
              unfold pf_C_uniform. apply unif_sugar_even_odd; auto. 
              apply Nat.even_spec. auto.
            -- apply assert_trans with (R:=  
                  (assert_Oplus ([[Pdeter (Dpred B_VN)]] /\ C_unif_depend_to_0v C V)
                                ([[Pdeter (Dpred B_VR)]] /\ C_unif_depend_to_0v C V) /\ (Dirac_v V))%assertion).
              ++ unfold B_VR, B_VN. unfold assert_implies. intros. intuition. 
                apply split_lt_2n_nat in H1; intuition.
                +++ right. left. intuition.
                +++ right. right. intuition.
              ++ apply assert_trans with (R:=  
                  ((assert_Oplus ([[Pdeter (Dpred B_VN)]] /\ C_unif_depend_to_0v C V) 
                                 ([[Pdeter (Dpred B_VR)]] /\ (assert_Oplus ([[phi1]]) (C_unif_depend_to_nv C V N))))
                   /\ (Dirac_v V))%assertion).
                +++ {
                      unfold assert_implies. intros. intuition. 
                      destruct H2.
                      - destruct H1 as (p1 & p2 & Hp1 & Hp2 & Hsum & Hrest). 
                        destruct Hrest as (pd1 & pd2 & Hrest). left. 
                        exists p1, p2. intuition. exists pd1, pd2. intuition.
                        unfold phi1. apply decom_C_unif_0v_to_oplus; auto.
                        unfold B_VR, B_VN in H12.
                        apply andb_sem_conj in H12.
                        destruct H12. auto.
                      - destruct H1. 
                        + right. left. intuition.
                        + right. right. intuition. 
                          unfold phi1. apply decom_C_unif_0v_to_oplus; auto.
                          unfold B_VR, B_VN in H2.
                          apply andb_sem_conj in H2.
                          destruct H2. auto.
                  }
                +++ fold phi0_L.  
                    apply assert_trans with (R:= 
                        (assert_Oplus phi0_L
                                      (assert_Oplus (([[Pdeter (Dpred B_VR)]] /\ [[~ B_CN]])%assertion 
                                                        /\ [[phi1]])%assertion
                                                    (([[Pdeter (Dpred (B_VR && B_CN))]])%assertion 
                                                        /\ (C_unif_depend_to_nv C V N))%assertion) 
                        /\ Dirac_v V)%assertion).
                  {
                    unfold assert_implies. intros. intuition. 
                    destruct H2.
                    - destruct H1. destruct H1. left. exists x,x0. intuition.
                      destruct H8. destruct H6. exists x1,x2. intuition.
                      destruct H15. 
                      + destruct H15. destruct H15. left. exists x3, x4. intuition. 
                        destruct H22. destruct H20. exists x5, x6. intuition.
                        * apply df_add_sem_decom with (pd0:= x5) (pd1:= x6) (pd:= x2) (p1:= x3) in H13; intuition. 
                          rewrite Rplus_comm in H16. apply Rplus_1_minus_r in H16. rewrite <- H16. auto.
                        * unfold phi1 in H25. unfold B_CN. 
                          apply unif_pf_C_uniform_lt in H25; auto; try lia.
                          apply PDeter_lt_le_inv; auto. 
                        * apply df_add_sem_decom with (pd0:= x5) (pd1:= x6) (pd:= x2) (p1:= x3) in H13; intuition. 
                          ** apply andb_sem_conj. intuition. 
                            apply unif_depend_pf_C_uniform_ge; auto.
                          ** rewrite Rplus_comm in H16. apply Rplus_1_minus_r in H16. rewrite <- H16. auto.
                      + destruct H15. 
                        * right. left. intuition. 
                          unfold phi1 in H15. unfold B_CN. 
                          apply unif_pf_C_uniform_lt in H15; auto; try lia.
                          apply PDeter_lt_le_inv; auto. 
                        * right. right. intuition. apply andb_sem_conj. intuition. 
                          apply unif_depend_pf_C_uniform_ge; auto.
                    - destruct H1. 
                      + right. left. intuition.
                      + right. right. intuition. destruct H4. 
                        * destruct H1. destruct H1. left. exists x,x0. intuition. 
                          destruct H9. destruct H7. exists x1,x2. intuition.
                          ** apply df_add_sem_decom with (pd0:= x1) (pd1:= x2) (pd:= pd) (p1:= x) in H2; intuition. 
                            rewrite Rplus_comm in H4. apply Rplus_1_minus_r in H4. rewrite <- H4. auto.
                          ** unfold phi1 in H12. unfold B_CN. 
                            apply unif_pf_C_uniform_lt in H12; auto; try lia.
                            apply PDeter_lt_le_inv; auto. 
                          ** apply df_add_sem_decom with (pd0:= x1) (pd1:= x2) (pd:= pd) (p1:= x) in H2; intuition. 
                            -- apply andb_sem_conj. intuition. 
                              apply unif_depend_pf_C_uniform_ge; auto.
                            -- rewrite Rplus_comm in H4. apply Rplus_1_minus_r in H4. rewrite <- H4. auto. 
                        * destruct H1. 
                          ** right. left. intuition. 
                            unfold phi1 in H1. unfold B_CN. 
                            apply unif_pf_C_uniform_lt in H1; auto; try lia.
                            apply PDeter_lt_le_inv; auto. 
                          ** right. right. intuition. 
                            apply andb_sem_conj. intuition. apply unif_depend_pf_C_uniform_ge; auto.
                  }

                  { 
                    unfold assert_implies. intros pd HV HZ Hsem. intuition. 
                    rename H into Hsem. rename H0 into HDirac. 
                    fold phi0_R in *.
                    destruct Hsem as [Hcase1 | Hsem]. 
                    + destruct Hcase1 as [p1 H]. destruct H as [p2 H].
                      destruct H as [Hp1 H]. destruct H as [Hp2 H]. destruct H as [Hp_eq H].
                      destruct H as [pd1 H]. destruct H as [pd2 H]. 
                      destruct H as [HWF1 H]. destruct H as [HWF2 H].
                      destruct H as [Hdom1 H]. destruct H as [Hdom2 H]. 
                      destruct H as [Hsem0 H]. destruct H as [Hsem1 H].
                      destruct H as [Hsum1 H]. destruct H as [Hsum2 Heq]. 
                      destruct Hsem1 as [Hsem11 | Hsem12]. 
                      * destruct Hsem11 as [p4 H]. destruct H as [p3 H]. 
                        destruct H as [Hp4 H]. destruct H as [Hp3 H]. 
                        destruct H as [Hp_eq' H].
                        destruct H as [pd4 H]. destruct H as [pd3 H]. 
                        destruct H as [HWF4 H]. destruct H as [HWF3 H].
                        destruct H as [Hdom4 H]. destruct H as [Hdom3 H]. 
                        destruct H as [Hsem4 H]. destruct H as [Hsem3 H].
                        destruct H as [Hsum4 H]. destruct H as [Hsum3 Heq'].
                        left. exists (1 - p2*p4)%R, (p2*p4)%R. 
                        assert (Hp24: 0 < (p2*p4)%R < 1). {
                          destruct Hp2; destruct Hp4.
                          split; try apply Rmult_lt_0_compat; try assumption.
                          rewrite <- Rmult_1_l. apply Rmult_gt_0_lt_compat; try assumption.
                          apply Rlt_0_1. } 
                        assert (Hp24_1: 0 < (1 - p2*p4)%R < 1). {
                          apply Rp_lt1_minus_p_bounds with (p:= (p2 * p4)%R). assumption. } 
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
                          rewrite Rplus_comm in Hp_eq'.
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
                        split. { 
                          split. 
                          - unfold phi0. split. 
                            { left. exists p1', p2'. intuition. 
                              - apply Rplus_sub_lt_1 in Hsum12'; destruct Hsum12'; assumption. 
                              - apply Rplus_sub_lt_1 in Hsum12'; destruct Hsum12'; assumption.
                              - exists pd1, pd3. intuition.
                                * simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
                                rewrite Hsum3. rewrite Hsum2. rewrite Hsum1.
                                rewrite <- Rmult_plus_distr_r. rewrite Hsum12'. rewrite Rmult_1_l. reflexivity.
                                * simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
                                rewrite Hsum3. rewrite Hsum2. rewrite Hsum1.
                                rewrite <- Rmult_plus_distr_r. rewrite Hsum12'. rewrite Rmult_1_l. reflexivity.
                                * simpl. apply dst_equiv_refl. 
                            }
                            apply Dirac_subset_supp_preserve with (pd:= pd); 
                              try assumption; try apply dom_equiv_refl.
                            simpl. rewrite Rplus_comm in Hsum12'. 
                            apply Rplus_1_minus_r in Hsum12'. rewrite Hsum12'.
                            rewrite <- supp_eq_linear; auto; try lra.
                            apply dst_equiv_implies_beq_supp in Heq; auto.
                            + apply supp_eq_implies_subset_conj in Heq. 
                              apply supp_subset_trans with (ls1:= supp_mu (p1 * mu pd1 + p2 * mu pd2)%dist_state); intuition;
                                try apply Sort_supp_if_WF_supp.
                              rewrite Rplus_comm in Hp_eq. 
                              apply Rplus_1_minus_r in Hp_eq. rewrite Hp_eq.
                              rewrite <- supp_eq_linear; auto; try lra.
                              apply dst_equiv_implies_beq_supp in Heq'; auto.
                              * apply supp_mu_subset_add_l; try apply Sort_supp_if_WF_supp. split.
                                ** apply supp_mu_subset_decom_add_l.
                                ** apply supp_eq_implies_subset_conj in Heq'. 
                                  apply supp_subset_trans with (ls1:= supp_mu (mu pd2)); intuition;
                                  try apply Sort_supp_if_WF_supp.
                                  -- rewrite Rplus_comm in Hp_eq'. 
                                    apply Rplus_1_minus_r in Hp_eq'. rewrite Hp_eq' in H17.
                                    rewrite <- supp_eq_linear in H17; auto; try lra.  
                                    apply supp_subset_trans with (ls1:= supp_mu (mu pd4 + mu pd3)%dist_state); intuition;
                                      try apply Sort_supp_if_WF_supp.
                                    apply supp_mu_subset_decom_add_r. 
                                  -- apply supp_mu_subset_decom_add_r.
                              * apply Valid_linear; auto; try lra. 
                            + apply Valid_linear; auto; try lra. 
    
                          - unfold guard. 
                            unfold phi0_L in Hsem0. 
                            assert (Hdom': (dom (cofe_pd pd1 p1') == dom (cofe_pd pd3 p2'))%domain). {
                              simpl. apply dom_equiv_sym. 
                              apply dom_equiv_trans with (l1:= dom pd); auto. 
                              apply dom_equiv_sym. auto.
                            }
                            assert (Heqpd: pd0 ≡ pd_add (cofe_pd pd1 p1') (cofe_pd pd3 p2') Hdom'). {
                              simpl. split; simpl; try apply dst_equiv_refl.
                              apply dom_equiv_sym. auto.
                            }
                            apply pd_equiv_preserves_sem with (pd0:= pd_add (cofe_pd pd1 p1') (cofe_pd pd3 p2') Hdom'); intuition.
                            + simpl. apply Valid_linear; auto; try lra.
                            + simpl. apply Valid_linear; auto; try lra.
                            + apply WD_Pdeter; try apply WD_Dpred; try lra. 
                            + eapply PDeter_or_add; intuition. 
                              * simpl. apply Valid_mult_cofe; auto; try lra.
                              * simpl. apply Valid_mult_cofe; auto; try lra.
                              * simpl. apply Valid_linear; auto; try lra.
                              * destruct H7. split; intuition. apply H16. 
                                simpl in H17. rewrite <- supp_eq_mult_coef in H17; try lra. auto.
                              * unfold phi0_R in Hsem3. destruct Hsem3. 
                                apply andb_sem_conj; intuition. 
                                ** unfold B_VR in H16. 
                                  apply andb_sem_conj in H16; intuition. 
                                  apply andb_sem_conj in H18; intuition. 
                                  destruct H16. split; intuition. 
                                  apply H18. simpl in H21.
                                  rewrite <- supp_eq_mult_coef in H21; try lra. auto.
                                ** apply andb_sem_conj in H16; intuition. 
                                  destruct H19. split; intuition. apply H19. 
                                  simpl in H20. rewrite <- supp_eq_mult_coef in H20; try lra. auto.
                        }                           

                        split; try assumption. {
                          split; auto. 
                          apply not_guard_sem; auto.
                          apply andb_sem_conj; intuition.
                          destruct H13. split. 
                            + simpl. simpl in H7. auto.
                            + intros. apply H13 in H15. destruct H15.
                              split. 
                              * simpl. simpl in H15. auto.
                              * unfold B_VR in H16. cbn [evalB_st] in *.
                                destruct ((negb (evalB_st B_VN st) && 
                                          evalB_st (V < 2%Q * inject_Z (Z.of_nat N)) st)%bool) eqn: HB; try contradiction.
                                apply andb_true_iff in HB. destruct HB. 
                                rewrite H17. auto. 
                        }

                        split. { 
                          simpl. rewrite dst_sum_prob_decom. repeat rewrite dst_sum_prob_coef_mult.
                          rewrite Hsum3. rewrite Hsum2. rewrite Hsum1.
                          rewrite <- Rmult_plus_distr_r. rewrite Hsum12'. rewrite Rmult_1_l. reflexivity. }
                          simpl.
                        split. { rewrite Hsum4. assumption. } 
                        apply dst_equiv_trans with (mu1:= (p1 * mu pd1 + p2 * mu pd2)%dist_state); try assumption.
                        apply dst_equiv_trans with (mu1:= (p1 * mu pd1 + p2 * (p3 * mu pd3 + p4 * mu pd4)%dist_state)%dist_state).
                        ** apply dst_add_inj_l. apply dst_mult_preserves_equiv. 
                          apply dst_equiv_trans with (mu1:= (p4 * mu pd4 + p3 * mu pd3)%dist_state); auto.
                          apply dst_add_comm.
                        ** rewrite dst_mult_plus_distr_r_eq. rewrite dst_add_assoc_eq. 
                        rewrite dst_mult_plus_distr_r_eq with (p:= (1 - p2 * p4)%R). 
                        apply dst_add_preserves_equiv.
                        -- repeat rewrite dst_mult_assoc_eq. unfold p1', p2'. unfold Rdiv.  
                          rewrite <- Rmult_assoc. rewrite <- Rmult_assoc with (r1:= (1 - p2 * p4)%R). 
                          repeat rewrite Rinv_r_simpl_m; try apply dst_equiv_refl; try apply Rgt_not_eq; assumption. 
                        -- rewrite dst_mult_assoc_eq. apply dst_equiv_refl.
                      * destruct Hsem12 as [H | H]. 
                        ** left. exists p1, p2. intuition. exists pd1, pd2. intuition. 
                          -- unfold phi0. intuition. 
                            ++ right. left. intuition.
                            ++ apply Dirac_subset_supp_preserve with (pd:= pd); auto. 
                              +++ apply dst_equiv_implies_beq_supp in Heq; auto.
                                --- apply supp_eq_implies_subset_conj in Heq. 
                                    apply supp_subset_trans with (ls1:= supp_mu (p1 * mu pd1 + p2 * mu pd2)%dist_state); intuition;
                                      try apply Sort_supp_if_WF_supp.
                                    rewrite Rplus_comm in Hp_eq. 
                                    apply Rplus_1_minus_r in Hp_eq. rewrite Hp_eq. 
                                    rewrite <- supp_eq_linear; try lra.
                                    apply supp_mu_subset_decom_add_l.
                                --- apply Valid_linear; try lra; auto.
                              +++ apply dom_equiv_sym. auto.
                          -- unfold guard. unfold phi0_L in Hsem0. destruct Hsem0.
                            apply Pdeter_L_implies_or; intuition. 
                            cbn [get_variables_in_bexp]. 
                            apply dst_satisfy_df_implies_dom in H4.
                            cbn [get_var_in_Pformular get_var_in_Dformular get_variables_in_bexp] in H4. 
                            apply dom_subset_orb_fst_iff; intuition.
                            apply dst_satisfy_df_implies_dom in H6.
                            cbn [get_var_in_Pformular get_var_in_Dformular get_variables_in_bexp] in H6. 
                            apply dom_subset_eq_compat_left with (X:= dom pd2); try assumption.
                            apply dom_equiv_sym in Hdom1.
                            apply dom_equiv_trans with (l1:= dom pd); auto.
                          -- unfold guard. apply Pde_morgan_and; auto. 
                            apply andb_sem_conj; intuition.
                            ++ unfold B_VR in H. apply andb_sem_conj in H; intuition.
                            ++ apply Pde_morgan_or; auto. 
                              apply Pdeter_R_implies_or; auto. 
                              cbn [get_variables_in_bexp]. 
                              apply dst_satisfy_df_implies_dom in H.
                              cbn [get_var_in_Pformular get_var_in_Dformular get_variables_in_bexp] in H. 
                              simpl in H. simpl. auto.
                        ** right. left. intuition. 
                          -- unfold phi0. intuition.  
                             left. exists p1, p2. intuition. exists pd1, pd2. intuition.
                          -- unfold guard. unfold phi0_L in Hsem0. destruct Hsem0. 
                            unfold phi0_R in H. destruct H. 
                            assert (Hdom12: (dom (cofe_pd pd1 p1) == dom (cofe_pd pd2 p2))%domain). {
                              simpl. apply dom_equiv_sym. 
                              apply dom_equiv_trans with (l1:= dom pd); auto. 
                              apply dom_equiv_sym. auto.
                            }
                            assert (Heqpd: pd ≡ pd_add (cofe_pd pd1 p1) (cofe_pd pd2 p2) Hdom12). {
                              simpl. split; simpl; try apply dst_equiv_refl; auto.
                              apply dom_equiv_sym. auto.
                            }
                            apply pd_equiv_preserves_sem with (pd0:= pd_add (cofe_pd pd1 p1) (cofe_pd pd2 p2) Hdom12); intuition.
                            ++ simpl. apply Valid_linear; try lra; auto.
                            ++ apply WD_Pdeter; try apply WD_Dpred; try lra. 
                            ++ eapply PDeter_or_add; intuition. 
                              *** simpl. apply Valid_mult_cofe; auto; try lra.
                              *** simpl. apply Valid_mult_cofe; auto; try lra.
                              *** simpl. apply Valid_linear; auto; try lra.
                              *** destruct H4. split; intuition. apply H7. 
                                  simpl in H8. rewrite <- supp_eq_mult_coef in H8; try lra. auto.
                              *** apply andb_sem_conj in H.
                                apply andb_sem_conj; intuition. 
                                --- unfold B_VR in H7. 
                                  apply andb_sem_conj in H7; intuition. 
                                  destruct H. split; intuition. 
                                  apply H7. simpl in H10.
                                  rewrite <- supp_eq_mult_coef in H10; try lra. auto.
                                --- destruct H8. split; intuition. apply H8. 
                                    simpl in H9. rewrite <- supp_eq_mult_coef in H9; try lra. auto.

                    + destruct Hsem. 
                      * right. left. unfold phi0. intuition. 
                        -- right. intuition.
                        -- unfold guard. unfold phi0_L in H. destruct H. 
                          apply Pdeter_L_implies_or; auto. 
                          cbn [get_variables_in_bexp]. 
                          apply dst_satisfy_df_implies_dom in H.
                          cbn [get_var_in_Pformular get_var_in_Dformular get_variables_in_bexp] in H. 
                          apply dom_subset_orb_fst_iff; intuition.
                          apply dom_subset_unif_0V in H0. 
                          simpl. simpl in H0. auto.
                      * destruct H.  
                        ** destruct H as [p1 H]. destruct H as [p2 H].
                          destruct H as [Hp1 H]. destruct H as [Hp2 H]. destruct H as [Hp_eq H].
                          destruct H as [pd1 H]. destruct H as [pd2 H]. 
                          destruct H as [HWF1 H]. destruct H as [HWF2 H].
                          destruct H as [Hdom1 H]. destruct H as [Hdom2 H]. 
                          destruct H as [Hsem0 H]. destruct H as [Hsem1 H].
                          destruct H as [Hsum1 H]. destruct H as [Hsum2 Heq]. 
                          left. exists p2, p1. intuition; try lra.
                          exists pd2, pd1. intuition. 
                          -- unfold phi0. intuition. 
                            ++ right. intuition.
                            ++ apply dom_equiv_sym in Hdom2. 
                              apply Dirac_subset_supp_preserve with (pd:= pd); 
                              try assumption; try apply dom_equiv_refl.
                              simpl. rewrite Rplus_comm in Hp_eq. 
                              apply Rplus_1_minus_r in Hp_eq. rewrite Hp_eq in Heq.
                              apply dst_equiv_implies_beq_supp in Heq; auto; 
                              try apply Valid_linear; auto; try lra. 
                              apply supp_eq_implies_subset_conj in Heq. 
                              apply supp_subset_trans with (ls1:= supp_mu (p1 * mu pd1 + (1 - p1) * mu pd2)%dist_state); intuition;
                                try apply Sort_supp_if_WF_supp.
                              rewrite <- supp_eq_linear; auto; try lra.
                              apply supp_mu_subset_decom_add_r.
                          
                          -- unfold phi0_R in Hsem1. destruct Hsem1. unfold guard. 
                              apply Pdeter_R_implies_or; auto. 
                              ++ apply andb_sem_conj in H3; intuition. 
                              apply andb_sem_conj; intuition.
                              unfold B_VR in H8. apply andb_sem_conj in H8; intuition.    
                              ++ apply andb_sem_conj in H3; intuition. 
                              cbn [get_variables_in_bexp]. 
                              apply dst_satisfy_df_implies_dom in H8.
                              simpl in H8. simpl. auto.
                          -- apply not_guard_sem; auto.
                            apply andb_sem_conj; intuition. 
                            unfold B_VR in H5. apply andb_sem_conj in H5; intuition.
                          -- apply dst_equiv_trans with (mu1:= (p1 * mu pd1 + p2 * mu pd2)%dist_state); auto. 
                            apply dst_add_comm.
                        ** destruct H. 
                          -- right. right. intuition. 
                            apply not_guard_sem; auto.
                            apply andb_sem_conj; intuition. 
                            unfold B_VR in H. apply andb_sem_conj in H; intuition.
                          -- right. left. intuition. 
                            ++ unfold phi0. intuition. right. auto.
                            ++ unfold phi0_R in H. destruct H. unfold guard. 
                              apply Pdeter_R_implies_or; auto. 
                              +++ apply andb_sem_conj in H; intuition. 
                                apply andb_sem_conj; intuition.
                                unfold B_VR in H1. apply andb_sem_conj in H1; intuition.    
                              +++ apply andb_sem_conj in H; intuition. 
                                cbn [get_variables_in_bexp]. 
                                apply dst_satisfy_df_implies_dom in H1.
                                simpl in H1. simpl. auto.
                  }

                      
          * unfold hoare_triple. intros. 
            inversion H2; subst. destruct H3 as ((H3a & H3b) & HDirac).
            unfold C_unif_depend_to_0v2 in H3b. 
            destruct H3b as [NV (HNV & (Heven & Hsem))].
            destruct Hsem as [Hsupp Hsem].
            unfold assert_Odot.
            
            pose (pd0:= Identify_pd).
            pose (X:= (singleton_bool_list C) ∪ (singleton_bool_list V)).
            assert (Hdom: X ⊆ dom pd). { 
              apply dst_satisfy_df_implies_dom in H3a. 
              apply satisfy_implies_dom_sub in Hsem; try assumption.
              - unfold X. apply dom_subset_orb_fst_iff. split. 
                + rewrite get_var_in_unif_MN in Hsem; [simpl; auto| apply Nat.div_str_pos; lia].
                + simpl. simpl in H3a. intuition. 
              - apply WD_Unif_MN. apply Nat.div_str_pos; lia.
            }
            pose (pd_inde:= restrict_pd pd X Hdom).
            assert (Hvar: dom pd0 ∩∅ dom pd_inde). { simpl. auto. }
            pose (pd':= RAssn_under_pd Bit Vbit_01 pd HWFa).

            assert (Htmp: {|
                dom := dom pd0 ∪ dom pd_inde;
                mu := mu pd0 ⊗ mu pd_inde;
                all_partial := PD_combine_invar_mu pd0 pd_inde Hvar
                |} ⊑ pd). { 
                split.
                - cbn [dom]. apply dom_subset_orb_fst_iff. split.
                  + simpl. auto.
                  + simpl. intuition. 
                - cbn [mu]. cbn [dom]. cbv [pd0]. 
                  apply dst_equiv_trans with (mu1:= mu pd_inde); try apply
                    combine_Identify_pd.
                  simpl. apply dst_equiv_refl.
                }  
                
            eapply readc_local_execution_exists with (c:= RA_Bit) (pd':= pd') in Htmp; 
              try assumption.
            { destruct Htmp as [pd0' (HNS & Hcomb)].
              assert(Hdom0': dom pd0' = singleton_bool_list Bit). {
                  inversion HNS; subst. simpl. auto. }
              assert (Hvar' : dom pd0' ∩∅ dom pd_inde). { simpl. rewrite Hdom0'. auto. }
              split; try intuition.
              {
                exists pd0', pd_inde, Hvar'. intuition.
                * simpl. apply Valid_forall_NS with (c:= RA_Bit) (pd:= pd0); 
                    try assumption. apply Valid_Iden.
                * simpl. apply Valid_after_resX. assumption.
                * eapply hoare_Rasgn with (pd:= pd0) (a1:= Aco 0) (a2:= Aco 1) (X:= Bit); intuition.
                  + apply WD_Pplus; try apply WD_Pdeter; try apply WD_Dpred; try lra. 
                  + apply Valid_Iden.
                  + cbn. intuition. unfold state_inject_Z, var_inject_Z, Empty_State. now constructor.
                  + unfold RA_Bit, Bit, Vbit_01, Bit_01 in HNS. unfold Bit. exact HNS.
                  + unfold PAssertion_sub. intros. split. 
                    - simpl. auto.
                    - intros. split; try assumption.
                    -- apply in_supp_return_domain_eq in H3. simpl in H3. 
                      apply dom_equiv_sym in H3.
                      apply dom_subset_eq_compat_left with (X:= [true]); try assumption.
                    -- apply in_supp_DAssn_under_dstate_inv in H3. destruct H3 as [st0 (Hin & Heq)]. 
                      apply st_eq_implies_get_eq with (x:= Bit) in Heq. 
                      cbn [evalB_st] in *. cbn [evalA_st] in *. rewrite get_update_eq in Heq.
                      apply Qeq_bool_iff in Heq. rewrite Heq. auto.
                  + unfold PAssertion_sub. intros. split. 
                    - simpl. auto.
                    - intros. split; try assumption.
                    -- apply in_supp_return_domain_eq in H3. simpl in H3. 
                      apply dom_equiv_sym in H3.
                      apply dom_subset_eq_compat_left with (X:= [true]); try assumption.
                    -- apply in_supp_DAssn_under_dstate_inv in H3. destruct H3 as [st0 (Hin & Heq)]. 
                      apply st_eq_implies_get_eq with (x:= Bit) in Heq. 
                      cbn [evalB_st] in *. cbn [evalA_st] in *. rewrite get_update_eq in Heq.
                      apply Qeq_bool_iff in Heq. rewrite Heq. auto.

                * apply sem_satisfies_project_implies_V with (V:= X) (HV:= Hdom) in H3a; try assumption.
                  -- apply WD_Pdeter; try apply WD_Dpred. 
                  -- simpl. auto.
                * unfold C_unif_depend_to_0v2. exists NV. 
                  split; try lia. split; try assumption. 
                  split.
                  ++ intros. simpl in H3. apply in_supp_res_inv in H3. 
                    destruct H3 as [st0 (Hin & Heq)].
                    apply Hsupp in Hin. cbn [evalA_st] in *. rewrite <- Hin.
                    apply st_eq_implies_get_eq with (x:= V) in Heq. rewrite <- Heq.
                    apply get_res_st_to_X. intuition.
                  ++ apply sem_satisfies_project_implies_V with (V:= X) (HV:= Hdom) in Hsem; try assumption.
                  -- apply WD_Unif_MN. apply Nat.div_str_pos; lia.
                  -- rewrite get_var_in_unif_MN; [simpl; auto| apply Nat.div_str_pos; lia].
              }
              apply Dirac_RA_neq; auto.
            }  

            -- unfold RA_Bit. apply NCF_RAssign.
            -- simpl. auto.
            -- simpl. apply Valid_after_RA; try assumption. 
              split; simpl; try lra. unfold prob_is_positive; try lra.
            -- apply Valid_after_resX. assumption.
            -- simpl. apply Valid_Iden.
        + apply hoare_conj. 
          { 
            apply hoare_conj.
            - apply hoare_consequence_pre with (P':= 
                ([[V < Aco 2%Q * inject_Z (Z.of_nat N)]] [V |-> Aco 2%Q * V])%assertion); 
                try apply hoare_Dasgn.
              unfold assert_implies. intros. 
              assert (HWFa: WF_aexp_with_pd (Aco 2%Q * V) pd). { 
                unfold WF_aexp_with_pd.
                apply dst_satisfy_df_implies_dom in H1. 
                simpl in H1. intuition. }
              assert (Hwf : well_defined_Pf (V < Aco 2%Q * inject_Z (Z.of_nat N))). {
                apply WD_Pdeter; try apply WD_Dpred; simpl; auto. }
              apply (proj2 (pf_sub_eq V (Aco 2%Q * V) (V < Aco 2%Q * inject_Z (Z.of_nat N)) pd HWFa Hwf H)).
              apply testVmult; try assumption; try lra. vm_compute. auto.
            - unfold hoare_triple. intros. inversion H2; subst. 
              unfold C_unif_depend_to_0v2.
              unfold C_unif_depend_to_nv in H3. destruct H3 as [NV (HNV & (Hin & Hsem))].
              exists (2*NV)%nat. split; try lia. split.
              * unfold Nat.Even. exists NV. auto.
              * split. 
                + intros. apply in_supp_DAssn_under_dstate_inv in H3. 
                  destruct H3 as [st0 (Hin0 & Heq)].
                  specialize Hin with st0. apply Hin in Hin0. 
                  apply st_eq_implies_get_eq with (x:= V) in Heq.
                  cbn [evalA_st] in *. rewrite Heq. 
                  rewrite get_update_eq. 
                  rewrite Hin0. 
                  change (inject_Z 2 * inject_Z (Z.of_nat NV) == inject_Z (Z.of_nat (2 * NV)))%Q.
                  rewrite <- inject_Z_mult.
                  change (inject_Z (2 * Z.of_nat NV) == inject_Z (Z.of_nat (2 * NV)))%Q.
                  f_equal.
                  rewrite Nat2Z.inj_mul.
                  reflexivity.
                + destruct Hsem as [HwD Hsem]. 
                  rewrite Nat.mul_comm. rewrite Nat.div_mul; try lia.
                  apply intersect_preserves_satisfy with (pd:= pd) (c:= V ::= 2%Q * V); try assumption.
                  ++ apply WD_Unif_MN. lia.
                  ++ simpl. rewrite get_var_in_unif_MN; try lia. simpl. auto.
          }
          unfold hoare_triple. intros. inversion H2; subst.
          destruct H3. destruct H4. split.
          * apply dom_subset_trans with (l1:= dom pd); auto. 
            simpl. apply dom_subset_orb_dom_r. apply dom_subset_refl.
          * exists (2*x)%Q. intros. 
            apply in_supp_DAssn_under_dstate_inv in H5. 
            destruct H5. destruct H5. apply H4 in H5. 
            cbn [evalA_st] in *. 
            apply st_eq_implies_get_eq with (x:= V) in H6. 
            rewrite H6. rewrite get_update_eq.
            rewrite H5. reflexivity.

      - unfold IF_VN,phi0,phi0_L,phi0_R. 
        apply hoare_consequence_pre with (P':=  
            ((assert_Oplus ([[Pdeter (Dpred B_VN)]] /\ (C_unif_depend_to_0v C V))%assertion   
                           ([[(~ B_VN) && ((V < 2%Q * inject_Z (Z.of_nat N)) && B_CN)]] /\ 
                              (C_unif_depend_to_nv C V N))) 
              /\ (Dirac_v V))%assertion).
        + 
            unfold B_VN, B_VR. eapply hoare_cond_sem; try apply hoare_skip.
            apply hoare_seq with (Q:= (([[Pdeter (Dpred B_VN)]] /\ C_unif_depend_to_nvn1 C V N)%assertion 
                                      /\ (Dirac_v V))%assertion).
            * unfold B_VN. apply hoare_conj.
              {
                apply hoare_Frame_sem; 
                  try apply WD_Pdeter; try apply WD_Dpred; simpl; auto. 
                unfold DA_C_minus. unfold hoare_triple. intros. 
                unfold C_unif_depend_to_nvn1 in H3. unfold C_unif_depend_to_0v.
                inversion H2; subst. destruct H3 as [NV (HNV & (Hin & Hsem))].
                exists NV. split; try lia. split.
                + intros. apply in_supp_DAssn_under_dstate_inv in H3. 
                  destruct H3 as [st0 (Hin0 & Heq)].
                  specialize Hin with st0. apply Hin in Hin0. 
                  rewrite <- Hin0.
                  apply st_eq_implies_get_eq with (x:= V) in Heq.
                  rewrite Heq. rewrite update_neq; auto with *. 
                + split; try apply WD_list_C_uniform.
                  apply uniform_after_assign_shift; assumption.  
              }

              unfold hoare_triple. intros. inversion H2; subst.
              destruct H3. split; intuition.
              -- apply dom_subset_trans with (l1:= dom pd); auto. 
              apply subset_NS in H2; intuition.
              apply Valid_forall_NS in H2; auto.
              -- destruct H4. exists x. 
              intros. 
              apply in_supp_DAssn_under_dstate_inv in H5. destruct H5. 
              destruct H5. apply H4 in H5. cbn [evalA_st] in *. 
              apply st_eq_implies_get_eq with (x:= V) in H6. rewrite H6.
              rewrite update_neq; try assumption. simpl. auto.
              
            * apply hoare_consequence_pre with (P':= 
              (([[V - Aco (inject_Z (Z.of_nat N)) < inject_Z (Z.of_nat N)]] 
                /\ C_unif_depend_to_nv C V N)%assertion
                  /\ (Dirac_v V))%assertion).
              { 
                apply hoare_conj.
                + unfold DA_V_minus. unfold B_VN. apply hoare_conj.
                  - apply hoare_consequence_pre with 
                      (P':= ([[V < inject_Z (Z.of_nat N)]] [V |-> V - inject_Z (Z.of_nat N)])%assertion);
                      try apply hoare_Dasgn.
                    unfold assert_implies. intros. 
                    assert (HWFa: WF_aexp_with_pd (V - inject_Z (Z.of_nat N)) pd). { 
                      unfold WF_aexp_with_pd.
                      apply dst_satisfy_df_implies_dom in H1. 
                      simpl in H1. intuition. }
                    assert (Hwf : well_defined_Pf (V < inject_Z (Z.of_nat N))). {
                      apply WD_Pdeter; try apply WD_Dpred; simpl; auto. }
                    apply (proj2 (pf_sub_eq V (V - inject_Z (Z.of_nat N)) (V < inject_Z (Z.of_nat N)) pd HWFa Hwf H)).
                    apply testV; try assumption.
                  - unfold hoare_triple. intros. inversion H2; subst. 
                    unfold C_unif_depend_to_nvn1.
                    unfold C_unif_depend_to_nv in H3. 
                    destruct H3 as [NV (HNV & (Hin & Hsem))].
                    exists (NV-N)%nat; auto. split; try lia. split.
                    * intros. apply in_supp_DAssn_under_dstate_inv in H3. 
                      destruct H3 as [st0 (Hsupp & Heq)]. 
                      apply Hin in Hsupp.
                      assert (Htmp: ((evalA_st (V - inject_Z (Z.of_nat N)) st0) == 
                                    inject_Z (Z.of_nat NV) - inject_Z (Z.of_nat N))%Q). {
                                      cbn [evalA_st]. 
                                      cbn [evalA_st] in Hsupp. rewrite Hsupp. 
                                      reflexivity.
                                    }
                      assert (Htemp: (update st0 V (evalA_st (V - inject_Z (Z.of_nat N)) st0) == 
                                    update st0 V (inject_Z (Z.of_nat NV) - inject_Z (Z.of_nat N)))%state). {
                          apply st_eq_implies_update_eq; auto. apply state_eq_refl.
                        }
                      apply state_eq_trans with (s0 := st) in Htemp; try assumption.
                      apply st_eq_implies_evalA with (a:= Ava V) in Htemp.
                      rewrite Htemp. cbn [evalA_st]. 
                      rewrite get_update_eq. unfold Qminus. 
                      rewrite <- inject_Z_opp.
                      rewrite <- inject_Z_plus.
                      replace (Z.of_nat NV + - Z.of_nat N)%Z with (Z.of_nat NV - Z.of_nat N)%Z by lia.
                      assert (Hle: (N <= NV)%nat). { lia. }
                      rewrite (Nat2Z.inj_sub NV N Hle). reflexivity.
                    * apply intersect_preserves_satisfy with (pd:= pd) (c:= V ::= V - inject_Z (Z.of_nat N)); 
                        try assumption.
                      ++ apply WD_Unif_MN. lia.
                      ++ simpl. rewrite get_var_in_unif_MN; try lia. simpl. auto.
                + unfold hoare_triple. intros. inversion H2; subst.
                  destruct H3. split; intuition.
                  - apply dom_subset_trans with (l1:= dom pd); auto. 
                  apply subset_NS in H2; intuition.
                  apply Valid_forall_NS in H2; auto.
                  - destruct H4. exists (x - inject_Z (Z.of_nat N))%Q. 
                  intros. 
                  apply in_supp_DAssn_under_dstate_inv in H5. destruct H5. 
                  destruct H5. apply H4 in H5. cbn [evalA_st] in *. 
                  apply st_eq_implies_get_eq with (x:= V) in H6. rewrite H6.
                  rewrite get_update_eq; try assumption. 
                  rewrite H5. reflexivity.
              }
              unfold assert_implies. intros. 
              destruct H1 as (H1 & Hdirac). destruct H1 as (HV & HCV).
              split; intuition.
              apply andb_sem_conj in HV. destruct HV.
              apply andb_sem_conj in H2. destruct H2.
              destruct H2. split.
              -- simpl. intuition.
              -- intros. apply H4 in H5. destruct H5. 
                split; intuition. 
                destruct (evalB_st (V < 2%Q * inject_Z (Z.of_nat N)) st) eqn: Hb; try contradiction.
                apply mult2_eval_implies in Hb. rewrite Hb. apply I. 
        
        + unfold assert_implies. intros. 
          destruct H1 as [Hoplus HDV]. destruct Hoplus as [H1 | H1]. 
          * destruct H1 as (p1 & p2 & Hp1 & Hp2 & Hsum_p & pd1 & pd2 & HV1 & HV2 & Hdom1 & Hdom2 & Hpd1 &Hpd2 & H').
            split; try assumption. left. 
            exists p1, p2. intuition. exists pd1, pd2. intuition. 
            apply andb_sem_conj in H7. destruct H7. 
            unfold B_VR in H7. apply andb_sem_conj in H7. intuition.
            apply andb_sem_conj. intuition. apply andb_sem_conj. intuition.
          * destruct H1 as [H1 | H1].
            ++ split; try assumption. right. left. intuition.
            ++ destruct H1 as (HB & HC). split; try assumption.  
              right. right. intuition. 
              apply andb_sem_conj in HB. destruct HB. 
              unfold B_VR in H1. apply andb_sem_conj in H1. intuition.
              apply andb_sem_conj. intuition. apply andb_sem_conj. intuition.
    }
    unfold assert_implies. intros. destruct H1. intuition.
    Unshelve. 
    simpl. auto.
  Qed.



  Lemma get_var_in_bexp_conj: forall b b', 
    get_variables_in_bexp (b && b') = get_variables_in_bexp b ∪ get_variables_in_bexp b'.
  Proof. 
    intros. simpl. auto.
  Qed.

  Lemma get_var_in_bexp_negb: forall b, 
    get_variables_in_bexp b = get_variables_in_bexp (~b).
  Proof. 
    intros. simpl. auto.
  Qed.



  
  Lemma FDR_correct :
    {{ [[⊤]] }} FDR {{invariant}}.
  Proof. 
    unfold FDR. 
    pose (PV:= [[V == 1%Q]]). 
    assert (HNminus: (N - 1 > 0)%nat). { apply from_Q_ineq_to_nat_sub1_pos in HN. auto. }
    apply hoare_seq with (Q:= PV).
    - pose (PC:= [[C == 0%Q]]). 
      apply hoare_consequence_pre with (P':= [[⊤ ∧ (V == 1%Q)]]); 
        try apply Conj_True; 
        try apply WD_Pdeter; try apply WD_Dpred; try assumption.
      apply hoare_seq with (Q:= (PC /\ PV)%assertion). 
      + apply hoare_consequence_pre with (P':= phi0_L). 
        * apply hoare_consequence_pre with (P':= (phi0 /\[[Pdeter (Dpred guard)]])%assertion). 
          ** apply hoare_consequence_pre with (P':= invariant).
            ++ apply hoare_consequence_post with (Q':= (invariant /\ [[~ guard]])%assertion). 
            -- unfold invariant. 
            apply hoare_consequence_post with (Q':= ([[phi1]] /\ [[~ guard]])%assertion).
            --- unfold phi0.
            { eapply hoare_while_sem with (P0:= (assert_Oplus phi0_L phi0_R /\ Dirac_v V)%assertion). 
              - unfold guard. apply WD_Pdeter; try apply WD_Dpred; try assumption.
              - unfold phi1. apply WD_Unif_MN. lia.
              - unfold phi1. apply exclude_Unif_MN. lia.
              - simpl. unfold phi1. rewrite get_var_in_unif_MN; simpl; auto. lia.
              - apply GA_and; try apply GA_oplus; try apply GA_Dirac.
                + unfold phi0_L. apply GA_and; try apply GA_pf. 
                  * apply WD_Pdeter; try apply WD_Dpred; try assumption.
                  * unfold C_unif_depend_to_0v. try apply GA_unif_depend.
                + unfold phi0_R. apply GA_and; try apply GA_pf. 
                  * apply WD_Pdeter; try apply WD_Dpred; try assumption.
                  * apply GA_Unif_Depend_n.
              - auto.
              - apply body_correct.
            } 
            --- unfold assert_implies. intros. destruct H1. split; intuition.
            right. intuition.
            -- unfold assert_implies. intros. destruct H1. intuition.
            ++ unfold invariant. unfold assert_implies. intros. right. left. intuition. 
          ** unfold phi0_L, phi0. unfold assert_implies. intros. destruct H1. intuition.
            ++ unfold assert_Oplus. intros. right. left. unfold phi0_L. intuition. 
            ++ destruct H2. intuition. split. 
              -- unfold B_VN in H1. apply dst_satisfy_df_implies_dom in H1. simpl in H1. intuition.
              -- exists (inject_Z (Z.of_nat x)). intuition.
            ++ unfold guard. apply Pdeter_L_implies_or; try assumption. 
              apply dst_satisfy_df_implies_dom in H1. 
              apply dom_subset_unif_0V in H2. 
              rewrite get_var_in_bexp_conj. 
              apply dom_subset_orb_fst_iff. intuition.

        * unfold phi0_L, B_VN. unfold assert_implies. intros. destruct H1 as [HC HV]. 
          split. 
          ** unfold PV in HV. destruct HV. split; try assumption. intros. 
            specialize (H2 st H3). destruct H2. split; try assumption. 
            destruct (evalB_st (V = 1%Q) st) eqn : HVst; try contradiction. 
            replace (evalB_st (V < inject_Z (Z.of_nat N)) st) with true; try trivial.
            symmetry. apply EVAL_V. assumption.
          ** unfold PV in HV. unfold PC in HC. 
            unfold C_unif_depend_to_0v, Unif_Depend_by. 
            exists 1%nat. split; try lia. split.
            ++ intros. destruct HV. apply H3 in H1. destruct H1. 
              destruct (evalB_st (V = 1%Q) st) eqn: HVst; try contradiction.
              apply EVAL_B_implies_A with (q:= 1%Q). assumption.
            ++ split. 
              -- simpl. apply dst_satisfy_df_implies_dom in HC. simpl in HC. intuition. 
                apply WD_Pdeter; try apply WD_Dpred; try assumption.
              -- intros. destruct HC. split; intuition. 
      + apply hoare_Frame; try apply WD_Pand; try apply WD_Pdeter; try apply WD_Dpred; try assumption; try reflexivity.
        apply hoare_consequence_pre with (P':= PC [C |-> (Aco 0)]); try apply hoare_Dasgn. 
        unfold assert_implies. intros. apply Pdeter_always_holds.
  - apply hoare_consequence_pre with (P':= PV [V |-> (Aco 1)]); try apply hoare_Dasgn. 
    unfold assert_implies. intros. apply Pdeter_always_holds.
  Qed.
  
  

    
End FastDice.
