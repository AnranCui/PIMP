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
Require Import Library.UtilityQR.
Import ListNotations.
Open Scope R_scope.

(*****This file contains definition and some properties about dist A ****)

Definition dist (A: Type) : Type := (list (A * R)).

Definition prob_is_positive (p: R) : Prop := (0 < p <= 1)%R. 
Fixpoint positive_probs {A:Type} (d :dist A): Prop :=  (*Each probability value in distribution d is in [0,1]*)
  match d with 
  | [] => True
  | (v,p) :: nd => prob_is_positive p /\ positive_probs nd
  end.
Fixpoint sum_probs {A:Type} (d : dist A) : R :=  (*Compute the sum of probabilities of a probability distribution*)
    match d with
    | [] => 0%R
    | (_, p) :: d' => (p + (sum_probs d'))%R
  end.
Definition Valid_dist {A:Type} (d : dist A): Prop := (*Ensure that each probability distribution is valid, the sum of probabilities is between 0 and 1, and each probability is positive*)
    (0 <= sum_probs d <= 1)%R /\ (positive_probs d). 

Definition add_dist {A: Type} (d0 d1 : dist A) : dist A := (d0 ++ d1). (*Define the addition operation of a probability distribution*)

Fixpoint mult_dist {A: Type} (p:R) (d: dist A) : dist A := (*Define the multiplication operation for a probability distribution. Every probability in d multipy a constant*)
  match d with 
  | [] => []
  | (s, p') :: d' => if Req_EM_T p 0 then [] 
                     else (s, (p * p')%R) :: mult_dist p d' 
  end.

Lemma sum_ge0_mult_p: forall {A: Type} p mu, 
  (0 <= @sum_probs A mu)%R -> (0 < p)%R -> (0 <= p * @sum_probs A mu)%R.
Proof.
  intros. apply Rmult_le_pos; try assumption. apply Rlt_le. assumption. 
Qed.

(* Now define the local state and the distributed state. *)
Declare Scope state_scope.
Delimit Scope state_scope with state.
Declare Scope domain_scope.
Delimit Scope domain_scope with domain.
Declare Scope dstate_scope.
Delimit Scope dstate_scope with dist_state.
Declare Scope supp_scope.
Delimit Scope supp_scope with supp.

(********************************************************)
Open Scope state_scope.
Definition state := list Q. 
Definition partial_st:= list (option Q).
Definition default_Q : Q := (-99999)%Q. (* Placeholder, indicating that the value of this variable is invalid *)
Definition Empty_State: partial_st := [].
Definition domain := list bool. (* Record the variables available in a local state *)

(**************** Function of partial_st ********************************************************)

Definition is_none {A : Type} (v : option A) : bool :=
  match v with
  | None => true
  | Some _ => false
  end.
Definition st_all_none (s: partial_st) := forallb (fun v => is_none v) s.  

(*Comparison operation between two states*)
Fixpoint beq_state (s0 s1 : partial_st) : bool := (*s0=s1*)
  match s0, s1 with 
  | [], _ => st_all_none s1
  | _, [] => st_all_none s0
  | Some v0 :: nv0, Some v1 :: nv1 => match Qcompare v0 v1 with
                                      | Eq => beq_state nv0 nv1
                                      | _ => false
                                      end
  | None :: nv0, None :: nv1 => beq_state nv0 nv1
  | _, _ => false
  end.  

Fixpoint ble_state (s0 s1: partial_st): bool:= (*s0<=s1*)
  match s0, s1 with 
  | [], _ => true
  | _, [] => (st_all_none s0)
  | Some v0 :: n0, Some v1::n1 => match Qcompare v0 v1 with
                                  | Eq => ble_state n0 n1
                                  | Lt => true
                                  | Gt => false
                                  end
  | Some v0 :: nv0, None :: nv1 => false
  | None :: nv0, None :: nv1 => ble_state nv0 nv1
  | None :: nv0, Some v1 :: nv1 => true 
end.
Notation "s0 '==' s1" := (beq_state s0 s1 = true) (at level 70): state_scope.
Notation "s0 '<=' s1" := (ble_state s0 s1 = true) (at level 70): state_scope.
Notation "s0 '!=' s1" := (beq_state s0 s1 = false) (at level 70): state_scope.

Fixpoint union_state (s1 s2: partial_st) : partial_st := (*The premise of the union operation is that "the domains do not intersect"*)
  match s1, s2 with
  | [], _ => s2
  | _, [] => s1
  | Some h1 :: t1, Some h2 :: t2 => []
  | Some h1 :: t1, None :: t2 => Some h1 :: union_state t1 t2
  | None :: t1, Some h2 :: t2 => Some h2 :: union_state t1 t2
  | None :: t1, None :: t2 => None :: union_state t1 t2
  end.

Fixpoint res_st_to_X (s: partial_st) (X: domain): partial_st := (*Only take the variables in the domain X in state s*)
  match s, X with
  | [], _ => []
  | _, [] => []
  | Some v :: s', b :: X' => if b then Some v :: (res_st_to_X s' X') else None :: (res_st_to_X s' X')
  | None :: s', b :: X' => None :: (res_st_to_X s' X')
  end.

(************Three relationships of domain: intersection, union, and subset**************************)
Open Scope domain_scope.
Definition return_domain (s: partial_st): domain := map (fun v => negb (is_none v)) s. (*How to get the domain of a state s*)
Definition all_false (l : domain) : bool := forallb (fun b => negb b) l. (*Equivalent to an empty list*)

Fixpoint is_domain_subset (l1 l2: domain): bool := 
  match l1, l2 with
  | [], _ => true  
  | _, [] => all_false l1
  | h1 :: t1, h2 :: t2 => (orb (negb h1) h2) && (is_domain_subset t1 t2)
  end.

Fixpoint is_domain_intersect (l1 l2 : domain) : bool :=
  match l1 with
  | [] => false
  | b :: l1' => match l2 with
                | [] => false
                | b' :: l2' => if (andb b b') then true 
                                else (is_domain_intersect l1' l2') 
                end
  end. 

Fixpoint orb_domain (l1 l2 :domain) : domain :=
  match l1 with
  | [] => l2
  | b :: l1' => match l2 with
                | [] => l1
                | b' :: l2' => (orb b b') :: (orb_domain l1' l2') 
                end
  end.

Fixpoint and_domain (l1 l2 :domain) : domain :=
  match l1 with
  | [] => []
  | b :: l1' => match l2 with
                | [] => []
                | b' :: l2' => (andb b b') :: (and_domain l1' l2') 
                end
  end.

Definition domain_equiv (l1 l2 : domain) : Prop := 
  is_domain_subset l1 l2 = true /\ is_domain_subset l2 l1 = true.

Notation "l0 '⊆' l1" := (is_domain_subset l0 l1 = true) (at level 70): domain_scope.
Notation "l0 '==' l1" := (domain_equiv l0 l1) (at level 70): domain_scope.
Notation "l0 '∩' l1" := (and_domain l0 l1) (at level 40): domain_scope.
Notation "l0 '∪' l1" := (orb_domain l0 l1) (at level 50): domain_scope.  
Notation "l0 '∩∅' l1" := (is_domain_intersect l0 l1 = false) (at level 50): domain_scope.

(***Function of Distribution state***********************************************************************************)

Open Scope dstate_scope.
Definition dist_state : Type := dist partial_st. (*Define distribution status*)

Fixpoint insert_st_pair (s:partial_st) (p:R) (mu: dist_state) : dist_state :=
  match mu with 
  | [] => [(s,p)]
  | (s',p') :: mu' => if beq_state s s' then (s', (p + p')%R) :: mu'
                      else if (ble_state s s') then (s,p) :: (s',p') :: mu'      
                      else (s',p') :: (insert_st_pair s p mu')
  end.
Fixpoint sort_dst (mu: dist_state) : dist_state := (*Sort the local state pairs in the distribution state by state size*)
  match mu with 
  | [] => []
  | (s1,p1) :: mu' => insert_st_pair s1 p1 (sort_dst mu')
end.

Definition supp: Type := list partial_st. (*The support of a distribution state is the set of local states*)
Definition supp_mu (mu: dist_state): supp := 
  let sorted_mu := sort_dst mu in (map fst sorted_mu).

Fixpoint is_in_supp (s: partial_st) (A : supp) : bool := (* Determine whether a state is in a supp set *)
  match A with
  | [] => false
  | s' :: A' => (beq_state s s') || (is_in_supp s A')
  end.

Fixpoint insert_st (s:partial_st) (A : supp) : supp :=
  match A with 
  | [] => [s]
  | s' :: A' => if beq_state s s' then s' :: A'
                else if (ble_state s s') then s :: s' :: A'      
                else s' :: (insert_st s A')
  end.
(*Two sorted lists*)
Fixpoint beq_supp (sp0 sp1: supp): bool := 
  match sp0, sp1 with 
  | [], [] => true
  | s0 :: supp0', s1 :: supp1' => (beq_state s0 s1) && (beq_supp supp0' supp1')
  | _, _ => false
  end. 

Fixpoint is_supp_subset (ls0 ls1: supp) : bool := 
  match ls0, ls1 with
  | [], _ => true               (* The empty set is always a subset of any set *)
  | _, [] => false 
  | s0 :: ts0, s1 :: ts1 =>
      if beq_state s0 s1 then
        is_supp_subset ts0 ts1 
      else if (ble_state s0 s1) then
        false                    
      else
        is_supp_subset (s0 :: ts0) ts1  
  end.
Notation "l0 '==' l1" := (beq_supp l0 l1 = true) (at level 70): supp_scope.
Notation "l0 '⊆' l1" := (is_supp_subset l0 l1 = true) (at level 70): supp_scope.

(********************************************)

Fixpoint get_prob_in_dstate (mu: dist_state) (s: partial_st): R :=
  match mu with 
  | [] => 0%R  
  | (s', p) :: mu' => if beq_state s s' then (p + (get_prob_in_dstate mu' s))%R
                      else (get_prob_in_dstate mu' s)
  end.

Definition dst_equiv (mu0 mu1 : dist_state) : Prop := 
  forall s, get_prob_in_dstate mu0 s = get_prob_in_dstate mu1 s.
Notation "mu0 '==' mu1" := (dst_equiv mu0 mu1) (at level 70): dstate_scope.
Notation "mu0 + mu1" := (add_dist mu0 mu1) (at level 50, left associativity) : dstate_scope.
Notation "p * mu" := (mult_dist p mu) (at level 40, left associativity) : dstate_scope.

Fixpoint beq_dst mu0 mu1: bool :=  (*Stricter definition of equality*)
  match mu0, mu1 with 
  | [], [] => true
  | (s0, p0) :: mu0', (s1, p1) :: mu1' => 
      ((beq_state s0 s1) && (Req_bool p0 p1)) && (beq_dst mu0' mu1')
  | _ , _  => false
  end.

Fixpoint combine_dst (mu1 mu2: dist_state) : dist_state := 
  match mu1 with 
  | [] => []
  | (s1, p1) :: nl1 => 
    let fix combine_op_helper (mu2:dist_state) : dist_state :=
      match mu2 with
      | [] => []
      | (s2, p2) :: nl2 => ([((union_state s1 s2), (p1 * p2)%R)] + combine_op_helper nl2)%dist_state
      end in 
    combine_op_helper mu2 ++ combine_dst nl1 mu2
end. 

Fixpoint res_dst_to_X (mu: dist_state) (X: domain) : dist_state := (*PI_X*)
  match mu with 
  | [] => []
  | (s,p) :: mu' => (res_st_to_X s X, p) :: res_dst_to_X mu' X
  end.  
Notation "mu '⊗' mu'" := (combine_dst mu mu') (at level 30): dstate_scope.
Notation "mu '\|' X" := (res_dst_to_X mu X) (at level 20): dstate_scope.

Fixpoint bulid_helper (ss: partial_st) ps (mu: dist_state) (X: domain) : dist_state :=
  match mu with
  | [] => []
  | (s, p) :: mu' =>
      if beq_state ss (res_st_to_X s X)
      then (s, (ps * p)%R) :: bulid_helper ss ps mu' X
      else bulid_helper ss ps mu' X
  end.

Fixpoint bulid_dst_sub (mu_sub mu: dist_state) (X: domain): dist_state := 
  match mu_sub with
  | [] => [] 
  | (ss,ps) :: mu_sub' => (/get_prob_in_dstate (mu \| X) ss) * (bulid_helper ss ps mu X)
                            + bulid_dst_sub mu_sub' mu X
  end.

(***************************)
Definition Identify_mu: dist_state := [(Empty_State,1)].

Inductive partial_dst_Prop (X : domain) : dist_state -> Prop := (*Ensure that the domain of each local state in a distribution is X*)
  | PD_nil : partial_dst_Prop X []
  | PD_cons : forall (s: partial_st) (p: R) mu,
      (domain_equiv X (return_domain s)) ->
      partial_dst_Prop X mu ->
      partial_dst_Prop X ((s, p) :: mu).

Record partial_dist := {
  dom : domain;
  mu : dist_state;
  all_partial : partial_dst_Prop dom mu;
}.
Definition partial_dst_equiv (pd1 pd2 : partial_dist) : Prop :=
  (pd1.(dom) == pd2.(dom))%domain /\ (pd1.(mu) == pd2.(mu))%dist_state.
Notation "pd1 ≡ pd2" := (partial_dst_equiv pd1 pd2) (at level 70).

Definition partial_dst_subset : partial_dist -> partial_dist -> Prop := 
  fun pd1 pd2 => is_domain_subset pd1.(dom) pd2.(dom) = true /\
                  (pd2.(mu) \| pd1.(dom)) == pd1.(mu).
Notation "pd1 '⊑' pd2" := (partial_dst_subset pd1 pd2) (at level 70): dstate_scope.

Definition pd_emp (X: domain): partial_dist := (*Empty partial order distribution*)
  {|
    dom:= X ;
    mu:= nil%dist_state ;
    all_partial:= PD_nil X;
  |}.


Close Scope R_scope.