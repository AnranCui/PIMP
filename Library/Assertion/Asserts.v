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
Require Import Stdlib.FSets.FMapList.
(* From mathcomp Require Import all_ssreflect. *)
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
Open Scope nat_scope.
Open Scope R_scope.
Open Scope dstate_scope.
Set Default Goal Selector "!".

(** ** Formula Expressions: the fundamental assertions of our Hoare Logic.**)
Inductive Dformula: Type :=
  | Dpred : bexp -> Dformula
  | Dexist: nat -> Dformula -> Dformula.

Inductive Pformula: Type :=
  | Pdeter: Dformula -> Pformula
  | Pplus : R -> Pformula -> Pformula -> Pformula
  | Oplus : Pformula -> Pformula -> Pformula
  | Odot  : Pformula -> Pformula -> Pformula
  | Pand  : Pformula -> Pformula -> Pformula.

Declare Scope formula_scope.
Bind Scope formula_scope with Dformula. 
Open Scope formula_scope.
Delimit Scope formula_scope with formula.

Bind Scope formula_scope with Pformula.
Delimit Scope formula_scope with formula.
Notation "⊤" := (Pdeter (Dpred Btrue)) : formula_scope.
Notation "x && y" := (Pdeter (Dpred (Band x y))) (at level 40, left associativity) : formula_scope.
Notation "'~' b"  := (Pdeter (Dpred (Bnot b))) (at level 75, right associativity) : formula_scope.
Notation "a < b" := (Pdeter (Dpred (Blt a b))) (at level 70, no associativity) : formula_scope.
Notation "x ≤ y" := (Pdeter (Dpred (Ble x y))) (at level 50) : formula_scope.
Notation "x == y" := (Pdeter (Dpred (Beq x y))) (at level 70) : formula_scope.
Notation "x <> y" := (Pdeter (Dpred (Bnot (Beq x y)))) : formula_scope.
Notation "x ⊕ y" := (Oplus x y) (at level 42, right associativity) : formula_scope.
Notation "P ⊕[ p ] Q" := 
  (Pplus p P%formula Q%formula)
  (at level 42, right associativity) : formula_scope.
Notation "x ⊙ y" := (Odot x y) (at level 41, right associativity) : formula_scope.
Notation "P ∧ Q" := (Pand P Q) (at level 40, left associativity) : formula_scope.

Fixpoint get_var_in_Dformular (df:Dformula) : list bool:=  (**FV(phi)*)
  match df with
  | Dpred b => get_variables_in_bexp b
  | Dexist n df' => (get_var_in_Dformular df') 
  end.
Fixpoint get_var_in_Pformular (phi:Pformula) : domain:= (** FV(phi)*)
  match phi with
  | Pdeter P           => get_var_in_Dformular P
  | Pplus p phi1 phi2 => 
      match Rle_lt_dec p 0%R with
      | left _ => get_var_in_Pformular phi2  (* p = 0 *)
      | right H0 =>
          match Rle_lt_dec 1%R p with
          | left _ => get_var_in_Pformular phi1  (* p = 1 *)
          | right H1 => ((get_var_in_Pformular phi1) ∪ (get_var_in_Pformular phi2))%domain  (* 0 < p < 1 *)
          end
      end
  | Oplus phi1 phi2    => orb_domain (get_var_in_Pformular phi1) (get_var_in_Pformular phi2)
  | Odot phi1 phi2     => orb_domain (get_var_in_Pformular phi1) (get_var_in_Pformular phi2)
  | Pand phi1 phi2     => orb_domain (get_var_in_Pformular phi1) (get_var_in_Pformular phi2)
  end.


Definition DAssertion := partial_st -> Prop.
Definition PAssertion := partial_dist -> Prop.

Declare Scope assertion_scope.
Bind Scope assertion_scope with PAssertion.
Bind Scope assertion_scope with DAssertion.
Delimit Scope assertion_scope with assertion. 

Notation "~ P" := (fun mu => ~  P mu) : assertion_scope.
Notation "P /\ Q" := (fun mu =>  P mu /\  Q mu) : assertion_scope.
Definition PAssertion_and (P1 P2: PAssertion): PAssertion := ((P1 /\ P2)%assertion).
Notation "P -> Q" := (fun mu =>  P mu ->   Q mu) : assertion_scope.
Notation "P <-> Q" := (fun mu =>  P mu <->   Q mu) : assertion_scope.
 
(*******************Syntax Layer/Well-Formedness************)
Inductive well_defined_Df : Dformula -> Prop := 
  | WD_Dpred : forall b, well_defined_Df (Dpred b)
  | WD_Dexist : forall X f', 
      is_domain_subset (singleton_bool_list X) (get_var_in_Dformular f') = true ->
      well_defined_Df f' -> well_defined_Df (Dexist X f').
Inductive well_defined_Pf : Pformula -> Prop :=
  | WD_Pdeter : forall df, 
      well_defined_Df df -> well_defined_Pf (Pdeter df)
  | WD_Pplus : forall p f1 f2,
      (0 <= p <= 1)%R ->
      well_defined_Pf f1 -> well_defined_Pf f2 ->
      well_defined_Pf (Pplus p f1 f2)
  | WD_Oplus : forall f1 f2,
      well_defined_Pf f1 -> well_defined_Pf f2 -> well_defined_Pf (Oplus f1 f2)
  | WD_Odot : forall f1 f2,
      well_defined_Pf f1 -> well_defined_Pf f2 ->
      is_domain_intersect (get_var_in_Pformular f1)
                          (get_var_in_Pformular f2) = false ->
      well_defined_Pf (Odot f1 f2)
  | WD_Pand : forall f1 f2,
      well_defined_Pf f1 -> well_defined_Pf f2 -> well_defined_Pf (Pand f1 f2).


Fixpoint df_sem (f : Dformula) : DAssertion :=  (* Get the semantics of a deterministic formula *)
  match f with
  | Dpred b => fun st => (is_domain_subset (get_variables_in_bexp b) (return_domain st) = true) /\
                          if (evalB_st b st) then True else False 
  | Dexist X f' => fun st => (is_domain_subset (get_var_in_Dformular f') (return_domain st) = true /\
                              exists r : Q, df_sem f' (update st X r))
  end.

Fixpoint pf_sem (f : Pformula) : PAssertion := 
  match f with
  | Pdeter df => fun pd => (is_domain_subset (get_var_in_Dformular df) pd.(dom) = true) /\
                            (forall st, is_in_supp st (supp_mu pd.(mu)) = true -> (df_sem df) st) 
  | Pplus p f1 f2 => fun pd => 
        ((0 < p < 1 /\ (exists pd1 pd2, 
                                      Valid_dist pd1.(mu) /\ Valid_dist pd2.(mu) /\ 
                                      (pd1.(dom) == pd.(dom))%domain /\ (pd2.(dom) == pd.(dom))%domain /\
                                      (pf_sem f1 pd1) /\ (pf_sem f2 pd2) /\
                                      (sum_probs pd1.(mu))%R = (sum_probs pd.(mu))%R /\ 
                                      (sum_probs pd2.(mu))%R = (sum_probs pd.(mu))%R /\
                                      (pd.(mu) == (p * pd1.(mu)) + (1-p) * pd2.(mu))%dist_state))
                                \/ (p = 1 /\ (exists pd1, 
                                      Valid_dist pd1.(mu) /\ (pd1 ≡ pd) /\ 
                                      (pf_sem f1 pd1) /\
                                      (sum_probs pd1.(mu))%R = (sum_probs pd.(mu))%R))
                                \/(p = 0 /\ (exists pd2, 
                                      Valid_dist pd2.(mu) /\ (pd2 ≡ pd) /\
                                      (pf_sem f2 pd2) /\
                                      (sum_probs pd2.(mu))%R = (sum_probs pd.(mu))%R)))
  | Oplus f1 f2 => fun pd => 
                          (exists p1 p2, (0 < p1 < 1)%R /\ (0 < p2 < 1)%R /\ (p1%R + p2%R = 1)%R /\
                                (exists pd1 pd2, 
                                  (Valid_dist pd1.(mu) /\ Valid_dist pd2.(mu) /\ 
                                  (pd1.(dom) == pd.(dom))%domain /\ (pd2.(dom) == pd.(dom))%domain /\
                                  (pf_sem f1 pd1) /\ (pf_sem f2 pd2) /\
                                  (sum_probs pd1.(mu) = sum_probs pd.(mu))%R /\ 
                                  (sum_probs pd2.(mu) = sum_probs pd.(mu))%R /\
                                  (pd.(mu) == (p1 * pd1.(mu)) + p2 * pd2.(mu))%dist_state))) 
                          \/(exists pd1,
                                  (Valid_dist pd1.(mu) /\ (pd1 ≡ pd) /\ 
                                  is_domain_subset (get_var_in_Pformular f2) pd.(dom) = true /\
                                  (pf_sem f1 pd1) /\ 
                                  (sum_probs pd1.(mu) = sum_probs pd.(mu))%R))
                          \/(exists pd2, 
                                  (Valid_dist pd2.(mu) /\ (pd2 ≡ pd) /\ 
                                  is_domain_subset (get_var_in_Pformular f1) pd.(dom) = true /\
                                  (pf_sem f2 pd2) /\ 
                                  (sum_probs pd2.(mu) = sum_probs pd.(mu))%R))
  | Odot f1 f2 => fun pd =>  (exists pd1 pd2 (Hvar: is_domain_intersect pd1.(dom) pd2.(dom) = false),
                                  Valid_dist pd1.(mu) /\ Valid_dist pd2.(mu) /\  
                                  (pf_sem f1 pd1) /\ (pf_sem f2 pd2) /\ 
                                  (let pd0:= Build_partial_dist (orb_domain pd1.(dom) pd2.(dom)) 
                                                                  (pd1.(mu) ⊗ pd2.(mu)) (PD_combine_invar_mu pd1 pd2 Hvar) in
                                    pd0 ⊑ pd))
  | Pand f1 f2 => fun pd => (pf_sem f1 pd) /\ (pf_sem f2 pd)
end.
Notation "'[[' P ']]'" := (pf_sem P) (at level 0, format "[[ P ]]") : formula_scope.

(************************************************************************************)




