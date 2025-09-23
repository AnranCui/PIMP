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
Open Scope list_scope.
Open Scope dstate_scope.

(*Here is the definition of syntax for programming languages*)
Inductive aexp :=
  | Aco : Q -> aexp
  | Ava : nat -> aexp
  | Apl : aexp -> aexp -> aexp
  | Amu : aexp -> aexp -> aexp
  | Asu : aexp -> aexp -> aexp.
Inductive bexp := (** Syntax of Boolean expressions *)
  | Btrue : bexp
  | Bfalse : bexp
  | Band : bexp -> bexp -> bexp
  | Bnot : bexp -> bexp
  | Beq : aexp -> aexp -> bexp
  | Ble : aexp -> aexp -> bexp (*less than*).

(*The premise of evaluation is that the variable a is a subset of the variables in state*)

Declare Scope imp_scope.
Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.
Notation "a + b"  := (Apl a b) (at level 50, left associativity) : imp_scope.
Notation "a * b"  := (Amu a b) (at level 40, left associativity) : imp_scope.
Notation "a - b"  := (Asu a b) (at level 50, left associativity) : imp_scope.
Notation "x && y" := (Band x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b"  := (Bnot b) (at level 75, right associativity) : imp_scope.
Notation "a = b"  := (Beq a b) (at level 70, no associativity) : imp_scope.
Notation "a <= b" := (Ble a b) (at level 70, no associativity) : imp_scope.
Definition Blt (a b : aexp) : bexp := Bnot (Ble b a).
Notation "a < b" := (Blt a b) (at level 70, no associativity) : imp_scope.

(** ** Commands *)
Definition valid_dist_aexp := { da : dist aexp | positive_probs da /\ sum_probs da = 1%R }.
Inductive winstr :=(** Syntax of pWHILE instructions *)
  | Skip   : winstr
  | DAssign: nat -> aexp -> winstr
  | RAssign: nat -> valid_dist_aexp -> winstr     
  | Seq    : winstr -> winstr -> winstr
  | If     : bexp -> winstr -> winstr -> winstr
  | While  : bexp -> winstr -> winstr. 
Bind Scope imp_scope with winstr.
Notation "'SKIP'"    :=  Skip : imp_scope.
Notation "x '::=' a" := (DAssign x a) (at level 60): imp_scope.
Notation "x '$=' d"  := (RAssign x d) (at level 60, right associativity): imp_scope.
Notation "c1 ;; c2"   := (Seq c1 c2) (at level 80, right associativity): imp_scope. (*;; 是防止和list中的；冲突 *)
Notation "'IF' b 'THEN' c1 'ELSE' c2 'FI'" := (If b c1 c2) (at level 80, right associativity): imp_scope.
Notation "'WHILE' b 'DO' c 'END'" := (While b c) (at level 80, right associativity): imp_scope.

(* ####################################################### *)
Fixpoint singleton_bool_list (n : nat) : domain :=
  match n with
  | 0%nat => [true]
  | S m => false :: singleton_bool_list m
  end.
Fixpoint get_variables_in_aexp (a:aexp): domain :=  (*V(e): Get the variable list in aexp*)
  match a with 
  | Aco _ => []
  | Ava (n) => singleton_bool_list n
  | Apl aexp1 aexp2 => orb_domain (get_variables_in_aexp aexp1) (get_variables_in_aexp aexp2)
  | Amu aexp1 aexp2 => orb_domain (get_variables_in_aexp aexp1) (get_variables_in_aexp aexp2)
  | Asu aexp1 aexp2 => orb_domain (get_variables_in_aexp aexp1) (get_variables_in_aexp aexp2)
  end.
Fixpoint get_variables_in_dist_aexp (da: dist aexp): domain :=  (*V(e): Get the variable list in aexp*)
  match da with 
  | [] => []
  | (a0,_):: nil  => get_variables_in_aexp a0
  | (a0,_):: da' => orb_domain (get_variables_in_aexp a0) (get_variables_in_dist_aexp da') 
  end.
Fixpoint get_variables_in_bexp (b:bexp): domain := 
  match b with
  | Btrue  => nil
  | Bfalse => nil
  | Band bexp1 bexp2 => orb_domain (get_variables_in_bexp bexp1) (get_variables_in_bexp bexp2)
  | Bnot bexp        => (get_variables_in_bexp bexp)
  | Beq aexp1 aexp2  => orb_domain (get_variables_in_aexp aexp1) (get_variables_in_aexp aexp2)
  | Ble aexp1 aexp2  => orb_domain (get_variables_in_aexp aexp1) (get_variables_in_aexp aexp2) (*less than*)
  end.
Fixpoint get_variables_in_winstr (i:winstr): domain :=  (****V(c)*)
  match i with 
  | Skip   => []
  | DAssign n aexp  => (singleton_bool_list n) ∪ (get_variables_in_aexp aexp)
  | RAssign n Vda => (singleton_bool_list n) ∪ (let '(exist _ d_A _) := Vda in get_variables_in_dist_aexp d_A)(**Assume that daexp does not contain variables ？*)     
  | Seq i1 i2 => (get_variables_in_winstr i1) ∪ (get_variables_in_winstr i2)
  | If bexp i1 i2 => (get_variables_in_bexp bexp) ∪ ((get_variables_in_winstr i1) ∪ (get_variables_in_winstr i2))
  | While bexp i1 => (get_variables_in_bexp bexp) ∪ (get_variables_in_winstr i1)
  end.

Fixpoint get_modvar_in_winstr (i:winstr): domain :=  (****MV(c)*)
  match i with 
  | Skip   => []
  | DAssign n aexp  => (singleton_bool_list n)
  | RAssign n Vda => (singleton_bool_list n) 
  | Seq i1 i2 => (get_modvar_in_winstr i1) ∪ (get_modvar_in_winstr i2)
  | If bexp i1 i2 => (get_modvar_in_winstr i1) ∪ (get_modvar_in_winstr i2)
  | While bexp i1 => (get_modvar_in_winstr i1)
  end.

Fixpoint get_readvar_in_winstr (i:winstr): domain := 
  match i with 
  | Skip   => []
  | DAssign n aexp  => (get_variables_in_aexp aexp)
  | RAssign n Vda =>  (let '(exist _ d_A _) := Vda in get_variables_in_dist_aexp d_A)
  | Seq i1 i2 => (get_readvar_in_winstr i1) ∪ (get_readvar_in_winstr i2)
  | If bexp i1 i2 => (get_variables_in_bexp bexp) ∪ ((get_readvar_in_winstr i1) ∪ (get_readvar_in_winstr i2))
  | While bexp i1 => (get_variables_in_bexp bexp) ∪ (get_readvar_in_winstr i1)
  end.

Lemma Win_Var_eq_orb_mod_read: forall i:winstr, 
  (get_variables_in_winstr i == (get_modvar_in_winstr i) ∪ (get_readvar_in_winstr i))%domain.
Proof.
  induction i; simpl; try apply dom_equiv_refl.
  - apply dom_equiv_trans with (l1:= ((get_modvar_in_winstr i1 ∪ get_readvar_in_winstr i1) ∪ 
                                      (get_modvar_in_winstr i2 ∪ get_readvar_in_winstr i2))%domain).
    + apply dom_eq_orb_compat; try assumption.
    + repeat rewrite orb_domain_assoc. apply dom_eq_orb_compat_right. 
      repeat rewrite <- orb_domain_assoc. apply dom_eq_orb_compat_left.
      rewrite orb_domain_comm. apply dom_equiv_refl.
  - rewrite orb_domain_assoc with (l1:= get_variables_in_bexp b). 
    rewrite orb_domain_comm with (l':= get_variables_in_bexp b). 
    rewrite <- orb_domain_assoc with (l0:= get_variables_in_bexp b). 
    apply dom_eq_orb_compat_left.
    apply dom_equiv_trans with (l1:= (get_modvar_in_winstr i1 ∪ get_readvar_in_winstr i1) ∪ 
                                      (get_modvar_in_winstr i2 ∪ get_readvar_in_winstr i2)%domain).
    + apply dom_eq_orb_compat; try assumption.
    + repeat rewrite orb_domain_assoc. apply dom_eq_orb_compat_right. 
      repeat rewrite <- orb_domain_assoc. apply dom_eq_orb_compat_left.
      rewrite orb_domain_comm. apply dom_equiv_refl.
  - rewrite orb_domain_comm. rewrite <- orb_domain_comm with (l:= get_readvar_in_winstr i).
    rewrite orb_domain_assoc. apply dom_eq_orb_compat_right. assumption.
Qed.

Lemma Win_mod_sub_var: forall i:winstr, 
  (get_modvar_in_winstr i ⊆ get_variables_in_winstr i)%domain.
Proof.
  intros. 
  assert ((get_variables_in_winstr i == 
        (get_modvar_in_winstr i) ∪ (get_readvar_in_winstr i))%domain) by apply Win_Var_eq_orb_mod_read.
  destruct H. apply dom_subset_orb_fst_iff in H0. destruct H0. assumption.
Qed.

Lemma Win_read_sub_var: forall i:winstr, 
  (get_readvar_in_winstr i ⊆ get_variables_in_winstr i)%domain.
Proof.
  intros. 
  assert ((get_variables_in_winstr i == 
        (get_modvar_in_winstr i) ∪ (get_readvar_in_winstr i))%domain) by apply Win_Var_eq_orb_mod_read.
  destruct H. apply dom_subset_orb_fst_iff in H0. destruct H0. assumption.
Qed.
