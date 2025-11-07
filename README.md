# Probabilistic Hoare Logic Formalization in Coq

## Overview
This repository formalizes probabilistic programs in Coq, including:
- A core library for probability distributions over states
- A denotational semantics for a simple probabilistic imperative language (PIMP)
- An assertion language for reasoning about programs with probabilistic properties
- A Hoare-style proof system with soundness proofs
- Small illustrative examples

---

## 🔑 Key Features

### 1) Core Definition of Probability Distributions
The core representation and operations are in `Library/DistState/CoreDef.v`.

- Representation:
  - A probability distribution over a type `A` is a finite list of weighted elements `(a, p)` with `a : A` and `p : R`.
  - Definition: `dist (A : Type) : Type := list (A × R)`.

- Operations:
  - Addition (`add_dist`): list concatenation of weighted pairs.
  - Scalar multiplication (`mult_dist`): multiplies the weight of each pair by a scalar while leaving elements unchanged.

We model partial states as finite lists of optional rationals:
- `Some q` indicates a defined entry; `None` indicates undefined.
- The validity mask (domain) is computed by a function (e.g., `return_domain`) mapping each position to a boolean indicating whether the entry is defined.
- A distribution state (`dist_state`) is a probability distribution over such partial states.

To enforce domain coherence, the inductive predicate `partial_dst_Prop X mu` requires that every partial state `s` in `mu` has a domain equivalent to `X`. The record `partial_dist` then packages:
```
Record partial_dist := {
  dom : domain;            
  mu  : dist state;        
  all_partial : partial_dst_Prop dom mu
}.
```

### 2) Probabilistic Program Semantics
We provide a relational big-step denotational semantics for a small probabilistic imperative language (PIMP).

- Syntax: `Library/PIMP/Syntax.v`
- Evaluation properties: `Library/PIMP/EvalProps.v`
- Semantics and lemmas: `Library/PIMP/Semantics.v`

### 3) Assertion Language
Assertions are predicates at two levels:

- State-level assertions: `DAssertion := partial_st → Prop`
- Distribution-level assertions: `PAssertion := partial_dist → Prop`

- Syntax: `Library/Assertion/Asserts.v`
- Semantics and properties: `Library/Assertion/SemProp.v`

### 4) Theorem-Proving Support
A Hoare-style proof system for probabilistic programs is provided under `Rule/HoareLogic.v`, with soundness proved at the end of the file.

### 5) Examples
Two small examples are included:

- `Example/Bays.v`
- `Example/Prog1.v`

---


## Directory Tree
```
.
├── Example
│   ├── Bays.v
│   └── Prog1.v
├── Library
│   ├── Assertion
│   │   ├── Asserts.v — assertion syntax
│   │   └── SemProp.v — semantics and properties of assertions
│   ├── DistState
│   │   ├── Arithmetic.v — properties of arithmetic operations on distributions
│   │   ├── Bulid.v — properties of the function "build_dst_sub", which rebuilds the original distribution from a restricted one
│   │   ├── Combine.v — properties of the function "combine_dst", which combines two distributions
│   │   ├── CoreDef.v — core definitions of probability distributions, operators, and states, including "partial_st" and "partial_dist"
│   │   ├── Domain.v — properties of state domains, defined as lists of booleans
│   │   ├── Partial.v — properties of partial states and partial distributions
│   │   ├── Restrict.v — properties of the function "restrict_dst", which restricts a distribution to a given domain
│   │   ├── Support.v — properties of the support set of a distribution state
│   │   └── ValidDst.v — properties of predicates describing valid distributions
│   ├── PIMP
│   │   ├── EvalProps.v — properties of the evaluation function eval
│   │   ├── Semantics.v — semantics of PIMP and useful lemmas for verifying Hoare triples
│   │   └── Syntax.v — syntax of PIMP
│   └── UtilityQR.v — lemmas related to rational and real numbers used
├── Makefile
├── Makefile.conf
├── README.md
├── Rule
│   └── HoareLogic.v — Hoare logic and its soundness proof
└── _CoqProject

7 directories, 23 files
```
---

## ⚙️ Quick Start

### Prerequisites
- The Rocq Prover, version `9.1+alpha` compiled with OCaml `4.14.0`
- CoqIDE or VSCode with the Coq extension

### Compilation
```bash
coq_makefile -f _CoqProject *.v -o Makefile
make
```

---

## ✉️ Contact
- Email: arcui@stu.ecnu.edu.cn