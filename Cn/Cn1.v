(* 

Implementation of the tableau for Cn, n>=2, presented in:

CONIGLIO, Marcelo E.; TOLEDO, Guilherme V. Two Decision Procedures for da Costa’s C n Logics Based on Restricted Nmatrix Semantics. Studia Logica, v. 110, n. 3, p. 601-642, 2022.

*)

Add LoadPath "../" as Main.
Require Import Main.Poly.
Require Import List.
Require Import String.
Import ListNotations.

Inductive LF :=
| Atom : string -> LF
| Neg : LF -> LF
| Conj : LF -> LF -> LF
| Disj : LF -> LF -> LF
| Impl : LF -> LF -> LF.

Notation "~ A" := (Neg A).
Notation "A \/ B" := (Disj A B).
Notation "A /\ B" := (Conj A B).
Notation "A -> B" := (Impl A B).

Definition p0 := Atom "p0".
Definition p1 := Atom "p1".
Definition p2 := Atom "p2".
Definition p3 := Atom "p3".
Definition p4 := Atom "p4".

Compute String.eqb "A" "A".

Fixpoint eqb_lf (A B : LF) :=
  match A, B with
  | Atom p, Atom q => String.eqb p q
  | ~P0, ~P1 => eqb_lf P0 P1
  | P0 /\ Q0, P1 /\ Q1 => andb (eqb_lf P0 P1) (eqb_lf Q0 Q1)
  | P0 \/ Q0, P1 \/ Q1 => andb (eqb_lf P0 P1) (eqb_lf Q0 Q1)
  | P0 -> Q0, P1 -> Q1 => andb (eqb_lf P0 P1) (eqb_lf Q0 Q1)
  | _, _ => false
  end.

Inductive SLF :=
| sign : nat -> LF -> SLF.

(* Tools *)

(* Check if A = B /\ ~B OR A = ~B /\ B*)
Definition isContradiction (A : LF) :=
  match A with
  | B /\ C =>
      let comp :=
        (fun P Q =>
           match Q with
           | ~ R => eqb_lf P R
           | _ => false
           end)
      in
      orb (comp B C) (comp C B)
  | _ => false
  end.

(* If A = B /\ ~B, then return B . If A = ~B /\ B, then return B.*)
Definition selectContra (A B : LF) :=
  if eqb_lf A (~B) then B else A.

Compute selectContra (~~p0) (~p0).

(* A^n *)
Fixpoint cngen (A : LF) (n : nat) : LF :=
  match n with
  | O => A
  | S m => ~ ((cngen A m) /\ (~ (cngen A m)))
  end.

(* A^(n) *)
Fixpoint cngen2 (A : LF) (n : nat) : LF :=
  match n with
  | O => A
  | S O => cngen A 1
  | S m => (cngen2 A m) /\ (cngen A (S m))
  end.

(* 

Given a Cn, we will adopt the following convention: 

0 : False 
1 : True
2 : t^n_0
.
.
n+1 : t^n_n-1

 *)

Compute getLastNEls [0;1;2;3;4;4;5;6] 2.

Fixpoint Neg_rule_aux1
  (A : LF)
  (V : list nat)
  (lN : list (pair SLF (list SLF)))
  :=
  match V with
  | nil => Leaf lN nil 0 nil nil
  | h::tl =>
      if Nat.eqb (List.length tl) 0
      then
        Alpha (sign h A) (Leaf (((sign h A); nil)::lN) nil 0 nil nil)
      else
        Beta
          (Alpha (sign h A) (Leaf (((sign h A); nil)::lN) nil 0 nil nil))
          (Neg_rule_aux1 A tl lN)
  end.

Definition Neg_rule
  (s : nat)
  (A : LF)
  (lN : list (pair SLF (list SLF)))
  (V : list nat)
  : btree SLF :=
  let In := getLastNEls V 2 in
  match s with
  | 0 => (* F *)
  | 1 => (* T *)
       Beta
        (Alpha (sign 0 A) (Leaf (((sign 0 A); nil)::lN) nil 0 nil nil))
        (Neg_rule_aux1 A In lN)
  | _ => (* any inconsistent value *)
  end.
