(* 

Implementation of the tableau for C1 presented in:

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

(* paraconsistent propositions generator *)

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

Check p1 -> p4.
Check p1 /\ (p2 \/ (~ p1 -> p4)).

Inductive SLF :=
| sign : nat -> LF -> SLF.

Check sign 0 p1.
Check sign 1 p2.

Check btree SLF.

(* 

Given a Cn, we will adopt the following convention: 

0 : False 
.
.
.
n+1 : True

*)

Definition Neg_rule
  (s : nat)
  (A : LF)
  (lN : list (pair SLF (list SLF)))
  : btree SLF :=
  match s with
  | 0 => (* F *)
      Alpha (sign 2 A) (Leaf (((sign 2 A); nil)::lN) nil 0 nil nil)
  | 1 => (* t *)
      Alpha (sign 1 A) (Leaf (((sign 1 A); nil)::lN) nil 0 nil nil)
  | _ => (* T *)
      Beta
        (Alpha (sign 0 A) (Leaf (((sign 0 A); nil)::lN) nil 0 nil nil))
        (Alpha (sign 1 A) (Leaf (((sign 1 A); nil)::lN) nil 0 nil nil))
  end.

Definition Conj_rule
  (s : nat)
  (A B : LF)
  (lN : list (pair SLF (list SLF)))
  : btree SLF :=
  match s with
  | 0 => (* F *)
      Beta
        (Alpha (sign 0 A) (Leaf (((sign 0 A); nil)::lN) nil 0 nil nil))
        (Alpha (sign 0 B) (Leaf (((sign 0 B); nil)::lN) nil 0 nil nil))
  | 1 => (* t *)
      Beta
        (Alpha (sign 2 A)
           (Alpha (sign 1 B)
              (Leaf (((sign 2 A); nil)::((sign 1 B); nil)::lN) nil 0 nil nil)))
        (Beta
           (Alpha (sign 1 A)
              (Alpha (sign 2 B)
                 (Leaf (((sign 1 A); nil)::((sign 2 B); nil)::lN) nil 0 nil nil)))
           (Alpha (sign 1 A)
              (Alpha (sign 1 B)
                 (Leaf (((sign 1 A); nil)::((sign 1 B); nil)::lN) nil 0 nil nil))))
  | _ => (* T *)
       Beta
        (Beta
           (Alpha (sign 2 A)
              (Alpha (sign 2 B)
                 (Leaf (((sign 2 A); nil)::((sign 2 B); nil)::lN) nil 0 nil nil)))
           (Alpha (sign 2 A)
              (Alpha (sign 1 B)
                 (Leaf (((sign 2 A); nil)::((sign 1 B); nil)::lN) nil 0 nil nil))))
        (Beta
           (Alpha (sign 1 A)
              (Alpha (sign 2 B)
                 (Leaf (((sign 1 A); nil)::((sign 2 B); nil)::lN) nil 0 nil nil)))
           (Alpha (sign 1 A)
              (Alpha (sign 1 B)
                 (Leaf (((sign 1 A); nil)::((sign 1 B); nil)::lN) nil 0 nil nil))))
  end.

Compute proj_r (1;2).

Definition Disj_rule
  (s : nat)
  (A B : LF)
  (lN : list (pair SLF (list SLF)))
  : btree SLF :=
  match s with
  | 0 => (* F *)
      Alpha (sign 0 A)
        (Alpha (sign 0 B)
           (Leaf (((sign 0 A); nil)::((sign 0 B); nil)::lN) nil 0 nil nil))
  | 1 => (* t *)
      Beta
        (Alpha (sign 1 A) (Leaf (((sign 1 A); nil)::lN) nil 0 nil nil))
        (Alpha (sign 1 B) (Leaf (((sign 1 B); nil)::lN) nil 0 nil nil))
  | _ => (* T *)
      Beta
        (Beta
           (Alpha (sign 2 A) (Leaf (((sign 2 A); nil)::lN) nil 0 nil nil))
           (Alpha (sign 1 A) (Leaf (((sign 1 A); nil)::lN) nil 0 nil nil)))
        (Beta
           (Alpha (sign 2 B) (Leaf (((sign 2 B); nil)::lN) nil 0 nil nil))
           (Alpha (sign 1 B) (Leaf (((sign 1 B); nil)::lN) nil 0 nil nil)))
  end.

Definition Impl_rule
  (s : nat)
  (A B : LF)
  (lN : list (pair SLF (list SLF)))
  : btree SLF :=
  match s with
  | 0 => (* F *)
      Beta
        (Alpha (sign 2 A)
           (Alpha (sign 0 B)
              (Leaf (((sign 2 A); nil)::((sign 0 B); nil)::lN) nil 0 nil nil)))
        (Alpha (sign 1 A)
           (Alpha (sign 0 B)
              (Leaf (((sign 1 A); nil)::((sign 0 B); nil)::lN) nil 0 nil nil)))
  | 1 => (* t *)
      Beta
        (Alpha (sign 1 A)
           (Alpha (sign 2 B)
              (Leaf (((sign 1 A); nil)::((sign 2 B); nil)::lN) nil 0 nil nil)))
        (Alpha (sign 1 B)
           (Leaf (((sign 1 B); nil)::lN) nil 0 nil nil))
  | _ => (* T *)
      Beta
        (Alpha (sign 0 A) (Leaf (((sign 0 A); nil)::lN) nil 0 nil nil))
        (Beta
           (Alpha (sign 2 B) (Leaf (((sign 2 B); nil)::lN) nil 0 nil nil))
           (Alpha (sign 1 B) (Leaf (((sign 1 B); nil)::lN) nil 0 nil nil)))
  end.

Definition C1_Tableau
  (snapshot : btree SLF)
  (lc : list (check SLF))
  (listNodes : list (pair SLF (list SLF)))
  (listR : list SLF)
  (loop_counter1 : nat)
  (cmodels : list (list SLF))
  (lvals : list SLF)
  (m : list (mem SLF))
  (p : parameters) :=
  match listNodes with
  | nil => state _ _ (Leaf nil nil 0 nil nil) lc m
  | h::tl =>
      let toExpand := proj_l h in
      match toExpand with
      | sign s A =>
          match A with
          | Atom _ => state _ _ (Leaf (explode listNodes) nil 0 nil nil) nil nil
          | ~ B => state _ _ (Neg_rule s B (explode listNodes)) nil nil
          | B /\ C => state _ _ (Conj_rule s B C (explode listNodes)) nil nil
          | B \/ C => state _ _ (Disj_rule s B C (explode listNodes)) nil nil
          | B -> C => state _ _ (Impl_rule s B C (explode listNodes)) nil nil
          end
      end
  end.

Fixpoint makeInitialTree
  (listNodes lNcp : list (pair SLF (list SLF))) :=
  match listNodes with
  | nil => Leaf lNcp nil 0 nil nil
  | h::tl =>
      match h with
      | Pair s _ => Alpha s (makeInitialTree tl lNcp)
      end
  end.

Compute pop [1;2;3] 2.

Definition makeC1 (A : LF) (deepness : nat) :=
  let lN := [((sign 0 A); nil)] in
  let initialTree := makeInitialTree lN lN in
  let trees := make _ _ C1_Tableau (makeInitialTree lN lN) deepness in
  pop trees (Leaf nil nil 0 nil nil).

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

Compute isContradiction (~p0 /\ p1).

Definition cond2 (A : SLF) :=
  match A with
  | sign s P => andb (Nat.eqb s 1) (isContradiction P)
  end.
        
Definition contra (A B : SLF) :=
  match A, B with
  | sign L P, sign L' Q =>
      if eqb_lf P Q then
        orb
          (negb (Nat.eqb L L'))
          (orb
             (cond2 A)
             (cond2 B))
      else false
  end.

Definition A0 := (~~~p1 -> ~p1).

Compute parse (makeC1 A0 10) nil.

Compute closure (makeC1 A0 20) contra.

(* EXAMPLES *)

Definition propag_consist_conj_1 :=
  ((cngen2 p0 1) /\ (cngen2 p1 1)) -> (cngen2 (p0 /\ p1) 1).
Definition propag_consist_disj_1 :=
  ((cngen2 p0 1) /\ (cngen2 p1 1)) -> (cngen2 (p0 \/ p1) 1).
Definition propag_consist_impl_1 :=
  ((cngen2 p0 1) /\ (cngen2 p1 1)) -> (cngen2 (p0 -> p1) 1).

Definition propag_consist_conj_2 :=
  ((cngen2 p0 2) /\ (cngen2 p1 2)) -> (cngen2 (p0 /\ p1) 2).
Definition propag_consist_disj_2 :=
  ((cngen2 p0 2) /\ (cngen2 p1 2)) -> (cngen2 (p0 \/ p1) 2).
Definition propag_consist_impl_2 :=
  ((cngen2 p0 2) /\ (cngen2 p1 2)) -> (cngen2 (p0 -> p1) 2).

Definition propag_consist_conj_3 :=
  ((cngen2 p0 3) /\ (cngen2 p1 3)) -> (cngen2 (p0 /\ p1) 3).

Definition propag_consist_conj_4 :=
  ((cngen2 p0 4) /\ (cngen2 p1 4)) -> (cngen2 (p0 /\ p1) 4).

Compute cngen2 p0 1.
Compute propag_consist_conj_1.
Compute closure (makeC1 (~~p0 -> p0) 20) contra.

Compute closure (makeC1 propag_consist_conj_1 20) contra.
Compute closure (makeC1 propag_consist_disj_1 20) contra.
Compute closure (makeC1 propag_consist_impl_1 20) contra.
