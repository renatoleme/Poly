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

Fixpoint whichIndex (A : LF) :=
  match A with
  | ~ B =>
      match B with
      | C /\ D =>
          if eqb_lf (selectContra C D) C then
            1 + (whichIndex C)
          else
            1 + (whichIndex D)
      | _ => 0
      end
  | _ => 0
  end.

Fixpoint whichFormula (A : LF) (n : nat) :=
  match n with
  | O => A
  | S m =>
      match A with
      | ~ B =>
          match B with
          | C /\ D => whichFormula (selectContra C D) m
          | _ => A
          end
      | _ => A
      end
  end.

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

(* DERIVED RULES *)

Definition isBola (A : LF) := Nat.eqb (whichIndex A) 1.
  (*match A with
  | ~ B => isContradiction B
  | _ => false
  end.*)


Compute isBola (cngen (p0) 1).
Compute whichIndex (~((~(p1 /\ ~p1)) /\ ~(~(p1 /\ ~p1)))).

Definition derived1
  (B C : LF)
  (lN : list (pair SLF (list SLF)))
  :=
  let contradicted := selectContra B C in
  Alpha (sign 1 contradicted)
    (Leaf (((sign 1 contradicted); nil)::lN) nil 0 nil nil).

Definition derived2
  (B C : LF)
  (lN : list (pair SLF (list SLF)))
  :=
  let contradicted := selectContra B C in
  Beta
    (Alpha (sign 2 contradicted) (Leaf (((sign 2 contradicted); nil)::lN) nil 0 nil nil))
    (Alpha (sign 0 contradicted) (Leaf (((sign 0 contradicted); nil)::lN) nil 0 nil nil)).

Definition derived3
  (B C : LF)
  (lN : list (pair SLF (list SLF)))
  :=
  Beta
    (Beta
       (Alpha (sign 2 B)
          (Alpha (sign 2 C)
             (Leaf (((sign 2 B); nil)::((sign 2 C); nil)::lN) nil 0 nil nil)))
       (Alpha (sign 2 B)
          (Alpha (sign 0 C)
             (Leaf (((sign 2 B); nil)::((sign 0 C); nil)::lN) nil 0 nil nil))))
    (Beta
       (Alpha (sign 0 B)
          (Alpha (sign 2 C)
             (Leaf (((sign 0 B); nil)::((sign 2 C); nil)::lN) nil 0 nil nil)))
       (Alpha (sign 0 B)
          (Alpha (sign 0 C)
             (Leaf (((sign 0 B); nil)::((sign 0 C); nil)::lN) nil 0 nil nil)))).

Definition derived4
  (B : LF)
  (lN : list (pair SLF (list SLF))) :=
  Alpha (sign 1 B) (Leaf (((sign 1 B); nil)::lN) nil 0 nil nil).

Definition derived5
  (B : LF)
  (lN : list (pair SLF (list SLF))) :=
  Beta
    (Alpha (sign 2 B) (Leaf (((sign 2 B); nil)::lN) nil 0 nil nil))
    (Alpha (sign 0 B) (Leaf (((sign 0 B); nil)::lN) nil 0 nil nil)).

Definition derived6
  (B C : LF)
  (lN : list (pair SLF (list SLF))) :=
  Beta
    (Alpha (sign 1 B) (Leaf (((sign 1 B); nil)::lN) nil 0 nil nil))
    (Alpha (sign 1 C) (Leaf (((sign 1 B); nil)::lN) nil 0 nil nil)).

Definition closeBranch : btree SLF :=
  Alpha (sign 0 (Atom "p"))
    (Alpha (sign 1 (Atom "p"))
       (Leaf nil nil 1 nil nil)).

(**)
(* lFBTC (lookForBranchesToClose) *)
(**)
Fixpoint lFBTC_aux
  (control : bool)
  (n1 : SLF)
  (t : btree SLF)
  (cond : SLF -> SLF -> bool)
  :=
  match t with
  | Leaf lN _ tag _ _ =>
      if control then tag::nil
      else nil
  | Alpha n2 nT =>
      if cond n1 n2 then lFBTC_aux true n1 nT cond
      else lFBTC_aux control n1 nT cond
  | Beta nT1 nT2 =>
      (lFBTC_aux control n1 nT1 cond)++
        (lFBTC_aux control n1 nT2 cond)
  end.

Fixpoint lFBTC_aux2
  (t : btree SLF)
  (cond : SLF -> SLF -> bool)
  :=
  match t with
  | Leaf lN _ tag _ _ => nil
  | Alpha N nT =>
      (lFBTC_aux false N nT cond)++(lFBTC_aux2 nT cond)
  | Beta nT1 nT2 =>
      (lFBTC_aux2 nT1 cond)++
        (lFBTC_aux2 nT2 cond)
  end.
    
Compute isElementInList [1;2;3] 2 Nat.eqb.

Fixpoint lFBTC_aux1
  (t : btree SLF)
  (l : list nat)
  :=
  match t with
  | Leaf lN _ tag _ _ =>
      if negb (Nat.eqb (List.length lN) 0) then
        if isElementInList l tag Nat.eqb then closeBranch
        else Leaf lN nil 0 nil nil
      else Leaf nil nil tag nil nil
  | Alpha N nT =>
      Alpha N (lFBTC_aux1 nT l)
  | Beta nT1 nT2 =>
      Beta
        (lFBTC_aux1 nT1 l)
        (lFBTC_aux1 nT2 l)
  end.

Definition lFBTC
  (t : btree SLF)
  (cond : SLF -> SLF -> bool)
  :=
  let taggedT := tagLeafs t in
  let lClosed := lFBTC_aux2 taggedT cond in
  lFBTC_aux1 taggedT lClosed.

Definition derivedDriver
  (s : nat)
  (A : LF)
  (lN : list (pair SLF (list SLF)))
  : stt SLF SLF
  :=
  match A with
  | B /\ C =>
      if isContradiction A then
        if Nat.eqb s 2 then
          state _ _ (derived1 B C lN) nil nil
        else
          if Nat.eqb s 0 then
            state _ _ (derived2 B C lN) nil nil
          else
            state _ _ (Conj_rule s B C lN) nil nil
      else
        if andb (isBola B) (isBola C) then
          let baseB := whichFormula B 1 in
          let baseC := whichFormula C 1 in
          if Nat.eqb s 2 then
            state _ _ (derived3 baseB baseC lN) nil nil
          else
            if Nat.eqb s 1 then
              state _ _ (closeBranch) nil nil
            else
              state _ _ (derived6 baseB baseC lN) nil nil
        else
          state _ _ (Conj_rule s B C lN) nil nil
  | ~ B =>
      if isBola A then
        let base := whichFormula A 1 in
        if Nat.eqb s 0 then state _ _ (derived4 base lN) nil nil
        else
          if Nat.eqb s 1 then state _ _ (closeBranch) nil nil
          else state _ _ (derived5 base lN) nil nil
      else
        state _ _ (Neg_rule s B lN) nil nil
  | _ => state _ _ (Leaf nil nil 0 nil nil) nil nil
  end.

Definition C1_Tableau
  (snapshot : btree SLF)
  (lc : list (check SLF))
  (listNodes : list (pair SLF (list SLF)))
  (branch : list SLF)
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

Definition C1_Tableau_optimal
  (snapshot : btree SLF)
  (lc : list (check SLF))
  (listNodes : list (pair SLF (list SLF)))
  (branch : list SLF)
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
          | ~ B => derivedDriver s A (explode listNodes)
          | B /\ C => derivedDriver s A (explode listNodes)
          | B \/ C => state _ _ (Disj_rule s B C (explode listNodes)) nil nil
          | B -> C => state _ _ (Impl_rule s B C (explode listNodes)) nil nil
          end
      end
  end.

Definition cond2 (A : SLF) :=
  match A with
  | sign s P => andb (Nat.eqb s 1) (isContradiction P)
  end.

Definition cond3 (A B : SLF) :=
  match A, B with
  | sign 0 P, (sign 0 Q | sign 2 Q) =>
      let f :=
        (fun A B =>
           match A with
           | P /\ Q =>
               if andb (isBola P) (isBola Q) then
                 orb (eqb_lf P B) (eqb_lf Q B)
               else
                 false
           | _ => false
           end
        ) in
      orb (f P Q) (f Q P)
  | _, _ => false
  end.

Compute cond3 (sign 0 ((cngen2 p1 1) /\ (cngen2 p1 1))) (sign 0 (cngen2 p1 1)).

Definition contra (A B : SLF) :=
  match A, B with
  | sign L P, sign L' Q =>
        orb
          (cond3 A B)
          (orb
             (andb (eqb_lf P Q) (negb (Nat.eqb L L')))
             (orb
                (cond2 A)
                (cond2 B)))
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

Fixpoint leafsClean (t : btree SLF) :=
  match t with
  | Leaf lN _ _ _ _ => Nat.eqb (List.length lN) 0
  | Alpha _ nT =>
      leafsClean nT
  | Beta nT1 nT2 =>
      andb
        (leafsClean nT1)
        (leafsClean nT2)
  end.

Fixpoint makeC1_aux (t : btree SLF) (deepness : list nat) :=
  match deepness with
  | nil => t
  | h::tl =>
      let ntree := pop (make _ _ C1_Tableau t h) (Leaf nil nil 0 nil nil) in
      let opt_tree := (lFBTC ntree contra) in
      if orb
           (closure opt_tree contra)
           (leafsClean opt_tree)
      then
        opt_tree
      else
        makeC1_aux opt_tree tl
  end.

Fixpoint makeC1_optimal_aux (t : btree SLF) (deepness : list nat) :=
  match deepness with
  | nil => t
  | h::tl =>
      let ntree := pop (make _ _ C1_Tableau_optimal t h) (Leaf nil nil 0 nil nil) in
      let opt_tree := (lFBTC ntree contra) in
      if orb
           (closure opt_tree contra)
           (leafsClean opt_tree)
      then
        opt_tree
      else
        makeC1_optimal_aux opt_tree tl
  end.

Fixpoint listOf1 (size : nat) :=
  match size with
  | O => nil
  | S n => 1::(listOf1 n)
  end.

Definition makeC1 (A : LF) (deepness : nat) (displayTree : bool) :=
  let lN := [((sign 0 A); nil)] in
  let initialTree := makeInitialTree lN lN in
  let deep := listOf1 deepness in
  let result := makeC1_aux initialTree deep in
  if displayTree then
    (result; (closure result contra; List.length (parse result nil)))
  else
    ((Leaf nil nil 0 nil nil); (closure result contra; List.length (parse result nil))).

Definition makeC1_optimal (A : LF) (deepness : nat) (displayTree : bool) :=
  let lN := [((sign 0 A); nil)] in
  let initialTree := makeInitialTree lN lN in
  let deep := listOf1 deepness in
  let result := makeC1_optimal_aux initialTree deep in
  if displayTree then
    (result; (closure result contra; List.length (parse result nil)))
  else
    ((Leaf nil nil 0 nil nil); (closure result contra; List.length (parse result nil))).

Definition A0 := (~~p2 -> p2).

Compute makeC1_optimal A0 20 true.

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
Definition propag_consist_disj_3 :=
  ((cngen2 p0 3) /\ (cngen2 p1 3)) -> (cngen2 (p0 \/ p1) 3).
Definition propag_consist_impl_3 :=
  ((cngen2 p0 3) /\ (cngen2 p1 3)) -> (cngen2 (p0 -> p1) 3).

Definition propag_consist_conj_4 :=
  ((cngen2 p0 4) /\ (cngen2 p1 4)) -> (cngen2 (p0 /\ p1) 4).

Definition propag_consist_conj_5 :=
  ((cngen2 p0 5) /\ (cngen2 p1 5)) -> (cngen2 (p0 /\ p1) 5).

Definition propag_consist_conj_6 :=
  ((cngen2 p0 6) /\ (cngen2 p1 6)) -> (cngen2 (p0 /\ p1) 6).

Definition propag_consist_conj_7 :=
  ((cngen2 p0 7) /\ (cngen2 p1 7)) -> (cngen2 (p0 /\ p1) 7).

Definition propag_consist_conj_8 :=
  ((cngen2 p0 8) /\ (cngen2 p1 8)) -> (cngen2 (p0 /\ p1) 8).


Compute makeC1_optimal (propag_consist_disj_1) 100 true.

Compute makeC1_optimal propag_consist_conj_4 100 false.


Compute makeC1_optimal (((((p0 /\ ~p0) /\ ~(p0 /\ ~p0)) -> ~~p0))) 100 true.

(**)
(*
Compute makeC1_optimal propag_consist_conj_5 100 false.
Compute makeC1_optimal propag_consist_conj_6 100 false.

Compute makeC1_optimal propag_consist_conj_1 100 false.
Compute makeC1_optimal propag_consist_conj_2 100 false.
Compute makeC1_optimal propag_consist_conj_3 100 false.
Compute makeC1_optimal propag_consist_conj_4 100 false.

Compute makeC1 propag_consist_conj_2 100 false.
Compute makeC1 propag_consist_conj_2 100 false.
Compute makeC1 propag_consist_conj_2 100 false.
Compute makeC1 propag_consist_conj_2 100 false.

*)
