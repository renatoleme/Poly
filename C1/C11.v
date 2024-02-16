(* 

Implementation of the tableau for C1 presented in:

CONIGLIO, Marcelo E.; TOLEDO, Guilherme V. Two Decision Procedures for da Costa’s C n Logics Based on Restricted Nmatrix Semantics. Studia Logica, v. 110, n. 3, p. 601-642, 2022.

*)

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
          if isContradiction B then
            if eqb_lf (selectContra C D) C then
              1 + (whichIndex C)
            else
              1 + (whichIndex D)
          else
            0
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

We will adopt the following convention: 

0 : False 
1 : t0
2 : True

*)

Definition Neg_rule
  (s : nat)
  (A : LF)
  (lN : list (pair SLF (list SLF)))
  (branch : list SLF)
  : btree SLF :=
  match s with
  | 0 => (* F *)
      Alpha (sign 2 A) (Leaf (((sign 2 A); nil)::lN) ((sign 2 A)::branch) 0 nil nil)
  | 1 => (* t *)
      Alpha (sign 1 A) (Leaf (((sign 1 A); nil)::lN) ((sign 1 A)::branch) 0 nil nil)
  | _ => (* T *)
      Beta
        (Alpha (sign 0 A) (Leaf (((sign 0 A); nil)::lN) ((sign 0 A)::branch) 0 nil nil))
        (Alpha (sign 1 A) (Leaf (((sign 1 A); nil)::lN) ((sign 1 A)::branch) 0 nil nil))
  end.

Definition Conj_rule
  (s : nat)
  (A B : LF)
  (lN : list (pair SLF (list SLF)))
  (branch : list SLF)
  : btree SLF :=
  match s with
  | 0 => (* F *)
      Beta
        (Alpha (sign 0 A) (Leaf (((sign 0 A); nil)::lN) ((sign 0 A)::branch) 0 nil nil))
        (Alpha (sign 0 B) (Leaf (((sign 0 B); nil)::lN) ((sign 0 B)::branch) 0 nil nil))
  | 1 => (* t *)
      Beta
        (Alpha (sign 2 A)
           (Alpha (sign 1 B)
              (Leaf
                 (((sign 2 A); nil)::((sign 1 B); nil)::lN)
                 ((sign 2 A)::(sign 1 B)::branch) 0 nil nil)))
        (Beta
           (Alpha (sign 1 A)
              (Alpha (sign 2 B)
                 (Leaf
                    (((sign 1 A); nil)::((sign 2 B); nil)::lN)
                    ((sign 1 A)::(sign 2 B)::branch) 0 nil nil)))
           (Alpha (sign 1 A)
              (Alpha (sign 1 B)
                 (Leaf
                    (((sign 1 A); nil)::((sign 1 B); nil)::lN)
                    ((sign 1 A)::(sign 1 B)::branch) 0 nil nil))))
  | _ => (* T *)
       Beta
        (Beta
           (Alpha (sign 2 A)
              (Alpha (sign 2 B)
                 (Leaf
                    (((sign 2 A); nil)::((sign 2 B); nil)::lN)
                    ((sign 2 A)::(sign 2 B)::branch) 0 nil nil)))
           (Alpha (sign 2 A)
              (Alpha (sign 1 B)
                 (Leaf
                    (((sign 2 A); nil)::((sign 1 B); nil)::lN)
                    ((sign 2 A)::(sign 1 B)::branch) 0 nil nil))))
        (Beta
           (Alpha (sign 1 A)
              (Alpha (sign 2 B)
                 (Leaf
                    (((sign 1 A); nil)::((sign 2 B); nil)::lN)
                    ((sign 1 A)::(sign 2 B)::branch) 0 nil nil)))
           (Alpha (sign 1 A)
              (Alpha (sign 1 B)
                 (Leaf
                    (((sign 1 A); nil)::((sign 1 B); nil)::lN)
                    ((sign 1 A)::(sign 1 B)::branch) 0 nil nil))))
  end.

Compute proj_r (1;2).

Definition Disj_rule
  (s : nat)
  (A B : LF)
  (lN : list (pair SLF (list SLF)))
  (branch : list SLF)
  : btree SLF :=
  match s with
  | 0 => (* F *)
      Alpha (sign 0 A)
        (Alpha (sign 0 B)
           (Leaf
              (((sign 0 A); nil)::((sign 0 B); nil)::lN)
              ((sign 0 A)::(sign 0 B)::branch) 0 nil nil))
  | 1 => (* t *)
      Beta
        (Alpha (sign 1 A) (Leaf (((sign 1 A); nil)::lN) ((sign 1 A)::branch) 0 nil nil))
        (Alpha (sign 1 B) (Leaf (((sign 1 B); nil)::lN) ((sign 1 B)::branch) 0 nil nil))
  | _ => (* T *)
      Beta
        (Beta
           (Alpha (sign 2 A) (Leaf (((sign 2 A); nil)::lN) ((sign 2 A)::branch) 0 nil nil))
           (Alpha (sign 1 A) (Leaf (((sign 1 A); nil)::lN) ((sign 1 A)::branch) 0 nil nil)))
        (Beta
           (Alpha (sign 2 B) (Leaf (((sign 2 B); nil)::lN) ((sign 2 B)::branch) 0 nil nil))
           (Alpha (sign 1 B) (Leaf (((sign 1 B); nil)::lN) ((sign 1 B)::branch) 0 nil nil)))
  end.

Definition Impl_rule
  (s : nat)
  (A B : LF)
  (lN : list (pair SLF (list SLF)))
  (branch : list SLF)
  : btree SLF :=
  match s with
  | 0 => (* F *)
      Beta
        (Alpha (sign 2 A)
           (Alpha (sign 0 B)
              (Leaf
                 (((sign 2 A); nil)::((sign 0 B); nil)::lN)
                 ((sign 2 A)::(sign 0 B)::branch) 0 nil nil)))
        (Alpha (sign 1 A)
           (Alpha (sign 0 B)
              (Leaf
                 (((sign 1 A); nil)::((sign 0 B); nil)::lN)
                 ((sign 1 A)::(sign 0 B)::branch) 0 nil nil)))
  | 1 => (* t *)
      Beta
        (Alpha (sign 1 A)
           (Alpha (sign 2 B)
              (Leaf
                 (((sign 1 A); nil)::((sign 2 B); nil)::lN)
                 ((sign 1 A)::(sign 2 B)::branch) 0 nil nil)))
        (Alpha (sign 1 B)
           (Leaf (((sign 1 B); nil)::lN) ((sign 1 B)::branch) 0 nil nil))
  | _ => (* T *)
      Beta
        (Alpha (sign 0 A) (Leaf (((sign 0 A); nil)::lN) ((sign 0 A)::branch) 0 nil nil))
        (Beta
           (Alpha (sign 2 B) (Leaf (((sign 2 B); nil)::lN) ((sign 2 B)::branch) 0 nil nil))
           (Alpha (sign 1 B) (Leaf (((sign 1 B); nil)::lN) ((sign 1 B)::branch) 0 nil nil)))
  end.

(* DERIVED RULES *)

Definition isBola (A : LF) := Nat.eqb (whichIndex A) 1.

Compute isBola (cngen (p0) 1).
Compute whichIndex (~((~(p1 /\ ~p1)) /\ ~(~(p1 /\ ~p1)))).

Definition derived1
  (B C : LF)
  (lN : list (pair SLF (list SLF)))
  (branch : list SLF)
  :=
  let contradicted := selectContra B C in
  Alpha (sign 1 contradicted)
    (Leaf
       (((sign 1 contradicted); nil)::lN)
       ((sign 1 contradicted)::branch) 0 nil nil).

Definition derived2
  (B C : LF)
  (lN : list (pair SLF (list SLF)))
  (branch : list SLF)
  :=
  let contradicted := selectContra B C in
  Beta
    (Alpha (sign 2 contradicted)
       (Leaf (((sign 2 contradicted); nil)::lN) ((sign 2 contradicted)::branch) 0 nil nil))
    (Alpha (sign 0 contradicted)
       (Leaf (((sign 0 contradicted); nil)::lN) ((sign 0 contradicted)::branch) 0 nil nil)).

Definition derived3
  (B C : LF)
  (lN : list (pair SLF (list SLF)))
  (branch : list SLF)
  :=
  Beta
    (Beta
       (Alpha (sign 2 B)
          (Alpha (sign 2 C)
             (Leaf
                (((sign 2 B); nil)::((sign 2 C); nil)::lN)
                ((sign 2 B)::(sign 2 C)::branch) 0 nil nil)))
       (Alpha (sign 2 B)
          (Alpha (sign 0 C)
             (Leaf
                (((sign 2 B); nil)::((sign 0 C); nil)::lN)
                ((sign 2 B)::(sign 0 C)::branch) 0 nil nil))))
    (Beta
       (Alpha (sign 0 B)
          (Alpha (sign 2 C)
             (Leaf
                (((sign 0 B); nil)::((sign 2 C); nil)::lN)
                ((sign 0 B)::(sign 2 C)::branch) 0 nil nil)))
       (Alpha (sign 0 B)
          (Alpha (sign 0 C)
             (Leaf
                (((sign 0 B); nil)::((sign 0 C); nil)::lN)
                ((sign 0 B)::(sign 0 C)::branch) 0 nil nil)))).

Definition derived4
  (B : LF)
  (lN : list (pair SLF (list SLF)))
  (branch : list SLF)
  :=
  Alpha (sign 1 B) (Leaf (((sign 1 B); nil)::lN) ((sign 1 B)::branch) 0 nil nil).

Definition derived5
  (B : LF)
  (lN : list (pair SLF (list SLF)))
  (branch : list SLF)
  :=
  Beta
    (Alpha (sign 2 B) (Leaf (((sign 2 B); nil)::lN) ((sign 2 B)::branch) 0 nil nil))
    (Alpha (sign 0 B) (Leaf (((sign 0 B); nil)::lN) ((sign 0 B)::branch) 0 nil nil)).

Definition derived6
  (B C : LF)
  (lN : list (pair SLF (list SLF)))
  (branch : list SLF)
  :=
  Beta
    (Alpha (sign 1 B) (Leaf (((sign 1 B); nil)::lN) ((sign 1 B)::branch) 0 nil nil))
    (Alpha (sign 1 C) (Leaf (((sign 1 C); nil)::lN) ((sign 1 C)::branch) 0 nil nil)).

Definition closeBranch : btree SLF :=
  Alpha (sign 0 (Atom "p"))
    (Alpha (sign 1 (Atom "p"))
       (Leaf nil nil 1 nil nil)).

(**)
(* lFBTC (lookForBranchesToClose) *)
(**)
Fixpoint lFBTC_aux2
  (cond : SLF -> SLF -> bool)
  (h1 : SLF)
  (l : list SLF)
  :=
  match l with
  | nil => false
  | h2::tl =>
      if cond h1 h2 then true
      else
        lFBTC_aux2 cond h1 tl
  end.

Fixpoint lFBTC_aux1
  (cond : SLF -> SLF -> bool)
  (l cpl : list SLF)
  :=
  match l with
  | nil => false
  | h::tl =>
      if lFBTC_aux2 cond h cpl then true
      else lFBTC_aux1 cond tl cpl
  end.

Fixpoint lFBTC
  (t : btree SLF)
  (cond : SLF -> SLF -> bool)
  :=
  match t with
  | Leaf lN branch tag _ lvals =>
      if Nat.eqb tag 0 then
        if lFBTC_aux1 cond branch branch then
          closeBranch
        else
          Leaf lN branch tag nil lvals
      else
        Leaf lN branch tag nil lvals
  | Alpha N nT =>
      Alpha N (lFBTC nT cond)
  | Beta nT1 nT2 =>
      Beta
        (lFBTC nT1 cond)
        (lFBTC nT2 cond)
  end.

Definition derivedDriver
  (s : nat)
  (A : LF)
  (lN : list (pair SLF (list SLF)))
  (branch : list SLF)
  : stt SLF SLF
  :=
  match A with
  | B /\ C =>
      if isContradiction A then
        if Nat.eqb s 2 then
          state _ _ (derived1 B C lN branch) nil nil
        else
          if Nat.eqb s 0 then
            state _ _ (derived2 B C lN branch) nil nil
          else
            state _ _ (Conj_rule s B C lN branch) nil nil
      else
        if andb (isBola B) (isBola C) then
          let baseB := whichFormula B 1 in
          let baseC := whichFormula C 1 in
          if Nat.eqb s 2 then
            state _ _ (derived3 baseB baseC lN branch) nil nil
          else
            if Nat.eqb s 1 then
              state _ _ (closeBranch) nil nil
            else
              state _ _ (derived6 baseB baseC lN branch) nil nil
        else
          state _ _ (Conj_rule s B C lN branch) nil nil
  | ~ B =>
      if isBola A then
        let base := whichFormula A 1 in
        if Nat.eqb s 0 then state _ _ (derived4 base lN branch) nil nil
        else
          if Nat.eqb s 1 then state _ _ (closeBranch) nil nil
          else state _ _ (derived5 base lN branch) nil nil
      else
        state _ _ (Neg_rule s B lN branch) nil nil
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
          | Atom _ => state _ _ (Leaf (explode listNodes) branch 0 nil nil) nil nil
          | ~ B => state _ _ (Neg_rule s B (explode listNodes) branch) nil nil
          | B /\ C => state _ _ (Conj_rule s B C (explode listNodes) branch) nil nil
          | B \/ C => state _ _ (Disj_rule s B C (explode listNodes) branch) nil nil
          | B -> C => state _ _ (Impl_rule s B C (explode listNodes) branch) nil nil
          end
      end
  end.

Fixpoint insert {X : Type} 
  (i : X) 
  (l : list X) 
  (cmp : X -> X -> bool)
  :=
  match l with
  | [] => [i]
  | h :: t => if cmp i h then i :: h :: t else h :: insert i t cmp
  end.

Fixpoint sort
  {X : Type} 
  (l : list X) 
  (cmp : X -> X -> bool)
  : list X :=
  match l with
  | [] => []
  | h :: t => insert h (sort t cmp) cmp
  end.

Require Import Arith.
Require Import Nat.

Compute 2 <=? 2.

Compute sort [3;1;4;1;5;9;2;6;5;3;5] Nat.ltb.

(* Define a order P < Q *)
Definition cmp_SLF (P Q : pair SLF (list SLF)) :=
  let sP := proj_l P in
  let sQ := proj_l Q in
  match sP with
  |  sign s1 P0 =>
    match sQ with
    |  sign s2 Q0 =>
      match P0 with
      | Atom _ => true
      | ~ A =>        
        if orb (Nat.eqb s1 0) (Nat.eqb s1 1) then true
        else
          match Q0 with
          | Atom _ => false
          | ~ B =>
            if orb (Nat.eqb s2 0) (Nat.eqb s2 1) then false
            else true
          | B /\ C => true
          | B \/ C =>
            if Nat.eqb s2 0 then false
            else true
          | B -> C =>
            if orb (Nat.eqb s2 0) (Nat.eqb s2 1) then false
            else true
          end
      | A /\ B => false
      | A \/ B =>
        if Nat.eqb s1 0 then true
        else false
      | A -> B =>
        if orb (Nat.eqb s1 0) (Nat.eqb s1 1) then true
        else false
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
  let lN_ordered := sort listNodes cmp_SLF in
  match lN_ordered with
  | nil => state _ _ (Leaf nil nil 0 nil nil) lc m
  | h::tl =>
      let toExpand := proj_l h in
      match toExpand with
      | sign s A =>
          match A with
          | Atom _ => state _ _ (Leaf (explode listNodes) branch 0 nil nil) nil nil
          | ~ B => derivedDriver s A (explode listNodes) branch
          | B /\ C => derivedDriver s A (explode listNodes) branch
          | B \/ C => state _ _ (Disj_rule s B C (explode listNodes) branch) nil nil
          | B -> C => state _ _ (Impl_rule s B C (explode listNodes) branch) nil nil
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

Fixpoint makeC1_aux (t : btree SLF) (deepness : nat) :=
  match deepness with
  | O => t
  | S m =>
      let ntree := pop (make _ _ C1_Tableau t 1) (Leaf nil nil 0 nil nil) in
      let opt_tree := (lFBTC ntree contra) in
      if leafsClean opt_tree
      then
        opt_tree
      else
        makeC1_aux opt_tree m
  end.

Fixpoint makeC1_optimal_aux (t : btree SLF) (deepness : nat) :=
  match deepness with
  | O => t
  | S m =>
      let ntree := pop (make _ _ C1_Tableau_optimal t 1) (Leaf nil nil 0 nil nil) in
      let opt_tree := (lFBTC ntree contra) in
      if leafsClean opt_tree
      then
        opt_tree
      else
        makeC1_optimal_aux opt_tree m
  end.

Definition makeC1 (A : LF) (deepness : nat) (t : nat) :=
  let lN := [((sign t A); nil)] in
  let initialTree := makeInitialTree lN lN in
  let result := makeC1_aux initialTree deepness in
  result.

Definition makeC1_optimal (A : LF) (deepness : nat) (t : nat) :=
  let lN := [((sign t A); nil)] in
  let initialTree := makeInitialTree lN lN in
  let result := makeC1_optimal_aux initialTree deepness in
  result.

(* Sequents addons *)

Fixpoint makeLN (l : list LF) (v : nat) : list (pair SLF (list SLF)) :=
  match l with
  | nil => nil
  | h::tl => ((sign v h); nil)::(makeLN tl v)
  end.

Definition makeC1_optimal_seq (lh lc : list LF) (deepness : nat) (t : nat) :=
  let hyp := makeLN lh 2 in
  let cnc := makeLN lc 0 in
  let initialTree := makeInitialTree (hyp++cnc) (hyp++cnc) in
  let result := makeC1_optimal_aux initialTree deepness in
  result.

Require Import ZArith.
Open Scope Z_scope.

Fixpoint lengthZ {X : Type} (l : list X) : Z :=
  match l with
  | nil => 0
  | h::tl => 1 + (lengthZ tl)
  end.

Fixpoint matrixSizeZ {X : Type} (l : list (list X)) : Z :=
  match l with
  | nil => 0
  | h::tl => (lengthZ h) + (matrixSizeZ tl)
  end.

Close Scope Z_scope.

Fixpoint matrixSize {X : Type} (l : list (list X)) : nat :=
  match l with
  | nil => 0
  | h::tl => (List.length h) + (matrixSize tl)
  end.

Definition branchesCount
  (t : btree SLF)
  :=
  List.length (parse t nil).

Definition matrixSizeCount
  (t : btree SLF)
  :=
  matrixSize (parse t nil).

Definition decideClosure
  (t : btree SLF)
  :=
  closure t contra.

Fixpoint getFirstNEls {X : Type} (l : list X) (n : nat) :=
  match n, l with
  | S m, h::tl => h::(getFirstNEls tl m)
  | _, _ => nil
  end.

Fixpoint getLastNEls {X : Type} (l : list X) (n : nat) :=
  match n with
  | O => l
  | S m => getLastNEls (explode l) m
  end.

(* Extractions for Ocaml *)

Require Coq.extraction.Extraction.

Definition makeTableau_lazy (A : LF) (t : nat) :=
  makeC1 A 100 t.

Definition makeTableau (A : LF) (t : nat) :=
  makeC1_optimal A 100 t.

Definition makeTableauSeq (hyp conc : list LF) (t : nat) :=
  makeC1_optimal_seq hyp conc 100 t.

Require Coq.extraction.ExtrOcamlString.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction
  makeTableauSeq.

Recursive Extraction
  branchesCount
  matrixSizeCount
  decideClosure
  makeC1_optimal
  makeC1
  cngen2
  makeTableau.

(*

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

*)
