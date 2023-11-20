(* 

Implementation of the tableau for Cn, n>=2, presented in:

CONIGLIO, Marcelo E.; TOLEDO, Guilherme V. Two Decision Procedures for da Costa’s C n Logics Based on Restricted Nmatrix Semantics. Studia Logica, v. 110, n. 3, p. 601-642, 2022.

*)

Add LoadPath "../" as Main.
Require Import Main.Poly.
Require Import List.
Require Import String.
Require Import Arith.
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

(* If A = B /\ ~B or A = ~B /\ B, then return B. *)
Definition selectContra (A B : LF) :=
  if eqb_lf A (~B) then B else A.

Definition selectContradicted (A B : LF) :=
  if eqb_lf A (~B) then A else B.

Definition removeOneNegation (A : LF) :=
  match A with
  | ~ B => B
  | _ => A
  end.

Compute removeOneNegation (~~~p0).
    
Compute selectContradicted (~~p0) (~p0).

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

Compute whichIndex (~ (Atom "p0" /\ Atom "p1")).

Compute cngen p0 2.

Compute whichIndex (cngen p0 3).

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
1 : True
2 : t^n_0
.
.
n+1 : t^n_n-1

 *)

Compute getLastNEls [0;1;2;3;4;4;5;6] 2.

(* General Tools *)

Fixpoint combineV1V2_aux
  (A B : LF)
  (fixed : nat)
  (V : list nat)
  :=
  match V with
  | nil => nil
  | h::tl =>
      ((sign fixed A);(sign h B))::(combineV1V2_aux A B fixed tl)
  end.

Fixpoint combineV1V2
  (A B : LF)
  (V1 V2 : list nat)
  :=
  match V1 with
  | nil => nil
  | h::tl =>
      (combineV1V2_aux A B h V2)++(combineV1V2 A B tl V2)
  end.

Fixpoint unaryComb
  (A : LF)
  (V : list nat)
  (lN : list (pair SLF (list SLF)))
  (lvals : list SLF)
  (branch : list SLF)
  :=
  match V with
  | nil => Leaf lN branch 0 nil nil
  | h::tl =>
      if Nat.eqb (List.length tl) 0
      then
        Alpha
          (sign h A)
          (Leaf (((sign h A); nil)::lN) ((sign h A)::branch) 0 nil lvals)
      else
        Beta
          (Alpha
             (sign h A)
             (Leaf (((sign h A); nil)::lN) ((sign h A)::branch) 0 nil lvals))
          (unaryComb A tl lN lvals branch)
  end.

Fixpoint binComb_aux
  (V : list (pair SLF SLF))
  (lN : list (pair SLF (list SLF)))
  (lvals : list SLF)
  (branch : list SLF)
  :=
  match V with
  | nil => Leaf lN nil 0 nil nil
  | h::tl =>
      let slfA := proj_l h in
      let slfB := proj_r h in
      if Nat.eqb (List.length tl) 0 then
        Alpha slfA
          (Alpha slfB
             (Leaf ((slfA; nil)::(slfB; nil)::lN) (slfA::slfB::branch) 0 nil lvals))
      else
        Beta
          (Alpha slfA
             (Alpha slfB
                (Leaf ((slfA; nil)::(slfB; nil)::lN) (slfA::slfB::branch) 0 nil lvals)))
          (binComb_aux tl lN lvals branch)
  end.

Definition binComb
  (A B : LF)
  (V1 V2 : list nat)
  (lN : list (pair SLF (list SLF)))
  (lvals : list SLF)
  (branch : list SLF)
  :=
  let comb := combineV1V2 A B V1 V2 in
  binComb_aux comb lN lvals branch.

(**)
(* Generalized rule for negation *)
(**)
Definition Neg_rule
  (s : nat)
  (A : LF)
  (lN : list (pair SLF (list SLF)))
  (V : list nat)
  (lvals : list SLF)
  (branch : list SLF)
  : btree SLF :=
  let Fn := 0 in
  let Tn := 1 in
  let In := getLastNEls V 2 in
  match s with
  | 0 => (* Fn *)
      Alpha (sign Tn A) (Leaf (((sign Tn A); nil)::lN) ((sign Tn A)::branch) 0 nil lvals)
  | 1 => (* Tn *)
      Beta
        (Alpha (sign Fn A) (Leaf (((sign Fn A); nil)::lN) ((sign Fn A)::branch) 0 nil lvals))
        (unaryComb A In lN lvals branch)
  | _ => (* any inconsistent value *)
      unaryComb A In lN lvals branch
  end.

(**)
(* Generalized rule for conjunction *)
(**)
Definition Conj_rule
  (s : nat)
  (A B : LF)
  (lN : list (pair SLF (list SLF)))
  (V : list nat)
  (lvals : list SLF)
  (branch : list SLF)
  : btree SLF :=
  let Fn := 0 in
  let Tn := 1 in
  let In := getLastNEls V 2 in
  let Dn := Tn::In in
  match s with
  | 0 => (* Fn *)
      Beta
        (Alpha (sign Fn A) (Leaf ((sign Fn A; nil)::lN) ((sign Fn A)::branch) 0 nil lvals))
        (Alpha (sign Fn B) (Leaf ((sign Fn B; nil)::lN) ((sign Fn B)::branch) 0 nil lvals))
  | 1 => (* Tn *)
      binComb A B Dn Dn lN lvals branch
  | _ => (* any inconsistent value *)
      Beta
        (binComb A B [Tn] In lN lvals branch)
        (Beta
           (binComb A B In In lN lvals branch)
           (binComb B A [Tn] In lN lvals branch))
  end.

(**)
(* Generalized rule for disjunction *)
(**)
Definition Disj_rule
  (s : nat)
  (A B : LF)
  (lN : list (pair SLF (list SLF)))
  (V : list nat)
  (lvals : list SLF)
  (branch : list SLF)
  : btree SLF :=
  let Fn := 0 in
  let Tn := 1 in
  let In := getLastNEls V 2 in
  let Dn := Tn::In in
  match s with
  | 0 => (* Fn *)
      Alpha
        (sign Fn A)
        (Alpha
           (sign Fn B)
           (Leaf
              ((sign Fn A; nil)::(sign Fn B; nil)::lN)
              ((sign Fn A)::(sign Fn B)::branch) 0 nil lvals))
  | 1 => (* Tn *)
      Beta
        (unaryComb A Dn lN lvals branch)
        (unaryComb B Dn lN lvals branch)
  | _ => (* any inconsistent value *)
      Beta
        (unaryComb A In lN lvals branch)
        (unaryComb B In lN lvals branch)
  end.

(**)
(* Generalized rule for implication *)
(**)
Definition Impl_rule
  (s : nat)
  (A B : LF)
  (lN : list (pair SLF (list SLF)))
  (V : list nat)
  (lvals : list SLF)
  (branch : list SLF)
  : btree SLF :=
  let Fn := 0 in
  let Tn := 1 in
  let In := getLastNEls V 2 in
  let Dn := Tn::In in
  match s with
  | 0 => (* Fn *)
      binComb B A [Fn] Dn lN lvals branch
  | 1 => (* Tn *)
      Beta
        (Alpha (sign Fn A)
           (Leaf ((sign Fn A; nil)::lN) ((sign Fn A)::branch) 0 nil lvals))
        (unaryComb B Dn lN lvals branch)
  | _ => (* any inconsistent value *)
      Beta
        (binComb B A [Tn] In lN lvals branch)
        (unaryComb B In lN lvals branch)
  end.

(* DERIVED RULES *)

Definition closeBranch (lvals : list SLF) : btree SLF :=
  Alpha (sign 0 (Atom "p"))
    (Alpha (sign 1 (Atom "p"))
       (Leaf nil nil 1 nil lvals)).

Definition derived1
  (s : nat)
  (B : LF)
  (lN : list (pair SLF (list SLF)))
  (lvals : list SLF)
  (branch : list SLF)
  :=
  Alpha (sign s B) (Leaf (((sign s B); nil)::lN) ((sign s B)::branch) 0 nil lvals).

Compute getLastNEls [2;3;4] 2.

Definition derived2
  (s : nat)
  (B : LF)
  (lN : list (pair SLF (list SLF)))
  (lvals : list SLF)
  (V : list nat)
  (branch : list SLF)
  :=
  let Dnk := getLastNEls (explode (explode V)) s in
  unaryComb B Dnk lN lvals branch.

Fixpoint getFirstNEls {X : Type} (l : list X) (n : nat) :=
  match n, l with
  | S m, h::tl => h::(getFirstNEls tl m)
  | _, _ => nil
  end.

Compute getFirstNEls [1;2;3;4] 3.


Definition derived3
  (s : nat)
  (B : LF)
  (lN : list (pair SLF (list SLF)))
  (lvals : list SLF)
  (V : list nat)
  (branch : list SLF)
  :=
  let Dni := getFirstNEls (explode V) s in
  Beta
    (Alpha (sign 0 B) (Leaf ((sign 0 B; nil)::lN) ((sign 0 B)::branch) 0 nil lvals))
    (unaryComb B Dni lN lvals branch).

Definition derived4
  (s : nat)
  (B : LF)
  (lN : list (pair SLF (list SLF)))
  (lvals : list SLF)
  (V : list nat)
  (branch : list SLF)
  :=
  let Dnj := getFirstNEls (explode V) s in
  Beta
    (Alpha (sign 0 B) (Leaf ((sign 0 B; nil)::lN) ((sign 0 B)::branch) 0 nil lvals))
    (unaryComb B Dnj lN lvals branch).

Compute whichIndex (~(p0 /\ ~p0)).

Definition derived5
  (s : nat)
  (B : LF)
  (lN : list (pair SLF (list SLF)))
  (lvals : list SLF)
  (V : list nat)
  (branch : list SLF)
  :=
  (Alpha (sign s B) (Leaf ((sign s B; nil)::lN) ((sign s B)::branch) 0 nil lvals)).

Definition derived6
  (s : nat)
  (B : LF)
  (lN : list (pair SLF (list SLF)))
  (lvals : list SLF)
  (V : list nat)
  (branch : list SLF)
  :=
  (Alpha (sign s B) (Leaf ((sign s B; nil)::lN) ((sign s B)::branch) 0 nil lvals)).

Compute (cngen p0 12).

Compute whichIndex (~(cngen p0 4)).

Compute getLastNEls [2;3;4] 1.

Definition derived7
  (s : nat)
  (B : LF)
  (lN : list (pair SLF (list SLF)))
  (lvals : list SLF)
  (V : list nat)
  (branch : list SLF)
  :=
  let Dnj := getLastNEls (explode (explode V)) s in
  unaryComb B Dnj lN lvals branch.

Definition derived8
  (s : nat)
  (B : LF)
  (lN : list (pair SLF (list SLF)))
  (lvals : list SLF)
  (V : list nat)
  (branch : list SLF)
  :=
  let Dnu := getLastNEls (explode (explode V)) s in
  unaryComb B Dnu lN lvals branch.

Compute getFirstNEls [1;2;3;4] 1.

Definition derived9
  (s : nat)
  (B : LF)
  (lN : list (pair SLF (list SLF)))
  (lvals : list SLF)
  (V : list nat)
  (branch : list SLF)
  :=
  let Dnj := getFirstNEls (explode V) s in
  Beta
    (unaryComb B Dnj lN lvals branch)
    (Alpha (sign 0 B) (Leaf ((sign 0 B; nil)::lN) ((sign 0 B)::branch) 0 nil lvals)).

Compute whichIndex (selectContra (cngen p0 2) (~(cngen p0 2))).

Compute whichIndex ((cngen p0 10)).

Compute (let i := if true then false else true in if i then 2 else 4).

Compute isContradiction ((Atom "p0" /\ ~ Atom "p0") /\ ~ (Atom "p0" /\ ~ Atom "p0")).
Compute selectContra (Atom "p0" /\ ~ Atom "p0") (~ (Atom "p0" /\ ~ Atom "p0")).
Compute selectContradicted (Atom "p0" /\ ~ Atom "p0") (~ (Atom "p0" /\ ~ Atom "p0")).
Compute whichIndex (selectContradicted (Atom "p0" /\ ~ Atom "p0") (~ (Atom "p0" /\ ~ Atom "p0"))).
Compute whichIndex ( selectContra (Atom "p0" /\ ~ Atom "p0") (~ (Atom "p0" /\ ~ Atom "p0"))).

Compute isContradiction (Atom "p0" /\ ~ Atom "p0").
Compute selectContra (Atom "p0") (~ Atom "p0").
Compute selectContradicted (Atom "p0") (~ Atom "p0").
Compute whichIndex (selectContra (Atom "p0") (~ Atom "p0")).
Compute whichIndex (selectContradicted (Atom "p0") (~ Atom "p0")).

Definition derivedDriver
  (s : nat)
  (A : LF)
  (lN : list (pair SLF (list SLF)))
  (lvals : list SLF)
  (V : list nat)
  (branch : list SLF)
  : stt SLF SLF
  :=
  let Cn := (List.length V) - 2 in (* determine on which n we are in *)
  let tin := fun a => andb (2 <=? a) (a <=? (Cn + 1)) in (* tin is t0n, t1n, ... , t(n-1)n *)
  let Tn := fun a => Nat.eqb a 1 in
  let Fn := fun a => Nat.eqb a 0 in
  match A with
  | B /\ C =>
      if isContradiction A then
        let cB := selectContra B C in
        let cC := selectContradicted B C in
        let expcB := whichIndex cB in
        let expcC := whichIndex cC in
        if Nat.eqb expcB expcC then
          if Tn s then
            let i := whichIndex (selectContra B C) in
            if Cn <=? i then
              state _ _ (closeBranch lvals) nil nil
            else
              if andb (0 <=? i) (i <=? (Cn-1)) then
                state _ _ (derived1 (i+2) (whichFormula (selectContra B C) i) lN lvals branch) nil nil
              else
                state _ _ (Conj_rule s B C lN V lvals branch) nil nil
          else
            if tin s then
              let k := whichIndex (selectContra B C) in
              if (Cn - 1) <=? k then
                state _ _ (closeBranch lvals) nil nil
              else
                if andb (0 <=? k) (k <=? (Cn - 2)) then
                  state _ _ (derived2 (k+1) (whichFormula (selectContra B C) k) lN lvals V branch) nil nil
                else
                  state _ _ (Conj_rule s B C lN V lvals branch) nil nil
            else
              if Fn s then
                let i := whichIndex (selectContra B C) in
                if andb (0 <=? i) (i <=? (Cn-1)) then (* here we use (i-1)+2=i+1 *)
                  state _ _ (derived3 (i+1) (whichFormula (selectContra B C) i) lN lvals V branch) nil nil
                else
                  state _ _ (Conj_rule s B C lN V lvals branch) nil nil
              else
                state _ _ (Conj_rule s B C lN V lvals branch) nil nil
        else
          state _ _ (Conj_rule s B C lN V lvals branch) nil nil
      else
        state _ _ (Conj_rule s B C lN V lvals branch) nil nil
  | ~ B =>
      let expA := whichIndex A in
      if expA =? 0 then
        let r := whichIndex B in
        if andb
             (andb (2 <=? s) (s <=? (Cn+1)))
             (Cn <=? r)
        then
          state _ _ (closeBranch lvals) nil nil
        else
          if Tn s then
            let j := whichIndex B in
            if andb (1 <=? j) (j <=? Cn) then
              state _ _ (derived7 (j-1) (whichFormula B j) lN lvals V branch) nil nil
            else
              state _ _ (Neg_rule s B lN V lvals branch) nil nil
          else
            if Fn s then
              let j := whichIndex B in
              if andb (1 <=? j) (j <=? Cn) then (* here we use (j-2)+2=j *)
                state _ _ (derived9 j (whichFormula B j) lN lvals V branch) nil nil
              else
                state _ _ (Neg_rule s B lN V lvals branch) nil nil
            else
              let u := whichIndex B in
              if andb (1 <=? u) (u <=? (Cn - 1)) then
                state _ _ (derived8 u (whichFormula B u) lN lvals V branch) nil nil
              else
                state _ _ (Neg_rule s B lN V lvals branch) nil nil
      else
        let r := expA in
        if andb
             (andb (2 <=? s) (s <=? (Cn+1)))
             (Cn <=? r)
        then
          state _ _ (closeBranch lvals) nil nil
        else
          if Tn s then
            let j := expA in
            if andb (1 <=? j) (j <=? Cn) then (* here we use (j-2)+2=j *)
              state _ _ (derived4 j (whichFormula A j) lN lvals V branch) nil nil
            else
              state _ _ (Neg_rule s B lN V lvals branch) nil nil
          else
            if Fn s then
              let j := expA in
              if andb (1 <=? j) (j <=? Cn) then (* here we use (j-1)+2=j+1 *)
                state _ _ (derived6 (j+1) (whichFormula A j) lN lvals V branch) nil nil
              else
                state _ _ (Neg_rule s B lN V lvals branch) nil nil
            else
              let u := expA in
              if andb (1 <=? u) (u <=? (Cn - 1)) then
                if andb (0 <=? (s - 2)) ((s - 2) <=? (Cn - u - 1)) then
                  state _ _ (derived5 (s+u) (whichFormula A u) lN lvals V branch) nil nil
                else
                  if andb ((Cn - u) <=? (s-2)) ((s-2) <=? (Cn - 1)) then
                    state _ _ (closeBranch lvals) nil nil
                  else
                    state _ _ (Neg_rule s B lN V lvals branch) nil nil
              else
                state _ _ (Neg_rule s B lN V lvals branch) nil nil
  | _ =>
      state _ _ (Leaf lN branch 0 nil lvals) nil nil
  end.

(* Cn Tableau Def *)

Definition l1 := [(sign 0 p0); (sign 1 p0); (sign 2 p0)].

Compute map (fun x => match x with sign n _ => n end) l1.

Definition Cn_Tableau
  (snapshot : btree SLF)
  (lc : list (check SLF))
  (listNodes : list (pair SLF (list SLF)))
  (branch : list SLF)
  (loop_counter1 : nat)
  (cmodels : list (list SLF))
  (lvals : list SLF)
  (m : list (mem SLF))
  (p : parameters) :=
  let V := map (fun x => match x with sign n _ => n end) lvals in
  match listNodes with
  | nil => state _ _ (Leaf nil nil 0 nil lvals) lc m
  | h::tl =>
      let toExpand := proj_l h in
      match toExpand with
      | sign s A =>
          match A with
          | Atom _ => state _ _ (Leaf (explode listNodes) branch 0 nil lvals) nil m
          | ~ B => state _ _ (Neg_rule s B (explode listNodes) V lvals branch) nil m
          | B /\ C => state _ _ (Conj_rule s B C (explode listNodes) V lvals branch) nil m
          | B \/ C => state _ _ (Disj_rule s B C (explode listNodes) V lvals branch) nil m
          | B -> C => state _ _ (Impl_rule s B C (explode listNodes) V lvals branch) nil m
          end
      end
  end.

Definition Cn_Tableau_optimal
  (snapshot : btree SLF)
  (lc : list (check SLF))
  (listNodes : list (pair SLF (list SLF)))
  (branch : list SLF)
  (loop_counter1 : nat)
  (cmodels : list (list SLF))
  (lvals : list SLF)
  (m : list (mem SLF))
  (p : parameters) :=
  let V := map (fun x => match x with sign n _ => n end) lvals in
  match listNodes with
  | nil => state _ _ (Leaf nil branch 0 nil lvals) lc m
  | h::tl =>
      let toExpand := proj_l h in
      match toExpand with
      | sign s A =>
          match A with
          | Atom _ => state _ _ (Leaf (explode listNodes) branch 0 nil lvals) nil m
          | ~ B => derivedDriver s A (explode listNodes) lvals V branch
          | B /\ C => derivedDriver s A (explode listNodes) lvals V branch
          | B \/ C => state _ _ (Disj_rule s B C (explode listNodes) V lvals branch) nil m
          | B -> C => state _ _ (Impl_rule s B C (explode listNodes) V lvals branch) nil m
          end
      end
  end.

(* Closure conditions *)

Definition cond2 (A B : SLF) :=
  let t0n := 2 in
  let tkn := fun a => 2 <=? a in (* tkn is t0n, t1n, ... *)
  match A, B with
  | sign s1 P, sign s2 Q =>
      let f :=
        fun A B =>
          match B with
          | P /\ Q => eqb_lf A (selectContra P Q)
          | _ => false
          end
      in
      if Nat.eqb s1 t0n then
        if tkn s2 then
          if isContradiction Q then
            f P Q
          else
            false
        else
          false
      else
        false
  end.

Compute cond2 (sign 2 (~p0)) (sign 10 (~~p0 /\ ~p0)).

Compute (fun a => 1 <=? a) 123.

Definition cond3 (A B : SLF) :=
  let Tn := fun a => Nat.eqb a 1 in
  let tkn := fun a => 3 <=? a in (* tkn is t1n, t2n, ...  *)
  match A, B with
  | sign s1 P, sign s2 Q =>
      let f :=
        fun A B =>
          match B with
          | P /\ Q => eqb_lf (selectContra P Q) A 
          | _ => false
          end
      in
      if tkn s1 then
        if Tn s2 then
          if isContradiction Q then
            f P Q
          else
            false
        else
          false
      else
        false
  end.

Compute cond3 (sign 5 (~p0)) (sign 1 (~~p0 /\ ~p0)).

Definition cond4
  (A B : SLF)
  :=
  let tkn := fun a => 3 <=? a in (* tkn is t1n, t2n, ...  *)
  match A, B with
  | sign s1 P, sign s2 Q =>
      let Ln := fun a => andb (negb (Nat.eqb a (s1 - 1))) (3 <=? a) in
      let f :=
        fun A B =>
          match B with
          | ~ Q =>
              if isContradiction Q then
                match Q with
                | Q0 /\ Q1 => eqb_lf (selectContra Q0 Q1) A
                | _ => false
                end
              else false
          | _ => false
          end
      in
      if tkn s1 then
        if Ln s2 then
          f P Q
        else
          false
      else
        false
  end.

Compute cond4 (sign 5 (~~p0)) (sign 7 (~(~~(~p0) /\ (~~p0)))).

Definition contra
  (A B : SLF)
  :=
  match A, B with
  | sign L P, sign L' Q =>
      let condA := andb (eqb_lf P Q) (negb (Nat.eqb L L')) in
      (*let condB := orb (cond2 A B) (cond2 B A) in (* perhaps only (condX A B) also works *)
      let condC := orb (cond3 A B) (cond3 B A) in
      let condD := orb (cond4 A B) (cond4 B A) in*)
      let condB := cond2 A B in
      let condC := cond3 A B in
      let condD := cond4 A B in
      orb
        condA
        (orb
           condB
           (orb
              condC
              condD))
  end.
(*
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

Fixpoint lFBTC_aux1
  (t : btree SLF)
  (l : list nat)
  (lvals : list SLF)
  :=
  match t with
  | Leaf lN _ tag _ _ =>
      if isElementInList l tag Nat.eqb then
        if negb (Nat.eqb (List.length lN) 0) then
          closeBranch lvals
        else Leaf nil nil 1 nil lvals
      else Leaf lN nil tag nil lvals
  | Alpha N nT =>
      Alpha N (lFBTC_aux1 nT l lvals)
  | Beta nT1 nT2 =>
      Beta
        (lFBTC_aux1 nT1 l lvals)
        (lFBTC_aux1 nT2 l lvals)
  end.

Definition lFBTC
  (t : btree SLF)
  (cond : SLF -> SLF -> bool)
  (lvals : list SLF)
  :=
  let taggedT := tagLeafs t in
  let lClosed := lFBTC_aux2 taggedT cond in
  lFBTC_aux1 taggedT lClosed lvals.
 *)

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
          closeBranch lvals
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

Fixpoint makeInitialTree
  (listNodes lNcp : list (pair SLF (list SLF)))
  (lvals : list SLF)
  :=
  match listNodes with
  | nil => Leaf lNcp nil 0 nil lvals
  | h::tl =>
      match h with
      | Pair s _ => Alpha s (makeInitialTree tl lNcp lvals)
      end
  end.

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

Fixpoint howManyLeafsClean (t : btree SLF) :=
  match t with
  | Leaf lN _ _ _ _ =>
      if Nat.eqb (List.length lN) 0 then 1
      else 0
  | Alpha _ nT =>
      howManyLeafsClean nT
  | Beta nT1 nT2 =>
      (howManyLeafsClean nT1) +
        (howManyLeafsClean nT2)
  end.

Fixpoint makeCn_aux1 (l : list nat) :=
  match l with
  | nil => nil
  | h::tl =>
      (sign h (Atom "p0"))::(makeCn_aux1 tl)
  end.

Fixpoint makeCn_aux
  (t : btree SLF)
  (deepness : nat)
  (lvals : list SLF)
  :=
  match deepness with
  | O => t
  | S n =>
      let ntree := pop (make _ _ Cn_Tableau t 1) (Leaf nil nil 0 nil lvals) in
      let opt_tree := lFBTC ntree contra in
      (*if orb
           (closure opt_tree contra)
           (leafsClean opt_tree)
      then
        opt_tree
      else *)
      makeCn_aux opt_tree n lvals
  end.

Definition makeCn (A : LF) (deepness : nat) (V : list nat) :=
  let lvals := makeCn_aux1 V in
  let lN := [((sign 0 A); nil)] in
  let initialTree := makeInitialTree lN lN lvals in
  let result := makeCn_aux initialTree deepness lvals in
  result.

Fixpoint makeCn_optimal_aux
  (t : btree SLF)
  (deepness : nat)
  (lvals : list SLF)
  :=
  match deepness with
  | O => t
  | S n =>
      let ntree := pop (make _ _ Cn_Tableau_optimal t 1) (Leaf nil nil 0 nil nil) in
      let opt_tree := lFBTC ntree contra in
      if leafsClean opt_tree
      then
        opt_tree
      else
      makeCn_optimal_aux opt_tree n lvals
  end.

Definition makeCn_optimal (A : LF) (deepness : nat) (V : list nat) (t : nat) :=
  let lvals := makeCn_aux1 V in
  let lN := [((sign t A); nil)] in
  let initialTree := makeInitialTree lN lN lvals in
  let result := makeCn_optimal_aux initialTree deepness lvals in
  result.

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
Definition propag_consist_disj_4 :=
  ((cngen2 p0 4) /\ (cngen2 p1 4)) -> (cngen2 (p0 \/ p1) 4).
Definition propag_consist_impl_4 :=
  ((cngen2 p0 4) /\ (cngen2 p1 4)) -> (cngen2 (p0 -> p1) 4).

(* TODO : Change the returned type to Big Int (Z Lib) ! *)

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

(** TESTES . A partir de T2 . **)

(* T2 *)
(*
Definition T2_conj1 (b : bool) := if b then makeCn_optimal (propag_consist_conj_1) 100 [0;1;2;3] else Leaf nil nil 0 nil nil.
Definition T2_disj1 (b : bool) := if b then makeCn_optimal (propag_consist_disj_1) 100 [0;1;2;3] else Leaf nil nil 0 nil nil.
Definition T2_impl1 (b : bool) := if b then makeCn_optimal (propag_consist_impl_1) 100 [0;1;2;3] else Leaf nil nil 0 nil nil.

Definition T2_conj2 (b : bool) := if b then makeCn_optimal (propag_consist_conj_2) 100 [0;1;2;3] else Leaf nil nil 0 nil nil.
Definition T2_disj2 (b : bool) := if b then makeCn_optimal (propag_consist_disj_2) 100 [0;1;2;3] else Leaf nil nil 0 nil nil.
Definition T2_impl2 (b : bool) := if b then makeCn_optimal (propag_consist_impl_2) 100 [0;1;2;3] else Leaf nil nil 0 nil nil.

Definition T2_conj3 (b : bool) := if b then makeCn_optimal (propag_consist_conj_3) 100 [0;1;2;3] else Leaf nil nil 0 nil nil.
Definition T2_disj3 (b : bool) := if b then makeCn_optimal (propag_consist_disj_3) 100 [0;1;2;3] else Leaf nil nil 0 nil nil.
Definition T2_impl3 (b : bool) := if b then makeCn_optimal (propag_consist_impl_3) 100 [0;1;2;3] else Leaf nil nil 0 nil nil.

Definition T2_conj4 (b : bool) := if b then makeCn_optimal (propag_consist_conj_4) 100 [0;1;2;3] else Leaf nil nil 0 nil nil.
Definition T2_disj4 (b : bool) := if b then makeCn_optimal (propag_consist_disj_4) 100 [0;1;2;3] else Leaf nil nil 0 nil nil.
Definition T2_impl4 (b : bool) := if b then makeCn_optimal (propag_consist_impl_4) 100 [0;1;2;3] else Leaf nil nil 0 nil nil.

(* T3 *)

Definition T3_conj1 (b : bool) := if b then makeCn_optimal (propag_consist_conj_1) 100 [0;1;2;3;4] else Leaf nil nil 0 nil nil.
Definition T3_disj1 (b : bool) := if b then makeCn_optimal (propag_consist_disj_1) 100 [0;1;2;3;4] else Leaf nil nil 0 nil nil.
Definition T3_impl1 (b : bool) := if b then makeCn_optimal (propag_consist_impl_1) 100 [0;1;2;3;4] else Leaf nil nil 0 nil nil.

Definition T3_conj2 (b : bool) := if b then makeCn_optimal (propag_consist_conj_2) 100 [0;1;2;3;4] else Leaf nil nil 0 nil nil.
Definition T3_disj2 (b : bool) := if b then makeCn_optimal (propag_consist_disj_2) 100 [0;1;2;3;4] else Leaf nil nil 0 nil nil.
Definition T3_impl2 (b : bool) := if b then makeCn_optimal (propag_consist_impl_2) 100 [0;1;2;3;4] else Leaf nil nil 0 nil nil.

Definition T3_conj3 (b : bool) := if b then makeCn_optimal (propag_consist_conj_3) 100 [0;1;2;3;4] else Leaf nil nil 0 nil nil.
Definition T3_disj3 (b : bool) := if b then makeCn_optimal (propag_consist_disj_3) 100 [0;1;2;3;4] else Leaf nil nil 0 nil nil.
Definition T3_impl3 (b : bool) := if b then makeCn_optimal (propag_consist_impl_3) 100 [0;1;2;3;4] else Leaf nil nil 0 nil nil.

Definition T3_conj4 (b : bool) := if b then makeCn_optimal (propag_consist_conj_4) 100 [0;1;2;3;4] else Leaf nil nil 0 nil nil.
Definition T3_disj4 (b : bool) := if b then makeCn_optimal (propag_consist_disj_4) 100 [0;1;2;3;4] else Leaf nil nil 0 nil nil.
Definition T3_impl4 (b : bool) := if b then makeCn_optimal (propag_consist_impl_4) 100 [0;1;2;3;4] else Leaf nil nil 0 nil nil.

(* T4 *)

Definition T4_conj1 (b : bool) := if b then makeCn_optimal (propag_consist_conj_1) 100 [0;1;2;3;4;5] else Leaf nil nil 0 nil nil.
Definition T4_disj1 (b : bool) := if b then makeCn_optimal (propag_consist_disj_1) 100 [0;1;2;3;4;5] else Leaf nil nil 0 nil nil.
Definition T4_impl1 (b : bool) := if b then makeCn_optimal (propag_consist_impl_1) 100 [0;1;2;3;4;5] else Leaf nil nil 0 nil nil.

Definition T4_conj2 (b : bool) := if b then makeCn_optimal (propag_consist_conj_2) 100 [0;1;2;3;4;5] else Leaf nil nil 0 nil nil.
Definition T4_disj2 (b : bool) := if b then makeCn_optimal (propag_consist_disj_2) 100 [0;1;2;3;4;5] else Leaf nil nil 0 nil nil.
Definition T4_impl2 (b : bool) := if b then makeCn_optimal (propag_consist_impl_2) 100 [0;1;2;3;4] else Leaf nil nil 0 nil nil.

Definition T4_conj3 (b : bool) := if b then makeCn_optimal (propag_consist_conj_3) 100 [0;1;2;3;4;5] else Leaf nil nil 0 nil nil.
Definition T4_disj3 (b : bool) := if b then makeCn_optimal (propag_consist_disj_3) 100 [0;1;2;3;4;5] else Leaf nil nil 0 nil nil.
Definition T4_impl3 (b : bool) := if b then makeCn_optimal (propag_consist_impl_3) 100 [0;1;2;3;4;5] else Leaf nil nil 0 nil nil.

Definition T4_conj4 (b : bool) := if b then makeCn_optimal (propag_consist_conj_4) 100 [0;1;2;3;4;5] else Leaf nil nil 0 nil nil.
Definition T4_disj4 (b : bool) := if b then makeCn_optimal (propag_consist_disj_4) 100 [0;1;2;3;4;5] else Leaf nil nil 0 nil nil.
Definition T4_impl4 (b : bool) := if b then makeCn_optimal (propag_consist_impl_4) 100 [0;1;2;3;4;5] else Leaf nil nil 0 nil nil.

Check T4_conj4.
*)

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

Compute makeCn_optimal (~(p0 /\ p1)) 0 [0;1;2;3] 0.

Compute whichIndex (~ (Atom "p0" /\ Atom "p1")).

Compute whichIndex (cngen p0 1).

(* Extractions for Ocaml *)

Require Coq.extraction.Extraction.

Compute getLastNEls (reverseListOrder (upto 2)) 1.

Definition makeTruthValues (n : nat) :=
  let vec := [0;1]++getLastNEls (reverseListOrder (upto (n+1))) 1
  in vec.

Definition makeTableau (A : LF) (n : nat) (t : nat) :=
  let tv := makeTruthValues n in
  makeCn_optimal A 1 tv t.

Require Coq.extraction.ExtrOcamlString.

(*Extraction makeTableau.*)

(*Recursive Extraction T2_conj1 T2_disj1 T2_impl1 T2_conj2 T2_disj2 T2_impl2 T2_conj3 T2_disj3 T2_impl3 T2_conj4 T2_disj4 T2_impl4 T3_conj1 T3_disj1 T3_impl1 T3_conj2 T3_disj2 T3_impl2 T3_conj3 T3_disj3 T3_impl3 T3_conj4 T3_disj4 T3_impl4 T4_conj1 T4_disj1 T4_impl1 T4_conj2 T4_disj2 T4_impl2 T4_conj3 T4_disj3 T4_impl3 T4_conj4 T4_disj4 T4_impl4 branchesCount matrixSizeCount decideClosure.*)

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Recursive Extraction branchesCount matrixSizeCount decideClosure getFirstNEls getLastNEls makeCn_optimal makeCn.

Extraction p0.

Extraction whichIndex.
