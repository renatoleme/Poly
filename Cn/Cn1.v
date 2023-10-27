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
  :=
  match V with
  | nil => Leaf lN nil 0 nil nil
  | h::tl =>
      if Nat.eqb (List.length tl) 0
      then
        Alpha
          (sign h A)
          (Leaf (((sign h A); nil)::lN) nil 0 nil lvals)
      else
        Beta
          (Alpha
             (sign h A)
             (Leaf (((sign h A); nil)::lN) nil 0 nil lvals))
          (unaryComb A tl lN lvals)
  end.

Fixpoint binComb_aux
  (V : list (pair SLF SLF))
  (lN : list (pair SLF (list SLF)))
  (lvals : list SLF)
  :=
  match V with
  | nil => Leaf lN nil 0 nil nil
  | h::tl =>
      let slfA := proj_l h in
      let slfB := proj_r h in
      if Nat.eqb (List.length tl) 0 then
        Alpha slfA (Alpha slfB (Leaf ((slfA; nil)::(slfB; nil)::lN) nil 0 nil lvals))
      else
        Beta
          (Alpha slfA (Alpha slfB (Leaf ((slfA; nil)::(slfB; nil)::lN) nil 0 nil lvals)))
          (binComb_aux tl lN lvals)
  end.

Definition binComb
  (A B : LF)
  (V1 V2 : list nat)
  (lN : list (pair SLF (list SLF)))
  (lvals : list SLF)
  :=
  let comb := combineV1V2 A B V1 V2 in
  binComb_aux comb lN lvals.

(**)
(* Generalized rule for negation *)
(**)
Definition Neg_rule
  (s : nat)
  (A : LF)
  (lN : list (pair SLF (list SLF)))
  (V : list nat)
  (lvals : list SLF)
  : btree SLF :=
  let Fn := 0 in
  let Tn := 1 in
  let In := getLastNEls V 2 in
  match s with
  | 0 => (* Fn *)
      Alpha (sign Tn A) (Leaf (((sign Tn A); nil)::lN) nil 0 nil lvals)
  | 1 => (* Tn *)
      Beta
        (Alpha (sign Fn A) (Leaf (((sign Fn A); nil)::lN) nil 0 nil lvals))
        (unaryComb A In lN lvals)
  | _ => (* any inconsistent value *)
      unaryComb A In lN lvals
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
  : btree SLF :=
  let Fn := 0 in
  let Tn := 1 in
  let In := getLastNEls V 2 in
  let Dn := Tn::In in
  match s with
  | 0 => (* Fn *)
      Beta
        (Alpha (sign Fn A) (Leaf ((sign Fn A; nil)::lN) nil 0 nil lvals))
        (Alpha (sign Fn B) (Leaf ((sign Fn B; nil)::lN) nil 0 nil lvals))
  | 1 => (* Tn *)
      binComb A B Dn Dn lN lvals
  | _ => (* any inconsistent value *)
      Beta
        (binComb A B [Tn] In lN lvals)
        (Beta
           (binComb A B In In lN lvals)
           (binComb B A [Tn] In lN lvals))
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
              ((sign Fn A; nil)::(sign Fn B; nil)::lN) nil 0 nil lvals))
  | 1 => (* Tn *)
      Beta
        (unaryComb A Dn lN lvals)
        (unaryComb B Dn lN lvals)
  | _ => (* any inconsistent value *)
      Beta
        (unaryComb A In lN lvals)
        (unaryComb B In lN lvals)
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
  : btree SLF :=
  let Fn := 0 in
  let Tn := 1 in
  let In := getLastNEls V 2 in
  let Dn := Tn::In in
  match s with
  | 0 => (* Fn *)
      binComb B A [Fn] Dn lN lvals
  | 1 => (* Tn *)
      Beta
        (Alpha (sign Fn A) (Leaf ((sign Fn A; nil)::lN) nil 0 nil lvals))
        (unaryComb B Dn lN lvals)
  | _ => (* any inconsistent value *)
      Beta
        (binComb B A [Tn] In lN lvals)
        (unaryComb B In lN lvals)
  end.

(* DERIVED RULES *)

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
          | Atom _ => state _ _ (Leaf (explode listNodes) nil 0 nil lvals) nil m
          | ~ B => state _ _ (Neg_rule s B (explode listNodes) V lvals) nil m
          | B /\ C => state _ _ (Conj_rule s B C (explode listNodes) V lvals) nil m
          | B \/ C => state _ _ (Disj_rule s B C (explode listNodes) V lvals) nil m
          | B -> C => state _ _ (Impl_rule s B C (explode listNodes) V lvals) nil m
          end
      end
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

Fixpoint makeCn_aux1 (l : list nat) :=
  match l with
  | nil => nil
  | h::tl =>
      (sign h (Atom "p0"))::(makeCn_aux1 tl)
  end.

Fixpoint makeCn_aux
  (t : btree SLF)
  (deepness : list nat)
  (lvals : list SLF)
  :=
  match deepness with
  | nil => t
  | h::tl =>
      let ntree := pop (make _ _ Cn_Tableau t h) (Leaf nil nil 0 nil lvals) in
      makeCn_aux ntree tl lvals
  end.

Definition makeCn (A : LF) (deepness : nat) (V : list nat) :=
  let lvals := makeCn_aux1 V in
  let lN := [((sign 0 A); nil)] in
  let initialTree := makeInitialTree lN lN lvals in
  let deep := listOf1 deepness in
  let result := makeCn_aux initialTree deep lvals in
  result.

Compute makeCn (p0 -> p0) 10 [0;1;2;3;4;5].

(* Closure conditions *)

Definition isBola (A : LF) :=
  match A with
  | ~ B => isContradiction B
  | _ => false
  end.

Definition cond2 (A B : SLF) :=
  let t0n := 2 in
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
        if isContradiction Q then
          f P Q
        else
          false
      else
        false
  end.

Compute selectContra ((p0 -> p0)) (~(p0 -> p0)).

Compute (fun a => 1 <=? a) 123.

Definition cond3 (A B : SLF) :=
  let Tn := fun a => Nat.eqb a 1 in
  let tkn := fun a => 1 <=? a in
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

(* n stands for n in Cn *)
Definition cond4
  (A B : SLF)
  (n : nat)
  :=
  let Ln := fun a => negb (Nat.eqb a (n - 2)) in
  let tkn := fun a => 1 <=? a in
  match A, B with
  | sign s1 P, sign s2 Q =>
      if tkn s1 then
        if Ln s2 then isBola Q
        else
          false
      else
        false
  end.

(*
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
*)

(* Compute cond3 (sign 0 ((cngen2 p1 1) /\ (cngen2 p1 1))) (sign 0 (cngen2 p1 1)). *)

Definition contra
  (n : nat)
  (A B : SLF)
  :=
  match A, B with
  | sign L P, sign L' Q =>
      let condA := (negb (Nat.eqb L L')) in
      let condB := orb (cond2 A B) (cond2 B A) in
      let condC := orb (cond3 A B) (cond3 B A) in
      let condD := orb (cond4 A B n) (cond4 B A n) in
      if eqb_lf P Q then
        orb
          condA
          (orb
             condB
             (orb
                condC
                condD))
      else
        false
  end.

Compute closure (makeCn (p0 \/ ~ p0) 10 [0;1;2]) (contra 1).
