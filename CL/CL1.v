(*

Tableau for Classical Logic (CL) using only Nor operator, defining the others as notations.

*)

Add LoadPath "../" as Main.
Require Import Main.Poly.
Require Import List.
Require Import String.

(* Tipo das fórmulas nor *)

Inductive LF :=
| Atom : string -> LF
| Nor : LF -> LF -> LF.

Notation "@ A" := (Atom A) (at level 50).
Notation "A ↓ B"   := (Nor A B) (at level 100).
Notation "~ A"     := (Nor A A).
Notation "A /\ B"  := (Nor (Nor A A) (Nor B B)).
Notation "A \/ B"  := (Nor (Nor A B) (Nor A B)).
Notation "A -> B"  := (Nor (Nor (Nor A A) B) (Nor (Nor A A) B)).

Inductive node :=
| Empty
| Node (SL : SignedLF LF).

Definition NORTableau
  (snapshot : btree node)
  (lc : list (check node))
  (listNodes : list (pair node (list node)))
  (listR : list node)
  (loop_counter1 : nat)
  (cmodels : list (list node))
  (lvals : list node)
  (m : list (mem node))
  (p : parameters) :=
  match listNodes with
  | nil => state _ _ (Leaf nil listR loop_counter1 cmodels lvals) lc m
  | head::tl =>
      let h := proj_l head in
      match h with
      | Empty => state _ _ (Leaf nil listR loop_counter1 cmodels lvals) lc m
      | Node SF => 
          match SF with 
          | T b L =>
              match L with
              | Atom _ => state _ _ (Leaf (explode listNodes) listR loop_counter1 cmodels lvals) lc m
              | Nor P Q =>
                  if b then
                    let node1 := (Node (T false P)) in
                    let node2 := (Node (T false Q)) in
                    state _ _
                      (Alpha node1
                         ((Alpha node2
                             (Leaf
                                (((Pair node1 nil)::(Pair node2 nil)::
                                    (explode listNodes)))
                                   listR
                                   loop_counter1
                                   cmodels
                                   lvals))))
                         lc m
                  else
                    let node1 := (Node (T true P)) in
                    let node2 := (Node (T true Q)) in
                    state _ _
                      (Beta
                         (Alpha node1
                            ((Leaf
                                ((Pair node1 nil)::(explode listNodes))
                                listR loop_counter1 cmodels lvals
                         )))
                         (Alpha node2
                            ((Leaf
                                ((Pair node2 nil)::(explode listNodes))
                                listR loop_counter1 cmodels lvals
                      ))))
                      lc m
              end
          end
      end
  end.

Open Scope string_scope.

Definition P := @ "P".
Definition Q := @ "Q".
Definition R := @ "R".
Definition S := @ "S".
Definition X := @ "X".

Require Import List.
Import ListNotations.

Definition node1 := Node (T false (~~P -> P)).
Definition node2 := Node (T false (((P -> Q) -> P) -> P)).
Definition lN2 := [node1].
Definition lN := [(Pair node1 [node1])].

Fixpoint makeInitialTree
  (l : list node)
  (listNodes : list (pair node (list node))) :=
  match l with
  | nil => Leaf listNodes nil 0 nil nil
  | h::tl => Alpha h (makeInitialTree tl listNodes)
  end.

Compute (pop (make _ _ NORTableau (makeInitialTree lN2 lN) 10) (Leaf nil nil 0 nil nil)).
