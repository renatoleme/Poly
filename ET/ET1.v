Add LoadPath "../" as Main.
Require Import Main.Poly.
Require Import List.
Require Import String.
Require Import Coq.Arith.EqNat.
Require Import Coq.Init.Nat.

Import ListNotations.

(*

******* ECUMENICAL PROPOSITIONAL TABLEAU *********

Implemented with Poly.v.

Se um argumento [H1;...Hn; C] é valido, entao o tablô

[T H1 0; ....; T Hn 0; F C 0; 0 R 0] FECHA

Senão,

um contra-modelo é apresentado.

 *)

Inductive LF :=
| Atom   : string -> LF
| Neg  : LF -> LF
| And  : LF -> LF -> LF
| iOr  : LF -> LF -> LF
| cOr  : LF -> LF -> LF
| iImp : LF -> LF -> LF
| cImp : LF -> LF -> LF.

Inductive node :=
| Node (SL : SignedLF LF) (n : nat)
| R : nat -> nat -> node.

Definition getMinFromNode (n : node) :=
  match n with
  | Node _ k => k
  | R k j => k
  end.

Definition getMaxFromNode (n : node) :=
  match n with
  | Node _ k => k
  | R k j => j
  end.

Notation "@ A" := (Atom A) (at level 50).
Notation "~ A" := (Neg A).
Notation "A /\ B" := (And A B).
Notation "A \/i B" := (iOr A B) (at level 100).
Notation "A \/c B" := (cOr A B) (at level 100).
Notation "A ->i B" := (iImp A B) (at level 90).
Notation "A ->c B" := (cImp A B) (at level 90).

Notation "A <->i B" := (And (iImp A B) (iImp B A)) (at level 90).
Notation "A <->c B" := (And (cImp A B) (cImp B A)) (at level 90).

Open Scope string_scope.

Definition P := @ "P".
Definition Q := @ "Q".
Definition S := @ "S".
Definition X := @ "X".

Close Scope string_scope.

Fixpoint eqb_LF (A : LF) (B : LF) :=
  match A with
  | @ p =>
      match B with
      | @ q => String.eqb p q
      | _ => false
      end
  | ~ p =>
      match B with
      | ~ q => eqb_LF p q
      | _ => false
      end
  | p /\ q =>
      match B with
      | r /\ t => andb (eqb_LF p r) (eqb_LF q t)
      | _ => false
      end
  | p \/i q =>
      match B with
      | r \/i t => andb (eqb_LF p r) (eqb_LF q t)
      | _ => false
      end
  | p \/c q =>
      match B with
      | r \/c t => andb (eqb_LF p r) (eqb_LF q t)
      | _ => false
      end
  | p ->i q =>
      match B with
      | r ->i t => andb (eqb_LF p r) (eqb_LF q t)
      | _ => false
      end
  | p ->c q =>
      match B with
      | r ->c t => andb (eqb_LF p r) (eqb_LF q t)
      | _ => false
      end
  end.

Definition eqb_node_R (A : node) (B : node) :=
  match A with
  | R k j =>
      match B with
      | R k1 j1 => if andb (beq_nat k k1) (beq_nat j j1) then true
                   else false
      | _ => false
      end
  | _ => false        
  end.

Definition eqb_node (A : node) (B : node) :=
  match A with
  | Node S1 k1 =>
      match B with
      | Node S2 k2 =>
          if (Nat.eqb k1 k2) then eqb_SignedLF S1 S2 eqb_LF
          else false
      | _ => false
      end
  | _ => eqb_node_R A B        
  end.


Fixpoint checkIfNodeIsInList (A : node) (l : list node) :=
  match l with
  | nil => false
  | h::tl => orb (eqb_node A h) (checkIfNodeIsInList A tl)
  end.

Definition Reflexivity (n : nat) : node := R n n.

Fixpoint CloseRToTransitivity
  (n : node)
  (ln : list node)
  (cp_ln : list node) :=
  match ln with
  | nil => nil
  | h::tl => match h with
             | Node _ k => CloseRToTransitivity n tl cp_ln
             | R k j => if (beq_nat j (getMinFromNode n))
                        then if negb (checkIfNodeIsInList (R k (getMaxFromNode n)) cp_ln)
                             then ((R k (getMaxFromNode n)))
                                    ::(CloseRToTransitivity n tl cp_ln)
                             else (CloseRToTransitivity n tl cp_ln)
                        else (CloseRToTransitivity n tl cp_ln)
             end
  end.

Fixpoint RemoveAmbiguity (ln : list node) :=
  match ln with
  | nil => nil
  | h::tl => if checkIfNodeIsInList h tl then
               RemoveAmbiguity tl
             else h::(RemoveAmbiguity tl)
  end.

Definition Transitivity (n : node) (ln : list node) :=
  RemoveAmbiguity (CloseRToTransitivity n ln ln).

Fixpoint closeToTrans_aux (l cl : list node) :=
  match l with
  | nil => nil
  | h::tl =>
      let closeThis := Transitivity h cl in
      if negb (Nat.eqb (List.length closeThis) 0) then (Transitivity h cl)++(closeToTrans_aux tl cl)
      else (closeToTrans_aux tl cl)
  end.

Definition closeToTrans (l : list node) := closeToTrans_aux l l.

Fixpoint ListMemNodeToListNode (lm : list (mem node)) :=
  match lm with
  | nil => nil
  | h::tl => match h with
             | empty _ => (ListMemNodeToListNode tl)
             | record _ _ val => val::(ListMemNodeToListNode tl)
             end
  end.

Fixpoint ListNodeToMemNode (ln : list node) :=
  match ln with
  | nil => nil
  | h::tl => (record _ 0 h)::(ListNodeToMemNode tl)
  end.

Fixpoint filter {X:Type} (test: X -> bool) (l: list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Definition isNodeAtomic (n : node) :=
  match n with
  | Node Sf _ =>
      match Sf with
      | T b A =>
          match A with
          | @ p => true
          | _ => false
          end
      end
  | _ => false
  end.

Definition getOnlyAtom (ekm : list node) :=
  filter isNodeAtomic ekm.

Fixpoint makeInitialTree
  (l : list node)
  (listNodes : list (pair node (list node))) :=
  match l with
  | nil => Alpha (R 0 0) (Leaf listNodes ((R 0 0)::nil) 0 [((R 0 0)::nil)] nil)
  | h::tl => Alpha h (makeInitialTree tl listNodes)
  end.

Fixpoint isElementInList
  {X : Type}
  (el : X)
  (l : list X)
  (cmp : X -> X -> bool) :=
  match l with
  | nil => false
  | h::tl =>
      if cmp el h then true
      else isElementInList el tl cmp
  end.

Fixpoint listNodeToListPair (l : list node) : list (pair node (list node)) :=
  match l with
  | nil => nil
  | h::tl => (Pair h nil)::(listNodeToListPair tl)
  end.

Fixpoint listPairToListNode_L  (l : list (pair node (list node))) : list node :=
  match l with
  | nil => nil
  | h::tl => (proj_l h)::(listPairToListNode_L tl)
  end.

Fixpoint removeReflexivity (l : list node) :=
  match l with
  | nil => nil
  | h::tl =>
      match h with
      | R k j =>
          if (Nat.eqb k j) then removeReflexivity tl
          else h::(removeReflexivity tl)
      | _ => removeReflexivity tl
      end
  end.

Fixpoint getOnlyR (l : list node) :=
  match l with
  | nil => nil
  | h::tl =>
      match h with
      | R k j => (R k j)::(getOnlyR tl)
      | _ => getOnlyR tl
      end
  end.

Fixpoint getOnlyNode (l : list node) :=
  match l with
  | nil => nil
  | h::tl =>
      match h with
      | Node sf w => (Node sf w)::(getOnlyNode tl)
      | _ => getOnlyNode tl
      end
  end.

(* make list of nodes for recurrent rule *)
(* receive list of relations on branch and list of expansible nodes 
   and n the current world 
*)
Fixpoint findRelations
  (lR : list node)
  (cP : pair node (list node))
  (n : nat)
  : list node :=
  match lR with
  | nil => nil
  | h::tl => 
      match h with
      | Node _ _ => nil
      | R k j =>
        if (Nat.eqb n k) 
        then
          if isElementInList (R k j) (proj_r cP) eqb_node
          then
            findRelations tl cP n
          else
            ((R k j))::(findRelations tl cP n)
        else
          findRelations tl cP n
      end
  end.

(* make list of nodes for recurrent rule *)
(* receive list of relations on branch and list of expansible nodes 
   and n the current world 
*)
Fixpoint makeNodesRecRules
  (sfor : SignedLF LF)
  (relations : list node)
  : list (pair node (list node)) :=
  match relations with
  | nil => nil
  | h::tl => 
      match h with
      | Node _ _ => nil
      | R k j =>
          let newnode := Node sfor j in
          (Pair newnode nil)::(makeNodesRecRules sfor tl)
      end
  end.

Fixpoint makeNodesRecRules_C
  (sfor : SignedLF LF)
  (relations : list node)
  (w : nat)
  (listR : list node)
  : list (pair node (list node)) :=
  match relations with
  | nil => nil
  | h::tl => 
      match h with
      | Node _ _ => nil
      | R k j =>
          let newnode := Node sfor w in
          let transClosure := listNodeToListPair (Transitivity (R j w) listR) in
          ((Pair newnode nil)::((Pair (R j w) nil)::(Pair (R w w) nil)::nil))++
            (makeNodesRecRules_C sfor tl (w+1) listR)
      end
  end.

Fixpoint makeBranchFromNodeList
  (l listR : list node)
  (queue : list (pair node (list node)))
  (cmodels : list (list node))
  (lvals : list node)
  :=
  match l with
  | nil => Leaf queue listR 0 cmodels lvals
  | h::tl =>
      Alpha h (makeBranchFromNodeList tl listR queue cmodels lvals)
  end.

Fixpoint genR (l : list (list node)) (newr : node) : list (list node) :=
  match l with
  | nil => nil
  | h::tl =>
      match newr with
      | R k j =>
          if (checkIfNodeIsInList (R k k) h) then
            ((R k j)::(R j j)::h)::(genR tl newr)
          else
            genR tl newr
      | _ => genR tl newr
      end
  end.

Fixpoint genR_list (l : list (list node)) (lnodes : list node) :=
  match lnodes with
  | nil => l
  | h::tl =>
      let nextlist := genR l h in
      nextlist++(genR_list nextlist tl)
  end.

Definition SemanticEcumenicalTableau
  (snapshot : btree node)
  (lc : list (check node))
  (listNodes : list (pair node (list node)))
  (listR : list node)
  (loop_counter1 : nat)
  (cmodels : list (list node))
  (lvals : list node)
  (m : list (mem node))
  (p : parameters)
  : stt node node :=
  let memvalue :=
    getMaxFromNode (pop listR (R 0 0)) in
  match listNodes with
  | nil => state _ _ (Leaf nil listR loop_counter1 cmodels lvals) lc m
  | head::tl =>
      let h := proj_l head in
      match h with
      | R k j =>
          if (checkIfNodeIsInList (R k j) listR) then
            state _ _
              (Leaf (explode listNodes) (listR) 0 cmodels lvals)
              lc m
          else
            state _ _
              (Alpha (R k j) (Leaf (explode listNodes) ((R k j)::listR) 0 cmodels lvals))
              lc m
      | Node SF n =>
          match SF with
          | T t L =>
              let unaryRuleWithRec :=
                (fun branch =>
                   state _ _ branch lc m) in
              let binaryRuleWithRec :=
                (fun branchL branchR =>
                  state _ _
                     (Beta
                        branchL
                        branchR)
                     lc m) in
              let unaryNewWorldRule :=
                (fun node =>
                   (* let nrecord := record _ 0 (R n (memvalue+1)) in *)
                   let transClosure := listNodeToListPair (Transitivity (R n (memvalue+1))
                                          listR) in
                   state _ _
                     (Alpha (R n (memvalue+1))
                        (Alpha (Reflexivity (memvalue+1))
                           (Alpha node
                              (Leaf
                                 ((explode listNodes)++transClosure++((Pair node nil)::nil))
                                 ((R n (memvalue+1))::
                                    (Reflexivity (memvalue+1))::listR)
                                 0
                                 (cmodels++(genR cmodels (R n (memvalue+1))))
                                 (node::lvals)
                     ))))
                     lc
                     m) in
              let binaryNewWorldRule :=
                (fun node1 node2 =>
                   (* let nrecord := record _ 0 (R n (memvalue+1)) in *)
                   let transClosure := listNodeToListPair (Transitivity (R n (memvalue+1))
                                                             listR) in
                   state _ _
                     (Alpha (R n (memvalue+1))
                        (Alpha (Reflexivity (memvalue+1))
                           (Alpha node1
                              (Alpha node2
                                 (Leaf
                                    ((explode listNodes)++transClosure++((Pair node1 nil)::(Pair node2 nil)::nil))
                                    ((R n (memvalue+1))::
                                       (Reflexivity (memvalue+1))::listR)
                                    0
                                    (cmodels++(genR cmodels (R n (memvalue+1))))
                                    (node1::node2::lvals)
                     )))))
                     lc
                     m) in
              let alphaRule :=
                (fun node1 node2 =>
                   state _ _
                     (Alpha node1
                        ((Alpha node2
                            (Leaf
                               (((explode listNodes)++(Pair node1 nil)::(Pair node2 nil)::nil))
                               listR 0 cmodels (node1::lvals))))) lc m) in
              let betaRule :=
                (fun node1 node2 =>
                   state _ _
                     (Beta
                        (Alpha node1
                           ((Leaf (((explode listNodes)++(Pair node1 nil)::nil))
                               listR 0 cmodels (node1::lvals))))
                        (Alpha node2
                           ((Leaf (((explode listNodes)++(Pair node2 nil)::nil))
                               listR 0 cmodels (node2::lvals))))) lc m) in
              match L with
              | Atom _ =>
                  if t then (* Heredity rule *)
                    let relations := removeReflexivity (findRelations listR head n) in
                    if negb (Nat.eqb (List.length relations) 0) then
                      let newNodes := makeNodesRecRules (T true L) relations in
                      let newBranch := makeBranchFromNodeList
                                         (listPairToListNode_L newNodes)
                                         listR
                                         ((explode listNodes)
                                            ++((Pair h (relations++(proj_r head)))::nil))
                                         cmodels
                                         (lvals)
                      in
                      unaryRuleWithRec newBranch
                    else
                      state _ _
                        (Leaf ((explode listNodes)++(head::nil)) listR (loop_counter1+1) cmodels lvals) lc m
                  else
                    state _ _
                      (Leaf (explode listNodes) listR 0 cmodels lvals) lc m
              | l /\ r => 
                  let an1 := (Node (T true l) n) in
                  let an2 := (Node (T true r) n) in 
                  let bn1 := (Node (T false l) n) in
                  let bn2 := (Node (T false r) n) in
                  if t then alphaRule an1 an2
                  else betaRule bn1 bn2
              | l \/c r => 
                  let an1 := (Node (T true (Neg l)) (memvalue+1)) in
                  let an2 := (Node (T true (Neg r)) (memvalue+1)) in 
                  if t then
                    let relations := findRelations listR head n in
                    if negb (Nat.eqb (List.length relations) 0) then
                      let newNodesL := makeNodesRecRules_C (T true l) relations (memvalue+1) listR in
                      let newNodesR := makeNodesRecRules_C (T true r) relations (memvalue+1) listR in
                      let newRelationsL := ((getOnlyR (listPairToListNode_L newNodesL))++listR) in
                      let newRelationsR := ((getOnlyR (listPairToListNode_L newNodesR))++listR) in
                      let newBranchL := makeBranchFromNodeList
                                          ((listPairToListNode_L newNodesL)++(closeToTrans newRelationsL))
                                          ((newRelationsL)++(closeToTrans newRelationsL))
                                          ((explode listNodes)++newNodesL
                                             ++((Pair h (relations++(proj_r head)))::nil))
                                          (cmodels++(genR_list cmodels newRelationsL))
                                          ((listPairToListNode_L newNodesL)++lvals)
                      in
                      let newBranchR := makeBranchFromNodeList
                                          ((listPairToListNode_L newNodesR)++(closeToTrans newRelationsR))
                                          ((newRelationsR)++(closeToTrans newRelationsR))
                                          ((explode listNodes)++newNodesR
                                             ++((Pair h (relations++(proj_r head)))::nil))
                                          (cmodels++(genR_list cmodels newRelationsR))
                                          ((listPairToListNode_L newNodesR)++lvals)
                      in
                      binaryRuleWithRec newBranchL newBranchR
                    else state _ _
                           (Leaf ((explode listNodes)++(head::nil)) listR (loop_counter1+1) cmodels lvals) lc m
                  else binaryNewWorldRule an1 an2
              | l ->c r =>
                  let an1 := (Node (T true l) (memvalue+1)) in
                  let an2 := (Node (T true (Neg r)) (memvalue+1)) in
                  if t then
                    let relations := findRelations listR head n in
                    if negb (Nat.eqb (List.length relations) 0) then
                      let newNodesL := makeNodesRecRules (T false l) relations in
                      let newNodesR := makeNodesRecRules_C (T true r) relations (memvalue+1) listR in
                      let newRelationsL := ((getOnlyR (listPairToListNode_L newNodesL))++listR) in
                      let newRelationsR := ((getOnlyR (listPairToListNode_L newNodesR))++listR) in
                      let newBranchL := makeBranchFromNodeList
                                          (listPairToListNode_L newNodesL)
                                          listR
                                          ((explode listNodes)++newNodesL
                                             ++((Pair h (relations++(proj_r head)))::nil))
                                          cmodels
                                          ((listPairToListNode_L newNodesL)++lvals)
                      in
                      let newBranchR := makeBranchFromNodeList
                                          ((listPairToListNode_L newNodesR)++(closeToTrans newRelationsR))
                                          ((newRelationsR)++(closeToTrans newRelationsR))
                                          ((explode listNodes)++newNodesR
                                             ++((Pair h (relations++(proj_r head)))::nil))
                                          (cmodels++(genR_list cmodels newRelationsR))
                                          ((listPairToListNode_L newNodesR)++lvals)
                      in
                      binaryRuleWithRec newBranchL newBranchR
                    else state _ _
                           (Leaf ((explode listNodes)++(head::nil)) listR (loop_counter1+1) cmodels lvals) lc m
                  else binaryNewWorldRule an1 an2
              | l \/i r =>
                  let an1 := (Node (T false l) n) in
                  let an2 := (Node (T false r) n) in 
                  let bn1 := (Node (T true l) n) in
                  let bn2 := (Node (T true r) n) in
                  if t then betaRule bn1 bn2
                  else alphaRule an1 an2
              | l ->i r =>
                  let an1 := (Node (T true l) n) in
                  let an2 := (Node (T false r) n) in
                  if t then
                    let relations := findRelations listR head n in
                    if negb (Nat.eqb (List.length relations) 0) then
                      let newNodesL := makeNodesRecRules (T false l) relations in
                      let newNodesR := makeNodesRecRules (T true r) relations in
                      let newBranchL := makeBranchFromNodeList
                                          (listPairToListNode_L newNodesL)
                                          listR
                                          ((explode listNodes)++newNodesL
                                             ++((Pair h (relations++(proj_r head)))::nil))
                                          cmodels
                                          ((listPairToListNode_L newNodesL)++lvals)
                      in
                      let newBranchR := makeBranchFromNodeList
                                          (listPairToListNode_L newNodesR)
                                          listR
                                          ((explode listNodes)++newNodesR
                                             ++((Pair h (relations++(proj_r head)))::nil))
                                          cmodels
                                          ((listPairToListNode_L newNodesR)++lvals)
                      in
                      binaryRuleWithRec newBranchL newBranchR
                    else state _ _
                           (Leaf ((explode listNodes)++(head::nil)) listR (loop_counter1+1) cmodels lvals) lc m
                  else alphaRule an1 an2
              | ~ r => 
                  let an2 := (Node (T true r) (memvalue+1)) in 
                  if t then
                    let relations := findRelations listR head n in
                    if negb (Nat.eqb (List.length relations) 0) then
                      let newNodes := makeNodesRecRules (T false r) relations in
                      let newBranch := makeBranchFromNodeList
                                         (listPairToListNode_L newNodes)
                                         listR
                                         ((explode listNodes)++newNodes
                                            ++((Pair h (relations++(proj_r head)))::nil))
                                         cmodels
                                         ((listPairToListNode_L newNodes)++lvals)
                      in
                      unaryRuleWithRec newBranch
                    else state _ _
                           (Leaf ((explode listNodes)++(head::nil)) listR (loop_counter1+1) cmodels lvals) lc m
                  else unaryNewWorldRule an2
              end
          end
      end
  end.

Fixpoint tableau_aux (l : list LF) :=
  match l with
  | nil => nil
  | h::tl =>
      if (Nat.eqb (List.length tl) 0)
      then (Node (T false h) 0)::(tableau_aux tl)
      else (Node (T true h) 0)::(tableau_aux tl)
  end.

Definition createInitialTree (l : list LF) :=
  let listNodes := tableau_aux l in 
  (makeInitialTree listNodes
     (listNodeToListPair listNodes)).

Definition oneStepTableau (t : btree node) :=
  pop
    (make _ _ SemanticEcumenicalTableau t 1)
    (Leaf nil nil 0 nil nil).

Fixpoint reverseListOrder
  {X : Type}
  (l : list X)
  :=
  match l with
  | nil => nil
  | h::tl => (reverseListOrder tl)++(h::nil)
  end.

Fixpoint reverseThisList {X : Type} (l : list (list X)) :=
  match l with
  | nil => nil
  | h::tl => (reverseListOrder h)::(reverseThisList tl)
  end.

Definition contra (A B : node) :=
  match A with
  | Node SF1 w1 =>
      match B with
      | Node SF2 w2 =>
          if (Nat.eqb w1 w2) then
            match SF1 with
            | T b1 L1 =>
                match SF2 with
                | T b2 L2 =>
                    if xorb b1 b2 then
                      match L1 with
                      | @ p =>
                          match L2 with
                          | @ q => if eqb_LF (@ p) (@ q) then true
                                   else false
                          | _ => false
                          end
                      | _ => false
                      end
                    else false
                end
            end
          else false
      | _ => false
      end
  | _ => false
  end.
  
Fixpoint closure_aux2 (el : node) (l : list node) :=
  match l with
  | nil => false
  | h::tl =>
      if contra el h then true
      else closure_aux2 el tl
  end.

Fixpoint closure_aux3 (l cl : list node) :=
  match l with
  | nil => false
  | h::tl =>
      let closed := closure_aux2 h cl in
      if closed then true
      else closure_aux3 tl cl
  end.

Fixpoint closure_aux1 (l : list (list node)) :=
  match l with
  | nil => true
  | h::tl =>
      if (negb (Nat.eqb (List.length h) 0)) then
        andb (closure_aux3 h h) (closure_aux1 tl)
      else closure_aux1 tl
  end.

Compute flattenList [[1;2;3]].

Definition closure (t : btree node) :=
  let l := parse t nil in
  if Nat.eqb (List.length (flattenList l)) 0 then false 
  else closure_aux1 l.

Compute closure (Leaf [] [] 0 [] []).

Fixpoint treeIsInLoop (t1 : btree node) :=
  match t1 with
  | Leaf lN lR lc lc2 _ =>
      if (List.length lN) <=? lc then true
      else false
  | Alpha n nT =>
      treeIsInLoop nT
  | Beta tL tR =>
      andb
        (treeIsInLoop tL)
        (treeIsInLoop tR)
  end.

(* O Leaf possui informaçoes essenciais para a computacao da arvore e uteis para debug, 
mas acaba deixando o output final muito carregado.
Essa funcao remove essas informacoes para facilitar 
a visualizacao do resultado.*)
Fixpoint cleanLeaf
  {X : Type}
  (t : btree X)
  := 
  match t with
  | Leaf _ _ lc cmodels lvals => Leaf nil nil lc nil lvals
  | Alpha n nT =>
      Alpha n (cleanLeaf nT)
  | Beta t1 t2 =>
      Beta (cleanLeaf t1) (cleanLeaf t2)
  end.

(* Modelo extracter *)

Fixpoint checkValInW (A : LF) (w : nat) (l : list node) :=
  match l with
  | nil => false
  | h::tl =>
      match h with
      | Node sf k =>
          if Nat.eqb w k then
            match sf with
            | T b L =>
                if (eqb_LF A L) then b
                else checkValInW A w tl
            end
          else checkValInW A w tl
      | _ => checkValInW A w tl
      end
  end.

Fixpoint getAllAccessedWorld (l : list node) (w : nat) :=
  match l with
  | nil => nil
  | h::tl =>
      match h with
      | R k j =>
          if Nat.eqb w k then
            j::(getAllAccessedWorld tl w)
          else
            getAllAccessedWorld tl w
      | _ => getAllAccessedWorld tl w
      end
  end.

Fixpoint checkAll (A : LF) (l : list nat) (lN : list node) :=
  match l with
  | nil => true
  | h::tl =>
      andb
        (checkValInW A h lN)
        (checkAll A tl lN)
  end.

Fixpoint checkAllFalse (A : LF) (l : list nat) (lN : list node) :=
  match l with
  | nil => true
  | h::tl =>
      andb
        (negb (checkValInW A h lN))
        (negb (checkAllFalse A tl lN))
  end.

Fixpoint getAllTrueIn (A : LF) (l : list nat) (ekm: list node) :=
  match l with
  | nil => nil
  | h::tl =>
      if checkValInW A h ekm then
        h::(getAllTrueIn A tl ekm)
      else
        getAllTrueIn A tl ekm
  end.

Fixpoint forallb (l : list bool) :=
  match l with
  | nil => true
  | h::tl =>
      andb h (forallb tl)
  end.

Fixpoint forallnegb (l : list bool) :=
  match l with
  | nil => true
  | h::tl =>
      andb (negb h) (forallnegb tl)
  end.

Fixpoint valIsHeredit_aux (A : LF) (accW : list nat) (ekm : list node) :=
  match accW with
  | nil => true
  | h::tl =>
      andb
        (checkValInW A h ekm)
        (valIsHeredit_aux A tl ekm)
  end.
  
Fixpoint valIsHeredit (atomicNodes : list node) (ekm : list node) :=
  match atomicNodes with
  | nil => true
  | h::tl =>
      match h with
      | Node Sf w =>
          match Sf with
          | T b A =>
              if b then
                let accW := getAllAccessedWorld ekm w in
                andb
                  (valIsHeredit_aux A accW ekm)
                  (valIsHeredit tl ekm)
              else
                valIsHeredit tl ekm
          end
      | _ => valIsHeredit tl ekm
      end
  end.

Fixpoint closeToH_aux2 (A : LF) (accW : list nat) (ekm : list node) :=
  match accW with
  | nil => nil
  | h::tl => (Node (T true A) h)::(closeToH_aux2 A tl ekm)
  end.
  
Fixpoint closeToH_aux1 (atomics : list node) (ekm : list node) :=
  match atomics with
  | nil => nil
  | h::tl =>
      match h with
      | Node Sf w =>
          match Sf with
          | T b A =>
              if b then
                let accW := getAllAccessedWorld ekm w in
                let newNodes := closeToH_aux2 A accW ekm in
                newNodes++(closeToH_aux1 tl ekm)
              else
                (Node Sf w)::closeToH_aux1 tl ekm
          end
      | _ => closeToH_aux1 tl ekm
      end
  end.

Definition closeToH (ekm : list node) :=
  RemoveAmbiguity (closeToH_aux1 (getOnlyAtom ekm) ekm)++(getOnlyR ekm).

Fixpoint isReflexive (ekm ekmcp : list node) :=
  match ekm with
  | nil => true
  | h::tl =>
      match h with
      | R k j =>
          andb
            (andb
               (checkIfNodeIsInList (R j j) ekmcp)
               (checkIfNodeIsInList (R k k) ekmcp))
            (isReflexive tl ekmcp)
      | _ => isReflexive tl ekmcp
      end
  end.
        
Definition isModelEKM (ekm  : list node) :=
  let isRefle := isReflexive ekm ekm in
  let isTrans := Nat.eqb (List.length (closeToTrans (getOnlyR ekm))) 0 in
  let atomics := getOnlyAtom ekm in
  andb
    (andb
       isTrans
       isRefle)
    (valIsHeredit atomics ekm).

Fixpoint flattenList {X : Type} (l : list (list X)) : list X :=
  match l with
  | nil => nil
  | h::tl => h++(flattenList tl)
  end.


Fixpoint mergeModel (cmodels : list (list node)) (lvals : list node) :=
  match cmodels with
  | nil => nil
  | h::tl =>
      (closeToH (lvals++((closeToTrans h)++h)))::(mergeModel tl lvals)
  end.

Fixpoint getOnlyModels (t : btree node) :=
  match t with
  | Leaf _ _ _ cmodels lvals => (mergeModel (cmodels) ((closeToH (getOnlyAtom lvals))++(getOnlyAtom lvals)))
  | Alpha n nT => getOnlyModels nT
  | Beta nT1 nT2 =>
      (getOnlyModels nT1)++(getOnlyModels nT2)
  end.
    
Fixpoint Val (A : LF) (ekm : list node) (w : nat) :=
  let accW := getAllAccessedWorld ekm w in
  match A with
  | @ _ => checkValInW A w ekm
  | ~ p => forallnegb (map (Val p ekm) accW)
  | p /\ q => andb (Val p ekm w) (Val q ekm w)
  | p \/i q => orb (Val p ekm w) (Val q ekm w)
  | p ->i q =>
      forallb (
          map
            (fun k =>
               if (Val p ekm k) then
                 (Val q ekm k)
                else true)
            accW)
  | p ->c q =>
      forallb
        (
          map
            (fun k =>
               let accW2 := getAllAccessedWorld ekm k in
               orb
                 (negb (Val p ekm k))
                 (negb (forallnegb (map (Val q ekm) accW2))))
            accW
        )
  | p \/c q =>
      forallb
        (
          map
            (fun k =>
               let accW2 := getAllAccessedWorld ekm k in
               (negb
                  (forallnegb
                     (map
                        (fun m =>
                           orb
                             (Val p ekm m)
                             (Val q ekm m)
                        )
                        accW2
               )))
            )
            accW
        )
  end.

(* 

   Para uma lista ekm ser contra-modelo de A em um mundo w, é necessário: 

   (1) ekm ser um modelo genuino (reflexivo, transitivo e hereditario)  
   (2) A ser falso em w

*)
Definition isCounterModel (A : LF) (ekm : list node) (w : nat) :=
  let isValidModel := isModelEKM ekm in
  let val := Val A ekm w in
  andb isValidModel (negb val).

Definition isAModel (A : LF) (ekm : list node) (w : nat) :=
  let isValidModel := isModelEKM ekm in
  let val := Val A ekm w in
  andb isValidModel val.

Fixpoint search_aux3 (H : list LF) (ekm : list node) :=
  match H with
  | nil => true
  | h::tl =>
      if isAModel h ekm 0 then
        search_aux3 tl ekm
      else false
  end.

Fixpoint search_aux2 (H : list LF) (C : LF) (ekmList : list (list node)) :=
  match ekmList with
  | nil => nil
  | ekm::tl =>
      if isCounterModel C ekm 0 then
        if search_aux3 H ekm then ekm
        else search_aux2 H C tl
      else search_aux2 H C tl
  end.

Fixpoint getConclusion (lF : list LF) (d : LF) :=
  match lF with
  | nil => d
  | h::tl => getConclusion tl h
  end.

Fixpoint getHypothesis (lF : list LF) :=
  match lF with
  | nil => nil
  | h::tl =>
      if Nat.eqb (List.length tl) 0 then
        getHypothesis tl
      else
        h::(getHypothesis tl)
  end.

(*
Fixpoint search_aux (lF : list LF) (deepness : list nat) :=
  if Nat.eqb (List.length lF) 0 then []
  else
    match deepness with
    | nil => nil
    | h::tl =>
        let cmCandidates := (getOnlyModels (tableau lF h)) in
        let cm := search_aux2 (getHypothesis lF) (getConclusion lF P) cmCandidates in
        if negb (Nat.eqb (List.length cm) 0) then cm
        else search_aux lF tl
    end.

Definition search (lF : list LF) :=
  search_aux lF (reverseListOrder (upto 50)).*)

Fixpoint auto_tableau_aux
  (l : list LF)
  (t : btree node)
  (steps : list nat)
  (res : pair (btree node) (list node)) :=
  match steps with
  | nil => res
  | h::tl =>
      let tree := oneStepTableau t in
      if orb (closure tree) (treeIsInLoop tree) then Pair tree nil
      else
        let cmCandidates := getOnlyModels tree in
        let cm := search_aux2 (getHypothesis l) (getConclusion l P) cmCandidates in
        if Nat.eqb (List.length cm) 0 then
          auto_tableau_aux l tree tl (Pair tree nil)
        else
          Pair (Leaf nil nil 0 nil nil) cm
  end.

(* Output: bool X btree , onde bool é true iff btree is closed *)
Definition auto_tableau (l : list LF) (displayTree : bool) :=
  let initialTree := createInitialTree l in
  let response :=
    auto_tableau_aux
      l
      initialTree
      ((listOf1 1000))
      (Pair (Leaf nil nil 0 nil nil) nil) in
  if displayTree then
    Pair (closure (proj_l response)) response
  else
    Pair (closure (proj_l response)) (Pair (Leaf nil nil 0 nil nil) nil).

(*******)

Definition ec1 := (P ->i Q) ->i (P ->c Q).
Definition ec2_ida := (P /\ Q) ->i ~(~P \/c ~Q).
Definition ec2_volta := ~(~P \/c ~Q) ->i (P /\ Q). (* Não vale! *)
Definition ec3_ida := (P /\ Q) ->i ~(P ->c ~Q).
Definition ec3_volta := (~(P ->c ~Q)) ->i (P /\ Q). (* Não vale! *)
Definition ec4 := ~(~P /\ ~Q) <->i (P \/c Q).
Definition ec5 := ~(P /\ ~Q) <->i (P ->c Q).

(*********************)
(* Van Dalen, p. 15. *)
(**)
Definition p1 := P ->i (~ (~ P)).
Definition p2 := (~ P) ->i (~ (~ (~ P))).
Definition p3 := ~ ( P /\ (~ P)).
Definition p4 := (~ (~ (P \/i (~ P)))).
Definition p5 := (~ (P \/i (Q)) <->i ((~ P) /\ (~ ( Q)))).
Definition p6 := (P \/i (~ P)) ->i (~ (~ P) ->i P).
Definition p7 := (P ->i ( Q)) ->i (~ (P /\ (~ ( Q)))).
Definition p8 := (P ->i (~ ( Q))) <->i (~ (P /\ ( Q))). 
Definition p9 := ((~ (~ P)) /\ (~ (~ ( Q)))) <->i (~ (~ (P /\ ( Q)))). (* Pesado *)
Definition p10 := ((~ (~ P)) ->i (~ (~ ( Q)))) <->i (~ (~ (P ->i ( Q)))). (* Pesado *)
Definition p11 := ((~ (~ P)) ->i ( Q)) ->i ((~ ( Q)) ->i (~ P)).

Compute auto_tableau [ec5] false.
