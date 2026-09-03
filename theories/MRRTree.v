(* Type of regular trees:
   - Param denotes tree variables (like de Bruijn indices) ()
     the first int is the depth of the occurrence (YJ: in nested inductive types),
     and the second int is the index in the array of trees introduced at that depth
     (YJ: index in mutual inductive types).
     ==============================================================================    Warning: Param's indices both start at 0!!!
   - Node denotes the usual tree node, labelled with X (YJ: exclusively recargs
      in the current implementation. [children] contains [Param]s, one for each
      constructor.)

   - Rec(j,v1..vn) introduces an infinite tree. It denotes v(j+1) with
    parameters 0..n-1 replaced by Rec(0,v1..vn)..Rec(n-1,v1..vn) respectively.
    (YJ: The root of a tree is always Rec. Mutual branches get Rec0, Rec1, etc.
    The name of Rec comes from "Recursive Types".

    [children] is a list of the mutual inductive types in the block. Say A, B
    are in the same mutual recursive block, [wf_paths A] will result in
    [Rec 0 [A, B]] , and [wf_paths B] will result in [Rec 1 [A, B]].

    In other words, if no mutual inductives are allowed, [children] is always
    a singleton [Node].)
 *)
Inductive rtree (X : Type) :=
  | Param (tree_index : nat) (ind_index : nat)
  | Node (l : X) (children : list (rtree X))
  | Rec (index : nat) (children : list (rtree X)).

Arguments Param {_}.
Arguments Node {_}.
Arguments Rec {_}.

From Stdlib Require Import List.
Import ListNotations.
Require Import Stdlib.Lists.ListSet.
From Stdlib.Arith Require Import PeanoNat.
From MetaRocq.Utils Require Import MRUtils.
From MetaRocq.Guarded Require Import util.

(* TODO: proper exception handling with the except monad *)

Open Scope bool_scope.

Unset Guard Checking.
Section trees.
Context {X : Type}.
Implicit Types (t : rtree X).

Definition default_tree := Param (X:=X) 42 0. (* bogus tree used as default value*)

(* Building trees *)
(* array of "references" to mutual inductives of innermostly introduced (by Rec) inductive *)
Definition mk_rec_calls i := tabulate (fun j => Param (X := X) 0 j) i.

Definition mk_node label children := Node (X := X) label children.

(* The usual lift operation *)
(* lift unbound references >= depth to inductive types by n *)
Fixpoint lift_rtree_rec depth n (t : rtree X) :=
  match t with
  | Param i j =>
      (* lift all but the innermost depth types by n *)
      if i <? depth then t else Param (i+n) j
  | Node l children => Node l (map (lift_rtree_rec depth n) children)
  | Rec j defs => Rec j (map (lift_rtree_rec (S depth) n) defs)
  end.

(* lift all unbound references by n *)
Definition rtree_lift n t := if n =? 0 then t else lift_rtree_rec 0 n t.


(* The usual subst operation *)
(* substitute the depth -th unbound type by sub *)
Fixpoint subst_rtree_rec depth sub t :=
  match t with
  | Param i j as t =>
      if i <? depth then t
      else if i =? depth then  (* we refer to the inductive, depth, we want to substitute *)
        rtree_lift depth (Rec j sub) (* substitute in and lift references in sub by depth in order to avoid capture *)
      else Param (i-1) j
  | Node l children => Node l (map (subst_rtree_rec depth sub) children)
  | Rec j defs => Rec j (map (subst_rtree_rec (S depth) sub) defs)
  end.

(* substitute the innermost unbound by sub *)
Definition subst_rtree sub t := subst_rtree_rec 0 sub t.

(* To avoid looping, we must check that every body introduces a node
   or a parameter *)
Fixpoint expand t :=
  match t with
  | Rec j defs => expand (subst_rtree defs (nth j defs default_tree)) (* substitute by the j-th inductive type declared here *)
  | t => t
  end.
(* loops on some inputs:*)
(*Fail Timeout 1 Compute(expand (Rec 0 [(Param 0 0)])). *)


(* Given a vector of n bodies, builds the n mutual recursive trees.
   Recursive calls are made with parameters (0,0) to (0,n-1). We check
   the bodies actually build something by checking it is not
   directly one of the parameters of depth 0. Some care is taken to
   accept definitions like  rec X=Y and Y=f(X,Y) *)
(* TODO: well, does it actually check that?? expanding first does not seem to be smart, see example from before *)
Definition mk_rec defs :=
  let check := fix rec (histo : set nat) d {struct d} :=
    match expand d with
    | Param 0 j =>
        if set_mem (Nat.eq_dec) j histo
        then None (* invalid recursive call *)
        else
          match nth_error defs j with
          | Some e => rec (set_add (Nat.eq_dec) j histo) e
          | None => None (* invalid tree *)
          end
    | _ => Some tt
    end
  in
    if existsb is_none (mapi (fun i d => check (set_add (Nat.eq_dec) i (empty_set _)) d) defs)
    then None
    else Some (mapi (fun i d => Rec i defs) defs).

(* Tree destructors, expanding loops when necessary *)
Definition destruct_param {Y} t (f : nat -> nat -> Y) y :=
  match expand t with
  | Param i j => f i j
  | _ => y
  end.
Definition destruct_node {Y} t (f : X -> list (rtree X) -> Y) y :=
  match expand t with
  | Node l children => f l children
  | _ => y
  end.
(** Get the recarg the root node of [t] is annotated with. *)
Definition destruct_recarg t : option X :=
  destruct_node t (fun r _ => Some r) None. 

Definition is_node t :=
  match expand t with
  | Node _ _ => true
  | _ => false
  end.

Fixpoint map_rtree {Y} (f : X -> Y) t :=
  match t with
  | Param i j => Param i j
  | Node a children => Node (f a) (map (map_rtree f) children)
  | Rec j defs => Rec j (map (map_rtree f) defs)
  end.

(** Structural equality test, parametrized by an equality on elements *)
Definition rtree_eqb (eqbX : X -> X -> bool) := fix rec t t' :=
  match t, t' with
  | Param i j, Param i' j' => Nat.eqb i i' && Nat.eqb j j'
  | Node x c, Node x' c' => eqbX x x' && list_eqb rec c c'
  | Rec i a, Rec i' a' => Nat.eqb i i' && list_eqb rec a a'
  | _, _ => false
  end.

(** Equivalence test on expanded trees. It is parametrized by two
    equalities on elements:
    - [cmp] is used when checking for already seen trees
    - [cmp'] is used when comparing node labels. *)
Unset Guard Checking.
Definition rtree_equiv (cmp : X -> X -> bool) (cmp' : X -> X -> bool) :=
  let compare := fix rec histo t t' :=
    set_memb (pair_eqb (rtree_eqb cmp)) (t, t') histo ||
    match expand t, expand t' with
    | Node x v, Node x' v' =>
        cmp' x x' &&
        forallb2 (rec ((t, t') :: histo)) v v'
    | _, _ => false
    end
  in compare [].

(** The main comparison on rtree tries first structural equality, then the logical equivalence *)
Definition rtree_equal eqb t t' := rtree_eqb eqb t t' || rtree_equiv eqb eqb t t'.


(** Intersection of rtrees of same arity *)
(* n is the Rec nesting level *)
Definition rtree_inter' (eqb : X -> X -> bool) (interlbl : X -> X -> option X) def := fix rec n (histo : list ((rtree X * rtree X) * (nat * nat))) t t' {struct t} : option (rtree X):=
  match lookup (pair_eqb (rtree_eqb eqb)) (t, t') histo with
  | Some (i, j) => Some (Param (n - i - 1) j)
  | None =>
      match t, t' with
      | Param i j, Param i' j' =>
          if Nat.eqb i i' && Nat.eqb j j' then Some t else None
      | Node x a, Node x' a' =>
          match interlbl x x' with
          | None => Some (mk_node def [])  (* cannot intersect labels, make node with default labels *)
          | Some x'' =>
              option_map (Node x'') (list_lift_option (map2 (rec n histo) a a'))
          end
      | Rec i v, Rec i' v' =>
          (* if possible, we preserve the shape of input trees *)
          if Nat.eqb i i' && Nat.eqb (length v) (length v') then
            let histo := ((t, t'), (n, i)) :: histo in
              option_map (Rec i) (list_lift_option (map2 (rec (S n) histo) v v'))
          else
            (* otherwise, mutually recursive trees are transformed into nested trees *)
            (* recursive occurrences refer to the n-th Rec, 0-th subtree *)
            let histo := ((t, t'), (n, 0)) :: histo in
              option_map (fun s => Rec 0 [s]) (rec (S n) histo (expand t) (expand t'))
        | Rec _ _, _ => rec n histo (expand t) t'
        | _, Rec _ _ => rec n histo t (expand t')
        | _, _ => None
      end
  end.
Definition rtree_inter eqb interlbl def t t' := rtree_inter' eqb interlbl def 0 [] t t'.

(** Inclusion of rtrees. *)
Definition rtree_incl (eqb : X -> X -> bool) interlbl def t t' :=
  match (rtree_inter eqb interlbl def t t') with
  | Some t'' => rtree_equal eqb t t''
  | _ => false
  end.
End trees.
