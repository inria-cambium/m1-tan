From MetaRocq.Guarded Require Import plugin. 

From Stdlib Require Import List.
Import ListNotations.

(* for printing of rtrees *)
From MetaRocq Require Import Common.BasicAst Utils.bytestring.
From MetaRocq.Guarded Require Import MRRTree Inductives.

#[bypass_check(guard)]
Fixpoint boom (x: nat) : False := boom (id (pred x + O)).
MetaRocq Run (check_fix_ci false boom).

Print Nat.sub.
Fixpoint div (n m : nat) := 
  match n with 
  | 0 => 0
  | S n => if Nat.ltb (S n) (S m) then 0 else S (div (n - m) m)
  end.  
Compute (div 6 2).
(** NOTE: broken. at least the calls to ltb and sub are properly checked...*)
(** spent a lot of time debugging, but proper debugging is effectively impossible due to slowness *)
(** might also be because I uncommented some reduction stuff because of slowness? who knows *)

(* MetaRocq Run (check_fix_ci true div).  *)
 
(** * Some examples + explanations *)
(** The guardedness checker works by recursively traversing terms and checking recursive guardedness syntactically.
  The main data structure it works off are regular trees/recursive trees.
  These are computed for every inductive type by the Rocq kernel's positivity checker. 
  Essentially, they capture the recursive structure of inductive types. 
  (more precisely, they describe all "well-founded paths", i.e. all paths of how
  an inhabitant of the inductive type can be constructed -- the positivity checker
  makes sure that there are no infinite "unguarded" paths)
*)

(** Example : lists *)
MetaRocq Run (check_inductive (Some "list_tree") list). 

MetaRocq Run (check_inductive (Some "vec_tree") Vector.t). 
MetaRocq Run (check_inductive (Some "fin_tree") Fin.t). 
(** 

Inductive list (X : Type) :=
| nil : list X
| cons : X -> list X -> list X. 

corresponds to
<<
                Rec 0 
                 | 
              (* list *)
          Node (Mrec list_ind)
        /                           \
    (* nil *)                     (* cons *)
    Node Norec                   Node Norec
                            /             \
                        (* x : X *)   (*l : list X *)
                        Node Norec    Param 0 0
  >>

A recursive tree always contains the trees for a whole mutual inductive block
(to account for recursive occurrences). The top-level node is a [Rec n], having
children for each of the mutually defined types, and describing the recursive
structure for the [n]-th type (starting at 0) of this block.

For lists, there is exactly one mutually inductive block.

Each of the node for the mutually defined types is annotated with the name of
the inductive and has children for each of the constructors. The nodes for the
constructors are not annotated with anything useful, the Norec does not mean
anything.

Each of the nodes for the constructors has children for each of the
non-parametric arguments. The [nil] constructor obviously has no children. The
[cons] constructor has two children.

The nodes for the arguments are [Norec] if their type does not involve one of
the mutually defined types. They are [Param i j] for recursive occurrences of
types. The index [i] refers to the number of [Rec]s up in the tree this refers
to (in de Bruijn style). (this can only be non-zero with nested inductives) The
index [j] refers to the index of the inductive type in the corresponding block
of mutual inductives. *)

(* clearly not strictly positive *)
#[bypass_check(positivity)]
Inductive bad1 : Set := bad1C : (bad1 -> bad1) -> bad1.
MetaRocq Run (check_inductive (Some "bad1_tree") bad1).
Fixpoint f (b : bad1) : False := match b with | bad1C fbad => f (fbad b) end.
MetaRocq Run (check_fix f).

(* test mutual *)
(* Unset Positivity Checking. *)
Inductive A : Set := A1 : B -> B -> A
with B : Set := B1 : A -> B
with C : Set := C1 : C -> C.
MetaRocq Run (check_inductive (Some "B_tree") B).
(* Print B_tree. *)

(** Nested inductives need special attention: to correctly handle matches (and subterms) on elements of a nested inductive type we are doing recursion over, the inner inductive type's parameters need to be properly instantiated with the outer inductive type. This is in particular the case for the recursive arguments tree. *)
(** Example: rose trees *)
   Inductive rtree (X : Type) := rnode (l : list (rtree X)).
(* When we check a fixpoint which is structural over [r : rtree X] and (after matching) [r] ≃ [rnode l], 
    we want to be able to do recursive calls with elements of [l]. 
   In order to obtain this subterm information when matching on [l], the recargs tree for the [list] type is instantiated with [rtree] beforehand. 
 *)
(*
<<
                Rec 0 
                 | 
            Node (Mrec list_ind)
        /                           \
    Node Norec                   Node Norec
                                /             \
                            Node Norec    Param 0 0
  >>

  is turned into

<<
                Rec 0 
                 | 
            Node (Imbr list_ind)
        /                           \
    Node Norec                   Node Norec
                                /             \
                          (* r : rtree *)     (* l : list rtree *)
                            Param 1 0      Param 0 0

  >>
  where the Param 1 0 references the node for [rtree] on the outside (we have to skip over the [Rec] for the inner list type).
  The full tree for [rtree] is then:

<<
              Rec 0
                |
        Node (Mrec rtree_ind)
                | 
            Node Norec
                | 
  [the instantiated tree for list] 
  >>
    
*)
MetaRocq Run (check_inductive (Some "rtree_tree") rtree). 
(* Print rtree_tree.  *)


(** When matching on a (loose) subterm of the recursive argument of a fixpoint, we can look in the recursive tree whether a
  particular binder introduced by a match branch is a subterm. *)

(** There are many more complicated behaviours in relation to matches: *)
(** - Matches can be subterms if all branches are subterms. 
    However, this is restricted for dependent matches, depending on the return-type function/match predicate.*)
Fail Fixpoint abc (n : nat) := 
  match n with 
  | 0 => 0
  | S n => abc (match n with | 0 => n | S n => S n end)
  end.

#[bypass_check(guard)]
Fixpoint abc_bad (n : nat) := 
  match n with 
  | 0 => 0
  | S n => abc_bad (match n with | 0 => n | S n => S n end)
  end.
MetaRocq Run (check_fix_ci false abc_bad). 

Fixpoint abc (n : nat) := 
  match n with 
  | 0 => 0
  | S n => abc (match n with | 0 => n | S n' => n end)
  end.
MetaRocq Run (check_fix_ci true abc). 

(** - If matches are applied to some arguments, we "virtually" apply those arguments to the branches (technically, the checker maintains a stack of such virtual arguments). 
    
    The subterm information of these which is allowed to flow into branches of the match is restricted, too, for dependent matches. *)


(** If we encounter nested fixpoints and apply this nested fixpoint to a subterm of the outer fixpoint (at the position of the recursive argument), we may assume in the body of the inner fixpoint that the recursive argument is a subterm of the outer fixpoint. 
  In this way, we can make recursive calls to the outer fixpoint in the inner fixpoint (see the rosetree example below). 
*)

(** Notably, the guardedness checker reduces at MANY intermediate points: *)
#[bypass_check(guard)]
Fixpoint haha_this_is_ridiculous (n : nat) :=
  let _ := haha_this_is_ridiculous n in 0. 
MetaRocq Run (check_fix_ci false haha_this_is_ridiculous). 

(** For more details, we refer to the comments in the implementation. *)


(** * Some tests *)

(* to check broken fixpoints *)
#[bypass_check(guard)]
Definition broken_app  {A : Type} := fix broken_app (l m : list A) {struct l} := 
  match l with
  | [] => m
  | a :: l' => broken_app l m
  end.

(*MetaRocq Run (check_fix broken_app ). *)
(* NOTE: as we only unfold constants at the very top, we need to remove maximally inserted implicits (as the lead to an implicit app, thus preventing broken_app from being unfolded*)
MetaRocq Run (check_fix_ci false (@broken_app)). 


Fixpoint weird_length {X} (l :list X) {struct l} := 
  match l with
  | nil => 0
  | cons x l' => 
      match l with 
      | nil => 1
      | cons y l'' => S (S (weird_length l''))
      end
  end.
MetaRocq Run (check_fix_ci true (@weird_length)). 

MetaRocq Run (check_fix_ci true app). 
MetaRocq Run (check_fix_ci true rev).
MetaRocq Run (check_fix_ci true (@Nat.div)).




(* some attempt at coming up with mutual inductives *)
Inductive even : nat -> Type := 
  | even0 : even 0
  | evenS n : odd n -> even (S n)
  | evenSS n : even n -> even (S (S n))
with odd : nat -> Type := 
  | oddS n : even n -> odd (S n).

Fixpoint count_cons_even n (e : even n) : nat := 
  match e with 
  | even0 => 1
  | evenS n' o => 1 + count_cons_odd n' o 
  | evenSS n e => 1 + count_cons_even n e
  end
with count_cons_odd n (o : odd n) : nat := 
  match o with 
  | oddS n e => 1 + count_cons_even n e
  end.

(* MetaRocq Run (check_fix_ci true count_cons_odd).  *)
(* MetaRocq Run (check_fix_ci true count_cons_even).  *)



(** Rosetrees *)
Definition sumn (l : list nat) := List.fold_left (fun a b => a + b) l 0. 
MetaRocq Run (check_fix_ci true sumn). 
 
Fixpoint rtree_size {X} (t : rtree X) := 
  match t with
  | rnode l => rnode X ((fix map (l : list (rtree X)) : list (rtree X) := match l with
                                                        | [] => []
                                                         | a :: t => rtree_size a :: map t
                                                                      end) l)
  end.
MetaRocq Run (check_inductive None rtree). 
(* MetaRocq Run (check_fix_ci true (@rtree_size)). *)

Inductive otree := onode (l : option otree).

Fixpoint otree_id (t : otree) :=
  match t with
  | onode l => match l with
               | Some x => onode (Some (otree_id x))
               | None => onode None
               end
  end.


(* I feel a little bad about lying to Rocq about the structural argument, but whatever *)
#[bypass_check(guard)]
Fixpoint rtree_size_broken {X} (t : rtree X) {struct t} := 
  match t with
  | rnode l => sumn (map (fun _ => rtree_size_broken t) l)
  end.
MetaRocq Run (check_fix_ci false (@rtree_size_broken)). 

Fixpoint test (l : list nat) := 
  match l with
  | [] => 0
  | n :: l => sumn l +  test l
  end.
MetaRocq Run (check_fix_ci true test). 


Module wo.
  Axiom p: nat -> Prop.
  Axiom p_dec: forall n, (p n) + ~(p n).

  Inductive T (n: nat) : Prop := C (phi: ~p n -> T (S n)).

  Definition W' : forall n, T n -> { k | p k } :=
    fix F n (a : T n) := 
      let (Φ) := a in 
      match p_dec n with 
      | inl H => exist p n H
      | inr H => F (S n) (Φ H)
      end.

MetaRocq Run (check_fix_ci true W').
End wo.




(** Vectors *)
Set Implicit Arguments.
Set Asymmetric Patterns.
From Stdlib.Vectors Require Vector.

(** Taken from  https://github.com/rocq/rocq/issues/4320 *)

Unset Guard Checking.
Section ilist.

(* Lists of elements whose types depend on an indexing set (CPDT's hlists).
These lists are a convenient way to implement finite maps
whose elements depend on their keys. The data structures used
by our ADT notations uses these to implement notation-friendly
method lookups. *)

Import Stdlib.Vectors.VectorDef.VectorNotations.

Context {A : Type}. (* The indexing type. *)
Context {B : A -> Type}. (* The type of indexed elements. *)

Fixpoint ilist {n} (l : Vector.t A n) : Type :=
match l with
| [] => unit
| a :: l => (B a) * (ilist l)
end.

MetaRocq Run (check_fix_ci true (@ilist)).

Definition icons (a : A) {n} {l : Vector.t A n} (b : B a) (il : ilist l) : ilist (a :: l) := pair b il.

Definition ilist_hd : forall {n} {As : Vector.t A n} (il : ilist As),
match As return ilist As -> Type with
| a :: As' => fun il => B a
| [] => fun _ => unit
end il.
intros. destruct As. exact tt. cbn in il. apply il.
Defined.

Definition ilist_tl : forall {n} {As : Vector.t A n} (il : ilist As),
match As return ilist As -> Type with
| a :: As' => fun il => ilist As'
| [] => fun _ => unit
end il.
intros. destruct As. exact tt. cbn in il. apply il.
Defined.

Definition ith_body 
    (ith : forall {m : nat} {As : Vector.t A m} (il : ilist As) (n : Fin.t m), B (Vector.nth As n))
    {m : nat}
    {As : Vector.t A m}
    (il : ilist As)
    (n : Fin.t m)
  : B (Vector.nth As n)
:= Eval cbv beta iota zeta delta [Vector.caseS] in
  match n in Fin.t m return forall (As : Vector.t A m), ilist As -> B (Vector.nth As n) with
  | Fin.F1 k =>
    fun As =>
      Vector.caseS (fun n As => ilist As -> B (Vector.nth As (@ Fin.F1 n)))
      (fun h n t => ilist_hd) As
  | Fin.FS k n' =>
    fun As =>
      Vector.caseS (fun n As => forall n', ilist As -> B (Vector.nth As (@ Fin.FS n n')))
        (fun h n t SMALLER il => @ ith _ _ (ilist_tl il) SMALLER)
        As n'
  end As il.

(* note that guard checking is turned off before the section *)
Fixpoint ith {m : nat} {As : Vector.t A m} (il : ilist As) (n : Fin.t m) {struct n} : B (Vector.nth As n) := 
  @ ith_body (@ ith) m As il n.

MetaRocq Run (check_fix_ci false (@ith)).

End ilist.
Set Guard Checking.

(** * Positivity examples *)

MetaRocq Run (check_inductive None even).

#[bypass_check(positivity)]
Inductive nonpos := 
  | nonposC (f : nonpos -> nat) : nonpos. 

MetaRocq Run (check_inductive None nonpos).


(*Inductive AczelPP (X : Type) := *)
  (*| node (f : X -> list (AczelPP X)). *)


(** Trying to find out what wf_paths intersection does *)
MetaRocq Run (check_inductive (Some "odd_tree") odd).
MetaRocq Run (check_inductive (Some "even_tree") even).

(* identity *)
(*Compute (inter_wf_paths odd_tree odd_tree).*)
(* tree of empty inductive type: Rec 0 [Node Norec []] *)
(*Compute (inter_wf_paths odd_tree even_tree).*)

(* empty inductive type tree *)
(*Compute (inter_wf_paths list_tree rtree_tree).*)
(* the list part of the rtree tree *)
Definition listnested := 
      Rec 0
           [Node
              (Mrec (RecArgInd (* TODO: originally Imbr *)
                 {|
                 inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"],
                                   "list");
                 inductive_ind := 0 |}))
              [mk_node Norec []; mk_node Norec [Param 1 0; Param 0 0]]].
(* None *)
(*Compute (inter_wf_paths list_tree listnested).*)

Definition nonrec_rtree := 
Rec 0
  [Node
     (Mrec (RecArgInd (* TODO: originally Imbr *)
        {|
        inductive_mind := (MPfile ["examples"; "Guarded"; "MetaRocq"],
                          "rtree");
        inductive_ind := 0 |}))
     [mk_node Norec
        [mk_node Norec []]]].
(* nonrec_rtree, so it removes the nested occurrence of list *)
(* Compute (inter_wf_paths nonrec_rtree rtree_tree). *)


(* * ** Some examples that were incorrectly recognized as guarded until 2013 due to commutative cuts handling. *)

(* https://sympa.inria.fr/sympa/arc/rocq-club/2013-12/msg00119.html *)
(* Set Guard Checking.

Require Import ClassicalFacts. *)

(* Section func_unit_discr.

Hypothesis Heq : (False -> False) = True. *)

(* Fixpoint contradiction (u : True) : False :=
match Heq in (eq _ T) return T with
| eq_refl => fun f:False => match f with end
end. *)

(*End func_unit_discr.*)

(*Lemma foo : provable_prop_extensionality -> False.*)
(*Proof.*)
(*intro; apply contradiction.*)
(*apply H.*)
(*trivial.*)
(*trivial.*)
(*Qed.*)


(* 
(* https://sympa.inria.fr/sympa/arc/rocq-club/2013-12/msg00155.html *)
Require Import ClassicalFacts.

Inductive True1 : Prop := I1 : True1
with True2 : Prop := I2 : True1 -> True2.

Section func_unit_discr.

Hypothesis Heq : True1 = True2.

Fixpoint contradiction (u : True2) : False :=
contradiction (
match u with
| I2 Tr =>
match Heq in (_ = T) return T with
| eq_refl => Tr
end
end).

End func_unit_discr.

Lemma foo : provable_prop_extensionality -> False.
Proof.
intro; apply contradiction.
etransitivity. apply H. constructor.
symmetry. apply H. constructor. constructor.
constructor. constructor.
Qed. *)


From Stdlib.Vectors Require Import Vector.

#[bypass_check(guard)]
Fixpoint map2 {A B C : Type} (f : A -> B -> C) (n : nat) (v1 : t A n) (v2 : t B n)
  {struct v1}
  : t C n :=
  match v1 with
  | @nil _ => fun _ => nil C
  | @cons _ a n' v1' => fun v2 : t B (S n') =>
                         match v2 with
                         | @cons _ b n'' v2' => fun v1'' : Vector.t A n'' => cons _ (f a b) _ (map2 f v1'' v2')
                         end v1'
  end v2.

MetaRocq Run (check_fix_ci false (@map2)).
