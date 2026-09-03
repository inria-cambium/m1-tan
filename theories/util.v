(* Utility functions that are term/ast-oblivious.
  term/ast-related utils go to Inductive.v. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Guarded Require Import Except.

Definition map2_i {A B C} (f : nat -> A -> B -> C) (a : list A) (b : list B) := 
  let map2' := fix rec a b n := 
     match a, b with
     | a0 :: a, b0 :: b => f n a0 b0 :: rec a b (S n)
     | _, _ => []
     end
  in map2' a b 0.
Fixpoint update_list {X} (l : list X) index x := 
  match l with 
  | [] => []
  | h :: l => 
      match index with 
      | 0 => x :: l
      | S index => h :: update_list l index x
      end
  end.

Section Except. 
  Context {Y : Type}. 
  Context {M : Type -> Type} {M_monad : Monad M}. 

  Definition list_iter {X} (f : X -> M unit) (l : list X) : M unit := 
    List.fold_left (fun (acc : M unit) x => _ <- acc;; f x) l (ret tt).
  Definition list_iteri {X} (f : nat -> X -> M unit) (l : list X) : M unit := 
    _ <- List.fold_left (fun (acc : M nat) x => i <- acc;; _ <- f i x;; ret (S i)) l (ret 0);;
    ret tt.
End Except.

Definition hd {X} (l : list X) : option X := 
  match l with 
  | [] => None
  | x :: l => Some x
  end.

Definition tl {X} (l : list X) : option(list X) := 
  match l with 
  | [] => None
  | x :: l => Some l
  end.

Definition is_none {X: Type} (a : option X) :=
  match a with
  | None => true
  | _ => false
  end.

Fixpoint tabulate {X : Type} (f : nat -> X) n :=
  match n with
  | 0 => []
  | S n => tabulate f n ++ [f n]
  end.

Definition repeat {X} (x : X) n := tabulate (fun _ => x) n.

Definition lookup {X Y: Type} (eqb : X -> X -> bool) (x : X) := fix rec (l : list (X * Y)) : option Y :=
  match l with
  | [] => None
  | (x', y') :: l => if eqb x x' then Some y' else rec l
  end.

Definition list_eqb {X : Type} (eqbX : X -> X -> bool) := fix rec l l' :=
  match l, l' with
  | nil, nil => true
  | cons x l0, cons x' l0' => eqbX x x' && rec l0 l0'
  | _, _ => false
  end.

Definition forallb2 {X : Type} (f : X -> X -> bool) := fix rec l l' :=
  match l, l' with
  | nil, nil => true
  | x :: l0, x' :: l0' => f x x' && rec l0 l0'
  | _, _ => false
  end.

Definition set_memb {X : Type} (eqbX : X -> X -> bool) := fix rec x s :=
  match s with
  | [] => false
  | x' :: s' =>  eqbX x x' || rec x s'
  end.

Definition map2 {X Y Z: Type} (f : X -> Y -> Z) := fix rec l1 l2 :=
  match l1, l2 with
  | [], [] => []
  | x :: l1, y :: l2 => f x y :: rec l1 l2
  | _, _ => []
  end.

Definition pair_eqb {X : Type} (eqb : X -> X -> bool) '(t, u) '(t', u') := eqb t t' && eqb u u'.

Definition option_lift {X Y Z} (f : X -> Y -> Z) (a : option X) (b : option Y) : option Z:=
  match a, b with
  | Some x, Some y => Some (f x y)
  | _, _ => None
  end.
Fixpoint list_lift_option {X} (l : list (option X)) : option (list X) :=
  match l with
  | [] => Some []
  | x :: l => option_lift (@cons X) x (list_lift_option l)
  end.

Definition fold_left_i {A B} (f : nat -> A -> B -> A) (l : list B) (init : A) : A :=
  let fix aux l i acc := match l with 
    | [] => acc
    | hd :: tl => aux tl (S i) (f i acc hd)
    end
  in aux l 0 init.

Definition map_i {A B} (f : nat -> A -> B) (l : list A) : list B :=
  let fix aux l i acc := match l with
    | [] => acc
    | hd :: tl => aux tl (S i) (f i hd :: acc)
    end
  in aux l 0 [].

Definition fold_left2_i {A X Y} (f : nat -> A -> X -> Y -> A) xs ys a :=
  fold_left_i (fun j a '(x, y) => f j a x y) (map2 pair xs ys) a.

Notation "f '$' a" := (f (a)) (at level 60, right associativity, only parsing).
