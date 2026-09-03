Inductive nat : Type :=
  | zero : nat 
  | suc : nat -> nat.

Notation "f '$' a" := (f (a)) (at level 99).
Notation "x '<-' a ';;' b" := (let x := a in b) (at level 100, a at next level, right associativity).

Definition three :=
  two <- S $ S O ;;
  S two.