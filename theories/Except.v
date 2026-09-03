From MetaRocq.Utils Require Export monad_utils.
From MetaRocq.Utils Require Import MRUtils.
Export MonadNotation.
From Stdlib Require Import List String.

(** The usual exception monad based on [sum] with a parameterizable type of exceptions. *)

#[global]
Instance sum_monad {Y}: Monad (fun X => X + Y)%type :=
  {|
    ret := fun T t => inl t;
    bind := fun T U x f =>
      match x with
      | inl x => f x
      | inr y => inr y
      end
  |}.

Definition except {X Y: Type} (def : Y) (x : option X) : X + Y :=
  match x with
  | Some x => inl x
  | None => inr def
  end.
Definition raise {X Y : Type} (def : Y) : X + Y := inr def.


Definition excOn (Y : Type) (A : Type) := (A + Y)%type.

Section Except.
  Context {Y : Type}.
  Notation "'exc' A" := (excOn Y A) (at level 100).

  Class ExcUnwrap (Xl : Type -> Type) := exc_unwrap X : Xl (exc X) -> exc (Xl X).
  Arguments exc_unwrap {_ _ _}.

  Fixpoint list_unwrap {X : Type} (l : list (exc X)) : exc (list X) :=
    match l with
    | [] => ret []
    | x :: l =>
        x <- x ;;
        l <- list_unwrap l;;
        ret (x :: l)
    end.
  Global Instance: ExcUnwrap list := @list_unwrap.

  Definition assert (b : bool) (err : Y) : exc unit :=
    match b with
    | false => raise err
    | true => ret tt
    end.

  (** catch error and potentially emit another error *)
  Definition catchE {X} (a : exc X) (f : Y -> exc X) : exc X :=
    match a with
    | inl a => ret a
    | inr e => f e
    end.

  (** catch error and unwrap *)
  Definition catch {X} (a : exc X) (f : Y -> X) : X :=
    match a with
    | inl a => a
    | inr e => f e
    end.

  (** catch error and map *)
  Definition catchMap {X Z} (e : exc X) (f : Y -> Z) (g : X -> Z) :=
    match e with
    | inr e => f e
    | inl a => g a
    end.
End Except.
Arguments exc_unwrap {_ _ _ _}.

