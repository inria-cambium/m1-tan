From MetaRocq.Utils Require Import MRUtils bytestring.
From MetaRocq.Guarded Require Import Except util.
From Stdlib Require Import List.

From Stdlib Require Import BinNat.

Definition TIMEOUT_TIME := 3000%N.
Definition TIMEOUT := false.
Definition TRACE := false.

Notation "'fast_if' c 'then' u 'else' v" :=
  (ltac:(let x := eval cbv in c in
         match x with
         | true => exact u
         | false => exact v
         end
  )) (at level 200, u at level 100).

(* Check (fast_if true then 1 else 0). *)
Section trace.
  Context (max_steps : N).
  Context {Y : Type}.
  Context (timeout : Y).

  Definition trace_info := string.
  Open Scope type_scope.
  Definition TraceM A :=  bool (* timeout *)
                        * N (* number of steps on the clock *)
                        * list trace_info (* trace *)
                        * excOn Y A.
  
  Open Scope nat_scope.
  (* max steps handling is not totally accurate as we cannot pass the current number of steps into the function in bind, but anyways *)
  Instance trace_monad : Monad TraceM :=
    {|
      ret := fun T t => (false, 0%N, [], ret t);
      bind := fun T U (x : TraceM T) (f : T -> TraceM U) => 
        match x with
        | (b, s, t, e) =>
            (* if (andb TIMEOUT b) then (b, s, t, raise timeout) else
            match e with
            | inl e =>
                match f e return TraceM U with
                | (b', s', t', e') =>
                    let s'' := if TIMEOUT then 1 + s' + s else 0 in
                    let t'' := if TRACE then t' ++ t else [] in
                    let terminate := andb TIMEOUT $ orb b (Nat.leb max_steps s'') in
                    (terminate, s'', t'', e')
                end
            | inr err => (false, s, t, inr err)
            end *)
            fast_if TIMEOUT then
              if b then (b, s, t, raise timeout) else 
                match e with
                | inl e =>
                    match f e return TraceM U with
                    | (b', s', t', e') =>
                        let s'' := (fast_if TIMEOUT then 1 + s' + s else 0)%N in
                        let t'' := (fast_if TRACE then t' ++ t else @nil trace_info) in
                        let terminate := andb TIMEOUT $ orb b (N.leb max_steps s'') in
                        (terminate, s'', t'', e')
                    end
                | inr err => (false, s, t, inr err)
                end
            else
                match e with
                | inl e =>
                    match f e return TraceM U with
                    | (b', s', t', e') =>
                        let s'' := (fast_if TIMEOUT then 1 + s' + s else 0)%N in
                        let t'' := (fast_if TRACE then t' ++ t else @nil trace_info) in
                        let terminate := andb TIMEOUT $ orb b (N.leb max_steps s'') in
                        (terminate, s'', t'', e')
                    end
                | inr err => (false, s, t, inr err)
                end
      end
    |}.

  (* emit a trace element *)
  Definition trace (i : trace_info) : TraceM unit :=
    (false, 0, fast_if TRACE then [i] else @nil trace_info, ret tt)%N.
  Definition step : TraceM unit :=
    (false, fast_if TIMEOUT then 1 else 0, [], ret tt)%N.


  (** Lifting of the primitive operations on the except monad *)
  Notation "'trc' A" := (@TraceM A) (at level 100).

  Definition raise {X} (y : Y) : trc X := (false, 0, [], Except.raise y)%N.
  Definition except {X} (y: Y) (a : option X) : trc X := (false, 0, [], Except.except y a)%N.

  Class TrcUnwrap (Xl : Type -> Type) := trc_unwrap X : Xl (trc X) -> trc (Xl X).
  Arguments trc_unwrap {_ _ _}.

  Fixpoint list_unwrap {X : Type} (l : list (trc X)) : trc (list X) :=
    match l with
    | [] => ret []
    | x :: l =>
        x <- x;;
        l <- list_unwrap l;;
        ret (x :: l)
    end.
  Instance list_trc_unwrap: TrcUnwrap list := @list_unwrap.

  Definition lift_exc {X} (a : excOn Y X) : trc X := (false, 0, [], a)%N.
  Definition add_trace {Z} (steps : N) trace (a : trc Z) :=
    match a with
    | (b', steps', trace', z) =>
        (* if (andb TIMEOUT b') then (b', steps', trace', z) else
        let s := if TIMEOUT then 1 + steps' + steps else 0 in
        let t := if TRACE then trace' ++ trace else [] in
        let terminate := andb TIMEOUT $ orb b' (Nat.leb max_steps s) in
        (terminate, s, t, z) *)
        let res := 
          let s := (fast_if TIMEOUT then 1 + steps' + steps else 0) in
          let t := fast_if TRACE then trace' ++ trace else @nil trace_info in
          let terminate := andb TIMEOUT $ orb b' (N.leb max_steps s) in
          (terminate, s, t, z)
        in fast_if TIMEOUT then (if b' then (b', steps', trace', z) else res) else res
    end%N.

  Definition assert (b : bool) (err : Y) : trc unit :=
    lift_exc (Except.assert b err).

  Definition catchE {X} (a : trc X) (f : Y -> trc X) : trc X :=
    match a with
    | (true, steps, trace, e) => (true, steps, trace, e)
    | (false, steps, trace, e) =>
        match e with
        | inl a => (false, steps, trace, e)
        | inr e =>
            add_trace steps trace (f e)
        end
    end.

  Definition catchMap {X Z} (e : trc X) (f : Y -> trc Z) (g : X -> trc Z) : trc Z.
    Proof using max_steps Y timeout.
      exact (
      fast_if TIMEOUT then
      match e with
      | (true, steps, trace, inl e) =>
          (true, steps, trace, inr timeout)
      | (true, steps, trace, inr e) =>
          (true, steps, trace, inr e)
      | (false, steps, trace, inr e) =>
          add_trace steps trace (f e)
      | (false, steps, trace, inl a) =>
          add_trace steps trace (g a)
      end
    else (* we leave TRACE checking to add_trace. *)
      match e with
      | (_, steps, trace, inr e) =>
          add_trace steps trace (f e)
      | (_, steps, trace, inl a) =>
          add_trace steps trace (g a)
      end).
    Defined.

End trace.
(* Check (catchMap : N -> forall Y : Type, Y -> forall X Z : Type, TraceM X -> (Y -> TraceM Z) -> (X -> TraceM Z) -> TraceM Z). *)

Arguments trc_unwrap {_ _ _ _}.

(* Module example. *)
(*   Inductive err := *)
(*   | TimeoutErr *)
(*   | OtherErr (s : string). *)

(*   Definition max_steps := 2%N. *)
(*   Definition catchE := @catchE max_steps. *)
(*   Arguments catchE {_ _}. *)

(*   (* Instance: Monad (@TraceM err) := @trace_monad max_steps err. *) *)
(*   Instance: Monad (@TraceM err). *)
(*   Proof. *)
(*     apply trace_monad. *)
(*     all: (apply max_steps || apply TimeoutErr). *)
(*   Defined. *)

(*   Notation "'trc' A" := (@TraceM err A) (at level 100). *)

(*   Open Scope string_scope. *)
(*   Definition test : trc unit := *)
(*     trace "test"%bs;; *)
(*     raise $ OtherErr "s"%bs. *)

(*   Definition test' : trc unit := *)
(*     catchE test (fun _ => step;; raise $ OtherErr "sss"%bs). *)
(*   (*Eval cbn in test'.*) *)
(* End example. *)
