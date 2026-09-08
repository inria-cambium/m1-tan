# Rocq's guard checker implemented in MetaRocq

This repository contains the guard checker of Rocq implemented in Rocq,
using the MetaRocq project.

## Installation
```sh
opam switch create metacoq-guard --packages="ocaml-variants.4.14.1+options,ocaml-option-flambda"
eval $(opam env --switch=metacoq-guard)
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin -n -y "https://github.com/MetaRocq/metacoq.git#v1.3.2-8.19"
opam install coq-metacoq-template coq-metacoq-utils
make -j
```

## Usage

```coq
From MetaRocq.Guarded Require Import plugin.
From MetaRocq Require Import Utils.bytestring.

Open Scope bs.

(* define your fixpoint *)
Fixpoint add (m n : nat) : nat :=
  match m with
  | O => n
  | S m' => add m' (S n)
  end.

MetaRocq Run (check_fix add).
(* accepts a boolean flag on the expected guardedness. *)
MetaRocq Run (check_fix_ci true add).
```

## Credits

This project is based on https://github.com/lgaeher/metacoq/blob/guarded/README_project.md.

