# Rocq's guard checker implemented in MetaRocq

This repository contains the guard checker of Rocq implemented in Rocq,
using the MetaRocq project.
It implements the guard checker at commit hash 
[d6550d16f01d39dee97f7e645e415de51725fd2e](https://github.com/rocq-prover/rocq/blob/d6550d16f01d39dee97f7e645e415de51725fd2e/kernel/inductive.ml#L569).

## Installation
```sh
opam switch create . ocaml-variants.5.5.1+options --repos=default,rocq-released -y
opam pin -n -y "https://github.com/MetaRocq/metarocq.git#v1.5.1-9.2"
opam install rocq-metarocq-template rocq-metarocq-utils
make -j
```

## Usage

```rocq
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
