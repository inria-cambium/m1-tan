From MetaRocq.Guarded Require Import plugin.
From MetaRocq Require Import Utils.bytestring.

Open Scope bs.

Set Printing Depth 200.
Set Printing Width 200.

Inductive rtree := rnode (l : list rtree).

Fixpoint rtree_size (t : rtree) :=
  let map_id :=
    (fix map (l : list (rtree)) : list (rtree) := match l with
                                                   | nil => nil
                                                   | cons a t => cons (rtree_size a) nil
                                                   end) in
  match t with
  | rnode l => rnode l
  end.

MetaRocq Quote Recursively Definition syntax := rtree_size.
Definition Σ := Eval cbv in fst syntax.

From MetaRocq.Template Require Import Ast AstUtils All.
From MetaRocq Require Import TemplateMonad.

MetaRocq Run (tmBind (compute_paths_env (Σ, Universes.Monomorphic_ctx) Σ.(Ast.Env.declarations)) (fun paths_env => tmDefinition "ρ" paths_env)).

Definition t := Eval cbv in
    let t := snd syntax in
  match t with 
  | tConst kn u => 
      match Inductives.lookup_env_const (Σ, Universes.Monomorphic_ctx) kn with 
      | Some const => 
          match const.(cst_body) with 
          | Some body => body
          | _ => t
          end
      | None => t
      end
  | _ => t
  end.

From MetaRocq.Guarded Require Import Inductives.

Axiom printf : string -> string.

Definition res :=
  match t with
  | tFix mfix _ =>
      match guardchecker.check_fix (Σ, Universes.Monomorphic_ctx) ρ nil mfix with
      | (_, trace, _) => List.map printf trace
      end
  | _ => nil
  end.

From Stdlib Require Import List.

Require Import Extraction.
From Stdlib Require Import Ascii FSets ExtrOcamlBasic ExtrOCamlFloats ExtrOCamlInt63.

Extraction "res" res.

Eval vm_compute in res.
