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

(* From ReductionEffect Require Import PrintingEffect. *)

(* Definition failure := fun _UNBOUND_REL_3 =>
  (String.String " "
   (String.String " "
      (String.String "s"
         (String.String "t"
            (String.String "a"
               (String.String "c"
                  (String.String "k"
                     (String.String "("
                        ((fix append (x y : string) {struct x} : string := match x with
                                                                           | "" => y
                                                                           | String.String x0 xs => String.String x0 (append xs y)
                                                                           end)
                           ((fix string_of_uint (n : Decimal.uint) : string :=
                               match n with
                               | Decimal.Nil => ""
                               | Decimal.D0 n0 => String.String "0" (string_of_uint n0)
                               | Decimal.D1 n0 => String.String "1" (string_of_uint n0)
                               | Decimal.D2 n0 => String.String "2" (string_of_uint n0)
                               | Decimal.D3 n0 => String.String "3" (string_of_uint n0)
                               | Decimal.D4 n0 => String.String "4" (string_of_uint n0)
                               | Decimal.D5 n0 => String.String "5" (string_of_uint n0)
                               | Decimal.D6 n0 => String.String "6" (string_of_uint n0)
                               | Decimal.D7 n0 => String.String "7" (string_of_uint n0)
                               | Decimal.D8 n0 => String.String "8" (string_of_uint n0)
                               | Decimal.D9 n0 => String.String "9" (string_of_uint n0)
                               end)
                              ((fix revapp (d d' : Decimal.uint) {struct d} : Decimal.uint :=
                                  match d with
                                  | Decimal.Nil => d'
                                  | Decimal.D0 d0 => revapp d0 (Decimal.D0 d')
                                  | Decimal.D1 d0 => revapp d0 (Decimal.D1 d')
                                  | Decimal.D2 d0 => revapp d0 (Decimal.D2 d')
                                  | Decimal.D3 d0 => revapp d0 (Decimal.D3 d')
                                  | Decimal.D4 d0 => revapp d0 (Decimal.D4 d')
                                  | Decimal.D5 d0 => revapp d0 (Decimal.D5 d')
                                  | Decimal.D6 d0 => revapp d0 (Decimal.D6 d')
                                  | Decimal.D7 d0 => revapp d0 (Decimal.D7 d')
                                  | Decimal.D8 d0 => revapp d0 (Decimal.D8 d')
                                  | Decimal.D9 d0 => revapp d0 (Decimal.D9 d')
                                  end)
                                 ((fix to_little_uint (n : nat) (acc : Decimal.uint) {struct n} : Decimal.uint := match n with
                                                                                                                  | 0 => acc
                                                                                                                  | S n0 => to_little_uint n0 (Decimal.Little.succ acc)
                                                                                                                  end)
                                    ((fix length (l : list guardchecker.stack_element) : nat := match l with
                                                                                                | []%list => 0
                                                                                                | (_ :: l')%list => S (length l')
                                                                                                end) _UNBOUND_REL_3) (Decimal.D0 Decimal.Nil)) Decimal.Nil))
                           (String.String ")"
                              (String.String ":"
                                 (String.String " "
                                    ((fix concat (sep : string) (s : list string) {struct s} : string :=
                                        match s with
                                        | []%list => ""
                                        | [s0]%list => s0
                                        | (s0 :: (_ :: _) as xs)%list => s0 ++ sep ++ concat sep xs
                                        end) "|"
                                       ((fix map (l : list guardchecker.stack_element) : list string :=
                                           match l with
                                           | []%list => []%list
                                           | (a :: t)%list =>
                                               ((fun z : guardchecker.stack_element =>
                                                 match z with
                                                 | guardchecker.SClosure _ G _ t0 =>
                                                     ("SClosure " ++
                                                      guardchecker.print_term
                                                        ({|
                                                           universes :=
                                                             ({|
                                                                VSet.this :=
                                                                  LevelSet.Raw.Node (BinNums.Zpos (BinNums.xO BinNums.xH)) LevelSet.Raw.Leaf Level.lzero
                                                                    (LevelSet.Raw.Node (BinNums.Zpos BinNums.xH) LevelSet.Raw.Leaf (Level.level "Rocq.Init.Datatypes.51") LevelSet.Raw.Leaf);
                                                                VSet.is_ok :=
                                                                  LevelSet.Raw.add_ok (s:=LevelSet.Raw.Node (BinNums.Zpos BinNums.xH) LevelSet.Raw.Leaf Level.lzero LevelSet.Raw.Leaf)
                                                                    (Level.level "Rocq.Init.Datatypes.51") (LevelSet.Raw.add_ok (s:=LevelSet.Raw.Leaf) Level.lzero LevelSet.Raw.empty_ok)
                                                              |}, {| CS.this := ConstraintSet.Raw.Leaf; CS.is_ok := ConstraintSet.Raw.empty_ok |});
                                                           declarations :=
                                                             [(MPfile ["test"; "Guarded"; "MetaRocq"], "rtree_size",
                                                               ConstantDecl
                                                                 {|
                                                                   cst_type :=
                                                                     tProd {| binder_name := nNamed "t"; binder_relevance := Relevant |}
                                                                       (tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} [])
                                                                       (tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} []);
                                                                   cst_body :=
                                                                     Some
                                                                       (tFix
                                                                          [{|
                                                                             dname := {| binder_name := nNamed "rtree_size"; binder_relevance := Relevant |};
                                                                             dtype :=
                                                                               tProd {| binder_name := nNamed "t"; binder_relevance := Relevant |}
                                                                                 (tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} [])
                                                                                 (tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} []);
                                                                             dbody :=
                                                                               tLambda {| binder_name := nNamed "t"; binder_relevance := Relevant |}
                                                                                 (tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} [])
                                                                                 (tLetIn {| binder_name := nNamed "map_id"; binder_relevance := Relevant |}
                                                                                    (tFix
                                                                                       [{|
                                                                                          dname := {| binder_name := nNamed "map"; binder_relevance := Relevant |};
                                                                                          dtype :=
                                                                                            tProd {| binder_name := nNamed "l"; binder_relevance := Relevant |}
                                                                                              (tApp (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |} [])
                                                                                                 [tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} []])
                                                                                              (tApp (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |} [])
                                                                                                 [tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} []]);
                                                                                          dbody :=
                                                                                            tLambda {| binder_name := nNamed "l"; binder_relevance := Relevant |}
                                                                                              (tApp (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |} [])
                                                                                                 [tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} []])
                                                                                              (tCase
                                                                                                 {|
                                                                                                   ci_ind := {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |};
                                                                                                   ci_npar := 1;
                                                                                                   ci_relevance := Relevant
                                                                                                 |}
                                                                                                 {|
                                                                                                   puinst := [];
                                                                                                   pparams :=
                                                                                                     [tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |}
                                                                                                        []];
                                                                                                   pcontext := [{| binder_name := nNamed "l"; binder_relevance := Relevant |}];
                                                                                                   preturn :=
                                                                                                     tApp
                                                                                                       (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |}
                                                                                                          [])
                                                                                                       [tInd
                                                                                                          {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |}
                                                                                                          []]
                                                                                                 |} (tRel 0)
                                                                                                 [{|
                                                                                                    bcontext := [];
                                                                                                    bbody :=
                                                                                                      tApp
                                                                                                        (tConstruct
                                                                                                           {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |} 0
                                                                                                           [])
                                                                                                        [tInd
                                                                                                           {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |}
                                                                                                           []]
                                                                                                  |};
                                                                                                  {|
                                                                                                    bcontext :=
                                                                                                      [{| binder_name := nNamed "t"; binder_relevance := Relevant |};
                                                                                                       {| binder_name := nNamed "a"; binder_relevance := Relevant |}];
                                                                                                    bbody :=
                                                                                                      tApp
                                                                                                        (tConstruct
                                                                                                           {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |} 1
                                                                                                           [])
                                                                                                        [tInd
                                                                                                           {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |}
                                                                                                           []; tApp (tRel 5) [tRel 1];
                                                                                                         tApp
                                                                                                           (tConstruct
                                                                                                              {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |}
                                                                                                              0 [])
                                                                                                           [tInd
                                                                                                              {|
                                                                                                                inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0
                                                                                                              |} []]]
                                                                                                  |}]);
                                                                                          rarg := 0
                                                                                        |}] 0)
                                                                                    (tProd {| binder_name := nNamed "l"; binder_relevance := Relevant |}
                                                                                       (tApp (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |} [])
                                                                                          [tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} []])
                                                                                       (tApp (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |} [])
                                                                                          [tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} []]))
                                                                                    (tCase
                                                                                       {|
                                                                                         ci_ind := {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |};
                                                                                         ci_npar := 0;
                                                                                         ci_relevance := Relevant
                                                                                       |}
                                                                                       {|
                                                                                         puinst := [];
                                                                                         pparams := [];
                                                                                         pcontext := [{| binder_name := nNamed "t"; binder_relevance := Relevant |}];
                                                                                         preturn :=
                                                                                           tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} []
                                                                                       |} (tRel 1)
                                                                                       [{|
                                                                                          bcontext := [{| binder_name := nNamed "l"; binder_relevance := Relevant |}];
                                                                                          bbody :=
                                                                                            tApp
                                                                                              (tConstruct {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |}
                                                                                                 0 []) [tRel 0]
                                                                                        |}]));
                                                                             rarg := 0
                                                                           |}] 0);
                                                                   cst_universes := Monomorphic_ctx;
                                                                   cst_relevance := Relevant
                                                                 |});
                                                              (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree",
                                                               InductiveDecl
                                                                 {|
                                                                   ind_finite := Finite;
                                                                   ind_npars := 0;
                                                                   ind_params := [];
                                                                   ind_bodies :=
                                                                     [{|
                                                                        ind_name := "rtree";
                                                                        ind_indices := [];
                                                                        Env.ind_sort :=
                                                                          sType
                                                                            {|
                                                                              t_set :=
                                                                                {| LevelExprSet.this := [(Level.lzero, 0)]; LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.lzero, 0) |};
                                                                              t_ne := eq_refl
                                                                            |};
                                                                        ind_type :=
                                                                          tSort
                                                                            (sType
                                                                               {|
                                                                                 t_set :=
                                                                                   {| LevelExprSet.this := [(Level.lzero, 0)]; LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.lzero, 0) |};
                                                                                 t_ne := eq_refl
                                                                               |});
                                                                        ind_kelim := IntoAny;
                                                                        ind_ctors :=
                                                                          [{|
                                                                             cstr_name := "rnode";
                                                                             cstr_args :=
                                                                               [{|
                                                                                  decl_name := {| binder_name := nNamed "l"; binder_relevance := Relevant |};
                                                                                  decl_body := None;
                                                                                  decl_type :=
                                                                                    tApp (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |} []) [tRel 0]
                                                                                |}];
                                                                             cstr_indices := [];
                                                                             cstr_type :=
                                                                               tProd {| binder_name := nNamed "l"; binder_relevance := Relevant |}
                                                                                 (tApp (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |} []) [tRel 0])
                                                                                 (tRel 1);
                                                                             cstr_arity := 1
                                                                           |}];
                                                                        ind_projs := [];
                                                                        ind_relevance := Relevant
                                                                      |}];
                                                                   ind_universes := Monomorphic_ctx;
                                                                   ind_variance := None
                                                                 |});
                                                              (MPfile ["Datatypes"; "Init"; "Rocq"], "list",
                                                               InductiveDecl
                                                                 {|
                                                                   ind_finite := Finite;
                                                                   ind_npars := 1;
                                                                   ind_params :=
                                                                     [{|
                                                                        decl_name := {| binder_name := nNamed "A"; binder_relevance := Relevant |};
                                                                        decl_body := None;
                                                                        decl_type :=
                                                                          tSort
                                                                            (sType
                                                                               {|
                                                                                 t_set :=
                                                                                   {|
                                                                                     LevelExprSet.this := [(Level.level "Rocq.Init.Datatypes.51", 0)];
                                                                                     LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.level "Rocq.Init.Datatypes.51", 0)
                                                                                   |};
                                                                                 t_ne := eq_refl
                                                                               |})
                                                                      |}];
                                                                   ind_bodies :=
                                                                     [{|
                                                                        ind_name := "list";
                                                                        ind_indices := [];
                                                                        Env.ind_sort :=
                                                                          sType
                                                                            {|
                                                                              t_set :=
                                                                                {|
                                                                                  LevelExprSet.this := [(Level.lzero, 0); (Level.level "Rocq.Init.Datatypes.51", 0)];
                                                                                  LevelExprSet.is_ok :=
                                                                                    LevelExprSet.Raw.add_ok (s:=[(Level.lzero, 0)]) (Level.level "Rocq.Init.Datatypes.51", 0)
                                                                                      (LevelExprSet.Raw.singleton_ok (Level.lzero, 0))
                                                                                |};
                                                                              t_ne :=
                                                                                Universes.NonEmptySetFacts.add_obligation_1 (Level.level "Rocq.Init.Datatypes.51", 0)
                                                                                  {|
                                                                                    t_set :=
                                                                                      {|
                                                                                        LevelExprSet.this := [(Level.lzero, 0)]; LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
                                                                                      |};
                                                                                    t_ne := eq_refl
                                                                                  |}
                                                                            |};
                                                                        ind_type :=
                                                                          tProd {| binder_name := nNamed "A"; binder_relevance := Relevant |}
                                                                            (tSort
                                                                               (sType
                                                                                  {|
                                                                                    t_set :=
                                                                                      {|
                                                                                        LevelExprSet.this := [(Level.level "Rocq.Init.Datatypes.51", 0)];
                                                                                        LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.level "Rocq.Init.Datatypes.51", 0)
                                                                                      |};
                                                                                    t_ne := eq_refl
                                                                                  |}))
                                                                            (tSort
                                                                               (sType
                                                                                  {|
                                                                                    t_set :=
                                                                                      {|
                                                                                        LevelExprSet.this := [(Level.lzero, 0); (Level.level "Rocq.Init.Datatypes.51", 0)];
                                                                                        LevelExprSet.is_ok :=
                                                                                          LevelExprSet.Raw.add_ok (s:=[(Level.lzero, 0)]) (Level.level "Rocq.Init.Datatypes.51", 0)
                                                                                            (LevelExprSet.Raw.singleton_ok (Level.lzero, 0))
                                                                                      |};
                                                                                    t_ne :=
                                                                                      Universes.NonEmptySetFacts.add_obligation_1 (Level.level "Rocq.Init.Datatypes.51", 0)
                                                                                        {|
                                                                                          t_set :=
                                                                                            {|
                                                                                              LevelExprSet.this := [(Level.lzero, 0)];
                                                                                              LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
                                                                                            |};
                                                                                          t_ne := eq_refl
                                                                                        |}
                                                                                  |}));
                                                                        ind_kelim := IntoAny;
                                                                        ind_ctors :=
                                                                          [{|
                                                                             cstr_name := "nil";
                                                                             cstr_args := [];
                                                                             cstr_indices := [];
                                                                             cstr_type :=
                                                                               tProd {| binder_name := nNamed "A"; binder_relevance := Relevant |}
                                                                                 (tSort
                                                                                    (sType
                                                                                       {|
                                                                                         t_set :=
                                                                                           {|
                                                                                             LevelExprSet.this := [(Level.level "Rocq.Init.Datatypes.51", 0)];
                                                                                             LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.level "Rocq.Init.Datatypes.51", 0)
                                                                                           |};
                                                                                         t_ne := eq_refl
                                                                                       |})) (tApp (tRel 1) [tRel 0]);
                                                                             cstr_arity := 0
                                                                           |};
                                                                           {|
                                                                             cstr_name := "cons";
                                                                             cstr_args :=
                                                                               [{|
                                                                                  decl_name := {| binder_name := nAnon; binder_relevance := Relevant |};
                                                                                  decl_body := None;
                                                                                  decl_type := tApp (tRel 2) [tRel 1]
                                                                                |}; {| decl_name := {| binder_name := nAnon; binder_relevance := Relevant |}; decl_body := None; decl_type := tRel 0 |}];
                                                                             cstr_indices := [];
                                                                             cstr_type :=
                                                                               tProd {| binder_name := nNamed "A"; binder_relevance := Relevant |}
                                                                                 (tSort
                                                                                    (sType
                                                                                       {|
                                                                                         t_set :=
                                                                                           {|
                                                                                             LevelExprSet.this := [(Level.level "Rocq.Init.Datatypes.51", 0)];
                                                                                             LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.level "Rocq.Init.Datatypes.51", 0)
                                                                                           |};
                                                                                         t_ne := eq_refl
                                                                                       |}))
                                                                                 (tProd {| binder_name := nAnon; binder_relevance := Relevant |} (tRel 0)
                                                                                    (tProd {| binder_name := nAnon; binder_relevance := Relevant |} (tApp (tRel 2) [tRel 1]) (tApp (tRel 3) [tRel 2])));
                                                                             cstr_arity := 2
                                                                           |}];
                                                                        ind_projs := [];
                                                                        ind_relevance := Relevant
                                                                      |}];
                                                                   ind_universes := Monomorphic_ctx;
                                                                   ind_variance := None
                                                                 |})];
                                                           retroknowledge :=
                                                             {|
                                                               Retroknowledge.retro_int63 := Some (MPfile ["PrimInt63"; "Int63"; "Cyclic"; "Numbers"; "Rocq"], "int");
                                                               Retroknowledge.retro_float64 := Some (MPfile ["PrimFloat"; "Floats"; "Rocq"], "float");
                                                               Retroknowledge.retro_array := Some (MPfile ["PArray"; "Array"; "Rocq"], "array")
                                                             |}
                                                         |}, Monomorphic_ctx) (guardchecker.loc_env G) t0)%bs
                                                 | guardchecker.SArg s =>
                                                     ("SArg " ++
                                                      guardchecker.print_subterm_spec
                                                        ({|
                                                           universes :=
                                                             ({|
                                                                VSet.this :=
                                                                  LevelSet.Raw.Node (BinNums.Zpos (BinNums.xO BinNums.xH)) LevelSet.Raw.Leaf Level.lzero
                                                                    (LevelSet.Raw.Node (BinNums.Zpos BinNums.xH) LevelSet.Raw.Leaf (Level.level "Rocq.Init.Datatypes.51") LevelSet.Raw.Leaf);
                                                                VSet.is_ok :=
                                                                  LevelSet.Raw.add_ok (s:=LevelSet.Raw.Node (BinNums.Zpos BinNums.xH) LevelSet.Raw.Leaf Level.lzero LevelSet.Raw.Leaf)
                                                                    (Level.level "Rocq.Init.Datatypes.51") (LevelSet.Raw.add_ok (s:=LevelSet.Raw.Leaf) Level.lzero LevelSet.Raw.empty_ok)
                                                              |}, {| CS.this := ConstraintSet.Raw.Leaf; CS.is_ok := ConstraintSet.Raw.empty_ok |});
                                                           declarations :=
                                                             [(MPfile ["test"; "Guarded"; "MetaRocq"], "rtree_size",
                                                               ConstantDecl
                                                                 {|
                                                                   cst_type :=
                                                                     tProd {| binder_name := nNamed "t"; binder_relevance := Relevant |}
                                                                       (tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} [])
                                                                       (tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} []);
                                                                   cst_body :=
                                                                     Some
                                                                       (tFix
                                                                          [{|
                                                                             dname := {| binder_name := nNamed "rtree_size"; binder_relevance := Relevant |};
                                                                             dtype :=
                                                                               tProd {| binder_name := nNamed "t"; binder_relevance := Relevant |}
                                                                                 (tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} [])
                                                                                 (tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} []);
                                                                             dbody :=
                                                                               tLambda {| binder_name := nNamed "t"; binder_relevance := Relevant |}
                                                                                 (tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} [])
                                                                                 (tLetIn {| binder_name := nNamed "map_id"; binder_relevance := Relevant |}
                                                                                    (tFix
                                                                                       [{|
                                                                                          dname := {| binder_name := nNamed "map"; binder_relevance := Relevant |};
                                                                                          dtype :=
                                                                                            tProd {| binder_name := nNamed "l"; binder_relevance := Relevant |}
                                                                                              (tApp (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |} [])
                                                                                                 [tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} []])
                                                                                              (tApp (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |} [])
                                                                                                 [tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} []]);
                                                                                          dbody :=
                                                                                            tLambda {| binder_name := nNamed "l"; binder_relevance := Relevant |}
                                                                                              (tApp (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |} [])
                                                                                                 [tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} []])
                                                                                              (tCase
                                                                                                 {|
                                                                                                   ci_ind := {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |};
                                                                                                   ci_npar := 1;
                                                                                                   ci_relevance := Relevant
                                                                                                 |}
                                                                                                 {|
                                                                                                   puinst := [];
                                                                                                   pparams :=
                                                                                                     [tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |}
                                                                                                        []];
                                                                                                   pcontext := [{| binder_name := nNamed "l"; binder_relevance := Relevant |}];
                                                                                                   preturn :=
                                                                                                     tApp
                                                                                                       (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |}
                                                                                                          [])
                                                                                                       [tInd
                                                                                                          {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |}
                                                                                                          []]
                                                                                                 |} (tRel 0)
                                                                                                 [{|
                                                                                                    bcontext := [];
                                                                                                    bbody :=
                                                                                                      tApp
                                                                                                        (tConstruct
                                                                                                           {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |} 0
                                                                                                           [])
                                                                                                        [tInd
                                                                                                           {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |}
                                                                                                           []]
                                                                                                  |};
                                                                                                  {|
                                                                                                    bcontext :=
                                                                                                      [{| binder_name := nNamed "t"; binder_relevance := Relevant |};
                                                                                                       {| binder_name := nNamed "a"; binder_relevance := Relevant |}];
                                                                                                    bbody :=
                                                                                                      tApp
                                                                                                        (tConstruct
                                                                                                           {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |} 1
                                                                                                           [])
                                                                                                        [tInd
                                                                                                           {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |}
                                                                                                           []; tApp (tRel 5) [tRel 1];
                                                                                                         tApp
                                                                                                           (tConstruct
                                                                                                              {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |}
                                                                                                              0 [])
                                                                                                           [tInd
                                                                                                              {|
                                                                                                                inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0
                                                                                                              |} []]]
                                                                                                  |}]);
                                                                                          rarg := 0
                                                                                        |}] 0)
                                                                                    (tProd {| binder_name := nNamed "l"; binder_relevance := Relevant |}
                                                                                       (tApp (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |} [])
                                                                                          [tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} []])
                                                                                       (tApp (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |} [])
                                                                                          [tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} []]))
                                                                                    (tCase
                                                                                       {|
                                                                                         ci_ind := {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |};
                                                                                         ci_npar := 0;
                                                                                         ci_relevance := Relevant
                                                                                       |}
                                                                                       {|
                                                                                         puinst := [];
                                                                                         pparams := [];
                                                                                         pcontext := [{| binder_name := nNamed "t"; binder_relevance := Relevant |}];
                                                                                         preturn :=
                                                                                           tInd {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |} []
                                                                                       |} (tRel 1)
                                                                                       [{|
                                                                                          bcontext := [{| binder_name := nNamed "l"; binder_relevance := Relevant |}];
                                                                                          bbody :=
                                                                                            tApp
                                                                                              (tConstruct {| inductive_mind := (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree"); inductive_ind := 0 |}
                                                                                                 0 []) [tRel 0]
                                                                                        |}]));
                                                                             rarg := 0
                                                                           |}] 0);
                                                                   cst_universes := Monomorphic_ctx;
                                                                   cst_relevance := Relevant
                                                                 |});
                                                              (MPfile ["test"; "Guarded"; "MetaRocq"], "rtree",
                                                               InductiveDecl
                                                                 {|
                                                                   ind_finite := Finite;
                                                                   ind_npars := 0;
                                                                   ind_params := [];
                                                                   ind_bodies :=
                                                                     [{|
                                                                        ind_name := "rtree";
                                                                        ind_indices := [];
                                                                        Env.ind_sort :=
                                                                          sType
                                                                            {|
                                                                              t_set :=
                                                                                {| LevelExprSet.this := [(Level.lzero, 0)]; LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.lzero, 0) |};
                                                                              t_ne := eq_refl
                                                                            |};
                                                                        ind_type :=
                                                                          tSort
                                                                            (sType
                                                                               {|
                                                                                 t_set :=
                                                                                   {| LevelExprSet.this := [(Level.lzero, 0)]; LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.lzero, 0) |};
                                                                                 t_ne := eq_refl
                                                                               |});
                                                                        ind_kelim := IntoAny;
                                                                        ind_ctors :=
                                                                          [{|
                                                                             cstr_name := "rnode";
                                                                             cstr_args :=
                                                                               [{|
                                                                                  decl_name := {| binder_name := nNamed "l"; binder_relevance := Relevant |};
                                                                                  decl_body := None;
                                                                                  decl_type :=
                                                                                    tApp (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |} []) [tRel 0]
                                                                                |}];
                                                                             cstr_indices := [];
                                                                             cstr_type :=
                                                                               tProd {| binder_name := nNamed "l"; binder_relevance := Relevant |}
                                                                                 (tApp (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Rocq"], "list"); inductive_ind := 0 |} []) [tRel 0])
                                                                                 (tRel 1);
                                                                             cstr_arity := 1
                                                                           |}];
                                                                        ind_projs := [];
                                                                        ind_relevance := Relevant
                                                                      |}];
                                                                   ind_universes := Monomorphic_ctx;
                                                                   ind_variance := None
                                                                 |});
                                                              (MPfile ["Datatypes"; "Init"; "Rocq"], "list",
                                                               InductiveDecl
                                                                 {|
                                                                   ind_finite := Finite;
                                                                   ind_npars := 1;
                                                                   ind_params :=
                                                                     [{|
                                                                        decl_name := {| binder_name := nNamed "A"; binder_relevance := Relevant |};
                                                                        decl_body := None;
                                                                        decl_type :=
                                                                          tSort
                                                                            (sType
                                                                               {|
                                                                                 t_set :=
                                                                                   {|
                                                                                     LevelExprSet.this := [(Level.level "Rocq.Init.Datatypes.51", 0)];
                                                                                     LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.level "Rocq.Init.Datatypes.51", 0)
                                                                                   |};
                                                                                 t_ne := eq_refl
                                                                               |})
                                                                      |}];
                                                                   ind_bodies :=
                                                                     [{|
                                                                        ind_name := "list";
                                                                        ind_indices := [];
                                                                        Env.ind_sort :=
                                                                          sType
                                                                            {|
                                                                              t_set :=
                                                                                {|
                                                                                  LevelExprSet.this := [(Level.lzero, 0); (Level.level "Rocq.Init.Datatypes.51", 0)];
                                                                                  LevelExprSet.is_ok :=
                                                                                    LevelExprSet.Raw.add_ok (s:=[(Level.lzero, 0)]) (Level.level "Rocq.Init.Datatypes.51", 0)
                                                                                      (LevelExprSet.Raw.singleton_ok (Level.lzero, 0))
                                                                                |};
                                                                              t_ne :=
                                                                                Universes.NonEmptySetFacts.add_obligation_1 (Level.level "Rocq.Init.Datatypes.51", 0)
                                                                                  {|
                                                                                    t_set :=
                                                                                      {|
                                                                                        LevelExprSet.this := [(Level.lzero, 0)]; LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
                                                                                      |};
                                                                                    t_ne := eq_refl
                                                                                  |}
                                                                            |};
                                                                        ind_type :=
                                                                          tProd {| binder_name := nNamed "A"; binder_relevance := Relevant |}
                                                                            (tSort
                                                                               (sType
                                                                                  {|
                                                                                    t_set :=
                                                                                      {|
                                                                                        LevelExprSet.this := [(Level.level "Rocq.Init.Datatypes.51", 0)];
                                                                                        LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.level "Rocq.Init.Datatypes.51", 0)
                                                                                      |};
                                                                                    t_ne := eq_refl
                                                                                  |}))
                                                                            (tSort
                                                                               (sType
                                                                                  {|
                                                                                    t_set :=
                                                                                      {|
                                                                                        LevelExprSet.this := [(Level.lzero, 0); (Level.level "Rocq.Init.Datatypes.51", 0)];
                                                                                        LevelExprSet.is_ok :=
                                                                                          LevelExprSet.Raw.add_ok (s:=[(Level.lzero, 0)]) (Level.level "Rocq.Init.Datatypes.51", 0)
                                                                                            (LevelExprSet.Raw.singleton_ok (Level.lzero, 0))
                                                                                      |};
                                                                                    t_ne :=
                                                                                      Universes.NonEmptySetFacts.add_obligation_1 (Level.level "Rocq.Init.Datatypes.51", 0)
                                                                                        {|
                                                                                          t_set :=
                                                                                            {|
                                                                                              LevelExprSet.this := [(Level.lzero, 0)];
                                                                                              LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
                                                                                            |};
                                                                                          t_ne := eq_refl
                                                                                        |}
                                                                                  |}));
                                                                        ind_kelim := IntoAny;
                                                                        ind_ctors :=
                                                                          [{|
                                                                             cstr_name := "nil";
                                                                             cstr_args := [];
                                                                             cstr_indices := [];
                                                                             cstr_type :=
                                                                               tProd {| binder_name := nNamed "A"; binder_relevance := Relevant |}
                                                                                 (tSort
                                                                                    (sType
                                                                                       {|
                                                                                         t_set :=
                                                                                           {|
                                                                                             LevelExprSet.this := [(Level.level "Rocq.Init.Datatypes.51", 0)];
                                                                                             LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.level "Rocq.Init.Datatypes.51", 0)
                                                                                           |};
                                                                                         t_ne := eq_refl
                                                                                       |})) (tApp (tRel 1) [tRel 0]);
                                                                             cstr_arity := 0
                                                                           |};
                                                                           {|
                                                                             cstr_name := "cons";
                                                                             cstr_args :=
                                                                               [{|
                                                                                  decl_name := {| binder_name := nAnon; binder_relevance := Relevant |};
                                                                                  decl_body := None;
                                                                                  decl_type := tApp (tRel 2) [tRel 1]
                                                                                |}; {| decl_name := {| binder_name := nAnon; binder_relevance := Relevant |}; decl_body := None; decl_type := tRel 0 |}];
                                                                             cstr_indices := [];
                                                                             cstr_type :=
                                                                               tProd {| binder_name := nNamed "A"; binder_relevance := Relevant |}
                                                                                 (tSort
                                                                                    (sType
                                                                                       {|
                                                                                         t_set :=
                                                                                           {|
                                                                                             LevelExprSet.this := [(Level.level "Rocq.Init.Datatypes.51", 0)];
                                                                                             LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.level "Rocq.Init.Datatypes.51", 0)
                                                                                           |};
                                                                                         t_ne := eq_refl
                                                                                       |}))
                                                                                 (tProd {| binder_name := nAnon; binder_relevance := Relevant |} (tRel 0)
                                                                                    (tProd {| binder_name := nAnon; binder_relevance := Relevant |} (tApp (tRel 2) [tRel 1]) (tApp (tRel 3) [tRel 2])));
                                                                             cstr_arity := 2
                                                                           |}];
                                                                        ind_projs := [];
                                                                        ind_relevance := Relevant
                                                                      |}];
                                                                   ind_universes := Monomorphic_ctx;
                                                                   ind_variance := None
                                                                 |})];
                                                           retroknowledge :=
                                                             {|
                                                               Retroknowledge.retro_int63 := Some (MPfile ["PrimInt63"; "Int63"; "Cyclic"; "Numbers"; "Rocq"], "int");
                                                               Retroknowledge.retro_float64 := Some (MPfile ["PrimFloat"; "Floats"; "Rocq"], "float");
                                                               Retroknowledge.retro_array := Some (MPfile ["PArray"; "Array"; "Rocq"], "array")
                                                             |}
                                                         |}, Monomorphic_ctx) s)%bs
                                                 end) a :: map t)%list
                                           end) _UNBOUND_REL_3)))))))))))))).
About failure.
Eval lazy in failure []. *)

From Stdlib Require Import List.

Require Import Extraction.
From Stdlib Require Import Ascii FSets ExtrOcamlBasic ExtrOCamlFloats ExtrOCamlInt63.

Extract Constant printf => "fun x -> print_endline (Obj.magic x) ; x".

Extraction "res" res.

(* Eval vm_compute in res. *)
