From MetaRocq.Template Require Import Checker. 
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Universes Environment Reflect.
From MetaRocq.Template Require Import Ast AstUtils.
From MetaRocq.Template Require Import LiftSubst Pretty.
From MetaRocq.Guarded Require Import MRRTree. 

From MetaRocq.Guarded Require Import Except util Trace Inductives.

(* non-recursive arguments = indices
  non-uniform = non-uniform 
*)
Open Scope list.

Unset Guard Checking.

Section checker.
  (* if [checkpos] is false, then positivity is assumed and we still attempt to compute the rectree *)
  Context (checkpos : bool).

  Implicit Types (Σ : global_env_ext) (Γ : context).

  (* recargs env *)
  Definition raEnv := list (recarg * wf_paths).
  (* inductive env: [(Γ, n, ntypes, ra_env)] where
      [Γ] is the dB context
      [n] is the dB index of the last inductive type of this block 
      [ntypes] is the number of inductive types (number of mutual clauses).
      [ra_env] is the list of recursive trees + recarg info for each element of the context
   *)
  Definition iEnv := context * nat * nat * raEnv.

  (** Push a variable [name] of type [type] with recursive tree [wf_paths] as non-recursive to the environment. *)
  Definition ienv_push_var (ienv : iEnv) name type (rt : wf_paths) : iEnv := 
    let '(Γ, n, ntypes, ra_env) := ienv in
    (Γ ,, vass name type, S n, ntypes, (Norec, rt) :: ra_env). 


  (** 
    Push a nested inductive to the ienv. It is assumed to have exactly one mutually defined body (mutual nested inductives are not supported).
    The uniform parameters are instantiated with [unif_param_inst]. 

    Specifically, for the j-th inductive in the block, we add [(Imbr $ mkInd ind_kn j, Param 0 j)], i.e. an inner inductive with a direct recursive reference to the j-th inductive in the block. 
    The rest of the env is lifted accordingly.
  *)
  Definition ienv_push_inductive Σ (ienv : iEnv) (ind : inductive) (unif_param_inst : list term) : exc iEnv := 
    '(mib, oib) <- lookup_mind_specif Σ ind;;
    let '(Γ, first_ind, ntypes, ra_env) := ienv in 
    (* add to Γ *)
    let relev := oib.(ind_relevance) in 
    let na := {| binder_name := nAnon; binder_relevance := relev |} in 
    (* get the type instantiated with params *)
    ty_inst <- hnf_prod_apps Σ Γ oib.(ind_type) unif_param_inst;;
    let Γ' := Γ ,, vass na ty_inst in 

    (* add to ra_env *)
    (* TODO: originally Imbr *)
    let ra_env' := map (fun t => (Mrec (RecArgInd ind), t)) (mk_rec_calls (X:=recarg) 1) ++ 
      (* lift the existing env *)
      map (fun '(r, t) => (r, rtree_lift 1 t)) ra_env in
    (* have to lift the index of the first inductive by one *)
    ret (Γ', S first_ind, ntypes, ra_env').

  (** Strip the first [n] prods off [c] and push them to [ienv]. *)
  Fixpoint ienv_decompose_prod Σ (ienv : iEnv) (n : nat) (c : term) {struct n} : exc iEnv * term := 
    let '(Γ, _, _, _) := ienv in 
    match n with 
    | 0 => ret (ienv, c)
    | S n => 
        c_whd <- whd_all Σ Γ c;;
        match c_whd with
        | tProd na ty body => 
            let ienv' := ienv_push_var ienv na ty mk_norec in 
            ienv_decompose_prod Σ ienv' n body 
        | _ => raise (OtherErr "ienv_decompose_prod" "not enough prods")
        end
    end.

  (* [weaker_rel_range_no_occur] checks that no dB indices between [n] and [n+nvars] (lower inclusive, upper exclusive) occur in [t]. 
    If some such occurrences are found, then reduction is performed in order to determine whether these occurrences are still there in the normal form. 
    If the occurrences are eliminated by reduction, then a witness reduct [Some t'] of [t] is returned. 
    Otherwise, if the occurrence could not be eliminated, [None] is returned. *)
  Definition weaker_rel_range_no_occur Σ Γ n nvars t : exc option term:=
    if rel_range_occurs n nvars t then 
      t' <- whd_all Σ Γ t;;
      if rel_range_occurs n nvars t' then ret None else ret $ Some t'
    else ret $ Some t.
  

  (** 
    Check positivity of one argument (of type [c]) of a constructor of inductive [ind].

    [ienv] is used to keep track of trees and recargs info of the context.
    [param_context] is the context of parameters of the inductive.
  *)
  Fixpoint check_positivity Σ (param_context : context) (ind : inductive) (ienv : iEnv) (c : term) {struct c}: exc wf_paths := 
    let '(Γ, first_ind, ntypes, ra_env) := ienv in 
    c_whd <- whd_all Σ Γ c;;
    let '(x, args) := decompose_app c_whd in 
    match x with 
    (* bullet 3 *)
    | tProd na ty body => 
        assert (args == []) (OtherErr "check_positivity" "constructor arg is ill-typed");; 
        (** If one of the inductives of the mutually inductive block occurs in the left-hand side of a product, then such an occurrence is a non-strictly positive recursive call.
          Occurrences on the right-hand side of the product must be strictly positive, which we check recursively. *)
        occur <- weaker_rel_range_no_occur Σ Γ first_ind ntypes ty;;
        match occur with 
        | None => 
            (* there is an occurrence *)
            if checkpos then 
              raise $ PositivityError "check_positivity" "tProd case: non-strictly positive occurrence"
            else check_positivity Σ param_context ind (ienv_push_var ienv na ty mk_norec) body
        | Some ty' => 
            check_positivity Σ param_context ind (ienv_push_var ienv na ty' mk_norec) body
        end
    | tRel k => 
      (* check if k is contained in the ra_env *)
      match nth_error ra_env k with 
    (* bullet 2 *)
      | Some (ra, rt) => 
          (* we have a tree and recarg info for k *)

          (* reduce args *)
          args_whd <- unwrap $ map (whd_all Σ Γ) args;;
          if checkpos && existsb (rel_range_occurs first_ind ntypes) args_whd 
          then 
            (** the case where one of the inductives of the mutually inductive block occurs as an argument of another is not known to be safe, so Rocq rejects it. *)
            raise $ PositivityError "check_positivity" "tRel case: non-strictly positive occurrence"
          else 
            (** just return the tree we have in the env *)
            ret rt
    (* bullet 1 *)
      | None => 
          (* if it is not, this refers to something outside the inductive decl and is non-recursive *)
          ret mk_norec
      end 
    (* nested case *)
    | tInd nested_ind _ => 
        (** check if one of the inductives of the mutually inductive block appears in the parameters *) 
        if existsb (rel_range_occurs first_ind ntypes) args 
        then 
          (** we have a nested inductive type and use [check_positivity_nested] *)
          check_positivity_nested Σ param_context ind ienv nested_ind args
        else ret mk_norec
    | _ => 
        if checkpos && (rel_range_occurs first_ind ntypes x || existsb (rel_range_occurs first_ind ntypes) args) 
        then raise (PositivityError "check_positivity" "non-strictly positive occurrence in other case") 
        else ret mk_norec
    end


  (** [check_positivity_nested] handles the case of nested inductive calls, i.e. where an inductive type from the current mutually inductive block is called as an argument of an inductive type (currently, this other inductive type must be a previously defined type, not one of the types of the current mutual block). 
  
    [nested_ind] is the nested inductive.
    [args] is the list of parameters the inductive is instantiated with.
  *)
  with check_positivity_nested Σ param_context ind (ienv : iEnv) (nested_ind : inductive) (args : list term) { struct args} : exc wf_paths := 
    let '(Γ, first_ind, ntypes, ra_env) := ienv in 
    (* get the nested inductive body *)
    '(mib, oib) <- lookup_mind_specif Σ nested_ind;;
    (* compute number of uniform params *)
    let num_unif_params := num_uniform_params mib in 
    let num_non_unif_params := mib.(ind_npars) - num_unif_params in 
    (* get the instantiation of uniform params provided by [args] *)
    let '(unif_param_inst, non_unif_params_inst) := chop num_unif_params args in 
    assert (length unif_param_inst == num_unif_params) (OtherErr "check_positivity_nested" "ill-formed inductive");;

    (* inductives of the inductive block being defined are only allowed to appear nested in the parameters of another inductive type, but not in index positions. *)
    assert (negb checkpos || forallb (fun arg => negb (rel_range_occurs first_ind ntypes arg)) non_unif_params_inst) (OtherErr "check_positivity_nested" "recursive occurrence in index position of nested inductive");;
    (* nested mutual inductives are not supported *)
    let nested_ntypes := length mib.(ind_bodies) in 
    assert (nested_ntypes == 1) (OtherErr "check_positivity_nested" "nested mutual inductive types are not supported");;
    
    (* push inductive to env *)
    ienv' <- ienv_push_inductive Σ ienv nested_ind unif_param_inst;; 
    let '(Γ', _, _ , _) := ienv' in

    (** get constructor types (with parameters), assuming that the mutual inductives are at [0]...[nested_ntypes-1]*)
    let constrs := map cstr_type oib.(ind_ctors) in
    (** abstract the parameters of the recursive occurrences of the inductive type in the constructor types *)
    (** we assume that at indices [0]... [nested_ntypes-1], the inductive types are instantiated _with_ the parameters *)
    let abstracted_constrs := abstract_params_mind_constrs nested_ntypes num_unif_params constrs in


    (* the inductive body in ienv' is already instantiated with the uniform parameters, but the types of the constructor in abstracted_constrs still quantify over them *)
    (* we now apply the constructors accordingly -- first the params need to be lifted since we just pushed the inductives *)
    let lifted_unif_param_inst := map (lift0 nested_ntypes) unif_param_inst in 
    (* apply them to the parameters and then check that the nesting inductive type is covariant in the parameters which are instantiated with inductives of the (outer) mutually inductive block, i.e. they occur positively in the types of the nested constructors *)
    recargs_constrs_nested <- unwrap $ map (fun constr => 
      (* apply to uniform params *)
      constr_inst <- hnf_prod_apps Σ Γ' constr lifted_unif_param_inst;;

      (** move non-uniform parameters into the context *) 
      '(ienv'', constr') <- ienv_decompose_prod Σ ienv' num_non_unif_params constr_inst;;     
      (* check positive occurrences recursively *)
      check_constructor Σ param_context ind ienv'' constr') abstracted_constrs;;
    (* make the tree for this nested inductive *)
    (* TODO: originally Imbr *)
    rec_trees <- except (OtherErr "check_positivity_nested" "out of fuel") $ mk_rec [mk_ind_paths (Mrec (RecArgInd nested_ind)) recargs_constrs_nested];;
    (* get the singleton *)
    match rec_trees with 
    | [s] => ret s
    | _ => raise $ OtherErr "check_positivity_nested" "mk_rec is broken"
    end

  (** [check_constructor] checks the positivity condition in type [c] of a constructor, that is it checks that recursive calls to the inductives of the mutually inductive definition appear strictly positively in each of the constructor's arguments. 
    It returns the list of recargs trees for the constructor's arguments.
  *)
  with check_constructor Σ (param_context : context) (ind : inductive) (ienv : iEnv) (c : term) {struct c} : exc (list wf_paths) :=  
    let check_constructor_rec := fix check_constructor_rec ienv (lrec :list wf_paths) (c : term) {struct c} : exc (list wf_paths) := 
      let '(Γ, first_ind, ntypes, ra_env) := ienv in 
      c_whd <- whd_all Σ Γ c;;
      let '(x, args) := decompose_app c_whd in
      match x with 
      | tProd na type body => 
          (* the constructor has an argument of type [type] *)
          assert (args == []) (OtherErr "check_constructor" "tProd case: ill-typed term");;
          (* compute the recursive structure of the type *) 
          rec_tree <- check_positivity Σ  param_context ind ienv type;;
          (* [na] of type [type] can be assumed to be of non-recursive type for this purpose *)
          let ienv' := ienv_push_var ienv na type mk_norec in 
          (* process the rest of the constructor type *)
          check_constructor_rec ienv' (rec_tree :: lrec) body
      | _ => 
          (* if we check positivity, then there should be no recursive occurrence in the args *)
          assert (negb (checkpos) || (forallb (fun arg => negb (rel_range_occurs first_ind ntypes arg)) args)) (OtherErr "check_constructor" "");;
          (* we have processed all the arguments of the constructor -- reverse to get a valid dB-indexed context *)
          ret $ MRList.rev lrec  
      end
  in check_constructor_rec ienv [] c. 

  (**
    Check the positivity of member [ind] of a mutual inductive definition. 
    It returns a recursive recargs tree which represents the positions of the recursive calls of inductives in [ind].

    [recursive] is true iff the inductive is recursive (recursivity != BiFinite).
    [cons_names] is the list of constructor names.
    [cons_types] is the list of constructor types (with parameters!).
    [ienv] is the current inductive context (already containing the ra_env entries for the type's parameters!).
  *)
  Definition check_positivity_one Σ (recursive : bool) (ienv : iEnv) (param_context : context) (ind : inductive) (cons_names : list string) (cons_types : list term) := 
    let '(Γ, _, ntypes, _) := ienv in 
    let num_params := length param_context in 
    recargs_constrs <- unwrap $ 
      map2 (fun name type => 
        (* get the constructor type without parameters *)
        '(_, raw_type) <- decompose_prod_n_assum Σ Γ num_params type;;
        (* get the trees for the (non-parameter) arguments of the constructor *)
        check_constructor Σ param_context ind ienv raw_type 
        ) cons_names cons_types;;
    (* make the tree for this inductive body *)
    ret $ mk_ind_paths (Mrec (RecArgInd ind)) recargs_constrs. 
    

  (**
    [check_positivity_mind kn consnames Σ Γ param_context finite inds] computes a list of recargs trees for the bodies of a mutual inductive.
    [kn] is the inductive's kernel name (used for the trees).
    [cons_names] are the names of the constructors.
    [Γ] is the dB context and should contain the parameters (at the head) and the inductives (for recursive usage; after the parameters).
    [param_context] is a context containing the inductive's parameters.
    [finite] determines the finiteness of the inductive.
    [inds] contains for each inductive body a list of constructor types (with parameters, in an environment where the inductives for recursive calls are bound at 0 .. )
  *)
  Definition check_positivity_mind (kn : kername) (cons_names : list (list string)) Σ Γ (param_context : context) (finite : recursivity_kind) (inds : list (list term)) : exc list wf_paths := 
    let ntypes := length inds in 
    let recursive := finite != BiFinite in 
    (* build trivially recursive trees + recarg headers*)
    let rc := mapi (fun j t => (Mrec (RecArgInd (mkInd kn j)), t)) (mk_rec_calls ntypes) in 
    (* build the initial ra_env - we have to reverse due to dB 
      this contains the entries for recursive uses of the inductives of this block*)
    let ra_env := MRList.rev rc in
    let nparams := length param_context in 
    let check_one_body i cons_names cons_types := 
      (* add parameters to ra_env as non-recursive *)
      let ra_env_pars := tabulate (fun _ => (Norec, mk_norec)) nparams ++ ra_env in 
      (* Γ and the ra_env_pars do line-up now. 
        build the initial ienv. *)
      (* nparams is the dB index of the first inductive of this mutual block in Γ *)
      let ienv := (Γ, nparams, ntypes, ra_env_pars) in 
      check_positivity_one Σ recursive ienv param_context (mkInd kn i) cons_names cons_types
    in 
    recargs_bodies <- unwrap $ map2_i check_one_body cons_names inds;; 
    except (OtherErr "check_positivity_mind" "mk_rec out of fuel") (mk_rec recargs_bodies).

End checker.
