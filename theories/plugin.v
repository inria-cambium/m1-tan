From MetaRocq.Common Require Import Environment.
From MetaRocq.Template Require Import Ast AstUtils All.
Open Scope string_scope.
From Stdlib Require Import List String.
Import ListNotations.
Open Scope string_scope.
From MetaRocq.Utils Require Import MRList.
From MetaRocq.Guarded Require Import MRRTree Inductives guardchecker positivitychecker Except Trace.

(* explicit instantiation with TemplateMonad as a definition parametric over the monad causes trouble with universe polymorphism *)
Definition list_iter {X} (f : X -> TemplateMonad unit) (l : list X) : TemplateMonad unit := 
  List.fold_left (fun (acc : TemplateMonad unit) x => _ <- acc;; f x) l (ret tt).


(** Compute the wf_paths for the bodies of a mutual inductive (returns a list for the mutually defined types). *)
Definition check_inductive_mib (Σ:global_env_ext) (kn : kername) (mib : mutual_inductive_body) : TemplateMonad (option (list wf_paths)) := 
  let cons_names := map (fun oib => map cstr_name oib.(ind_ctors)) mib.(ind_bodies) in
  let cons_types := map (fun oib => map cstr_type oib.(ind_ctors)) mib.(ind_bodies) in

  match mib.(ind_bodies) with 
  | oib :: _ => 
    let '(param_context, _) := decompose_arity oib.(ind_type) mib.(ind_npars) in

    cons_names <- tmEval cbv cons_names;;
    cons_types <- tmEval cbv cons_types;;
    param_conext <- tmEval cbv param_context;;

    (* [Γ] should contain the parameters (at the head) and the inductives (for recursive usage; after the parameters). *)
    (* the first type should be last in the list *)
    let Γ := List.fold_right (fun oib acc => acc ,, vass (mkBindAnn nAnon oib.(ind_relevance)) oib.(ind_type)) [] mib.(ind_bodies) in
    (* add parameters *)
    let Γ := Γ ,,, param_context in

    match check_positivity_mind true kn cons_names Σ Γ param_context mib.(ind_finite) cons_types with
    | (_, _, _, inl l) =>  
        (* | inl l => *)
        l <- tmEval cbv l;;
        ret (Some l)
    | (_, _, _, inr e) =>  
        (* | inr e => *)
        e <- tmEval cbv e;; 
        tmPrint e;; ret None
    end
  | _ => ret None
  end.

(** Positivity checker *)
Definition check_inductive {A} (def : option ident) (a : A) : TemplateMonad unit := 
  '(Σ', t) <- tmQuoteRec a;;
  let Σ := (Σ', Monomorphic_ctx) in
  match t with
  | tInd ind _ => 
      match lookup_mind_specif Σ ind with 
      | (_, _, _, inl (mib, oib)) =>
        (* | inl (mib, oib) => *)
          l <- check_inductive_mib Σ ind.(inductive_mind) mib;;
          match l with
          | None => ret tt
          | Some l =>
              tmPrint "passed positivity check";;
              match def with
              | None => ret tt
              | Some name =>
                l <- tmEval cbv l;;
                match nth_error l ind.(inductive_ind) with
                | Some tree =>
                    tmPrint tree ;;
                    tmDefinitionRed_ false name None tree;;
                    ret tt
                | None => ret tt
                end
              end
          end
      | _ => ret tt
      end
  | _ => ret tt
  end.

(** Compute paths_env *)
(** Since the MR inductives representation does not include wf_paths, we first compute them via the positivity checker. The trees are carried around in an additional paths_env. *)
Fixpoint compute_paths_env Σ0 Σ : TemplateMonad (list (kername * (list wf_paths))):= 
  match Σ with
  | [] => ret []
  | (kn, InductiveDecl mib) :: Σ' => 
      l <- check_inductive_mib Σ0 kn mib;;
      match l with 
      | None => compute_paths_env Σ0 Σ'
      | Some l => 
          r <- compute_paths_env Σ0 Σ';;
          ret ((kn, l) :: r)
      end 
  | _ :: Σ' => compute_paths_env Σ0 Σ'
  end.

Set Universe Polymorphism. 
Polymorphic Definition tmAnd (ma mb : TemplateMonad bool) := tmBind ma (fun a => if a then mb else ret false).

Notation "ma m&& mb" := (tmAnd ma mb) (at level 105).

(** recursively traverse term and check fixpoints *)
(* needed for the const unfolding case for demonstrational purposes *)
#[bypass_check(guard)]
Fixpoint check_fix_term (Σ : global_env) ρ (Γ : context) (t : term) {struct t} : TemplateMonad bool := 
  match t with
  | tFix mfix _ => 
      (* (** we should first recursively check the body of the fix (in case of nested fixpoints!) *) *)
      (* let mfix_ctx := push_assumptions_context (map dname mfix, map dtype mfix) Γ in *)
      (* fold_left (fun mbool d => mbool m&& check_fix_term Σ ρ mfix_ctx d.(dbody)) mfix (tmReturn true) *)
      (* m&&  *)
      tmPrint "checking fixpoint:" ;;
      (* tmPrint mfix ;; *)
      (* NOTE : uncomment if using trace monad *)
      res <- tmEval lazy (check_fix (Σ, Monomorphic_ctx) ρ Γ mfix) ;;
      match res with
      | (_, trace, inr e) => (* not guarded *)
          trace <- tmEval lazy trace;;
          e <- tmEval lazy e;;
          _ <- monad_iter tmPrint (MRList.rev trace) ;;
          tmPrint e ;;
          tmReturn false
      | (_, trace, inl tt) => (* guarded *)
          trace <- tmEval lazy trace;;
          _ <- monad_iter tmPrint (MRList.rev trace) ;;
          tmPrint "success" ;;
          tmReturn true
      end

      (* NOTE : uncomment if using exc monad *)
      (*match (check_fix Σ Γ mfix) with*)
      (*| inr e => *)
          (*e <- tmEval cbv e;;*)
          (*tmPrint e*)
      (*| _ => tmPrint "success"*)
      (*end*)

  | tCoFix mfix idx =>
      tmPrint "co-fixpoint checking is currently not implemented" ;;
      tmReturn true
  | tLambda na T M => 
      check_fix_term Σ ρ Γ T m&&
      check_fix_term Σ ρ (Γ ,, vass na T) M
  | tApp u v => 
      check_fix_term Σ ρ Γ u m&&
      fold_left (fun mbool t => mbool m&& check_fix_term Σ ρ Γ t) v (tmReturn true)
  | tProd na A B => 
      check_fix_term Σ ρ Γ A m&&
      check_fix_term Σ ρ (Γ ,, vass na A) B
  | tCast C kind t => 
      check_fix_term Σ ρ Γ C m&&
      check_fix_term Σ ρ Γ t
  | tLetIn na b t b' => 
      check_fix_term Σ ρ Γ b m&&
      check_fix_term Σ ρ Γ t m&&
      check_fix_term Σ ρ (Γ ,, vdef na b t) b'
  | tCase ind rtf discriminant brs =>
      check_fix_term Σ ρ Γ rtf.(preturn) m&&
      check_fix_term Σ ρ Γ discriminant m&&
      fold_left (fun mbool '(mk_branch _ b) => mbool m&& check_fix_term Σ ρ Γ b) brs (tmReturn true)
  | tProj _ C => 
      check_fix_term Σ ρ Γ C
  | tConst kn u => 
      (* NOTE: this is just done for demonstrational purposes for things we have to extract from the global env. 
      Normally, we would not check things which are already in the global env, as they should already have been checked. *)
      match lookup_env_const (Σ, Monomorphic_ctx) kn with 
      | Some const => 
          match const.(cst_body) with 
          | Some t => check_fix_term Σ ρ Γ t
          | _ => tmReturn true
          end
      | None => tmReturn true
      end
      (* do not unfold nested consts *)

  | _ => tmReturn true 
  end.

Definition check_fix {A} (a : A) : TemplateMonad bool :=
  tmBind (tmQuoteRec a) (fun '(Σ, t) =>
  tmBind (compute_paths_env (Σ, Monomorphic_ctx) Σ.(declarations)) (fun paths_env =>
  let t := match t with 
       | tConst kn u => 
          match lookup_env_const (Σ, Monomorphic_ctx) kn with 
          | Some const => 
              match const.(cst_body) with 
              | Some body => body
              | _ => t
              end
          | None => t
          end
        | _ => t
       end in
  check_fix_term Σ paths_env [] t)).



(* Fails iff check_fix's result doesn't match b. *)
Definition check_fix_ci {A} (b : bool) (a : A) : TemplateMonad unit :=
  res <- check_fix a ;;
  if (res == b) then tmReturn tt else tmFail "error".

Definition check_module mod :=
  refs <- (tmQuoteModule mod) ;;
  monad_iter (fun ref =>
                match ref with
                | ConstRef kn => nm <- tmEval lazy (("checking " ++ string_of_kername kn)%bs) ;;
                                 tmPrint nm ;;
                                 t <- tmUnquote (tConst kn Instance.empty) ;;
                                 t' <- tmEval hnf (my_projT2 t) ;;
                                 check_fix t' ;; ret tt
                | _ => ret tt
                end
    ) refs ;;
  ret tt.

Definition check_module_ci b mod :=
  refs <- (tmQuoteModule mod) ;;
  monad_iter (fun ref =>
                match ref with
                | ConstRef kn => nm <- tmEval lazy (("checking " ++ string_of_kername kn)%bs) ;;
                                 tmPrint nm ;;
                                 t <- tmUnquote (tConst kn Instance.empty) ;;
                                 t' <- tmEval hnf (my_projT2 t) ;;
                                 check_fix_ci b t'
                | _ => ret tt
                end
    ) refs ;;
  ret tt.
