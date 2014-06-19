open Btype
open Ctype
open Types
open Typedtree
open Typeimplicit

(** Misc functions *)

let rec list_extract f acc = function
  | x :: xs when f x -> x, List.rev_append acc xs
  | x :: xs -> list_extract f (x :: acc) xs
  | [] -> raise Not_found

let list_extract f xs = list_extract f [] xs

let rec list_findmap f = function
  | [] -> raise Not_found
  | x :: xs ->
      match f x with
      | None -> list_findmap f xs
      | Some x' -> x'

let string_of_path path =
  Path.to_longident path |> Longident.flatten |> String.concat "."

let print_inst (path,_) =
  Printf.eprintf "%s\n%!" (string_of_path path)

let papply path arg = Path.Papply (path, arg)

(** [target] is the point from which a search starts *)
type target = {
  (* The module type we try to find an instance for *)
  target_type : Types.module_type;
  (* The identifier to which bound the result of the search to.
     E.g we are trying to fill the hole in:
       module %target_id : %target_type = _ *)
  target_id   : Ident.t;

  (* A unique identifier that will be used for termination checking.  When the
     target is the argument to a functor instantiation, if this functor is
     instantiated multiple times we enforce that the constraints on the
     argument are stronger.

     Pair (Arg_1) (Pair (Arg_1') (Arg_2))

     Arg_1 and Arg_1' targets will have a different target_id but the same
     target_uid.  We check that constraints on Arg_1' are stronger than those
     on Arg_1'.

     Note: This is also true of (Pair (Arg_1') (Arg_2)) and Arg_2, used as
     second arguments to Pair.  *)
  target_uid  : Ident.t;

  target_hkt  : (type_expr * type_expr) list;
}

(** Constraints are a list of equations of the form [path] = [type_expr].
    The [Constraints] module apply those equations to a module type by
    setting [type_expr] as a manifest for type at [path].

    [Constraints.apply_abstract] expects all pointed types to be abstract (no
    manifest), and fail if this is not the case.
    [Constraints.apply] will try to unify those types.
*)
module Constraints = struct

  (* Apply constraints to a module type.

    1. Traverse the module type to substitute type declarations with
      constraints and accumulate types to unify.

      When constraining a type declaration, add the constraint as manifest.
      If the type declaration already had a manifest, keep the original
      manifest in a separate list to unify it in a later pass.

      During traversal, we register module and submodule types in environment
      because find_modtype_expansion might need them.

     2. Do a second pass, rebuilding the environment and unifying constraints.

      Environment is rebuilt with the types obtained after substitution.
      For each type in the unify list, instantiate it in its local
      environment and unify it with the constrained type.
  *)
  let name_match name (qname,_) = name = qname

  (* A tree of constraints, sub levels correspond to constraints applied to sub
     modules *)
  type ('n,'cstr) t =
    | Local of 'cstr
    | Sub of ('n,'cstr) ts
  and ('n,'cstr) ts = ('n * ('n,'cstr) t) list

  let local_constraint = function
    | Local cstr -> cstr
    | Sub _ -> assert false

  let sub_constraints = function
    | Local _ -> assert false
    | Sub cstrs -> cstrs

  let rec add_constraint env acc = function
    | [], _ ->
        assert false
    | [x], c ->
        begin match (try Some (list_extract (name_match x) acc)
                     with Not_found -> None)
        with
        | None -> (x, Local c) :: acc
        | Some ((_x, c'), _) ->
            unify env (local_constraint c') c;
            acc
        end
    | (x :: xs), c ->
        let (x, cstr), acc =
          try list_extract (name_match x) acc
          with Not_found -> (x, Sub []), acc
        in
        let cstr = sub_constraints cstr in
        (x, Sub (add_constraint env cstr (xs, c))) :: acc

  let split_constraints env l =
    List.fold_left (add_constraint env) [] l

  (* Register possibly recursive definitions in environment
     (again, we need a populated environment because find_modtype_expansion
      might need to lookup local definitions ) *)
  let register_items env
    : Types.signature_item list -> Env.t
    = function
    | Sig_type (id, ty, (Trec_not | Trec_first)) :: items ->
        let rec aux env id ty items =
          let env = Env.add_type ~check:false id ty env in
          match items with
          | Sig_type (id, ty, Trec_next) :: items ->
              aux env id ty items
          | _ -> env
        in
        aux env id ty items
    | Sig_module (id, decl, (Trec_not | Trec_first)) :: items ->
        let rec aux env id decl items =
          let env = Env.add_module_declaration id decl env in
          match items with
          | Sig_module (id, decl, Trec_next) :: items ->
              aux env id decl items
          | _ -> env
        in
        aux env id decl items
    | Sig_modtype (id,mtd) :: _ ->
        Env.add_modtype id mtd env
    | _ -> env

  let rec prepare_mty
    : Env.t -> (string, type_expr) ts -> Types.module_type ->
      (Ident.t, type_expr) ts * Types.module_type
    = fun env cstrs mty ->
    if cstrs = [] then [], mty else
      match mty with
      | Mty_functor _ | Mty_alias _ -> assert false
      | Mty_ident p ->
          begin try
            let mty = Env.find_modtype_expansion p env in
            prepare_mty env cstrs mty
          with Not_found ->
            assert false
          end
      | Mty_signature sg ->
          let to_unify, sg' = prepare_sig env cstrs sg in
          to_unify, Mty_signature sg'

  and prepare_sig_item env cstrs field =
    match field with
    | Sig_value _ | Sig_class _ | Sig_modtype _
    | Sig_class_type _ | Sig_typext _ ->
        [], cstrs, field
    | Sig_type (id,decl,recst) ->
        let name = Ident.name id in
        begin try
          let (_, cstr), cstrs = list_extract (name_match name) cstrs in
          let ty = local_constraint cstr in
          let to_unify =
            match decl.type_manifest with
            | None -> []
            | Some ty' -> [(id, Local ty')]
          in
          to_unify, cstrs,
          Sig_type (id,{decl with type_manifest = Some ty}, recst)
        with Not_found ->
          [], cstrs, field
        end
    | Sig_module (id,decl,recst) ->
        let name = Ident.name id in
        begin try
          let (_, subs), cstrs = list_extract (name_match name) cstrs in
          let subs = sub_constraints subs in
          let subs, mty = prepare_mty env subs decl.md_type in
          let to_unify = match subs with
            | [] -> []
            | subs -> [(id, Sub subs)]
          in
          to_unify, cstrs,
          Sig_module (id,{decl with md_type = mty}, recst)
        with Not_found ->
          [], cstrs, field
        end

  and prepare_sig' env to_unify fields cstrs items =
    let env = register_items env items in
    match items, cstrs with
    | items, [] ->
        List.rev to_unify,
        List.rev_append fields items
    | [], cstrs ->
        let txt = String.concat ", " (List.map fst cstrs) in
        failwith ("constraints " ^ txt ^ " failed to apply")
    | item :: items, cstrs ->
        let to_unify', cstrs, item' = prepare_sig_item env cstrs item in
        prepare_sig' env (to_unify' @ to_unify) (item' :: fields) cstrs items

  and prepare_sig
    : Env.t -> (string, type_expr) ts -> Types.signature ->
      (Ident.t, type_expr) ts * Types.signature
    = fun env cstrs sg ->
    if cstrs = [] then
      [], sg
    else
      prepare_sig' env [] [] cstrs sg

  let rec constraint_mty env to_unify mty =
    if to_unify <> [] then
      match mty with
      | Mty_functor _ | Mty_alias _ | Mty_ident _ -> assert false
      | Mty_signature sg ->
          constraint_sig env to_unify sg

  and constraint_sig_item env cstrs field =
    match field, cstrs with
    | Sig_type (id,decl,recst),
      ((id', Local ty') :: cstrs) when Ident.same id id' ->
        let ty = match decl.type_manifest with
          | None -> assert false (* filled in previous pass *)
          | Some ty -> ty
        in
        let ty' = instance env ty' in
        unify env ty ty';
        cstrs

    | Sig_module (id,decl,recst),
      ((id', Sub subs) :: cstrs) when Ident.same id id' ->
        constraint_mty env subs decl.md_type;
        cstrs

      | _ -> cstrs

  and constraint_sig env cstrs items =
    let env = register_items env items in
    match items, cstrs with
    | _, [] -> ()
      (* generated constraints should all have been satisfied *)
    | [], _ -> assert false
    | item :: items, cstrs ->
        let cstrs = constraint_sig_item env cstrs item in
        constraint_sig env cstrs items

  let apply env mty cstrs =
    let cstrs = split_constraints env cstrs in
    let to_unify, mty = prepare_mty env cstrs mty in
    constraint_mty env to_unify mty;
    mty

  let apply_abstract env mty cstrs =
    let cstrs = split_constraints env cstrs in
    let to_unify, mty = prepare_mty env cstrs mty in
    assert (to_unify = []);
    mty

  let flatten ~root cstrs =
    let flatten_cstr (n,t) =
      let id', dots = Path.flatten n in
      assert (Ident.same root id');
      assert (dots <> []);
      List.map fst dots, t
    in
    List.map flatten_cstr cstrs

  (* Apply a list of equations to a list of targets.
     Types referred to by paths *must* be abstract. *)
  let targets
    : Env.t -> target list -> (Path.t * type_expr) list -> target list
    = fun env targets constraints ->
    (* [env] is needed only to expand module type names *)
    let register_constraint table (path, ty) =
      let id, path = Path.flatten path in
      let path = List.map fst path in
      let cstrs =
        try Ident.find_same id table
        with Not_found -> []
      in
      Ident.add id ((path, ty) :: cstrs) table
    in
    let constraint_table =
      List.fold_left register_constraint Ident.empty constraints in
    let constraint_target (targets,env) target =
      let target =
        try
          let cstrs = Ident.find_same target.target_id constraint_table in
          let mty = apply_abstract env target.target_type cstrs in
          {target with target_type = mty}
        with Not_found ->
          target
      in
      let env = Env.add_module target.target_id target.target_type env in
      (target :: targets, env)
    in
    let rtargets, _env = List.fold_left constraint_target ([],env) targets in
    List.rev rtargets

end

(* Various functions to preprocess pending implicit and implicit declarations
   when searching *)

let remove_type_variables () =
  let variables = ref [] in
  let it_type_expr it ty =
    let ty = repr ty in
    match ty.desc with
    | Tvar name when ty.level < generic_level ->
        let name = match name with
          | None -> "ex"
          | Some name -> name
        in
        let ident = Ident.create name in
        variables := (ty, ident) :: !variables;
        let ty' = newgenty (Tconstr (Path.Pident ident, [], ref Mnil)) in
        link_type ty ty'
    | _ -> type_iterators.it_type_expr it ty;
  in
  let it = {type_iterators with it_type_expr} in
  variables, it

(*let unify_equations env variables equations =
  List.iter (fun (ty, id) ->
           List.iter
             (function
          | Path.Pident id' as path, ty' when Ident.same id id' ->
              Format.fprintf Format.err_formatter "unifying %a with %a (= %a)\n%!"
                Printtyp.type_expr ty
                Printtyp.type_expr ty'
                Printtyp.path path;
              unify env ty ty'
          | _ -> ())
        equations
  ) variables*)

let target_of_pending inst =
  let env = inst.implicit_env in
  let ident = inst.implicit_id in
  let path, nl, tl = inst.implicit_type in
  (* Extract base module type *)
  let mtd = Env.find_modtype path env in
  let mty = match mtd.mtd_type with
                | None -> assert false
                | Some mty -> mty
  in
  let basekinded (ty,_tyvar) = match (repr ty).desc with
    | Tconstr (_, [], _) -> true
    | Tconstr (_, (_ :: _), _) -> false
    | _ -> assert false
  in
  let basepath (ty,tyvar) = match (repr ty).desc  with
    | Tconstr (path, [], _) -> path, tyvar
    | _ -> assert false
  in
  let bkt, hkt = List.partition basekinded inst.implicit_constraints in
  let bkt = List.map basepath bkt in
  let cstrs =
    (* Constraints from package type *)
    (List.map2 (fun n t -> Longident.flatten n, t) nl tl)
    (* Constraints from implicit instance *) @
    (Constraints.flatten ~root:ident bkt)
  in
  let mty = Constraints.apply env mty cstrs in
  let variables, it = remove_type_variables () in
  it.it_module_type it mty;
  List.iter (fun (ty,tyvar) ->
      it.it_type_expr it ty;
      it.it_type_expr it tyvar)
    hkt;
  let id = inst.implicit_id in
  !variables,
  {target_type = mty; target_id = id; target_uid = id; target_hkt = hkt}

let rec extract_implicit_parameters targets n omty nmty =
  assert (n >= 0);
  if n = 0 then
    List.rev targets, nmty
  else match omty, nmty with
    | Mty_functor (target_uid, Some _, omty'),
      Mty_functor (target_id, Some target_type, nmty') ->
        extract_implicit_parameters
        ({target_uid; target_id; target_type; target_hkt = []} :: targets) (n - 1) omty' nmty'
    | _ -> assert false

let find_implicit_parameters {Types. md_type = omty; md_implicit} =
  match md_implicit with
  | Asttypes.Nonimplicit -> assert false
  | Asttypes.Implicit 0 ->
      (* No copy, so we don't lose equality *)
      [], omty

  | Asttypes.Implicit arity ->
      let nmty = Subst.modtype Subst.identity omty in
      extract_implicit_parameters [] arity omty nmty

(** Termination checking **)
module Termination : sig

  (* A termination criterion is a set of constraints applying on a target_uid.
     It's satisfied in a given state iff its constraints are stronger than
     those found the state. *)
  type t
  type state
  val initial : state

  (* From a list of target and constraints applying on those targets,
     returns a termination criterion for each target *)
  val normalize_equations
    : target list -> (Path.t * type_expr) list -> (target * t) list

  (* [check env t state] ensures that termination criterion for [t] is
     satisfied in [state] and returns the stronger state.
     Otherwise, [Terminate] is raised *)
  exception Terminate
  val check : Env.t -> t -> state -> state

end = struct

  (* Set of equations used for computing termination criterion.
     The list of equations is sorted by path, and each path is unique. *)
  type eqns = (string list * type_expr) list

  let rec wellformed_eqns = function
    | (path1, _) :: ((path2, _) :: _ as tail) ->
      (path1 < path2) && wellformed_eqns tail
    | _ -> true

  (* Checking that an individial type is smaller than another one.
     The exception never escapes. *)
  exception Type_is_smaller
  let smaller env t1 t2 : [`Smaller | `Equal | `Different] =
    let rec check_ty t =
      if equal env true [t1] [t] then
        raise Type_is_smaller;
      iter_type_expr check_ty t
    in
    try if equal env true [t1] [t2]
      then `Equal
      else (iter_type_expr check_ty t2; `Different)
    with Type_is_smaller ->
      `Smaller

  (* Check that a set of equations is stronger than another one.
     [stronger env neqns oeqns] returns true iff
     - all equations from oeqns must be smaller or equal in neqns, AND
     - one equation must be strictly smaller or neqns must contain more
       equations. *)
  let rec stronger env acc (neqns : eqns) (oeqns : eqns) =
    match neqns, oeqns with
      (* Equation on same path, check inclusion of type *)
    | (n, nt) :: neqns, (o, ot) :: oeqns when n = o ->
        begin match smaller env nt ot with
        | `Equal -> stronger env acc neqns oeqns
        | `Smaller -> stronger env true neqns oeqns
        | `Different -> false
        end
      (* Same number of equations, at least one must have been stronger *)
    | [], [] -> acc
      (* More equations, always stronger *)
    | _, [] -> true
    | (n, _) :: neqns, (o, _) :: _ when n < o ->
      stronger env true neqns oeqns
      (* Less equations, always weaker *)
    | [], _ -> false
    | (n, _) :: neqns, (o, _) :: _  ->
      assert (n > o);
      false

  let stronger env neqns oeqns = stronger env false neqns oeqns

  (* Checking for termination starts from a target uid and a list of equations.
     A state is table mapping uids to the strongest set of equations seen so
     far. *)
  type t = Ident.t * eqns
  type state = eqns Ident.tbl
  let initial = Ident.empty

  let normalize_equations
      (* List of targets *)
      (targets : target list)
      (* All path must refer to some target_id *)
      (equations : (Path.t * type_expr) list)
      (* List of equations applying to each target *)
    : (target * t) list =
    (* Map target_id to target_uid *)
    let table = List.fold_left
        (fun table {target_id; target_uid} ->
           Ident.add target_id (target_uid,ref []) table)
        Ident.empty targets
    in
    (* Add equations to target_id *)
    List.iter
      (fun (path, eq) ->
         try
           let id, path = Path.flatten path in
           let path = List.map fst path in
           let _uid, eqns = Ident.find_same id table in
           eqns := (path, eq) :: !eqns
         with Not_found -> assert false)
      equations;
    List.map
      (fun target ->
         try
           let uid, eqns = Ident.find_same target.target_id table in
           let eqns = List.sort (fun (a,_) (b,_) -> compare a b) !eqns in
           assert (wellformed_eqns eqns);
           target, (uid, eqns)
         with Not_found -> assert false)
      targets

  exception Terminate
  let check env (uid, eqns) stack =
    let eqns' =
      try Ident.find_same uid stack
      with Not_found -> []
    in
    if not (stronger env eqns eqns') then raise Terminate;
    Ident.add uid eqns stack

end

let report_error exn =
  try
    Location.report_exception Format.err_formatter exn
  with exn ->
    Printf.eprintf "%s\n%!" (Printexc.to_string exn)

(* Make the search stack explicit.
end

   This helps resuming search (e.g to search for ambiguity), explaining search
   state or errors, etc. *)
(** TODO **)

module Search : sig

  type candidate = Path.t * Types.module_declaration

  type query
  type partial
  type result

  val get : result -> Path.t
  val equations : result -> (Path.t * type_expr) list

  val all_candidates : query -> candidate list

  val start : Env.t -> Ident.t list -> target -> query

  type outcome = [
    | `Done of result
    | `Step of partial * query
  ]

  val step : query -> candidate list -> outcome * candidate list
  val apply : partial -> result -> outcome

end = struct

  type candidate = Path.t * Types.module_declaration

  type 'a state =
    {
      payload: 'a;
      termination: Termination.state;
      target: target;
      env: Env.t;

      (* Equality snapshots.

         When resuming a search from this state,
         [eq_var] should be set to [eq_initial].

         [eq_var] is referenced in [eq_table], so new equations valid in this
         branch of the search will be added to [eq_var]. *)
      eq_initial: (Path.t * type_expr) list;
      eq_var: (Path.t * type_expr) list ref;
      eq_table: (Path.t * type_expr) list ref Ident.tbl;
    }

  type query =
    (* Start point for a search, a state without other information attached *)
    unit state

  type partial =
    (* Intermediate result: a path has been found, but some arguments are
       missing and need to be applied *)
    (Path.t * (target * Termination.t) list) state

  type result =
    (* Final result: the path points to a module with the desired type *)
    Path.t state

  let get t = t.payload

  let equations t = t.eq_initial

  type outcome = [
    | `Done of result
    | `Step of partial * query
  ]

  let start env vars target =
    let level = get_current_level () in
    let env = List.fold_left (fun env variable ->
        Env.add_type ~check:false variable
          (new_declaration (Some (level, level)) None) env)
        env vars
    in
    let eq_var = ref [] in
    let eq_table = List.fold_left
        (fun tbl id -> Ident.add id eq_var tbl)
        Ident.empty vars
    in
    {
      payload = ();
      termination = Termination.initial;
      target = target;
      env = env;

      eq_initial = [];
      eq_var = eq_var;
      eq_table = eq_table;
    }

  let all_candidates t =
    Env.implicit_instances t.env

  let step0 state (path, md) =
    state.eq_var := state.eq_initial;
    let target = state.target in
    let sub_targets, candidate = find_implicit_parameters md in
    let new_eqns = ref [] in
    (* Generate coercion. if this succeeds this produce equations in new_eqns and eq_var *)
    let eq_table, env = List.fold_left
        (fun (eq_table, env) {target_id} ->
          Ident.add target_id new_eqns eq_table,
          Env.add_module target.target_id target.target_type env)
        (state.eq_table, state.env) sub_targets
    in
    let accepting_eq = Ident.fold_all
        (fun ident _ acc -> Ident.name ident :: acc)
        eq_table []
    in
    Format.fprintf Format.err_formatter "Starting from equations on %s:\n%!"
      (String.concat ", " accepting_eq);
    List.iter (fun (path,ty) ->
        Format.fprintf Format.err_formatter "\t%a = %a\n%!"
          Printtyp.path path
          Printtyp.type_expr ty)
      !(state.eq_var);
    Ctype.with_equality_equations eq_table
      (fun () ->
        let subst = Subst.add_module target.target_id path Subst.identity in
        let tyl, tvl = List.split target.target_hkt in
        let tyl = List.map (Subst.type_expr subst) tyl in
        let tvl = List.map (Subst.type_expr subst) tvl in
        begin try Ctype.equal' env false tyl tvl
        with Ctype.Unify tls ->
          Format.fprintf Format.err_formatter "Failed to instantiate:\n";
          List.iter2 (fun t1 t2 ->
              Format.fprintf Format.err_formatter "\t%a = %a\n%!"
                Printtyp.type_expr t1
                Printtyp.type_expr t2)
            tyl tvl;
          Format.fprintf Format.err_formatter "With equations on %s:\n%!"
            (String.concat ", " accepting_eq);
          List.iter (fun (path,ty) ->
              Format.fprintf Format.err_formatter "\t%a = %a\n%!"
                Printtyp.path path
                Printtyp.type_expr ty)
            !(state.eq_var);
          Format.fprintf Format.err_formatter "Because:\n%!";
          List.iter (fun (ty1,ty2) ->
              let rec find_aliases acc ty = match (repr ty).desc with
                | Tconstr (path,args,_)  ->
                    let acc = try
                        let _args,ty',_ = Env.find_type_expansion path env in
                        (ty,ty') :: acc
                      with Not_found -> (ty,ty) :: acc
                    in
                    List.fold_left find_aliases acc args
                | _ -> acc
              in
              let aliases = find_aliases [] ty1 in
              let aliases = find_aliases aliases ty2 in
              List.iter (fun (ty1,ty2) ->
                  Format.fprintf Format.err_formatter " %a ~ %a;"
                    Printtyp.type_expr ty1
                    Printtyp.type_expr ty2)
                aliases;
              Format.fprintf Format.err_formatter "\n\t%a != %a \n%!"
                Printtyp.type_expr ty1
                Printtyp.type_expr ty2)
            tls;
          raise Not_found
        end;
        let _ : module_coercion =
          Includemod.modtypes env candidate target.target_type
        in
        ());
    let eqns = !new_eqns in
    (* Constraints target types *)
    let sub_targets = Constraints.targets state.env sub_targets eqns in
    (* Add termination criteria *)
    let sub_targets = Termination.normalize_equations sub_targets eqns in

    (* Keep new equations potentially added to top variables *)
    let state = {state with eq_initial = !(state.eq_var)} in
    match sub_targets with
    | [] ->
      `Done {state with payload = path}
    | (target, crit) :: sub_targets ->
      let partial = {state with payload = (path, sub_targets)} in
      let termination = Termination.check state.env crit state.termination in
      let state = {state with target; termination} in
      `Step (partial, state)

  let rec step state = function
    | [] -> raise Not_found
    | candidate :: candidates ->
      try
        step0 state candidate, candidates
      with
      | Termination.Terminate as exn -> raise exn
      | exn ->
        report_error exn;
        step state candidates

  let apply partial arg =
    let partial_path, sub_targets = partial.payload in
    let arg_path = arg.payload in
    let path = papply partial_path arg_path in
    match sub_targets with
    | [] ->
      let state = {partial with
                   payload = path;
                   (* We get the equations from the argument but keep
                      termination state from the parent *)
                   eq_initial = arg.eq_initial} in
      `Done state
    | (target, crit) :: sub_targets ->
      let partial = {partial with payload = (path, sub_targets)} in
      let md = Env.find_module path arg.env in
      (* The original module declaration might be implicit, we want to avoid
         rebinding implicit *)
      let md = {md with md_implicit = Asttypes.Nonimplicit} in
      let termination = Termination.check arg.env crit partial.termination in
      let env = Env.add_module_declaration target.target_id md arg.env in
      let arg = {arg with payload = (); target; termination; env} in
      `Step (partial, arg)
end

module Solution = struct

  type t = {
    (* The original query *)
    query: Search.query;

    (* If we want to resume search, start from these candidates *)
    next: Search.candidate list;

    (* Intermediate steps with solutions to subquerys *)
    steps: (Search.partial * t) list;

    result: Search.result;
  }

  let rec search query =
    search_candidates query (Search.all_candidates query)

  and search_candidates query candidates =
    let step, next = Search.step query candidates in
    search_arguments query next [] step

  and search_arguments query next steps = function
    | `Done result ->
      {query; next; steps; result}
    | `Step (partial,subquery) ->
      apply_argument query next steps partial (search subquery)

  and apply_argument query next steps partial solution =
    search_arguments query next
      ((partial, solution) :: steps)
      (Search.apply partial solution.result)

  let rec search_next_steps solution = function
    | ((partial, step) :: steps) ->
      begin try
        let {query; next; _} = solution in
        apply_argument query next steps partial (search_next step)
      with Not_found ->
        search_next_steps solution steps
      end
    | [] ->
      search_candidates solution.query solution.next

  and search_next solution = search_next_steps solution solution.steps

  let get {result} = Search.get result
end

let find_pending_instance inst =
  let snapshot = Btype.snapshot () in
  let vars, target = target_of_pending inst in
  let env = inst.implicit_env in
  let env = List.fold_left (fun env (_ty,ident) ->
      (* Create a fake abstract type declaration for name. *)
      let level = get_current_level () in
      let decl = {
        type_params = [];
        type_arity = 0;
        type_kind = Type_abstract;
        type_private = Asttypes.Public;
        type_manifest = None;
        type_variance = [];
        type_newtype_level = Some (level, level);
        type_loc = Location.none;
        type_attributes = [];
      }
      in
      Env.add_type ~check:false ident decl env
    ) env vars
  in
  let loc = inst.implicit_loc in
  let query = Search.start env (List.map snd vars) target in
  try
    let solution = Solution.search query in
    let alternative =
      try Some (Solution.search_next solution)
      with _ -> None
    in
    match alternative with
    | None ->
      Btype.backtrack snapshot;
      (* Not needed, since Link.to_path should do the proper checks:
         unify_equations env fvars (Search.equations result);*)
      Link.to_path inst (Solution.get solution);
      true
    | Some alternative ->
      let p1 = Solution.get solution in
      let p2 = Solution.get alternative in
      raise Typecore.(Error (loc, env, Ambiguous_implicit (inst,p1,p2)))
  with
  | Termination.Terminate ->
    raise Typecore.(Error (loc, env, Termination_fail inst))

(* Pack module at given path to match a given implicit instance and
   update the instance to point to this module.
   Return the correct package if any.
*)
let pack_implicit inst path =
  let { implicit_type = p,nl,tl;
        implicit_env  = env;
        implicit_loc  = loc } = inst in
  let rec translpath = function
    | Path.Pident _ | Path.Pdot _ as path ->
        let md = Env.find_module path env in
        let lident = Location.mkloc (Path.to_longident path) loc in
        {
          mod_desc = Tmod_ident (path, lident);
          mod_loc = loc;
          mod_type = md.md_type;
          mod_env = env;
          mod_attributes = [];
        }
    | Path.Papply (p1,p2) ->
        let mfun = translpath p1 and marg = translpath p2 in
        match mfun.mod_type with
        | Mty_functor (param, Some mty_param, mty_res) ->
            let coercion = Includemod.modtypes env marg.mod_type mty_param in
            let mty_appl = Subst.modtype
                (Subst.add_module param path Subst.identity)  mty_res
            in
            { mod_desc = Tmod_apply(mfun, marg, coercion);
              mod_type = mty_appl;
              mod_env = env;
              mod_attributes = [];
              mod_loc = loc;
            }
        | _ -> assert false
  in
  let modl = translpath path in
  let (modl, tl') = !type_implicit_instance env modl p nl tl in
  {
    exp_desc = Texp_pack modl;
    exp_loc = loc; exp_extra = [];
    exp_type = newty (Tpackage (p, nl, tl'));
    exp_attributes = [];
    exp_env = env;
  }

let () =
  Typeimplicit.pack_implicit_ref := pack_implicit

let generalize_implicits () =
  let current_level = get_current_level () in
  let not_linked = function
    | {implicit_argument = {arg_expression = Some _}} -> false
    | _ -> true
  in
  let pending = List.filter not_linked !pending_implicits in
  let need_generalization inst =
    List.exists
      (fun (ty,var) ->
         assert (var.level <> generic_level);
         max ty.level var.level >= current_level)
      inst.implicit_constraints
    || inst.implicit_constraints = []
  in
  let to_generalize, rest =
    List.partition need_generalization pending
  in
  pending_implicits := rest;
  (* The reversal is important to ensure we search from the outer most
     to the inner most implicits *)
  let to_generalize = List.rev to_generalize in
  try
    let not_instantiable inst = not (find_pending_instance inst) in
    let inst = List.find not_instantiable to_generalize in
    let loc = inst.implicit_loc in
    let env = inst.implicit_env in
    raise Typecore.(Error (loc, env, No_instance_found inst))
  with Not_found -> ()

let () =
  Typeimplicit.generalize_implicits_ref := generalize_implicits
