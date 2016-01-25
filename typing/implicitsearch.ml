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

let rec list_filtermap f = function
  | [] -> []
  | x :: xs ->
      match f x with
      | None -> list_filtermap f xs
      | Some x' -> x' :: list_filtermap f xs

let string_of_path path =
  Path.to_longident path |> Longident.flatten |> String.concat "."

let has_suffix ~suffix str =
  let l = String.length str and n = String.length suffix in
  l >= n &&
  try
    for i = 0 to n - 1 do
      if str.[l - n + i] <> suffix.[i] then
        raise Exit
    done;
    true
  with Exit -> false

let papply path arg = Path.Papply (path, arg, Asttypes.Implicit)

(** [goal] is the point from which a search starts *)
type goal = {
  (* The module type we try to find an instance for *)
  goal_type : Types.module_type;
  (* The identifier to which the result of the search will be bound.
     E.g we are trying to fill the hole in:
       module %goal_id : %goal_type = _ *)
  goal_var : Ident.t;

  (* Constraints that should be satisfied by a solution.  That is when a
     concrete module is bound to goal_var, equalities in goal_constraints
     should be true. *)
  goal_constraints : (type_expr * type_expr) list;

  (* A unique identifier that will be used for termination checking.  When the
     goal is the argument to a functor instantiation, if this functor is
     instantiated multiple times we enforce that the constraints on the
     argument are stronger.

     Pair (Arg_1) (Pair (Arg_1') (Arg_2))

     Arg_1 and Arg_1' targets will have a different goal_var but the same
     goal_uid.  We check that constraints on Arg_1' are stronger than those
     on Arg_1'.

     Note: This is also true of (Pair (Arg_1') (Arg_2)) and Arg_2, used as
     second arguments to Pair.  *)
  goal_termination_id : Ident.t;
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

  (* Apply a list of equations to a goal.
     Types referred to by paths *must* be abstract. *)
  let goal
    : Env.t -> goal -> equality_equation list -> goal
    = fun env goal eqns ->
    (* [env] is needed only to expand module type names *)
    let extract_constraint acc eqn =
      let id, path = Path.flatten eqn.eq_lhs_path in
      if not (Ident.same id goal.goal_var) then
        acc
      else
        let path = List.map fst path in
        let rec is_row = function
          | [t] -> has_suffix ~suffix:"#row" t
          | _ :: xs -> is_row xs
          | [] -> assert false
        in
        let cstrs, hkt = acc in
        if eqn.eq_lhs_params = [] && not (is_row path) then
          ((path, eqn.eq_rhs) :: cstrs), hkt
        else
          cstrs, ((eqn.eq_lhs, eqn.eq_rhs) :: hkt) in
    let cstrs, hkt = List.fold_left extract_constraint ([],[]) eqns in
    let mty = apply_abstract env goal.goal_type cstrs in
    let goal = {goal with goal_type = mty;
                   goal_constraints = hkt @ goal.goal_constraints} in
    goal

end

(* Various functions to preprocess pending implicit and implicit declarations
   when searching *)

let remove_type_variables () =
  let k = ref 0 in
  let variables = ref [] in
  let it_type_expr it ty =
    let ty = repr ty in
    if ty.level >= lowest_level then begin
      match ty.desc with
      | Tvar name when ty.level < generic_level ->
          let name = match name with
            | None -> "ex" ^ string_of_int (incr k; !k)
            | Some name -> name
          in
          let ident = Ident.create name in
          variables := (ty, ident) :: !variables;
          let ty' = newgenty (Tconstr (Path.Pident ident, [], ref Mnil)) in
          link_type ty ty';
          mark_type_node ty
      | _ ->
          mark_type_node ty;
          type_iterators.it_do_type_expr it ty;
    end
  in
  let it = {type_iterators with it_type_expr} in
  variables, it

(*let unify_equations env variables equations =
  List.iter (fun (ty, id) ->
           List.iter
             (function
          | Path.Pident id' as path, ty' when Ident.same id id' ->
              printf "unifying %a with %a (= %a)\n%!"
                Printtyp.type_expr ty
                Printtyp.type_expr ty'
                Printtyp.path path;
              unify env ty ty'
          | _ -> ())
        equations
  ) variables*)

let goal_of_pending inst =
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
  unmark_iterators.it_module_type unmark_iterators mty;
  List.iter (fun (ty,tyvar) ->
      unmark_type ty;
      unmark_type tyvar)
    hkt;
  let id = inst.implicit_id in
  !variables,
  {goal_type = mty;
   goal_var = id;
   goal_termination_id = id;
   goal_constraints = hkt}

(** Termination checking **)
module Termination : sig

  (* A termination criterion is a set of constraints applying on a
     goal_termination_id.
     It's satisfied in a search state iff its constraints are stronger than
     those found the search state. *)
  type t
  type state
  val initial : state

  (* From a goal and an initial list of constraints,
     build a termination criterion *)
  val normalize_equations
    : goal -> equality_equation list -> t

  (* [check env t state] ensures that termination criterion for [t] is
     satisfied in [state] and returns the stronger state.
     Otherwise, [Terminate] is raised *)
  type eqns = (string list * (type_expr list * type_expr) list) list
  exception Terminate of (Ident.t * eqns * eqns)
  val explain : bool -> Format.formatter -> Ident.t * eqns * eqns -> unit

  val check : Env.t -> t -> state -> state

  val check_goal : Env.t -> goal -> equality_equation list -> state -> state
end = struct

  (* Set of equations used for computing termination criterion.
     The list of equations is sorted by path, and each path is unique. *)
  type eqns = (string list * (type_expr list * type_expr) list) list

  let rec merge_eqns = function
    | (path1, args) :: (path2, args') :: tail when path1 = path2 ->
      merge_eqns ((path1, args' @ args) :: tail)
    | head :: tail ->
      head :: merge_eqns tail
    | [] -> []

  let rec wellformed_eqns = function
    | (path1, args) :: ((path2, _) :: _ as tail) ->
      (path1 < path2) &&
      (match args with
      (* One base-kinded *)
      | [[], _] -> true
      (* Or one-or-more higher-kinded, same arity *)
      | (((_ :: _), _ as first) :: rest) ->
        let arity (params,_path) = List.length params in
        let a0 = arity first in
        assert (List.for_all (fun t -> arity t = a0) rest);
        true
      | _ -> false) &&
      wellformed_eqns tail
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

  let smaller env t1 t2 : [`Smaller | `Equal | `Different] =
    match smaller env t1 t2 with
    | (`Equal | `Different) as r -> r
    | `Smaller ->
      match smaller env t2 t1 with
      | `Smaller -> `Different (* t1 < t2 && t2 < t1 *)
      | _ -> `Smaller

  let smallers env t1s t2s : [`Smaller | `Equal | `Different] =
    try
      let rec aux t2s acc = function
        | [] -> acc
        | (params, t1) :: t1s ->
          let (params', t2), t2s = list_extract
              (fun (params', t2) -> equal env true params params')
              t2s in
          match smaller env t1 t2 with
          | `Different -> raise Not_found
          | `Equal -> aux t2s acc t1s
          | `Smaller -> aux t2s `Smaller t1s
      in
      aux t2s `Equal t1s
    with Not_found ->
      `Different

  (* Check that a set of equations is stronger than another one.
     [stronger env neqns oeqns] returns true iff
     - all equations from oeqns must be smaller or equal in neqns, AND
     - one equation must be strictly smaller or neqns must contain more
       equations. *)
  let rec stronger env acc (neqns : eqns) (oeqns : eqns) =
    let is_base_kinded = function
      | _, [[], _] -> true
      | _, _ -> false in
    match neqns, oeqns with
      (* Equation on same path, check inclusion of type *)
      (* Base-kinded *)
    | (n, [[], nt]) :: neqns, (o, [[], ot]) :: oeqns when n = o ->
        begin match smaller env nt ot with
        | `Equal -> stronger env acc neqns oeqns
        | `Smaller -> stronger env true neqns oeqns
        | `Different -> false
        end
      (* Higher-kinded *)
    | (n, nt) :: neqns, (o, ot) :: oeqns when n = o ->
        begin match smallers env nt ot with
        | `Equal -> stronger env acc neqns oeqns
        | `Smaller -> stronger env true neqns oeqns
        | `Different -> false
        end
      (* Same number of equations, at least one must have been stronger *)
    | [], [] -> acc
      (* More equations, stronger if base-kinded *)
    | _, [] -> List.exists is_base_kinded neqns
    | (n, _ as neqn) :: neqns, (o, _) :: _ when n < o && is_base_kinded neqn ->
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
      (* Goal *)
      (goal : goal)
      (* All path must refer to some goal_var *)
      (eqns : equality_equation list)
      (* List of equations applying to goal *)
    : t =
    (* Add equations to goal_var *)
    let eqns = list_filtermap
        (fun eqn ->
          let id, path = Path.flatten eqn.eq_lhs_path in
          if not (Ident.same goal.goal_var id) then
            None
          else
            let path = List.map fst path in
            Some (path, [eqn.eq_lhs_params, eqn.eq_rhs]))
        eqns in
    let eqns = List.sort (fun (a,_) (b,_) -> compare a b) eqns in
    let eqns = merge_eqns eqns in
    assert (wellformed_eqns eqns);
    (goal.goal_termination_id, eqns)

  let explain success ppf (id,eqns,eqns') =
    let print_ppath ppf (path,params) = match params with
      | [] -> Format.pp_print_string ppf path
      | [p] -> Format.fprintf ppf "%a %s" Printtyp.type_expr p path
      | (p::ps) -> Format.fprintf ppf "(%a%a) %s"
                     Printtyp.type_expr p
                     (fun ppf -> List.iter (fun ty ->
                         Format.fprintf ppf ", %a" Printtyp.type_expr ty))
                     ps
                     path in
    let print_eqn ppf path (params,ty) =
      Format.fprintf ppf "\t%a = %a\n"
        print_ppath (path,params)
        Printtyp.type_expr ty in
    let print_eqns_at_path ppf (path,eqns) =
      let path = String.concat "." path in
      List.iter (print_eqn ppf path) eqns in
    let print_eqns ppf peqns = List.iter (print_eqns_at_path ppf) peqns in
    if eqns' = [] && success then
      Format.fprintf ppf
        "Termination of %a: introducing equation set [\n%a]\n%!"
        Printtyp.ident id
        print_eqns eqns
    else
      Format.fprintf ppf
        "Termination of %a: equation set [\n%a] is %sstronger than [\n%a]\n%!"
        Printtyp.ident id
        print_eqns eqns
        (if success then "" else "not ")
        print_eqns eqns'

  exception Terminate of (Ident.t * eqns * eqns)
  let check env (uid, eqns) stack =
    begin try
      let eqns' = Ident.find_same uid stack in
      if not (stronger env eqns eqns') then raise (Terminate (uid, eqns, eqns'));
      explain true printf_output (uid,eqns,eqns')
    with Not_found ->
      explain true printf_output (uid,eqns,[])
    end;
    Ident.add uid eqns stack

  let check_goal env goal eqns stack =
    let t = normalize_equations goal eqns in
    check env t stack
end

let report_error msg exn =
  try
    Location.report_exception printf_output exn
  with exn ->
    printf "%s%s\n%!" msg (Printexc.to_string exn)

(* Make the search stack explicit.

   This helps resuming search (e.g to search for ambiguity), explaining search
   state or errors, etc. *)

module Search : sig

  type candidate = Path.t * goal list * Types.module_type

  type query
  type partial
  type result

  val get : result -> Path.t
  val equations : result -> equality_equation list

  val all_candidates : query -> candidate list

  val start : Env.t -> Ident.t list -> goal -> query

  type outcome = [
    | `Done of result
    | `Step of partial * query
  ]

  val step : query -> candidate list -> outcome * candidate list
  val apply : partial -> result -> outcome

end = struct

  type candidate = Path.t * goal list * Types.module_type

  type 'a state =
    {
      payload: 'a;
      termination: Termination.state;
      goal: goal;
      env: Env.t;

      (* List of partials paths being constructed, only for debug purpose *)
      debug_path: Path.t list;

      (* Equality snapshots.

         When resuming a search from this state,
         [eq_var] should be set to [eq_initial].

         [eq_var] is referenced in [eq_table], so new equations valid in this
         branch of the search will be added to [eq_var]. *)
      eq_initial: equality_equation list;
      eq_var: equality_equation list ref;
      eq_table: (Ident.t, equality_equation list ref) Tbl.t;
    }

  type query =
    (* Start point for a search, a state without other information attached *)
    unit state

  type partial =
    (* Intermediate result: a path has been found, but some arguments are
       missing and need to be applied *)
    (Path.t * goal list) state

  type result =
    (* Final result: the path points to a module with the desired type *)
    Path.t state

  let get t = t.payload

  let equations t = t.eq_initial

  type outcome = [
    | `Done of result
    | `Step of partial * query
  ]

  let start env vars goal =
    let level = get_current_level () in
    let env = List.fold_left (fun env variable ->
        Env.add_type ~check:false variable
          (new_declaration (Some (level, level)) None) env)
        env vars
    in
    let eq_var = ref [] in
    let eq_table = List.fold_left
        (fun tbl id -> Tbl.add id eq_var tbl)
        Tbl.empty vars
    in
    {
      payload = ();
      termination = Termination.initial;
      goal = goal;
      env = env;

      debug_path = [];

      eq_initial = [];
      eq_var = eq_var;
      eq_table = eq_table;
    }

  let make_candidate path params mty =
    let rec loop path res s acc = function
      | [] -> path, List.rev acc, Subst.modtype s res
      | (id, param) :: rest ->
          let param' = Subst.modtype s param in
          let id' = Ident.rename id in
          let s' = Subst.add_module id (Path.Pident id') s in
          let goal = {
            goal_var = id';
            goal_type = param';
            goal_constraints = [];
            goal_termination_id = id;
          } in
          let acc' = goal :: acc in
            loop path res s' acc' rest
    in
      loop path mty Subst.identity [] params

  let make_candidate (path, params, mty) =
    match params with
    | [] -> (path, [], mty)
    | params -> make_candidate path params mty

  let all_candidates t =
    List.map make_candidate (Env.implicit_instances t.env)

  let cleanup_equations ident eq_table =
    try
      let eqns = Tbl.find ident eq_table in
      let not_in_ident {eq_lhs_path} = Path.head eq_lhs_path <> ident in
      eqns := List.filter not_in_ident !eqns;
      Tbl.remove ident eq_table
    with Not_found -> eq_table

  exception Invalid_candidate

  let step0 state (path, sub_goals, candidate_mty) =
    state.eq_var := state.eq_initial;
    let rec print_paths ppf = function
      | [] -> Format.pp_print_string ppf "_";
      | p :: ps -> Format.fprintf ppf "%a (%a)" Printtyp.path p print_paths ps
    in
    let print_paths ppf ps = print_paths ppf (List.rev ps) in
    printf "%a <- %a\n" print_paths state.debug_path Printtyp.path path;
    let goal = state.goal in
    (* Generate coercion. if this succeeds this produce equations in eq_var *)
    let eq_table, env = List.fold_left
        (fun (eq_table, env) sub_goal ->
          printf "Binding %a with type %a\n%!"
            Printtyp.ident sub_goal.goal_var
            Printtyp.modtype sub_goal.goal_type;
          Tbl.add sub_goal.goal_var state.eq_var eq_table,
          Env.add_module sub_goal.goal_var sub_goal.goal_type env)
        (state.eq_table, state.env) sub_goals
    in
    let env = Env.add_module goal.goal_var candidate_mty env in
    Ctype.with_equality_equations eq_table
      (fun () ->
        let tyl, tvl = List.split goal.goal_constraints in
        begin try
          if tyl <> [] then
            printf "Checkinq equalities between hkt constraints:\n%!";
          List.iter2 (fun t1 t2 ->
            printf "\t%a = %a\n%!"
              Printtyp.type_expr t1
              Printtyp.type_expr t2)
            tyl tvl;
          Ctype.equal' env true tyl tvl
        with Ctype.Unify tls ->
          printf "Failed to instantiate %s with constraints:\n"
            (string_of_path path);
          let accepting_eq = Tbl.fold
              (fun ident _ acc -> Ident.name ident :: acc)
              eq_table []
          in
          printf "Assuming the following equalities on %s:\n"
            (String.concat ", " accepting_eq);
          List.iter (fun {eq_lhs; eq_rhs} ->
              printf "\t%a = %a\n%!"
                Printtyp.type_expr eq_lhs Printtyp.type_expr eq_rhs)
            !(state.eq_var);
          printf "Because:\n%!";
          List.iter (fun (ty1,ty2) ->
              printf "\t%a != %a\n%!"
                Printtyp.type_expr ty1
                Printtyp.type_expr ty2;
              let rec check_expansion ty = match (repr ty).desc with
                | Tconstr (path,args,_)  ->
                    begin try
                      ignore (Env.find_type_expansion path env : _ * _ *_)
                    with Not_found -> try
                      ignore (Env.find_type path env : _)
                    with Not_found ->
                      printf "Fatal error: %a not found.\n%!"
                        Printtyp.path path
                    end;
                    List.iter check_expansion args
                | _ -> ()
              in
              check_expansion ty1;
              check_expansion ty2;
              printf "\n%!"
            ) tls;
          raise Invalid_candidate
        end;
        let _ : module_coercion =
          Includemod.modtypes env candidate_mty goal.goal_type
        in
        ());
    let rec neweqns = function
      | l when l == state.eq_initial -> []
      | [] -> []
      | x :: xs -> x :: neweqns xs
    in
    let eq_final = !(state.eq_var) in
    let neweqns = neweqns eq_final in
    let print_eqn {eq_lhs; eq_rhs} =
      printf "\t%a = %a\n%!"
        Printtyp.type_expr eq_lhs
        Printtyp.type_expr eq_rhs
    in
    if eq_final != state.eq_initial then
      (printf "Equations produced:\n";
       List.iter print_eqn neweqns)
    else
      printf "No equations produced.\n";


    (* Pass the env will all arguments bound to next state: constraints
       might be referring to other modules in any order, e.g in
       functor F (X : T) (Y : S) = ...

       we might have type t = Y.t X.t as a constraint on X *)
    let eq_table = cleanup_equations goal.goal_var eq_table in

    (* Keep new equations potentially added to top variables *)
    let state = {state with eq_initial = eq_final; env; eq_table = eq_table} in
    match sub_goals with
    | [] ->
      `Done {state with payload = path}
    | goal :: sub_goals ->
      let debug_path = state.debug_path in
      let partial = {state with payload = (path, sub_goals)} in
      let goal = Constraints.goal state.env goal eq_final in
      let termination =
        Termination.check_goal state.env goal eq_final state.termination in
      let state = {state with goal; termination; debug_path = path :: debug_path} in
      `Step (partial, state)

  let rec step state = function
    | [] -> raise Not_found
    | candidate :: candidates ->
      try
        step0 state candidate, candidates
      with
      | Termination.Terminate eqns as exn ->
        printf "%a\n%!" (Termination.explain false) eqns;
        raise exn
      | Invalid_candidate -> step state candidates
      | exn ->
        report_error "Exception while testing candidate: " exn;
        step state candidates

  let apply partial arg =
    let partial_path, sub_goals = partial.payload in
    let arg_path = arg.payload in
    let eq_initial = arg.eq_initial in
    let path = papply partial_path arg_path in
    match sub_goals with
    | [] ->
      let state = {partial with
                  (* We get the equations from the argument but keep
                      termination state from the parent *)
                    payload = path; eq_initial} in
      `Done state
    | goal :: sub_goals ->
      let partial = {partial with payload = (path, sub_goals) } in
      let md = Env.find_module path arg.env in
      (* The original module declaration might be implicit, we want to avoid
         rebinding implicit *)
      let md = {md with md_implicit = Asttypes.Nonimplicit} in
      let goal = Constraints.goal arg.env goal eq_initial in
      let termination =
        Termination.check_goal arg.env goal eq_initial partial.termination in
      let env = Env.add_module_declaration goal.goal_var md arg.env in
      let debug_path = path :: partial.debug_path in
      let arg = {arg with payload = (); goal; debug_path; termination; env} in
      `Step (partial, arg)
end

module Solution = struct

  type t = {
    (* The original query *)
    query: Search.query;

    (* If we want to resume search, start from these candidates *)
    next: Search.candidate list;

    (* Intermediate steps with solutions to subqueries *)
    steps: (Search.partial * t) list;

    result: Search.result;
  }

  let rec search query =
    search_candidates query (Search.all_candidates query)

  and search_candidates query candidates =
    let step, next = Search.step query candidates in
    try search_arguments query next [] step
    with Not_found ->
      search_candidates query next

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

let rec canonical_path env path =
  try
    let md = Env.find_module path env in
    match md.Types.md_type with
    | Mty_alias path -> canonical_path env path
    | _ -> match path with
      | Path.Pident _ -> path
      | Path.Pdot (p1,s,pos) ->
          let p1' = canonical_path env p1 in
          if p1 == p1' then
            path
          else
            Path.Pdot (p1', s, pos)
      | Path.Papply (p1, p2, i) ->
          let p1' = canonical_path env p1
          and p2' = canonical_path env p2 in
          if p1' == p1 && p2 == p2' then
            path
          else
            Path.Papply (p1', p2', i)
  with Not_found ->
    (*?!*)
    path

let find_pending_instance inst =
  let snapshot = Btype.snapshot () in
  let vars, goal = goal_of_pending inst in
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
  let query = Search.start env (List.map snd vars) goal in
  try
    let solution = Solution.search query in
    let path = Solution.get solution in
    let reference = canonical_path env path in
    let rec check_alternatives solution =
      match (try Some (Solution.search_next solution)
             with _ -> None)
      with
      | Some alternative ->
        let path' = Solution.get alternative in
        let reference' = canonical_path env (Solution.get alternative) in
        if reference = reference' then
          check_alternatives alternative
        else
          raise Typecore.(Error (loc, env, Ambiguous_implicit (inst,path,path')))
      | None -> ()
    in
    check_alternatives solution;
    Btype.backtrack snapshot;
    Link.to_path inst path;
    true
  with
  | Termination.Terminate eqns ->
      printf "%a\n%!" (Termination.explain false) eqns;
      raise Typecore.(Error (loc, env, Termination_fail inst))
  | Not_found ->
      false

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
    | Path.Papply (p1, p2, i) ->
        let mfun = translpath p1 and marg = translpath p2 in
        let rec loop acc mty =
          match mty with
          | Mty_functor (param, mty_res) ->
              let param, mty_param =
                match param with
                | Mpar_generative -> assert false
                | Mpar_applicative(param, mty_param)
                | Mpar_implicit(_, param, mty_param) ->
                    param, mty_param
              in
              let coercion = Includemod.modtypes env marg.mod_type mty_param in
              let mty_appl =
                Subst.modtype
                  (Subst.add_module param p2 Subst.identity) mty_res
              in
              let marg =
                match i with
                | Asttypes.Nonimplicit -> Tmarg_applicative(marg, coercion)
                | Asttypes.Implicit -> Tmarg_implicit(marg, coercion)
              in
              { mod_desc = Tmod_apply(acc, marg);
                mod_type = mty_appl;
                mod_env = env;
                mod_attributes = [];
                mod_loc = loc;
              }
          | Mty_ident path ->
              let mty = Includemod.expand_module_path env [] path in
              loop acc mty
          | Mty_alias path ->
              let path = Env.normalize_path (Some loc) env path in
              let mty = Includemod.expand_module_alias env [] path in
              let acc =
                { mod_desc = Tmod_constraint (acc, mty, Tmodtype_implicit,
                                 Tcoerce_alias (path, Tcoerce_none));
                  mod_type = mty;
                  mod_env = env;
                  mod_attributes = [];
                  mod_loc = loc;
                }
              in
                loop acc mty
          | _ -> assert false
        in
          loop mfun mfun.mod_type
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
    | {implicit_argument = {arg_expression = Some _}} -> None
    | inst -> Some inst in
  let not_linkeds l =
    match list_filtermap not_linked l with
    | [] -> None
    | xs -> Some xs in
  let pending = list_filtermap not_linkeds !pending_implicits in
  let need_generalization inst =
    List.exists
      (fun (ty,var) ->
         assert (var.level <> generic_level);
         max ty.level var.level >= current_level)
      inst.implicit_constraints
    || inst.implicit_constraints = [] in
  let need_generalization insts =
    List.exists need_generalization insts in
  let to_generalize, rest =
    List.partition need_generalization pending in
  pending_implicits := rest;
  (* The reversal is important to ensure we search from the outer most
     to the inner most implicits *)
  let to_generalize = List.flatten (List.rev to_generalize) in
  try
    let not_instantiable inst = not (find_pending_instance inst) in
    let inst = List.find not_instantiable to_generalize in
    let loc = inst.implicit_loc in
    let env = inst.implicit_env in
    raise Typecore.(Error (loc, env, No_instance_found inst))
  with Not_found -> ()

let () =
  Typeimplicit.generalize_implicits_ref := generalize_implicits
