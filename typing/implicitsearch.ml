open Btype
open Ctype
open Types
open Typedtree
open Typeimplicit

(** Misc definitions *)

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
    for i = 0 to n - 1 do if str.[l - n + i] <> suffix.[i] then
        raise Exit
    done;
    true
  with Exit -> false

let papply path arg = Path.Papply (path, arg, Asttypes.Implicit)

let safe_report_exn ppf exn =
  match Location.error_of_exn exn with
  | None -> Format.fprintf ppf "%s" (Printexc.to_string exn)
  | Some error -> Location.report_error ppf error

type identset = (Ident.t, unit) Tbl.t

type candidate =
  (Path.t * (Ident.t * Types.module_type) list * Types.module_type)

let add_ident set id = Tbl.add id () set


module Equalities = struct
  type t = Ctype.equalities list

  let classify_constraint flexible env subst (t1,t2) =
     let directly_flexible p =
       not (Path.is_application p) &&
       Tbl.mem (Path.head p) flexible
     in
     let assocl x =
       let rec aux = function
         | (x', y) :: _ when x == x' -> y
         | _ :: l -> aux l
         | [] -> raise Not_found
       in
       aux subst
     and assocr y =
       let rec aux = function
         | (x, y') :: _ when y == y' -> x
         | _ :: l -> aux l
         | [] -> raise Not_found
       in
       aux subst
     in
     let defining assoc lhs rhs =
       match lhs.desc with
       | Tconstr (p, tl, _) when directly_flexible p ->
           let tl = List.map (Ctype.expand_head env) tl in
           begin match List.map assoc tl with
           | exception Not_found -> `None (* Not a type variable *)
           | tl' ->
               (* Check uniqueness *)
               let rec uniq = function
                 | [] -> true
                 | x :: xs -> not (List.memq x xs) && uniq xs
               in
               let freevars = Ctype.free_variables ~env rhs in
               if uniq tl' &&
                  List.for_all (fun var -> List.memq (Ctype.repr var) tl')
                    freevars
               then `Expansion (p, (tl', rhs, None), tl)
               else `None
           end
       | _ -> `None
     in
     let t1 = Ctype.repr t1 and t2 = Ctype.repr t2 in
     let lhs = defining assocl t1 t2 and rhs = defining assocr t2 t1 in
     match lhs, rhs with
     | `Expansion e, `None | `None, `Expansion e ->
         `Definition e
     | `Expansion e1, `Expansion e2 ->
         (* Check for trivial equalities *)
         let (p1, (tl1, rhs, _), _) = e1 in
         let (p2, (_, _, _), tl2) = e2 in
         if Path.same p1 p2 && List.for_all2 (==) tl1 tl2 then
           (* This can happen because Ctype.eqtype don't check equality
                  on parameters of a flexible path, equation is just collected
                  immediately. *)
           `Trivial
         else
           `Equivalence (e1, e2)
     |  _ -> `Equality

  let classify_constraints flexible env eqs =
    let classify_collected (def,equiv,equal) {Ctype.subst ; equalities} =
      let rec aux def equiv equalities = function
        | [] -> (def, equiv, equalities)
        | tt :: tts ->
            match classify_constraint flexible env subst tt with
            | `Definition d -> aux (d :: def) equiv equalities tts
            | `Equivalence eq -> aux def (eq :: equiv) equalities tts
            | `Equality -> aux def equiv (tt :: equalities) tts
            | `Trivial -> aux def equiv equalities tts
      in
      let def, equiv, equalities = aux def equiv [] equalities in
      if equalities = [] then (def, equiv, equal)
      else (def, equiv, {Ctype. subst; equalities} :: equal)
    in
    List.fold_left classify_collected ([], [], []) eqs

   let rec refine flexible env acc eqs =
     (* Refine equalities, reinforce environnement *)
     let (), eqs =
       Ctype.collect_equalities ~on:flexible @@ fun () ->
       let refine_equalities {Ctype. subst; equalities} =
         let xs, ys = List.split equalities in
         Ctype.equal' env ~subst ~rename:true xs ys
       in
       List.iter refine_equalities eqs
     in
     let definitions, equivalences, equalities =
       classify_constraints flexible env eqs in
     let add_definition env (p, (tl, t, _ as def), _) =
       match Env.find_type_expansion p env with
       | (tl', t', _) ->
           Ctype.equal' env ~rename:true (t :: tl) (t' :: tl');
           env
       | exception Not_found ->
           printf "defining %a = %a\n"
             Printtyp.path p Printtyp.type_expr t;
           Env.add_local_expansion p def env

     and add_equivalence env ((p1,def1,_), (p2,def2,_)) =
       let (tl1, t1, _) = def1 and (tl2, t2, _) = def2 in
       match Env.find_type_expansion p1 env with
       | exception Not_found ->
           begin match Env.find_type_expansion p2 env with
           | exception Not_found ->
               printf "equivalent %a = %a\n"
                 Printtyp.path p1 Printtyp.path p2;
               if Ident.binding_time (Path.head p1) <=
                  Ident.binding_time (Path.head p2)
               then Env.add_local_expansion p1 def1 env
               else Env.add_local_expansion p2 def2 env
           | (tl2', t2', _) ->
               printf "arbitrary equality %a = %a\n"
                 Printtyp.type_expr t1 Printtyp.type_expr t2;
               Ctype.equal' env ~rename:true (t2 :: tl2) (t2' :: tl2');
               Env.add_local_expansion p1 def1 env
           end
       | (tl1', t1', _) ->
           Ctype.equal' env ~rename:true (t1 :: tl1) (t1' :: tl1');
           begin match Env.find_type_expansion p2 env with
           | exception Not_found ->
               printf "defining %a = %a\n"
                 Printtyp.path p2 Printtyp.type_expr t1;
               Env.add_local_expansion p2 def2 env
           | (tl2', t2', _) ->
               Ctype.equal' env ~rename:true (t2 :: tl2) (t2' :: tl2');
               env
           end
     in
     let acc = equalities @ acc in
     (* Equal definitions will introduce new equalities.
        Repeat to mimic unification. *)
     match
       Ctype.collect_equalities ~on:flexible
         (fun () ->
            let env = List.fold_left add_definition env definitions in
            let env = List.fold_left add_equivalence env equivalences in
            env)
     with
     | env, [] -> acc, env
     | env, eqs' -> refine flexible env acc eqs'

   let refine flexible env eqs = refine flexible env [] eqs
end

module Termination : sig
  (** The termination checker tracks all arguments to implicit functors.
      For an environment env and a flexible argument M, it will decides
      whether enough is known about M to allow searching for an instance. *)

  type symbol
  val index : Env.t -> candidate -> symbol

  type t
  val empty : t

  val enter : Env.t -> symbol -> Ident.t list -> t -> t
  val blocked : Env.t -> flexible:identset -> symbol -> t -> bool
  val explain : Env.t -> flexible:identset -> symbol -> t -> string

end = struct

  (* Helpers *)

  (* Structural ordering of types. *)

  exception Type_is_smaller
  let smaller ?subst env t1 t2 : [`Smaller | `Equal | `Different] =
    let rec check_ty t =
      if equal ?subst ~rename:true env [t1] [t] then
        raise Type_is_smaller;
      iter_type_expr check_ty t
    in
    try if equal ?subst ~rename:true env [t1] [t2]
      then `Equal
      else (iter_type_expr check_ty t2; `Different)
    with Type_is_smaller ->
      `Smaller

  let smaller env p1 p2 : [`Smaller | `Equal | `Different] =
    match Env.find_type_expansion p2 env with
    | exception Not_found ->
        begin match Env.find_type_expansion p1 env with
        | exception Not_found -> `Equal
        | _ -> `Different
        end
    | (tyl2, ty2, _) ->
        match Env.find_type_expansion p1 env with
        | exception Not_found -> `Smaller
        | (tyl1, ty1, _) ->
            let subst = List.combine tyl1 tyl2 in
            match smaller ~subst env ty1 ty2 with
            | (`Equal | `Different) as r -> r
            | `Smaller ->
                match smaller ~subst env ty2 ty1 with
                | `Smaller -> `Different (* t1 < t2 && t2 < t1 *)
                | _ -> `Smaller

  (* Collection of paths in a module type *)

  let collect_type_paths env id mty =
    let rec collect_mty acc path = function
      | Mty_signature sg -> collect_sig acc path sg
      | Mty_functor _ -> acc
      | Mty_alias p ->
          collect_mty acc path (Env.find_module p env).md_type
      | Mty_ident p ->
          begin match (Env.find_modtype p env).mtd_type with
          | None -> acc
          | Some mty -> collect_mty acc path mty
          end
    and collect_sig acc path = function
      | [] -> acc
      | x :: xs ->
          let acc = match x with
            | Sig_type (id, {type_kind = Type_abstract; type_manifest = None}, _) ->
                Path.Pdot (path, Ident.name id, 0) :: acc
            | Sig_module (id, md, _) ->
                collect_mty acc (Path.Pdot (path, Ident.name id, 0)) md.md_type
            | _ -> acc
          in
          collect_sig acc path xs
    in
    collect_mty [] (Path.Pident id) mty

  let rec rewrite_path id = function
    | Path.Pident _ -> Path.Pident id
    | Path.Papply _ -> assert false
    | Path.Pdot (p, s, x) -> Path.Pdot (rewrite_path id p, s, x)

  (** Termination checker *)

  type symbol = {
    (* UID *)
    path: Path.t;
    parameters: (Ident.t * Path.t list) list;
  }

  let index env (path, params, _) =
    let parameter (id, mty) = (id, collect_type_paths env id mty) in
    { path; parameters = List.map parameter params }

  type instance = {
    arguments: Ident.t list;
    decreasing: (Path.t list) list;
  }

  type chain = instance list

  let initial env symbol arguments =
    let rewrite_paths argument (_id,paths) =
      List.map (rewrite_path argument) paths
    in
    let decreasing = List.map2 rewrite_paths arguments symbol.parameters in
    { arguments; decreasing }

  let refine_parameter env decreasing argument =
    let decreased p1 =
      let p2 = rewrite_path argument p1 in
      match smaller env p1 p2 with
      | `Smaller -> Some p2
      | _ -> None
    in
    list_filtermap decreased decreasing

  let refine_parameters env inst arguments =
    let decreasing =
      List.map2 (refine_parameter env) inst.decreasing arguments in
    { arguments; decreasing }

  type t = (Path.t, chain) Tbl.t

  let empty = Tbl.empty

  let enter env symbol arguments t =
    if symbol.parameters = [] then t else
      let chain =
        match Tbl.find symbol.path t with
        | exception Not_found -> [initial env symbol arguments]
        | (x :: _) as xs -> refine_parameters env x arguments :: xs
        | [] -> assert false
      in
      Tbl.add symbol.path chain t

  let rec retry_chain env = function
    | [] -> assert false
    | [x] -> x
    | x :: xs ->
        let x' = retry_chain env xs in
        refine_parameters env x' x.arguments

  let non_flexible env flexible =
    let rec aux = function
      | Path.Pident id ->
          if Tbl.mem id flexible then raise Exit
      | Path.Papply (p1, p2, _) ->
          aux p1; aux p2
      | Path.Pdot (p, _, _) ->
          aux p
    in
    let it_path = function
      | Path.Pident _ -> ()
      | p -> aux p
    in
    let it = {Btype.type_iterators with Btype.it_path} in
    fun path ->
      match Env.find_type_expansion path env with
      | exception Not_found -> assert false
      | (_, ty, _) ->
          try
            it.Btype.it_type_expr it ty;
            Btype.unmark_type ty;
            true
          with Exit ->
            Btype.unmark_type ty;
            false

  exception Decreasing of Path.t

  let find_decreasing env flexible symbol t =
    match Tbl.find symbol.path t with
    | [] -> assert false
    | exception Not_found -> assert false
    | [_] -> `Root
    | (x :: _) as xs  ->
        let non_flexible = non_flexible env flexible in
        let try_instance inst =
          try
            List.iter
              (List.iter (fun path ->
                   if non_flexible path then
                     raise (Decreasing path)
                 ))
              inst.decreasing;
            `None
          with Decreasing p ->
            `Decreasing p
        in
        match try_instance x with
        | `None -> try_instance (retry_chain env xs)
        | x -> x

  let blocked env ~flexible symbol t =
    if symbol.parameters = [] then false else
    match find_decreasing env flexible symbol t with
    | `None -> true
    | _ -> false

  let explain env ~flexible symbol t =
    let print x = Format.fprintf Format.str_formatter x in
    if symbol.parameters = [] then
      print "Termination succeeds: this is a ground module"
    else begin
      match find_decreasing env flexible symbol t with
      | `Root -> print "Termination succeeds: no nested call"
      | `Decreasing x ->
          print "Termination succeeds: %a is structurally decreasing"
            Printtyp.path x
      | `None ->
          let x, x' =
            match Tbl.find symbol.path t with
            | x :: x' :: _ -> x, x'
            | [] | [_] -> assert false
          in
          let rec path arguments decreasing =
            match arguments, decreasing with
            | (id :: _), ((p :: _) :: _) -> rewrite_path id p
            | (_ :: arguments), (_ :: decreasing) -> path arguments decreasing
            | _ -> assert false
          in
          let path = path x.arguments x'.decreasing in
          print "Cannot ensure termination: %a is not structurally decreasing, "
            Printtyp.path path;
          begin match Env.find_type_expansion path env with
          | exception Not_found ->
              print "nested occurrence is not constrained."
          | (_, ty2, _) ->
              let _, ty1, _ = Env.find_type_expansion path env in
              print "%a is not smaller than %a."
                Printtyp.type_expr ty2
                Printtyp.type_expr ty1
          end
    end;
    Format.flush_str_formatter ()

end

module Pending = struct
  (* Various functions to preprocess pending implicit and implicit declarations
     when searching *)

  let variables_reifier () =
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

  let reify_variables mty tl constraints =
    let variables, it = variables_reifier () in
    it.it_module_type it mty;
    List.iter (it.it_type_expr it) tl;
    List.iter (fun (ty,tyvar) ->
        it.it_type_expr it ty;
        it.it_type_expr it tyvar)
      constraints;
    unmark_iterators.it_module_type unmark_iterators mty;
    List.iter unmark_type tl;
    List.iter (fun (ty,tyvar) ->
        unmark_type ty;
        unmark_type tyvar)
      constraints;
    !variables

  let add_variable env (_, ident) =
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

  let prepare inst =
    let env = inst.implicit_env in
    let var = inst.implicit_id in
    let path, nl, tl = inst.implicit_type in
    let constraints = inst.implicit_constraints in
    (* Extract base module type *)
    let mty =
      let mtd = Env.find_modtype path env in
      match mtd.mtd_type with
      | None -> assert false
      | Some mty -> mty
    in
    (* Turn with constraints into equality constraints *)
    let with_cstrs = List.map2 (fun li ty ->
        let rec path = function
          | Longident.Lident s -> Path.Pdot (Path.Pident var, s, 0)
          | Longident.Ldot (l, s) -> Path.Pdot (path l, s, 0)
          | Longident.Lapply _ -> assert false
        in
        Ctype.newconstr (path li) [], ty
      ) nl tl
    in
    (* Reify variables *)
    let variables = reify_variables mty tl constraints in
    let env = List.fold_left add_variable env variables in
    let flexible =
      List.fold_left (fun set (_,id) -> add_ident set id) Tbl.empty variables
    in
    env, flexible, var, mty, (with_cstrs @ constraints)

end

module Search = struct

  type t = {
    (** {2 Variables} *)

    (*vars : Ident.t list;*)
    (* Flexible modules for which we want to find a concrete instance.
       At the beginning of the search, these are bound to abstract modules in
       [env].  In a successful search, they get bound to concrete modules. *)

    blocked: (Termination.t * Termination.symbol * Ident.t list) list;

    flexible : identset;
    (* All paths on which new constraints can be introduced. *)

    (* Invariant: flexible is a superset of vars & blocked *)

    (** {2 Context & constraints} *)

    env : Env.t;
    (* Environment in which they should be satisfied.
       All [vars] are bound to abstract modules at this stage *)

    constraints : Equalities.t;
    (* Constraints that should be satisfied by a solution.  That is when all
       vars are bound to concrete modules, equalities in constraints
       should hold.  *)

    (* Invariant: [constraints] and [env] must be refined (Equalities.refine). *)

    (** {2 Result} *)

    bound : (Ident.t, Path.t) Tbl.t;
    (* Progression of the search is expressed as a mapping from variables
       variables to the path they were bound to.
       When all flexibles variables are bound, the paths are closed. *)

    roots : Ident.t list;
    (* Variables the search started from, used to display results and construct
       final paths. *)
  }

  let introduce_var env (var, mty) =
    Env.add_module var mty env

  let make env flexible vars equalities =
    let env = List.fold_left introduce_var env vars in
    let roots = List.map fst vars in
    let flexible = List.fold_left add_ident flexible roots in
    let constraints, env =
      Equalities.refine flexible env [{Ctype. subst = []; equalities}] in
    { env; constraints; roots; flexible;
      bound = Tbl.empty; blocked = []; }

  let instantiate_parameters (path, params, mty) =
    match params with
    | [] -> path, [], Mty_alias path
    | params ->
        let rec loop res ~subst ~path ~params = function
          | [] -> path, List.rev params, Subst.modtype subst res
          | (id, param) :: rest ->
              let param' = Subst.modtype subst param in
              let id' = Ident.rename id in
              let path' = Path.Pident id' in
              loop res
                ~subst:(Subst.add_module id path' subst)
                ~path:(papply path path')
                ~params:((id', param') :: params)
                rest
        in
        loop mty ~subst:Subst.identity ~path ~params:[] params

  (* Reference implementation:
     - bind one variable to a candidate.
     - if succeeds, update the goal.
     - raises an exception if candidate is not compatible
  *)
  let bind_candidate goal (term, var) (symbol, candidate) =
    (* Instantiate implicit parameters *)
    let path, params, mty = instantiate_parameters candidate in
    let newvars = List.map fst params in
    (* Update environment *)
    let env = List.fold_left introduce_var goal.env params in
    (* Update set of flexible variables *)
    let flexible = goal.flexible in
    assert (Tbl.mem var flexible);
    let flexible = List.fold_left add_ident flexible newvars in
    (* Check inclusion relation, collect constraints on parameters *)
    let (_ : module_coercion), equalities =
      let mty1 = Env.scrape_alias env mty in
      let path = Path.Pident var in
      let mty2 = (Env.find_module path env).md_type in
      let mty2 = Mtype.strengthen_except_rows env mty2 path in
      Ctype.collect_equalities ~on:flexible @@ fun () ->
      Ctype.without_moregeneral @@ fun () ->
      Includemod.modtypes env mty1 mty2
    in
    (* Rigidify module after inclusion check: inclusion can introduce new
       constraints on the module itself, e.g. when discovering associated
       types. *)
    let flexible = Tbl.remove var flexible in
    (* Bind concrete module *)
    let env = Env.add_module var mty env in
    (* Propagate constraints *)
    let constraints, env =
      Equalities.refine flexible env (equalities @ goal.constraints) in
    let term = Termination.enter env symbol newvars term in
    let newvars, blocked =
      if Termination.blocked env ~flexible symbol term then
        [], ((term, symbol, newvars) :: goal.blocked)
      else
        List.map (fun var -> (term, var)) newvars, goal.blocked
    in
    newvars,
    {
      (* Variables *)
      flexible; blocked;

      (* Constraints *)
      env; constraints;

      (* Result *)
      bound = Tbl.add var path goal.bound;
      roots = goal.roots;
    }

  let unblock t =
    let is_blocked (term, sym, _) =
      Termination.blocked t.env ~flexible:t.flexible sym term in
    let blocked, unblocked = List.partition is_blocked t.blocked in
    {t with blocked},
    let unblocked = List.map
        (fun (term, _sym, vars) ->
           List.map (fun var -> (term, var)) vars)
        unblocked
    in
    List.flatten unblocked

  let construct_paths goal =
    let rec mk_spine = function
      | Path.Pident v -> Path.Pident v
      | Path.Pdot (p', s, x) -> Path.Pdot (mk_spine p', s, x)
      | Path.Papply (p1, Path.Pident var, Asttypes.Implicit) ->
          Path.Papply (mk_spine p1, mk_var var, Asttypes.Implicit)
      | Path.Papply (_, _, _) -> assert false
    and mk_var var =
      match Tbl.find var goal.bound with
      | exception Not_found -> Path.Pident var
      | path -> mk_spine path
    in
    List.map (fun root -> root, mk_var root) goal.roots

  let print_roots ppf goal =
    let open Format in
    let rec print_spine ppf = function
      | Path.Pident var -> Printtyp.ident ppf var
      | Path.Pdot (p', s, _) -> fprintf ppf "%a.%s" print_spine p' s
      | Path.Papply (p1, Path.Pident var, Asttypes.Implicit) ->
          fprintf ppf "%a{%a}" print_spine p1 print_var var
      | Path.Papply (p1, _, _) -> assert false
    and print_var ppf var =
      match Tbl.find var goal.bound with
      | exception Not_found -> fprintf ppf "?%a" Printtyp.ident var
      | path -> print_spine ppf path
    in
    let print_binding root =
      fprintf ppf "@[%a = %a@]\n" Printtyp.ident root print_var root in
    List.iter print_binding goal.roots

  let print_candidate ppf (_, (path, params, _)) =
    Printtyp.path ppf path;
    List.iter (fun _param -> Format.fprintf ppf "{_}") params

  let rec bind_candidates acc goal (_, id as var) = function
    | [] -> List.rev acc
    | candidate :: candidates ->
        let acc = match bind_candidate goal var candidate with
          | goal' -> goal' :: acc
          | exception exn ->
              printf "Cannot bind @[%a <- %a@]: %a\n"
                Printtyp.ident id
                print_candidate candidate
                safe_report_exn exn;
              acc
        in
        bind_candidates acc goal var candidates

  let bind_candidates goal var candidates =
    bind_candidates [] goal var candidates
end

module Backtrack = struct

  let search candidates goal0 vars0 termination_fail found_solution acc0 =
    let rec conjunction acc goal = function
      | [] ->
          let goal, newvars = Search.unblock goal in
          if newvars = [] then
            if goal.Search.blocked = []
            then found_solution goal acc0
            else termination_fail goal acc0
          else conjunction acc goal newvars
      | var :: vars ->
          disjunction vars acc
            (Search.bind_candidates goal var candidates)

    and disjunction vars acc = function
      | [] -> acc
      | (newvars, goal) :: alternatives ->
          disjunction vars
            (conjunction acc goal (newvars @ vars))
            alternatives

    in
    conjunction acc0 goal0 vars0

end

module Local_progress = struct

  let rec bind_candidates acc goal (_, id as var) = function
    | [] ->
        begin match acc with
        | None -> `None
        | Some (candidate, goal') -> `Some goal'
        end
    | candidate :: candidates ->
        begin match Search.bind_candidate goal var candidate with
        | exception exn ->
            printf "Cannot bind @[%a <- %a@]: %a\n"
              Printtyp.ident id
              Search.print_candidate candidate
              safe_report_exn exn;
            bind_candidates acc goal var candidates
        | goal' ->
            begin match acc with
            | None ->
                bind_candidates (Some (candidate, goal')) goal var candidates
            | Some (candidate', _) ->
                `Ambiguous (var, candidate' :: candidate :: candidates)
            end
        end

  let bind_candidates goal var candidates =
    bind_candidates None goal var candidates

  let search candidates goal0 vars0 termination_fail found_solution acc0 =
    let rec conjunction blocked goal = function
      | [] ->
          let goal, newvars = Search.unblock goal in
          if newvars = [] then
            if blocked = [] then
              if goal.Search.blocked = []
              then found_solution goal acc0
              else termination_fail goal acc0
            else unblock goal blocked
          else conjunction blocked goal newvars
      | var :: vars ->
          match bind_candidates goal var candidates with
          | `None -> acc0
          | `Some (newvars, goal) ->
              conjunction blocked goal (newvars @ vars)
          | `Ambiguous var_candidates ->
              conjunction (var_candidates :: blocked) goal vars

    and unblock goal blocked0 =
      let rec resume blocked' = function
        | [] -> termination_fail goal acc0
        | (var, candidates) :: blocked ->
            match bind_candidates goal var candidates with
            | `None -> acc0
            | `Some (newvars, goal) ->
                conjunction (blocked' @ blocked) goal newvars
            | `Ambiguous var_candidates ->
                resume (var_candidates :: blocked') blocked
      in
      resume [] blocked0
    in
    conjunction [] goal0 vars0

end

let canonical_candidates env =
  let seen = Hashtbl.create 7 in
  let rec aux acc = function
    | [] -> acc
    | (path, params, mty) :: xs ->
        let path = Env.normalize_path None env path in
        let acc =
          if Hashtbl.mem seen path then acc else (
            Hashtbl.add seen path ();
            let candidate = (path, params, mty) in
            let symbol = Termination.index env candidate in
            (symbol, candidate) :: acc
          )
        in
        aux acc xs
  in
  aux [] (Env.implicit_instances env)

let find_pending_instance inst =
  let snapshot = Btype.snapshot () in
  let env, flexible, var, mty, cstrs = Pending.prepare inst in
  let loc = inst.implicit_loc in
  let goal = Search.make env flexible [var, mty] cstrs in
  let goal_path solution =
    List.assoc var (Search.construct_paths solution)
  in
  let candidates = canonical_candidates env in
  let search_fun =
    if !Clflags.backtracking_implicits
    then Backtrack.search
    else Local_progress.search
  in
  let solution =
    let open Typecore in
    search_fun candidates goal [Termination.empty, var]
      (fun _ _ ->
         raise (Error (loc, inst.implicit_env,
                       Termination_fail inst)))
      (fun solution solutions ->
         match solutions with
         | solution' :: _ ->
             raise (Error (loc, inst.implicit_env,
                           Ambiguous_implicit (inst,
                                               goal_path solution,
                                               goal_path solution')))
         | [] -> [solution])
      []
  in
  Btype.backtrack snapshot;
  match solution with
  | [] -> false
  | [solution] ->
      let path = List.assoc var (Search.construct_paths solution) in
      Link.to_path inst path;
      true
  | _ -> assert false

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
