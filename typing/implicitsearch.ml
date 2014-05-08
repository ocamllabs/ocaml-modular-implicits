open Btype
open Ctype
open Types
open Typedtree
open Typeimplicit

module Constraints = struct

  (* Apply constraints to a module type.

    1. Traverse the module type to substitute type declarations with
      constraints and accumulate types to unify.

      When constraining a type declaration, add the constraint as manifest.
      If the type declaration already had a manifest, keep the original
      manifest in a separate list to unify it in a later pass.

      During traversal, register module and submodule types in
      environment because find_modtype_expansion might need them.

     2. Do a second pass, rebuilding the environment and unifying constraints.

      Envirnoment is rebuilt with the types obtained after substitution.
      For each type in the unify list, instantiate it in its local
      environment and unify it with the constrained type.
  *)

  let rec list_extract f acc = function
    | x :: xs when f x -> x, List.rev_append acc xs
    | x :: xs -> list_extract f (x :: acc) xs
    | [] -> raise Not_found
  let list_extract f xs = list_extract f [] xs

  let name_match name (qname,_) = name = qname

  type ('n,'cstr) t =
    | Local of 'cstr
    | Sub of ('n * ('n,'cstr) t) list

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

  let register_items env = function
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

  let rec prepare_mty env cstrs mty =
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

  and prepare_sig env cstrs sg =
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

  let flatten ~root cstrs =
    let flatten_cstr (n,t) =
      let id', dots = Path.flatten n in
      assert (Ident.same root id');
      assert (dots <> []);
      List.map fst dots, t
    in
    List.map flatten_cstr cstrs

end

type target = {
  target_type : Types.module_type;
  target_id : Ident.t;
}

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
  let cstrs =
    (* Constraints from package type *)
    (List.map2 (fun n t -> Longident.flatten n, t) nl tl)
    (* Constraints from implicit instance *) @
    (Constraints.flatten ~root:ident inst.implicit_constraints)
  in
  let mty = Constraints.apply env mty cstrs in
  { target_type = mty; target_id = inst.implicit_id }

let candidate_of_implicit_declaration env {Types. md_type; md_implicit} =
  let rec find_mty targets n mty =
    assert (n >= 0);
    if n = 0 then
      List.rev targets, mty
    else match mty with
      | Mty_functor (target_id, Some target_type, mty) ->
          find_mty ({target_id; target_type} :: targets) (n - 1) mty
      | _ -> assert false
  in
  let arity = match md_implicit with
    | Asttypes.Nonimplicit -> assert false
    | Asttypes.Implicit n -> n
  in
  (* Take a fresh copy of the module type, as unlinking is a destructive
     operation *)
  let md_type = Subst.modtype Subst.identity md_type in

  let targets, md_type = find_mty [] arity md_type in
  let targets_constraints = List.fold_left
      (fun tbl target -> Ident.add target.target_id (ref []) tbl)
      Ident.empty targets
  in
  (* Unlink types, generate constraints *)
  begin match targets with
  | [] -> ()
  | _ :: targets' ->
      let module Unlink = Unlink (struct
          let register_constraints_for ident =
            try
              let lst = Ident.find_same ident targets_constraints in
              let add_constraint path var = lst := (path,var) :: !lst in
              Some add_constraint
            with Not_found ->
              None
        end)
      in
      List.iter Unlink.module_type
        (md_type :: List.map (fun t -> t.target_type) targets')
  end;
  (* Apply constraints to module types *)
  let targets =
    List.map (fun target ->
        let cstrs = Constraints.flatten
            ~root:target.target_id
            !(Ident.find_same target.target_id targets_constraints)
        in
        let target_type = Constraints.apply env target.target_type cstrs in
        {target with target_type})
      targets
  in
  targets,
  md_type

let target_in_stack stack _ =
  List.length stack >= 4 (* TODO *)

let rec list_findmap f = function
  | [] -> raise Not_found
  | x :: xs ->
      match f x with
      | None -> list_findmap f xs
      | Some x' -> x'

let string_of_path path =
  Path.to_longident path |> Longident.flatten |> String.concat "."

let report_error exn =
  try
    Location.report_exception Format.err_formatter exn
  with exn ->
    prerr_endline (Printexc.to_string exn)

let rec find_target env stack target =
  prerr_endline "enter find_target\n";
  Misc.try_finally
    (fun () ->
       let snapshot = Btype.snapshot () in
       let stack = target :: stack in
       let papply path arg = Path.Papply (path, arg) in
       let build_path (path, md) =
         prerr_endline ("trying candidate " ^ (string_of_path path));
         let targets, candidate = candidate_of_implicit_declaration env md in
         try
           if List.exists (target_in_stack stack) targets then
             failwith "loop";
           ignore (Includemod.modtypes env candidate target.target_type
                   : module_coercion);
           let args = List.map (find_target env stack) targets in
           Some (List.fold_left papply path args)
         with exn ->
           Btype.backtrack snapshot;
           report_error exn;
           None
       in
       list_findmap build_path (Env.implicit_instances env)
    )
    (fun () -> prerr_endline "exit find_target\n")

let find_pending_instance inst =
  let print_inst (path,_) =
    prerr_endline (string_of_path path)
  in
  prerr_endline "entering search\ncandidates:";
  List.iter print_inst (Env.implicit_instances inst.implicit_env);
  let target = target_of_pending inst in
  try
    let path = find_target inst.implicit_env [] target in
    Link.to_path inst path;
    true
  with _ ->
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
         var.level >= current_level)
      inst.implicit_constraints
    || inst.implicit_constraints = []
  in
  let to_generalize, rest =
    List.partition need_generalization pending
  in
  pending_implicits := rest;
  try
    let not_instantiable inst = not (find_pending_instance inst) in
    let inst = List.find not_instantiable to_generalize in
    let loc = inst.implicit_loc in
    let env = inst.implicit_env in
    raise Typecore.(Error (loc, env, Pending_implicit inst))
  with Not_found -> ()

let () =
  Typeimplicit.generalize_implicits_ref := generalize_implicits
