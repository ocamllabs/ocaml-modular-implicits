open Btype
open Ctype
open Types
open Typedtree
open Typeimplicit

(*let alias_id = ref 0
let alias_ty env ty =
  incr alias_id;
  let name = "%t" ^ string_of_int !alias_id in
  let tyd = { type_params        = [];
              type_arity         = 0;
              type_kind          = Type_abstract;
              type_private       = Asttypes.Public;
              type_manifest      = Some ty;
              type_variance      = [];
              type_newtype_level = None;
              type_loc           = Location.none;
              type_attributes    = [] }
  in
  let _, env = Env.enter_type name tyd env in
  env, Ast_helper.Typ.constr (Location.mknoloc (Longident.Lident name)) []

let alias_tys (env,tl) ty =
  let env, t = alias_ty env ty in
  env, t :: tl

let implicit_mty inst =
  let (path, nl, tl) = inst.implicit_type in
  let mtd = { mtd_type = Some (Mty_ident path);
              mtd_attributes = [];
              mtd_loc = Location.none; }
  in
  (* Generate fresh name for module *)
  let _, env = Env.enter_modtype "%M" mtd inst.implicit_env in

  (* Generate fresh names for types *)
  let env, tl' = List.fold_left alias_tys (env,[]) tl in
  let tl' = List.rev tl' in

  let _, pmty =
    Typetexp.create_package_mty Location.none env
      (Location.mknoloc (Longident.Lident "%M"),
       List.map2 (fun n t -> Location.mknoloc n, t) nl tl')
  in
  let mty = !Typetexp.transl_modtype env pmty in

  let mty = Mtype.scrape env mty.mty_type in
  mty*)

module Constraints = struct

  let rec list_extract f acc = function
    | x :: xs when f x -> x, List.rev_append acc xs
    | x :: xs -> list_extract f (x :: acc) xs
    | [] -> raise Not_found
  let list_extract f xs = list_extract f [] xs

  let name_match prj name (qname,_) = name = prj qname

  let split_constraint (local,subs) = function
    | [], _ ->
        assert false
    | [x], c ->
        ((x, c) :: local, subs)
    | (x :: xs), c ->
        let (x, sub), subs =
          try list_extract (name_match (fun x->x) x) subs
          with Not_found -> (x, []), subs
        in
        (local, (x, (xs, c) :: sub) :: subs)

  let split_constraints l =
    List.fold_left split_constraint ([],[]) l

  let rec try_mty env prj cstrs mty =
    if cstrs = [] then [], mty else
      match mty with
      | Mty_functor _ | Mty_alias _ -> cstrs, mty
      | Mty_ident p ->
          begin try
            let mty = Env.find_modtype_expansion p env in
            try_mty env prj cstrs mty
          with Not_found ->
            cstrs, mty
          end
      | Mty_signature sg ->
          let failed, sg' = try_sig env prj cstrs sg in
          failed, Mty_signature sg'

  and try_sig_item env prj failed (locs, subs as cstrs) field =
    match field with
    | Sig_value _ | Sig_modtype _ | Sig_class _
    | Sig_class_type _ | Sig_exception _ ->
        failed, cstrs, field
    | Sig_type (id,decl,recst) ->
        let name = Ident.name id in
        begin try
          let (qname, ty), locs = list_extract (name_match prj name) locs in
          begin match decl.type_manifest with
          | None -> ()
          | Some ty' ->
              let ty' = instance env ty' in
              unify env ty ty';
          end;
          failed, (locs, subs),
          Sig_type (id,{decl with type_manifest = Some ty},recst)
        with Not_found ->
          failed, cstrs, field
        end
    | Sig_module (id,decl,recst) ->
        let name = Ident.name id in
        begin try
          let (qname, sub), subs = list_extract (name_match prj name) subs in
          let subfailed, md_type = try_mty env prj sub decl.md_type in
          let subfailed = List.rev_map (fun(xs,t)->(qname::xs,t)) subfailed in
          (subfailed @ failed), (locs, subs),
          Sig_module (id,{decl with md_type},recst)
        with Not_found ->
          failed, cstrs, field
        end
    | Sig_implicit (id,decl) ->
        let name = Ident.name id in
        begin try
          let (qname, sub), subs = list_extract (name_match prj name) subs in
          let imd = decl.imd_module in
          let subfailed, md_type = try_mty env prj sub imd.md_type in
          let subfailed = List.rev_map (fun(xs,t)->(qname::xs,t)) subfailed in
          (subfailed @ failed), (locs, subs),
          Sig_implicit (id,{decl with imd_module = {imd with md_type}})
        with Not_found ->
          failed, cstrs, field
        end

  and try_sig' env prj fields failed cstrs = function
    | [] ->
        let (locs, subs) = cstrs in
        let locs = List.map (fun (x,t) -> [x],t) locs in
        let subs = List.map
            (fun (x,xss) -> List.map (fun (xs,c) -> (x::xs),c) xss)
            subs
        in
        let failed = locs @ List.flatten subs @ failed in
        failed, List.rev fields

    | item :: items ->
        let failed, cstrs, item' = try_sig_item env prj failed cstrs item in
        try_sig' env prj (item' :: fields) failed cstrs items

  and try_sig env prj cstrs sg =
    if cstrs = [] then
      [], sg
    else
      try_sig' env prj [] [] (split_constraints cstrs) sg

end

type sign = {
  sign_type : Types.module_type;
  sign_id : Ident.t;
  sign_constraints : (Path.t * Types.type_expr) list;
}

let sign_of_pending inst =
  let env = inst.implicit_env in
  let path, nl, tl = inst.implicit_type in
  let mtd = Env.find_modtype path env in
  let mty = match mtd.mtd_type with
    | None -> assert false
    | Some mty -> mty
  in
  let with_cstrs = List.map2 (fun n t -> Longident.flatten n, t) nl tl in
  let mty =
    let failed, mty = Constraints.try_mty env (fun x->x) with_cstrs mty in
    (* No constraint should fail to apply, otherwise we are doing something
       wrong with package_type. *)
    assert (failed = []);
    mty
  in
  let ident = inst.implicit_id in
  let flatten_cstr (n,t) =
    let id', dots = Path.flatten n in
    (* All constraints should apply to fields of the implicit module *)
    assert (Ident.same ident id');
    assert (dots <> []);
    dots, t
  in
  let cstrs = inst.implicit_constraints in
  let cstrs = List.map flatten_cstr cstrs in
  let failed, mty = Constraints.try_mty env fst cstrs mty in
  let unflatten_cstr (n,t) = Path.unflatten ident n, t in
  let constraints = List.map unflatten_cstr failed in
  { sign_type = mty; sign_id = ident; sign_constraints = constraints }

let sign_of_implicit_declaration imd =
  let rec find_mty acc n mty =
    assert (n >= 0);
    if n = 0 then
      List.rev acc, mty
    else match mty with
      | Mty_functor (arg_id, Some arg_ty, mty) ->
          find_mty ((arg_id, arg_ty) :: acc) (n - 1) mty
      | _ -> assert false
  in
  let _mty = find_mty [] imd.imd_arity imd.imd_module.md_type in
  failwith "TODO"


let sign_match env sign (path,imd) =
  let subst = Subst.add_module sign.sign_id path Subst.identity in
  List.iter (fun (tpath,ty') ->
      let tpath = Subst.type_path subst tpath in
      let ty = newconstr tpath [] in
      let ty' = Subst.type_expr subst ty' in
      unify env ty ty'
    )
    sign.sign_constraints

let sign_in_stack _sign stack =
  List.length stack >= 4 (* TODO *)

let find_sign env stack sign =
  if sign_in_stack sign stack then
    raise Not_found
  else begin
    let _candidates = Env.implicit_instances env in
    failwith "TODO"
  end

let find_instance inst =
  let snapshot = Btype.snapshot () in
  let candidates = Env.implicit_instances inst.implicit_env in
  let sign = sign_of_pending inst in
  let module_match (path,_ as candidate) =
    try
      sign_match inst.implicit_env sign candidate;
      link_implicit_to_path inst path;
      true
    with _ ->
      Btype.backtrack snapshot;
      false
  in
  List.exists module_match candidates


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
    let not_instantiable inst = not (find_instance inst) in
    let inst = List.find not_instantiable to_generalize in
    let loc = inst.implicit_loc in
    let env = inst.implicit_env in
    raise Typecore.(Error (loc, env, Pending_implicit inst))
  with Not_found -> ()

let () =
  Typeimplicit.generalize_implicits_ref := generalize_implicits
