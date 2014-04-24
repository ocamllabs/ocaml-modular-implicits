open Btype
open Ctype
open Types
open Typedtree

(* Forward declaration, to be filled in by Typemod.type_package *)

let type_package
  : (Env.t -> Parsetree.module_expr -> Path.t -> Longident.t list ->
     type_expr list -> Typedtree.module_expr * type_expr list) ref
  = ref (fun _ -> assert false)

(* Instantiate implicits in a function type

   Given a type expression, find all path refering to an implicit module.
   1. Find any implicit bindings: if none, return the original type.
   2. Generate fresh idents for all implicit bindings, substitute idents in the
      type.
   3. Replace all type constructors referring to an implicit module
      by a fresh type variable and remember the (constr, var) constraint
      association.

   (*If a typed expression is a function containing implicit arguments,
   this produces a new expression corresponding to the function with all
   implicits instantiated together with the hole to be filled with actual
   instances and a set of constraints to be satisfied.*)
*)

type pending_implicit = {
  implicit_id: Ident.t;
  implicit_env: Env.t;
  implicit_loc: Location.t;
  implicit_type: Path.t * Longident.t list * type_expr list;
  mutable implicit_constraints: (type_expr * type_expr) list;
  implicit_argument: argument;
}

let pending_implicits
  : pending_implicit list ref
  = ref []

let instantiate_implicits loc env ty =
  let rec has_implicit ty = match ty.desc with
    | Tarrow (Tarr_implicit id,_,_,_) -> true
    | Tarrow (_,_,rhs,_) -> has_implicit rhs
    | _ -> false
  in
  if not (has_implicit ty) then Ident.empty, ty
  else
    let fresh_implicit id ty =
      let ty = repr ty in
      match ty.desc with
      | Tpackage (p,nl,tl) -> {
          implicit_id = id;
          implicit_env = env;
          implicit_loc = loc;
          implicit_type = (p,nl,tl);
          implicit_constraints = [];
          implicit_argument = {
            arg_flag = Tapp_implicit;
            arg_expression = None
          };
        }
      | _ -> assert false
    in
    let rec extract_implicits ty =
      let ty = repr ty in
      match ty.desc with
      | Tarrow (Tarr_implicit id, lhs, rhs, comm) ->
          let id' = Ident.rename id in
          let instances, subst, rhs' = extract_implicits rhs in
          Ident.add id' (fresh_implicit id' lhs) instances,
          Subst.add_implicit id (Path.Pident id') subst,
          {ty with desc = Tarrow (Tarr_implicit id', lhs, rhs', comm)}
      | Tarrow (arr, lhs, rhs, comm) ->
          let instances, subst, rhs' = extract_implicits rhs in
          instances, subst,
          {ty with desc = Tarrow (arr, lhs, rhs', comm)}
      | _ -> Ident.empty, Subst.identity, ty
    in
    let instances, subst, ty = extract_implicits ty in
    let ty = Subst.type_expr subst ty in
    (* Set of constraints : maintain a table mapping implicit binding
       identifier to a list of type variable pairs.
       An implicit instance is correct only iff, in an environment where the
       ident is bound to the instance, all pairs in the list unify.
    *)
    let linked = Hashtbl.create 7 in
    let add_constraint inst ~constr ~ty ~var =
      begin try
        let var' = Hashtbl.find linked constr in
        link_type var var'
      with Not_found ->
        Hashtbl.add linked constr var
      end;
      inst.implicit_constraints <- (ty,var) :: inst.implicit_constraints
    in
    let rec unlink_constructors ty =
      (* First recurse in sub expressions *)
      iter_type_expr unlink_constructors ty;
      (* Then replace current type if it is a constructor referring to an
         implicit *)
      match ty.desc with
      | Tconstr (path,_,_) as constr ->
          begin try
            let inst = Ident.find_same (Path.head path) instances in
            (* Fresh variable *)
            let ty' = newvar() in
            (* Swap the content of ty and ty' … *)
            let {desc = desc; level = lv; id = id} = ty in
            let {desc = desc'; level = lv'; id = id'} = ty' in
            ty.desc   <- desc';
            ty.level  <- lv';
            ty.id     <- id';
            ty'.desc  <- desc;
            ty'.level <- lv;
            ty'.id    <- id;
            add_constraint inst ~constr ~ty:ty' ~var:ty
          with Not_found -> ()
          end
      | _ -> ()
    in
    unlink_constructors ty;
    instances, ty

(* Pack module at given path to match a given implicit instance and
   update the instance to point to this module.
   Return the correct package if any.
*)
let pack_implicit inst path =
  let { implicit_type = p,nl,tl;
        implicit_env  = env;
        implicit_loc  = loc } = inst in
  let md = Env.find_module path env in
  let md = {md with md_type = (Mty_alias path)} in
  let _, env' = Env.enter_module_declaration "Pkg" md env in
  let pmd = Ast_helper.(Mod.ident (Convenience.lid "Pkg")) in
  let (modl, tl') = !type_package env' pmd p nl tl in
  {
    exp_desc = Texp_pack modl;
    exp_loc = loc; exp_extra = [];
    exp_type = newty (Tpackage (p, nl, tl'));
    exp_attributes = [];
    exp_env = env;
  }

(* Link a pending implicit to the module at specified path.
   May fail with unifications or module subtyping errors.
*)
let link_implicit_to_path inst path =
  (* Check that all constraints are satisfied *)
  let subst = Subst.add_module inst.implicit_id path Subst.identity in
  List.iter (fun (ty,ty') ->
      let ty = Subst.type_expr subst ty in
      let ty' = Subst.type_expr subst ty' in
      unify inst.implicit_env ty ty'
    )
    inst.implicit_constraints;
  (* Pack the module to appropriate signature *)
  let expr = pack_implicit inst path in
  (* Update the argument *)
  inst.implicit_argument.arg_expression <- Some expr

let link_implicit_to_expr inst expr =
  (* An implicit instance always have to be a path to a module in scope *)
  let rec mod_path me = match me.mod_desc with
    | Tmod_ident (path,_) -> path
    | Tmod_constraint (me,_,_,_) ->
        mod_path me
    | _ -> assert false
  in
  let path = match expr.exp_desc with
    | Texp_pack me -> mod_path me
    | _ -> assert false
  in
  link_implicit_to_path inst path

(* Naive resolution procedure *)
let find_instance inst =
  let snapshot = Btype.snapshot () in
  let modules = Env.implicit_instances inst.implicit_env in
  let module_match (path,_) =
    try
      prerr_endline ("try " ^ Path.last path);
      link_implicit_to_path inst path;
      true
    with _ ->
      Btype.backtrack snapshot;
      false
  in
  List.exists module_match modules

let generalize_implicits () =
  prerr_endline "generalize_implicits";
  let current_level = get_current_level () in
  let need_generalization inst =
    prerr_endline "found one";
    List.exists
      (fun (ty,ty') ->
         (*assert (ty.level <> generic_level);
         assert (ty'.level <> generic_level);*)
         ty.level > current_level || ty'.level > current_level || true)
      inst.implicit_constraints
  in
  let to_generalize, rest =
    List.partition need_generalization !pending_implicits
  in
  pending_implicits := rest;
  assert (List.for_all find_instance to_generalize)

let () = Ctype.generalize_implicits := generalize_implicits
