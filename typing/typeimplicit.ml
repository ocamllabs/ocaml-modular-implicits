open Btype
open Ctype
open Types
open Typedtree

(* Forward declaration, to be filled in by Typemod.type_package *)

let type_implicit_instance
  : (Env.t -> Typedtree.module_expr -> Path.t -> Longident.t list ->
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
  (* When linking with an implicit module M, a constraint (path, ty) is
     satisfied iff path unify with ty when implicit_id is bound to M in
     implicit_env *)
  implicit_argument: argument;
}

(*val env : Env.t
  val unlink_on
  : Ident.t -> (type_expr -> type_expr -> unit) option*)
let unlink env unlink_on =
  let path_table = Hashtbl.create 7 in

  let add_constraint register path ty tyvar =
    let instance_list =
      try Hashtbl.find path_table path
      with Not_found -> []
    in
    try
      let eq_args (ty',_tyvar') =
        TypeOps.equal ty ty' || Ctype.equal env false [ty] [ty']
      in
      let _ty', tyvar' = List.find eq_args instance_list in
      link_type tyvar tyvar'
    with Not_found ->
      Hashtbl.replace path_table path ((ty, tyvar) :: instance_list);
      register ty tyvar
  in

  (* When crossing an implicit binder, prevent unlinking it in the rhs by
     registering it in shadow_tbl *)
  let rec it_type_expr shadow_tbl it ty =
    let ty = repr ty in
    (* Then replace current type if it is a constructor referring to an
       implicit *)
    match ty.desc with
    | Tconstr (path,args,_) ->
      (* First recurse in sub expressions *)
      type_iterators.it_type_expr it ty;
      let ident = Path.head path in
      begin match unlink_on ident with
      | None -> ()
        (* Identifier is shadowed, skip unlinking *)
      | Some register when Ident.mem ident shadow_tbl ->
        (*assert false*) ()
      | Some register ->
        let ty' = newvar () in
        (* Swap `ty' with a fresh variable *)
        let {desc = desc; level = lv} = ty in
        let {desc = desc'; level = lv'} = ty' in
        ty.desc  <- desc';
        ty.level <- lv';
        ty'.desc  <- desc;
        ty'.level <- lv;
        add_constraint register path ty' ty
      end
    | Tarrow (Tarr_implicit id, lhs, rhs, _) ->
      it_type_expr shadow_tbl it lhs;
      let shadow_tbl = Ident.add id () shadow_tbl in
      let it = {it with it_type_expr = it_type_expr shadow_tbl} in
      it_type_expr shadow_tbl it rhs
    | _ -> type_iterators.it_type_expr it ty
  in

  {type_iterators with it_type_expr = it_type_expr Ident.empty}

let pending_implicits
  : pending_implicit list ref
  = ref []

let rec has_implicit ty = match (repr ty).desc with
  | Tarrow (Tarr_implicit id,_,_,_) -> true
  | Tarrow (_,_,rhs,_) -> has_implicit rhs
  | _ -> false

let instantiate_one_implicit loc env id ty_arg ty_res =
  let inst = match (repr ty_arg).desc with
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
  let add_constraint ty tyvar =
    inst.implicit_constraints <-
      (ty, tyvar) :: inst.implicit_constraints
  in
  let unlink_ident ident =
    if Ident.same id ident then
      Some add_constraint
    else
      None
  in
  (* Unlink main types *)
  let unlink_it = unlink env unlink_ident in
  List.iter (unlink_it.it_type_expr unlink_it) ty_res;
  pending_implicits := inst :: !pending_implicits;
  inst

let instantiate_implicits_ty loc env ty =
  if not (has_implicit ty) then [], [], ty
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
          (*prerr_endline "found one";*)
          let inst = fresh_implicit id lhs in
          let arguments, instances, rhs' = extract_implicits rhs in
          inst.implicit_argument :: arguments,
          inst :: instances,
          rhs'
          (*{ty with desc = Tarrow (Tarr_implicit id', lhs, rhs', comm)}*)
      | Tarrow (arr, lhs, rhs, comm) ->
          let arguments, instances, rhs' = extract_implicits rhs in
          {arg_flag = (tapp_of_tarr arr); arg_expression = None} :: arguments,
          instances,
          {ty with desc = Tarrow (arr, lhs, rhs', comm)}
      | _ -> [], [], ty
    in
    let ty = Subst.type_expr Subst.identity ty in
    let arguments, instances, ty = extract_implicits ty in
    (* Set of constraints : maintain a table mapping implicit binding
       identifier to a list of type variable pairs.
       An implicit instance is correct only iff, in an environment where the
       ident is bound to the instance, all pairs in the list unify.
    *)
    let unlink_ident ident =
      try
        let inst = List.find (fun inst -> inst.implicit_id = ident) instances in
        let add_constraint ty tyvar =
          inst.implicit_constraints <-
            (ty, tyvar) :: inst.implicit_constraints
        in
        Some add_constraint
      with Not_found ->
        None
    in
    (* Unlink main types *)
    let unlink_it = unlink env unlink_ident in
    let unlink_it = unlink_it.it_type_expr unlink_it in
    unlink_it ty;
    (* Unlink with types appearing in with constraints *)
    List.iter (fun inst ->
      let _p,_nl,tl = inst.implicit_type in
      List.iter unlink_it tl
    ) instances;
    arguments, instances, ty

let instantiate_implicits_expr env expr =
  let implicits, expr =
    match instantiate_implicits_ty expr.exp_loc env expr.exp_type with
    | [], implicits, _ ->
        implicits, expr
    | arguments, implicits, ty ->
        implicits,
        { exp_desc = Texp_apply (expr, arguments);
          exp_type = ty;
          exp_loc = expr.exp_loc;
          exp_extra = [];
          exp_env = env;
          exp_attributes = []
        }
  in
  pending_implicits := List.rev_append implicits !pending_implicits;
  expr


let pack_implicit_ref
  : (pending_implicit -> Path.t -> Typedtree.expression) ref
  = ref (fun _ _ -> assert false)

let pack_implicit inst path =
  !pack_implicit_ref inst path

module Link = struct
  (* Link a pending implicit to the module at specified path.
     May fail with unifications or module subtyping errors.
  *)
  let to_path inst path =
    (* Check that all constraints are satisfied *)
    let subst = Subst.add_module inst.implicit_id path Subst.identity in
    List.iter (fun (ty,tyvar) ->
        let ty = Subst.type_expr subst ty in
        let tyvar = Subst.type_expr subst tyvar in
        unify inst.implicit_env ty tyvar
      )
      inst.implicit_constraints;
    (* Pack the module to appropriate signature *)
    let expr = pack_implicit inst path in
    (* Update the argument *)
    inst.implicit_argument.arg_expression <- Some expr

  let to_expr inst expr =
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
    to_path inst path
end

(* Forward reference to be initialized by Implicitsearch *)
let generalize_implicits_ref
  : (unit -> unit) ref
  = ref (fun () -> assert false)

let generalize_implicits () =
  !generalize_implicits_ref ()
