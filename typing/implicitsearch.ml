open Btype
open Ctype
open Types
open Typedtree
open Typeimplicit


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
