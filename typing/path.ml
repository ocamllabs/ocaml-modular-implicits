(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

type t =
    Pident of Ident.t
  | Pdot of t * string * int
  | Papply of t * t

let nopos = -1

let rec same p1 p2 =
  match (p1, p2) with
    (Pident id1, Pident id2) -> Ident.same id1 id2
  | (Pdot(p1, s1, pos1), Pdot(p2, s2, pos2)) -> s1 = s2 && same p1 p2
  | (Papply(fun1, arg1), Papply(fun2, arg2)) ->
       same fun1 fun2 && same arg1 arg2
  | (_, _) -> false

let rec isfree id = function
    Pident id' -> Ident.same id id'
  | Pdot(p, s, pos) -> isfree id p
  | Papply(p1, p2) -> isfree id p1 || isfree id p2

let rec binding_time = function
    Pident id -> Ident.binding_time id
  | Pdot(p, s, pos) -> binding_time p
  | Papply(p1, p2) -> max (binding_time p1) (binding_time p2)

let kfalse x = false

let rec name ?(paren=kfalse) = function
    Pident id -> Ident.name id
  | Pdot(p, s, pos) ->
      name ~paren p ^ if paren s then ".( " ^ s ^ " )" else "." ^ s
  | Papply(p1, p2) -> name ~paren p1 ^ "(" ^ name ~paren p2 ^ ")"

let rec is_application = function
  | Pdot (p, _, _) -> is_application p
  | Papply _ -> true
  | Pident _ -> false

let rec head = function
    Pident id -> id
  | Pdot(p, s, pos) -> head p
  | Papply(p1, p2) -> assert false

let rec last = function
  | Pident id -> Ident.name id
  | Pdot(_, s, _) -> s
  | Papply(_, p) -> last p

let rec to_longident = function
  | Pident id -> Longident.Lident (Ident.name id)
  | Pdot(p, s, _) -> Longident.Ldot (to_longident p, s)
  | Papply (p1, p2) -> Longident.Lapply (to_longident p1, to_longident p2)
let to_string p = Longident.to_string (to_longident p)

let rec flatten acc = function
  | Pident id -> id, acc
  | Pdot (p, s, pos) -> flatten ((s,pos) :: acc) p
  | Papply _ -> assert false
let flatten path = flatten [] path

let rec unflatten p = function
  | [] -> p
  | (s, spos) :: dots -> unflatten (Pdot (p, s, spos)) dots
let unflatten id dots = unflatten (Pident id) dots
