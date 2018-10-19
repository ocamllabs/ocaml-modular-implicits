(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*     Daniel de Rauglaudre, projet Cristal, INRIA Rocquencourt        *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Module [Outcometree]: results displayed by the toplevel *)

(* These types represent messages that the toplevel displays as normal
   results or errors. The real displaying is customisable using the hooks:
      [Toploop.print_out_value]
      [Toploop.print_out_type]
      [Toploop.print_out_sig_item]
      [Toploop.print_out_phrase] *)

type out_ident =
  | Oide_apply of out_ident * out_ident * Asttypes.implicit_flag
  | Oide_dot of out_ident * string
  | Oide_ident of string

type out_value =
  | Oval_array of out_value list
  | Oval_char of char
  | Oval_constr of out_ident * out_value list
  | Oval_ellipsis
  | Oval_float of float
  | Oval_int of int
  | Oval_int32 of int32
  | Oval_int64 of int64
  | Oval_nativeint of nativeint
  | Oval_list of out_value list
  | Oval_printer of (Format.formatter -> unit)
  | Oval_record of (out_ident * out_value) list
  | Oval_string of string
  | Oval_stuff of string
  | Oval_tuple of out_value list
  | Oval_variant of string * out_value option

type out_type =
  | Otyp_abstract
  | Otyp_open
  | Otyp_alias of out_type * string
  | Otyp_arrow of string * out_type * out_type
  | Otyp_implicit_arrow of string * out_type * out_type
  | Otyp_class of bool * out_ident * out_type list
  | Otyp_constr of out_ident * out_type list
  | Otyp_manifest of out_type * out_type
  | Otyp_object of (string * out_type) list * bool option
  | Otyp_record of (string * bool * out_type) list
  | Otyp_stuff of string
  | Otyp_sum of (string * out_type list * out_type option) list
  | Otyp_tuple of out_type list
  | Otyp_var of bool * string
  | Otyp_variant of
      bool * out_variant * bool * (string list) option
  | Otyp_poly of string list * out_type
  | Otyp_module of string * string list * out_type list

and out_variant =
  | Ovar_fields of (string * bool * out_type list) list
  | Ovar_name of out_ident * out_type list

type out_class_type =
  | Octy_constr of out_ident * out_type list
  | Octy_arrow of string * out_type * out_class_type
  | Octy_signature of out_type option * out_class_sig_item list
and out_class_sig_item =
  | Ocsg_constraint of out_type * out_type
  | Ocsg_method of string * bool * bool * out_type
  | Ocsg_value of string * bool * bool * out_type

type out_module_type =
  | Omty_abstract
  | Omty_functor of out_module_parameter * out_module_type
  | Omty_ident of out_ident
  | Omty_signature of out_sig_item list
  | Omty_alias of out_ident
and out_module_parameter =
  | Ompar_generative
  | Ompar_applicative of string * out_module_type
  | Ompar_implicit of string * out_module_type
and out_sig_item =
  | Osig_class of
      bool * string * (string * (bool * bool)) list * out_class_type *
        out_rec_status
  | Osig_class_type of
      bool * string * (string * (bool * bool)) list * out_class_type *
        out_rec_status
  | Osig_typext of out_extension_constructor * out_ext_status
  | Osig_modtype of string * out_module_type
  | Osig_module of
      string * out_module_type * Asttypes.implicit_flag * out_rec_status
  | Osig_type of out_type_decl * out_rec_status
  | Osig_value of string * out_type * string list
  | Osig_implicit of out_implicit_kind * out_ident * out_imp_status
and out_type_decl =
  { otype_name: string;
    otype_params: (string * (bool * bool)) list;
    otype_type: out_type;
    otype_private: Asttypes.private_flag;
    otype_cstrs: (out_type * out_type) list }
and out_extension_constructor =
  { oext_name: string;
    oext_type_name: string;
    oext_type_params: string list;
    oext_args: out_type list;
    oext_ret_type: out_type option;
    oext_private: Asttypes.private_flag }
and out_type_extension =
  { otyext_name: string;
    otyext_params: string list;
    otyext_constructors: (string * out_type list * out_type option) list;
    otyext_private: Asttypes.private_flag }
and out_implicit_kind =
  | Oimp_implicit
  | Oimp_explicit
and out_rec_status =
  | Orec_not
  | Orec_first
  | Orec_next
and out_ext_status =
  | Oext_first
  | Oext_next
  | Oext_exception
and out_imp_status =
  | Oimps_standalone
  | Oimps_attached

type out_phrase =
  | Ophr_eval of out_value * out_type
  | Ophr_signature of (out_sig_item * out_value option) list
  | Ophr_exception of (exn * out_value)
