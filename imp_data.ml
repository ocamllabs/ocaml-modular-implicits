module type Any = sig
  type t
end

module type Show = sig
  type t
  val to_string: t -> string
  val buffer_add : Buffer.t -> t -> unit
  val pp_print : Format.formatter -> t -> unit
end

module Show = struct
  let to_string (implicit M : Show) = M.to_string
  let buffer_add (implicit M : Show) = M.buffer_add
  let pp_print (implicit M : Show) = M.pp_print
end

module type Eq = sig
  type t
  val ( = ) : t -> t -> bool
end

module Eq = struct
  let ( = ) (implicit M : Eq) = M.(=)
end

module type Ord = sig
  type t
  val compare : t -> t -> int
end

module Ord = struct
  let ( =  ) (implicit M : Ord) a b = M.compare a b =  0
  let ( <> ) (implicit M : Ord) a b = M.compare a b <> 0
  let ( <  ) (implicit M : Ord) a b = M.compare a b <  0
  let ( <= ) (implicit M : Ord) a b = M.compare a b <= 0
  let ( >  ) (implicit M : Ord) a b = M.compare a b >  0
  let ( >= ) (implicit M : Ord) a b = M.compare a b >= 0
  let compare (implicit M : Ord) = M.compare
end

module type Num = sig
  type t
  val zero : t
  val one : t
  val of_int : int -> t
  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( * ) : t -> t -> t
  val ( / ) : t -> t -> t
  val (~- ) : t -> t
end

module Num = struct
  let zero   (implicit M : Num) () = M.zero
  let one    (implicit M : Num) () = M.one
  let of_int (implicit M : Num) = M.of_int
  let ( + )  (implicit M : Num) = M.( + )
  let ( - )  (implicit M : Num) = M.( - )
  let ( * )  (implicit M : Num) = M.( * )
  let ( / )  (implicit M : Num) = M.( / )
  let (~- )  (implicit M : Num) = M.(~- )
end

module type Bounded = sig
  type t
  val bounds : t * t
end

module Bounded = struct
  let bounds (implicit M : Bounded) () = M.bounds
end

module type Enum = sig
  include Ord
  val succ : t -> t
  val pred : t -> t
end

module Enum = struct
  let succ (implicit M : Enum) x = M.succ
  let pred (implicit M : Enum) x = M.pred

  let rec fold_enum_to
    : (implicit M : Enum) -> M.t -> M.t -> (M.t -> 'a -> 'a) -> 'a -> 'a
    = fun (implicit M : Enum) a b f acc ->
    if M.compare a b < 0 then
      fold_enum_to (M.succ a) b f (f a acc)
    else
      acc

  let rec fold_enum_downto
    : (implicit M : Enum) -> M.t -> M.t -> (M.t -> 'a -> 'a) -> 'a -> 'a
    = fun (implicit M : Enum) a b f acc ->
    if M.compare b a < 0 then
      fold_enum_downto (M.pred a) b f (f a acc)
    else
      acc

  let list_enum_to (implicit M : Enum) (a : M.t) b =
    List.rev (fold_enum_to a b (fun x acc -> x :: acc) [])

  let list_enum_downto (implicit M : Enum) (a : M.t) b =
    List.rev (fold_enum_downto a b (fun x acc -> x :: acc) [])
end

module type Monoid = sig
  type t
  val empty : t
  val append : t -> t -> t
end

module Monoid = struct
  let empty (implicit M : Monoid) () = M.empty
  let append (implicit M : Monoid) = M.append
end

(* Instances *)

implicit module Int = struct
  type t = int

  (* Show *)
  let to_string = string_of_int
  let buffer_add b i = Buffer.add_string b (to_string i)
  let pp_print = Format.pp_print_int

  (* Eq *)
  let ( = ) (a : int) b = a = b

  (* Ord *)
  let compare (a : int) b = compare a b

  (* Num *)
  let zero = 0
  let one  = 1
  let of_int x = x
  let ( + ) = ( + )
  let ( - ) = ( - )
  let ( * ) = ( * )
  let ( / ) = ( / )
  let (~- ) = (~- )

  (* Bounded *)
  let bounds = (min_int, max_int)

  (* Enum *)
  let succ = succ
  let pred = pred

  (* Monoid, addition *)
  let empty = 0
  let append = (+)
end

implicit module Float = struct
  type t = float

  (* Show *)
  let to_string = string_of_float
  let buffer_add b i = Buffer.add_string b (to_string i)
  let pp_print = Format.pp_print_float

  (* Eq *)
  let ( = ) (a : float) b = a = b

  (* Ord *)
  let compare (a : float) b = compare a b

  (* Num *)
  let zero = 0.
  let one  = 1.
  let of_int = float_of_int
  let ( + ) = ( +.)
  let ( - ) = ( -.)
  let ( * ) = ( *.)
  let ( / ) = ( /.)
  let (~- ) = (~-.)

  (* Bounded *)
  let bounds = (neg_infinity, infinity)

  (* Monoid, addition *)
  let empty = 0.
  let append = (+.)
end

implicit module Bool = struct
  type t = bool

  (* Show *)
  let to_string = string_of_bool
  let buffer_add b i = Buffer.add_string b (to_string i)
  let pp_print = Format.pp_print_bool

  (* Eq *)
  let ( = ) (a : bool) b = a = b

  (* Ord *)
  let compare (a : bool) b = compare a b

  (* Bounded *)
  let bounds = (neg_infinity, infinity)

  (* Enum *)
  let succ = function
    | false -> true
    | true  -> invalid_arg "Bool.succ"

  let pred = function
    | true  -> false
    | false -> invalid_arg "Bool.pred"

  (* Monoid, addition *)
  let empty = false
  let append = (||)
end

implicit module Char = struct
  type t = char

  (* Show *)
  let to_string c = String.escaped (String.make 1 c)
  let buffer_add b c = Buffer.add_string b (to_string c)
  let pp_print ppf c = Format.pp_print_string ppf c

  (* Eq *)
  let ( = ) (a : char) b = a = b

  (* Ord *)
  let compare (a : char) b = compare a b

  (* Bounded *)
  let bounds = ('\000', '\255')

  (* Enum *)
  let succ = function
    | '\255' -> invalid_arg "Char.succ"
    | n -> Char.chr (succ (Char.code n))

  let pred = function
    | '\000' -> invalid_arg "Char.succ"
    | n -> Char.chr (pred (Char.code n))
end

implicit module String = struct
  type t = string

  (* Show *)
  let to_string = String.escaped
  let buffer_add b s = Buffer.add_string b (to_string s)
  let pp_print ppf s = Format.pp_print_string ppf (to_string s)

  (* Eq *)
  let ( = ) (a : string) b = a = b

  (* Ord *)
  let compare (a : string) b = compare a b

  (* Monoid *)
  let empty = ""
  let append = (^)
end

implicit module Int32 = struct
  type t = int32

  (* Show *)
  let to_string = Int32.to_string
  let buffer_add b i = Buffer.add_string b (to_string i)
  let pp_print ppf s = Format.pp_print_string ppf (to_string s)

  (* Eq *)
  let ( = ) (a : int32) b = a = b

  (* Ord *)
  let compare = Int32.compare

  (* Num *)
  let zero = 0l
  let one  = 1l
  let of_int = Int32.of_int
  let ( + ) = Int32.add
  let ( - ) = Int32.sub
  let ( * ) = Int32.mul
  let ( / ) = Int32.div
  let (~- ) = Int32.neg

  (* Bounded *)
  let bounds = (Int32.min_int, Int32.max_int)

  (* Enum *)
  let succ = Int32.succ
  let pred = Int32.pred

  (* Monoid, addition *)
  let empty = 0l
  let append = Int32.add
end

implicit module Int64 = struct
  type t = int64

  (* Show *)
  let to_string = Int64.to_string
  let buffer_add b i = Buffer.add_string b (to_string i)
  let pp_print ppf i = Format.pp_print_string ppf (to_string i)

  (* Eq *)
  let ( = ) (a : int64) b = a = b

  (* Ord *)
  let compare = Int64.compare

  (* Num *)
  let zero = 0L
  let one  = 1L
  let of_int = Int64.of_int
  let ( + ) = Int64.add
  let ( - ) = Int64.sub
  let ( * ) = Int64.mul
  let ( / ) = Int64.div
  let (~- ) = Int64.neg

  (* Bounded *)
  let bounds = (Int64.min_int, Int64.max_int)

  (* Enum *)
  let succ = Int64.succ
  let pred = Int64.pred

  (* Monoid, addition *)
  let empty = 0L
  let append = Int64.add
end

implicit module Nativeint = struct
  type t = nativeint

  (* Show *)
  let to_string = Nativeint.to_string
  let buffer_add b i = Buffer.add_string b (to_string i)
  let pp_print ppf i = Format.pp_print_string ppf (to_string i)

  (* Eq *)
  let ( = ) (a : nativeint) b = a = b

  (* Ord *)
  let compare = Nativeint.compare

  (* Num *)
  let zero = 0L
  let one  = 1L
  let of_int = Nativeint.of_int
  let ( + ) = Nativeint.add
  let ( - ) = Nativeint.sub
  let ( * ) = Nativeint.mul
  let ( / ) = Nativeint.div
  let (~- ) = Nativeint.neg

  (* Bounded *)
  let bounds = (Nativeint.min_int, Nativeint.max_int)

  (* Enum *)
  let succ = Nativeint.succ
  let pred = Nativeint.pred

  (* Monoid, addition *)
  let empty = 0L
  let append = Nativeint.add
end
