(* Purity *)
module Pure1_ok {X : Map.OrderedType} = struct
  let test = "test"
end;;

module Pure1_ko {X : Map.OrderedType} = struct
  let test = ref "test"
end;;

module Pure2_ok {X : Map.OrderedType} = struct
  module M () = Map.Make(X)
end;;

module Pure2_ko {X : Map.OrderedType} = struct
  module M = Map.Make(X)
end;;

module Pure3_ok {X : Map.OrderedType} = struct
  module P = Pure2_ok{X}
  module M = P.M
end;;

module Pure3_ko {X : Map.OrderedType} = struct
  module P = Pure2_ok{X}
  module M = P.M()
end;;

(* Implicit parameters type escape *)
module Escape1_ok {X : sig type t val x : t end} = struct
  type t = X.t
  let x : t = X.x
end;;

module Escape1_ko {X : sig type t val x : t end} = struct
  let x = X.x
end;;

(* Virtual parameters *)

module Virtual0_ok {virtual X : sig end} = struct end;;

module Virtual1_ok {virtual X : sig type t end} = struct end;;

module Virtual1_ko {virtual X : sig val x : int end} = struct end;;

module Virtual2_ok {virtual X : sig module X : sig end end} = struct end;;

module Virtual3_ok {virtual X : sig module X : sig type t end end} = struct end;;

module Virtual3_ko {virtual X : sig module X : sig val x : int end end} = struct end;;

(* Same on module types *)

module type Escape1_ok =
  functor {X : sig type t val x : t end} -> sig type t = X.t val x : t end

module type Escape1_ko =
  functor {X : sig type t val x : t end} -> sig val x : X.t end

module type Virtual0_ok = functor {virtual X : sig end} -> sig end;;

module type Virtual1_ok = functor {virtual X : sig type t end} -> sig end;;

module type Virtual1_ko = functor {virtual X : sig val x : int end} -> sig end;;

module type Virtual2_ok = functor {virtual X : sig module X : sig end end} -> sig end;;

module type Virtual3_ok = functor {virtual X : sig module X : sig type t end end} -> sig end;;

module type Virtual3_ko = functor {virtual X : sig module X : sig val x : int end end} -> sig end;;
