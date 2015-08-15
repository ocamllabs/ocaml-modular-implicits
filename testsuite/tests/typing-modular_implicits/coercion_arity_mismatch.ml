(* Issue #10 *)
module type S = sig type t end;;
module type T = sig type _ t end;;
let f (x : {X : S} -> X.t) () = (x :> {X : T} -> unit X.t);;
