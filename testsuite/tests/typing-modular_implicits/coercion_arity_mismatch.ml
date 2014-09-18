(* Issue #10 *)
module type S = sig type t end;;
module type T = sig type _ t end;;
let f (x : (implicit X:S) -> X.t) () = (x :> (implicit X:T) -> unit X.t);;
