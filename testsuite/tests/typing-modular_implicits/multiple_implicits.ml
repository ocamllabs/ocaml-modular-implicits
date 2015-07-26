(* Issue #1 *)
module type T = sig type a end
;;

let f : {A: T} -> {B: T} -> A.a * B.a -> unit =
  fun {A : T} {B : T} (x : A.a * B.a) -> ()
;;
