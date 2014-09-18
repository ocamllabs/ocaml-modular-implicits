(* Issue #1 *)
module type T = sig type a end
;;

let f : (implicit A: T) -> (implicit B: T) -> A.a * B.a -> unit =
  fun (implicit A : T) (implicit B : T) (x : A.a * B.a) -> ()
;;
