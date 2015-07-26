
module type T = sig type t val x : t end;;

(* BAD *)
let f () =
  let x = ref [] in
  let g {M : T} () = x := [M.x] in
    ();;

(* BAD *)
let f (x : 'a) {M : T} =
  (x : M.t);
  ();;

(* OK *)
let f {M : T} (x : M.t) y =
  (y : M.t);
  ();;

(* OK *)
let rec f {M : T} (x : M.t) = ();;

(* OK *)
let rec f {M : T} (x : M.t) y =
  (y : M.t);
  ();;

(* BAD *)
let f : {M : T} -> 'a -> unit =
  fun {M : T} (x : M.t) -> ();;

(* OK *)
let f (g : {M : T} -> M.t -> unit) () = ();;

(* OK *)
let f {M : T} {N : T} = N.x;;
