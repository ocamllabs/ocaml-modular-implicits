module type STRINGIFY = sig type t val to_string : t -> string end;;

(* Define "overloaded" string function *)
let to_string (implicit M : STRINGIFY) x = M.to_string x;;

(* Locally bind implicit instance *)
let g (x : int) =
  let implicit module Int = struct
    type t = int
    let to_string = string_of_int
  end in
  to_string x;;

(* M is implicitly rebind inside f *)
let f (implicit M : STRINGIFY) (x : M.t) = to_string x;;

(* Global instance *)
implicit module S = struct type t = string let to_string x = x end;;

print_endline (to_string "4");;

print_endline (f "4");;

print_endline (g 4);;

let x = assert (to_string "4" = f "4" && to_string "4" = g 4) in x;;
