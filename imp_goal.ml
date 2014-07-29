module type Goalish = sig
  type t
  val x : int -> t
end
implicit module Goal_string = struct
  type t = string -> string
  let x n s = "g" ^ String.make n 'o' ^ s
end
implicit functor Goal_unit (G : Goalish) = struct
  type t = unit -> G.t
  let x n () = G.x (n + 1)
end
let g (implicit G : Goalish) = G.x 0;;

let () =
  print_endline (g "al");
  print_endline (g () "al");
  print_endline (g () () "al");
  print_endline (g () () () "al");
  print_endline (g () () () () "al");
  print_endline (g () () () () () "al");
