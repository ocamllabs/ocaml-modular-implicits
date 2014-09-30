module type Show = sig
  type t
  val show : t -> string
end;;

let show (implicit S : Show) x = S.show x;;

let print (implicit S : Show) (x : S.t) =
  print_endline (show x);;

implicit module ShowString = struct
  type t = string
  let show x = "\"" ^ x ^ "\""
end;;

implicit module ShowInt = struct
  type t = int
  let show x = string_of_int x
end;;

print_endline (show "4");;

print 5;;


implicit functor StringifyPair (A : Show) (B : Show) = struct
  type t = A.t * B.t
  let show (a,b) = "(" ^ A.show a ^ "," ^ B.show b ^ ")"
end;;

implicit functor StringifyList (X : Show) = struct
  type t = X.t list
  let show xs = "[" ^ String.concat "; " (List.map X.show xs) ^ "]"
end

let () = print [("hello", 1); ("world", 2)];;

let g (x : float) =
  let implicit module Float = struct
    type t = float
    let show = string_of_float
  end in
  show x;;

let () = print_endline (g 5.5)
