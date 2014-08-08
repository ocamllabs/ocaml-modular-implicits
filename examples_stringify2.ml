module type STRINGIFY = sig type t val to_string : t -> string end
let to_string (implicit M : STRINGIFY) (xs : M.t) = M.to_string xs;;

implicit module StringifyString = struct 
  type t = string
  let to_string x = "\"" ^ String.escaped x ^ "\""
end

implicit functor StringifyList (X : STRINGIFY) = struct
  type t = X.t list
  let to_string xs = "[" ^ String.concat "; " (List.map X.to_string xs) ^ "]"
end 

implicit module StringifyInt = struct
  type t = int
  let to_string = string_of_int
end

implicit functor StringifyPair (A : STRINGIFY) (B : STRINGIFY) = struct
  type t = A.t * B.t 
  let to_string (a,b) = "(" ^ A.to_string a ^ "," ^ B.to_string b ^ ")"
end;;

print_endline (to_string "a");;
print_endline (to_string ["a";"b";"c"]);;
print_endline (to_string [1;2;3]);;
print_endline (to_string (1,"lol"));;
print_endline (to_string [1, "a";2, "b";3, "c"]);;
