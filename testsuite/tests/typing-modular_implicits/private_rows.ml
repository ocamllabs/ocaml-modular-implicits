module type Show = sig type t val show : t -> string end

let show {M : Show} = M.show

implicit module ShowObj {X : sig type x = private < show : string; .. > end} = struct
  type t = X.x
  let show (o : t) = o#show
end

implicit module X = struct
  type x = < show : string >
end
;;

let obj = object method show = "show" end
;;

show obj
;;

class type show = object method show : string end
;;

let f (obj : #show) =
  print_endline (show obj)
;;

let g (obj : #show) =
  print_endline (show {ShowObj{X}} obj)
;;

f obj;;
g obj;;
