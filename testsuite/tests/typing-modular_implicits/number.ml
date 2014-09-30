module type Num = sig
  type t
  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( * ) : t -> t -> t
  val ( / ) : t -> t -> t
  val (~- ) : t -> t
end;;

let ( + ) (implicit N : Num) = N.( + );;
let ( - ) (implicit N : Num) = N.( - );;
let ( * ) (implicit N : Num) = N.( * );;
let ( / ) (implicit N : Num) = N.( / );;
let (~- ) (implicit N : Num) = N.(~- );;

implicit module Int = struct
  type t = int
  open Pervasives
  let ( + ), ( - ), ( * ), ( / ), (~- ) =
      ( + ), ( - ), ( * ), ( / ), (~- )
end;;

implicit module Float = struct
  type t = float
  let ( + ), ( - ), ( * ), ( / ), (~- ) =
      ( +. ), ( -. ), ( *. ), ( /. ), (~-. )
end;;

let x = 1 + 4 + 5 / 5;;

let y = 1.2 + 4.4 + 5.9 / 6.2;;

let sq (implicit N : Num) (x : N.t) = x * x;;

let a = sq 4.9;;

let b = sq 6;;
