module type NUM = sig 
  type t
  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( * ) : t -> t -> t
  val ( / ) : t -> t -> t
  val (~- ) : t -> t
  val zero : t
  val one : t
  val of_int : int -> t
end;;

module NUM = struct
  let ( + ) (implicit M : NUM) = M.( + )
  let ( - ) (implicit M : NUM) = M.( - )
  let ( * ) (implicit M : NUM) = M.( * )
  let ( / ) (implicit M : NUM) = M.( / )
  let (~- ) (implicit M : NUM) = M.(~- )
  let zero  (implicit M : NUM) = M.zero
  let one   (implicit M : NUM) = M.one
  let (~~)  (implicit M : NUM) = M.of_int
end;;

module type ORD = sig
  type t
  val ( =  ) : t -> t -> bool
  val ( <> ) : t -> t -> bool
  val ( <  ) : t -> t -> bool
  val ( <= ) : t -> t -> bool
  val ( >  ) : t -> t -> bool
  val ( >= ) : t -> t -> bool
end;;

module ORD = struct
  let ( =  ) (implicit M : ORD) = M.( =  )
  let ( <> ) (implicit M : ORD) = M.( <> )
  let ( <  ) (implicit M : ORD) = M.( <  )
  let ( <= ) (implicit M : ORD) = M.( <= )
  let ( >  ) (implicit M : ORD) = M.( >  )
  let ( >= ) (implicit M : ORD) = M.( >= )
end;;

implicit module Int = struct
  type t = int
  let ( + ),( - ),( * ), ( / ), (~- ) = ( + ),( - ),( * ), ( / ), (~- )
  let zero = 0
  let one = 1
  let of_int x = x
  let (( =  ), ( <> ), ( <  ), ( <= ), ( >  ), ( >= ))
    : (t -> t -> bool)
    * (t -> t -> bool)
    * (t -> t -> bool)
    * (t -> t -> bool)
    * (t -> t -> bool)
    * (t -> t -> bool)
    = ( =  ), ( <> ), ( <  ), ( <= ), ( >  ), ( >= ) 
end;;

implicit module Float = struct
  type t = float
  let ( + ),( - ),( * ), ( / ), (~- ) = ( +.),( -.),( *.), ( /.), (~-.)
  let zero = 0.
  let one = 1.
  let of_int = float_of_int
  let (( =  ), ( <> ), ( <  ), ( <= ), ( >  ), ( >= ))
    : (t -> t -> bool)
    * (t -> t -> bool)
    * (t -> t -> bool)
    * (t -> t -> bool)
    * (t -> t -> bool)
    * (t -> t -> bool)
    = ( =  ), ( <> ), ( <  ), ( <= ), ( >  ), ( >= )
end;;

implicit functor PairNUM (A : NUM) (B : NUM) = struct
  type t = A.t * B.t
  let ( + ) (a1,b1) (a2,b2) = (A.( + ) a1 a2, B.( + ) b1 b2)
  let ( - ) (a1,b1) (a2,b2) = (A.( - ) a1 a2, B.( - ) b1 b2)
  let ( * ) (a1,b1) (a2,b2) = (A.( * ) a1 a2, B.( * ) b1 b2)
  let ( / ) (a1,b1) (a2,b2) = (A.( / ) a1 a2, B.( / ) b1 b2)
  let (~- ) (a1,b1) = (A.(~- ) a1, B.(~- ) b1)
  let zero = A.zero, B.zero
  let one = A.one, B.zero
  let of_int i = A.of_int i, B.zero
end;;

implicit functor PairORD (A : ORD) (B : ORD) = struct
  type t = A.t * B.t
  let ( =  ) (a1,b1) (a2,b2) = A.(=) a1 a2 && B.(=) b1 b2
  let ( <> ) (a1,b1) (a2,b2) = A.(<>) a1 a2 || B.(<>) b1 b2
  let ( <  ) (a1,b1) (a2,b2) = A.(<) a1 a2  || (A.(=) a1 a2 && B.(<) b1 b2  )
  let ( <= ) (a1,b1) (a2,b2) = A.(<=) a1 a2 || (A.(=) a1 a2 && B.(<=) b1 b2 )
  let ( >  ) (a1,b1) (a2,b2) = A.(>) a1 a2  || (A.(=) a1 a2 && B.(>) b1 b2  )
  let ( >= ) (a1,b1) (a2,b2) = A.(>=) a1 a2 || (A.(=) a1 a2 && B.(>=) b1 b2 )
end;;

open NUM;;
open ORD;;

assert ( ~~2 / ~~3 = 0
      && ~~2 / ~~3 = 0.666666666666666666666666666666666666);;

(1, -1.) + (2, -2.);;
