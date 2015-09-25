module type T1 = sig type _ t end

module Eq :
sig
  type (_, _) eq

  val refl : ('a, 'a) eq
  val cast : ('a, 'b) eq -> 'a -> 'b
  val lift : ('a, 'b) eq -> (implicit T:T1) -> ('a T.t, 'b T.t) eq
  val symm : ('a, 'b) eq -> ('b, 'a) eq
  val trans : ('a, 'b) eq -> ('b, 'c) eq -> ('a, 'c) eq
end =
struct
  implicit module Id = struct type 'a t = 'a end

  type ('a, 'b) eq = (implicit T: T1) -> 'a T.t -> 'b T.t

  let refl (implicit T: T1) (x : _ T.t) = x
  let cast (eq : (_, _) eq) = eq (implicit Id)
  let lift (eq : (_, _) eq) (implicit T:T1) (implicit U:T1) =
    let module TU = struct type 'a t = 'a T.t U.t end in eq (implicit TU)
  let symm (type a) (type b) (eq : (a, b) eq) =
    let module R = struct type 'a t = ('a, a) eq end in
    lift eq (implicit R) (implicit Id) refl
  let trans ab bc (implicit T : T1) x =
    lift bc (implicit T) (implicit Id) (lift ab (implicit T) (implicit Id) x)
end;;
