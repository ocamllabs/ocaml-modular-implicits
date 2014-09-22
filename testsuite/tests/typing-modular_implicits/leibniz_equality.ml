module type T1 = sig type _ t end

module Eq :
sig
  type (_, _) eq

  val refl : ('a, 'a) eq
  val cast : ('a, 'b) eq -> 'a -> 'b
  val lift : ('a, 'b) eq -> {T : T1} -> ('a T.t, 'b T.t) eq
  val symm : ('a, 'b) eq -> ('b, 'a) eq
  val trans : ('a, 'b) eq -> ('b, 'c) eq -> ('a, 'c) eq
end =
struct
  implicit module Id = struct type 'a t = 'a end

  type ('a, 'b) eq = {T: T1} -> 'a T.t -> 'b T.t

  let refl {T: T1} (x : _ T.t) = x
  let cast (eq : (_, _) eq) = eq {Id}
  let lift (eq : (_, _) eq) {T : T1} {U : T1} =
    let module TU = struct type 'a t = 'a T.t U.t end in eq {TU}
  let symm (type a) (type b) (eq : (a, b) eq) =
    let module R = struct type 'a t = ('a, a) eq end in
    lift eq {R} {Id} refl
  let trans ab bc {T : T1} x =
    lift bc {T} {Id} (lift ab {T} {Id} x)
end;;
