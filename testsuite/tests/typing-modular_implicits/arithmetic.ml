type z = Z
type 'n s = S of 'n

module type N = sig type n val n : n end
implicit module Z : N with type n = z = struct type n = z let n = Z end
implicit functor S(N:N) : N with type n = N.n s = struct type n = N.n
s let n = S N.n end

module type ADD =
sig
  type a and b and c
  val a : a
  val b : b
  val c : c
end

let add (implicit Add: ADD) (a: Add.a) (b : Add.b) : Add.c = Add.c

implicit functor AddZ (B: N) : ADD with type a = z
                                    and type b = B.n
                                    and type c = B.n =
struct
  type a = z and b = B.n and c = B.n
  let  a = Z and b = B.n and c = B.n
end

implicit functor AddS (A: N) (B: N) (Add : ADD with type a = A.n and
type b = B.n)
       : ADD with type a = A.n s
              and type b = B.n
              and type c = Add.c s =
struct
  type a = A.n s and b = B.n and c = Add.c s
  let  a = S A.n and b = B.n and c = S Add.c
end
;;

(* Stress Implicitsearch.translpath
   Resolved code: add (implicit AddS(Z)(Z)(AddZ(Z))) (S Z) Z *)
add (S Z) Z
;;
