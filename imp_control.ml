module type Functor = sig
  type 'a t
  val fmap : ('a -> 'b) -> 'a t -> 'b t
end

module Functor = struct
  let fmap (implicit M : Functor) = M.fmap
end

module type Applicative = sig
  include Functor
  val pure : 'a -> 'a t
  val apply : ('a -> 'b) t -> 'a t -> 'b t
end

module Applicative = struct
  let pure (implicit M : Applicative) = M.pure
  let apply (implicit M : Applicative) = M.apply
end

module type Monad = sig
  include Functor
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end

module Monad = struct
  let return (implicit M : Monad) = M.return
  let bind (implicit M : Monad) = M.bind
end

module type Monad_plus = sig
  include Monad
  val mzero : unit -> 'a t
  val mplus : 'a t -> 'a t -> 'a t
end

module Monad_plus = struct
  let mzero (implicit M : Monad_plus) = M.mzero
  let mplus (implicit M : Monad_plus) = M.mplus

  let mguard (implicit M : Monad_plus) b =
    if b then
      M.return ()
    else
      M.mzero ()
end

module type Foldable = sig
  type 'a t
  val fold : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
end

module Foldable = struct
  let fold (implicit F : Foldable) = F.fold
end

module type Traversable = sig
  include Functor
  val traverse : (implicit F : Applicative) ->
                 ('a -> 'b F.t) -> 'a t -> 'b t F.t
end

module Traversable = struct
  let traverse (implicit T : Traversable) = T.traverse
end

implicit module Option = struct
  type 'a t = 'a option

  (* Functor *)
  let fmap f = function
    | None -> None
    | Some a -> Some (f a)

  (* Applicative *)
  let pure x = Some x
  let apply f x = match f, x with
    | Some f, Some x -> Some (f x)
    | _, _ -> None

  (* Monad *)
  let return x = Some x
  let bind x f = match x with
    | None -> None
    | Some x -> f x

  (* Monad_plus *)
  let mzero = None
  let mplus a b = match a with
    | None -> b
    | Some _ -> a

  (* Foldable *)
  let fold f t acc = match t with
    | None -> acc
    | Some x -> f x acc

  (* Traversable *)
  let traverse (implicit F : Applicative) f = function
    | None -> F.pure None
    | Some x -> F.apply (F.pure (fun x -> Some x)) (f x)
end

implicit module List = struct
  type 'a t = 'a list

  (* Functor *)
  let fmap = List.map

  (* Monad *)
  let return x = [x]
  let bind x f =
    let rec aux acc = function
      | x :: xs -> aux (x @ acc) xs
      | [] -> acc in
    aux [] (List.rev_map f x)

  (* Applicative *)
  let pure x = [x]
  let apply fs xs = bind fs (bind xs)

  (* Monad_plus *)
  let mzero = []
  let mplus = (@)

  (* Foldable *)
  let rec fold f t acc = match t with
    | [] -> acc
    | x :: xs -> fold f xs (f x acc)

  (* Traversable *)
  let traverse (implicit F : Applicative) f t =
    let cons = F.pure (fun x xs -> x :: xs) in
    let cons x xs = F.apply (F.apply cons (F.pure (f x))) xs in
    fold cons t (F.pure [])
end

