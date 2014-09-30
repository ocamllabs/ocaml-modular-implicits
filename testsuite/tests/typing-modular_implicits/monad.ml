module type Monad = sig
  type 'a t
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end;;

let return (implicit M : Monad) x = M.return x;;

let (>>=) (implicit M : Monad) m k = M.bind m k;;

implicit module ListMonad = struct
  type 'a t = 'a list
  let return x = [x]
  let bind x f =
    let rec aux acc = function
      | x :: xs -> aux (x @ acc) xs
      | [] -> acc in
    aux [] (List.rev_map f x)
end;;

implicit module OptionMonad = struct
  type 'a t = 'a option
  let return x = Some x
  let bind x f = match x with
    | None -> None
    | Some x -> f x
end;;

(* Ambiguous *)
let a = (return 5) >>= fun x -> return x;;

let l : 'a list = (return 5) >>= fun x -> return x;;

let o : 'a option = (return 5) >>= fun x -> return x;;

let m = [1; 2; 3] >>= fun x -> return x;;

let n = return 5 >>= fun x -> [x; 2; 3];;

(* Various implementations of sequence to test the handling of recursion *)
let rec sequence : (implicit M : Monad) -> 'a M.t list -> 'a list M.t =
  fun (implicit M : Monad) (x : 'a M.t list) ->
    match x with
    | [] -> (return [] : 'a list M.t)
    | x :: xs ->
        x >>= fun y ->
        sequence xs >>= fun ys ->
          return (y :: ys);;

let rec sequence : type a. (implicit M : Monad) -> a M.t list -> a list M.t =
  fun (implicit M : Monad) (x : a M.t list) ->
    match x with
    | [] -> (return [] : a list M.t)
    | x :: xs ->
        x >>= fun y ->
        sequence xs >>= fun ys ->
          return (y :: ys);;

let rec sequence : (implicit M : Monad) -> 'a M.t list -> 'a list M.t =
  fun (implicit M : Monad) x ->
    match x with
    | [] -> return []
    | x :: xs ->
        x >>= fun y ->
        sequence xs >>= fun ys ->
          return (y :: ys);;

let rec sequence : 'a. (implicit M : Monad) -> 'a M.t list -> 'a list M.t =
  fun (implicit M : Monad) x ->
    match x with
    | [] -> return []
    | x :: xs ->
        x >>= fun y ->
        sequence xs >>= fun ys ->
          return (y :: ys);;

let rec sequence : type a. (implicit M : Monad) -> a M.t list -> a list M.t =
  fun (implicit M : Monad) x ->
    match x with
    | [] -> return []
    | x :: xs ->
        x >>= fun y ->
        sequence xs >>= fun ys ->
          return (y :: ys);;

let rec sequence : (implicit M : Monad) -> 'a M.t list -> 'a list M.t =
  fun (implicit M : Monad) x ->
    match x with
    | [] -> M.return []
    | x :: xs ->
        M.bind x (fun y ->
        M.bind (sequence xs) (fun ys ->
          M.return (y :: ys)));;

let rec sequence : 'a. (implicit M : Monad) -> 'a M.t list -> 'a list M.t =
  fun (implicit M : Monad) x ->
    match x with
    | [] -> M.return []
    | x :: xs ->
        M.bind x (fun y ->
        M.bind (sequence xs) (fun ys ->
          M.return (y :: ys)));;

let rec sequence : type a. (implicit M : Monad) -> a M.t list -> a list M.t =
  fun (implicit M : Monad) x ->
    match x with
    | [] -> M.return []
    | x :: xs ->
        M.bind x (fun y ->
        M.bind (sequence xs) (fun ys ->
          M.return (y :: ys)));;
