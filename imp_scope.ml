module type Manageable = sig
  type 'a t
  type 'a value
  type 'a lock

  val acquire : 'a t -> 'a lock * 'a value
  val release : 'a lock -> unit
end

let with_resource (implicit M : Manageable) r f =
  let lock, value = M.acquire r in
  try
    let result = f value in
    M.release lock;
    result
  with exn ->
    M.release lock;
    raise exn

implicit module In_channel = struct
  type 'a t     = in_channel
  type 'a value = in_channel
  type 'a lock  = in_channel
  let acquire c = c, c
  let release c = close_in_noerr c
end

implicit module Out_channel = struct
  type 'a t     = out_channel
  type 'a value = out_channel
  type 'a lock  = out_channel
  let acquire c = c, c
  let release c = close_out_noerr c
end
