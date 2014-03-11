external ( = ) : 'a -> 'a -> bool = "%equal"
external ( + ) : int -> int -> int = "%addint"

type 'a t = F of ('a t -> 'a -> 'a)
let f (F g) h x = g (F g) h (h x)
let iter h x = f (F f) h x

let _ = iter (fun x -> if x = 33 then assert false else x+1) 0
