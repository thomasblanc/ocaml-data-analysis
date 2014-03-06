let f x = 5+x

let a = f 3

(* let _ = assert false *)

let rec rev acc = function
  | h::t -> rev (h::acc) t
  | [] -> acc

let _ = assert false

let rev l = rev [] l

let l = [1;2;3;4]

let l' = rev l

exception E1
exception E2

let () =
  match l' with
  | [] -> raise E1
  | 5::_ -> raise E2
  | _ -> assert false
