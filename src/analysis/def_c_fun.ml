open Envs

module P =
struct
  type t = string
  let hash ( d : t) = Hashtbl.hash d
  let equal (a:t) (b:t) = a = b
  let print = Format.pp_print_string
end

module HP = Utils.Htbl.Make ( P )

type fun_applyer =
    Common_types.tid list ->
    Common_types.tid ->
    Envs.t ->
    Envs.t * Envs.t

let defs : fun_applyer HP.t = HP.create 1024

let default = fun _ i e -> ( e >! Access.set_env i Data.top, Envs.bottom)

let get_envs d =
  try HP.find defs d.Primitive.prim_name with
    _ -> default

let add_def = HP.add defs
