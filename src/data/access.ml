open Common_types
open Locations
open Envs

let ignore_bottom f e = e >? f

(* basic env management *)

let loc_of_tid tid = Locations.of_tid tid

(* let set_env id data = *)
(*   no_bottom "set_env" *)
(*     (fun env -> *)
(*        let i = i_of_id id in *)
(*        Env { *)
(*          entries = TIdm.add id (Locs.singleton i) env.entries; *)
(*          values = Locm.add i data env.values; *)
(*        } *)
(*     ) *)

(* let set_data i data = *)
(*   no_bottom "set_data" *)
(*     (fun env -> Env { env with values = Locm.add i data env.values }) *)

let fold_to_on f env loc d e = Envs.join (f loc d env) e
let on_first_acc = Envs.bottom

let fold_loc f loc acc env =
  Locm.fold_key f loc env.values acc

let on_loc f loc e env =
  fold_loc (fold_to_on f env) loc e env

let fold_locs f locs acc (env:Envs.t') =
  Locs.fold f locs acc

let fold__locs f locs acc (env:Envs.t') =
  fold_locs (fun loc acc -> fold_loc f loc acc env) locs acc env

let on__locs f locs env =
  fold__locs (fold_to_on f env) locs on_first_acc env

let fold_tid f tid acc env =
  let locs = TIdm.find tid env.entries in
  fold__locs f locs acc env

let on_tid f tid env =
  fold_tid (fold_to_on f env) tid on_first_acc env

let set_data loc d env =
  Env { env with values = Locm.add loc d env.values }

let set_env tid d env =
  let loc = loc_of_tid tid in
  !> {
    entries = TIdm.add tid (Locs.singleton loc) env.entries;
    values = Locm.add loc d env.values;
  }


let get_idents tid env = TIdm.find tid env.entries
let set_idents tid locs env = !> { env with entries = TIdm.add tid locs env.entries }
let set_ident tid loc env = set_idents tid (Locs.singleton loc) env

let reg_data d env =
  let loc = loc_of_tid (TId.create ()) in
  set_data loc d env, loc

let rm_env tid env =
  !> { env with entries = TIdm.remove tid env.entries }


(* let get_env id = *)
(*   no_bottom "set_env" *)
(*     (fun env -> *)
(*        try Locm.find (TIdm.find id env.entries) env.values *)
(*        with Not_found -> bottom ) *)

(* let get_idents id = *)
(*   no_bottom "get_idents" *)
(*     (fun env -> TIdm.find id env.entries) *)

(* let set_idents id locs = *)
(*   no_bottom "set_idents" *)
(*     (fun env -> TIdm.add id locs env.entries) *)

(* let get_ident id env = *)
(*   let locs = get_idents id env in *)
(*   if Locs.cardinal locs = 1 *)
(*   then Some (Locs.choose locs) *)
(*   else None *)

(* let get_data i = *)
(*   no_bottom "get_data" *)
(*     (fun env -> try Locm.find i env.values with Not_found -> bottom ) *)

(* let reg_data data env = *)
(*   let i = loc_of_tid (TId.create ()) in *)
(*   ( set_data i data env, i) *)

(* let reg_env id = *)
(*   no_bottom "reg_env" *)
(*     (fun env -> *)
(*        let i = loc_of_tid id in *)
(*        Env { env with entries = TIdm.add id (Locs.singleton i) env.entries }, i) *)

(* let reg_ident i = *)
(*   no_bottom "reg_ident" *)
(*     (fun env -> *)
(*        let id = TId.create () in *)
(*        Env { env with entries = TIdm.add id (Locs.singleton i) env.entries; }, id) *)

(* let mem_env id = *)
(*   no_bottom "mem_env" *)
(*     (fun m -> TIdm.mem id m.entries && *)
(*               Locs.for_all (fun i -> Locm.mem i m.values) *)
(*                 (TIdm.find id m.entries) ) *)

(* let mem_data i = *)
(*   no_bottom "mem_data" *)
(*     (fun m -> Locm.mem i m.values) *)

(* (\* let cp_data i env = *\) *)
(* (\*   reg_data (get_data i env) env *\) *)

(* let rm_env id = *)
(*   no_bottom "rm_env" (fun m -> Env {m with entries = TIdm.remove id m.entries} ) *)
