open Common_types
open Locations
open Data

type 'a locm = 'a Locm.t

(* The environment *)
type environment =
  | Bottom
  | Env of env_descr
and env_descr = 
  {
    entries: locs TIdm.t;
    values : Data.t locm;
  }


(* Environment management *)

let is_bottom = function
  | Bottom -> true
  | _ -> false

let bottom = Bottom
let empty =
  Env {
    entries = TIdm.empty;
    values = Locm.empty;
  }

let no_bottom str f = function
  | Bottom -> Format.eprintf "Bottom error on %s@." str; assert false
  | Env e -> f e

(* Joining and widening helper *)

let merger_rec f _ x y =
  match x, y with
  | None, a| a, None -> a
  | Some a, Some b -> Some (f a b)

let merger_locs = merger_rec Locs.union

let merger_simple x y = merger_rec (fun a b -> assert (a=b); a) x y

let join_or_widen (union: Data.t -> Data.t -> Data.t) e1 e2 =
  match e1, e2 with
  | Bottom, e | e, Bottom -> e
  | Env d1, Env d2 ->
    let entries = TIdm.merge merger_locs d1.entries d2.entries in
    let values = Locm.merge (merger_rec union) d1.values d2.values in
    Env { values; entries }


(* Environment joining *)

let join e1 e2 = join_or_widen union e1 e2

(* Environment joining with widening *)

let widening e1 e2 = join_or_widen widening e1 e2




(* Garbage collection *)

(* let gc roots env = *)
(*   let dep_blocks b res = *)
(*     Tagm.fold (fun _ t res -> *)
(*         Intm.fold *)
(*           (fun _ a res -> *)
(*              Array.fold_left (fun res ids -> List.rev_append (Ids.elements ids) res ) res a *)
(*           ) t res *)
(*       ) b res *)
(*   and dep_funs f res = *)
(*     Fm.fold (fun _ a res -> *)
(*         Array.fold_left (fun res ids -> List.rev_append (Ids.elements ids) res ) res a *)
(*       ) f res *)
(*   and dep_expr es res = *)
(*     Hinfos.fold (fun e res -> *)
(*         match e with *)
(*         | Var x *)
(*         | Lazyforce x -> x :: res *)
(*         | App_prep ( x, y ) *)
(*         | Send ( x, y ) ->  x :: y :: res *)
(*         | Constraint _ *)
(*         | Const _ -> res *)
(*         | Prim ( _, l ) *)
(*         | Ccall ( _, l )-> *)
(*           List.rev_append l res *)
(*         | App_return | App_exn | Return _ | Retexn _ -> failwith "TODO: GC function return" *)
(*         | App -> assert false *)
(*       ) *)
(*       es res *)
(*   in *)
(*   let dependancies id idm = *)
(*     let d = Idm.find id idm in *)
(*     dep_blocks d.blocks ( dep_funs d.f ( dep_expr d.expr [] ) ) *)
(*   in *)
(*   let rec add_with_dependants id idm res = *)
(*     if mem_env id res *)
(*     then res *)
(*     else *)
(*       let res = set_env id (Idm.find id idm) res in *)
(*       aux res idm (dependancies id idm) *)
(*   and aux res idm = function *)
(*     | [] -> res *)
(*     | id :: tl -> *)
(*       aux ( add_with_dependants id idm res ) idm tl *)
(*   in *)
(*   match env with *)
(*     Bottom -> Bottom *)
(*   | Env m -> aux empty m roots *)

