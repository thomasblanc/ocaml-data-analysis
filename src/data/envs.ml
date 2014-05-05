open Locations
open Data

type 'a locm = 'a Locm.t

(* The environment *)
type t =
  | Bottom
  | Env of t'
and t' = 
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

let (!!) = function
  | Bottom -> assert false
  | Env e -> e

let (>!) e f = f (!!e)
let (>?) e f = match e with
  | Bottom -> Bottom
  | Env e -> f e

let (>>?) e def f = match e with
  | Bottom -> def
  | Env e -> f e

let (!>) e = Env e

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
let (>+) = join

(* Environment joining with widening *)

(* let widening e1 e2 = join_or_widen widening e1 e2 *)

(* total location set *)

module Atpls = Utils.Set.Make (
  struct
    type t = atpl
    let compare = Pervasives.compare
    let print = print_atpl
  end)


let widening e1 e2 =
  let fold_helper loc e loct =
    Locm.fold_key
      (fun loc d (dt,loct) -> Data.union d dt, Atpls.add loc loct)
      loc e.values (Data.bottom, loct)
  in
  match e1, e2 with
  | Bottom, a | a, Bottom -> a
  | Env e1, Env e2 ->
    let entries = TIdm.merge merger_locs e1.entries e2.entries in
    let values = Locm.fold_by_loc
        (fun loc values ->
           let d1, loct = fold_helper loc e1 Atpls.empty in
           let d2, loct = fold_helper loc e2 loct in
           let d3 = Data.widening d1 d2 in
           Atpls.fold (fun loc values -> Locm.add loc d3 values) loct values
        ) e1.values e2.values in
    !> { entries; values; }



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

