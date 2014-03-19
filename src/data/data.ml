(* The atomic types *)
open Utils
open Common_types

module DId = MakeId (struct end)

type id = DId.t

type constant = Constants.t

open Constants

type tag = int

type f = F.t

module Ints = Set.Make (struct type t = int let compare = compare let print = Format.pp_print_int end)
module Intm = Map.Make (struct type t = int let compare = compare let print = Format.pp_print_int end)

module Tagm = Map.Make (struct type t = tag let compare = compare let print = Format.pp_print_int end)

module Idm = Map.Make (DId)
module Ids = Set.Make (DId)

module TIdm = Map.Make (TId)

module Fm = Map.Make (F)

module Hinfos = Set.Make (struct type t = hinfo let compare = compare let print _ _ = () end)

type array_descr =
  {
    a_elems: Ids.t;
    a_size: Int_interv.t;
    a_float: bool;
    a_gen: bool;
    a_addr: bool;
    a_int: bool;
  }

(* The data *)

type data =
  {
    top : bool;
    int : Int_interv.t;
    float : simple;
    string : simple;
    i32 : simple;
    i64 : simple;
    inat : simple;
    cp : Ints.t;
    blocks : Ids.t array Intm.t Tagm.t; (* referenced by tag, then by size *)
    arrays : array_descr;
    f : Ids.t array Fm.t;
    expr : Hinfos.t;
  }

(* The environment *)
type environment =
  | Bottom
  | Env of env_descr
and env_descr = 
  {
    entries: id TIdm.t;
    values : data Idm.t;
  }

let simple_bottom = Constants Constants.empty

let bottom =
  {
    top = false;
    int = Int_interv.bottom;
    float = simple_bottom;
    string = simple_bottom;
    i32 = simple_bottom;
    i64 = simple_bottom;
    inat = simple_bottom;
    cp = Ints.empty;
    blocks = Tagm.empty;
    arrays = {
      a_elems = Ids.empty; a_size = Int_interv.bottom;
      a_float = false; a_gen = false; a_addr = false; a_int = false;
    };
    f = Fm.empty;
    expr = Hinfos.empty;
  }

let top = { bottom with top = true; }

let is_top { top; _ } = top


(* basic env management *)

let no_bottom str f = function
  | Bottom -> Format.eprintf "Bottom error on %s@." str; assert false
  | Env e -> f e

let set_env id data =
  no_bottom "set_env"
    (fun env ->
       let i =
         match TId.name id with
         | None -> DId.create ()
         | Some name -> DId.create ~name ()
       in
       Env {
         entries = TIdm.add id i env.entries;
         values = Idm.add i data env.values;
       }
    )

let set_data i data =
  no_bottom "set_data"
    (fun env -> Env { env with values = Idm.add i data env.values })

let get_env id =
  no_bottom "set_env"
    (fun env ->
       try Idm.find (TIdm.find id env.entries) env.values
       with Not_found -> bottom )


let get_ident id =
  no_bottom "get_ident"
    (fun env -> TIdm.find id env.entries)

let get_data i =
  no_bottom "get_data"
    (fun env -> try Idm.find i env.values with Not_found -> bottom )

let reg_data data env =
  let i = DId.create () in
  ( set_data i data env, i)

let reg_env id =
  no_bottom "reg_env"
    (fun env ->
       let i = DId.create () in
       Env { env with entries = TIdm.add id i env.entries }, i)
let mem_env id =
  no_bottom "mem_env"
    (fun m -> TIdm.mem id m.entries && Idm.mem (TIdm.find id m.entries) m.values)

let mem_data i =
  no_bottom "mem_data"
    (fun m -> Idm.mem i m.values)

let cp_data i env =
  reg_data (get_data i env) env

let rm_env id =
  no_bottom "rm_env" (fun m -> Env {m with entries = TIdm.remove id m.entries} )

(* Bottom test *)

let ignore_first f _ = f
let array_for_all f a =
  let rec aux i =
    if i = Array.length a
    then true
    else f i a.(i) && aux (succ i)
  in aux 0

let is_bottom_simple = function
  | Top -> false
  | Constants c -> Constants.is_empty c

let rec is_bottom env { top; int; float; string; i32;
                    i64; inat; cp; blocks; arrays = { a_elems; a_size; }; f; } =
  top = false &&
  Int_interv.is_bottom int && is_bottom_simple float &&
  is_bottom_simple string &&
  is_bottom_simple i32 && is_bottom_simple i64 &&
  is_bottom_simple inat &&
  Ints.is_empty cp &&
  Tagm.for_all
    (ignore_first
       (Intm.for_all
          (ignore_first
             (array_for_all
                (ignore_first
                   (Ids.for_all (fun i -> is_bottom env (get_data i env)))
                )
             ))
       )) blocks &&
  ( Ids.is_empty a_elems || Int_interv.is_bottom a_size ) &&
  Fm.is_empty f




(* simple functions and values *)

let set_a i v a =
  let a = Array.copy a in
  a.(i) <- v;
  a

(* Union *)

let map_merge_helper f _ a b =
  match a, b with
  | x, None | None, x -> x
  | Some x, Some y -> Some ( f x y )

let array_merge_with ~unioner s1 s2 =
  Array.mapi (fun i i1 -> unioner i1 s2.(i)) s1

let block_merge_with ~unioner b1 b2 =
  Tagm.merge
    (map_merge_helper
       ( Intm.merge
           ( map_merge_helper (array_merge_with ~unioner) )
       )
    ) b1 b2

let array_descr_merge_with ~unioner ~integers a1 a2 =
  {
    a_elems = unioner a1.a_elems a2.a_elems;
    a_size = integers a1.a_size a2.a_size;
    a_float = a1.a_float || a2.a_float;
    a_gen = a1.a_gen || a2.a_gen;
    a_addr = a1.a_addr || a2.a_addr;
    a_int = a1.a_int || a2.a_int;
  }

let union_simple a b = match a, b with
  | Top, _ | _, Top -> Top
  | Constants s, Constants s' -> Constants ( Constants.union s s')

let merge_template ~unioner ~integers a b =
  if a.top || b.top
  then top
  else
    let blocks = block_merge_with ~unioner a.blocks b.blocks in
    let arrays = array_descr_merge_with ~unioner ~integers a.arrays b.arrays in
    let f = Fm.merge (map_merge_helper (array_merge_with ~unioner)) a.f b.f in
    {
      top = false;
      int = integers a.int b.int;
      float = union_simple a.float b.float;
      string = union_simple a.string b.string;
      i32 = union_simple a.i32 b.i32;
      i64 = union_simple a.i64 b.i64;
      inat = union_simple a.inat b.inat;
      cp = Ints.union a.cp b.cp;
      blocks; arrays; f;
      expr = Hinfos.union a.expr b.expr;
    }


let rec union a b =
  merge_template ~unioner:Ids.union ~integers:Int_interv.join a b

and union_id env i1 i2 =
  let  u = union (get_data i1 env) (get_data i2 env) in
  reg_data u env

let union_ids env ids =
  Ids.fold (fun a b -> union (get_data a env) b) ids ( bottom)

let fun_ids i env =
  Fm.fold (fun i _ l -> i::l ) (get_data i env).f []

let rec widening enva envb renvres a b =
  let unioner = widening_ids enva envb renvres in
  merge_template ~unioner ~integers:Int_interv.widening a b

and widening_ids enva envb renvres idsa idsb =
  if Ids.subset idsa idsb
  then idsb
  else
    let da = union_ids enva idsa in
    let db = union_ids envb idsb in
    let d = widening enva envb renvres da db in
    let envres, id = reg_data d !renvres in
    renvres := envres;
    Ids.singleton id

(* Inclusion test *)

let included_simple a b = match a, b with
  | Top, _ | _, Top -> true
  | Constants s, Constants s' -> Constants.exists ( fun a -> Constants.mem a s') s

let array2_forall f a b =
  let l = Array.length a in
  let rec aux i = i = l || f a.(i) b.(i) || aux (succ i) in
  aux 0

let rec included env i1 i2 =
  let a = get_data i1 env
  and b = get_data i2 env in
  if is_bottom env b
  then is_bottom env a
  else 
    b.top
    || a.top
    || Int_interv.is_leq a.int b.int
    || included_simple a.float b.float
    || included_simple a.string b.string
    || included_simple a.i32 b.i32
    || included_simple a.i64 b.i64
    || included_simple a.inat b.inat
    || Ints.exists (fun a -> Ints.mem a b.cp) a.cp
    || Tagm.exists
      (fun k a ->
         try
           let b = Tagm.find k b.blocks in
           Intm.exists
             (fun k a ->
                let b = Intm.find k b in
                array2_forall
                  (fun a b ->
                     Ids.exists
                       (fun a -> Ids.exists ( included env a) b)
                       a
                  )
                  a b
             ) a
         with Not_found -> false) a.blocks
    || ( Int_interv.is_leq a.arrays.a_size b.arrays.a_size && true (* TODO: the idsets and the atypes*) )
    || Fm.exists
      (fun k a ->
         try
           let b = Fm.find k b.f in
           array2_forall
             (fun a b ->
                Ids.exists
                  (fun a -> Ids.exists ( included env a) b)
                  a
             ) a b
         with Not_found -> false) a.f

(* Leq test *)

let leq_simple a b =
  match a, b with
  | _, Top -> true
  | Top, _ -> false
  | Constants a, Constants b -> Constants.subset a b

let is_leq a b =
  b.top
  || begin
    not a.top
    && Int_interv.is_leq a.int b.int
    && leq_simple a.float b.float
    && leq_simple a.string b.string
    && leq_simple a.i32 b.i32
    && leq_simple a.i64 b.i64
    && leq_simple a.inat b.inat
    && Ints.subset a.cp b.cp
    && Tagm.for_all
      (fun k a ->
         try
           let b = Tagm.find k b.blocks in
           Intm.for_all
             (fun k a ->
                let b = Intm.find k b in
                array2_forall Ids.subset a b
             ) a
         with Not_found -> false
      ) a.blocks
    && Ids.subset a.arrays.a_elems b.arrays.a_elems
    && Int_interv.is_leq a.arrays.a_size b.arrays.a_size
    && ( b.arrays.a_gen
         || not a.arrays.a_gen
            && ( not a.arrays.a_float || b.arrays.a_float )
            && ( not a.arrays.a_addr || b.arrays.a_addr )
            && ( not a.arrays.a_int || b.arrays.a_int )
       )
    && Fm.for_all
      (fun k a ->
         try
           let b = Fm.find k b.f in
           array2_forall Ids.subset a b
         with Not_found -> false
      ) a.f
  end

(* Intersection *)

let intersection_simple a b = match a, b with
  | Top, a | a, Top -> a
  | Constants s, Constants s' ->
    Constants ( Constants.inter s s')


let intersect_noncommut env a b =
  (* keeps the ids in a that are possibly compatible with b *)
  if a.top then (env, b)
  else if b.top then (env, a)
  else
    let blocks = 
      Tagm.merge
        begin
          fun _ a b ->
            match a, b with
            | _, None | None, _ -> None
            | Some is1, Some is2 ->
              Some (
                Intm.merge
                  (fun _ a b ->
                     match a, b with
                     | _, None | None, _ -> None
                     | Some s1, Some s2 ->
                       Some
                         (
                           Array.mapi
                             (fun i i1 ->
                                ( Ids.filter (fun id -> Ids.exists ( included env id) s2.(i)) i1)
                             )
                             s1
                         )
                  )
                  is1 is2
              )
        end
        a.blocks b.blocks
    in
    let f =
      Fm.merge
        begin
          fun _ a b ->
            match a, b with
            | _, None | None, _ -> None
            | Some a, Some b ->
              Some (
                Array.mapi
                  (fun i a ->
                     Ids.filter
                       (fun a ->
                          Ids.exists (included env a) b.(i)
                       ) a
                  ) a
              )
        end
        a.f b.f
    in
    env,
    { top = false;
      int = Int_interv.meet a.int b.int;
      float = intersection_simple a.float b.float;
      string = intersection_simple a.string b.string;
      i32 = intersection_simple a.i32 b.i32;
      i64 = intersection_simple a.i64 b.i64;
      inat = intersection_simple a.inat b.inat;
      cp = Ints.inter a.cp b.cp;
      blocks;
      arrays =
        {
          a_elems = b.arrays.a_elems (* TODO: see that again *);
          a_size = Int_interv.meet a.arrays.a_size b.arrays.a_size;
          a_gen = a.arrays.a_gen && b.arrays.a_gen;
          a_float = a.arrays.a_float && b.arrays.a_float;
          a_addr = a.arrays.a_addr && b.arrays.a_addr;
          a_int = a.arrays.a_int && b.arrays.a_int;
        };
      f;
      expr = Hinfos.empty;
    }
