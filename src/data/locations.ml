open Utils
open Common_types

module TIdm = Map.Make (TId)


type ap = TId.t
(* allocation point are represented by the corresponding tid *)

module AId : Id = struct
  type t = int
  let compare (a:t) (b:t) = Pervasives.compare a b
  let hash (a:t) = a
  let equal (a:t) b = a=b
  let name _ = None
  let to_string = string_of_int
  let output fd i = output_string fd (to_string i)
  let print = Format.pp_print_int

  let init = ref (-1)
  let create ?name () =
    incr init;
    !init
end

module AIdo = struct
  type t = AId.t option
  let compare (a:t) (b:t) =
    match a,b with
    | Some a, Some b -> AId.compare a b
    | None,None -> 0
    | Some _, None -> -1
    | None, Some _ -> 1
  let equal a b =
    match a, b with
    | Some a, Some b -> AId.equal a b
    | None, None -> true
    | _,_ -> false
  let print ppf = function
    | Some a -> AId.print ppf a
    | None -> Format.pp_print_char ppf 'N'
  let create ?name () = Some (AId.create ())
  let any : t = None
  let either ~any ~f = function
    | Some x -> f x
    | None -> any
  let of_aid x : t= Some x
  let to_aid : t -> AId.t = function
    | Some x -> x
    | None -> assert false
  let subset (a:t) (b:t) =
    match a,b with
    | None, None | Some _, None -> true
    | None, Some _ -> false
    | Some a, Some b -> AId.equal a b
end

type atpl = AIdo.t * ap
(* the allocation tuple *)

let of_tid tid = (AIdo.create (), tid)
let print_atpl pp (aido,tid) = Format.fprintf pp "(%a,%a)" AIdo.print aido TId.print tid

module AIdm = Map.Make(AId)

module Locs : Set.S
  with type elt = atpl
= struct

  type elt = atpl
  type t = AIdo.t TIdm.t
      
  let empty = TIdm.empty
              
  let is_empty = TIdm.is_empty

  let mem (aido,tid) s =
    try
      match TIdm.find tid s, aido with
      | None,_ -> true
      | Some a, Some b when AId.equal a b -> true
      | _, _ -> false
    with Not_found -> false

  let add (aido,tid) s =
    try
      let aido2 = TIdm.find tid s in
      if AIdo.equal aido aido2
      then s
      else TIdm.add tid AIdo.any s
    with Not_found -> TIdm.add tid aido s

  let singleton (aido,tid) = TIdm.singleton tid aido

  let remove (aido,tid) s =
    try
      let aido2 = TIdm.find tid s in
      if AIdo.equal aido aido2 || AIdo.equal aido AIdo.any
      then TIdm.remove tid s
      else s
    with Not_found -> s

  let union s1 s2 =
    TIdm.merge
      (fun _ o1 o2 ->
         match o1,o2 with
         | a,None | None,a -> a
         | Some a, Some b ->
           if AIdo.equal a b
           then o1
           else Some AIdo.any
      ) s1 s2

  let inter s1 s2 =
    TIdm.merge
      (fun _ o1 o2 ->
         match o1,o2 with
         | _,None | None,_ -> None
         | Some a, Some b when AIdo.equal a b -> o1
         | Some a, _ when AIdo.equal a AIdo.any -> o2
         | _, Some a when AIdo.equal a AIdo.any -> o1
         | _, _ -> None
      ) s1 s2

  let diff s1 s2 =
    TIdm.merge
      (fun _ o1 o2 ->
         match o1,o2 with
         | Some a1, Some a2
           when
             AIdo.equal a1 a2 ||
             AIdo.equal AIdo.any a2
           -> None
         | _, _ -> o1
      ) s1 s2

  let compare = TIdm.compare AIdo.compare
  let equal s1 s2 = TIdm.equal AIdo.equal s1 s2

  let subset s1 s2 =
    try
      TIdm.for_all (fun tid aido ->
          let aido2 = TIdm.find tid s2 in
          AIdo.subset aido aido2
        ) s1
    with Not_found -> false

  let decurry f tid aido = f (aido,tid)

  let iter f s = TIdm.iter (decurry f) s
  let fold f s acc = TIdm.fold (decurry f) s acc
  let for_all f s = TIdm.for_all (decurry f) s
  let exists f s = TIdm.exists (decurry f) s
  let filter f s = TIdm.filter (decurry f) s
  let partition f s = TIdm.partition (decurry f) s

  let cardinal s = TIdm.cardinal s
  let elements s = fold (fun e acc -> e::acc) s []

  let inv_tuple (a,b) = b,a
  let min_elt s = inv_tuple ( TIdm.min_binding s)
  let max_elt s = inv_tuple ( TIdm.max_binding s)
  let choose s = inv_tuple (TIdm.choose s)

  let split (aido,tid) s =
    let (s1,aidoo,s2) = TIdm.split tid s in
    match aidoo with
    | None -> s1,false,s2
    | Some aido2 ->
      begin
        let c = AIdo.compare aido aido2 in
        if c < 0
        then s1, false, TIdm.add tid aido2 s2
        else if c = 0
        then s1, true, s2
        else TIdm.add tid aido2 s1, false, s2
      end

  let find ((aido,tid) as x) s =
    if mem x s
    then (TIdm.find tid s, tid)
    else raise Not_found

  let print pp s = TIdm.iter (fun tid aido -> print_atpl pp (aido,tid)) s
  let print_sep f pp s =
    if TIdm.is_empty s
    then ()
    else
      begin
        let (tid,aido) = TIdm.min_binding s in
        print_atpl pp (aido,tid);
        TIdm.iter
          (fun tid aido -> f pp;print_atpl pp (aido,tid))
          (TIdm.remove tid s)
      end
end

module Locm : sig
  include Map.S with type key = atpl
  val fold_key : ( key -> 'a -> 'b -> 'b) -> key -> 'a t -> 'b -> 'b
  val fold_by_loc : (key -> 'b -> 'b) -> 'a t -> 'b -> 'b
end = struct

  type key = atpl
  type 'a t = 'a AIdm.t TIdm.t

  let empty = TIdm.empty
  let is_empty = TIdm.is_empty

  let mem (aido,tid) m =
    TIdm.mem tid m &&
    AIdo.either
      ~any:true
      ~f:(fun aid -> AIdm.mem aid (TIdm.find tid m)) aido

  let add (aido,tid) x m =
    let aid = AIdo.to_aid aido in
    TIdm.add
      tid
      (AIdm.add aid x
         (try TIdm.find tid m
          with Not_found -> AIdm.empty)
      ) m

  let singleton (aido,tid) x =
    let aid = AIdo.to_aid aido in
    TIdm.singleton tid (AIdm.singleton aid x) 

  let remove (aido,tid) m =
    AIdo.either
      ~any:m
      ~f:(fun aid -> try
             let a = TIdm.find tid m in
             TIdm.add tid (AIdm.remove aid a) m
           with Not_found -> m )
      aido

  let merge f m1 m2 =
    TIdm.merge
      (fun tid o1 o2 ->
         let a1 = match o1 with Some a -> a | None -> AIdm.empty in
         let a2 = match o2 with Some a -> a | None -> AIdm.empty in
         let a3 =
           AIdm.merge
             (fun aid x y -> f (AIdo.of_aid aid,tid) x y)
             a1 a2
         in
         if AIdm.is_empty a3
         then None
         else Some a3
      ) m1 m2

  let compare c m1 m2 = TIdm.compare (AIdm.compare c) m1 m2
  let equal e m1 m2 = TIdm.equal (AIdm.equal e) m1 m2

  let app_two_steps s1 s2 f m =
    s1 (fun tid a -> s2 (fun aid x -> f (AIdo.of_aid aid,tid) x) a) m

  let iter f m = app_two_steps TIdm.iter AIdm.iter f m
  let fold f m acc = app_two_steps TIdm.fold AIdm.fold f m acc
  let for_all f m = app_two_steps TIdm.for_all AIdm.for_all f m
  let exists f m = app_two_steps TIdm.exists AIdm.exists f m
  let filter f m = app_two_steps TIdm.mapi AIdm.filter f m
  let partition f m =
    fold
      (fun k x (yes,no) ->
         if f k x
         then add k x yes, no
         else yes, add k x no )
      m (empty,empty)

  let cardinal m = TIdm.fold (fun _ a acc -> acc + AIdm.cardinal a) m 0
  let bindings m = fold (fun k x l -> (k,x)::l) m []
  let getb f1 f2 m =
    let (tid,a) = f1 m in
    let (aid,x) = f2 a in
    ((AIdo.of_aid aid,tid),x)
  let min_binding m = getb TIdm.min_binding AIdm.min_binding m
  let max_binding m = getb TIdm.max_binding AIdm.max_binding m
  let choose m = getb TIdm.choose AIdm.choose m

  let split (aido,tid) m =
    let m1,o,m2 = TIdm.split tid m in
    match o with
    | None -> m1,None,m2
    | Some a ->
      AIdo.either
        ~any:(m1,None,TIdm.add tid a m2)
        ~f:(fun aid ->
            let a1,o,a2 = AIdm.split aid a in
            TIdm.add tid a1 m1, o, TIdm.add tid a2 m2)
        aido

  let find (aido,tid) m = AIdm.find (AIdo.to_aid aido) (TIdm.find tid m)

  let map f m = TIdm.map (fun a -> AIdm.map f a) m

  let mapi f m = TIdm.mapi (fun tid a -> AIdm.mapi (fun aid x -> f (AIdo.of_aid aid,tid) x) a) m

  let fold_key f (aido,tid) m acc =
    let id x = x in
    AIdo.either
      ~any:(try
              AIdm.fold
                (fun aid x acc -> f ((AIdo.of_aid aid),tid) x acc)
                (TIdm.find tid m)
            with Not_found -> id )
      ~f:(fun aid ->
          try f ((AIdo.of_aid aid),tid) (AIdm.find aid (TIdm.find tid m))
          with Not_found -> id )
      aido acc

  let print f pp m =
    TIdm.iter
      (fun tid aidm ->
         AIdm.iter
           (fun aid x ->
              Format.fprintf pp "@[%a@ ->@ %a@]"
              print_atpl (AIdo.of_aid aid, tid)
              f x
           ) aidm
      ) m
  let print_sep fsep f pp s =
    TIdm.print_sep fsep (AIdm.print_sep fsep f) pp s

  let fold_by_loc f m acc =
    TIdm.fold (fun tid _ acc ->
        f (AIdo.any,tid) acc
      ) m acc

end


