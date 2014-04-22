open Locations
open Data

let field i f =
  Fm.fold (fun _ a locs -> Locs.union a.(i) locs) f.f Locs.empty

let has_fid i fu = Fm.mem i fu.f

let fid i fu =
  assert(Fm.mem i fu.f);
  { bottom with f = Fm.singleton i ( Fm.find i fu.f ); }

let mk i l =
  { bottom with
    f = Fm.singleton i
        ( Array.map
            Locs.singleton
            ( Array.of_list l )
        );
  }

let extract_ids { f; _ } acc =
  Fm.fold (fun k _ l -> k::l) f acc
