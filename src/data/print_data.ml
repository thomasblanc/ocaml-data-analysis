open Utils
open Common_types
open Locations
open Data
open Envs

let odo f g = function
  | Some x -> f x
  | None -> g ()

let str s pp = Format.pp_print_string pp s

let print_option f none pp = function
  | Some x -> f pp x
  | None -> str none pp

let sep pp = Format.fprintf pp ",@ "

let print_simple pp t =
  let open Constants in
  let open Format in
  function
  | Top -> fprintf pp "@[%s:@ Top@]@." t
  | Constants s when Constants.is_empty s -> ()
  | Constants s ->
    fprintf pp "%s:@ [@ @[" t;
    Constants.print_sep sep pp s;
    fprintf pp "@]@ ]@."

let print_ids_array pp a = ()
(* let open Format in *)
(* let l = Array.length a  in *)
(* if l = 0 *)
(* then ( pp_print_string pp "[||]"; Ids.empty ) *)
(* else ( *)
(*   fprintf pp "[|@ @[@ %a"; *)
(*   Array.iter *)
(*     (fun ids -> *)
(*        failwith "pretty-printing ids" *)
(*     ) *)
(*     a; *)
(*   fprintf pp "@]@ |]" *)
(* ) *)

let print_interv pp i =
  if not ( Int_interv.is_bottom i )
  then
    Format.fprintf pp "Ints:@ [@ @[%a%t%a@]@ ]@."
      (print_option Format.pp_print_int "-inf")
      (Int_interv.lower i)
      sep
      (print_option Format.pp_print_int "inf")
      (Int_interv.higher i)
  else ()

let extract_locs { blocks; f; arrays; _} =
  let ig f _ = f in
  let arr = Array.fold_right Locs.union in
   Tagm.fold
   (ig
      (Intm.fold
         (ig arr )
      )
   ) blocks
   (Fm.fold (ig arr) f arrays.a_elems)

let print_data pp d =
  let open Format in
  if d.top
  then ( fprintf pp "Top@.")
  else
    begin
      print_interv pp d.int;
      print_simple pp "Floats" d.float;
      print_simple pp "Strings" d.string;
      print_simple pp "Int32" d.i32;
      print_simple pp "Int64" d.i64;
      print_simple pp "Native ints" d.inat;
      if not ( Ints.is_empty d.cp )
      then
        fprintf pp
          "Const pointers@ :@ @[[@[<2>%a@]]@]@."
          (Ints.print_sep sep) d.cp;
      if not ( Tagm.is_empty d.blocks )
      then
        fprintf pp "Blocks@.@[@ %a@ @]@."
          ( Tagm.print
              (fun pp im ->
                 fprintf pp "@[{@[<2>@ %a@]}@]@."
                   (Intm.print_sep sep print_ids_array)
                   im
              )
          ) d.blocks;
      let a = d.arrays in
      if not ( Locs.is_empty a.a_elems || Int_interv.is_bottom a.a_size )
      then
        (
          fprintf pp "Arrays%s@.[@[@ sizes:@["
            (if a.a_gen
             then ""
             else 
               "(" ^
               (String.concat ","
                  (
                    List.filter ((<>) "")
                      [
                        if a.a_float then "f" else "";
                        if a.a_addr then "b" else "";
                        if a.a_int then "i" else ""
                      ]
                  )
               )
               ^ ")"
            );
          fprintf pp "%a@]@ elements:@[%a@]@ @]]@."
            Int_interv.print a.a_size
            (Locs.print_sep sep) a.a_elems
        );
      if not ( Fm.is_empty d.f )
      then
          fprintf pp "Functions: {@[@ %a@ @]}@."
            (Fm.print_sep sep (fun _ _ -> ())) d.f
    end

let print_loc' pp loc env =
  Locm.fold_key (fun loc data locs ->
      Format.fprintf pp
        "@[%a@ ->@ @[%a@]@]"
        print_atpl loc
        print_data data;
      Locs.union locs (extract_locs data)
    ) loc env.values Locs.empty

let print_loc pp loc =
  Envs.no_bottom "print_loc" (print_loc' pp loc)

let print_tid' pp tid env =
  let locs = TIdm.find tid env.entries in
  Format.fprintf pp
    "@[%a@ :@ @[{@[<2>%a@]}@]."
    TId.print tid
    Locs.print locs;
  locs

let print_tid pp tid = Envs.no_bottom "print_tid" (print_tid' pp tid)

let rec print_until_done pp todo finished env =
  let todonext =
    Locs.fold
      (fun loc todo -> Locs.union (print_loc' pp loc env) todo)
      todo Locs.empty in
  let finished = Locs.union finished todo in
  let todonext = Locs.diff todonext finished in
  if not ( Locs.is_empty todonext)
  then print_until_done pp todonext finished env

let print' pp tid env =
  let todo = print_tid' pp tid env in
  let finished = TIdm.find tid env.entries in
  print_until_done pp todo finished env

let print pp tid = Envs.no_bottom "print" (print' pp tid)
