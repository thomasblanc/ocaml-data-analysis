open Utils
open Common_types
open Data

let odo f g = function
  | Some x -> f x
  | None -> g ()

let sep pp = Format.fprintf pp ",@ "

let print_simple pp t =
  let open Constants in
  let open Format in
  function
  | Top -> fprintf pp "@[%s: Top@]@." t
  | Constants s when Constants.is_empty s -> ()
  | Constants s ->
    fprintf pp "%s: [@ @[" t;
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


let print pp id env =
  let open Format in
  TId.print pp id;
  fprintf pp ":@[";
  pp_open_box pp 0;
  let d = get_env id env in
  begin
    if d.top
    then ( fprintf pp "Top@.")
    else
      begin
        if not ( Int_interv.is_bottom d.int )
        then
          (
            fprintf pp "Ints: [@ @[";
            odo
              (pp_print_int pp)
              (fun () -> pp_print_string pp "-inf")
              (Int_interv.lower d.int);
            fprintf pp ",@ ";
            odo
              (pp_print_int pp)
              (fun () -> pp_print_string pp "inf")
              (Int_interv.higher d.int);
            fprintf pp "@]@ ]@."
          );
        print_simple pp "Floats" d.float;
        print_simple pp "Strings" d.string;
        print_simple pp "Int32" d.i32;
        print_simple pp "Int64" d.i64;
        print_simple pp "Native ints" d.inat;
        if not ( Ints.is_empty d.cp )
        then
          (
            fprintf pp  "Const pointers : [ @[@ ";
            Ints.print_sep sep pp d.cp;
            fprintf pp "@]@ ]@."
          );
        if not ( Tagm.is_empty d.blocks )
        then
          (
            fprintf pp "Blocks@.@[@ ";
            Tagm.print
              (fun pp im ->
                 fprintf pp "@[{@ ";
                 Intm.print_sep
                   sep
                   print_ids_array
                   pp 
                   im;
                 fprintf pp "}@]@." )
              pp
              d.blocks;
            fprintf pp "@ @]@."
          );
        let a = d.arrays in
        if not ( Ids.is_empty a.a_elems || Int_interv.is_bottom a.a_size )
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
            Int_interv.print pp a.a_size;
            fprintf pp "@]@ elements:@[";
            Ids.print_sep sep pp a.a_elems;
            fprintf pp "@]@ @]]@."
          );
        if not ( Fm.is_empty d.f )
        then
          (
            fprintf pp "Functions: {@[@ ";
            Fm.print_sep sep (fun _ _ -> ()) pp d.f;
            fprintf pp "@ @]}@."
          )
      end
  end;
  fprintf pp "@]@."
