let ppf = Format.std_formatter

open My_main_args

let print_hedge_attribute ppf hattr =
  let open Common_types in
  let aux ppf = function
    | Prim (prim, _) ->
      Print_tlambda.primitive ppf prim
    | App_prep _ ->
      Format.fprintf ppf "App_prep"
    | App ->
      Format.fprintf ppf "App"
    | Return _ ->
      Format.fprintf ppf "Return"
    | Retexn _ ->
      Format.fprintf ppf "Retexn"
    | Var _ ->
      Format.fprintf ppf "Var"
    | Const _ ->
      Format.fprintf ppf "Const"
    | Constraint _ ->
      Format.fprintf ppf "Constraint"
    | Lazyforce _ ->
      Format.fprintf ppf "Lazyforce"
    | Ccall _ ->
      Format.fprintf ppf "Ccall"
    | Send _ ->
      Format.fprintf ppf "Send"
  in
  match hattr with
  | [] -> ()
  | [_, hinfo] -> aux ppf hinfo
  | (_, hinfo) :: t ->
    aux ppf hinfo;
    List.iter (fun (_,hinfo) -> Format.fprintf ppf ", %a" aux hinfo)
      t

let print_attrhedge ppf h attr =
  Format.fprintf ppf "%a: %a"
    Tlambda_to_hgraph.T.Hedge.print h
    print_hedge_attribute attr

let () =
  Arg.parse arg_parser (handle_file ppf)
    "Make sure that all your files are in the right order";
  if not !only_compile
  then
    begin
      let t = get_targets () in
      let (g,funs,inv,exnv,outv) = Cmb.import_list t in
      let module E =
      struct
        let inv = inv
        let outv = outv
        let exnv = exnv
        let g = g
        let funs = funs
        let mk_vertex = Tlambda_to_hgraph.Vertex.mk ~modulename:""
        let mk_hedge = Tlambda_to_hgraph.Hedge.mk
      end
      in
      let module Manager = Tlambda_analysis.M ( E ) in
      let module F = Fixpoint.Fixpoint ( Tlambda_to_hgraph.T ) ( Manager ) in
      print_endline "starting the analysis";
      let result, assotiation_map =
        F.kleene_fixpoint g ( Manager.H.VertexSet.singleton inv ) in
      let exnv_output = Manager.H.VertexSet.elements
          (Manager.H.VertexMap.find exnv assotiation_map) in
      let exn_env =
        Manager.join_list exnv
          (List.map (Tlambda_to_hgraph.G.vertex_attrib result) exnv_output) in
      if !count_apply
      then Format.fprintf ppf "Pass count: %d@." (Tlambda_analysis.get_counter ());
      begin match !dot_file with
        | None -> ()
        | Some file ->
          let oc = open_out (file ^ ".dot") in
          let ppf = Format.formatter_of_out_channel oc in
          Manager.H.print_dot
            ~print_attrvertex:(fun ppf v _ -> Tlambda_to_hgraph.T.Vertex.print ppf v)
            ~print_attrhedge
            ppf result;
          close_out oc
      end;
      if Envs.is_bottom exn_env
      then ()
      else
        begin
          Format.pp_print_string ppf "I found something:\n";
          Data.print
            ppf
            Manager.exn_tid
            exn_env;
          exit 1
        end

    end
