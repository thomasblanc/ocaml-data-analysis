open Common_types

(* let ppf = Format.std_formatter in *)

let cmbise outputprefix = outputprefix ^ ".cmb"
let targets = ref []
let add_target t = targets := t :: !targets

let get_targets () = List.rev !targets

let only_compile = ref false
let target_string : string option ref = ref None

let count_apply = ref false

let dot_file : string option ref = ref None
let show_unreachable = ref false

let dump_tlambda = ref false
let dot_bigraphs = ref false
let dot_total_bigraph : string option ref = ref None

let arg_parser =
  let open Arg in
  align
    [
      ( "-open",
        String Mk_lambda.open_module,
        " Add an implicitly opened module" );
      ( "-close",
        String Mk_lambda.close_module,
        " Remove an implicitly opened module" );
      ( "-c",
        Set only_compile,
        " Only build the .cmb intermediate representations");
      ( "-o",
        String (fun s -> target_string := Some s ),
        " Specify the name of the target to build");
      ( "-counter",
        Set count_apply,
        " Output the pass count");
      ( "-dot",
        String (fun s -> dot_file := Some s ),
        " Dumps the result to a dot file");
      ( "-show-unreachable",
        Set show_unreachable,
        " show unreachable nodes in the dot graph");
      ( "-dtlambda",
        Set dump_tlambda,
        " Dump the produced tlambda in a .tml file");
      ( "-dot-bigraphs",
        Set dot_bigraphs,
        " Output the seperated bigraphs produced in .dot files");
      ( "-dot-total-bigraphs",
        String ( fun s -> dot_total_bigraph := Some s),
        " Output the total bigraph to a dot files");
      
    ]

let handle_file ppf sourcefile =

  let outputprefix =
    match !only_compile, !target_string with
    | true, Some s -> s
    | _ ->  Filename.chop_extension sourcefile
  in

  let handle_lambda (lambda,modulename) =
    let funs : ( F.t, Tlambda.tlambda ) Hashtbl.t = Hashtbl.create 1024 in

    let tlambda = Mk_tlambda.lambda_to_tlambda ~modname:modulename ~funs lambda in

    if !dump_tlambda
    then (Format.fprintf ppf "%a@." Print_tlambda.tlambda tlambda);

    let (g,funtbl,vin,vout,vexn,exn_id,return_id) =
      Tlambda_to_hgraph.mk_graph ~modulename funs tlambda in

    if !dot_bigraphs
    then Print_hgraph . (
        Tlambda_to_hgraph.G.print_dot
          ~print_attrvertex ~print_attrhedge ppf g);

    Cmb.export g funtbl vin vout vexn outputprefix;
    add_target (cmbise outputprefix)

  in
  
  let c = Filename.check_suffix sourcefile in

  if c ".ml"
  then handle_lambda ( Mk_lambda.ml_file ppf sourcefile outputprefix)
  else if c ".cmt"
  then handle_lambda ( Mk_lambda.cmt_file ppf sourcefile outputprefix)
  else if c ".mli"
  then Mk_lambda.mli_file ppf sourcefile outputprefix
  else if c ".cmti"
  then Mk_lambda.cmti_file ppf sourcefile outputprefix
  else if c ".cmb"
  then add_target sourcefile
  else failwith ("bad file suffix for file " ^ sourcefile )
