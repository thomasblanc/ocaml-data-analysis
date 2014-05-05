open Common_types
open Lambda
open Tlambda

module Idm = Map.Make ( Id )
module Ids = Set.Make ( Id )

let zero_of k =
  let open Asttypes in
  Const_base (
    match k with
    | Pnativeint -> Const_nativeint 0n
    | Pint32 -> Const_int32 0l
    | Pint64 -> Const_int64 0L
  )

let zeroint =  Const_base ( Asttypes.Const_int 0 )

let prim_translate = function
  (* Operations on heap blocks *)
  | Pfield i -> TPfield i
  | Psetfield ( i, b) -> TPsetfield ( i, b)
  | Pfloatfield i -> TPfloatfield i
  | Psetfloatfield i -> TPsetfloatfield i
  | Pduprecord ( t, i ) -> TPduprecord ( t, i )
  (* Boolean operations *)
  | Pnot -> TPnot
  (* Integer operations *)
  | Pnegint -> TPnegint
  | Paddint -> TPaddint
  | Psubint -> TPsubint
  | Pmulint -> TPmulint
  | Pdivint -> TPdivint
  | Pmodint -> TPmodint
  | Pandint -> TPandint
  | Porint -> TPorint
  | Pxorint -> TPxorint
  | Plslint -> TPlslint
  | Plsrint -> TPlsrint
  | Pasrint -> TPasrint
  | Pintcomp c -> TPintcomp c
  | Poffsetint i -> TPoffsetint i
  | Poffsetref i -> TPoffsetref i
  (* Float operations *)
  | Pintoffloat -> TPintoffloat
  | Pfloatofint -> TPfloatofint
  | Pnegfloat -> TPnegfloat
  | Pabsfloat -> TPabsfloat
  | Paddfloat -> TPaddfloat
  | Psubfloat -> TPsubfloat
  | Pmulfloat -> TPmulfloat
  | Pdivfloat -> TPdivfloat
  | Pfloatcomp c -> TPfloatcomp c
  (* String operations *)
  | Pstringlength -> TPstringlength
  | Pstringrefu -> TPstringrefu
  | Pstringsetu -> TPstringsetu
  (* Array operations *)
  | Parraylength k -> TParraylength k
  | Parrayrefu k -> TParrayrefu k
  | Parraysetu k -> TParraysetu k
  (* Test if the argument is a block or an immediate integer *)
  | Pisint -> TPisint
  (* Test if the (integer) argument is outside an interval *)
  | Pisout -> TPisout
  (* Bitvect operations *)
  | Pbittest -> TPbittest
  (* Operations on boxed integers (Nativeint.t, Int32.t, Int64.t) *)
  | Pbintofint k -> TPbintofint k
  | Pintofbint k -> TPintofbint k
  | Pcvtbint ( ksource, kdest ) -> TPcvtbint ( ksource, kdest )
  | Pnegbint k -> TPnegbint k
  | Paddbint k -> TPaddbint k
  | Psubbint k -> TPsubbint k
  | Pmulbint k -> TPmulbint k
  | Pdivbint k -> TPdivbint k
  | Pmodbint k -> TPmodbint k
  | Pandbint k -> TPandbint k
  | Porbint k -> TPorbint k
  | Pxorbint k -> TPxorbint k
  | Plslbint k -> TPlslbint k
  | Plsrbint k -> TPlsrbint k
  | Pasrbint k -> TPasrbint k
  | Pbintcomp ( k, c ) -> TPbintcomp ( k, c )
  (* Operations on big arrays: (unsafe, #dimensions, kind, layout) *)
  | Pbigarrayref ( b, i, k, l ) -> TPbigarrayref ( b, i, k, l )
  | Pbigarrayset ( b, i, k, l ) -> TPbigarrayset ( b, i, k, l )
  (* size of the nth dimension of a big array *)
  | Pbigarraydim i -> TPbigarraydim i
  (* load/set 16,32,64 bits from a string: (unsafe)*)
  | Pstring_load_16 b -> TPstring_load_16 b
  | Pstring_load_32 b -> TPstring_load_32 b
  | Pstring_load_64 b -> TPstring_load_64 b
  | Pstring_set_16 b -> TPstring_set_16 b
  | Pstring_set_32 b -> TPstring_set_32 b
  | Pstring_set_64 b -> TPstring_set_64 b
  (* load/set 16,32,64 bits from a
     (char, int8_unsigned_elt, c_layout) Bigarray.Array1.t : (unsafe) *)
  | Pbigstring_load_16 b -> TPbigstring_load_16 b
  | Pbigstring_load_32 b -> TPbigstring_load_32 b
  | Pbigstring_load_64 b -> TPbigstring_load_64 b
  | Pbigstring_set_16 b -> TPbigstring_set_16 b
  | Pbigstring_set_32 b -> TPbigstring_set_32 b
  | Pbigstring_set_64 b -> TPbigstring_set_64 b
  (* Compile time constants *)
  | Pctconst c -> TPctconst c
  (* byte swap *)
  | Pbswap16 -> TPbswap16
  | Pbbswap k -> TPbbswap k
  | _ -> assert false

let alloc_translate = function
  | Pmakeblock ( i, m) -> TPmakeblock ( i, m)
  | Pmakearray k -> TPmakearray k
  | _ -> assert false


let var_name_of_lambda = function
  | Lvar v -> ( match Id.name v with Some n -> n | None -> "_var_" )
  | Llet _ | Lletrec _ -> "_var_"
  | Lassign _ | Lifused _ | Levent _ -> assert false
  | Lsequence _ -> "_seq_"
  | Lconst _ -> "_const_"
  | Lapply _ -> "_app_"
  | Lfunction _ -> "_funct_"
  | Lprim _ -> "_primitive_"
  | Lswitch _ -> "_match_"
  | Lstaticcatch _ -> "_scatch_"
  | Ltrywith _ -> "_trywith_"
  | Lifthenelse _ -> "_if_"
  | Lsend _ -> "_send_"
  | Lstaticraise _ | Lwhile _ | Lfor _ -> "()"
  

let cp i = Lconst ( Const_pointer i )

let lvars = List.map (fun v -> Lvar v)

let lambda_to_tlambda ~modname ~funs code =

  let mk ?(name="$$") () = Id.create ~name () in

  let tid i : tid = modname,i in

  let tlet ?(k = Strict) ~id te_lam te_in =
    Tlet { te_kind = k; te_id = tid id; te_lam; te_in; }
  in

  (* let funcs : ( F.t, tlambda ) Hashtbl.t = Hashtbl.create 256 in *)

  let register_function tlam arg fv =
    let i = F.create ~name:modname ()  in
    let idf = tid ( mk ~name:"func_fv" ()) in
    let targ = tid arg in
    let tlam, _ =
      Idm.fold (fun _ id (tlam,n) ->
          tlet ~k:Alias ~id ( Tprim ( TPfunfield n, [idf] ) ) tlam, succ n
        )
        fv ( tlam, 0 )
    in
    Hashtbl.add funs i (
      ( Tlet
          {
            te_kind = Alias;
            te_id = idf;
            te_lam = (Tprim ( TPgetfun i, [] ));
            te_in = 
              Tlet { te_kind = Alias; te_id = targ; 
                     te_lam = (Tprim ( TPgetarg, [] ));
                     te_in = tlam; };
          }
      ) );
    i
  in

  let lraise_glob x l =
    Lprim (
      Praise,
      [Lprim 
         ( Pmakeblock (0,Asttypes.Immutable),
           (Lprim (Pgetglobal x, []))::l )]
    )
  in
  let ldiv_by_zero =
    lraise_glob
      Ident.({ name = "Division_by_zero"; stamp = 23; flags = 0; })
      []
  in
  let linvalid_arg =
    lraise_glob
      Ident.({ name = "Invalid_argument"; stamp = 18; flags = 0; })
      [ Lconst (Const_base (Asttypes.Const_string "index out of bounds")) ]
  in
  let lout_of_bounds = linvalid_arg in

  let rec tlambda rv nfv fv = function
    | Lvar v ->
      let fv,v = check rv nfv fv v in
      ( fv , Tend (tid v) )
    | Lconst _
    | Lapply _
    | Lfunction _
    | Lprim _
    | Lswitch _
    | Lstaticraise _
    | Lstaticcatch _
    | Ltrywith _
    | Lifthenelse _
    | Lwhile _
    | Lfor _
    | Lsend _
      as lam ->
      let id = mk ~name:(var_name_of_lambda lam) () in
      tcontrol rv (Ids.add id nfv) fv [id, Lvar id] lam
    | Llet ( k, id , e, cont ) ->
      tcontrol rv (Ids.add id nfv) fv [id, cont] e
    | Lletrec (l, continuation) -> trec_main rv nfv fv [] l continuation
    | Lsequence ( a, b ) ->
      let id = mk ~name:"()" () in
      tcontrol rv (Ids.add id nfv) fv [id, b] a
    | Lassign _
    | Levent _
    | Lifused _ -> assert false

  and trec_main rv nfv fv stack l continuation =
    let vars, promoted, expelled =
      List.fold_left
        (fun (vars,promoted, expelled) (id, lam) -> promote_rec vars promoted expelled id lam )
        ([],[],[]) l
    in
    if expelled = []
    then
      let nrv =
        List.fold_left
          (fun rv (i,_) -> Ids.add i rv)
          Ids.empty promoted
      in
      let brv = Ids.union nrv rv in
      (* let nfv = Ids.union nfv rv in *)
      let fv, tr_decls = mk_tletrec brv nfv fv [] promoted in
      (* let fv = *)
      (*   List.fold_left *)
      (*     (fun fv i -> Idm.remove i fv) *)
      (*     fv vars in *)
      let fv, tr_in =
        if stack = []
        then tlambda rv (Ids.union nfv nrv) fv continuation
        else tcontrol rv (Ids.union nfv nrv) fv stack continuation
      in
      ( fv, ( Trec { tr_decls; tr_in } ) )
    else
      let stack, cont =
        List.fold_left
          (fun (stack,cont) (i,lam) -> ((i,cont)::stack,lam))
          ( stack, Lletrec ( promoted, continuation ) ) expelled
      in
      tcontrol rv nfv fv stack cont


  and tcontrol rv nfv fv stack = function
    | Lvar v ->
      let fv,v = check rv nfv fv v in
      mk_tlet rv nfv fv stack ( Tvar (tid v) )
    | Lconst c -> mk_tlet rv nfv fv stack ( Tconst c )
    | Lapply ( Lvar f, [Lvar x], _ ) ->
      let fv, f = check rv nfv fv f in
      let fv, x = check rv nfv fv x in
      mk_tlet rv nfv fv stack ( Tapply ( tid f, tid x ) )
    | Lapply ( Lvar _ as f, [x], loc ) ->
      let ix = mk ~name:"_arg_" () in
      tcontrol rv (Ids.add ix nfv) fv
        ( (ix, Lapply ( f, [Lvar ix], loc ))::stack)
        x
    | Lapply ( f, ( _::[] as arg), loc ) ->
      let idf = mk ~name:"_fun_" () in
      tcontrol rv (Ids.add idf nfv) fv
        ( (idf, Lapply ( Lvar idf, arg, loc ) )::stack)
        f
    | Lapply ( f, arg::args, loc ) ->
      tcontrol rv nfv fv stack
        ( Lapply ( Lapply ( f, [arg], loc ), args, loc ))
    | Lfunction ( _, [arg], body ) ->
      let fv, f, l = fun_create Ids.empty nfv fv arg body in
      mk_tlet rv nfv fv stack ( Talloc ( f, List.map tid l ) )
    | Lfunction ( k, arg::args, body ) ->
      tcontrol rv nfv fv stack
        ( Lfunction ( k, [arg], Lfunction (k,args,body) ) )
    | Llet ( k, id, e, cont ) ->
      tcontrol rv (Ids.add id nfv) fv ((id,cont)::stack) e
    | Lletrec ( l, continuation ) -> trec_main rv nfv fv stack l continuation
    | Lprim ( Psequand, [a;b] ) ->
      tcontrol rv nfv fv stack ( Lifthenelse ( a, b, cp 0 ) )
    | Lprim ( Psequor, [a;b] ) ->
      tcontrol rv nfv fv stack ( Lifthenelse ( a, cp 1, b ) )
    | Lprim ( p, l ) ->
      extract_and_apply rv nfv fv stack
        (fun l -> Lprim ( p, l ) )
        ( prim_handle rv nfv fv stack p )
        l
    | Lswitch ( Lvar v, s ) ->
      let fv, v = check rv nfv fv v in
      let f fv =
        List.fold_left (fun (fv,l) (i,lam) ->
            let fv, tlam = tlambda rv nfv fv lam in
            (fv, (i,tlam)::l) ) (fv,[]) in
      let fv, t_consts = f fv s.sw_consts in
      let fv, t_blocks = f fv s.sw_blocks in
      let fv, t_failaction =
        match s.sw_failaction with
        | Some lam ->
          let fv, tlam = tlambda rv nfv fv lam in
          fv, Some tlam
        | None -> fv, None
      in
      mk_tlet rv nfv fv stack     
        ( Tswitch
            ( tid v,
              {
                t_numconsts = s.sw_numconsts;
                t_numblocks = s.sw_numblocks;
                t_consts; t_blocks; t_failaction;
              }
            )
        )                                
    | Lswitch ( lam, s ) ->
      let i = mk ~name:"_tomatch_" () in
      tcontrol rv nfv fv ( (i, Lswitch ( Lvar i, s))::stack ) lam
    | Lstaticraise (i, l) ->
      extract_and_apply rv nfv fv stack
        (fun l -> Lstaticraise ( i, l ) )
        (fun l ->
           let fv, l = lcheck rv nfv fv l in
           mk_tlet rv nfv fv stack ( Tstaticraise ( i, List.map tid l ))
        )
        l
    | Lstaticcatch ( lam, args, lam2 ) ->
      let fv, tlam = tlambda rv nfv fv lam in
      let nfv =
        List.fold_left
          (fun nfv v -> Ids.add v nfv)
          nfv (snd args) in
      let fv, tlam2 = tlambda rv nfv fv lam2 in
      mk_tlet rv nfv fv stack ( Tstaticcatch ( tlam, (fst args, List.map tid (snd args)), tlam2 ) )
    | Ltrywith ( lam, i, lam2 ) ->
      let fv, tlam = tlambda rv nfv fv lam in
      let nfv = Ids.add i nfv in
      let fv, tlam2 = tlambda rv nfv fv lam2 in
      mk_tlet rv nfv fv stack ( Ttrywith ( tlam, tid i, tlam2 ) )
    | Lifthenelse ( Lvar v, t, e ) ->
      let fv, v = check rv nfv fv v in
      let fv, t = tlambda rv nfv fv t in
      let fv, e = tlambda rv nfv fv e in
      mk_tlet rv nfv fv stack ( Tifthenelse ( tid v, t, e) )
    | Lifthenelse ( c, t, e ) ->
      let i = mk ~name:"_ifcond_"() in
      tcontrol rv (Ids.add i nfv) fv
        (( i, Lifthenelse ( Lvar i, t, e ) )
         ::stack )
        c
    | Lsequence ( a, b ) ->
      let i = mk ~name:"()" () in
      tcontrol rv (Ids.add i nfv) fv ((i,b)::stack) a
    | Lwhile ( c, b ) ->
      let fv, c = tlambda rv nfv fv c in
      let fv, b = tlambda rv nfv fv b in
      mk_tlet rv nfv fv stack ( Twhile ( c, b ) )
    | Lfor ( i, Lvar s, Lvar e, d, b ) ->
      let fv, s = check rv nfv fv s in
      let fv, e = check rv nfv fv e in
      let nfv = Ids.add i nfv in
      let fv, b = tlambda rv nfv fv b in
      mk_tlet rv nfv fv stack
        ( Tfor ( tid i, tid s, tid e, d, b ) )
    | Lfor ( i, s, e, d, b ) ->
      let is = mk ~name:"_start_" () in
      let ie = mk ~name:"_stop_" () in
      tcontrol rv nfv fv
        ((is,e)
         ::(ie, Lfor ( i, Lvar is, Lvar ie, d, b ) )
         ::stack)
        s
    | Lsend ( k, Lvar o, Lvar m, [], _ ) ->
      let fv, o = check rv nfv fv o in
      let fv, m = check rv nfv fv m in
      mk_tlet rv nfv fv stack
        ( Tsend ( k, tid o, tid m ) )
    | Lsend ( k, ( Lvar _ as o ), m, [], loc ) ->
      let im = mk ~name:"_meth_" () in
      tcontrol rv nfv fv
        ( (im, Lsend ( k, o, Lvar im, [], loc))
          ::stack )
        m
    | Lsend ( k, o, (Lvar _ as m), [], loc ) ->
      let io = mk ~name:"_obj_" () in
      tcontrol rv nfv fv
        ( (io, Lsend ( k, Lvar io, m, [], loc))
          ::stack )
        o
    | Lsend ( k, o,  m, [], loc ) ->
      let im = mk ~name:"_meth_" () in
      let io = mk ~name:"_obj_" () in
      tcontrol rv nfv fv
        ( (io, m)
          ::( im, Lsend ( k, Lvar io, Lvar im, [], loc ) )
          ::stack )
        o
    | Lsend ( k, o, m, args, loc ) ->
      tcontrol rv nfv fv stack
        ( Lapply
            ( Lsend ( k, o, m, [], loc )
            , args, loc )
        )
    | _ -> assert false


  and mk_tlet rv nfv fv stack tc =
    match stack with
    | [ ( id ), cont ] ->
      let fv, cont = tlambda rv (Ids.add id nfv) fv cont in
      fv, tlet ~id tc cont
    | (id,cont) :: stack ->
      let fv, lam = ( tcontrol rv (Ids.add id nfv) fv stack cont ) in
      fv, tlet ~id tc lam
    | [] -> assert false

  and prim_handle rv nfv fv stack p l =
    match p, l with
    | Pdivint, [a;b]
    | Pmodint, [a;b] ->
      let lb = Lvar b in
      tcontrol rv nfv fv stack
        ( Lifthenelse (
             Lprim ( Pintcomp Cneq, [lb; Lconst zeroint] ),
             Lprim ( p, [Lvar a; lb; lb]),
             ldiv_by_zero )
        )
    | Pstringrefs, [a;b] ->
      let la = Lvar a in
      let lb = Lvar b in
      tcontrol rv nfv fv stack
        ( Lifthenelse (
             Lprim ( Pintcomp Clt , [lb; Lprim ( Pstringlength, [la])] ),
             Lprim ( Pstringrefu, [la; lb]),
             linvalid_arg )
        )
    | Pstringsets, [a;b;c] ->
      let la = Lvar a in
      let lb = Lvar b in
      tcontrol rv nfv fv stack
        ( Lifthenelse (
             Lprim ( Pintcomp Clt , [lb; Lprim ( Pstringlength, [la])] ),
             Lprim ( Pstringsetu, [la; lb; Lvar c]),
             linvalid_arg )
        )
    | Parrayrefs k, [a;b] ->
      let la = Lvar a in
      let lb = Lvar b in
      tcontrol rv nfv fv stack
        ( Lifthenelse (
             Lprim ( Pintcomp Clt , [lb; Lprim ( Parraylength k, [la])] ),
             Lprim ( Parrayrefu k, [la; lb]),
             lout_of_bounds )
        )
    | Parraysets k, [a;b;c] ->
      let la = Lvar a in
      let lb = Lvar b in
      tcontrol rv nfv fv stack
        ( Lifthenelse (
             Lprim ( Pintcomp Clt , [lb; Lprim ( Parraylength k, [la])] ),
             Lprim ( Parraysetu k, [la; lb; Lvar c]),
             lout_of_bounds )
        )
    | Pdivbint k, [a;b]
    | Pmodbint k, [a;b] ->
      let lb = Lvar b in
      tcontrol rv nfv fv stack
        ( Lifthenelse (
             Lprim ( Pintcomp Cneq, [lb; Lconst (zero_of k)] ),
             Lprim ( p, [Lvar a; lb; lb]),
             ldiv_by_zero )
        )
    | _,_ ->
      begin
        let fv, l = lcheck rv nfv fv l in
        let tl = mk_tlet rv nfv fv stack in
        match p, l with
        | Pidentity, [a] -> tl ( Tvar (tid a) )
        | Pignore, [a] -> tl ( Tconst ( Const_pointer 0 ) )
        | Prevapply loc, x::f::tl
        | Pdirapply loc, f::x::tl ->
          tcontrol rv nfv fv stack
            ( Lapply ( Lvar f, lvars (x::tl), loc ) )
        | Pgetglobal i, [] ->
          if builtin i
          then tl ( Tprim ( TPbuiltin, [tid i] ) )
          else
            let fv, i = check rv nfv fv i in
            mk_tlet rv nfv fv stack ( Tvar ( tid i ) )
        | Psetglobal ig, [ir] ->
          let fv, cont =
            tcontrol rv nfv fv stack
              ( Lconst ( Const_pointer 0))
          in
          fv, Tlet {
            te_id = ("",ig);
            te_lam = Tvar (tid ir);
            te_kind = Alias;
            te_in = cont;
          }
        | Plazyforce, [a] ->
          tl ( Tlazyforce ( tid a ) )
        | Praise, [e] ->
          tl ( Traise (tid e) )
        | Pccall c, _ -> tl ( Tccall ( c, List.map tid l ) )
        | Pdivint, [a;b;_] -> (* yup, that's a hack *)
          tl ( Tprim ( TPdivint, [tid a;tid b]))
        | Pmodint, [a;b;_] ->
          tl ( Tprim ( TPmodint, [tid a;tid b]))
        | Pdivbint k, [a;b;_] -> (* yup, that's a hack *)
          tl ( Tprim ( TPdivbint k, [tid a;tid b]))
        | Pmodbint k, [a;b;_] ->
          tl ( Tprim ( TPmodbint k, [tid a;tid b]))
        | Pmakearray _, _ | Pmakeblock _, _ ->
          tl ( Talloc ( alloc_translate p, List.map tid l) )
        | _, _ ->
          tl ( Tprim ( prim_translate p, List.map tid l ) )
      end

  and promote_rec vars promoted expelled i lam =
    let p_l vars promoted expelled =
      List.fold_left
        (fun (v,p,e) (id,lam) -> promote_rec v p e id lam )
        ( vars, promoted, expelled )
    in
    match lam with
    | Lfunction ( _, _::[], _ ) ->
      ( vars, ( i, lam ) :: promoted, expelled )
    | Lfunction ( k, x::tl, body ) ->
      ( x :: vars, 
        ( i, Lfunction ( k, [x],
                         Lfunction ( k, tl, body ) )
        ) :: promoted,
        expelled )
    | Lprim ( Pmakeblock _ as p, l )
    | Lprim ( Pmakearray _ as p, l ) ->
      let ( lams, l ) = extract_lams [] [] l in
      let vars, promoted, expelled =
        p_l vars promoted expelled lams in
      ( vars, ( i, Lprim ( p, l ) ) :: promoted, expelled )
    | Llet ( k, id, e, cont ) ->
      let ( vars, promoted, expelled ) =
        promote_rec vars promoted expelled id e in
      promote_rec vars promoted expelled i cont
    | Lletrec ( l, cont ) ->
      let ( vars, promoted, expelled ) =
        p_l vars promoted expelled l in
      promote_rec vars promoted expelled i cont
    | _ -> ( vars, promoted, ( i, lam ) :: expelled )

  and mk_tletrec rv nfv fv res l =
    match l with
    | [] -> fv, res
    | (i,lam) :: tl ->
      let fv, x =
        begin
          match lam with
          | Lprim ( p, l ) ->
            let fv, l = lcheck rv nfv fv ( get_vars l) in
            let p = alloc_translate p in
            fv, ( tid i, p, List.map tid l )
          | Lfunction ( _, [arg], body ) ->
            let fv, f, l = fun_create rv nfv fv arg body in
            fv, ( tid i, f, List.map tid l)
          | _ -> assert false
        end in
      mk_tletrec rv nfv fv (x::res) tl

  and extract_vars l =
    let b, l =
      List.fold_left
        ( fun (b,l) lam ->
           match lam with
           | Lvar v -> (b,v::l)
           | _ ->
             let i = mk ~name:(var_name_of_lambda lam) () in
             (false,i::l)
        ) (true,[]) l
    in
    ( b, (List.rev l) )

  and extract_lams res l = function
    | [] -> res, List.rev l
    | ( Lvar _ as lam ) :: tl -> extract_lams res (lam::l) tl
    | lam :: tl ->
      let i = mk ~name:(var_name_of_lambda lam) () in
      extract_lams ((i,lam)::res) ((Lvar i)::l) tl

  and extract_and_apply rv nfv fv stack mkl mkt l =
    let ok, lv = extract_vars l in
    if ok
    then mkt lv
    else
      let stack, nfv, cont, _ =
        List.fold_left
          (fun (stack,nfv,cont,lv) lam ->
             match lam,lv with
             | Lvar v, x::tl ->
               assert (x = v);
               ( stack, nfv, cont, tl )
             | _, i::tl ->
               ( (i,cont)::stack,
                 ( Ids.add i nfv ),
                 lam, tl )
             | _,[] -> assert false

          )
          ( stack, nfv, ( mkl ( lvars lv ) ), lv ) l
      in
      tcontrol rv nfv fv stack cont

  and check rv nfv fv v =
    if Ids.mem v nfv || Ids.mem v rv
    then fv,v
    else
      try
        fv, Idm.find v fv
      with
        Not_found ->
        let i = match Id.name v with
          | None -> mk ()
          | Some name -> mk ~name ()
        in
        Idm.add v i fv, i

  and lcheck rv nfv fv l =
    let fv, l =
      List.fold_left
        (fun (fv,l) i ->
           let fv,i = check rv nfv fv i in
           (fv,i::l)
        ) (fv,[]) l
    in fv, List.rev l

  and get_vars = List.map (function Lvar v -> v | _ -> assert false )

  and fun_create rv nfv fv arg body =
    let nfv = Ids.add arg nfv in
    let nfv2 = Ids.singleton arg in
    let fv2 = Idm.empty in
    let fv2, lam = tlambda rv nfv2 fv2 body in
    let i = register_function lam arg fv2 in
    let fv, l = Idm.fold
        (fun i _ (fv,l) ->
           let fv,i = check rv nfv fv i in
           (fv,i::l)
        )
        fv2 (fv,[])
    in
    let l = List.rev l in
    ( fv, TPfun i, l )

  in

  let fv, lam =  tlambda Ids.empty Ids.empty Idm.empty code in
  let lam =
    Idm.fold (fun gid id lam ->
        (* Format.printf "Gid : %s %i@." gid.Ident.name gid.Ident.stamp; *)
        assert ( gid.Ident.stamp = 0 );
        tlet ~k:Alias ~id ( Tvar ( "",gid ) ) lam
      )
      fv lam
  in
  lam
