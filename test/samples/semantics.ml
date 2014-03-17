
let () =
  assert true;
  assert( not false );
  assert( true && true );
  assert(not ( true && false ) );
  assert(not ( false && true ) );
  assert(not ( false && false ) );
  assert( true || true );
  assert( true || false );
  assert( false || true );
  assert(not ( false || false ));
  ()

let () =
  assert( 1 = 1 );
  assert( not( 1 = 2 ) );
  assert( 1 <> 2 );
  assert( not( 1 <> 1 ) );
  assert( 1 == 1 );
  assert( not( 1 == 2 ) );
  assert( 1 != 2 );
  assert( not( 1 != 1 ) );
  assert( 1 < 2 );
  assert( not( 2 < 2 ) );
  assert( 2 > 1 );
  assert( not( 2 > 2 ) );
  assert( 2 <= 2 );
  assert( not( 3 <= 2 ) );
  assert( 2 >= 2 );
  assert( not( 2 >= 3 ) );
  ()

let () =
  (* assert( compare 0 0 = 0 ); *)
  (* assert( compare 0 1 < 0 ); *)
  (* assert( compare 1 0 > 0 ); *)
  ()

let () =
  assert( ~- 1 = -1 );
  assert( ~+ 1 = 1 );
  assert( succ 1 = 2 );
  assert( pred 1 = 0 );
  assert( 1 + 1 = 2 );
  assert( 1 - 1 = 0 );
  (* assert( 1 * 2 = 2 ); *)
  (* assert( 1 / 1 = 1 ); *)
  (* assert( 3 mod 2 = 1 ); *)
  assert( abs (-1) = 1 );
  (* assert( -1 land 3 = 3 ); *)
  (* assert( -1 lor 3 = -1 ); *)
  (* assert( -1 lxor 3 = -4 ); *)
  (* assert( lnot (-1) = 0 ); *)
  (* assert( 1 lsl 2 = 4 ); *)
  (* assert( 1 lsr 1 = 0 ); *)
  (* assert( 1 asr 1 = 0 ); *)
  ()

let () =
  (* assert( ~- min_int = min_int ); *)
  (* assert( ~- max_int = min_int + 1 ); *)
  ()

let () =
  let f x = x + x in
  assert( 1 |> f = 2 );
  (* assert( 1 |> f |> f = 4 ); *)
  assert( f @@ 1 = 2 );
  (* assert( f @@ f @@ 1 = 4 ); *)
  ()

let () =
  let a = "a" in
  let b = "b" in
  (* assert( a == a ); *)
  (* assert( a != b ); *)
  (* assert( "a" = "a" ); *)
  (* assert( "a" <> "b" ); *)
  (* assert( "a" ^ "b" = "ab" ); *)
  (* assert( "a" ^ "c" <> "ab" ); *)
  ()

let () =
  (* assert( ignore 1 = () ); *)
  (* assert( string_of_bool true = "true" ); *)
  ()

let () =
  assert( fst (1,2) = 1 );
  assert( snd (1,2) = 2 );
  ()


let () =
  let r = ref 0 in
  assert( !r = 0 );
  r := 1;
  assert( !r = 1 );
  incr r;
  assert( !r = 2 );
  decr r;
  assert( !r = 1 );
  ()

let () =
  let r = ref 0 in
  ignore( r == r ); (* forbid promotion to variable *)
  (* assert( !r = 0 ); *)
  r := 1;
  (* assert( !r = 1 ); *)
  (* incr r; *)
  (* assert( !r = 2 ); *)
  (* decr r; *)
  (* assert( !r = 1 ); *)
  ()


let () =
  let x = if true then 1 else 2 in
  assert( x = 1 );
  let x = if false then 1 else 2 in
  assert( x = 2 );
  let x = if true then 1 else assert false in
  assert( x = 1 );
  let x = if false then assert false else 2 in
  assert( x = 2 );

  for i = 1 to 10 do
    if i = 5 then assert(i = 5);
    (* if i <> 5 then assert(i <> 5); *) (* cannot be represented by interval *)
    if i > 5 then assert(i > 5);
    (* if i < 5 then assert(i < 5); *)
  done;

  ()

let () =
  let f x y = x + y in
  let g f x = f x in
  assert( f 1 2 = 3 );
  assert( not (f 1 2 = 4) );
  assert( g f 1 2 = 3 );
  assert( not (g f 1 2 = 4) );
  ()


type tt =
  | A | B | C | D
  | E of int | F of int

exception Exn1
exception Exn2

let () =

  let x =
    match A with
    | A -> 1
    | _ -> 2 in
  (* assert(x = 1); *)

  let x =
    match B with
    | A -> 1
    | C -> 2
    | _ -> 3 in
  assert(x = 3);

  let x =
    match E 4 with
    | E x -> x
    | _ -> 0 in
  assert(x = 4);

  let r = ref None in
  for i = 0 to 1 do
    let v =
      if i = 0
      then E 5
      else F 4
    in
    match v with
    | E i -> r := Some i
    | F i -> r := Some (i + 1)
    | _ -> r := Some 0
  done;
  (match !r with
   | Some x ->
     (* TODO: add a primitive to help assert that a node is reachable *)
     (* assert_visited () *)
     assert(x = 5)
   | None ->
     (* assert false; *)
     ());

  for i = 0 to 10 do
    let v = match i with
      | 0 -> A
      | 1 -> B
      | 2 -> C
      | 3 -> D
      | 4 -> E 1
      | n -> F n
    in

    match v with
    | A ->
      (match v with
       | A ->
         (* assert_visited () *)
         ()
       | _ -> assert false)
    | E _ ->
      (match v with
       | E _ ->
         (* assert_visited () *)
         ()
       | _ -> assert false)
    (* | F n -> *)
    (*   (match v with *)
    (*    | F m -> *)
    (*      (\* assert_visited () *\) *)
    (*      assert (n = m) *)
    (*    | _ -> raise Exn1) *)
    | _ -> ()

  done;
  (* assert_visited (); *)
  ()
