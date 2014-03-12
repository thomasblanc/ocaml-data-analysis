
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
  assert( 1 * 2 = 2 );
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
    (* if i = 5 then assert(i <> 5); *) (* cannot be represented by interval *)
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
