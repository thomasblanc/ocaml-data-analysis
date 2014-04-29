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
