open SmtCertif
open SmtForm
open SatAtom
open SmtTrace
open Zchaff
open Sat_checker


let mkInt = ExtrNative.of_int
let mkArray = ExtrNative.of_array


let make_roots first last =
  let roots = Array.make (last.id + 1) (mkArray [||]) in
  let mk_elem l =
    let x = match Form.pform l with
      | Fatom x -> x + 2
      | _ -> assert false  in
    mkInt (if Form.is_pos l then x lsl 1 else (x lsl 1) lxor 1) in
  let r = ref first in
  while !r.id < last.id do
    let root = Array.of_list (get_val !r) in
    let croot = Array.make (Array.length root) (mkInt 0) in
    Array.iteri (fun i l -> croot.(i) <- mk_elem l) root;
    roots.(!r.id) <- mkArray croot;
    r := next !r
  done;
  let root = Array.of_list (get_val !r) in
  let croot = Array.make (Array.length root) (mkInt 0) in
  Array.iteri (fun i l -> croot.(i) <- mk_elem l) root;
  roots.(!r.id) <- mkArray croot;
  mkArray roots


let to_coq confl =
  let out_c c = mkInt (get_pos c) in
  let step_to_coq c =
    match c.kind with
      | Res res ->
	let size = List.length res.rtail + 2 in
	let args = Array.make size (mkInt 0) in
	args.(0) <- out_c res.rc1;
	args.(1) <- out_c res.rc2;
	let l = ref res.rtail in
	for i = 2 to size - 1 do
	  match !l with
	    | c::tl ->
	      args.(i) <- out_c c;
	      l := tl
	    | _ -> assert false
	done;
        Sat_Checker.Res (out_c c, mkArray args)
      | _ -> assert false in
  let def_step = Sat_Checker.Res (mkInt 0, mkArray [|mkInt 0|]) in
  let r = ref confl in
  let nc = ref 0 in
  while not (isRoot !r.kind) do r := prev !r; incr nc done;
  let size = !nc in
  let max = Parray.max_array_length32 - 1 in
  let q,r1 = size / max, size mod max in

  let trace =
    let len = if r1 = 0 then q else q + 1 in
    Array.make len (mkArray [|def_step|]) in
  for j = 0 to q - 1 do
    let tracej = Array.make Parray.max_array_length32 def_step in
    for i = 0 to max - 1 do
      r := next !r;
      tracej.(i) <- step_to_coq !r;
    done;
    trace.(j) <- mkArray tracej
  done;
  if r1 <> 0 then begin
    let traceq = Array.make r1 def_step in
    for i = 0 to r1-1 do
      r := next !r;
      traceq.(i) <- step_to_coq !r;
    done;
    trace.(q) <- mkArray traceq
  end;
  mkArray trace


let checker fdimacs ftrace =
  SmtTrace.clear ();
  let _,first,last,reloc = import_cnf fdimacs in
  let d = make_roots first last in

  let max_id, confl = import_cnf_trace reloc ftrace first last in
  let tres = to_coq confl in
  let certif = Sat_Checker.Certif (mkInt (max_id+1), tres, mkInt (get_pos confl)) in

  let b = Sat_Checker.checker d certif in
  SmtTrace.clear ();
  b
