open Entries
open Declare
open Decl_kinds

open CoqTerms
open SmtMisc

module Vector = struct
  type 'a t = { 
    mutable pos : int; 
    dfl : 'a;
    mutable vec : 'a array }
    
  let create n a = {pos = 0; dfl = a; vec = Array.make n a}

  let extend v =
    let len = Array.length v.vec in
    if len <= v.pos then begin
      let nlen = min (2*len+1) Sys.max_array_length in
      let vec = Array.make nlen v.dfl in
      Array.blit v.vec 0 vec 0 len;
      v.vec <- vec
    end

  let push v a = 
    extend v;
    v.vec.(v.pos) <- a;
    v.pos <- v.pos + 1

  let size v = v.pos

  let clear v = v.pos <- 0

  let to_array v = 
    let t = Array.sub v.vec 0 v.pos in
    clear v; t

end
    
let rec next_char in_channel = 
  let c = input_char in_channel in
  if c = ' ' || c = '\n' then next_char in_channel
  else c

let unread_char in_channel = 
  seek_in in_channel (pos_in in_channel - 1)
    
let ichar0 = int_of_char '0'

let to_int c = int_of_char c - ichar0 
  
let read_int in_channel = 
  let c = next_char in_channel in
  let rec aux n =
    let i = to_int (input_char in_channel) in
    if (0 <= i && i < 10) then aux (n*10 + i) else n in
  let sign,c = 
    if c = '-' then -1, input_char in_channel else 1, c in
  let n = aux (to_int c) in
  sign * n 

let rec skip_line in_channel = 
  let c = input_char in_channel in
  if c <> '\n' then skip_line in_channel

let mk_clit x = 
  let cx = if 0 <= x then x + 1 else (-x + 1) in
  mkInt (if 0 <= x then cx lsl 1 else (cx lsl 1) lxor 1)

let cvec = Vector.create 100 (mkInt 0)

let rec read_clause1 in_channel = 
  let i = read_int in_channel in
  if i <> 0 then (Vector.push cvec (mk_clit i); read_clause1 in_channel)

let read_clause in_channel =
  read_clause1 in_channel;
  (* Push the default value *)
  Vector.push cvec (mkInt 0);
  Term.mkArray (Lazy.force cint, Vector.to_array cvec)

let read_dimacs fdimacs = 
  let in_channel = open_in fdimacs in
  let cdefault = Term.mkArray (Lazy.force cint, Array.make 1 (mkInt 0)) in
  let roots = Vector.create 30000 cdefault in
  let rec read_cnf () = 
    let c = try Some (next_char in_channel) with End_of_file -> None in
    match c with
    | Some 'c' -> skip_line in_channel;read_cnf () 
    | Some 'p' -> skip_line in_channel;read_cnf ()
    | Some _   -> 
      unread_char in_channel; 
      Vector.push roots (read_clause in_channel);
      read_cnf ()
    | None -> () in
  read_cnf ();
  let nclauses = Vector.size roots in
  (* Push the default value *)
  Vector.push roots cdefault;
  Term.mkArray (mklApp carray [|Lazy.force cint|],Vector.to_array roots), 
  nclauses

let rec read_reso1 in_channel = 
  let i = read_int in_channel in
  if i <> 0 then 
    (Vector.push cvec (mkInt (i-1)); read_reso1 in_channel)

let read_reso in_channel =
  read_reso1 in_channel;
  (* Push the default value *)
  Vector.push cvec (mkInt 0);
  Vector.to_array cvec

let rec skip_clause in_channel = 
  let i = read_int in_channel in
  if i <> 0 then skip_clause in_channel
  
let sat_checker_modules = [ ["SMTCoq";"Trace";"Sat_Checker"] ]
let cRes = gen_constant sat_checker_modules "Res"
let cCertif = gen_constant sat_checker_modules "Certif"
let step = gen_constant sat_checker_modules "step"
let mk_cres pos reso =
  mklApp cRes [|mkInt (pos-1); Term.mkArray (Lazy.force cint, reso)|]

let read_trace needed_size ftrace = 
  let in_channel = open_in ftrace in
  let rdefault = mk_cres 1 (Array.make 1 (mkInt 0)) in
  let trace = Vector.create 15000000 rdefault in
  let rec read last = 
    let id = try Some (read_int in_channel) with End_of_file -> None in
    match id with
    | Some id -> 
      needed_size := max !needed_size id;
      skip_clause in_channel;
      Vector.push trace (mk_cres id (read_reso in_channel));
      read id
    | None -> (last - 1) in
  let confl = read 0 in
  (* Push the default value *)
  Vector.push trace rdefault;
  (* FIXME *)
  (* Allocate the trace *)
  let size = Vector.size trace in
  let max = Parray.max_array_length32 - 1 in
  let q = size / max and r1 = size mod max in
  let ttrace = 
    let len = if r1 = 0 then q + 1 else q + 2 in
    Array.make len (Term.mkArray (Lazy.force step, [|rdefault|])) in
  let k = ref 0 in
  let get () = let res = trace.Vector.vec.(!k) in incr k; res in
  for j = 0 to q - 1 do
    let tracej = Array.make Parray.max_array_length32 rdefault in
    for i = 0 to max - 1 do tracej.(i) <- get () done;
    ttrace.(j) <- Term.mkArray (Lazy.force step, tracej)
  done;
  if r1 <> 0 then begin
    let traceq = Array.make (r1 + 1) rdefault in
    for i = 0 to r1-1 do traceq.(i)  <- get () done;
    ttrace.(q) <- Term.mkArray (Lazy.force step, traceq)
  end;
  Term.mkArray (mklApp carray [|Lazy.force step|], ttrace), confl
    
let parse_certif dimacs trace fdimacs ftrace =
  let t0 = Sys.time () in
  let cnf, nclauses = read_dimacs fdimacs in
  let t1 = Sys.time () in
  Format.eprintf "initial = %.3f@." (t1 -. t0);
  let needed_size = ref nclauses in
  let tres, confl = read_trace needed_size ftrace in
  let ce1 =
    { const_entry_body = cnf;
      const_entry_type = None;
      const_entry_secctx = None;
      const_entry_opaque = false;
      const_entry_inline_code = false} in
  let t2 = Sys.time () in
  Format.eprintf "initial = %.3f, trace = %.3f@." (t1 -. t0) (t2 -. t1);
  let _ = 
    declare_constant dimacs (DefinitionEntry ce1, IsDefinition Definition) in
  let t3 = Sys.time () in
  Format.eprintf "initial = %.3f, trace = %.3f;type init = %.3f@." 
    (t1 -. t0) (t2 -. t1) (t3 -. t2);
  let certif = 
    mklApp cCertif [|mkInt !needed_size; tres; mkInt confl|] in 
  let ce2 =
    { const_entry_body = certif;
      const_entry_type = None;
      const_entry_secctx = None;
      const_entry_opaque = false;
      const_entry_inline_code = false} in
  let _ = 
    declare_constant trace (DefinitionEntry ce2, IsDefinition Definition) in
  let t4 = Sys.time () in
  Format.eprintf "initial = %.3f, trace = %.3f;type init = %.3f; type trace = %.3f@." (t1 -. t0) (t2 -. t1) (t3 -. t2) (t4 -. t3);
  ()

let cchecker = gen_constant sat_checker_modules "checker"

let checker fdimacs ftrace =
  let t0 = Sys.time () in
  let cnf, nclauses = read_dimacs fdimacs in
  let t1 = Sys.time () in
  Format.eprintf "initial = %.3f@." (t1 -. t0);
  let needed_size = ref nclauses in
  let tres, confl = read_trace needed_size ftrace in
  let certif = 
    mklApp cCertif [|mkInt !needed_size; tres; mkInt confl|] in 
  let t2 = Sys.time () in
  Format.eprintf "initial = %.3f, trace = %.3f@." (t1 -. t0) (t2 -. t1);
  let tm = mklApp cchecker [|cnf; certif|] in
  let env = Global.env () in
  let res = 
    Nativenorm.native_norm env tm (Lazy.force cbool) in
  let expr = Constrextern.extern_constr true env res in
  Vernacentries.interp (Vernacexpr.VernacCheckMayEval (None, None, expr))

let ccertif = gen_constant sat_checker_modules "certif"
let ctheorem_checker = gen_constant sat_checker_modules "theorem_checker"
let cinterp_var = gen_constant sat_checker_modules "interp_var"
let cvalid = gen_constant sat_checker_modules "valid"

let dimacs dimacs fdimacs = 
  let cnf, nclauses = read_dimacs fdimacs in
  let ce1 =
    { const_entry_body = cnf;
      const_entry_type = None;
      const_entry_secctx = None;
      const_entry_opaque = false;
      const_entry_inline_code = false} in
  let _ = declare_constant dimacs (DefinitionEntry ce1, IsDefinition Definition) in
  ()

  
let theorem dimacs name fdimacs ftrace =   
  let t0 = Sys.time () in
  let cnf, nclauses = read_dimacs fdimacs in
  let t1 = Sys.time () in
  Format.eprintf "initial = %.3f@." (t1 -. t0);
  let ce1 =
    { const_entry_body = cnf;
      const_entry_type = None;
      const_entry_secctx = None;
      const_entry_opaque = false;
      const_entry_inline_code = false} in
  let roots = 
    declare_constant dimacs (DefinitionEntry ce1, IsDefinition Definition) in
  let t2 = Sys.time () in
  Format.eprintf "initial = %.3f, typing init = %.3f@." (t1 -. t0) (t2 -. t1);
  let needed_size = ref nclauses in
  let tres, confl = read_trace needed_size ftrace in
  let certif = 
    mklApp cCertif [|mkInt !needed_size; tres; mkInt confl|] in 
  let t3 = Sys.time () in
  Format.eprintf "initial = %.3f, typing init = = %.3f;trace = %.3f@." 
    (t1 -. t0) (t2 -. t1) (t3 -. t2);
  
  let rhotype = 
    Term.mkProd(Names.Anonymous, Lazy.force cint, Lazy.force cbool) in
  let d = Term.mkConst roots in
  let theorem_type = 
    Term.mkProd
      (mkName "rho", rhotype,
       let interp = mklApp cinterp_var [| Term.mkRel 1 (*rho*) |] in
       mklApp cnot [| mklApp cis_true [|mklApp cvalid [| interp; d|] |] |]) in
  let theorem_proof = 
    Term.mkLetIn 
      (mkName "c", certif, Lazy.force ccertif,
         mklApp ctheorem_checker
           [| d; Term.mkRel 1 (*c*);
	      native_cast_true (mklApp cchecker [|d; Term.mkRel 1(*c*)|]) |]) in
  let ce =
    { const_entry_body = theorem_proof;
      const_entry_type = Some theorem_type;
      const_entry_secctx = None;
      const_entry_opaque = true;
      const_entry_inline_code = false} in
  let _ = 
    declare_constant name (DefinitionEntry ce, IsDefinition Definition) in
  ()

      

