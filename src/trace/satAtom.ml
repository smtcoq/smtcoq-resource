(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2014                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     INRIA - École Polytechnique - MSR                                  *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

open SmtMisc
open CoqTerms

module Atom = 
  struct 

    type t = int 

    let index a = a

    let equal a1 a2 = a1 == a2

    let is_bool_type a = true

    type reify_tbl =
        { mutable count : int;
	          tbl : (Term.constr, int) Hashtbl.t 
	}

    let create () = 
      { count = 0;
	tbl =  Hashtbl.create 17 }

    let declare reify a = 
      let res = reify.count in
      Hashtbl.add reify.tbl a res;
      reify.count <- res + 1;
      res

    let get reify a =
      try Hashtbl.find reify.tbl a 
      with Not_found -> declare reify a

    let atom_tbl reify =
      let t = Array.make (reify.count + 1) (Lazy.force ctrue) in
      let set c i = t.(i) <- c in
      Hashtbl.iter set reify.tbl;
      t

    let interp_tbl reify =
      Term.mkArray (Lazy.force cbool, atom_tbl reify)

  end

module Form = SmtForm.Make(Atom)
module Trace = SmtTrace.MakeOpt(Form)
module Cnf = SmtCnf.MakeCnf(Form)

      

