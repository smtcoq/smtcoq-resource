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

Require Export Int31 List PArray.
Require Export State SMT_terms Trace.
Export Atom Form Sat_Checker Cnf_Checker Euf_Checker.
Require Export State2 Trace2.

Declare ML Module "trace/smt_tactic".
