Add LoadPath ".." as SMTCoq. 
Require Import SMTCoq. 
Require Import Bool PArray Int31 List ZArith.

Local Open Scope int31_scope.

(*Time Zchaff_Checker "sat1.cnf" "sat1.zlog".*)

(*Time Parse_certif_trim d20 t20 "dubois20.cnf" "duboislongmult11.cctrim".
(* initial = 0.027, trace = 3.847;type init = 0.123; type trace = 13.176
Finished transaction in 17. secs (16.922711u,0.250174s) *)
Time Eval native_compute in Sat_Checker.checker d20 t20.
(* 
Evaluation done in 10.40857
     = true
     : bool
Finished transaction in 20. secs (19.377579u,0.109751s)
*)
*)


Require Import Trace2.
Import String. Import Resource.

Time Trim_dimacs erdos "erdos1161_60.cnf".  

Lemma foo :  forall rho : Valuation.t,
       Valuation.wf rho -> ~ Sat_Checker.valid rho erdos.
apply (@Sat_Checker.checker_correct erdos "erdos1161_60.reso"%string).
native_cast_no_check (refl_equal true).
Time Qed.
