Add LoadPath ".." as SMTCoq. 
Require Import SMTCoq.
Require Import Bool PArray Int31 List ZArith.

Local Open Scope int31_scope.

Require Import Trace2.
Import String. Import Resource.

Time Trim_dimacs erdos60 "erdos1161_60.cnf".  

Lemma erdos60th :  forall rho : Valuation.t,
       Valuation.wf rho -> ~ Sat_Checker.valid rho erdos60.
apply (@Sat_Checker.checker_correct erdos60 "erdos1161_60.reso"%string).
native_cast_no_check (refl_equal true).
Time Qed.

