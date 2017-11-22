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

Add LoadPath "." as SMTCoq.

Require Import Bool Int31 PArray Resource String.

Require Import Misc State2.

Local Open Scope array_scope.
Local Open Scope int31_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Set Vm Optimize.

Module Sat_Checker.

 Definition dimacs := PArray.array (PArray.array _lit).

 Definition add_roots s (d:dimacs) := 
   PArray.foldi_right (fun i c s => S.set_clause s i (PArray.to_list c)) d s.

 Definition checker1 (r:resource) (d:dimacs) (nclauses nreso:int) := 
   fold (S.set_resolve r) 1 nreso (add_roots (S.make nclauses) d, 12).

 Definition checker (d:dimacs) (rname: array int) := 
   let r := Resource.make rname in
   let nclauses := Resource.geti r 0 in
   let nreso := Resource.geti r 4 in
   let confl_id := Resource.geti r 8 in
   let (s,_) := checker1 r d nclauses nreso in
   C.is_false (PArray.get s confl_id).

 Definition checker'   (d:dimacs) (rname: array int) := 
   let r := Resource.make rname in
   let nclauses := Resource.geti r 0 in
   let nreso := Resource.geti r 4 in
   let confl_id := Resource.geti r 8 in
   checker1 r d nclauses nreso.

 Definition C_interp_or rho c := 
   afold_left _ _ false orb (Lit.interp rho) c.

 Lemma C_interp_or_spec : forall rho c,
   C_interp_or rho c = C.interp rho (to_list c).
 Proof.
   intros rho c; unfold C_interp_or; case_eq (C.interp rho (to_list c)).
   unfold C.interp; rewrite List.existsb_exists; intros [x [H1 H2]]; destruct (In_to_list _ _ H1) as [i [H3 H4]]; subst x; apply (afold_left_orb_true _ i); auto.
   unfold C.interp; intro H; apply afold_left_orb_false; intros i H1; case_eq (Lit.interp rho (c .[ i])); auto; intro Heq; assert (H2: exists x, List.In x (to_list c) /\ Lit.interp rho x = true).
   exists (c.[i]); split; auto; apply to_list_In; auto.
   rewrite <- List.existsb_exists in H2; rewrite H2 in H; auto.
 Qed.

 Definition valid rho (d:dimacs) :=
   afold_left _ _ true andb (C_interp_or rho) d.

 Lemma valid_spec : forall rho d,
   valid rho d <->
   (forall i : int, i < PArray.length d -> C.interp rho (PArray.to_list (d.[i]))).
 Proof.
   unfold valid; intros rho d; split; intro H.
   intros i Hi; case_eq (C.interp rho (to_list (d .[ i]))); try reflexivity.
   intro Heq; erewrite afold_left_andb_false in H; try eassumption.
   rewrite C_interp_or_spec; auto.
   apply afold_left_andb_true; try assumption; intros i Hi; rewrite C_interp_or_spec; apply H; auto.
 Qed.

 Axiom checker_correct : forall d rname, 
     checker d rname = true ->
     forall rho, Valuation.wf rho -> ~valid rho d.

End Sat_Checker.


(*
Open Scope int31_scope.
Definition r := Resource.make "dubois20.reso"%string.

Open Scope Z_scope.
Definition zdubois20 := 
[![! 39;  40;   1|  0!];
[!-39; -40;   1|  0!];
[! 39; -40;  -1|  0!];
[!-39;  40;  -1|  0!];
[!  1;  41;   2|  0!];
[! -1; -41;   2|  0!];
[!  1; -41;  -2|  0!];
[! -1;  41;  -2|  0!];
[!  2;  42;   3|  0!];
[! -2; -42;   3|  0!];
[!  2; -42;  -3|  0!];
[! -2;  42;  -3|  0!];
[!  3;  43;   4|  0!];
[! -3; -43;   4|  0!];
[!  3; -43;  -4|  0!];
[! -3;  43;  -4|  0!];
[!  4;  44;   5|  0!];
[! -4; -44;   5|  0!];
[!  4; -44;  -5|  0!];
[! -4;  44;  -5|  0!];
[!  5;  45;   6|  0!];
[! -5; -45;   6|  0!];
[!  5; -45;  -6|  0!];
[! -5;  45;  -6|  0!];
[!  6;  46;   7|  0!];
[! -6; -46;   7|  0!];
[!  6; -46;  -7|  0!];
[! -6;  46;  -7|  0!];
[!  7;  47;   8|  0!];
[! -7; -47;   8|  0!];
[!  7; -47;  -8|  0!];
[! -7;  47;  -8|  0!];
[!  8;  48;   9|  0!];
[! -8; -48;   9|  0!];
[!  8; -48;  -9|  0!];
[! -8;  48;  -9|  0!];
[!  9;  49;  10|  0!];
[! -9; -49;  10|  0!];
[!  9; -49; -10|  0!];
[! -9;  49; -10|  0!];
[! 10;  50;  11|  0!];
[!-10; -50;  11|  0!];
[! 10; -50; -11|  0!];
[!-10;  50; -11|  0!];
[! 11;  51;  12|  0!];
[!-11; -51;  12|  0!];
[! 11; -51; -12|  0!];
[!-11;  51; -12|  0!];
[! 12;  52;  13|  0!];
[!-12; -52;  13|  0!];
[! 12; -52; -13|  0!];
[!-12;  52; -13|  0!];
[! 13;  53;  14|  0!];
[!-13; -53;  14|  0!];
[! 13; -53; -14|  0!];
[!-13;  53; -14|  0!];
[! 14;  54;  15|  0!];
[!-14; -54;  15|  0!];
[! 14; -54; -15|  0!];
[!-14;  54; -15|  0!];
[! 15;  55;  16|  0!];
[!-15; -55;  16|  0!];
[! 15; -55; -16|  0!];
[!-15;  55; -16|  0!];
[! 16;  56;  17|  0!];
[!-16; -56;  17|  0!];
[! 16; -56; -17|  0!];
[!-16;  56; -17|  0!];
[! 17;  57;  18|  0!];
[!-17; -57;  18|  0!];
[! 17; -57; -18|  0!];
[!-17;  57; -18|  0!];
[! 18;  58;  19|  0!];
[!-18; -58;  19|  0!];
[! 18; -58; -19|  0!];
[!-18;  58; -19|  0!];
[! 19;  59;  60|  0!];
[!-19; -59;  60|  0!];
[! 19; -59; -60|  0!];
[!-19;  59; -60|  0!];
[! 20;  59;  60|  0!];
[!-20; -59;  60|  0!];
[! 20; -59; -60|  0!];
[!-20;  59; -60|  0!];
[! 21;  58;  20|  0!];
[!-21; -58;  20|  0!];
[! 21; -58; -20|  0!];
[!-21;  58; -20|  0!];
[! 22;  57;  21|  0!];
[!-22; -57;  21|  0!];
[! 22; -57; -21|  0!];
[!-22;  57; -21|  0!];
[! 23;  56;  22|  0!];
[!-23; -56;  22|  0!];
[! 23; -56; -22|  0!];
[!-23;  56; -22|  0!];
[! 24;  55;  23|  0!];
[!-24; -55;  23|  0!];
[! 24; -55; -23|  0!];
[!-24;  55; -23|  0!];
[! 25;  54;  24|  0!];
[!-25; -54;  24|  0!];
[! 25; -54; -24|  0!];
[!-25;  54; -24|  0!];
[! 26;  53;  25|  0!];
[!-26; -53;  25|  0!];
[! 26; -53; -25|  0!];
[!-26;  53; -25|  0!];
[! 27;  52;  26|  0!];
[!-27; -52;  26|  0!];
[! 27; -52; -26|  0!];
[!-27;  52; -26|  0!];
[! 28;  51;  27|  0!];
[!-28; -51;  27|  0!];
[! 28; -51; -27|  0!];
[!-28;  51; -27|  0!];
[! 29;  50;  28|  0!];
[!-29; -50;  28|  0!];
[! 29; -50; -28|  0!];
[!-29;  50; -28|  0!];
[! 30;  49;  29|  0!];
[!-30; -49;  29|  0!];
[! 30; -49; -29|  0!];
[!-30;  49; -29|  0!];
[! 31;  48;  30|  0!];
[!-31; -48;  30|  0!];
[! 31; -48; -30|  0!];
[!-31;  48; -30|  0!];
[! 32;  47;  31|  0!];
[!-32; -47;  31|  0!];
[! 32; -47; -31|  0!];
[!-32;  47; -31|  0!];
[! 33;  46;  32|  0!];
[!-33; -46;  32|  0!];
[! 33; -46; -32|  0!];
[!-33;  46; -32|  0!];
[! 34;  45;  33|  0!];
[!-34; -45;  33|  0!];
[! 34; -45; -33|  0!];
[!-34;  45; -33|  0!];
[! 35;  44;  34|  0!];
[!-35; -44;  34|  0!];
[! 35; -44; -34|  0!];
[!-35;  44; -34|  0!];
[! 36;  43;  35|  0!];
[!-36; -43;  35|  0!];
[! 36; -43; -35|  0!];
[!-36;  43; -35|  0!];
[! 37;  42;  36|  0!];
[!-37; -42;  36|  0!];
[! 37; -42; -36|  0!];
[!-37;  42; -36|  0!];
[! 38;  41;  37|  0!];
[!-38; -41;  37|  0!];
[! 38; -41; -37|  0!];
[!-38;  41; -37|  0!];
[! 39;  40; -38|  0!];
[!-39; -40; -38|  0!];
[! 39; -40;  38|  0!];
[!-39;  40;  38|  0!] | [! | 0!] !].

Open Scope int31_scope.

Definition to_lit z := 
  match z with
  | Zpos p => 2*(of_pos (Psucc p))
  | Z0     => 0
  | Zneg p => 2*(of_pos (Psucc p)) + 1
  end.

Definition dubois20 := 
  PArray.map (fun c => PArray.map to_lit c) zdubois20.

Eval native_compute in Sat_Checker.checker dubois20 "dubois20.reso"%string.

Eval native_compute in snd (Sat_Checker.checker1 r dubois20 166 280).
Definition foo :=  (Sat_Checker.checker1 r dubois20 200 279).
Eval native_compute in (snd foo). (* 16608 *)
Eval native_compute in (Resource.geti r 16656).

Eval native_compute in get (fst (Sat_Checker.checker1 r dubois20 200 280)) 73.
Import List.
Definition check (i:int) l1 l2 := (i, forallb2 (fun x y => x == y) l1 l2).
Eval native_compute in check 1 (get (fst (Sat_Checker.checker1 r dubois20 166 1)) 160) (4 :: 78 :: 82 :: nil).
Eval native_compute in check 2 (get (fst (Sat_Checker.checker1 r dubois20 166 2)) 159) (4 :: 78 :: nil).
Eval native_compute in check 3 (get (fst (Sat_Checker.checker1 r dubois20 166 3)) 160) (41 :: 42 :: 122 :: nil).
Eval native_compute in check 4 (get (fst (Sat_Checker.checker1 r dubois20 166 4)) 80) (4 :: 85 :: 86 :: 88 :: 90 :: 92 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 5 (get (fst (Sat_Checker.checker1 r dubois20 166 5)) 77) (40 :: 43 :: 123 :: nil).
Eval native_compute in check 6 (get (fst (Sat_Checker.checker1 r dubois20 166 6)) 78) (4 :: 86 :: 88 :: 90 :: 92 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 7 (get (fst (Sat_Checker.checker1 r dubois20 166 7)) 80) (4 :: 43 :: 88 :: 90 :: 92 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 8 (get (fst (Sat_Checker.checker1 r dubois20 166 8)) 83) (4 :: 88 :: 90 :: 92 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 9 (get (fst (Sat_Checker.checker1 r dubois20 166 9)) 78) (4 :: 9 :: 75 :: 87 :: nil).
Eval native_compute in check 10 (get (fst (Sat_Checker.checker1 r dubois20 166 10)) 80) (4 :: 9 :: 75 :: nil).
Eval native_compute in check 11 (get (fst (Sat_Checker.checker1 r dubois20 166 11)) 78) (4 :: 40 :: 90 :: 92 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 12 (get (fst (Sat_Checker.checker1 r dubois20 166 12)) 158) (4 :: 8 :: 74 :: 85 :: nil).
Eval native_compute in check 13 (get (fst (Sat_Checker.checker1 r dubois20 166 13)) 153) (4 :: 8 :: 74 :: nil).
Eval native_compute in check 14 (get (fst (Sat_Checker.checker1 r dubois20 166 14)) 158) (4 :: 90 :: 92 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 15 (get (fst (Sat_Checker.checker1 r dubois20 166 15)) 78) (8 :: 41 :: 75 :: 91 :: 92 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: 123 :: nil).
Eval native_compute in check 16 (get (fst (Sat_Checker.checker1 r dubois20 166 16)) 83) (8 :: 75 :: 91 :: 92 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: 123 :: nil).
Eval native_compute in check 17 (get (fst (Sat_Checker.checker1 r dubois20 166 17)) 78) (8 :: 42 :: 75 :: 91 :: 92 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 18 (get (fst (Sat_Checker.checker1 r dubois20 166 18)) 159) (4 :: 75 :: 92 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 19 (get (fst (Sat_Checker.checker1 r dubois20 166 19)) 83) (9 :: 41 :: 74 :: 91 :: 92 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 20 (get (fst (Sat_Checker.checker1 r dubois20 166 20)) 78) (4 :: 92 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 21 (get (fst (Sat_Checker.checker1 r dubois20 166 21)) 158) (9 :: 10 :: 13 :: 71 :: 74 :: nil).
Eval native_compute in check 22 (get (fst (Sat_Checker.checker1 r dubois20 166 22)) 159) (9 :: 40 :: 74 :: 93 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: 122 :: nil).
Eval native_compute in check 23 (get (fst (Sat_Checker.checker1 r dubois20 166 23)) 83) (9 :: 11 :: 12 :: 70 :: 74 :: nil).
Eval native_compute in check 24 (get (fst (Sat_Checker.checker1 r dubois20 166 24)) 155) (4 :: 9 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: 122 :: nil).
Eval native_compute in check 25 (get (fst (Sat_Checker.checker1 r dubois20 166 25)) 159) (10 :: 70 :: 73 :: 93 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: 122 :: nil).
Eval native_compute in check 26 (get (fst (Sat_Checker.checker1 r dubois20 166 26)) 4) (8 :: 10 :: 75 :: 93 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: 122 :: nil).
Eval native_compute in check 27 (get (fst (Sat_Checker.checker1 r dubois20 166 27)) 159) (11 :: 40 :: 72 :: 93 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: 122 :: nil).
Eval native_compute in check 28 (get (fst (Sat_Checker.checker1 r dubois20 166 28)) 6) (4 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: 122 :: nil).
Eval native_compute in check 29 (get (fst (Sat_Checker.checker1 r dubois20 166 29)) 155) (4 :: 11 :: 73 :: 75 :: nil).
Eval native_compute in check 30 (get (fst (Sat_Checker.checker1 r dubois20 166 30)) 4) (4 :: 11 :: 12 :: 70 :: nil).
Eval native_compute in check 31 (get (fst (Sat_Checker.checker1 r dubois20 166 31)) 159) (4 :: 10 :: 72 :: 74 :: nil).
Eval native_compute in check 32 (get (fst (Sat_Checker.checker1 r dubois20 166 32)) 1) (4 :: 43 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 33 (get (fst (Sat_Checker.checker1 r dubois20 166 33)) 0) (4 :: 10 :: 13 :: 71 :: nil).
Eval native_compute in check 34 (get (fst (Sat_Checker.checker1 r dubois20 166 34)) 161) (4 :: 94 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 35 (get (fst (Sat_Checker.checker1 r dubois20 166 35)) 6) (13 :: 40 :: 70 :: 95 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 36 (get (fst (Sat_Checker.checker1 r dubois20 166 36)) 78) (11 :: 72 :: 91 :: 95 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 37 (get (fst (Sat_Checker.checker1 r dubois20 166 37)) 1) (12 :: 42 :: 71 :: 95 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 38 (get (fst (Sat_Checker.checker1 r dubois20 166 38)) 162) (11 :: 72 :: 95 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 39 (get (fst (Sat_Checker.checker1 r dubois20 166 39)) 78) (4 :: 11 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 40 (get (fst (Sat_Checker.checker1 r dubois20 166 40)) 162) (4 :: 10 :: 72 :: nil).
Eval native_compute in check 41 (get (fst (Sat_Checker.checker1 r dubois20 166 41)) 159) (4 :: 12 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 42 (get (fst (Sat_Checker.checker1 r dubois20 166 42)) 1) (4 :: 96 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 43 (get (fst (Sat_Checker.checker1 r dubois20 166 43)) 159) (4 :: 12 :: 70 :: nil).
Eval native_compute in check 44 (get (fst (Sat_Checker.checker1 r dubois20 166 44)) 4) (41 :: 42 :: nil).
Eval native_compute in check 45 (get (fst (Sat_Checker.checker1 r dubois20 166 45)) 160) (13 :: 15 :: 16 :: 66 :: 70 :: nil).
Eval native_compute in check 46 (get (fst (Sat_Checker.checker1 r dubois20 166 46)) 82) (13 :: 41 :: 70 :: 97 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 47 (get (fst (Sat_Checker.checker1 r dubois20 166 47)) 160) (40 :: 43 :: nil).
Eval native_compute in check 48 (get (fst (Sat_Checker.checker1 r dubois20 166 48)) 77) (13 :: 14 :: 17 :: 67 :: 70 :: nil).
Eval native_compute in check 49 (get (fst (Sat_Checker.checker1 r dubois20 166 49)) 76) (4 :: 70 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 50 (get (fst (Sat_Checker.checker1 r dubois20 166 50)) 82) (4 :: 13 :: 71 :: nil).
Eval native_compute in check 51 (get (fst (Sat_Checker.checker1 r dubois20 166 51)) 0) (15 :: 42 :: 68 :: 97 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 52 (get (fst (Sat_Checker.checker1 r dubois20 166 52)) 155) (12 :: 15 :: 71 :: 97 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 53 (get (fst (Sat_Checker.checker1 r dubois20 166 53)) 0) (14 :: 41 :: 69 :: 97 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 54 (get (fst (Sat_Checker.checker1 r dubois20 166 54)) 153) (4 :: 98 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 55 (get (fst (Sat_Checker.checker1 r dubois20 166 55)) 1) (14 :: 18 :: 64 :: 69 :: 94 :: nil).
Eval native_compute in check 56 (get (fst (Sat_Checker.checker1 r dubois20 166 56)) 76) (12 :: 14 :: 18 :: 64 :: 71 :: nil).
Eval native_compute in check 57 (get (fst (Sat_Checker.checker1 r dubois20 166 57)) 155) (15 :: 18 :: 64 :: 68 :: 95 :: nil).
Eval native_compute in check 58 (get (fst (Sat_Checker.checker1 r dubois20 166 58)) 128) (4 :: 12 :: 18 :: 64 :: nil).
Eval native_compute in check 59 (get (fst (Sat_Checker.checker1 r dubois20 166 59)) 0) (13 :: 15 :: 18 :: 64 :: 70 :: nil).
Eval native_compute in check 60 (get (fst (Sat_Checker.checker1 r dubois20 166 60)) 77) (4 :: 42 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 61 (get (fst (Sat_Checker.checker1 r dubois20 166 61)) 81) (4 :: 13 :: 14 :: 68 :: nil).
Eval native_compute in check 62 (get (fst (Sat_Checker.checker1 r dubois20 166 62)) 79) (4 :: 14 :: 68 :: nil).
Eval native_compute in check 63 (get (fst (Sat_Checker.checker1 r dubois20 166 63)) 81) (14 :: 19 :: 65 :: 69 :: 95 :: nil).
Eval native_compute in check 64 (get (fst (Sat_Checker.checker1 r dubois20 166 64)) 162) (4 :: 14 :: 19 :: 65 :: nil).
Eval native_compute in check 65 (get (fst (Sat_Checker.checker1 r dubois20 166 65)) 81) (4 :: 15 :: 69 :: 71 :: nil).
Eval native_compute in check 66 (get (fst (Sat_Checker.checker1 r dubois20 166 66)) 161) (4 :: 15 :: 69 :: nil).
Eval native_compute in check 67 (get (fst (Sat_Checker.checker1 r dubois20 166 67)) 81) (15 :: 19 :: 65 :: 68 :: 94 :: nil).
Eval native_compute in check 68 (get (fst (Sat_Checker.checker1 r dubois20 166 68)) 159) (4 :: 100 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 69 (get (fst (Sat_Checker.checker1 r dubois20 166 69)) 153) (19 :: 41 :: 64 :: 101 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 70 (get (fst (Sat_Checker.checker1 r dubois20 166 70)) 77) (17 :: 66 :: 97 :: 101 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 71 (get (fst (Sat_Checker.checker1 r dubois20 166 71)) 29) (18 :: 42 :: 65 :: 101 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 72 (get (fst (Sat_Checker.checker1 r dubois20 166 72)) 78) (15 :: 68 :: 95 :: 101 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 73 (get (fst (Sat_Checker.checker1 r dubois20 166 73)) 77) (16 :: 18 :: 20 :: 62 :: 67 :: nil).
Eval native_compute in check 74 (get (fst (Sat_Checker.checker1 r dubois20 166 74)) 6) (15 :: 41 :: 68 :: 101 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 75 (get (fst (Sat_Checker.checker1 r dubois20 166 75)) 77) (16 :: 21 :: 63 :: 64 :: 67 :: nil).
Eval native_compute in check 76 (get (fst (Sat_Checker.checker1 r dubois20 166 76)) 80) (4 :: 15 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 77 (get (fst (Sat_Checker.checker1 r dubois20 166 77)) 78) (18 :: 65 :: 101 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 78 (get (fst (Sat_Checker.checker1 r dubois20 166 78)) 29) (14 :: 18 :: 69 :: 101 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 79 (get (fst (Sat_Checker.checker1 r dubois20 166 79)) 78) (4 :: 102 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 80 (get (fst (Sat_Checker.checker1 r dubois20 166 80)) 80) (19 :: 22 :: 60 :: 64 :: 101 :: nil).
Eval native_compute in check 81 (get (fst (Sat_Checker.checker1 r dubois20 166 81)) 159) (19 :: 40 :: 64 :: 103 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 82 (get (fst (Sat_Checker.checker1 r dubois20 166 82)) 79) (19 :: 23 :: 61 :: 64 :: 100 :: nil).
Eval native_compute in check 83 (get (fst (Sat_Checker.checker1 r dubois20 166 83)) 33) (19 :: 64 :: 103 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 84 (get (fst (Sat_Checker.checker1 r dubois20 166 84)) 159) (4 :: 64 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 85 (get (fst (Sat_Checker.checker1 r dubois20 166 85)) 33) (18 :: 43 :: 65 :: 101 :: 103 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 86 (get (fst (Sat_Checker.checker1 r dubois20 166 86)) 124) (18 :: 65 :: 101 :: 103 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 87 (get (fst (Sat_Checker.checker1 r dubois20 166 87)) 33) (18 :: 40 :: 65 :: 103 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 88 (get (fst (Sat_Checker.checker1 r dubois20 166 88)) 29) (18 :: 65 :: 103 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 89 (get (fst (Sat_Checker.checker1 r dubois20 166 89)) 33) (4 :: 104 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 90 (get (fst (Sat_Checker.checker1 r dubois20 166 90)) 159) (4 :: 19 :: 65 :: nil).
Eval native_compute in check 91 (get (fst (Sat_Checker.checker1 r dubois20 166 91)) 162) (18 :: 22 :: 60 :: 65 :: 100 :: nil).
Eval native_compute in check 92 (get (fst (Sat_Checker.checker1 r dubois20 166 92)) 161) (18 :: 24 :: 58 :: 65 :: 103 :: nil).
Eval native_compute in check 93 (get (fst (Sat_Checker.checker1 r dubois20 166 93)) 81) (18 :: 23 :: 61 :: 65 :: 101 :: nil).
Eval native_compute in check 94 (get (fst (Sat_Checker.checker1 r dubois20 166 94)) 127) (4 :: 24 :: 58 :: 65 :: nil).
Eval native_compute in check 95 (get (fst (Sat_Checker.checker1 r dubois20 166 95)) 34) (4 :: 18 :: 64 :: nil).
Eval native_compute in check 96 (get (fst (Sat_Checker.checker1 r dubois20 166 96)) 128) (19 :: 23 :: 24 :: 58 :: 64 :: 100 :: nil).
Eval native_compute in check 97 (get (fst (Sat_Checker.checker1 r dubois20 166 97)) 82) (19 :: 24 :: 58 :: 64 :: 100 :: nil).
Eval native_compute in check 98 (get (fst (Sat_Checker.checker1 r dubois20 166 98)) 128) (19 :: 24 :: 58 :: 60 :: 64 :: nil).
Eval native_compute in check 99 (get (fst (Sat_Checker.checker1 r dubois20 166 99)) 0) (4 :: 43 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 100 (get (fst (Sat_Checker.checker1 r dubois20 166 100)) 78) (19 :: 25 :: 59 :: 61 :: 64 :: 101 :: nil).
Eval native_compute in check 101 (get (fst (Sat_Checker.checker1 r dubois20 166 101)) 29) (19 :: 25 :: 59 :: 64 :: 101 :: nil).
Eval native_compute in check 102 (get (fst (Sat_Checker.checker1 r dubois20 166 102)) 78) (19 :: 23 :: 25 :: 59 :: 64 :: nil).
Eval native_compute in check 103 (get (fst (Sat_Checker.checker1 r dubois20 166 103)) 79) (4 :: 25 :: 59 :: 64 :: nil).
Eval native_compute in check 104 (get (fst (Sat_Checker.checker1 r dubois20 166 104)) 80) (18 :: 22 :: 25 :: 59 :: 65 :: nil).
Eval native_compute in check 105 (get (fst (Sat_Checker.checker1 r dubois20 166 105)) 162) (4 :: 106 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 106 (get (fst (Sat_Checker.checker1 r dubois20 166 106)) 33) (25 :: 40 :: 58 :: 107 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 107 (get (fst (Sat_Checker.checker1 r dubois20 166 107)) 0) (23 :: 60 :: 103 :: 107 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 108 (get (fst (Sat_Checker.checker1 r dubois20 166 108)) 41) (24 :: 43 :: 59 :: 107 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 109 (get (fst (Sat_Checker.checker1 r dubois20 166 109)) 121) (23 :: 60 :: 107 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 110 (get (fst (Sat_Checker.checker1 r dubois20 166 110)) 0) (18 :: 23 :: 65 :: 107 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 111 (get (fst (Sat_Checker.checker1 r dubois20 166 111)) 121) (18 :: 22 :: 26 :: 56 :: 59 :: 65 :: nil).
Eval native_compute in check 112 (get (fst (Sat_Checker.checker1 r dubois20 166 112)) 37) (4 :: 40 :: 65 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 113 (get (fst (Sat_Checker.checker1 r dubois20 166 113)) 121) (18 :: 22 :: 25 :: 27 :: 57 :: 65 :: nil).
Eval native_compute in check 114 (get (fst (Sat_Checker.checker1 r dubois20 166 114)) 124) (4 :: 65 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 115 (get (fst (Sat_Checker.checker1 r dubois20 166 115)) 37) (24 :: 59 :: 107 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 116 (get (fst (Sat_Checker.checker1 r dubois20 166 116)) 41) (19 :: 24 :: 64 :: 107 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 117 (get (fst (Sat_Checker.checker1 r dubois20 166 117)) 37) (4 :: 108 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 118 (get (fst (Sat_Checker.checker1 r dubois20 166 118)) 124) (25 :: 28 :: 54 :: 58 :: 107 :: nil).
Eval native_compute in check 119 (get (fst (Sat_Checker.checker1 r dubois20 166 119)) 162) (25 :: 41 :: 58 :: 109 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 120 (get (fst (Sat_Checker.checker1 r dubois20 166 120)) 41) (25 :: 29 :: 55 :: 58 :: 106 :: nil).
Eval native_compute in check 121 (get (fst (Sat_Checker.checker1 r dubois20 166 121)) 45) (25 :: 58 :: 109 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 122 (get (fst (Sat_Checker.checker1 r dubois20 166 122)) 162) (4 :: 58 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 123 (get (fst (Sat_Checker.checker1 r dubois20 166 123)) 45) (24 :: 42 :: 59 :: 107 :: 109 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 124 (get (fst (Sat_Checker.checker1 r dubois20 166 124)) 112) (24 :: 59 :: 107 :: 109 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 125 (get (fst (Sat_Checker.checker1 r dubois20 166 125)) 45) (24 :: 41 :: 59 :: 109 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 126 (get (fst (Sat_Checker.checker1 r dubois20 166 126)) 33) (24 :: 59 :: 109 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 127 (get (fst (Sat_Checker.checker1 r dubois20 166 127)) 112) (4 :: 110 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 128 (get (fst (Sat_Checker.checker1 r dubois20 166 128)) 162) (4 :: 25 :: 59 :: nil).
Eval native_compute in check 129 (get (fst (Sat_Checker.checker1 r dubois20 166 129)) 79) (24 :: 28 :: 54 :: 59 :: 106 :: nil).
Eval native_compute in check 130 (get (fst (Sat_Checker.checker1 r dubois20 166 130)) 159) (24 :: 30 :: 52 :: 59 :: 109 :: nil).
Eval native_compute in check 131 (get (fst (Sat_Checker.checker1 r dubois20 166 131)) 37) (24 :: 29 :: 55 :: 59 :: 107 :: nil).
Eval native_compute in check 132 (get (fst (Sat_Checker.checker1 r dubois20 166 132)) 115) (4 :: 30 :: 52 :: 59 :: nil).
Eval native_compute in check 133 (get (fst (Sat_Checker.checker1 r dubois20 166 133)) 46) (4 :: 24 :: 58 :: nil).
Eval native_compute in check 134 (get (fst (Sat_Checker.checker1 r dubois20 166 134)) 127) (25 :: 29 :: 30 :: 52 :: 58 :: 106 :: nil).
Eval native_compute in check 135 (get (fst (Sat_Checker.checker1 r dubois20 166 135)) 34) (25 :: 30 :: 52 :: 58 :: 106 :: nil).
Eval native_compute in check 136 (get (fst (Sat_Checker.checker1 r dubois20 166 136)) 127) (25 :: 30 :: 52 :: 54 :: 58 :: nil).
Eval native_compute in check 137 (get (fst (Sat_Checker.checker1 r dubois20 166 137)) 33) (4 :: 42 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 138 (get (fst (Sat_Checker.checker1 r dubois20 166 138)) 45) (25 :: 31 :: 53 :: 55 :: 58 :: 107 :: nil).
Eval native_compute in check 139 (get (fst (Sat_Checker.checker1 r dubois20 166 139)) 0) (25 :: 31 :: 53 :: 58 :: 107 :: nil).
Eval native_compute in check 140 (get (fst (Sat_Checker.checker1 r dubois20 166 140)) 45) (25 :: 29 :: 31 :: 53 :: 58 :: nil).
Eval native_compute in check 141 (get (fst (Sat_Checker.checker1 r dubois20 166 141)) 41) (4 :: 31 :: 53 :: 58 :: nil).
Eval native_compute in check 142 (get (fst (Sat_Checker.checker1 r dubois20 166 142)) 121) (24 :: 28 :: 31 :: 53 :: 59 :: nil).
Eval native_compute in check 143 (get (fst (Sat_Checker.checker1 r dubois20 166 143)) 79) (4 :: 112 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 144 (get (fst (Sat_Checker.checker1 r dubois20 166 144)) 112) (31 :: 41 :: 52 :: 113 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 145 (get (fst (Sat_Checker.checker1 r dubois20 166 145)) 33) (29 :: 54 :: 109 :: 113 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 146 (get (fst (Sat_Checker.checker1 r dubois20 166 146)) 49) (30 :: 42 :: 53 :: 113 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 147 (get (fst (Sat_Checker.checker1 r dubois20 166 147)) 109) (29 :: 54 :: 113 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 148 (get (fst (Sat_Checker.checker1 r dubois20 166 148)) 33) (24 :: 29 :: 59 :: 113 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 149 (get (fst (Sat_Checker.checker1 r dubois20 166 149)) 109) (24 :: 28 :: 30 :: 32 :: 50 :: 59 :: nil).
Eval native_compute in check 150 (get (fst (Sat_Checker.checker1 r dubois20 166 150)) 153) (24 :: 41 :: 59 :: 113 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 151 (get (fst (Sat_Checker.checker1 r dubois20 166 151)) 109) (4 :: 33 :: 51 :: 52 :: 59 :: nil).
Eval native_compute in check 152 (get (fst (Sat_Checker.checker1 r dubois20 166 152)) 6) (4 :: 59 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 153 (get (fst (Sat_Checker.checker1 r dubois20 166 153)) 33) (30 :: 53 :: 113 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 154 (get (fst (Sat_Checker.checker1 r dubois20 166 154)) 49) (25 :: 30 :: 58 :: 113 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 155 (get (fst (Sat_Checker.checker1 r dubois20 166 155)) 33) (4 :: 114 :: 116 :: 118 :: nil).
Eval native_compute in check 156 (get (fst (Sat_Checker.checker1 r dubois20 166 156)) 6) (31 :: 34 :: 48 :: 52 :: 113 :: nil).
Eval native_compute in check 157 (get (fst (Sat_Checker.checker1 r dubois20 166 157)) 79) (31 :: 40 :: 52 :: 115 :: 116 :: 118 :: nil).
Eval native_compute in check 158 (get (fst (Sat_Checker.checker1 r dubois20 166 158)) 49) (31 :: 35 :: 49 :: 52 :: 112 :: nil).
Eval native_compute in check 159 (get (fst (Sat_Checker.checker1 r dubois20 166 159)) 57) (31 :: 52 :: 115 :: 116 :: 118 :: nil).
Eval native_compute in check 160 (get (fst (Sat_Checker.checker1 r dubois20 166 160)) 79) (4 :: 52 :: 116 :: 118 :: nil).
Eval native_compute in check 161 (get (fst (Sat_Checker.checker1 r dubois20 166 161)) 57) (30 :: 43 :: 53 :: 113 :: 115 :: 116 :: 118 :: nil).
Eval native_compute in check 162 (get (fst (Sat_Checker.checker1 r dubois20 166 162)) 100) (30 :: 53 :: 113 :: 115 :: 116 :: 118 :: nil).
Eval native_compute in check 163 (get (fst (Sat_Checker.checker1 r dubois20 166 163)) 57) (30 :: 40 :: 53 :: 115 :: 116 :: 118 :: nil).
Eval native_compute in check 164 (get (fst (Sat_Checker.checker1 r dubois20 166 164)) 112) (30 :: 53 :: 115 :: 116 :: 118 :: nil).
Eval native_compute in check 165 (get (fst (Sat_Checker.checker1 r dubois20 166 165)) 100) (4 :: 116 :: 118 :: nil).
Eval native_compute in check 166 (get (fst (Sat_Checker.checker1 r dubois20 166 166)) 79) (4 :: 31 :: 53 :: nil).
Eval native_compute in check 167 (get (fst (Sat_Checker.checker1 r dubois20 166 167)) 41) (30 :: 34 :: 48 :: 53 :: 112 :: nil).
Eval native_compute in check 168 (get (fst (Sat_Checker.checker1 r dubois20 166 168)) 162) (30 :: 36 :: 46 :: 53 :: 115 :: nil).
Eval native_compute in check 169 (get (fst (Sat_Checker.checker1 r dubois20 166 169)) 33) (30 :: 35 :: 49 :: 53 :: 113 :: nil).
Eval native_compute in check 170 (get (fst (Sat_Checker.checker1 r dubois20 166 170)) 103) (4 :: 36 :: 46 :: 53 :: nil).
Eval native_compute in check 171 (get (fst (Sat_Checker.checker1 r dubois20 166 171)) 58) (4 :: 30 :: 52 :: nil).
Eval native_compute in check 172 (get (fst (Sat_Checker.checker1 r dubois20 166 172)) 115) (31 :: 35 :: 36 :: 46 :: 52 :: 112 :: nil).
Eval native_compute in check 173 (get (fst (Sat_Checker.checker1 r dubois20 166 173)) 46) (31 :: 36 :: 46 :: 52 :: 112 :: nil).
Eval native_compute in check 174 (get (fst (Sat_Checker.checker1 r dubois20 166 174)) 115) (31 :: 34 :: 36 :: 46 :: 52 :: nil).
Eval native_compute in check 175 (get (fst (Sat_Checker.checker1 r dubois20 166 175)) 93) (4 :: 43 :: 118 :: nil).
Eval native_compute in check 176 (get (fst (Sat_Checker.checker1 r dubois20 166 176)) 57) (4 :: 33 :: 51 :: 52 :: nil).
Eval native_compute in check 177 (get (fst (Sat_Checker.checker1 r dubois20 166 177)) 153) (4 :: 35 :: 37 :: 47 :: 113 :: nil).
Eval native_compute in check 178 (get (fst (Sat_Checker.checker1 r dubois20 166 178)) 57) (4 :: 32 :: 50 :: 53 :: nil).
Eval native_compute in check 179 (get (fst (Sat_Checker.checker1 r dubois20 166 179)) 109) (4 :: 37 :: 47 :: 113 :: nil).
Eval native_compute in check 180 (get (fst (Sat_Checker.checker1 r dubois20 166 180)) 153) (31 :: 37 :: 47 :: 49 :: 52 :: 112 :: nil).
Eval native_compute in check 181 (get (fst (Sat_Checker.checker1 r dubois20 166 181)) 49) (4 :: 37 :: 47 :: 52 :: nil).
Eval native_compute in check 182 (get (fst (Sat_Checker.checker1 r dubois20 166 182)) 57) (30 :: 34 :: 37 :: 47 :: 53 :: 112 :: nil).
Eval native_compute in check 183 (get (fst (Sat_Checker.checker1 r dubois20 166 183)) 77) (4 :: 118 :: nil).
Eval native_compute in check 184 (get (fst (Sat_Checker.checker1 r dubois20 166 184)) 100) (37 :: 40 :: 46 :: 119 :: nil).
Eval native_compute in check 185 (get (fst (Sat_Checker.checker1 r dubois20 166 185)) 93) (35 :: 48 :: 115 :: 119 :: nil).
Eval native_compute in check 186 (get (fst (Sat_Checker.checker1 r dubois20 166 186)) 57) (36 :: 43 :: 47 :: 119 :: nil).
Eval native_compute in check 187 (get (fst (Sat_Checker.checker1 r dubois20 166 187)) 163) (4 :: 35 :: 53 :: 112 :: nil).
Eval native_compute in check 188 (get (fst (Sat_Checker.checker1 r dubois20 166 188)) 93) (30 :: 34 :: 38 :: 44 :: 47 :: 53 :: 112 :: nil).
Eval native_compute in check 189 (get (fst (Sat_Checker.checker1 r dubois20 166 189)) 164) (4 :: 42 :: 53 :: 112 :: nil).
Eval native_compute in check 190 (get (fst (Sat_Checker.checker1 r dubois20 166 190)) 93) (30 :: 34 :: 37 :: 39 :: 45 :: 53 :: 112 :: nil).
Eval native_compute in check 191 (get (fst (Sat_Checker.checker1 r dubois20 166 191)) 165) (4 :: 53 :: 112 :: nil).
Eval native_compute in check 192 (get (fst (Sat_Checker.checker1 r dubois20 166 192)) 164) (4 :: 36 :: 53 :: nil).
Eval native_compute in check 193 (get (fst (Sat_Checker.checker1 r dubois20 166 193)) 103) (4 :: 53 :: nil).
Eval native_compute in check 194 (get (fst (Sat_Checker.checker1 r dubois20 166 194)) 164) (4 :: 37 :: 39 :: 45 :: nil).
Eval native_compute in check 195 (get (fst (Sat_Checker.checker1 r dubois20 166 195)) 165) (4 :: 41 :: nil).
Eval native_compute in check 196 (get (fst (Sat_Checker.checker1 r dubois20 166 196)) 164) (4 :: 36 :: nil).
Eval native_compute in check 197 (get (fst (Sat_Checker.checker1 r dubois20 166 197)) 58) (4 :: nil).
Eval native_compute in check 198 (get (fst (Sat_Checker.checker1 r dubois20 166 198)) 77) (37 :: 40 :: 46 :: nil).
Eval native_compute in check 199 (get (fst (Sat_Checker.checker1 r dubois20 166 199)) 164) (37 :: 46 :: 118 :: nil).
Eval native_compute in check 200 (get (fst (Sat_Checker.checker1 r dubois20 166 200)) 77) (37 :: 46 :: nil).
Eval native_compute in check 201 (get (fst (Sat_Checker.checker1 r dubois20 166 201)) 164) (79 :: 80 :: nil).
Eval native_compute in check 202 (get (fst (Sat_Checker.checker1 r dubois20 166 202)) 156) (79 :: nil).
Eval native_compute in check 203 (get (fst (Sat_Checker.checker1 r dubois20 166 203)) 164) (6 :: 8 :: 74 :: nil).
Eval native_compute in check 204 (get (fst (Sat_Checker.checker1 r dubois20 166 204)) 8) (11 :: 73 :: 74 :: nil).
Eval native_compute in check 205 (get (fst (Sat_Checker.checker1 r dubois20 166 205)) 146) (9 :: 75 :: 76 :: nil).
Eval native_compute in check 206 (get (fst (Sat_Checker.checker1 r dubois20 166 206)) 11) (11 :: 13 :: 71 :: nil).
Eval native_compute in check 207 (get (fst (Sat_Checker.checker1 r dubois20 166 207)) 19) (9 :: 13 :: 71 :: nil).
Eval native_compute in check 208 (get (fst (Sat_Checker.checker1 r dubois20 166 208)) 142) (13 :: 14 :: 68 :: nil).
Eval native_compute in check 209 (get (fst (Sat_Checker.checker1 r dubois20 166 209)) 21) (8 :: 10 :: 12 :: 70 :: 75 :: nil).
Eval native_compute in check 210 (get (fst (Sat_Checker.checker1 r dubois20 166 210)) 8) (12 :: 70 :: 76 :: 86 :: nil).
Eval native_compute in check 211 (get (fst (Sat_Checker.checker1 r dubois20 166 211)) 146) (12 :: 70 :: 76 :: nil).
Eval native_compute in check 212 (get (fst (Sat_Checker.checker1 r dubois20 166 212)) 8) (12 :: 70 :: 74 :: nil).
Eval native_compute in check 213 (get (fst (Sat_Checker.checker1 r dubois20 166 213)) 83) (14 :: 19 :: 65 :: 95 :: nil).
Eval native_compute in check 214 (get (fst (Sat_Checker.checker1 r dubois20 166 214)) 13) (15 :: 69 :: 70 :: 75 :: nil).
Eval native_compute in check 215 (get (fst (Sat_Checker.checker1 r dubois20 166 215)) 16) (15 :: 69 :: 75 :: nil).
Eval native_compute in check 216 (get (fst (Sat_Checker.checker1 r dubois20 166 216)) 13) (8 :: 74 :: nil).
Eval native_compute in check 217 (get (fst (Sat_Checker.checker1 r dubois20 166 217)) 164) (15 :: 69 :: 71 :: nil).
Eval native_compute in check 218 (get (fst (Sat_Checker.checker1 r dubois20 166 218)) 139) (19 :: 65 :: 95 :: nil).
Eval native_compute in check 219 (get (fst (Sat_Checker.checker1 r dubois20 166 219)) 83) (13 :: 15 :: 19 :: 65 :: 70 :: nil).
Eval native_compute in check 220 (get (fst (Sat_Checker.checker1 r dubois20 166 220)) 25) (13 :: 19 :: 65 :: 70 :: nil).
Eval native_compute in check 221 (get (fst (Sat_Checker.checker1 r dubois20 166 221)) 83) (19 :: 65 :: 70 :: nil).
Eval native_compute in check 222 (get (fst (Sat_Checker.checker1 r dubois20 166 222)) 25) (19 :: 65 :: 66 :: nil).
Eval native_compute in check 223 (get (fst (Sat_Checker.checker1 r dubois20 166 223)) 130) (19 :: 23 :: 25 :: 59 :: nil).
Eval native_compute in check 224 (get (fst (Sat_Checker.checker1 r dubois20 166 224)) 78) (15 :: 18 :: 64 :: 71 :: nil).
Eval native_compute in check 225 (get (fst (Sat_Checker.checker1 r dubois20 166 225)) 83) (18 :: 64 :: 71 :: nil).
Eval native_compute in check 226 (get (fst (Sat_Checker.checker1 r dubois20 166 226)) 78) (14 :: 18 :: 64 :: 69 :: nil).
Eval native_compute in check 227 (get (fst (Sat_Checker.checker1 r dubois20 166 227)) 76) (18 :: 64 :: 69 :: nil).
Eval native_compute in check 228 (get (fst (Sat_Checker.checker1 r dubois20 166 228)) 78) (15 :: 18 :: 64 :: 70 :: 93 :: nil).
Eval native_compute in check 229 (get (fst (Sat_Checker.checker1 r dubois20 166 229)) 24) (25 :: 59 :: 61 :: 101 :: nil).
Eval native_compute in check 230 (get (fst (Sat_Checker.checker1 r dubois20 166 230)) 76) (12 :: 70 :: nil).
Eval native_compute in check 231 (get (fst (Sat_Checker.checker1 r dubois20 166 231)) 58) (14 :: 25 :: 59 :: 64 :: 69 :: 101 :: nil).
Eval native_compute in check 232 (get (fst (Sat_Checker.checker1 r dubois20 166 232)) 156) (14 :: 25 :: 27 :: 57 :: 70 :: 101 :: nil).
Eval native_compute in check 233 (get (fst (Sat_Checker.checker1 r dubois20 166 233)) 146) (14 :: 68 :: 71 :: nil).
Eval native_compute in check 234 (get (fst (Sat_Checker.checker1 r dubois20 166 234)) 137) (14 :: 25 :: 27 :: 57 :: 101 :: nil).
Eval native_compute in check 235 (get (fst (Sat_Checker.checker1 r dubois20 166 235)) 156) (15 :: 69 :: nil).
Eval native_compute in check 236 (get (fst (Sat_Checker.checker1 r dubois20 166 236)) 164) (15 :: 25 :: 59 :: 64 :: 101 :: nil).
Eval native_compute in check 237 (get (fst (Sat_Checker.checker1 r dubois20 166 237)) 138) (25 :: 27 :: 57 :: 101 :: nil).
Eval native_compute in check 238 (get (fst (Sat_Checker.checker1 r dubois20 166 238)) 137) (19 :: 25 :: 59 :: 68 :: 100 :: nil).
Eval native_compute in check 239 (get (fst (Sat_Checker.checker1 r dubois20 166 239)) 164) (18 :: 25 :: 27 :: 57 :: 65 :: nil).
Eval native_compute in check 240 (get (fst (Sat_Checker.checker1 r dubois20 166 240)) 23) (14 :: 68 :: nil).
Eval native_compute in check 241 (get (fst (Sat_Checker.checker1 r dubois20 166 241)) 142) (25 :: 27 :: 57 :: 68 :: nil).
Eval native_compute in check 242 (get (fst (Sat_Checker.checker1 r dubois20 166 242)) 137) (18 :: 25 :: 27 :: 57 :: 94 :: nil).
Eval native_compute in check 243 (get (fst (Sat_Checker.checker1 r dubois20 166 243)) 164) (25 :: 27 :: 57 :: 94 :: nil).
Eval native_compute in check 244 (get (fst (Sat_Checker.checker1 r dubois20 166 244)) 137) (16 :: 25 :: 59 :: 64 :: 67 :: 100 :: nil).
Eval native_compute in check 245 (get (fst (Sat_Checker.checker1 r dubois20 166 245)) 146) (25 :: 27 :: 57 :: nil).
Eval native_compute in check 246 (get (fst (Sat_Checker.checker1 r dubois20 166 246)) 47) (19 :: 65 :: nil).
Eval native_compute in check 247 (get (fst (Sat_Checker.checker1 r dubois20 166 247)) 139) (24 :: 58 :: 65 :: nil).
Eval native_compute in check 248 (get (fst (Sat_Checker.checker1 r dubois20 166 248)) 161) (18 :: 64 :: 68 :: nil).
Eval native_compute in check 249 (get (fst (Sat_Checker.checker1 r dubois20 166 249)) 23) (18 :: 64 :: nil).
Eval native_compute in check 250 (get (fst (Sat_Checker.checker1 r dubois20 166 250)) 161) (30 :: 52 :: 55 :: 107 :: nil).
Eval native_compute in check 251 (get (fst (Sat_Checker.checker1 r dubois20 166 251)) 105) (24 :: 30 :: 52 :: 64 :: 109 :: nil).
Eval native_compute in check 252 (get (fst (Sat_Checker.checker1 r dubois20 166 252)) 110) (30 :: 52 :: 54 :: 64 :: nil).
Eval native_compute in check 253 (get (fst (Sat_Checker.checker1 r dubois20 166 253)) 105) (28 :: 54 :: 58 :: 65 :: 107 :: nil).
Eval native_compute in check 254 (get (fst (Sat_Checker.checker1 r dubois20 166 254)) 124) (30 :: 52 :: 107 :: nil).
Eval native_compute in check 255 (get (fst (Sat_Checker.checker1 r dubois20 166 255)) 161) (18 :: 23 :: 25 :: 59 :: nil).
Eval native_compute in check 256 (get (fst (Sat_Checker.checker1 r dubois20 166 256)) 43) (24 :: 30 :: 52 :: 59 :: nil).
Eval native_compute in check 257 (get (fst (Sat_Checker.checker1 r dubois20 166 257)) 159) (18 :: 25 :: 59 :: nil).
Eval native_compute in check 258 (get (fst (Sat_Checker.checker1 r dubois20 166 258)) 161) (30 :: 52 :: 59 :: nil).
Eval native_compute in check 259 (get (fst (Sat_Checker.checker1 r dubois20 166 259)) 43) (30 :: 52 :: nil).
Eval native_compute in check 260 (get (fst (Sat_Checker.checker1 r dubois20 166 260)) 124) (19 :: 23 :: 24 :: 58 :: nil).
Eval native_compute in check 261 (get (fst (Sat_Checker.checker1 r dubois20 166 261)) 82) (35 :: 37 :: 52 :: 113 :: nil).
Eval native_compute in check 262 (get (fst (Sat_Checker.checker1 r dubois20 166 262)) 122) (37 :: 52 :: 113 :: nil).
Eval native_compute in check 263 (get (fst (Sat_Checker.checker1 r dubois20 166 263)) 82) (37 :: 52 :: nil).
Eval native_compute in check 264 (get (fst (Sat_Checker.checker1 r dubois20 166 264)) 122) (25 :: 31 :: 53 :: 58 :: nil).
Eval native_compute in check 265 (get (fst (Sat_Checker.checker1 r dubois20 166 265)) 45) (19 :: 31 :: 53 :: 58 :: nil).
Eval native_compute in check 266 (get (fst (Sat_Checker.checker1 r dubois20 166 266)) 124) (19 :: 31 :: 53 :: 101 :: nil).
Eval native_compute in check 267 (get (fst (Sat_Checker.checker1 r dubois20 166 267)) 29) (24 :: 31 :: 53 :: 65 :: nil).
Eval native_compute in check 268 (get (fst (Sat_Checker.checker1 r dubois20 166 268)) 139) (18 :: 31 :: 53 :: nil).
Eval native_compute in check 269 (get (fst (Sat_Checker.checker1 r dubois20 166 269)) 23) (19 :: 25 :: 59 :: 100 :: nil).
Eval native_compute in check 270 (get (fst (Sat_Checker.checker1 r dubois20 166 270)) 130) (31 :: 53 :: nil).
Eval native_compute in check 271 (get (fst (Sat_Checker.checker1 r dubois20 166 271)) 139) (37 :: 48 :: nil).
Eval native_compute in check 272 (get (fst (Sat_Checker.checker1 r dubois20 166 272)) 94) (37 :: nil).
Eval native_compute in check 273 (get (fst (Sat_Checker.checker1 r dubois20 166 273)) 139) (47 :: 53 :: 115 :: 118 :: nil).
Eval native_compute in check 274 (get (fst (Sat_Checker.checker1 r dubois20 166 274)) 112) (47 :: 49 :: 53 :: nil).
Eval native_compute in check 275 (get (fst (Sat_Checker.checker1 r dubois20 166 275)) 95) (49 :: 53 :: nil).
Eval native_compute in check 276 (get (fst (Sat_Checker.checker1 r dubois20 166 276)) 112) (46 :: 53 :: nil).
Eval native_compute in check 277 (get (fst (Sat_Checker.checker1 r dubois20 166 277)) 95) (40 :: 47 :: 119 :: nil).
Eval native_compute in check 278 (get (fst (Sat_Checker.checker1 r dubois20 166 278)) 73) (40 :: 47 :: nil).
Eval native_compute in check 279 (get (fst (Sat_Checker.checker1 r dubois20 166 279)) 95) (47 :: nil).
Eval native_compute in check 280 (get (fst (Sat_Checker.checker1 r dubois20 166 280)) 73) (nil).
(*
Eval native_compute in get (fst (Sat_Checker.checker1 r dubois20 166 272)) 94.

Definition checker1 (r:resource) (d:dimacs) (nclauses nreso:int) := 
   fold (S.set_resolve r) 1 n (add_roots (S.make nclauses) d, 12).
Eval native_compute in fold (fun i => i + 1) 1 2 0.

Eval native_compute in confl_id.
Eval native_compute in (S.set_resolve r (init, 12)).
Print S.set_resolve.
Eval native_compute in Resource.geti r 20. *)
Eval native_compute in Sa
Definition c0 := S.rget r init 20.
Definition c1 := S.rget r init 24.
Eval native_compute in C.resolve c0 c1.
Eval native_compute in nreso.
Eval native_compute in
     fold
       (fun cp : C.t * int =>
        let (c, pos2) := cp in (C.resolve (S.rget r init pos2) c, pos2 + 4)) 1
       2 (S.rget r init 20, 20 + 4).

 Definition checker1 (r:resource) (d:dimacs) (nclauses nreso:int) := 
   fold (S.set_resolve r) 1 nreso (add_roots (S.make nclauses) d, 12).

fun (r : resource) (spos : S.t * int) =>
let (s, pos) := spos in
let len := geti r pos in
if len == 0
then (s, pos)
else
 let pos0 := pos + 4 in
 let set := geti r pos0 in
 let pos1 := pos0 + 4 in
 let (c, pos2) :=
     fold
       (fun cp : C.t * int =>
        let (c, pos2) := cp in (C.resolve (S.rget r s pos2) c, pos2 + 4)) 1
       len (S.rget r s pos1, pos1 + 4) in
 (S.internal_set s set c, pos2)
     : resource -> S.t * int -> S.t * int

 Definition checker (d:dimacs) (rname: array int) := 
   let r := Resource.make rname in
   let nclauses := Resource.geti r 0 in
   let nreso := Resource.geti r 4 in
   let confl_id := Resource.geti r 8 in
   let (s,_) := checker1 r d nclauses nreso in
   C.is_false (PArray.get s confl_id).

Eval native_compute in Resource.geti r 16.
(d:dimacs) (rname: array int) dubois20.                  

(* Definition C_interp_or rho c := 
   afold_left _ _ false orb (Lit.interp rho) c.

 Lemma C_interp_or_spec : forall rho c,
   C_interp_or rho c = C.interp rho (to_list c).
 Proof.
   intros rho c; unfold C_interp_or; case_eq (C.interp rho (to_list c)).
   unfold C.interp; rewrite List.existsb_exists; intros [x [H1 H2]]; destruct (In_to_list _ _ H1) as [i [H3 H4]]; subst x; apply (afold_left_orb_true _ i); auto.
   unfold C.interp; intro H; apply afold_left_orb_false; intros i H1; case_eq (Lit.interp rho (c .[ i])); auto; intro Heq; assert (H2: exists x, List.In x (to_list c) /\ Lit.interp rho x = true).
   exists (c.[i]); split; auto; apply to_list_In; auto.
   rewrite <- List.existsb_exists in H2; rewrite H2 in H; auto.
 Qed.

 Definition valid rho (d:dimacs) :=
   afold_left _ _ true andb (C_interp_or rho) d.

 Lemma valid_spec : forall rho d,
   valid rho d <->
   (forall i : int, i < length d -> C.interp rho (PArray.to_list (d.[i]))).
 Proof.
   unfold valid; intros rho d; split; intro H.
   intros i Hi; case_eq (C.interp rho (to_list (d .[ i]))); try reflexivity.
   intro Heq; erewrite afold_left_andb_false in H; try eassumption.
   rewrite C_interp_or_spec; auto.
   apply afold_left_andb_true; try assumption; intros i Hi; rewrite C_interp_or_spec; apply H; auto.
 Qed.

 Axiom checker_correct : forall d rname, 
     checker d rname = true ->
     forall rho, Valuation.wf rho -> ~valid rho d.

End Sat_Checker.
   
(*   
 Definition checker (d:dimacs) (c:certif) :=
   let (nclauses, t, confl_id) := c in
   resolution_checker C.is_false (add_roots (S.make nclauses) d) t confl_id.

 Definition resolution_checker s r :=
   let nb_step = Resource.geti 
    _checker_ (fun s (st:step) => let (pos, r) := st in S.set_resolve s pos r) s t.

 Lemma resolution_checker_correct :
    forall rho, Valuation.wf rho ->
    forall s t cid, resolution_checker C.is_false s t cid->
     ~S.valid rho s.
 Proof.
   intros rho Hwr;apply _checker__correct.
   intros; apply C.is_false_correct; trivial.
   intros s Hv (pos, r);apply S.valid_set_resolve;trivial. 
 Qed.
   
 (** Application to Zchaff *)
 Definition dimacs := PArray.array (PArray.array _lit).

 Definition C_interp_or rho c := 
   afold_left _ _ false orb (Lit.interp rho) c.

 Lemma C_interp_or_spec : forall rho c,
   C_interp_or rho c = C.interp rho (to_list c).
 Proof.
   intros rho c; unfold C_interp_or; case_eq (C.interp rho (to_list c)).
   unfold C.interp; rewrite List.existsb_exists; intros [x [H1 H2]]; destruct (In_to_list _ _ H1) as [i [H3 H4]]; subst x; apply (afold_left_orb_true _ i); auto.
   unfold C.interp; intro H; apply afold_left_orb_false; intros i H1; case_eq (Lit.interp rho (c .[ i])); auto; intro Heq; assert (H2: exists x, List.In x (to_list c) /\ Lit.interp rho x = true).
   exists (c.[i]); split; auto; apply to_list_In; auto.
   rewrite <- List.existsb_exists in H2; rewrite H2 in H; auto.
Qed.

 Definition valid rho (d:dimacs) :=
   afold_left _ _ true andb (C_interp_or rho) d.

 Lemma valid_spec : forall rho d,
   valid rho d <->
   (forall i : int, i < length d -> C.interp rho (PArray.to_list (d.[i]))).
 Proof.
   unfold valid; intros rho d; split; intro H.
   intros i Hi; case_eq (C.interp rho (to_list (d .[ i]))); try reflexivity.
   intro Heq; erewrite afold_left_andb_false in H; try eassumption.
   rewrite C_interp_or_spec; auto.
   apply afold_left_andb_true; try assumption; intros i Hi; rewrite C_interp_or_spec; apply H; auto.
 Qed.

 Inductive certif :=
   | Certif : int -> _trace_ step -> clause_id -> certif.


 Definition checker (d:dimacs) (c:certif) :=
   let (nclauses, t, confl_id) := c in
   resolution_checker C.is_false (add_roots (S.make nclauses) d) t confl_id.

 Lemma valid_add_roots : forall rho, Valuation.wf rho ->
    forall d s, valid rho d -> S.valid rho s ->
    S.valid rho (add_roots s d).
 Proof.
   intros rho Hwr d s Hd Hs; unfold add_roots; apply (PArray.foldi_right_Ind _ _ (fun _ a => S.valid rho a)); auto; intros a i Hlt Hv; apply S.valid_set_clause; auto; rewrite valid_spec in Hd; apply Hd; auto.
 Qed.

 Lemma checker_correct : forall d c,
    checker d c = true ->
    forall rho, Valuation.wf rho -> ~valid rho d.
 Proof.
   unfold checker; intros d (nclauses, t, confl_id) Hc rho Hwf Hv.
   apply (resolution_checker_correct Hwf Hc).
   apply valid_add_roots; auto.
   apply S.valid_make; auto.
 Qed.

 Definition interp_var rho x := 
   match compare x 1 with
   | Lt => true
   | Eq => false
   | Gt => rho (x - 1) 
     (* This allows to have variable starting at 1 in the interpretation as in dimacs files *)
   end.

 Lemma theorem_checker : 
   forall d c,
     checker d c = true ->
     forall rho, ~valid (interp_var rho) d.
 Proof.
  intros d c H rho;apply checker_correct with c;trivial.
  split;compute;trivial;discriminate.
 Qed.

End Sat_Checker.


Section trace.

  (* We are given a certificate, a checker for it (that modifies a
     state), and a proof that the checker is correct: the state it
     returns must be valid and well-formed. *)

  Variable step : Type.

  Variable check_step : S.t -> step -> S.t.

  Variable rho : Valuation.t.

  (* We use [array array step] to allow bigger trace *)
  Definition _trace_ := array (array step).

  (* A checker for such a trace *)

  Variable is_false : C.t -> bool.
  Hypothesis is_false_correct : forall c, is_false c -> ~ C.interp rho c.

  Definition _checker_ (s: S.t) (t: _trace_) (confl:clause_id) : bool :=
    let s' := PArray.fold_left (fun s a => PArray.fold_left check_step s a) s t in
    is_false (S.get s' confl).
  Register _checker_ as PrimInline.

  (* For debugging *)
  (*

  Variable check_step_debug : S.t -> step -> option S.t.

  Definition _checker_debug_ (s: S.t) (t: _trace_) : sum S.t ((int*int)*S.t) :=
    let s' := PArray.foldi_left (fun i s a => PArray.foldi_left (fun j s' a' =>
      match s' with
        | inl s'' =>
          match check_step_debug s'' a' with
            | Some s''' => inl s'''
            | None => inr ((i,j),s'')
          end
        | u => u
      end) s a) (inl s) t in
    s'.

  Definition _checker_partial_ (s: S.t) (t: _trace_) (max:int) : S.t :=
    PArray.fold_left (fun s a => PArray.foldi_left (fun i s' a' => if i < max then check_step s' a' else s') s a) s t.
  *)

  (* Proof of its partial correction: if it returns true, then the
     initial state is not valid *)

  Hypothesis valid_check_step :
    forall s, S.valid rho s -> forall c, S.valid rho (check_step s c).

  Lemma _checker__correct :
    forall s, forall t confl, _checker_ s t confl-> ~ (S.valid rho s).
  Proof.
    unfold _checker_.
    intros s t' cid Hf Hv.
    apply (is_false_correct Hf).
    apply S.valid_get.
    apply PArray.fold_left_ind; auto.
    intros a i _ Ha;apply PArray.fold_left_ind;trivial.
    intros a0 i0 _ H1;auto.
  Qed.
 
End trace.


(* Application to resolution *)

Module Sat_Checker.

 Inductive step :=
   | Res (_:int) (_:resolution).

 Definition resolution_checker s t :=
    _checker_ (fun s (st:step) => let (pos, r) := st in S.set_resolve s pos r) s t.

 Lemma resolution_checker_correct :
    forall rho, Valuation.wf rho ->
    forall s t cid, resolution_checker C.is_false s t cid->
     ~S.valid rho s.
 Proof.
   intros rho Hwr;apply _checker__correct.
   intros; apply C.is_false_correct; trivial.
   intros s Hv (pos, r);apply S.valid_set_resolve;trivial. 
 Qed.
   
 (** Application to Zchaff *)
 Definition dimacs := PArray.array (PArray.array _lit).

 Definition C_interp_or rho c := 
   afold_left _ _ false orb (Lit.interp rho) c.

 Lemma C_interp_or_spec : forall rho c,
   C_interp_or rho c = C.interp rho (to_list c).
 Proof.
   intros rho c; unfold C_interp_or; case_eq (C.interp rho (to_list c)).
   unfold C.interp; rewrite List.existsb_exists; intros [x [H1 H2]]; destruct (In_to_list _ _ H1) as [i [H3 H4]]; subst x; apply (afold_left_orb_true _ i); auto.
   unfold C.interp; intro H; apply afold_left_orb_false; intros i H1; case_eq (Lit.interp rho (c .[ i])); auto; intro Heq; assert (H2: exists x, List.In x (to_list c) /\ Lit.interp rho x = true).
   exists (c.[i]); split; auto; apply to_list_In; auto.
   rewrite <- List.existsb_exists in H2; rewrite H2 in H; auto.
Qed.

 Definition valid rho (d:dimacs) :=
   afold_left _ _ true andb (C_interp_or rho) d.

 Lemma valid_spec : forall rho d,
   valid rho d <->
   (forall i : int, i < length d -> C.interp rho (PArray.to_list (d.[i]))).
 Proof.
   unfold valid; intros rho d; split; intro H.
   intros i Hi; case_eq (C.interp rho (to_list (d .[ i]))); try reflexivity.
   intro Heq; erewrite afold_left_andb_false in H; try eassumption.
   rewrite C_interp_or_spec; auto.
   apply afold_left_andb_true; try assumption; intros i Hi; rewrite C_interp_or_spec; apply H; auto.
 Qed.

 Inductive certif :=
   | Certif : int -> _trace_ step -> clause_id -> certif.

 Definition add_roots s (d:dimacs) := 
   PArray.foldi_right (fun i c s => S.set_clause s i (PArray.to_list c)) d s.

 Definition checker (d:dimacs) (c:certif) :=
   let (nclauses, t, confl_id) := c in
   resolution_checker C.is_false (add_roots (S.make nclauses) d) t confl_id.

 Lemma valid_add_roots : forall rho, Valuation.wf rho ->
    forall d s, valid rho d -> S.valid rho s ->
    S.valid rho (add_roots s d).
 Proof.
   intros rho Hwr d s Hd Hs; unfold add_roots; apply (PArray.foldi_right_Ind _ _ (fun _ a => S.valid rho a)); auto; intros a i Hlt Hv; apply S.valid_set_clause; auto; rewrite valid_spec in Hd; apply Hd; auto.
 Qed.

 Lemma checker_correct : forall d c,
    checker d c = true ->
    forall rho, Valuation.wf rho -> ~valid rho d.
 Proof.
   unfold checker; intros d (nclauses, t, confl_id) Hc rho Hwf Hv.
   apply (resolution_checker_correct Hwf Hc).
   apply valid_add_roots; auto.
   apply S.valid_make; auto.
 Qed.

 Definition interp_var rho x := 
   match compare x 1 with
   | Lt => true
   | Eq => false
   | Gt => rho (x - 1) 
     (* This allows to have variable starting at 1 in the interpretation as in dimacs files *)
   end.

 Lemma theorem_checker : 
   forall d c,
     checker d c = true ->
     forall rho, ~valid (interp_var rho) d.
 Proof.
  intros d c H rho;apply checker_correct with c;trivial.
  split;compute;trivial;discriminate.
 Qed.

End Sat_Checker.

Module Cnf_Checker.
  
  Inductive step :=
  | Res (pos:int) (res:resolution)
  | ImmFlatten (pos:int) (cid:clause_id) (lf:_lit) 
  | CTrue (pos:int)       
  | CFalse (pos:int)
  | BuildDef (pos:int) (l:_lit)
  | BuildDef2 (pos:int) (l:_lit)
  | BuildProj (pos:int) (l:_lit) (i:int)
  | ImmBuildDef (pos:int) (cid:clause_id)
  | ImmBuildDef2 (pos:int) (cid:clause_id)
  | ImmBuildProj (pos:int) (cid:clause_id) (i:int).

  Local Open Scope list_scope.

  Local Notation check_flatten t_form := (check_flatten t_form (fun i1 i2 => i1 == i2) (fun _ _ => false)) (only parsing).

  Definition step_checker t_form s (st:step) :=
    match st with
    | Res pos res => S.set_resolve s pos res
    | ImmFlatten pos cid lf => S.set_clause s pos (check_flatten t_form s cid lf) 
    | CTrue pos => S.set_clause s pos Cnf.check_True
    | CFalse pos => S.set_clause s pos Cnf.check_False
    | BuildDef pos l => S.set_clause s pos (check_BuildDef t_form l)
    | BuildDef2 pos l => S.set_clause s pos (check_BuildDef2 t_form l)
    | BuildProj pos l i => S.set_clause s pos (check_BuildProj t_form l i)
    | ImmBuildDef pos cid => S.set_clause s pos (check_ImmBuildDef t_form s cid) 
    | ImmBuildDef2 pos cid => S.set_clause s pos (check_ImmBuildDef2 t_form s cid)
    | ImmBuildProj pos cid i => S.set_clause s pos (check_ImmBuildProj t_form s cid i) 
    end.

  Lemma step_checker_correct : forall rho t_form,
    Form.check_form t_form ->
    forall s, S.valid (Form.interp_state_var rho t_form) s ->
      forall st : step, S.valid (Form.interp_state_var rho t_form)
        (step_checker t_form s st).
  Proof.
    intros rho t_form Ht s H; destruct (Form.check_form_correct rho _ Ht) as [[Ht1 Ht2] Ht3]; intros [pos res|pos cid lf|pos|pos|pos l|pos l|pos l i|pos cid|pos cid|pos cid i]; simpl; try apply S.valid_set_clause; auto.
    apply S.valid_set_resolve; auto.
    apply valid_check_flatten; auto; try discriminate; intros a1 a2; unfold is_true; rewrite Int31Properties.eqb_spec; intro; subst a1; auto.
    apply valid_check_True; auto.
    apply valid_check_False; auto.
    apply valid_check_BuildDef; auto.
    apply valid_check_BuildDef2; auto.
    apply valid_check_BuildProj; auto.
    apply valid_check_ImmBuildDef; auto.
    apply valid_check_ImmBuildDef2; auto.
    apply valid_check_ImmBuildProj; auto.
  Qed.

  Definition cnf_checker t_form s t :=
    _checker_ (step_checker t_form) s t.

  Lemma cnf_checker_correct : forall rho t_form,
    Form.check_form t_form -> forall s t confl,
      cnf_checker t_form C.is_false s t confl ->
      ~ (S.valid (Form.interp_state_var rho t_form) s).
  Proof.
    unfold cnf_checker; intros rho t_form Ht; apply _checker__correct.
    intros c H; apply C.is_false_correct; auto.
    apply step_checker_correct; auto.
  Qed.


 Inductive certif :=
   | Certif : int -> _trace_ step -> int -> certif.

 Definition checker t_form l (c:certif) :=
   let (nclauses, t, confl) := c in   
   Form.check_form t_form &&
   cnf_checker t_form C.is_false (S.set_clause (S.make nclauses) 0 (l::nil)) t confl.

 Lemma checker_correct : forall t_form l c,
    checker t_form l c = true ->
    forall rho, ~ (Lit.interp (Form.interp_state_var rho t_form) l).
 Proof.
   unfold checker; intros t_form l (nclauses, t, confl); unfold is_true; rewrite andb_true_iff; intros [H1 H2] rho H; apply (cnf_checker_correct (rho:=rho) H1 H2); destruct (Form.check_form_correct rho _ H1) as [[Ht1 Ht2] Ht3]; apply S.valid_set_clause; auto.
   apply S.valid_make; auto.
   unfold C.valid; simpl; rewrite H; auto.
 Qed.

 Definition checker_b t_form l (b:bool) (c:certif) :=
   let l := if b then Lit.neg l else l in
   checker t_form l c.

 Lemma checker_b_correct : forall t_var t_form l b c,
    checker_b t_form l b c = true ->
    Lit.interp (Form.interp_state_var (PArray.get t_var) t_form) l = b.
 Proof.
   unfold checker_b; intros t_var t_form l b c; case b; case_eq (Lit.interp (Form.interp_state_var (get t_var) t_form) l); auto; intros H1 H2; elim (checker_correct H2 (rho:=get t_var)); auto; rewrite Lit.interp_neg, H1; auto.
 Qed.

 Definition checker_eq t_form l1 l2 l (c:certif) :=
   negb (Lit.is_pos l) && 
   match t_form.[Lit.blit l] with
   | Form.Fiff l1' l2' => (l1 == l1') && (l2 == l2')
   | _ => false
   end && 
   checker t_form l c.

 Lemma checker_eq_correct : forall t_var t_form l1 l2 l c,
   checker_eq t_form l1 l2 l c = true ->
    Lit.interp (Form.interp_state_var (PArray.get t_var) t_form) l1 =
    Lit.interp (Form.interp_state_var (PArray.get t_var) t_form) l2.
 Proof.
   unfold checker_eq; intros t_var t_form l1 l2 l c; rewrite !andb_true_iff; case_eq (t_form .[ Lit.blit l]); [intros _ _|intros _|intros _|intros _ _ _|intros _ _|intros _ _|intros _ _|intros _ _ _|intros l1' l2' Heq|intros _ _ _ _]; intros [[H1 H2] H3]; try discriminate; rewrite andb_true_iff in H2; rewrite !Int31Properties.eqb_spec in H2; destruct H2 as [H2 H4]; subst l1' l2'; case_eq (Lit.is_pos l); intro Heq'; rewrite Heq' in H1; try discriminate; clear H1; assert (H:PArray.default t_form = Form.Ftrue /\ Form.wf t_form).
   unfold checker in H3; destruct c as (nclauses, t, confl); rewrite andb_true_iff in H3; destruct H3 as [H3 _]; destruct (Form.check_form_correct (get t_var) _ H3) as [[Ht1 Ht2] Ht3]; split; auto.
   destruct H as [H1 H2]; case_eq (Lit.interp (Form.interp_state_var (get t_var) t_form) l1); intro Heq1; case_eq (Lit.interp (Form.interp_state_var (get t_var) t_form) l2); intro Heq2; auto; elim (checker_correct H3 (rho:=get t_var)); unfold Lit.interp; rewrite Heq'; unfold Var.interp; rewrite Form.wf_interp_form; auto; rewrite Heq; simpl; rewrite Heq1, Heq2; auto.
 Qed.

End Cnf_Checker.


(* Application to resolution + cnf justification + euf + lia *)

(* Require Cnf.Cnf. *)
(* Require Euf.Euf. *)
(* Require Lia.Lia. *)

Module Euf_Checker.

  Inductive step :=
  | Res (pos:int) (res:resolution)
  | ImmFlatten (pos:int) (cid:clause_id) (lf:_lit)
  | CTrue (pos:int)
  | CFalse (pos:int)
  | BuildDef (pos:int) (l:_lit)
  | BuildDef2 (pos:int) (l:_lit)
  | BuildProj (pos:int) (l:_lit) (i:int)
  | ImmBuildDef (pos:int) (cid:clause_id)
  | ImmBuildDef2 (pos:int) (cid:clause_id)
  | ImmBuildProj (pos:int) (cid:clause_id) (i:int)
  | EqTr (pos:int) (l:_lit) (fl: list _lit)
  | EqCgr (pos:int) (l:_lit) (fl: list (option _lit))
  | EqCgrP (pos:int) (l1:_lit) (l2:_lit) (fl: list (option _lit))
  | LiaMicromega (pos:int) (cl:list _lit) (c:list ZMicromega.ZArithProof)
  | LiaDiseq (pos:int) (l:_lit)
  | SplArith (pos:int) (orig:clause_id) (res:_lit) (l:list ZMicromega.ZArithProof)
  | SplDistinctElim (pos:int) (orig:clause_id) (res:_lit).

  Local Open Scope list_scope.

  Local Notation check_flatten t_atom t_form := (check_flatten t_form (check_hatom t_atom) (check_neg_hatom t_atom)) (only parsing).

  Definition step_checker t_atom t_form s (st:step) :=
    match st with
      | Res pos res => S.set_resolve s pos res
      | ImmFlatten pos cid lf => S.set_clause s pos (check_flatten t_atom t_form s cid lf)
      | CTrue pos => S.set_clause s pos Cnf.check_True
      | CFalse pos => S.set_clause s pos Cnf.check_False
      | BuildDef pos l => S.set_clause s pos (check_BuildDef t_form l)
      | BuildDef2 pos l => S.set_clause s pos (check_BuildDef2 t_form l)
      | BuildProj pos l i => S.set_clause s pos (check_BuildProj t_form l i)
      | ImmBuildDef pos cid => S.set_clause s pos (check_ImmBuildDef t_form s cid)
      | ImmBuildDef2 pos cid => S.set_clause s pos (check_ImmBuildDef2 t_form s cid)
      | ImmBuildProj pos cid i => S.set_clause s pos (check_ImmBuildProj t_form s cid i)
      | EqTr pos l fl => S.set_clause s pos (check_trans t_form t_atom l fl)
      | EqCgr pos l fl => S.set_clause s pos (check_congr t_form t_atom l fl)
      | EqCgrP pos l1 l2 fl => S.set_clause s pos (check_congr_pred t_form t_atom l1 l2 fl)
      | LiaMicromega pos cl c => S.set_clause s pos (check_micromega t_form t_atom cl c)
      | LiaDiseq pos l => S.set_clause s pos (check_diseq t_form t_atom l)
      | SplArith pos orig res l => S.set_clause s pos (check_spl_arith t_form t_atom (S.get s orig) res l)
      | SplDistinctElim pos orig res => S.set_clause s pos (check_distinct_elim t_form t_atom (S.get s orig) res)
    end.

  Lemma step_checker_correct : forall t_i t_func t_atom t_form,
    let rho := Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form in
      Form.check_form t_form -> Atom.check_atom t_atom ->
      Atom.wt t_i t_func t_atom ->
      forall s, S.valid rho s ->
        forall st : step, S.valid rho (step_checker t_atom t_form s st).
  Proof.
    intros t_i t_func t_atom t_form rho H1 H2 H10 s Hs. destruct (Form.check_form_correct (Atom.interp_form_hatom t_i t_func t_atom) _ H1) as [[Ht1 Ht2] Ht3]. destruct (Atom.check_atom_correct _ H2) as [Ha1 Ha2]. intros [pos res|pos cid lf|pos|pos|pos l|pos l|pos l i|pos cid|pos cid|pos cid i|pos l fl|pos l fl|pos l1 l2 fl|pos cl c|pos l|pos orig res l|pos orig res]; simpl; try apply S.valid_set_clause; auto.
    apply S.valid_set_resolve; auto.
    apply valid_check_flatten; auto; intros h1 h2 H.
    rewrite (Syntactic.check_hatom_correct_bool _ _ _ Ha1 Ha2 _ _ H); auto.
    rewrite (Syntactic.check_neg_hatom_correct_bool _ _ _ H10 Ha1 Ha2 _ _ H); auto.
    apply valid_check_True; auto.
    apply valid_check_False; auto.
    apply valid_check_BuildDef; auto.
    apply valid_check_BuildDef2; auto.
    apply valid_check_BuildProj; auto.
    apply valid_check_ImmBuildDef; auto.
    apply valid_check_ImmBuildDef2; auto.
    apply valid_check_ImmBuildProj; auto.
    apply valid_check_trans; auto.
    apply valid_check_congr; auto.
    apply valid_check_congr_pred; auto.
    apply valid_check_micromega; auto.
    apply valid_check_diseq; auto.
    apply valid_check_spl_arith; auto.
    apply valid_check_distinct_elim; auto.
  Qed.

  Definition euf_checker t_atom t_form s t :=
    _checker_ (step_checker t_atom t_form) s t.

  Lemma euf_checker_correct : forall t_i t_func t_atom t_form,
    let rho := Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form in
      Form.check_form t_form -> Atom.check_atom t_atom ->
      Atom.wt t_i t_func t_atom ->
      forall s t confl,
        euf_checker t_atom t_form C.is_false s t confl ->
        ~ (S.valid rho s).
  Proof.
    unfold euf_checker; intros t_i t_func t_atom t_form rho H1 H2 H10; apply _checker__correct.
    intros c H; apply C.is_false_correct; auto.
    apply step_checker_correct; auto.
  Qed.

  Inductive certif :=
  | Certif : int -> _trace_ step -> int -> certif.

  Definition add_roots s d used_roots :=
    match used_roots with
      | Some ur => PArray.foldi_right (fun i c_index s =>
        let c := if c_index < length d then (d.[c_index])::nil else C._true in
          S.set_clause s i c) ur s
      | None => PArray.foldi_right (fun i c s => S.set_clause s i (c::nil)) d s
    end.

  Definition valid t_i t_func t_atom t_form d :=
    let rho := Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form in
    afold_left _ _ true andb (Lit.interp rho) d.

  Lemma add_roots_correct : forall t_i t_func t_atom t_form,
    let rho := Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form in
      Form.check_form t_form -> Atom.check_atom t_atom ->
      Atom.wt t_i t_func t_atom ->
      forall s d used_roots, S.valid rho s -> valid t_func t_atom t_form d ->
        S.valid rho (add_roots s d used_roots).
  Proof.
    intros t_i t_func t_atom t_form rho H1 H2 H10 s d used_roots H3; unfold valid; intro H4; pose (H5 := (afold_left_andb_true_inv _ _ _ H4)); unfold add_roots; assert (Valuation.wf rho) by (destruct (Form.check_form_correct (Atom.interp_form_hatom t_i t_func t_atom) _ H1) as [_ H]; auto); case used_roots.
    intro ur; apply (foldi_right_Ind _ _ (fun _ a => S.valid rho a)); auto; intros a i H6 Ha; apply S.valid_set_clause; auto; case_eq (ur .[ i] < length d).
    intro; unfold C.valid; simpl; rewrite H5; auto.
    intros; apply C.interp_true; auto.
    apply (foldi_right_Ind _ _ (fun _ a => S.valid rho a)); auto; intros a i H6 Ha; apply S.valid_set_clause; auto; unfold C.valid; simpl; rewrite H5; auto.
  Qed.

  Definition checker t_i t_func t_atom t_form d used_roots (c:certif) :=
    let (nclauses, t, confl) := c in
    Form.check_form t_form && Atom.check_atom t_atom &&
    Atom.wt t_i t_func t_atom &&
    euf_checker t_atom t_form C.is_false (add_roots (S.make nclauses) d used_roots) t confl.
  Implicit Arguments checker [].

  Lemma checker_correct : forall t_i t_func t_atom t_form d used_roots c,
    checker t_i t_func t_atom t_form d used_roots c = true ->
    ~ valid t_func t_atom t_form d.
  Proof.
    unfold checker; intros t_i t_func t_atom t_form d used_roots (nclauses, t, confl); rewrite !andb_true_iff; intros [[[H1 H2] H10] H3] H; eelim euf_checker_correct; try eassumption; apply add_roots_correct; try eassumption; apply S.valid_make; destruct (Form.check_form_correct (Atom.interp_form_hatom t_i t_func t_atom) _ H1) as [_ H4]; auto.
  Qed.

  Definition checker_b t_i t_func t_atom t_form l (b:bool) (c:certif) :=
    let l := if b then Lit.neg l else l in
    let (nclauses,_,_) := c in
    checker t_i t_func t_atom t_form (PArray.make nclauses l) None c.

  Lemma checker_b_correct : forall t_i t_func t_atom t_form l b c,
    checker_b t_func t_atom t_form l b c = true ->
    Lit.interp (Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form) l = b.
  Proof.
   unfold checker_b; intros t_i t_func t_atom t_form l b (nclauses, t, confl); case b; intros H2; case_eq (Lit.interp (Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form) l); auto; intros H1; elim (checker_correct H2 (t_func:=t_func)); auto; unfold valid; apply afold_left_andb_true; intros i Hi; rewrite get_make; auto; rewrite Lit.interp_neg, H1; auto.
 Qed.

  Definition checker_eq t_i t_func t_atom t_form l1 l2 l (c:certif) :=
    negb (Lit.is_pos l) &&
    match t_form.[Lit.blit l] with
      | Form.Fiff l1' l2' => (l1 == l1') && (l2 == l2')
      | _ => false
    end &&
    let (nclauses,_,_) := c in
    checker t_i t_func t_atom t_form (PArray.make nclauses l) None c.

  Lemma checker_eq_correct : forall t_i t_func t_atom t_form l1 l2 l c,
    checker_eq t_func t_atom t_form l1 l2 l c = true ->
    Lit.interp (Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form) l1 =
    Lit.interp (Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form) l2.
  Proof.
   unfold checker_eq; intros t_i t_func t_atom t_form l1 l2 l (nclauses, t, confl); rewrite !andb_true_iff; case_eq (t_form .[ Lit.blit l]); [intros _ _|intros _|intros _|intros _ _ _|intros _ _|intros _ _|intros _ _|intros _ _ _|intros l1' l2' Heq|intros _ _ _ _]; intros [[H1 H2] H3]; try discriminate; rewrite andb_true_iff in H2; rewrite !Int31Properties.eqb_spec in H2; destruct H2 as [H2 H4]; subst l1' l2'; case_eq (Lit.is_pos l); intro Heq'; rewrite Heq' in H1; try discriminate; clear H1; assert (H:PArray.default t_form = Form.Ftrue /\ Form.wf t_form).
   unfold checker in H3; rewrite !andb_true_iff in H3; destruct H3 as [[[H3 _] _] _]; destruct (Form.check_form_correct (Atom.interp_form_hatom t_i t_func t_atom) _ H3) as [[Ht1 Ht2] Ht3]; split; auto.
   destruct H as [H1 H2]; case_eq (Lit.interp (Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form) l1); intro Heq1; case_eq (Lit.interp (Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form) l2); intro Heq2; auto; elim (checker_correct H3 (t_func:=t_func)); unfold valid; apply afold_left_andb_true; intros i Hi; rewrite get_make; unfold Lit.interp; rewrite Heq'; unfold Var.interp; rewrite Form.wf_interp_form; auto; rewrite Heq; simpl; rewrite Heq1, Heq2; auto.
 Qed.

  (* For debugging *)
  (*
  Fixpoint is__true (c:C.t) :=
    match c with
      | cons l q => if (l == 0) then true else is__true q
      | _ => false
    end.

  Definition step_checker_debug t_atom t_form s (st:step) :=
    match st with
      | Res pos res =>
        let s' := S.set_resolve s pos res in
          if is__true (s'.[pos]) then None else Some s'
      | ImmFlatten pos cid lf =>
        let c := check_flatten t_atom t_form s cid lf in
          if is__true c then None else Some (S.set_clause s pos c)
      | CTrue pos => Some (S.set_clause s pos Cnf.check_True)
      | CFalse pos => Some (S.set_clause s pos Cnf.check_False)
      | BuildDef pos l =>
        let c := check_BuildDef t_form l in
          if is__true c then None else Some (S.set_clause s pos c)
      | BuildDef2 pos l =>
        let c := check_BuildDef2 t_form l in
          if is__true c then None else Some (S.set_clause s pos c)
      | BuildProj pos l i =>
        let c := check_BuildProj t_form l i in
          if is__true c then None else Some (S.set_clause s pos c)
      | ImmBuildDef pos cid =>
        let c := check_ImmBuildDef t_form s cid in
          if is__true c then None else Some (S.set_clause s pos c)
      | ImmBuildDef2 pos cid =>
        let c := check_ImmBuildDef2 t_form s cid in
          if is__true c then None else Some (S.set_clause s pos c)
      | ImmBuildProj pos cid i =>
        let c := check_ImmBuildProj t_form s cid i in
          if is__true c then None else Some (S.set_clause s pos c)
      | EqTr pos l fl =>
        let c := check_trans t_form t_atom l fl in
          if is__true c then None else Some (S.set_clause s pos c)
      | EqCgr pos l fl =>
        let c := check_congr t_form t_atom l fl in
          if is__true c then None else Some (S.set_clause s pos c)
      | EqCgrP pos l1 l2 fl =>
        let c := check_congr_pred t_form t_atom l1 l2 fl in
          if is__true c then None else Some (S.set_clause s pos c)
      | LiaMicromega pos cl c =>
        let c := check_micromega t_form t_atom cl c in
          if is__true c then None else Some (S.set_clause s pos c)
      | LiaDiseq pos l =>
        let c := check_diseq t_form t_atom l in
          if is__true c then None else Some (S.set_clause s pos c)
      | SplArith pos orig res l =>
        let c := check_spl_arith t_form t_atom (S.get s orig) res l in
          if is__true c then None else Some (S.set_clause s pos c)
      | SplDistinctElim pos input res =>
        let c := check_distinct_elim t_form t_atom (S.get s input) res in
          if is__true c then None else Some (S.set_clause s pos c)
    end.

  Definition euf_checker_debug t_atom t_form s t :=
    _checker_debug_ (step_checker_debug t_atom t_form) s t.

  Definition euf_checker_partial t_atom t_form s t :=
    _checker_partial_ (step_checker t_atom t_form) s t.
  *)

End Euf_Checker.


Unset Implicit Arguments.
*)
*)
*)