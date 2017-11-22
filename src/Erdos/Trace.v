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

Require Import Bool Int31 PArray Resource String.

Require Import Misc State.

Local Open Scope array_scope.
Local Open Scope int31_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Set Vm Optimize.


Definition dimacs := PArray.array (PArray.array _lit).

Definition add_roots s (d:dimacs) := 
  PArray.foldi_right (fun i c s => S.set_clause s i (PArray.to_list c)) d s.

Definition resolution_checker (r:resource) (d:dimacs) (nclauses nreso:int) := 
  fold (S.set_resolve r) 1 nreso (add_roots (S.make nclauses) d, 12).

Definition checker (d:dimacs) (rname: array int) := 
  let r := Resource.make rname in
  let nclauses := Resource.geti r 0 in
  let nreso := Resource.geti r 4 in
  let confl_id := Resource.geti r 8 in
  let (s,_) := resolution_checker r d nclauses nreso in
  C.is_false (PArray.get s confl_id).

Definition C_interp_or rho c := 
  afold_left _ _ false orb (Lit.interp rho) c.

Lemma C_interp_or_spec : forall rho c,
  C_interp_or rho c = C.interp rho (to_list c).
Proof.
  intros rho c; unfold C_interp_or; case_eq (C.interp rho (to_list c)).
  unfold C.interp; rewrite List.existsb_exists; intros [x [H1 H2]]; 
    destruct (In_to_list _ _ H1) as [i [H3 H4]]; subst x; apply (afold_left_orb_true _ i); auto.
  unfold C.interp; intro H; apply afold_left_orb_false; intros i H1; 
    case_eq (Lit.interp rho (c .[ i])); auto; intro Heq; 
    assert (H2: exists x, List.In x (to_list c) /\ Lit.interp rho x = true).
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
  apply afold_left_andb_true; try assumption; intros i Hi; 
    rewrite C_interp_or_spec; apply H; auto.
Qed.

Lemma valid_add_roots : forall rho, Valuation.wf rho ->
  forall d s, valid rho d -> S.valid rho s ->
  S.valid rho (add_roots s d).
Proof.
  intros rho Hwr d s Hd Hs; unfold add_roots.
  apply (PArray.foldi_right_Ind _ _ (fun _ a => S.valid rho a)); auto.
  intros a i Hlt Hv; apply S.valid_set_clause; auto; rewrite valid_spec in Hd; apply Hd; auto.
Qed.

Lemma resolution_checker_correct : forall rho, Valuation.wf rho ->
  forall r d nclauses nreso, valid rho d -> 
  S.valid rho (fst (resolution_checker r d nclauses nreso)).
Proof.
 unfold resolution_checker;intros rho Hwf r d nclauses nreso Hd.
 apply fold_ind. apply valid_add_roots;auto.     
 apply S.valid_make; auto.
 intros (s,pos) Hs; apply S.valid_set_resolve;auto.
Qed.

Lemma checker_correct_aux : forall d rname, 
  checker d rname = true ->
  forall rho, Valuation.wf rho -> ~valid rho d.
Proof.
  unfold checker; intros d rname Hc rho Hwf Hv.
  generalize (@resolution_checker_correct rho Hwf (make rname) d (geti (make rname) 0)
             (geti (make rname) 4) Hv) Hc;clear Hc.
  destruct (resolution_checker (make rname) d (geti (make rname) 0) (geti (make rname) 4))
    as (s,pos);simpl;intros Hs Hf.
  apply (C.is_false_correct (s.[ geti (make rname) 8]) Hf rho).
  apply S.valid_get;auto.
Qed.

Definition interp_var rho x := 
  match compare x 1 with
  | Lt => true
  | Eq => false
  | Gt => rho (x - 1) 
  end.

Lemma checker_correct : forall d rname, 
  checker d rname = true ->
  forall rho, ~valid (interp_var rho) d.
Proof.
  intros d c H rho;apply checker_correct_aux with c;trivial.
  split;compute;trivial;discriminate.
Qed.
