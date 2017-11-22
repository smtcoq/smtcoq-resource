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

Require Import PArray List Bool.
(* Add LoadPath ".." as SMTCoq. *)
Require Import Misc State SMT_terms.

Import Form.

Local Open Scope array_scope.
Local Open Scope int31_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Definition or_of_imp args :=
  let last := PArray.length args - 1 in
  PArray.mapi (fun i l => if i == last then l else Lit.neg l) args.
Register or_of_imp as PrimInline.

Lemma length_or_of_imp : forall args,
  PArray.length (or_of_imp args) = PArray.length args.
Proof. intro; apply length_mapi. Qed.

Lemma get_or_of_imp : forall args i,
  i < (PArray.length args) - 1 -> (or_of_imp args).[i] = Lit.neg (args.[i]).
Proof.
  unfold or_of_imp; intros args i H; case_eq (0 < PArray.length args).
  intro Heq; rewrite get_mapi.
  replace (i == PArray.length args - 1) with false; auto; symmetry; rewrite eqb_false_spec; intro; subst i; unfold is_true in H; rewrite ltb_spec, (to_Z_sub_1 _ _ Heq) in H; omega.
  rewrite ltb_spec; unfold is_true in H; rewrite ltb_spec, (to_Z_sub_1 _ _ Heq) in H; omega.
  rewrite ltb_negb_geb; case_eq (PArray.length args <= 0); try discriminate; intros Heq _; assert (H1: PArray.length args = 0).
  apply to_Z_inj; rewrite leb_spec in Heq; destruct (to_Z_bounded (PArray.length args)) as [H1 _]; change [|0|] with 0%Z in *; omega.
  rewrite !get_outofbound.
  rewrite default_mapi, H1; auto.
  rewrite H1; case_eq (i < 0); auto; intro H2; eelim ltb_0; eassumption.
  rewrite length_mapi, H1; case_eq (i < 0); auto; intro H2; eelim ltb_0; eassumption.
Qed.

Lemma get_or_of_imp2 : forall args i, 0 < PArray.length args ->
  i = (PArray.length args) - 1 -> (or_of_imp args).[i] = args.[i].
Proof.
  unfold or_of_imp; intros args i Heq Hi; rewrite get_mapi; subst i.
  rewrite Int31Axioms.eqb_refl; auto.
  rewrite ltb_spec, (to_Z_sub_1 _ _ Heq); omega.
Qed.


Section CHECKER.

  Variable t_form : PArray.array form.
  Local Notation get_hash := (PArray.get t_form) (only parsing).
  Variable s : S.t.


  (*  * true             : {true}  *)

  Definition check_True := C._true.


  (* * false             : {(not false)} *)

  Definition check_False  := Lit.neg (Lit._false)::nil.


  (* * and_neg          : {(and a_1 ... a_n) (not a_1) ... (not a_n)}
     * or_pos           : {(not (or a_1 ... a_n)) a_1 ... a_n} 
     * implies_pos      : {(not (implies a b)) (not a) b}
     * xor_pos1         : {(not (xor a b)) a b}
     * xor_neg1         : {(xor a b) a (not b)}
     * equiv_pos1       : {(not (iff a b)) a (not b)}
     * equiv_neg1       : {(iff a b) (not a) (not b)}
     * ite_pos1         : {(not (if_then_else a b c)) a c}
     * ite_neg1         : {(if_then_else a b c) a (not c)} *)

  Definition check_BuildDef l :=
    match get_hash (Lit.blit l) with
    | Fand args => 
      if Lit.is_pos l then l :: List.map Lit.neg (PArray.to_list args) 
      else C._true
    | For args =>
      if Lit.is_pos l then C._true
      else l :: PArray.to_list args
    | Fimp args =>
      if Lit.is_pos l then C._true
      else
        let args := or_of_imp args in
        l :: PArray.to_list args
    | Fxor a b =>
      if Lit.is_pos l then l::a::Lit.neg b::nil 
      else l::a::b::nil
    | Fiff a b =>
      if Lit.is_pos l then l::Lit.neg a::Lit.neg b::nil
      else l::a::Lit.neg b::nil
    | Fite a b c =>
      if Lit.is_pos l then l::a::Lit.neg c::nil
      else l::a::c::nil
    | _ => C._true
    end.

 
  (* * not_and           : {(not (and a_1 ... a_n))} --> {(not a_1) ... (not a_n)}
     * or                : {(or a_1 ... a_n)} --> {a_1 ... a_n}
     * implies           : {(implies a b)} --> {(not a) b}
     * xor1              : {(xor a b)} --> {a b}
     * not_xor1          : {(not (xor a b))} --> {a (not b)}
     * equiv2            : {(iff a b)} --> {a (not b)}
     * not_equiv2        : {(not (iff a b))} --> {(not a) (not b)}
     * ite1              : {(if_then_else a b c)} --> {a c}
     * not_ite1          : {(not (if_then_else a b c))} --> {a (not c)} *)

  Definition check_ImmBuildDef pos :=
    match S.get s pos with
    | l::nil =>
      match get_hash (Lit.blit l) with
      | Fand args => 
        if Lit.is_pos l then C._true
        else List.map Lit.neg (PArray.to_list args) 
      | For args =>
        if Lit.is_pos l then PArray.to_list args
        else C._true
      | Fimp args =>
        if Lit.is_pos l then 
          let args := or_of_imp args in
          PArray.to_list args
        else C._true
      | Fxor a b =>
        if Lit.is_pos l then a::b::nil
        else a::Lit.neg b::nil 
      | Fiff a b =>
        if Lit.is_pos l then a::Lit.neg b::nil
        else Lit.neg a::Lit.neg b::nil
      | Fite a b c =>
        if Lit.is_pos l then a::c::nil
        else a::Lit.neg c::nil
      | _ => C._true
      end
    | _ => C._true
    end.


  (* * xor_pos2          : {(not (xor a b)) (not a) (not b)}
     * xor_neg2          : {(xor a b) (not a) b}
     * equiv_pos2        : {(not (iff a b)) (not a) b}
     * equiv_neg2        : {(iff a b) a b}
     * ite_pos2          : {(not (if_then_else a b c)) (not a) b}
     * ite_neg2          : {(if_then_else a b c) (not a) (not b)} *)

  Definition check_BuildDef2 l :=
    match get_hash (Lit.blit l) with
    | Fxor a b =>
      if Lit.is_pos l then l::Lit.neg a::b::nil
      else l::Lit.neg a::Lit.neg b::nil
    | Fiff a b =>
      if Lit.is_pos l then l::a::b::nil
      else l::Lit.neg a::b::nil
    | Fite a b c =>
      if Lit.is_pos l then l::Lit.neg a::Lit.neg b::nil
      else l::Lit.neg a::b::nil
    | _ => C._true
    end.


  (* * xor2              : {(xor a b)} --> {(not a) (not b)}
     * not_xor2          : {(not (xor a b))} --> {(not a) b}
     * equiv1            : {(iff a b)} --> {(not a) b}
     * not_equiv1        : {(not (iff a b))} --> {a b}
     * ite2              : {(if_then_else a b c)} --> {(not a) b}
     * not_ite2          : {(not (if_then_else a b c))} --> {(not a) (not b)}
     *)

  Definition check_ImmBuildDef2 pos :=
    match S.get s pos with
    | l::nil =>
      match get_hash (Lit.blit l) with
      | Fxor a b =>
        if Lit.is_pos l then Lit.neg a::Lit.neg b::nil
        else Lit.neg a::b::nil
      | Fiff a b =>
        if Lit.is_pos l then Lit.neg a::b::nil
        else a::b::nil
      | Fite a b c =>
        if Lit.is_pos l then Lit.neg a::b::nil
        else Lit.neg a::Lit.neg b::nil
      | _ => C._true
      end
    | _ => C._true
    end.

 
  (* * or_neg           : {(or a_1 ... a_n) (not a_i)}
     * and_pos          : {(not (and a_1 ... a_n)) a_i} 
     * implies_neg1     : {(implies a b) a}
     * implies_neg2     : {(implies a b) (not b)} *)

  Definition check_BuildProj l i :=
    let x := Lit.blit l in
    match get_hash x with
    | For args =>
      if i < PArray.length args then Lit.lit x::Lit.neg (args.[i])::nil
      else C._true
    | Fand args =>
      if i < PArray.length args then Lit.nlit x::(args.[i])::nil
      else C._true
    | Fimp args =>
      let len := PArray.length args in
      if i < len then
        if i == len - 1 then Lit.lit x::Lit.neg (args.[i])::nil
        else Lit.lit x::(args.[i])::nil
      else C._true
    | _ => C._true
    end.


  (* * and               : {(and a_1 ... a_n)} --> {a_i} 
     * not_or            : {(not (or a_1 ... a_n))} --> {(not a_i)}
     * not_implies1      : {(not (implies a b))} --> {a}
     * not_implies2      : {(not (implies a b))} --> {(not b)} *)

  Definition check_ImmBuildProj pos i := 
    match S.get s pos with
    | l::nil =>
      let x := Lit.blit l in
      match get_hash x with
      | For args =>
        if (i < PArray.length args) && negb (Lit.is_pos l) then Lit.neg (args.[i])::nil
        else C._true
      | Fand args =>
        if (i < PArray.length args) && (Lit.is_pos l) then (args.[i])::nil
        else C._true
      | Fimp args =>
        let len := PArray.length args in
        if (i < len) && negb (Lit.is_pos l) then
          if i == len - 1 then Lit.neg (args.[i])::nil
          else (args.[i])::nil
        else C._true
      | _ => C._true
      end
    | _ => C._true
    end.

  (** The correctness proofs *)

  Variable interp_atom : atom -> bool.

  Hypothesis Hch_f : check_form t_form.

  Local Notation rho := (Form.interp_state_var interp_atom t_form).

  Let Hwfrho : Valuation.wf rho.
  Proof.
    destruct (check_form_correct interp_atom _ Hch_f) as (_, H);exact H. 
  Qed.

  Lemma valid_check_True : C.valid rho check_True.
  Proof. 
    apply C.interp_true;trivial.
  Qed.

  Lemma valid_check_False : C.valid rho check_False.
  Proof.
    unfold check_False, C.valid;simpl.
    rewrite Lit.interp_neg.
    assert (W:= Lit.interp_false _ Hwfrho).
    destruct (Lit.interp rho Lit._false);trivial;elim W;red;trivial.
  Qed.

  Let rho_interp : forall x : int,
    rho x = interp interp_atom t_form (t_form.[ x]).
  Proof.
    destruct (check_form_correct interp_atom _ Hch_f) as ((H,H0), _).
    intros x;apply wf_interp_form;trivial.
  Qed.

  Ltac tauto_check :=
   try (rewrite !Lit.interp_neg);
   repeat 
     match goal with |- context [Lit.interp rho ?x] => 
     destruct (Lit.interp rho x);trivial end.


  Lemma afold_left_and a :
    afold_left bool int true andb (Lit.interp rho) a =
    List.forallb (Lit.interp rho) (to_list a).
  Proof.
    case_eq (afold_left bool int true andb (Lit.interp rho) a); intro H; symmetry.
      assert (H1:=afold_left_andb_true_inv _ _ _ H); clear H. rewrite forallb_forall. intros i H. apply In_to_list in H. destruct H as [j [H2 H3]]. subst. apply H1. auto.
      apply afold_left_andb_false_inv in H. destruct H as [i [H H1]]. case_eq (forallb (Lit.interp rho) (to_list a)); auto. rewrite forallb_forall. intro H2. rewrite <- H1. symmetry. auto using to_list_In.
  Qed.


  Lemma afold_left_or a :
    afold_left bool int false orb (Lit.interp rho) a =
    C.interp rho (to_list a).
  Proof.
    case_eq (afold_left bool int false orb (Lit.interp rho) a); intro H; symmetry.
      apply afold_left_orb_true_inv in H. destruct H as [i [H H1]]. unfold C.interp. rewrite existsb_exists. exists (a.[i]); split; auto using to_list_In.
      assert (H1:=afold_left_orb_false_inv _ _ _ H); clear H. unfold C.interp. case_eq (existsb (Lit.interp rho) (to_list a)); auto. rewrite existsb_exists. intros [x [H H2]]. apply In_to_list in H. destruct H as [i [H H3]]. subst. rewrite <- H2. auto.
  Qed.


  Lemma afold_right_impb a :
    (afold_right bool int false implb (Lit.interp rho) a) =
    C.interp rho (to_list (or_of_imp a)).
  Proof.
    case_eq (afold_right bool int false implb (Lit.interp rho) a); intro H; symmetry.
      apply afold_right_implb_true_inv in H. destruct H as [H [[i [H1 H2]]|H1]].
        unfold C.interp. rewrite existsb_exists. exists (Lit.neg (a.[i])). split.
          apply (to_list_In2 i).
            rewrite length_or_of_imp, ltb_spec. rewrite ltb_spec, (to_Z_sub_1 _ 0) in H1; auto. omega.
            unfold or_of_imp. rewrite get_mapi.
              replace (i == PArray.length a - 1) with false; auto. symmetry. rewrite eqb_false_spec. intro H3. rewrite <- H3 in H1. apply (not_ltb_refl i). auto.
              rewrite ltb_spec. rewrite ltb_spec, (to_Z_sub_1 _ 0) in H1; auto. omega.
          rewrite Lit.interp_neg, H2; auto.
        unfold C.interp. rewrite existsb_exists. exists (a.[PArray.length a - 1]). split.
          apply (to_list_In2 (PArray.length a - 1)).
            rewrite length_or_of_imp, ltb_spec, (to_Z_sub_1 _ 0); auto. omega.
            unfold or_of_imp. rewrite get_mapi.
              rewrite Int31Axioms.eqb_refl. auto.
              rewrite ltb_spec, (to_Z_sub_1 _ 0); auto. omega.
          apply H1. rewrite ltb_spec, (to_Z_sub_1 _ 0); auto. omega.
      apply afold_right_implb_false_inv in H. destruct H as [H|[H H1]].
        unfold C.interp. case_eq (existsb (Lit.interp rho) (to_list (or_of_imp a))); auto. rewrite existsb_exists. intros [x [H1 H2]]. apply In_to_list in H1. destruct H1 as [i [H1 _]]. rewrite length_or_of_imp, <- H in H1. eelim ltb_0; eauto.
        unfold C.interp. case_eq (existsb (Lit.interp rho) (to_list (or_of_imp a))); auto. rewrite existsb_exists. intros [x [H2 H3]]. apply In_to_list in H2. destruct H2 as [i [H2 H4]]. subst. unfold or_of_imp in H3. rewrite get_mapi in H3.
          case_eq (i == PArray.length a - 1); intro H4; rewrite H4 in H3.
            rewrite eqb_spec in H4. subst. rewrite <- H3. auto.
            rewrite Lit.interp_neg in H3. rewrite eqb_false_spec in H4. rewrite H in H3; try discriminate. case_eq (PArray.length a == 0).
              rewrite eqb_spec. intro H5. rewrite length_or_of_imp, H5 in H2. eelim ltb_0; eauto.
              rewrite eqb_false_spec. intro H5. rewrite ltb_spec, to_Z_sub_1_diff; auto. assert (H6:[|i|] <> ([|PArray.length a|] - 1)%Z).
                intro H6. apply H4, to_Z_inj. rewrite to_Z_sub_1_diff; auto.
                rewrite length_or_of_imp, ltb_spec in H2. omega.
          rewrite length_or_of_imp in H2; auto.
  Qed.


  Lemma Cinterp_neg cl :
     C.interp rho (map Lit.neg cl) = negb (forallb (Lit.interp rho) cl).
  Proof.
    unfold C.interp. case_eq (forallb (Lit.interp rho) cl); simpl.
      rewrite forallb_forall. intro H. case_eq (existsb (Lit.interp rho) (map Lit.neg cl)); auto. rewrite existsb_exists. intros [l [H1 H2]]. rewrite in_map_iff in H1. destruct H1 as [x [H1 H3]]. subst l. rewrite <- H2, Lit.interp_neg, H; auto.
      rewrite existsb_exists. induction cl as [ |l cl IHcl]; simpl; try discriminate.
      rewrite andb_false_iff. intros [H|H].
        exists (Lit.neg l). intuition. rewrite Lit.interp_neg, H. auto.
        destruct (IHcl H) as [x [H1 H2]]. exists x; auto.
  Qed.


  Lemma valid_check_BuildDef : forall l, C.valid rho (check_BuildDef l).
  Proof.
   unfold check_BuildDef,C.valid;intros l.
   case_eq (t_form.[Lit.blit l]);intros;auto using C.interp_true;
   case_eq (Lit.is_pos l);intros Heq;auto using C.interp_true;simpl;
   unfold Lit.interp at 1;rewrite Heq;unfold Var.interp; rewrite rho_interp, H;simpl;
   tauto_check.
   rewrite afold_left_and, Cinterp_neg;apply orb_negb_r.
   rewrite afold_left_or, orb_comm;apply orb_negb_r.
   rewrite afold_right_impb, orb_comm;apply orb_negb_r.
  Qed.

  Lemma valid_check_BuildDef2 : forall l, C.valid rho (check_BuildDef2 l).
  Proof.
   unfold check_BuildDef2,C.valid;intros l.
   case_eq (t_form.[Lit.blit l]);intros;auto using C.interp_true;
   case_eq (Lit.is_pos l);intros Heq;auto using C.interp_true;simpl;
   unfold Lit.interp at 1;rewrite Heq;unfold Var.interp; rewrite rho_interp, H;simpl;
   tauto_check.
  Qed.

  Lemma valid_check_BuildProj : forall l i, C.valid rho (check_BuildProj l i).
  Proof.
   unfold check_BuildProj,C.valid;intros l i.
   case_eq (t_form.[Lit.blit l]);intros;auto using C.interp_true;
   case_eq (i < PArray.length a);intros Hlt;auto using C.interp_true;simpl.

   rewrite Lit.interp_nlit;unfold Var.interp;rewrite rho_interp, orb_false_r, H.
   simpl;rewrite afold_left_and.
   case_eq (forallb (Lit.interp rho) (to_list a));trivial.
   rewrite forallb_forall;intros Heq;rewrite Heq;trivial.
   apply to_list_In; auto.
   rewrite Lit.interp_lit;unfold Var.interp;rewrite rho_interp, orb_false_r, H.
   simpl;rewrite afold_left_or.
      
   unfold C.interp;case_eq (existsb (Lit.interp rho) (to_list a));trivial.
   rewrite <-not_true_iff_false, existsb_exists, Lit.interp_neg.
   case_eq (Lit.interp rho (a .[ i]));trivial.
   intros Heq Hex;elim Hex;exists (a.[i]);split;trivial.
   apply to_list_In; auto.
   case_eq (i == PArray.length a - 1);intros Heq;simpl;
   rewrite Lit.interp_lit;unfold Var.interp;rewrite rho_interp, H;simpl;
   rewrite afold_right_impb; case_eq (C.interp rho (to_list (or_of_imp a)));trivial;
   unfold C.interp;rewrite <-not_true_iff_false, existsb_exists;
   try rewrite Lit.interp_neg; case_eq (Lit.interp rho (a .[ i]));trivial;
   intros Heq' Hex;elim Hex.
   exists (a.[i]);split;trivial.
   assert (H1: 0 < PArray.length a) by (apply (leb_ltb_trans _ i _); auto; apply leb_0); rewrite Int31Properties.eqb_spec in Heq; rewrite <- (get_or_of_imp2 H1 Heq); apply to_list_In; rewrite length_or_of_imp; auto.
   exists (Lit.neg (a.[i]));rewrite Lit.interp_neg, Heq';split;trivial.
   assert (H1: i < PArray.length a - 1 = true) by (rewrite ltb_spec, (to_Z_sub_1 _ _ Hlt); rewrite eqb_false_spec in Heq; assert (H1: [|i|] <> ([|PArray.length a|] - 1)%Z) by (intro H1; apply Heq, to_Z_inj; rewrite (to_Z_sub_1 _ _ Hlt); auto); rewrite ltb_spec in Hlt; omega); rewrite <- (get_or_of_imp H1); apply to_list_In; rewrite length_or_of_imp; auto.
  Qed.

  Hypothesis Hs : S.valid rho s.

  Lemma valid_check_ImmBuildDef : forall cid,
     C.valid rho (check_ImmBuildDef cid).
  Proof.
   unfold check_ImmBuildDef,C.valid;intros cid.
   generalize (Hs cid);unfold C.valid.
   destruct (S.get s cid) as [ | l [ | _l _c]];auto using C.interp_true.
   simpl;unfold Lit.interp, Var.interp; rewrite !rho_interp;
   destruct (t_form.[Lit.blit l]);auto using C.interp_true;
   case_eq (Lit.is_pos l);intros Heq;auto using C.interp_true;simpl;
   tauto_check.
   rewrite afold_left_and, Cinterp_neg, orb_false_r;trivial.
   rewrite afold_left_or, orb_false_r;trivial.
   rewrite afold_right_impb, orb_false_r;trivial.
  Qed.

  Lemma valid_check_ImmBuildDef2 : forall cid, C.valid rho (check_ImmBuildDef2 cid).
  Proof.
    unfold check_ImmBuildDef2,C.valid;intros cid.
    generalize (Hs cid);unfold C.valid.
    destruct (S.get s cid) as [ | l [ | _l _c]];auto using C.interp_true.
    simpl;unfold Lit.interp, Var.interp; rewrite !rho_interp;
    destruct (t_form.[Lit.blit l]);auto using C.interp_true;
    case_eq (Lit.is_pos l);intros Heq;auto using C.interp_true;simpl;
    tauto_check.
  Qed.

  Lemma valid_check_ImmBuildProj : forall cid i, C.valid rho (check_ImmBuildProj cid i).
  Proof.
   unfold check_ImmBuildProj,C.valid;intros cid i.
   generalize (Hs cid);unfold C.valid.
   destruct (S.get s cid) as [ | l [ | _l _c]];auto using C.interp_true.
   simpl;unfold Lit.interp, Var.interp; rewrite !rho_interp;
     destruct (t_form.[Lit.blit l]);auto using C.interp_true;
       case_eq (i < PArray.length a); intros Hlt;auto using C.interp_true;
       case_eq (Lit.is_pos l);intros Heq;auto using C.interp_true;simpl;
       rewrite !orb_false_r.  
   rewrite afold_left_and.
   rewrite forallb_forall;intros H;apply H;auto.
   apply to_list_In; auto.
   rewrite negb_true_iff, <-not_true_iff_false, afold_left_or.
   unfold C.interp;rewrite existsb_exists, Lit.interp_neg.
   case_eq (Lit.interp rho (a .[ i]));trivial.
   intros Heq' Hex;elim Hex;exists (a.[i]);split;trivial.
   apply to_list_In; auto.
   rewrite negb_true_iff, <-not_true_iff_false, afold_right_impb.
   case_eq (i == PArray.length a - 1);intros Heq';simpl;
     unfold C.interp;simpl;try rewrite Lit.interp_neg;rewrite orb_false_r,
   existsb_exists;case_eq (Lit.interp rho (a .[ i]));trivial;
   intros Heq2 Hex;elim Hex.
   exists (a.[i]);split;trivial.
   assert (H1: 0 < PArray.length a) by (apply (leb_ltb_trans _ i _); auto; apply leb_0); rewrite Int31Properties.eqb_spec in Heq'; rewrite <- (get_or_of_imp2 H1 Heq'); apply to_list_In; rewrite length_or_of_imp; auto.
   exists (Lit.neg (a.[i]));rewrite Lit.interp_neg, Heq2;split;trivial.
   assert (H1: i < PArray.length a - 1 = true) by (rewrite ltb_spec, (to_Z_sub_1 _ _ Hlt); rewrite eqb_false_spec in Heq'; assert (H1: [|i|] <> ([|PArray.length a|] - 1)%Z) by (intro H1; apply Heq', to_Z_inj; rewrite (to_Z_sub_1 _ _ Hlt); auto); rewrite ltb_spec in Hlt; omega); rewrite <- (get_or_of_imp H1); apply to_list_In; rewrite length_or_of_imp; auto.
  Qed.

End CHECKER.
  
Unset Implicit Arguments.