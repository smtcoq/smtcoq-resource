Add LoadPath ".." as SMTCoq. 
Require Import SMTCoq Bool PArray Int31 List ZArith.
Require Import ssreflect ssrbool eqtype ssrnat choice seq.
Require Import fintype bigop ssralg ssrnum ssrint zmodp div.
Import Sat_Checker.
Import GRing.Theory.

(******************************************************************************)
(*                                                                            *)
(*      Bool to int conversion  [b] = if b then 1 else -1                     *)
(*                                                                            *)
(******************************************************************************)

Definition b2i x : int := if x is true then 1 else (-1)%R.
Notation "[ x ]" := (b2i x).

Lemma b2iT : [true] = 1.
Proof. by []. Qed.

Lemma b2iF : [false] = (-1)%R.
Proof. by []. Qed.


(******************************************************************************)
(*                                                                            *)
(*                         CNF formula and evaluation                         *)
(*                                                                            *)
(******************************************************************************)

(* literals *)

Inductive lit := Plit (_ : N) | Nlit (_ : N) | Blit (_ : bool).
Notation " + a " := (Plit a) (at level 70).
Notation " ~ a " := (Nlit a).

(* Evaluate a literal *)

Definition eval_lit (env : N -> bool) (l : lit) :=
  match l with + a => env a | ~ a => ~~ (env a) | Blit b => b end.

(* Evaluate a clause *)
Definition eval_cl (env : N -> bool) (l : seq lit) :=
  foldl (fun r x => r || eval_lit env x) false l.

Lemma eval_cl_cons env a l : 
  eval_cl env (a :: l) = eval_lit env a || eval_cl env l.
Proof.
rewrite /eval_cl /=.
case: (eval_lit _ a) => //=.
by elim: l => //=.
Qed.

Lemma eval_clE env l : 
  eval_cl env l = existsb (fun x => eval_lit env x) l.
Proof.
elim: l => //= a l.
by rewrite eval_cl_cons => ->.
Qed.

(* Evaluate a cnf formula *)
Definition eval_cnf (env : N -> bool) (l : seq (seq lit)) :=
  foldl (fun r l => r && eval_cl env l) true l.

Lemma eval_cnf_cons env a l : 
  eval_cnf env (a :: l) = eval_cl env a && eval_cnf env l.
Proof.
rewrite /eval_cnf /=.
case: (eval_cl _ a) => //=.
by elim: l => //=.
Qed.

Lemma eval_cnf_rcons env a l : 
  eval_cnf env (rcons l a) = eval_cl env a && eval_cnf env l.
Proof.
rewrite /eval_cnf /= -[rcons l a]revK foldl_rev rev_rcons /=.
case: (eval_cl _ a) => //=.
  by rewrite -foldl_rev revK // andbT.
by rewrite andbC.
Qed.

Lemma eval_cnf_rev env cs :
  eval_cnf env cs -> eval_cnf env (rev cs).
Proof.
elim: cs => // c cs IH.
rewrite eval_cnf_cons rev_cons eval_cnf_rcons => /andP[-> HH] /=.
by apply: IH.
Qed.

Lemma eval_consE env l : 
  eval_cnf env l = forallb (fun x => existsb (fun x => eval_lit env x) x) l.
Proof.
elim: l => //= a l.
rewrite eval_cnf_cons => ->.
by rewrite eval_clE.
Qed.

Definition n2i (f : N -> bool) x := f (Z.to_N (to_Z x)).

(* dimacs literal gives lit *)
Definition i2l a :=
if is_even a
 then
  match (Lit.blit a ?= 1)%int31 with
  | Eq => Blit false
  | Lt => Blit true
  | Gt => Plit (Z.to_N [|Lit.blit a - 1|]%int31)
  end
 else
  match (Lit.blit a ?= 1)%int31 with
  | Eq => Blit true
  | Lt => Blit false
  | Gt => Nlit (Z.to_N [|Lit.blit a - 1|]%int31)
  end.

Lemma eval_cl_interp rho c :
   C_interp_or (interp_var (n2i rho)) c =
       eval_cl rho (map i2l (to_list c)).
Proof.
rewrite C_interp_or_spec eval_clE.
elim: to_list => //= a l ->.
rewrite /eval_lit /n2i /Lit.interp /Var.interp /Lit.is_pos /i2l.
rewrite /interp_var.
by case: is_even; case: (_ ?= _)%int31.
Qed.

Lemma eval_cnf_valid rho c :
 eval_cnf rho (map (fun l => map i2l (to_list l)) (to_list c)) ->
   Sat_Checker.valid (interp_var (n2i rho)) c.
Proof.
move=> H.
case: (valid_spec (interp_var (n2i rho)) c) => _ H1.
apply: H1 => i H2.
rewrite -C_interp_or_spec eval_cl_interp.
move: H.
have := Misc.to_list_In c i H2.
elim: to_list => //= a l IH.
rewrite eval_cnf_cons.
case => [-> | /IH] //; first by move=> /andP[].
by move=> HH /andP[H3 H4]; apply: HH.
Qed.

(* literal to natural number *)
Definition lit2nat l := match l with Plit n => n | Nlit n => n | Blit _ => 0%num end.

(* the maximal literal *)

Definition max_cl (l : seq lit) : nat :=
  foldr (fun x => maxn (lit2nat x)) 0 l.

Definition max_cnf (l : seq (seq lit)) : nat :=
  foldr (fun l => maxn (max_cl l)) 0 l.

Lemma max_cnf_cons a l : 
  max_cnf (a :: l) = maxn (max_cl a) (max_cnf l).
Proof. by []. Qed.

Lemma max_cnf_rcons a l : 
  max_cnf (rcons l a) = maxn (max_cl a) (max_cnf l).
Proof.
have F l1 a1 : foldr (fun l => maxn (max_cl l)) a1 l1 = maxn a1 (max_cnf l1).
  elim: l1 a1 => //= b1 l2 H a1.
  by rewrite H maxnA [maxn _ a1]maxnC !maxnA.
rewrite /max_cnf -foldl_rev rev_rcons -foldl_rev /=.
by rewrite !foldl_rev !F max0n.
Qed.

Lemma max_cnf_rev cs : max_cnf (rev cs) = max_cnf cs.
Proof.
elim: cs => //= c cs IH.
by rewrite rev_cons max_cnf_rcons IH.
Qed.

(* Only value less than max_cnf matters when evaluation *)
Lemma eval_cnf_eq cs (env1 env2 : N -> bool) : 
 (forall i : N, i <= max_cnf cs -> env1 i = env2 i) ->  
  eval_cnf env1 cs =  eval_cnf env2 cs.
Proof.
elim: cs => //= c l IH EH; rewrite !eval_cnf_cons; congr (_ && _).
  elim: c EH => //= a c1 IH1 EH; rewrite !eval_cl_cons; congr (_ || _).
    case: a EH => //= n -> //=; first by rewrite !leq_max leqnn.
    by rewrite !leq_max leqnn.
  apply: IH1 => i Hi.
  apply: EH.
  by rewrite -maxnA; apply: (leq_trans _ (leq_maxr _ _)).
apply: IH => i Hi.
apply: EH.
by apply: leq_trans (leq_maxr _ _).
Qed.

(* Conversion dimacs -> cnf *)

Definition a2l (l : dimacs) :=
  Misc.afold_left _ _  [::] cat
     (fun x => [:: Misc.afold_left _ _  [::] cat (fun x => [::i2l x]) x]) l.

Fixpoint copy_list {A B : Type} (f : A -> B) l v i :=
  if l is a :: l1 then copy_list f l1 (set v i (f a)) (i + 1)%int31 else v.

Definition copy_cl l :=
  let v := make (of_Z (Z.of_nat (size l))) 0%int31 in
  copy_list (fun x => match x with Plit n => of_Z (Z.of_N ((n + 1) * 2)) |
                                  Nlit n => of_Z (Z.of_N ((n + 1) * 2  + 1)) |
                                  Blit true => 1%int31 |
                                  Blit false => 0%int31 end) l v 0.

Definition l2a l :=
  let v := make (of_Z (Z.of_nat (size l))) (make 0 0%int31) in
  copy_list copy_cl l v 0.

Section Erdos.

(* Generated size *)
Variable size : nat.

(* Sequence *)
Variable x_ : nat -> bool.

(* The element of the sequence we know is true *)
Variable z : N.
Hypothesis x_z : z <= size /\ x_ z = true.

(* All the sequences stay within 2 *)
Hypothesis Hx_ : forall k : 'I_size.+2, forall d : 'I_size.+2, 
  `|(\sum_(1 <= i < k) [x_ (i * d)])%R| <= 2.

(* Key property that makes the coding work :
   the value of an odd number of elements of a subsequent can
   be encoded by a boolean
*)

Lemma key_prop (k m : 'I_size.+2) (v : int := (\sum_(1 <= j < m) [x_ (j * k)])%R) : 
  0 < m -> ~~ odd m -> (v = [(0 <= v)%R] :> int)%R.
Proof.
rewrite {}/v; case: m => m Hm /=.
elim: m {-2}m (leqnn m) Hm => [[]//|m IH [ | [ |m1]] //=].
case: m1 => [_ _ _|m1 m1Lm Om _].
  rewrite big_ltn // big_geq //.
  by case: x_ => /=; rewrite !(exprS, expr0, addr0, mulr1).
rewrite negbK => m1O.
have FF : m1.+1 <= m1.+3 by rewrite ltnW.
have := Hx_ (Ordinal Om) k.
rewrite (big_cat_nat _  _ _ _ FF) //=.
rewrite IH //; last 2 first.
- by rewrite ltnW.
- by apply: leq_trans Om.
set x := (0 <= _)%R.
rewrite 2?big_ltn // big_geq // ?addr0.
case: x; case: x_; case: x_ => //=;
   rewrite !(exprS, expr0, addr0, mulr1).
Qed.


(******************************************************************************)
(*                                                                            *)
(*                          The clause generator                              *)
(*                                                                            *)
(******************************************************************************)

Definition cNlit x := Nlit (bin_of_nat x).
Definition cPlit x := Plit (bin_of_nat x).

Fixpoint gen (k n a b i : nat) cs : nat * seq (seq lit) :=
  let c  := b + k in
  if c > size then (i, cs) else
  let cs := [:: [:: cNlit a; cNlit b ; cNlit c]; 
                [:: cPlit a; cPlit b ; cPlit c]] ++ cs in
  if c + 2 * k > size then (i, cs) else
  let cs :=
   [:: [:: cNlit b; cNlit c ; cPlit i]; [:: cPlit b; cPlit c ; cNlit i];
       [:: cNlit a; cNlit c ; cPlit i]; [:: cPlit a; cPlit c ; cNlit i];
       [:: cNlit a; cNlit b ; cPlit i]; [:: cPlit a; cPlit b ; cNlit i]] ++ cs  in
   if n is n1.+1 then gen k n1 i (b + k.*2) i.+1 cs else (i.+1, cs).

Fixpoint gen_rec m k i cs :=
  if m is m1.+1 then
    let: (i1, cs1) := gen k size k k.*2 i cs in
    gen_rec m1 k.+1 i1 cs1 else (i, cs).

Definition gen_all := 
  let (i, cs) := gen_rec size 1 size.+1 [:: [:: Plit z]] in (i, rev cs).

(******************************************************************************)
(*                                                                            *)
(*          Clause generator + assignment that valides the clauses            *)
(*                                                                            *)
(******************************************************************************)

Fixpoint fgen (k n a b i : nat) cs (env : N -> bool) :=
  let c  := b + k in
  if c > size then (i, cs, env) else
  let cs := [:: [:: cNlit a; cNlit b ; cNlit c];
                [:: cPlit a; cPlit b ; cPlit c]] ++ cs in
  if c + 2 * k > size then (i, cs, env) else
  let cs :=
   [:: [:: cNlit b; cNlit c ; cPlit i]; [:: cPlit b; cPlit c ; cNlit i];
       [:: cNlit a; cNlit c ; cPlit i]; [:: cPlit a; cPlit c ; cNlit i];
       [:: cNlit a; cNlit b ; cPlit i]; [:: cPlit a; cPlit b ; cNlit i]] ++ cs  in
  let env1 (j : N) := 
       if i == j then (0 <= \sum_(1 <= j < (b %/ k).+2) [x_ (j * k)])%R 
       else env j in         
   if n is n1.+1 then fgen k n1 i (b + k.*2) i.+1 cs env1 
   else (i.+1, cs, env1).

Fixpoint fgen_rec m k i cs env :=
  if m is m1.+1 then
    let: (i1, cs1, env1) := fgen k size k k.*2 i cs env in
    fgen_rec m1 k.+1 i1 cs1 env1 else (i, cs, env).

Definition fgen_all := 
  let: (i, cs, env) := fgen_rec size 1 size.+1 [:: [:: Plit z]] x_ in
  (i, rev cs, env).

(******************************************************************************)
(*                                                                            *)
(*     Clause generator computes the same Clause generator + assignment       *)
(*                                                                            *)
(******************************************************************************)

Lemma fgen_gen (k n a b i : nat) cs env :
  let: (i1, cs1, env1) := fgen k n a b i cs env in
  let: (i2, cs2) := gen k n a b i cs in
  i1 = i2 /\ cs1 = cs2.
Proof.
elim : n a b i cs env => [ | n IH] /= a b i cs env;
   case: leqP => // _; case: leqP => //= _.
by apply: IH.
Qed.

Lemma fgen_gen_rec (m k i : nat) cs env :
  let: (i1, cs1, env1) := fgen_rec m k i cs env in
  let: (i2, cs2) := gen_rec m k i cs in
  i1 = i2 /\ cs1 = cs2.
Proof.
elim : m k i cs env => [ | m IH] //= k i cs env.
have := fgen_gen k size k k.*2 i cs env.
case: fgen => [[i1 cs1]] env1; case: gen => i2 c2 [<- <-].
by apply: IH.
Qed.

Lemma fgen_gen_all :
  let: (i1, cs1, env1) := fgen_all in
  let: (i2, cs2) := gen_all in i1 = i2 /\ cs1 = cs2.
Proof.
rewrite /fgen_all /gen_all. 
have := fgen_gen_rec size 1 size.+1 [:: [:: Plit z]] x_.
by case: gen_rec; case: fgen_rec => [[i1 cs1] env1 i cs] [-> ->].
Qed.

(******************************************************************************)
(*                                                                            *)
(*                          Index grows                                       *)
(*                                                                            *)
(******************************************************************************)

Lemma fgenL k n a b i cs env : 
  i <= fst (fst (fgen k n a b i cs env)).
Proof.
elim: n a b i cs env => [ |n IH] /= a b i cs env;
  case: leqP => //; try (move=> *; apply: leqnn);
  case: leqP => //=; try (move=> *; apply: leqnn).
 move=> *; apply: leqnSn.
move=> _ _.
 apply: (leq_trans (_ : i <= i.+1)).
apply: leqnSn.
apply: IH.
Qed.

(******************************************************************************)
(*                                                                            *)
(*                    Assignement invariant                                   *)
(*                                                                            *)
(******************************************************************************)

Definition env_inv i cs env :=
  [/\ max_cnf cs < i,
      (forall v, 0 < v <= size -> x_ v = env (bin_of_nat v)) &
      eval_cnf env cs].

Lemma fgen_inv k n a b i cs env :
  0 < k ->  k <= b -> k %| b -> ~~ odd (b %/ k) ->
  a < i -> size < i ->
  env_inv i cs env ->
  (\sum_(1 <= j < (b %/ k)) [x_ (j * k)] = [env (bin_of_nat a)])%R ->
  let: (i1, cs1, env1) :=  fgen k n a b i cs env in
  env_inv i1 cs1 env1.
Proof.
move=> kP.
elim : n a b i cs env => [ |n IH] /= a b i cs env kLb kDb kbE aLi sLi;
   case: leqP => // bkLs;
    (case: leqP => //= sLbkkk [maxH xH eH] aH; last first).
- have bkLi : b + k < i by apply: leq_ltn_trans sLi.
  have bLi : b < i by apply: leq_ltn_trans (leq_addr _ _) bkLi.
  repeat split => //=.
     rewrite !bin_of_natK !gtn_max aLi bLi bkLi /=.
     by have ->: 0 < i by apply: leq_ltn_trans bLi.
  rewrite !eval_cnf_cons !eval_cl_cons eH andbT !orbF.
  have bP : 0 < b by apply: leq_trans kLb.
  have Ok : k < size.+2.
    rewrite ltnW // !ltnS.
    by apply: leq_trans bkLs; case: (b) bP => //= b1 _; apply: leq_addl.
  have Obk : (b %/ k).+2 < size.+2.
    rewrite !ltnS.
    apply: leq_ltn_trans (leq_div b k) _.
    apply: leq_trans _ bkLs.
    by case: (k) kP => // k1 _; rewrite addnS leq_addr.
  have /= := Hx_ (Ordinal Obk) (Ordinal Ok).
  have FF : b %/ k <= (b %/ k).+2 by rewrite ltnW.
  rewrite (big_cat_nat _  _ _ _ FF) /=; last by rewrite divn_gt0.
  rewrite aH /= 2?big_ltn // big_geq // ?addr0.
  rewrite mulSn divnK // !xH ?[_ + b]addnC; first by do 3 case: (env _).
    by rewrite bkLs (leq_trans bP) // leq_addr.
  by rewrite bP // (leq_trans _ bkLs) // leq_addr.
- have bkLi : b + k < i by apply: leq_ltn_trans sLi.
  have bLi : b < i by apply: leq_ltn_trans (leq_addr _ _) bkLi.
  repeat split => //=; rewrite ?bin_of_natK.
  - rewrite !gtn_max !leqnn /= !andbT ltnW // ltnW // ltnW // ltnW //=.
  - move=> v vPLs.
    case: eqP sLi => [->|_ _]; last exact: xH.
    by have /andP[_ vLs] := vPLs; rewrite bin_of_natK ltnNge vLs.
  - rewrite !eval_cnf_cons !eval_cl_cons /= !bin_of_natK eqxx.
    move: bLi; rewrite ltn_neqAle eq_sym => /andP[/negPf-> _].
    move: bkLi; rewrite ltn_neqAle eq_sym => /andP[/negPf-> _].
    move: aLi; rewrite ltn_neqAle eq_sym => /andP[/negPf-> _].
    set env1 := fun j => if _ then _ else _.
    have->: eval_cnf env1 cs = eval_cnf env cs.
      apply: eval_cnf_eq => j Hj; rewrite /env1.
      have : j < i by apply: leq_ltn_trans maxH.
      by rewrite ltn_neqAle eq_sym => /andP[/negPf->].
    rewrite eH andbT !orbF.
  have bP : 0 < b by apply: leq_trans kLb.
  have Ok : k < size.+2.
    rewrite ltnW // !ltnS.
    by apply: leq_trans bkLs; case: (b) bP => //= b1 _; apply: leq_addl.
  have Obk : (b %/ k).+2 < size.+2.
    rewrite !ltnS.
    apply: leq_ltn_trans (leq_div b k) _.
    apply: leq_trans _ bkLs.
    by case: (k) kP => // k1 _; rewrite addnS leq_addr.
  have /= := Hx_ (Ordinal Obk) (Ordinal Ok).
  have FF : b %/ k <= (b %/ k).+2 by rewrite ltnW.
  rewrite (big_cat_nat _  _ _ _ FF) /=; last by rewrite divn_gt0.
  rewrite aH /= 2?big_ltn // big_geq // ?addr0.
  rewrite mulSn divnK // !xH ?[_ + b]addnC.
  - by case: (env _); case: (env _); case: (env _) => //=.
  - by rewrite bkLs (leq_trans bP) // leq_addr.
  by rewrite bP // (leq_trans _ bkLs) // leq_addr.
- have bkLi : b + k < i by apply: leq_ltn_trans sLi.
  have bLi : b < i by apply: leq_ltn_trans (leq_addr _ _) bkLi.
  repeat split => //=.
    rewrite !bin_of_natK !gtn_max aLi bLi bkLi.
    by have->: 0 < i by apply: leq_ltn_trans bLi.
  rewrite !eval_cnf_cons !eval_cl_cons eH andbT !orbF.
  have bP : 0 < b by apply: leq_trans kLb.
  have Ok : k < size.+2.
    rewrite ltnW // !ltnS.
    by apply: leq_trans bkLs; case: (b) bP => //= b1 _; apply: leq_addl.
  have Obk : (b %/ k).+2 < size.+2.
    rewrite !ltnS.
    apply: leq_ltn_trans (leq_div b k) _.
    apply: leq_trans _ bkLs.
    by case: (k) kP => // k1 _; rewrite addnS leq_addr.
  have /= := Hx_ (Ordinal Obk) (Ordinal Ok).
  have FF : b %/ k <= (b %/ k).+2 by rewrite ltnW.
  rewrite (big_cat_nat _  _ _ _ FF) /=; last by rewrite divn_gt0.
  rewrite aH /= 2?big_ltn // big_geq // ?addr0.
  rewrite mulSn divnK // !xH ?[_ + b]addnC; first by do 3 case: (env _).
    by rewrite bkLs (leq_trans bP) // leq_addr.
  by rewrite bP // (leq_trans _ bkLs) // leq_addr.
apply: IH => //=.
- by apply: leq_trans kLb (leq_addr _ _).
- by rewrite -mul2n dvdn_add // ?dvdn_mull // mulnK ?modnDr.
- by rewrite -mul2n divnDr ?dvdn_mull // mulnK ?addnS ?addn0 /= ?negbK.
- by apply: leqnn.
- by apply: leq_trans sLi (leqnSn _).
- have bkLi : b + k < i by apply: leq_ltn_trans sLi.
  have bLi : b < i by apply: leq_ltn_trans (leq_addr _ _) bkLi.
  repeat split => //=; rewrite ?bin_of_natK.
  - by rewrite !gtn_max !leqnn !andbT ltnW // ltnW // ltnW // ltnW.
  - move=> v vPLs.
    case: eqP sLi => [->|_ _]; last exact: xH.
    by have /andP[_ vLs] := vPLs; rewrite !bin_of_natK ltnNge vLs.
  - rewrite !eval_cnf_cons !eval_cl_cons /= !bin_of_natK eqxx.
    move: bLi; rewrite ltn_neqAle eq_sym => /andP[/negPf-> _].
    move: bkLi; rewrite ltn_neqAle eq_sym => /andP[/negPf-> _].
    move: aLi; rewrite ltn_neqAle eq_sym => /andP[/negPf-> _].
    set env1 := fun j => if _ then _ else _.
    have->: eval_cnf env1 cs = eval_cnf env cs.
      apply: eval_cnf_eq => j Hj; rewrite /env1.
      have : j < i by apply: leq_ltn_trans maxH.
      by rewrite ltn_neqAle eq_sym => /andP[/negPf->].
    rewrite eH andbT !orbF.
  have bP : 0 < b by apply: leq_trans kLb.
  have Ok : k < size.+2.
    rewrite ltnW // !ltnS.
    by apply: leq_trans bkLs; case: (b) bP => //= b1 _; apply: leq_addl.
  have Obk : (b %/ k).+2 < size.+2.
    rewrite !ltnS.
    apply: leq_ltn_trans (leq_div b k) _.
    apply: leq_trans _ bkLs.
    by case: (k) kP => // k1 _; rewrite addnS leq_addr.
  have /= := Hx_ (Ordinal Obk) (Ordinal Ok).
  have FF : b %/ k <= (b %/ k).+2 by rewrite ltnW.
  rewrite (big_cat_nat _  _ _ _ FF) /=; last by rewrite divn_gt0.
  rewrite aH /= 2?big_ltn // big_geq // ?addr0.
  rewrite mulSn divnK // !xH ?[_ + b]addnC.
  - by case: (env _); case: (env _); case: (env _) => //=.
  - by rewrite bkLs (leq_trans bP) // leq_addr.
  by rewrite bP // (leq_trans _ bkLs) // leq_addr.
rewrite bin_of_natK.
rewrite eqxx -mul2n divnDr ?dvdn_mull // mulnK // !addnS addn0.
have bP : 0 < b by apply: leq_trans kLb.
have Ok : k < size.+2.
  rewrite ltnW // !ltnS.
  by apply: leq_trans bkLs; case: (b) bP => //= b1 _; apply: leq_addl.
have Obk : (b %/ k).+2 < size.+2.
  rewrite !ltnS.
  apply: leq_ltn_trans (leq_div b k) _.
  apply: leq_trans _ bkLs.
  by case: (k) kP => // k1 _; rewrite addnS leq_addr.
by apply: (key_prop (Ordinal Ok) (Ordinal Obk)) => //=; rewrite negbK.
Qed.

Lemma fgen_rec_inv m k i cs env :
  0 < k -> k + m  = size.+1 -> size < i ->
  env_inv i cs env ->
  let: (i1, cs1, env1) := fgen_rec m k i cs env in
  env_inv i1 cs1 env1.
Proof.
elim: m k i cs env => //= m IH k i cs env kP kmE sLi eH.
have := fgen_inv k size k k.*2 i cs env.
have := fgenL k size k k.*2 i cs env.
case: fgen => [[i1 cs1] env1] /= iLi HH.
apply: IH => //; first by rewrite addSnnS.
  by apply: leq_trans sLi _.
have k2E :  k.*2 %/ k = 2 by rewrite -muln2 mulKn.
have kLs : k <= size by rewrite -ltnS -kmE addnS ltnS leq_addr.
apply: HH => //.
- by rewrite -addnn leq_addr.
- by rewrite -muln2 dvdn_mulr.
- by rewrite k2E.
- by apply: leq_ltn_trans sLi.
rewrite k2E big_ltn // big_geq // mul1n addr0.
by have [_ -> //] := eH; rewrite kP.
Qed.


Lemma env_inv_rec i cs env : env_inv i cs env -> env_inv i (rev cs) env.
Proof.
move=> [H1 H2 H3]; repeat split => //.
  by rewrite max_cnf_rev.
by exact: eval_cnf_rev.
Qed.


Lemma fgen_all_inv :
  let: (i1, cs1, env1) := fgen_all in env_inv i1 cs1 env1.
Proof.
have [H1 H2] := x_z. 
rewrite /fgen_all.
have :=  fgen_rec_inv size 1 size.+1 [:: [:: + z]] (fun x : N => x_ x).
case:  fgen_rec => [[i cs] env] H.
apply: env_inv_rec.
apply: H => //; repeat split; rewrite //=.
  by apply: leqnn.
by move=> v; rewrite bin_of_natK.
Qed.

Lemma gen_all_sat :
  let (i, cs) := gen_all in exists env, eval_cnf env cs.
Proof.
have := fgen_gen_all; have := fgen_all_inv.
case: fgen_all; case: gen_all => i2 cs2 [i1 cs1] env1 [_ _ HH] [_ <-].
by exists env1.
Qed.

End Erdos.

Definition lerdos60 := snd (gen_all 1161 60).

Definition erdos60 := l2a lerdos60.


Lemma erdo60th : 
   forall rho, ~ Sat_Checker.valid (interp_var rho)  erdos.
Proof.
move=> rho.
have H := erdos60th rho.
suff ->: erdos60 = erdos60 by [].
vm_cast_no_check (refl_equal erdos60).
Time Qed.
*)

Lemma eval_erdos env : 
    eval_cnf env lerdos60 -> Sat_Checker.valid (interp_var (n2i env)) erdos60.
Proof.
move=> H.
apply: eval_cnf_valid.
have <-: lerdos60 = [seq [seq i2l i | i <- to_list l] | l <- to_list erdos60].
  native_cast_no_check (refl_equal lerdos60).
exact: H.
Time Qed.

Lemma sum_sym k d x_ : 
  (\sum_(1 <= i < k) [~~ x_ (i * d)%N] = - \sum_(1 <= i < k) [x_ (i * d)%N])%R.
Proof.
by rewrite -sumrN; apply: eq_bigr => i; case: x_.
Qed.

Lemma Erdos (x_ : nat -> bool) :
  exists k, exists d, `|(\sum_(1 <= i < k) [x_ (i * d)%N])%R| > 2.
Proof.
have [xP|xN] := boolP (x_ 60).
  have [ |Hf] := boolP [exists k : 'I_1163, exists d : 'I_1163,
               `|(\sum_(1 <= i < k) [x_ (i * d)%N])%R| > 2].
    move/existsP => [] [k Hk] /existsP [[d Hd]] HP.
    by exists k; exists d.
  have : exists env, eval_cnf env (snd (gen_all 1161 60)).
    move: (gen_all_sat 1161 x_ 60).
    case: gen_all=> a cs H.
    apply: H; rewrite ?xP // => k d.
    move: Hf; rewrite negb_exists => /forallP/(_ k).
    by rewrite negb_exists => /forallP/(_ d); rewrite -leqNgt.
  case=> env HH.
  have [] := erdos60th (n2i env).
  exact: eval_erdos.
pose xb_ x := ~~ x_ x.
  suff: exists k d : nat, 
          2 < `|(\sum_(1 <= i < k) [xb_ (i * d)%N])%R|.
    move=> [k [d Hdk]]; exists k; exists d.
    by rewrite sum_sym abszN in Hdk.
have [ |Hf] := boolP [exists k : 'I_1163, exists d : 'I_1163,
             `|(\sum_(1 <= i < k) [xb_ (i * d)%N])%R| > 2].
  move/existsP => [] [k Hk] /existsP [[d Hd]] HP.
  by exists k; exists d.
have : exists env, eval_cnf env (snd (gen_all 1161 60)).
  move: (gen_all_sat 1161 xb_ 60).
  case: gen_all=> a cs H.
  apply: H; rewrite ?xP // => k d.
  move: Hf; rewrite negb_exists => /forallP/(_ k).
  by rewrite negb_exists => /forallP/(_ d); rewrite -leqNgt.
case=> env HH.
have [] := erdos60th (n2i env).
exact: eval_erdos.
Qed.


