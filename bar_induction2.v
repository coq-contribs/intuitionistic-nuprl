(*

  Copyright 2014 Cornell University

  This file is part of VPrl (the Verified Nuprl project).

  VPrl is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  VPrl is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export approx_props3.
Require Export bar_induction.
Require Export per_props4.
Require Export cvterm4.
Require Export per_can.


(* ========================== *)

Lemma implies_equality_natk2nat {o} :
  forall lib (f g : @CTerm o) n,
    (forall m,
       m < n
       -> {k : nat
           & computes_to_valc lib (mkc_apply f (mkc_nat m)) (mkc_nat k)
           # computes_to_valc lib (mkc_apply g (mkc_nat m)) (mkc_nat k)})
    -> equality lib f g (natk2nat (mkc_nat n)).
Proof.
  introv imp.
  apply equality_in_fun; dands; eauto 3 with slow.

  { apply type_mkc_natk.
    exists (Z.of_nat n); spcast.
    apply computes_to_valc_refl; eauto 3 with slow. }

  introv e.
  apply equality_in_natk in e; exrepnd; spcast.

  eapply equality_respects_cequivc_left;
    [apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply cequivc_sym;
        apply computes_to_valc_implies_cequivc;
        exact e0]
    |].

  eapply equality_respects_cequivc_right;
    [apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply cequivc_sym;
        apply computes_to_valc_implies_cequivc;
        exact e2]
    |].

  clear dependent a.
  clear dependent a'.

  apply computes_to_valc_isvalue_eq in e3; eauto 3 with slow.
  rw @mkc_nat_eq in e3; ginv.

  assert (m < n) as ltm by omega.
  clear e1.

  apply equality_in_tnat.
  pose proof (imp m ltm) as h; exrepnd.
  exists k; dands; spcast; auto.
Qed.

Lemma implies_member_natk2nat {o} :
  forall lib (f : @CTerm o) n,
    (forall m,
       m < n
       -> {k : nat & computes_to_valc lib (mkc_apply f (mkc_nat m)) (mkc_nat k)})
    -> member lib f (natk2nat (mkc_nat n)).
Proof.
  introv imp.
  apply implies_equality_natk2nat.
  introv ltm.
  apply imp in ltm; exrepnd.
  exists k; auto.
Qed.

Lemma cequivc_nat_implies_computes_to_valc {o} :
  forall lib (t : @CTerm o) (n : nat),
    cequivc lib t (mkc_nat n)
    -> computes_to_valc lib t (mkc_nat n).
Proof.
  introv ceq.
  pose proof (cequivc_integer lib (mkc_nat n) t (Z.of_nat n)) as h.
  repeat (autodimp h hyp); eauto 3 with slow.

  { apply computes_to_valc_refl; eauto 3 with slow. }

  apply cequivc_sym; auto.
Qed.

Lemma equality_natk2nat_implies {o} :
  forall lib m (f g : @CTerm o) n,
    m < n
    -> equality lib f g (natk2nat (mkc_nat n))
    -> {k : nat
        & computes_to_valc lib (mkc_apply f (mkc_nat m)) (mkc_nat k)
        # computes_to_valc lib (mkc_apply g (mkc_nat m)) (mkc_nat k)}.
Proof.
  introv ltm mem.
  apply equality_in_fun in mem; repnd.
  clear mem0 mem1.
  pose proof (mem (mkc_nat m) (mkc_nat m)) as h; clear mem.
  autodimp h hyp.

  { apply equality_in_natk.
    exists m (Z.of_nat n); dands; spcast; try omega;
    try (apply computes_to_valc_refl; eauto 2 with slow). }

  apply equality_in_tnat in h.
  apply equality_of_nat_imp_tt in h.
  unfold equality_of_nat_tt in h; exrepnd.
  exists k; auto.
Qed.

Lemma member_natk2nat_implies {o} :
  forall lib m (f : @CTerm o) n,
    m < n
    -> member lib f (natk2nat (mkc_nat n))
    -> {k : nat & computes_to_valc lib (mkc_apply f (mkc_nat m)) (mkc_nat k)}.
Proof.
  introv ltm mem.
  eapply equality_natk2nat_implies in mem;[|exact ltm].
  exrepnd.
  exists k; auto.
Qed.

(* ========================== *)


Definition update_seq {o} (s : @CTerm o) (n m : nat) (v : NVar) :=
  mkc_lam
    v
    (mkcv_inteq
       [v]
       (mkc_var v)
       (mk_cv [v] (mkc_nat n))
       (mk_cv [v] (mkc_nat m))
       (mkcv_apply [v] (mk_cv [v] s) (mkc_var v))).

Definition const_seq {o} (n : nat) : @CTerm o := mkc_lam nvarx (mk_cv [nvarx] (mkc_nat n)).

Definition emseqc {o} : @CTerm o := const_seq 0.

Definition eq_kseq {o} lib (s1 s2 : @CTerm o) (n : nat) :=
  equality lib s1 s2 (natk2nat (mkc_nat n)).

Definition eq_seq {o} lib (s1 s2 : @CTerm o) :=
  equality lib s1 s2 nat2nat.

Lemma eq_seq_implies_eq_kseq {o} :
  forall lib (s1 s2 : @CTerm o),
    eq_seq lib s1 s2
    -> forall n, eq_kseq lib s1 s2 n.
Proof.
  introv e; introv.
  unfold eq_kseq.
  unfold eq_seq in e.
  apply equality_nat2nat_to_natk2nat; auto.
  apply nat_in_nat.
Qed.

Definition seq2kseq {o} (s : @CTerm o) (n : nat) (v : NVar) : CTerm :=
  mkc_lam
    v
    (mkcv_less
       [v]
       (mkc_var v)
       (mkcv_zero [v])
       (mkcv_bot [v])
       (mkcv_less
          [v]
          (mkc_var v)
          (mkcv_nat [v] n)
          (mkcv_apply [v] (mk_cv [v] s) (mkc_var v))
          (mkcv_bot [v]))).

Lemma mkcv_nat_substc {o} :
  forall v (t : @CTerm o) n,
    substc t v (mkcv_nat [v] n) = mkc_nat n.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma seq2kseq_prop1 {o} :
  forall lib (s1 s2 : @CTerm o) n v,
    eq_kseq lib s1 s2 n
    -> eq_kseq lib (seq2kseq s1 n v) (seq2kseq s2 n v) n.
Proof.
  introv equ.
  apply implies_equality_natk2nat.
  introv ltm.
  apply (equality_natk2nat_implies _ m) in equ; auto; exrepnd.
  exists k.
  dands.

  - apply cequivc_nat_implies_computes_to_valc.
    unfold seq2kseq.
    eapply cequivc_trans;[apply cequivc_beta|].
    allrw @mkcv_less_substc.
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @mkcv_bot_substc.
    allrw @csubst_mk_cv.
    allrw @mkcv_nat_substc.
    allrw @mkcv_zero_substc.
    allrw @mkc_zero_eq.
    eapply cequivc_trans;[apply cequivc_mkc_less_nat|].
    boolvar; try omega.
    eapply cequivc_trans;[apply cequivc_mkc_less_nat|].
    boolvar; try omega.
    apply computes_to_valc_implies_cequivc; auto.

  - apply cequivc_nat_implies_computes_to_valc.
    unfold seq2kseq.
    eapply cequivc_trans;[apply cequivc_beta|].
    allrw @mkcv_less_substc.
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @mkcv_bot_substc.
    allrw @csubst_mk_cv.
    allrw @mkcv_nat_substc.
    allrw @mkcv_zero_substc.
    allrw @mkc_zero_eq.
    eapply cequivc_trans;[apply cequivc_mkc_less_nat|].
    boolvar; try omega.
    eapply cequivc_trans;[apply cequivc_mkc_less_nat|].
    boolvar; try omega.
    apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma prog_sub_sub_keep {o} :
  forall (s : @Sub o) vs, prog_sub s -> prog_sub (sub_keep s vs).
Proof.
  induction s; introv ps; allsimpl; auto.
  destruct a; boolvar; allsimpl; auto;
  allrw @prog_sub_cons; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve prog_sub_sub_keep : slow.

Lemma in_dom_sub_sub_keep_implies {o} :
  forall (sub : @Sub o) vs v,
    LIn v (dom_sub (sub_keep sub vs))
    <=> (LIn v vs # LIn v (dom_sub sub)).
Proof.
  induction sub; split; introv i; repnd; allsimpl; tcsp.
  - boolvar; allsimpl; repndors; subst; tcsp; apply IHsub in i; sp.
  - boolvar; allsimpl; repndors; subst; tcsp.
    + right; apply IHsub; sp.
    + apply IHsub; sp.
Qed.

Definition sub_find_def {o} (sub : @Sub o) v d : NTerm :=
  match sub_find sub v with
    | Some t => t
    | None => d
  end.

Fixpoint sub_select {o} (sub : @Sub o) (vars : list NVar) (d : NTerm) : Sub :=
  match vars with
    | nil => nil
    | v :: vs => (v,sub_find_def sub v d) :: sub_select sub vs d
  end.

Lemma implies_isprog_sub_find_def {o} :
  forall (s : @Sub o) v d,
    isprog d
    -> prog_sub s
    -> isprog (sub_find_def s v d).
Proof.
  introv ispd isps.
  unfold sub_find_def.
  remember (sub_find s v) as sf; destruct sf; symmetry in Heqsf; auto.
  apply sub_find_some in Heqsf.
  rw <- @prog_sub_eq in isps.
  apply in_sub_eta in Heqsf; repnd.
  apply isps in Heqsf; eauto 3 with slow.
Qed.
Hint Resolve implies_isprog_sub_find_def : slow.

Lemma implies_closed_sub_find_def {o} :
  forall (s : @Sub o) v d,
    closed d
    -> cl_sub s
    -> closed (sub_find_def s v d).
Proof.
  introv ispd isps.
  unfold sub_find_def.
  remember (sub_find s v) as sf; destruct sf; symmetry in Heqsf; auto.
  apply sub_find_some in Heqsf.
  rw @cl_sub_eq in isps.
  apply in_sub_eta in Heqsf; repnd.
  apply isps in Heqsf; eauto 3 with slow.
Qed.
Hint Resolve implies_closed_sub_find_def : slow.

Lemma prog_sub_sub_select {o} :
  forall (s : @Sub o) d vs,
    isprog d
    -> prog_sub s
    -> prog_sub (sub_select s vs d).
Proof.
  induction vs; introv pd ps; allsimpl; eauto 3 with slow.
  apply prog_sub_cons; dands; auto.
  destruct a; boolvar; allsimpl; auto;
  allrw @prog_sub_cons; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve prog_sub_sub_select : slow.

Lemma cl_sub_sub_select {o} :
  forall (s : @Sub o) d vs,
    closed d
    -> cl_sub s
    -> cl_sub (sub_select s vs d).
Proof.
  induction vs; introv pd ps; allsimpl; eauto 3 with slow.
  apply cl_sub_cons; dands; auto.
  destruct a; boolvar; allsimpl; auto;
  allrw @cl_sub_cons; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve cl_sub_sub_select : slow.

Lemma dom_sub_sub_select {o} :
  forall (s : @Sub o) d vs,
    dom_sub (sub_select s vs d) = vs.
Proof.
  induction vs; introv; allsimpl; tcsp.
  rw IHvs; auto.
Qed.

Lemma sub_find_sub_select {o} :
  forall (s : @Sub o) vs d v,
    sub_find (sub_select s vs d) v
    = if memvar v vs
      then Some (sub_find_def s v d)
      else None.
Proof.
  induction vs; introv; simpl; auto.
  allrw memvar_cons; boolvar; tcsp.
  - rw IHvs; boolvar; tcsp.
  - rw IHvs; boolvar; tcsp.
Qed.

Definition eq_option {o} (op1 op2 : option (@NTerm o)) :=
  match op1, op2 with
    | Some t1, Some t2 => t1 = t2
    | None, None => True
    | _,_ => False
  end.

Definition ext_eq_subs {o} vs (sub1 sub2 : @Sub o) :=
  forall v,
    LIn v vs
    -> eq_option (sub_find sub1 v) (sub_find sub2 v).

Lemma eq_lsubst_aux_if_ext_eq {o} :
  forall (t : @NTerm o) sub1 sub2,
    ext_eq_subs (free_vars t) sub1 sub2
    -> disjoint (bound_vars t) (sub_free_vars sub1)
    -> disjoint (bound_vars t) (sub_free_vars sub2)
    -> lsubst_aux t sub1 = lsubst_aux t sub2.
Proof.
  nterm_ind1s t as [v|f|op bs ind] Case; introv ext d1 d2; allsimpl; auto.

  - Case "vterm".
    pose proof (ext v) as h.
    remember (sub_find sub1 v) as sf1; symmetry in Heqsf1; destruct sf1;
    remember (sub_find sub2 v) as sf2; symmetry in Heqsf2; destruct sf2;
    allsimpl; tcsp.

  - Case "oterm".
    f_equal.
    apply eq_maps; introv i.
    destruct x as [l t].
    allsimpl.
    f_equal.

    pose proof (ind t t l i) as h; clear ind.
    autodimp h hyp; eauto 3 with slow.
    apply h.

    + introv j.
      allrw @sub_find_sub_filter_eq.
      destruct (in_deq _ deq_nvar v l) as [d|d]; boolvar; tcsp; GC.
      apply ext.
      rw lin_flat_map.
      eexists; dands; eauto.
      simpl.
      rw in_remove_nvars; sp.

    + introv j k.
      pose proof (d1 t0) as q.
      autodimp q hyp.
      { rw lin_flat_map.
        eexists; dands; eauto.
        simpl.
        rw in_app_iff; sp. }
      apply subset_sub_free_vars_sub_filter in k; sp.

    + introv j k.
      pose proof (d2 t0) as q.
      autodimp q hyp.
      { rw lin_flat_map.
        eexists; dands; eauto.
        simpl.
        rw in_app_iff; sp. }
      apply subset_sub_free_vars_sub_filter in k; sp.
Qed.

Lemma cl_eq_lsubst_if_ext_eq {o} :
  forall (t : @NTerm o) sub1 sub2,
    cl_sub sub1
    -> cl_sub sub2
    -> ext_eq_subs (free_vars t) sub1 sub2
    -> lsubst t sub1 = lsubst t sub2.
Proof.
  introv cl1 cl2 ext.
  repeat unflsubst.
  apply eq_lsubst_aux_if_ext_eq; eauto 3 with slow;
  rw @sub_free_vars_if_cl_sub; auto.
Qed.

Lemma cl_lsubst_trim_select {o} :
  forall t (sub : @Sub o) lv d,
    cl_sub sub
    -> closed d
    -> (forall v, LIn v (free_vars t) -> (LIn v lv <=> LIn v (dom_sub sub)))
    -> lsubst t sub = lsubst t (sub_select sub lv d).
Proof.
  introv cls cld sv.
  apply cl_eq_lsubst_if_ext_eq; eauto 3 with slow.
  introv i.
  applydup sv in i.
  rw @sub_find_sub_select.
  unfold sub_find_def.
  boolvar.
  - applydup i0 in Heqb.
    apply in_dom_sub_exists in Heqb0; exrepnd.
    rw Heqb1; simpl; auto.
  - rw @sub_find_none_if; simpl; auto.
    intro h.
    apply i0 in h; sp.
Qed.

Definition pv_olift {o} (R : NTrel) (x y : @NTerm o) vs : [univ] :=
  forall sub: Sub,
    prog_sub sub
    -> dom_sub sub = vs
    -> R (lsubst x sub) (lsubst y sub).

Lemma cl_olift_iff_pv_olift {o} :
  forall R (x y : @NTerm o) vs,
    isprog_vars vs x
    -> isprog_vars vs y
    -> (pv_olift R x y vs <=> cl_olift R x y).
Proof.
  introv ispx ispy.
  unfold pv_olift, cl_olift.
  split; intro h; repnd; dands; eauto 3 with slow.

  - introv ps isp1 isp2.
    applydup @lsubst_program_implies in isp1.
    applydup @lsubst_program_implies in isp2.
    applydup @isprog_vars_eq in ispx; repnd.
    applydup @isprog_vars_eq in ispy; repnd.
    allrw @subvars_eq.

    pose proof (h (sub_select sub vs mk_axiom)) as q; clear h.
    rw @dom_sub_sub_select in q.
    repeat (autodimp q hyp); eauto 2 with slow.

    rw <- @cl_lsubst_trim_select in q; eauto 2 with slow;
    [|introv i;applydup isp0 in i;apply ispx1 in i; sp].

    rw <- @cl_lsubst_trim_select in q; eauto 2 with slow.
    introv i;applydup isp3 in i;apply ispy1 in i; sp.

  - introv ps e.
    apply h; auto.

    + apply isprogram_lsubst_if_isprog_sub; eauto 2 with slow.
      introv i.
      apply isprog_vars_eq in ispx; repnd.
      allrw subvars_eq.
      apply ispx0 in i; subst; sp.

    + apply isprogram_lsubst_if_isprog_sub; eauto 2 with slow.
      introv i.
      apply isprog_vars_eq in ispy; repnd.
      allrw subvars_eq.
      apply ispy0 in i; subst; sp.
Qed.

Lemma isvalue_like_lam {o} :
  forall v (t : @NTerm o), isvalue_like (mk_lam v t).
Proof.
  introv.
  unfold isvalue_like; simpl; tcsp.
Qed.
Hint Resolve isvalue_like_lam : slow.

Lemma implies_approxc_lam {o} :
  forall lib v (t1 t2 : @CVTerm o [v]),
    (forall u : CTerm, cequivc lib (substc u v t1) (substc u v t2))
    -> approxc lib (mkc_lam v t1) (mkc_lam v t2).
Proof.
  introv imp.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  allunfold @approxc; allsimpl.

  constructor.
  unfold close_comput; dands;
  try (apply isprogram_lam);
  eauto 3 with slow.

  + introv comp.
    apply computes_to_value_isvalue_eq in comp;
      try (apply isvalue_mk_lam); eauto 3 with slow.
    unfold mk_lam in comp; ginv; fold_terms.
    exists [bterm [v] x]; fold_terms.
    dands.
    { apply computes_to_value_isvalue_refl;
      try (apply isvalue_mk_lam); eauto 3 with slow. }

    unfold lblift; simpl; dands; auto.
    introv ltn.
    destruct n; try omega; clear ltn.
    unfold selectbt; simpl.
    unfold blift.
    exists [v] x0 x; dands; eauto 3 with slow.
    apply clearbots_olift.
    apply cl_olift_implies_olift; eauto 3 with slow.

    pose proof (cl_olift_iff_pv_olift (approx lib) x0 x [v]) as xx.
    repeat (autodimp xx hyp).
    apply xx; clear xx.
    introv ps e.
    destruct sub as [|p s]; allsimpl; ginv.
    destruct s; ginv.
    destruct p as [z u]; allsimpl.
    allrw @fold_subst.
    allrw @prog_sub_cons; repnd.
    pose proof (imp (mk_cterm u ps0)) as h; clear imp; allsimpl.
    destruct h; sp.

  + introv comp.
    apply can_doesnt_raise_an_exception in comp; sp.

  + introv comp.
    apply reduces_to_if_isvalue_like in comp; ginv; eauto 3 with slow.
Qed.

Lemma implies_cequivc_lam {o} :
  forall lib v (t1 t2 : @CVTerm o [v]),
    (forall u : CTerm, cequivc lib (substc u v t1) (substc u v t2))
    -> cequivc lib (mkc_lam v t1) (mkc_lam v t2).
Proof.
  introv imp.
  apply cequivc_iff_approxc; dands.
  - apply implies_approxc_lam; auto.
  - apply implies_approxc_lam; auto.
    introv.
    apply cequivc_sym; auto.
Qed.

Lemma isprog_vars_mk_less {p} :
  forall (a b c d : @NTerm p) vs,
    isprog_vars vs (mk_less a b c d)
    <=> (isprog_vars vs a
         # isprog_vars vs b
         # isprog_vars vs c
         # isprog_vars vs d).
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw remove_nvars_nil_l).
  repeat (rw app_nil_r).
  repeat (rw subvars_app_l).
  repeat (rw <- @wf_term_eq).
  allrw <- @wf_less_iff; split; sp.
Qed.

Lemma isprogram_mk_less {p} :
  forall (a b c d : @NTerm p),
    isprogram (mk_less a b c d)
    <=> (isprogram a
         # isprogram b
         # isprogram c
         # isprogram d).
Proof.
  introv.
  pose proof (isprog_vars_mk_less a b c d []) as h.
  allrw <- @isprog_vars_nil_iff_isprog.
  allrw @isprogram_eq; auto.
Qed.

Lemma implies_approxc_mkc_less1 {o} :
  forall lib (a b c d e f g : @CTerm o),
    (forall i : Z,
       computes_to_valc lib a (mkc_integer i)
       -> cequivc lib (mkc_less (mkc_integer i) b c d) (mkc_less (mkc_integer i) e f g))
    -> approxc lib (mkc_less a b c d) (mkc_less a e f g).
Proof.
  introv imp.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  allunfold @computes_to_valc; allsimpl.

  constructor.
  unfold close_comput; dands; auto;
  try (apply isprogram_mk_less; dands; eauto 3 with slow).

  + introv comp.
    apply computes_to_value_mk_less in comp; eauto 3 with slow; exrepnd.

    pose proof (imp k1) as h; clear imp.
    autodimp h hyp.
    { split; eauto 3 with slow. }
    destruct h as [h1 h2]; clear h2.
    inversion h1 as [cl]; clear h1.
    unfold close_comput in cl; repnd.

    pose proof (cl2 c tl_subterms) as h.
    autodimp h hyp.

    * split;[|allunfold @computes_to_value; sp];[].
      eapply reduces_to_trans;
        [apply reduce_to_prinargs_comp;
          [apply computes_to_value_isvalue_refl;eauto 3 with slow
          |eauto 3 with slow
          |exact comp2]
        |].
      repndors; repnd; allunfold @computes_to_value; repnd.

      { eapply reduces_to_if_split2;[|exact comp4].
        csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl.
        boolvar;try omega;auto. }

      { eapply reduces_to_if_split2;[|exact comp4].
        csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl.
        boolvar;try omega;auto. }

    * exrepnd.
      exists tr_subterms; dands; auto.

      allunfold @computes_to_value; repnd.
      split; tcsp.
      eapply reduces_to_trans;[apply reduces_to_prinarg;exact comp0|].
      auto.

  + introv comp.
    apply computes_to_exception_mk_less in comp; eauto 3 with slow.
    repndors; exrepnd.

    * pose proof (imp k1) as h; clear imp.
      autodimp h hyp.
      { split; eauto 3 with slow. }
      destruct h as [h1 h2]; clear h2.
      inversion h1 as [cl]; clear h1.
      unfold close_comput in cl; repnd.

      pose proof (cl3 a e) as h.
      autodimp h hyp.

      { eapply reduces_to_trans;
        [apply reduce_to_prinargs_comp;
          [apply computes_to_value_isvalue_refl;eauto 3 with slow
          |eauto 3 with slow
          |exact comp2]
        |].
        repndors; repnd.

        { eapply reduces_to_if_split2;[|exact comp1].
          csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl.
          boolvar;try omega;auto. }

        { eapply reduces_to_if_split2;[|exact comp1].
          csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl.
          boolvar;try omega;auto. }
      }

      { exrepnd.
        exists a' e'; dands; auto.

        eapply reduces_to_trans;[apply reduces_to_prinarg;exact comp0|].
        auto.
      }

    * applydup @preserve_program_exc2 in comp; eauto 3 with slow; repnd.
      exists a e; dands; eauto 3 with slow;
      try (left; apply approx_refl; eauto 3 with slow).
      eapply reduces_to_trans;[apply reduces_to_prinarg;exact comp|].
      apply reduces_to_if_step.
      csunf; simpl; auto.

    * applydup @preserve_program_exc2 in comp0; eauto 3 with slow; repnd.

      pose proof (imp z) as h; clear imp.
      autodimp h hyp.
      { split; eauto 3 with slow. }
      destruct h as [h1 h2]; clear h2.
      inversion h1 as [cl]; clear h1.
      unfold close_comput in cl; repnd.

      pose proof (cl3 a e) as h.
      autodimp h hyp.

      { eapply reduces_to_trans;
        [apply reduce_to_prinargs_comp;
          [apply computes_to_value_isvalue_refl;eauto 3 with slow
          |eauto 3 with slow
          |exact comp0]
        |]; fold_terms.
        apply reduces_to_if_step.
        csunf; simpl; dcwf h; simpl; auto.
      }

      { exrepnd.
        exists a' e'; dands; auto.

        eapply reduces_to_trans;[apply reduces_to_prinarg;exact comp1|].
        auto.
      }

  + introv comp; allsimpl.
    apply computes_to_seq_implies_computes_to_value in comp;
      [|apply isprogram_mk_less; dands; eauto 3 with slow].
    applydup @computes_to_value_mk_less in comp; exrepnd; eauto 3 with slow.

    pose proof (imp k1) as h; autodimp h hyp.
    { split; dands; eauto 3 with slow. }

    destruct h as [h1 h2]; clear h2.
    inversion h1 as [cl]; clear h1.
    unfold close_comput in cl; repnd; GC.
    clear cl2 cl3.

    pose proof (cl4 f) as h.
    autodimp h hyp.

    * eapply reduces_to_trans;
        [apply reduce_to_prinargs_comp;
          [apply computes_to_value_isvalue_refl;eauto 3 with slow
          |eauto 3 with slow
          |exact comp2]
        |].
      repndors; repnd; allunfold @computes_to_value; repnd.

      { eapply reduces_to_if_split2;[|exact comp4].
        csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl.
        boolvar;try omega;auto. }

      { eapply reduces_to_if_split2;[|exact comp4].
        csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl.
        boolvar;try omega;auto. }

    * exrepnd.
      exists f'; dands; auto.

      eapply reduces_to_trans;[apply reduces_to_prinarg;exact comp1|].
      auto.
Qed.

Lemma implies_cequivc_mkc_less1 {o} :
  forall lib (a b c d e f g : @CTerm o),
    (forall i : Z,
       computes_to_valc lib a (mkc_integer i)
       -> cequivc lib (mkc_less (mkc_integer i) b c d) (mkc_less (mkc_integer i) e f g))
    -> cequivc lib (mkc_less a b c d) (mkc_less a e f g).
Proof.
  introv imp.
  apply cequivc_iff_approxc; dands.
  - apply implies_approxc_mkc_less1; auto.
  - apply implies_approxc_mkc_less1; auto.
    introv comp.
    apply cequivc_sym; auto.
Qed.

Lemma seq2kseq_prop2 {o} :
  forall lib v (s1 s2 : @CTerm o) n,
    eq_kseq lib s1 s2 n
    -> cequivc lib (seq2kseq s1 n v) (seq2kseq s2 n v).
Proof.
  introv equ.
  apply implies_cequivc_lam.
  introv.
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @mkcv_bot_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_nat_substc.
  allrw @mkcv_zero_substc.

  apply implies_cequivc_mkc_less1.
  introv compu.
  allrw @mkc_zero_eq.
  allrw (@mkc_nat_eq o 0).

  eapply cequivc_trans;[apply cequivc_mkc_less_int|].
  eapply cequivc_trans;[|apply cequivc_sym;apply cequivc_mkc_less_int].
  boolvar; auto.

  eapply cequivc_trans;
    [apply cequivc_mkc_less;
      [apply computes_to_valc_implies_cequivc;exact compu
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl]
    |].

  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_mkc_less;
      [apply computes_to_valc_implies_cequivc;exact compu
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl]
    ].

  apply Wf_Z.Z_of_nat_complete_inf in l; exrepnd; subst; fold_terms.
  allrw <- @mkc_nat_eq.

  eapply cequivc_trans;[apply cequivc_mkc_less_nat|].
  eapply cequivc_trans;[|apply cequivc_sym;apply cequivc_mkc_less_nat].

  boolvar; auto.

  eapply cequivc_trans;
    [apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply computes_to_valc_implies_cequivc;exact compu]
    |].

  eapply cequivc_trans;
    [|apply cequivc_sym;apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply computes_to_valc_implies_cequivc;exact compu]
    ].

  apply (equality_natk2nat_implies _ n0) in equ; auto.
  exrepnd.
  eapply cequivc_trans;
    [apply computes_to_valc_implies_cequivc;exact equ1
    |apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact equ0].
Qed.

Definition is_kseq {o} lib (s : @CTerm o) (n : nat) := eq_kseq lib s s n.

Definition is_seq {o} lib (s : @CTerm o) := member lib s nat2nat.

Definition barind_meta_dec {o} lib (B : @CTerm o) :=
  forall (n : nat) (s : CTerm),
    is_kseq lib s n
    -> inhabited_type
         lib
         (mkc_or
            (mkc_apply2 B (mkc_nat n) s)
            (mkc_not (mkc_apply2 B (mkc_nat n) s))).

Definition meta_on_seq {o} lib (A : @CTerm o) (n : nat) (s : CTerm) :=
  inhabited_type lib (mkc_apply2 A (mkc_nat n) s).

Definition barind_meta_bar {o} lib (B : @CTerm o) :=
  forall (s : CTerm),
    is_seq lib s
    -> {m : nat , meta_on_seq lib B m s }.

Definition barind_meta_imp {o} lib (B X : @CTerm o) :=
  forall (n : nat) (s : CTerm),
    is_kseq lib s n
    -> meta_on_seq lib B n s
    -> meta_on_seq lib X n s.

Definition meta_on_upd_seq {o} lib (X s : @CTerm o) (n m : nat) (v : NVar) :=
  meta_on_seq lib X (S n) (update_seq s n m v).

Definition barind_meta_ind {o} lib (X : @CTerm o) v :=
  forall (n : nat) (s : CTerm),
    is_kseq lib s n
    -> (forall (m : nat), meta_on_upd_seq lib X s n m v)
    -> meta_on_seq lib X n s.

Definition barind_meta_ind_cont {o} lib (X : @CTerm o) v :=
  forall (n : nat) (s : CTerm),
    is_kseq lib s n
    -> !meta_on_seq lib X n s
    -> {m : nat , !meta_on_upd_seq lib X s n m v}.

Definition meta_seq_NA {o} lib (X : @CTerm o) :=
  {n : nat
   & {s : CTerm
   & is_kseq lib s n
   # !meta_on_seq lib X n s }}.

Definition mk_meta_seq_NA {o} {lib} {X : @CTerm o}
           (n : nat)
           (s : CTerm)
           (i : is_kseq lib s n)
           (p : !meta_on_seq lib X n s) : meta_seq_NA lib X :=
  existT _ n (existT _ s (i,p)).

Definition meta_seq_NA_nat {o} {lib} {X : @CTerm o} (x : meta_seq_NA lib X) : nat :=
  projT1 x.

Definition meta_seq_NA_seq {o} {lib} {X : @CTerm o} (x : meta_seq_NA lib X) : CTerm :=
  match x with
    | existT _ (existT s _) => s
  end.

Definition barind_meta_ind_cont2 {o} lib (X : @CTerm o) v :=
  forall (x : meta_seq_NA lib X),
    {m : nat
     , !meta_on_upd_seq lib X (meta_seq_NA_seq x) (meta_seq_NA_nat x) m v}.

Definition barind_meta_ind_cont2_2 {o} lib (X : @CTerm o) v :=
  forall (x : meta_seq_NA lib X),
    {m : nat
     | !meta_on_upd_seq lib X (meta_seq_NA_seq x) (meta_seq_NA_nat x) m v}.

Definition barind_meta_ind_cont3 {o} lib (X : @CTerm o) v :=
  {f : meta_seq_NA lib X -> nat
   , forall a : meta_seq_NA lib X,
       !meta_on_upd_seq lib X (meta_seq_NA_seq a) (meta_seq_NA_nat a) (f a) v}.

Lemma barind_meta_ind_implies_cont {o} :
  forall lib (X : @CTerm o) v,
    barind_meta_ind lib X v
    -> barind_meta_ind_cont lib X v.
Proof.
  introv ind mem ni.
  pose proof (ind n s mem) as h; clear ind.
  apply contraposition in h; auto.
  (* We use Markov's principle *)
  apply not_all_ex_not in h; auto.
Qed.

Lemma barind_meta_ind_cont_implies_cont2 {o} :
  forall lib (X : @CTerm o) v,
    barind_meta_ind_cont lib X v
    -> barind_meta_ind_cont2 lib X v.
Proof.
  introv ind; introv.
  unfold meta_seq_NA in x; exrepnd.
  pose proof (ind n s x0 x1) as h; clear ind.
  simpl; auto.
Qed.

Lemma barind_meta_ind_cont_implies_cont2_2 {o} :
  forall lib (X : @CTerm o) v,
    barind_meta_ind_cont lib X v
    -> barind_meta_ind_cont2_2 lib X v.
Proof.
  introv ind; introv.
  unfold meta_seq_NA in x; exrepnd; simpl.
  pose proof (ind n s x0 x1) as h; clear ind.
(*  pose proof (classic {m : nat | !meta_on_upd_seq lib X s n m v}) as ni. *)
Abort.

Lemma barind_meta_ind_cont2_implies_cont3 {o} :
  forall lib (X : @CTerm o) v,
    barind_meta_ind_cont2 lib X v
    -> barind_meta_ind_cont3 lib X v.
Proof.
  introv ind; introv.
  unfold barind_meta_ind_cont2 in ind.
  apply FunctionalChoice_on in ind; auto.
Qed.

Definition meta_kseq_at_is {o} lib (s : @CTerm o) (n m : nat) :=
  cequivc lib (mkc_apply s (mkc_nat n)) (mkc_nat m).

Definition meta_kseq_NA {o} lib (n : nat) (A : @CTerm o) :=
  {m : nat
   & {s : CTerm
   & is_kseq lib s (S n)
   # meta_kseq_at_is lib s n m
   # !meta_on_seq lib A (S n) s }}.

Definition mk_meta_kseq_NA {o} {lib} {n : nat} {A : @CTerm o}
           (m : nat)
           (s : CTerm)
           (i : is_kseq lib s (S n))
           (e : meta_kseq_at_is lib s n m)
           (p : !meta_on_seq lib A (S n) s) : meta_kseq_NA lib n A :=
  existT _ m (existT _ s (i,(e,p))).

Definition meta_kseq_NA_nat {o} {lib} {n : nat} {A : @CTerm o}
           (x : meta_kseq_NA lib n A) : nat:=
  match x with
    | existT m _ => m
  end.

Definition meta_kseq_NA_seq {o} {lib} {n : nat} {A : @CTerm o}
           (x : meta_kseq_NA lib n A) : CTerm:=
  match x with
    | existT _ (existT s _) => s
  end.

Lemma eq_kseq_0 {o} :
  forall lib (s1 s2 : @CTerm o),
    eq_kseq lib s1 s2 0.
Proof.
  introv.
  unfold eq_kseq, natk2nat.
  apply equality_in_fun; dands; eauto 3 with slow.

  { apply type_mkc_natk.
    exists 0%Z; spcast.
    apply computes_to_valc_refl; eauto 3 with slow. }

  introv e.
  apply equality_in_natk in e; exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in e3; eauto 3 with slow.
  allrw @mkc_nat_eq; ginv; omega.
Qed.

Lemma is_kseq_0 {o} : forall lib (t : @CTerm o), is_kseq lib t 0.
Proof.
  introv.
  apply eq_kseq_0.
Qed.

Lemma meta_kseq_at_is_update {o} :
  forall lib (s : @CTerm o) (n m : nat) (v : NVar),
    meta_kseq_at_is lib (update_seq s n m v) n m.
Proof.
  introv.
  unfold meta_kseq_at_is, update_seq.
  eapply cequivc_trans;[apply cequivc_beta|].
  allrw @mkcv_inteq_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @csubst_mk_cv.
  eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
  boolvar; tcsp; GC.
Qed.

Lemma eq_kseq_update {o} :
  forall lib (s1 s2 : @CTerm o) (n m : nat) (v : NVar),
    eq_kseq lib s1 s2 n
    -> eq_kseq lib (update_seq s1 n m v) (update_seq s2 n m v) (S n).
Proof.
  introv i.
  allunfold @eq_kseq.
  unfold update_seq.
  apply implies_equality_natk2nat.
  introv ltm0.

  destruct (deq_nat m0 n) as [d|d]; subst.

  - exists m.
    dands.

    + apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; tcsp.

    + apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; tcsp.

  - pose proof (equality_natk2nat_implies lib m0 s1 s2 n) as h.
    repeat (autodimp h hyp); try omega.
    exrepnd.
    exists k.
    dands.

    + apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; tcsp; GC.
      apply computes_to_valc_implies_cequivc; auto.

    + apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; tcsp; GC.
      apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma is_kseq_update {o} :
  forall lib (s : @CTerm o) (n m : nat) (v : NVar),
    is_kseq lib s n
    -> is_kseq lib (update_seq s n m v) (S n).
Proof.
  introv i.
  apply eq_kseq_update; auto.
Qed.

Lemma eq_kseq_implies {o} :
  forall lib m (s1 s2 : @CTerm o) n,
    m < n
    -> eq_kseq lib s1 s2 n
    -> {k : nat
        & computes_to_valc lib (mkc_apply s1 (mkc_nat m)) (mkc_nat k)
        # computes_to_valc lib (mkc_apply s2 (mkc_nat m)) (mkc_nat k)}.
Proof.
  introv ltm i.
  unfold eq_kseq in i.
  eapply equality_natk2nat_implies in i;[|exact ltm]; auto.
Qed.

Lemma is_kseq_implies {o} :
  forall lib m (s : @CTerm o) n,
    m < n
    -> is_kseq lib s n
    -> {k : nat & computes_to_valc lib (mkc_apply s (mkc_nat m)) (mkc_nat k)}.
Proof.
  introv ltm i.
  unfold is_kseq in i.
  eapply member_natk2nat_implies in i;[|exact ltm]; auto.
Qed.

Lemma meta_kseq_NA_seq_mk_meta_kseq_NA {o} :
  forall lib n (A : @CTerm o) m s i e p,
    meta_kseq_NA_seq (@mk_meta_kseq_NA o lib n A m s i e p) = s.
Proof. sp. Qed.

Fixpoint malpha {o}
         (lib : library)
         (X c : @CTerm o)
         (v : NVar)
         (h : !meta_on_seq lib X 0 c)
         (f : meta_seq_NA lib X -> nat)
         (ind : forall a : meta_seq_NA lib X,
                  !meta_on_upd_seq lib X (meta_seq_NA_seq a) (meta_seq_NA_nat a) (f a) v)
         (n : nat) : meta_kseq_NA lib n X :=
  match n with
    | 0 =>
      let i := is_kseq_0 lib c in
      let p := mk_meta_seq_NA 0 c i h in
      let k := f p in
      mk_meta_kseq_NA
        k
        (update_seq c 0 k v)
        (is_kseq_update lib c 0 k v i)
        (meta_kseq_at_is_update lib c 0 k v)
        (ind p)
    | S m =>
      let (_,r) := malpha lib X c v h f ind m in
      let (s,r) := r in
      let (i,r) := r in
      let (_,na) := r in
      let p := mk_meta_seq_NA (S m) s i na in
      let k := f p in
      mk_meta_kseq_NA
        k
        (update_seq s (S m) k v)
        (is_kseq_update lib s (S m) k v i)
        (meta_kseq_at_is_update lib s (S m) k v)
        (ind p)
  end.

Lemma malpha_prop1 {o} :
  forall lib
         (X c : @CTerm o)
         (v : NVar)
         (h : !meta_on_seq lib X 0 c)
         (f : meta_seq_NA lib X -> nat)
         (ind : forall a : meta_seq_NA lib X,
                  !meta_on_upd_seq lib X (meta_seq_NA_seq a) (meta_seq_NA_nat a) (f a) v)
         (n m : nat)
         (lemn : m <= n),
    equality
      lib
      (meta_kseq_NA_seq (malpha lib X c v h f ind n))
      (meta_kseq_NA_seq (malpha lib X c v h f ind m))
      (natk2nat (mkc_nat m)).
Proof.
  introv lemn.
  assert {k : nat & n = k + m} as e.
  { exists (n - m); omega. }
  exrepnd; subst.
  clear lemn.
  induction k; introv; allsimpl; apply implies_equality_natk2nat; introv ltm0.

  - remember (malpha lib X c v h f ind m) as am.
    unfold meta_kseq_NA in am; exrepnd; allsimpl.

    dup am0 as i.
    apply (is_kseq_implies lib m0) in i; try omega; exrepnd.
    exists k; dands; auto.

  - remember (malpha lib X c v h f ind (k + m)) as am.
    unfold meta_kseq_NA in am; exrepnd; simphyps.
    rw @meta_kseq_NA_seq_mk_meta_kseq_NA.

    eapply equality_natk2nat_implies in IHk;[|exact ltm0].
    exrepnd.
    exists k0; dands; auto.

    unfold update_seq.
    apply cequivc_nat_implies_computes_to_valc.
    eapply cequivc_trans;[apply cequivc_beta|].
    allrw @mkcv_inteq_substc.
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @csubst_mk_cv.
    eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
    boolvar; tcsp; GC; try omega.
    apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma cequivc_beta_nseq {o} :
  forall (lib : @library o) s n,
    cequivc lib (mkc_apply (mkc_nseq s) (mkc_nat n)) (mkc_nat (s n)).
Proof.
  introv.
  unfold cequivc; simpl.
  apply reduces_to_implies_cequiv;
    [apply isprogram_apply;eauto 3 with slow;apply isprogram_mk_nseq|].
  eapply reduces_to_if_split2;[csunf;simpl;auto|].
  apply reduces_to_if_step; csunf; simpl.
  boolvar; try omega.
  rw Znat.Nat2Z.id; auto.
Qed.

Lemma is_seq_nseq {o} :
  forall (lib : @library o) s, is_seq lib (mkc_nseq s).
Proof.
  introv.
  apply member_nseq_nat2nat.
Qed.
Hint Resolve is_seq_nseq : slow.

Lemma eq_seq_nseq {o} :
  forall (lib : @library o) s, eq_seq lib (mkc_nseq s) (mkc_nseq s).
Proof.
  introv.
  apply member_nseq_nat2nat.
Qed.
Hint Resolve eq_seq_nseq : slow.

Lemma is_kseq_nseq {o} :
  forall (lib : @library o) s n, is_kseq lib (mkc_nseq s) n.
Proof.
  introv.
  pose proof (is_seq_nseq lib s) as h.
  apply equality_nat2nat_to_natk2nat; auto.
  apply nat_in_nat.
Qed.
Hint Resolve is_kseq_nseq : slow.

Definition barind_meta_fun_n {o} lib (A : @CTerm o) (n : nat) :=
  forall s1 s2,
    eq_kseq lib s1 s2 n
    -> tequality lib (mkc_apply2 A (mkc_nat n) s1) (mkc_apply2 A (mkc_nat n) s2).

Definition barind_meta_fun {o} lib (A : @CTerm o) :=
  forall (n : nat), barind_meta_fun_n lib A n.

Lemma meta_on_seq_eq_kseq {o} :
  forall lib (A : @CTerm o) n s1 s2,
    eq_kseq lib s1 s2 n
    -> barind_meta_fun_n lib A n
    -> meta_on_seq lib A n s1
    -> meta_on_seq lib A n s2.
Proof.
  introv e f h.
  allunfold @meta_on_seq.
  apply f in e.
  eapply inhabited_type_tequality; eauto.
Qed.

Lemma not_meta_on_seq_eq_kseq {o} :
  forall lib (A : @CTerm o) n s1 s2,
    eq_kseq lib s1 s2 n
    -> barind_meta_fun_n lib A n
    -> !meta_on_seq lib A n s1
    -> !meta_on_seq lib A n s2.
Proof.
  introv e f h m; destruct h.
  eapply meta_on_seq_eq_kseq;[|auto|exact m].
  apply equality_sym; auto.
Qed.

(* in [barind_true_classically], [c] is [emseqc]*)
Lemma bar_induction_meta {o} :
  forall lib (B X c : @CTerm o) v,
    barind_meta_fun lib X
    -> barind_meta_bar lib B
    -> barind_meta_imp lib B X
    -> barind_meta_ind lib X v
    -> meta_on_seq lib X 0 c.
Proof.
  introv func bar imp ind.
  pose proof (classic (meta_on_seq lib X 0 c)) as ni.
  repndors; auto.
  provefalse.

  apply barind_meta_ind_implies_cont in ind.
  apply barind_meta_ind_cont_implies_cont2 in ind.
  apply barind_meta_ind_cont2_implies_cont3 in ind.
  unfold barind_meta_ind_cont3 in ind; exrepnd.
  rename ind0 into ind.

  remember (malpha lib X c v ni f ind) as g.
  remember (fun m => meta_kseq_NA_nat (g m)) as s.

  assert (forall n, eq_kseq lib (mkc_nseq s) (meta_kseq_NA_seq (g n)) n) as e.
  { introv.
    apply implies_equality_natk2nat; introv ltm.
    subst.
    exists (meta_kseq_NA_nat (malpha lib X c v ni f ind m)).
    dands.

    - apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta_nseq|].
      simpl; auto.

    - pose proof (malpha_prop1 lib X c v ni f ind n (S m)) as q.
      autodimp q hyp; try omega.
      apply (equality_natk2nat_implies lib m) in q; try omega.
      exrepnd.

      apply cequivc_nat_implies_computes_to_valc.
      apply computes_to_valc_implies_cequivc in q1.
      apply computes_to_valc_implies_cequivc in q0.

      apply cequivc_sym in q1.
      eapply cequivc_trans in q1;[|exact q0].
      clear q0.
      eapply cequivc_trans;[apply cequivc_sym;exact q1|].
      clear q1.
      simpl.

      remember (malpha lib X c v ni f ind m) as am.
      unfold meta_kseq_NA in am; exrepnd; simphyps.
      rw @meta_kseq_NA_seq_mk_meta_kseq_NA.
      unfold update_seq.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; auto; try omega.
  }

  pose proof (bar (mkc_nseq s)) as b.
  autodimp b hyp; eauto 3 with slow.
  exrepnd.
  rename b0 into b.

  apply imp in b; eauto 3 with slow.

  induction m; allsimpl.

  { pose proof (eq_kseq_0 lib (mkc_nseq s) c) as h.
    eapply meta_on_seq_eq_kseq in b;[|exact h|auto]; sp. }

  pose proof (e (S m)) as q1.
  eapply meta_on_seq_eq_kseq in b;[|exact q1|auto].
  pose proof (e m) as q2.
  eapply not_meta_on_seq_eq_kseq in IHm;[|exact q2|auto].
  clear q1 q2 e.

  subst; allsimpl.
  remember (malpha lib X c v ni f ind m) as am.
  unfold meta_kseq_NA in am; exrepnd; allsimpl.

  assert (eq_kseq lib (update_seq s (S m) (f (mk_meta_seq_NA (S m) s am0 am1)) v) s (S m)) as ee.
  { unfold eq_kseq.
    apply implies_equality_natk2nat; introv ltm1.
    dup am0 as e.
    unfold is_kseq, eq_kseq in e.
    eapply member_natk2nat_implies in e;[|exact ltm1]; exrepnd.
    exists k; dands; auto.
    unfold update_seq.
    apply cequivc_nat_implies_computes_to_valc.
    eapply cequivc_trans;[apply cequivc_beta|].
    allrw @mkcv_inteq_substc.
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @csubst_mk_cv.
    eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
    boolvar; tcsp; GC; try omega.
    apply computes_to_valc_implies_cequivc; auto.
  }

  eapply meta_on_seq_eq_kseq in b;[|exact ee|auto].
  sp.
Qed.

Lemma cequivc_preserves_meta_on_seq {o} :
  forall lib (A : @CTerm o) n s1 s2,
    cequivc lib s1 s2
    -> meta_on_seq lib A n s1
    -> meta_on_seq lib A n s2.
Proof.
  introv ceq m.
  allunfold @meta_on_seq.
  eapply inhabited_type_cequivc;[|exact m].
  apply implies_cequivc_apply2; auto.
Qed.

Lemma implies_is_kseq_seq2kseq {o} :
  forall lib (s : @CTerm o) m v,
    is_kseq lib s m
    -> is_kseq lib (seq2kseq s m v) m.
Proof.
  introv i.
  apply seq2kseq_prop1; auto.
Qed.

Lemma cequivc_preserves_not_meta_on_seq {o} :
  forall lib (A : @CTerm o) n s1 s2,
    cequivc lib s1 s2
    -> !meta_on_seq lib A n s1
    -> !meta_on_seq lib A n s2.
Proof.
  introv ceq nm m.
  allunfold @meta_on_seq.
  destruct nm.
  eapply inhabited_type_cequivc;[|exact m].
  apply cequivc_sym.
  apply implies_cequivc_apply2; auto.
Qed.

Definition barind_meta_bar2 {o} lib (B : @CTerm o) v :=
  forall (s : CTerm),
    is_seq lib s
    -> {m : nat , meta_on_seq lib B m (seq2kseq s m v) }.

Definition seq_normalizable {o} lib (s : @CTerm o) n v :=
  cequivc lib s (seq2kseq s n v).

Definition meta_kseq_NA2 {o} lib (n : nat) (A : @CTerm o) v :=
  {m : nat
   & {s : CTerm
   & is_kseq lib s (S n)
   # seq_normalizable lib s (S n) v
   # meta_kseq_at_is lib s n m
   # !meta_on_seq lib A (S n) s }}.

Definition mk_meta_kseq_NA2 {o} {lib} {n : nat} {A : @CTerm o} {v}
           (m : nat)
           (s : CTerm)
           (i : is_kseq lib s (S n))
           (q : seq_normalizable lib s (S n) v)
           (e : meta_kseq_at_is lib s n m)
           (p : !meta_on_seq lib A (S n) s) : meta_kseq_NA2 lib n A v :=
  existT _ m (existT _ s (i,(q,(e,p)))).

Definition meta_kseq_NA2_nat {o} {lib} {n : nat} {A : @CTerm o} {v}
           (x : meta_kseq_NA2 lib n A v) : nat:=
  match x with
    | existT m _ => m
  end.

Definition meta_kseq_NA2_seq {o} {lib} {n : nat} {A : @CTerm o} {v}
           (x : meta_kseq_NA2 lib n A v) : CTerm:=
  match x with
    | existT _ (existT s _) => s
  end.

Lemma cequivc_seq2kseq_twice {o} :
  forall lib (s : @CTerm o) n v,
    cequivc lib (seq2kseq s n v) (seq2kseq (seq2kseq s n v) n v).
Proof.
  introv.
  unfold seq2kseq.

  apply implies_cequivc_lam.
  introv.
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @mkcv_bot_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_nat_substc.
  allrw @mkcv_zero_substc.

  apply implies_cequivc_mkc_less1.
  introv compu.
  allrw @mkc_zero_eq.
  allrw (@mkc_nat_eq o 0).

  eapply cequivc_trans;[apply cequivc_mkc_less_int|].
  eapply cequivc_trans;[|apply cequivc_sym;apply cequivc_mkc_less_int].
  boolvar; auto.

  eapply cequivc_trans;
    [apply cequivc_mkc_less;
      [apply computes_to_valc_implies_cequivc;exact compu
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl]
    |].

  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_mkc_less;
      [apply computes_to_valc_implies_cequivc;exact compu
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl]
    ].

  apply Wf_Z.Z_of_nat_complete_inf in l; exrepnd; subst; fold_terms.
  allrw <- @mkc_nat_eq.

  eapply cequivc_trans;[apply cequivc_mkc_less_nat|].
  eapply cequivc_trans;[|apply cequivc_sym;apply cequivc_mkc_less_nat].

  boolvar; auto.

  eapply cequivc_trans;
    [apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply computes_to_valc_implies_cequivc;exact compu]
    |].

  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_beta].
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @mkcv_bot_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_nat_substc.
  allrw @mkcv_zero_substc.

  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_mkc_less;
      [apply computes_to_valc_implies_cequivc;exact compu
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_mkc_less;
        [apply computes_to_valc_implies_cequivc;exact compu
        |apply cequivc_refl
        |apply cequivc_refl
        |apply cequivc_refl]
      ]
    ].

  allrw @mkc_zero_eq.

  eapply cequivc_trans;[|apply cequivc_sym;apply cequivc_mkc_less_nat].
  boolvar; auto; try omega.
  eapply cequivc_trans;[|apply cequivc_sym;apply cequivc_mkc_less_nat].
  boolvar; auto; try omega.

  eapply cequivc_trans;
    [|apply cequivc_sym;apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply computes_to_valc_implies_cequivc;exact compu]
    ].
  auto.
Qed.

Lemma computes_to_value_mk_int_eq {o} :
  forall lib (a b c d v : @NTerm o),
    wf_term a
    -> wf_term b
    -> wf_term c
    -> wf_term d
    -> computes_to_value lib (mk_int_eq a b c d) v
    -> {pk1 : param_kind
        & {pk2 : param_kind
        & reduces_to lib a (pk2term pk1)
        # reduces_to lib b (pk2term pk2)
        # ((pk1 = pk2 # computes_to_value lib c v)
           [+]
           (pk1 <> pk2 # computes_to_value lib d v)
          )}}.
Proof.
  introv wfa wfb wfc wfd hv.
  unfold computes_to_value in hv; repnd.
  unfold reduces_to in hv0; exrepnd.
  pose proof (computes_to_val_like_in_max_k_steps_comp_implies
                lib k CompOpEq a b c d v) as h.
  repeat (autodimp h hyp).
  { unfold computes_to_val_like_in_max_k_steps; dands; eauto with slow. }

  repndors; exrepnd; repndors; exrepnd; ginv.

  - allunfold @spcan; fold_terms.
    allunfold @computes_to_can_in_max_k_steps; repnd.
    exists pk1 pk2; dands; eauto with slow.
    boolvar; subst.
    + left; dands; auto.
      allunfold @computes_to_val_like_in_max_k_steps; repnd.
      unfold computes_to_value; dands; auto.
      exists (k - (k1 + k2 + 1)); auto.
    + right; dands; auto.
      allunfold @computes_to_val_like_in_max_k_steps; repnd.
      unfold computes_to_value; dands; auto.
      exists (k - (k1 + k2 + 1)); auto.

  - provefalse; subst; inversion hv; allsimpl; tcsp.

  - provefalse; subst; inversion hv; allsimpl; tcsp.
Qed.

Lemma approx_pk2term_implies_reduces_to {o} :
  forall lib pk (t : @NTerm o),
    approx lib (pk2term pk) t
    -> reduces_to lib t (pk2term pk).
Proof.
  introv ap.
  destruct ap as [c].
  unfold close_comput in c; repnd.
  destruct pk; allsimpl.

  - pose proof (c2 (NTok s) []) as h; fold_terms.
    autodimp h hyp.
    { apply computes_to_value_isvalue_refl; eauto with slow. }
    exrepnd.
    unfold lblift in h0; allsimpl; repnd; cpx; fold_terms.
    unfold computes_to_value in h1; repnd; auto.

  - pose proof (c2 (NUTok g) []) as h; fold_terms.
    autodimp h hyp.
    { apply computes_to_value_isvalue_refl; eauto with slow. }
    exrepnd.
    unfold lblift in h0; allsimpl; repnd; cpx; fold_terms.
    unfold computes_to_value in h1; repnd; auto.

  - pose proof (c2 (Nint z) []) as h; fold_terms.
    autodimp h hyp.
    { apply computes_to_value_isvalue_refl; eauto with slow. }
    exrepnd.
    unfold lblift in h0; allsimpl; repnd; cpx; fold_terms.
    unfold computes_to_value in h1; repnd; auto.
Qed.

Lemma computes_to_exception_mk_int_eq {o} :
  forall lib (a b c d : @NTerm o) n e,
    wf_term a
    -> wf_term b
    -> wf_term c
    -> wf_term d
    -> computes_to_exception lib n (mk_int_eq a b c d) e
    -> {pk1 : param_kind
        & {pk2 : param_kind
        & reduces_to lib a (pk2term pk1)
        # reduces_to lib b (pk2term pk2)
        # ((pk1 = pk2 # computes_to_exception lib n c e)
           [+]
           (pk2 <> pk1 # computes_to_exception lib n d e)
          )}}
       [+] computes_to_exception lib n a e
       [+] {pk : param_kind
            & reduces_to lib a (pk2term pk)
            # computes_to_exception lib n b e}.
Proof.
  introv wfa wfb wfc wfd comp.
  unfold computes_to_exception, reduces_to in comp; exrepnd.
  pose proof (computes_to_val_like_in_max_k_steps_comp_implies
                lib k CompOpEq a b c d (mk_exception n e)) as h.
  repeat (autodimp h hyp).
  { unfold computes_to_val_like_in_max_k_steps; dands; eauto 3 with slow. }

  repndors; exrepnd; repndors; exrepnd; ginv.

  - left.
    allunfold @computes_to_can_in_max_k_steps; repnd.
    allunfold @spcan; fold_terms.
    exists pk1 pk2; dands; eauto with slow.
    boolvar;[left|right]; dands; auto;
    allunfold @computes_to_val_like_in_max_k_steps; repnd;
    exists (k - (k1 + k2 + 1)); auto.

  - right; left.
    exists k1; auto.

  - right; right; allsimpl.
    exists pk; dands; auto.
    + allunfold @computes_to_can_in_max_k_steps; repnd.
      unfold computes_to_can; dands; eauto with slow.
    + exists k2; auto.
Qed.

Lemma approx_open_mk_int_eq {o} :
  forall lib (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    approx_open lib a1 a2
    -> approx_open lib b1 b2
    -> approx_open lib c1 c2
    -> approx_open lib d1 d2
    -> approx_open lib (mk_int_eq a1 b1 c1 d1) (mk_int_eq a2 b2 c2 d2).
Proof.
  introv apro1 apro2 apro3 apro4.

  allrw <- @approx_open_simpler_equiv.
  allunfold @simpl_olift; repnd.
  allrw @nt_wf_eq.
  dands; try (apply wf_int_eq; auto).
  introv prs ispl1 ispl2.

  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow).
  repeat (rw @cl_lsubst_lsubst_aux in ispl1; eauto 3 with slow).
  repeat (rw @cl_lsubst_lsubst_aux in ispl2; eauto 3 with slow).
  allsimpl; fold_terms; allrw @sub_filter_nil_r.

  allrw @isprogram_eq.
  allrw @isprog_inteq; repnd.

  pose proof (apro1 sub) as h1.
  repeat (rw @cl_lsubst_lsubst_aux in h1; eauto 3 with slow).
  allrw @isprogram_eq.
  repeat (autodimp h1 hyp);[].

  pose proof (apro2 sub) as h2.
  repeat (rw @cl_lsubst_lsubst_aux in h2; eauto 3 with slow).
  allrw @isprogram_eq.
  repeat (autodimp h2 hyp);[].

  pose proof (apro3 sub) as h3.
  repeat (rw @cl_lsubst_lsubst_aux in h3; eauto 3 with slow).
  allrw @isprogram_eq.
  repeat (autodimp h3 hyp);[].

  pose proof (apro4 sub) as h4.
  repeat (rw @cl_lsubst_lsubst_aux in h4; eauto 3 with slow).
  allrw @isprogram_eq.
  repeat (autodimp h4 hyp);[].

  constructor.
  unfold close_comput.
  allrw @isprogram_eq; allrw @isprog_inteq; dands; auto;[| |].

  - introv comp.
    apply computes_to_value_mk_int_eq in comp; exrepnd;
    try (apply lsubst_aux_preserves_wf_term2; eauto 3 with slow);[].

    eapply approx_comput_functionality_left in h1;[|exact comp0].
    eapply approx_comput_functionality_left in h2;[|exact comp2].
    allapply @approx_pk2term_implies_reduces_to.

    repndors; repnd; subst;[|].

    + eapply approx_canonical_form in h3;[|exact comp1].
      destruct h3 as [tr_subterms apr]; repnd.
      exists tr_subterms; dands; try (apply clearbot_relbt2); auto.
      allunfold @computes_to_value; repnd; dands; tcsp.
      eapply reduces_to_trans;
        [apply reduce_to_prinargs_comp2;[exact h1|idtac|]; eauto 3 with slow|];[].
      eapply reduces_to_if_split2;
        [csunf; simpl; allrw @pk2term_eq; dcwf h;
         allsimpl; unfold compute_step_comp; simpl;
         allrw @get_param_from_cop_pk2can; auto;
         allrw @co_wf_pk2can;ginv|];[].
      boolvar;tcsp;try omega.

    + eapply approx_canonical_form in h4;[|exact comp1].
      destruct h4 as [tr_subterms apr]; repnd.
      exists tr_subterms; dands; try (apply clearbot_relbt2); auto.
      allunfold @computes_to_value; repnd; dands; tcsp.
      eapply reduces_to_trans;
        [apply reduce_to_prinargs_comp2;[exact h1|idtac|]; eauto 3 with slow|];[].
      eapply reduces_to_if_split2;
        [csunf; simpl; allrw @pk2term_eq; dcwf h;
         allsimpl; unfold compute_step_comp; simpl;
         allrw @get_param_from_cop_pk2can; auto;
         allrw @co_wf_pk2can;ginv|];[].
      boolvar;tcsp;try omega.

  - introv comp.
    apply computes_to_exception_mk_int_eq in comp; repndors; exrepnd;
    try (apply lsubst_aux_preserves_wf_term2; eauto 3 with slow);[|idtac|].

    + eapply approx_comput_functionality_left in h1;[|exact comp0].
      eapply approx_comput_functionality_left in h2;[|exact comp2].
      allapply @approx_pk2term_implies_reduces_to.

      repndors; repnd;[|].

      * apply computes_to_exception_implies_approx in comp1; eauto 3 with slow;[]; repnd.
        eapply approx_trans in h3;[|exact comp4].
        apply approx_exception in h3; exrepnd.
        exists x c; dands; tcsp.
        allunfold @computes_to_exception.
        eapply reduces_to_trans;
          [apply reduce_to_prinargs_comp2;[exact h1|idtac|]; eauto 3 with slow|];[].
        eapply reduces_to_if_split2;
          [csunf; simpl; allrw @pk2term_eq; dcwf h;
           allsimpl; unfold compute_step_comp; simpl;
           allrw @get_param_from_cop_pk2can; auto;
           allrw @co_wf_pk2can;ginv|];[].
        boolvar;tcsp;try omega.

      * apply computes_to_exception_implies_approx in comp1; eauto 3 with slow;[]; repnd.
        eapply approx_trans in h4;[|exact comp4].
        apply approx_exception in h4; exrepnd.
        exists x c; dands; tcsp.
        allunfold @computes_to_exception.
        eapply reduces_to_trans;
          [apply reduce_to_prinargs_comp2;[exact h1|idtac|]; eauto 3 with slow|];[].
        eapply reduces_to_if_split2;
          [csunf; simpl; allrw @pk2term_eq; dcwf h;
           allsimpl; unfold compute_step_comp; simpl;
           allrw @get_param_from_cop_pk2can; auto;
           allrw @co_wf_pk2can;ginv|];[].
        boolvar;tcsp;try omega.

    + apply computes_to_exception_implies_approx in comp; eauto 3 with slow;[]; repnd.
      eapply approx_trans in h1;[|exact comp0].
      apply approx_exception in h1; exrepnd.
      exists x c; dands; tcsp;[].
      allunfold @computes_to_exception.
      unfold mk_less, nobnd.
      eapply reduces_to_trans;[eapply reduces_to_prinarg;exact h0|].
      apply reduces_to_if_step.
      csunf; simpl; auto.

    + apply computes_to_exception_implies_approx in comp0; eauto 3 with slow;[]; repnd.
      eapply approx_trans in h2;[|exact comp2].
      apply approx_exception in h2; exrepnd.

      exists x c; dands; tcsp;[].
      apply reduces_to_implies_approx1 in comp1; eauto 3 with slow;[].
      eapply approx_trans in h1;[|exact comp1].
      apply approx_pk2term_implies_reduces_to in h1.
      allunfold @computes_to_exception.
      eapply reduces_to_trans;
        [apply reduce_to_prinargs_comp2;[exact h1|idtac|exact h0] |]; eauto 3 with slow.
      apply reduces_to_if_step.
      csunf; simpl.
      allrw @pk2term_eq.
      dcwf h; try (complete (allrw @co_wf_pk2can;ginv));[].
      simpl; auto.

  - introv comp.
    apply computes_to_seq_implies_computes_to_value in comp;
      [|apply isprogram_compop_iff;eexists; eexists; eexists; eexists;
        unfold nobnd; dands; eauto 3 with slow];[].

    apply computes_to_value_mk_int_eq in comp; exrepnd;
    try (apply lsubst_aux_preserves_wf_term2; eauto 3 with slow);[].

    eapply approx_comput_functionality_left in h1;[|exact comp0].
    eapply approx_comput_functionality_left in h2;[|exact comp2].
    allapply @approx_pk2term_implies_reduces_to.

    repndors; repnd; subst;[|].

    + eapply approx_sterm in h3;[|eauto]; exrepnd.
      exists f'; dands; auto.
      eapply reduces_to_trans;
        [apply reduce_to_prinargs_comp2;[exact h1|idtac|]; eauto 3 with slow|];[].
      eapply reduces_to_if_split2;
        [csunf; simpl; allrw @pk2term_eq; dcwf h;
         allsimpl; unfold compute_step_comp; simpl;
         allrw @get_param_from_cop_pk2can; auto;
         allrw @co_wf_pk2can;ginv|];[].
      boolvar;tcsp;try omega.
      allunfold @computes_to_value; sp.

    + eapply approx_sterm in h4;[|eauto]; exrepnd.
      exists f'; dands; auto.
      eapply reduces_to_trans;
        [apply reduce_to_prinargs_comp2;[exact h1|idtac|]; eauto 3 with slow|];[].
      eapply reduces_to_if_split2;
        [csunf; simpl; allrw @pk2term_eq; dcwf h;
         allsimpl; unfold compute_step_comp; simpl;
         allrw @get_param_from_cop_pk2can; auto;
         allrw @co_wf_pk2can;ginv|];[].
      boolvar;tcsp;try omega.
      allunfold @computes_to_value; sp.
Qed.

Lemma approx_mk_int_eq {o} :
  forall lib (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    approx lib a1 a2
    -> approx lib b1 b2
    -> approx lib c1 c2
    -> approx lib d1 d2
    -> approx lib (mk_int_eq a1 b1 c1 d1) (mk_int_eq a2 b2 c2 d2).
Proof.
  introv apra aprb aprc aprd.

  applydup @approx_isprog in apra.
  applydup @approx_isprog in aprb.
  applydup @approx_isprog in aprc.
  applydup @approx_isprog in aprd.
  repnd.

  apply approx_open_approx; allrw @isprogram_eq; try (apply isprog_inteq_implies); auto.
  apply approx_open_mk_int_eq; apply approx_implies_approx_open; auto.
Qed.

Lemma cequiv_mk_int_eq {o} :
  forall lib (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> cequiv lib c1 c2
    -> cequiv lib d1 d2
    -> cequiv lib (mk_int_eq a1 b1 c1 d1) (mk_int_eq a2 b2 c2 d2).
Proof.
  introv ceqa ceqb ceqc ceqd.
  allunfold @cequiv; repnd; dands; apply approx_mk_int_eq; auto.
Qed.

Lemma cequivc_mkc_inteq {o} :
  forall lib (a1 a2 b1 b2 c1 c2 d1 d2 : @CTerm o),
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> cequivc lib c1 c2
    -> cequivc lib d1 d2
    -> cequivc lib (mkc_inteq a1 b1 c1 d1) (mkc_inteq a2 b2 c2 d2).
Proof.
  introv ceqa ceqb ceqc ceqd.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  apply cequiv_mk_int_eq; auto.
Qed.

Lemma isprog_vars_mk_int_eq {p} :
  forall (a b c d : @NTerm p) vs,
    isprog_vars vs (mk_int_eq a b c d)
    <=> (isprog_vars vs a
         # isprog_vars vs b
         # isprog_vars vs c
         # isprog_vars vs d).
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw remove_nvars_nil_l).
  repeat (rw app_nil_r).
  repeat (rw subvars_app_l).
  repeat (rw <- @wf_term_eq).
  allrw <- @wf_inteq_iff; split; sp.
Qed.

Lemma isprogram_mk_int_eq {p} :
  forall (a b c d : @NTerm p),
    isprogram (mk_int_eq a b c d)
    <=> (isprogram a
         # isprogram b
         # isprogram c
         # isprogram d).
Proof.
  introv.
  pose proof (isprog_vars_mk_int_eq a b c d []) as h.
  allrw <- @isprog_vars_nil_iff_isprog.
  allrw @isprogram_eq; auto.
Qed.

Lemma approx_bts_refl {o} :
  forall lib (bs : list (@BTerm o)),
    (forall b, LIn b bs -> bt_wf b)
    -> approx_bts lib bs bs.
Proof.
  introv imp.
  unfold approx_bts, lblift.
  dands; auto.
  introv i.
  unfold blift.
  remember (selectbt bs n) as b.
  destruct b as [l t].
  exists l t t; dands; eauto 3 with slow.
  apply approx_open_refl.
  pose proof (imp (bterm l t)) as h.
  autodimp h hyp.
  { rw Heqb; apply selectbt_in; auto. }
  allrw @bt_wf_iff; auto.
Qed.

Lemma isprogram_bt_implies_bt_wf {o} :
  forall (b : @BTerm o), isprogram_bt b -> bt_wf b.
Proof.
  introv isp.
  destruct b.
  apply isprogam_bt_nt_wf_eauto in isp.
  apply wfbt; auto.
Qed.
Hint Resolve isprogram_bt_implies_bt_wf : slow.

Lemma approx_inteq_less_swap1 {o} :
  forall lib (t : @NTerm o) n m u v w,
    m <= n
    -> isprog t
    -> isprog u
    -> isprog v
    -> isprog w
    -> approx
         lib
         (mk_int_eq t (mk_nat n) u (mk_less t (mk_nat m) v w))
         (mk_less t (mk_nat m) v (mk_int_eq t (mk_nat n) u w)).
Proof.
  introv ltm ispt ispu ispv ispw.
  constructor.
  unfold close_comput.
  dands; auto;
    repeat (try (apply isprogram_mk_int_eq; dands; eauto 3 with slow);
            try (apply isprogram_mk_less; dands; eauto 3 with slow)).

  - introv comp.
    apply computes_to_value_mk_int_eq in comp;
      try (apply wf_less); eauto 3 with slow.
    exrepnd.
    apply reduces_to_if_isvalue_like in comp2; eauto 3 with slow.
    destruct pk2; allsimpl; ginv.
    unfold mk_nat in comp2; ginv; fold_terms.
    repndors; repnd; subst.

    + exists tl_subterms.
      dands; auto.

      * allunfold @computes_to_value; repnd; dands; auto.
        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp0|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; try omega.
        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp0|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; tcsp.

      * apply clearbot_relbt2.
        fold (approx_open lib).
        fold (approx_bts lib).
        apply approx_bts_refl.
        allunfold @computes_to_value; repnd.
        apply compute_max_steps_eauto2 in comp1.
        apply isprogram_ot_iff in comp1; repnd.
        introv j; apply comp1 in j; eauto 3 with slow.

    + apply computes_to_value_mk_less in comp1; eauto 3 with slow.
      exrepnd.
      apply reduces_to_if_isvalue_like in comp4; eauto 3 with slow.
      unfold mk_nat in comp4; ginv; fold_terms.
      eapply reduces_to_eq_val_like in comp0;
        [|exact comp3
         |eauto 3 with slow
         |eauto 3 with slow].
      destruct pk1; allsimpl; ginv.
      repndors; repnd; subst.

      * exists tl_subterms.
        dands; auto.

        { allunfold @computes_to_value; repnd; dands; auto.
          eapply reduces_to_trans;
            [apply reduces_to_prinarg;exact comp3|].
          eapply reduces_to_if_split2;
            [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
          boolvar; try omega; auto. }

        { apply clearbot_relbt2.
          fold (approx_open lib).
          fold (approx_bts lib).
          apply approx_bts_refl.
          allunfold @computes_to_value; repnd.
          apply compute_max_steps_eauto2 in comp1.
          apply isprogram_ot_iff in comp1; repnd.
          introv j; apply comp1 in j; eauto 3 with slow. }

      * exists tl_subterms.
        dands; auto.

        { allunfold @computes_to_value; repnd; dands; auto.
          eapply reduces_to_trans;
            [apply reduces_to_prinarg;exact comp3|].
          eapply reduces_to_if_split2;
            [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
          boolvar; try omega; auto.
          eapply reduces_to_trans;
            [apply reduces_to_prinarg;exact comp3|].
          eapply reduces_to_if_split2;
            [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
          boolvar;tcsp. }

        { apply clearbot_relbt2.
          fold (approx_open lib).
          fold (approx_bts lib).
          apply approx_bts_refl.
          allunfold @computes_to_value; repnd.
          apply compute_max_steps_eauto2 in comp1.
          apply isprogram_ot_iff in comp1; repnd.
          introv j; apply comp1 in j; eauto 3 with slow. }

  - introv comp.
    apply computes_to_exception_mk_int_eq in comp;
      try (apply wf_less); eauto 3 with slow.
    repndors; exrepnd.

    + apply reduces_to_if_isvalue_like in comp2; eauto 3 with slow.
      destruct pk2; allsimpl; ginv.
      unfold mk_nat in comp2; ginv; fold_terms.
      repndors; repnd; subst.

      * exists a e.
        applydup @preserve_program_exc2 in comp1; eauto 3 with slow; repnd.
        dands; try (complete (left; apply approx_refl; eauto with slow)).

        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp0|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; try omega.
        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp0|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; tcsp.

      * apply computes_to_exception_mk_less in comp1; eauto 3 with slow.
        repndors; exrepnd.

        { apply reduces_to_if_isvalue_like in comp4; eauto 3 with slow.
          unfold mk_nat in comp4; ginv; fold_terms.
          eapply reduces_to_eq_val_like in comp0;
            [|exact comp3
             |eauto 3 with slow
             |eauto 3 with slow].
          destruct pk1; allsimpl; ginv.
          repndors; repnd; subst.

          - exists a e.
            applydup @preserve_program_exc2 in comp1; eauto 3 with slow; repnd.
            dands; try (complete (left; apply approx_refl; eauto with slow)).

            eapply reduces_to_trans;
              [apply reduces_to_prinarg;exact comp3|].
            eapply reduces_to_if_split2;
              [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
            boolvar; try omega; auto.

          - exists a e.
            applydup @preserve_program_exc2 in comp1; eauto 3 with slow; repnd.
            dands; try (complete (left; apply approx_refl; eauto with slow)).

            eapply reduces_to_trans;
              [apply reduces_to_prinarg;exact comp3|].
            eapply reduces_to_if_split2;
              [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
            boolvar; try omega; auto.

            eapply reduces_to_trans;
              [apply reduces_to_prinarg;exact comp3|].
            eapply reduces_to_if_split2;
              [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
            boolvar; try omega; ginv; tcsp.
        }

        { exists a e.
          applydup @preserve_program_exc2 in comp1; eauto 3 with slow; repnd.
          dands; try (complete (left; apply approx_refl; eauto with slow)).

          eapply reduces_to_trans;
            [apply reduces_to_prinarg;exact comp1|].
          apply reduces_to_if_step; csunf; simpl; auto.
        }

        { apply can_doesnt_raise_an_exception in comp3; sp. }

    + exists a e.
      applydup @preserve_program_exc2 in comp; eauto 3 with slow; repnd.
      dands; try (complete (left; apply approx_refl; eauto with slow)).

      eapply reduces_to_trans;
        [apply reduces_to_prinarg;exact comp|].
      apply reduces_to_if_step; csunf; simpl; auto.

    + apply can_doesnt_raise_an_exception in comp0; sp.

  - introv comp.
    apply computes_to_seq_implies_computes_to_value in comp;
      [|apply isprogram_mk_int_eq; dands; eauto 3 with slow;
        apply isprogram_mk_less; dands; eauto 3 with slow].

    apply computes_to_value_mk_int_eq in comp;
      try (apply wf_less); eauto 3 with slow.
    exrepnd.
    apply reduces_to_if_isvalue_like in comp2; eauto 3 with slow.
    destruct pk2; allsimpl; ginv.
    unfold mk_nat in comp2; ginv; fold_terms.
    repndors; repnd; subst.

    + exists f.
      dands; auto.

      allunfold @computes_to_value; repnd; dands; auto.
      eapply reduces_to_trans;
        [apply reduces_to_prinarg;exact comp0|].
      eapply reduces_to_if_split2;
        [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
      boolvar; try omega.
      eapply reduces_to_trans;
        [apply reduces_to_prinarg;exact comp0|].
      eapply reduces_to_if_split2;
        [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
      boolvar; tcsp.

    + apply computes_to_value_mk_less in comp1; eauto 3 with slow.
      exrepnd.
      apply reduces_to_if_isvalue_like in comp4; eauto 3 with slow.
      unfold mk_nat in comp4; ginv; fold_terms.
      eapply reduces_to_eq_val_like in comp0;
        [|exact comp3
         |eauto 3 with slow
         |eauto 3 with slow].
      destruct pk1; allsimpl; ginv.
      repndors; repnd; subst.

      * exists f.
        dands; auto.

        allunfold @computes_to_value; repnd; dands; auto.
        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp3|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; try omega; auto.

      * exists f.
        dands; auto.

        allunfold @computes_to_value; repnd; dands; auto.
        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp3|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; try omega; auto.
        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp3|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar;tcsp.
Qed.

Lemma approx_less_inteq_swap1 {o} :
  forall lib (t : @NTerm o) n m u v w,
    m <= n
    -> isprog t
    -> isprog u
    -> isprog v
    -> isprog w
    -> approx
         lib
         (mk_less t (mk_nat m) v (mk_int_eq t (mk_nat n) u w))
         (mk_int_eq t (mk_nat n) u (mk_less t (mk_nat m) v w)).
Proof.
  introv ltm ispt ispu ispv ispw.
  constructor.
  unfold close_comput.
  dands; auto;
    repeat (try (apply isprogram_mk_int_eq; dands; eauto 3 with slow);
            try (apply isprogram_mk_less; dands; eauto 3 with slow)).

  - introv comp.
    apply computes_to_value_mk_less in comp;
      try (apply wf_less); eauto 3 with slow.
    exrepnd.
    apply reduces_to_if_isvalue_like in comp2; eauto 3 with slow.
    unfold mk_nat in comp2; ginv; fold_terms.
    repndors; repnd; subst.

    + exists tl_subterms.
      dands; auto.

      * allunfold @computes_to_value; repnd; dands; auto.
        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp0|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; ginv; try omega.
        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp0|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; tcsp; try omega.

      * apply clearbot_relbt2.
        fold (approx_open lib).
        fold (approx_bts lib).
        apply approx_bts_refl.
        allunfold @computes_to_value; repnd.
        apply compute_max_steps_eauto2 in comp1.
        apply isprogram_ot_iff in comp1; repnd.
        introv j; apply comp1 in j; eauto 3 with slow.

    + apply computes_to_value_mk_int_eq in comp1; eauto 3 with slow.
      exrepnd.
      apply reduces_to_if_isvalue_like in comp4; eauto 3 with slow.
      destruct pk2; allsimpl; ginv.
      unfold mk_nat in comp4; ginv; fold_terms.
      eapply reduces_to_eq_val_like in comp0;
        [|exact comp3
         |eauto 3 with slow
         |eauto 3 with slow].
      destruct pk1; allsimpl; ginv.
      repndors; repnd; subst; ginv.

      * exists tl_subterms.
        dands; auto.

        { allunfold @computes_to_value; repnd; dands; auto.
          eapply reduces_to_trans;
            [apply reduces_to_prinarg;exact comp3|].
          eapply reduces_to_if_split2;
            [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
          boolvar; try omega; tcsp. }

        { apply clearbot_relbt2.
          fold (approx_open lib).
          fold (approx_bts lib).
          apply approx_bts_refl.
          allunfold @computes_to_value; repnd.
          apply compute_max_steps_eauto2 in comp1.
          apply isprogram_ot_iff in comp1; repnd.
          introv j; apply comp1 in j; eauto 3 with slow. }

      * exists tl_subterms.
        dands; auto.

        { allunfold @computes_to_value; repnd; dands; auto.
          eapply reduces_to_trans;
            [apply reduces_to_prinarg;exact comp3|].
          eapply reduces_to_if_split2;
            [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
          boolvar; ginv; try omega; tcsp.
          eapply reduces_to_trans;
            [apply reduces_to_prinarg;exact comp3|].
          eapply reduces_to_if_split2;
            [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
          boolvar;tcsp;try omega. }

        { apply clearbot_relbt2.
          fold (approx_open lib).
          fold (approx_bts lib).
          apply approx_bts_refl.
          allunfold @computes_to_value; repnd.
          apply compute_max_steps_eauto2 in comp1.
          apply isprogram_ot_iff in comp1; repnd.
          introv j; apply comp1 in j; eauto 3 with slow. }

  - introv comp.
    apply computes_to_exception_mk_less in comp;
      try (apply wf_less); eauto 3 with slow.
    repndors; exrepnd.

    + apply reduces_to_if_isvalue_like in comp2; eauto 3 with slow.
      unfold mk_nat in comp2; ginv; fold_terms.
      repndors; repnd; subst.

      * exists a e.
        applydup @preserve_program_exc2 in comp1; eauto 3 with slow; repnd.
        dands; try (complete (left; apply approx_refl; eauto with slow)).

        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp0|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; ginv; try omega.
        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp0|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; tcsp; try omega.

      * apply computes_to_exception_mk_int_eq in comp1; eauto 3 with slow.
        repndors; exrepnd.

        { apply reduces_to_if_isvalue_like in comp4; eauto 3 with slow.
          destruct pk2; allsimpl; ginv.
          unfold mk_nat in comp4; ginv; fold_terms.
          eapply reduces_to_eq_val_like in comp0;
            [|exact comp3
             |eauto 3 with slow
             |eauto 3 with slow].
          destruct pk1; allsimpl; ginv.
          repndors; repnd; subst; ginv.

          - exists a e.
            applydup @preserve_program_exc2 in comp1; eauto 3 with slow; repnd.
            dands; try (complete (left; apply approx_refl; eauto with slow)).

            eapply reduces_to_trans;
              [apply reduces_to_prinarg;exact comp3|].
            eapply reduces_to_if_split2;
              [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
            boolvar; try omega; tcsp.

          - exists a e.
            applydup @preserve_program_exc2 in comp1; eauto 3 with slow; repnd.
            dands; try (complete (left; apply approx_refl; eauto with slow)).

            eapply reduces_to_trans;
              [apply reduces_to_prinarg;exact comp3|].
            eapply reduces_to_if_split2;
              [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
            boolvar; try omega; tcsp.

            eapply reduces_to_trans;
              [apply reduces_to_prinarg;exact comp3|].
            eapply reduces_to_if_split2;
              [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
            boolvar; try omega; ginv; tcsp.
        }

        { exists a e.
          applydup @preserve_program_exc2 in comp1; eauto 3 with slow; repnd.
          dands; try (complete (left; apply approx_refl; eauto with slow)).

          eapply reduces_to_trans;
            [apply reduces_to_prinarg;exact comp1|].
          apply reduces_to_if_step; csunf; simpl; auto.
        }

        { apply can_doesnt_raise_an_exception in comp3; sp. }

    + exists a e.
      applydup @preserve_program_exc2 in comp; eauto 3 with slow; repnd.
      dands; try (complete (left; apply approx_refl; eauto with slow)).

      eapply reduces_to_trans;
        [apply reduces_to_prinarg;exact comp|].
      apply reduces_to_if_step; csunf; simpl; auto.

    + apply can_doesnt_raise_an_exception in comp0; sp.

  - introv comp.
    apply computes_to_seq_implies_computes_to_value in comp;
      [|apply isprogram_mk_less; dands; eauto 3 with slow;
        apply isprogram_mk_int_eq; dands; eauto 3 with slow].

    apply computes_to_value_mk_less in comp;
      try (apply wf_less); eauto 3 with slow.
    exrepnd.
    apply reduces_to_if_isvalue_like in comp2; eauto 3 with slow.
    unfold mk_nat in comp2; ginv; fold_terms.
    repndors; repnd; subst.

    + exists f.
      dands; auto.

      allunfold @computes_to_value; repnd; dands; auto.
      eapply reduces_to_trans;
        [apply reduces_to_prinarg;exact comp0|].
      eapply reduces_to_if_split2;
        [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
      boolvar; ginv; try omega.
      eapply reduces_to_trans;
        [apply reduces_to_prinarg;exact comp0|].
      eapply reduces_to_if_split2;
        [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
      boolvar; tcsp; try omega.

    + apply computes_to_value_mk_int_eq in comp1; eauto 3 with slow.
      exrepnd.
      apply reduces_to_if_isvalue_like in comp4; eauto 3 with slow.
      destruct pk2; allsimpl; ginv.
      unfold mk_nat in comp4; ginv; fold_terms.
      eapply reduces_to_eq_val_like in comp0;
        [|exact comp3
         |eauto 3 with slow
         |eauto 3 with slow].
      destruct pk1; allsimpl; ginv.
      repndors; repnd; subst; ginv.

      * exists f.
        dands; auto.

        allunfold @computes_to_value; repnd; dands; auto.
        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp3|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; try omega; tcsp.

      * exists f.
        dands; auto.

        allunfold @computes_to_value; repnd; dands; auto.
        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp3|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; ginv; try omega; tcsp.
        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp3|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar;tcsp;try omega.
Qed.

Lemma cequivc_inteq_less_swap1 {o} :
  forall lib (t : @CTerm o) n m u v w,
    m <= n
    -> cequivc
         lib
         (mkc_inteq t (mkc_nat n) u (mkc_less t (mkc_nat m) v w))
         (mkc_less t (mkc_nat m) v (mkc_inteq t (mkc_nat n) u w)).
Proof.
  introv ltm.
  destruct_cterms.
  unfold cequivc; simpl.
  split.
  - apply approx_inteq_less_swap1; auto.
  - apply approx_less_inteq_swap1; auto.
Qed.

Lemma seq_normalizable_update {o} :
  forall lib (s : @CTerm o) n k v,
    seq_normalizable lib s n v
    -> seq_normalizable lib (update_seq s n k v) (S n) v.
Proof.
  introv norm.
  allunfold @seq_normalizable.

  unfold update_seq, seq2kseq.
  apply implies_cequivc_lam.
  introv.
  allrw @mkcv_inteq_substc.
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @mkcv_bot_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_nat_substc.
  allrw @mkcv_zero_substc.

  eapply cequivc_trans;
    [|apply cequivc_mkc_less;
       [apply cequivc_refl
       |apply cequivc_refl
       |apply cequivc_refl
       |apply cequivc_mkc_less;
         [apply cequivc_refl
         |apply cequivc_refl
         |apply cequivc_sym;apply cequivc_beta
         |apply cequivc_refl]
       ]
    ].
  allrw @mkcv_inteq_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @csubst_mk_cv.

  eapply cequivc_trans;
    [apply cequivc_mkc_inteq;
      [apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl
      |apply implies_cequivc_apply;
        [exact norm|apply cequivc_refl]
      ]
    |].
  unfold seq2kseq.

  eapply cequivc_trans;
    [apply cequivc_mkc_inteq;
      [apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_beta]
    |].
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @mkcv_bot_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_nat_substc.
  allrw @mkcv_zero_substc.

  eapply cequivc_trans;
    [allrw @mkc_zero_eq; apply cequivc_inteq_less_swap1; try omega|].
  allrw <- @mkc_zero_eq.

  apply implies_cequivc_mkc_less1.
  introv compu.
  allrw @mkc_zero_eq.
  allrw @mkc_nat_eq.

  eapply cequivc_trans;
    [apply cequivc_mkc_less_int|].
  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_mkc_less_int].
  boolvar; tcsp.
  apply Wf_Z.Z_of_nat_complete_inf in l; exrepnd; subst; fold_terms.
  allrw <- @mkc_nat_eq.

  eapply cequivc_trans;
    [apply cequivc_mkc_inteq;
      [apply computes_to_valc_implies_cequivc; exact compu
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_mkc_less;
        [apply computes_to_valc_implies_cequivc; exact compu
        |apply cequivc_refl
        |apply cequivc_refl
        |apply cequivc_refl]
      ]
    |].

  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_mkc_less;
       [apply computes_to_valc_implies_cequivc; exact compu
       |apply cequivc_refl
       |apply cequivc_mkc_inteq;
         [apply computes_to_valc_implies_cequivc; exact compu
         |apply cequivc_refl
         |apply cequivc_refl
         |apply cequivc_refl]
       |apply cequivc_refl
       ]
    ].

  eapply cequivc_trans;
    [apply cequivc_inteq_less_swap1; try omega|].

  eapply cequivc_trans;
    [apply cequivc_mkc_less;
      [apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_mkc_inteq_nat]
    |].

  eapply cequivc_trans;
    [apply cequivc_mkc_less_nat|].

  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_mkc_less;
      [apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_mkc_inteq_nat
      |apply cequivc_refl]
    ].

  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_mkc_less_nat].

  boolvar; subst; tcsp; try omega.
Qed.

Fixpoint malpha2 {o}
         (lib : library)
         (X c : @CTerm o)
         (v : NVar)
         (q : seq_normalizable lib c 0 v)
         (h : !meta_on_seq lib X 0 c)
         (f : meta_seq_NA lib X -> nat)
         (ind : forall a : meta_seq_NA lib X,
                  !meta_on_upd_seq lib X (meta_seq_NA_seq a) (meta_seq_NA_nat a) (f a) v)
         (n : nat) : meta_kseq_NA2 lib n X v :=
  match n with
    | 0 =>
      let i := is_kseq_0 lib c in
      let p := mk_meta_seq_NA 0 c i h in
      let k := f p in
      mk_meta_kseq_NA2
        k
        (update_seq c 0 k v)
        (is_kseq_update lib c 0 k v i)
        (seq_normalizable_update lib c 0 k v q)
        (meta_kseq_at_is_update lib c 0 k v)
        (ind p)
    | S m =>
      let (_,r) := malpha2 lib X c v q h f ind m in
      let (s,r) := r in
      let (i,r) := r in
      let (z,r) := r in
      let (_,na) := r in
      let p := mk_meta_seq_NA (S m) s i na in
      let k := f p in
      mk_meta_kseq_NA2
        k
        (update_seq s (S m) k v)
        (is_kseq_update lib s (S m) k v i)
        (seq_normalizable_update lib s (S m) k v z)
        (meta_kseq_at_is_update lib s (S m) k v)
        (ind p)
  end.

Lemma meta_kseq_NA2_seq_mk_meta_kseq_NA2 {o} :
  forall lib n (A : @CTerm o) v m s i q e p,
    meta_kseq_NA2_seq (@mk_meta_kseq_NA2 o lib n A v m s i q e p) = s.
Proof. sp. Qed.

Lemma malpha2_prop1 {o} :
  forall lib
         (X c : @CTerm o)
         (v : NVar)
         (q : seq_normalizable lib c 0 v)
         (h : !meta_on_seq lib X 0 c)
         (f : meta_seq_NA lib X -> nat)
         (ind : forall a : meta_seq_NA lib X,
                  !meta_on_upd_seq lib X (meta_seq_NA_seq a) (meta_seq_NA_nat a) (f a) v)
         (n m : nat)
         (lemn : m <= n),
    equality
      lib
      (meta_kseq_NA2_seq (malpha2 lib X c v q h f ind n))
      (meta_kseq_NA2_seq (malpha2 lib X c v q h f ind m))
      (natk2nat (mkc_nat m)).
Proof.
  introv lemn.
  assert {k : nat & n = k + m} as e.
  { exists (n - m); omega. }
  exrepnd; subst.
  clear lemn.
  induction k; introv; allsimpl; apply implies_equality_natk2nat; introv ltm0.

  - remember (malpha2 lib X c v q h f ind m) as am.
    unfold meta_kseq_NA2 in am; exrepnd; allsimpl.

    dup am0 as i.
    apply (is_kseq_implies lib m0) in i; try omega; exrepnd.
    exists k; dands; auto.

  - remember (malpha2 lib X c v q h f ind (k + m)) as am.
    unfold meta_kseq_NA2 in am; exrepnd; simphyps.
    rw @meta_kseq_NA2_seq_mk_meta_kseq_NA2.

    eapply equality_natk2nat_implies in IHk;[|exact ltm0].
    exrepnd.
    exists k0; dands; auto.

    unfold update_seq.
    apply cequivc_nat_implies_computes_to_valc.
    eapply cequivc_trans;[apply cequivc_beta|].
    allrw @mkcv_inteq_substc.
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @csubst_mk_cv.
    eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
    boolvar; tcsp; GC; try omega.
    apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma seq_normalizable_seq2kseq {o} :
  forall lib (s : @CTerm o) n v,
    seq_normalizable lib (seq2kseq s n v) n v.
Proof.
  introv.
  apply cequivc_seq2kseq_twice.
Qed.

(* same as bar_induction_meta but does not use X's functionality and
   adds a few seq2kseq instead *)
Lemma bar_induction_meta2 {o} :
  forall lib (B X c : @CTerm o) v,
    barind_meta_bar2 lib B v
    -> barind_meta_imp lib B X
    -> barind_meta_ind lib X v
    -> meta_on_seq lib X 0 (seq2kseq c 0 v).
Proof.
  introv bar imp ind.
  pose proof (classic (meta_on_seq lib X 0 (seq2kseq c 0 v))) as ni.
  repndors; auto.
  provefalse.

  apply barind_meta_ind_implies_cont in ind.
  apply barind_meta_ind_cont_implies_cont2 in ind.
  apply barind_meta_ind_cont2_implies_cont3 in ind.
  unfold barind_meta_ind_cont3 in ind; exrepnd.
  rename ind0 into ind.

  remember (malpha2 lib X (seq2kseq c 0 v) v (seq_normalizable_seq2kseq lib c 0 v) ni f ind) as g.
  remember (fun m => meta_kseq_NA2_nat (g m)) as s.

  assert (forall n, eq_kseq lib (mkc_nseq s) (meta_kseq_NA2_seq (g n)) n) as e.
  { introv.
    apply implies_equality_natk2nat; introv ltm.
    subst.
    exists (meta_kseq_NA2_nat (malpha2 lib X (seq2kseq c 0 v) v (seq_normalizable_seq2kseq lib c 0 v) ni f ind m)).
    dands.

    - apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta_nseq|].
      simpl; auto.

    - pose proof (malpha2_prop1 lib X (seq2kseq c 0 v) v (seq_normalizable_seq2kseq lib c 0 v) ni f ind n (S m)) as q.
      autodimp q hyp; try omega.
      apply (equality_natk2nat_implies lib m) in q; try omega.
      exrepnd.

      apply cequivc_nat_implies_computes_to_valc.
      apply computes_to_valc_implies_cequivc in q1.
      apply computes_to_valc_implies_cequivc in q0.

      apply cequivc_sym in q1.
      eapply cequivc_trans in q1;[|exact q0].
      clear q0.
      eapply cequivc_trans;[apply cequivc_sym;exact q1|].
      clear q1.
      simpl.

      remember (malpha2 lib X (seq2kseq c 0 v) v (seq_normalizable_seq2kseq lib c 0 v) ni f ind m) as am.
      unfold meta_kseq_NA2 in am; exrepnd; simphyps.
      rw @meta_kseq_NA2_seq_mk_meta_kseq_NA2.
      unfold update_seq.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; auto; try omega.
  }

  pose proof (bar (mkc_nseq s)) as b.
  autodimp b hyp; eauto 3 with slow.
  exrepnd.
  rename b0 into b.

  apply imp in b;[|apply implies_is_kseq_seq2kseq; eauto 3 with slow].

  induction m; allsimpl.

  { pose proof (eq_kseq_0 lib (mkc_nseq s) c) as h.
    apply (seq2kseq_prop2 _ v) in h.
    eapply cequivc_preserves_meta_on_seq in b;[|exact h]; auto.
  }

  pose proof (e (S m)) as q1.
  apply (seq2kseq_prop2 _ v) in q1.
  eapply cequivc_preserves_meta_on_seq in b;[|exact q1].
  pose proof (e m) as q2.
  apply (seq2kseq_prop2 _ v) in q2.
  eapply cequivc_preserves_not_meta_on_seq in IHm;[|exact q2].
  clear q1 q2 e.

  subst; allsimpl.
  remember (malpha2 lib X (seq2kseq c 0 v) v (seq_normalizable_seq2kseq lib c 0 v) ni f ind m) as am.
  unfold meta_kseq_NA2 in am; exrepnd; allsimpl.

  assert (eq_kseq
            lib
            (update_seq s (S m) (f (mk_meta_seq_NA (S m) s am0 am1)) v)
            s
            (S m)) as ee.
  { unfold eq_kseq.
    apply implies_equality_natk2nat; introv ltm1.
    dup am0 as e.
    unfold is_kseq, eq_kseq in e.
    eapply member_natk2nat_implies in e;[|exact ltm1]; exrepnd.
    exists k; dands; auto.
    unfold update_seq.
    apply cequivc_nat_implies_computes_to_valc.
    eapply cequivc_trans;[apply cequivc_beta|].
    allrw @mkcv_inteq_substc.
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @csubst_mk_cv.
    eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
    boolvar; tcsp; GC; try omega.
    apply computes_to_valc_implies_cequivc; auto.
  }

  apply (seq2kseq_prop2 _ v) in ee.
  eapply cequivc_preserves_meta_on_seq in b;[|exact ee].
  clear ee.
  unfold seq_normalizable in am2.
  eapply cequivc_preserves_meta_on_seq in b;
    [|apply cequivc_sym;exact am2].
  sp.
Qed.

Definition meta_fun_on_seq {o} lib (A1 A2 : @CTerm o) (n : nat) (s1 s2 : CTerm) :=
  inhabited_type lib (mkc_apply2 A1 (mkc_nat n) s1)
  # tequality lib (mkc_apply2 A1 (mkc_nat n) s1) (mkc_apply2 A2 (mkc_nat n) s2).

Definition meta_fun_on_upd_seq {o} lib (X1 X2 s1 s2 : @CTerm o) (n m : nat) (v : NVar) :=
  meta_fun_on_seq lib X1 X2 (S n) (update_seq s1 n m v) (update_seq s2 n m v).

Definition barind_meta_fun_ind {o} lib (X1 X2 : @CTerm o) v :=
  forall (n : nat) (s1 s2 : CTerm),
    eq_kseq lib s1 s2 n
    -> (forall (m : nat), meta_fun_on_upd_seq lib X1 X2 s1 s2 n m v)
    -> meta_fun_on_seq lib X1 X2 n s1 s2.

Definition barind_meta_fun_ind_cont {o} lib (X1 X2 : @CTerm o) v :=
  forall (n : nat) (s1 s2 : CTerm),
    eq_kseq lib s1 s2 n
    -> !meta_fun_on_seq lib X1 X2 n s1 s2
    -> {m : nat , !meta_fun_on_upd_seq lib X1 X2 s1 s2 n m v}.

Definition meta_fun_seq_NA {o} lib (X1 X2 : @CTerm o) :=
  {n : nat
   & {s1 : CTerm
   & {s2 : CTerm
   & eq_kseq lib s1 s2 n
   # !meta_fun_on_seq lib X1 X2 n s1 s2 }}}.

Definition mk_meta_fun_seq_NA {o} {lib} {X1 X2 : @CTerm o}
           (n  : nat)
           (s1 : CTerm)
           (s2 : CTerm)
           (i  : eq_kseq lib s1 s2 n)
           (p  : !meta_fun_on_seq lib X1 X2 n s1 s2) : meta_fun_seq_NA lib X1 X2 :=
  existT _ n (existT _ s1 (existT _ s2 (i,p))).

Definition meta_fun_seq_NA_nat {o} {lib} {X1 X2 : @CTerm o} (x : meta_fun_seq_NA lib X1 X2) : nat :=
  projT1 x.

Definition meta_fun_seq_NA_seq1 {o} {lib} {X1 X2 : @CTerm o} (x : meta_fun_seq_NA lib X1 X2) : CTerm :=
  match x with
    | existT _ (existT s _) => s
  end.

Definition meta_fun_seq_NA_seq2 {o} {lib} {X1 X2 : @CTerm o} (x : meta_fun_seq_NA lib X1 X2) : CTerm :=
  match x with
    | existT _ (existT _ (existT s _)) => s
  end.

Definition barind_meta_fun_ind_cont2 {o} lib (X1 X2 : @CTerm o) v :=
  forall (x : meta_fun_seq_NA lib X1 X2),
    {m : nat
     , !meta_fun_on_upd_seq
        lib X1 X2
        (meta_fun_seq_NA_seq1 x)
        (meta_fun_seq_NA_seq2 x)
        (meta_fun_seq_NA_nat x)
        m v}.

Definition barind_meta_fun_ind_cont3 {o} lib (X1 X2 : @CTerm o) v :=
  {f : meta_fun_seq_NA lib X1 X2 -> nat
   , forall a : meta_fun_seq_NA lib X1 X2,
       !meta_fun_on_upd_seq
          lib X1 X2
          (meta_fun_seq_NA_seq1 a)
          (meta_fun_seq_NA_seq2 a)
          (meta_fun_seq_NA_nat a)
          (f a) v}.

Lemma barind_meta_fun_ind_implies_cont {o} :
  forall lib (X1 X2 : @CTerm o) v,
    barind_meta_fun_ind lib X1 X2 v
    -> barind_meta_fun_ind_cont lib X1 X2 v.
Proof.
  introv ind mem ni.
  pose proof (ind n s1 s2 mem) as h; clear ind.
  apply contraposition in h; auto.
  (* We use Markov's principle *)
  apply not_all_ex_not in h; auto.
Qed.

Lemma barind_meta_fun_ind_cont_implies_cont2 {o} :
  forall lib (X1 X2 : @CTerm o) v,
    barind_meta_fun_ind_cont lib X1 X2 v
    -> barind_meta_fun_ind_cont2 lib X1 X2 v.
Proof.
  introv ind; introv.
  unfold meta_fun_seq_NA in x; exrepnd.
  pose proof (ind n s1 s2 x1 x0) as h; clear ind.
  simpl; auto.
Qed.

Lemma barind_meta_fun_ind_cont2_implies_cont3 {o} :
  forall lib (X1 X2 : @CTerm o) v,
    barind_meta_fun_ind_cont2 lib X1 X2 v
    -> barind_meta_fun_ind_cont3 lib X1 X2 v.
Proof.
  introv ind; introv.
  unfold barind_meta_fun_ind_cont2 in ind.
  apply FunctionalChoice_on in ind; auto.
Qed.

Definition meta_fun_kseq_NA {o} lib (n : nat) (A1 A2 : @CTerm o) v :=
  {m : nat
   & {s1 : CTerm
   & {s2 : CTerm
   & eq_kseq lib s1 s2 (S n)
   # seq_normalizable lib s1 (S n) v
   # seq_normalizable lib s2 (S n) v
   # meta_kseq_at_is lib s1 n m
   # meta_kseq_at_is lib s2 n m
   # !meta_fun_on_seq lib A1 A2 (S n) s1 s2 }}}.

Definition mk_meta_fun_kseq_NA {o} {lib} {n : nat} {A1 A2 : @CTerm o} {v}
           (m : nat)
           (s1 s2 : CTerm)
           (i  : eq_kseq lib s1 s2 (S n))
           (q1 : seq_normalizable lib s1 (S n) v)
           (q2 : seq_normalizable lib s2 (S n) v)
           (e1 : meta_kseq_at_is lib s1 n m)
           (e2 : meta_kseq_at_is lib s2 n m)
           (p  : !meta_fun_on_seq lib A1 A2 (S n) s1 s2) : meta_fun_kseq_NA lib n A1 A2 v :=
  existT _ m (existT _ s1 (existT _ s2 (i,(q1,(q2,(e1,(e2,p))))))).

Definition meta_fun_kseq_NA_nat {o} {lib} {n : nat} {A1 A2 : @CTerm o} {v}
           (x : meta_fun_kseq_NA lib n A1 A2 v) : nat:=
  match x with
    | existT m _ => m
  end.

Definition meta_fun_kseq_NA_seq1 {o} {lib} {n : nat} {A1 A2 : @CTerm o} {v}
           (x : meta_fun_kseq_NA lib n A1 A2 v) : CTerm:=
  match x with
    | existT _ (existT s _) => s
  end.

Definition meta_fun_kseq_NA_seq2 {o} {lib} {n : nat} {A1 A2 : @CTerm o} {v}
           (x : meta_fun_kseq_NA lib n A1 A2 v) : CTerm:=
  match x with
    | existT _ (existT _ (existT s _)) => s
  end.

Fixpoint m_fun_alpha {o}
         (lib : library)
         (X1 X2 c1 c2 : @CTerm o)
         (v  : NVar)
         (q1 : seq_normalizable lib c1 0 v)
         (q2 : seq_normalizable lib c2 0 v)
         (h  : !meta_fun_on_seq lib X1 X2 0 c1 c2)
         (f  : meta_fun_seq_NA lib X1 X2 -> nat)
         (ind : forall a : meta_fun_seq_NA lib X1 X2,
                  !meta_fun_on_upd_seq
                     lib X1 X2
                     (meta_fun_seq_NA_seq1 a)
                     (meta_fun_seq_NA_seq2 a)
                     (meta_fun_seq_NA_nat a) (f a) v)
         (n : nat) : meta_fun_kseq_NA lib n X1 X2 v :=
  match n with
    | 0 =>
      let i := eq_kseq_0 lib c1 c2 in
      let p := mk_meta_fun_seq_NA 0 c1 c2 i h in
      let k := f p in
      mk_meta_fun_kseq_NA
        k
        (update_seq c1 0 k v)
        (update_seq c2 0 k v)
        (eq_kseq_update lib c1 c2 0 k v i)
        (seq_normalizable_update lib c1 0 k v q1)
        (seq_normalizable_update lib c2 0 k v q2)
        (meta_kseq_at_is_update lib c1 0 k v)
        (meta_kseq_at_is_update lib c2 0 k v)
        (ind p)
    | S m =>
      let (_,r) := m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind m in
      let (s1,r) := r in
      let (s2,r) := r in
      let (ek,r) := r in
      let (z1,r) := r in
      let (z2,r) := r in
      let (e1,r) := r in
      let (e2,na) := r in
      let p := mk_meta_fun_seq_NA (S m) s1 s2 ek na in
      let k := f p in
      mk_meta_fun_kseq_NA
        k
        (update_seq s1 (S m) k v)
        (update_seq s2 (S m) k v)
        (eq_kseq_update lib s1 s2 (S m) k v ek)
        (seq_normalizable_update lib s1 (S m) k v z1)
        (seq_normalizable_update lib s2 (S m) k v z2)
        (meta_kseq_at_is_update lib s1 (S m) k v)
        (meta_kseq_at_is_update lib s2 (S m) k v)
        (ind p)
  end.

Lemma meta_fun_kseq_NA_seq1_mk_meta_fun_kseq_NA {o} :
  forall lib n (A1 A2 : @CTerm o) v m s1 s2 i q1 q2 e1 e2 p,
    meta_fun_kseq_NA_seq1 (@mk_meta_fun_kseq_NA o lib n A1 A2 v m s1 s2 i q1 q2 e1 e2 p) = s1.
Proof. sp. Qed.

Lemma meta_fun_kseq_NA_seq2_mk_meta_fun_kseq_NA {o} :
  forall lib n (A1 A2 : @CTerm o) v m s1 s2 i q1 q2 e1 e2 p,
    meta_fun_kseq_NA_seq2 (@mk_meta_fun_kseq_NA o lib n A1 A2 v m s1 s2 i q1 q2 e1 e2 p) = s2.
Proof. sp. Qed.

Lemma m_fun_alpha_prop1 {o} :
  forall lib
         (X1 X2 c1 c2 : @CTerm o)
         (v  : NVar)
         (q1 : seq_normalizable lib c1 0 v)
         (q2 : seq_normalizable lib c2 0 v)
         (h  : !meta_fun_on_seq lib X1 X2 0 c1 c2)
         (f  : meta_fun_seq_NA lib X1 X2 -> nat)
         (ind : forall a : meta_fun_seq_NA lib X1 X2,
                  !meta_fun_on_upd_seq
                     lib X1 X2
                     (meta_fun_seq_NA_seq1 a)
                     (meta_fun_seq_NA_seq2 a)
                     (meta_fun_seq_NA_nat a) (f a) v)
         (n m : nat)
         (lemn : m <= n),
    equality
      lib
      (meta_fun_kseq_NA_seq1 (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind n))
      (meta_fun_kseq_NA_seq1 (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind m))
      (natk2nat (mkc_nat m)).
Proof.
  introv lemn.
  assert {k : nat & n = k + m} as e.
  { exists (n - m); omega. }
  exrepnd; subst.
  clear lemn.
  induction k; introv; allsimpl; apply implies_equality_natk2nat; introv ltm0.

  - remember (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind m) as am.
    unfold meta_fun_kseq_NA in am; exrepnd; allsimpl.

    dup am1 as i.
    apply (eq_kseq_implies lib m0) in i; try omega; exrepnd.
    exists k; dands; auto.

  - remember (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind (k + m)) as am.
    unfold meta_fun_kseq_NA in am; exrepnd; simphyps.
    rw @meta_fun_kseq_NA_seq1_mk_meta_fun_kseq_NA.

    eapply equality_natk2nat_implies in IHk;[|exact ltm0].
    exrepnd.
    exists k0; dands; auto.

    unfold update_seq.
    apply cequivc_nat_implies_computes_to_valc.
    eapply cequivc_trans;[apply cequivc_beta|].
    allrw @mkcv_inteq_substc.
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @csubst_mk_cv.
    eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
    boolvar; tcsp; GC; try omega.
    apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma m_fun_alpha_prop2 {o} :
  forall lib
         (X1 X2 c1 c2 : @CTerm o)
         (v  : NVar)
         (q1 : seq_normalizable lib c1 0 v)
         (q2 : seq_normalizable lib c2 0 v)
         (h  : !meta_fun_on_seq lib X1 X2 0 c1 c2)
         (f  : meta_fun_seq_NA lib X1 X2 -> nat)
         (ind : forall a : meta_fun_seq_NA lib X1 X2,
                  !meta_fun_on_upd_seq
                     lib X1 X2
                     (meta_fun_seq_NA_seq1 a)
                     (meta_fun_seq_NA_seq2 a)
                     (meta_fun_seq_NA_nat a) (f a) v)
         (m : nat),
    equality
      lib
      (meta_fun_kseq_NA_seq1 (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind m))
      (meta_fun_kseq_NA_seq2 (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind m))
      (natk2nat (mkc_nat m)).
Proof.
  introv.
  induction m; introv; allsimpl; apply implies_equality_natk2nat; introv ltm0; try omega.

  remember (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind m) as am.
  unfold meta_fun_kseq_NA in am; exrepnd; simphyps.
  rw @meta_fun_kseq_NA_seq1_mk_meta_fun_kseq_NA.
  rw @meta_fun_kseq_NA_seq2_mk_meta_fun_kseq_NA.

  destruct (deq_nat m0 m) as [d|d].

  - subst.
    exists m1.
    dands.

    + unfold update_seq.
      apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; tcsp; GC; try omega.

    + unfold update_seq.
      apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; tcsp; GC; try omega.

  - assert (m0 < m) as ltm by omega.
    clear d ltm0.

    eapply equality_natk2nat_implies in IHm;[|exact ltm].
    exrepnd.
    exists k; dands; auto.

    + unfold update_seq.
      apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; tcsp; GC; try omega.
      apply computes_to_valc_implies_cequivc; auto.

    + unfold update_seq.
      apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; tcsp; GC; try omega.
      apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma eq_kseq_seq2kseq_0 {o} :
  forall lib v (s1 s2 : @CTerm o),
    eq_kseq lib (seq2kseq s1 0 v) (seq2kseq s2 0 v) 0.
Proof.
  introv.
  apply implies_equality_natk2nat.
  introv ltm; omega.
Qed.

Lemma cequivc_seq2kseq_0 {o} :
  forall lib v (s1 s2 : @CTerm o),
    cequivc lib (seq2kseq s1 0 v) (seq2kseq s2 0 v).
Proof.
  introv.
  eapply cequivc_trans;[apply cequivc_seq2kseq_twice|].
  eapply cequivc_trans;[|apply cequivc_sym;apply cequivc_seq2kseq_twice].
  apply seq2kseq_prop2.
  apply eq_kseq_seq2kseq_0.
Qed.

Lemma implies_cequivc_seq2kseq {o} :
  forall lib v n (s1 s2 : @CTerm o),
    cequivc lib s1 s2
    -> cequivc lib (seq2kseq s1 n v) (seq2kseq s2 n v).
Proof.
  introv ceq.
  unfold seq2kseq.
  apply implies_cequivc_lam; introv.
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_bot_substc.
  allrw @mkcv_nat_substc.
  allrw @mkcv_zero_substc.

  eapply cequivc_mkc_less;
    [apply cequivc_refl
    |apply cequivc_refl
    |apply cequivc_refl
    |eapply cequivc_mkc_less;
      [apply cequivc_refl
      |apply cequivc_refl
      |apply sp_implies_cequivc_apply;auto
      |apply cequivc_refl]
    ].
Qed.

Lemma cequivc_update_seq {o} :
  forall lib (s1 s2 : @CTerm o) n m v,
    cequivc lib s1 s2
    -> cequivc lib (update_seq s1 n m v) (update_seq s2 n m v).
Proof.
  introv ceq.

  unfold update_seq.
  apply implies_cequivc_lam; introv.
  allrw @mkcv_inteq_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @csubst_mk_cv.

  eapply cequivc_mkc_inteq;
    [apply cequivc_refl
    |apply cequivc_refl
    |apply cequivc_refl
    |apply sp_implies_cequivc_apply;auto].
Qed.

Lemma m_fun_alpha_prop3 {o} :
  forall lib
         (X1 X2 c1 c2 : @CTerm o)
         (v  : NVar)
         (q1 : seq_normalizable lib c1 0 v)
         (q2 : seq_normalizable lib c2 0 v)
         (h  : !meta_fun_on_seq lib X1 X2 0 c1 c2)
         (f  : meta_fun_seq_NA lib X1 X2 -> nat)
         (ind : forall a : meta_fun_seq_NA lib X1 X2,
                  !meta_fun_on_upd_seq
                     lib X1 X2
                     (meta_fun_seq_NA_seq1 a)
                     (meta_fun_seq_NA_seq2 a)
                     (meta_fun_seq_NA_nat a) (f a) v)
         (m : nat),
    cequivc
      lib
      (meta_fun_kseq_NA_seq1 (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind m))
      (meta_fun_kseq_NA_seq2 (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind m)).
Proof.
  introv.

  assert (cequivc lib c1 c2) as ceq.
  { eapply cequivc_trans;[exact q1|].
    eapply cequivc_trans;[|apply cequivc_sym;exact q2].
    apply cequivc_seq2kseq_0. }

  induction m; introv; allsimpl.

  - remember (f (mk_meta_fun_seq_NA 0 c1 c2 (eq_kseq_0 lib c1 c2) h)) as n; clear Heqn.
    apply cequivc_update_seq; auto.

  - remember (m_fun_alpha lib X1 X2 c1 c2 v q1 q2 h f ind m) as am.
    unfold meta_fun_kseq_NA in am; exrepnd; simphyps.
    rw @meta_fun_kseq_NA_seq1_mk_meta_fun_kseq_NA.
    rw @meta_fun_kseq_NA_seq2_mk_meta_fun_kseq_NA.
    apply cequivc_update_seq; auto.
Qed.

Definition barind_meta_fun_bar {o} lib (B1 B2 : @CTerm o) v :=
  forall (s1 s2 : CTerm),
    eq_seq lib s1 s2
    -> {m : nat , meta_fun_on_seq lib B1 B2 m (seq2kseq s1 m v) (seq2kseq s2 m v) }.

Definition barind_meta_fun_imp {o} lib (B1 B2 X1 X2 : @CTerm o) :=
  forall (n : nat) (s1 s2 : CTerm),
    eq_kseq lib s1 s2 n
    -> meta_fun_on_seq lib B1 B2 n s1 s2
    -> meta_fun_on_seq lib X1 X2 n s1 s2.

Lemma cequivc_preserves_meta_fun_on_seq_left {o} :
  forall lib (A1 A2 : @CTerm o) n s1 s2 s,
    cequivc lib s1 s
    -> meta_fun_on_seq lib A1 A2 n s1 s2
    -> meta_fun_on_seq lib A1 A2 n s s2.
Proof.
  introv ceq m.
  allunfold @meta_fun_on_seq; repnd.
  dands.
  - eapply inhabited_type_cequivc;[|exact m0].
    apply implies_cequivc_apply2; auto.
  - eapply tequality_respects_cequivc_left;[|exact m].
    apply implies_cequivc_apply2; auto.
Qed.

Lemma cequivc_preserves_meta_fun_on_seq_right {o} :
  forall lib (A1 A2 : @CTerm o) n s1 s2 s,
    cequivc lib s2 s
    -> meta_fun_on_seq lib A1 A2 n s1 s2
    -> meta_fun_on_seq lib A1 A2 n s1 s.
Proof.
  introv ceq m.
  allunfold @meta_fun_on_seq; repnd.
  dands; auto.
  eapply tequality_respects_cequivc_right;[|exact m].
  apply implies_cequivc_apply2; auto.
Qed.

Lemma cequivc_preserves_not_meta_fun_on_seq_left {o} :
  forall lib (A1 A2 : @CTerm o) n s1 s2 s,
    cequivc lib s1 s
    -> !meta_fun_on_seq lib A1 A2 n s1 s2
    -> !meta_fun_on_seq lib A1 A2 n s s2.
Proof.
  introv ceq h m.
  allunfold @meta_fun_on_seq; repnd.
  destruct h; dands.
  - eapply inhabited_type_cequivc;[|exact m0].
    apply implies_cequivc_apply2; auto.
    apply cequivc_sym; auto.
  - eapply tequality_respects_cequivc_left;[|exact m].
    apply implies_cequivc_apply2; auto.
    apply cequivc_sym; auto.
Qed.

Lemma cequivc_preserves_not_meta_fun_on_seq_right {o} :
  forall lib (A1 A2 : @CTerm o) n s1 s2 s,
    cequivc lib s2 s
    -> !meta_fun_on_seq lib A1 A2 n s1 s2
    -> !meta_fun_on_seq lib A1 A2 n s1 s.
Proof.
  introv ceq h m.
  allunfold @meta_fun_on_seq; repnd.
  destruct h; dands; auto.
  eapply tequality_respects_cequivc_right;[|exact m].
  apply implies_cequivc_apply2; auto.
  apply cequivc_sym; auto.
Qed.

Lemma bar_induction_meta3 {o} :
  forall lib (B1 B2 X1 X2 c1 c2 : @CTerm o) v,
    barind_meta_fun_bar lib B1 B2 v
    -> barind_meta_fun_imp lib B1 B2 X1 X2
    -> barind_meta_fun_ind lib X1 X2 v
    -> meta_fun_on_seq lib X1 X2 0 (seq2kseq c1 0 v) (seq2kseq c2 0 v).
Proof.
  introv bar imp ind.
  pose proof (classic (meta_fun_on_seq lib X1 X2 0 (seq2kseq c1 0 v) (seq2kseq c2 0 v))) as ni.
  repndors; auto.
  provefalse.

  apply barind_meta_fun_ind_implies_cont in ind.
  apply barind_meta_fun_ind_cont_implies_cont2 in ind.
  apply barind_meta_fun_ind_cont2_implies_cont3 in ind.
  unfold barind_meta_fun_ind_cont3 in ind; exrepnd.
  rename ind0 into ind.

  remember (seq_normalizable_seq2kseq lib c1 0 v) as nc1.
  remember (seq_normalizable_seq2kseq lib c2 0 v) as nc2.
  clear Heqnc1 Heqnc2.

  pose proof (cequivc_seq2kseq_0 lib v c1 c2) as ceq0.

  remember (m_fun_alpha lib X1 X2 (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2 ni f ind) as g.
  remember (fun m => meta_fun_kseq_NA_nat (g m)) as s.

  assert (forall n, eq_kseq lib (mkc_nseq s) (meta_fun_kseq_NA_seq1 (g n)) n) as e.
  { introv.
    apply implies_equality_natk2nat; introv ltm.
    subst.
    exists (meta_fun_kseq_NA_nat (m_fun_alpha lib X1 X2 (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2 ni f ind m)).
    dands.

    - apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta_nseq|].
      simpl; auto.

    - pose proof (m_fun_alpha_prop1 lib X1 X2 (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2 ni f ind n (S m)) as q.
      autodimp q hyp; try omega.
      apply (equality_natk2nat_implies lib m) in q; try omega.
      exrepnd.

      apply cequivc_nat_implies_computes_to_valc.
      apply computes_to_valc_implies_cequivc in q1.
      apply computes_to_valc_implies_cequivc in q0.

      apply cequivc_sym in q1.
      eapply cequivc_trans in q1;[|exact q0].
      clear q0.
      eapply cequivc_trans;[apply cequivc_sym;exact q1|].
      clear q1.
      simpl.

      remember (m_fun_alpha lib X1 X2 (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2 ni f ind m) as am.
      unfold meta_fun_kseq_NA in am; exrepnd; simphyps.
      rw @meta_fun_kseq_NA_seq1_mk_meta_fun_kseq_NA.
      unfold update_seq.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; auto; try omega.
  }

  pose proof (m_fun_alpha_prop3
                lib X1 X2
                (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2
                ni f ind) as ceqn.
  rw <- Heqg in ceqn.

  pose proof (bar (mkc_nseq s) (mkc_nseq s)) as b.
  autodimp b hyp; eauto 3 with slow.
  exrepnd.
  rename b0 into b.

  apply imp in b;[|apply implies_is_kseq_seq2kseq; eauto 3 with slow].

  induction m; allsimpl.

  { pose proof (eq_kseq_0 lib (mkc_nseq s) c1) as h1.
    apply (seq2kseq_prop2 _ v) in h1.
    pose proof (eq_kseq_0 lib (mkc_nseq s) c2) as h2.
    apply (seq2kseq_prop2 _ v) in h2.
    eapply cequivc_preserves_meta_fun_on_seq_left in b;[|exact h1].
    eapply cequivc_preserves_meta_fun_on_seq_right in b;[|exact h2].
    auto.
  }

  pose proof (e (S m)) as q1.
  apply (seq2kseq_prop2 _ v) in q1.

  pose proof (ceqn (S m)) as ceqsm.
  apply (implies_cequivc_seq2kseq _ v (S m)) in ceqsm.

  eapply cequivc_preserves_meta_fun_on_seq_left in b;[|exact q1].
  eapply cequivc_preserves_meta_fun_on_seq_right in b;[|exact q1].
  eapply cequivc_preserves_meta_fun_on_seq_right in b;[|exact ceqsm].

  pose proof (e m) as q2.
  apply (seq2kseq_prop2 _ v) in q2.

  pose proof (ceqn m) as ceqm.
  apply (implies_cequivc_seq2kseq _ v m) in ceqm.

  eapply cequivc_preserves_not_meta_fun_on_seq_left in IHm;[|exact q2].
  eapply cequivc_preserves_not_meta_fun_on_seq_right in IHm;[|exact q2].
  eapply cequivc_preserves_not_meta_fun_on_seq_right in IHm;[|exact ceqm].
  clear q1 q2 e ceqsm ceqm.

  subst; allsimpl.
  remember (m_fun_alpha lib X1 X2 (seq2kseq c1 0 v) (seq2kseq c2 0 v) v nc1 nc2 ni f ind m) as am.
  unfold meta_fun_kseq_NA in am; exrepnd; allsimpl.

  remember (f (mk_meta_fun_seq_NA (S m) s1 s2 am1 am0)) as fn.

  assert (eq_kseq lib (update_seq s1 (S m) fn v) s1 (S m)) as ee1.
  { unfold eq_kseq.
    apply implies_equality_natk2nat; introv ltm1.
    dup am1 as e.
    unfold eq_kseq in e.
    eapply equality_natk2nat_implies in e;[|exact ltm1]; exrepnd.
    exists k; dands; auto.
    unfold update_seq.
    apply cequivc_nat_implies_computes_to_valc.
    eapply cequivc_trans;[apply cequivc_beta|].
    allrw @mkcv_inteq_substc.
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @csubst_mk_cv.
    eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
    boolvar; tcsp; GC; try omega.
    apply computes_to_valc_implies_cequivc; auto.
  }

  assert (eq_kseq lib (update_seq s2 (S m) fn v) s2 (S m)) as ee2.
  { unfold eq_kseq.
    apply implies_equality_natk2nat; introv ltm1.
    dup am1 as e.
    unfold eq_kseq in e.
    eapply equality_natk2nat_implies in e;[|exact ltm1]; exrepnd.
    exists k; dands; auto.
    unfold update_seq.
    apply cequivc_nat_implies_computes_to_valc.
    eapply cequivc_trans;[apply cequivc_beta|].
    allrw @mkcv_inteq_substc.
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @csubst_mk_cv.
    eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
    boolvar; tcsp; GC; try omega.
    apply computes_to_valc_implies_cequivc; auto.
  }

  apply (seq2kseq_prop2 _ v) in ee1.
  apply (seq2kseq_prop2 _ v) in ee2.
  eapply cequivc_preserves_meta_fun_on_seq_left in b;[|exact ee1].
  eapply cequivc_preserves_meta_fun_on_seq_right in b;[|exact ee2].
  clear ee1 ee2.

  unfold seq_normalizable in am2.
  unfold seq_normalizable in am3.
  eapply cequivc_preserves_meta_fun_on_seq_left in b;
    [|apply cequivc_sym;exact am2].
  eapply cequivc_preserves_meta_fun_on_seq_right in b;
    [|apply cequivc_sym;exact am3].
  sp.
Qed.


Definition meta2_fun_on_seq {o} lib P (A1 : @CTerm o) (n : nat) (s1 : CTerm) :=
  forall A2 s2,
    eq_kseq lib s1 s2 n
    -> P A2
    -> inhabited_type lib (mkc_apply2 A1 (mkc_nat n) s1)
       # tequality lib (mkc_apply2 A1 (mkc_nat n) s1) (mkc_apply2 A2 (mkc_nat n) s2).

Definition meta2_fun_on_upd_seq {o} lib P (X s : @CTerm o) (n m : nat) (v : NVar) :=
  meta2_fun_on_seq lib P X (S n) (update_seq s n m v).

Definition barind_meta2_fun_ind {o} lib P (X : @CTerm o) v :=
  forall (n : nat) (s : CTerm),
    is_kseq lib s n
    -> (forall (m : nat), meta2_fun_on_upd_seq lib P X s n m v)
    -> meta2_fun_on_seq lib P X n s.

Definition barind_meta2_fun_ind_cont {o} lib P (X : @CTerm o) v :=
  forall (n : nat) (s : CTerm),
    is_kseq lib s n
    -> !meta2_fun_on_seq lib P X n s
    -> {m : nat , !meta2_fun_on_upd_seq lib P X s n m v}.

Definition meta2_fun_seq_NA {o} lib P (X : @CTerm o) :=
  {n : nat
   & {s : CTerm
   & is_kseq lib s n
   # !meta2_fun_on_seq lib P X n s }}.

Definition mk_meta2_fun_seq_NA {o} {lib} {P} {X : @CTerm o}
           (n : nat)
           (s : CTerm)
           (i : is_kseq lib s n)
           (p : !meta2_fun_on_seq lib P X n s) : meta2_fun_seq_NA lib P X :=
  existT _ n (existT _ s (i,p)).

Definition meta2_fun_seq_NA_nat {o} {lib} {P} {X : @CTerm o} (x : meta2_fun_seq_NA lib P X) : nat :=
  projT1 x.

Definition meta2_fun_seq_NA_seq {o} {lib} {P} {X : @CTerm o} (x : meta2_fun_seq_NA lib P X) : CTerm :=
  match x with
    | existT _ (existT s _) => s
  end.

Definition barind_meta2_fun_ind_cont2 {o} lib P (X : @CTerm o) v :=
  forall (x : meta2_fun_seq_NA lib P X),
    {m : nat
     , !meta2_fun_on_upd_seq
        lib P X
        (meta2_fun_seq_NA_seq x)
        (meta2_fun_seq_NA_nat x)
        m v}.

Definition barind_meta2_fun_ind_cont3 {o} lib P (X : @CTerm o) v :=
  {f : meta2_fun_seq_NA lib P X -> nat
   , forall a : meta2_fun_seq_NA lib P X,
       !meta2_fun_on_upd_seq
          lib P X
          (meta2_fun_seq_NA_seq a)
          (meta2_fun_seq_NA_nat a)
          (f a) v}.

Lemma barind_meta2_fun_ind_implies_cont {o} :
  forall lib P (X : @CTerm o) v,
    barind_meta2_fun_ind lib P X v
    -> barind_meta2_fun_ind_cont lib P X v.
Proof.
  introv ind i ni.
  pose proof (ind n s i) as h; clear ind.
  apply contraposition in h; auto.
  (* We use Markov's principle *)
  apply not_all_ex_not in h; auto.
Qed.

Lemma barind_meta2_fun_ind_cont_implies_cont2 {o} :
  forall lib P (X : @CTerm o) v,
    barind_meta2_fun_ind_cont lib P X v
    -> barind_meta2_fun_ind_cont2 lib P X v.
Proof.
  introv ind; introv.
  unfold meta2_fun_seq_NA in x; exrepnd.
  pose proof (ind n s x0 x1) as h; clear ind.
  simpl; auto.
Qed.

Lemma barind_meta2_fun_ind_cont2_implies_cont3 {o} :
  forall lib P (X : @CTerm o) v,
    barind_meta2_fun_ind_cont2 lib P X v
    -> barind_meta2_fun_ind_cont3 lib P X v.
Proof.
  introv ind; introv.
  unfold barind_meta2_fun_ind_cont2 in ind.
  apply FunctionalChoice_on in ind; auto.
Qed.

Definition meta2_fun_kseq_NA {o} lib P (n : nat) (A : @CTerm o) v :=
  {m : nat
   & {s : CTerm
   & is_kseq lib s (S n)
   # seq_normalizable lib s (S n) v
   # meta_kseq_at_is lib s n m
   # !meta2_fun_on_seq lib P A (S n) s }}.

Definition mk_meta2_fun_kseq_NA {o} {lib} {P} {n : nat} {A : @CTerm o} {v}
           (m : nat)
           (s : CTerm)
           (i : is_kseq lib s (S n))
           (q : seq_normalizable lib s (S n) v)
           (e : meta_kseq_at_is lib s n m)
           (p : !meta2_fun_on_seq lib P A (S n) s) : meta2_fun_kseq_NA lib P n A v :=
  existT _ m (existT _ s (i,(q,(e,p)))).

Definition meta2_fun_kseq_NA_nat {o} {lib} {P} {n : nat} {A : @CTerm o} {v}
           (x : meta2_fun_kseq_NA lib P n A v) : nat:=
  match x with
    | existT m _ => m
  end.

Definition meta2_fun_kseq_NA_seq {o} {lib} {P} {n : nat} {A : @CTerm o} {v}
           (x : meta2_fun_kseq_NA lib P n A v) : CTerm:=
  match x with
    | existT _ (existT s _) => s
  end.

Fixpoint meta2_fun_alpha {o}
         (lib : library)
         P
         (X c : @CTerm o)
         (v : NVar)
         (q : seq_normalizable lib c 0 v)
         (h : !meta2_fun_on_seq lib P X 0 c)
         (f : meta2_fun_seq_NA lib P X -> nat)
         (ind : forall a : meta2_fun_seq_NA lib P X,
                  !meta2_fun_on_upd_seq
                     lib P X
                     (meta2_fun_seq_NA_seq a)
                     (meta2_fun_seq_NA_nat a) (f a) v)
         (n : nat) : meta2_fun_kseq_NA lib P n X v :=
  match n with
    | 0 =>
      let i := is_kseq_0 lib c in
      let p := mk_meta2_fun_seq_NA 0 c i h in
      let k := f p in
      mk_meta2_fun_kseq_NA
        k
        (update_seq c 0 k v)
        (is_kseq_update lib c 0 k v i)
        (seq_normalizable_update lib c 0 k v q)
        (meta_kseq_at_is_update lib c 0 k v)
        (ind p)
    | S m =>
      let (_,r) := meta2_fun_alpha lib P X c v q h f ind m in
      let (s,r) := r in
      let (i,r) := r in
      let (z,r) := r in
      let (e,na) := r in
      let p := mk_meta2_fun_seq_NA (S m) s i na in
      let k := f p in
      mk_meta2_fun_kseq_NA
        k
        (update_seq s (S m) k v)
        (is_kseq_update lib s (S m) k v i)
        (seq_normalizable_update lib s (S m) k v z)
        (meta_kseq_at_is_update lib s (S m) k v)
        (ind p)
  end.

Lemma meta2_fun_kseq_NA_seq_mk_meta2_fun_kseq_NA {o} :
  forall lib P n (A : @CTerm o) v m s i q e p,
    meta2_fun_kseq_NA_seq (@mk_meta2_fun_kseq_NA o lib P n A v m s i q e p) = s.
Proof. sp. Qed.

Lemma meta2_fun_alpha_prop1 {o} :
  forall lib P
         (X c : @CTerm o)
         (v : NVar)
         (q : seq_normalizable lib c 0 v)
         (h : !meta2_fun_on_seq lib P X 0 c)
         (f : meta2_fun_seq_NA lib P X -> nat)
         (ind : forall a : meta2_fun_seq_NA lib P X,
                  !meta2_fun_on_upd_seq
                     lib P X
                     (meta2_fun_seq_NA_seq a)
                     (meta2_fun_seq_NA_nat a) (f a) v)
         (n m : nat)
         (lemn : m <= n),
    equality
      lib
      (meta2_fun_kseq_NA_seq (meta2_fun_alpha lib P X c v q h f ind n))
      (meta2_fun_kseq_NA_seq (meta2_fun_alpha lib P X c v q h f ind m))
      (natk2nat (mkc_nat m)).
Proof.
  introv lemn.
  assert {k : nat & n = k + m} as e.
  { exists (n - m); omega. }
  exrepnd; subst.
  clear lemn.
  induction k; introv; allsimpl; apply implies_equality_natk2nat; introv ltm0.

  - remember (meta2_fun_alpha lib P X c v q h f ind m) as am.
    unfold meta2_fun_kseq_NA in am; exrepnd; allsimpl.

    dup am0 as i.
    apply (is_kseq_implies lib m0) in i; try omega; exrepnd.
    exists k; dands; auto.

  - remember (meta2_fun_alpha lib P X c v q h f ind (k + m)) as am.
    unfold meta2_fun_kseq_NA in am; exrepnd; simphyps.
    rw @meta2_fun_kseq_NA_seq_mk_meta2_fun_kseq_NA.

    eapply equality_natk2nat_implies in IHk;[|exact ltm0].
    exrepnd.
    exists k0; dands; auto.

    unfold update_seq.
    apply cequivc_nat_implies_computes_to_valc.
    eapply cequivc_trans;[apply cequivc_beta|].
    allrw @mkcv_inteq_substc.
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @csubst_mk_cv.
    eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
    boolvar; tcsp; GC; try omega.
    apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma is_kseq_seq2kseq_0 {o} :
  forall lib v (s : @CTerm o),
    is_kseq lib (seq2kseq s 0 v) 0.
Proof.
  introv.
  apply implies_equality_natk2nat.
  introv ltm; omega.
Qed.

Definition barind_meta2_fun_bar {o} lib Q (B : @CTerm o) v :=
  forall (s : CTerm),
    is_seq lib s
    -> {m : nat , meta2_fun_on_seq lib Q B m (seq2kseq s m v) }.

Definition barind_meta2_fun_imp {o} lib Q P (B X : @CTerm o) :=
  forall (n : nat) (s : CTerm),
    is_kseq lib s n
    -> meta2_fun_on_seq lib Q B n s
    -> meta2_fun_on_seq lib P X n s.

Lemma cequivc_preserves_eq_kseq_left {o} :
  forall lib (s s1 s2 : @CTerm o) n,
    cequivc lib s1 s2
    -> eq_kseq lib s1 s n
    -> eq_kseq lib s2 s n.
Proof.
  introv ceq ek.
  allunfold @eq_kseq.
  eapply equality_respects_cequivc_left;[|exact ek]; auto.
Qed.

Lemma cequivc_preserves_eq_kseq_right {o} :
  forall lib (s s1 s2 : @CTerm o) n,
    cequivc lib s1 s2
    -> eq_kseq lib s s1 n
    -> eq_kseq lib s s2 n.
Proof.
  introv ceq ek.
  allunfold @eq_kseq.
  eapply equality_respects_cequivc_right;[|exact ek]; auto.
Qed.

Lemma cequivc_preserves_meta2_fun_on_seq {o} :
  forall lib P (A : @CTerm o) n s1 s2,
    cequivc lib s1 s2
    -> meta2_fun_on_seq lib P A n s1
    -> meta2_fun_on_seq lib P A n s2.
Proof.
  introv ceq m.
  allunfold @meta2_fun_on_seq; repnd.
  introv ek p.
  pose proof (m A2 s0) as h; clear m.
  repeat (autodimp h hyp).
  { eapply cequivc_preserves_eq_kseq_left;[|exact ek]; auto.
    apply cequivc_sym; auto. }
  repnd.
  dands.
  - eapply inhabited_type_cequivc;[|exact h0].
    apply implies_cequivc_apply2; auto.
  - eapply tequality_respects_cequivc_left;[|exact h].
    apply implies_cequivc_apply2; auto.
Qed.

Lemma cequivc_preserves_not_meta2_fun_on_seq {o} :
  forall lib P (A : @CTerm o) n s1 s2,
    cequivc lib s1 s2
    -> !meta2_fun_on_seq lib P A n s1
    -> !meta2_fun_on_seq lib P A n s2.
Proof.
  introv ceq h m.
  allunfold @meta2_fun_on_seq; repnd.
  destruct h.
  introv ek p.
  pose proof (m A2 s0) as h; clear m.
  repeat (autodimp h hyp).
  { eapply cequivc_preserves_eq_kseq_left;[|exact ek]; auto. }
  repnd.
  dands.
  - eapply inhabited_type_cequivc;[|exact h0].
    apply implies_cequivc_apply2; auto.
    apply cequivc_sym; auto.
  - eapply tequality_respects_cequivc_left;[|exact h].
    apply implies_cequivc_apply2; auto.
    apply cequivc_sym; auto.
Qed.

Lemma bar_induction_meta4 {o} :
  forall lib Q P (B X c : @CTerm o) v,
    barind_meta2_fun_bar lib Q B v
    -> barind_meta2_fun_imp lib Q P B X
    -> barind_meta2_fun_ind lib P X v
    -> meta2_fun_on_seq lib P X 0 (seq2kseq c 0 v).
Proof.
  introv bar imp ind.
  pose proof (classic (meta2_fun_on_seq lib P X 0 (seq2kseq c 0 v))) as ni.
  repndors; auto.
  provefalse.

  apply barind_meta2_fun_ind_implies_cont in ind.
  apply barind_meta2_fun_ind_cont_implies_cont2 in ind.
  apply barind_meta2_fun_ind_cont2_implies_cont3 in ind.
  unfold barind_meta2_fun_ind_cont3 in ind; exrepnd.
  rename ind0 into ind.

  remember (seq_normalizable_seq2kseq lib c 0 v) as nc.
  clear Heqnc.

  remember (meta2_fun_alpha lib P X (seq2kseq c 0 v) v nc ni f ind) as g.
  remember (fun m => meta2_fun_kseq_NA_nat (g m)) as s.

  assert (forall n, eq_kseq lib (mkc_nseq s) (meta2_fun_kseq_NA_seq (g n)) n) as e.
  { introv.
    apply implies_equality_natk2nat; introv ltm.
    subst.
    exists (meta2_fun_kseq_NA_nat (meta2_fun_alpha lib P X (seq2kseq c 0 v) v nc ni f ind m)).
    dands.

    - apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta_nseq|].
      simpl; auto.

    - pose proof (meta2_fun_alpha_prop1 lib P X (seq2kseq c 0 v) v nc ni f ind n (S m)) as q.
      autodimp q hyp; try omega.
      apply (equality_natk2nat_implies lib m) in q; try omega.
      exrepnd.

      apply cequivc_nat_implies_computes_to_valc.
      apply computes_to_valc_implies_cequivc in q1.
      apply computes_to_valc_implies_cequivc in q0.

      apply cequivc_sym in q1.
      eapply cequivc_trans in q1;[|exact q0].
      clear q0.
      eapply cequivc_trans;[apply cequivc_sym;exact q1|].
      clear q1.
      simpl.

      remember (meta2_fun_alpha lib P X (seq2kseq c 0 v) v nc ni f ind m) as am.
      unfold meta2_fun_kseq_NA in am; exrepnd; simphyps.
      rw @meta2_fun_kseq_NA_seq_mk_meta2_fun_kseq_NA.
      unfold update_seq.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; auto; try omega.
  }

  pose proof (bar (mkc_nseq s)) as b.
  autodimp b hyp; eauto 3 with slow.
  exrepnd.
  rename b0 into b.

  apply imp in b;[|apply implies_is_kseq_seq2kseq; eauto 3 with slow].

  induction m; allsimpl.

  { pose proof (eq_kseq_0 lib (mkc_nseq s) c) as h1.
    apply (seq2kseq_prop2 _ v) in h1.
    eapply cequivc_preserves_meta2_fun_on_seq in b;[|exact h1].
    auto.
  }

  pose proof (e (S m)) as q1.
  apply (seq2kseq_prop2 _ v) in q1.

  eapply cequivc_preserves_meta2_fun_on_seq in b;[|exact q1].

  pose proof (e m) as q2.
  apply (seq2kseq_prop2 _ v) in q2.

  eapply cequivc_preserves_not_meta2_fun_on_seq in IHm;[|exact q2].
  clear q1 q2 e.

  subst; allsimpl.
  remember (meta2_fun_alpha lib P X (seq2kseq c 0 v) v nc ni f ind m) as am.
  unfold meta2_fun_kseq_NA in am; exrepnd; allsimpl.

  remember (f (mk_meta2_fun_seq_NA (S m) s am0 am1)) as fn.

  assert (eq_kseq lib (update_seq s (S m) fn v) s (S m)) as ee1.
  { unfold eq_kseq.
    apply implies_equality_natk2nat; introv ltm1.
    dup am0 as e.
    eapply member_natk2nat_implies in e;[|exact ltm1]; exrepnd.
    exists k; dands; auto.
    unfold update_seq.
    apply cequivc_nat_implies_computes_to_valc.
    eapply cequivc_trans;[apply cequivc_beta|].
    allrw @mkcv_inteq_substc.
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @csubst_mk_cv.
    eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
    boolvar; tcsp; GC; try omega.
    apply computes_to_valc_implies_cequivc; auto.
  }

  apply (seq2kseq_prop2 _ v) in ee1.
  eapply cequivc_preserves_meta2_fun_on_seq in b;[|exact ee1].
  clear ee1.

  unfold seq_normalizable in am2.
  eapply cequivc_preserves_meta2_fun_on_seq in b;
    [|apply cequivc_sym;exact am2].
  sp.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
