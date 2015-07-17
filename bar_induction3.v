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


Require Export bar_induction2.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export per_props_equality.
Require Export per_props_nat.


(* !!MOVE *)
Lemma member_mkc_squash {p} :
  forall lib (T : @CTerm p),
    member lib mkc_axiom (mkc_squash T)
    <=> inhabited_type lib T.
Proof.
  intros.
  rw @equality_in_mkc_squash.
  split; intro h; repnd; dands; auto; spcast;
  apply computes_to_valc_refl; eauto 3 with slow.
Qed.

Lemma cover_vars_var_iff {o} :
  forall (v : NVar) (sub : @CSub o),
    cover_vars (mk_var v) sub <=> LIn v (dom_csub sub).
Proof.
  introv; split; introv h; try (apply cover_vars_var;auto).
  rw @cover_vars_eq in h; allsimpl.
  allrw subvars_singleton_l; auto.
Qed.

Lemma free_vars_mk_natk2nat {o} :
  forall v, @free_vars o (mk_natk2nat (mk_var v)) = [v].
Proof.
  introv; simpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw remove_nvars_cons.
  allrw remove_nvars_nil_l.

  pose proof (@newvar_prop o (mk_var v)) as nvp.
  remember (newvar (mk_var v)) as nv.
  clear Heqnv; simphyps.
  allrw not_over_or; repnd; GC.

  pose proof (@newvar_prop o (mk_less_than (mk_var nv) (mk_var v))) as nvp'.
  remember (newvar (mk_less_than (mk_var nv) (mk_var v))) as nv'.
  clear Heqnv'; simphyps.
  allrw not_over_or; repnd; GC.

  allsimpl; boolvar; tcsp.
  simpl.
  boolvar; tcsp.
Qed.

Lemma lsubstc_mk_natk2nat_sp2 {o} :
  forall v (t : @CTerm o) w s c,
    !LIn v (dom_csub s)
    -> alphaeqc
         (lsubstc (mk_natk2nat (mk_var v)) w (snoc s (v,t)) c)
         (natk2nat t).
Proof.
  introv niv.

  assert (cover_vars (mk_natk2nat (mk_var v)) ((v, t) :: s)) as cv.
  { allrw @cover_vars_mk_natk2nat.
    allrw @cover_vars_var_iff.
    allsimpl.
    allrw @dom_csub_snoc; allsimpl.
    allrw in_snoc; sp. }

  pose proof (lsubstc_mk_natk2nat_sp1 v t w s cv) as h.
  eapply alphaeqc_trans;[|exact h].

  unfold alphaeqc; simpl.
  apply alpha_eq_lsubst_if_ext_eq; auto.
  unfold ext_alpha_eq_subs.
  rw @free_vars_mk_natk2nat; simpl.
  introv e; repndors; tcsp; subst.
  boolvar; tcsp.
  rw @csub2sub_snoc.
  rw @sub_find_snoc.
  boolvar.
  rw @sub_find_none_if; eauto 3 with slow.
  rw @dom_csub_eq; auto.
Qed.

Lemma mkc_nat_eq_implies {o} :
  forall n m, @mkc_nat o n = mkc_nat m -> n = m.
Proof.
  introv h.
  inversion h as [q].
  apply Znat.Nat2Z.inj in q; auto.
Qed.

Lemma wf_tnat {p} : @wf_term p mk_tnat.
Proof.
  sp.
Qed.

Lemma wf_or {o} :
  forall (a b : @NTerm o),
    wf_term (mk_or a b) <=> (wf_term a # wf_term b).
Proof.
  introv.
  unfold mk_or.
  rw @wf_union; sp.
Qed.

Lemma wf_dec {o} :
  forall (a : @NTerm o),
    wf_term (mk_dec a) <=> wf_term a.
Proof.
  introv.
  unfold mk_dec.
  rw @wf_or.
  rw @wf_not.
  split; sp.
Qed.

Lemma cover_vars_union {o} :
  forall (a b : @NTerm o) s,
    cover_vars (mk_union a b) s <=> (cover_vars a s # cover_vars b s).
Proof.
  introv.
  allrw @cover_vars_eq; simpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw subvars_app_l; sp.
Qed.

Lemma cover_vars_or {o} :
  forall (a b : @NTerm o) s,
    cover_vars (mk_or a b) s <=> (cover_vars a s # cover_vars b s).
Proof.
  introv.
  unfold mk_or.
  rw @cover_vars_union; sp.
Qed.

Lemma cover_vars_dec {o} :
  forall (a : @NTerm o) s,
    cover_vars (mk_dec a) s <=> cover_vars a s.
Proof.
  introv.
  unfold mk_dec.
  rw @cover_vars_or.
  rw @cover_vars_not.
  split; sp.
Qed.

Lemma covered_union {o} :
  forall (a b : @NTerm o) vs,
    covered (mk_union a b) vs <=> (covered a vs # covered b vs).
Proof.
  introv.
  unfold covered; simpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw subvars_app_l; sp.
Qed.

Lemma covered_or {o} :
  forall (a b : @NTerm o) vs,
    covered (mk_or a b) vs <=> (covered a vs # covered b vs).
Proof.
  introv.
  unfold mk_or.
  rw @covered_union; sp.
Qed.

Lemma covered_not {o} :
  forall (a : @NTerm o) vs,
    covered (mk_not a) vs <=> covered a vs.
Proof.
  introv.
  unfold mk_not.
  rw @covered_fun.
  split; sp.
Qed.

Lemma covered_dec {o} :
  forall (a : @NTerm o) vs,
    covered (mk_dec a) vs <=> covered a vs.
Proof.
  introv.
  unfold mk_dec.
  rw @covered_or.
  rw @covered_not.
  split; sp.
Qed.

Lemma covered_snoc_implies {o} :
  forall (t : @NTerm o) (v : NVar) (vs : list NVar),
    !LIn v (free_vars t)
    -> covered t (snoc vs v)
    -> covered t vs.
Proof.
  introv ni cov.
  allunfold @covered; allsimpl.
  allrw subvars_eq.
  introv i.
  applydup cov in i.
  allrw in_snoc.
  repndors; subst; tcsp.
Qed.

Lemma wf_term_mk_nat2nat {o} : @wf_term o mk_nat2nat.
Proof.
  introv.
  unfold mk_nat2nat.
  apply wf_fun; dands; apply wf_tnat.
Qed.

Lemma cover_vars_mk_nat2nat {o} :
  forall (s : @CSub o), cover_vars mk_nat2nat s.
Proof.
  introv.
  unfold mk_nat2nat.
  apply cover_vars_fun; dands; apply cover_vars_mk_tnat.
Qed.

Definition mk_update_seq {o} (s n m : @NTerm o) v :=
  mk_lam v (mk_int_eq (mk_var v) n m (mk_apply s (mk_var v))).

Definition mk_seq2kseq {o} (s n : @NTerm o) (v : NVar) : NTerm :=
  mk_lam
    v
    (mk_less
       (mk_var v)
       mk_zero
       mk_bot
       (mk_less
          (mk_var v)
          n
          (mk_apply s (mk_var v))
          mk_bot)).

Lemma wf_seq2kseq {o} :
  forall (t : @NTerm o) n v,
    wf_term (mk_seq2kseq t n v) <=> (wf_term t # wf_term n).
Proof.
  introv.
  unfold mk_seq2kseq.
  rw <- @wf_lam_iff.
  allrw <- @wf_less_iff.
  rw <- @wf_apply_iff.
  split; intro h; repnd; dands; eauto 3 with slow.
Qed.

Lemma cover_vars_upto_mk_nat {o} :
  forall n (s : @CSub o) vs,
    cover_vars_upto (mk_nat n) s vs.
Proof.
  introv.
  unfold cover_vars_upto; simpl; sp.
Qed.
Hint Resolve cover_vars_upto_mk_nat : slow.

Lemma cover_vars_seq2kseq {o} :
  forall (t : @NTerm o) n v s,
    !LIn v (free_vars t)
    -> !LIn v (free_vars n)
    -> (cover_vars (mk_seq2kseq t n v) s <=> (cover_vars t s # cover_vars n s)).
Proof.
  introv nit niv.
  unfold mk_seq2kseq.
  rw @cover_vars_lam.
  allrw @cover_vars_upto_less.
  allrw @cover_vars_upto_apply.
  allrw @cover_vars_upto_var.
  allsimpl.
  split; intro h; repnd; dands; eauto 3 with slow.
  - apply cover_vars_upto_csub_filter_disjoint in h6; auto.
    apply disjoint_singleton_r; auto.
  - apply cover_vars_upto_csub_filter_disjoint in h4; auto.
    apply disjoint_singleton_r; auto.
  - apply cover_vars_upto_csub_filter_disjoint; auto.
    apply disjoint_singleton_r; auto.
  - apply cover_vars_upto_csub_filter_disjoint; auto.
    apply disjoint_singleton_r; auto.
Qed.

Lemma csubst_mk_less {o} :
  forall (a b c d : @NTerm o) s,
    csubst (mk_less a b c d) s
    = mk_less (csubst a s) (csubst b s) (csubst c s) (csubst d s).
Proof.
  introv.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd. sp.
Qed.

Lemma csubst_mk_bot {o} :
  forall (sub : @CSub o), csubst mk_bot sub = mk_bot.
Proof.
  introv.
  rw @csubst_trivial; auto.
  simpl; auto.
Qed.

Lemma csubst_mk_nat {o} :
  forall n (sub : @CSub o), csubst (mk_nat n) sub = mk_nat n.
Proof.
  introv.
  rw @csubst_trivial; auto.
  simpl; auto.
Qed.

Definition seq2kseq2 {o} (s n : @CTerm o) (v : NVar) : CTerm :=
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
          (mk_cv [v] n)
          (mkcv_apply [v] (mk_cv [v] s) (mkc_var v))
          (mkcv_bot [v]))).

Lemma seq2kseq2_as_seq2kseq {o} :
  forall lib (s : @CTerm o) n m v,
    computes_to_valc lib n (mkc_nat m)
    -> cequivc lib (seq2kseq2 s n v) (seq2kseq s m v).
Proof.
  introv comp.
  unfold seq2kseq, seq2kseq2.
  apply implies_cequivc_lam; introv.
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @mkcv_bot_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_nat_substc.
  allrw @mkcv_zero_substc.
  allrw @mkc_zero_eq.
  eapply cequivc_mkc_less;
    [apply cequivc_refl
    |apply cequivc_refl
    |apply cequivc_refl
    |eapply cequivc_mkc_less;
      [apply cequivc_refl
      |apply computes_to_valc_implies_cequivc; auto
      |apply cequivc_refl
      |apply cequivc_refl]
    ].
Qed.

Lemma seq2kseq2_as_seq2kseq2 {o} :
  forall (s : @CTerm o) n v,
   seq2kseq2 s (mkc_nat n) v = seq2kseq s n v.
Proof.
  introv.
  apply cterm_eq; simpl; auto.
Qed.

Lemma lsubstc_mk_seq2kseq2 {o} :
  forall (t : @NTerm o) n v w s c,
    !LIn v (free_vars t)
    -> !LIn v (free_vars n)
    -> {wt : wf_term t
        & {ct : cover_vars t s
        & {wn : wf_term n
        & {cn : cover_vars n s
        & lsubstc (mk_seq2kseq t n v) w s c
          = seq2kseq2 (lsubstc t wt s ct) (lsubstc n wn s cn) v }}}}.
Proof.
  introv nit nin.

  assert (wf_term t) as wt.
  { apply wf_seq2kseq in w; sp. }

  assert (cover_vars t s) as ct.
  { apply cover_vars_seq2kseq in c; sp. }

  assert (wf_term n) as wn.
  { apply wf_seq2kseq in w; sp. }

  assert (cover_vars n s) as cn.
  { apply cover_vars_seq2kseq in c; sp. }

  exists wt ct wn cn.
  apply cterm_eq; simpl.
  unfold mk_seq2kseq.
  rw @csubst_mk_lam.
  allrw @csubst_mk_less.
  allrw @csubst_mk_apply.
  allrw @csubst_mk_zero.
  allrw @csubst_mk_bot.
  allrw @csubst_mk_nat.
  repeat (rw @csubst_var_not_in;
          [|rw @dom_csub_csub_filter;rw in_remove_nvars;rw in_single_iff;sp]).
  allrw @csubst_csub_filter; auto; apply disjoint_singleton_r; auto.
Qed.

Lemma lsubstc_mk_nat {o} :
  forall n w (s : @CSub o) c,
    lsubstc (mk_nat n) w s c = mkc_nat n.
Proof.
  unfold lsubstc, mkc_axiom; sp.
  apply cterm_eq; sp.
Qed.

Lemma lsubstc_mk_seq2kseq {o} :
  forall (t : @NTerm o) n v w s c,
    !LIn v (free_vars t)
    -> {wt : wf_term t
        & {ct : cover_vars t s
        & lsubstc (mk_seq2kseq t (mk_nat n) v) w s c
          = seq2kseq (lsubstc t wt s ct) n v }}.
Proof.
  introv nit.
  pose proof (lsubstc_mk_seq2kseq2 t (mk_nat n) v w s c) as h.
  simpl in h.
  repeat (autodimp h hyp); tcsp; exrepnd.
  allrw @lsubstc_mk_nat.
  exists wt ct; auto.
  rw @seq2kseq2_as_seq2kseq2 in h1; auto.
Qed.

Lemma implies_cequivc_seq2kseq2 {o} :
  forall lib (v : NVar) (s1 s2 n1 n2 : @CTerm o),
    cequivc lib s1 s2
    -> cequivc lib n1 n2
    -> cequivc lib (seq2kseq2 s1 n1 v) (seq2kseq2 s2 n2 v).
Proof.
  introv ceq1 ceq2.
  unfold seq2kseq2.
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
      |auto
      |apply sp_implies_cequivc_apply;auto
      |apply cequivc_refl]
    ].
Qed.

Lemma implies_cequivc_natk2nat {o} :
  forall lib (t1 t2 : @CTerm o),
    cequivc lib t1 t2
    -> cequivc lib (natk2nat t1) (natk2nat t2).
Proof.
  introv ceq.
  unfold natk2nat.
  apply cequivc_mkc_fun;[|apply cequivc_refl].
  apply cequivc_mkc_natk; auto.
Qed.

Lemma tequality_natk2nat_nat {o} :
  forall lib n,
    @tequality o lib (natk2nat (mkc_nat n)) (natk2nat (mkc_nat n)).
Proof.
  introv.
  apply tequality_natk2nat.
  exists (Z.of_nat n) (Z.of_nat n).
  dands; spcast; try (apply computes_to_valc_refl; eauto 3 with slow).
  introv ltk.
  destruct (Z_lt_le_dec k (Z.of_nat n)); sp.
Qed.
Hint Resolve tequality_natk2nat_nat : slow.

Definition lam_axiom {o} := @mkc_lam o nvarx (mkcv_axiom nvarx).

Lemma cequivc_lsubstc_mk_plus1 {o} :
  forall lib n (w : @wf_term o (mk_plus1 (mk_var n))) m a (sub : @CSub o) n k s t c,
    m <> n
    -> !LIn n (dom_csub sub)
    -> cequivc
         lib
         (lsubstc (mk_plus1 (mk_var n)) w
                  ((m, a) :: snoc (snoc sub (n, mkc_nat k)) (s, t)) c)
         (mkc_nat (S k)).
Proof.
  introv d1 ni.
  unfold cequivc; simpl.
  unfold csubst, mk_plus1.
  rw @cl_lsubst_lsubst_aux; eauto 3 with slow; simpl.
  boolvar; simpl; tcsp.
  allrw @sub_filter_nil_r.
  allrw @csub2sub_snoc.
  allrw @sub_find_snoc.
  rw @sub_find_none_if; auto; try (rw @dom_csub_eq;auto).
  boolvar; tcsp; fold_terms.
  apply reduces_to_implies_cequiv;
    [rw @isprogram_eq; apply isprog_add_implies;eauto 3 with slow|].
  apply reduces_to_if_step; csunf; simpl; dcwf h; simpl; auto.
  unfold mk_nat, mk_integer.

  assert (1%Z = Z.of_nat 1) as e by (simpl; auto).
  rw e.
  rw <- @Znat.Nat2Z.inj_add.
  rw plus_comm; auto.
Qed.

Lemma implies_cequivc_mkc_image {o} :
  forall lib (a b c d : @CTerm o),
    cequivc lib a c
    -> cequivc lib b d
    -> cequivc lib (mkc_image a b) (mkc_image c d).
Proof.
  introv ceq1 ceq2.
  destruct_cterms; allunfold @cequivc; allsimpl.
  destruct ceq1, ceq2.
  split; repeat prove_approx; eauto 3 with slow.
Qed.

Lemma implies_cequivc_mkc_squash {o} :
  forall lib (t u : @CTerm o),
    cequivc lib t u
    -> cequivc lib (mkc_squash t) (mkc_squash u).
Proof.
  introv c.
  unfold mkc_squash.
  apply implies_cequivc_mkc_image; auto.
Qed.

Lemma cequivc_lsubstc_mk_plus1_sp1 {o} :
  forall lib n w (sub : @CSub o) k c,
    !LIn n (dom_csub sub)
    -> cequivc
         lib
         (lsubstc (mk_plus1 (mk_var n)) w
                  (snoc sub (n, mkc_nat k)) c)
         (mkc_nat (S k)).
Proof.
  introv ni.
  unfold cequivc; simpl.
  unfold csubst, mk_plus1.
  rw @cl_lsubst_lsubst_aux; eauto 3 with slow; simpl.
  boolvar; simpl; tcsp.
  allrw @sub_filter_nil_r.
  allrw @csub2sub_snoc.
  allrw @sub_find_snoc.
  rw @sub_find_none_if; auto; try (rw @dom_csub_eq;auto).
  boolvar; tcsp; fold_terms.
  apply reduces_to_implies_cequiv;
    [rw @isprogram_eq; apply isprog_add_implies;eauto 3 with slow|].
  apply reduces_to_if_step; csunf; simpl; dcwf h; simpl; auto.
  unfold mk_nat, mk_integer.

  assert (1%Z = Z.of_nat 1) as e by (simpl; auto).
  rw e.
  rw <- @Znat.Nat2Z.inj_add.
  rw plus_comm; auto.
Qed.

Lemma implies_cequiv_mk_add {o} :
  forall lib (a b c d : @NTerm o),
    cequiv lib a c
    -> cequiv lib b d
    -> cequiv lib (mk_add a b) (mk_add c d).
Proof.
  introv ceq1 ceq2.
  destruct ceq1, ceq2.
  unfold mk_add.
  applydup @approx_relates_only_progs in a0.
  applydup @approx_relates_only_progs in a2.
  repnd.
  split; repeat prove_approx; eauto 3 with slow.
Qed.

Lemma implies_cequivc_mkc_add {o} :
  forall lib (a b c d : @CTerm o),
    cequivc lib a c
    -> cequivc lib b d
    -> cequivc lib (mkc_add a b) (mkc_add c d).
Proof.
  introv ceq1 ceq2.
  destruct_cterms; allunfold @cequivc; allsimpl.
  apply implies_cequiv_mk_add; auto.
Qed.

Lemma cequivc_lsubstc_mk_plus1_sp2 {o} :
  forall lib n w (sub : @CSub o) t k c,
    !LIn n (dom_csub sub)
    -> cequivc lib t (mkc_nat k)
    -> cequivc
         lib
         (lsubstc (mk_plus1 (mk_var n)) w
                  (snoc sub (n,t)) c)
         (mkc_nat (S k)).
Proof.
  introv ni ceq.
  allunfold @cequivc; simpl.
  unfold csubst, mk_plus1.
  rw @cl_lsubst_lsubst_aux; eauto 3 with slow; simpl.
  boolvar; simpl; tcsp.
  allrw @sub_filter_nil_r.
  allrw @csub2sub_snoc.
  allrw @sub_find_snoc.
  rw @sub_find_none_if; auto; try (rw @dom_csub_eq;auto).
  boolvar; tcsp; fold_terms.
  eapply cequiv_trans;
    [apply implies_cequiv_mk_add;
      [exact ceq
      |apply cequiv_refl;eauto 3 with slow]
    |].

  apply reduces_to_implies_cequiv;
    [rw @isprogram_eq; apply isprog_add_implies;eauto 3 with slow|].
  apply reduces_to_if_step; csunf; simpl; dcwf h; simpl; auto.
  unfold mk_nat, mk_integer.

  assert (1%Z = Z.of_nat 1) as e by (simpl; auto).
  rw e.
  rw <- @Znat.Nat2Z.inj_add.
  rw plus_comm; auto.
Qed.

Lemma implies_approx_lam {o} :
  forall lib v (t1 t2 : @NTerm o),
    isprog_vars [v] t1
    -> isprog_vars [v] t2
    -> (forall u : NTerm, isprog u -> cequiv lib (subst t1 v u) (subst t2 v u))
    -> approx lib (mk_lam v t1) (mk_lam v t2).
Proof.
  introv isp1 isp2 imp.

  constructor.
  unfold close_comput; dands;
  try (apply isprogram_lam);
  eauto 3 with slow.

  + introv comp.
    apply computes_to_value_isvalue_eq in comp;
      try (apply isvalue_mk_lam); eauto 3 with slow.
    unfold mk_lam in comp; ginv; fold_terms.
    exists [bterm [v] t2]; fold_terms.
    dands.
    { apply computes_to_value_isvalue_refl;
      try (apply isvalue_mk_lam); eauto 3 with slow. }

    unfold lblift; simpl; dands; auto.
    introv ltn.
    destruct n; try omega; clear ltn.
    unfold selectbt; simpl.
    unfold blift.
    exists [v] t1 t2; dands; eauto 3 with slow.
    apply clearbots_olift.
    apply cl_olift_implies_olift; eauto 3 with slow.

    pose proof (cl_olift_iff_pv_olift (approx lib) t1 t2 [v]) as xx.
    repeat (autodimp xx hyp).
    apply xx; clear xx.
    introv ps e.
    destruct sub as [|p s]; allsimpl; ginv.
    destruct s; ginv.
    destruct p as [z u]; allsimpl.
    allrw @fold_subst.
    allrw @prog_sub_cons; repnd.
    pose proof (imp u) as h; clear imp; allsimpl.
    destruct h; eauto 3 with slow.

  + introv comp.
    apply can_doesnt_raise_an_exception in comp; sp.

  + introv comp.
    apply reduces_to_if_isvalue_like in comp; eauto 3 with slow; ginv.
Qed.

Lemma implies_cequiv_lam {o} :
  forall lib v (t1 t2 : @NTerm o),
    isprog_vars [v] t1
    -> isprog_vars [v] t2
    -> (forall u : NTerm, isprog u -> cequiv lib (subst t1 v u) (subst t2 v u))
    -> cequiv lib (mk_lam v t1) (mk_lam v t2).
Proof.
  introv isp1 isp2 imp.
  split.
  - apply implies_approx_lam; auto.
  - apply implies_approx_lam; auto.
    introv ispu.
    apply cequiv_sym; auto.
Qed.

Lemma lsubst_aux_get_cterm {o} :
  forall (t : @CTerm o) sub,
    lsubst_aux (get_cterm t) sub = get_cterm t.
Proof.
  introv.
  apply lsubst_aux_trivial_cl_term2; eauto 3 with slow.
Qed.

Hint Resolve isprogram_mk_nat : slow.

Lemma cequivc_lsubstc_mk_update_seq_sp1 {o} :
  forall lib s n m v w (sub : @CSub o) a k j t c,
    n <> m
    -> s <> n
    -> s <> m
    -> n <> v
    -> s <> v
    -> m <> v
    -> !LIn n (dom_csub sub)
    -> !LIn s (dom_csub sub)
    -> computes_to_valc lib a (mkc_nat j)
    -> cequivc
         lib
         (lsubstc (mk_update_seq (mk_var s) (mk_var n) (mk_var m) v) w
                  ((m,a) :: snoc (snoc sub (n,mkc_nat k)) (s,t)) c)
         (update_seq t k j v).
Proof.
  introv d1 d2 d3 d4 d5 d6 ni1 ni2 comp.
  unfold cequivc; simpl.
  unfold csubst, mk_update_seq.
  rw @cl_lsubst_lsubst_aux; eauto 3 with slow; simpl.
  allrw memvar_singleton.

  repeat (boolvar; simpl; tcsp;[]).
  allrw @sub_filter_nil_r.
  allrw @csub2sub_snoc.
  allrw @sub_find_sub_filter_eq.
  allrw memvar_singleton.
  repeat (boolvar; simpl; tcsp;[]).
  allrw @sub_find_snoc.
  repeat (rw @sub_find_none_if; auto; try (rw @dom_csub_eq;auto);[]).
  repeat (boolvar; simpl; tcsp; fold_terms;[]).

  apply implies_cequiv_lam;
    try (apply isprog_vars_mk_int_eq; dands);
    try (apply isprog_vars_apply_implies);
    try (apply mk_cv_pf);
    eauto 2 with slow.

  introv ispu.
  unfold subst.
  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow;[]).
  simpl; boolvar; tcsp.
  allrw @lsubst_aux_get_cterm.

  apply cequiv_mk_int_eq;
    [apply cequiv_refl;fold_terms;eauto 3 with slow
    |apply cequiv_refl;fold_terms;eauto 3 with slow
    |
    |apply cequiv_refl;apply isprogram_apply;eauto 3 with slow].

  apply reduces_to_implies_cequiv; eauto 3 with slow.
Qed.

Lemma cequivc_lsubstc_mk_update_seq_sp2 {o} :
  forall lib s n m v w (sub : @CSub o) a k j t u c,
    n <> m
    -> s <> n
    -> s <> m
    -> n <> v
    -> s <> v
    -> m <> v
    -> !LIn n (dom_csub sub)
    -> !LIn s (dom_csub sub)
    -> computes_to_valc lib a (mkc_nat j)
    -> computes_to_valc lib u (mkc_nat k)
    -> cequivc
         lib
         (lsubstc (mk_update_seq (mk_var s) (mk_var n) (mk_var m) v) w
                  ((m,a) :: snoc (snoc sub (n,u)) (s,t)) c)
         (update_seq t k j v).
Proof.
  introv d1 d2 d3 d4 d5 d6 ni1 ni2 comp1 comp2.
  unfold cequivc; simpl.
  unfold csubst, mk_update_seq.
  rw @cl_lsubst_lsubst_aux; eauto 3 with slow; simpl.
  allrw memvar_singleton.

  repeat (boolvar; simpl; tcsp;[]).
  allrw @sub_filter_nil_r.
  allrw @csub2sub_snoc.
  allrw @sub_find_sub_filter_eq.
  allrw memvar_singleton.
  repeat (boolvar; simpl; tcsp;[]).
  allrw @sub_find_snoc.
  repeat (rw @sub_find_none_if; auto; try (rw @dom_csub_eq;auto);[]).
  repeat (boolvar; simpl; tcsp; fold_terms;[]).

  apply implies_cequiv_lam;
    try (apply isprog_vars_mk_int_eq; dands);
    try (apply isprog_vars_apply_implies);
    try (apply mk_cv_pf);
    eauto 2 with slow.

  introv ispu.
  unfold subst.
  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow;[]).
  simpl; boolvar; tcsp.
  allrw @lsubst_aux_get_cterm.

  allunfold @computes_to_valc.
  allunfold @computes_to_value; repnd.

  apply cequiv_mk_int_eq;
    [apply cequiv_refl;eauto 3 with slow
    |apply reduces_to_implies_cequiv;eauto
    |
    |apply cequiv_refl;apply isprogram_apply;eauto 3 with slow].

  apply reduces_to_implies_cequiv; eauto 3 with slow.
Qed.

Lemma cover_vars_upto_add {o} :
  forall (a b : @NTerm o) sub vs,
    cover_vars_upto (mk_add a b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b sub vs.
Proof.
  unfold cover_vars_upto; introv; simpl.
  rw app_nil_r.
  allrw remove_nvars_nil_l.
  rw subvars_app_l; sp.
Qed.

Lemma cover_vars_upto_one {o} :
  forall (sub : @CSub o) vs,
    cover_vars_upto mk_one sub vs.
Proof.
  unfold cover_vars_upto; introv; simpl; auto.
Qed.
Hint Resolve cover_vars_upto_one : slow.

Lemma cover_vars_upto_int_eq {o} :
  forall vs (a b c d : @NTerm o) sub,
    cover_vars_upto (mk_int_eq a b c d) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b sub vs
        # cover_vars_upto c sub vs
        # cover_vars_upto d sub vs.
Proof.
  introv.
  unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw subvars_app_l.
  sp.
Qed.

Lemma eq_kseq_left {o} :
  forall lib (seq1 seq2 : @CTerm o) k,
    eq_kseq lib seq1 seq2 k
    -> eq_kseq lib seq1 seq1 k.
Proof.
  introv e.
  apply equality_refl in e; auto.
Qed.

Lemma cequivc_mkc_apply_lam_axiom {o} :
  forall lib (a : @CTerm o),
    cequivc lib (mkc_apply lam_axiom a) mkc_axiom.
Proof.
  introv.
  unfold lam_axiom.
  eapply cequivc_trans;[apply cequivc_beta|].
  rw @substc_mkcv_axiom; auto.
Qed.

Definition fun_sim_eq {o} lib s1 H (t : @NTerm o) w (u : CTerm) :=
  {s2 : CSub
   & {c2 : cover_vars t s2
   & similarity lib s1 s2 H
   # u = lsubstc t w s2 c2}}.

Ltac clear_wf_hyps :=
  repeat match goal with
           | [ H : cover_vars _ _ |- _ ] => clear H
           | [ H : wf_term _ |- _ ] => clear H
         end.



(**

  Bar induction, where
    T is a type
    R is the spread law
    B is the bar
    con stands for consistent with the spread law
    ext(s,n,t) = \m. if m=n then t else s m
<<
   H |- squash (X 0 c)

     By bar_induction B i a s x m n t

     H, n:nat, s: nat_n -> nat |- (B n s) \/ not(B n s)   // B is decidable on consistent sequences in the spread
     H, s: nat -> nat |- squash(exists n:nat. B n s)      // B is a bar
     H, n:nat, s: nat_n -> nat, m: B n s |- X n s         // Base case: the conclusion is true at the bar
     H, n:nat, s: nat_n -> nat, x: (forall m: nat. X (n + 1) (ext(s,n,m))) |- X n s // induction case
>>

*)

Definition rule_bar_induction_nat {o}
           (f X c B d e : @NTerm o)
           (s n m v x : NVar)
           (H : barehypotheses) :=
  mk_rule
    (mk_bseq H (mk_conclax (mk_squash (mk_apply2 X mk_zero (mk_seq2kseq c (mk_nat 0) v)))))
    [ mk_bseq (snoc (snoc H (mk_hyp n mk_tnat))
                    (mk_hyp s (mk_natk2nat (mk_var n))))
              (mk_concl (mk_dec (mk_apply2 B (mk_var n) (mk_var s))) d),
      mk_bseq (snoc H (mk_hyp s mk_nat2nat))
              (mk_conclax (mk_squash
                             (mk_exists mk_tnat
                                        n
                                        (mk_apply2 B (mk_var n) (mk_seq2kseq (mk_var s) (mk_var n) v))))),
      mk_bseq (snoc (snoc (snoc H (mk_hyp n mk_tnat))
                          (mk_hyp s (mk_natk2nat (mk_var n))))
                    (mk_hyp m (mk_apply2 B (mk_var n) (mk_var s))))
              (mk_concl (mk_apply2 X (mk_var n) (mk_var s)) e),
      mk_bseq (snoc (snoc (snoc H (mk_hyp n mk_tnat))
                          (mk_hyp s (mk_natk2nat (mk_var n))))
                    (mk_hyp x (mk_all
                                 mk_tnat
                                 m
                                 (mk_squash (mk_apply2 X (mk_plus1 (mk_var n)) (mk_update_seq (mk_var s) (mk_var n) (mk_var m) v))))))
              (mk_conclax (mk_apply2 X (mk_var n) (mk_var s)))
    ]
    [].

Lemma rule_bar_induction_nat_true {o} :
  forall lib (f X c B d e : @NTerm o)
         (s n m v x : NVar)
         (H : @barehypotheses o)
         (dxv : x <> v)
         (dsv : s <> v)
         (dnv : n <> v)
         (dnv : m <> v)
         (dnm : n <> m)
         (dsm : s <> m)
         (nvc : !LIn v (free_vars c))
         (nnB : !LIn n (free_vars B))
         (nsB : !LIn s (free_vars B)),
    rule_true lib (rule_bar_induction_nat f X c B d e s n m v x H).
Proof.
  unfold rule_bar_induction_nat, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp  as [wf1 hyp_dec].
  destruct Hyp0 as [wf2 hyp_bar].
  destruct Hyp1 as [wf3 hyp_imp].
  destruct Hyp2 as [wf4 hyp_ind].
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  assert (s <> n
          # s <> x
          # n <> x
          # !LIn x (free_vars c)
          # !LIn s (free_vars c)
          # !LIn n (free_vars c)
          # !LIn x (free_vars X)
          # !LIn s (free_vars X)
          # !LIn n (free_vars X)
          # !LIn m (free_vars X)
          # !LIn x (vars_hyps H)
          # !LIn s (vars_hyps H)
          # !LIn n (vars_hyps H)) as vhyps.

  clear hyp_dec hyp_bar hyp_ind hyp_imp.
  dwfseq.
  assert (forall x : NVar, LIn x (free_vars c) -> x <> v -> LIn x (vars_hyps H)) as imp.
  { introv h1 h2.
    apply cg.
    repeat (first [rw remove_nvars_cons_r|rw remove_nvars_app_r]).
    allrw memvar_singleton.
    allrw <- beq_var_refl.
    allrw remove_nvars_nil_r; allrw app_nil_r.
    rw in_remove_nvars; rw in_single_iff; sp. }
  sp; GC;
  try (complete (discover; allapply @subset_hs_vars_hyps; sp)).

  destruct vhyps as [ nsn vhyps ].
  destruct vhyps as [ nsx vhyps ].
  destruct vhyps as [ nnx vhyps ].
  destruct vhyps as [ nxc vhyps ].
  destruct vhyps as [ nsc vhyps ].
  destruct vhyps as [ nnc vhyps ].
  destruct vhyps as [ nxX vhyps ].
  destruct vhyps as [ nsX vhyps ].
  destruct vhyps as [ nnX vhyps ].
  destruct vhyps as [ nmX vhyps ].
  destruct vhyps as [ nxH vhyps ].
  destruct vhyps as [ nsH nnH ].
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.

  pose proof (lsubstc_mk_seq2kseq c 0 v w3 s1 c3) as sc1.
  repeat (autodimp sc1 hyp).
  exrepnd.
  rw sc1.

  pose proof (lsubstc_mk_seq2kseq c 0 v w3 s2 c7) as sc2.
  autodimp sc2 hyp.
  exrepnd.
  rw sc2.

  clear sc1 sc2.
  clear_irr.
  clear_wf_hyps.

  rw @tequality_mkc_squash.
  rw @member_mkc_squash.

  assert (!LIn n (dom_csub s1)) as nns1.
  { apply similarity_dom in sim; repnd.
    rw sim0; auto. }

  assert (!LIn n (dom_csub s2)) as nns2.
  { apply similarity_dom in sim; repnd.
    rw sim; auto. }

  assert (!LIn s (dom_csub s1)) as nss1.
  { apply similarity_dom in sim; repnd.
    rw sim0; auto. }

  assert (!LIn s (dom_csub s2)) as nss2.
  { apply similarity_dom in sim; repnd.
    rw sim; auto. }

  assert (!LIn x (dom_csub s1)) as nxs1.
  { apply similarity_dom in sim; repnd.
    rw sim0; auto. }

  assert (!LIn x (dom_csub s2)) as nxs2.
  { apply similarity_dom in sim; repnd.
    rw sim; auto. }

  assert (wf_term B) as wB.
  { clear hyp_dec.
    allrw @wf_dec.
    allrw <- @wf_apply2_iff; sp.
  }

  assert (cover_vars B s1 # cover_vars B s2) as cB.
  { clear hyp_dec.
    allrw @covered_dec.
    allrw @covered_apply2; repnd.
    allrw @vars_hyps_snoc; allsimpl.
    apply covered_snoc_implies in ct5; auto.
    apply covered_snoc_implies in ct5; auto.
    dands.
    - eapply s_cover_typ1;[exact ct5|exact sim].
    - eapply s_cover_typ1;[exact ct5|].
      apply similarity_sym in sim;[exact sim|]; auto.
  }
  destruct cB as [cB1 cB2].


  assert (forall k seq1 seq2 s1a s2a cB1 cB2,
            similarity lib s1a s2a H
            -> hyps_functionality lib s1a H
            -> eq_kseq lib seq1 seq2 k
            -> tequality
                 lib
                 (mkc_apply2 (lsubstc B wB s1a cB1) (mkc_nat k) seq1)
                 (mkc_apply2 (lsubstc B wB s2a cB2) (mkc_nat k) seq2)) as Bfunc.
  { introv sim0 hf0 eqk.
    vr_seq_true in hyp_dec.
    pose proof (hyp_dec
                  (snoc (snoc s1a (n,mkc_nat k)) (s,seq1))
                  (snoc (snoc s2a (n,mkc_nat k)) (s,seq2)))
      as h; clear hyp_dec.
    repeat (autodimp h hyp).

    { apply hyps_functionality_snoc2; simpl; auto.

      { introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'.
        exrepnd; subst; ginv; inj.
        eapply tequality_respects_alphaeqc_left;
          [apply alphaeqc_sym; apply lsubstc_mk_natk2nat_sp2; auto;
           apply similarity_dom in sim'3; repnd; rw sim'0; auto
          |].
        eapply tequality_respects_alphaeqc_right;
          [apply alphaeqc_sym; apply lsubstc_mk_natk2nat_sp2; auto;
           apply similarity_dom in sim'3; repnd; rw sim'3; auto
          |].
        allrw @lsubstc_mkc_tnat.
        apply equality_int_nat_implies_cequivc in sim'1.
        eapply tequality_respects_cequivc_right;
          [apply implies_cequivc_natk2nat; exact sim'1|].
        eauto 3 with slow.
      }

      apply hyps_functionality_snoc2; simpl; auto.

      introv equ' sim'.
      allrw @lsubstc_mkc_tnat.
      apply tnat_type.
    }

    { assert (@wf_term o (mk_natk2nat (mk_var n))) as wfn.
      { apply wf_term_mk_natk2nat; auto. }
      assert (cover_vars (mk_natk2nat (mk_var n)) (snoc s1a (n,mkc_nat k))) as cvn.
      { apply cover_vars_mk_natk2nat.
        apply cover_vars_var.
        rw @dom_csub_snoc.
        rw in_snoc; simpl; sp. }
      sim_snoc.
      dands; auto.

      { pose proof (cover_vars_mk_tnat s1a) as cvs1.
        pose proof (@wf_tnat o) as wftn.
        sim_snoc.
        dands; auto.
        allrw @lsubstc_mkc_tnat.
        apply equality_in_tnat_nat.
      }

      eapply alphaeqc_preserving_equality;
        [|apply alphaeqc_sym;
           apply lsubstc_mk_natk2nat_sp2; auto];
        auto.
      apply similarity_dom in sim0; repnd.
      rw sim1; auto.
    }

    exrepnd.
    clear h1.
    unfold mk_dec in h0.
    lsubst_tac.
    apply tequality_mkc_or in h0; repnd; auto.
  }

  pose proof (bar_induction_meta4
                lib
                (fun_sim_eq lib s1 H B wB)
                (fun_sim_eq lib s1 H X w0)
                (lsubstc B wB s1 cB1)
                (lsubstc X w0 s1 c0)
                (lsubstc c wt s1 ct3)
                v)
    as bi.

  repeat (autodimp bi hyp);
    [idtac
    |idtac
    |idtac
    |pose proof (bi (lsubstc X w0 s2 c5) (seq2kseq (lsubstc c wt s2 ct4) 0 v)) as h;
      allrw <- @mkc_zero_eq;
      repeat (autodimp h hyp);[apply eq_kseq_seq2kseq_0|idtac|repnd; dands; complete auto];
      exists s2 c5;
      dands; complete auto].

  - intros seq1 iss.

    vr_seq_true in hyp_bar.
    pose proof (hyp_bar
                  (snoc s1 (s,seq1))
                  (snoc s1 (s,seq1)))
      as hf; clear hyp_bar.
    repeat (autodimp hf hyp).

    { apply hyps_functionality_snoc2; simpl; auto.

      introv equ' sim'.
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;
          apply lsubstc_mk_nat2nat; auto
        |].
      eapply tequality_respects_alphaeqc_right;
        [apply alphaeqc_sym;
          apply lsubstc_mk_nat2nat; auto
        |].
      apply type_nat2nat.
    }

    { assert (@wf_term o mk_nat2nat) as wfn.
      { apply wf_term_mk_nat2nat; auto. }
      assert (cover_vars mk_nat2nat s1) as cvn.
      { apply cover_vars_mk_nat2nat. }
      sim_snoc.
      dands; auto.
      { eapply similarity_refl; eauto. }
      eapply alphaeqc_preserving_equality;
        [|apply alphaeqc_sym;
           apply lsubstc_mk_nat2nat; auto].
      auto.
    }

    exrepnd.
    clear hf0.
    lsubst_tac.
    apply equality_in_mkc_squash in hf1; exrepnd.
    clear hf0 hf2.
    allunfold @mk_exists.
    lsubst_tac.
    allrw @lsubstc_mkc_tnat.
    apply inhabited_product in hf1; exrepnd.
    clear hf2.

    apply member_tnat_implies_computes in hf1; exrepnd.

    exists k.
    introv eqs fse.
    unfold fun_sim_eq in fse; exrepnd; subst.

    repeat substc_lsubstc_vars3.
    lsubst_tac.
    clear_wf_hyps.
    proof_irr.

    pose proof (lsubstc_mk_seq2kseq2
                  (mk_var s) (mk_var n) v w6
                  ((n, a) :: snoc s1 (s, seq1)) c10) as ss.
    simpl in ss.
    repeat (autodimp ss hyp); try (complete (intro xx; repndors; tcsp)).
    exrepnd.
    rw ss1 in hf3.
    clear ss1.

    clear_wf_hyps.
    proof_irr.
    lsubst_tac.

    eapply inhabited_type_cequivc in hf3;
      [|apply implies_cequivc_apply2;
         [apply cequivc_refl
         |apply computes_to_valc_implies_cequivc;exact hf2
         |apply cequivc_refl]
      ].
    eapply inhabited_type_cequivc in hf3;
      [|apply implies_cequivc_apply2;
         [apply cequivc_refl
         |apply cequivc_refl
         |apply implies_cequivc_seq2kseq2;
           [apply cequivc_refl
           |apply computes_to_valc_implies_cequivc;exact hf2]
         ]
      ].
    allrw @seq2kseq2_as_seq2kseq2.
    dands; auto.

  - intros k seq1 iss sb C seq2 eqs fse.
    clear iss.
    unfold fun_sim_eq in fse; exrepnd; subst.
    unfold meta2_fun_on_seq in sb.
    rename fse0 into sim0.

    assert (cover_vars B s0) as cB0.
    { eapply similarity_cover_vars;[exact sim0|]; auto. }

    pose proof (sb (lsubstc B wB s0 cB0) seq2) as h; clear sb.
    repeat (autodimp h hyp).
    { exists s0 cB0; dands; auto. }
    repnd.

    unfold inhabited_type in h0; exrepnd.
    rename h1 into mem.
    rename h into teq.

    vr_seq_true in hyp_imp.
    pose proof (hyp_imp
                  (snoc (snoc (snoc s1 (n,mkc_nat k)) (s,seq1)) (m,t))
                  (snoc (snoc (snoc s0 (n,mkc_nat k)) (s,seq2)) (m,t)))
      as hf.
    repeat (autodimp hf hyp).

    { apply hyps_functionality_snoc2; simpl; auto.

      { introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'.
        exrepnd; subst; ginv; inj.
        apply similarity_snoc in sim'3; simpl in sim'3.
        exrepnd; subst; ginv; inj.
        lsubst_tac.
        allrw @lsubstc_mkc_tnat.
        apply equality_int_nat_implies_cequivc in sim'2.
        eapply alphaeqc_preserving_equality in sim'1;
          [|apply lsubstc_mk_natk2nat_sp2; auto].
        eapply tequality_respects_cequivc_right;
          [apply implies_cequivc_apply2;
            [apply cequivc_refl
            |exact sim'2
            |apply cequivc_refl]
          |].
        auto.
      }

      apply hyps_functionality_snoc2; simpl; auto.

      { introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'.
        exrepnd; subst; ginv; cpx.
        assert (!LIn n (dom_csub s2a)) as nns2a.
        { apply similarity_dom in sim'3; repnd.
          rw sim'3; auto. }
        eapply tequality_respects_alphaeqc_left;
          [apply alphaeqc_sym;
            apply lsubstc_mk_natk2nat_sp2; auto
          |].
        eapply tequality_respects_alphaeqc_right;
          [apply alphaeqc_sym;
            apply lsubstc_mk_natk2nat_sp2; auto
          |].
        rw @lsubstc_mkc_tnat in sim'1.
        apply equality_int_nat_implies_cequivc in sim'1.
        eapply tequality_respects_cequivc_right;
          [apply implies_cequivc_natk2nat; exact sim'1|].
        eauto 3 with slow.
      }

      apply hyps_functionality_snoc2; simpl; auto.

      introv equ' sim'.
      allrw @lsubstc_mkc_tnat.
      apply tnat_type.
    }

    { assert (wf_term (mk_apply2 B (mk_var n) (mk_var s))) as wfn.
      { apply wf_apply2; eauto 3 with slow. }
      assert (cover_vars (mk_apply2 B (mk_var n) (mk_var s)) (snoc (snoc s1 (n,mkc_nat k)) (s,seq1))) as cvn.
      { apply cover_vars_apply2.
        repeat (rw @cover_vars_var_iff).
        repeat (rw @dom_csub_snoc); simpl.
        repeat (rw in_snoc).
        dands; tcsp.
        repeat (apply cover_vars_snoc_weak); auto. }
      sim_snoc.
      dands; auto.

      { assert (@wf_term o (mk_natk2nat (mk_var n))) as wfk.
        { apply wf_term_mk_natk2nat; auto. }
        assert (cover_vars (mk_natk2nat (mk_var n)) (snoc s1 (n,mkc_nat k))) as cvk.
        { apply cover_vars_mk_natk2nat.
          apply cover_vars_var_iff.
          repeat (rw @dom_csub_snoc); simpl.
          repeat (rw in_snoc); sp. }
        sim_snoc.
        dands; auto.

        { assert (@wf_term o mk_tnat) as wft.
          { eauto 3 with slow. }
          assert (cover_vars mk_tnat s1) as cvt.
          { apply cover_vars_mk_tnat. }
          sim_snoc.
          dands; auto.
          allrw @lsubstc_mkc_tnat.
          eauto 3 with slow.
        }

        eapply alphaeqc_preserving_equality;
          [|apply alphaeqc_sym; apply lsubstc_mk_natk2nat_sp2; auto].
        auto.
      }

      { lsubst_tac; auto. }
    }

    exrepnd.
    lsubst_tac.
    apply inhabited_type_if_equality in hf1.
    unfold meta_fun_on_seq.
    dands; auto.

  - intros k seq1 iss ind C seq2 eqs fse.
    clear iss.
    unfold fun_sim_eq in fse; exrepnd; subst.

    vr_seq_true in hyp_ind.

    pose proof (hyp_ind
                  (snoc (snoc (snoc s1 (n,mkc_nat k)) (s,seq1)) (x,lam_axiom))
                  (snoc (snoc (snoc s0 (n,mkc_nat k)) (s,seq2)) (x,lam_axiom)))
      as hf; clear hyp_ind.
    repeat (autodimp hf hyp).

    { apply hyps_functionality_snoc2; simpl; auto.

      { introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'.
        exrepnd; subst; ginv; inj.
        apply similarity_snoc in sim'3; simpl in sim'3.
        exrepnd; subst; ginv; inj.
        allunfold @mk_all.
        lsubst_tac.
        allrw @lsubstc_mkc_tnat.
        apply equality_int_nat_implies_cequivc in sim'2.
        eapply alphaeqc_preserving_equality in sim'1;
          [|apply lsubstc_mk_natk2nat_sp2; auto].

        apply tequality_function; dands.
        { apply tnat_type. }
        introv en.
        repeat substc_lsubstc_vars3.
        lsubst_tac.
        apply equality_in_tnat in en.
        unfold equality_of_nat in en; exrepnd; spcast.

        apply tequality_mkc_squash.

        eapply tequality_respects_cequivc_left;
          [apply cequivc_sym;
            apply implies_cequivc_apply2;
            [apply cequivc_refl
            |apply cequivc_lsubstc_mk_plus1_sp1;auto
            |apply cequivc_lsubstc_mk_update_seq_sp1;auto;
             exact en1]
          |].

        assert (!LIn n (dom_csub s2a0)) as nin2.
        { apply similarity_dom in sim'4; repnd.
          rw sim'4; auto. }

        assert (!LIn s (dom_csub s2a0)) as nis2.
        { apply similarity_dom in sim'4; repnd.
          rw sim'4; auto. }

        eapply tequality_respects_cequivc_right;
          [apply cequivc_sym;
            apply implies_cequivc_apply2;
            [apply cequivc_refl
            |apply cequivc_lsubstc_mk_plus1_sp2; auto;
             apply cequivc_sym;exact sim'2
            |apply cequivc_lsubstc_mk_update_seq_sp2;auto;
             [exact en0
             |apply cequivc_nat_implies_computes_to_valc;
               apply cequivc_sym;exact sim'2]
            ]
          |].

        pose proof (ind k0) as h; clear ind.
        unfold meta2_fun_on_upd_seq in h.
        unfold meta2_fun_on_seq in h; repnd.

        pose proof (h (lsubstc X w0 s2a0 c27) (update_seq t2 k k0 v)) as q; clear h.
        repeat (autodimp q hyp).
        { apply eq_kseq_update; auto. }
        { exists s2a0 c27; dands; auto. }
        repnd; auto.
      }

      apply hyps_functionality_snoc2; simpl; auto.

      { introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'.
        exrepnd; subst; ginv; inj.
        assert (!LIn n (dom_csub s2a)) as nns2a.
        { apply similarity_dom in sim'3; repnd.
          rw sim'3; auto. }
        eapply tequality_respects_alphaeqc_left;
          [apply alphaeqc_sym;
            apply lsubstc_mk_natk2nat_sp2; auto
          |].
        eapply tequality_respects_alphaeqc_right;
          [apply alphaeqc_sym;
            apply lsubstc_mk_natk2nat_sp2; auto
          |].
        rw @lsubstc_mkc_tnat in sim'1.
        apply equality_int_nat_implies_cequivc in sim'1.
        eapply tequality_respects_cequivc_right;
          [apply implies_cequivc_natk2nat; exact sim'1|].
        eauto 3 with slow.
      }

      apply hyps_functionality_snoc2; simpl; auto.

      introv equ' sim'.
      allrw @lsubstc_mkc_tnat.
      apply tnat_type.
    }

    { assert (wf_term (mk_all mk_tnat m
                              (mk_squash
                                 (mk_apply2 X (mk_plus1 (mk_var n))
                                            (mk_update_seq (mk_var s) (mk_var n) (mk_var m) v))))) as wa.
      { apply wf_function; auto.
        apply wf_squash.
        apply wf_apply2; auto. }
      assert (cover_vars (mk_all mk_tnat m
                              (mk_squash
                                 (mk_apply2 X (mk_plus1 (mk_var n))
                                            (mk_update_seq (mk_var s) (mk_var n) (mk_var m) v))))
                         (snoc (snoc s1 (n, mkc_nat k)) (s, seq1))) as ca.
      { apply cover_vars_function; dands; auto.
        { apply cover_vars_mk_tnat. }
        apply cover_vars_upto_squash.
        apply cover_vars_upto_apply2; dands; auto.
        { repeat (rw @csub_filter_snoc).
          allrw memvar_singleton.
          boolvar;tcsp;GC;[].
          repeat (apply cover_vars_upto_snoc_weak).
          apply cover_vars_upto_csub_filter_disjoint; auto.
          apply disjoint_singleton_r; auto. }
        { apply cover_vars_upto_add; dands; eauto 3 with slow.
          repeat (rw @csub_filter_snoc).
          allrw memvar_singleton.
          boolvar;tcsp;GC;[].
          apply cover_vars_upto_var; simpl.
          repeat (rw @dom_csub_snoc).
          repeat (rw in_snoc;simpl).
          sp. }
        { unfold mk_update_seq.
          apply cover_vars_upto_lam.
          rw @csub_filter_swap.
          rw <- @csub_filter_app_r; simpl.
          repeat (rw @csub_filter_snoc).
          allrw memvar_cons; simpl.
          boolvar;tcsp;GC;[].
          apply cover_vars_upto_int_eq; dands.
          { apply cover_vars_upto_var; simpl.
            repeat (rw @dom_csub_snoc).
            repeat (rw in_snoc;simpl).
            sp. }
          { apply cover_vars_upto_var; simpl.
            repeat (rw @dom_csub_snoc).
            repeat (rw in_snoc;simpl).
            sp. }
          { apply cover_vars_upto_var; simpl.
            repeat (rw @dom_csub_snoc).
            repeat (rw in_snoc;simpl).
            sp. }
          { apply cover_vars_upto_apply; dands.
            { apply cover_vars_upto_var; simpl.
              repeat (rw @dom_csub_snoc).
              repeat (rw in_snoc;simpl).
              sp. }
            { apply cover_vars_upto_var; simpl.
              repeat (rw @dom_csub_snoc).
              repeat (rw in_snoc;simpl).
              sp. }
          }
        }
      }
      sim_snoc.
      dands; auto.

      { assert (@wf_term o (mk_natk2nat (mk_var n))) as wfk.
        { apply wf_term_mk_natk2nat; auto. }
        assert (cover_vars (mk_natk2nat (mk_var n)) (snoc s1 (n,mkc_nat k))) as cvk.
        { apply cover_vars_mk_natk2nat.
          apply cover_vars_var_iff.
          repeat (rw @dom_csub_snoc); simpl.
          repeat (rw in_snoc); sp. }
        sim_snoc.
        dands; auto.

        { assert (@wf_term o mk_tnat) as wft.
          { eauto 3 with slow. }
          assert (cover_vars mk_tnat s1) as cvt.
          { apply cover_vars_mk_tnat. }
          sim_snoc.
          dands; auto.
          allrw @lsubstc_mkc_tnat.
          eauto 3 with slow.
        }

        eapply alphaeqc_preserving_equality;
          [|apply alphaeqc_sym; apply lsubstc_mk_natk2nat_sp2; auto].
        auto.
      }

      { unfold mk_all.
        lsubst_tac.
        allrw @lsubstc_mkc_tnat.
        apply equality_in_function.
        dands; auto.

        { apply tnat_type. }

        { introv en.
          repeat substc_lsubstc_vars3.
          lsubst_tac.
          apply equality_in_tnat in en.
          unfold equality_of_nat in en; exrepnd; spcast.

          apply tequality_mkc_squash.

          eapply tequality_respects_cequivc_left;
            [apply cequivc_sym;
              apply implies_cequivc_apply2;
              [apply cequivc_refl
              |apply cequivc_lsubstc_mk_plus1_sp1;auto
              |apply cequivc_lsubstc_mk_update_seq_sp1;auto;
               exact en1]
            |].

          eapply tequality_respects_cequivc_right;
            [apply cequivc_sym;
              apply implies_cequivc_apply2;
              [apply cequivc_refl
              |apply cequivc_lsubstc_mk_plus1_sp2; auto;
               apply cequivc_sym;exact sim'2
              |apply cequivc_lsubstc_mk_update_seq_sp1;auto;
               exact en0]
            |].

          pose proof (ind k0) as h; clear ind.
          unfold meta2_fun_on_upd_seq in h.
          unfold meta2_fun_on_seq in h; repnd.

          pose proof (h (lsubstc X w0 s1 c0) (update_seq seq1 k k0 v)) as q; clear h.
          repeat (autodimp q hyp).
          { apply eq_kseq_update; auto.
            eapply eq_kseq_left; eauto. }
          { exists s1 c0; dands; auto.
            eapply similarity_refl; eauto. }
          repnd; auto.
        }

        { introv en.
          repeat substc_lsubstc_vars3.
          eapply equality_respects_cequivc_left;
            [apply cequivc_sym;apply cequivc_mkc_apply_lam_axiom|].
          eapply equality_respects_cequivc_right;
            [apply cequivc_sym;apply cequivc_mkc_apply_lam_axiom|].

          clear_wf_hyps.
          proof_irr.
          lsubst_tac.

          apply equality_in_mkc_squash; dands; spcast;
          try (apply computes_to_valc_refl; eauto 3 with slow).

          apply equality_in_tnat in en.
          unfold equality_of_nat in en; exrepnd; spcast.

          eapply inhabited_type_cequivc;
            [apply cequivc_sym;
              apply implies_cequivc_apply2;
              [apply cequivc_refl
              |apply cequivc_lsubstc_mk_plus1_sp1;auto
              |apply cequivc_lsubstc_mk_update_seq_sp1;auto;
               exact en1]
            |].

          pose proof (ind k0) as h; clear ind.
          unfold meta2_fun_on_upd_seq in h.
          unfold meta2_fun_on_seq in h; repnd.

          pose proof (h (lsubstc X w0 s1 c0) (update_seq seq1 k k0 v)) as q; clear h.
          repeat (autodimp q hyp).
          { apply eq_kseq_update; auto.
            eapply eq_kseq_left; eauto. }
          { exists s1 c0; dands; auto.
            eapply similarity_refl; eauto. }
          repnd; auto.
        }
      }
    }

    exrepnd.
    lsubst_tac.
    apply inhabited_type_if_equality in hf1.
    dands; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
