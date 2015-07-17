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
g
*)

Require Import csubst.

Lemma simple_substc2_ex {p} :
  forall (t : @CTerm p) x u s w cu,
    !LIn x (dom_csub s)
    -> {c : cover_vars u (snoc s (x, t))
        & substc t x (lsubstc_vars u w (csub_filter s [x]) [x] cu)
          = lsubstc u w (snoc s (x, t)) c}.
Proof.
  introv ni.

  assert (cover_vars u (snoc s (x, t))) as c.
  unfold cover_vars_upto in cu.
  rw @cover_vars_eq.
  provesv.
  allrw in_app_iff; allrw in_single_iff; allrw @dom_csub_snoc; allrw in_snoc; allsimpl.
  allrw @dom_csub_csub_filter; allrw in_remove_nvars; allrw in_single_iff; sp.

  exists c.
  symmetry.
  apply simple_substc2; auto.
Qed.

Lemma simple_lsubstc_subst_ex {p} :
  forall (t : @NTerm p) x B ws s cs wt ct,
    disjoint (free_vars t) (bound_vars B)
    -> {wb : wf_term B
        & {cb : cover_vars_upto B (csub_filter s [x]) [x]
        & lsubstc (subst B x t) ws s cs
          = substc (lsubstc t wt s ct) x (lsubstc_vars B wb (csub_filter s [x]) [x] cb)}}.
Proof.
  introv disj.
  dup ws as wB.
  apply lsubst_wf_term in wB.
  exists wB.
  dup cs as cB.
  rw @cover_vars_eq in cB.

  generalize (eqvars_free_vars_disjoint B [(x,t)]); introv eqv.
  apply subvars_eqvars with (s2 := dom_csub s) in eqv; auto.
  rw subvars_app_l in eqv; repnd.
  rw subvars_remove_nvars in eqv0.
  allsimpl.
  assert (cover_vars_upto B (csub_filter s [x]) [x]) as cb.
  unfold cover_vars_upto; rw subvars_prop; introv ib.
  rw in_app_iff; rw in_single_iff.
  rw @dom_csub_csub_filter; rw in_remove_nvars; rw in_single_iff.
  rw subvars_prop in eqv0.
  apply eqv0 in ib.
  rw in_app_iff in ib.
  rw in_single_iff in ib.
  destruct (deq_nvar x0 x); subst; sp.
  exists cb.

  apply simple_lsubstc_subst; auto.
Qed.


Ltac substc_lsubstc_vars2 :=
  match goal with
    | [ |- context[substc ?t ?x (lsubstc_vars ?u ?w (csub_filter ?s [?x]) [?x] ?cu)] ] =>
      let eq := fresh "eq" in
      let h := fresh "h" in
      let c := fresh "c" in
      generalize (simple_substc2_ex t x u s w cu);
        intro eq;
        autodimp eq h;
        try (destruct eq as [c eq]; rewrite eq; clear eq)
    | [ H : context[substc ?t ?x (lsubstc_vars ?u ?w (csub_filter ?s [?x]) [?x] ?cu)] |- _ ] =>
      let eq := fresh "eq" in
      let h := fresh "h" in
      let c := fresh "c" in
      generalize (simple_substc2_ex t x u s w cu);
        intro eq;
        autodimp eq h;
        try (destruct eq as [c eq]; rewrite eq in H; clear eq)

    | [ |- context[lsubstc (subst ?B ?x ?t) ?ws ?s ?cs] ] =>
      let eq := fresh "eq" in
      let h  := fresh "h"  in
      let wb := fresh "wb" in
      let cb := fresh "cb" in
      let wt := fresh "wt" in
      let ct := fresh "ct" in
      assert (wf_term t) as wt by auto;
        assert (cover_vars t s) as ct by auto;
        generalize (simple_lsubstc_subst_ex t x B ws s cs wt ct);
        intro eq;
        autodimp eq h;
        try (destruct eq as [wb eq]; destruct eq as [cb eq]; rewrite eq; clear eq)

    | [ H : context[lsubstc (subst ?B ?x ?t) ?ws ?s ?cs] |- _ ] =>
      let eq := fresh "eq" in
      let h  := fresh "h"  in
      let wb := fresh "wb" in
      let cb := fresh "cb" in
      let wt := fresh "wt" in
      let ct := fresh "ct" in
      assert (wf_term t) as wt by auto;
        assert (cover_vars t s) as ct by auto;
        generalize (simple_lsubstc_subst_ex t x B ws s cs wt ct);
        intro eq;
        autodimp eq h;
        try (destruct eq as [wb eq]; destruct eq as [cb eq]; rewrite eq in H; clear eq)
  end.

Lemma simple_substc3 {p} :
  forall (t : @CTerm p) x u s w c cu,
    lsubstc u w ((x,t) :: s) c
    = substc t x (lsubstc_vars u w (csub_filter s [x]) [x] cu).
Proof.
  introv.

  assert (wf_term (csubst u [(x, t)])) as wc by (apply csubst_preserves_wf_term; sp).
  assert (cover_vars (csubst u [(x, t)]) s) as cc by (apply cover_vars_csubst3; simpl; sp).

  generalize (simple_substc t x u wc s cc w cu); intro eq.
  rewrite <- eq; clear eq.

  generalize (lsubstc_csubst_ex u [(x,t)] s wc cc); intro eq; exrepnd; clear_irr; allrw.
  simpl; sp.
Qed.

Lemma simple_substc3_ex {p} :
  forall (t : @CTerm p) x u s w cu,
    {c : cover_vars u ((x,t) :: s)
     & substc t x (lsubstc_vars u w (csub_filter s [x]) [x] cu)
       = lsubstc u w ((x,t) :: s) c}.
Proof.
  introv.

  assert (cover_vars u ((x,t) :: s)) as c.
  unfold cover_vars_upto in cu.
  rw @cover_vars_eq.
  provesv.
  allrw in_app_iff; allrw in_single_iff; allrw @dom_csub_snoc; allrw in_snoc; allsimpl.
  allrw @dom_csub_csub_filter; allrw in_remove_nvars; allrw in_single_iff; sp.

  exists c.
  symmetry.
  apply simple_substc3; auto.
Qed.


Ltac substc_lsubstc_vars3 :=
  match goal with
    | [ |- context[substc ?t ?x (lsubstc_vars ?u ?w (csub_filter ?s [?x]) [?x] ?cu)] ] =>
      let eq := fresh "eq" in
      let h := fresh "h" in
      let c := fresh "c" in
      generalize (simple_substc3_ex t x u s w cu);
        intro eq;
        try (destruct eq as [c eq]; rewrite eq; clear eq)
    | [ H : context[substc ?t ?x (lsubstc_vars ?u ?w (csub_filter ?s [?x]) [?x] ?cu)] |- _ ] =>
      let eq := fresh "eq" in
      let h := fresh "h" in
      let c := fresh "c" in
      generalize (simple_substc3_ex t x u s w cu);
        intro eq;
        try (destruct eq as [c eq]; rewrite eq in H; clear eq)

    | [ |- context[lsubstc (subst ?B ?x ?t) ?ws ?s ?cs] ] =>
      let eq := fresh "eq" in
      let h  := fresh "h"  in
      let wb := fresh "wb" in
      let cb := fresh "cb" in
      let wt := fresh "wt" in
      let ct := fresh "ct" in
      assert (wf_term t) as wt by auto;
        assert (cover_vars t s) as ct by auto;
        generalize (simple_lsubstc_subst_ex t x B ws s cs wt ct);
        intro eq;
        autodimp eq h;
        try (destruct eq as [wb eq]; destruct eq as [cb eq]; rewrite eq; clear eq)

    | [ H : context[lsubstc (subst ?B ?x ?t) ?ws ?s ?cs] |- _ ] =>
      let eq := fresh "eq" in
      let h  := fresh "h"  in
      let wb := fresh "wb" in
      let cb := fresh "cb" in
      let wt := fresh "wt" in
      let ct := fresh "ct" in
      assert (wf_term t) as wt by auto;
        assert (cover_vars t s) as ct by auto;
        generalize (simple_lsubstc_subst_ex t x B ws s cs wt ct);
        intro eq;
        autodimp eq h;
        try (destruct eq as [wb eq]; destruct eq as [cb eq]; rewrite eq in H; clear eq)
  end.


Lemma lsubstc_snoc_app {o} :
  forall (t : @NTerm o) s1 s2 x a w c,
    !LIn x (free_vars t)
    -> {c' : cover_vars t (s1 ++ s2)
        $ lsubstc t w (snoc s1 (x, a) ++ s2) c
           = lsubstc t w (s1 ++ s2) c'}.
Proof.
  introv ni.

  assert (cover_vars t (s1 ++ s2)) as cv.
  allrw @cover_vars_eq; allrw subvars_eq.
  introv i; applydup c in i.
  allrw @dom_csub_app; allrw @dom_csub_snoc; allsimpl; allrw in_app_iff; allrw in_snoc.
  sp; subst; sp.

  exists cv.

  pose proof (lsubstc_csubst_ex2 t s1 s2 w cv) as h; exrepnd.
  rw <- h1.

  pose proof (lsubstc_csubst_ex2 t (snoc s1 (x,a)) s2 w c) as k; exrepnd.
  rw <- k1.

  clear k1 h1.
  revert w'0 p'0.
  rw @subset_free_vars_csub_snoc; auto; introv.
  clear_irr; auto.
Qed.

Ltac lsubstc_snoc_app :=
  match goal with
    | [ H1 : !LIn ?x (free_vars ?t), H2 : context[lsubstc ?t ?w (snoc ?s1 (?x, ?a) ++ ?s2) ?c] |- _ ] =>
      let h := fresh "h" in
      let c := fresh "c" in
      pose proof (lsubstc_snoc_app t s1 s2 x a w c H1) as h;
        destruct h as [c h];
        rewrite h in H2;
        clear h;
        clear_irr
  end.

Ltac rw_lsubstc_subst_snoc_eq :=
  match goal with
    | [ wb : wf_term ?b
      , cb : cover_vars_upto ?b (csub_filter ?s [?x]) [?x]
      , H  : context[lsubstc (subst ?b ?x (mk_var ?y)) ?w (snoc ?s (?y, ?a)) ?c]
      |- _ ] =>
      let h := fresh "h" in
      let hh := fresh "hh" in
      pose proof (lsubstc_subst_snoc_eq s b x y a w wb c cb) as h;
        repeat (autodimp h hh);
        try (rewrite h in H; clear h)
  end.
