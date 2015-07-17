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


Require Export per_props_more.



(* ========= W TYPES ========= *)

Definition wlistA T := mkc_union mkc_unit T.

Definition wlistB v :=
  mkc_ite_vars
    [v]
    (mkc_var v)
    (mk_cv [v] mkc_void)
    (mk_cv [v] mkc_unit).

Definition wlist (T : CTerm) := mkc_w (wlistA T) nvarx (wlistB nvarx).

Definition wnil := mkc_sup (mkc_inl mkc_axiom) mkc_id.

Definition wcons a b := mkc_sup (mkc_inr a) (mkc_lamc nvarx b).

Definition ex3ones :=
  wcons (mkc_nat 1) (wcons (mkc_nat 1) (wcons (mkc_nat 1) wnil)).

Definition unit_eq : term-equality :=
  fun t t' =>
    ccomputes_to_valc t mkc_axiom
    # ccomputes_to_valc t' mkc_axiom
    # capproxc mkc_axiom mkc_axiom.

Definition void_eq : term-equality := fun (t t' : CTerm) => void.

Definition wlist_eqa eqT :=
  fun t t' => per_union_eq unit_eq eqT t t'.

Definition per_isl (a a' : CTerm)
                   (eq : term-equality)
                   (e : wlist_eqa eq a a')
                   (T1 T2 : [U]) :=
  match e with
    | or_introl _ => T1
    | or_intror _ => T2
  end.

Definition wlist_eqb eqT :=
  fun a a' (e : wlist_eqa eqT a a') t t' =>
    per_isl a a' eqT e (void_eq t t') (unit_eq t t').

Definition wlist_eq eqT :=
  fun t t' => weq (wlist_eqa eqT) (wlist_eqb eqT) t t'.

Lemma lsubst_wlistB_as_decide :
  forall v x,
    ! LIn nvarx (free_vars x)
    -> lsubst (mk_decide (mk_var v) nvarx mk_void nvarx mk_unit) [(v, x)]
       = mk_decide x nvarx mk_void nvarx mk_unit.
Proof.
  introv ninx.
  unfold lsubst.
  destruct (dec_disjointv
              (bound_vars (mk_decide (mk_var v) nvarx mk_void nvarx mk_unit))
              (flat_map free_vars (range [(v, x)]))).

  simpl.
  remember (beq_var v v); destruct b; simpl.
  remember (memvar v [nvarx]); destruct b; simpl.
  symmetry in Heqb0.
  rw fold_assert in Heqb0.
  rw assert_memvar in Heqb0; simpl in Heqb0; sp.
  rw <- Heqb0; simpl.
  remember (beq_var v nvarx); destruct b; simpl; sp.
  apply beq_var_true in Heqb1; sp; subst.
  symmetry in Heqb0. rw not_of_assert in Heqb0.
  rw assert_memvar in Heqb0; simpl in Heqb0; sp.
  rw not_over_or in Heqb0; sp.
  rw <- beq_var_refl in Heqb; sp.

  assert (eqvars
            (bound_vars (mk_decide (mk_var v) nvarx mk_void nvarx mk_unit))
            [nvarx]) as eqv1.
  simpl; rw eqvars_prop; simpl; sp; split; sp.

  assert (flat_map free_vars (range [(v, x)]) = free_vars x) as eqv2.
  simpl; rw app_nil_r; sp.

  destruct n.
  rewrite eqv2.
  apply eqvars_disjoint with (s1 := [nvarx]); sp.
  rw disjoint_singleton_l; sp.
Qed.

Lemma computes_substc_wlistB_inl :
  forall a x,
    computes_to_valc a (mkc_inl x)
    -> computes_to_valc (substc a nvarx (wlistB nvarx)) mkc_void.
Proof.
  introv c.
  destruct_cterms.
  allunfold computes_to_valc; allsimpl.
  unfold subst.

  allrw isprog_eq.
  allunfold isprogram; repnd.

  assert (lsubst (mk_decide (mk_var nvarx) nvarx mk_void nvarx mk_unit) [(nvarx, x0)]
          = mk_decide x0 nvarx mk_void nvarx mk_unit) as eq.
  change_to_lsubst_aux4; try (complete (simpl; allrw; simpl; sp)).

  rw eq.

  apply implies_computes_to_value_inl_decide with (a := x); sp.
  unfold subst; simpl.
  change_to_lsubst_aux4; simpl; sp; allrw; simpl; sp.
  apply computes_to_value_isvalue_refl; sp.
Qed.

Lemma computes_substc_wlistB_inr :
  forall a x,
    computes_to_valc a (mkc_inr x)
    -> computes_to_valc (substc a nvarx (wlistB nvarx)) mkc_unit.
Proof.
  introv c.
  destruct_cterms.
  allunfold computes_to_valc; allsimpl.
  unfold subst.

  allrw isprog_eq.
  allunfold isprogram; repnd.

  assert (lsubst (mk_decide (mk_var nvarx) nvarx mk_void nvarx mk_unit) [(nvarx, x0)]
          = mk_decide x0 nvarx mk_void nvarx mk_unit) as eq.
  change_to_lsubst_aux4; try (complete (simpl; allrw; simpl; sp)).

  rw eq.

  apply implies_computes_to_value_inr_decide with (a := x); sp.
  unfold subst; simpl.
  change_to_lsubst_aux4; simpl; sp; allrw; simpl; sp.
  apply computes_to_value_isvalue_refl; sp.
Qed.

Lemma nuprl_mkc_void :
  nuprl mkc_void mkc_void void_eq.
Proof.
  apply CL_sqle; unfold per_sqle.
  exists mkc_axiom mkc_bot mkc_axiom mkc_bot; sp;
  try (complete (rw <- mkc_false_eq; rw mkc_void_eq_mkc_false;
                 apply computes_to_valc_refl; sp;
                 apply iscvalue_mkc_false)).
  unfold void_eq; split; sp.
  allapply not_axiom_approxc_bot; sp.
Qed.
Hint Immediate nuprl_mkc_void.

Lemma nuprl_mkc_unit :
  nuprl mkc_unit mkc_unit unit_eq.
Proof.
  apply CL_sqle; unfold per_sqle.
  exists mkc_axiom mkc_axiom mkc_axiom mkc_axiom; sp;
  try (complete (rw <- mkc_true_eq; rw mkc_unit_eq_mkc_true;
                 apply computes_to_valc_refl; sp;
                 apply iscvalue_mkc_true)).
Qed.
Hint Immediate nuprl_mkc_unit.

Lemma wnil_is_list :
  forall T, type T -> member wnil (wlist T).
Proof.
  introv tT.
  unfold member, equality, nuprl.
  unfold type, tequality in tT; exrepnd.
  exists (wlist_eq eq); sp.
  apply CL_w; unfold per_w, type_family.
  exists (wlist_eqa eq) (wlist_eqb eq); sp.
  exists (wlistA T) (wlistA T) nvarx nvarx (wlistB nvarx) (wlistB nvarx); sp;
  repeat (apply computes_to_valc_refl; try (apply iscvalue_mkc_w)).

  apply CL_union; unfold per_union.
  exists unit_eq eq mkc_unit mkc_unit T T; sp;
  repeat (apply computes_to_valc_refl; try (apply iscvalue_mkc_union)).

  fold nuprl.
  unfold wlist_eqa, per_union_eq in e; exrepnd; repdors; repnd.

  unfold unit_eq in e0; repnd.
  generalize (computes_substc_wlistB_inl a x)
             (computes_substc_wlistB_inl a' y);
    intros c1 c2.
  dest_imp c1 hyp.
  dest_imp c2 hyp.
  apply computes_to_valc_implies_cequivc in c1.
  apply computes_to_valc_implies_cequivc in c2.
  apply nuprl_value_respecting_left with (t1 := mkc_void);
    try (complete (apply cequivc_sym; sp)).
  apply nuprl_value_respecting_right with (t2 := mkc_void);
    try (complete (apply cequivc_sym; sp)).

  unfold wlist_eqb, per_isl; simpl.
  unfold void_eq; fold void_eq.
  apply nuprl_mkc_void.

  unfold unit_eq in e2; repnd.
  generalize (computes_substc_wlistB_inr a x)
             (computes_substc_wlistB_inr a' y);
    intros c1 c2.
  dest_imp c1 hyp.
  dest_imp c2 hyp.
  apply computes_to_valc_implies_cequivc in c1.
  apply computes_to_valc_implies_cequivc in c2.
  apply nuprl_value_respecting_left with (t1 := mkc_unit);
    try (complete (apply cequivc_sym; sp)).
  apply nuprl_value_respecting_right with (t2 := mkc_unit);
    try (complete (apply cequivc_sym; sp)).

  unfold wlist_eqb, per_isl; simpl.
  unfold unit_eq; fold unit_eq.
  apply nuprl_mkc_unit.

  unfold wlist_eq.

  assert (wlist_eqa eq (mkc_inl mkc_axiom) (mkc_inl mkc_axiom)) as e.
  unfold wlist_eqa, per_union_eq.
  exists mkc_axiom mkc_axiom; sp; left; sp;
  repeat (apply computes_to_valc_refl; try (apply iscvalue_mkc_inl)).
  unfold unit_eq; sp;
  repeat (apply computes_to_valc_refl; try (apply iscvalue_mkc_axiom)).
  assert (cequivc mkc_axiom mkc_axiom) as c; sp.
  destruct c; sp.

  apply weq_cons with
        (a := mkc_inl mkc_axiom) (a' := mkc_inl mkc_axiom)
        (f := mkc_id) (f' := mkc_id)
        (e := e); sp;
  repeat (apply computes_to_valc_refl; try (apply iscvalue_mkc_sup)).
  unfold wlist_eqb, void_eq, per_isl in X; allsimpl; sp.
  destruct e; allsimpl; sp; allsimpl; sp.
  provefalse.
  allunfold computes_to_valc; allsimpl.
  destruct_cterms.
  unfold mkc_inr in p0; allsimpl.
  apply computes_to_value_isvalue_eq in p0; sp.
  inversion p0.
  apply isvalue_inl; sp.
Qed.
