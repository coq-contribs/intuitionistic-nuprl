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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export stronger_continuity_rule_v2.
Require Export stronger_continuity_rule4.

Unset Regular Subst Tactic.


Lemma equality_in_modulus_fun_type_u_implies_v2 {o} :
  forall lib (M1 M2 n1 n2 f1 f2 : @CTerm o) T,
    equality lib M1 M2 (modulus_fun_type_u_v2 T)
    -> equality lib n1 n2 mkc_tnat
    -> equality lib f1 f2 (nat2T T)
    -> equality
         lib
         (mkc_apply2 M1 n1 f1)
         (mkc_apply2 M2 n2 f2)
         natU.
Proof.
  introv eM en ef.

  apply equality_in_function2 in eM; repnd.
  clear eM0.
  applydup eM in en as e.
  eapply alphaeqc_preserving_equality in e;[|apply substc_mkcv_fun].
  rw @csubst_mk_cv in e.

  eapply alphaeqc_preserving_equality in e;
    [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
      apply substc_mkcv_fun].
  eapply alphaeqc_preserving_equality in e;
    [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
      apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
      apply mkcv_natk_substc
    ].
  allrw @mkc_var_substc.
  allrw @mkcv_tnat_substc.

  try (fold (natk2nat n1) in e).

  applydup @equality_refl in en.
  apply (equality_nat2T_to_natk2T lib n1) in ef; auto;[].

  apply equality_in_fun in e; repnd; clear e0 e1.
  allrw @csubst_mk_cv.
  apply e in ef.
  allrw <- @mkc_apply2_eq; auto.
Qed.

Lemma spM_cond2_v2 {o} :
  forall lib (F f : @CTerm o) n k T,
    member lib F (mkc_fun (nat2T T) mkc_tnat)
    -> member lib f (nat2T T)
    -> cequivc lib (mkc_apply2 (spM_c F) (mkc_nat n) f) (mkc_nat k)
    -> cequivc lib (mkc_apply F f) (mkc_nat k).
Proof.
  introv mF mf ceq.
  eapply cequivc_trans in ceq;
    [|apply cequivc_sym; apply cequivc_apply2_spM_c].
  rw @test_c_eq in ceq.

  destruct (fresh_atom o (getc_utokens F ++ getc_utokens f)) as [a nia].
  allrw in_app_iff; allrw not_over_or; repnd.

  pose proof (cequivc_fresh_nat_implies
                lib nvare
                (test_try2_cv F nvarc nvarx nvarz nvare (mkc_nat n) f)
                a k) as ceq1.
  repeat (autodimp ceq1 hyp).
  { destruct_cterms; allunfold @getc_utokens; allsimpl.
    allunfold @getcv_utokens; allsimpl; allrw app_nil_r; allrw in_app_iff; sp. }

  rw @substc_test_try2_cv in ceq1.

  eapply cequivc_trans in ceq1;
    [|apply simpl_cequivc_mkc_try;
       [apply implies_cequivc_apply;
         [apply cequivc_refl|apply cequivc_sym; apply cequiv_bound2_c_cbv]
       |apply cequivc_refl]
    ].
  apply cequivc_nat_implies in ceq1.

  pose proof (hasvalue_likec_try
                lib
                (mkc_apply F (bound2_cbv_c nvarx nvarz (mkc_nat n) f (mkc_utoken a)))
                (mkc_utoken a) nvarc (mkcv_axiom nvarc)) as hv.
  autodimp hv hyp.
  { eapply computes_to_valc_implies_hasvalue_likec;exact ceq1. }

  apply hasvalue_likec_implies_or in hv; repndors.

  - apply hasvaluec_computes_to_valc_implies in hv; exrepnd.

    pose proof (computes_to_valc_mkc_try
                  lib
                  (mkc_apply F (bound2_cbv_c nvarx nvarz (mkc_nat n) f (mkc_utoken a)))
                  (mkc_utoken a) nvarc (mkcv_axiom nvarc)
                  b (PKa a)) as comp.
    repeat (autodimp comp hyp).
    { apply computes_to_pkc_refl; apply mkc_utoken_eq_pk2termc. }

    computes_to_eqval.

    pose proof (equality_lam_force_nat_c_in_nat2nat_v2 lib nvarx nvarz f T mf) as h.
    apply equality_in_fun in mF; repnd; clear mF0 mF1.
    apply mF in h; clear mF.
    apply equality_in_tnat in h.
    apply equality_of_nat_imp_tt in h.
    unfold equality_of_nat_tt in h; exrepnd.

    applydup @computes_to_valc_implies_hasvalue_likec in hv0.

    pose proof (computes_to_valc_differ_force2
                  lib (mkc_apply F (lam_force_nat_c nvarx nvarz f))
                  (mkc_apply F (bound2_cbv_c nvarx nvarz (mkc_nat n) f (mkc_utoken a)))
                  n a f k0) as h.
    repeat (autodimp h hyp);[|].
    { destruct_cterms; simpl.
      clear ceq1 h1 h0 hv0 hv1 mf.
      allunfold @getc_utokens; allsimpl.
      apply differ_force_oterm; simpl; tcsp.
      introv j; repndors; tcsp; ginv; constructor.
      - apply differ_force_refl; auto.
      - apply differ_force_oterm; simpl; tcsp.
        introv j; repndors; tcsp; ginv; constructor.
        apply differ_force_nat; auto. }

    repndors.

    + computes_to_eqval.
      allapply @eq_mkc_nat_implies; subst; auto.
      apply computes_to_valc_implies_cequivc; auto.

    + provefalse.
      apply cequivc_spexcc in h; exrepnd.
      eapply computes_to_valc_and_excc_false in h2; eauto.

  - provefalse.

    apply raises_exceptionc_as_computes_to_excc in hv; exrepnd.
    eapply computes_to_valc_mkc_try_if_exc in ceq1;[|exact hv1].
    apply computes_to_valc_mkc_atom_eq_pk_implies in ceq1; exrepnd.
    allrw @substc_mkcv_axiom.
    boolvar.

    + apply computes_to_valc_isvalue_eq in ceq1; eauto 3 with slow; ginv.

    + eapply computes_to_valc_and_excc_false in ceq1; tcsp.
      apply computes_to_excc_iff_reduces_toc.
      apply reduces_to_symm.
Qed.

Definition strong_continuous_type2_v2 {o} (x M f n : NVar) (F : @NTerm o) T :=
  mk_sqexists
    (mod_fun_type_v2 x T)
    M
    (mk_all
       (mk_nat2T T)
       f
       (mk_prod
          (mk_sqexists
             mk_tnat
             n
             (mk_equality
                (mk_apply2 (mk_var M) (mk_var n) (mk_var f))
                (mk_apply F (mk_var f))
                mk_natU))
          (mk_all
             mk_tnat
             n
             (mk_ufun
                (mk_isint (mk_apply2 (mk_var M) (mk_var n) (mk_var f)) mk_true mk_false)
                (mk_equality
                   (mk_apply2 (mk_var M) (mk_var n) (mk_var f))
                   (mk_apply F (mk_var f))
                   mk_tnat))))).

Definition rule_strong_continuity2_v2 {o}
           (F T t : @NTerm o)
           (x M f n : NVar)
           (H : barehypotheses) :=
    mk_rule
      (mk_baresequent H (mk_conclax (strong_continuous_type2_v2 x M f n F T)))
      [ mk_baresequent H (mk_conclax (mk_member F (mk_fun (mk_nat2T T) mk_tnat))),
        mk_baresequent H (mk_conclax (mk_member t T)) ]
      [].

Lemma rule_strong_continuity_true2_v2 {p} :
  forall lib
         (F T t : NTerm)
         (x M f n : NVar)
         (H : @barehypotheses p)
         (d1 : M <> f)
         (d2 : n <> f)
         (d3 : n <> M)
         (d4 : !LIn M (free_vars F))
         (d5 : !LIn f (free_vars F))
         (d6 : !LIn n (free_vars F))
         (d7 : !LIn x (free_vars T))
         (d8 : !LIn M (free_vars T))
         (nut : has_eq_value_type_nut lib T),
    rule_true lib (rule_strong_continuity2_v2
                     F T t
                     x M f n
                     H).
Proof.
  unfold rule_strong_continuity2, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  rename Hyp into hyp1.
  destruct hyp1 as [wc1 hyp1].
  rename Hyp0 into hyp2.
  destruct hyp2 as [wc2 hyp2].
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.

  exists (@covered_axiom p (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as h; exrepnd; clear hyp1.

  vr_seq_true in hyp2.
  pose proof (hyp2 s1 s2 eqh sim) as hTT; exrepnd; clear hyp2.

  allunfold @strong_continuous_type2_v2.
  allunfold @mk_sqexists.
  lsubst_tac.

  apply equality_in_member in hTT1; repnd.
  apply tequality_mkc_member_sp in hTT0; repnd.
  clear hTT0 hTT2 hTT3.

  apply member_if_inhabited in h1.
  apply tequality_mkc_member_sp in h0; repnd.
  allrw @fold_equorsq.
  clear h2.

  lsubst_tac.
  allrw @lsubstc_mkc_tnat.
  eapply member_respects_alphaeqc_r in h1;
    [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
      apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)].
  eapply respects_alphaeqc_equorsq3 in h0;
    [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
      apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)].

  dup h1 as memF.
  eapply cequorsq_equality_trans1 in memF;[|apply equorsq_sym;exact h0].
  apply equality_sym in memF.
  clear h0.

  prove_and teq.

  - apply tequality_mkc_squash.

    unfold mk_exists.
    lsubst_tac.

    apply tequality_product.
    dands.

    + eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply (lsubstc_mod_fun_type_v2_aux x T w3 s1 c4 wT cT);auto|].
      eapply tequality_respects_alphaeqc_right;
        [apply alphaeqc_sym;apply (lsubstc_mod_fun_type_v2_aux x T w3 s2 c6 wT cT1);auto|].
      apply tequality_modulus_fun_type_u_v2; auto.

    + intros M1 M2 em.
      eapply alphaeqc_preserving_equality in em;
        [|apply (lsubstc_mod_fun_type_v2_aux x T w3 s1 c4 wT cT);auto].
      repeat substc_lsubstc_vars3.

      unfold mk_all.
      lsubst_tac.

      apply tequality_function; dands.

      * eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)|].
        eapply tequality_respects_alphaeqc_right;
          [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w0 s2 c13 wT cT1)|].
        apply tequality_nat2T; auto.

      * intros f1 f2 en2n.
        eapply alphaeqc_preserving_equality in en2n;
          [|apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)].
        repeat substc_lsubstc_vars3.
        lsubst_tac.

        apply tequality_mkc_prod; dands.

        { apply tequality_mkc_squash.
          allrw @lsubstc_mkc_tnat.

          apply tequality_product; dands; eauto 3 with slow.
          { apply type_tnat. }

          intros n1 n2 en.
          repeat substc_lsubstc_vars3.
          a_lsubst_tac.

          apply tequality_mkc_equality_if_equal.

          { eapply tequality_respects_alphaeqc_left;
            [apply alphaeqc_sym; apply lsubstc_mk_natU|].
            eapply tequality_respects_alphaeqc_right;
              [apply alphaeqc_sym; apply lsubstc_mk_natU|].
            apply type_natU. }

          { eapply alphaeqc_preserving_equality;
            [|apply alphaeqc_sym; apply lsubstc_mk_natU].
            eapply equality_in_modulus_fun_type_u_implies_v2; eauto. }

          { eapply alphaeqc_preserving_equality;
            [|apply alphaeqc_sym; apply lsubstc_mk_natU].
            apply equality_in_fun in memF; repnd; clear memF0 memF1.
            apply memF in en2n; auto.
            apply equality_in_bunion_left; eauto 2 with slow. }
        }

        { intro inh; clear inh.
          allrw @lsubstc_mkc_tnat.
          apply tequality_function; dands.
          { apply type_tnat. }

          intros n1 n2 en.
          repeat substc_lsubstc_vars3.
          a_lsubst_tac.
          allrw @lsubstc_mk_true.
          allrw @lsubstc_mk_false.
          allrw @lsubstc_mk_tnat.
          apply tequality_mkc_ufun; dands.

          { pose proof (equality_in_modulus_fun_type_u_implies_v2
                          lib M1 M2 n1 n2 f1 f2 (lsubstc T wT s1 cT)) as h.
            repeat (autodimp h hyp).
            apply equality_in_disjoint_bunion in h; eauto 3 with slow.
            repnd; clear h0 h2.
            repndors.

            - apply equality_in_tnat in h.
              unfold equality_of_nat in h; exrepnd; spcast.
              eapply tequality_respects_cequivc_left;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_right;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_left;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
              eapply tequality_respects_cequivc_right;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
              apply type_mkc_true.

            - apply equality_in_unit in h; repnd; spcast.
              eapply tequality_respects_cequivc_left;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_right;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_left;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
              eapply tequality_respects_cequivc_right;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
              apply tequality_false.
          }

          { introv inh.
            pose proof (equality_in_modulus_fun_type_u_implies_v2
                          lib M1 M2 n1 n2 f1 f2 (lsubstc T wT s1 cT)) as h.
            repeat (autodimp h hyp).
            apply equality_in_fun in memF; repnd; clear memF0 memF1.
            apply memF in en2n; auto.
            apply equality_in_natU_implies_cequivc in h; spcast.
            apply equality_in_tnat_implies_cequivc in en2n.
            apply tequality_equality_if_cequivc; eauto 3 with slow.
            apply type_tnat.
          }
        }

  - apply equality_in_mkc_squash; dands;
    try (spcast; apply computes_to_valc_refl; eauto 3 with slow);[].

    unfold mk_exists.
    lsubst_tac.

    exists (mkc_pair (spM_c (lsubstc F wt0 s1 ct2))
                     (mkc_lam f (mkcv_pair
                                   [f]
                                   (mkcv_axiom f)
                                   (mkcv_lam [f] n (mkcv_ax [n,f]))))).

    apply equality_in_product.
    dands.

    + eapply type_respects_alphaeqc;
      [apply alphaeqc_sym;apply (lsubstc_mod_fun_type_v2_aux x T w3 s1 c4 wT cT);auto|].
      apply tequality_modulus_fun_type_u_v2; eauto 3 with slow.
      eapply tequality_refl; eauto.

    + intros M1 M2 em.
      eapply alphaeqc_preserving_equality in em;
        [|apply (lsubstc_mod_fun_type_v2_aux x T w3 s1 c4 wT cT);auto].
      repeat substc_lsubstc_vars3.

      unfold mk_all.
      lsubst_tac.

      apply tequality_function; dands.

      * eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)|].
        eapply tequality_respects_alphaeqc_right;
          [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)|].
        apply tequality_nat2T.
        eapply tequality_refl; eauto.

      * intros f1 f2 en2n.
        eapply alphaeqc_preserving_equality in en2n;
          [|apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)].
        repeat substc_lsubstc_vars3.
        lsubst_tac.

        apply tequality_mkc_prod; dands.

        { apply tequality_mkc_squash.
          allrw @lsubstc_mkc_tnat.

          apply tequality_product; dands; eauto 3 with slow.
          { apply type_tnat. }

          intros n1 n2 en.
          repeat substc_lsubstc_vars3.
          a_lsubst_tac.

          apply tequality_mkc_equality_if_equal.

          { eapply tequality_respects_alphaeqc_left;
            [apply alphaeqc_sym; apply lsubstc_mk_natU|].
            eapply tequality_respects_alphaeqc_right;
              [apply alphaeqc_sym; apply lsubstc_mk_natU|].
            apply type_natU. }

          { eapply alphaeqc_preserving_equality;
            [|apply alphaeqc_sym; apply lsubstc_mk_natU].
            eapply equality_in_modulus_fun_type_u_implies_v2; eauto. }

          { eapply alphaeqc_preserving_equality;
            [|apply alphaeqc_sym; apply lsubstc_mk_natU].
            apply equality_refl in memF.
            apply equality_in_fun in memF; repnd; clear memF0 memF1.
            apply memF in en2n; auto.
            apply equality_in_bunion_left; eauto 2 with slow. }
        }

        { intro inh; clear inh.
          allrw @lsubstc_mkc_tnat.
          apply tequality_function; dands.
          { apply type_tnat. }

          intros n1 n2 en.
          repeat substc_lsubstc_vars3.
          a_lsubst_tac.
          allrw @lsubstc_mk_true.
          allrw @lsubstc_mk_false.
          allrw @lsubstc_mk_tnat.
          apply tequality_mkc_ufun; dands.

          { pose proof (equality_in_modulus_fun_type_u_implies_v2
                          lib M1 M2 n1 n2 f1 f2 (lsubstc T wT s1 cT)) as h.
            repeat (autodimp h hyp).
            apply equality_in_disjoint_bunion in h; eauto 3 with slow.
            repnd; clear h0 h2.
            repndors.

            - apply equality_in_tnat in h.
              unfold equality_of_nat in h; exrepnd; spcast.
              eapply tequality_respects_cequivc_left;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_right;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_left;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
              eapply tequality_respects_cequivc_right;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
              apply type_mkc_true.

            - apply equality_in_unit in h; repnd; spcast.
              eapply tequality_respects_cequivc_left;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_right;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_left;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
              eapply tequality_respects_cequivc_right;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
              apply tequality_false.
          }

          { introv inh.
            pose proof (equality_in_modulus_fun_type_u_implies_v2
                          lib M1 M2 n1 n2 f1 f2 (lsubstc T wT s1 cT)) as h.
            repeat (autodimp h hyp).
            apply equality_refl in memF.
            apply equality_in_fun in memF; repnd; clear memF0 memF1.
            apply memF in en2n; auto.
            apply equality_in_natU_implies_cequivc in h; spcast.
            apply equality_in_tnat_implies_cequivc in en2n.
            apply tequality_equality_if_cequivc; eauto 3 with slow.
            apply type_tnat.
          }
        }

    + eexists; eexists; eexists; eexists; dands; spcast;
      try (apply computes_to_valc_refl; eauto 3 with slow).

      * eapply alphaeqc_preserving_equality;
        [|apply alphaeqc_sym;apply (lsubstc_mod_fun_type_v2_aux x T w3 s1 c4 wT cT);auto].

        apply (spM_in_modulus_fun_type_u_v2 _ _ (lsubstc t wt s1 ct1)); auto.

      * repeat substc_lsubstc_vars3.
        unfold mk_all.
        lsubst_tac.

        apply equality_in_function.
        dands.

        { eapply type_respects_alphaeqc;
          [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)|].
          eauto 3 with slow.
          apply tequality_nat2T; eauto 3 with slow.
          eapply tequality_refl; eauto. }

        { intros f1 f2 en2n.
          eapply alphaeqc_preserving_equality in en2n;
            [|apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)].
          repeat substc_lsubstc_vars3.
          lsubst_tac.

          apply tequality_mkc_prod; dands.

          { apply tequality_mkc_squash.
            allrw @lsubstc_mkc_tnat.

            apply tequality_product; dands; eauto 3 with slow.
            { apply type_tnat. }

            intros n1 n2 en.
            repeat substc_lsubstc_vars3.
            a_lsubst_tac.

            apply tequality_mkc_equality_if_equal.

            { eapply tequality_respects_alphaeqc_left;
              [apply alphaeqc_sym; apply lsubstc_mk_natU|].
              eapply tequality_respects_alphaeqc_right;
                [apply alphaeqc_sym; apply lsubstc_mk_natU|].
              apply type_natU. }

            { eapply alphaeqc_preserving_equality;
              [|apply alphaeqc_sym; apply lsubstc_mk_natU].
              pose proof (spM_in_modulus_fun_type_u_v2
                            lib
                            (lsubstc F wt0 s1 ct2)
                            (lsubstc t wt s1 ct1)
                            (lsubstc T wT s1 cT)) as h.
              repeat (autodimp h hyp);[].
              eapply equality_in_modulus_fun_type_u_implies_v2; eauto. }

            { eapply alphaeqc_preserving_equality;
              [|apply alphaeqc_sym; apply lsubstc_mk_natU].
              apply equality_refl in memF.
              apply equality_in_fun in memF; repnd; clear memF0 memF1.
              apply memF in en2n; auto.
              apply equality_in_bunion_left; eauto 2 with slow. }
          }

          { intro inh; clear inh.
            allrw @lsubstc_mkc_tnat.
            apply tequality_function; dands.
            { apply type_tnat. }

            intros n1 n2 en.
            repeat substc_lsubstc_vars3.
            a_lsubst_tac.
            allrw @lsubstc_mk_true.
            allrw @lsubstc_mk_false.
            allrw @lsubstc_mk_tnat.

            pose proof (spM_in_modulus_fun_type_u_v2
                          lib
                          (lsubstc F wt0 s1 ct2)
                          (lsubstc t wt s1 ct1)
                          (lsubstc T wT s1 cT)) as spMt.
            repeat (autodimp spMt hyp);[].
            apply tequality_mkc_ufun; dands.

            { pose proof (equality_in_modulus_fun_type_u_implies_v2
                            lib
                            (spM_c (lsubstc F wt0 s1 ct2))
                            (spM_c (lsubstc F wt0 s1 ct2))
                            n1 n2 f1 f2
                            (lsubstc T wT s1 cT)) as h.
              repeat (autodimp h hyp).
              apply equality_in_disjoint_bunion in h; eauto 3 with slow.
              repnd; clear h0 h2.
              repndors.

              - apply equality_in_tnat in h.
                unfold equality_of_nat in h; exrepnd; spcast.
                eapply tequality_respects_cequivc_left;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_right;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_left;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                eapply tequality_respects_cequivc_right;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                apply type_mkc_true.

              - apply equality_in_unit in h; repnd; spcast.
                eapply tequality_respects_cequivc_left;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_right;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_left;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                eapply tequality_respects_cequivc_right;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                apply tequality_false.
            }

            { introv inh.
              pose proof (equality_in_modulus_fun_type_u_implies_v2
                            lib
                            (spM_c (lsubstc F wt0 s1 ct2))
                            (spM_c (lsubstc F wt0 s1 ct2))
                            n1 n2 f1 f2
                            (lsubstc T wT s1 cT)) as h.
              repeat (autodimp h hyp).
              apply equality_refl in memF.
              apply equality_in_fun in memF; repnd; clear memF0 memF1.
              apply memF in en2n; auto.
              apply equality_in_natU_implies_cequivc in h; spcast.
              apply equality_in_tnat_implies_cequivc in en2n.
              apply tequality_equality_if_cequivc; eauto 3 with slow.
              apply type_tnat.
            }
          }
        }

        { intros f1 f2 en2n.
          eapply alphaeqc_preserving_equality in en2n;
            [|apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)].
          repeat substc_lsubstc_vars3.
          lsubst_tac.

          eapply equality_respects_cequivc_left;
            [apply cequivc_sym;apply cequivc_beta|].
          eapply equality_respects_cequivc_right;
            [apply cequivc_sym;apply cequivc_beta|].
          allrw @mkcv_pair_substc.
          allrw @substc_mkcv_axiom.
          repeat (rw @mkcv_lam_substc;auto;[]).
          allrw @mkcv_ax_eq.
          allrw @substc2_mk_cv.
          allrw @lsubstc_mkc_tnat.

          apply equality_in_prod.
          dands.

          { apply tequality_mkc_squash.

            apply tequality_product; dands; eauto 3 with slow.
            { apply type_tnat. }

            intros n1 n2 en.
            repeat substc_lsubstc_vars3.
            a_lsubst_tac.

            apply tequality_mkc_equality_if_equal.

            { eapply tequality_respects_alphaeqc_left;
              [apply alphaeqc_sym; apply lsubstc_mk_natU|].
              eapply tequality_respects_alphaeqc_right;
                [apply alphaeqc_sym; apply lsubstc_mk_natU|].
              apply type_natU. }

            { eapply alphaeqc_preserving_equality;
              [|apply alphaeqc_sym; apply lsubstc_mk_natU].
              applydup @equality_refl in en2n.
              pose proof (spM_in_modulus_fun_type_u_v2
                            lib
                            (lsubstc F wt0 s1 ct2)
                            (lsubstc t wt s1 ct1)
                            (lsubstc T wT s1 cT)) as h.
              repeat (autodimp h hyp);[].
              eapply equality_in_modulus_fun_type_u_implies_v2; eauto. }

            { eapply alphaeqc_preserving_equality;
              [|apply alphaeqc_sym; apply lsubstc_mk_natU].
              apply equality_refl in memF; auto.
              apply equality_in_fun in memF; repnd; clear memF0 memF1.
              apply memF in en2n; auto.
              applydup @equality_refl in en2n.
              apply equality_in_bunion_left; eauto 2 with slow. }
          }

          { intro inh; clear inh.
            allrw @lsubstc_mkc_tnat.
            apply tequality_function; dands.
            { apply type_tnat. }

            intros n1 n2 en.
            repeat substc_lsubstc_vars3.
            a_lsubst_tac.
            allrw @lsubstc_mk_true.
            allrw @lsubstc_mk_false.
            allrw @lsubstc_mk_tnat.

            pose proof (spM_in_modulus_fun_type_u_v2
                          lib
                          (lsubstc F wt0 s1 ct2)
                          (lsubstc t wt s1 ct1)
                          (lsubstc T wT s1 cT)) as spMt.
            repeat (autodimp spMt hyp);[].
            apply tequality_mkc_ufun; dands.

            { applydup @equality_refl in en2n.
              pose proof (equality_in_modulus_fun_type_u_implies_v2
                            lib
                            (spM_c (lsubstc F wt0 s1 ct2))
                            (spM_c (lsubstc F wt0 s1 ct2))
                            n1 n2 f1 f1
                            (lsubstc T wT s1 cT)) as h.
              repeat (autodimp h hyp);[].
              apply equality_in_disjoint_bunion in h; eauto 3 with slow.
              repnd; clear h0 h2.
              repndors.

              - apply equality_in_tnat in h.
                unfold equality_of_nat in h; exrepnd; spcast.
                eapply tequality_respects_cequivc_left;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_right;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_left;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                eapply tequality_respects_cequivc_right;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                apply type_mkc_true.

              - apply equality_in_unit in h; repnd; spcast.
                eapply tequality_respects_cequivc_left;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_right;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_left;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                eapply tequality_respects_cequivc_right;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                apply tequality_false.
            }

            { introv inh.
              applydup @equality_refl in en2n.
              pose proof (equality_in_modulus_fun_type_u_implies_v2
                            lib
                            (spM_c (lsubstc F wt0 s1 ct2))
                            (spM_c (lsubstc F wt0 s1 ct2))
                            n1 n2 f1 f1
                            (lsubstc T wT s1 cT)) as h.
              repeat (autodimp h hyp).
              apply equality_refl in memF.
              apply equality_in_fun in memF; repnd; clear memF0 memF1.
              apply memF in en2n; auto.
              applydup @equality_refl in en2n.
              apply equality_in_natU_implies_cequivc in h; spcast.
              apply equality_in_tnat_implies_cequivc in en2n.
              apply tequality_equality_if_cequivc; eauto 3 with slow.
              apply type_tnat.
            }
          }

          { exists (@mkc_axiom p) (@mkc_axiom p)
                   (@mkc_lam p n (mk_cv [n] mkc_axiom))
                   (@mkc_lam p n (mk_cv [n] mkc_axiom)).
            dands; spcast.
            { apply computes_to_valc_refl; eauto 3 with slow. }
            { apply computes_to_valc_refl; eauto 3 with slow. }

            { apply equality_in_mkc_squash; dands; spcast;
              try (apply computes_to_valc_refl; eauto 3 with slow);[].

              applydup @equality_refl in en2n as mf1.
              pose proof (spM_cond_v2
                            lib
                            (lsubstc F wt0 s1 ct2)
                            f1
                            (lsubstc T wT s1 cT)
                            h1 mf1) as h.
              exrepnd.

              allrw @lsubstc_mkc_tnat.

              exists (mkc_pair (mkc_nat n0) (@mkc_axiom p)).

              apply equality_in_product; dands; eauto 3 with slow.

              - intros n1 n2 en.
                repeat substc_lsubstc_vars3.
                a_lsubst_tac.

                apply tequality_mkc_equality_if_equal.

                { eapply tequality_respects_alphaeqc_left;
                  [apply alphaeqc_sym; apply lsubstc_mk_natU|].
                  eapply tequality_respects_alphaeqc_right;
                    [apply alphaeqc_sym; apply lsubstc_mk_natU|].
                  apply type_natU. }

                { eapply alphaeqc_preserving_equality;
                  [|apply alphaeqc_sym; apply lsubstc_mk_natU].

                  pose proof (spM_in_modulus_fun_type_u_v2
                                lib
                                (lsubstc F wt0 s1 ct2)
                                (lsubstc t wt s1 ct1)
                                (lsubstc T wT s1 cT)) as h.
                  repeat (autodimp h hyp);[].
                  rw @equality_in_function in h; repnd.
                  applydup h in en as e.
                  eapply alphaeqc_preserving_equality in e;[|apply substc_mkcv_fun].
                  rw @csubst_mk_cv in e.

                  try (fold (@natU p) in e).
                  eapply alphaeqc_preserving_equality in e;
                    [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
                      apply substc_mkcv_fun].
                  eapply alphaeqc_preserving_equality in e;
                    [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
                      apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
                      apply mkcv_natk_substc
                    ].
                  allrw @mkc_var_substc.
                  allrw @mkcv_tnat_substc.

                  try (fold (natk2nat n1) in e).

                  applydup @equality_refl in en.
                  apply (equality_nat2T_to_natk2T lib n1) in en2n; auto;[].

                  apply equality_in_fun in e; repnd; clear e0 e1.
                  applydup @equality_refl in en2n as ef.
                  allrw @csubst_mk_cv.
                  apply e in ef.
                  allrw <- @mkc_apply2_eq; auto. }

                { eapply alphaeqc_preserving_equality;
                  [|apply alphaeqc_sym; apply lsubstc_mk_natU].
                  apply equality_refl in memF.
                  apply equality_in_fun in memF; repnd; clear memF0 memF1.
                  apply memF in en2n; auto.
                  apply equality_in_bunion_left; eauto 2 with slow. }

              - eexists; eexists; eexists; eexists; dands; spcast;
                try (apply computes_to_valc_refl; eauto 3 with slow);
                eauto 3 with slow.

                repeat substc_lsubstc_vars3.
                a_lsubst_tac.

                apply member_equality.
                eapply alphaeqc_preserving_equality;
                  [|apply alphaeqc_sym; apply lsubstc_mk_natU].
                auto.
            }

            { apply equality_in_function3.
              dands; eauto 3 with slow;[].

              intros n1 n2 en.
              repeat substc_lsubstc_vars3.
              a_lsubst_tac.
              allrw @lsubstc_mk_true.
              allrw @lsubstc_mk_false.
              allrw @lsubstc_mkc_tnat.

              dands.

              - pose proof (spM_in_modulus_fun_type_u_v2
                                lib
                                (lsubstc F wt0 s1 ct2)
                                (lsubstc t wt s1 ct1)
                                (lsubstc T wT s1 cT)) as spMt.
                repeat (autodimp spMt hyp);[].
                apply tequality_mkc_ufun; dands.

                { applydup @equality_refl in en2n.
                  pose proof (equality_in_modulus_fun_type_u_implies_v2
                                lib
                                (spM_c (lsubstc F wt0 s1 ct2))
                                (spM_c (lsubstc F wt0 s1 ct2))
                                n1 n2 f1 f1
                                (lsubstc T wT s1 cT)) as h.
                  repeat (autodimp h hyp).
                  apply equality_in_disjoint_bunion in h; eauto 3 with slow.
                  repnd; clear h0 h2.
                  repndors.

                  - apply equality_in_tnat in h.
                    unfold equality_of_nat in h; exrepnd; spcast.
                    eapply tequality_respects_cequivc_left;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_right;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_left;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                    eapply tequality_respects_cequivc_right;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                    apply type_mkc_true.

                  - apply equality_in_unit in h; repnd; spcast.
                    eapply tequality_respects_cequivc_left;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_right;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_left;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                    eapply tequality_respects_cequivc_right;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                    apply tequality_false.
                }

                { introv inh.
                  applydup @equality_refl in en2n.
                  pose proof (equality_in_modulus_fun_type_u_implies_v2
                                lib
                                (spM_c (lsubstc F wt0 s1 ct2))
                                (spM_c (lsubstc F wt0 s1 ct2))
                                n1 n2 f1 f1
                                (lsubstc T wT s1 cT)) as h.
                  repeat (autodimp h hyp).
                  apply equality_refl in memF.
                  apply equality_in_fun in memF; repnd; clear memF0 memF1.
                  apply memF in en2n; auto.
                  applydup @equality_refl in en2n.
                  apply equality_in_natU_implies_cequivc in h; spcast.
                  apply equality_in_tnat_implies_cequivc in en2n.
                  apply tequality_equality_if_cequivc; eauto 3 with slow.
                  apply type_tnat.
                }

              - apply equality_in_ufun.
                pose proof (spM_in_modulus_fun_type_u_v2
                              lib
                              (lsubstc F wt0 s1 ct2)
                              (lsubstc t wt s1 ct1)
                              (lsubstc T wT s1 cT)) as spMt.
                repeat (autodimp spMt hyp);[].

                dands.

                { applydup @equality_refl in en2n.
                  pose proof (equality_in_modulus_fun_type_u_implies_v2
                                lib
                                (spM_c (lsubstc F wt0 s1 ct2))
                                (spM_c (lsubstc F wt0 s1 ct2))
                                n1 n2 f1 f1
                                (lsubstc T wT s1 cT)) as h.
                  repeat (autodimp h hyp).
                  apply equality_in_disjoint_bunion in h; eauto 3 with slow.
                  repnd; clear h0 h2.
                  repndors.

                  - apply equality_in_tnat in h.
                    unfold equality_of_nat in h; exrepnd; spcast.
                    eapply tequality_respects_cequivc_left;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_right;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_left;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                    eapply tequality_respects_cequivc_right;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                    apply type_mkc_true.

                  - apply equality_in_unit in h; repnd; spcast.
                    eapply tequality_respects_cequivc_left;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_right;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_left;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                    eapply tequality_respects_cequivc_right;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                    apply tequality_false.
                }

                { introv inh; clear inh.
                  applydup @equality_refl in en2n.
                  pose proof (equality_in_modulus_fun_type_u_implies_v2
                                lib
                                (spM_c (lsubstc F wt0 s1 ct2))
                                (spM_c (lsubstc F wt0 s1 ct2))
                                n1 n2 f1 f1
                                (lsubstc T wT s1 cT)) as h.
                  repeat (autodimp h hyp).
                  apply equality_refl in memF.
                  apply equality_in_fun in memF; repnd; clear memF0 memF1.
                  apply memF in en2n; auto.
                  applydup @equality_refl in en2n.
                  apply equality_in_natU_implies_cequivc in h; spcast.
                  apply equality_in_tnat_implies_cequivc in en2n.
                  apply tequality_equality_if_cequivc; eauto 3 with slow.
                  apply type_tnat.
                }

                { introv inh.
                  eapply equality_respects_cequivc_left;
                    [apply cequivc_sym;apply cequivc_beta|].
                  eapply equality_respects_cequivc_right;
                    [apply cequivc_sym;apply cequivc_beta|].
                  allrw @csubst_mk_cv.

                  applydup @equality_refl in en2n.
                  pose proof (equality_in_modulus_fun_type_u_implies_v2
                                lib
                                (spM_c (lsubstc F wt0 s1 ct2))
                                (spM_c (lsubstc F wt0 s1 ct2))
                                n1 n2 f1 f1
                                (lsubstc T wT s1 cT)) as h.
                  repeat (autodimp h hyp).

                  apply equality_in_disjoint_bunion in h; eauto 3 with slow.
                  repnd; clear h0 h2.
                  repndors; apply equality_refl in h.

                  - apply equality_in_tnat in h.
                    unfold equality_of_nat in h; exrepnd; spcast.

                    apply equality_in_tnat in en.
                    unfold equality_of_nat in en; exrepnd; spcast.

                    pose proof (spM_cond2_v2
                                  lib (lsubstc F wt0 s1 ct2) f1 k0 k
                                  (lsubstc T wT s1 cT)) as cond2.
                    repeat (autodimp cond2 hyp).
                    { eapply cequivc_trans;
                      [apply implies_cequivc_apply2;
                        [apply cequivc_refl
                        |apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact en1
                        |apply cequivc_refl]
                      |].
                      apply computes_to_valc_implies_cequivc; auto. }
                    apply member_equality.

                    eapply equality_respects_cequivc_right;
                      [apply cequivc_sym;exact cond2|].

                    eapply equality_respects_cequivc_left;
                      [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2|].
                    eauto 3 with slow.

                  - apply equality_in_unit in h.
                    repnd; spcast.
                    eapply inhabited_type_cequivc in inh;
                      [|apply implies_cequivc_isint;
                         [apply computes_to_valc_implies_cequivc;exact h
                         |apply cequivc_refl
                         |apply cequivc_refl]
                      ].
                    eapply inhabited_type_cequivc in inh;
                      [|apply cequivc_mkc_isint_mkc_axiom].
                    unfold inhabited_type in inh; exrepnd.
                    apply false_not_inhabited in inh0; sp.
                }
            }
          }
        }
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
