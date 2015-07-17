(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export alphaeq.
Require Export computation.
Require Export rel_nterm.
Require Export substitution2.
Require Export cequiv.

Definition cequiv_option {o} lib (op1 op2 : option (@NTerm o)) :=
  match op1, op2 with
    | Some t1, Some t2 => cequiv lib t1 t2
    | None, None => True
    | _,_ => False
  end.

Lemma cequiv_option_trans {o} :
   forall lib (t1 t3 : option (@NTerm o)) (t2 : @NTerm o),
   cequiv_option lib t1 (Some t2) -> 
   cequiv_option lib (Some t2) t3 -> 
   cequiv_option lib t1 t3.
Proof. introv eq1 eq2.
       destruct t1; destruct t3;
       allsimpl; auto.
       eapply cequiv_trans; eauto.
Qed.

Definition ext_cequiv_subs {o} lib  (sub1 sub2 : @Sub o) :=
  (forall v, LIn v (dom_sub sub1) <=> LIn v (dom_sub sub2)) #
  forall v,
    LIn v (dom_sub sub1)
    -> cequiv_option lib (sub_find sub1 v) (sub_find sub2 v).


Lemma ext_cequiv_subs_trans {o} :
   forall lib  (sub1 sub2 sub3 : @Sub o),
   ext_cequiv_subs lib  sub1 sub2 -> 
   ext_cequiv_subs lib  sub2 sub3 -> 
   ext_cequiv_subs lib  sub1 sub3.
Proof. introv eq1 eq2. 
       destruct eq1 as [domeq1 eq1].
       destruct eq2 as [domeq2 eq2].
       split; intro.
       -  rw domeq1; rw domeq2; sp.
       -  introv indom. dup indom as indom2. rw domeq1 in indom2. 
           pose proof (eq1 v indom) as eqa; clear eq1.
           pose proof (eq2 v indom2) as eqb; clear eq2.
           apply in_dom_sub_exists in indom2; exrepnd.
           rw indom0 in eqa. 
           rw indom0 in eqb.
           eapply cequiv_option_trans; eauto.
Qed.

Lemma ext_cequiv_sym {o} :
   forall lib  (sub1 sub2 : @Sub o),
   ext_cequiv_subs lib  sub1 sub2 -> 
   ext_cequiv_subs lib  sub2 sub1.
Proof. introv eq1. 
       destruct eq1 as [domeq1 eq1].
       split; intro.
       -  rw domeq1;  sp.
       -  introv indom. rw<- domeq1 in indom. 
           pose proof (eq1 v indom) as eqa; clear eq1.
           remember (sub_find sub2 v) as a; destruct a;
          remember  (sub_find sub1 v) as b; destruct b;
          allsimpl; auto; apply cequiv_sym; auto.
Qed.


Lemma cequiv_subst_implies_ext_cequiv_subs {o} :
    forall lib  (sub1 sub2 : @Sub o),
    cequiv_subst lib  sub1 sub2 -> 
   ext_cequiv_subs lib  sub1 sub2.
Proof. induction sub1; induction sub2; introv eq;
       inversion eq.
       - split; simpl; auto; sp.
       - apply IHsub1 in X0.
         split.
         + destruct X0 as [samedom X0]; simpl; split; introv Z; destruct Z as [Z1|Z2];
           try (left;exact Z1); right; apply samedom; auto.
         +  introv Z; destruct Z as [Z1|Z2]. 
            * allsimpl; subst; rw<- beq_var_refl; simpl; auto.
            * allsimpl; remember (beq_var v v0) as c; destruct c; simpl; auto.
              destruct X0 as [b c]; apply c; auto.
Qed.


Lemma ext_alpha_eq_subs_implies_ext_cequiv_subs {o} :
    forall lib  (sub1 sub2 : @Sub o),
    (forall v : NVar, LIn v (dom_sub sub1) <=> LIn v (dom_sub sub2)) ->
    ext_alpha_eq_subs (dom_sub sub1) sub1 sub2 -> 
   ext_cequiv_subs lib  sub1 sub2.
Proof. introv samedom eq. split. auto. introv indom. 
       pose proof (eq v indom) as eq2.
       revert eq2. generalize (sub_find sub1 v); generalize (sub_find sub2 v).
       intros; destruct o0; destruct o1; allsimpl; auto.
       apply alpha_implies_cequiv; auto.
Qed. 


Lemma ext_cequiv_preserves_isprogram {o} :
   forall lib,
   forall sub1 sub2 : @Sub o,
   forall t,
   ext_cequiv_subs lib  sub1 sub2  ->
   isprogram (lsubst t sub1) ->
   isprogram (lsubst t sub2).
Proof. admit.
Qed.

Lemma ext_cequiv_to_cequiv_subst {o} :
   forall lib,
   forall sub1 sub2 : @Sub o,
   ext_cequiv_subs lib  sub1 sub2  ->
   { suba : @Sub o $
   { subb : @Sub o $ 
     ext_alpha_eq_subs (dom_sub sub1) suba sub1 # 
     ext_alpha_eq_subs (dom_sub sub1) subb sub2 # 
     cequiv_subst lib suba subb
   }}.
Proof. admit.
Qed.

Lemma cequiv_lsubst_if_ext_cequiv {o} :
  forall lib,
  forall (t1 t2 : @NTerm o) sub1 sub2,
    cequiv_open lib t1 t2
    -> ext_cequiv_subs lib sub1 sub2
    ->  isprogram (lsubst t1 sub1)
    ->  isprogram (lsubst t2 sub2)
    -> cequiv lib (lsubst t1 sub1) (lsubst t2 sub2).
Proof.
  introv aeq ext isp1 isp2.
  apply ext_cequiv_to_cequiv_subst in ext; exrepnd.
  assert (isprogram (lsubst t1 suba)).
   {eapply ext_cequiv_preserves_isprogram; [ | exact isp1].
    admit.
   }
  assert (isprogram (lsubst t2 subb)).
   {admit. }
  assert (cequiv lib (lsubst t1 sub1) (lsubst t1 suba)) as eq1.
    apply alpha_implies_cequiv; auto.
    { apply alpha_eq_lsubst_if_ext_eq; eauto 3 with slow. 
      admit.
    }
  assert (cequiv lib (lsubst t2 sub2) (lsubst t2 subb)) as eq2.
    apply alpha_implies_cequiv; auto.
    { apply alpha_eq_lsubst_if_ext_eq; eauto 3 with slow. 
      admit.
    }
  assert (cequiv lib (lsubst t1 suba) (lsubst t2 subb)) as eq3 by
    (apply lsubst_cequiv_congr; auto).
  eapply cequiv_trans; [exact eq1 |].
  eapply cequiv_trans; [exact eq3 | apply cequiv_sym; auto].
Qed.

