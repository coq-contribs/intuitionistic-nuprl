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
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand &  Vincent Rahli & Mark Bickford

*)

Require Export list.
Require Export sequents.

(** substitute_hyp applies a substitution to the type of an hypothesis *)
Definition lsubst_hyp {o} (sub : (@Substitution o)) (h : hypothesis) : hypothesis :=
  match h with
  | {| hvar := hv; hidden := hi; htyp := ht; lvl := l |} =>
      {| hvar := hv; hidden := hi; htyp := lsubst ht sub; lvl := l |}
  end.

(** substitute_hyps applies a substitution to all the types of a list of
 * hypotheses. *)
Fixpoint lsubst_hyps {o} (sub : (@Substitution o)) (hs : barehypotheses) : barehypotheses :=
  match hs with
    | [] => []
    | h :: hs => lsubst_hyp sub h :: lsubst_hyps sub hs
  end.

Lemma is_nh_lsubst_hyp  {o} :
  forall sub a,
    is_nh (@lsubst_hyp o sub a) = is_nh a.
Proof.
  intros.
  destruct a; simpl; sp.
Qed.
Hint Rewrite @is_nh_lsubst_hyp : core.

Lemma lsubst_hyp_nil_sub {o} :
  forall h, @lsubst_hyp o [] h = h.
Proof.
  intro; unfold lsubst_hyp.
  destruct h.
  rewrite lsubst_nil; auto.
Qed.
Hint Rewrite @lsubst_hyp_nil_sub : core.


Lemma lsubst_hyps_nil_sub {o} :
  forall hs, @lsubst_hyps o [] hs = hs.
Proof.
  induction hs; simpl; auto.
  repeat (rewrite IHhs).
  rewrite lsubst_hyp_nil_sub; auto.
Qed.
Hint Rewrite @lsubst_hyps_nil_sub : core.


Lemma lsubst_hyps_snoc {o} :
  forall sub hs h, @lsubst_hyps o sub (snoc hs h) = snoc (lsubst_hyps sub hs) (lsubst_hyp sub h).
Proof.
  induction hs; simpl; auto; intros.
  repeat (rewrite IHhs); auto.
Qed.
Hint Rewrite @lsubst_hyps_snoc : core.


Lemma lsubst_hyps_cons {o} :
  forall sub h hs,
    @lsubst_hyps o sub (h :: hs) = lsubst_hyp sub h :: lsubst_hyps sub hs.
Proof.
  simpl; auto.
Qed.
Hint Rewrite @lsubst_hyps_cons : core.


Lemma mk_hs_subst_lsubst_hyps {o} :
  forall ts sub hs,
    mk_hs_subst ts (@lsubst_hyps o sub hs) = mk_hs_subst ts hs.
Proof.
  induction ts; simpl; intros; auto.
  destruct hs; simpl; auto.
  rewrite IHts.
  destruct h; simpl; auto.
Qed.
Hint Rewrite @mk_hs_subst_lsubst_hyps : core.


Lemma hvar_lsubst_hyp {o} :
  forall sub a,
    hvar (@lsubst_hyp o sub a) = hvar a.
Proof.
  destruct a; sp.
Qed.

Hint Rewrite @hvar_lsubst_hyp : core.

Lemma htyp_lsubst_hyp {o} :
  forall sub a,
    htyp (@lsubst_hyp o sub a) = lsubst (htyp a) sub.
Proof.
  destruct a; sp.
Qed.

Hint Rewrite @htyp_lsubst_hyp : core.

Lemma lvl_lsubst_hyp {o} :
  forall sub a,
    lvl (@lsubst_hyp o sub a) = lvl a.
Proof.
  destruct a; sp.
Qed.

Hint Rewrite @lvl_lsubst_hyp : core.

Lemma vars_hyps_lsubst_hyps {o} :
  forall sub hs,
    vars_hyps (@lsubst_hyps o sub hs) = vars_hyps hs.
Proof.
  induction hs; simpl; sp.
  rewrite IHhs.
  rewrite hvar_lsubst_hyp; sp.
Qed.

Hint Rewrite @vars_hyps_lsubst_hyps : core.

Lemma nh_vars_hyps_lsubst_hyps {o} :
  forall sub hs,
    nh_vars_hyps (@lsubst_hyps o sub hs) = nh_vars_hyps hs.
Proof.
  induction hs; simpl; sp.
  repeat (rewrite nh_vars_hyps_cons).
  rewrite IHhs.
  rewrite is_nh_lsubst_hyp.
  rewrite hvar_lsubst_hyp; sp.
Qed.

Hint Rewrite @nh_vars_hyps_lsubst_hyps : core.

Lemma length_lsubst_hyps {o} :
  forall sub hs,
    length (@lsubst_hyps o sub hs) = length hs.
Proof.
  induction hs; simpl; sp.
Qed.

Hint Rewrite @length_lsubst_hyps : core.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
