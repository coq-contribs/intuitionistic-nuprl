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

Require Export per_props.

Lemma type_mkc_top {o} : forall lib, @type o lib mkc_top.
Proof.
  introv.
  rw @tequality_isect; dands.
  apply tequality_false.
  introv ea.
  allrw @csubst_mk_cv.
  apply tequality_false.
Qed.
Hint Resolve type_mkc_top : slow.

Lemma equality_mkc_top {o} :
  forall lib (a b : @CTerm o), equality lib a b mkc_top.
Proof.
  introv.
  rw @equality_in_isect; dands; introv.

  - apply tequality_false.

  - introv e.
    apply equality_in_false in e; sp.

  - introv e.
    apply equality_in_false in e; sp.
Qed.
Hint Resolve equality_mkc_top : slow.

(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
