(*******************************************************************************

Title: Pullbacks3.v
Authors: Jeremy Avigad, Chris Kapulkin, Peter LeFanu Lumsdaine
Date: 1 March 2013

The (abstract) two pullbacks lemma.

*******************************************************************************)

(* Imports *)

Require Import HoTT EquivalenceVarieties.

Require Import Auxiliary Pullbacks.

(*******************************************************************************

The *abstract* two pullbacks lemma.

Suppose we have two squares that paste together to a rectangle, and
the right square is a pullback. Then the whole rectangle is a
pullback if and only if the left square is.

P2 ---> P1 ---> A
|       |_|     |f
V       V       V
B2 -h-> B1 -g-> C

For the proof, we first fix the outer cospan and right-hand square:

        P1 ---> A
        |_|     |f
        V       V
B2 -h-> B1 -g-> C

We then show that a cone over the left square is a pullback for that
square iff the composite cone is a pullback for the whole rectangle.

To prove this, we first construct a commutative triangle as follows:

        _->  (Cones from X to left-hand square)
      _-                 |
[X,P2]_                  |
       -_                V
         ->  (Cones from X to rectangle)

and show that the right-hand vertical map is a weak equivalence.

It then follows, by 2-of-3, that either of the diagonal maps is an
equivalence if the other one is; i.e. that the two universal
properties are equivalent.

See TwoPullbacks_alt.v for a more detailed discussion, and multiple approaches.

A naming convention we mostly adhere to: cones over the right-hand 
square (f,g) are named [C1], [C1'], etc; cones over the left-hand square
(or similar squares) are [C2], [C2'], etc; and cones over the whole
rectangle as [C3], etc. 

*******************************************************************************)

Section Abstract_Two_Pullbacks_Lemma.

Context {A B1 B2 C : Type} (f : A -> C) (g : B1 -> C) (h : B2 -> B1).

Definition left_cospan_cone_to_composite {P1 : Type} (C1 : cospan_cone f g P1)
  {P2 : Type} (C2: cospan_cone (cospan_cone_map2 C1) h P2)
: cospan_cone f (g o h) P2.
Proof.
  exists (cospan_cone_map1 C1 o cospan_cone_map1 C2).
  exists (cospan_cone_map2 C2).
  intros x.
  apply (concat (cospan_cone_comm C1 (cospan_cone_map1 C2 x))).
  apply (ap g (cospan_cone_comm C2 x)).
Defined.

Lemma two_pullback_triangle_commutes {P1 : Type} (C1 : cospan_cone f g P1)
  {P2 : Type} (C2 : cospan_cone (cospan_cone_map2 C1) h P2)
  {X : Type} (m : X -> P2)
: left_cospan_cone_to_composite C1 (map_to_cospan_cone C2 X m)
  = map_to_cospan_cone (left_cospan_cone_to_composite C1 C2) X m.
Proof.
  exact 1.
Defined.

Lemma composite_cospan_cone_to_left (P1 : abstract_pullback f g)
  {X : Type} (C2 : cospan_cone f (g o h) X)
: cospan_cone (cospan_cone_map2 P1) h X.
Proof.
  set (C1_UP_at_X := BuildEquiv (pullback_cone_UP P1 X)).
  set (C1' := @mk_cospan_cone _ _ _ f g _ _ _ (cospan_cone_comm C2)).
  exists (C1_UP_at_X ^-1 C1').
  exists (cospan_cone_map2 C2).
  intros x.
  apply (ap10 (packed_cospan_cone_map2 P1 C1') x).
Defined.

Lemma composite_cospan_cone_to_left_is_section
  (P1 : abstract_pullback f g) (X : Type)
: (@left_cospan_cone_to_composite _ P1 X) o (composite_cospan_cone_to_left P1)
  == idmap.
Proof.
  intro C2.
  set (C1' := @mk_cospan_cone _ _ _ f g _ _ _ (cospan_cone_comm C2)).
  apply cospan_cone_path'. simpl.
  exists (packed_cospan_cone_map1 P1 C1'). exists 1.
  intros x; simpl. apply (concatR (concat_p1 _)^).
  unfold cospan_cone_comm; simpl.
  apply moveR_pM. apply (packed_cospan_cone_comm P1 C1').
Qed.

Lemma left_cospan_cone_aux0 (P1 : abstract_pullback f g)
  {X : Type} (C2 : cospan_cone (cospan_cone_map2 P1) h X)
: @mk_cospan_cone _ _ _ f g _ _ _ (cospan_cone_comm (left_cospan_cone_to_composite P1 C2))
  = map_to_cospan_cone P1 X (cospan_cone_map1 C2).
Proof.
  apply cospan_cone_path'; simpl. exists 1.
  (* Helps human-readability, but slows Coq down:
  unfold cospan_cone_map2; simpl. *)
  exists (path_forall (fun x => (cospan_cone_comm C2 x)^)).
  intros x. unfold cospan_cone_comm at 1 2 3; simpl.
  apply concat2. apply inverse, concat_1p.
  apply (concatR (ap_V _ _)), ap.
  apply (concat (inv_V _)^), ap.
  revert x; apply apD10. apply inverse, eisretr.
Defined.

Lemma left_cospan_cone_aux1 (P1 : abstract_pullback f g)
  {X : Type} (C2 : cospan_cone (cospan_cone_map2 P1) h X)
: (BuildEquiv (pullback_cone_UP P1 X))^-1
      (@mk_cospan_cone _ _ _ f g _ _ _
        (cospan_cone_comm (left_cospan_cone_to_composite P1 C2)))
  = cospan_cone_map1 C2.
Proof.
  apply moveR_I. apply left_cospan_cone_aux0.
Defined.
 
Lemma left_cospan_cone_aux2 (P1 : abstract_pullback f g)
  {X : Type} (C2 : cospan_cone (cospan_cone_map2 P1) h X) (x:X)
  (C1' := @mk_cospan_cone _ _ _ f g _ _ _
             (cospan_cone_comm (left_cospan_cone_to_composite P1 C2)))
: ap (cospan_cone_map2 P1) (ap10 (left_cospan_cone_aux1 P1 C2) x)
  = (ap10 (ap cospan_cone_map2 (eisretr (map_to_cospan_cone P1 X) C1')) x
    @ (cospan_cone_comm C2 x)^).
Proof.
  set (P1_UP_at_X := BuildEquiv (pullback_cone_UP P1 X)).
  rewrite <- ap10_ap_postcompose.  
  change ((fun f' : X -> P1 => cospan_cone_map2 P1 o f'))
    with (cospan_cone_map2 o P1_UP_at_X).
  rewrite ap_compose.
  path_via' (ap10
    (ap cospan_cone_map2 (eisretr P1_UP_at_X C1')
    @ path_forall (fun y => (cospan_cone_comm C2 y)^)) x).
    Focus 2. rewrite ap10_pp.
    apply ap. revert x; apply apD10. apply eisretr.
  revert x; apply apD10; apply ap.
  unfold left_cospan_cone_aux1, moveR_I. fold P1_UP_at_X.
  rewrite ap_pp. rewrite ap_inverse_o_equiv. fold C1'.
  path_via' (ap cospan_cone_map2 (eisretr P1_UP_at_X C1'
                                 @ left_cospan_cone_aux0 P1 C2)).
    apply ap. rewrite eisadj. apply concat_pV_p.
  rewrite ap_pp. apply ap. refine (cospan_cone_path'_map2 _).
Qed.

Lemma composite_cospan_cone_to_left_is_retraction
  (P1 : abstract_pullback f g) (X : Type)
: (composite_cospan_cone_to_left P1) o (@left_cospan_cone_to_composite _ P1 X)
  == idmap.
Proof.
  intros C2.
  set (e := BuildEquiv (pullback_cone_UP P1 X)).
  set (C1' := (@mk_cospan_cone _ _ _ f g _ _ _
             (cospan_cone_comm (left_cospan_cone_to_composite P1 C2)))).
  unfold composite_cospan_cone_to_left.
  fold C1'. fold e.
  apply cospan_cone_path'.
    exists (left_cospan_cone_aux1 P1 C2).
    exists 1.
  intros x.
  path_via' (ap10 (packed_cospan_cone_map2 P1 C1') x).
    exact 1.
  apply (concatR (concat_p1 _)^).
  unfold packed_cospan_cone_map2.  simpl.
  path_via'
    ((ap10 (ap cospan_cone_map2 (eisretr e C1')) x
    @ (cospan_cone_comm C2 x)^)
    @ cospan_cone_comm C2 x).
    apply inverse, concat_pV_p.
  apply whiskerR. apply inverse. apply left_cospan_cone_aux2.
Qed.

Lemma left_cospan_cone_to_composite_isequiv
  (P1 : abstract_pullback f g) (X : Type)
: IsEquiv (@left_cospan_cone_to_composite _ P1 X).
Proof.
  apply (isequiv_adjointify (composite_cospan_cone_to_left P1)).
  apply composite_cospan_cone_to_left_is_section.
  apply composite_cospan_cone_to_left_is_retraction.
Qed.

Lemma abstract_two_pullbacks_lemma
  (P1 : abstract_pullback f g)
  {P2 : Type} (C2 : cospan_cone (cospan_cone_map2 P1) h P2)
: is_pullback_cone C2 <-> is_pullback_cone (left_cospan_cone_to_composite P1 C2).
Proof.
  set (P1_UP := pullback_cone_UP P1).
  split.
  (* -> *)
  intros C2_UP X.
  change (map_to_cospan_cone (left_cospan_cone_to_composite P1 C2) X)
  with (left_cospan_cone_to_composite P1 o (map_to_cospan_cone C2 X)).
  apply @isequiv_compose.
    apply C2_UP.
  apply left_cospan_cone_to_composite_isequiv.
  (* <- *)
  intros C3_UP X.
  refine (cancelL_isequiv (left_cospan_cone_to_composite P1)).
  apply left_cospan_cone_to_composite_isequiv.
  change (left_cospan_cone_to_composite P1 o (map_to_cospan_cone C2 X))
  with (map_to_cospan_cone (left_cospan_cone_to_composite P1 C2) X).
  apply C3_UP.
Qed.

End Abstract_Two_Pullbacks_Lemma.

(*
Local Variables:
coq-prog-name: "hoqtop"
End:
*)
