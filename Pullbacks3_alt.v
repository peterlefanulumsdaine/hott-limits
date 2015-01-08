(*******************************************************************************

Title: Pullbacks3.v
Authors: Jeremy Avigad, Chris Kapulkin, Peter LeFanu Lumsdaine
Date: 1 March 2013

Alternative approaches to the (abstract) two pullbacks lemma, as discussed
in the paper.

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

Below we give three approaches.

A naming convention we mostly adhere to: cones over the right-hand 
square (f,g) are named [C1], [C1'], etc; cones over the left-hand square
(or similar squares) are [C2], [C2'], etc; and cones over the whole
rectangle as [C3], etc. 

*******************************************************************************)

Section Abstract_Two_Pullbacks_Lemma.

Context {A B1 B2 C : Type} (f : A -> C) (g : B1 -> C) (h : B2 -> B1).

Lemma left_cospan_cone_to_composite {P1 : Type} (C1 : cospan_cone f g P1)
  {X : Type} (C2 : cospan_cone (cospan_cone_map2 C1) h X)
: cospan_cone f (g o h) X.
Proof.
  exists (cospan_cone_map1 C1 o cospan_cone_map1 C2).
  exists (cospan_cone_map2 C2).
  intros x.
  apply (concat (cospan_cone_comm C1 (cospan_cone_map1 C2 x))).
  apply (ap g (cospan_cone_comm C2 x)).
Defined.

(*******************************************************************************

Approach 1: via showing that spaces of cones are equivalent. Both
directions given.

In this approach, we consider just the outer cospan and the right
square as given:

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

and then show that the right-hand vertical map is a weak equivalence.

It then follows, by 2-of-3, that either of the diagonal maps is an
equivalence if the other one is; i.e. that the two universal
properties are equivalent.

*******************************************************************************)

Section Approach1.

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

End Approach1.

(*******************************************************************************

Approach 2: in this approach, we only show one direction: that if the
left-hand square is a pullback, then so is the outer rectangle.

We produce the equivalence required by the universal property as a
composite of known equivalences; we then show that the underlying ap
of the resulting equivalence is indeed [map_to_cospan_cone] as
required.

*******************************************************************************)

Section Approach2.

Definition cospan_cone_map_to_pullback_equiv {A B C : Type}
  (f : A -> C) (g : B -> C) (X : Type)
  := equiv_inverse (BuildEquiv (pullback_universal f g X))
: (cospan_cone f g X) <~> (X -> pullback f g).

Lemma left_cospan_cone_to_composite_UP_equiv
  (P1 : abstract_pullback f g)
  (P2 : abstract_pullback (cospan_cone_map2 P1) h) (X : UU)
: (X -> P2) <~> (cospan_cone f (g o h) X).
Proof.
  set (e1 := abstract_pullback_unique P1 (standard_pullback f g)).
  set (e2 := BuildEquiv (pullback_cone_UP P2 X)).

  apply (equiv_composeR' e2).
  apply (equiv_composeR' (cospan_cone_map_to_pullback_equiv _ _ _)).
  apply equiv_inverse.
  apply (equiv_composeR' (cospan_cone_map_to_pullback_equiv _ _ _)).
  apply equiv_postcompose'.
  apply (equiv_composeR' (two_pullbacks_equiv f g h)).
  (* If [pullback_universal] were transparent, the following would be
  a definitional equality: *)
  assert (H : cospan_cone_map2 P1 = (g ^* f) o (equiv_inverse e1) ^-1).
    change ((equiv_inverse e1) ^-1) with (fun x => e1 x).
    unfold e1, abstract_pullback_unique. simpl.
    unfold abstract_pullback_equiv_cospan_cone_1, equiv_composeR'. simpl.
    rewrite pullback_universal_unlock.
    exact 1.
  rewrite H. apply (pullback_resp_equiv_A _ _ (equiv_inverse e1)).
Defined.

(* Try a more direct version. *)
Lemma left_cospan_cone_to_composite_UP_equiv2
  (P1 : abstract_pullback f g)
  (P2 : abstract_pullback (cospan_cone_map2 P1) h) (X : UU)
: (X -> P2) <~> (cospan_cone f (g o h) X).
Proof.
  set (e1 := abstract_pullback_unique P1 (standard_pullback f g)).
  set (e2 := BuildEquiv (pullback_cone_UP P2 X)).

  apply (equiv_composeR' e2).
  apply (equiv_composeR' (cospan_cone_map_to_pullback_equiv _ _ _)).
  equiv_via (X -> pullback (g ^* f) h).
    apply equiv_inverse. apply equiv_postcompose'.
    assert (H : cospan_cone_map2 P1 = (g ^* f) o (equiv_inverse e1) ^-1).
      change ((equiv_inverse e1) ^-1) with (fun x => e1 x).
      unfold e1, abstract_pullback_unique,
        abstract_pullback_equiv_cospan_cone_1, equiv_composeR'. simpl.
      rewrite pullback_universal_unlock.
      exact 1.
    rewrite H.
    apply (pullback_resp_equiv_A (g ^* f) h (equiv_inverse e1)).
  equiv_via (X -> pullback f (g o h)).
  apply equiv_postcompose'. exact (equiv_inverse (two_pullbacks_equiv f g h)).
  apply (equiv_inverse (cospan_cone_map_to_pullback_equiv _ _ _)).
Defined.

Lemma left_cospan_cone_to_composite_UP_equiv_path
  (P1 : abstract_pullback f g)
  (P2 : abstract_pullback (cospan_cone_map2 P1) h) (X : UU)
: equiv_fun (left_cospan_cone_to_composite_UP_equiv2 P1 P2 X)
  ==
   map_to_cospan_cone (left_cospan_cone_to_composite P1 P2) X.
Proof.
(*
  intros alpha.
  unfold left_cospan_cone_to_composite_UP_equiv2, left_cospan_cone_to_composite,
    map_to_cospan_cone.
  simpl. simpl.
  unfold pullback_pr2, pullback_pr1. simpl.
  unfold cospan_cone_map_to_pullback_equiv. simpl.
  unfold equiv_postcompose'. simpl.
  unfold equiv_inv. simpl.
  unfold cospan_cone_map2, cospan_cone_map1,cospan_cone_comm. simpl.
  unfold cospan_cone_map2, cospan_cone_map1,cospan_cone_comm. simpl.
  idmap. simpl.
  set (pg := pr1 P1). set (pf := pr1 (pr2 P1)).
    set (phi := pr2 (pr2 P1)).
  set (ph := pr1 P2). set (ppf := pr1 (pr2 P2)).
    set (psi := pr2 (pr2 P2)).
  unfold projT1, projT2. simpl.
  unfold map_to_cospan_cone. simpl.
  unfold cospan_cone_map2, cospan_cone_comm. simpl.
  assert (id_elim_lemma :
    forall (x:X) (b:B1) (q : b = h (ppf (alpha x)))
      (p : f (pg (ph (alpha x))) = g b),
    @id_opp_elim B1 (h (ppf (alpha x)))
      (fun (b : B1) (_ : b = h (ppf (alpha x))) =>
         f (pg (ph (alpha x))) = g b ->
         @pullback A B2 C f (fun x0 : B2 => g (h x0)))
      (fun p : f (pg (ph (alpha x))) = g (h (ppf (alpha x))) =>
         @mk_pullback A B2 C f (fun x0 : B2 => g (h x0))
           (pg (ph (alpha x))) (ppf (alpha x)) p)
      b q p
   =
      @mk_pullback A B2 C f (g o h)
        (pg (ph (alpha x)))
        (ppf (alpha x))
        (p @ ap g q)).
  assert (id_elim_lemma' :
    forall (x:X) (b:B1) (q : h (ppf (alpha x)) = b)
      (p : f (pg (ph (alpha x))) = g b),
    @id_opp_elim B1 (h (ppf (alpha x)))
      (fun (b : B1) (_ : b = h (ppf (alpha x))) =>
         f (pg (ph (alpha x))) = g b ->
         @pullback A B2 C f (fun x0 : B2 => g (h x0)))
      (fun p : f (pg (ph (alpha x))) = g (h (ppf (alpha x))) =>
         @mk_pullback A B2 C f (fun x0 : B2 => g (h x0))
           (pg (ph (alpha x))) (ppf (alpha x)) p)
      b (q^) p
   =
      @mk_pullback A B2 C f (g o h)
        (pg (ph (alpha x)))
        (ppf (alpha x))
        (p @ ap g (q^))).
    intros x b q p. destruct q. simpl.
    unfold id_opp_elim. simpl.
    apply ap.
    apply inverse. apply concat_p1.
    (* id_elim_lemma' proven *)
    intros x b q. rewrite <- (inv_V _ _ _ q).
    apply id_elim_lemma'.
    (* id_elim_lemma proven *)
  path_via
    (map_to_pullback_to_cospan_cone f (fun x : B2 => g (h x)) X
    (fun x:X => mk_pullback f (g o h)
      (pg (ph (alpha x)))
      (ppf (alpha x))
      (phi (ph (alpha x)) @ ap g (psi (alpha x))))).
  apply ap. apply path_forall. intros x.
  path_via (@id_opp_elim B1 (h (ppf (alpha x)))
     (fun (b : B1) (_ : b = h (ppf (alpha x))) =>
      f (pg (ph (alpha x))) = g b ->
      pullback f (g o h))
     (fun p : f (pg (ph (alpha x))) = g (h (ppf (alpha x))) =>
      mk_pullback f (g o h)
        (pg (ph (alpha x))) (ppf (alpha x)) p) (pf (ph (alpha x)))
     (psi (alpha x))
     (phi (ph (alpha x)))).
  apply (ap (fun q => @id_opp_elim B1 (h (ppf (alpha x)))
     (fun (b : B1) (_ : b = h (ppf (alpha x))) =>
      f (pg (ph (alpha x))) = g b ->
      pullback f (g o h))
     (fun p : f (pg (ph (alpha x))) = g (h (ppf (alpha x))) =>
      mk_pullback f (g o h)
        (pg (ph (alpha x))) (ppf (alpha x)) p) (pf (ph (alpha x)))
     q
     (phi (ph (alpha x))))).
  path_via (ap (fun x0 : B1 => x0) (psi (alpha x))).
  apply ap_idmap. *)
Admitted.
(* This succeeds during proof-building, but fails to pass the [Defined.]
*)

Lemma left_cospan_cone_to_composite_UP_first_version
  (P1 : abstract_pullback f g) (P2 : abstract_pullback (cospan_cone_map2 P1) h)
  : is_pullback_cone (left_cospan_cone_to_composite P1 P2).
Proof.
  intros X.
Admitted.

End Approach2.


(*******************************************************************************

Approach 3: one direction only: if the left square is a pullback, then
so is the whole rectangle.

A completely direct construction of the equivalence required by the
universal property.

*******************************************************************************)

Section Approach3.

Lemma left_cospan_cone_to_composite_UP_inverse
  (P1 : abstract_pullback f g)
  (P2 : abstract_pullback (cospan_cone_map2 P1) h) (X : UU)
: cospan_cone f (g o h) X -> (X -> P2).
Proof.
  intros C3.
  set (C1_UP_at_X := BuildEquiv (pullback_cone_UP P1 X)).
  set (C2_UP_at_X := BuildEquiv (pullback_cone_UP P2 X)).
  set (cone_to_f_g := (@mk_cospan_cone _ _ _ f g X _ _ (cospan_cone_comm C3))).
  (* For the eventual ap, use the universal property of the left-hand square. *)
  apply (C2_UP_at_X ^-1).
  (* For the first leg of this cone, use the universal property of the
     right-hand square. *)
  exists (C1_UP_at_X ^-1 cone_to_f_g).
  exists (cospan_cone_map2 C3).
  intros x.
  change (h (cospan_cone_map2 C3 x)) with (cospan_cone_map2 cone_to_f_g x).
  change (cospan_cone_map2 P1 ((C1_UP_at_X ^-1) cone_to_f_g x))
    with (cospan_cone_map2 (C1_UP_at_X
           (C1_UP_at_X ^-1 cone_to_f_g)) x).
  apply ap10. apply packed_cospan_cone_map2.
Defined.

Lemma left_cospan_cone_to_composite_aux1
  (P1 : abstract_pullback f g) (P2 : abstract_pullback (cospan_cone_map2 P1) h)
  (X : Type)  (C4 : cospan_cone f (g o h) X)
: cospan_cone_map1 (map_to_cospan_cone (left_cospan_cone_to_composite P1 P2) X
    (left_cospan_cone_to_composite_UP_inverse P1 P2 X C4))
  = cospan_cone_map1 C4.
Proof.
  set (C1_UP_at_X := BuildEquiv (pullback_cone_UP P1 X)).
  set (C2_UP_at_X := BuildEquiv (pullback_cone_UP P2 X)).

  change (cospan_cone_map1 (map_to_cospan_cone (left_cospan_cone_to_composite P1 P2) X
     (left_cospan_cone_to_composite_UP_inverse P1 P2 X C4)))
  with (cospan_cone_map1 P1 o (cospan_cone_map1 P2
    o left_cospan_cone_to_composite_UP_inverse P1 P2 X C4)).

  change (cospan_cone_map1 P1 o
    (cospan_cone_map1 P2 o left_cospan_cone_to_composite_UP_inverse P1 P2 X C4))
    with ((cospan_cone_map1 o C1_UP_at_X)
    (cospan_cone_map1 P2 o left_cospan_cone_to_composite_UP_inverse P1 P2 X C4)).
  change (cospan_cone_map1 P2 o
       (left_cospan_cone_to_composite_UP_inverse P1 P2 X C4))
    with ((cospan_cone_map1 o C2_UP_at_X)
       (left_cospan_cone_to_composite_UP_inverse P1 P2 X C4)).

  unfold left_cospan_cone_to_composite_UP_inverse. fold C2_UP_at_X C1_UP_at_X.

  path_via
    ((cospan_cone_map1 o C1_UP_at_X) ((C1_UP_at_X ^-1)
     (@mk_cospan_cone _ _ _ f g _ _ _ (cospan_cone_comm C4)))).
    apply (ap (cospan_cone_map1 o C1_UP_at_X)). 
    apply (packed_cospan_cone_map1 P2).
  apply (packed_cospan_cone_map1 P1).
Defined.

Lemma left_cospan_cone_to_composite_aux2
  (P1 : abstract_pullback f g) (P2 : abstract_pullback (cospan_cone_map2 P1) h)
  (X : UU)  (C4 : cospan_cone f (g o h) X)
:  cospan_cone_map2 (map_to_cospan_cone (left_cospan_cone_to_composite P1 P2) X
     (left_cospan_cone_to_composite_UP_inverse P1 P2 X C4)) =
   cospan_cone_map2 C4.
Proof.
  set (C1_UP_at_X := BuildEquiv (pullback_cone_UP P1 X)).
  set (C2_UP_at_X := BuildEquiv (pullback_cone_UP P2 X)).
  unfold left_cospan_cone_to_composite. 

  unfold cospan_cone_map2 at 1; simpl.
  unfold cospan_cone_map2 at 1; simpl.

  change (cospan_cone_map2 P2 o
    left_cospan_cone_to_composite_UP_inverse P1 P2 X C4)
    with ((cospan_cone_map2 o C2_UP_at_X)
      (left_cospan_cone_to_composite_UP_inverse P1 P2 X C4)).
  unfold left_cospan_cone_to_composite_UP_inverse. fold C1_UP_at_X C2_UP_at_X.
  apply (packed_cospan_cone_map2 P2).
Defined.

Lemma map_to_cospan_cone__left_cospan_cone_to_composite
  (P1 : abstract_pullback f g)
  {P2 : Type} (C2 : cospan_cone (cospan_cone_map2 P1) h P2)
  {X : Type} (m : X -> P2)
: @mk_cospan_cone _ _ _ f g _ _ _
    (cospan_cone_comm (map_to_cospan_cone (left_cospan_cone_to_composite P1 C2) X m))
  = map_to_cospan_cone P1 X (cospan_cone_map1 (map_to_cospan_cone C2 X m)).
Proof.
  change (@mk_cospan_cone _ _ _ f g _ _ _
    (cospan_cone_comm (map_to_cospan_cone (left_cospan_cone_to_composite P1 C2) X m)))
  with (@mk_cospan_cone _ _ _ f g _ _ _
    (fun x => cospan_cone_comm (left_cospan_cone_to_composite P1 C2) (m x))).
  change (map_to_cospan_cone P1 X
      (cospan_cone_map1 (map_to_cospan_cone C2 X m)))
  with (map_to_cospan_cone P1 X ((cospan_cone_map1 C2) o m)).
  apply cospan_cone_path'.
  unfold cospan_cone_map1, cospan_cone_map2. simpl.
  exists 1. exists (path_forall (fun x => (cospan_cone_comm C2 (m x))^)).
  intros x. unfold cospan_cone_comm. simpl.
  fold (cospan_cone_comm C2). apply concat2.
    apply inverse, concat_1p.
  path_via'
    (ap g (ap10 (path_forall (fun x0 => (cospan_cone_comm C2 (m x0))^)) x)^).
    Focus 2. apply ap_V.
  apply ap.
  path_via' (ap10 (path_forall (fun x0 => (cospan_cone_comm C2 (m x0))^))^ x).
    Focus 2.
    apply (apD10_V (path_forall (fun x0 => (cospan_cone_comm C2 (m x0))^))).
  path_via' (ap10 (path_forall (fun x0 => (cospan_cone_comm C2 (m x0))^^)) x).
    path_via' ((cospan_cone_comm C2 (m x))^^).
      apply inverse, inv_V.
    apply inverse.
    revert x. apply apD10. apply eisretr.
  apply (ap
    (fun p : (fun x0 => cospan_cone_map2 P1 (cospan_cone_map1 C2 (m x0)))
             = (fun x0 => h (cospan_cone_map2 C2 (m x0)))
           => ap10 p x)).
  apply path_forall_V.
Defined.

Lemma UP_inverse_left_cospan_cone_to_composite
  (P1 : abstract_pullback f g)
  {P2 : Type} (C2 : cospan_cone (cospan_cone_map2 P1) h P2)
  {X : UU} (m : X -> P2)
: ((BuildEquiv (pullback_cone_UP P1 X)) ^-1)
      (@mk_cospan_cone _ _ _ f g _ _ _
         (cospan_cone_comm (map_to_cospan_cone
           (left_cospan_cone_to_composite P1 C2) X m))) =
      cospan_cone_map1 C2 o m.
Proof.
  apply moveR_equiv_M. simpl.
  apply map_to_cospan_cone__left_cospan_cone_to_composite.
Defined.


Lemma left_cospan_cone_to_composite_UP_inverse_is_section
  (P1 : abstract_pullback f g) (P2 : abstract_pullback (cospan_cone_map2 P1) h)
  (X : Type)
: (map_to_cospan_cone (left_cospan_cone_to_composite P1 P2) X)
    o (left_cospan_cone_to_composite_UP_inverse P1 P2 X)
  == idmap.
Proof.
  set (C1_UP_at_X := BuildEquiv (pullback_cone_UP P1 X)).
  set (C2_UP_at_X := BuildEquiv (pullback_cone_UP P2 X)).

  intros C4.
  apply (cospan_cone_path (left_cospan_cone_to_composite_aux1 _ _ _ _)
    (left_cospan_cone_to_composite_aux2 _ _ _ _)).
  intros x.
  unfold cospan_cone_comm. unfold left_cospan_cone_to_composite. simpl.
  unfold cospan_cone_comm. simpl.
  fold (cospan_cone_comm C4) (cospan_cone_comm P1) (cospan_cone_comm P2).
  rewrite concat_pp_p.
  apply moveL_Mp. apply moveL_pM.
  rewrite inv_V.

  set (C1' := @mk_cospan_cone _ _ _ f g _ _ _ (cospan_cone_comm C4)).
  set (C2' :=
    @mk_cospan_cone _ _ _ _ _ _
      (C1_UP_at_X ^-1 C1')
      (cospan_cone_map2 C4)
      (ap10 (packed_cospan_cone_map2 P1 C1'))).
  (* Why don’t the instances of C2' in the goal get recognised and fold!?
  We can at least refer to C2', though, so it is still useful. *)

  (* At this point, a diagram is very helpful. Below, we name various paths;
  these named paths will be the arrows of the diagram, and commutativity of
  the diagram is equivalent to our current goal.

  So: draw a regular hexagon, with [p0] (the RHS of the goal) along the base;
  edges [p1]…[p5] (oriented appropriately) going clockwise around the
  perimeter (their composite [p1^ @ p2^ @ p3 @ p4 @ p5] is the LHS of the goal);
  edges [q1], [q2], [q2'], [q3],  going from various vertices in to the
  centre (which vertices can be inferred from the six key facts below);
  and extra edges [p2'], [p5'], parallel to [p2] and [p5] respectively.

  Overall commutativity then follows from the five key facts [p2 = p2'],
  [p5 = p5'], [p1^ @ q3 @ q1 = p0], [q2^ @ p4 @ p5' = q1], and
  [p2'^ @ p3 = q3 @ q2^].

  So: from here, we first name all the paths; then show the five key facts;
  and then go through the algebra of paths, putting all the pieces together.
  *)
  set (p0 := cospan_cone_comm C4 x).
  set (p1 := ap f (ap10 (packed_cospan_cone_map1 P1 C1') x)).
  set (p2 := ap f (ap10 (ap (fun g => compose (cospan_cone_map1 P1) g)
         (packed_cospan_cone_map1 P2 C2')) x)).
  set (p3 := cospan_cone_comm P1 (cospan_cone_map1 P2 (C2_UP_at_X ^-1 C2' x))).
  set (p4 := ap g (cospan_cone_comm P2 (C2_UP_at_X ^-1 C2' x))).
  set (p5 := ap (g o h)
    (ap10 (packed_cospan_cone_map2 P2 C2') x)).

  set (p2' := ap (f o (cospan_cone_map1 P1))
        (ap10 (packed_cospan_cone_map1 P2 C2') x)).
  set (p5' := ap g (ap h (ap10 (packed_cospan_cone_map2 P2 C2') x))).

  set (q1 := ap g (ap10 (packed_cospan_cone_map2 P1 C1') x)).
  set (q2 := ap g (ap (cospan_cone_map2 P1)
        (ap10 (packed_cospan_cone_map1 P2 C2') x))).
  set (q3 := cospan_cone_comm P1 (C1_UP_at_X ^-1 C1' x)).

  assert (p2 = p2') as H1.
    unfold p2, p2'.
    path_via' (ap f (ap (cospan_cone_map1 P1)
      (ap10 (packed_cospan_cone_map1 P2 C2') x))).
      apply ap.
      exact (ap10_ap_postcompose (cospan_cone_map1 P1)
        (packed_cospan_cone_map1 P2 C2') x).
    apply inverse, ap_compose.
  assert (p5 = p5') as H2.
    apply ap_compose.
  assert (p1^ @ q3 @ q1 = p0) as H3.
    apply moveR_pM, moveR_Vp.  apply (concatR concat_pp_p).
    apply packed_cospan_cone_comm.
  assert (q2^ @ p4 @ p5' = q1) as H4.
    apply moveR_pM, moveR_Vp.  apply (concatR concat_pp_p).
    path_via' (ap g
      ((ap (cospan_cone_map2 P1) (ap10 (packed_cospan_cone_map1 P2 C2') x))
      @ (ap10 (packed_cospan_cone_map2 P1 C1') x)
      @ (ap h (ap10 (packed_cospan_cone_map2 P2 C2') x))^)).
      apply ap, (packed_cospan_cone_comm P2 C2').
    path_via' (ap g
      ((ap (cospan_cone_map2 P1) (ap10 (packed_cospan_cone_map1 P2 C2') x) @
         ap10 (packed_cospan_cone_map2 P1 C1') x))
      @ ap g (ap h (ap10 (packed_cospan_cone_map2 P2 C2') x))^).
      apply ap_pp.
    apply concat2. apply ap_pp. apply ap_V.
  assert (p2'^ @ p3 = q3 @ q2^) as H5.       (* naturality *)
    apply (cancelL p2').
    rewrite <- concat_pp_p.
    rewrite concat_pV.
    rewrite concat_1p.
    apply (fun p p' => cancelR p p' q2).
    rewrite !concat_pp_p.
    rewrite concat_Vp.
    rewrite concat_p1.
    apply inverse.
    unfold p3, q2, p2', q3.
    rewrite <- ap_compose.
    exact (@concat_Ap  _ _ (f o cospan_cone_map1 P1)
      (g o cospan_cone_map2 P1) (cospan_cone_comm P1) _ _ _).

  (* Put it all together. First, pull the original goal into a composite
  of our basic paths. *)
  path_via' (p1^ @ p2^ @ p3 @ p4 @ p5).
    apply whiskerR.
    path_via' ((p1^ @ p2^) @ (p3 @ p4)).
      Focus 2. apply inverse, concat_pp_p.
    apply whiskerR.
    path_via' ((ap f (ap10 (ap (cospan_cone_map1 o C1_UP_at_X)
                              (packed_cospan_cone_map1 P2 C2')) x)
            @ (ap f (ap10 (packed_cospan_cone_map1 P1 C1') x)))^).
      Focus 2. apply inv_pp.
    apply ap.
    path_via' (ap f
        ((ap10 (ap (cospan_cone_map1 o C1_UP_at_X)
           (packed_cospan_cone_map1 P2 C2')) x)
      @ (ap10 (packed_cospan_cone_map1 P1 C1') x))).
      apply ap.
      refine (ap10_pp _ (packed_cospan_cone_map1 P1 C1') x).
    apply ap_pp.
  (* Next, reassociate to make H5 applicable. *)
  path_via' (p1^ @ ((p2^ @ p3) @ (p4 @ p5))).
    path_via' (p1^ @ (p2^ @ p3) @ p4 @ p5).
      apply whiskerR, whiskerR, concat_pp_p.
    path_via' (p1^ @ (p2^ @ p3) @ (p4 @ p5)).
      apply concat_pp_p.
    apply concat_pp_p.
  path_via' (p1^ @ ((q3 @ q2^) @ (p4 @ p5))).
    apply whiskerL, whiskerR.
    path_via' (p2'^ @ p3).
      apply whiskerR, ap, H1.
      apply H5.
  path_via' (p1^ @ q3 @ (q2^ @ p4 @ p5)).
    path_via' (p1^ @ (q3 @ (q2^ @ (p4 @ p5)))).
      apply ap, concat_pp_p.
    path_via' (p1^ @ q3 @ (q2^ @ (p4 @ p5))).
      apply (concat_pp_p^).
    apply ap, (concat_pp_p^).
  path_via' (p1^ @ q3 @ q1).
    Focus 2. apply H3.
  apply ap. path_via' ((q2^ @ p4) @ p5').
    apply ap, H2.
  apply H4.
Qed.

Lemma left_cospan_cone_to_composite_UP_inverse_is_retraction
  (P1 : abstract_pullback f g) (P2 : abstract_pullback (cospan_cone_map2 P1) h)
  (X : Type)
: (left_cospan_cone_to_composite_UP_inverse P1 P2 X)
    o (map_to_cospan_cone (left_cospan_cone_to_composite P1 P2) X)
  == idmap.

Proof.
  set (C1_UP_at_X := BuildEquiv (pullback_cone_UP P1 X)).
  set (C2_UP_at_X := BuildEquiv (pullback_cone_UP P2 X)).
  intros m4. (* corresponds to C4 in previous direction *)
  unfold left_cospan_cone_to_composite_UP_inverse.
  fold C1_UP_at_X. fold C2_UP_at_X.   simpl.
    apply moveR_I.  simpl.
  apply cospan_cone_path'. simpl.
    exists (UP_inverse_left_cospan_cone_to_composite P1 P2 m4).
    exists 1.
  intros x. apply (concatR (concat_p1 _)^).
  unfold cospan_cone_comm, UP_inverse_left_cospan_cone_to_composite. simpl.
  fold C1_UP_at_X.
  eapply concatR.
    eapply whiskerR.
    refine (ap10_ap_postcompose _ _ x).
  unfold packed_cospan_cone_map2. fold C1_UP_at_X.
  change (fun f' : X -> P1 => cospan_cone_map2 P1 o f')
  with (cospan_cone_map2 o (map_to_cospan_cone P1 X)).
  unfold moveR_equiv_M. rewrite ap_pp. rewrite ap10_pp.
  rewrite (ap_compose (map_to_cospan_cone P1 X) cospan_cone_map2).
  change (map_to_cospan_cone P1 X) with (fun x => C1_UP_at_X x).
  rewrite (ap_inverse_o_equiv C1_UP_at_X).
  rewrite !ap_pp. rewrite !ap10_pp.
  rewrite !concat_pp_p.
  set (p := ap10
     (ap cospan_cone_map2
        (eisretr C1_UP_at_X
           (@mk_cospan_cone _ _ _ f g _ _ _
              (fun z : X => cospan_cone_comm (left_cospan_cone_to_composite P1 P2)
                  (m4 z))))) x).
  path_via' (p @ 1). apply inverse, concat_p1.
  apply whiskerL.
  unfold map_to_cospan_cone__left_cospan_cone_to_composite.
  rewrite cospan_cone_path'_map2. simpl.
  assert (H : ap10 (path_forall (fun x0 => (cospan_cone_comm P2 (m4 x0))^)) x
              = (cospan_cone_comm P2 (m4 x))^).
    clear p. revert x. apply apD10. apply eisretr.
  apply (concatR (whiskerR H^ _)).
  apply moveL_Mp.
  rewrite concat_p1.
  rewrite <- concat_pp_p.
  apply moveL_pM.
  rewrite concat_Vp.
  rewrite (ap_compose (map_to_cospan_cone P1 X) cospan_cone_map2).
  rewrite <- (@ap10_pp X B1 _ _
     (cospan_cone_map2 (map_to_cospan_cone P1 X
         (cospan_cone_map1 P2 o m4))) _ _).
  rewrite <- ap_pp.
  change (map_to_cospan_cone P1 X) with (equiv_fun C1_UP_at_X).
  rewrite eisadj.
  rewrite concat_Vp.
  exact 1.
Qed.

Lemma left_cospan_cone_to_composite_UP
  (P1 : abstract_pullback f g) (P2 : abstract_pullback (cospan_cone_map2 P1) h)
: is_pullback_cone (left_cospan_cone_to_composite P1 P2).
Proof.
  intros X.
  apply (isequiv_adjointify
    (left_cospan_cone_to_composite_UP_inverse P1 P2 X)).
  apply left_cospan_cone_to_composite_UP_inverse_is_section.
  apply left_cospan_cone_to_composite_UP_inverse_is_retraction.
Qed.

End Approach3.

End Abstract_Two_Pullbacks_Lemma.

(*
Local Variables:
coq-prog-name: "hoqtop"
End:
*)

