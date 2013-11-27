(*******************************************************************************

Title: LongExactSequences.v
Authors: Jeremy Avigad, Chris Kapulkin, Peter LeFanu Lumsdaine
Date: 1 March 2013

Gives a construction analogous to the long exact sequence of a fibration in
classical homotopy theory.

*******************************************************************************)

(* Imports *)

Require Import HoTT EquivalenceVarieties.

Require Import Auxiliary Arith Fundamentals Pullbacks Pullbacks2 PointedTypes.

Open Scope path_scope.


(******************************************************************************

Some small lemmas, required for the theorems of this section but not quite
fitting anywhere else.

*******************************************************************************)

Section Varia.

Lemma sigma_of_contractibles_isequiv {X:Type} {Y:X->Type}
: (forall x:X, Contr (Y x)) -> IsEquiv (@projT1 X Y).
Proof.
  intros H. apply isequiv_fcontr. intros x.
  apply @contr_equiv' with (Y x).
  apply fiber_to_hfiber_equiv.
  apply H.
Defined.

Lemma hfiber_over_hprop {Y X : Type} (X_hprop : IsHProp X)
  (f : Y -> X) (x:X)
: IsEquiv (hfiber_incl f x).
Proof.
  apply sigma_of_contractibles_isequiv.
  intros y. apply X_hprop.
Defined.

End Varia.


(*******************************************************************************

General long sequences

*******************************************************************************)

Section Sequences.

Record long_sequence := {
  seq_obs :> nat -> pointed_type;
  seq_maps : forall n:nat, seq_obs (1+n) .-> seq_obs n;
  seq_null : forall n:nat, compose_ptd (seq_maps n) (seq_maps (1+n)) .== point }.

Definition lseq_is_exact (X : long_sequence)
  := forall n, is_exact (seq_maps X (1+n)) (seq_maps X n) (seq_null X n).

End Sequences.

(* Long sequences are often constructed inductively.  This is just a little
delicate, due to the dependency between the types of the components.

Here we give a typical example construction; this serves as a template for
[hfiber_sequence] and [loop_space_sequence] below.  This template could of
course be generalised to a precise theorem, but for the present applications,
that would be more trouble than it's worth. *)

Section Sequence_Template.  

Hypothesis A0 : pointed_type.
Hypothesis template_iterator_dom : forall A B (f : B .-> A), pointed_type.
Arguments template_iterator_dom [A B] f.
Hypothesis template_iterator_map : forall A B (f : B .-> A), (template_iterator_dom f) .-> B.
Arguments template_iterator_map [A B] f.

Definition template_aux (n:nat) : { A:pointed_type & {B : pointed_type & B .-> A}}.
Proof.
  induction n as [ | n' ABf].
  (* n=0 *) exists A0; exists A0; apply idmap_ptd.
  set (B := pr1 (pr2 ABf)).
  set (f := pr2 (pr2 ABf)).
  exists B. exists (template_iterator_dom f). exact (template_iterator_map f).
Defined.

Definition template_obs (n:nat) : pointed_type
  := pr1 (template_aux n).

Definition template_map (n:nat) : template_obs (1+n) .-> template_obs n.
Proof.
  unfold template_obs; simpl.
  exact (pr2 (pr2 (template_aux n))).
Defined.

End Sequence_Template.


(*******************************************************************************

The fiber sequence of a pointed map

We first construct the long exact sequence of a pointed map simply by iteratedly
taking its fiber.  Constructed this way, it is evidently exact.  We then show,
afterwards, that it is equivalent to a sequence of loop spaces.

(TODO: complete this last part.)

*******************************************************************************)

Section Hfiber_Sequence.

Definition hfiber_sequence_aux {A0 B0} (f0 : B0 .-> A0) (n:nat)
  : { A:pointed_type & {B : pointed_type & B .-> A}}.
Proof.
  induction n as [ | n' ABf].
  (* n=0 *) exists A0; exists B0; exact f0.
  (* n=1+n' *)
  set (B := pr1 (pr2 ABf)). set (f := pr2 (pr2 ABf)).
  exists B. exists (hfiber_ptd f). apply hfiber_incl_ptd.
Defined.

Definition hfiber_sequence {A B} (f : B .-> A) : long_sequence
:= {| seq_obs n := pr1 (hfiber_sequence_aux f n);
      seq_maps n := pr2 (pr2 (hfiber_sequence_aux f n));
      seq_null n := hfiber_null _ |}.

Lemma is_exact_hfiber_sequence {A B} (f : B .-> A)
  : lseq_is_exact (hfiber_sequence f).
Proof.
  intro; apply (is_exact_hfiber _).
Qed.

End Hfiber_Sequence.

(******************************************************************************
Long exact sequence.

                                     x
                                     |
                                     V
                                W -> X -> z
                                |    |    |
                                V    V    V
                                y -> Y -> Z
*******************************************************************************)

Lemma hfiber_to_Omega {X Y : pointed_type} (f:Y.->X)
: (hfiber_ptd (hfiber_incl_ptd f)) .-> Omega_ptd X.
Proof.
  apply @composeR_ptd with (pullback_ptd (hfiber_incl_ptd f) name_point).
    apply hfiber_to_pullback_ptd.
  apply @composeR_ptd with (pullback_ptd (pullback_ptd_pr1 f name_point) name_point).
    apply pullback_ptd_fmap.
    apply mk_ptd_cospan_map with (hfiber_to_pullback_ptd _) (idmap_ptd _) (idmap_ptd _). 
      apply hfiber_to_pullback_ptd_factn.
      apply (concat_ptd_htpy (compose_f1_ptd _)).
      apply inverse_ptd_htpy, compose_1f_ptd.
  apply @composeR_ptd with (pullback_ptd (pullback_ptd_pr2 name_point f) name_point).
    apply pullback_ptd_fmap.
    apply mk_ptd_cospan_map with (pullback_ptd_symm _ _) (idmap_ptd _) (idmap_ptd _). 
      apply (concat_ptd_htpy (pullback_ptd_symm_pr2 _ _)).
        apply inverse_ptd_htpy, compose_1f_ptd.
      apply (concat_ptd_htpy (compose_f1_ptd _)).
      apply inverse_ptd_htpy, compose_1f_ptd.
  apply @composeR_ptd with (pullback_ptd name_point (compose_ptd f name_point)).
    apply (@equiv_inverse_ptd _ _ (outer_to_double_pullback_ptd _ _ _)).
    apply two_pullbacks_isequiv.
  apply @composeR_ptd with (pullback_ptd (@name_point X) name_point).
    admit. (* pointed invariance of pullback under homotopy *)
  apply equiv_inverse_ptd with (Omega_to_pullback_ptd X).
    apply isequiv_Omega_to_pullback.
Defined.

Lemma isequiv_hfiber_to_Omega {X Y : pointed_type} (f:Y.->X)
: IsEquiv (hfiber_to_Omega f).
Proof.
  assert (isequiv_compose' : forall {A B C} (g:A.->B) (h:B.->C),
              IsEquiv g -> IsEquiv h -> IsEquiv (composeR_ptd g h)).
    intros; apply isequiv_compose.
(* Why define [isequiv_compose']?  It works slightly faster in the
following steps, since Coq doesn't need to unfold [compose_ptd] to unify
when using it; and the saving is significant since [hfiber_to_Omega f]
gets quite large as it unfolds. *)
  apply @isequiv_compose'.
    apply isequiv_hfiber_to_pullback.
  apply @isequiv_compose'.
    apply (pullback_fmap_isequiv _ name_point _ name_point).
      apply isequiv_hfiber_to_pullback.
      apply isequiv_idmap.
      apply isequiv_idmap.
  apply @isequiv_compose'.
    apply (pullback_fmap_isequiv _ name_point _ name_point).
      apply pullback_symm_isequiv.
      apply isequiv_idmap.
      apply isequiv_idmap.
  apply @isequiv_compose'.
    apply isequiv_inverse.
  apply @isequiv_compose'.
    admit.
  apply isequiv_inverse.
Qed.

(* TODO: remove after cannibalising. *)
Lemma long_exact_lemma_old
: forall {X Y : pointed_type} (f:Y.->X),
    (pt_type (hfiber_ptd (hfiber_incl_ptd f)))
    <~> Omega_ptd X.
Proof.
  intros. simpl.
  set (y := @point Y). set (x := @point X).
  equiv_via (pullback (name x) (name x)). Focus 2.
    apply equiv_inverse. apply Omega_to_pullback_equiv.
  equiv_via (pullback (hfiber_incl f x) (name y)).
    apply hfiber_to_pullback_equiv.
  equiv_via (pullback (name x) (f o name y)). Focus 2.
    assert (f o name y = name x) as name_path.
      apply path_forall. intros [ ]. apply pt_map_pt.
    rewrite name_path. apply equiv_idmap.
  equiv_via (pullback (f^* (name x)) (name y)). Focus 2.
    apply equiv_inverse. apply two_pullbacks_equiv.
  equiv_via (pullback
    (hfiber_incl f x o equiv_inv (hfiber_to_pullback_equiv f x)) (name y)).
    apply pullback_resp_equiv_A.
  assert ( hfiber_incl f x o (hfiber_to_pullback_equiv f x) ^-1
           = @pullback_pr1 _ _ _ f (name x)) as pr1_path.
    apply path_forall. intros [y' [[] p]]. unfold name in p. simpl.
    unfold compose. simpl. exact 1.
  rewrite pr1_path.
  assert ((@pullback_pr1 _ _ _ f (name x)
          o (pullback_symm_equiv f (name x)) ^-1)
          = f^* (name x)) as symm_path.
    apply path_forall. intros [[] [y' p]].
    unfold compose, pullback_pr2; simpl. exact 1.
  rewrite <- symm_path.
  apply pullback_resp_equiv_A.
Defined.

Lemma long_exact_sequence_aux1 {X Y} (f : Y .-> X) (n:nat)
  : hfiber_sequence f (n*3) .-> (iterate Omega_ptd n) X.
Proof.
  induction n as [ | n' IH]; simpl.  
  (* n=0 *) apply idmap_ptd.
  (* n=S n' *)
  apply @compose_ptd with (Y := Omega_ptd (hfiber_sequence f (n'*3))).
    apply Omega_ptd_fmap, IH.
  apply hfiber_to_Omega.
Defined.

Lemma long_exact_sequence_aux2 {X Y} (f : Y .-> X) (n:nat)
  : IsEquiv (long_exact_sequence_aux1 f n).
Proof.
  induction n as [ | n' IH].  
  (* n=0 *) simpl; apply isequiv_idmap.
  (* n=S n' *)
  apply @isequiv_compose with (B := Omega_ptd (hfiber_sequence f (n'*3))).
    apply isequiv_hfiber_to_Omega.
  apply isequiv_Omega_ptd_fmap, IH.
Qed.

(* TODO: also show how this interacts with the functoriality of Omega. *)

(*******************************************************************************
Application of the LES: equivalence of loop spaces, via truncatedness of fibers.

Goal of the section: if [X -> Y] has [n]-truncated fibers, then
[Omega ^n X <~> Omega ^n Y].
*******************************************************************************)

Corollary isequiv_loop_space_map_from_trunc_fiber
  {Y X} (f : Y .-> X)
  {n:nat} (Hn : forall x:X, IsTrunc n (hfiber f x))
: IsEquiv (Omega_ptd_fmap_iterate f n).
Proof.
Admitted.

(*******************************************************************************

An alternative construction of the [hiber_to_Omega] equivalence, this time by
hand instead of via pullbacks.  Though elementary, this is not quite as
straightforward as one might expect.

*******************************************************************************)

Lemma hfiber_to_Omega_by_hand {X Y : pointed_type} (f:Y.->X)
: (hfiber_ptd (hfiber_incl_ptd f)) .-> Omega_ptd X.
Proof.
  exists (fun y1_p_q =>
    match y1_p_q with ((y1;p);q) => ((pt_map_pt f)^ @ (ap f q)^ @ p) end).
  simpl. exact (whiskerR (concat_p1 _) _ @ concat_Vp _).
Defined.

Lemma isequiv_hfiber_to_Omega_by_hand {X Y : pointed_type} (f:Y.->X)
: IsEquiv (hfiber_to_Omega_by_hand f).
Proof.
  apply (isequiv_adjointify (fun p => ((point; pt_map_pt f @ p); 1))).
  (* section *) intro p; simpl.
    apply (concat (whiskerR (concat_p1 _) _)).
    apply concat_V_pp.
  (* retraction *) intros [[y1 p] q]. simpl in *.
    revert y1 q p.
    refine (@id_opp_elim Y point _ _).
    intro p; simpl.
    assert (pt_map_pt f @ (((pt_map_pt f) ^ @ 1) @ p) = p) as H.
      apply (concat (whiskerL _ (whiskerR (concat_p1 _) _))).
      apply concat_p_Vp.
    apply total_path'. simpl.
    set (pp := @total_path _ (fun y => f y = point) (point; pt_map_pt f @ (((pt_map_pt f) ^ @ 1) @ p)) (point;p) 1 H).
    exists pp.
    apply (concat (transport_compose (fun (y:Y) => y = point) (hfiber_incl f point) pp _)).
    apply (concat (transport_paths_l _ _)).
    apply (concat (concat_p1 _)).
    refine (@ap _ _ inverse _ 1 _).
    admit. (* Should use the non-existent [total_path_pr1]. *)
Defined.

(*
Local Variables:
coq-prog-name: "hoqtop"
End:
*)
