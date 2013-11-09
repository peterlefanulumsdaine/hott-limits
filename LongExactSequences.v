(*******************************************************************************

Title: LongExactSequences.v
Authors: Jeremy Avigad, Chris Kapulkin, Peter LeFanu Lumsdaine
Date: 1 March 2013

Gives a construction analogous to the long exact sequence of a fibration in
classical homotopy theory.

*******************************************************************************)

(* Imports *)

Require Import HoTT EquivalenceVarieties.

Require Import Auxiliary Fundamentals Pullbacks Pullbacks2 PointedTypes.


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

Pointed maps/short exact sequence.

A (short) homotopy fiber sequence may be given in several equivalent ways:

(a) a sequence F -> E -> B of maps of pointed types, together with an
equivalence (pointed and over E) between F and the (pointed) homotopy
fiber of E over the base;

(b) a map E -> B of pointed types [from F may be recovered as the
(pointed) homotopy fiber];

(c) a map E -> B of types, and a point of E [from which, for (c), the
point of B may be recovered as the image];

(d) a pointed type (B,b0), and a map P : B -> Type, with a point of P
b0 [from which, for (c), E may be recovered as the total space];

…more?

TODO (mid): consider which of these definitions will give the clearest
versions of theorems and proofs. (c) seems most parsimonious; (b)
gives perhaps the clearest categorical picture; (d) perhaps reduces
how much use of homotopy fibers is required?

*******************************************************************************)

(* TODO (mid), perhaps: equivalence of the various definitions [or... well,
the full equivalence of all would require univalence... how much, if
anything, should we do?]. *)

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

(* TODO (high): make this a pointed equivalence!  Possibly also rewrite this
to make the underlying map explicit. *)
Theorem long_exact_thm
: forall {X Y : pointed_type} (f:Y.->X),
    (pt_type (hfiber_ptd (hfiber_incl_ptd f)))
    <~> Omega_ptd X.
Proof.
  intros. simpl.
  set (y := point Y). set (x := point X).
  equiv_via (pullback (name x) (name x)). Focus 2.
    apply equiv_inverse. apply loop_is_pullback.
  equiv_via (pullback (hfiber_incl f x) (name y)).
    apply hfiber_as_pullback_equiv.
  equiv_via (pullback (name x) (f o name y)). Focus 2.
    assert (f o name y = name x) as name_path.
      apply path_forall. intros [ ]. apply pt_map_pt.
    rewrite name_path. apply equiv_idmap.
  equiv_via (pullback (f^* (name x)) (name y)). Focus 2.
    apply equiv_inverse. apply two_pullbacks_equiv.
  equiv_via (pullback
    (hfiber_incl f x o equiv_inv (hfiber_as_pullback_equiv f x)) (name y)).
    apply pullback_resp_equiv_A.
  assert ( hfiber_incl f x o (hfiber_as_pullback_equiv f x) ^-1
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

(* We also need to know how this interacts with the functoriality of Omega. *)
Lemma long_exact_seq_naturality {X Y : pointed_type} (f:Y .-> X)
: Omega_ptd_fmap f
  == (long_exact_thm f)
     o pt_map _ _ (hfiber_incl_ptd (hfiber_incl_ptd (hfiber_incl_ptd f)))
     o ((long_exact_thm (hfiber_incl_ptd f)) ^-1).
Proof.
(*
  intros p. unfold long_exact_thm. simpl.
  unfold equiv_inv at 1, loop_is_pullback. simpl.
  unfold compose. simpl.
  unfold equiv_compose.
*)
Admitted.

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

(*
Local Variables:
coq-prog-name: "hoqtop"
End:
*)
