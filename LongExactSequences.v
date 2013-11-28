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

(*******************************************************************************

General long sequences

*******************************************************************************)

Section Long_Sequences.

Record long_sequence := {
  lseq_obs :> nat -> pointed_type;
  lseq_maps : forall n:nat, lseq_obs (1+n) .-> lseq_obs n;
  lseq_null : forall n:nat, compose_ptd (lseq_maps n) (lseq_maps (1+n)) .== point }.

Definition lseq_is_exact (X : long_sequence)
  := forall n, is_exact (lseq_maps X (1+n)) (lseq_maps X n) (lseq_null X n).

End Long_Sequences.

(* Long sequences are often constructed inductively.  This is just a little
delicate, due to the dependency between the types of the components.

Here we give a typical example construction; this serves as a template for
[hfiber_sequence] and [loop_space_sequence] below.  This template could of
course be generalised to a precise theorem, but for the present applications,
that would be more trouble than it's worth. *)

Section Long_Sequence_Template.  

Hypothesis A0 : pointed_type.
Hypothesis template_iterator_dom : forall A B (f : B .-> A),
  pointed_type.
Arguments template_iterator_dom [A B] f.
Hypothesis template_iterator_map : forall A B (f : B .-> A),
  (template_iterator_dom f) .-> B.
Arguments template_iterator_map [A B] f.
Hypothesis template_iterator_null : forall A B (f : B .-> A),
  compose_ptd f (template_iterator_map f) .== point.
Arguments template_iterator_null [A B] f.

Definition lseq_template_aux (n:nat) : { A:pointed_type & {B : pointed_type & B .-> A}}.
Proof.
  induction n as [ | n' ABf].
  (* n=0 *) exists A0; exists A0; apply idmap_ptd.
  set (B := pr1 (pr2 ABf)).
  set (f := pr2 (pr2 ABf)).
  exists B. exists (template_iterator_dom f). exact (template_iterator_map f).
Defined.

Definition lseq_template (n:nat) : long_sequence
  := {| lseq_obs n := pr1 (lseq_template_aux n);
        lseq_maps n := pr2 (pr2 (lseq_template_aux n));
        lseq_null n := template_iterator_null
                        (pr2 (pr2 (lseq_template_aux n))) |}.

End Long_Sequence_Template.


(*******************************************************************************

The fiber sequence of a pointed map.

We first construct the long exact sequence of a pointed map simply by iteratedly
taking its fiber.  Constructed this way, it is evidently exact.  We then show,
in [Omega_to_hfiber_seq_0] et seq., that it is equivalent to a sequence of loop
spaces.

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

Arguments hfiber_sequence_aux [A B] f n : rename, simpl nomatch.

Definition hfiber_sequence {A B} (f : B .-> A) : long_sequence
:= {| lseq_obs n := pr1 (hfiber_sequence_aux f n);
      lseq_maps n := pr2 (pr2 (hfiber_sequence_aux f n));
      lseq_null n := hfiber_null _ |}.

Lemma is_exact_hfiber_sequence {A B} (f : B .-> A)
  : lseq_is_exact (hfiber_sequence f).
Proof.
  intro; apply (is_exact_hfiber _).
Qed.

Lemma hfiber_sequence_shift_aux {A B} (f : B .-> A) (n:nat)
  : hfiber_sequence_aux f (1+n)
  = hfiber_sequence_aux (hfiber_incl_ptd f) n.
Proof.
  induction n as [ | n' IH].
  (* n = 0 *) simpl; exact 1.
  (* n = 1+n' *) exact (ap (fun ABf =>
    (pr1 (pr2 ABf); (hfiber_ptd (pr2 (pr2 ABf));
      hfiber_incl_ptd (pr2 (pr2 ABf))))) IH).
Defined.

Lemma hfiber_sequence_shift {A B} (f : B .-> A) (n:nat)
  : hfiber_sequence f (1+n) = hfiber_sequence (hfiber_incl_ptd f) n.
Proof.
  simpl. 
  change (pr1 (pr2 (hfiber_sequence_aux f n)))
  with (pr1 (hfiber_sequence_aux f (1+n))).
  apply ap, hfiber_sequence_shift_aux.
Defined.

End Hfiber_Sequence.

(******************************************************************************

The long exact sequence of loop spaces.

                                W -> Z -> 1
                                |    |    |
                                V    V    V
                                1 -> Y -> X

We show that the objects of the hfiber sequence of a map are equivalent to
iterated loop spaces.  The key lemma is showing that the double fiber of a
pointed map [f : Y .-> X] is pointed-equivalent to the loop space [Omega_ptd X].

We do *not* currently show the stronger statement that the *maps* of the hfiber
sequence agree (under the above equivalences) with the action on iterated loop
spaces of [f], and hence that the whole sequence is equivalent to one built
from loop spaces.

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
    apply pullback_ptd_fmap.
    apply mk_ptd_cospan_map with (idmap_ptd _) (idmap_ptd _) (idmap_ptd _).
      apply (concat_ptd_htpy (compose_f1_ptd _)).
      apply inverse_ptd_htpy, compose_1f_ptd.
      apply (concat_ptd_htpy (compose_f1_ptd _)).
      apply inverse_ptd_htpy, (concat_ptd_htpy (compose_1f_ptd _)).
      exists (fun _ => pt_map_pt f).     
      simpl. exact ((concat_p1 _ @ concat_1p _)^).
  apply equiv_inverse_ptd with (Omega_to_pullback_ptd X).
    apply isequiv_Omega_to_pullback.
Defined.

Lemma isequiv_hfiber_to_Omega {X Y : pointed_type} (f:Y.->X)
: IsEquiv (hfiber_to_Omega f).
Proof.
  apply @isequiv_composeR_ptd.
    apply isequiv_hfiber_to_pullback.
  apply @isequiv_composeR_ptd.
    apply (pullback_fmap_isequiv _ name_point _ name_point).
      apply isequiv_hfiber_to_pullback.
      apply isequiv_idmap.
      apply isequiv_idmap.
  apply @isequiv_composeR_ptd.
    apply (pullback_fmap_isequiv _ name_point _ name_point).
      apply pullback_symm_isequiv.
      apply isequiv_idmap.
      apply isequiv_idmap.
  apply @isequiv_composeR_ptd.
    apply isequiv_inverse.
  apply @isequiv_composeR_ptd.
    apply (pullback_fmap_isequiv name_point (f o name_point)
                                 name_point name_point);
    apply isequiv_idmap.
  apply isequiv_inverse.
Qed.

(* Note that this must be defined as a *pointed* map, since pointedness is
required for the functoriality of Omega, and hence for the induction step. *)
Lemma Omega_to_hfiber_seq_0 {X Y} (f : Y .-> X) (n:nat)
  : hfiber_sequence f (n*3) .-> (iterate Omega_ptd n) X.
Proof.
  induction n as [ | n' IH]; simpl.  
  (* n=0 *) apply idmap_ptd.
  (* n=S n' *)
  apply @compose_ptd with (Y := Omega_ptd (hfiber_sequence f (n'*3))).
    apply Omega_ptd_fmap, IH.
  apply hfiber_to_Omega.
Defined.

Lemma isequiv_Omega_to_hfiber_seq_0 {X Y} (f : Y .-> X) (n:nat)
  : IsEquiv (Omega_to_hfiber_seq_0 f n).
Proof.
  induction n as [ | n' IH].  
  (* n=0 *) simpl; apply isequiv_idmap.
  (* n=S n' *)
  apply @isequiv_compose with (B := Omega_ptd (hfiber_sequence f (n'*3))).
    apply isequiv_hfiber_to_Omega.
  apply isequiv_Omega_ptd_fmap, IH.
Qed.

Corollary Omega_to_hfiber_seq_1 {X Y} (f : Y .-> X) (n:nat)
  : hfiber_sequence f (1 + n*3) .-> (iterate Omega_ptd n) Y.
Proof.
  apply (compose_ptd (Omega_to_hfiber_seq_0 (hfiber_incl_ptd f) n)).
  apply equiv_path_ptd, hfiber_sequence_shift.
Defined.

Corollary isequiv_Omega_to_hfiber_seq_1 {X Y} (f : Y .-> X) (n:nat)
  : IsEquiv (Omega_to_hfiber_seq_1 f n).
Proof.
  apply isequiv_compose_ptd.
    apply isequiv_Omega_to_hfiber_seq_0.
  exact _. (* [equiv_isequiv equiv_path] found automagically. *)
Qed.

Corollary Omega_to_hfiber_seq_2 {X Y} (f : Y .-> X) (n:nat)
  : hfiber_sequence f (2 + n*3) .-> (iterate Omega_ptd n) (hfiber_ptd f).
Proof.
  apply (compose_ptd (Omega_to_hfiber_seq_1 (hfiber_incl_ptd f) n)).
  apply equiv_path_ptd, hfiber_sequence_shift.
Defined.

Corollary isequiv_Omega_to_hfiber_seq_2 {X Y} (f : Y .-> X) (n:nat)
  : IsEquiv (Omega_to_hfiber_seq_2 f n).
Proof.
  apply isequiv_compose_ptd.
    apply isequiv_Omega_to_hfiber_seq_1.
  exact _. (* [equiv_isequiv equiv_path] found automagically. *)
Qed.

(*
Local Variables:
coq-prog-name: "hoqtop"
End:
*)
