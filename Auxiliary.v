(*******************************************************************************

Title: Auxiliary.v
Authors: Jeremy Avigad, Chris Kapulkin, Peter LeFanu Lumsdaine
Date: 1 March 2013

This file contains lemmas that are required as background in the
Fibration Categories project, but are not supplied by the HoTT
library.

*******************************************************************************)

Require Import HoTT.

Require Export FunextAxiom.

Open Scope path.
Open Scope equiv.

Monomorphic Definition UU := Type.

Notation pr1 := projT1.
Notation pr2 := projT2.

Arguments pr1 {_ _} _.
Arguments pr2 {_ _} _.

(* TODO (mid): possible improvements now that we’re over the new library.

- increase usage of the [moveL_Pm] family;

- use [apply (concat H)] and [apply (concatR H)], rather than e.g. [path_via' p. apply H.]

- use [whiskerL], [whiskerR] rather than [apply (ap (concat p))] and [apply (ap (fun q => q @ p))].

*)

(*******************************************************************************

Paths.

*******************************************************************************)

Section Paths.

(* Convenient for the frequent idiom [apply (concat (concat_pp_p))] and variants. *)
Global Arguments concat_pp_p {_ _ _ _ _ _ _ _}.
Global Arguments concat_p_pp {_ _ _ _ _ _ _ _}.

(* The Paulin-Mohring elimination principle for equalities is
very useful, but asymmetric. This is its left-handed counterpart. *)
Definition id_opp_elim {X:Type} (x:X)
  {P:forall (y:X) (p:y=x), Type}
: (P x 1)
  -> forall (y:X) (p:y=x), P y p.
Proof.
  intros P1 y p. destruct p. assumption.
Defined.
(* Note: this proof, while clean, is proof-theoretically overkill — it requires a universe, since inspecting it carefully, it Id-eliminates into a Pi-type with large domain (since P has to be generalized).  With a little more work, it can be proved more economically, using just pure M-L TT. *)
 
Definition path_space (A : Type) := { x:A & { y:A & x = y }}.

(* Useful mainly for the idiom [apply (concatR (expression))]. *)
Definition concatR {A : Type} {x y z : A}  (q : y = z) (p : x = y)
  := concat p q.

End Paths.

(* A variant of [path_via] that does not attempt to do anything clever. *)
Ltac path_via' mid :=
  apply @concat with (y := mid).

(*******************************************************************************

Lemmas about paths in types of the form [{a : A & {b : B & C a b}}].

*******************************************************************************)

Section TriplePaths.

Lemma triple_path  {A : Type} {B : Type} (C : A -> B -> Type)
  (u v : {a : A & {b : B & C a b}})
  (p : (pr1 u) = (pr1 v))
  (q : (pr1 (pr2 u)) = (pr1 (pr2 v)))
  (r : (transport (fun x => C x (pr1 (pr2 v))) p
         (transport (C (pr1 u)) q (pr2 (pr2 u))))
       = (pr2 (pr2 v)))
: u = v.
Proof.
  destruct u as [u1 [u2 u3]], v as [v1 [v2 v3]]. simpl in * |- *.
  destruct p; destruct q; destruct r. simpl. exact 1.
Defined.

Lemma pr1_triple_path  {A : Type} {B : Type} (C : A -> B -> Type)
  (u v : {a : A & {b : B & C a b}})
  (p : (pr1 u) = (pr1 v))
  (q : (pr1 (pr2 u)) = (pr1 (pr2 v)))
  (r : (transport (fun x => C x (pr1 (pr2 v))) p
         (transport (C (pr1 u)) q (pr2 (pr2 u))))
       = (pr2 (pr2 v)))
: ap pr1 (triple_path C u v p q r) = p.
Proof.
  destruct u as [u1 [u2 u3]], v as [v1 [v2 v3]]. simpl in * |- *.
  destruct p. destruct q. destruct r. simpl. exact 1.
Defined.

Lemma pr2_triple_path  {A : Type} {B : Type} (C : A -> B -> Type)
  (u v : {a : A & {b : B & C a b}})
  (p : (pr1 u) = (pr1 v))
  (q : (pr1 (pr2 u)) = (pr1 (pr2 v)))
  (r : (transport (fun x => C x (pr1 (pr2 v))) p
         (transport (C (pr1 u)) q (pr2 (pr2 u))))
       = (pr2 (pr2 v)))
: ap (fun xyz => pr1 (pr2 xyz)) (triple_path C u v p q r) = q.
Proof.
  destruct u as [u1 [u2 u3]], v as [v1 [v2 v3]]. simpl in * |- *.
  destruct p. destruct q. destruct r. simpl. exact 1.
Defined.

(* TODO (low): triple_path_pr3.  (The tricky bit is typing the statement.) *)

End TriplePaths.

(*******************************************************************************

Equivalences.

*******************************************************************************)

(* TODO (low): move this declarations into the section itself, once weird bug is sorted out. *)
Arguments BuildEquiv [A B f] _ : rename.

Section Equivs.

(* TODO (high): move to library. *)
Global Arguments equiv_inv [A B] f {_} x.

(* TODO (low): consider; possibly move to library. *)
Global Arguments equiv_fun [A B] _ _.
Global Arguments equiv_isequiv [A B] e.
Global Arguments isequiv_adjointify [A B f] _ _ _.

(* TODO (med): Unnecessary here; but probably move to library. *)
Global Arguments isequiv_ap [A B] f {_} x y.

(* TODO (high): move to library. *)
Global Arguments isequiv_postcompose {_} A [B C] f {_}.
Global Arguments isequiv_precompose {_} [A B] C f {_}.

(*
TODO (low): also consider/try changing arguments as follows:
Arguments cancelL_isequiv [B C] g {ge} [A] f {fge} : rename.
Arguments cancelR_isequiv [A B] f {fe} [C] g {gfe}.

Also: consider changing the order of their arguments; and *definitely* try making them not instances.
*)

(* Compare to [map_equiv_o_inverse] in old library *)
(* TODO (low): actually, this is an instance of homotopy-naturality, [concat_Ap].  Can it be replaced by that? *)
Lemma ap_inverse_o_equiv {A B : Type} (e : A <~> B)
  {x y : B} (p : x = y)
: ap e (ap (e ^-1) p)
  = (eisretr e x @ p) @ (eisretr e y)^.
Proof.
  destruct p. simpl.
  path_via (eisretr e x @ (eisretr e x)^).
    symmetry. apply concat_pV.
  apply whiskerR, inverse, concat_p1. 
Defined.

(* Every type [P] is equivalent to the function type [1 -> P]. *)
Lemma well_pointedness (P : Type) : P <~> (Unit -> P).
Proof.
  exists (fun x _ => x).
  apply (isequiv_adjointify (fun f => f tt)).
  intros f. apply path_forall. intros []. exact 1.
  intros x. exact 1.
Defined.

End Equivs.


(*******************************************************************************

HLevels.

*******************************************************************************)

Section HLevels.

(* TODO (low): move to HoTT? *)
Record HSet := {
  hset_carrier :> Type;
  ishset_hset : IsHSet hset_carrier }.

End HLevels.

(*******************************************************************************

Functional Extensionality.

*******************************************************************************)

Section Funext.

Global Arguments path_forall {_} [_ _ _ _] _.

(** [path_forall] commutes with [inverse].  (This follows purely formally from the fact that its inverse [apD10] does.) *)
Definition path_forall_V {X : Type} {P : X -> Type} {f g : forall x, P x}
  (H : forall x, f x = g x)
: path_forall (fun x => (H x)^) = (path_forall H)^.
Proof.
  path_via' (path_forall (fun x => (apD10 (path_forall H) x)^)).
    apply ap, (@ap _ _ (fun h x => (h x)^)). apply inverse, eisretr.
  path_via' (path_forall (apD10 (path_forall H)^)).
    apply ap, inverse. apply path_forall; intros x. apply apD10_V.
  apply eissect.
Defined.

(** Note: this differs from the library function [apD10_path_forall] essentially only in having [pointwise_paths] unfolded in its type.  However, that is enough to make working with it more convenient — in particular, [rewrite] often works with this where it fails with [apD10_path_forall]. *)
Definition apD10_path_forall' {A : Type} {P : A -> Type}
  {f g : forall x, P x} (h : f == g) (x:A)
  : apD10 (path_forall h) x = h x
:= (apD10_path_forall _ _ h x).
(*TODO (high): consistentize the various ways of using [eisretr], [apD10_path_forall], etc. *)

End Funext.

(*******************************************************************************

Various things that don’t have a clear home.

*******************************************************************************)

Section Varia.

(* TODO (low): move to live with hfibers?  Where do they live? *)
Definition hfiber_incl {X Y:Type} (f:X -> Y) (y:Y) : hfiber f y -> X
:= pr1.

Fixpoint iterate {A:Type} (f:A->A) (n:nat)
:= fun x => match n with O => x | S n' => f (iterate f  n' x) end.

Fixpoint iterate_dep {A:Type} (f:A->A) (B:A->Type)
  (g : forall a:A, B a -> B (f a))
  (n:nat)
:= fun (x:A) (y:B x) => match n return (B (iterate f n x)) with
     | O => y
     | S n' => g _ (iterate_dep _ _ g n' x y) end.

Lemma moveR_I {AA BB : Type} (ff : AA -> BB) {H : IsEquiv ff} (x : AA) (y : BB)
  : y = ff x -> ff ^-1 y = x.
Proof.
  intros H_eq.  path_via (ff ^-1 (ff x)).
  apply ap, H_eq.  apply eissect.
Defined.

(* Compare [equiv_sigma_contr] in library. *)
Lemma isequiv_sigma_contr {X:Type} {Y:X->Type}
: (forall x:X, Contr (Y x)) -> IsEquiv (@projT1 X Y).
Proof.
  intros H. exact (equiv_isequiv (equiv_sigma_contr _)).
Defined.

Lemma isequiv_hfiber_incl_over_hprop {Y X : Type} (X_hprop : IsHProp X)
  (f : Y -> X) (x:X)
: IsEquiv (hfiber_incl f x).
Proof.
  refine (isequiv_sigma_contr _).
Defined.

End Varia.

Notation "A /\ B" := (A * B).
Notation "A <-> B" := ((A -> B) /\ (B -> A)).


(*
Local Variables:
coq-prog-name: "hoqtop"
End:
*)
