(*******************************************************************************

Title: Pullbacks2.v
Authors: Jeremy Avigad, Chris Kapulkin, Peter LeFanu Lumsdaine
Date: 1 March 2013

Examples of pullbacks, various properties.

*******************************************************************************)

(* Imports *)

Require Import HoTT EquivalenceVarieties.

Require Import Auxiliary Fundamentals Pullbacks Equalizers.

(*******************************************************************************

Example of pullbacks:

homotopy fibers can be expressed as pullbacks.

*******************************************************************************)

Section Hfiber_as_Pullback.

Definition name {A : Type} (a : A) (t : Unit) : A := a.

Definition hfiber_to_pullback {A B : Type} (f : B -> A) (a : A)
    (bp : hfiber f a) : (pullback f (name a)).
Proof.
  exists (pr1 bp). exists tt. apply (pr2 bp).
Defined.

Definition pullback_to_hfiber {A B : Type} (f : B -> A) (a : A)
  (btp : pullback f (name a)) : hfiber f a.
Proof.
  exists (pr1 btp). exact (pr2 (pr2 btp)).
Defined.

Lemma isequiv_hfiber_to_pullback {A B : Type} (f : B -> A) (a : A)
  : IsEquiv (hfiber_to_pullback f a).
Proof.
  apply (isequiv_adjointify (pullback_to_hfiber f a)).
  (* is_section *) intros [b [[] p]]. exact 1.
  (* is_retraction *) intros [b p]. exact 1.
Defined.

Definition hfiber_to_pullback_equiv {A B : Type} (f : B -> A) (a : A)
  : (hfiber f a) <~> (pullback f (name a))
:= BuildEquiv (isequiv_hfiber_to_pullback f a).

End Hfiber_as_Pullback.


(*******************************************************************************

Example of pullbacks:

Loop spaces can be expressed as pullbacks.

*******************************************************************************)

Section Loops.

Definition Omega (A : Type) (a0 : A) : Type
:= (a0 = a0).

Definition Omega_to_pullback {A : Type} {a0 : A} (l : Omega A a0)
: pullback (name a0) (name a0).
Proof.
  exists tt. exists tt. exact l.
Defined.

Definition pullback_to_Omega {A : Type} {a0 : A}
  (tsl : pullback (name a0) (name a0))
: Omega A a0.
Proof.
  destruct tsl as [[] [[] l]]. exact l.
Defined.

Lemma isequiv_Omega_to_pullback {A : Type} (a0 : A)
: IsEquiv (@Omega_to_pullback A a0).
Proof.
  apply (isequiv_adjointify (pullback_to_Omega)).
  (* is_section *) intros [[] [[] l]]. exact 1.
  (* is_retraction *) intros l. exact 1.
Qed.

Definition Omega_to_pullback_equiv {A : Type} {a0 : A}
: (Omega A a0) <~> (pullback (name a0) (name a0))
:= BuildEquiv (isequiv_Omega_to_pullback a0).

Definition Omega_fmap {A B : Type} (a0 : A) (f : A->B)
: (Omega A a0) -> (Omega B (f a0)).
Proof.
  exact (ap f).
Defined.

Instance isequiv_Omega_fmap {A B : Type} (a0 : A) (f : A->B)
: IsEquiv f -> IsEquiv (Omega_fmap a0 f).
Proof.
  intros f_iseq. apply isequiv_ap; assumption.
Qed.

Definition Omega_conj {A} {a0 a1:A} (p:a0 = a1)
: Omega A a0 -> Omega A a1.
Proof.
  exact ((concatR p) o (concat p^)).
Defined.

Instance isequiv_Omega_conj {A} {a0 a1:A} (p:a0 = a1)
: IsEquiv (Omega_conj p).
Proof.
  apply isequiv_compose.
  (* [isequiv_concat], [isequiv_concatR] found automatically! *)
Qed.

End Loops.


(*******************************************************************************

Pullbacks vs. Equalizers:

- the construction of the equalizer as a pullback, and the fact this is
  equivalent to the direct construction;
- and vice versa, the construction of pullbacks as equalizers, and
  attendant equivalence.

*******************************************************************************)

Section Equalizers_as_Pullbacks.

Context {A B : Type} (f : A -> B) (g : A -> B).

Definition eq_as_pb
:= pullback (fun a => (f a, g a)) (@Delta B).

Definition equalizer_to_eq_as_pb
: equalizer f g -> eq_as_pb.
Proof.
  intros [a r].
  exists a; exists (g a).
  apply path_prod'. exact r. exact 1.
Defined.

Definition eq_as_pb_to_equalizer
: eq_as_pb -> equalizer f g.
Proof.
  intros [a [b pq]].
  exists a.
  set (p := ap fst pq).
  set (q := ap snd pq).
  exact (p @ q^).
Defined.

Definition eq_as_pb_equiv
: (equalizer f g) <~> eq_as_pb.
Proof.
  exists equalizer_to_eq_as_pb.
  apply (isequiv_adjointify eq_as_pb_to_equalizer).
  (* is_section *)
  intros [a [b pq]]. simpl.
  (* Note: would be lovely if we had a tactic here that would
     let us “destruct pq”. *)
  apply path_sigma_uncurried. exists 1. simpl.
  apply path_sigma_uncurried. simpl. exists (ap snd pq).
  (* transport lemma *)
  assert (forall (b1 b2 : B) (e:b1 = b2)
       (pq : (f a, g a) = Delta b1),
         transport (fun b => (f a, g a) = Delta b) e pq
       = path_prod' (ap fst pq @ e) (ap snd pq @ e))
       as transp_lemma.
    intros b1 b2 e pq'. destruct e. simpl.
    repeat rewrite concat_p1. apply inverse, eta_path_prod.
    rewrite transp_lemma.
  unfold Delta. (* Why is this necessary?

  Delta appears in imlicit arguments, and needs to be
  unfolded before rewrites can be applied.

  Working out what why these rewrites weren’t working was
  painful… *)
  unfold path_prod'.  rewrite ap_fst_path_prod. rewrite ap_snd_path_prod. simpl.
    rewrite concat_pp_p.
    rewrite concat_Vp. rewrite concat_p1.
  rewrite concat_1p. apply eta_path_prod.
  (* is_retraction *)
  intros [a p]. simpl.
  apply path_sigma_uncurried. exists 1. simpl.
  unfold Delta.
  unfold path_prod'.  rewrite ap_fst_path_prod. rewrite ap_snd_path_prod.
  simpl. apply concat_p1.
Defined.

End Equalizers_as_Pullbacks.

Section Pullbacks_as_Equalizers.

Context {A B C : Type} (f : A -> C) (g : B -> C).

Definition pb_as_eq
  := equalizer (f o fst) (g o snd).

Definition pullback_to_pb_as_eq
  : pullback f g -> pb_as_eq.
Proof.
  intros [a [b p]].
  exists (a, b). exact p.
Defined.

Definition pb_as_eq_to_pullback
  : pb_as_eq -> pullback f g.
Proof.
  intros [[a b] p].
  exists a. exists b. exact p.
Defined.

Definition pb_as_eq_equiv
  : (pullback f g) <~> pb_as_eq.
Proof.
  exists pullback_to_pb_as_eq.
  apply (isequiv_adjointify pb_as_eq_to_pullback).
  (* section *)
  intros [[a b] p]. simpl. exact 1.
  (* retraction *)
  intros [a [b p]]. simpl. exact 1.
Defined.

End Pullbacks_as_Equalizers.


(*******************************************************************************

Various interesting properties of maps are stable under pullback.

In particular, any property of the form “all hfibers of [g] are nice”
is pullback-stable, since each hfiber of the pullback of [g] is
equivalent to an hfiber of [g] itself.

*******************************************************************************)

Section Stable_properties.

Lemma hfiber_of_pullback {A B C:Type} (f:A->C) (g:B->C)
: forall a:A, hfiber (f^* g) a <~> hfiber g (f a).
Proof.
  intros a.
  equiv_via (pullback (f^* g) (name a)).
    apply hfiber_to_pullback_equiv.
  equiv_via (pullback g (f o (name a))).
    apply equiv_inverse. apply two_pullbacks_equiv.
  apply equiv_inverse. apply hfiber_to_pullback_equiv.
Defined.

Lemma pullback_preserves_equiv {A B C:Type} (f:A->C) (g:B->C)
: IsEquiv g -> IsEquiv (f^* g).
Proof.
  intros g_iseq.
  apply isequiv_fcontr. intros a.
  apply (@contr_equiv' (hfiber g (f a))).
  apply equiv_inverse. apply hfiber_of_pullback.
  apply fcontr_isequiv, g_iseq.
Qed.

(* A slight aside, generalizing the previous lemma: if [P] is any
property of types preserved under equivalence, then the property of
being “fiberwise [P]” is stable under pullback.

Under Univalence, the hypothesis [P_pres_equiv] is of course unnecessary. *)
Lemma pullback_preserves_fiberwise_properties
  (P : Type -> Type) (P_pres_equiv : forall A B : Type, (A <~> B) -> P A -> P B)
  {A B C:Type} (f:A->C) (g:B->C)
: (forall c:C, P (hfiber g c)) -> (forall a:A, P (hfiber (f^* g) a)).
Proof.
  intros g_is_fiberwise_P a.
  apply (P_pres_equiv (hfiber g (f a))).
  apply equiv_inverse. apply hfiber_of_pullback.
  apply g_is_fiberwise_P.
Defined.

(* TODO (low): corollary — stability of n-equivalences and n-truncated
maps under pullback. (Issue: we don’t have these defined in library.)
*)

End Stable_properties.


(*
Local Variables:
coq-prog-name: "hoqtop"
End:
*)
