(*******************************************************************************

Title: Pullbacks.v
Authors: Jeremy Avigad, Chris Kapulkin, Peter LeFanu Lumsdaine
Date: 1 March 2013

The standard pullback construction, the abstract characterization of pullbacks,
and properties of both of these.

*******************************************************************************)

Require Import HoTT.

Require Import Auxiliary CommutativeSquares.


(*******************************************************************************

The standard construction of a pullback.

*******************************************************************************)

Section Concrete_Pullbacks.

Definition pullback {A B C : Type} (f : A -> C) (g : B -> C)
:= { x : A & { y : B & (f x) = (g y) }} : Type.

Definition pullback_pr1 {A B C : Type} {f : A -> C} {g : B -> C}
  (x : pullback f g) := pr1 x.

Definition pullback_pr2 {A B C : Type} {f : A -> C} {g : B -> C}
  (x : pullback f g) := pr1 (pr2 x).

Definition pullback_comm {A B C : Type} {f : A -> C} {g : B -> C}
  (x : pullback f g) := pr2 (pr2 x).

(* Sometimes one wants to view one the pullback projections as the
pullback of a map. Arbitrarily, we choose the second projection as
the one to use in this way. *)
Notation "f ^* g" := (@pullback_pr2 _ _ _ g f) (at level 45).

Definition mk_pullback {A B C : Type} (f : A -> C) (g : B -> C)
  (a : A) (b : B) (p : (f a) = (g b))
: pullback f g.
Proof.
  exists a, b. exact p.
Defined.

Definition pullback_path {A B C : Type} {f : A -> C} {g : B -> C}
  (u u' : pullback f g)
  (p : pullback_pr1 u = pullback_pr1 u')
  (q : pullback_pr2 u = pullback_pr2 u')
  (r : (ap f p)^ @ (pullback_comm u) @ (ap g q)
       = pullback_comm u')
: u = u'.
Proof.
  destruct u as [a [b c]], u' as [a' [b' c']].
  unfold pullback_pr2 in q. simpl in p, q.
  destruct p, q. apply ap, ap. simpl in r.
  exact ((concat_1p _)^ @ (concat_p1 _)^ @ r).
Defined.

Global Arguments pullback_path : simpl never.

(* Alias of [pullback_path]; useful for [apply]ing and then using
   [exists] to supply the arguments (compare [path_sigma_uncurried]). *)
Definition pullback_path' {A B C : Type} {f : A -> C} {g : B -> C}
  (u u' : pullback f g)
: { p : pullback_pr1 u = pullback_pr1 u'
    & {q : pullback_pr2 u = pullback_pr2 u'
    & (ap f p)^ @ (pullback_comm u) @ (ap g q)
      = pullback_comm u' } }
  -> u = u'.
Proof.
  intros [p [q r]]. apply (pullback_path u u' p q r).
Defined.

Global Arguments pullback_path' [_ _ _ _ _] _ _ _ : simpl never.

Definition pullback_path_pr1 {A B C : Type} {f : A -> C} {g : B -> C}
  (u u' : pullback f g)
  (p : pullback_pr1 u = pullback_pr1 u')
  (q : pullback_pr2 u = pullback_pr2 u')
  (r : (ap f p)^ @ (pullback_comm u) @ (ap g q)
       = pullback_comm u')
: ap pullback_pr1 (pullback_path u u' p q r) = p.
Proof.
  destruct u as [a [b c]], u' as [a' [b' c']].
  unfold pullback_pr2 in q. simpl in p, q.
  destruct p, q. simpl.
  apply (concat (ap_compose (existT _ a) pullback_pr1 _)^).
  apply ap_const.
Defined.

Definition pullback_path_pr2 {A B C : Type} {f : A -> C} {g : B -> C}
  (u u' : pullback f g)
  (p : pullback_pr1 u = pullback_pr1 u')
  (q : pullback_pr2 u = pullback_pr2 u')
  (r : (ap f p)^ @ (pullback_comm u) @ (ap g q)
       = pullback_comm u')
: ap pullback_pr2 (pullback_path u u' p q r) = q.
Proof.
  destruct u as [a [b c]], u' as [a' [b' c']].
  unfold pullback_pr2 in q. simpl in p, q.
  destruct p, q. unfold pullback_path; simpl.
  rewrite <- ! ap_compose.
  apply ap_const.
Defined.

Definition pullback_path'_pr1 {A B C : Type} {f : A -> C} {g : B -> C}
  (u u' : pullback f g)
  (pqr : { p : pullback_pr1 u = pullback_pr1 u'
    & {q : pullback_pr2 u = pullback_pr2 u'
    & (ap f p)^ @ (pullback_comm u) @ (ap g q)
      = pullback_comm u' } })
: ap pullback_pr1 (pullback_path' u u' pqr) = pr1 pqr.
Proof.
  destruct pqr as [p [q r]]. apply pullback_path_pr1.
Defined.

Definition pullback_path'_pr2 {A B C : Type} {f : A -> C} {g : B -> C}
  (u u' : pullback f g)
  (pqr : { p : pullback_pr1 u = pullback_pr1 u'
    & {q : pullback_pr2 u = pullback_pr2 u'
    & (ap f p)^ @ (pullback_comm u) @ (ap g q)
      = pullback_comm u' } })
: ap pullback_pr2 (pullback_path' u u' pqr) = pr1 (pr2 pqr).
Proof.
  destruct pqr as [p [q r]]. apply pullback_path_pr2.
Defined.

End Concrete_Pullbacks.

Notation "f ^* g" := (@pullback_pr2 _ _ _ g f) (at level 45).


(*******************************************************************************

The standard pullback is symmetric.

*******************************************************************************)

Section Pullback_Symm.

Definition pullback_symm {A B C : Type} (f : A -> C) (g : B -> C)
: pullback f g -> pullback g f.
Proof.
  intros abp.
  exists (pullback_pr2 abp), (pullback_pr1 abp).
  exact ((pullback_comm abp)^).
Defined.

Lemma pullback_symm_isequiv {A B C : Type} (f : A -> C) (g : B -> C)
: IsEquiv (pullback_symm f g).
Proof.
apply (isequiv_adjointify (pullback_symm g f)).
  (* section *)
  intros [b [a q]]; simpl. apply pullback_path'.
  unfold pullback_pr2, pullback_comm; simpl.
  exists 1, 1. simpl. exact (concat_p1 _ @ concat_1p _ @ inv_V _).
  (* retraction *)
  intros [a [b p]]; simpl. apply pullback_path'.
  unfold pullback_pr2, pullback_comm; simpl.
  exists 1, 1. simpl. exact (concat_p1 _ @ concat_1p _ @ inv_V _).
Defined.

Definition pullback_symm_equiv {A B C : Type} (f : A -> C) (g : B -> C)
  := BuildEquiv (pullback_symm_isequiv f g)
  : pullback f g <~> pullback g f.

End Pullback_Symm.


(*******************************************************************************

Cospan cones, that is, cones on the data A, B, C, f : A -> C, g : B -> C.
(The pullback is a universal such cone.)

*******************************************************************************)

Section Cospan_Cone.

Definition cospan_cone {A B C : Type} (f : A -> C) (g : B -> C) (X : Type)
:= { h : (X -> A) & { k : (X -> B) & forall x, (f(h x)) = (g(k x)) }}.

Definition mk_cospan_cone {A B C : Type} {f : A -> C} {g : B -> C} {X : Type}
  {h : X -> A} {k : (X -> B)} (alpha : forall x, (f(h x)) = (g(k x)))
: cospan_cone f g X.
Proof.
  exists h. exists k. apply alpha.
Defined.

Definition cospan_cone_map1 {A B C : Type} {f : A -> C} {g : B -> C}
  {X : Type} (C : cospan_cone f g X) := pr1 C.

Definition cospan_cone_map2 {A B C : Type} {f : A -> C} {g : B -> C}
  {X : Type} (C : cospan_cone f g X) := pr1 (pr2 C).

Definition cospan_cone_comm {A B C : Type} {f : A -> C} {g : B -> C}
  {X : Type} (C : cospan_cone f g X) := pr2 (pr2 C).

(* TODO (mid): try redoing without triple_path
  (but then be careful to check Pullbacks3 over it). *)
Definition cospan_cone_path
  {A B C : Type} {f : A -> C} {g : B -> C} {X : Type}
  {Phi1 Phi2 : cospan_cone f g X}
  (p : cospan_cone_map1 Phi1 = cospan_cone_map1 Phi2)
  (q : cospan_cone_map2 Phi1 = cospan_cone_map2 Phi2)
  (r : forall x:X,
    cospan_cone_comm Phi1 x
    = (ap f (ap10 p x)) @ cospan_cone_comm Phi2 x @ (ap g (ap10 q x))^)
: Phi1 = Phi2.
Proof.
  apply (triple_path _ Phi1 Phi2 p q).
  destruct Phi1 as [h1 [k1 alpha1]], Phi2 as [h2 [k2 alpha2]].
  unfold cospan_cone_map2 in q; simpl in p, q. destruct p, q.
  unfold cospan_cone_comm in r; simpl in *.
  apply path_forall. intros x.
  apply (concat (r x)). apply (concat_p1 _ @ concat_1p _).
Defined.

Definition cospan_cone_path'
  {A B C : Type} {f : A -> C} {g : B -> C} {X : Type}
  {Phi1 Phi2 : cospan_cone f g X}
: { p : cospan_cone_map1 Phi1 = cospan_cone_map1 Phi2
  & { q : cospan_cone_map2 Phi1 = cospan_cone_map2 Phi2
  & forall x:X,
       cospan_cone_comm Phi1 x
     = (ap f (ap10 p x)) @ cospan_cone_comm Phi2 x @ (ap g (ap10 q x))^ }}
-> Phi1 = Phi2
  := fun pqr => cospan_cone_path (pr1 pqr) (pr1 (pr2 pqr)) (pr2 (pr2 pqr)).

(* a converse to the above *)
Definition cospan_cone_path_comm
  {A B C : Type} {f : A -> C} {g : B -> C} {X : Type}
  {Phi1 Phi2 : cospan_cone f g X} (e : Phi1 = Phi2)
: forall x:X,
    cospan_cone_comm Phi1 x
  = (ap f (ap10 (ap cospan_cone_map1 e) x))
    @ cospan_cone_comm Phi2 x
    @ (ap g (ap10 (ap cospan_cone_map2 e) x))^.
Proof.
  intros x. destruct e; simpl. exact ((concat_p1 _ @ concat_1p _)^).
Defined.

Definition cospan_cone_path_map1
  {A B C : Type} {f : A -> C} {g : B -> C} {X : Type}
  {Phi1 Phi2 : cospan_cone f g X}
  (p : cospan_cone_map1 Phi1 = cospan_cone_map1 Phi2)
  (q : cospan_cone_map2 Phi1 = cospan_cone_map2 Phi2)
  (r : forall x:X,
    cospan_cone_comm Phi1 x
    = (ap f (ap10 p x))
      @ cospan_cone_comm Phi2 x
      @ (ap g (ap10 q x))^) :
  ap cospan_cone_map1 (cospan_cone_path p q r) = p.
Proof.
  apply pr1_triple_path.
Defined.

Definition cospan_cone_path_map2
  {A B C : Type} {f : A -> C} {g : B -> C} {X : Type}
  {Phi1 Phi2 : cospan_cone f g X}
  (p : cospan_cone_map1 Phi1 = cospan_cone_map1 Phi2)
  (q : cospan_cone_map2 Phi1 = cospan_cone_map2 Phi2)
  (r : forall x:X,
    cospan_cone_comm Phi1 x
    = (ap f (ap10 p x))
      @ cospan_cone_comm Phi2 x
      @ (ap g (ap10 q x))^)
: ap cospan_cone_map2 (cospan_cone_path p q r) = q.
Proof.
  apply (pr2_triple_path _ Phi1 Phi2).
Defined.

Lemma cospan_cone_path'_map1
  {A B C : Type} {f : A -> C} {g : B -> C} 
  {X : Type} {Phi1 Phi2 : cospan_cone f g X}
  (pqr : {p : cospan_cone_map1 Phi1 = cospan_cone_map1 Phi2 &
         {q : cospan_cone_map2 Phi1 = cospan_cone_map2 Phi2 &
         forall x : X, cospan_cone_comm Phi1 x
           = (ap f (ap10 p x) @ cospan_cone_comm Phi2 x)
             @ (ap g (ap10 q x)) ^}})
: ap cospan_cone_map1 (cospan_cone_path' pqr) = pr1 pqr. 
Proof.
  apply cospan_cone_path_map1.
Defined.

Lemma cospan_cone_path'_map2
  {A B C : Type} {f : A -> C} {g : B -> C} 
  {X : Type} {Phi1 Phi2 : cospan_cone f g X}
  (pqr : {p : cospan_cone_map1 Phi1 = cospan_cone_map1 Phi2 &
         {q : cospan_cone_map2 Phi1 = cospan_cone_map2 Phi2 &
         forall x : X, cospan_cone_comm Phi1 x
           = (ap f (ap10 p x) @ cospan_cone_comm Phi2 x)
             @ (ap g (ap10 q x)) ^}})
: ap cospan_cone_map2 (cospan_cone_path' pqr) = pr1 (pr2 pqr). 
Proof.
  apply cospan_cone_path_map2.
Defined.

(* TODO (mid): cospan_cone_path_comm, cospan_cone_path'_comm *)

End Cospan_Cone.


(*******************************************************************************

The universal property of pullbacks.

*******************************************************************************)

Section Pullback_UP.

(* TODO (high): try finding a naming scheme more related to the idea of “composition”. *) 
Definition map_to_cospan_cone {A B C : Type} {f : A -> C} {g : B -> C}
  {P : Type} (D: cospan_cone f g P) (X : Type) (u : X -> P)
: cospan_cone f g X.
Proof.
  exists ((cospan_cone_map1 D) o u), ((cospan_cone_map2 D) o u).
  intros z; apply (cospan_cone_comm D).
Defined.

Definition is_pullback_cone {A B C : Type} {f : A -> C} {g : B -> C}
  {P : Type} (D : cospan_cone f g P)
:= forall (X : UU), IsEquiv (map_to_cospan_cone D X).

Lemma hprop_is_pullback_cone {A B C : Type} {f : A -> C} {g : B -> C}
  {P : Type} (D : cospan_cone f g P)
: IsHProp (is_pullback_cone D).
Proof.
(* Coq automatically finds [trunc_forall] and [hprop_isequiv]: *)
  exact _.
Defined.

Definition pullback_cospan_cone {A B C : Type} (f : A -> C) (g : B -> C)
  : cospan_cone f g (pullback f g)
:= mk_cospan_cone (@pullback_comm _ _ _ f g).

Definition map_to_pullback_to_cospan_cone
  {A B C : Type} {f : A -> C} {g : B -> C} {X : Type} (m : X -> pullback f g)
  : cospan_cone f g X
:= map_to_cospan_cone (pullback_cospan_cone f g) _ m.

Definition cospan_cone_to_map_to_pullback
  {A B C : Type} {f : A -> C} {g : B -> C} {X : Type} (D : cospan_cone f g X)
  : (X -> pullback f g).
Proof.
  intros x. exists (cospan_cone_map1 D x), (cospan_cone_map2 D x). 
  exact (cospan_cone_comm D x).
Defined.

(* Most of the time, one can use this universal property opaquely, and doing so improves efficiency significantly.  However, sometimes one wants to recover the computational content.  There are several ways one could do this; we do it by giving first a transparent and then an opaque form, and providing an “unlocking” lemma to convert the latter to the former when required. *)
Lemma pullback_universal_transparent {A B C : Type} (f : A -> C) (g : B -> C)
: is_pullback_cone (pullback_cospan_cone f g).
Proof.
  intros X.
  apply (isequiv_adjointify (cospan_cone_to_map_to_pullback)).
  (* is_section *)
  intros [y1 [y2 y3]].
  unfold map_to_cospan_cone, cospan_cone_to_map_to_pullback.
  unfold cospan_cone_map2, cospan_cone_comm; simpl.
  unfold pullback_comm, compose; simpl.
  exact 1.
  (* is_retraction *)
  intros m. apply path_forall.
  intros x; simpl.
  apply pullback_path'.
  exists 1, 1. simpl.
  exact (concat_p1 _ @ concat_1p _).
Defined.

(* The opaque version, to be used by default. *)
Lemma pullback_universal {A B C : Type} (f : A -> C) (g : B -> C)
: is_pullback_cone (pullback_cospan_cone f g).
Proof.
  apply pullback_universal_transparent.
Qed.

Lemma pullback_universal_unlock
: @pullback_universal = @pullback_universal_transparent.
Proof.
  do 5 (apply path_forall; intro). 
  apply hprop_is_pullback_cone.
Qed.

End Pullback_UP.


(*******************************************************************************

An equivalent, and small, formulation of the abstract pullback property.

*******************************************************************************)

Section Pullback_UP'.

Definition is_pullback_cone' {A B C : Type} {f : A -> C} {g : B -> C} {P : Type}
  (D : cospan_cone f g P)
:= IsEquiv (cospan_cone_to_map_to_pullback D).

Lemma is_pullback_cone'_to_is_pullback_cone
  {A B C : Type} {f : A -> C} {g : B -> C} {P : Type} (D : cospan_cone f g P)
: is_pullback_cone' D -> is_pullback_cone D.
Proof.
  unfold is_pullback_cone, is_pullback_cone'. intros D_is_PB' X.
  assert (H : map_to_cospan_cone D X
             = (map_to_cospan_cone (pullback_cospan_cone f g) X)
             o (fun m : X -> P => cospan_cone_to_map_to_pullback D o m)).
    apply path_forall. intros m.
    apply cospan_cone_path'. simpl.
    exists 1, 1. simpl.
    intros x. apply inverse. exact (concat_p1 _ @ concat_1p _).
  rewrite H; clear H.
  apply @isequiv_compose.
  apply isequiv_postcompose; assumption.
  apply pullback_universal.
Qed.

Lemma is_pullback_cone_to_is_pullback_cone'
  {A B C : Type} {f : A -> C} {g : B -> C} {P : Type} (D : cospan_cone f g P)
: is_pullback_cone D -> is_pullback_cone' D.
Proof.
  intros D_is_pullback. unfold is_pullback_cone, is_pullback_cone' in *.
  set (e1 := (BuildEquiv (D_is_pullback Unit))).
  set (e2 := equiv_inverse
          (BuildEquiv (pullback_universal_transparent f g Unit))).
  set (e := equiv_compose' (equiv_inverse (well_pointedness (pullback f g)))
           (equiv_compose' e2
           (equiv_compose' e1
                           (well_pointedness P)))).
  assert (H : cospan_cone_to_map_to_pullback D = e).
    apply path_forall. intros x.
    apply pullback_path'; simpl.
    exists 1, 1; simpl.
    exact (concat_p1 _ @ concat_1p _).
  rewrite H.
  apply equiv_isequiv.
Defined.

End Pullback_UP'.


(*******************************************************************************

Properties of pullbacks in general, via U.P.’s.

*******************************************************************************)

Section Pullback_UP_facts.

(* TODO (med): is this really needed, or would it be more natural to go directly from [is_pullback_cone] to [abstract_pullback]? *)
Definition pullback_cone {A B C : Type} (f : A -> C) (g : B -> C) (P : Type)
:= { CP : cospan_cone f g P & is_pullback_cone CP }.

Definition pullback_cone_cone {A B C : Type} {f : A -> C} {g : B -> C}
  {P : Type} (CP : pullback_cone f g P)
:= pr1 CP : cospan_cone f g P.
Coercion pullback_cone_cone : pullback_cone >-> cospan_cone.

(* TODO (low): would it affect anything to make this opaque? *)
Definition pullback_cone_UP {A B C : Type} {f : A -> C} {g : B -> C}
  {P : Type} (CP : pullback_cone f g P)
:= pr2 CP : is_pullback_cone CP.

Record abstract_pullback {A B C : Type} (f : A -> C) (g : B -> C)
:= mk_abstract_pullback
  { abstract_pullback_vertex :> Type;
    abstract_pullback_cone :> pullback_cone f g abstract_pullback_vertex }.

Global Arguments mk_abstract_pullback [A B C f g P] CP : rename.
Global Arguments abstract_pullback_vertex [A B C f g] PB : rename.
Global Arguments abstract_pullback_cone [A B C f g] PB : rename.

(* For convenience, one can specify a [abstract_pullback] just by its UP. *)
Definition mk_abstract_pullback' {A B C : Type} {f : A -> C} {g : B -> C}
  {P : Type} {CP : cospan_cone f g P} (CP_UP : is_pullback_cone CP)
  := (mk_abstract_pullback (existT _ CP CP_UP))
: abstract_pullback f g.

Definition standard_pullback {A B C : Type} (f : A -> C) (g : B -> C)
  := mk_abstract_pullback' (pullback_universal f g)
: abstract_pullback f g.

(* TODO (low): the following is currently broken due to a bug(?) with univ poly(?):
  Canonical Structure standard_pullback.
Once fixed, many references to [standard_pullback] below can be changed back to simply [pullback]. *)

(* TODO (high): improve the following section to better reflect the paper?? *)
Lemma is_pullback_cone_resp_equiv {A B C : Type} {f : A -> C} {g : B -> C}
  {P P' : Type} (e : P' <~> P) (CP : cospan_cone f g P)
: is_pullback_cone CP -> is_pullback_cone (map_to_cospan_cone CP P' e).
Proof.
  intros CP_UP X.
  set (e1 := isequiv_postcompose X e).
  apply (@isequiv_compose _ _ _ e1 _ _ (CP_UP X)).
Qed.

(* [pullback_cone f g X] is functorial along equivalences in [X]. *)
Lemma pullback_cone_fequiv {A B C : Type} {f : A -> C} {g : B -> C}
  {P P' : Type} (e : P' <~> P)
: pullback_cone f g P -> pullback_cone f g P'.
Proof.
  intros CP.
  exists (map_to_cospan_cone CP P' e).
  apply is_pullback_cone_resp_equiv.
  exact (pullback_cone_UP CP).
Defined.

Lemma equiv_pullback_to_pullback_cone {A B C : Type} {f : A -> C} {g : B -> C}
  {P : Type} (e : P <~> (pullback f g))
: pullback_cone f g P.
Proof.
  apply (pullback_cone_fequiv e).
  exists (pullback_cospan_cone f g).
  apply pullback_universal.
Defined.

Lemma abstract_pullback_equiv_cospan_cone_1 {A B C : Type}
  {f : A -> C} {g : B -> C} (P : abstract_pullback f g)
: P <~> (cospan_cone f g Unit).
Proof.
  equiv_via (Unit -> P).
    apply well_pointedness.
  exists (map_to_cospan_cone P Unit).
  apply pullback_cone_UP.
Defined.

Lemma abstract_pullback_unique {A B C : Type} {f : A -> C} {g : B -> C}
  (PB1 PB2 : abstract_pullback f g)
: PB1 <~> PB2.
Proof.
  equiv_via (cospan_cone f g Unit).
    apply abstract_pullback_equiv_cospan_cone_1.
  apply equiv_inverse, abstract_pullback_equiv_cospan_cone_1.
Defined.

(* TODO (mid): we should really show if possible, that this map is the same as the (unique by construction) map that takes the cone of PB2 to the cone of PB1. *)

End Pullback_UP_facts.


(*******************************************************************************

The main goal of the next few sections is to prove functoriality of
the standard pullback construction.

For this, we first need to define and show some basic properties of
*aps of cospans*; these follow from the analogous results about
commutative squares.

*******************************************************************************)

Section Cospan_maps.

Record cospan_map
  {A B C : Type} (f : A -> C) (g : B -> C)
  {A' B' C' : Type} (f' : A' -> C') (g' : B' -> C')
:= mk_cospan_map
  { cospan_map_A : A -> A';
    cospan_map_B : B -> B';
    cospan_map_C : C -> C';
    cospan_map_f : f' o cospan_map_A == cospan_map_C o f;
    cospan_map_g : g' o cospan_map_B == cospan_map_C o g }.

Global Arguments cospan_map_A [A B C f g A' B' C' f' g'] k a : rename.
Global Arguments cospan_map_B [A B C f g A' B' C' f' g'] k b : rename.
Global Arguments cospan_map_C [A B C f g A' B' C' f' g'] k c : rename.
Global Arguments cospan_map_f [A B C f g A' B' C' f' g'] k a : rename.
Global Arguments cospan_map_g [A B C f g A' B' C' f' g'] k b : rename.
Global Arguments mk_cospan_map [A B C f g A' B' C' f' g'] kA kB kC kf kg :
  rename.

Record cospan_map_homot
  {A B C : Type} {f : A -> C} {g : B -> C}
  {A' B' C' : Type} {f' : A' -> C'} {g' : B' -> C'}
  {k1 k2 : cospan_map f g f' g'}
:= mk_cospan_map_homot
  { cospan_map_homot_A : cospan_map_A k1 == cospan_map_A k2;
    cospan_map_homot_B : cospan_map_B k1 == cospan_map_B k2;
    cospan_map_homot_C : cospan_map_C k1 == cospan_map_C k2;
    cospan_map_homot_f : forall a:A,
                         cospan_map_f k1 a @ cospan_map_homot_C (f a)
                       = ap f' (cospan_map_homot_A a) @ cospan_map_f k2 a;
    cospan_map_homot_g : forall b:B,
                         cospan_map_g k1 b @ cospan_map_homot_C (g b)
                       = ap g' (cospan_map_homot_B b) @ cospan_map_g k2 b}.

Global Arguments cospan_map_homot [A B C f g A' B' C' f' g'] k1 k2.
Global Arguments mk_cospan_map_homot [A B C f g A' B' C' f' g'] k1 k2
  _ _ _ _ _.

Lemma cospan_map_homot_to_path   {A B C : Type} {f : A -> C} {g : B -> C}
  {A' B' C' : Type} {f' : A' -> C'} {g' : B' -> C'}
  {k1 k2 : cospan_map f g f' g'}
  (h : cospan_map_homot k1 k2)
: k1 = k2.
Proof.
  destruct k1 as [k1_A k1_B k1_C k1_f k1_g],
           k2 as [k2_A k2_B k2_C k2_f k2_g],
           h as [hA hB hC hf hg]. simpl in *.
  revert hA hB hC hf hg.
  equiv_intro (@apD10 _ _ k1_A k2_A) hA.
  equiv_intro (@apD10 _ _ k1_B k2_B) hB.
  equiv_intro (@apD10 _ _ k1_C k2_C) hC.
  intros hf hg.
  destruct hA, hB, hC. simpl in *.
  assert (p : k1_f = k2_f).
    apply path_forall. intros x.
    exact ((concat_p1 _)^ @ hf _ @ concat_1p _).
  destruct p.
  assert (p : k1_g = k2_g).
    apply path_forall. intros x.
    exact ((concat_p1 _)^ @ hg _ @ concat_1p _).
  destruct p. exact 1.
Defined.

Definition cospan_idmap {A B C : Type} (f : A -> C) (g : B -> C)
  := mk_cospan_map (f := f) (g := g) idmap idmap idmap
    (fun _ => 1) (fun _ => 1)
: cospan_map f g f g.

Definition cospan_comp
  {A B C : Type} {f : A -> C} {g : B -> C}
  {A' B' C' : Type} {f' : A' -> C'} {g' : B' -> C'}
  {A'' B'' C'' : Type} {f'' : A'' -> C''} {g'' : B'' -> C''}
: cospan_map f' g' f'' g'' -> cospan_map f g f' g'
  -> cospan_map f g f'' g''
:= fun h k => mk_cospan_map
    (cospan_map_A h o cospan_map_A k)
    (cospan_map_B h o cospan_map_B k)
    (cospan_map_C h o cospan_map_C k)
    (comm_square_comp (cospan_map_f h) (cospan_map_f k))
    (comm_square_comp (cospan_map_g h) (cospan_map_g k)).

(* Important fact: a cospan map whose components are equivalences is itself
   an equivalence in the category of cospans. *)
Lemma cospan_equiv_inverse
  {A B C : Type} {f : A -> C} {g : B -> C}
  {A' B' C' : Type} {f' : A' -> C'} {g' : B' -> C'}
  (w : cospan_map f g f' g')
  (is_eq_wA : IsEquiv (cospan_map_A w))
  (is_eq_wB : IsEquiv (cospan_map_B w))
  (is_eq_wC : IsEquiv (cospan_map_C w))
: cospan_map f' g' f g.
Proof.
  set (wA := BuildEquiv is_eq_wA).
  set (wB := BuildEquiv is_eq_wB).
  set (wC := BuildEquiv is_eq_wC).
  apply (mk_cospan_map (wA^-1) (wB^-1) (wC^-1)).
  apply (@comm_square_inverse _ _ _ _ _ _ wA wC (cospan_map_f w)).
  apply (@comm_square_inverse _ _ _ _ _ _ wB wC (cospan_map_g w)).
Defined.

Lemma cospan_inverse_is_section
  {A B C : Type} (f : A -> C) (g : B -> C)
  {A' B' C' : Type} (f' : A' -> C') (g' : B' -> C')
  (w : cospan_map f g f' g')
  (is_eq_wA : IsEquiv (cospan_map_A w))
  (is_eq_wB : IsEquiv (cospan_map_B w))
  (is_eq_wC : IsEquiv (cospan_map_C w))
: cospan_comp w (cospan_equiv_inverse w is_eq_wA is_eq_wB is_eq_wC) =
  cospan_idmap f' g'.
Proof.
  apply cospan_map_homot_to_path.
  set (wA := BuildEquiv is_eq_wA).
  set (wB := BuildEquiv is_eq_wB).
  set (wC := BuildEquiv is_eq_wC).
  exists (eisretr wA) (eisretr wB) (eisretr wC); simpl.
  (* Square from [f] to [f']. *)
    intros a. apply (concatR (concat_p1 _)^).
    apply (comm_square_inverse_is_retr wA wC _ a).
  (* Square from [g] to [g']. *)
    intros b. apply (concatR (concat_p1 _)^).
    apply (comm_square_inverse_is_retr wB wC _ b).
Defined.

Lemma cospan_inverse_is_retraction
  {A B C : Type} (f : A -> C) (g : B -> C)
  {A' B' C' : Type} (f' : A' -> C') (g' : B' -> C')
  (w : cospan_map f g f' g')
  (is_eq_wA : IsEquiv (cospan_map_A w))
  (is_eq_wB : IsEquiv (cospan_map_B w))
  (is_eq_wC : IsEquiv (cospan_map_C w))
: cospan_comp (cospan_equiv_inverse w is_eq_wA is_eq_wB is_eq_wC) w =
    cospan_idmap f g.
Proof.
  apply cospan_map_homot_to_path.
  set (wA := BuildEquiv is_eq_wA).
  set (wB := BuildEquiv is_eq_wB).
  set (wC := BuildEquiv is_eq_wC).
  exists (eissect wA) (eissect wB) (eissect wC). simpl.
  (* Square from [f] to [f']. *)
    intros a. apply (concatR (concat_p1 _)^).
    apply (comm_square_inverse_is_sect wA wC _ a).
  (* Square from [g] to [g']. *)
    intros b. apply (concatR (concat_p1 _)^).
    apply (comm_square_inverse_is_sect wB wC _ b).
  (* Require [comm_square_inverse_is_sect]. *)
Defined.

End Cospan_maps.


(*******************************************************************************

Functoriality of the standard pullback.

*******************************************************************************)

Section Pullbacks_Functoriality.

(* Functoriality of pullback *)
Lemma pullback_fmap
  {A B C : Type} {f : A -> C} {g : B -> C}
  {A' B' C' : Type} {f' : A' -> C'} {g' : B' -> C'}
: cospan_map f g f' g'
  -> pullback f g -> pullback f' g'.
Proof.
  intros k abp. set (a := pullback_pr1 abp); set (b := pullback_pr2 abp).
  apply (mk_pullback f' g' (cospan_map_A k a) (cospan_map_B k b)).
  path_via' (cospan_map_C k (f a)). apply cospan_map_f.
  path_via' (cospan_map_C k (g b)). apply ap, pullback_comm. 
  apply inverse, cospan_map_g.
Defined.

Lemma pullback_fmap_id
  {A B C : Type} (f : A -> C) (g : B -> C)
  : pullback_fmap (cospan_idmap f g) == idmap.
Proof.
  intros abp. apply pullback_path'.
  exists 1, 1. simpl.
  unfold pullback_comm, pullback_pr2; simpl. hott_simpl.
Defined.

(* TODO (low): a better associativity tactic would vastly simplify this
   proof! 
   TODO (low): rewrite to avoid destructing? *)
Lemma pullback_fmap_comp
  {A B C : Type} (f : A -> C) (g : B -> C)
  {A' B' C' : Type} (f' : A' -> C') (g' : B' -> C')
  {A'' B'' C'' : Type} (f'' : A'' -> C'') (g'' : B'' -> C'')
  (h : cospan_map f' g' f'' g'') (k : cospan_map f g f' g')
: pullback_fmap (cospan_comp h k)
  == (pullback_fmap h) o (pullback_fmap k).
Proof.
  destruct h as [hA hB hC hf hg], k as [kA kB kC kf kg].
  intros [a [b p]]. unfold cospan_comp, compose; simpl.
  apply pullback_path'. simpl.
  exists 1, 1. simpl.
  apply (concat (concat_p1 _)), (concat (concat_1p _)).
  unfold pullback_comm, pullback_pr2; simpl.
  unfold comm_square_comp.
  apply (concat (concat_pp_p)), whiskerL.
  apply (concatR (whiskerR (ap_pp hC _ _)^ _)).
  apply (concatR (concat_p_pp)), whiskerL.
  path_via' (ap hC (ap kC p) @ ap hC (kg b)^ @ (hg (kB b))^).
    apply (concatR (concat_p_pp)).
    apply concat2.
      apply (ap_compose kC hC).
    apply (concat (inv_pp _ _)), whiskerR. 
    apply inverse, ap_V.
  apply whiskerR, inverse, ap_pp.
Defined.

End Pullbacks_Functoriality.


(*******************************************************************************

Functoriality of pullbacks along equivalences.

The general form can be deduced from the general functoriality of pullbacks.

*******************************************************************************)

Section Pullbacks_Equiv_Functoriality.

Lemma pullback_fmap_isequiv
  {A B C : Type} (f : A -> C) (g : B -> C)
  {A' B' C' : Type} (f' : A' -> C') (g' : B' -> C')
  (w : cospan_map f g f' g')
  (ewA : IsEquiv (cospan_map_A w))
  (ewB : IsEquiv (cospan_map_B w))
  (ewC : IsEquiv (cospan_map_C w))
: IsEquiv (pullback_fmap w).
Proof.
  set (w_inv := cospan_equiv_inverse w ewA ewB ewC).
  apply isequiv_adjointify with (pullback_fmap w_inv).
  (* is_section *)
  intros y.
  path_via (pullback_fmap (cospan_comp w w_inv) y).
    apply inverse. apply pullback_fmap_comp.
  path_via (pullback_fmap (cospan_idmap f' g') y).
    apply ap10. apply ap.
    apply cospan_inverse_is_section.
  apply pullback_fmap_id.
  (* is_retraction *)
  intros x.
  path_via (pullback_fmap (cospan_comp w_inv w) x).
    apply inverse. apply pullback_fmap_comp.
  path_via (pullback_fmap (cospan_idmap f g) x).
    apply ap10. apply ap.
    apply cospan_inverse_is_retraction.
  apply pullback_fmap_id.
Qed.

Lemma pullback_fmap_equiv
  {A B C : Type} (f : A -> C) (g : B -> C)
  {A' B' C' : Type} (f' : A' -> C') (g' : B' -> C')
  (w : cospan_map f g f' g')
  (ewA : IsEquiv (cospan_map_A w))
  (ewB : IsEquiv (cospan_map_B w))
  (ewC : IsEquiv (cospan_map_C w))
: pullback f g <~> pullback f' g'.
Proof.
  exists (pullback_fmap w). apply pullback_fmap_isequiv; assumption.
Defined.

(* A handy re-currying of [pullback_fmap_equiv], allowing arguments to be
   given one at a time. *)
Lemma pullback_fmap_equiv'
  {A B C : Type} (f : A -> C) (g : B -> C)
  {A' B' C' : Type} (f' : A' -> C') (g' : B' -> C')
: { wA : A -> A'
    & { ewA : IsEquiv wA
    & { wB : B -> B'
    & { ewB : IsEquiv wB
    & { wC : C -> C'
    & { ewC : IsEquiv wC
    & { wf : f' o wA == wC o f
    &       g' o wB == wC o g
    }}}}}}}
  -> pullback f g <~> pullback f' g'.
Proof.
  intros [wA [ewA [wB [ewB [wC [ewC [wf wg]]]]]]].
  set (w := mk_cospan_map wA wB wC wf wg).
  apply pullback_fmap_equiv with w; assumption.
Defined.

Lemma pullback_resp_equiv_A
  {A B C : Type} (f : A -> C) (g : B -> C)
  {A' : Type} (w : A <~> A')
: pullback f g <~> pullback (f o (equiv_inv w)) g.
Proof.
  apply (pullback_fmap_equiv _ _ _ _
    (@mk_cospan_map _ _ _ _ _ _ _ _ (f o (w ^-1)) g
    w idmap idmap
    (fun a => ap f (eissect w a)) (fun b => 1)));
  simpl.
  apply equiv_isequiv. apply isequiv_idmap. apply isequiv_idmap.
Defined.

End Pullbacks_Equiv_Functoriality.


(*******************************************************************************

The two pullbacks lemma(ta).

Here we show (the “concrete” version) that the standardly-constructed
double pullback is equal to the standardly-constructed one-step pullback.

In Pullbacks3.v, we show (the “abstract” form) that given any pair of suitably
composable squares, if the right-hand square is a pullback, then the outer
rectangle is if and only if the left-hand square is.

*******************************************************************************)


(******************************************************************************

To show: when we package a cone up into a map and then unpack it,
we recover the components of the original cone.

*******************************************************************************)

Section cospan_cones_vs_UP_pullback.

Definition packed_cospan_cone_map1
  {A B C : Type} {f : A -> C} {g : B -> C} (P : abstract_pullback f g)
  {X : Type} (CX : cospan_cone f g X)
  (P_UP_at_X := BuildEquiv (pullback_cone_UP P X))
: (cospan_cone_map1 P) o (P_UP_at_X ^-1 CX) = cospan_cone_map1 CX.
Proof.
  change (compose (cospan_cone_map1 P)) with (cospan_cone_map1 o P_UP_at_X).
  unfold compose. apply ap, eisretr.
Defined.

Definition packed_cospan_cone_map2
  {A B C : Type} {f : A -> C} {g : B -> C} (P : abstract_pullback f g)
  {X : Type} (CX : cospan_cone f g X)
  (P_UP_at_X := BuildEquiv (pullback_cone_UP P X))
: (cospan_cone_map2 P) o (P_UP_at_X ^-1 CX) = cospan_cone_map2 CX.
Proof.
  change (compose (cospan_cone_map2 P)) with (cospan_cone_map2 o P_UP_at_X).
  unfold compose. apply ap, eisretr.
Defined.

Definition packed_cospan_cone_comm
  {A B C : Type} {f : A -> C} {g : B -> C} (P : abstract_pullback f g)
  {X : Type} (CX : cospan_cone f g X)
  (P_UP_at_X := BuildEquiv (pullback_cone_UP P X))
: forall x:X,
    (cospan_cone_comm P (P_UP_at_X ^-1 CX x))
  =
    (ap f (ap10 (packed_cospan_cone_map1 _ CX) x))
    @ (cospan_cone_comm CX x)
    @ (ap g (ap10 (packed_cospan_cone_map2 _ CX) x))^.
Proof.
  intros x.
  change (cospan_cone_comm P (P_UP_at_X ^-1 CX x))
  with (cospan_cone_comm (P_UP_at_X (P_UP_at_X ^-1 CX)) x).
  apply (cospan_cone_path_comm (eisretr P_UP_at_X CX)).
Defined.

End cospan_cones_vs_UP_pullback.


(*******************************************************************************
The *concrete* two pullbacks lemma:

This lemma states that given maps

                A
                |f
                V
B2 -h-> B1 -g-> C

the (standard) pullback of the overall rectangle, [pullback f (g o h)],
is equivalent to the pullback constructed in two steps.
*******************************************************************************)

Section Concrete_Two_Pullbacks_Lemma.

Context {A B1 B2 C : Type} (f : A -> C) (g : B1 -> C) (h : B2 -> B1).

Definition outer_to_double_pullback
: (pullback f (g o h)) -> (pullback (g ^* f) h).
Proof.
  intros adp.
  exists (mk_pullback f g (pullback_pr1 adp) (h (pullback_pr2 adp))
          (pullback_comm adp)).
  exists (pullback_pr2 adp). exact 1.
Defined.

Definition double_to_outer_pullback
: (pullback (g ^* f) h) -> (pullback f (g o h)).
Proof.
  intros abpdq.
  exists (pullback_pr1 (pullback_pr1 abpdq)),
         (pullback_pr2 (abpdq)).
  path_via (g (pullback_pr2 (pullback_pr1 abpdq))).
    apply pullback_comm.
  unfold compose. apply ap, pullback_comm.
Defined.

Lemma two_pullbacks_isequiv: IsEquiv (outer_to_double_pullback).
Proof.
  apply (isequiv_adjointify double_to_outer_pullback).
  (* is_section *)
  intros [[a [b p]] [d q]]. unfold pullback_pr2 in q; simpl in q.
  apply pullback_path'.
  exists (pullback_path (a; (h d; p @ ap g q)) (a; (b; p)) 1 q^  
    (concat_pp_p @ concat_1p _ @ (whiskerL _ (ap_V _ _))
       @ concat_pp_V p (ap g q))).
  exists 1.
  apply (concat (concat_p1 _)), (concat (concat_p1 _)).
  apply (concatR (inv_V _)), ap.
  apply (pullback_path_pr2 (a; (h d; p @ ap g q)) (a; (b; p))).
  (* is_retraction *)
  unfold compose. intros [a [d p]]. simpl. 
  apply pullback_path'. exists 1, 1. simpl.
  apply (concat (concat_p1 _)), (concat (concat_1p _)).
  apply concat_p1.
Qed.

Definition two_pullbacks_equiv
  : (pullback f (g o h)) <~> (pullback (g ^* f) h)
:= BuildEquiv two_pullbacks_isequiv.

End Concrete_Two_Pullbacks_Lemma.

(*
Local Variables:
coq-prog-name: "hoqtop"
End:
*)
