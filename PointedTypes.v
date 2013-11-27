(*******************************************************************************

Title: PointedTypes.v
Authors: Jeremy Avigad, Chris Kapulkin, Peter LeFanu Lumsdaine
Date: 1 March 2013

Defines pointed types, and some key constructions thereon.

*******************************************************************************)

Require Import HoTT.

Require Import Auxiliary Pullbacks Pullbacks2.


(*******************************************************************************

Pointed types.

*******************************************************************************)

(* TODO (high): consistentize use of capital letters, throughout development *)
Section Pointed_Types.

Record pointed_type := mk_pointed_type {
  pt_type :> Type;
  point : pt_type }.

Global Arguments point [X] : rename.

Record pointed_map (X Y : pointed_type) := mk_pointed_map {
  pt_map :> X -> Y;
  pt_map_pt : pt_map point = point }.

Global Arguments pt_map_pt [X Y] f : rename.
Global Arguments mk_pointed_map [X Y] f alpha : rename.

Record pointed_htpy {X Y} (f g : pointed_map X Y)
:= mk_pointed_htpy {
  pt_htpy :> f == g;
  pt_htpy_pt : pt_htpy point = (pt_map_pt f) @ (pt_map_pt g)^ }.

Global Arguments pt_htpy [X Y f g] H x : rename.
(* [pt_htpy] seems not to work as coercion.  TODO: investigate? *)
Global Arguments pt_htpy_pt [X Y f g] H : rename.
Global Arguments mk_pointed_htpy [X Y f g] H Hpt : rename.

End Pointed_Types.

Notation "A .-> B" := (pointed_map A B)
  (at level 75, right associativity) : type_scope.

Notation "f .== g" := (pointed_htpy f g)
  (at level 70, no associativity) : type_scope.

(* A quick notation for using maps that *definitionally* preserve
  the point as pointed maps. *)
Notation "[ 'defpointed' f ]" := {| pt_map := f; pt_map_pt := 1 |}
  (at level 40).
(* Note: this often doesn't work, e.g. for the pointed pullback projections.
TODO: understand better why not! *)

(*******************************************************************************

More on pointed maps.

*******************************************************************************)

Section Pointed_Maps.

Definition pointed_map_ptd (X Y : pointed_type)
:= mk_pointed_type (X .-> Y) ([defpointed (fun _ => point)]).

Canonical Structure pointed_map_ptd.

Definition idmap_ptd (X : pointed_type) : pointed_map X X
:= {| pt_map := idmap ; pt_map_pt := 1 |}.

(* Can't make [idmap_ptd] a Canonical Structure, since [idmap] neither is nor
resolves to an identifier; it's a notation, resolving to [ (fun x => x) ].) *)
 
Definition compose_ptd {X Y Z} (f : Y .-> Z) (g : X .-> Y)
:= {| pt_map := f o g ; pt_map_pt := (ap f (pt_map_pt g) @ pt_map_pt f) |}.

Canonical Structure compose_ptd.
(* Doesn't seem to work, e.g. in [is_exact] below.  TODO (low): investigate? 
TODO (mid): in meantime, make better notation for this??  Problem:
none of the obvious candidates [f .o g], [f o. g], [f o.o g] work, due
to Coq's special treatment of the period. *)

Definition composeR_ptd {X Y Z} (g : X .-> Y) (f : Y .-> Z)
:= compose_ptd f g.

Definition compose_1f_ptd {X Y} (f : X .-> Y)
  : compose_ptd (idmap_ptd _) f .== f.
Proof.
  destruct f as [f fp].
  exists ((fun x => 1) : (idmap o f) == f).
  simpl. apply moveL_pV.
  exact (concat_1p _ @ (ap_idmap _)^ @ (concat_p1 _)^). 
Defined.

Definition compose_f1_ptd {X Y} (f : X .-> Y)
  : compose_ptd f (idmap_ptd _) .== f.
Proof.
  destruct f as [f fp].
  exists ((fun x => 1) : (f o idmap) == f). 
  simpl. apply moveL_pV. exact 1.
Defined.

Definition concat_ptd_htpy {X Y} {f g h : X.-> Y}
  : (f .== g) -> (g .== h) -> (f .== h).
Proof.
  intros H J.
  exists (fun x => pt_htpy H x @ pt_htpy J x).
  apply (concat (concat2 (pt_htpy_pt H) (pt_htpy_pt J))).
  apply (concat concat_pp_p), whiskerL.
  apply concat_V_pp.
Defined.

Definition concatR_ptd_htpy {X Y} {f g h : X.-> Y}
  : (g .== h) -> (f .== g) -> (f .== h)
:= (fun H J => concat_ptd_htpy J H).

Definition inverse_ptd_htpy {X Y} {f g : X.-> Y}
  : (f .== g) -> (g .== f).
Proof.
  intros H.
  exists (fun x => (pt_htpy H x)^).
  apply (concat (ap inverse (pt_htpy_pt H))). apply inv_pV.
Defined.

(* This lemma and the next are, logically speaking, redundant: they are
simply aliases for [isequiv_compose] acting on the underlying functions
of a pointed composite.

However, when working with a large composite, these save a lot of time,
since Coq can recognise where to break the pointed composite, rather than
having to unfold [compose_ptd] and try multiple break-points in the under-
lying map. *)
Lemma isequiv_compose_ptd {X Y Z} (f:Y.->Z) (g:X.->Y) 
  : IsEquiv f -> IsEquiv g -> IsEquiv (compose_ptd f g).
Proof.
  intros; apply isequiv_compose.
Defined.

Lemma isequiv_composeR_ptd {X Y Z} (g:X.->Y) (f:Y.->Z) 
  : IsEquiv g -> IsEquiv f -> IsEquiv (composeR_ptd g f).
Proof.
  intros; apply isequiv_compose.
Defined.

(* Useful fact: the inverse of a pointed equivalence is also pointed. *)
Definition equiv_inverse_ptd {A B} (f : A .-> B) {f_iseq : IsEquiv f}
  : B .-> A.
Proof.
  exists (f ^-1).
  apply equiv_inj.
  exact (eisretr _ _ @ (pt_map_pt f)^).
Defined.

Canonical Structure equiv_inverse_ptd.

(* The equivalence produced by [equiv_path] on an equality of pointed types
is always pointed. *)
Lemma equiv_path_ptd {X Y : pointed_type} (p : X = Y)
  : X .-> Y.
Proof.
  exists (equiv_path X Y (ap pt_type p)); simpl. 
  refine ((transport_compose _ _ _ _)^ @ _).
  apply apD.
Defined.

End Pointed_Maps.


(*******************************************************************************

Some examples of pointed types.

*******************************************************************************)

Section Pointed_Types_Examples.

Definition Unit_ptd : pointed_type
  := mk_pointed_type Unit tt.

Canonical Structure Unit_ptd.

Definition name_point {X : pointed_type} : Unit_ptd .-> X
  := [ defpointed (name point) ].

Canonical Structure name_point.

Definition hfiber_ptd {X Y : pointed_type} (f : X .-> Y) : pointed_type
:= mk_pointed_type (hfiber f point) (point; pt_map_pt f).

Canonical Structure hfiber_ptd.

Definition hfiber_incl_ptd {X Y : pointed_type} (f : X .-> Y)
  : (hfiber_ptd f) .-> X
:= @mk_pointed_map (hfiber_ptd f) X (hfiber_incl f point) 1.

Definition hfiber_null {X Y : pointed_type} (f : X .-> Y)
  : compose_ptd f (hfiber_incl_ptd f) .== point.
Proof.
  exists (fun xp => pr2 xp); simpl.
  apply inverse. exact (concat_p1 _ @ concat_1p _).
Defined.

End Pointed_Types_Examples.

Section Pointed_Pullbacks.

Definition pullback_ptd {A B C} (f : A .-> C) (g : B .-> C) : pointed_type
:= mk_pointed_type (pullback f g)
  (point; (point; (pt_map_pt f @ (pt_map_pt g)^))).

Canonical Structure pullback_ptd.

Definition pullback_ptd_pr1 {A B C} (f : A .-> C) (g : B .-> C)
  : (pullback_ptd f g) .-> A.
Proof. 
  exists pullback_pr1. exact 1.
Defined.

Definition pullback_ptd_pr2 {A B C} (f : A .-> C) (g : B .-> C)
  : (pullback_ptd f g) .-> B.
Proof. 
  exists pullback_pr2. exact 1.
Defined.

Definition hfiber_to_pullback_ptd {X Y : pointed_type} (f : X .-> Y)
  : (hfiber_ptd f) .-> pullback_ptd f name_point.
Proof.
  exists (hfiber_to_pullback f point).
  apply pullback_path'. exists 1; exists 1.
  unfold pullback_comm; simpl. apply whiskerR, concat_1p.
Defined.

Lemma hfiber_to_pullback_ptd_factn {X Y : pointed_type} (f:Y.->X)
  : compose_ptd (pullback_ptd_pr1 f name_point) (hfiber_to_pullback_ptd f)
  .== compose_ptd (idmap_ptd Y) (hfiber_incl_ptd f).
Proof.
  exists ((fun y => 1)
    : ((pullback_ptd_pr1 f name_point) o (hfiber_to_pullback_ptd f)
      == hfiber_incl_ptd f)).
  apply inverse, moveR_pV.
  change (1 @ pt_map_pt (hfiber_incl_ptd f)) with (@idpath _ (@point Y)).
  apply (concat (concat_p1 _)).
  simpl.
  exact (pullback_path'_pr1
    (hfiber_to_pullback f point (point; pt_map_pt f))
    (point; (tt; pt_map_pt f @ 1)) _).
Defined.

Record ptd_cospan_map
  {A B C} (f : A .-> C) (g : B .-> C)
  {A' B' C'} (f' : A' .-> C') (g' : B' .-> C')
:= mk_ptd_cospan_map
  { ptd_cospan_map_A : A .-> A';
    ptd_cospan_map_B : B .-> B';
    ptd_cospan_map_C : C .-> C';
    ptd_cospan_map_f : compose_ptd f' ptd_cospan_map_A .== compose_ptd ptd_cospan_map_C f;
    ptd_cospan_map_g : compose_ptd g' ptd_cospan_map_B .== compose_ptd ptd_cospan_map_C g }.

Global Arguments ptd_cospan_map_A [A B C f g A' B' C' f' g'] k : rename.
Global Arguments ptd_cospan_map_B [A B C f g A' B' C' f' g'] k : rename.
Global Arguments ptd_cospan_map_C [A B C f g A' B' C' f' g'] k : rename.
Global Arguments ptd_cospan_map_f [A B C f g A' B' C' f' g'] k : rename.
Global Arguments ptd_cospan_map_g [A B C f g A' B' C' f' g'] k : rename.
Global Arguments mk_ptd_cospan_map [A B C f g A' B' C' f' g'] kA ckB kC kf kg :
  rename.

Definition cospan_map_of_ptd_cospan_map
  {A B C} {f : A .-> C} {g : B .-> C}
  {A' B' C'} {f' : A' .-> C'} {g' : B' .-> C'}
  : ptd_cospan_map f g f' g' -> cospan_map f g f' g'
:= (fun M => mk_cospan_map
    (ptd_cospan_map_A M)
    (ptd_cospan_map_B M)
    (ptd_cospan_map_C M)
    (ptd_cospan_map_f M)
    (ptd_cospan_map_g M)).

Coercion cospan_map_of_ptd_cospan_map : ptd_cospan_map >-> cospan_map.

(*TODO (low): this seems unnecessarily painful!  Simplify??*)
Lemma pullback_ptd_fmap
  {A B C} {f : A .-> C} {g : B .-> C}
  {A' B' C'} {f' : A' .-> C'} {g' : B' .-> C'}
: ptd_cospan_map f g f' g'
  -> (pullback_ptd f g .-> pullback_ptd f' g').
Proof.
  intros M.
  exists (pullback_fmap M).
  apply pullback_path'; simpl.
    exists (pt_map_pt _).
    exists (pt_map_pt _).
  unfold pullback_comm; simpl. unfold pullback_pr2, pullback_comm; simpl.
  set (MA := ptd_cospan_map_A M).
  set (MB := ptd_cospan_map_B M).
  set (MC := ptd_cospan_map_C M).
  set (Mf := ptd_cospan_map_f M).
  set (Mg := ptd_cospan_map_g M).
(* Modulo algebra, the essential content of the prood from here on is just
[pt_htpy_pt Mf] and [pt_htpy_pt Mg]. *)
  apply moveR_pM, moveR_Vp.
  apply (concat (whiskerR (pt_htpy_pt Mf) _)). simpl; fold Mf MA MC.
  apply (concat concat_pp_p), (concat concat_pp_p), whiskerL.
  apply (concatR concat_p_pp), whiskerL. apply moveR_Vp.
  apply (concat (whiskerR (ap_pp MC _ _) _)).
  apply (concat concat_pp_p), (concatR concat_p_pp), whiskerL.
  apply moveR_pV, moveL_Mp, inverse.
  apply (concat (pt_htpy_pt Mg)). simpl; fold MB MC Mg.
  apply (concat (whiskerL _ (inv_pp _ _))).
  apply (concat concat_p_pp).
  apply inverse, concat2. Focus 2. apply ap_V.
  apply (concat (inv_pp _ _)). apply whiskerR.
  apply (concat (inv_pp _ _)). apply concat2; apply inv_V.
Defined.

(*TODO (low): this seems unnecessarily painful!  Simplify??*)
Definition outer_to_double_pullback_ptd {A B1 B2 C}
  (f : A .-> C) (g : B1 .-> C) (h : B2 .-> B1)
: (pullback_ptd f (compose_ptd g h)) .-> (pullback_ptd (pullback_ptd_pr2 f g) h).
Proof.
  exists (outer_to_double_pullback f g h).
  apply pullback_path'. 
    assert ((1 @ (pt_map_pt f @ (ap g (pt_map_pt h) @ pt_map_pt g) ^)) @ ap g (pt_map_pt h)
             = pt_map_pt f @ (pt_map_pt g) ^) as H.
      apply moveR_pM.
      apply (concat (concat_1p _)).
      apply (concatR concat_p_pp).
      apply whiskerL. apply inv_pp.
    exists (pullback_path
      (point; (h point; (pt_map_pt f @ (ap g (pt_map_pt h) @ pt_map_pt g) ^)))
      (point; (point; pt_map_pt f @ (pt_map_pt g) ^))
      1 (pt_map_pt h) H).
    exists 1.
  path_via' ((pt_map_pt h)^
     @ pullback_comm (outer_to_double_pullback f g h point)
     @ 1).
    apply whiskerR, whiskerR, ap.
    apply pullback_path_pr2.
   unfold pullback_comm; simpl.
   apply (concatR (concat_1p _)^).
   refine (concat_p1 _ @ concat_p1 _).
Defined.

Definition pullback_ptd_symm {A B C} (f : A .-> C) (g : B .-> C)
  : pullback_ptd f g .-> pullback_ptd g f.
Proof.
  exists (pullback_symm f g).
  apply pullback_path'.
  unfold pullback_symm; unfold pullback_pr2, pullback_comm; simpl.
  exists 1. exists 1. simpl.
  refine (concat_p1 _ @ concat_1p _ @ _). apply inv_pV.
Defined.

Definition pullback_ptd_symm_pr1 {A B C} (f : A .-> C) (g : B .-> C)
  : compose_ptd (pullback_ptd_pr1 g f) (pullback_ptd_symm f g)
    .== (pullback_ptd_pr2 f g).
Proof.
  exists ((fun p => 1)
    : pullback_pr1 o (pullback_symm f g) == pullback_pr2).
  apply inverse, moveR_pV.
  change (1 @ pt_map_pt (pullback_ptd_pr2 f g)) with (@idpath _ (@point B)).
  apply (concat (concat_p1 _)); simpl.
  apply (pullback_path'_pr1 (pullback_symm f g point) point).
Defined.

Definition pullback_ptd_symm_pr2 {A B C} (f : A .-> C) (g : B .-> C)
  : compose_ptd (pullback_ptd_pr2 g f) (pullback_ptd_symm f g)
    .== (pullback_ptd_pr1 f g).
Proof.
  exists ((fun p => 1)
    : pullback_pr2 o (pullback_symm f g) == pullback_pr1).
  apply inverse, moveR_pV.
  change (1 @ pt_map_pt (pullback_ptd_pr1 f g)) with (@idpath _ (@point A)).
  apply (concat (concat_p1 _)); simpl.
  apply (pullback_path'_pr2 (pullback_symm f g point) point).
Defined.

End Pointed_Pullbacks.

(*******************************************************************************

Some lemmas on (based) loop spaces, preparatory to the long exact
sequence. Based on the unpointed case, [Section Loops] in
Pullbacks2.v.

*******************************************************************************)

Section Omega_Ptd.

Definition Omega_ptd (A:pointed_type) : pointed_type
:= {| pt_type := Omega A point;
      point := idpath point |}.

(* Doesn't seem to work, eg in [Omega_ptd_fmap] below.  TODO: figure out issue? *)
Canonical Structure Omega_ptd.

Definition Omega_ptd_fmap {A B : pointed_type} (f : A .-> B)
: (Omega_ptd A) .-> (Omega_ptd B).
Proof.
  exists (Omega_conj (pt_map_pt f) o Omega_fmap point f).
  unfold Omega_conj, compose, concatR; simpl.
  path_via ((pt_map_pt f)^ @ pt_map_pt f).
  apply whiskerR, concat_p1.
  apply concat_Vp.
Defined.

Definition Omega_to_pullback_ptd (A : pointed_type)
  : Omega_ptd A .-> pullback_ptd (@name_point A) (name_point)
:= [defpointed Omega_to_pullback].

Instance isequiv_Omega_ptd_fmap {A B : pointed_type} (f : A .-> B)
  : IsEquiv f -> IsEquiv (Omega_ptd_fmap f).
Proof.
  intros f_iseq. apply isequiv_compose.
  (* [isequiv_Omega_conj] and [isequiv_Omega_fmap] found automagically *)
Defined.  

Fixpoint Omega_ptd_fmap_iterate {A B : pointed_type} (f : A .-> B) (n : nat)
  : (iterate Omega_ptd n A) .-> (iterate Omega_ptd n B)
:= match n with
    | O => f
    | (S n') => Omega_ptd_fmap (Omega_ptd_fmap_iterate f n')
   end.

End Omega_Ptd.

(*******************************************************************************

Exact pairs and sequences.

*******************************************************************************)

Section Exactness.

(* If [Z -g-> Y -f-> X] are pointed maps, a (pointed) nullhomotopy of the
composite induces a factorisation of [g] through the fiber of [f].  *)
Definition hfiber_factorisation {Z Y X}
  (g : Z .-> Y) (f : Y .-> X) (H : compose_ptd f g .== point)
: Z .-> (hfiber_ptd f).
Proof.
  exists (fun z => ((g z); (pt_htpy H) z)).
  apply total_path'; simpl.
    exists (pt_map_pt g).
  path_via ((ap f (pt_map_pt g))^ @ (pt_htpy H) point).
    refine ((transport_compose (fun x => (x = point)) _ _ _) @ _).
    apply transport_paths_l.
  apply moveR_Vp. apply (concat (pt_htpy_pt H)); simpl.
  apply concat_p1.
Defined.

(* TODO (mid): show that this is a factorisation of [g], i.e. that 
[compose_ptd (hfiber_incl f) (hfiber_factorisation g f H) .== g].  *)

(* A pair of pointed maps, together with a nullhomotopy of their composite,
is called "exact" if the induced map to the hfiber is an equivalence. *)
Definition is_exact {Z Y X} (g : Z .-> Y) (f : Y .-> X)
  (H : compose_ptd f g .== point)
:= IsEquiv (hfiber_factorisation g f H).
(* Note that this really can depend on [H], not just on [f] and [g].
Consider the sequence [Int -> 1 -> S1]: with the nullhomotopy
[fun n => loop ^n], it is exact, but with [fun _ => refl], it is not. *)

Definition is_exact_hfiber {Y X} (f : Y .-> X)
  : is_exact (hfiber_incl_ptd f) f (hfiber_null f).
Proof.
  unfold is_exact.
  apply isequiv_homotopic with (idmap_ptd _).
  apply isequiv_idmap.
  intros [y p]; exact 1.
Defined.

End Exactness.

(*
Local Variables:
coq-prog-name: "hoqtop"
End:
*)
