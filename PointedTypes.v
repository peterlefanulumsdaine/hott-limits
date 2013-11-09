(*******************************************************************************

Title: PointedTypes.v
Authors: Jeremy Avigad, Chris Kapulkin, Peter LeFanu Lumsdaine
Date: 1 March 2013

Defines pointed types, and some key constructions thereon.

*******************************************************************************)

Require Import HoTT.

Require Import Auxiliary Pullbacks2.


(*******************************************************************************

Pointed types.

*******************************************************************************)

(* TODO (high): consistentize use of capital letters, throughout development *)
Section Pointed_Types.

(* TODO (low): would these be better just as sigma-types, maybe? *)
Record pointed_type := mk_pointed_type {
  pt_type :> Type;
  point : pt_type }.

Record pointed_map (X Y : pointed_type) := mk_pointed_map {
  pt_map :> X -> Y;
  pt_map_pt : pt_map (point X) = point Y }.

Global Arguments pt_map_pt [X Y] f : rename.
Global Arguments mk_pointed_map [X Y] f alpha : rename.

Definition idmap_ptd (X : pointed_type) : pointed_map X X
:= {| pt_map := idmap ; pt_map_pt := 1 |}.

(* TODO (mid): category structure on maps. *)

End Pointed_Types.

Notation "A .-> B" := (pointed_map A B)
  (at level 75, right associativity).

(* A quick notation for using maps that *definitionally* preserve
  the point as pointed maps. *)
Notation "[ 'pointed' f ]" := {| pt_map := f; pt_map_pt := 1 |}
  (at level 40).


(*******************************************************************************

Some examples of pointed types.

*******************************************************************************)

Section Pointed_Types_Examples.

Definition Unit_Ptd : pointed_type
  := mk_pointed_type Unit tt.

Canonical Structure Unit_Ptd.

Definition hfiber_ptd {X Y : pointed_type} (f : X .-> Y) : pointed_type
:= mk_pointed_type (hfiber f (point Y)) (point X; pt_map_pt f).

(* TODO (mid): fix once this issue is cleared up. *)
(* Canonical Structure hfiber_ptd. *)

Definition hfiber_incl_ptd {X Y : pointed_type} (f : X .-> Y)
  : (hfiber_ptd f) .-> X
:= @mk_pointed_map (hfiber_ptd f) X (hfiber_incl f (point Y)) 1.

End Pointed_Types_Examples.


(*******************************************************************************

Some lemmas on (based) loop spaces, preparatory to the long exact
sequence. Based on the unpointed case, [Section Loops] in
Pullbacks2.v.

*******************************************************************************)

Section Omega_Ptd.

Definition Omega_ptd (A:pointed_type) : pointed_type
:= {| pt_type := Omega A (point A);
      point := idpath (point A) |}.

(* TODO (mid): fix once this issue is cleared up. *)
(* Canonical Structure Omega_Ptd. *)

Definition Omega_ptd_fmap {A B : pointed_type} (f : A .-> B)
: (Omega_ptd A) .-> (Omega_ptd B).
Proof.
  exists (fun p : Omega_ptd A => (pt_map_pt f)^ @ ap f p @ pt_map_pt f).
  path_via ((pt_map_pt f)^ @ pt_map_pt f).
  apply whiskerR, concat_p1.
  apply concat_Vp.
Defined.

Fixpoint Omega_ptd_fmap_iterate {A B : pointed_type} (f : A .-> B) (n : nat)
  : (iterate Omega_ptd n A) .-> (iterate Omega_ptd n B)
:= match n with
    | O => f
    | (S n') => Omega_ptd_fmap (Omega_ptd_fmap_iterate f n')
   end.

End Omega_Ptd.

(*
Local Variables:
coq-prog-name: "hoqtop"
End:
*)
