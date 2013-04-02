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
Section PointedTypes.

(* TODO (low): would these be better just as sigma-types, maybe? *)
Record PointedType := {
  PT_type :> Type;
  point : PT_type }.

Record PointedMap (X Y : PointedType) := {
  PT_map :> X -> Y;
  PT_map_pt : PT_map (point X) = point Y }.

Global Arguments PT_map_pt [X Y] f : rename.
Global Arguments Build_PointedMap [X Y] f alpha : rename.

Definition idmap_ptd (X:PointedType) : PointedMap X X
:= {| PT_map := idmap ; PT_map_pt := 1 |}.

(* TODO (mid): category structure on aps. *)

End PointedTypes.

Notation "A .-> B" := (PointedMap A B)
  (at level 75, right associativity).

(* A quick notation for using aps that *definitionally* preserve
  the point as pointed aps. *)
Notation "[ 'pointed' f ]" := {| PT_map := f; PT_map_pt := 1 |}
  (at level 40).


(*******************************************************************************

Some examples of pointed types.

*******************************************************************************)

Section PointedTypes_Examples.

Definition Unit_Ptd : PointedType
  := Build_PointedType Unit tt.

Canonical Structure Unit_Ptd.

Definition hfiber_ptd {X Y : PointedType} (f : X .-> Y) : PointedType
:= Build_PointedType (hfiber f (point Y)) (point X; PT_map_pt f).

(* TODO (mid): fix once this issue is cleared up. *)
(* Canonical Structure hfiber_ptd. *)

Definition hfiber_incl_ptd {X Y : PointedType} (f : X .-> Y)
  : (hfiber_ptd f) .-> X
:= @Build_PointedMap (hfiber_ptd f) X (hfiber_incl f (point Y)) 1.

End PointedTypes_Examples.


(*******************************************************************************

Some lemmas on (based) loop spaces, preparatory to the long exact
sequence. Based on the unpointed case, [Section Loops] in
Pullbacks2.v.

*******************************************************************************)

Section Omega_Ptd.

Definition Omega_Ptd (A:PointedType) : PointedType
:= {| PT_type := Omega A (point A);
      point := idpath (point A) |}.

(* TODO (mid): fix once this issue is cleared up. *)
(* Canonical Structure Omega_Ptd. *)

Definition Omega_Ptd_fmap {A B : PointedType} (f : A .-> B)
: (Omega_Ptd A) .-> (Omega_Ptd B).
Proof.
  exists (fun p : Omega_Ptd A => (PT_map_pt f)^ @ ap f p @ PT_map_pt f).
  path_via ((PT_map_pt f)^ @ PT_map_pt f).
  apply whiskerR, concat_p1.
  apply concat_Vp.
Defined.

Fixpoint Omega_Ptd_fmap_iterate {A B : PointedType} (f : A .-> B) (n : nat)
  : (iterate Omega_Ptd n A) .-> (iterate Omega_Ptd n B)
:= match n with
    | O => f
    | (S n') => Omega_Ptd_fmap (Omega_Ptd_fmap_iterate f n')
   end.

End Omega_Ptd.

(*
Local Variables:
coq-prog-name: "hoqtop"
End:
*)
