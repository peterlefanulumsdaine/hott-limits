(*******************************************************************************

Title: MWE.v
Authors: Jeremy Avigad, Chris Kapulkin, Peter LeFanu Lumsdaine
Date created: 6 Jan 2014

*Not a part of the HoTT-Limits library.*  This is a MWE extracted from the 
HoTT-Limits library, to demo in self-contained form a bug(?) encountered there.

Most of the file is background; the error is at [hfiber_null], the last sentence of the file.  Details of the errors are given there.

Produced over HoTT/HoTT@3500510.  Reported at https://coq.inria.fr/bugs/show_bug.cgi?id=3903.
*******************************************************************************)

Require Import HoTT.

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
Global Arguments pt_htpy_pt [X Y f g] H : rename.
Global Arguments mk_pointed_htpy [X Y f g] H Hpt : rename.

Notation "A .-> B" := (pointed_map A B)
  (at level 75, right associativity) : type_scope.

Notation "f .== g" := (pointed_htpy f g)
  (at level 70, no associativity) : type_scope.

Definition pointed_map_ptd (X Y : pointed_type)
:= mk_pointed_type (X .-> Y)
     {| pt_map := fun _ => point ; pt_map_pt := 1 |}.
 
Canonical Structure pointed_map_ptd.

Definition compose_ptd {X Y Z} (f : Y .-> Z) (g : X .-> Y)
:= {| pt_map := f o g ; pt_map_pt := (ap f (pt_map_pt g) @ pt_map_pt f) |}.

End Pointed_Types.

(* Redefining notations, to globalise them: *)
Notation "A .-> B" := (pointed_map A B)
  (at level 75, right associativity) : type_scope.
Notation "f .== g" := (pointed_htpy f g)
  (at level 70, no associativity) : type_scope.

Definition hfiber_ptd {X Y : pointed_type} (f : X .-> Y) : pointed_type
:= mk_pointed_type (hfiber f point) (point; pt_map_pt f).

Definition hfiber_pr1_ptd {X Y : pointed_type} (f : X .-> Y)
  : (hfiber_ptd f) .-> X
:= @mk_pointed_map (hfiber_ptd f) X pr1 1.

Definition hfiber_null {X Y : pointed_type} (f : X .-> Y)
  : compose_ptd f (hfiber_pr1_ptd f) .== point
:= @mk_pointed_htpy _ _
     (compose_ptd f (hfiber_pr1_ptd f))
     point
     (fun xp : hfiber_ptd f => pr2 xp)
     (concat_p1 _ @ concat_1p _)^. 

(* Without universe annotations, this definition errors:
 
> Error: Unsatisfied constraints: […]
> (maybe a bugged tactic).

If enough universe annotations are given, e.g. if in the statement of the definition, we add [pointed_type@{i}] and [point@{i}], then the error changes to 

> Anomaly: Uncaught exception Invalid_argument("index out of bounds").
> Please report.

If in the body of the definition, [point] is expanded to [ (@point (pointed_map_ptd (hfiber_ptd f) Y)) ], then the definition checks OK.
*)

(*
Local Variables:
coq-prog-name: "hoqtop"
End:
*)
