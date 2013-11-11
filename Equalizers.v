(*******************************************************************************

Title: Equalizers.v
Authors: Jeremy Avigad, Chris Kapulkin, Peter LeFanu Lumsdaine
Date: 1 March 2013

Basic results on equalizers. Just a stub for now; given a file of its
own since it is used in both [Limits.v] and [Pullbacks.v], which are
otherwise independent.

*******************************************************************************)

Require Import HoTT.
Require Import Auxiliary.

Section Equalizers.

Definition equalizer {A B : Type} (f : A -> B) (g : A -> B)
  := { x:A & (f x) = (g x) }.

End Equalizers.

(*
Local Variables:
coq-prog-name: "hoqtop"
End:
*)
