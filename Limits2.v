(*******************************************************************************

Title: Limits2.v
Authors: Jeremy Avigad, Chris Kapulkin, Peter LeFanu Lumsdaine
Date: 1 March 2013

More on limits, following Limits.v

*******************************************************************************)

Require Import HoTT.HoTT.

Require Import Arith.

Require Import Auxiliary Equalizers Limits1 Pullbacks.


(*******************************************************************************

Examples

As examples, we show that the pullbacks and equalizers of the previous
section can equivalently be constructed as instances of the general
[limit].

*******************************************************************************)

Section Limit_Examples.


(*******************************************************************************

Pullbacks

*******************************************************************************)

Section Pullback_as_Limit.

Inductive cospan_graph_0 : Type :=
  cosp_left | cosp_mid | cosp_right.

Definition cospan_graph_1 (i j : cospan_graph_0) : Type
:= match (i,j) with
       | (cosp_left,cosp_mid) => Unit
       | (cosp_right,cosp_mid) => Unit
       | _ => Empty
     end.

Definition cosp_left_leg : cospan_graph_1 cosp_left cosp_mid
:= tt.

Definition cosp_right_leg : cospan_graph_1 cosp_right cosp_mid
:= tt.

Definition cospan_graph : graph
:= Build_graph cospan_graph_0 cospan_graph_1.

Definition cg_diag_from_cospan {A B C : Type} (f : A -> C) (g : B -> C)
: diagram cospan_graph.
Proof.
  set (cg_diag_0 :=
    fun (v:cospan_graph) => match v with
      cosp_left => A | cosp_right => B | cosp_mid => C end).
  exists cg_diag_0. intros [ | | ] [ | | ] y; destruct y.
  exact f. exact g.
Defined.

Definition cg_diag_A (D : diagram cospan_graph) := D (cosp_left).

Definition cg_diag_B (D : diagram cospan_graph) := D (cosp_right).

Definition cg_diag_C (D : diagram cospan_graph) := D (cosp_mid).

Definition cg_diag_f D : cg_diag_A D -> cg_diag_C D
:= D.1 cosp_left_leg.

Definition cg_diag_g D : cg_diag_B D -> cg_diag_C D
:= D.1 cosp_right_leg.

Definition pb_as_lim {A B C} (f : A -> C) (g : B -> C)
:= limit (cg_diag_from_cospan f g).

Definition pb_as_lim_to_pullback {A B C} (f : A -> C) (g : B -> C)
: pb_as_lim f g -> pullback f g.
Proof.
  intros tau. unfold pb_as_lim in tau.
  exists (tau cosp_left). exists (tau cosp_right).
  path_via (tau cosp_mid).
    exact (lim_pr2 tau cosp_left_leg).
    exact ((lim_pr2 tau cosp_right_leg)^).
Defined.

Definition pullback_to_pb_as_lim {A B C} (f : A -> C) (g : B -> C)
: pullback f g -> pb_as_lim f g.
Proof.
  intros [a [b p]].
  exists (fun v => match v return (cg_diag_from_cospan f g v) with
    cosp_left => a | cosp_right => b | cosp_mid => f a end).
  intros [ | | ] [ | | ] y; destruct y; simpl.
  exact 1. exact (p^).
Defined.

Definition pb_as_lim_equiv {A B C} (f : A -> C) (g : B -> C)
: (pullback f g) <~> (pb_as_lim f g).
Proof.
  exists (pullback_to_pb_as_lim f g).
  apply (isequiv_adjointify (pb_as_lim_to_pullback f g)).
  (* is_section *)
  intros x. apply limit_homot_to_path.
  unfold limit_homot.
  exists (fun v => match v return (lim_pr1
     (pullback_to_pb_as_lim f g (pb_as_lim_to_pullback f g x)) v)
     = (lim_pr1 x v)
  with
    | cosp_left => 1 | cosp_right => 1
    | cosp_mid => (lim_pr2 x cosp_left_leg) end).
  intros [ | | ] [ | | ] y; destruct y; simpl.
    exact 1.
    set (pl := lim_pr2 x cosp_left_leg).
    set (pr := lim_pr2 x cosp_right_leg).
    apply (concat (concat_1p _)).
    path_via' ((pr @ inverse pl) @ pl).
      apply (concatR (concat_p_pp)).
      apply (concat (concat_p1 _)^).
      apply ap, inverse, concat_Vp.
      apply whiskerR.
    symmetry. apply inv_pV.
  (* is_retraction *)
  intros [a [b p]]. apply pullback_path'.
    exists 1. exists 1.
  unfold pb_as_lim_to_pullback, pullback_to_pb_as_lim; simpl.
  unfold pullback_path; simpl. path_via (p^^).
  apply (concat (concat_p1 _)).
  apply (concat (concat_1p _)).
  exact (concat_1p _).
Defined.

End Pullback_as_Limit.


(*******************************************************************************

Equalizer as limit.

*******************************************************************************)

Section Equalizer_as_Limit.

(* TODO (low): use these, or just bool? *)
Inductive equalizer_graph_0 : Type :=
  eq_source | eq_target.

Inductive equalizer_arrows : Type :=
  eq_left | eq_right.

Definition equalizer_graph_1 (i j : equalizer_graph_0) : Type
  := match (i, j) with
       | (eq_source, eq_target) => equalizer_arrows
       | _ => Empty
     end.

Definition equalizer_left_arrow : equalizer_graph_1 eq_source eq_target
:= eq_left.

Definition equalizer_right_arrow : equalizer_graph_1 eq_source eq_target
:= eq_right.

Definition equalizer_graph : graph
:= Build_graph equalizer_graph_0 equalizer_graph_1.

Definition eq_diag_from_arrows {A B : Type} (f g : A -> B)
: diagram equalizer_graph.
Proof.
  set (eq_diag_0 :=
    fun (v: equalizer_graph) => match v with
      eq_source => A | eq_target => B end).
  exists eq_diag_0. intros [ | ] [ | ] e; destruct e.
  exact f. exact g.
Defined.

Definition eq_diag_source (D : diagram equalizer_graph) := D eq_source.

Definition eq_diag_target (D : diagram equalizer_graph) := D eq_target.

Definition eq_diag_left (D : diagram equalizer_graph)
:= D.1 equalizer_left_arrow.

Definition eq_diag_right (D : diagram equalizer_graph)
:= D.1 equalizer_right_arrow.

Definition eq_as_lim {A B : Type} (f g : A -> B)
:= limit (eq_diag_from_arrows f g).

Definition eq_as_lim_to_equalizer {A B : Type} (f g : A -> B)
: eq_as_lim f g -> equalizer f g.
Proof.
  intros tau. unfold eq_as_lim in tau.
  exists (tau eq_source).
  apply (lim_pr2 tau equalizer_left_arrow
        @ (lim_pr2 tau equalizer_right_arrow)^).
Defined.

Definition equalizer_to_eq_as_lim {A B : Type} (f g : A -> B)
: equalizer f g -> eq_as_lim f g.
Proof.
  intros [a p].
  exists (fun v => match v return (eq_diag_from_arrows f g v) with
    eq_source => a | eq_target => f a end).
  intros [ | ] [ | ] y; destruct y; simpl.
  exact 1. exact (p^).
Defined.

Definition eq_as_lim_equiv {A B : Type} (f g : A -> B)
: (equalizer f g) <~> (eq_as_lim f g).
Proof.
  exists (equalizer_to_eq_as_lim f g).
  apply (isequiv_adjointify (eq_as_lim_to_equalizer f g)).
  (* is_section *)
  intros x. apply limit_homot_to_path.
  unfold limit_homot.
  exists (fun v => match v return
    (lim_pr1 (equalizer_to_eq_as_lim f g (eq_as_lim_to_equalizer f g x)) v) =
    (lim_pr1 x v) with
  | eq_source => 1
  | eq_target => (lim_pr2 x equalizer_left_arrow) end).
  intros [ | ] [ | ] y; destruct y; simpl.
    exact 1.
  apply (concat (concat_1p _)).
  rewrite inv_pV.
  rewrite concat_pp_p.
  rewrite concat_Vp.
  apply inverse; apply concat_p1.
  (* is_retraction *)
  intros [a p]. apply path_sigma_uncurried.
  exists 1. simpl.
  apply (concat_1p _ @ inv_V _).
Defined.

End Equalizer_as_Limit.


(*******************************************************************************

Limits over the natural numbers.

*******************************************************************************)

Section Nat_graph.

Definition nat_graph_1 (i j : nat) : Type
:= if (booleq_nat i (S j)) then Unit else Empty.

Definition nat_graph := Build_graph nat nat_graph_1.

End Nat_graph.

Section Nat_Limit_Facts.
(* TODO (mid): Think of some theorem(s) to give here?

E.g.: limit of a chain of n-equivalences is an n-equivalence.

*)
End Nat_Limit_Facts.

End Limit_Examples.


(*******************************************************************************

Limits over the natural numbers.

*******************************************************************************)

Section Trunc_Limits_Preserve_Trunc.

Lemma trunc_limits_preserve_trunc {G : graph} {D : diagram G} {n : nat}
  (hlnD : forall i : G, IsTrunc n (D i))
: IsTrunc n (limit D).
Proof.
  apply @trunc_sigma.
    apply trunc_forall; apply hlnD.
  intros a. apply (@trunc_forall _).
  intros v1. apply (@trunc_forall _).
  intros v2. apply (@trunc_forall _).
  intros e. apply trunc_succ.
Defined.

End Trunc_Limits_Preserve_Trunc.

(*
Local Variables:
coq-prog-name: "hoqtop"
End:
*)
