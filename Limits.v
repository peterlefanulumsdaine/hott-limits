(*******************************************************************************

Title: Limits.v
Authors: Jeremy Avigad, Chris Kapulkin, Peter LeFanu Lumsdaine
Date: 1 March 2013

The standard limit construction for limits over general (free categories
on) graphs, the abstract characterization of such limits, and properties of
both of these.

This file parallels Pullbacks.v.

*******************************************************************************)

Require Import HoTT.

Require Import Auxiliary.
Require Import CommutativeSquares Equalizers.

(*******************************************************************************

Graphs and diagrams on a graph.

*******************************************************************************)

Section Graphs.

Record graph :=
  { graph0 :> Type;
    graph1 :> graph0 -> graph0 -> Type }.

Record diagram (G : graph) :=
  { diagram0 :> G -> Type;
    diagram1 : forall (i j : G), G i j -> (diagram0 i -> diagram0 j) }.

Global Arguments diagram0 [G] D i : rename.
Global Arguments diagram1 [G] D [i j] f x : rename.

End Graphs.

Notation "D .1" := (@diagram1 _ D _ _) (at level 3).


(*******************************************************************************

Fix a graph for the rest of the file.

*******************************************************************************)

Section Limits.

Context {G : graph}.


(*******************************************************************************

The standard construction of a limit.

*******************************************************************************)

Section Concrete_Limits.

Definition limit (D : diagram G)
:= { x : forall i:G, D i
     & forall i j (f : G i j), D.1 f (x i) = x j }.

Definition lim_pr1 {D : diagram G} (x : limit D)
:= pr1 x.

Coercion lim_pr1 : limit >-> Funclass.

(* Explicitly named so that we can set implicit arguments  *)
Definition lim_pr2 {D : diagram G} (x : limit D) {i j} (f : G i j)
:= pr2 x i j f.

Definition mk_limit (D : diagram G) (x : forall i : G, D i)
  (alpha : forall i j (f : G i j), D.1 f (x i) = x j)
: limit D.
Proof.
  exists x. exact alpha.
Defined.

Definition limit_homot {D} (x y : limit D)
:= { alpha : lim_pr1 x == lim_pr1 y
     & forall i j (f : G i j),
       ap (D.1 f) (alpha i) @ lim_pr2 y f
       = lim_pr2 x f @ (alpha j) }.

Theorem limit_homot_to_path {D} (x y : limit D)
: limit_homot x y -> x = y.
Proof.
  intros alpha.
  set (alpha1 := pr1 alpha).
  set (alpha2 := pr2 alpha).
  apply (total_path (path_forall alpha1)).
  assert (transport_lemma
    : forall (p : pr1 x = pr1 y), p # pr2 x =
        (fun (i j:G) (f : G i j)
           => (ap ((D .1) f) (apD10 p i))^
              @ lim_pr2 x f
              @ (apD10 p j))).
    destruct x as [x1 x2], y as [y1 y2]. simpl.
    intros p. destruct p. simpl.
    apply path_forall. intros i. apply path_forall. intros j.
    apply path_forall. intros f.
    apply inverse. exact (concat_p1 _ @ concat_1p _).
  rewrite transport_lemma.
  (* Maybe: a tactic that does this sort of repeated application of path_forall
  automatically? *)
  apply path_forall. intros i. apply path_forall. intros j.
  apply path_forall. intros f.
  path_via' (((ap ((D .1) f) (apD10 (path_forall alpha1) i))^ @ lim_pr2 x f)
             @ alpha1 j).
    apply ap.  clear f; revert j. apply apD10. apply eisretr.
  path_via' (((ap ((D .1) f) (alpha1 i))^ @ lim_pr2 x f) @ alpha1 j).
    apply (ap (fun p => (((ap ((D .1) f) p)^ @ lim_pr2 x f) @ alpha1 j))).
    clear f; revert i. apply apD10. apply eisretr.
  path_via ((ap ((D .1) f) (alpha1 i))^ @ (lim_pr2 x f @ alpha1 j)).
  apply moveR_Mp.
  path_via' (ap ((D .1) f) (alpha1 i) @ lim_pr2 y f).
    apply inverse. apply alpha2.
  apply whiskerR. apply inverse, inv_V.
Defined.

(* TODO (low): show how [limit_homot_to_path] acts when apped under
projections (analogous to [pr1_total_path], etc). *)

End Concrete_Limits.


(*******************************************************************************

Graph cones, that is, cones on a diagram on G.
(The limit is a universal such cone.)

*******************************************************************************)

Section Graph_Cone.

Definition graph_cone (D : diagram G) (X : Type)
:= { tau : forall i : G, X -> D i
     & forall (i j : G) (f : G i j), (D.1 f o tau i) == tau j }.

Definition mk_graph_cone {D} {X} tau tau1 : graph_cone D X
:= existT _ tau tau1.

Definition graph_cone_pr1 {D : diagram G} {X} (tau : graph_cone D X)
  := pr1 tau.
Coercion graph_cone_pr1 : graph_cone >-> Funclass.

Definition graph_cone_pr2 {D : diagram G} {X} (tau: graph_cone D X)
  {i j} (f : G i j) (x:X)
:= pr2 tau i j f x.

Definition graph_cone_homot {D : diagram G} {X:Type}
  (sigma tau : graph_cone D X)
:= { alpha : forall i, sigma i == tau i
   & forall i j f x, graph_cone_pr2 sigma f x @ alpha j x
                     = ap (D.1 f) (alpha i x) @ graph_cone_pr2 tau f x}.

Definition graph_cone_homot_to_path {D : diagram G} {X:Type}
  {sigma tau : graph_cone D X} (alpha : graph_cone_homot sigma tau)
: sigma = tau.
Proof.
  destruct sigma as [sigma sigma1], tau as [tau tau1],
    alpha as [alpha alpha1]. simpl in alpha, alpha1.
  set (alpha' := path_forall (fun i => path_forall (alpha i))).
  assert (alpha1' : forall (i j : G) (f : G i j) (x : X),
           sigma1 i j f x @ (ap10 (apD10 alpha' j) x) =
           ap ((D .1) f) (ap10 (apD10 alpha' i) x) @ tau1 i j f x).
    intros i j f x.
    path_via (sigma1 i j f x @ alpha j x).
      apply (ap (fun p => sigma1 i j f x @ p)).
      path_via (ap10 (path_forall (alpha j)) x).
        apply (ap (fun p => ap10 p x)). unfold alpha'; simpl.
        apply (apD10_path_forall' (fun i => path_forall (alpha i))).
      apply (apD10_path_forall' (alpha j)).
    path_via (ap ((D .1) f) (alpha i x) @ tau1 i j f x).
      apply (ap (fun p => (ap ((D .1) f) p @ tau1 i j f x))).
      path_via (ap10 (path_forall (alpha i)) x).
        apply inverse. revert x. apply apD10, eisretr.
      apply (ap (fun p => ap10 p x)). apply inverse.
      apply (apD10_path_forall' (fun i => path_forall (alpha i))).
  generalize alpha' alpha1'. clear alpha alpha' alpha1 alpha1'.
  intros alpha' alpha1'. destruct alpha'. apply ap.
  simpl in alpha1'.
  apply path_forall; intros i. apply path_forall; intros j.
  apply path_forall; intros f. apply path_forall; intros x.
  apply (concat (concat_p1 _)^). apply (concatR (concat_1p _)).
  apply alpha1'.
Defined.

End Graph_Cone.


(*******************************************************************************

The universal property of pullbacks.

*******************************************************************************)

Section Limit_UP.

Definition map_to_graph_cone {D : diagram G}
  {X} (C : graph_cone D X) (Y:Type) (f : Y -> X)
: graph_cone D Y.
Proof.
  exists (fun i y => C i (f y)).
  intros i j a y. apply (graph_cone_pr2 C).
Defined.

Definition is_limit_cone {D : diagram G} {L} (C : graph_cone D L)
:= forall (X : UU), IsEquiv (map_to_graph_cone C X).

Definition limit_graph_cone (D : diagram G)
: graph_cone D (limit D).
Proof.
  exists (fun i x => x i).
  intros i j f x. unfold compose; simpl. exact (lim_pr2 x f).
Defined.

(* TODO: should D and X be implicit here and in the next definition?
   (Also in Pullbacks.) *)
Definition map_to_limit_to_graph_cone {D : diagram G} {X : Type}
  (m : X -> limit D)
  := map_to_graph_cone (limit_graph_cone D) _ m
: graph_cone D X.

Definition inv_map_to_limit_to_graph_cone
  {D : diagram G} {X} (C : graph_cone D X)
: (X -> limit D).
Proof.
  intros x. exists (fun i => C i x).
  intros i j f. apply (graph_cone_pr2 C).
Defined.

Lemma limit_universal (D : diagram G)
: is_limit_cone (limit_graph_cone D).
Proof.
  unfold is_limit_cone. intros X.
  apply (isequiv_adjointify (inv_map_to_limit_to_graph_cone)).
  (* is_section *)
  intros tau. apply graph_cone_homot_to_path.
  unfold map_to_graph_cone, limit_graph_cone, inv_map_to_limit_to_graph_cone;
    simpl.
  unfold graph_cone_homot; simpl.
  exists (fun i y => 1). simpl.
  intros i j f x. exact (concat_p1 _ @ (concat_1p _)^).
  (* is_retraction *)
  intros k. apply path_forall. intros x. apply limit_homot_to_path.
  unfold map_to_graph_cone, limit_graph_cone, inv_map_to_limit_to_graph_cone;
    simpl.
  unfold limit_homot; simpl.
  exists (fun i => 1). simpl.
  intros i j f. exact (concat_1p _ @ (concat_p1 _)^).
Defined.

(* TODO: lock this, as in pullbacks *)

End Limit_UP.


(*******************************************************************************

An equivalent, and small, formulation of the abstract limit property.

*******************************************************************************)

Section Limit_UP'.

Definition is_limit_cone' {D : diagram G} {L} (C : graph_cone D L)
:= IsEquiv (inv_map_to_limit_to_graph_cone C).

Lemma is_limit_cone'_to_is_limit_cone {D : diagram G} {L} (C : graph_cone D L)
: is_limit_cone' C -> is_limit_cone C.
Proof.
  intros C_is_limit'. unfold is_limit_cone, is_limit_cone' in *.
  intros X.
  assert (H : map_to_graph_cone C X
             = (map_to_graph_cone (limit_graph_cone D) X)
             o (fun g : X -> L => inv_map_to_limit_to_graph_cone C o g)).
    apply path_forall. intros f.
    apply graph_cone_homot_to_path. unfold graph_cone_homot. simpl.
    exists (fun i y => 1). simpl.
    intros. exact (concat_p1 _ @ (concat_1p _)^).
  rewrite H; clear H.
  apply @isequiv_compose.
  apply (equiv_postcompose (BuildEquiv C_is_limit')).
  apply limit_universal.
Qed.

Lemma is_limit_cone_to_is_limit_cone' {D : diagram G} {L} (C : graph_cone D L)
: is_limit_cone C -> is_limit_cone' C.
Proof.
  intros C_is_limit. unfold is_limit_cone, is_limit_cone' in *.
  set (e1 := (BuildEquiv (C_is_limit Unit))).
  set (e2 := equiv_inverse (BuildEquiv (limit_universal D Unit))).
  set (e := equiv_compose (equiv_inverse (well_pointedness (limit D)))
           (equiv_compose e2
           (equiv_compose e1
                          (well_pointedness L)))).
  assert (H : e == inv_map_to_limit_to_graph_cone C).
    intros x. apply limit_homot_to_path. unfold limit_homot.
    exists (fun i => 1). simpl.
    intros i j g. exact (concat_1p _ @ (concat_p1 _)^).
  apply (isequiv_homotopic _ _ H).
Defined.

End Limit_UP'.


(*******************************************************************************

Properties of limits in general, via U.P.’s.

*******************************************************************************)

Section Limit_UP_facts.

Definition limit_cone (D : diagram G) (L : Type)
  := { CL : graph_cone D L & is_limit_cone CL }.

Definition limit_cone_cone (D : diagram G) {L : Type} (CL : limit_cone D L)
:= pr1 CL : graph_cone D L.
Coercion limit_cone_cone : limit_cone >-> graph_cone.

Definition limit_cone_UP {D : diagram G} {L : Type} (CL : limit_cone D L)
:= pr2 CL : is_limit_cone CL.

Record abstract_limit (D : diagram G)
:= mk_abstract_limit
  { abstract_limit_vertex :> Type;
    abstract_limit_cone :> limit_cone D abstract_limit_vertex }.

Global Arguments mk_abstract_limit [D L] CL : rename.
Global Arguments abstract_limit_vertex [D] L : rename.
Global Arguments abstract_limit_cone [D] L : rename.

Definition mk_abstract_limit' {D : diagram G} {L : Type} {CL : graph_cone D L}
  (CL_UP : is_limit_cone CL)
  : abstract_limit D
:= (mk_abstract_limit (existT _ CL CL_UP)).

(* TODO (med): change back to Canonical Structure once bug fixed. *)
Definition standard_limit (D : diagram G) : abstract_limit D
:= mk_abstract_limit' (limit_universal D).

Lemma is_limit_cone_resp_equiv {D : diagram G} {L L' : Type} (e : L' <~> L)
    (CL: graph_cone D L)
  : is_limit_cone CL -> is_limit_cone (map_to_graph_cone CL L' e).
Proof.
  intros CL_UP X.
  apply (@isequiv_compose _ _ _ (isequiv_postcompose X e) _ _ (CL_UP X)).
Defined.

(* [limit_cone D X] is functorial along equivalences in [X] *)
Lemma limit_cone_fequiv {D : diagram G} {L L' : Type} (e : L' <~> L)
  : limit_cone D L -> limit_cone D L'.
Proof.
  intros CL.
  exists (map_to_graph_cone CL L' e).
  apply is_limit_cone_resp_equiv.
  exact (limit_cone_UP CL).
Defined.

Lemma equiv_limit_to_limit_cone {D : diagram G} {L : Type}
  (e : L <~> (limit D)) : limit_cone D L.
Proof.
  apply (limit_cone_fequiv e).
  exists (limit_graph_cone D).
  apply limit_universal.
Defined.

Lemma abstract_limit_equiv_graph_cone_1 {D : diagram G} {L : abstract_limit D}
  : L <~> (graph_cone D Unit).
Proof.
  equiv_via (Unit -> L).
    apply well_pointedness.
  exists (map_to_graph_cone L Unit).
  apply limit_cone_UP.
Defined.

Lemma abstract_limit_unique {D : diagram G} (L1 L2 : abstract_limit D)
: L1 <~> L2.
Proof.
  equiv_via (graph_cone D Unit).
    apply abstract_limit_equiv_graph_cone_1.
  apply equiv_inverse.
  apply abstract_limit_equiv_graph_cone_1.
Defined.

End Limit_UP_facts.


(*******************************************************************************

The main goal of the next few sections is to prove functoriality of
the standard limit construction. As in Pullbacks, we first prove
basic properties of maps of diagrams.

*******************************************************************************)

Section Diagram_maps.

Record diagram_map (D1 D2 : diagram G) :=
  mk_diagram_map
  { diagram_map_obj :> forall (i : G), D1 i -> D2 i;
    diagram_map_comm: forall (i j : G), forall (f : G i j),
      D2.1 f o diagram_map_obj i == diagram_map_obj j o D1.1 f }.

Global Arguments diagram_map_obj [D1 D2] m i x : rename.
Global Arguments diagram_map_comm  [D1 D2] m [i j] f x : rename.
Global Arguments mk_diagram_map [D1 D2] _ _.

Record diagram_map_homot {D1 D2 : diagram G}
  {m1 m2 : diagram_map D1 D2}
:= mk_diagram_map_homot
  {  diagram_map_homot_obj : forall (i : G), m1 i == m2 i;
     diagram_map_homot_comm : forall (i j : G), forall (f : G i j),
         forall (x : D1 i),
             diagram_map_comm m1 f x @ diagram_map_homot_obj j (D1.1 f x) =
             ap (D2.1 f) (diagram_map_homot_obj i x) @
                 diagram_map_comm m2 f x}.

Global Arguments diagram_map_homot [D1 D2] m1 m2.
Global Arguments mk_diagram_map_homot [D1 D2] m1 m2 _ _ .

Lemma diagram_map_homot_to_path {D1 D2 : diagram G}
  {m1 m2 : diagram_map D1 D2}
  (h : diagram_map_homot m1 m2)
: m1 = m2.
Proof.
  destruct m1 as [m1_obj m1_comm].
  destruct m2 as [m2_obj m2_comm].
  destruct h as [h_obj h_comm]. simpl in *.
  revert h_obj h_comm.
  (* TODO (mid): the following two steps wwer much easier over old library.
  Can that ease be recovered? *)
  set (E := (@equiv_functor_forall _
    G (fun i => m1_obj i = m2_obj i)
    G (fun i => m1_obj i == m2_obj i)
    idmap _
    (fun i => @apD10 _ _ (m1_obj i) (m2_obj i)))
    (fun i => isequiv_apD10 _ _ _ _)).
  equiv_intro E h_obj.
  revert h_obj.
  equiv_intro (@apD10 _ _ m1_obj m2_obj) h_obj.
  destruct h_obj. simpl.
  intros h_comm.
  assert (H : m1_comm = m2_comm).
    apply path_forall. intros i.
    apply path_forall. intros j.
    apply path_forall. intros f.
    apply path_forall. intros x.
    apply (concatR (concat_1p _)).
    apply (concatR (h_comm _ _ _ _)).
    apply inverse, concat_p1.
  destruct H. exact 1.
Defined.

Definition diagram_idmap (D : diagram G) : diagram_map D D
  := mk_diagram_map (fun _ => idmap) (fun _ _ _ _ => 1).

Definition diagram_comp {D1 D2 D3 : diagram G} (m2 : diagram_map D2 D3)
  (m1 : diagram_map D1 D2) : diagram_map D1 D3.
Proof.
  apply (mk_diagram_map (fun i => m2 i o m1 i)).
  intros i j f.
  exact (comm_square_comp (diagram_map_comm m2 f) (diagram_map_comm m1 f)).
Defined.

Lemma diagram_equiv_inverse
  {D1 D2 : diagram G} (w : diagram_map D1 D2)
  (is_eq_w : forall (i : G), IsEquiv (w i))
: diagram_map D2 D1.
Proof.
  apply (mk_diagram_map (fun i => (BuildEquiv (is_eq_w i))^-1)).
  intros i j f.
  apply (@comm_square_inverse _ _ _ _ _ _
    (BuildEquiv (is_eq_w i)) (BuildEquiv (is_eq_w j))).
  apply diagram_map_comm.
Defined.

Lemma diagram_inverse_is_section
  {D1 D2 : diagram G} (w : diagram_map D1 D2)
  (is_eq_w : forall (i : G), IsEquiv (w i))
: diagram_comp w (diagram_equiv_inverse w is_eq_w) = diagram_idmap D2.
Proof.
  apply diagram_map_homot_to_path.
  destruct w as [w_obj w_comm]. simpl in *.
  set (we i := BuildEquiv (is_eq_w i)).
  exists (fun i => eisretr (we i)).
  intros i j f x. apply (concatR (concat_p1 _)^).
  apply (comm_square_inverse_is_retr (we i) (we j) _ x).
Defined.

Lemma diagram_inverse_is_retraction
  {D1 D2 : diagram G} (w : diagram_map D1 D2)
  (is_eq_w : forall (i : G), IsEquiv (w i))
: diagram_comp (diagram_equiv_inverse w is_eq_w) w = diagram_idmap D1.
Proof.
  apply diagram_map_homot_to_path.
  destruct w as [w_obj w_comm]. simpl in *.
  set (we i := BuildEquiv (is_eq_w i)).
  exists (fun i => eissect (we i)). simpl.
  intros i j f x. apply (concatR (concat_p1 _)^).
  apply (comm_square_inverse_is_sect (we i) (we j) _ x).
Defined.

End Diagram_maps.


(*******************************************************************************

Functoriality of the standard limit.

*******************************************************************************)

Section Limit_Functoriality.

Lemma limit_fmap {D1 D2 : diagram G}
: diagram_map D1 D2 -> limit D1 -> limit D2.
Proof.
  intros [m1 m2] [l1 l2].
  exists (fun i => m1 i (l1 i)).
  intros i j f.
  apply ((m2 i j f (l1 i)) @ (ap (m1 j) (l2 i j f))).
Defined.

Lemma limit_fmap_id (D : diagram G)
: limit_fmap (diagram_idmap D) == idmap.
Proof.
  intros [l1 l2].
  apply limit_homot_to_path.
  exists (fun i => 1). simpl.
  intros i j f. rewrite concat_p1.
  apply inverse.
  apply ap_idmap.
Defined.

Lemma limit_fmap_comp {D1 D2 D3 : diagram G}
  (m2 : diagram_map D2 D3) (m1 : diagram_map D1 D2)
  : limit_fmap (diagram_comp m2 m1)
   == (limit_fmap m2) o (limit_fmap m1).
Proof.
  destruct m2 as [m2_obj m2_comm].
  destruct m1 as [m1_obj m1_comm].
  intros [l1 l2].
  apply limit_homot_to_path. unfold limit_homot. simpl.
  exists (fun i => 1). simpl.
  intros i j f.
  rewrite concat_p1.
  unfold comm_square_comp.
  rewrite ap_compose.
  rewrite ap_pp.
  apply (concat (concat_1p _)).
  apply concat_p_pp.
Defined.

End Limit_Functoriality.


(*******************************************************************************

Functoriality of limits along equivalences.

*******************************************************************************)

Section Limits_Equiv_Functoriality.

Lemma limit_fmap_isequiv
  (D1 D2 : diagram G)
  (w : diagram_map D1 D2)
  (is_eq_w : forall (i : G), IsEquiv (w i))
: IsEquiv (limit_fmap w).
Proof.
  set (w_inv := diagram_equiv_inverse w is_eq_w).
  apply isequiv_adjointify with (limit_fmap w_inv).
  (* is_section *)
  intros y.
  path_via (limit_fmap (diagram_comp w w_inv) y).
    apply inverse. apply limit_fmap_comp.
  path_via (limit_fmap (diagram_idmap D2) y).
    apply ap10. apply ap.
    apply diagram_inverse_is_section.
  apply limit_fmap_id.
  (* is_retraction *)
  intros x.
  path_via (limit_fmap (diagram_comp w_inv w) x).
    apply inverse. apply limit_fmap_comp.
  path_via (limit_fmap (diagram_idmap D1) x).
    apply ap10. apply ap.
    apply diagram_inverse_is_retraction.
  apply limit_fmap_id.
Qed.

Lemma limit_fmap_equiv
  (D1 D2 : diagram G)
  (w : diagram_map D1 D2)
  (is_eq_w : forall (i : G), IsEquiv (w i))
: limit D1 <~> limit D2.
Proof.
  exists (limit_fmap w).
  apply limit_fmap_isequiv; assumption.
Defined.

End Limits_Equiv_Functoriality.


(******************************************************************************

Construction of the limit using products and equalizers.

*******************************************************************************)

Section Limits_From_Products_And_Equalizers.

Definition lim_as_eq {G : graph} (D : diagram G) : Type
:= let prod1 := forall i:G, D i in
   let prod2 := forall (i j:G) (f:G i j), D j in
   let ap1 (x : prod1) {i j:G} (f:G i j) := (D .1 f) (x i) in
   let ap2 (x : prod1) {i j:G} (f:G i j) := x j in
   equalizer ap1 ap2.

(* TODO (low): Is there a way to make this a coercion!?  It’s late at night,
and I can’t see what the target class ought to be to do so.

TODO (low): move, if we can get this working as a coercion; delete, if not. *)
Definition equalizer_pr1 {X Y} {f g:X -> Y} (x : equalizer f g) : X
:= pr1 x.

Definition lim_as_eq_cone (D : diagram G)
: graph_cone D (lim_as_eq D).
Proof.
  unfold graph_cone.
  exists (fun i x => (pr1 x) i).
  intros i j f x. unfold compose.
  set (x2 := pr2 x). simpl in x2.
  apply (ap10 (apD10 (apD10 x2 i) j) f).
Defined.

Definition graph_cone_to_map_to_lim_as_eq {D : diagram G}
  {X:Type} (C : graph_cone D X)
: X -> lim_as_eq D.
Proof.
  intros x. unfold lim_as_eq.
  exists (fun i => C i x).
  apply path_forall; intros i. apply path_forall; intros j.
  apply path_forall; intros f. apply (pr2 C).
Defined.

Lemma lim_as_eq_UP (D : diagram G)
: is_limit_cone (lim_as_eq_cone D).
Proof.
  apply is_limit_cone'_to_is_limit_cone.
  apply (isequiv_adjointify (graph_cone_to_map_to_lim_as_eq
    (limit_graph_cone D))).
  (* is_section *)
  intros y. set (y0 := pr1 y). set (y1 := pr2 y).
  apply limit_homot_to_path. unfold limit_homot; simpl.
  exists (fun i => 1).
  simpl. intros. apply inverse.
  path_via (ap10 (apD10 (apD10
             (path_forall (fun i' : G =>
               (path_forall (fun j' : G =>
                 (path_forall (fun f' : G i' j' => y1 i' j' f'))))))
           i) j) f ).
  path_via (ap10 (apD10
             (path_forall (fun j' : G =>
               (path_forall (fun f' : G i j' => y1 i j' f')))) j) f).
    apply (ap (fun p : (fun (i' j' : G) (f' : G i' j') => (D .1) f' (y0 i')) i
                      = (fun (i' j' : G) (_ : G i' j') => y0 j') i
         => apD10 (apD10 p j) f)).
    clear f; revert i. apply apD10. apply eisretr.
  path_via (ap10 (path_forall (fun f' : G i j => y1 i j f')) f).
    apply (ap (fun p : (fun f' : G i j => (D .1) f' (y0 i))
                      = (fun f' : G i j => y0 j)
                => ap10 p f)).
    clear f; revert j. apply apD10. apply eisretr.
  apply (concatR (concat_1p _)^).
  revert f. apply apD10. apply eisretr.

  (* is_retraction *)
  intros [x0 x1].
  apply total_path'. simpl.
  exists 1. simpl.
  path_via (path_forall (fun i : G =>
             (path_forall (fun j : G =>
               (apD10 (apD10 x1 i) j))))).
    apply ap. apply path_forall. intros i.
    apply ap. apply path_forall. intros j.
    apply eissect.
  path_via (path_forall (apD10 x1)).
    apply ap. apply path_forall. intros i.
    apply eissect.
  apply eissect.
Qed.

End Limits_From_Products_And_Equalizers.

End Limits.


(*
Local Variables:
coq-prog-name: "hoqtop"
End:
*)
