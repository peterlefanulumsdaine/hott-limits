(*******************************************************************************

Title: Fundamentals.v
Authors: Jeremy Avigad, Chris Kapulkin, Peter LeFanu Lumsdaine
Date: 1 March 2013

Gives the fundamental constructions of fibration categories (as
defined in K. Brown 1973, Abstract Homotopy Theory and Generalized
Sheaf Cohomology), within type theory.

*******************************************************************************)

Require Import HoTT EquivalenceVarieties.
Require Import Auxiliary.

(*******************************************************************************

Each homotopy fiber of the total space of a fibration is weakly equivalent to
the corresponding fiber of the original fibration.

*******************************************************************************)

Section Fibration_Equiv.

Definition fiber_to_hfiber {A : Type} (B : A -> Type) (a : A) 
  : (B a) -> (hfiber (@projT1 A B) a)
  := (fun (b : B a) => ((a;b); 1)).

Lemma fiber_to_hfiber_isequiv {A : Type} (B : A -> Type) (a : A)
  : IsEquiv (fiber_to_hfiber B a).
Proof.
  set (hfiber_to_fiber := fun (w : hfiber (@projT1 A B) a)
    => match w with ((a';b');p) => transport _ p b' end).
  apply (isequiv_adjointify hfiber_to_fiber).
    intros [[a' b'] p]. destruct p. exact 1.
  intros b. simpl. exact 1.
Qed.

Definition fiber_to_hfiber_equiv {A : Type} (B : A -> Type) (a : A)
  : (B a) <~> (hfiber (@projT1 A B) a)
:= BuildEquiv (fiber_to_hfiber_isequiv B a).

End Fibration_Equiv.

(*******************************************************************************

Acyclic fibrations are stable under pullback.

*******************************************************************************)

Section Acyclic_Fibrations.

Lemma str_pullback_pres_acyclic_fib (A A' : Type) (f : A' -> A) (B : A -> Type)
: IsEquiv (@projT1 A B) -> IsEquiv (@projT1 A' (B o f)).
Proof.
  intros H. apply isequiv_fcontr. intros c.
  apply @contr_equiv' with (B (f c)).
    apply (fiber_to_hfiber_equiv (B o f)).
  apply @contr_equiv' with (hfiber (@projT1 A B) (f c)).
    apply equiv_inverse, fiber_to_hfiber_equiv.
  apply fcontr_isequiv, H.
Qed.

End Acyclic_Fibrations.


(*******************************************************************************

The (strict) pullback of a weak equivalence along a fibration is again a weak
equivalence.

*******************************************************************************)

Section Right_Proper.

(* Maps have strict pullbacks along fibrations. *)
Definition str_pullback_along_fib {A A' : Type} (B : A -> Type) (f : A' -> A)
: {x:A' & B (f x)} -> {x:A & B x}.
Proof.
  intros [a' b]. exact (existT B (f a') b).
Defined.

Lemma str_pullback_along_fib_inv {A A' : Type} (B : A -> Type) (f : A' <~> A)
: {x:A & B x} -> {x:A' & B (f x)}.
Proof.
  intros [a b]. exists (equiv_inv f a).
  apply (transport _ (inverse (eisretr f a))). apply b.
Defined.

(* The strict pullback of an equivalence is an equivalence. *)
Lemma right_properness {A A' : Type} (B : A -> Type) (f : A' <~> A)
: IsEquiv (str_pullback_along_fib B f).
Proof.
  apply (isequiv_adjointify (str_pullback_along_fib_inv B f)).
  (* is_section *)
  intros [a b]; simpl.
  apply total_path'. exists (eisretr f a); simpl.
  apply transport_pV.
  (* is_retraction *)
  intros [c b]. simpl.
  apply total_path'. simpl. exists (eissect f c).
  apply (concat (transport_compose B f _ _)).
  apply (concat (transport_pp _ _ _ b)^).
  apply (@ap _ _ (fun p => p # b) _ 1).
  apply (concatR (concat_Vp (ap f (eissect f c)))).
  apply whiskerR, ap, eisadj.
Qed.

Notation str_pullback_along_fib_isequiv := right_properness.

End Right_Proper.


(******************************************************************************

Every map factors into a weak equivalence followed by a fibration.

Note: somewhat redundant with material in [Section FibrationReplacement] in
[UsefulEquivalences.v.]

*******************************************************************************)

Section Factorization.

Definition fib_factn {A B : Type} (f : A -> B) : Type :=
  { y : B & { x : A & (f x) = y }}.

Definition fib_factn_path' {A B : Type} (f : A -> B) {u v : fib_factn f}
: { p : pr1 u = pr1 v
    & { q : pr1 (pr2 u) = pr1 (pr2 v)
    & pr2 (pr2 u) @ p = (ap f q) @ pr2 (pr2 v) }}
  -> u = v.
Proof.
  destruct u as [b1 [a1 p1]], v as [b2 [a2 p2]]. simpl.
  intros [p [q r]]. destruct p, q. simpl.
  apply ap, ap. exact ((concat_p1 _)^ @ r @ (concat_1p _)).
Defined.

Definition fib_factn_incl {A B : Type} (f : A -> B)
  : A -> fib_factn f
:= (fun x : A => existT _ (f x) (existT _ x 1)).

Lemma factorization_1_isequiv {A B : Type} (f : A -> B)
: IsEquiv (fib_factn_incl f).
Proof.
  apply (isequiv_adjointify (fun (u : fib_factn f) => pr1 (pr2 u))).
  (* is_section *)
  intros [b [a p]]. simpl.
  apply (fib_factn_path' f). simpl.
  exists p. exists 1. exact 1.
  (* is_retraction *)
  intros a. exact 1.
Qed.

End Factorization.

(*******************************************************************************

The path space is weakly equivalent to the [fib_factn] of the diagonal map.

*******************************************************************************)

Definition Delta {A : Type} (a:A) := (a,a).

Section Factorization_Compare.

Definition paths_to_fib_factn {A : Type}
: path_space A -> fib_factn (@Delta A).
Proof.
  intros [x [y e]]. unfold fib_factn.
  exists (x,y). exists y.
  destruct e. exact 1.
Defined.

Definition fib_factn_to_paths {A : Type}
: fib_factn (@Delta A) -> path_space A.
Proof.
  intros [[x y] [z pq]].
  set (p := ap fst pq). simpl in p.
  set (q := @ap (A*A) A snd _ _ pq). simpl in q.
  exists x. exists y. exact (p^ @ q).
Defined.

Lemma paths_to_fib_factn_isequiv {A : Type}
: IsEquiv (@paths_to_fib_factn A).
Proof.
  apply (isequiv_adjointify (fib_factn_to_paths)).
    intros [xy [z pq]]. destruct pq. simpl. exact 1.
  intros [x [y e]]. destruct e. simpl. exact 1.
Qed.

End Factorization_Compare.


(******************************************************************************

Various facts on weak equivalences.

*******************************************************************************)

Section Equivalences.

(*******************************************************************************
The 2 out of 3 property for equivalences: given a pair of maps
A --f-> B --g-> C, if any two of f, g, and (g o f) are equivalences, then so
is the third.

Note: these already exist as library functions, under different names;
we restate them here for just the sake of visibility.
*******************************************************************************)

Definition equiv_two_of_three_composite {X Y Z : Type} (f: X -> Y) (g: Y -> Z)
  : IsEquiv f -> IsEquiv g -> IsEquiv (g o f)
:= (fun _ _ => isequiv_compose).

Definition equiv_two_of_three_left {X Y Z : Type} (f: X -> Y) (g: Y -> Z)
  : IsEquiv f -> IsEquiv (g o f) -> IsEquiv g
:= (fun _ _ => Equivalences.cancelR_isequiv g).

Definition equiv_two_of_three_right {X Y Z : Type} (f: X -> Y) (g: Y -> Z)
  : IsEquiv g -> IsEquiv (g o f) -> IsEquiv f
:= (fun _ _ => Equivalences.cancelL_isequiv f).

(*******************************************************************************
2 out of 6: a strengthening of the 2 out of 3 property,
stating that in a chain [h o g o f], if [h o g] and [g o f] are both weak
equivalences, then so are [h], [g], [f], and [h o g o f].
*******************************************************************************)

Lemma two_of_six_hgf {X Y Z W : Type} (f: X -> Y) (g: Y -> Z) (h: Z -> W)
: IsEquiv (h o g) -> IsEquiv (g o f) -> IsEquiv (h o g o f).
Proof.
  intros hg_iseq gf_iseq.
  apply isequiv_adjointify with ((g o f) ^-1 o g o (h o g) ^-1).
  (* is_section *)
  intros y. unfold compose; simpl.
  path_via (h ( g ((h o g) ^-1 y))).
    apply ap. apply (eisretr (g o f)).
    apply (eisretr (h o g)).
  (* is_retraction *)
  intros x. unfold compose; simpl.
  path_via ((g o f) ^-1 (g (f x))).
    repeat apply ap. apply (eissect (h o g)).
    apply (eissect (g o f)).
Qed.

Lemma two_of_six_h {X Y Z W : Type} (f: X -> Y) (g: Y -> Z) (h: Z -> W)
: IsEquiv (h o g) -> IsEquiv (g o f) -> IsEquiv h.
Proof.
  intros hg_iseq gf_iseq.
  apply isequiv_adjointify with (g o (h o g) ^-1).
  (* is_section *)
  intros w. apply (eisretr (h o g)).
  (* is_retraction *)
  intros z.
  path_via ((g o (h o g) ^-1) (h (g (f ((g o f)^-1 z))))).
    apply ap, ap, inverse, (eisretr (g o f)).
  path_via (g (f ((g o f)^-1 z))).
    apply (ap g), (eissect (h o g)).
  apply (eisretr (g o f)).
Qed.

Lemma two_of_six_g {X Y Z W : Type} (f: X -> Y) (g: Y -> Z) (h: Z -> W)
: IsEquiv (h o g) -> IsEquiv (g o f) -> IsEquiv g.
Proof.
  intros hg_iseq gf_iseq.
  apply equiv_biinv; split.
  (* left inverse*) exists ((h o g)^-1 o h). apply eissect.
  (* right inverse*) exists (f o (g o f)^-1). apply (eisretr (g o f)).
Qed.

Lemma two_of_six_f {X Y Z W : Type} (f: X -> Y) (g: Y -> Z) (h: Z -> W)
: IsEquiv (h o g) -> IsEquiv (g o f) -> IsEquiv f.
Proof.
  intros hg_iseq gf_iseq.
  apply isequiv_adjointify with ((g o f) ^-1 o g).
  (* is_section *)
  intros y.
  apply (concat (eissect (h o g) _)^).
  apply (fun p => p @ (eissect (h o g) y)).
  apply (ap (h o g)^-1), (ap h), (eisretr (g o f)).
  (* is_retraction *)
  apply (eissect (g o f)).
Qed.

End Equivalences.

(*
Local Variables:
coq-prog-name: "hoqtop"
End:
*)
