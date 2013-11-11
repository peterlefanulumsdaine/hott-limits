(*******************************************************************************

Title: Arith.v
Authors: Jeremy Avigad, Chris Kapulkin, Peter LeFanu Lumsdaine
Date: 1 March 2013

This file contains some basic arithmetic, ported from Coq’s standard Peano.v.
(We cannot import that, since it is not all homotopy-compatible.)

Once the HoTT library contains its own development of arithmetic, this
file will be obsolete.

*******************************************************************************)

Require Import HoTT.
Require Import Auxiliary.

Open Scope nat_scope.

Hint Resolve (ap S): v62.
Hint Resolve (ap (A:=nat)): core.

(** Booleans *)
Inductive Bool : Type :=
  | true : Bool
  | false : Bool.

Definition is_true (b:Bool) : Type
  := match b with true => Unit | false => Empty end.

Definition true_neq_false : true = false -> Empty
  := (fun H => transport is_true H tt).

(** The predecessor function *)

Definition pred (n:nat) : nat := match n with
                                 | O => n
                                 | S u => u
                                 end.
Hint Resolve (ap pred): v62.

Theorem pred_Sn : forall n:nat, n = pred (S n).
Proof.
  simpl; reflexivity.
Defined.

(** Injectivity of successor *)

(* eq_add_S in Peano.v *)
Definition S_inj : forall {n m:nat}, S n = S m -> n = m.
Proof.
  intros n m p. apply (ap pred p).
Defined.
Hint Resolve S_inj: core.

Definition is_succ (n:nat) : Type :=
  match n with
  | O => Empty
  | S p => Unit
  end.

Definition is_zero (n:nat) : Type :=
  match n with
  | O => Unit
  | S p => Empty
  end.

(** Zero is not the successor of a number *)

Theorem O_neq_S {n:nat} : 0 = S n -> Empty.
Proof.
  intros p. apply (transport is_zero p). constructor.
Defined.

Hint Resolve O_neq_S: core.

Theorem n_Sn : forall n:nat, n = S n -> Empty.
Proof.
  induction n; auto; apply O_neq_S.
Defined.

Hint Resolve n_Sn: core.

(** Addition *)

Fixpoint plus (n m:nat) : nat :=
  match n with
  | O => m
  | S p => S (p + m)
  end

where "n + m" := (plus n m) : nat_scope.

Hint Resolve (ap10 o (ap plus)): v62.

Lemma plus_n_O : forall n:nat, n = n + 0.
Proof.
  induction n; simpl; auto.
Defined.
Hint Resolve plus_n_O: core.

Lemma plus_O_n : forall n:nat, 0 + n = n.
Proof.
  auto.
Defined.

Lemma plus_n_Sm : forall n m:nat, S (n + m) = n + S m.
Proof.
  intros n m; induction n; simpl; auto.
Defined.
Hint Resolve plus_n_Sm: core.

Lemma plus_Sn_m : forall n m:nat, S n + m = S (n + m).
Proof.
  auto.
Defined.

(** Standard associated names *)

Notation plus_0_r_reverse := plus_n_O (compat "8.2").
Notation plus_succ_r_reverse := plus_n_Sm (compat "8.2").

(** Multiplication *)

Fixpoint mult (n m:nat) : nat :=
  match n with
  | O => 0
  | S p => m + p * m
  end

where "n * m" := (mult n m) : nat_scope.

Hint Resolve (ap10 o (ap mult)): core.

Lemma mult_n_O : forall n:nat, 0 = n * 0.
Proof.
  induction n; simpl; auto.
Defined.
Hint Resolve mult_n_O: core.

Lemma mult_n_Sm : forall n m:nat, n * m + n = n * S m.
Proof.
  intros; induction n as [| p H]; simpl; auto.
  destruct H; rewrite <- plus_n_Sm; apply (ap S).
  pattern m at 1 3; elim m; simpl; auto.
Defined.
Hint Resolve mult_n_Sm: core.

(** Standard associated names *)

Notation mult_0_r_reverse := mult_n_O (compat "8.2").
Notation mult_succ_r_reverse := mult_n_Sm (compat "8.2").

(** Truncated subtraction: [m-n] is [0] if [n>=m] *)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O, _ => n
  | S k, O => n
  | S k, S l => k - l
  end

where "n - m" := (minus n m) : nat_scope.

(** Definition of the usual orders, the basic properties of [le] and [lt]
    can be found in files Le and Lt *)

Inductive le (n:nat) : nat -> Type :=
  | le_n : n <= n
  | le_S : forall m:nat, n <= m -> n <= S m

where "n <= m" := (le n m) : nat_scope.

Hint Constructors le: core.
(*i equivalent to : "Hints Resolve le_n le_S : core." i*)

Definition lt (n m:nat) := S n <= m.
Hint Unfold lt: core.

Infix "<" := lt : nat_scope.

Definition ge (n m:nat) := m <= n.
Hint Unfold ge: core.

Infix ">=" := ge : nat_scope.

Definition gt (n m:nat) := m < n.
Hint Unfold gt: core.

Infix ">" := gt : nat_scope.

(* Awaiting definition of /\:
Notation "x <= y <= z" := (x <= y /\ y <= z) : nat_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : nat_scope.
Notation "x < y < z" := (x < y /\ y < z) : nat_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : nat_scope.
*)

Theorem S_preserves_le : forall n m, n <= m -> (S n) <= (S m).
Proof.
intros n m H; induction H; auto.
Defined.

(** le_pred in Peano.v *)
Theorem pred_preserves_le : forall n m, n <= m -> pred n <= pred m.
Proof.
induction 1; auto. destruct m; simpl; auto.
Defined.

(** le_S_n *)
Theorem S_reflects_le : forall {n m}, S n <= S m -> n <= m.
Proof.
intros n m. exact (pred_preserves_le (S n) (S m)).
Defined.

Theorem O_le_n n : O <= n.
Proof.
  induction n; auto.
Defined.

Theorem n_le_O : forall {n:nat}, n <= 0 -> n = 0.
Proof.
  assert (gen : forall n m, 0 = m -> n <= m -> n = m).
  intros n. induction n as [ | n' IH].
    intros; auto.
    intros m p H. destruct H as [ | m' H'].
      destruct (O_neq_S p).
      destruct (O_neq_S p).
  intros; apply gen; auto.
Defined.

Definition le_refl := le_n.

Theorem le_trans : forall {i j k:nat}, i <= j -> j <= k -> i <= k.
Proof.
  intros i j k Hij Hjk. induction Hjk as [ | k' Hjk' IH].
    auto.
    auto.
Defined.

(** Case analysis *)

Theorem nat_case :
 forall (n:nat) (P:nat -> Type), P 0 -> (forall m:nat, P (S m)) -> P n.
Proof.
  induction n; auto.
Defined.

(** Principle of double induction *)

Theorem nat_double_ind :
 forall R:nat -> nat -> Type,
   (forall n:nat, R 0 n) ->
   (forall n:nat, R (S n) 0) ->
   (forall n m:nat, R n m -> R (S n) (S m)) -> forall n m:nat, R n m.
Proof.
  induction n; auto.
  destruct m; auto.
Defined.

(** max and min omitted *)

(** [n]th iteration of the function [f] *)

Fixpoint nat_iter (n:nat) {A} (f:A->A) (x:A) : A :=
  match n with
    | O => x
    | S n' => f (nat_iter n' f x)
  end.

Lemma nat_iter_succ_r n {A} (f:A->A) (x:A) :
  nat_iter (S n) f x = nat_iter n f (f x).
Proof.
  induction n; intros; simpl; rewrite <- ?IHn; trivial.
Defined.

Theorem nat_iter_plus :
  forall (n m:nat) {A} (f:A -> A) (x:A),
    nat_iter (n + m) f x = nat_iter n f (nat_iter m f x).
Proof.
  induction n; intros; simpl; rewrite ?IHn; trivial.
Defined.

(** Preservation of invariants : if [f : A->A] preserves the invariant [Inv],
    then the iterates of [f] also preserve it. *)

Theorem nat_iter_invariant :
  forall (n:nat) {A} (f:A -> A) (P : A -> Type),
    (forall x, P x -> P (f x)) ->
    forall x, P x -> P (nat_iter n f x).
Proof.
  induction n; simpl; trivial.
  intros A f P Hf x Hx. apply Hf, IHn; trivial.
Defined.

(** Decidability

Note: there are several possible approaches to decidability.
Here we mix a few of them. *)

Fixpoint booleq_nat (n m:nat) : Bool :=
  match n with
    | O => match m with
      | O => true
      | S m' => false
      end
    | S n' => match m with
      | O => false
      | S m' => booleq_nat n' m'
      end
    end.

Fixpoint le_bool (n m:nat) : Bool :=
  match n with
    | O => true
    | S n' => match m with
      | O => false
      | S m' => le_bool n' m'
      end
    end.

Definition le_bool__le {n m : nat} : (le_bool n m = true) -> n <= m.
Proof.
  revert m. induction n as [ | n' IHn]; intros [ | m']; simpl.
    auto.
    intros; apply O_le_n.
    intros H. destruct (true_neq_false (H^)).
    intros H. apply S_preserves_le. apply IHn. assumption.
Defined.

Definition le__le_bool {n m : nat} : n <= m -> (le_bool n m = true).
Proof.
  revert m. induction n as [ | n' IHn]; intros [ | m']; simpl.
    auto.
    auto.
    intros H. destruct (O_neq_S (n_le_O H)^).
    intros H. apply IHn. apply S_reflects_le. assumption.
Defined.

Definition Decide (A:Type) := (A + (A -> Empty))%type.

Definition eq_dec_nat : forall (n m:nat), Decide (n = m).
Proof.
  intros n; induction n as [ | n' IHn];
    intros m; destruct m as [ | m'].
    (* O = O *) apply inl. auto.
    (* O = S m' *) apply inr. apply O_neq_S.
    (* S n' = 0 *) apply inr.
      intros H. exact (O_neq_S H^).
    (* Sn' = S m' *)
      destruct (IHn m') as [ yes | no ].
      (* yes *) apply inl; auto.
      (* now *) apply inr.
        intros H. apply no. apply (S_inj H).
Defined.

Definition le_dec : forall (n m:nat), Decide (n <= m).
Proof.
  intros n; induction n as [ | n' IHn];
    intros m; destruct m as [ | m'].
    (* O = O *) apply inl. auto.
    (* O = S m' *) apply inl. apply O_le_n.
    (* S n' = 0 *) apply inr.
      intros H. exact (O_neq_S (n_le_O H)^).
    (* Sn' = S m' *)
      destruct (IHn m') as [ yes | no ].
      (* yes *) apply inl; apply S_preserves_le; auto.
      (* now *) apply inr.
        intros H. apply no. apply (S_reflects_le H).
Defined.

Theorem nat_is_hset : IsHSet nat.
Proof.
  apply hset_decidable. unfold decidable_paths. apply eq_dec_nat.
Defined.

Definition nat_HSet : HSet
  := Build_HSet nat nat_is_hset.

(*
Local Variables:
coq-prog-name: "hoqtop"
End:
*)
