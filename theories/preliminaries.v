From Stdlib Require Import StrictProp.
From HB Require Export structures.
From mathcomp Require Export ssreflect ssrfun ssrbool.
From Stdlib Require Export Setoid Morphisms Basics.

#[export] Set Implicit Arguments.
#[export] Unset Printing Implicit Defensive.

#[export] Set Primitive Projections.

#[export] Unset Transparent Obligations.
#[export] Obligation Tactic := intros. (* mitigate painful behaviour or [Program] *)

(** identity and composition *)
Notation types_id := Datatypes.id.
Notation types_comp := compose.
(** we setup a notation "∘" (\circ) for plain composition, consistently with the one in program_scope
    (we may restrict its scope to a libray-specific one later on)
    in subsequent modules, we also setup "°" (degree) for composition of monotone functions *)
Infix "∘" := types_comp (at level 40, left associativity). 
Reserved Infix "°" (at level 40, left associativity).
(** we let [comp] and [const] reduce more easily than in Basics
    if problematic, we can also redefine them *)
Arguments compose {_ _ _} _ _ _/.
Arguments const {_ _} _ _/.

Lemma compA {X Y Z T} (f: Z->T) (g: Y->Z) (h: X->Y): f ∘ (g ∘ h) = (f ∘ g) ∘ h.
Proof. by []. Qed.
Lemma compIx {X Y} (f: X->Y): id ∘ f = f.
Proof. by []. Qed.
Lemma compxI {X Y} (f: X->Y): f ∘ id = f.
Proof. by []. Qed.
Lemma compCx {X Y Z} (f: X->Y) (z: Z): const z ∘ f = const z.
Proof. by []. Qed.
Lemma compxC {X Y Z} (f: Y->Z) (y: Y): f ∘ @const _ X y = const (f y).
Proof. by []. Qed.

(** equality on tiny types *)
Lemma False_eq: forall x y: False, x = y.
Proof. done. Qed.
Lemma unit_eq: forall x y: unit, x = y.
Proof. by case; case. Qed.

(** standard functions *)
Definition empty_fun {X}: False -> X := False_rect X. 
Definition bool_fun X (x y: X): bool -> X := fun b => if b then y else x.
Definition unit_fun {X}: X -> unit := fun _ => tt. 

(** common predicates *)
Definition empty {X}: X -> Prop := fun _ => False. 
Definition full {X}: X -> Prop := fun _ => True. 
Notation single x := (eq x) (only parsing).
Definition pair {X} (x y: X): X -> Prop := fun z => z=x \/ z=y.
Lemma forall_empty {X} (P: X -> Prop): (forall z, empty z -> P z) <-> True.
Proof. by firstorder subst. Qed.
Lemma forall_single {X} (P: X -> Prop) x: (forall z, single x z -> P z) <-> P x.
Proof. by firstorder subst. Qed.
Lemma forall_pair {X} (P: X -> Prop) x y: (forall z, pair x y z -> P z) <-> P x /\ P y.
Proof. by firstorder subst. Qed.

Lemma forall_iff X (P Q: X -> Prop) (H: forall a, P a <-> Q a): (forall a, P a) <-> (forall a, Q a).
Proof. firstorder. Qed.
Lemma forall_and X (Q R: X -> Prop):
  (forall a, Q a /\ R a) <-> (forall a, Q a) /\ (forall a, R a).
Proof. firstorder. Qed.
Lemma forall_iff_and X (P Q R: X -> Prop) (H: forall a, P a <-> Q a /\ R a):
  (forall a, P a) <-> (forall a, Q a) /\ (forall a, R a).
Proof. firstorder. Qed.

(** testing that two structures are definitionally equal *)
Notation same T X Y := (eq_refl: @eq T X Y).

(** testing that two terms unify *)
Notation unify M N := (same _ M N).

(** a definitionally proof irrelevant version of [is_true] (no longer used) *)
Definition is_true' (b: bool) : SProp := if b then sUnit else sEmpty.
Definition is_true'_eq_true b : is_true' b -> true = b
  := match b with
     | true => fun _ => eq_refl
     | false => sEmpty_ind _
     end.
Definition eq_true_is_true' b (H: true=b) : is_true' b
  := match H in _ = x return is_true' x with eq_refl => stt end.
Lemma is_true'_leq: forall b c, implb b c -> is_true' b -> is_true' c. 
Proof. (* by case; case. *) by destruct b; destruct c. Qed.
Notation sEmpty_rect := sEmpty_rect.
  
(** automatically apply reflexivity *)
#[export] Hint Extern 0 => reflexivity: core.
