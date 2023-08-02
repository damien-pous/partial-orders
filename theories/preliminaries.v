Require Import StrictProp.  
Require Import ssreflect ssrfun ssrbool.
Require Export Setoid Morphisms Basics.

Set Implicit Arguments.

(** identity and composition *)
Notation types_id := Datatypes.id.
Notation types_comp := compose.
(** we setup a notation "∘" (\circ) for plain composition, consistently with the one in program_scope
    (we may restrict its scope to a libray-specific one later on)
    in subsequent modules, we also setup "°" (degree) for categorical composition *)
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

(** common predicates *)
Definition empty {X}: X -> Prop := fun _ => False. 
Notation single x := (eq x) (only parsing).
Definition pair {X} (x y: X): X -> Prop := fun z => z=x \/ z=y.
Lemma forall_empty {X} (P: X -> Prop): (forall z, empty z -> P z) <-> True.
Proof. by firstorder subst. Qed.
Lemma forall_single {X} (P: X -> Prop) x: (forall z, single x z -> P z) <-> P x.
Proof. by firstorder subst. Qed.
Lemma forall_pair {X} (P: X -> Prop) x y: (forall z, pair x y z -> P z) <-> P x /\ P y.
Proof. by firstorder subst. Qed.
(* Notation "a &&& b" := (if a then b else false) (at level 60): bool_scope.  *)
(* Notation "a ||| b" := (if a then true else b) (at level 60): bool_scope.  *)
(* Notation "a ==> b" := (if a then b else true): bool_scope. *)

(** testing that two terms unify *)
Notation unify M N := (eq_refl: M = N).

(** a definitionally proof irrelevant version of [is_true] *)
Definition is_true' (b: bool) : SProp := if b then sUnit else sEmpty.
Definition is_true'_eq_true b : is_true' b -> true = b
  := match b with
     | true => fun _ => eq_refl
     | false => sEmpty_ind _
     end.
Definition eq_true_is_true' b (H: true=b) : is_true' b
  := match H in _ = x return is_true' x with eq_refl => stt end.
Lemma is_true'_leq: forall b c, implb b c -> is_true' b -> is_true' c. 
Proof. by move=>[][]//=_ []. Qed.
Notation sEmpty_rect := sEmpty_rect.
  
(** automatically apply reflexivity *)
#[export] Hint Extern 0 => reflexivity: core.
