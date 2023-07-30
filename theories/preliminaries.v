Require Import StrictProp. 
Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.

Definition comp {X Y Z} (f: Y -> Z) (g: X -> Y): X -> Z := fun x => f (g x).
Arguments comp {_ _ _} _ _ _/. 
#[local] Infix "°" := comp (at level 20).
Definition const {X Y} y: X -> Y := fun _ => y. 
Arguments const {_ _} _ _/.

Lemma compA {X Y Z T} (f: Z->T) (g: Y->Z) (h: X->Y): f ° (g ° h) = (f ° g) ° h.
Proof. by []. Qed.
Lemma compIx {X Y} (f: X->Y): id ° f = f.
Proof. by []. Qed.
Lemma compxI {X Y} (f: X->Y): f ° id = f.
Proof. by []. Qed.
Lemma compCx {X Y Z} (f: X->Y) (z: Z): const z ° f = const z.
Proof. by []. Qed.
Lemma compxC {X Y Z} (f: Y->Z) (y: Y): f ° @const X _ y = const (f y).
Proof. by []. Qed.

Definition empty {X}: X -> Prop := fun _ => False. 
Definition pair {X} (x y: X): X -> Prop := fun z => z=x \/ z=y.
Lemma forall_pair {X} (P: X -> Prop) x y: (forall z, pair x y z -> P z) <-> P x /\ P y.
Proof. split. move=>H; split; apply H; cbv; auto. by move=>[??]?[->|->]. Qed.

(* Notation "a &&& b" := (if a then b else false) (at level 60): bool_scope.  *)
(* Notation "a ||| b" := (if a then true else b) (at level 60): bool_scope.  *)
(* Notation "a ==> b" := (if a then b else true): bool_scope. *)

Notation unify M N := (eq_refl: M = N).

(* a definitionally proof irrelevant version of [is_true] *)
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
