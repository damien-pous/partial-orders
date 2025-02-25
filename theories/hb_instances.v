From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Import Arith.
Require Export hb_lattice.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

(** ** natural numbers *)

Lemma po_nat: po_axm Peano.le.
Proof.
  apply: mk_po_axm. 
  split. now intros <-. intros. now apply Nat.le_antisymm.
Qed.
HB.instance Definition _ := Setoid_isPO.Build nat po_nat.

(** ** lists *)

Section s.
 Variables (X: Setoid.type).
 (** pointwise equivalence *)
 Fixpoint eqv_list (h k: list X) :=
   match h,k with cons x h,cons y k => x≡y /\ eqv_list h k | nil,nil => True | _,_ => False end.
 Lemma setoid_list: Equivalence eqv_list.
 Proof.
   constructor.
   - by elim=>//.
   - by elim=>[|x h IH][|y k]//=[? ?]; split; auto. 
   - elim=>[|x h IH][|y k][|z l]//=[? ?][? ?]; split; try etransitivity; eauto. 
 Qed.
 HB.instance Definition _ := isSetoid.Build _ setoid_list.
End s.
Arguments eqv_list {_} _ _/.

Section s.
 Variables (X: PO.type).
 (** lexicographic ordering *)
 Fixpoint leq_list (h k: list X) :=
   match h,k with cons x h,cons y k => x<=y /\ leq_list h k | nil,_ => True | _,_ => False end.
 Lemma po_list: po_axm leq_list.
 Proof.
  apply: mk_po_axm. split. 
   - by elim=>//.
   - by elim=>[|x h IH][|y k][|z l]//=[? ?][? ?]; split; try etransitivity; eauto.
   - elim=>[|x h IH][|y k]; cbn; try tauto.
     rewrite eqv_of_leq. setoid_rewrite IH. tauto.
 Qed.
 HB.instance Definition _ := Setoid_isPO.Build (list X) po_list.
End s.
Arguments leq_list [_] _ _/.


(** ** extensional functions on Types *)
(** NB: different from extensional functions between setoids (setoid_morphisms), here we use [eq] on the codomain *)
Definition efun X Y := arrow X Y.
Definition eid {X}: efun X X := types_id. 
HB.instance Definition _ X Y :=
  isSetoid.Build (efun X Y) (@Equivalence.pointwise_equivalence X Y eq eq_equivalence). 

