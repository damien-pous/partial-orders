From Stdlib Require Import Arith.
Require Export lattice.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.


(** ** Unit *)

Lemma unit_sup_spec P: is_sup P tt.
Proof. done. Qed.
HB.instance Definition _ := PO_sup.Build unit _ unit_sup_spec.
HB.instance Definition _ := CL_isup.Build unit.

(** ** Booleans *)

Lemma bool_bot_spec: is_sup empty false.
Proof. done. Qed. 
Lemma bool_top_spec: is_inf empty true.
Proof. by case. Qed. 
Lemma bool_cup_spec b c: is_sup (pair b c) (b || c).
Proof. rewrite is_sup_pair/=. case; case:b; case:c; cbn; intuition discriminate. Qed. 
Lemma bool_cap_spec b c: is_inf (pair b c) (b && c).
Proof. rewrite is_inf_pair/=. case; case:b; case:c; cbn; intuition discriminate. Qed. 
HB.instance Definition _ := PO_bot.Build bool bool_bot_spec.
HB.instance Definition _ := PO_top.Build bool bool_top_spec.
HB.instance Definition _ := PO_cup.Build bool _ bool_cup_spec.
HB.instance Definition _ := PO_cap.Build bool _ bool_cap_spec.

(** ** natural numbers *)

Lemma po_nat: po_axm Peano.le.
Proof.
  apply: mk_po_axm. 
  split. now intros <-. intros. now apply Nat.le_antisymm.
Qed.
HB.instance Definition _ := isPO.Build nat po_nat.
Lemma nat_bot_spec: is_sup empty 0.
Proof. rewrite is_sup_empty/=. exact: le_0_n. Qed.
Lemma nat_cup_spec n m: is_sup (pair n m) (max n m).
Proof. rewrite is_sup_pair/=. exact: Nat.max_lub_iff. Qed.
Lemma nat_cap_spec n m: is_inf (pair n m) (min n m).
Proof. rewrite is_inf_pair/=. exact: Nat.min_glb_iff. Qed.
HB.instance Definition _ := PO_bot.Build nat nat_bot_spec.
HB.instance Definition _ := PO_cup.Build nat max nat_cup_spec.
HB.instance Definition _ := PO_cap.Build nat min nat_cap_spec.

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
 HB.instance Definition _ := isPO.Build (list X) po_list.
End s.
Arguments leq_list [_] _ _/.


(** ** extensional functions on Types *)
(** NB: different from extensional functions between setoids (setoid_morphisms), here we use [eq] on the codomain *)
Definition efun X Y := arrow X Y.
Definition eid {X}: efun X X := types_id. 
HB.instance Definition _ X Y :=
  isSetoid.Build (efun X Y) (@Equivalence.pointwise_equivalence X Y eq eq_equivalence). 
