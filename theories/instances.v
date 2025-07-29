From Stdlib Require Import Arith.
From mathcomp Require Import eqtype ssrnat.
Require Export lattice.

(** ** unit *)

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

HB.instance Definition _ := eqtype_setoid nat.
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

(** ** extensional functions on Types *)
(** NB: different from extensional functions between setoids (setoid_morphisms), here we use [eq] on the codomain *)
Definition extfun X Y := arrow X Y.
Definition extid {X}: extfun X X := types_id. 
HB.instance Definition _ X Y :=
  isSetoid.Build (extfun X Y) (@Equivalence.pointwise_equivalence X Y eq eq_equivalence). 
