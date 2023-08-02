From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Import Arith.
Require Export hb_gpo.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

(** natural numbers *)
HB.instance Definition _ := eq_setoid nat.
Lemma po_nat: po_axm Peano.le.
Proof.
  split. apply PeanoNat.Nat.le_preorder .
  split. now intros <-. intros. now apply Nat.le_antisymm.
Qed.
HB.instance Definition _ := isPO.Build nat po_nat.
