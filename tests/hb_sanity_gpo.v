From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Export hb_gpo hb_categories.

(** * levels  *)

Check fun l: level => unify (types_comp l inl) (suplevel l). 
Check fun l: level => unify (types_comp l inr) (inflevel l). 
Check fun l: level => unify (types_comp (dual_level l) inr) (types_comp l inl). 
Fail Check fun l: level => unify (dual_level (dual_level l)) l. (* dommage, but ok with behaviour below *)
Check fun (l: level) x => unify (dual_level (dual_level l) x) (l x). 
Fail Check fun l => unify (lA << l) (lA << dual_level l). (* dommage *)

Goal forall l, sA<<l -> sE <<l.
  intros l L. solve_lower. 
Qed.

(** * GPOs  *)

Compute fun P: (nat -> nat -> Prop) -> Prop => inf P. (* nice thanks to indexed sups *)
Compute fun P: nat -> nat -> Prop => P⊔P.
Compute fun P: nat -> nat -> Prop => P⊓P.
