Require Import ssreflect ssrfun ssrbool.
From PartialOrders Require Import spo.

Goal forall l, sA<<l -> sE <<l.
  intros l L. solve_lower. 
Qed.

(* Set Debug "unification". *)
(* Set Printing All. *)
Time Goal
  let T := ((bool -> Prop): PO) in
  let X := ((T-mon->T): SPO sA) in
  True.
intros.
simpl in *.
(* cbv in T. *)
Abort.
