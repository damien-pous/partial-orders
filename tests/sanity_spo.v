Require Import ssreflect ssrfun ssrbool.
From PartialOrders Require Import spo.

Goal forall l, sA<<l -> sE <<l.
  intros l L. solve_lower. 
Qed.

(* Set Debug "unification". *)
(* Set Printing All. *)
Time Goal
  let T := ((bool -> bool -> bool -> bool -> Prop)) in
  let T' := (T: PO ) in
  let T'' := (T: SPO sA) in
  (* let X := ((T-mon->T): SPO sA) in (* slow *) *)
  (* let X := ((T'-mon->T'): SPO sA) in (* slow *) *)
  let X := ((T''-mon->T''): SPO sA) in (* fast *)
  True.
intros.
simpl in *.
(* cbv in T. *)
Abort.
