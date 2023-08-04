Require Import ssreflect ssrfun ssrbool.
From PartialOrders Require Import cs_spo.

Goal forall l, sA<<l -> sE <<l.
  intros l L. solve_lower. 
Qed.

(* Set Debug "unification". *)
(* Set Printing All. *)
Time Goal
  let T := ((bool -> bool -> bool -> bool -> Prop)) in
  let T' := (T: PO.type ) in
  let T'' := (T: SPO.type sA) in
  (* let X := ((T-mon->T): SPO sA) in (* slow *) *)
  (* let X := ((T'-mon->T'): SPO sA) in (* slow *) *)
  let X := ((T''-mon->T''): SPO.type sA) in (* fast *)
  True.
intros.
simpl in *.
(* cbv in T. *)
Abort.
