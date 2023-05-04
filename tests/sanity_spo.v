Require Import ssreflect ssrfun ssrbool.
From PartialOrders Require Import spo.

Goal forall l, sA<<l -> sE <<l.
  intros l L. solve_lower. 
Qed.
