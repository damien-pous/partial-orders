Require Import ssreflect ssrfun ssrbool.
From PartialOrders Require Import cs_gpo.


Compute fun P: (nat -> nat -> Prop) -> Prop => inf P. (* nice thanks to indexed sups *)
Compute fun P: nat -> nat -> Prop => P⊔P.
Compute fun P: nat -> nat -> Prop => P⊓P.
