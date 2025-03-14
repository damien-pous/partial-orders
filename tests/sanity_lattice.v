From PartialOrders Require Import lattice.


(* nice thanks to indexed sups *)
Compute fun P: (nat -> nat -> Prop) -> Prop => inf P. 
Compute fun P: nat -> nat -> Prop => cup P P.
Compute fun P: nat -> nat -> Prop => cap P P.
