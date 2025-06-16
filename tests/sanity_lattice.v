From PartialOrders Require Import lattice.


(* nice thanks to indexed sups *)
Compute fun P: (nat -> nat -> Prop) -> Prop => inf P. 
Compute fun P: nat -> nat -> Prop => cup P P.
Compute fun P: nat -> nat -> Prop => cap P P.


Check fun X: CompleteLattice.type => dual X: CompleteLattice.type.
Check fun X: boundedLattice.type => (X -mon-> X): boundedLattice.type.
Check fun X: CompleteLattice.type => (X -mon-> X): CompleteLattice.type.
Fail Check fun X: boundedLattice.type => (X -eqv-> X): boundedLattice.type.
Fail Check fun X: CompleteLattice.type => (X -eqv-> X): CompleteLattice.type.
Fail Check fun X: boundedLattice.type => (nat -> X): boundedLattice.type.
(* should eventually work; need to HB.saturate w.r.t [forall _,_] and [setoid_morphism.type] *)

Check fun X: boundedLattice.type =>
        let X' := dual X: boundedLattice.type in
        unify (top: X) (bot: X'). 
