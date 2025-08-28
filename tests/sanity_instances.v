From PartialOrders Require Import instances.

Check False: PO.type.
Check False: DecidableOrder.type.
Check False: DistributiveLattice.type.

Check unit: PO.type.
Check unit: boundedPO.type.
Check unit: DecidableOrder.type.
Check unit: CompleteLattice.type.
Check unit: DistributiveLattice.type.

Check bool: PO.type.
Check bool: boundedLattice.type.
Check bool: DecidableOrder.type.
Check bool: DistributiveLattice.type.

Check Prop: PO.type.
Check Prop: botPO.type.
Check Prop: topPO.type.
Check Prop: supCL.type.
Check Prop: infCL.type.
Check Prop: DistributiveLattice.type.
(* TOFIX *)
Fail HB.saturate Prop.
Fail Check Prop: boundedPO.type.
Fail Check Prop: boundedLattice.type.
Fail Check Prop: CompleteLattice.type.

Check nat: botPO.type.
Check nat: ChainLattice.type.
Check nat: DecidableOrder.type.
Check nat: DistributiveLattice.type.

Check (nat -> Prop): PO.type.
Check (nat -> Prop): botPO.type.
Check (nat -> Prop): topPO.type.
Check (nat -> Prop): supCL.type.
Check (nat -> Prop): infCL.type.
Check (nat -> Prop): DistributiveLattice.type.
(* TOFIX *)
Fail Check (nat -> Prop): boundedPO.type.
Fail Check (nat -> Prop): boundedLattice.type.
Fail Check (nat -> Prop): CompleteLattice.type.



Check (prod bool unit): PO.type.
Check (prod bool unit): DecidablePO.type.
Check (prod bool unit): StrictPO.type.
Check (prod bool unit): botPO.type.
Check (prod bool unit): joinSemiLattice.type.
Check (prod bool unit): boundedLattice.type.
Check (prod unit unit): supCL.type.
Fail Check (prod unit unit): CompleteLattice.type.

Check (lex_prod bool unit): PO.type.
Check (lex_prod bool unit): DecidablePO.type.
Check (lex_prod bool unit): StrictPO.type.
Check same PO.type ((lex_prod bool unit): StrictPO.type) (lex_prod bool unit).
Check (lex_prod bool unit): Order.type.
Check (lex_prod bool unit): botPO.type.
Check same PO.type ((lex_prod bool unit): botPO.type) (lex_prod bool unit).
Check (lex_prod bool unit): boundedPO.type.
Fail Check same PO.type ((lex_prod bool unit): boundedPO.type) (lex_prod bool unit). (* TOFIX *)
Check (lex_prod bool unit): joinSemiLattice.type.
Check (lex_prod bool unit): DecidableOrder.type.
Check same PO.type ((lex_prod bool unit): joinSemiLattice.type) (lex_prod bool unit). (* through decidable order? *)
Check fun X Y: joinSemiLattice.type => lex_prod X Y: joinSemiLattice.type.  (* should not work! *)
Fail Check fun X Y: joinSemiLattice.type => same PO.type (lex_prod X Y: joinSemiLattice.type) (lex_prod X Y).  (* should indeed fail *)

Check (sum bool unit): PO.type.
Check (sum bool unit): DecidablePO.type.
Check (sum bool unit): StrictPO.type.
Check (sequential_sum bool unit): PO.type.
Check (sequential_sum bool unit): DecidablePO.type.
Check same PO.type ((sequential_sum bool unit): DecidablePO.type) (sequential_sum bool unit).
Check same PO.type ((sequential_sum bool unit): StrictPO.type) (sequential_sum bool unit).
Check (sequential_sum bool unit): Order.type.
(* TOFIX *)
Fail Check (sequential_sum bool unit): botPO.type.  (* should eventually work *)
Fail Check (sequential_sum bool unit): boundedPO.type.  (* should eventually work *)

