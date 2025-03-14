From PartialOrders Require Import sups.

Check ((nat->bool)-mon->(nat->Prop)): CPO.type.
Check ((nat->bool)-mon->(nat->Prop)): supCL.type.

(** complexity issue (solved, test left here to see if it appears again)*)

Time Goal
  let T := ((bool -> bool -> bool -> bool -> Prop)) in
  let T' := (T: PO.type) in
  let T'' := (T: supCL.type) in
  let X := ((T-mon->T): supCL.type) in (* fast *)
  let X' := ((T'-mon->T'): supCL.type) in (* fast *)
  let X'' := ((T''-mon->T''): supCL.type) in (* fast *)
  True.
intros.
hnf in *.
Abort.

