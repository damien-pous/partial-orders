From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Export hb_spo hb_categories.


(** complexity issue *)

Time Goal
  let T := ((bool -> bool -> bool -> bool -> Prop)) in
  let T' := (T: PO.type) in
  let T'' := (T: SPO.type sA) in
  let X := ((T-mon->T): SPO.type _) in (* fast *)
  let X' := ((T'-mon->T'): SPO.type _) in (* fast *)
  let X'' := ((T''-mon->T''): SPO.type _) in (* fast *)
  True.
intros.
cbn in *.
Abort.

