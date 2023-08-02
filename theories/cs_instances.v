Require Import Arith.
Require Export cs_gpo.

Canonical Structure nat_setoid := eq_setoid nat.

Program Canonical Structure nat_po := PO.build nat Peano.le _ _.
Next Obligation. split. now intros <-. intros. now apply Nat.le_antisymm. Qed.

Program Canonical Structure nat_spo :=
  SPO.build sF nat
    (fun k => match k with
           | kE => fun _ => exist _ (fun _ => 0) _
           | kB => fun _ => exist _ (fun '(x,y) => Peano.max x y) _
           | kC | kD | kA  => discriminate
           end).
Next Obligation. intro. firstorder. apply Nat.le_0_l. Qed.
Next Obligation. intro x. now rewrite Nat.max_lub_iff, forall_pair. Qed.

Program Canonical Structure nat_ipo :=
  IPO.build sB nat
    (fun k => match k with
           | kB => fun _ => exist _ (fun '(x,y) => Peano.min x y) _
           | kE | kC | kD | kA  => discriminate
           end).
Next Obligation. intro x. cbn. now rewrite Nat.min_glb_iff, forall_pair. Qed.

Canonical Structure nat_gpo := GPO.from_ISPO (lSI pF pB) nat. 

