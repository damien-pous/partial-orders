Require Import ssreflect ssrfun ssrbool.
Require Import Arith.
Require Export cs_gpo.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

(** ** natural numbers *)

Canonical Structure nat_setoid := eq_setoid nat.

Program Canonical Structure nat_po := PO.Build nat Peano.le _.
Next Obligation.
  split. typeclasses eauto.
  split. by intros <-. intros. now apply Nat.le_antisymm.
Qed.

Program Canonical Structure nat_spo :=
  SPO.Build sF nat
    (fun k => match k with
           | kE => fun _ => exist _ (fun _ => 0) _
           | kB => fun _ => exist _ (fun '(x,y) => Peano.max x y) _
           | kC | kD | kA  => sEmpty_rect _
           end).
Next Obligation. intro. firstorder. apply Nat.le_0_l. Qed.
Next Obligation. intro. cbn. by rewrite Nat.max_lub_iff forall_pair. Qed.

Program Canonical Structure nat_ipo :=
  IPO.Build sB nat
    (fun k => match k with
           | kB => fun _ => exist _ (fun '(x,y) => Peano.min x y) _
           | kE | kC | kD | kA  => sEmpty_rect _
           end).
Next Obligation. intro. cbn. by rewrite Nat.min_glb_iff forall_pair. Qed.

Canonical Structure nat_gpo := GPO.from_ISPO (lSI pF pB) nat. 



(** ** lists *)

Fixpoint list_eqv {X: Setoid.type} (h k: list X) :=
  match h,k with cons x h,cons y k => x≡y /\ list_eqv h k | nil,nil => True | _,_ => False end.
Program Canonical Structure list_setoid (X: Setoid.type) :=
  Setoid.Build (list X) list_eqv _.
Next Obligation.
  constructor.
  - by elim=>//.
  - by elim=>[|x h IH][|y k]//=[? ?]; split; auto. 
  - elim=>[|x h IH][|y k][|z l]//=[? ?][? ?]; split; try etransitivity; eauto. 
Qed.



Fixpoint leq_list {X: PO.type} (h k: list X) :=
  match h,k with cons x h,cons y k => x<=y /\ leq_list h k | nil,_ => True | _,_ => False end.
Program Canonical Structure list_po (X: PO.type) :=
  PO.Build (list X) leq_list _.
Next Obligation.
  split. 
  - constructor.
    by elim=>//=.
    by elim=>[|x h IH][|y k][|z l]//=[? ?][? ?]; split; try etransitivity; eauto.
  - elim=>[|x h IH][|y k]; cbn; try tauto.
    rewrite eqv_of_leq. setoid_rewrite IH. tauto. 
Qed.



(** ** extensional functions on Types *)
(** NB: different from extensional functions between setoids (setoid_morphisms), here we use [eq] on the codomain *)
Definition efun X Y := arrow X Y.
Definition eid {X}: efun X X := types_id. 
Canonical Structure efun_setoid X Y :=
  Setoid.Build (efun X Y) _ (@Equivalence.pointwise_equivalence X Y eq eq_equivalence). 
