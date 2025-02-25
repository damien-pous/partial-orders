From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Export hb_sup hb_inf.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

HB.structure Definition boundedPO := {X of botPO X & topPO X }.
HB.structure Definition Lattice := {X of joinSemiLattice X & meetSemiLattice X }.
HB.structure Definition boundedLattice := {X of boundedPO X & Lattice X }.
HB.structure Definition CompleteLattice := {X of PO X & PO_isup X & PO_iinf X }.

(** constructing complete lattices from their (indexed) sups  *)
HB.factory Record CL_isup X of supCL X := {}. 
HB.builders Context X of CL_isup X.
  Definition iinf I (P: I -> Prop) (h: I -> X): X := sup (fun y => forall i, P i -> y <= h i).
  Lemma iinf_spec I P (h: I -> X): is_inf (image h P) (iinf P h).
  Proof.
    rewrite /iinf/= =>z. split=>/=H.
    move=>y [i [Pi ->]]. by rewrite H sup_spec=>/=; auto.
    eapply sup_spec. reflexivity. by move: H=>/forall_image. 
  Qed.
  HB.instance Definition _ := PO_iinf.Build X _ iinf_spec.
HB.end.

(** constructing complete lattices from their (indexed) infs  *)
HB.factory Record CL_iinf X of infCL X := {}. 
HB.builders Context X of CL_iinf X.
  Definition isup I (P: I -> Prop) (h: I -> X): X := inf (fun y => forall i, P i -> h i <= y).
  Lemma isup_spec I P (h: I -> X): is_sup (image h P) (isup P h).
  Proof.
    rewrite /isup/= =>z. split=>/=H.
    move=>y [i [Pi ->]]. by rewrite -H/isup inf_spec=>/=; auto.
    eapply inf_spec. reflexivity. by move: H=>/forall_image.
  Qed.
  HB.instance Definition _ := PO_isup.Build X _ isup_spec.
HB.end.

(* TODO: modular, distributive, residuated, etc *)
