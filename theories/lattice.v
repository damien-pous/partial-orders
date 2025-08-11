Require Export lfp gfp.

HB.structure Definition boundedPO := {X of botPO X & topPO X }.
HB.structure Definition Lattice := {X of joinSemiLattice X & meetSemiLattice X }.
HB.structure Definition boundedLattice := {X of boundedPO X & Lattice X }.
HB.structure Definition CompleteLattice := {X of supCL X & infCL X }. (* FIX: loong *)

HB.saturate dual.
(* HB.saturate setoid_morphism.type. (* hangs (already right after boundedPO) *) *)
HB.saturate po_morphism.type.
HB.saturate (forall _, _).           (* void... *)


(** ** alternative ways to construct sups *)

(** constructing indexed sups from non-indexed ones *)
HB.factory Record PO_sup X of PO X := {
    #[canonical=no] sup: (X -> Prop) -> X;
    #[canonical=no] sup_spec: forall P: X -> Prop, is_sup P (sup P);
  }.
HB.builders Context X of PO_sup X.
  Definition isup I P (h: I -> X) := sup (image h P).
  Lemma isup_spec I P h: is_sup (image h P) (@isup I P h).
  Proof. apply: sup_spec. Qed.
  HB.instance Definition _ := PO_isup.Build X _ isup_spec.
HB.end.

(** arbitrary sups from directed and binary ones *)
HB.factory Record PO_cup_dsup X of PO X & PO_cup X & PO_dsup X := {}.
HB.builders Context X of PO_cup_dsup X.
  Definition sup (P: X -> Prop) := dsup (sup_closure P) (@directed_sup_closure _ P).
  Lemma sup_spec P: is_sup P (sup P).
  Proof. apply is_sup_closure. exact: dsup_spec. Qed.
  HB.instance Definition _ := PO_sup.Build X _ sup_spec.
HB.end.

(** constructing complete lattices from their (indexed) sups  *)
HB.factory Record CL_isup X of supCL X := {}. 
HB.builders Context X of CL_isup X.
  Definition iinf I (P: I -> Prop) (h: I -> X): X := sup (fun y => forall i, P i -> y <= h i).
  Lemma iinf_spec I P (h: I -> X): is_inf (image h P) (iinf P h).
  Proof.
    rewrite /iinf/= =>z. split=>/=H.
    move=>y [i [Pi ->]]. by rewrite H sup_spec /upper_bound=>/=; auto.
    eapply sup_spec. reflexivity. by move: H; rewrite lower_boundE=>/image_adj. 
  Qed.
  HB.instance Definition _ := PO_iinf.Build X _ iinf_spec.
HB.end.

(** ** alternative ways to construct infs *)

(** constructing indexed infs from non-indexed ones *)
HB.factory Record PO_inf X of PO X := {
    #[canonical=no] inf: (X -> Prop) -> X;
    #[canonical=no] inf_spec: forall P: X -> Prop, is_inf P (inf P);
  }.
HB.builders Context X of PO_inf X.
  Definition iinf I P (h: I -> X) := inf (image h P).
  Lemma iinf_spec I P h: is_inf (image h P) (@iinf I P h).
  Proof. apply: inf_spec. Qed.
  HB.instance Definition _ := PO_iinf.Build X _ iinf_spec.
HB.end.

(** arbitrary infs from codirected and binary ones *)
HB.factory Record PO_cap_dinf X of PO X & PO_cap X & PO_dinf X := {}.
HB.builders Context X of PO_cap_dinf X.
  Definition inf (P: X -> Prop) := dinf (inf_closure P) (@codirected_inf_closure _ P).
  Lemma inf_spec P: is_inf P (inf P).
  Proof. apply is_inf_closure. exact: dinf_spec. Qed.
  HB.instance Definition _ := PO_inf.Build X _ inf_spec.
HB.end.

(** constructing complete lattices from their (indexed) infs  *)
HB.factory Record CL_iinf X of infCL X := {}. 
HB.builders Context X of CL_iinf X.
  Definition isup I (P: I -> Prop) (h: I -> X): X := inf (fun y => forall i, P i -> h i <= y).
  Lemma isup_spec I P (h: I -> X): is_sup (image h P) (isup P h).
  Proof.
    rewrite /isup/= =>z. split=>/=H.
    move=>y [i [Pi ->]]. by rewrite -H/isup inf_spec/lower_bound=>/=; auto.
    eapply inf_spec. reflexivity. by move: H; rewrite upper_boundE=>/forall_image.
  Qed.
  HB.instance Definition _ := PO_isup.Build X _ isup_spec.
HB.end.



(* TODO: modular, distributive, residuated, etc *)

(** ** theory *)

Lemma cuptx {X: boundedLattice.type} (x: X): cup top x ≡ top.
Proof. apply: antisym; auto with lattice. exact: leq_top. Qed.
Lemma cupxt {X: boundedLattice.type} (x: X): cup x top ≡ top.
Proof. by rewrite cupC cuptx. Qed.
Lemma capbx {X: boundedLattice.type} (x: X): cap bot x ≡ bot.
Proof. exact: (@cuptx (dual X) x). Qed.
Lemma capxb {X: boundedLattice.type} (x: X): cap x bot ≡ bot.
Proof. exact: (@cupxt (dual X)). Qed.
