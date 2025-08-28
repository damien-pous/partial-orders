Require Export lfp gfp.

HB.structure Definition boundedPO := {X of botPO X & topPO X }.
HB.structure Definition Lattice := {X of joinSemiLattice X & meetSemiLattice X }.
HB.structure Definition boundedLattice := {X of boundedPO X & Lattice X }.
HB.structure Definition CompleteLattice := {X of supCL X & infCL X }. (* FIX: loong *)

HB.saturate dual.
(* HB.saturate setoid_morphism.type. (* hangs (already right after boundedPO) *) *)
HB.saturate po_morphism.type.
HB.saturate (forall _, _).           (* void... *)


(** ** modular lattices *)
HB.mixin Record isModular X of Lattice X := {
    #[canonical=no] modular_: forall x a b: X, x <= b -> cap (cup x a) b <= cup x (cap a b)
  }.
HB.structure Definition ModularLattice := {X of isModular X & }.
Lemma modular {X: ModularLattice.type} (x a b: X):
  x <= b -> cup x (cap a b) ≡ cap (cup x a) b.
Proof.
  move=>xb. apply: antisym. 2: exact/modular_.
  apply: geq_cup. apply: leq_cap=>//. exact/cup_l.
  by rewrite -cup_r.
Qed.
Lemma dual_modular_ {X: ModularLattice.type} (x a b: X):
  b <= x -> cap x (cup a b) <= cup (cap x a) b.
Proof.
  move=>bx. rewrite capC cupC modular_//.
  (* TOFIX: line below should work *)
  (* by rewrite cupC capC. *)
  rewrite cupC. apply: cup_leq=>//. by rewrite capC.
Qed.
HB.instance Definition _ (X: ModularLattice.type) := isModular.Build (dual X) dual_modular_.

HB.instance Definition _ I (X: I -> ModularLattice.type) :=
  isModular.Build (forall i, X i) (fun x a b ab i => @modular_ (X i) (x i) (a i) (b i) (ab i)).
HB.instance Definition _ X (Y: ModularLattice.type) :=
  isModular.Build (X -eqv-> Y) (fun x a b ab i => @modular_ Y (x i) (a i) (b i) (ab i)).
HB.instance Definition _ X (Y: ModularLattice.type) :=
  isModular.Build (X -mon-> Y) (fun x a b ab i => @modular_ Y (x i) (a i) (b i) (ab i)).

(** ** distributive lattices *)
HB.mixin Record isDistributive X of Lattice X := {
    #[canonical=no] distributive_: forall x y z: X, cap x (cup y z) <= cup (cap x y) (cap x z) 
  }.
HB.builders Context X of isDistributive X.
Lemma modular_ (x a b: X) (xb: x <= b): cap (cup x a) b <= cup x (cap a b).
Proof.
  rewrite capC distributive_. apply: geq_cup.
  rewrite cap_r; exact/cup_l.
  rewrite capC; exact/cup_r.
Qed.
HB.instance Definition _ := isModular.Build X modular_.
HB.end.
HB.structure Definition DistributiveLattice := {X of isDistributive X & }.
Lemma distributive {X: DistributiveLattice.type} (x y z: X):
  cap x (cup y z) ≡ cup (cap x y) (cap x z).
Proof.
  apply: antisym. exact/distributive_.
  apply: geq_cup. by rewrite -cup_l. by rewrite -cup_r. 
Qed.
Lemma dual_distributive_ {X: DistributiveLattice.type} (x y z: X):
  cap (cup x y) (cup x z) <= cup x (cap y z).
Proof.
  rewrite distributive_.
  (* TOFIX: should work *)
  (* rewrite capC.  *)
  etransitivity. apply: cup_leq. rewrite capC. reflexivity. reflexivity. 
  rewrite distributive_.
  repeat apply: geq_cup.
  rewrite capI; exact/cup_l. 
  rewrite cap_l; exact/cup_l. 
  rewrite capC distributive_.
  apply: geq_cup.
  rewrite cap_r; exact/cup_l. 
  rewrite capC; exact/cup_r.
Qed.
HB.instance Definition _ (X: DistributiveLattice.type) :=
  isDistributive.Build (dual X) dual_distributive_.

Program Definition _Prop_distributive := isDistributive.Build Prop _.
Next Obligation. cbv. tauto. Qed.
HB.instance Definition _ := _Prop_distributive.

HB.instance Definition _ I (X: I -> DistributiveLattice.type) :=
  isDistributive.Build (forall i, X i) (fun x y z i => @distributive_ (X i) (x i) (y i) (z i)).
HB.instance Definition _ X (Y: DistributiveLattice.type) :=
  isDistributive.Build (X -eqv-> Y) (fun x y z i => @distributive_ Y (x i) (y i) (z i)).
HB.instance Definition _ X (Y: DistributiveLattice.type) :=
  isDistributive.Build (X -mon-> Y) (fun x y z i => @distributive_ Y (x i) (y i) (z i)).

Lemma distributive' {X: DistributiveLattice.type} (x y z: X):
  cup x (cap y z) ≡ cap (cup x y) (cup x z).
Proof. exact: (@distributive (dual X)). Qed.

HB.structure Definition ChainLattice := { X of Lattice X & Chain X }.
Inductive cup_cap_case {X: PO.type} (x y: X): X -> X -> X -> X -> Prop :=
  | cup_cap_case_leq: x <= y -> cup_cap_case x y y y x x
  | cup_cap_case_geq: y <= x -> cup_cap_case x y x x y y
  | cup_cap_case_eqv_: Proper (eqv ==> eqv ==> eqv ==> eqv ==> impl) (cup_cap_case x y).
Instance cup_cap_case_eqv {X: PO.type} (x y: X):
  Proper (eqv ==> eqv ==> eqv ==> eqv ==> iff) (cup_cap_case x y).
Proof. split; exact: cup_cap_case_eqv_. Qed.
Lemma case_chainlattice {X: ChainLattice.type} (x y: X):
  cup_cap_case x y (cup x y) (cup y x) (cap x y) (cap y x).
Proof.
  case: (leq_chain x y)=>H; 
  move:(H)=>/leq_of_cup U; 
  move:(H)=>/leq_of_cap A;
  rewrite U A cupC capC U A;
  by constructor.
Qed.

(** chain lattices are distributive *)
(* TODO: include distributivity in the definition of ChainLattice (forgetful inheritance),
   and use appropriate builders to infer it automatically (need HB support for it) *)
HB.factory Record ChainLattice_isDistributive X of ChainLattice X := {}.
HB.builders Context X of ChainLattice_isDistributive X.
Lemma distributive_ (x y z: X): cap x (cup y z) <= cup (cap x y) (cap x z).
Proof.
  elim: (case_chainlattice y z).
  move=>_. exact/cup_r.
  move=>_. exact/cup_l.
  by move=>?? + _ _ _ _ _ _ _ _ _ _=> ->.
  Restart.
  case: (leq_chain y z)=>/leq_of_cup.
  move=>->. exact/cup_r.
  rewrite cupC. move=>->. exact/cup_l.
Qed.
HB.instance Definition _ := isDistributive.Build X distributive_.
HB.end.

(** decidable orders are (chain) lattices *)
(* TOTHINK: here this is again the "a posteriori inheritance" pattern:
   we do not want to include the Lattice structure in DecidableOrder;
   still, it inherits from it *)
HB.factory Record DecidableOrder_isLattice X of DecidableOrder X := {}.
HB.builders Context X of DecidableOrder_isLattice X.
Definition cup (x y: X) := if x <=? y then y else x. 
Definition cap (x y: X) := if x <=? y then x else y. 
Lemma cup_spec x y: is_sup (pair x y) (cup x y).
Proof.
  apply/is_sup_pair=>/=z. 
  rewrite /cup. case: le_lt_dec.
  - split. split=>//. by transitivity y. by case.
  - split. split=>//. by apply ltle_le with x. by case.
Qed.
HB.instance Definition _ := PO_cup.Build X cup cup_spec. 
Lemma cap_spec x y: is_inf (pair x y) (cap x y).
Proof.
  apply/is_inf_pair=>/=z. 
  rewrite /cap. case: le_lt_dec.
  - split. split=>//. by transitivity x. by case.
  - split. split=>//. by apply lelt_le with y. by case.
Qed.
HB.instance Definition _ := PO_cap.Build X cap cap_spec.
HB.instance Definition _ := ChainLattice_isDistributive.Build X. 
HB.end.

(* TODO: Heyting, Boole *)


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


(** ** theory *)

Lemma cuptx {X: boundedLattice.type} (x: X): cup top x ≡ top.
Proof. apply: antisym; auto with lattice. exact: leq_top. Qed.
Lemma cupxt {X: boundedLattice.type} (x: X): cup x top ≡ top.
Proof. by rewrite cupC cuptx. Qed.
Lemma capbx {X: boundedLattice.type} (x: X): cap bot x ≡ bot.
Proof. exact: (@cuptx (dual X) x). Qed.
Lemma capxb {X: boundedLattice.type} (x: X): cap x bot ≡ bot.
Proof. exact: (@cupxt (dual X)). Qed.


(** ** helpers for duality *)
Lemma cup_dualf {X: PO.type} {Y: meetSemiLattice.type} (f g: X-mon->Y):
  @cup (dual X -mon-> dual Y) (dualf f) (dualf g) ≡ dualf (cap f g).
Proof. done. Qed.
Lemma cap_dualf {X: PO.type} {Y: joinSemiLattice.type} (f g: X-mon->Y):
  @cap (dual X -mon-> dual Y) (dualf f) (dualf g) ≡ dualf (cup f g).
Proof. done. Qed.
Lemma bot_dualf {X: PO.type} {Y: topPO.type}:
  @bot (dual X -mon-> dual Y) ≡ dualf (@top (X-mon->Y)).
Proof. done. Qed.
Lemma top_dualf {X: PO.type} {Y: botPO.type}:
  @top (dual X -mon-> dual Y) ≡ dualf (@bot (X-mon->Y)).
Proof. done. Qed.
Lemma const_dualf {X Y: PO.type} y:
  @const (dual Y) (dual X) y ≡[dual X-mon->dual Y] dualf (@const Y X y).
Proof. done. Qed.
Lemma id_dualf {X: PO.type}:
  @types_id (dual X) ≡[dual X-mon->dual X] dualf (@types_id X).
Proof. done. Qed.
