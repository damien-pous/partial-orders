From Stdlib Require Classical.
Require Export infs.
Require Import lfp.

(** * greatest fixpoint theorems *)
(** by duality with least fixpoint ones *)

Section s.
Context {X: PO.type}.
Implicit Types x y z: X.
Implicit Types f g: X -> X.

(** post-fixpoints *)
Definition is_postfp f x := x <= f x.

(** greatest (post-)fixpoints *)
Definition is_gfp f := greatest (is_postfp f).

Lemma is_gfp_leq (f g: X -mon-> X): f <= g -> forall x y, is_gfp f x -> is_gfp g y -> x <= y.
Proof. intros; exact: (is_lfp_leq (f:=dualf g) (g:=dualf f)). Qed.

Lemma gfp_unique (f: X -mon-> X): forall x y, is_gfp f x -> is_gfp f y -> x ≡ y.
Proof. intros; exact: (lfp_unique (f:=dualf f)). Qed.

(** second half of Knaster-Tarski theorem on montone functions,
    also known as Lambek lemma in category theory *)
Proposition is_gfp_fixpoint (f: X -mon-> X) x: is_gfp f x -> f x ≡ x.
Proof. exact: (is_lfp_fixpoint (dualf f)). Qed.

(** for monotone functions, pre-fixpoints are closed under infima *)
Lemma sup_closed_postfp (f: X-mon->X): sup_closed (is_postfp f).
Proof. exact: (inf_closed_prefp (dualf f)). Qed.  

(** characterisation as the supremum of all post-fixpoints (again, for monotone functions) *)
Proposition is_gfp_sup (f: X -mon-> X) (z: X): is_gfp f z <-> is_sup (fun x => x <= f x) z.
Proof. exact: (is_lfp_inf (dualf f)). Qed.  

End s.

(** partial orders with a greatest fixpoint operator for monotone functions
    (in fact, equivalent to CPO's)
    later we equip all CPO's with such a struture, using classical logic
    as well as all dCPO's, constructively
 *)
HB.mixin Record PO_gfp X of PO X := {
    #[canonical=no] gfp: (X-mon->X) -> X;
    #[canonical=no] gfpE: forall f: X-mon->X, is_gfp f (gfp f);
  }.
HB.builders Context X of PO_gfp X.
Definition top: X := gfp types_id.
Lemma top_spec: is_inf empty top.
Proof. rewrite is_inf_empty/==>t. by apply (gfpE types_id). Qed.
HB.instance Definition _ := PO_top.Build X top_spec.
HB.end.
HB.structure Definition gfpPO := {X of PO_gfp X &}. 

(** duality *)
Section s.
  Context {X: lfpPO.type}.
  Definition dual_gfp (f: dual X-mon->dual X) := lfp (dualf' f): dual X.
  HB.instance Definition _ := PO_gfp.Build (dual X) dual_gfp (fun f => lfpE (dualf' f)).
End s.
Section s.
  Context {X: gfpPO.type}.
  Definition dual_lfp (f: dual X-mon->dual X) := gfp (dualf' f): dual X.
  HB.instance Definition _ := PO_lfp.Build (dual X) dual_lfp (fun f => gfpE (dualf' f)).
End s.

(** theory of such least fixpoint operators *)

Lemma gfp_pfp {X: gfpPO.type} (f: X -mon-> X): is_postfp f (gfp f).
Proof. dualf. exact: (lfp_pfp (dualf f)). Qed.

Lemma gfp_ind {X: gfpPO.type} (f: X -mon-> X) x: x <= f x -> x <= gfp f.
Proof. dualf. exact: (lfp_ind (dualf f)). Qed.

Lemma gfp_fixpoint {X: gfpPO.type} (f: X -mon-> X): is_fp f (gfp f).
Proof. dualf. exact: (lfp_fixpoint (dualf f)). Qed.

Instance gfp_leq {X}: Proper (leq ==> leq) (@gfp X).
Proof. move=>f g fg. apply: (is_gfp_leq fg); exact: gfpE. Qed.
Instance gfp_eqv {X}: Proper (eqv ==> eqv) (@gfp X) := op_leq_eqv_1.

Lemma leq_mon_gfp {X Y: gfpPO.type} (f: X-mon->Y) (g: X-mon->X) (h: Y-mon->Y) :
  f ∘ g <= h ∘ f -> f (gfp g) <= gfp h.
Proof. dualf. exact: (geq_mon_lfp (dualf f) (dualf g) (dualf h)). Qed.

Lemma rolling_gfp {X Y: gfpPO.type} (f: X-mon->Y) (g: Y-mon->X):
  g (gfp (f ∘ g)) ≡ gfp (g ∘ f).
Proof. dualf. exact: (rolling_lfp (dualf f) (dualf g)). Qed.

Lemma geq_adj_gfp {X Y: gfpPO.type} (f: X ⊢ Y) (g: X-mon->X) (h: Y-mon->Y) :
  h ∘ f <= f ∘ g -> gfp h <= f (gfp g).
Proof. dualf. exact: (leq_adj_lfp (dualf f) (dualf g) (dualf h)). Qed.

Lemma adj_gfp {X Y: gfpPO.type} (f: X ⊢ Y) (g: X-mon->X) (h: Y-mon->Y) :
  f ∘ g ≡ h ∘ f -> f (gfp g) ≡ gfp h.
Proof. dualf. exact: (adj_lfp (dualf f) (dualf g) (dualf h)). Qed.

Lemma exchange_gfp_leq {X Y: gfpPO.type} (f: X ⊢ Y) (g: X-mon->Y) (h: Y-mon->X):
  g ∘ h ∘ f <= f ∘ h ∘ g  -> gfp (g ∘ h) <= gfp (f ∘ h).
Proof. dualf. exact: (exchange_lfp_leq (dualf f) (dualf g) (dualf h)). Qed.
Lemma exchange_gfp_leq' {X Y: gfpPO.type} (f: X ⊢ Y) (g: X-mon->Y) (h: Y-mon->X):
  g ∘ h ∘ f <= f ∘ h ∘ g  -> gfp (h ∘ g) <= gfp (h ∘ f).
Proof. dualf. exact: (exchange_lfp_leq' (dualf f) (dualf g) (dualf h)). Qed.

Lemma exchange_gfp_eqv {X Y: gfpPO.type} (f g: X ⊢ Y) (h: Y-mon->X):
  f ∘ h ∘ g ≡ g ∘ h ∘ f -> gfp (f ∘ h) ≡ gfp (g ∘ h).
Proof. dualf. exact: (exchange_lfp_eqv (dualf f) (dualf g) (dualf h)). Qed.
Lemma exchange_gfp_eqv' {X Y: gfpPO.type} (f g: X ⊢ Y) (h: Y-mon->X):
  f ∘ h ∘ g ≡ g ∘ h ∘ f -> gfp (h ∘ f) ≡ gfp (h ∘ g).
Proof. dualf. exact: (exchange_lfp_eqv' (dualf f) (dualf g) (dualf h)). Qed.

(** * cochain construction *)

Section c.
 Context {X: PO.type}.
 Section d.
 Variable f: X -> X.

 (** the set of all (transfinite) iterations of f *)
 Inductive C': X -> Prop :=
 | Cf': forall x, C' x -> C' (f x)
 | Cinf: inf_closed C'.

 (** duality with the chain  *)
 Lemma C'C: C' ≡ C (dualf f).
 Proof.
   apply: antisym.
   * move=>x. elim=>[{}x Cx IH|T TC IH t Ht].
     ** exact: Cf.
     ** apply: Csup. exact: IH. done.
   * move=>x. elim=>[{}x Cx IH|T TC IH t Ht].
     ** exact: Cf'.
     ** apply: Cinf. exact: IH. done.
 Qed.

 (* TODO: duality for Chain/Chain' *)
 
 (** a type for the elements of the cochain *)
 Definition Chain' := sig C'.
 Definition chn' c (Cc: C' c): Chain' := exist _ c Cc.
 Arguments chn': clear implicits.
 Lemma Celem' (c: Chain'): C' (sval c).
 Proof. exact: proj2_sig. Qed.

 (** the cochain is closed under [f] *)
 Definition next' (x: Chain') := chn' (f (sval x)) (Cf' (Celem' x)).

 (** the cochain is inductively generated *)
 Proposition tower': forall (P: Chain' -> Prop), inf_closed P -> (forall x, P x -> P (next' x)) -> forall x, P x.
 Proof.
   move=>P Pinf Pnext.
   suff H: forall x, C' x -> forall Cx, P (chn' x Cx). by move=>[??]; apply H.
   induction 1 as [x Cx IH|T TC IH t Ht]=>[Cfx|Ct].
   - move: (Pnext (chn' x Cx) (IH _)). by apply inf_closed_Proper.
   - apply: (Pinf (fun t => T (sval t))).
     -- move=>[x Cx] Tx. by apply IH.
     -- move=>/=[x Cx]. etransitivity. apply Ht.
        split. clear; firstorder.
        move=>H y Ty. by apply (H (chn' _ (TC _ Ty))).
 Qed.

 End d.
 Arguments next': clear implicits.

 (** when [f] is monotone (on [X]), so is [next] (on [Chain' f])  *)
 Section d.
 Variable f: X -mon-> X.
 Lemma next_leq: Proper (leq ==> leq) (next' f).   
 Proof. by move =>???; apply f. Qed.
 HB.instance Definition _ := isMonotone.Build _ _ (next' f) next_leq.

 (** elements of the cochain are pre-fixpoints of [f] *)
 Lemma chain_prefixpoint: forall c: Chain' f, next' f c <= c.
 Proof.
   apply tower'. apply: inf_closed_leq. 
   by move=>*; apply f.
 Qed.

 (** they are below all pre-fixpoints of [f] *)
 Theorem chain_above_postfixpoints x: x <= f x -> forall c: Chain' f, x <= sval c.
 Proof.
   (* we would like to use [tower], but this requires closure under sups in [Chain f],
      and [sup_closed_leq] does not apply... *)
   move=>Hx []/=.
   induction 1 as [y Cy IH|T TC IH t Ht].
   - by rewrite -IH.
   - move: T {TC} IH t Ht. exact: (inf_closed_leq (const x)). 
 Qed.

 (** if the cochain contains a post-fixpoint, then this is the greatest (post-)fixpoint *)
 Theorem gfp_of_chain_postfixpoint (c: Chain' f): sval c <= f (sval c) -> is_gfp f (sval c).
 Proof.
   move=>Hc. split=>//x H.
   exact: chain_above_postfixpoints.
 Qed.

 (** if the cochain has an infimum, then this is the greatest (post-)fixpoint *)
 Theorem gfp_of_chain_infimum x: is_inf (C' f) x -> is_gfp f x.
 Proof.
   rewrite C'C. exact: (lfp_of_chain_supremum (dualf f)). 
 Qed.

End d.
End c.
Lemma CC' {X: PO.type} (f: X->X): C f ≡ C' (dualf f).
Proof.
  rewrite C'C. Fail apply: C_eqv. (* TODO *)
  Restart.
  apply: antisym.
  * move=>x. elim=>[{}x Cx IH|T TC IH t Ht].
    ** exact: Cf'.
    ** apply: Cinf. exact: IH. done.
  * move=>x. elim=>[{}x Cx IH|T TC IH t Ht].
    ** exact: Cf.
    ** apply: Csup. exact: IH. done.
Qed.

(** being inf-closed, the cochain inherits infs from the starting partial order *)
HB.instance Definition _ k {X: ginfPO.type k} (f: X -> X) :=
  ginfPO.copy (Chain' f) (inf_closed_sig (@inf_ginf_closed _ X (C' f) (@Cinf _ f))).
HB.instance Definition _ {X: topPO.type} (f: X -> X) :=
  topPO.copy (Chain' f) (top_gen (@Chain' (top_gen X) f)). 
HB.instance Definition _ {X: meetSemiLattice.type} (f: X -> X) :=
  meetSemiLattice.copy (Chain' f) (cap_gen (@Chain' (cap_gen X) f)). 
HB.instance Definition _ {X: CPO'.type} (f: X -> X) :=
  CPO'.copy (Chain' f) (cinf_gen (@Chain' (cinf_gen X) f)). 
HB.instance Definition _ {X: dCPO'.type} (f: X -> X) :=
  dCPO'.copy (Chain' f) (dinf_gen (@Chain' (dinf_gen X) f)). 
HB.instance Definition _ {X: infCL.type} (f: X -> X) :=
  infCL.copy (Chain' f) (iinf_gen (@Chain' (iinf_gen X) f)). 

(** partial orders where the cochain of every monotone function has a least element *)
HB.mixin Record Chain_gfp X of PO X := {
    #[canonical=no] chain_gfp: (X-mon->X) -> X;
    #[canonical=no] chain_gfpE: forall f: X-mon->X, is_inf (C' f) (chain_gfp f);
  }.
(** hence where every monotone function has a least fixpoint *)
HB.builders Context X of Chain_gfp X.
  HB.instance Definition _ := PO_gfp.Build X chain_gfp (fun f => gfp_of_chain_infimum f (chain_gfpE f)).
HB.end.
HB.structure Definition chain_gfpPO := { X of Chain_gfp X & }.
(** we do not develop the theory of this class yet; still, the idea is that this subclass of PO with greatest fixpoints of monotone functions supports tower induction, and hence nice up-to techniques for coinduction *)

(** duality *)
Section s.
  Context {X: chain_lfpPO.type}.
  Definition dual_chain_gfp (f: dual X-mon->dual X) := chain_lfp (dualf' f): dual X.
  Lemma dual_chain_gfpE (f: dual X-mon->dual X): is_inf (C' f) (dual_chain_gfp f).
  Proof. rewrite C'C. exact: chain_lfpE. Qed.
  HB.instance Definition _ := Chain_gfp.Build (dual X) dual_chain_gfp dual_chain_gfpE.
End s.
Section s.
  Context {X: chain_gfpPO.type}.
  Definition dual_chain_lfp (f: dual X-mon->dual X) := chain_gfp (dualf' f): dual X.
  Lemma dual_chain_lfpE (f: dual X-mon->dual X): is_sup (C f) (dual_chain_lfp f).
  Proof. rewrite CC'. exact: chain_gfpE. Qed.
  HB.instance Definition _ := Chain_lfp.Build (dual X) dual_chain_lfp dual_chain_lfpE.
End s.


(** * Pataraia's fixpoint theorem *)
Module Pataraia. 
Section s.
 Context {X: dCPO'.type}.
 Variable f: X-mon->X.
 Definition gfp: X := Pataraia.lfp (dualf f).     
 Theorem is_greatest_fixpoint: is_gfp f gfp. 
 Proof. exact: (Pataraia.is_least_fixpoint (dualf f)). Qed.
 Proposition gfp_is_inf_C': is_inf (C' f) gfp.
 Proof. rewrite C'C. exact: (Pataraia.lfp_is_sup_C (dualf f)). Qed.
End s.
Opaque gfp.
End Pataraia.

(** * Bourbaki-Witt's fixpoint theorems *)
Module BourbakiWitt.
Section b.
 Context {X: CPO'.type}.
 Variable f: X -eqv-> X. 
 Hypothesis f_ctr: forall x, f x <= x. 
 Definition fixpoint: X := BourbakiWitt.fixpoint (dualf f) f_ctr.
 Theorem is_fixpoint: f fixpoint ≡ fixpoint.
 Proof. exact: (BourbakiWitt.is_fixpoint (dualf f) f_ctr). Qed. 
End b. 
Opaque fixpoint.
Section b.
 Context {X: CPO'.type}.
 Variable f: X -mon-> X. 
 Definition gfp: X := BourbakiWitt.lfp (dualf f).
 Theorem is_greatest_fixpoint: is_gfp f gfp.
 Proof. exact: (BourbakiWitt.is_least_fixpoint (dualf f)). Qed. 
 Proposition gfp_is_inf_C': is_inf (C' f) gfp.
 Proof. rewrite C'C. exact: (BourbakiWitt.lfp_is_sup_C (dualf f)). Qed.
End b. 
Opaque gfp.
End BourbakiWitt.


(** * Extending structures to implement late inheritance *)

(** cf. [lfp.v] for dual explanations *)

HB.structure Definition gfpCPO := {X of infs.CPO' X & Chain_gfp X }.
HB.structure Definition dCPO' := {X of infs.dCPO' X & Chain_gfp X }. 
HB.structure Definition infCL := {X of infs.infCL X & Chain_gfp X }. 

HB.mixin Record EMTag X := {}.
HB.structure Definition CPO' := {X of gfpCPO X & EMTag X }.


(** empty factory to upgrade [infs.dCPO'] to [dCPO'], via Pataraia *)
HB.factory Record dCPO_gfp X of infs.dCPO' X := {}.
HB.builders Context X of dCPO_gfp X.
HB.instance Definition _ := Chain_gfp.Build X Pataraia.gfp Pataraia.gfp_is_inf_C'.
HB.end.
(** overriden factory *)
HB.factory Record PO_dinf X of PO X := {
    #[canonical=no] dinf: forall P: X -> Prop, codirected P -> X;
    #[canonical=no] dinf_spec: forall (P: X -> Prop) D, is_inf P (dinf P D);
  }.
HB.builders Context X of PO_dinf X.
  HB.instance Definition _ := infs.PO_dinf.Build X dinf dinf_spec.
  HB.instance Definition _ := dCPO_gfp.Build X.
HB.end.

(** empty factory to upgrade [infs.CPO'] to [CPO'], via BourbakiWitt *)
HB.factory Record CPO_gfp X of infs.CPO' X := {}.
HB.builders Context X of CPO_gfp X.
HB.instance Definition _ := Chain_gfp.Build X BourbakiWitt.gfp BourbakiWitt.gfp_is_inf_C'.
HB.instance Definition _ := EMTag.Build X.
HB.end.
(** overriden factory *)
HB.factory Record PO_cinf X of PO X := {
    #[canonical=no] cinf: forall P: X -> Prop, cochain P -> X;
    #[canonical=no] cinf_spec: forall (P: X -> Prop) C, is_inf P (cinf P C);
  }.
HB.builders Context X of PO_cinf X.
  HB.instance Definition _ := infs.PO_cinf.Build X cinf cinf_spec.
  HB.instance Definition _ := CPO_gfp.Build X.
HB.end.

(** overriden factory for infCL *)
HB.factory Record PO_iinf X of PO X := {
    #[canonical=no] iinf: forall I, (I -> Prop) -> (I -> X) -> X;
    #[canonical=no] iinf_inf_spec: forall I P (h: I -> X), is_inf (image h P) (iinf I P h);
  }.
HB.builders Context X of PO_iinf X.
  HB.instance Definition _ := infs.PO_iinf.Build X iinf iinf_inf_spec.
  HB.instance Definition _ := dCPO_gfp.Build X.
HB.end.

(** we need to redeclare/upgrade all previously known instances of [dCPO'] *)
HB.instance Definition _ := dCPO_gfp.Build Prop.
HB.instance Definition _ I (X: I -> infs.dCPO'.type) := dCPO_gfp.Build (forall i, X i).
HB.instance Definition _ (X: Setoid.type) (Y: infs.dCPO'.type) := dCPO_gfp.Build (X -eqv-> Y).
HB.instance Definition _ (X: PO.type) (Y: infs.dCPO'.type) := dCPO_gfp.Build (X -mon-> Y).
HB.instance Definition _ (X: infs.dCPO'.type) (f: X -> X) := dCPO_gfp.Build (Chain' f). 
HB.instance Definition _ (X: infs.dCPO'.type) := dCPO_lfp.Build (dual X).
HB.instance Definition _ (X: sups.dCPO.type) := dCPO_gfp.Build (dual X).
(* this one is directly defined here, in order to avoid useless overriding *)
HB.factory Record monadic_dinf Y of PO Y := { X: dCPO'.type; f: Y ·⊣ X; }.
HB.builders Context Y of monadic_dinf Y.
 HB.instance Definition _ := monadic_ginf.Build (@directed) Y (X:=dinf_gen X) f.
 HB.instance Definition _ := infs.dCPO'.copy Y (dinf_gen Y).
 HB.instance Definition _ := dCPO_gfp.Build Y.
HB.end.

(** similarly for [CPO'] (we do it after the ones for [dCPO'] so that the latter, which are axiom-free, take precedence)*)
HB.instance Definition _ := CPO_gfp.Build Prop.
HB.instance Definition _ I (X: I -> infs.CPO'.type) := CPO_gfp.Build (forall i, X i).
HB.instance Definition _ (X: Setoid.type) (Y: infs.CPO'.type) := CPO_gfp.Build (X -eqv-> Y).
HB.instance Definition _ (X: PO.type) (Y: infs.CPO'.type) := CPO_gfp.Build (X -mon-> Y).
HB.instance Definition _ (X: infs.CPO'.type) (f: X -> X) := CPO_gfp.Build (Chain' f).
HB.instance Definition _ (X: infs.CPO'.type) := CPO_lfp.Build (dual X).
HB.instance Definition _ (X: sups.CPO.type) := CPO_gfp.Build (dual X).
(* this one is directly defined here, in order to avoid useless overriding *)
HB.factory Record monadic_cinf Y of PO Y := { X: CPO'.type; f: Y ·⊣ X; }.
HB.builders Context Y of monadic_cinf Y.
 HB.instance Definition _ := monadic_ginf.Build (@chain) Y (X:=cinf_gen X) f.
 HB.instance Definition _ := infs.CPO'.copy Y (cinf_gen Y).
 HB.instance Definition _ := CPO_gfp.Build Y.
HB.end.

(** similarly for [infCL] *)
HB.instance Definition _ I (X: I -> infs.infCL.type) := dCPO_gfp.Build (forall i, X i).
HB.instance Definition _ (X: Setoid.type) (Y: infs.infCL.type) := dCPO_gfp.Build (X -eqv-> Y).
HB.instance Definition _ (X: PO.type) (Y: infs.infCL.type) := dCPO_gfp.Build (X -mon-> Y).
HB.instance Definition _ (X: infs.infCL.type) (f: X -> X) := dCPO_gfp.Build (Chain' f). 
HB.instance Definition _ (X: infs.infCL.type) := dCPO_lfp.Build (dual X).
HB.instance Definition _ (X: sups.supCL.type) := dCPO_gfp.Build (dual X).
(* this one is directly defined here, in order to avoid useless overriding *)
HB.factory Record monadic_iinf Y of PO Y := { X: infCL.type; f: Y ·⊣ X }.
HB.builders Context Y of monadic_iinf Y.
 HB.instance Definition _ := monadic_ginf.Build any_kind Y (X:=iinf_gen X) f.
 HB.instance Definition _ := infs.infCL.copy Y (iinf_gen Y).
 HB.instance Definition _ := dCPO_gfp.Build Y.
HB.end.

