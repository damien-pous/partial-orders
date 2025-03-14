From Stdlib Require Classical.
Require Export infs adjunction.
Require Import lfp.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

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
    gfp: (X-mon->X) -> X;
    gfpE: forall f: X-mon->X, is_gfp f (gfp f);
  }.
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
Proof. exact: (lfp_pfp (dualf f)). Qed.

Lemma gfp_ind {X: gfpPO.type} (f: X -mon-> X) x: x <= f x -> x <= gfp f.
Proof. exact: (lfp_ind (dualf f)). Qed.

Lemma gfp_fixpoint {X: gfpPO.type} (f: X -mon-> X): is_fp f (gfp f).
Proof. exact: (lfp_fixpoint (dualf f)). Qed.

Instance gfp_leq {X}: Proper (leq ==> leq) (@gfp X).
Proof. move=>f g fg. apply: (is_gfp_leq fg); exact: gfpE. Qed.
Instance gfp_eqv {X}: Proper (eqv ==> eqv) (@gfp X) := op_leq_eqv_1.

Lemma leq_mon_gfp {X Y: gfpPO.type} (f: X-mon->Y) (g: X-mon->X) (h: Y-mon->Y) :
  f ∘ g <= h ∘ f -> f (gfp g) <= gfp h.
Proof. exact: (geq_mon_lfp (dualf f) (dualf g) (dualf h)). Qed.

Lemma rolling_gfp {X Y: gfpPO.type} (f: X-mon->Y) (g: Y-mon->X):
  g (gfp (f ∘ g)) ≡ gfp (g ∘ f).
Proof. exact: (rolling_lfp (dualf f) (dualf g)). Qed.

Lemma geq_adj_gfp {X Y: gfpPO.type} (f: X ⊢ Y) (g: X-mon->X) (h: Y-mon->Y) :
  h ∘ f <= f ∘ g -> gfp h <= f (gfp g).
Proof. exact: (leq_adj_lfp (dualf f) (dualf g) (dualf h)). Qed.

Lemma adj_gfp {X Y: gfpPO.type} (f: X ⊢ Y) (g: X-mon->X) (h: Y-mon->Y) :
  f ∘ g ≡ h ∘ f -> f (gfp g) ≡ gfp h.
Proof. exact: (adj_lfp (dualf f) (dualf g) (dualf h)). Qed.

Lemma exchange_gfp_leq {X Y: gfpPO.type} (f: X ⊢ Y) (g: X-mon->Y) (h: Y-mon->X):
  g ∘ h ∘ f <= f ∘ h ∘ g  -> gfp (g ∘ h) <= gfp (f ∘ h).
Proof. exact: (exchange_lfp_leq (dualf f) (dualf g) (dualf h)). Qed.
Lemma exchange_gfp_leq' {X Y: gfpPO.type} (f: X ⊢ Y) (g: X-mon->Y) (h: Y-mon->X):
  g ∘ h ∘ f <= f ∘ h ∘ g  -> gfp (h ∘ g) <= gfp (h ∘ f).
Proof. exact: (exchange_lfp_leq' (dualf f) (dualf g) (dualf h)). Qed.

Lemma exchange_gfp_eqv {X Y: gfpPO.type} (f g: X ⊢ Y) (h: Y-mon->X):
  f ∘ h ∘ g ≡ g ∘ h ∘ f -> gfp (f ∘ h) ≡ gfp (g ∘ h).
Proof. exact: (exchange_lfp_eqv (dualf f) (dualf g) (dualf h)). Qed.
Lemma exchange_gfp_eqv' {X Y: gfpPO.type} (f g: X ⊢ Y) (h: Y-mon->X):
  f ∘ h ∘ g ≡ g ∘ h ∘ f -> gfp (h ∘ f) ≡ gfp (h ∘ g).
Proof. exact: (exchange_lfp_eqv' (dualf f) (dualf g) (dualf h)). Qed.


Module BourbakiWitt.
Section b.
 Context {X: CPO'.type}.
 Variable f: X -eqv-> X. 
 Hypothesis f_ctr: forall x, f x <= x. 
 Definition fixpoint: X := BourbakiWitt.fixpoint (dualf f) f_ctr.
 Theorem is_fixpoint: f fixpoint ≡ fixpoint.
 Proof. exact: (BourbakiWitt.is_fixpoint (dualf f) f_ctr). Qed. 
End b. 
End BourbakiWitt. 

Module BourbakiWitt'.
Section b.
 Context {X: CPO'.type}.
 Variable f: X -mon-> X. 
 Definition gfp: X := BourbakiWitt'.lfp (dualf f).
 Theorem is_greatest_fixpoint: is_gfp f gfp.
 Proof. exact: (BourbakiWitt'.is_least_fixpoint (dualf f)). Qed. 
End b. 
#[non_forgetful_inheritance]
HB.instance Definition _ (X: CPO'.type) := PO_gfp.Build X (@gfp X) (@is_greatest_fixpoint X).  
End BourbakiWitt'. 

Module Pataraia. 
Section s.
 Context {X: dCPO'.type}.
 Variable f: X-mon->X.
 Definition gfp: X := Pataraia.lfp (dualf f).     
 Theorem is_greatest_fixpoint: is_gfp f gfp. 
 Proof. exact: (Pataraia.is_least_fixpoint (dualf f)). Qed.
End s.
End Pataraia.

#[non_forgetful_inheritance]
HB.instance Definition _ (X: dCPO'.type) := PO_gfp.Build X (@Pataraia.gfp X) (@Pataraia.is_greatest_fixpoint X).  
