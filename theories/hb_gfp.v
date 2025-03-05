From HB Require Import structures.
From Stdlib Require Classical.
Require Import ssreflect ssrfun ssrbool.
Require Export hb_inf hb_lfp.

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

(** greatest (post-)fixpoints *)
Definition is_gfp f z := z <= f z /\ forall y, y <= f y -> y <= z. 

Lemma is_gfp_leq (f g: X -mon-> X): f <= g -> forall x y, is_gfp f x -> is_gfp g y -> x <= y.
Proof. intros; exact: (is_lfp_leq (f:=dualf g) (g:=dualf f)). Qed.
Lemma is_gfp_unique (f g: X -mon-> X): f ≡ g -> forall x y, is_gfp f x -> is_gfp g y -> x ≡ y.
Proof. intros; exact: (is_lfp_unique (f:=dualf f) (g:=dualf g)). Qed.

(** second half of Knaster-Tarski theorem on montone functions,
    also known as Lambek lemma in category theory *)
Proposition is_gfp_fixpoint (f: X -mon-> X) x: is_gfp f x -> f x ≡ x.
Proof. exact: (is_lfp_fixpoint (dualf f)). Qed.

(** characterisation as the supremum of all post-fixpoints (again, for monotone functions) *)
Proposition is_gfp_sup (f: X -mon-> X) (z: X): is_gfp f z <-> is_sup (fun x => x <= f x) z.
Proof. exact: (is_lfp_inf (dualf f)). Qed.  

End s.

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

Notation gfp := Pataraia.gfp.
Notation is_greatest_fixpoint := Pataraia.is_greatest_fixpoint.

Lemma gfp_pfp {X: dCPO'.type} (f: X -mon-> X): gfp f <= f (gfp f).
Proof. exact: (lfp_pfp (dualf f)). Qed.

Lemma gfp_ind {X: dCPO'.type} (f: X -mon-> X) x: x <= f x -> x <= gfp f.
Proof. exact: (lfp_ind (dualf f)). Qed.

Lemma gfp_fixpoint {X: dCPO'.type} (f: X -mon-> X): f (gfp f) ≡ gfp f.
Proof. exact: (lfp_fixpoint (dualf f)). Qed.

Instance gfp_leq {X}: Proper (leq ==> leq) (@gfp X).
Proof. move=>f g fg. apply: (is_gfp_leq fg); exact: is_greatest_fixpoint. Qed.
Instance gfp_eqv {X}: Proper (eqv ==> eqv) (@gfp X) := op_leq_eqv_1.

Lemma leq_mon_gfp {X Y: dCPO'.type} (f: X-mon->Y) (g: X-mon->X) (h: Y-mon->Y) :
  f ∘ g <= h ∘ f -> f (gfp g) <= gfp h.
Proof. exact: (geq_mon_lfp (dualf f) (dualf g) (dualf h)). Qed.

Lemma rolling_gfp {X Y: dCPO'.type} (f: X-mon->Y) (g: Y-mon->X):
  g (gfp (f ∘ g)) ≡ gfp (g ∘ f).
Proof. exact: (rolling_lfp (dualf f) (dualf g)). Qed.

Lemma geq_adj_gfp {X Y: dCPO'.type} (f: X ⊢ Y) (g: X-mon->X) (h: Y-mon->Y) :
  h ∘ f <= f ∘ g -> gfp h <= f (gfp g).
Proof. exact: (leq_adj_lfp (dualf f) (dualf g) (dualf h)). Qed.

Lemma adj_gfp {X Y: dCPO'.type} (f: X ⊢ Y) (g: X-mon->X) (h: Y-mon->Y) :
  f ∘ g ≡ h ∘ f -> f (gfp g) ≡ gfp h.
Proof. exact: (adj_lfp (dualf f) (dualf g) (dualf h)). Qed.

Lemma exchange_gfp_leq {X Y: dCPO'.type} (f: X ⊢ Y) (g: X-mon->Y) (h: Y-mon->X):
  g ∘ h ∘ f <= f ∘ h ∘ g  -> gfp (g ∘ h) <= gfp (f ∘ h).
Proof. exact: (exchange_lfp_leq (dualf f) (dualf g) (dualf h)). Qed. (* slow, why? *)
Lemma exchange_gfp_leq' {X Y: dCPO'.type} (f: X ⊢ Y) (g: X-mon->Y) (h: Y-mon->X):
  g ∘ h ∘ f <= f ∘ h ∘ g  -> gfp (h ∘ g) <= gfp (h ∘ f).
Proof. exact: (exchange_lfp_leq' (dualf f) (dualf g) (dualf h)). Qed. (* slow, why? *)

Lemma exchange_gfp_eqv {X Y: dCPO'.type} (f g: X ⊢ Y) (h: Y-mon->X):
  f ∘ h ∘ g ≡ g ∘ h ∘ f -> gfp (f ∘ h) ≡ gfp (g ∘ h).
Proof. exact: (exchange_lfp_eqv (dualf f) (dualf g) (dualf h)). Qed.
Lemma exchange_gfp_eqv' {X Y: dCPO'.type} (f g: X ⊢ Y) (h: Y-mon->X):
  f ∘ h ∘ g ≡ g ∘ h ∘ f -> gfp (h ∘ f) ≡ gfp (h ∘ g).
Proof. exact: (exchange_lfp_eqv' (dualf f) (dualf g) (dualf h)). Qed.
