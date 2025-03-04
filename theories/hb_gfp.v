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
Proposition gfp_fixpoint (f: X -mon-> X) x: is_gfp f x -> f x ≡ x.
Proof. exact: (lfp_fixpoint (dualf f)). Qed.

(** characterisation as the supremum of all post-fixpoints (again, for monotone functions) *)
Lemma is_gfp_sup (f: X -mon-> X) (z: X): is_gfp f z <-> is_sup (fun x => x <= f x) z.
Proof. exact: (is_lfp_inf (dualf f)). Qed.  

End s.

Module BourbakiWitt.
Section b.
 Context {X: CPO'.type}.
 Variable f: X -eqv-> X. 
 Hypothesis f_ctr: forall x, f x <= x. 
 Definition fixpoint': X := BourbakiWitt.fixpoint (dualf f) f_ctr.
 Theorem is_fixpoint': f fixpoint' ≡ fixpoint'.
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
