Require Import ssreflect ssrfun ssrbool.
Require Export preliminaries.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

(** * setoids *)

(** ** class *)

Module Setoid.
Record mixin X := from_type {
    eqv: relation X;
    axm: Equivalence eqv;
}.
Structure type := pack {
    sort:> Type;
    #[canonical=no] mix: mixin sort;
}.
Notation copy T X := (@pack T (mix X)).
Definition Build X eq eqE := @pack X (@from_type X eq eqE). 
Arguments Build: clear implicits. 
End Setoid.
#[reversible] Coercion Setoid.sort: Setoid.type >-> Sortclass.
Definition eqv {X: Setoid.type} := Setoid.eqv (Setoid.mix X).
Infix "≡" := eqv (at level 70).
Infix "≡[ X ]" := (@eqv X) (at level 70, only parsing).

#[export] Instance Equivalence_eqv {X}: Equivalence (@eqv X) :=
  Setoid.axm _.

(** testing that two setoids are definitionally equal *)
Notation unify_setoids X Y := (unify (X: Setoid.type) (Y: Setoid.type)).

(** ** morphisms *)

Structure setoid_morphism (X Y: Setoid.type) := {
    setoid_body:> X -> Y;
    #[canonical=no] extensional: Proper (eqv ==> eqv) setoid_body;
}.
Arguments Build_setoid_morphism {_ _}.
Arguments extensional {_ _ _}.
#[export] Existing Instance extensional.
Notation "X '-eqv->' Y" := (setoid_morphism X Y) (at level 99, Y at level 200).

(** identity morphism *)
Canonical Structure setoid_id {X}: X-eqv->X :=
  Build_setoid_morphism types_id _.

(** composition of morphisms *)
Canonical Structure setoid_comp {X Y Z} (f: Y-eqv->Z) (g: X-eqv->Y): X-eqv->Z :=
  Build_setoid_morphism (f ∘ g) _. 

(** constant morphism *)
Program Canonical Structure setoid_const {X Y: Setoid.type} (y: Y): X-eqv->Y :=
  Build_setoid_morphism (const y) _.
Next Obligation. by move=>/=_ _ _. Qed.

(** ** properties *)

Lemma eqv_refl {X: Setoid.type} (x: X): x ≡ x.
Proof. reflexivity. Qed.
Lemma eqv_sym {X: Setoid.type} (x y: X): x ≡ y -> y ≡ x.
Proof. apply symmetry. Qed.
#[export] Hint Extern 0 (_ ≡ _)=> exact: (eqv_refl _) || apply: eqv_sym; assumption: core.

(** ** duality *)
(** trivial for setoids, but required for subsequent layers *)

Definition dual (X: Type) := X.
Canonical Structure dual_setoid (X: Setoid.type) := Setoid.copy (dual X) X.

Definition dualf {X Y: Type} (f: X -> Y): dual X -> dual Y := f.
Program Canonical Structure dual_setoid_morphism {X Y} (f: X -eqv-> Y): dual X -eqv-> Y :=
  Build_setoid_morphism (dualf f) extensional.
Ltac dual0 t :=
  match type of t with
  | forall X: ?T, _ =>
      match goal with
      | X: T |- _ => apply: (t (dual X))
      end
  end.
Ltac dual t := dual0 t.

(** ** instances *)

(** discrete setoids, for types where [eq] is fine *)
Definition eq_setoid X := Setoid.Build X eq eq_equivalence.
Canonical Structure bool_setoid := eq_setoid bool.

(** trivial setoids, for proof irrelevant types *)
Definition trivial (X: Type) := X.
Program Canonical Structure trivial_setoid (X: Type) :=
  Setoid.Build (trivial X) (fun _ _ => True) _.
Next Obligation. firstorder. Qed.
Canonical Structure unit_setoid :=
  Setoid.copy unit (trivial unit). 

(** setoid of extensional propositions *)
Canonical Structure Prop_setoid :=
  Setoid.Build Prop iff _.

(** (dependent) function space *)
Program Canonical Structure dprod_setoid A (X: A -> Setoid.type) :=
  Setoid.Build (forall a, X a) (fun f g => forall a, f a ≡ g a) _.
Next Obligation.
  constructor.
  - by move=>??. 
  - by move=>????; symmetry. 
  - by move=>??????; etransitivity; eauto.
Qed.
Definition app {A} {X: A -> Type} (a: A): (forall a, X a) -> X a := fun f => f a.
Canonical Structure setoid_app {A} {X: A -> Setoid.type} (a: A): (forall a, X a) -eqv-> X a :=
  Build_setoid_morphism (app a) (fun f g fg => fg a).

Section s.
 Variables (X Y: Setoid.type).

 (** direct product *)
 Program Canonical Structure prod_setoid :=
   Setoid.Build (X*Y) (fun p q => fst p ≡ fst q /\ snd p ≡ snd q) _.
 Next Obligation.
   constructor=>//.
   by move=>??[??]; split; symmetry; assumption.
   by move=>???[??][]; split; etransitivity; eassumption.
 Qed.
 Canonical Structure setoid_fst: (prod X Y) -eqv-> X :=
  Build_setoid_morphism fst (fun p q pq => proj1 pq).
 Canonical Structure setoid_snd: (prod X Y) -eqv-> Y :=
  Build_setoid_morphism snd (fun p q pq => proj2 pq).

 (** direct sum *)
 Definition eqv_sum (p q: X+Y) :=
   match p,q with inl p,inl q | inr p,inr q => p ≡ q | _,_ => False end.
 Program Canonical Structure sum_setoid := Setoid.Build (X+Y) eqv_sum _.
 Next Obligation.
   constructor.
   by move=>[?|?]//=. 
   by move=>[?|?][?|?]?//=. 
   by move=>[?|?][y|y][?|?]??//=; transitivity y. 
 Qed.
 Canonical Structure setoid_inl: X -eqv-> (sum X Y) :=
  Build_setoid_morphism inl (fun p q pq => pq).
 Canonical Structure setoid_inr: Y -eqv-> (sum X Y) :=
  Build_setoid_morphism inr (fun p q pq => pq).

 (** option type *)
 Definition eqv_option (p q: option X) :=
   match p,q with Some p,Some q => p≡q | None,None => True | _,_ => False end.
 Program Canonical Structure option_setoid :=
   Setoid.Build (option X) eqv_option _.
 Next Obligation.
   constructor.
   by move=>[?|]//=. 
   by move=>[?|][?|]//=. 
   by move=>[?|][y|][?|]??//=; transitivity y. 
 Qed.
 Canonical Structure setoid_Some: X -eqv-> option X :=
  Build_setoid_morphism Some (fun p q pq => pq).

End s.

(** constructing setoids via functions into other setoids *)
Definition kernel {A X: Type} (f: A -> X) := A.
Definition kernelf {A X: Type} (f: A -> X): kernel f -> X := f.
Section kernel.
 Variables (A: Type) (X: Setoid.type) (f: A -> X).
 Program Canonical Structure kern_setoid A (X: Setoid.type) (f: A -> X) :=
   Setoid.Build (kernel f) (fun a b => f a ≡ f b) _.
 Next Obligation.
   constructor.
   - by move=>?; reflexivity. 
   - by move=>???; symmetry.
   - by move=>?????; etransitivity; eauto.
 Defined.
 Canonical Structure setoid_kernelf: (kernel f) -eqv-> X :=
   Build_setoid_morphism (kernelf f) (fun p q pq => pq).
End kernel.
(* NB: [kern_setoid] should be defined carefully, and left transparent, so that we have:  *)
(* Check fun (X: Setoid.type) (f g: X -> X) => *)
(*         unify_setoids *)
(*           (kernel (X:=kernel g) f) *)
(*           (kernel (types_comp g f)). *)

(** sub-setoids as a special case *)
Canonical Structure sig_setoid (X: Setoid.type) (P: X -> Prop) :=
  Setoid.copy (sig P) (kernel (@proj1_sig X P)).
Canonical Structure setoid_proj1_sig (X: Setoid.type) (P: X -> Prop): (sig P) -eqv-> X :=
  Build_setoid_morphism (@proj1_sig X P) (fun p q pq => pq).

(** extensional functions as special case *)
Canonical Structure setoid_morphisms_setoid {X Y: Setoid.type} :=
  Setoid.copy (X-eqv->Y) (kernel (@setoid_body X Y)).

(** extensionality of the constant function construction *)
#[export] Instance const_eqv {X} {Y: Setoid.type}:
  Proper (eqv ==> eqv) (@const Y X).
Proof. move=>/=y y' yy x. apply yy. Qed.
#[export] Instance const_eqv' {X} {Y: Setoid.type}:
  Proper (eqv ==> @eqv (X-eqv->Y)) (@const Y X) := const_eqv.

(** extensionality of functional composition,
    provided the outer function is extensive *)
Lemma types_comp_eqv {X Y Z: Setoid.type}:
  Proper (@eqv (Y-eqv->Z) ==> eqv ==> eqv) (@types_comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x=>/=. rewrite (gg' x). apply: ff'. Qed.

(** the following restrictions are useful for [setoid_rewrite] *)
(* TOTHINK: redundant with support to come in cs_categories? *)
#[export] Instance setoid_comp_eqv {X Y Z: Setoid.type}: Proper (eqv ==> eqv ==> eqv) (@setoid_comp X Y Z) := types_comp_eqv.
#[export] Instance setoid_const_eqv {X} {Y: Setoid.type}: Proper (eqv ==> eqv) (@setoid_const X Y) := const_eqv.
