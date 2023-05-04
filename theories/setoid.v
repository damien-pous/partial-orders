Require Import ssreflect ssrfun ssrbool.
Require Export Setoid Morphisms Basics.
Require Export preliminaries.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

(** ** class *)

Module Setoid.

Record mixin X := from_type {
    eqv: relation X;
    Equivalence_eqv: Equivalence eqv;
}.
Structure type := pack {
    sort:> Type;
    #[canonical=no] mix: mixin sort;
}.
Notation cast T X := (let X':=X in @pack T (mix X')).
Definition build X eq eqE := @pack X (@from_type X eq eqE). 
Arguments build: clear implicits. 

Structure morphism (X Y: type) := build_morphism {
    body:> X -> Y;
    #[canonical=no] body_eqv: Proper (eqv (mix X) ==> eqv (mix Y)) body;
}.
Arguments build_morphism {_ _}. 

Canonical Structure id {X: type}: morphism X X :=
  build_morphism Datatypes.id _.
Program Canonical Structure comp {X Y Z: type} (f: morphism Y Z) (g: morphism X Y): morphism X Z :=
  build_morphism (comp f g) _. 
Next Obligation. move=>x y xy. apply f, g, xy. Qed.
Program Canonical Structure const {X Y: type} (y: Y): morphism X Y :=
  build_morphism (const y) _.
Next Obligation. move=>/=_ _ _. apply Equivalence_eqv. Qed.

End Setoid.
Notation Setoid := Setoid.type. 
#[reversible] Coercion Setoid.sort: Setoid >-> Sortclass.
#[reversible] Coercion Setoid.body: Setoid.morphism >-> Funclass.
Notation "X '-eqv->' Y" := (Setoid.morphism X Y) (at level 99, Y at level 200).
Canonical Setoid.id.
Canonical Setoid.comp.
Canonical Setoid.const.
Definition eqv {X: Setoid} := Setoid.eqv (Setoid.mix X).
#[export] Instance Equivalence_eqv {X: Setoid}: @Equivalence X eqv := Setoid.Equivalence_eqv (Setoid.mix X).
#[export] Instance body_eqv {X Y} {f: X-eqv->Y}: Proper (eqv ==> eqv) f := Setoid.body_eqv f.
Infix "≡" := eqv (at level 70).
Infix "≡[ X ]" := (@eqv X) (at level 70, only parsing).
Lemma eqv_refl {X: Setoid} (x: X): x ≡ x.
Proof. reflexivity. Defined.
Lemma eqv_sym {X: Setoid} (x y: X): x ≡ y -> y ≡ x.
Proof. apply symmetry. Defined.
#[export] Hint Extern 0 (_ ≡ _)=> exact: (eqv_refl _) || apply: eqv_sym; assumption: core.

(** ** instances *)

Definition dual (X: Type) := X.
Canonical Structure dual_setoid (X: Setoid) := Setoid.cast (dual X) X.
Program Canonical Structure dual_setoid_morphism {X Y: Setoid} (f: X -eqv-> Y): dual X -eqv-> Y :=
  Setoid.build_morphism f body_eqv.
Ltac dual0 t :=
  match type of t with
  | forall X: ?T, _ =>
      match goal with
      | X: T |- _ => apply: (t (dual X))
      end
  end.
Ltac dual t := dual0 t.

Definition eq_setoid X := Setoid.build X eq eq_equivalence.
Canonical Structure unit_setoid := eq_setoid unit.
Canonical Structure bool_setoid := eq_setoid bool.
Canonical Structure nat_setoid := eq_setoid nat.

(* Program Canonical Structure irrelevant_setoid (P: Prop) := *)
(*   Setoid.build P (fun _ _ => True) _. *)
(* Next Obligation. by constructor. Qed. *)

Canonical Structure Prop_setoid := Setoid.build Prop iff _.

Program Canonical Structure prod_setoid (X Y: Setoid) :=
  Setoid.build (X*Y) (fun p q => fst p ≡ fst q /\ snd p ≡ snd q) _.
Next Obligation.
  constructor=>//.
  by move=>??[??]; split; symmetry; assumption.
  by move=>???[??][]; split; etransitivity; eassumption.
Qed.

Definition sum_eqv {X Y: Setoid} (p q: X+Y) :=
  match p,q with inl p,inl q | inr p,inr q => p ≡ q | _,_ => False end.
Program Canonical Structure sum_setoid (X Y: Setoid) := Setoid.build (X+Y) sum_eqv _.
Next Obligation.
  constructor.
  by move=>[?|?]//=. 
  by move=>[?|?][?|?]?//=. 
  by move=>[?|?][y|y][?|?]??//=; transitivity y. 
Qed.

Definition option_eqv {X: Setoid} (p q: option X) :=
  match p,q with Some p,Some q => p≡q | None,None => True | _,_ => False end.
Program Canonical Structure option_setoid (X: Setoid) :=
  Setoid.build (option X) option_eqv _.
Next Obligation.
  constructor.
  by move=>[?|]//=. 
  by move=>[?|][?|]//=. 
  by move=>[?|][y|][?|]??//=; transitivity y. 
Qed.
  
Fixpoint list_eqv {X: Setoid} (h k: list X) :=
  match h,k with cons x h,cons y k => x≡y /\ list_eqv h k | nil,nil => True | _,_ => False end.
Program Canonical Structure list_setoid (X: Setoid) :=
  Setoid.build (list X) list_eqv _.
Next Obligation.
  constructor.
  - by elim=>//.
  - by elim=>[|x h IH][|y k]//=[? ?]; split; auto. 
  - elim=>[|x h IH][|y k][|z l]//=[? ?][? ?]; split; try etransitivity; eauto. 
Qed.

Program Canonical Structure dprod_setoid A (X: A -> Setoid) :=
  Setoid.build (forall a, X a) (fun f g => forall a, f a ≡ g a) _.
Next Obligation.
  constructor.
  - by move=>??. 
  - by move=>????; symmetry. 
  - by move=>??????; etransitivity; eauto.
Qed.

Program Definition kern_setoid A (X: Setoid) (f: A -> X) :=
  Setoid.build A (fun a b => f a ≡ f b) _.
Next Obligation.
  constructor.
  - by move=>?. 
  - by move=>???.
  - by move=>?????; etransitivity; eauto.
Defined.

Canonical Structure sig_setoid (X: Setoid) (P: X -> Prop) :=
  kern_setoid X (@proj1_sig X P).

Canonical Structure setoid_morphisms_setoid (X Y: Setoid) :=
  kern_setoid _ (@Setoid.body X Y).


(* most general lemma *)
Lemma comp_eqv {X Y Z}: Proper (@eqv (Y-eqv->Z) ==> eqv ==> eqv) (@comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x=>/=. rewrite (gg' x). apply: ff'. Qed.
(* but only this restriction makes it possible to use [setoid_rewrite] *)
#[export] Instance setoid_comp_eqv {X Y Z: Setoid}: Proper (eqv ==> eqv ==> eqv) (@Setoid.comp X Y Z) := comp_eqv.

#[export] Instance const_eqv {X} {Y: Setoid}: Proper (eqv ==> eqv) (@const X Y).
Proof. move=>/=y y' yy' _/=. apply yy'. Qed.
#[export] Instance setoid_const_eqv {X} {Y: Setoid}: Proper (eqv ==> eqv) (@Setoid.const X Y) := const_eqv.
