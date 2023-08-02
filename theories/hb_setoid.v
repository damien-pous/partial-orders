From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Export preliminaries.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

(** * setoids *)

(** ** class *)

HB.mixin Record isSetoid (X: Type) := {
  #[canonical=no] eqv: relation X;
  #[canonical=no] Equivalence_eqv: Equivalence eqv
}.
HB.structure Definition Setoid :=
  { X of isSetoid X }.
Infix "≡" := eqv (at level 70).
Notation "x ≡[ X ] y" := (@eqv X x y) (at level 70, only parsing).

(** testing that two setoids are definitionally equal *)
Notation unify_setoids X Y := (unify (X: Setoid.type) (Y: Setoid.type)).

(** ** morphisms *)

HB.mixin Record isExtensional (X Y: Setoid.type) (f: X -> Y) := {
  #[canonical=no] extensional: Proper (eqv ==> eqv) f
}.
HB.structure Definition setoid_morphism (X Y: Setoid.type) :=
  { f of isExtensional X Y f }.
Notation "X '-eqv->' Y" := (setoid_morphism.type X Y) (at level 99, Y at level 200).

(** identity morphism *)
HB.instance Definition _ {X} :=
  isExtensional.Build X X types_id (fun _ _ H => H). 
Notation setoid_id := (types_id: _ -eqv-> _) (only parsing). 

(** composition of morphisms *)
Program Definition setoid_comp {X Y Z} (f: Y-eqv->Z) (g: X-eqv->Y) := 
  isExtensional.Build X Z (types_comp f g) _.
Next Obligation. move=>x y xy. by do 2 apply extensional. Qed. 
HB.instance Definition _ {X Y Z} f g := @setoid_comp X Y Z f g.

(** constant morphism *)
Program Canonical Structure setoid_const {X Y: Setoid.type} (y: Y) :=
  isExtensional.Build X Y (const y) _.
Next Obligation. move=>/=_ _ _. apply Equivalence_eqv. Qed.
HB.instance Definition _ {X Y} y := @setoid_const X Y y.

(** ** properties *)

#[export] Existing Instance Equivalence_eqv.
#[export] Existing Instance extensional.
Lemma eqv_refl {X: Setoid.type} (x: X): x ≡ x.
Proof. reflexivity. Qed.
Lemma eqv_sym {X: Setoid.type} (x y: X): x ≡ y -> y ≡ x.
Proof. apply symmetry. Qed.
#[export] Hint Extern 0 (_ ≡ _)=> exact: (eqv_refl _) || apply: eqv_sym; assumption: core.

(** ** duality *)
(** trivial for setoids, but required for subsequent layers *)

Definition dual (X: Type) := X.
HB.instance Definition _ {X: Setoid.type} := isSetoid.Build (dual X) Equivalence_eqv.

Definition dualf {X Y: Type} (f: X -> Y): dual X -> dual Y := f.
Program Definition setoid_dualf {X Y} (f: X -eqv-> Y)
  := isExtensional.Build (dual X) (dual Y) (dualf f) extensional.
HB.instance Definition _ {X Y} f := @setoid_dualf X Y f.

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
Definition eq_setoid X := isSetoid.Build X eq_equivalence.
HB.instance Definition _ := eq_setoid bool.

(** trivial setoids, for proof irrelevant types *)
Definition trivial (X: Type) := X.
Program Definition setoid_trivial (X: Type) := isSetoid.Build (trivial X) (eqv := fun _ _ => True) _.
Next Obligation. split; firstorder. Qed.
HB.instance Definition _ X := setoid_trivial X. 
HB.instance Definition _ := Setoid.copy unit (trivial unit). 

(** setoid of extensional propositions *)
HB.instance Definition _ := isSetoid.Build Prop iff_equivalence. 

(** setoid of extenstional functions (between types)
    NB: different from extensional functions between setoids (setoid_morphisms), here we use [eq] on the codomain *)
Definition efun X Y := arrow X Y.
Definition eid {X}: efun X X := types_id. 
HB.instance Definition _ X Y :=
  isSetoid.Build (efun X Y) (@Equivalence.pointwise_equivalence X Y eq eq_equivalence). 

(** (dependent) function space *)
Section dprod.
 Variables (A: Type) (X: A -> Setoid.type).
 Definition eqv_dprod: relation (forall a, X a) := fun f g => forall a, f a ≡ g a.
 Lemma setoid_dprod: Equivalence eqv_dprod.
 Proof.
   constructor.
   - by move=>??. 
   - by move=>????; symmetry. 
   - by move=>??????; etransitivity; eauto.
 Qed.
 HB.instance Definition _ := isSetoid.Build (forall a, X a) setoid_dprod.  
End dprod.
Arguments eqv_dprod {_ _} _ _/.
Definition app {A} {X: A -> Type} (a: A): (forall a, X a) -> X a := fun f => f a.
Definition setoid_app {A} {X: A -> Setoid.type} (a: A) :=
  isExtensional.Build (forall a, X a) (X a) (app a) (fun f g fg => fg a).
HB.instance Definition _ A X a := @setoid_app A X a.

(** direct sum and product *)
Section sumprod.
 Variables (X Y: Setoid.type).
 Definition eqv_prod: relation (X*Y) := fun x y => fst x ≡ fst y /\ snd x ≡ snd y.
 Lemma setoid_prod: Equivalence eqv_prod.
 Proof.
   constructor=>//.
   - by move=>??[]; split; symmetry. 
   - by move=>???[??][]; split; etransitivity; eassumption.
 Qed.
 HB.instance Definition _ :=
   isSetoid.Build _ setoid_prod.
 HB.instance Definition _ :=
   isExtensional.Build (prod X Y) X fst (fun p q pq => proj1 pq).
 HB.instance Definition _ :=
   isExtensional.Build (prod X Y) Y snd (fun p q pq => proj2 pq).

 Definition eqv_sum: relation (X+Y) :=
   fun x y => match x,y with inl x,inl y | inr x,inr y => x ≡ y | _,_ => False end.
 Lemma setoid_sum: Equivalence eqv_sum.
 Proof.
   constructor.
   - by move=>[]//=. 
   - by move=>[?|?][?|?]//=; symmetry. 
   - by move=>[?|?][?|?][?|?]//=; etransitivity; eassumption.
 Qed.
 HB.instance Definition _ :=
   isSetoid.Build _ setoid_sum.
 HB.instance Definition _ :=
   isExtensional.Build X (sum X Y) inl (fun p q pq => pq).
 HB.instance Definition _ :=
   isExtensional.Build Y (sum X Y) inr (fun p q pq => pq).
End sumprod.
Arguments eqv_prod {_ _} _ _/. 
Arguments eqv_sum {_ _}_ _/. 

(** option & list setoids *)
Section optionlist.
 Variables (X: Setoid.type).
 Definition eqv_option (p q: option X) :=
  match p,q with Some p,Some q => p≡q | None,None => True | _,_ => False end.
 Lemma setoid_option: Equivalence eqv_option.
 Proof.
   constructor.
   by move=>[?|]//=. 
   by move=>[?|][?|]//=. 
   by move=>[?|][y|][?|]??//=; transitivity y. 
 Qed.
 HB.instance Definition _ := isSetoid.Build _ setoid_option.

 Fixpoint eqv_list (h k: list X) :=
   match h,k with cons x h,cons y k => x≡y /\ eqv_list h k | nil,nil => True | _,_ => False end.
 Lemma setoid_list: Equivalence eqv_list.
 Proof.
   constructor.
   - by elim=>//.
   - by elim=>[|x h IH][|y k]//=[? ?]; split; auto. 
   - elim=>[|x h IH][|y k][|z l]//=[? ?][? ?]; split; try etransitivity; eauto. 
 Qed.
 HB.instance Definition _ := isSetoid.Build _ setoid_list.
End optionlist.
Arguments eqv_option [_] _ _/.
Arguments eqv_list [_] _ _/.

(** constructing setoids via functions into other setoids *)
Definition kernel {A X: Type} (f: A -> X) := A.
Definition kernelf {A X: Type} (f: A -> X): kernel f -> X := f.
Section kernel.
 Variables (A: Type) (X: Setoid.type) (f: A -> X).
 Definition eqv_kern: relation (kernel f) := fun x y => f x ≡ f y.
 Lemma setoid_kern: Equivalence eqv_kern.
 Proof.
   rewrite /eqv_kern.
   constructor.
   - by move=>?; reflexivity. 
   - by move=>???; symmetry. 
   - by move=>?????; etransitivity; eauto.
     (* need to be Defined so that kernel compositions properly reduce *)     
 Defined. 
 HB.instance Definition _ := isSetoid.Build (kernel f) setoid_kern.
 HB.instance Definition _ := isExtensional.Build (kernel f) X (kernelf f) (fun _ _ xy => xy). 
End kernel.
Arguments eqv_kern [_ _] _ _ _/.

(** sub-setoids as a special case *)
HB.instance Definition _ (X: Setoid.type) (P: X -> Prop) :=
  Setoid.copy (sig P) (kernel (@proj1_sig X P)).
HB.instance Definition _ (X: Setoid.type) (P: X -> Prop) :=
  isExtensional.Build (sig P) X (@proj1_sig X P) (fun p q pq => pq).

(** extensional functions as special case *)
HB.instance Definition _ {X Y: Setoid.type} :=
  Setoid.copy (X-eqv->Y) (kernel (fun f: X-eqv->Y => f: X -> Y)).

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
Proof. move=>/=f f' ff' g g' gg' x=>/=. rewrite (gg' x). apply ff'. Qed.
