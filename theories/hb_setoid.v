From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Export preliminaries.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

(** * setoids *)

(** ** class *)

#[primitive]
HB.mixin Record isSetoid (X: Type) := {
  #[canonical=no] eqv: relation X;
  #[canonical=no] axm: Equivalence eqv
}.
(* #[primitive] *)
HB.structure Definition Setoid :=
  { X of isSetoid X }.
Infix "≡" := eqv (at level 70).
Infix "≡[ X ]" := (@eqv X) (at level 70, only parsing).
Notation unify_setoids X Y := (same Setoid.type X Y).

(** ** properties *)

Instance Equivalence_eqv {X}: Equivalence (@eqv X) :=
  isSetoid.axm _.

Lemma eqv_refl {X: Setoid.type} (x: X): x ≡ x.
Proof. exact: reflexivity. Qed.
Arguments eqv_refl {_ _}, {_}.
Lemma eqv_sym {X: Setoid.type} (x y: X): x ≡ y -> y ≡ x.
Proof. exact: symmetry. Qed.
Lemma eqv_trans {X: Setoid.type} (x y z: X): x ≡ y -> y ≡ z -> x ≡ z.
Proof. exact: transitivity. Qed.
Lemma eq_eqv {X: Setoid.type} (x y: X): x = y -> x ≡ y.
Proof. by move=>->. Qed.

Hint Extern 0 (_ ≡ _) =>
  exact: (eqv_refl _) ||
  apply: eqv_sym; assumption: core.


(** ** duality *)
(** trivial for setoids, but required for subsequent layers *)

Definition dual (X: Type) := X.
HB.instance Definition _setoid_on_dual (X: Setoid.type) := Setoid.on (dual X).

(* for expanding a structure, to help with duality *)
Definition eta (X: Type) := X.
HB.instance Definition _setoid_on_eta (X: Setoid.type) := Setoid.on (eta X).

Section s.
  Variable X: Setoid.type.
  Fail Check same Setoid.type X (dual (dual X)). (* needs Setoid.type to be #[primitive] *)
  Check same Setoid.type (eta X) (dual (dual X)).
End s.

Ltac dual0 t :=
  match type of t with
  | forall X: ?T, _ =>
      match goal with
      | X: T |- _ => apply: (t (dual X))
      end
  end.
Ltac dual t := dual0 t.


(** ** morphisms *)

#[primitive]
HB.mixin Record isExtensional (X Y: Setoid.type) (f: X -> Y) := {
  #[canonical=no] extensional: Proper (eqv ==> eqv) f
  }.
(* #[primitive] *)
HB.structure Definition setoid_morphism (X Y: Setoid.type) :=
  { f of isExtensional X Y f }.
Existing Instance extensional.
Notation "X '-eqv->' Y" := (setoid_morphism.type X Y) (at level 99, Y at level 200).

Section s.
 Context {X Y: Setoid.type}.
 Definition mk_ext (f: X -> Y) (Hf: Proper (eqv ==> eqv) f) := f.
 HB.instance Definition _ f Hf := isExtensional.Build X Y (@mk_ext f Hf) Hf.
End s.
Arguments mk_ext {_ _}.

(** identity morphism *)
HB.instance Definition _ {X} :=
  isExtensional.Build X X types_id (fun _ _ H => H).
Notation setoid_id := (types_id: _ -eqv-> _) (only parsing). 

(** composition of morphisms *)
Definition setoid_comp {X Y Z} (f: Y-eqv->Z) (g: X-eqv->Y) := 
  isExtensional.Build X Z (types_comp f g) _.
HB.instance Definition _ {X Y Z} f g := @setoid_comp X Y Z f g.

(** constant morphism *)
Program Definition setoid_const {X Y: Setoid.type} (y: Y) :=
  isExtensional.Build X Y (const y) _.
Next Obligation. by move=>/=_ _ _. Qed.
HB.instance Definition _ {X Y} y := @setoid_const X Y y.

(** dual morphisms *)
Definition dualf {X Y: Type} (f: X -> Y): dual X -> dual Y := f.
Program Definition setoid_dualf {X Y} (f: X -eqv-> Y)
  := isExtensional.Build (dual X) (dual Y) (dualf f) extensional.
HB.instance Definition _ {X Y} f := @setoid_dualf X Y f.

(** expanded morphisms *)
Definition etaf {X Y: Type} (f: X -> Y): eta X -> eta Y := f.
HB.instance Definition _ {X Y} (f: X-eqv->Y) := isExtensional.Build (eta X) (eta Y) (etaf f) (@extensional X Y f).

Section s.
  Variables (X Y: Setoid.type) (f: X-eqv->Y).
  Check same (X-eqv->Y) (etaf f) (dualf f).
  Check same (X-eqv->Y) (etaf f) (dualf (dualf f)).
End s.

(** ** strict setoids, where [eqv=eq] *)

Definition eq_setoid X := isSetoid.Build X eq_equivalence.

#[primitive]
HB.mixin Record Setoid_isStrict X of Setoid X := {
  #[canonical=no] eqv_eq: subrelation eqv (@eq X);
}.
HB.structure Definition StrictSetoid := { X of Setoid_isStrict X & }.

HB.factory Record isStrictSetoid X := {}.
HB.builders Context X of isStrictSetoid X.
  HB.instance Definition _ := eq_setoid X.
  HB.instance Definition _ := Setoid_isStrict.Build X _.
HB.end.
Notation strict_setoid X := (isStrictSetoid.Build X).

Definition strict (X: Type) := X.
HB.instance Definition _ X := strict_setoid (strict X).

HB.factory Record StrictThusExtensional (X: StrictSetoid.type) (Y: Setoid.type) (f: X -> Y) := {}.
HB.builders Context X Y f of StrictThusExtensional X Y f.
  Lemma extensional: Proper (eqv ==> eqv) f.
  Proof. by move=>x y /eqv_eq ->. Qed.
  HB.instance Definition _ := isExtensional.Build X Y f extensional. 
HB.end.
Definition strictext {X: StrictSetoid.type} {Y: Setoid.type} (f: X -> Y) := f.   
HB.instance Definition _ X Y f := StrictThusExtensional.Build X Y (strictext f).


(** ** instances *)

(** trivial setoids, for proof irrelevant types *)
Program Definition trivial_setoid X := isSetoid.Build X (eqv := fun _ _ => True) _.
Next Obligation. firstorder. Qed.
Definition trivial (X: Type) := X.
HB.instance Definition _ X := trivial_setoid (trivial X).

(** trivial & strict setoid for the empty type *)
HB.instance Definition _ := trivial_setoid False.
HB.instance Definition _ := Setoid_isStrict.Build False (fun x y _ => False_eq x y).

(** trivial & strict setoid for the unit type *)
HB.instance Definition _ := trivial_setoid unit.
HB.instance Definition _ := Setoid_isStrict.Build unit (fun x y _ => unit_eq x y).

(** strict setoid for [bool] and [nat] *)
HB.instance Definition _ := strict_setoid bool.
HB.instance Definition _ := strict_setoid nat.

(** setoid of extensional propositions *)
HB.instance Definition _ := isSetoid.Build Prop iff_equivalence. 

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

(** product, sum, and option on Setoids *)
Section s.
 Variables (X Y: Setoid.type).

 (** direct product *)
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

 (** direct sum *)
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

 (** option type *)
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
 HB.instance Definition _ :=
   isExtensional.Build X (option X) Some (fun p q pq => pq).
 
End s.
Arguments eqv_prod {_ _} _ _/. 
Arguments eqv_sum {_ _}_ _/. 
Arguments eqv_option {_}_ _/. 

(** product, sum, and option on strict Setoids *)
Section s.
 Variables (X Y: StrictSetoid.type).

 (** direct product *)
 Lemma strictsetoid_prod: subrelation eqv (@eq (X*Y)).
 Proof. move=>[??][??][/eqv_eq?/eqv_eq?]. by f_equal. Qed.
 HB.instance Definition _ := Setoid_isStrict.Build (prod X Y) strictsetoid_prod.

 (** direct sum *)
 Lemma strictsetoid_sum: subrelation eqv (@eq (X+Y)).
 Proof. move=>[?|?][?|?]///eqv_eq?; by f_equal. Qed.
 HB.instance Definition _ := Setoid_isStrict.Build (sum X Y) strictsetoid_sum.

 (** option *)
 Lemma strictsetoid_option: subrelation eqv (@eq (option X)).
 Proof. move=>[?|][?|]///eqv_eq?; by f_equal. Qed.
 HB.instance Definition _ := Setoid_isStrict.Build (option X) strictsetoid_option.
End s.

(** constructing setoids via functions into other setoids *)
Definition kernel {A X: Type} (f: A -> X) := A.
Definition kernelf {A X: Type} (f: A -> X): kernel f -> X := f.
Section kernel.
 Variables (A: Type) (X: Setoid.type) (f: A -> X).
 Definition eqv_kern: relation (kernel f) := fun x y => f x ≡ f y.
 Lemma kern_setoid: Equivalence eqv_kern.
 Proof.
   rewrite /eqv_kern.
   constructor.
   - by move=>?; reflexivity. 
   - by move=>???; symmetry. 
   - by move=>?????; etransitivity; eauto.
 Defined. 
 HB.instance Definition _ := isSetoid.Build (kernel f) kern_setoid.
 HB.instance Definition _ := isExtensional.Build (kernel f) X (kernelf f) (fun _ _ xy => xy). 
End kernel.
Arguments eqv_kern [_ _] _ _ _/.
(* NB: [kern_setoid] should be defined carefully, and left transparent, so that we have:  *)
Check fun (X Y Z: Setoid.type) (f: X -> Y) (g: Y -> Z) =>
        same Setoid.type
          (kernel (X:=kernel g) f)
          (kernel (g ∘ f)).

(** sub-setoids as a special case *)
HB.instance Definition _ (X: Setoid.type) (P: X -> Prop) :=
  Setoid.copy (sig P) (kernel sval).
HB.instance Definition _ (X: Setoid.type) (P: X -> Prop) :=
  isExtensional.Build (sig P) X sval (fun p q pq => pq).

(** extensional functions as special case *)
HB.instance Definition _ {X Y: Setoid.type} :=
  Setoid.copy (X-eqv->Y) (kernel (@setoid_morphism.sort X Y)).
Definition setoidbody {X Y} := kernelf (@setoid_morphism.sort X Y).

(** extensionality of functional composition,
    provided the outer function is extensive *)
Lemma types_comp_eqv {X Y Z: Setoid.type}:
  Proper (@eqv (Y-eqv->Z) ==> eqv ==> eqv) (@types_comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x=>/=. rewrite (gg' x). exact: ff'. Qed.

(** extensionality of the constant function construction *)
Instance const_eqv {X} {Y: Setoid.type}:
  Proper (eqv ==> eqv) (@const Y X).
Proof. move=>/=y y' yy x. apply yy. Qed.
Instance const_eqv' {X} {Y: Setoid.type}:
  Proper (eqv ==> @eqv (X-eqv->Y)) (@const Y X) := const_eqv.


(** ** categories (for [id] and [°] notations (TOFIX: broken), and isomorphisms) *)


(* #[universes(polymorphic=yes)] *)
Structure CATEGORY := {
    ob: Type;
    hom: ob -> ob -> Setoid.type;
#[canonical=no] id: forall {A}, hom A A;
#[canonical=no] comp: forall {A B C}, hom B C -> hom A B -> hom A C;
#[canonical=no] comp_eqv:: forall {A B C}, Proper (eqv ==> eqv ==> eqv) (@comp A B C);
(* #[canonical=no] idl: forall {A B} f, @comp A A B f id ≡ f; *)
(* #[canonical=no] idr: forall {A B} f, @comp B A A id f ≡ f; *)
(* #[canonical=no] compA: forall {A B C D} f g h, @comp A B D (@comp B C D h g) f ≡ @comp A C D h (@comp A B C g f) *)
  }.
Arguments hom {_} _ _.
Arguments id {_ _}.
Arguments comp {_ _ _ _}.
Infix "°" := comp.

(* Record Iso {C} (X Y: ob C) := { *)
(*     fwd: hom X Y;  *)
(*     bwd: hom Y X;  *)
(*     isoE: fwd ° bwd ≡ id; *)
(*     isoE': bwd ° fwd ≡ id *)
(*   }. *)
(* Infix "≃" := Iso (at level 70).  *)
(* Infix "≃[ C ] " := (@Iso C) (at level 70, only parsing).  *)

(* Definition iso_sym {C} (X Y: ob C): X ≃ Y -> Y ≃ X. *)
(*   move=>i. exists (bwd i) (fwd i). exact: isoE'. exact: isoE. *)
(* Defined. *)

(** the category of setoids and extensional functions *)
Program Canonical Structure SETOIDS :=
  {|
    ob := Setoid.type;
    (* below: want to write [X -eqv-> Y], but then the canonical projection is on "reversible coercions"; *)
    hom X Y := setoid_morphism_type__canonical__hb_setoid_Setoid X Y; 
    comp := @types_comp;
    id := @types_id;
    comp_eqv := @types_comp_eqv;
  |}.

(* Check forall X: Setoid.type, forall f: hom X X, f ° f ≡ f ° f. *)
(* Fail Check forall f: hom Prop Prop, True. *)
(* Check forall f: Prop -eqv-> Prop, f ° f ≡ f ° f. *)


(* Definition bool_dfun {X Y: Setoid.type} (x: X) (y: Y): forall b, bool_fun X Y b := fun b => if b return bool_fun X Y b then y else x. *)
(* Section prod_dprod_bool. *)
(*   Context {X Y: Setoid.type}. *)
(*   Program Definition iso_prod_dprod_bool: prod X Y ≃[SETOIDS] forall b, bool_fun X Y b := *)
(*     {| *)
(*       fwd := mk_ext (fun p => (bool_dfun p.1 p.2)) _; *)
(*       bwd := mk_ext (fun h => (h false, h true)) _; *)
(*     |}. *)
(*   Next Obligation. by move=>p q [??][]. Qed. *)
(*   Next Obligation. by move=>h g; split; apply: H. Qed. *)
(*   Next Obligation. by move => ?[]. Qed. *)
(*   Next Obligation. by split. Qed. *)
(* End prod_dprod_bool. *)


(*

C: CATEGORY
A B: ob C
f: C A B  /  f: A ~> B       hom coercion (parsing only) + notation
id: C A A

f: X -eqv-> Y                (forces X,Y to be setoids)
f: X -mon-> Y                (forces X,Y to be pos)
recogniseds as SETOIDS X Y / POS X Y         by hom indexing

f ° g    fine
f <= g   -> f: PO 



*)





(* HB.mixin Record isCategory (ob: Type) := { *)
(*     #[canonical=no] hom: ob -> ob -> Setoid.type; *)
(*     #[canonical=no] id: forall {A}, hom A A; *)
(*     #[canonical=no] comp: forall {A B C}, hom B C -> hom A B -> hom A C; *)
(*     #[canonical=no] comp_eqv: forall {A B C}, Proper (eqv ==> eqv ==> eqv) (@comp A B C); *)
(*     #[canonical=no] idl: forall {A B} f, @comp A A B f id ≡ f; *)
(*     #[canonical=no] idr: forall {A B} f, @comp B A A id f ≡ f; *)
(*     #[canonical=no] compA: forall {A B C D} f g h, @comp A B D (@comp B C D h g) f ≡ @comp A C D h (@comp A B C g f)     *)
(*   }. *)
(* HB.structure Definition Category := *)
(*   { X of isCategory X }. *)
(* Arguments id {_ _}, {_}. *)
(* Arguments comp {_ _ _ _}. *)
(* Infix "°" := comp. *)



(* (** the category of setoids and extensional functions *) *)
(* HB.instance Definition _ := *)
(*   isCategory.Build *)
(*     Setoid.type *)
(*     (fun X Y => X -eqv-> Y) *)
(*     (@types_id) *)
(*     (@types_comp) *)
(*     (@types_comp_eqv) *)
(*     (fun A B f x => eqv_refl) *)
(*     (fun A B f x => eqv_refl) *)
(*     (fun A B C D f g h x => eqv_refl). *)


(* Check forall X: Setoid.type, forall f: hom X X, f ° f ≡ f ° f. *)
(* Fail Check forall f: hom Prop Prop, True. *)
(* Check forall f: Prop -eqv-> Prop, f ° f ≡ f ° f. *)
