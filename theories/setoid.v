Require Export preliminaries.
From mathcomp Require Import eqtype. 

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
HB.instance Definition _ (X: Setoid.type) := Setoid.on (dual X).

(* for expanding a structure, to help with duality *)
Definition eta (X: Type) := X.
HB.instance Definition _ (X: Setoid.type) := Setoid.on (eta X).

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

(* setting this structure as primitive would give us definitionally
   involutive duality on morphisms, but it breaks some ssreflect
   rewriting and is considered fragile for CS inferrence
   thus we rely on explicit eta expansions at the few places where we need abstract duality *)
HB.structure Definition setoid_morphism (X Y: Setoid.type) :=
  { f of isExtensional X Y f }.
Existing Instance extensional.
Notation "X '-eqv->' Y" := (setoid_morphism.type X Y) (at level 99, Y at level 200).
Arguments extensional {_ _} _ [_ _]. 
Arguments setoid_morphism.sort [_ _] _ _/: simpl nomatch. 

Section s.
 Context {X Y: Setoid.type}.
 Definition mk_ext' (f: X -> Y) (Hf: Proper (eqv ==> eqv) f) := f.
 HB.instance Definition _ f Hf := isExtensional.Build X Y (@mk_ext' f Hf) Hf.
 Definition mk_ext (f: X -> Y) Hf := @mk_ext' f Hf: X-eqv->Y.
End s.
Arguments mk_ext' {_ _} _ _ _/.
Arguments mk_ext {_ _} _ _.
Notation "'efun' x .. y => p" := (mk_ext (fun x => .. (mk_ext (fun y => p) _) .. ) _)
  (at level 200, x binder, right associativity).

(** identity morphism *)
HB.instance Definition _ {X} :=
  isExtensional.Build X X types_id (fun _ _ H => H).
Notation setoid_id := (types_id: _ -eqv-> _) (only parsing). 

(** composition of morphisms *)
HB.instance Definition _ {X Y Z} (f: X-eqv->Y) (g: Y-eqv->Z) :=
  isExtensional.Build X Z (g ∘ f) (fun _ _ xy => extensional g (extensional f xy)).
Definition setoid_comp {X Y Z} (g: Y-eqv->Z) (f: X-eqv->Y) := g ∘ f: X-eqv->Z.

(** constant morphism *)
Program Definition setoid_const {X Y: Setoid.type} (y: Y) :=
  isExtensional.Build X Y (const y) _.
Next Obligation. by move=>/=_ _ _. Qed.
HB.instance Definition _ {X Y} y := @setoid_const X Y y.

(** dual morphisms *)
Definition dualf {X Y: Type} (f: X -> Y): dual X -> dual Y := f.
HB.instance Definition _ {X Y} (f: X -eqv-> Y) :=
  isExtensional.Build (dual X) (dual Y) (dualf f) (fun _ _ xy => extensional f xy).
Definition dualf' {X Y: Type} (f: dual X -> dual Y): X -> Y := f.
HB.instance Definition _ {X Y: Setoid.type} (f: dual X -eqv-> dual Y) :=
  isExtensional.Build X Y (dualf' f) (fun _ _ xy => extensional f xy).
(* would be definitional if setoid_morphism were declared #[primitive] *)
Lemma dualfE {X Y}: forall f: X-eqv->Y, f = dualf' (dualf f).
Proof. by case. Qed.

(** eta expanded morphisms *)
Definition etaf {X Y: Type} (f: X -> Y): X -> Y := f.
HB.instance Definition _ {X Y} (f: X-eqv->Y) := setoid_morphism.on (etaf f).
(* would be definitional if setoid_morphism were declared #[primitive] *)
Lemma etafE {X Y}: forall f: X -eqv-> Y, f = etaf f.
Proof. by case. Qed.

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

HB.instance Definition _ (X: StrictSetoid.type) := Setoid_isStrict.Build (dual X) eqv_eq.
HB.instance Definition _ (X: StrictSetoid.type) := Setoid_isStrict.Build (eta X) eqv_eq.


(** ** decidable setoids, where [eqv] is decidable *)

#[primitive]
HB.mixin Record Setoid_isDecidable X of Setoid X := {
  #[canonical=no] eqvb: X -> X -> bool;
  #[canonical=no] eqv_dec: forall x y, reflect (x ≡ y) (eqvb x y);
}.
HB.structure Definition DecidableSetoid := { X of Setoid_isDecidable X & }.
Infix "≡?" := eqvb (at level 70). 

HB.factory Record isDecidableSetoid X := {
  #[canonical=no] eqvb: X -> X -> bool;
  #[canonical=no] eqv_refl: forall x, eqvb x x;
  #[canonical=no] eqv_sym: forall x y, eqvb x y -> eqvb y x;
  #[canonical=no] eqv_trans: forall x y z, eqvb x y -> eqvb y z -> eqvb x z;
}.
HB.builders Context X of isDecidableSetoid X.
  Definition eqv (x y: X): Prop := eqvb x y.
  Lemma Equivalence_eqv: Equivalence eqv.
  Proof.
    split; repeat intro.
    - exact: eqv_refl.
    - exact: eqv_sym.
    - apply: eqv_trans; eassumption.
  Qed.
  HB.instance Definition _ := isSetoid.Build X Equivalence_eqv.
  HB.instance Definition _ := Setoid_isDecidable.Build X _ (fun _ _ => idP).
HB.end.

HB.instance Definition _ (X: DecidableSetoid.type) := Setoid_isDecidable.Build (dual X) _ eqv_dec.
HB.instance Definition _ (X: DecidableSetoid.type) := Setoid_isDecidable.Build (eta X) _ eqv_dec.


(** ** strict and decidable setoids, i.e., eqtypes
    (this structure is equivalent to [Equality] from mathcomp.ssreflect) *)
HB.structure Definition Equality' := { X of StrictSetoid X & DecidableSetoid X }.

HB.factory Record eqtype_Setoid X of Equality X := {}.
HB.builders Context X of eqtype_Setoid X.
  HB.instance Definition _ := strict_setoid X. 
  HB.instance Definition _ := Setoid_isDecidable.Build X _ (@eqP X). 
HB.end.
Notation eqtype_setoid X := (eqtype_Setoid.Build X).
  
HB.factory Record eqtype_Decidable X of StrictSetoid X & Equality X := {}.
HB.builders Context X of eqtype_Decidable X.
  Program Definition dec := Setoid_isDecidable.Build X eq_op _.
  Next Obligation.
    apply: equivP. exact: eqP.
    split. by move=>->. exact: eqv_eq. 
  Qed.
HB.instance Definition _ := dec.
HB.end.

(** ** instances *)

(** trivial setoids, for proof irrelevant types *)
Program Definition trivial_setoid X := isDecidableSetoid.Build X (fun _ _ => true) _ _ _.
Next Obligation. done. Qed.
Next Obligation. done. Qed.
Next Obligation. done. Qed.
Definition trivial (X: Type) := X.
HB.instance Definition _ X := trivial_setoid (trivial X).

(** trivial & strict setoid for the empty type *)
HB.instance Definition _ := trivial_setoid False.
HB.instance Definition _ := Setoid_isStrict.Build False (fun x y _ => False_eq x y).
HB.instance Definition _ (X: Setoid.type) := StrictThusExtensional.Build False X empty_fun.

(** trivial & strict setoid for the unit type *)
HB.instance Definition _ := trivial_setoid unit.
HB.instance Definition _ := Setoid_isStrict.Build unit (fun x y _ => unit_eq x y).

(** strict & decidable setoid for [bool] *)
HB.instance Definition _ := eqtype_setoid bool.
HB.instance Definition _ (X: Setoid.type) (x y: X) := StrictThusExtensional.Build bool X (bool_fun x y).

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
Arguments app {_ _} _ _/.
Definition setoid_app {A} {X: A -> Setoid.type} (a: A) :=
  isExtensional.Build (forall a, X a) (X a) (app a) (fun f g fg => fg a).
HB.instance Definition _ A X a := @setoid_app A X a.

(** product, sum, lists, and option on Setoids *)
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

 (** lists *)
 Fixpoint eqv_list (h k: list X) :=
   match h,k with
   | nil,nil => True
   | cons a h,cons b k => a ≡ b /\ eqv_list h k
   | _,_ => False
   end.
 Lemma setoid_list: Equivalence eqv_list.
 Proof.
   constructor.
   - by elim; split. 
   - elim=>[|a h IH] [|b k] //=[ab hk]=>//; split. by symmetry. exact: IH.
   - elim=>[|a h IH] [|b k] [|c l]//=[ab hk] [bc kl]=>//; split.
     by transitivity b. by eauto. 
 Qed.
 HB.instance Definition _ :=
   isSetoid.Build _ setoid_list.
 
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
Arguments eqv_list {_}_ _/. 
Arguments eqv_option {_}_ _/. 

(** product, sum, and option on strict Setoids *)
Section s.
 Variables X Y: StrictSetoid.type.

 (** direct product *)
 Lemma strictsetoid_prod: subrelation eqv (@eq (X*Y)).
 Proof. move=>[??][??][/eqv_eq?/eqv_eq?]. by f_equal. Qed.
 HB.instance Definition _ := Setoid_isStrict.Build (prod X Y) strictsetoid_prod.

 (** direct sum *)
 Lemma strictsetoid_sum: subrelation eqv (@eq (X+Y)).
 Proof. move=>[?|?][?|?]///eqv_eq?; by f_equal. Qed.
 HB.instance Definition _ := Setoid_isStrict.Build (sum X Y) strictsetoid_sum.

 (** lists *)
 Lemma strictsetoid_list: subrelation eqv (@eq (list X)).
 Proof. elim=>[|a h IH][|b k]//[/eqv_eq? /IH?]; by f_equal. Qed.
 HB.instance Definition _ := Setoid_isStrict.Build (list X) strictsetoid_list.

 (** option *)
 Lemma strictsetoid_option: subrelation eqv (@eq (option X)).
 Proof. move=>[?|][?|]///eqv_eq?; by f_equal. Qed.
 HB.instance Definition _ := Setoid_isStrict.Build (option X) strictsetoid_option.
End s.

(** product, sum, and option on decidable Setoids *)
Section s.
 Variables X Y: DecidableSetoid.type.

 (** direct product *)
 Definition eqvb_prod (x y: X*Y) := (fst x ≡? fst y) && (snd x ≡? snd y).
 Program Definition dsetoid_prod := Setoid_isDecidable.Build (prod X Y) eqvb_prod _.
 Next Obligation. apply: andPP; apply eqv_dec. Qed.
 HB.instance Definition _ := dsetoid_prod. 

 (** direct sum *)
 Definition eqvb_sum (x y: X+Y) :=
   match x,y with inl x,inl y | inr x,inr y => x ≡? y | _,_ => false end.
 Program Definition dsetoid_sum := Setoid_isDecidable.Build (sum X Y) eqvb_sum _.
 Next Obligation.
   destruct x; destruct y; cbn.
   exact: eqv_dec. exact: ReflectF.
   exact: ReflectF. exact: eqv_dec.
 Qed.
 HB.instance Definition _ := dsetoid_sum. 

 (** lists *)
 Fixpoint eqvb_list (h k: list X) :=
   match h,k with
   | nil,nil => true
   | cons a h,cons b k => (a ≡? b) && eqvb_list h k
   | _,_ => false
   end.
 Program Definition dsetoid_list := Setoid_isDecidable.Build (list X) eqvb_list _.
 Next Obligation.
   revert x y. 
   elim=>[|a h IH] [|b k]/=.
   - exact: ReflectT. 
   - exact: ReflectF. 
   - exact: ReflectF. 
   - apply: andPP. exact: eqv_dec. exact: IH. 
 Qed.
 HB.instance Definition _ := dsetoid_list. 

 (** option type *)
 Definition eqvb_option (p q: option X) :=
  match p,q with Some p,Some q => p≡?q | None,None => true | _,_ => false end.
 Program Definition dsetoid_option := Setoid_isDecidable.Build (option X) eqvb_option _.
 Next Obligation.
   destruct x; destruct y; cbn.
   exact: eqv_dec. exact: ReflectF.
   exact: ReflectF. exact: ReflectT.
 Qed.
 HB.instance Definition _ := dsetoid_option. 
End s. 
Arguments eqvb_prod [_ _] _ _/.
Arguments eqvb_sum [_ _] _ _/.
Arguments eqvb_list [_]_ _/. 
Arguments eqvb_option [_] _ _/.
HB.saturate prod.
HB.saturate sum.
HB.saturate list.
HB.saturate option.


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
HB.instance Definition _ (A: Type) (X: DecidableSetoid.type) (f: A -> X) :=
  Setoid_isDecidable.Build (kernel f) (fun x y => f x ≡? f y) (fun _ _ => eqv_dec _ _).

(** sub-setoids as a special case *)
HB.instance Definition _ (X: Setoid.type) (P: X -> Prop) :=
  Setoid.copy (sig P) (kernel sval).
HB.instance Definition _ (X: DecidableSetoid.type) (P: X -> Prop) :=
  DecidableSetoid.copy (sig P) (kernel sval).
HB.instance Definition _ (X: Setoid.type) (P: X -> Prop) :=
  isExtensional.Build (sig P) X sval (fun p q pq => pq).

(** extensional functions as special case *)
HB.instance Definition _ {X Y: Setoid.type} :=
  Setoid.copy (X-eqv->Y) (kernel (@setoid_morphism.sort X Y)).
Definition setoidbody {X Y} := kernelf (@setoid_morphism.sort X Y).
Instance setoid_morphism_eqv {X Y}: Proper (eqv ==> eqv ==> eqv) (@setoid_morphism.sort X Y).
Proof. move=>f g fg x y xy. transitivity (g x). exact: fg. by apply g. Qed.

(** extensionality of functional composition,
    provided the outer function is extensive *)
Lemma types_comp_eqv {X} {Y Z: Setoid.type}:
  Proper (@eqv (Y-eqv->Z) ==> eqv ==> eqv) (@types_comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x=>/=. rewrite (gg' x). exact: ff'. Qed.

Instance setoid_comp_eqv {X Y Z: Setoid.type}: Proper (eqv ==> eqv ==> eqv) (@setoid_comp X Y Z) := types_comp_eqv.

(** extensionality of the constant function construction *)
Instance const_eqv {X} {Y: Setoid.type}:
  Proper (eqv ==> eqv) (@const Y X).
Proof. move=>/=y y' yy x. apply yy. Qed.
Instance const_eqv' {X} {Y: Setoid.type}:
  Proper (eqv ==> @eqv (X-eqv->Y)) (@const Y X) := const_eqv.

(** ** sets *)

Section set.
Context {A: Setoid.type}. 
Implicit Types a b c: A.

(** we want sets to be consistent with the setoid structure on [A] *)
Definition set := A -eqv-> Prop.
Implicit Types U V W: set.
HB.instance Definition _ := Setoid.on set.

Definition mem U a := U a.

#[export] Instance mem_eqv: Proper (eqv ==> eqv ==> eqv) mem.
Proof. move=>U V UV a b ab. rewrite /mem. by rewrite (UV a) ab. Qed.

(** turning a predicate into a set by giving an explicit extensionality proof *)
Definition mk_set P HP: set := mk_ext P HP.
Arguments mk_set: clear implicits.

(** empty/full set (we just reuse the [empty/full] functions) *)
HB.instance Definition _ {X} := isExtensional.Build X Prop empty (fun _ _ _ => eqv_refl).
HB.instance Definition _ {X} := isExtensional.Build X Prop full (fun _ _ _ => eqv_refl).
(* Check empty: set. *)
(* Check full: set. *)

(** singleton set *)
Definition single a := mk_set (eqv a) _.
Lemma mem_single a: mem (single a) ≡ (eqv a).
Proof. done. Qed.

(** pair (or singleton if [a≡b]) *)
Program Definition pair a b: set := efun c => a ≡ c \/ b ≡ c.
Next Obligation. move=>z z' e/=. by rewrite e. Qed.

End set.
Arguments set: clear implicits.
Notation "a ∈ U" := (mem U a) (at level 20). 

(** direct image *)
Section direct_image.
Context {X: Type} {Y: Setoid.type} (f: X -> Y).

Definition image (P: X -> Prop) := fun a => exists x, P x /\ a ≡ f x.
Program Definition _image P := isExtensional.Build _ _ (image P) _.
Next Obligation. move=>y y' e. rewrite /image. by setoid_rewrite e. Qed.
HB.instance Definition _ P := _image P. 

Lemma in_image (P: X -> Prop) x: P x -> image P (f x).
Proof. by exists x. Qed.

Lemma forall_image' (P: X -> Prop) (Q: Y -> Prop):
  (forall a, image P a -> Q a) -> forall x, P x -> Q (f x).
Proof. move=>H x Px. apply: H. by exists x. Qed.

Lemma forall_image (P: X -> Prop) (Q: set Y):
  (forall a, image P a -> Q a) <-> forall x, P x -> Q (f x).
Proof.
  split=>H. exact: forall_image'. 
  move=>y [x [Px ->]]; auto. 
Qed.

Lemma image_empty: image empty ≡ empty.
Proof. cbv. by firstorder. Qed.
Lemma image_eq (x: X): image (eq x) ≡ single (f x).
Proof.
  move=>y; split.
  - by move=>[y' [-> ->]]. 
  - move=><-; exact: in_image.
Qed.

End direct_image.
Arguments image {_ _} _ &.

Lemma image_id {X} (P: set X): image types_id P ≡ P.
Proof. split. by move=>[? [? ->]]. exact: in_image. Qed.

Lemma image_comp {X Y Z} (f: Y -eqv-> Z) (g: X -> Y) (P: X -> Prop):
  image (f ∘ g) P ≡ image f (image g P).
Proof.
  intro z; split.
  - move=>[x [Px ->]]. apply: in_image. exact: in_image.
  - move=>[y [[x [Px xy]] ->]].
    exists x; split=>//. by rewrite xy.
Qed.

Lemma image_single {X Y} (f: X -eqv-> Y) (x: X): image f (single x) ≡ single (f x).
Proof.
  move=>y/=; split.
  - by move=>[? [-> ->]].
  - exists x. by split. 
Qed.
Lemma image_pair {X Y} (f: X -eqv-> Y) (x x': X): image f (pair x x') ≡ pair (f x) (f x').
Proof.
  move=>y/=; split.
  - by move=>[? [[->|->] ->]]; [left|right].
  - case=>H. by exists x=>/=; auto. by exists x'=>/=; auto.
Qed.

(** turning a predicate into a set by saturation *)
Section saturate.
Context {X: Setoid.type}.
Definition saturate (P: X -> Prop) := image types_id P.
Lemma mem_saturate P (HP: Proper (eqv ==> eqv) P): mem (saturate P) ≡ P.
Proof. move=>a; split. by move=>[? [? ->]]. by exists a. Qed.
Lemma saturate_eq (x: X): saturate (eq x) ≡ single x.
Proof. exact: image_eq. Qed.
End saturate.
