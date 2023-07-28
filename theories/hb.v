From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Export Setoid Morphisms Basics.
Require Export preliminaries.
Require Classical.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

Notation types_id := Datatypes.id.
Notation types_comp := preliminaries.comp.

(** * setoids *)

(** ** class *)

HB.mixin Record isSetoid X := {
  #[canonical=no] eqv: relation X;
  #[canonical=no] Equivalence_eqv: Equivalence eqv
}.
HB.structure Definition Setoid :=
  { X of isSetoid X }.
Infix "≡" := eqv (at level 70).
Notation "x ≡[ X ] y" := (@eqv X x y) (at level 70, only parsing).

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
  isExtensional.Build X Z (comp f g) _.
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
Proof. reflexivity. Defined.
Lemma eqv_sym {X: Setoid.type} (x y: X): x ≡ y -> y ≡ x.
Proof. apply symmetry. Defined.
#[export] Hint Extern 0 (_ ≡ _)=> exact: (eqv_refl _) || apply: eqv_sym; assumption: core.

(** ** duality *)
(** trivial for setoids, but required for subsequent layers *)

Definition dual (X: Type) := X.
HB.instance Definition dual_Setoid {X: Setoid.type} := isSetoid.Build (dual X) Equivalence_eqv.

Definition dualf {X Y: Type} (f: X -> Y): dual X -> dual Y := f.
Program Definition dual_extensional {X Y} (f: X -eqv-> Y)
  := isExtensional.Build (dual X) (dual Y) (dualf f) extensional.
HB.instance Definition _ {X Y} f := @dual_extensional X Y f.

(** ** instances *)

(** types for which [eq] is the right equality *)
Definition eq_Setoid X := isSetoid.Build X eq_equivalence.
HB.instance Definition bool_Setoid := eq_Setoid bool.
HB.instance Definition nat_Setoid := eq_Setoid nat.

(** irrelevant types - with at most one element *)
Section trivial.
 Variable (X: Type).
 Definition eqv_trivial: relation X := fun _ _ => True.
 Lemma Equivalence_eqv_trivial: Equivalence eqv_trivial.
 Proof. by constructor. Qed.
 Definition trivial_Setoid := isSetoid.Build X Equivalence_eqv_trivial.
End trivial.
Arguments eqv_trivial {_} _ _/. 
HB.instance Definition unit_Setoid := trivial_Setoid unit. 
(* HB.instance Definition irrelevant_Setoid (P: Prop) := trivial_Setoid P. *)

(** extensional propositions *)
HB.instance Definition Prop_Setoid := isSetoid.Build Prop iff_equivalence. 

(** direct sum and product *)
Section sumprod.
 Variables (X Y: Setoid.type).
 Definition eqv_prod: relation (X*Y) := fun x y => fst x ≡ fst y /\ snd x ≡ snd y.
 Lemma Equivalence_eqv_prod: Equivalence eqv_prod.
 Proof.
   constructor=>//.
   - by move=>??[]; split; symmetry. 
   - by move=>???[??][]; split; etransitivity; eassumption.
 Qed.
 HB.instance Definition prod_Setoid := isSetoid.Build _ Equivalence_eqv_prod.

 Definition eqv_sum: relation (X+Y) :=
   fun x y => match x,y with inl x,inl y | inr x,inr y => x ≡ y | _,_ => False end.
 Lemma Equivalence_eqv_sum: Equivalence eqv_sum.
 Proof.
   constructor.
   - by move=>[]//=. 
   - by move=>[?|?][?|?]//=; symmetry. 
   - by move=>[?|?][?|?][?|?]//=; etransitivity; eassumption.
 Qed.
 HB.instance Definition sum_Setoid := isSetoid.Build _ Equivalence_eqv_sum.
End sumprod.
Arguments eqv_prod {_ _} _ _/. 
Arguments eqv_sum {_ _}_ _/. 

(** dependent product space *)
Section dprod.
 Variables (A: Type) (X: A -> Setoid.type).
 Definition eqv_dprod: relation (forall a, X a) := fun f g => forall a, f a ≡ g a.
 Lemma Equivalence_eqv_dprod: Equivalence eqv_dprod.
 Proof.
   constructor.
   - by move=>??. 
   - by move=>????; symmetry. 
   - by move=>??????; etransitivity; eauto.
 Qed.
 HB.instance Definition dprod_Setoid := isSetoid.Build _ Equivalence_eqv_dprod.  
End dprod.
Arguments eqv_dprod {_ _} _ _/. 

#[export] Instance const_eqv {X} {Y: Setoid.type}:
  Proper (eqv ==> eqv) (@const X Y).
Proof. move=>/=y y' yy x. apply yy. Qed.

(** constructing setoids via functions into other setoids *)
Section kernel.
 Variables (A: Type) (X: Setoid.type) (f: A -> X).
 Definition eqv_kern: relation A := fun x y => f x ≡ f y.
 Lemma Equivalence_eqv_kern: Equivalence eqv_kern.
 Proof.
   rewrite /eqv_kern.
   constructor.
   - by move=>//=. 
   - by move=>???; symmetry. 
   - by move=>?????; etransitivity; eauto.
 Qed.
 Definition kern_Setoid := isSetoid.Build _ Equivalence_eqv_kern.  
End kernel.
Arguments eqv_kern [_] _ _ _ _/.

(** [sig] setoids as special case *)
HB.instance Definition sig_Setoid (X: Setoid.type) (P: X -> Prop) :=
  kern_Setoid _ (@proj1_sig X P).

(** extensional functions as special case *)
HB.instance Definition _ {X Y: Setoid.type} :=
  kern_Setoid _ (fun f: X-eqv->Y => f: X -> Y).

(* TOTHINK: useful as an instance? *)
Lemma precomp_eqv {X Y Z: Setoid.type}:
  Proper (@eqv (Y-eqv->Z) ==> eqv ==> eqv) (@types_comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x=>/=. rewrite (gg' x). apply ff'. Qed.


(** SANITY *)
Goal forall a b: nat*Prop*unit, a≡b.
  move=>[[a a'] a''] [[b b'] b'']/=. cbn.
Abort.
Goal forall (x: nat * sig (fun b: bool=> b=true)), x ≡ x.
  intros [x [b ?]]. cbn.
Abort.
Goal forall (x: nat * (bool -> nat) * {y: nat | y=5}), x ≡ x.
  intros [[x f] [p ?]]. cbv.
Abort.
Check forall X: Setoid.type, forall f: X -eqv-> prod nat X, f ≡ f.
(* below: need setoid of irrelevant propositions *)
(* Goal forall a b: nat*True, a≡b. *)
(*   move=>[a a'] [b b']/=. cbn. *)
(* Abort. *)
(* Check forall (x: nat * forall b: bool, nat + (b=true)), x ≡ x. *)


(** * categories *)
Structure CATEGORY := {
    ob: Type;
    hom:> ob -> ob -> Setoid.type;
#[canonical=no] id: forall {A}, hom A A;
#[canonical=no] comp: forall {A B C}, hom B C -> hom A B -> hom A C;
#[canonical=no] comp_eqv:: forall {A B C}, Proper (eqv ==> eqv ==> eqv) (@comp A B C);
#[canonical=no] idl: forall {A B} f, @comp A A B f id ≡ f;
#[canonical=no] idr: forall {A B} f, @comp B A A id f ≡ f;
#[canonical=no] compA: forall {A B C D} f g h, @comp A B D (@comp B C D h g) f ≡ @comp A C D h (@comp A B C g f)
  }.
Arguments id {_ _}.
Arguments comp {_ _ _ _}.
Notation "g ° f" := (comp g f).

(** the category of setoids and extensional functions *)
Program Canonical Structure SETOIDS :=
  {|
    ob := Setoid.type;
    hom X Y := X -eqv-> Y;
    comp := @types_comp;
    id := @types_id;
  |}.
Next Obligation. apply: precomp_eqv. Qed.


(* SANITY *)
Check forall X: Setoid.type, forall f: X -eqv-> X, f ° f ≡ f.
Check forall (X: Setoid.type) (f: X -eqv-> X), id ° f ≡ id. 
Check forall (X: Setoid.type) (f: X -eqv-> X), f ≡ id.
Check fun X: Setoid.type => (id: X -eqv-> X). 
Check forall (X: Setoid.type) (f: X -eqv-> X), id ≡ f. 

Goal forall X: Setoid.type, forall f g h: X-eqv->X, f ≡ g -> f ° g ≡ h.
Proof. intros * H. rewrite H. rewrite -H. Abort.
Goal forall (X: Setoid.type) (f: X -eqv-> X) (x y: X), x≡y -> f (f x) ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  
Goal forall (X: Setoid.type) (f: X -eqv-> X) (x y: X), x≡y -> (f ° f) x ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  


(** * partial orders *)

(** ** class *)

HB.mixin Record isPO X of Setoid X := {
    #[canonical=no] leq: relation X;
    #[canonical=no] PreOrder_leq: PreOrder leq;
    #[canonical=no] eqv_of_leq: forall x y, eqv x y <-> (leq x y /\ leq y x);
}.
HB.structure Definition PO := { X of isPO X & }.
Infix "<=" := leq (at level 70).
Notation "x <=[ X ] y" := (@leq X x y) (at level 70, only parsing).

(* SANITY *)
Goal forall (X: PO.type) (x: nat -> X), x ≡ x.
  intros * n.  
Abort.
Goal forall A (X: A -> PO.type) (x: forall a, X a), x ≡ x. 
  intros * a.
Abort.

(** ** morphisms *)

(** helpers to deduce extensionality out of monotonicity *)
Lemma op_leq_eqv_1 {X Y: PO.type} {f: X -> Y} 
{Hf: Proper (leq ==> leq) f}: Proper (eqv ==> eqv) f.
Proof.
  rewrite /Proper/respectful.
  setoid_rewrite eqv_of_leq. 
  split; apply Hf; tauto.
Qed.
Lemma op_leq_eqv_2 {X Y Z: PO.type} {f: X -> Y -> Z}
  {Hf: Proper (leq ==> leq ==> leq) f}: Proper (eqv ==> eqv ==> eqv) f.
Proof.
  rewrite /Proper/respectful.
  setoid_rewrite eqv_of_leq. 
  split; apply Hf; tauto.
Qed.

(** class of monotone functions (i.e., po morphisms) *)
HB.mixin Record isMonotone (X Y: PO.type) (f: X -> Y) := {
    #[canonical=no] monotone: Proper (leq ==> leq) f
  }.
(** inheritance: setoid morphisms are po morphisms *)
HB.builders Context X Y f (F : isMonotone X Y f).
  HB.instance
  Definition to_SetoidMorphism :=
    isExtensional.Build X Y f (@op_leq_eqv_1 _ _ _ monotone).
HB.end.
HB.structure Definition po_morphism (X Y: PO.type) := { f of isMonotone X Y f }.
Notation "X '-mon->' Y" := (po_morphism.type X Y) (at level 99, Y at level 200).

(** identity morphism *)
HB.instance Definition _ {X} :=
  isMonotone.Build X X types_id (fun _ _ H => H). 
Notation po_id := (types_id: _ -mon-> _) (only parsing). 

(** composition of morphisms *)
Program Definition po_comp {X Y Z} (f: Y-mon->Z) (g: X-mon->Y) := 
  isMonotone.Build X Z (types_comp f g) _.
Next Obligation. move=>x y xy. by do 2apply monotone. Qed. 
HB.instance Definition _ {X Y Z} f g := @po_comp X Y Z f g.

(** constant morphism *)
Program Definition po_const {X Y: PO.type} (y: Y) :=
  isMonotone.Build X Y (const y) _.
Next Obligation. move=>/=_ _ _. apply PreOrder_leq. Qed.
HB.instance Definition _ {X Y} y := @po_const X Y y.




(* SANITY *)
Check fun X: PO.type => @types_id X: X-mon->X. 
Check fun (X: PO.type) (f g: X -mon-> X) => types_comp f g: X -mon->X. 
Check fun (X: PO.type) (f g: X -mon-> X) => f: X -eqv->X. 



(** ** immediate properties *)

#[export] Existing Instance PreOrder_leq.
#[export] Existing Instance monotone.
#[export] Instance PartialOrder_eqv_leq {X: PO.type}: @PartialOrder X eqv _ leq _.
Proof. intros x y. apply eqv_of_leq. Qed.
#[export] Instance leq_rw {X: PO.type}: @RewriteRelation X leq := {}.

Lemma leq_refl {X: PO.type} (x: X): x <= x.
Proof. reflexivity. Defined.
#[export] Hint Extern 0 (_ <= _)=> exact: (leq_refl _): core.


(** ** duality *)

Section dual.
 Context {X: PO.type}.
 Lemma dual_eqv_of_leq (x y: dual X): x ≡ y <-> y <= x /\ x <= y.
 Proof. cbn. rewrite eqv_of_leq. tauto. Qed.
 HB.instance Definition dual_PO :=
   isPO.Build (dual X) (flip_PreOrder _) dual_eqv_of_leq.
End dual.
Program Definition dual_monotone {X Y} (f: X -mon-> Y)
  := isMonotone.Build (dual X) (dual Y) (dualf f) _.
Next Obligation. move=>x y. apply f. Qed.
HB.instance Definition _ {X Y} f := @dual_monotone X Y f.

(** ** instances *)

(** building partial orders from bare preorders
    unused so far,
    it could be used to declare the partial order on Prop, but we may want to get access to its associated setoid before loading the po module.  *)
HB.mixin Record isPO_from_PreOrder X := {
    #[canonical=no] leq: relation X;
    #[canonical=no] PreOrder_leq: PreOrder leq;
}.
HB.builders Context X (PO: isPO_from_PreOrder X).
  Definition leq_kernel (x y: X) := leq x y /\ leq y x. 
  Fact Equivalence_leq_kernel : Equivalence leq_kernel. 
  Proof.
    pose proof PreOrder_leq. unfold leq_kernel.
    constructor; repeat intro.
    - split; reflexivity. 
    - tauto.
    - split; transitivity y; tauto.
  Qed.
  HB.instance
  Definition to_Setoid :=
    isSetoid.Build X Equivalence_leq_kernel. 
  HB.instance
  Definition to_PO :=
    isPO.Build X PreOrder_leq (fun _ _ => reflexivity _).
HB.end.

(*
Variable T: Type.
Variable Tleq: relation T.
Variable HTleq: PreOrder Tleq.
HB.instance Definition T_PO := isPO_from_PreOrder.Build _ HTleq. 
Check fun t: T => t ≡ t. 
*)

(** discrete partial orders *)
Section discrete.
  HB.declare Context X of Setoid X.
  Program Definition discrete_PO := isPO.Build X (leq:=eqv) _ _.
  Next Obligation. intuition. Qed.
End discrete.
(* TOFIX: why do we need to specify [unit_Setoid]? *)
HB.instance Definition unit_PO := discrete_PO unit_Setoid. 

(** Booleans *)
Lemma impl_PreOrder: PreOrder impl. 
Proof. split; cbv; tauto. Qed.
HB.instance Definition Prop_PO := isPO.Build Prop impl_PreOrder (fun _ _ => reflexivity _).

(** Propositions *)
Lemma bool_PreOrder: PreOrder Bool.le.
Admitted.
Lemma bool_eqv_of_leq (a b: bool): a=b <-> Bool.le a b /\ Bool.le b a.
Admitted.
HB.instance Definition bool_PO := isPO.Build bool bool_PreOrder bool_eqv_of_leq.

(** natural numbers *)
Lemma nat_PreOrder: PreOrder Peano.le.
Admitted.
Lemma nat_eqv_of_leq (a b: nat): a=b <-> Peano.le a b /\ Peano.le b a.
Admitted.
HB.instance Definition nat_PO := isPO.Build nat PeanoNat.Nat.le_preorder nat_eqv_of_leq.

(** dependent product space *)
Section dprod.
 Variables (A: Type) (X: A -> PO.type).
 Definition leq_dprod: relation (forall a, X a) := fun f g => forall a, f a <= g a.
 Lemma PreOrder_leq_dprod: PreOrder leq_dprod.
 Proof.
   constructor.
   - by move=>??. 
   - by move=>??????; etransitivity; eauto.
 Qed.
 Lemma eqv_of_leq_dprod (f g: forall a, X a): f ≡ g <-> leq_dprod f g /\ leq_dprod g f.
 Proof.
   cbn. rewrite /leq_dprod /eqv_dprod /=.
   setoid_rewrite eqv_of_leq. firstorder. 
 Qed.
 HB.instance Definition dprod_PO :=
   isPO.Build (forall a, X a) PreOrder_leq_dprod eqv_of_leq_dprod.
End dprod.
Arguments leq_dprod {_ _} _ _/. 

#[export] Instance const_leq {X} {Y: PO.type}:
  Proper (leq ==> leq) (@const X Y).
Proof. move=>/=y y' yy x. apply yy. Qed.

(** constructing partial orders out of functions into partial orders *)
Section kernel.
 Variables (A: Type) (X: PO.type) (f: A -> X).
 Definition leq_kern: relation A := fun x y => f x <= f y.
 Lemma PreOrder_leq_kern: PreOrder leq_kern.
 Proof.
   rewrite /leq_kern.
   constructor.
   - by move=>//=. 
   - by move=>?????; etransitivity; eauto.
 Qed.
 Lemma eqv_of_leq_kern (a b: A): eqv_kern X f a b <-> leq_kern a b /\ leq_kern b a.
 Proof. apply eqv_of_leq. Qed.
 
 (* local, just so that the definition below typechecks *)
 #[local] HB.instance Definition _ := kern_Setoid X f.
 Definition kern_PO := isPO.Build A PreOrder_leq_kern eqv_of_leq_kern.  
End kernel.
Arguments leq_kern [_] _ _ _ _/.

(** [sig] partial orders as special cases *)
HB.instance Definition sig_PO (X: PO.type) (P: X -> Prop) :=
  kern_PO X (@proj1_sig X P).

(** extensional functions as special cases (already a setoid) *)
HB.instance Definition _ {X: Setoid.type} {Y: PO.type} := kern_PO _ (fun f: X-eqv->Y => f: X -> Y).

(** monotone functions as special cases *)
HB.instance Definition _ {X Y: PO.type} := kern_Setoid _ (fun f: X-mon->Y => f: X -> Y).
HB.instance Definition _ {X Y: PO.type} := kern_PO _ (fun f: X-mon->Y => f: X -> Y).

(* TOHINK: useful as an instance? *)
Lemma precomp_leq {X Y Z: PO.type}:
  Proper (@leq (Y-mon->Z) ==> leq ==> leq) (@types_comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x=>/=. rewrite (gg' x). apply ff'. Qed.

(** the category of partial orders and monotone functions *)
Program Canonical Structure POS :=
  {|
    ob := PO.type;
    hom X Y := X -mon-> Y;
    comp := @types_comp;
    id := @types_id;
  |}.
Next Obligation. apply: precomp_eqv. Qed.
(* notation to help typechecking morphisms comparisons *)
Infix "≦" := (@leq (_ -mon-> _)) (at level 70, only parsing). 

(* this instance of [precomp_leq] needs to be explicited to be useful for setoid-rewriting *)
#[export] Instance comp_leq {X Y Z: PO.type}:
  Proper (leq ==> leq ==> leq) (@comp POS X Y Z) := precomp_leq.


(* SANITY *)

Check forall (X: PO.type) (f: X -mon-> X), id ° f <= id. 
Check forall (X: PO.type) (f: X -eqv-> X), f <= id.
Check forall (X: PO.type) (f: X -mon-> X), f <= id.
Check forall (X: PO.type) (f: X -mon-> X), f ≡ id.
Check forall (X: PO.type) (f: X -mon-> X), id ≡ f. 

(* this one fails, but we have the three alternatives below *)
Fail Check forall (X: PO.type) (f: X -mon-> X), id <= f. 
Check forall (X: PO.type) (f: X -mon-> X), po_id <= f. 
Check forall (X: PO.type) (f: X -mon-> X), id <=[X-mon->X] f.
Check forall (X: PO.type) (f: X -mon-> X), id ≦ f. 

Goal forall X: PO.type, forall f g h: X-mon->X, f ≡ g -> f ° g ≡ h.
Proof. intros * H. rewrite H. rewrite -H. Abort.
Goal forall (X: PO.type) (f: X -mon-> X) (x y: X), x≡y -> y<=x -> f (f x) <= (f (f x)).
Proof. intros * H H'. rewrite {1}H H'. reflexivity. Abort.  
Goal forall (X: PO.type) (f g: X -mon-> X) (x y: X), x≡y -> y<=x -> f <= g -> (f ° f) x <= (f ° f) x /\ f ° f <= g ° g.
Proof.
  intros * H H' H''. rewrite {1}H H'. split=>//.
  rewrite {2}H''. 
Abort.


(** ** properties *)

Definition lt {X: PO.type} (x y: X) := x<=y /\ ~y<=x.
Infix "<" := lt (at level 70).
Notation "x <[ X ] y" := (@lt X x y) (at level 70, only parsing).

Section s.
Context {X: PO.type}.
Implicit Types x y: X.

Lemma eqv_leq x y: x ≡ y -> x <= y.
Proof. apply eqv_of_leq. Qed.
Lemma eqv_geq x y: x ≡ y -> y <= x.
Proof. apply eqv_of_leq. Qed.
Lemma antisym x y: x <= y -> y <= x -> x ≡ y.
Proof. intros. by apply eqv_of_leq. Qed.

Lemma antisym' x y: x <= y -> (x <= y -> y <= x) -> x ≡ y.
Proof. intros. apply antisym; tauto. Qed.

Lemma leq_from_above x y: (forall z, y <= z -> x <= z) -> x <= y.
Proof. by auto. Qed.
Lemma from_above x y: (forall z, x <= z <-> y <= z) -> x ≡ y.
Proof. intro E. by apply antisym; apply E. Qed.

Lemma lt_le x y: x < y -> x <= y.
Proof. apply proj1. Qed.
Lemma lelt_lt x y z: x <= y -> y < z -> x < z.
Proof.
  move=>xy [yz zy]. split. by transitivity y.
  contradict zy. by transitivity x.
Qed.
Lemma ltle_lt x y z: x < y -> y <= z -> x < z.
Proof.
  move=>[xy yx] yz. split. by transitivity y.
  contradict yx. by transitivity z.
Qed.
#[export] Instance Transitive_lt: Transitive (@lt X).
Proof. move=>x y z [xy _]. by apply lelt_lt. Qed.

End s.


(** some generic helpers *)
Lemma Proper_forall {S} (A B: S -> Prop): A ≡ B -> (forall x, A x) ≡ (forall x, B x).
Proof. cbv. firstorder. Qed.
Lemma Proper_exists {S} (A B: S -> Prop): A ≡ B -> (exists x, A x) ≡ (exists x, B x).
Proof. cbv. firstorder. Qed.
Lemma Proper_iff: Proper (iff ==> iff ==> iff) iff. 
Proof. cbv. tauto. Qed.
Lemma Proper_impl: Proper (iff ==> iff ==> iff) impl. 
Proof. cbv. tauto. Qed.
Lemma Proper_and: Proper (iff ==> iff ==> iff) and. 
Proof. cbv. tauto. Qed.
Lemma Proper_or: Proper (iff ==> iff ==> iff) or. 
Proof. cbv. tauto. Qed.


Section s.
Context {X: PO.type}.
Definition covered: relation (X -> Prop) := fun P Q => forall x, P x -> exists y, Q y /\ x <= y.
#[export] Instance PreOrder_covered: PreOrder covered.
Proof.
  constructor.
  - by move=>P x Px; eauto.
  - move=>P Q R PQ QR x Hx. 
    case: (PQ x Hx)=>[y [Hy xy]]. 
    case: (QR y Hy)=>[z [Hz yz]].
    exists z. split=>//. by transitivity y.
Qed.
Definition bicovered f g := covered f g /\ covered g f.
#[export] Instance Equivalence_bicovered: Equivalence bicovered.
Proof.
  constructor.
  - split; reflexivity. 
  - move=>??. unfold bicovered; tauto.
  - move=>f g h [??] [??]. split; by transitivity g.
Qed.
#[export] Instance PO_covered: PartialOrder bicovered covered.
Proof. by []. Qed.
(* TOTHINK: declare [subrelation] instances? *)
Lemma leq_covered P Q: P <= Q -> covered P Q.
Proof. move=>H x Px. exists x; split=>//. by apply H. Qed.
Lemma eqv_covered f g: f ≡ g -> bicovered f g.
Proof. by rewrite eqv_of_leq; move=>[??]; split; apply leq_covered. Qed.
End s.

Section s.
Context {X: PO.type}.
Definition is_sup (P: X -> Prop) x := forall z, x <= z <-> forall y, P y -> y <= z.

(* infer [is_sup] using typeclasses? *)
Lemma leq_sup P x: is_sup P x -> forall y, P y -> y <= x.
Proof. move=>H y Py. by apply H. Qed.

Lemma is_sup_leq P p Q q: is_sup P p -> is_sup Q q -> covered P Q -> p<=q.
Proof.
  move=>Pp Qq PQ. apply Pp=>x Px.
  case: (PQ x Px)=>y [Qy ->]. by apply Qq.
Qed.

Lemma is_sup_eqv P p Q q: is_sup P p -> is_sup Q q -> bicovered P Q -> p≡q.
Proof. rewrite eqv_of_leq=>??[??]. eauto using is_sup_leq. Qed.

Lemma supU (P: X -> Prop) x y: is_sup P x -> is_sup P y -> x ≡ y.
Proof. intros; eapply is_sup_eqv; eauto. reflexivity. Qed.

Lemma is_sup_single x: is_sup (eq x) x.
Proof. intro. by firstorder subst. Qed.

#[export] Instance Proper_is_sup: Proper (bicovered ==> eqv ==> eqv) is_sup.
Proof.
  rewrite /is_sup=> P Q PQ x y xy.
  apply Proper_forall=>z. apply Proper_iff. by rewrite xy.
  have E: forall P Q, covered P Q -> (forall t, Q t -> t <= z) <= (forall t, P t -> t <= z).
   clear=>P Q PQ H t Pt. by case: (PQ _ Pt)=>s [? ->]; apply H. 
  split; apply E; apply PQ. 
Qed.

Definition sup_closed (P: X -> Prop) := forall Q, Q <= P -> forall z, is_sup Q z -> P z.

Lemma sup_closed_impl (P Q: X -> Prop): Proper (leq --> leq) P -> sup_closed Q -> sup_closed (fun x => P x -> Q x).
Proof.
  intros HP HQ T TPQ x Tx Px.
  eapply HQ. 2: apply Tx.
  intros y Ty. apply TPQ=>//.
  eapply HP. 2: apply Px.
  by apply Tx. 
Qed.

Lemma sup_closed_leq (f: X -mon-> X): sup_closed (fun x => x <= f x).
Proof.
  intros T HT x Tx. apply Tx=>y Ty. 
  transitivity (f y). by apply HT.
  by apply f, Tx.
Qed.

Lemma sup_closed_Proper P: sup_closed P -> Proper (eqv ==> eqv) P.
Proof.
  move=>H. suff E: Proper (eqv ==> leq) P.
   by move=>x y xy; apply: antisym; apply E=>//; symmetry. 
  move=>x y xy Px. apply (H (eq x)). by move=>?<-. 
  move: (is_sup_single x). apply Proper_is_sup=>//. reflexivity.
Qed.

Definition downward_closed (P: X -> Prop) := Proper (leq ==> leq) P. 

Definition directed (P: X -> Prop) :=
  forall x y, P x -> P y -> exists z, P z /\ x <= z /\ y <= z.

Definition chain (P: X -> Prop) :=
  forall x y, P x -> P y -> x <= y \/ y <= x.

Lemma chain_directed P: chain P -> directed P.
Proof. move=>H x y Px Py; by case:(H _ _ Px Py); eauto. Qed.

End s.

Section s.
Context {X: PO.type}.
Implicit Types x y: X.

Lemma leq_from_below x y: (forall z, z <= x -> z <= y) -> x <= y.
Proof. apply (leq_from_above (y: dual X)). Qed.
Lemma from_below x y: (forall z, z <= x <-> z <= y) -> x ≡ y.
Proof. apply (from_above (x: dual X)). Qed.

Definition is_inf (P: X -> Prop) x := forall z, z <= x <-> forall y, P y -> z <= y.
Lemma geq_inf P x: is_inf P x -> forall y, P y -> x <= y.
Proof. apply: (leq_sup (x:=x: dual X)). Qed.
Definition cocovered (P Q: X -> Prop) := covered (P: dual X -> _) (Q: dual X -> _).
Definition cobicovered (P Q: X -> Prop) := bicovered (P: dual X -> _) (Q: dual X -> _).
Lemma is_inf_leq P p Q q: is_inf P p -> is_inf Q q -> cocovered P Q -> q<=p.
Proof. apply: (@is_sup_leq _ (P: dual X -> Prop)). Qed.
Lemma is_inf_eqv P p Q q: is_inf P p -> is_inf Q q -> cobicovered P Q -> p≡q.
Proof. apply: (@is_sup_eqv _ (P: dual X -> Prop)). Qed.
Lemma infU (P: X -> Prop) x y: is_inf P x -> is_inf P y -> x ≡ y.
Proof. apply (supU (P:=P: dual X -> Prop)). Qed.

Definition inf_closed (P: X -> Prop) := forall Q, Q <= P -> forall z, is_inf Q z -> P z.

Lemma inf_closed_impl (P Q: X -> Prop): Proper (leq ==> leq) P -> inf_closed Q -> inf_closed (fun x => P x -> Q x).
Proof. apply (sup_closed_impl (P:=P: dual X->Prop)). Qed.

Lemma inf_closed_leq (f: X -mon-> X): inf_closed (fun x => f x <= x).
Proof. apply (sup_closed_leq (dualf f)). Qed.

End s.


Definition image {X Y: Type} (f: X -> Y) (P: X -> Prop) y := exists x, P x /\ y = f x.
Definition image_id {X: Type} (P: X -> Prop): image types_id P ≡ P.
Proof. cbv. by firstorder subst. Qed.
Definition image_comp {X Y Z: Type} (f: Y -> Z) (g: X -> Y) (P: X -> Prop): image (types_comp f g) P ≡ image f (image g P).
Proof. cbv. firstorder subst; eauto. Qed.
Lemma forall_image {X Y: Type} (f: X -> Y) (P: X -> Prop) (Q: Y -> Prop):
  image f P <= Q <-> forall x, P x -> Q (f x).
Proof.
  split=>H.
  - move=>x Px. apply H. by exists x.
  - move=>y [x [Px ->]]; auto. 
Qed.
Section s.
Context {X: Type} {Y: PO.type}.
Lemma is_sup_image (f: X -> Y) (P: X -> Prop) y:
  is_sup (image f P) y <-> forall z, y <= z <-> forall x, P x -> f x <= z.
Proof.
  change ((forall z, y <= z <-> (image f P <= (fun t => t <= z))) <->
            (forall z, y <= z <-> (forall x, P x -> f x <= z))).        
  by setoid_rewrite forall_image.
Qed.
#[export] Instance covered_image: Proper (leq ==> leq ==> covered) (@image X Y).
Proof.
  move=>f g fg P Q PQ. apply forall_image=>x Px.
  exists (g x); split. exists x; split=>//. by apply PQ. by apply fg.
Qed.  
End s.

(** sups must be computed pointwise in function spaces *)
(** not clear we can prove it without using decidability of equality on [A] *)
Lemma dprod_sup {A} {X: A -> PO.type}
      (A_dec: forall a b: A, {a=b} + {a<>b})
      (P: (forall a, X a)->Prop) (f: forall a, X a):
  is_sup P f -> forall a, is_sup (image (fun h => h a) P) (f a).
Proof.
  move=>Pf a. split=>az.
  - move=>_ [b [Pb ->]]. rewrite -az. by apply Pf.
  - set h := fun b =>
               match A_dec a b return X b with
               | left E => match E in _=c return X c with
                          | eq_refl _ => z
                          end
               | _ => f b
               end.
    have ha: h a = z. {
      unfold h. case A_dec=>//e.
      have E: e = eq_refl by apply Eqdep_dec.UIP_dec.
      by rewrite E.
    }
    rewrite -ha. apply Pf=>g Pg b.
    unfold h. case A_dec=>ab. destruct ab.
    -- apply az. by exists g.
    -- by apply Pf. 
Qed.


(** adjunctions *)
Section s.
  Context {X Y: PO.type}.
  Variables (f: X -> Y) (g: Y -> X).
  Class adjunction := adj: forall x y, f x <= y <-> x <= g y.
  
  #[export] Instance left_adjoint_leq {A: adjunction}: Proper (leq ==> leq) f.
  Proof. intros x y xy. apply adj. rewrite xy. by apply adj. Qed.
  
  #[export] Instance right_adjoint_leq {A: adjunction}: Proper (leq ==> leq) g.
  Proof. intros x y xy. apply adj. rewrite -xy. by apply adj. Qed.
  
  Lemma left_adjoint_sup (A: adjunction) P x: is_sup P x -> is_sup (image f P) (f x).
  Proof.
    unfold is_sup. intros H y. rewrite adj H.
    setoid_rewrite <-adj. symmetry. apply forall_image.
  Qed.
End s.

Lemma adjoint_id {X}: @adjunction X X types_id types_id.
Proof. by []. Qed.

Lemma adjoint_comp {X Y Z f g f' g'} {A: @adjunction X Y f g} {B: @adjunction Y Z f' g'}:
  adjunction (types_comp f' f) (types_comp g g').
Proof. move=>x y/=. by rewrite 2!adj. Qed.

Lemma dual_adjunction `(A: adjunction): adjunction (g: dual Y -> dual X) (f: dual X -> dual Y).
Proof. rewrite /adjunction/= => y x. symmetry. by apply adj. Qed.

Lemma right_adjoint_inf `(A: adjunction) P y: is_inf P y -> is_inf (image g P) (g y).
Proof. apply (left_adjoint_sup (dual_adjunction A)). Qed. 

(** least (pre-)fixpoints of monotone functions *)
Section d.
 Context {X: PO.type}.
 Definition is_lfp (f: X -> X) := is_inf (fun x => f x <= x). 
 Variable f: X -mon-> X.
 (** essentially Knaster-Tarski *)
 Proposition lfp_fixpoint x: is_lfp f x -> f x ≡ x.
 Proof.   
   move=>H. apply: antisym'.
   apply H=>y Hy. rewrite -Hy. apply f. by apply H.
   move=>P. apply H=>//. by apply f.
 Qed.
End d.   

(** * lattices *)

Definition empty {X}: X -> Prop := fun _ => False. 
Definition pair {X} (x y: X): X -> Prop := fun z => z=x \/ z=y. 

Unset Implicit Arguments.  
HB.mixin Record isLattice X of PO X := {
    #[canonical=no] bot: X;
    #[canonical=no] top: X;
    #[canonical=no] cup: X -> X -> X;
    #[canonical=no] cap: X -> X -> X;
    #[canonical=no] bot_spec: is_sup empty bot;
    #[canonical=no] top_spec: is_inf empty top;
    #[canonical=no] cup_spec: forall x y, is_sup (pair x y) (cup x y);
    #[canonical=no] cap_spec: forall x y, is_inf (pair x y) (cap x y)
}.
Set Implicit Arguments.  
HB.structure Definition Lattice := { X of isLattice X & }.

Program Definition Prop_Lattice := isLattice.Build Prop False True or and _ _ _ _.
Next Obligation. cbv. firstorder. Qed.
Next Obligation. cbv. firstorder. Qed.
Next Obligation. cbv. firstorder subst; eauto. Qed.
Next Obligation. cbv. firstorder subst; eauto; apply H; eauto. Qed.
HB.instance Definition _ := Prop_Lattice.

Program Definition dprod_Lattice {A} {X: A -> Lattice.type} :=
  isLattice.Build
    (forall a, X a) (fun _ => bot) (fun _ => top)
    (fun f g a => cup (f a) (g a))
    (fun f g a => cap (f a) (g a)) _ _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
HB.instance Definition _ {A} {X: A -> Lattice.type} := @dprod_Lattice A X.

Definition mon_cup {X: PO.type} {Y: Lattice.type} (f g: X-mon->Y) :=
  fun x => cup (f x) (g x).

Program Definition mon_cup' {X: PO.type} {Y: Lattice.type} (f g: X-mon->Y) :=
  isMonotone.Build X Y (mon_cup f g) _.
Next Obligation. move=>x y xy. Admitted. 
HB.instance Definition _ {X Y} f g := @mon_cup' X Y f g.

Definition mon_cap {X: PO.type} {Y: Lattice.type} (f g: X-mon->Y) :=
  fun x => cap (f x) (g x).

Program Definition mon_cap' {X: PO.type} {Y: Lattice.type} (f g: X-mon->Y) :=
  isMonotone.Build X Y (mon_cap f g) _.
Next Obligation. move=>x y xy. Admitted.
HB.instance Definition _ {X Y} f g := @mon_cap' X Y f g.

Program Definition mon_Lattice {X: PO.type} {Y: Lattice.type} :=
  isLattice.Build
    (X-mon->Y) (const bot) (const top) mon_cup mon_cap _ _ _ _. 
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
HB.instance Definition _ {X Y} := @mon_Lattice X Y.

Time Goal
  let T := ((bool -> bool -> bool -> bool -> Prop)) in
  let T' := (T: PO.type) in
  let T'' := (T: Lattice.type) in
  let X := ((T-mon->T): Lattice.type) in (* fast *)
  let X' := ((T'-mon->T'): Lattice.type) in (* fast *)
  let X'' := ((T''-mon->T''): Lattice.type) in (* fast *)
  True.
intros.
cbn in *.
Abort.



(** * dCPOs *)

HB.mixin Record isdCPO X of PO X := {
    #[canonical=no] dsup: forall D: X -> Prop, directed D -> X;
    #[canonical=no] dsup_spec: forall D (DD: directed D), is_sup D (dsup D DD);
}.
HB.structure Definition dCPO := { X of isdCPO X & }.

Lemma leq_dsup {X: dCPO.type} (P: X -> Prop) D: forall y, P y -> y <= dsup P D.
Proof. apply leq_sup, dsup_spec. Qed.

Program Definition dprod_dCPO {A} (X: A -> dCPO.type) :=
  isdCPO.Build (forall a, X a) (fun F DF a => dsup (image (fun f => f a) F) _) _.
Next Obligation.
  move=>/=_ _ [g [G ->]] [h [H ->]].
  case: (DF _ _ G H)=>/=[i [I [gi hi]]].
  exists (i a). split. by exists i. split. apply gi. apply hi.
Qed.
Next Obligation.
  move=>/=f. split=>H.
  - move=>g G. rewrite -H=>a. apply leq_dsup. by exists g.
  - move=>a. apply dsup_spec=>/=_ [g [G ->]]. by apply H. 
Qed.
HB.instance Definition _ {A} (X: A -> dCPO.type) := dprod_dCPO X.


(** * CPOs *)

HB.mixin Record isCPO X of PO X := {
    #[canonical=no] csup: forall C: X -> Prop, chain C -> X;
    #[canonical=no] csup_spec: forall C (CC: chain C), is_sup C (csup C CC);
}.
HB.structure Definition CPO := { X of isCPO X & }.

Lemma leq_csup {X: CPO.type} (P: X -> Prop) C: forall y, P y -> y <= csup P C.
Proof. apply leq_sup, csup_spec. Qed.

Program Definition dprod_CPO {A} (X: A -> CPO.type) :=
  isCPO.Build (forall a, X a) (fun F CF a => csup (image (fun f => f a) F) _) _.
Next Obligation.
  move=>/=_ _ [g [G ->]] [h [H ->]].
  case: (CF _ _ G H)=>E;[left|right]; apply E.
Qed.
Next Obligation.
  move=>/=f. split=>H.
  - move=>g G. rewrite -H=>a. apply leq_csup. by exists g.
  - move=>a. apply csup_spec=>/=_ [g [G ->]]. by apply H. 
Qed.
HB.instance Definition _ {A} (X: A -> CPO.type) := dprod_CPO X.

Section c.
 Context {A: Type} {X: dCPO.type}.
 Variable f: A->X.
 Variable from_sup: forall (P: A -> Prop) x, directed (image f P) -> is_sup (image f P) x -> A.
 Hypothesis f_from_sup: forall P x DfP (fPx: is_sup (image f P) x), f (from_sup DfP fPx) ≡ x.
 #[local] HB.instance Definition _ := kern_Setoid X f.
 #[local] HB.instance Definition _ := kern_PO X f.
 Program Definition kern_dCPO :=
   isdCPO.Build A (fun P D =>
                                   let D' := _: directed (image f P) in
                                   from_sup D' (dsup_spec (image f P) D')) _.
 Next Obligation.
   move=>??[a [Pa ->]][b [Pb ->]]. case: (D _ _ Pa Pb)=>/=[c [Pc [ab ac]]].
   exists (f c). split. by exists c. by split.
 Qed.
 Next Obligation.
   move=>/=a. cbn. rewrite f_from_sup. rewrite dsup_spec=>/=. apply forall_image. 
 Qed.
End c. 


(** * chain construction *)

Module Chain.
Section c.
 Context {X: PO.type}.
 Section d.
 Variable f: X -> X.

 (** the set of all (transfinite) iterations of f *)
 Inductive C: X -> Prop :=
 | Cf: forall x, C x -> C (f x)
 | Csup: forall P, P <= C -> forall x, is_sup P x -> C x.
 
 (** a type for the elements of the chain *)
 Structure Chain := chn { elem:> X; #[canonical=no] Celem: C elem}.
 Definition elem' := elem: Chain -> Setoid.sort X.
 Arguments elem' _/. 
 Coercion elem': Chain >-> Setoid.sort. 

 (** the chain inherits the partial order structure from X *)
 HB.instance Definition Chain_Setoid := kern_Setoid _ elem.
 HB.instance Definition Chain_PO := kern_PO _ elem.

 (** the chain is closed under [f] *)
 Canonical Structure next (x: Chain) := {| elem := f x; Celem := Cf (Celem x) |}.

 (** the chain is closed under (existing) sups *)
 Lemma Csup' (P: Chain -> Prop) (x: X): is_sup (fun x => exists Cx, P (@chn x Cx)) x -> C x.
 Proof. move=>H. by apply: (Csup _ H)=>y [Cy _]. Qed.

 (** the chain is inductively generated *)
 Proposition tower: forall (P: Chain -> Prop), sup_closed P -> (forall x, P x -> P (next x)) -> forall x, P x.
 Proof.
   move=>P Psup Pnext.
   suff H: forall x, C x -> forall Cx: C x, P (chn Cx). by move=>[??]; apply H. 
   induction 1 as [x Cx IH|T TC IH t Ht]=>[Cfx|Ct].
   - move: (Pnext (chn Cx) (IH _)). by apply sup_closed_Proper.
   - apply (Psup (fun t => T t)).
     -- move=>[x Cx] Tx. by apply IH.
     -- move=>/=[x Cx]. etransitivity. apply Ht.
        split. clear; firstorder.
        move=>H y Ty. by apply (H (chn (TC _ Ty))).
 Qed.

 (** the chain is equivalence preserving *)
 #[export] Instance C_eqv: Proper (eqv ==> eqv) C.
 Proof. apply sup_closed_Proper. apply: Csup. Qed.
 
 End d.
 Arguments next: clear implicits.

 (** when [f] is eqv-preserving (on [X]), so is [next] (on [Chain f])  *)
 Section d.
 Variable f: X -eqv-> X.
 Lemma next_eqv: Proper (eqv ==> eqv) (next f).
 Proof. by move =>???; apply f. Qed.
 HB.instance Definition _ := isExtensional.Build _ _ _ next_eqv.
 End d.
 
 (** when [f] is monotone (on [X]), so is [next] (on [Chain f])  *)
 Section d.
 Variable f: X -mon-> X.
 Lemma next_leq: Proper (leq ==> leq) (next f).
 Proof. by move =>???; apply f. Qed.
 HB.instance Definition _ := isMonotone.Build _ _ _ next_leq.

 (** elements of the chain are post-fixpoints of [f] *)
 Lemma chain_postfixpoint: forall c: Chain f, c <= next f c.
 Proof.
   apply tower. apply: sup_closed_leq. 
   by move=>*; apply f.
 Qed.

 (** they are below all pre-fixpoints of [f] *)
 Theorem chain_below_prefixpoints x: f x <= x -> forall c: Chain f, c <=[X] x.
 Proof.
   (* we would like to use [tower], but this requires closure under sups in [Chain f],
      and [sup_closed_leq] does not apply... *)
   move=>Hx []/=.
   induction 1 as [y Cy IH|T TC IH t Ht].
   - by rewrite IH.
   - move: T {TC} IH t Ht. apply: (sup_closed_leq (const x)). 
 Qed.

 (** if the chain contains a pre-fixpoint, then this is the least (pre-)fixpoint *)
 Theorem lpfp_of_chain_prefixpoint (c: Chain f): f c <= c -> is_lfp f c.
 Proof.
   move=>Hc x. split=>H.
   - move=>y Hy. rewrite H. by apply chain_below_prefixpoints.
   - by apply H.
 Qed.

 (** if the chain has a supremum, then this is the least (pre-)fixpoint *)
 Theorem lpfp_of_chain_supremum c: is_sup (C f) c -> is_lfp f c.
 Proof.
   intro Hc.
   have Cc: C f c by eapply Csup.
   apply (lpfp_of_chain_prefixpoint (chn Cc))=>/=. 
   apply Hc=>//. by apply Cf. 
 Qed.

 (** not clear whether the chain always contains the potential least fixpoint 
     - true (classically) in CPOs (cf [BourbakiWitt'.any_lfp_in_chain])
     - true (constructively) in dCPOs (cf [Pataraia.any_lfp_in_chain])
  *)
 Fact any_lfp_in_chain: forall x, is_lfp f x -> C f x.
 Abort.
 End d.
End c.
Section c.
 Context {X: dCPO.type}.
 Variable f: X->X.
 Program Definition Chain_dCPO := kern_dCPO (f:=@elem _ f) (fun Q x _ Hx => @chn _ f x _) _.
 Next Obligation.
   eapply Csup. 2: apply Hx.
   move=>/=_ [z [_ ->]]. apply Celem. 
 Qed.
 HB.instance Definition _ := Chain_dCPO.
 
   
 (*   isdCPO.Build (Chain f) (fun P D => {| elem := dsup (fun c => exists Cf: C f c, P (chn Cf)) _ |}) _. *)
 (* Next Obligation. *)
 (*   move=>x y [Cx Px] [Cy Py]. case: (D _ _ Px Py)=>/=[[z Cz]] [Pz [xz yz]]. *)
 (*   exists z. split. eauto. by split. *)
 (* Qed. *)
 (* Next Obligation. *)
   
 (* Qed. *)
 (* Next Obligation. *)
 (*   move=>/=x. etransitivity. apply dsup_spec. simpl. *)
 (*   split;[|clear; firstorder]=>H [y Cy] Dy. *)
 (*   apply H. eauto. *)
 (* Qed. *)
End c. 
Arguments tower {_}.  
Arguments next {_}.  

Section classical.
 Import Classical.

 (** a generic consequence of excluded-middle *)
 Lemma choose_gen (X: Type) (P A B: X -> Prop):
   (forall x, P x -> A x \/ B x) -> (forall x, P x -> A x) \/ (exists x, P x /\ B x).
 Proof.
   intro H. classical_left. intros x Px.
   destruct (H _ Px). assumption. exfalso; eauto. 
 Qed.

 (** a more specific consequence; 
     - we only use it with [f=id, y=y'] to get than the chain is totally ordered
     - we only use it with [f=id, y'=next y] and [f=next, y'= y] to get the stronger [total_chain_strong]
  *)
 Lemma choose (X: PO.type) (P: X -> Prop) (f: X -eqv-> X) y y':
   (forall x, P x -> f x <= y \/ y' <= x) -> (forall x, P x -> f x <= y) \/ (exists x, P x /\ y' <= x).
 Proof. apply choose_gen. Qed.
End classical.


(** * Bournaki-Witt: every extensive function on a CPO has a fixpoint 
    requires classical logic; more precisely, the above lemma [choose] 
    the fixpoint is obtained as [sup (C f)], 
    the difficulty consists in proving that [C f] is a chain so that it's sup exists
 *)
Module BourbakiWitt.
 Section b.

 Context {C: PO.type}.
 Implicit Types x y z: C.

 Variable next: C -eqv-> C. 
 Hypothesis tower: forall P, sup_closed P -> (forall x, P x -> P (next x)) -> forall x, P x.
 Hypothesis id_next: forall x, x <= next x.

 (** relativised tower induction *)
 (* unused for now *)
 Lemma ptower (Q P: C -> Prop):
   Proper (leq --> leq) Q -> 
   sup_closed P ->
   (forall x, Q x -> P x -> P (next x)) ->
   (forall x, Q x -> P x).
 Proof.
   intros HQ Psup Pb. apply: tower. 
   - by apply sup_closed_impl.
   - intros x I H. cut (Q x); auto. revert H. apply HQ, id_next. 
 Qed.

 (** strengthening the above result as follows requires more work, but leads to a proof that [X] is a well-order *)
 Theorem total_chain_strong: forall x y, x <= y \/ next y <= x.
 Proof.
   (** this proof is inspired from Bourbaki's proof, 
       as reported in [Serge Lang, Algebra, p883]
       differences are that:
       - we use definitions that attempt to minimise the required amount of classical logic
       - we do not assume X (and thus admissible sets) to be non-empty
       - we do not start from a CPO, only from a mere partial order 
         (accordingly, the [tower] assumption requires closure under all existing suprema rather than under all directed suprema)
    *)
   (* [split c x] is [x \in M c] in the aforementioned book *)
   set split := fun c x => x <= c \/ next c <= x.
   (* [extreme c], up to classical logic, is [forall x, x < c -> next x <= c] *)
   set extreme := fun c => forall x, x <= c -> split x c. 
   (* Lemma 2.2 *)
   have M: forall c, extreme c -> forall x, split c x. {
     move=>c Ec. apply: tower.
     - move=>T IH t Ht.
       case: (choose T types_id c (next c)).
         by move=>x Tx; apply IH.
       -- move=>F. left. by apply Ht.
       -- move=>[x [Tx xc]]. right. rewrite xc. by apply Ht. 
     - move=>x [xc|cx].
       -- case: (Ec _ xc)=>cx. 2: by left.
          have E: x≡c by apply antisym. by right; rewrite E. 
       -- right. rewrite cx. apply id_next. 
   }
   (* Lemma 2.3 *)
   have N: forall c, extreme c. {
     apply: tower.
     - move=>T IH b Hb x xb.
       case: (choose T next x x).
         move=>z Tz. rewrite or_comm. apply M=>//. by apply IH.
       -- move=>F. left. apply Hb=>y Ty. rewrite ->(id_next y). by apply F.
       -- move=>[c [Tc xc]].
          case: (IH _ Tc x xc)=>cx; swap 1 2.
          right. rewrite cx. by apply Hb.
          case: (M _ (IH _ Tc) b)=>bc.
          left. by transitivity c.
          right. have E: x≡c by apply antisym. by rewrite E. 
     - move=>c IH x xc'.
       case: (M c IH x)=>[xc|cx]. right.
        case: (IH _ xc)=>cx. have E: x≡c by apply antisym. by rewrite E. 
        by rewrite cx; apply id_next.  
       by left. 
   }
   move=>??. by apply M, N. 
 Qed.

 Corollary lt_leq x y: x < next y -> x <= y.
 Proof. case: (total_chain_strong x y)=>?[]; tauto. Qed. 
 Corollary lt_leq' x y: x < y -> next x <= y.
 Proof. case=>_ yx. case: (total_chain_strong y x) =>//. Qed.   

 (** [X] is totally ordered, as an immediate corollary  *)
 Corollary total_chain x y: x <= y \/ y <= x.
 Proof.
   case: (total_chain_strong x y); auto=>xy.
   right. rewrite -xy. apply id_next.
 Qed.

 (** there is at most one prefixpoint, which must be a top element  *)
 Lemma prefixpoint_top x: next x <= x -> is_sup (fun _ => True) x.
 Proof.
   move=>H y. split; auto=>xy z _. rewrite -xy. clear y xy.
   revert z. apply: tower. apply (sup_closed_leq (const x)).
   move=>y yx. case: (total_chain_strong x y); auto=>xy.
   have E: y≡x by apply antisym. by rewrite E.
 Qed.

 (** the chain is well-founded, and thus a well-order
     TOTHINK: 
     - did not see this in the litterature, any applications?
     - is there a way to get it constructively? 
       (it seems we only have to replay the [tower] assumption, 
        but we probably have to use a weaker definition of [lt])
  *)
 Theorem wf_chain: @well_founded C lt.
 Proof.
   have E: forall x, (forall y, y<=x -> Acc lt y). {
     apply: tower.
     - move=>T IH t Ht y yx. constructor=>z zy. 
       have zx: z < t by apply ltle_lt with y. 
       case: (choose T types_id z z).
       by move=>*; apply total_chain.
       -- move=>H. apply proj2 in zx. contradict zx. by apply Ht, H. 
       -- move=>[u [Tu /=zu]]. by apply IH with u.
     - move=>x IH y yx. constructor=>z zy. apply IH.
       apply lt_leq. eapply ltle_lt; eassumption.
   }
   by move=>?; eauto.
 Qed.
 
 (** not clear [choose/choose_gen] is enough to entail decidability *)
 Lemma chain_dec: forall x y, x <= y \/ ~ x <= y.
 Proof.
   apply: tower.
   - move=>T IH t Ht y.
     case: (choose_gen T (fun x => x <= y) (fun x => ~ x <= y)).
       by move=>*; apply: IH. 
     -- move=>F. left. by apply Ht, F.
     -- move=>[x [Tx xy]]. right. contradict xy. rewrite -xy. by apply Ht.
   - move=>x IH y.
     case: (total_chain_strong (next x) y); auto=>yn.
     case: (IH y)=>xy; swap 1 2.
     right. contradict xy. rewrite -xy. by apply id_next.
     (* ?? *)

   (* excluded middle of course works *)
   Restart.
   intros. apply: Classical_Prop.classic.
 Qed.
 
 Corollary chain_le_lt_dec x y: x <= y \/ y < x.
 Proof.
   case: (total_chain x y); auto=>yx. 
   case: (chain_dec x y); auto=>xy.
   by right.
 Qed.

 (** [next] is strictly increasing, except possibly on the top element *)
 Corollary lt_next x: x < next x \/ is_sup (fun _ => True) x.
 Proof.
   case: (chain_le_lt_dec (next x) x); auto.
   by right; apply prefixpoint_top.
 Qed.

 (** [x<y] is almost equivalent to [next x<=y] *)
 Corollary lt_leq'' x y: next x <= y -> x < y \/ is_sup (fun _ => top) x. 
 Proof.
   move=>H. case: (lt_next x); auto=>//H'.
   left. eapply ltle_lt; eassumption. 
 Qed.   

End b.
Section b.

 Context {X: CPO.type}.
 Variable f: X -eqv-> X. 
 Hypothesis f_ext: forall x, x <= f x.
 
 Lemma chain_C: chain (C f).
 Proof.
   move=>x y Cx Cy.
   apply: (total_chain _ (tower f) _ (chn Cx) (chn Cy)).
   move=>*; apply f_ext.
 Qed.
 
 Definition fixpoint := csup (C f) chain_C.
 Theorem is_fixpoint: f fixpoint ≡ fixpoint.
 Proof.
   apply: antisym=>//.
   apply leq_csup. apply Cf. apply Csup with (C f)=>//. apply csup_spec.
 Qed.

 (* note: 
    our definition of CPO implicitly requires a least element (since the empty set is a chain) 
    we can drop this assumption assuming [X] contains some element x: 
    { y: X | x <= y } is a CPO with least element x.
  *)
 
End b. 
End BourbakiWitt. 

(** * A variant of Bournaki-Witt: every monotone function on a CPO has a least (pre-)fixpoint 
      still requires classical logic, but slightly less: only [forall T x, choose T id x x] 
      the fixpoint is obtained as [sup (C f)],     
      the difficulty consists in proving that [C f] is a chain so that it's sup exists

      When moving to dCPOs, we can get a constructive proof (cf. Pataraia below): 
      we can prove constructively that [C f] is directed.
 *)
Module BourbakiWitt'.
Section b.

 Context {C: PO.type}.
 Implicit Types x y z: C.

 (** tower induction *)
 Variable next: C -mon-> C.
 Hypothesis tower: forall (P: C -> Prop), sup_closed P -> (forall x, P x -> P (next x)) -> forall x, P x.

 (** the function [next] must be extensive *)
 Lemma id_next: po_id <= next.
 Proof.
   apply: tower=>/=.
   - apply sup_closed_leq.
   - by move=>*; apply next.
 Qed.

 (** thus we have relativised tower induction  *)
 Lemma ptower (Q P: C -> Prop):
   Proper (leq --> leq) Q -> 
   sup_closed P ->
   (forall x, Q x -> P x -> P (next x)) ->
   (forall x, Q x -> P x).
 Proof. apply (BourbakiWitt.ptower _ tower id_next). Qed.

 (** there is at most one prefixpoint, which must be a top element  *)
 Lemma prefixpoint_top x: next x <= x -> is_sup (fun _ => True) x.
 Proof.
   move=>H y. split; auto=>xy z _. rewrite -xy. clear y xy.
   revert z. apply: tower. apply (sup_closed_leq (const x)).
   by move=>y ->.
 Qed.

 (** a helper for the proof of [total_chain] *)
 Lemma leq_next: forall x y, (forall z, next z <= x -> z <= y) -> x <= next y.
 Proof.
   apply: tower.
   - move=>T IH t Ht y H. apply Ht=>x Tx. apply IH=>//z zx.
     apply H. rewrite zx. by apply Ht.
   - move=>x IH y H. by apply next, H.
 Qed.

 (** [X] is totally ordered *)
 Theorem total_chain: forall x y, x <= y \/ y <= x.
 Proof.
   (** actually an instance of [Bourbaki.total_chain] *)
   exact (BourbakiWitt.total_chain next tower id_next).
   Restart. 
   (** but the following proof is simpler and requires only [choose _ id x x] *)
   apply: tower.
   - move=>T IH t Ht y.
     case: (choose T types_id y y). by move=>*; apply IH.
     -- move=>F. left. apply Ht=>x Tx. by apply F.
     -- move=>[x [Tx yx]]. right. rewrite yx. by apply Ht.
   - move=>x IH y.
     case: (choose (fun t => next t <= y) types_id x x).
     by move=>t _; move: (IH t); tauto.
     -- move=>F. right. apply leq_next=>z zy. by apply F.
     -- move=>[t [ty xt]]. left. by rewrite xt.
 Qed.

End b.
Section b.

 Context {X: CPO.type}.
 Variable f: X -mon-> X. 

 Lemma chain_C: chain (C f).
 Proof.
   move=>x y Cx Cy.
   exact: (total_chain _ (tower f) (chn Cx) (chn Cy)).
 Qed.
 
 Definition lfp := csup (C f) chain_C.
 Theorem is_least_fixpoint: is_lfp f lfp.
 Proof. apply lpfp_of_chain_supremum. apply csup_spec. Qed.

 (* note: 
    our definition of CPO implicitly requires a least element (since the empty set is a chain) 
    we can drop this assumption assuming [X] contains some element x: 
    { y: X | x <= y } is a CPO with least element x.
  *)

 Corollary any_lfp_in_chain: forall x, is_lfp f x -> C f x.
 Proof.
   move=>x H. have E: x≡lfp.
   apply: is_inf_eqv. apply H. apply is_least_fixpoint.
   rewrite /cobicovered; reflexivity.
   rewrite E; clear.
   apply Csup with (C f)=>//. apply csup_spec. 
 Qed.
 
End b. 
End BourbakiWitt'. 


(** the dCPO of monotone functions *)
(* TODO: generic construction (via dprod_CPO) *)
Section s.
 Context {X: PO.type} {Y: dCPO.type}. 
 Program Definition mon_dCPO := kern_dCPO (f:=fun f: X -mon-> Y => f: X -> Y) (fun Q f D Qf => _) _.
 Next Obligation.
   have E: f ≡ dsup _ D. apply: is_sup_eqv. apply Qf. apply: dsup_spec. reflexivity.
   have I: Proper (leq ==> leq) f. {
     move=>x y xy. rewrite (E x) (E y).
     apply: is_sup_leq; try apply: dsup_spec. simpl.
     etransitivity. apply eqv_covered. apply image_comp. 
     etransitivity. 2: apply eqv_covered; symmetry; apply image_comp. 
     apply covered_image=>//g/=. by apply g.
   }
   unshelve eexists. exact f.
   constructor. constructor. exact I. 
   (* TOFIX: why do we need to provide this proof? *)
   constructor. apply op_leq_eqv_1. 
 Defined.
 HB.instance Definition _ := mon_dCPO.
End s.

Module Pataraia. 

Section s.
 Context {C: dCPO.type}.

 (** the largest monotone and extensive function on [C] *)
 Program Definition h: C-mon->C := dsup (fun f => id ≦ f) _.
 Next Obligation.
   (* grrr: goals are not nice-looking *)
   move=>/=i j I J. exists (i°j)=>/=. split; last split.
   - by rewrite -I. 
   - by rewrite -J.
   - by rewrite -I.
 Qed.
 
 Lemma h_ext: id ≦ h.
 Proof. by apply: leq_dsup. Qed.

 Lemma h_invol: h ° h <= h.
 Proof.
   apply: leq_dsup.
   by rewrite -h_ext.
 Qed.

 (* TODO: define [bot] in all CPOs *)
 Program Definition extensive_fixpoint := h (dsup empty _).
 Next Obligation. by []. Qed.

 Variable f: C-mon->C.
 Hypothesis f_ext: id ≦ f. 
 
 Lemma h_prefixpoint: f ° h <= h.
 Proof. apply: leq_dsup. by rewrite -f_ext -h_ext. Qed.

 Theorem is_extensive_fixpoint: f extensive_fixpoint ≡ extensive_fixpoint. 
 Proof. apply antisym. apply h_prefixpoint. apply f_ext. Qed.
End s.

Section s.
 Context {X: dCPO.type}.
 Variable f: X-mon->X.

 Definition lfp: X := elem (@extensive_fixpoint (Chain f)).
 (* TOTHINK: how to have elem be inferred automatically?
    (without adding yet another coercion [elem'': Chain >-> dCPO.sort])  *)
   
 Theorem is_least_fixpoint: is_lfp f lfp. 
 Proof.
   apply lpfp_of_chain_prefixpoint. apply eqv_leq.
   apply: (is_extensive_fixpoint (f:=next f)).
   move=>x; apply chain_postfixpoint.
 Qed.

 (* note: we could also prove that [C f] admits a supremum and is thus trivially directed, 
    so that we could define [lfp] as [dsup (C f) _], uniformly with the definitions in [Bourbakiwitt'.lfp]

    we proceed more directly, and prove a posteriori that [lfp] as defined above is indeed the sup of [C f] *)
 Proposition lfp_is_sup_C: is_sup (C f) lfp. 
 Proof.
   move=>x. split=>H.
   - move=>c Cc. rewrite -H.
     apply: (chain_below_prefixpoints f _ _ (chn Cc)).
     apply eqv_leq, lfp_fixpoint, is_least_fixpoint.
   - apply H. apply Celem.
 Qed.

 Corollary any_lfp_in_chain: forall x, is_lfp f x -> C f x.
 Proof.
   move=>x H. have E: x≡lfp.
   apply: is_inf_eqv. apply H. apply is_least_fixpoint.
   rewrite /cobicovered; reflexivity.
   rewrite E; clear.
   apply Csup with (C f)=>//. apply lfp_is_sup_C. 
 Qed.

 (** as a consequence, any property holding on the whole chain holds on the least fixpoint 
     (this is the starting point for the [coinduction] tactic) *)
 Corollary lfp_prop (P: X -> Prop): (forall c: Chain f, P (elem c)) -> P lfp.
 (* TODO: get rid of the explicit [elem] *)
 Proof. move=>H. apply (H (chn (any_lfp_in_chain is_least_fixpoint))). Qed.
 
End s.

End Pataraia.
End Chain.

Print Assumptions Chain.BourbakiWitt.is_fixpoint.
Print Assumptions Chain.BourbakiWitt'.is_least_fixpoint.
Print Assumptions Chain.Pataraia.is_least_fixpoint.
