Require Import Arith.           (* TMP *)
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

#[export] Hint Extern 0 => reflexivity: core.

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
HB.instance Definition _ := eq_setoid nat.

(** trivial setoids, for proof irrelevant types *)
Definition trivial (X: Type) := X.
Program Definition setoid_trivial (X: Type) := isSetoid.Build (trivial X) (eqv := fun _ _ => True) _.
Next Obligation. split; firstorder. Qed.
HB.instance Definition _ X := setoid_trivial X. 
HB.instance Definition _ := Setoid.copy unit (trivial unit). 

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

(* SANITY: kernel composition,
   taking two successive kernels is definitionally equivalent to taking a composite one
   crucial from some inheritance paths to be equivalent, e.g.,
   (X-eqv->Y) -> (sig (Proper ...)) -> X->Y
          \____________________________/
 *)
Check fun (X: Setoid.type) (f g: X -> X) =>
        unify_setoids
          (kernel (X:=kernel g) f)
          (kernel (types_comp g f)).

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
  Proper (eqv ==> eqv) (@const X Y).
Proof. move=>/=y y' yy x. apply yy. Qed.
#[export] Instance const_eqv' {X} {Y: Setoid.type}:
  Proper (eqv ==> @eqv (X-eqv->Y)) (@const X Y) := const_eqv.

(** extensionality of functional composition,
    provided the outer function is extensive *)
Lemma types_comp_eqv {X Y Z: Setoid.type}:
  Proper (@eqv (Y-eqv->Z) ==> eqv ==> eqv) (@types_comp X Y Z).
Proof.
  move=>/=f f' ff' g g' gg' x=>/=. rewrite (gg' x). apply ff'.
Qed.


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
Goal forall X: Setoid.type, forall f g: X-eqv->X, forall x y: X, f ≡ g -> x ≡ y -> f x ≡ g y /\ types_comp f (const x) ≡[X->X] const (g y) /\ const x ≡[X->X] const y.
Proof.
  intros X f g x y fg xy. repeat split.
  rewrite xy. by apply fg.
  2: by rewrite xy. 
  Fail rewrite fg.            (* dommage *)
Abort.  


(** * categories *)
#[universes(polymorphic=yes)] Structure CATEGORY := {
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
Notation "g ° f" := (comp g f) (at level 20).

(** the category of setoids and extensional functions *)
Program Canonical Structure SETOIDS :=
  {|
    ob := Setoid.type;
    hom X Y := X -eqv-> Y;
    comp := @types_comp;
    id := @types_id;
    comp_eqv := @types_comp_eqv;
  |}.

(* SANITY SETOID *)
Check forall X (f: X -eqv-> X), f ° f ≡ f.
Check forall X (f: X -eqv-> X), id ° f ≡ id. 
Check forall X (f: X -eqv-> X), f ≡ id.
Check fun X => (id: X -eqv-> X). 
Check forall X (f: X -eqv-> X), id ≡ f. 
Goal forall X, forall f g h: X-eqv->X, f ≡ g -> f ° g ≡ h.
Proof. intros * H. rewrite H. rewrite -H. Abort.
Goal forall X (f: X -eqv-> X) (x y: X), x≡y -> f (f x) ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  
Goal forall X (f: X -eqv-> X) (x y: X), x≡y -> (f ° f) x ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  
Goal forall X: Setoid.type, forall f g: X-eqv->X, forall x y: X, f ≡ g -> x ≡ y -> f x ≡ g y /\ f ° const x ≡[X-eqv->X] const (g y) /\ const x ≡[X->X] const y.
Proof.
  intros X f g x y fg xy. repeat split.
  Fail rewrite fg.              (* fair enough *)
  rewrite xy. by apply fg.
  2: by rewrite xy.
  rewrite fg.
  by rewrite xy.                (* thanks to [const_eqv'] *)
Abort.  
Goal forall X: Setoid.type, forall f g: X-eqv->X, f ≡ g -> f ° g ≡ g ° g.
Proof. by move=>X f g ->. Abort.

Check fun f: bool -eqv-> bool => f ≡ id. 
Check fun f: bool -eqv-> bool => f ≡ types_id. 
Check fun f: bool -eqv-> bool => id ≡ f. 
Fail Check fun f: bool -eqv-> bool => types_id ≡ f. 
Check fun f: bool -eqv-> bool => @types_id bool ≡ f. 
Check fun f: bool -eqv-> bool => f ≡ Datatypes.id. 
Fail Check fun f: bool -eqv-> bool => Datatypes.id ≡ f. 
Check fun f: bool -eqv-> bool => @Datatypes.id bool ≡ f. 
Fail Check fun f: bool -eqv-> bool => id ≡[bool->bool] f. (* fair enough *)
Check fun f: bool -eqv-> bool => f ≡[bool->bool] types_id. 
Check fun f: bool -eqv-> bool => f ° f. 
Check fun f: bool -eqv-> bool => f ° id ° f. 

Goal forall X, forall f g h: X -eqv-> X, f ≡ g -> f ° g ≡ h.
Proof. intros * H. rewrite H -H. Abort.

Goal forall X, forall h: X-eqv->X, forall x y: X, x ≡ y -> const x ≡ h.
Proof. intros * H. rewrite H -H. Abort. 

Check bool: Setoid.type. 
Check (bool * (unit -> dual bool) * sig (fun b: bool=> b=true)  (* * True *))%type: Setoid.type. 
Check (bool -> bool -> Prop): Setoid.type. 
Check (bool -eqv-> bool -eqv-> Prop): Setoid.type. 

Goal forall f: nat -> Prop, f ≡ f.
  move=>f x.
Abort.
Goal forall X, forall f g h: X -eqv-> X, f ≡ g -> f ° g ≡ h.
  intros * ->.
Abort.
Goal forall X, forall f g h: X -eqv-> X, f ≡ g -> types_comp f g ≡ h.
  Fail intros * ->.              (* fair enough *)
Abort.
Goal forall f g: nat -> Prop, f ≡ g -> f ≡ g.
  intros * ->.
Abort.

Section s.
  Variable X: Setoid.type.
  Check forall f g: X -eqv-> X, f ° g ≡ id.
  Check forall f g: bool -eqv-> bool, f ° g ≡ id.
End s.

Goal forall X, forall f: X -eqv-> X, forall x y: X, x≡y -> f (f x) ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  

Goal forall X, forall f: X -eqv-> X, forall x y: X, x≡y -> (f ° f) x ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  

(* /SANITY SETOID *)



(** * partial orders *)

(** ** class *)

Definition po_axm {X: Setoid.type} (leq: relation X) :=
  PreOrder leq /\ forall x y, eqv x y <-> (leq x y /\ leq y x).
HB.mixin Record isPO X of Setoid X := {
    #[canonical=no] leq: relation X;
    #[canonical=no] PO_axm: po_axm leq;
}.
HB.structure Definition PO := { X of isPO X & }.
Infix "<=" := leq (at level 70).
Notation "x <=[ X ] y" := (@leq X x y) (at level 70, only parsing).

(* those two projections need to be Defined in order kernel composition to behave well *)
#[export] Instance PreOrder_leq {X: PO.type}: @PreOrder X leq.
Proof. apply PO_axm. Defined.
Lemma eqv_of_leq {X: PO.type} (x y: X): x ≡ y <-> x <= y /\ y <= x. 
Proof. apply PO_axm. Defined.

(** testing that two partial orders are definitionally equal *)
Notation unify_po X Y := (unify (X: PO.type) (Y: PO.type)).


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
  HB.instance Definition _ :=
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
Goal forall (X: PO.type) (x: nat -> X), x ≡ x.
  intros * n.  
Abort.
Goal forall A (X: A -> PO.type) (x: forall a, X a), x ≡ x. 
  intros * a.
Abort.
Check fun X: PO.type => @types_id X: X-mon->X. 
Check fun (X: PO.type) (f g: X -mon-> X) => types_comp f g: X -mon->X. 
Check fun (X: PO.type) (f g: X -mon-> X) => f: X -eqv->X. 
(* /SANITY *)


(** ** immediate properties *)

#[export] Existing Instance monotone.
#[export] Instance PartialOrder_eqv_leq {X: PO.type}: @PartialOrder X eqv _ leq _.
Proof. intros x y. apply eqv_of_leq. Qed.
#[export] Instance leq_rw {X: PO.type}: @RewriteRelation X leq := {}.

Lemma leq_refl {X: PO.type} (x: X): x <= x.
Proof. reflexivity. Qed.
#[export] Hint Extern 0 (_ <= _)=> exact: (leq_refl _): core.


(** ** duality *)

Section dual.
 Context {X: PO.type}.
 Lemma po_dual: po_axm (flip (@leq X)).
 Proof. split. by typeclasses eauto. by move=>??/=; rewrite eqv_of_leq; tauto. Qed.
 HB.instance Definition _ := isPO.Build (dual X) po_dual.
End dual.
Program Definition po_dualf {X Y} (f: X -mon-> Y)
  := isMonotone.Build (dual X) (dual Y) (dualf f) _.
Next Obligation. move=>x y. apply f. Qed.
HB.instance Definition _ {X Y} f := @po_dualf X Y f.

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
  Definition _ :=
    isSetoid.Build X Equivalence_leq_kernel. 
  HB.instance
  Definition _ :=
    isPO.Build X (conj PreOrder_leq (fun _ _ => reflexivity _)).
HB.end.

(** discrete partial order on top of a setoid *)
Definition discrete (X: Type) := X.
HB.instance Definition _ {X: Setoid.type} := Setoid.copy (discrete X) X.
Program Definition po_discrete (X: Setoid.type) := isPO.Build (discrete X) (leq:=eqv) _.
Next Obligation. split. typeclasses eauto. intuition. Qed.
HB.instance Definition _ X := po_discrete X.

(** trivial partial order as the discrete partial order on the trivial setoid *)
HB.instance Definition _ (X: Type) := PO.copy (trivial X) (discrete (trivial X)).

(* SANITY *)
Check unify_po (discrete unit) (trivial unit). 
Fail Check unit: PO.type.       (* should indeed fail before next declaration *)

(** trivial partial order on the unit type *)
HB.instance Definition _ := PO.copy unit (discrete unit).



(* SANITY *)
Check fun X: Type => trivial X: Setoid.type.
Fail Check fun X: Type => discrete X: Setoid.type. (* should indeed fail *)
Check fun X: Setoid.type => discrete X: PO.type.
Check fun X: Type => discrete (trivial X): PO.type.
Check fun X: Type => trivial X: PO.type.


(** propositions ordered by implication *)
Lemma po_Prop: po_axm impl. 
Proof. split=>//. split; cbv; tauto. Qed.
HB.instance Definition _ := isPO.Build Prop po_Prop.

(** Booleans with [false ≦ true] *)
Lemma po_bool: po_axm Bool.le.
Proof.
  split. split. by case. move=>[][][]//=.
  case; case=>//=; intuition discriminate.
Qed.
HB.instance Definition _ := isPO.Build bool po_bool.

(** natural numbers *)
Lemma po_nat: po_axm Peano.le.
Proof.
  split. apply PeanoNat.Nat.le_preorder .
  split. now intros <-. intros. now apply Nat.le_antisymm.
Qed.
HB.instance Definition _ := isPO.Build nat po_nat.

(** (dependent) function space, ordered pointwise *)
Section dprod.
 Variables (A: Type) (X: A -> PO.type).
 Definition leq_dprod: relation (forall a, X a) := fun f g => forall a, f a <= g a.
 Lemma po_dprod: po_axm leq_dprod.
 Proof.
   split. split.
   - by move=>??. 
   - by move=>??????; etransitivity; eauto.
   - cbn. rewrite /leq_dprod /eqv_dprod /=.
     setoid_rewrite eqv_of_leq. firstorder. 
 Qed.
 HB.instance Definition _ := isPO.Build (forall a, X a) po_dprod.
End dprod.
Arguments leq_dprod {_ _} _ _/. 
Definition po_app {A} {X: A -> PO.type} (a: A) :=
  isMonotone.Build (forall a, X a) (X a) (app a) (fun f g fg => fg a).
HB.instance Definition _ A X a := @po_app A X a.

(** products and sums of partial orders *)
Section sumprod.
 Variables X Y: PO.type.

 (** direct product *)
 Definition leq_prod: relation (X*Y) :=
   fun p q => fst p <= fst q /\ snd p <= snd q.
 Lemma po_prod: po_axm leq_prod.
 Proof.
   split. constructor=>//.
   by move=>???[??][]; split; etransitivity; eassumption.
   unfold eqv, leq_prod=>??/=. rewrite 2!eqv_of_leq. tauto. 
 Qed.
 HB.instance Definition _ := isPO.Build (prod X Y) po_prod.
 HB.instance Definition _ :=
   isMonotone.Build (prod X Y) X fst (fun p q pq => proj1 pq).
 HB.instance Definition _ :=
   isMonotone.Build (prod X Y) Y snd (fun p q pq => proj2 pq).

 (** lexicographic product *)
 (** we use an alias for product to guide structure inferrence *)
 (** TOREPORT? we need to eta expand this alias otherwise we run into universe problems with SPOs... *)
 Definition lex_prod X Y := prod X Y. 
 Definition leq_lex_prod: relation (X*Y) :=
   fun p q => fst p <= fst q /\ (fst q <= fst q -> snd p <= snd q).
 Lemma po_lex_prod: po_axm leq_lex_prod.
 Proof.
   split. constructor=>//. unfold leq_lex_prod.
   move=>[x x'][y y'][z z']/=.
   intuition solve [transitivity y; auto|transitivity y'; auto].
   unfold eqv, leq_lex_prod=>??/=. rewrite 2!eqv_of_leq. intuition.
 Qed.
 HB.instance Definition _ := isPO.Build (lex_prod X Y) po_lex_prod.

 (** direct sum (called "parallel" by opposition with the sequential operation below) *)
 Definition leq_parallel_sum: relation (X+Y) :=
   fun p q => match p,q with
           | inl x,inl y | inr x,inr y => x<=y
           | _,_ => False
           end.
 Lemma po_parallel_sum: po_axm leq_parallel_sum.
 Proof.
   split. constructor.
   by case=>//=.
   by case=>?; case=>y; case=>?//=; transitivity y.
   case=>x; case=>y; cbn; rewrite ?eqv_of_leq; tauto. 
 Qed.
 HB.instance Definition _ :=
   isPO.Build (sum X Y) po_parallel_sum.
 HB.instance Definition _ :=
   isMonotone.Build X (sum X Y) inl (fun p q pq => pq).
 HB.instance Definition _ :=
   isMonotone.Build Y (sum X Y) inr (fun p q pq => pq).

 (** sequential sum *)
 Definition sequential_sum := sum. 
 Definition leq_sequential_sum: relation (X+Y) :=
   fun p q => match p,q with
           | inl x,inl y | inr x,inr y => x<=y
           | inl _,inr _ => True
           | _,_ => False
           end.
 Lemma po_sequential_sum: po_axm leq_sequential_sum.
 Proof.
   split. constructor.
   by case=>//=.
   by case=>?; case=>y; case=>?//=; transitivity y.
   case=>x; case=>y; cbn; rewrite ?eqv_of_leq; tauto. 
 Qed.
 HB.instance Definition _ := isPO.Build (sequential_sum X Y) po_sequential_sum.
End sumprod. 
Arguments leq_prod [_ _] _ _/.
Arguments leq_lex_prod [_ _] _ _/.
Arguments leq_parallel_sum [_ _] _ _/.
Arguments leq_sequential_sum [_ _] _ _/.
  
(** option & list partial orders *)
Section optionlist.
 Variables (X: PO.type).

 (** [option] type, adding [None] as top element *)
 (* TODO: propose the other variant;
    do it via sequential_sum and unit? *)
 Definition leq_option (p q: option X) :=
  match q,p with Some q,Some p => p<=q | None,_ => True | _,_ => False end.
 Lemma po_option: po_axm leq_option.
 Proof.
   split. constructor.
   by move=>[?|]//=. 
   by move=>[?|][y|][?|]??//=; transitivity y. 
   case=>[?|]; case=>[?|]; cbn; rewrite ?eqv_of_leq; tauto.
 Qed.
 HB.instance Definition _ := isPO.Build (option X) po_option.

 (** lists ordered lexicographically *)
 Fixpoint leq_list (h k: list X) :=
   match h,k with cons x h,cons y k => x<=y /\ leq_list h k | nil,_ => True | _,_ => False end.
 Lemma po_list: po_axm leq_list.
 Proof.
   split. constructor.
   - by elim=>//.
   - by elim=>[|x h IH][|y k][|z l]//=[? ?][? ?]; split; try etransitivity; eauto.
   - elim=>[|x h IH][|y k]; cbn; try tauto.
     rewrite eqv_of_leq. setoid_rewrite IH. tauto.
 Qed.
 HB.instance Definition _ := isPO.Build (list X) po_list.
End optionlist.
Arguments leq_option [_] _ _/.
Arguments leq_list [_] _ _/.

(** constructing a partial order via a function into another partial order *)
Section kernel.
 Variables (A: Type) (X: PO.type) (f: A -> X).
 Definition leq_kern: relation (kernel f) := fun x y => f x <= f y.
 Lemma po_kern: po_axm leq_kern.
 Proof.
   split.
   - rewrite /leq_kern. constructor.
     -- by move=>?; reflexivity.
     -- by move=>?????; etransitivity; eauto.
   - cbn=>??. apply eqv_of_leq.
     (* need to be defined for kernel composition to behave well *)
 Defined.
 HB.instance Definition _ := isPO.Build (kernel f) po_kern.  
 HB.instance Definition _ := isMonotone.Build (kernel f) X (kernelf f) (fun _ _ xy => xy). 
End kernel.
Arguments leq_kern [_ _] _ _ _/.

Check fun (X: PO.type) (f g: X -> X) =>
        unify_po
          (kernel (X:=kernel g) f)
          (kernel (types_comp g f)).

(** sub partial orders as a special case *)
HB.instance Definition _ (X: PO.type) (P: X -> Prop) :=
  PO.copy (sig P) (kernel (@proj1_sig X P)).
HB.instance Definition _ (X: PO.type) (P: X -> Prop) :=
  isMonotone.Build (sig P) X (@proj1_sig X P) (fun p q pq => pq).

(** extensional functions as a special case (already declared as a setoid) *)
HB.instance Definition _ {X: Setoid.type} {Y: PO.type} :=
  PO.copy (X-eqv->Y) (kernel (fun f: X-eqv->Y => f: X -> Y)).

(** monotone functions as a special case *)
HB.instance Definition _ {X Y: PO.type} :=
  PO.copy (X-mon->Y) (kernel (fun f: X-mon->Y => f: X -> Y)).

(* TOHINK: useful as instances? *)
Lemma types_comp_leq {X} {Y Z: PO.type}:
  Proper (@leq (Y-mon->Z) ==> leq ==> leq) (@types_comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x=>/=. rewrite (gg' x). apply ff'. Qed.
Lemma types_comp_leq_eqv {X} {Y: Setoid.type} {Z: PO.type}: Proper (@leq (Y-eqv->Z) ==> eqv ==> leq) (@types_comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x/=. rewrite (gg' x). apply: ff'. Qed.

#[export] Instance const_leq {X} {Y: PO.type}:
  Proper (leq ==> leq) (@const X Y).
Proof. move=>/=y y' yy x. apply yy. Qed.
#[export] Instance const_leq' {X} {Y: PO.type}:
  Proper (leq ==> @leq (X-mon->Y)) (@const X Y) := const_leq.

(** the category of partial orders and monotone functions *)
Program Canonical Structure POS :=
  {|
    ob := PO.type;
    hom X Y := X -mon-> Y;
    comp := @types_comp;
    id := @types_id;
    comp_eqv := @types_comp_eqv;    
  |}.
(* notation to help typechecking morphisms comparisons *)
Infix "≦" := (@leq (_ -mon-> _)) (at level 70, only parsing). 

(* this instance of [types_comp_leq] needs to be explicited to be useful for setoid-rewriting *)
#[export] Instance po_comp_leq {X Y Z: PO.type}:
  Proper (leq ==> leq ==> leq) (@comp POS X Y Z) := types_comp_leq.
(* idem for this one? *)
#[export] Instance setoid_comp_leq {X: Setoid.type} {Y Z: PO.type}:
  Proper (leq ==> eqv ==> leq) (@comp SETOIDS X Y Z) := types_comp_leq_eqv.


(* SANITY PO *)

Compute tt <= tt.

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


(** ** theory *)

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

Lemma Proper_flip A B (R: relation A) (S: relation B): Proper (flip R ==> S) ≡ Proper (R ==> flip S).
Proof. move=>f. apply: antisym=>Hf x y xy; by apply Hf. Qed.
Lemma Proper_half X Y: Proper (@eqv X ==> @leq Y) <= Proper (@eqv X ==> @eqv Y).
Proof. move=>f H x y xy. apply: antisym; apply H=>//. Qed.


Notation downward_closed := (Proper (leq ==> impl)). 
Notation upward_closed := (Proper (leq --> impl)). 

Section props.
Context {X: PO.type}.
Implicit Types x y z: X. 
Implicit Types P Q: X -> Prop.

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
#[export] Instance leq_covered: subrelation leq covered.
Proof. move=>P Q H x Px. exists x; split=>//. by apply H. Qed.
#[export] Instance eqv_covered: subrelation eqv bicovered.
Proof. move=>P Q. by rewrite eqv_of_leq; move=>[??]; split; apply leq_covered. Qed.

(* TOTHINK: infer [is_sup] using typeclasses? *)
Definition is_sup P x := forall z, x <= z <-> forall y, P y -> y <= z.

Lemma leq_is_sup P x: is_sup P x -> forall y, P y -> y <= x.
Proof. move=>H y Py. by apply H. Qed.

Lemma is_sup_leq P p Q q: is_sup P p -> is_sup Q q -> covered P Q -> p<=q.
Proof.
  move=>Pp Qq PQ. apply Pp=>x Px.
  case: (PQ x Px)=>y [Qy ->]. by apply Qq.
Qed.

Lemma is_sup_eqv P p Q q: is_sup P p -> is_sup Q q -> bicovered P Q -> p≡q.
Proof. rewrite eqv_of_leq=>??[??]. eauto using is_sup_leq. Qed.

Lemma supU (P: X -> Prop) x y: is_sup P x -> is_sup P y -> x ≡ y.
Proof. intros; eapply is_sup_eqv; eauto. Qed.

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
  move: (is_sup_single x). by apply Proper_is_sup. 
Qed.

Inductive sup_closure P: X -> Prop :=
| sc_inj: P <= sup_closure P
| sc_sup: sup_closed (sup_closure P).

Lemma is_sup_closure P: is_sup (sup_closure P) ≡ is_sup P.
Proof.
  move=>x. 
  apply: Proper_forall=>z.
  apply: Proper_iff=>//{x}.
  split=>H x Px.
  - by apply H, sc_inj.
  - elim: Px=>//Q QP IH y Hy. by apply Hy, IH. 
Qed.

(** greateast (post-)fixpoints of monotone functions,
    essentially Knaster-Tarski, also known as Lambek lemma in category theory *)
Definition is_gfp (f: X -> X) := is_sup (fun x => x <= f x). 
Proposition gfp_fixpoint (f: X -mon-> X) x: is_gfp f x -> f x ≡ x.
Proof.
  move=>H. symmetry; apply: antisym'.
  apply H=>y Hy. rewrite Hy. apply f. by apply H.
  move=>P. apply H=>//. by apply f.
Qed.

Definition directed P :=
  forall x y, P x -> P y -> exists z, P z /\ x <= z /\ y <= z.
Lemma directed_empty: directed empty.
Proof. by []. Qed.

Definition chain P :=
  forall x y, P x -> P y -> x <= y \/ y <= x.
Lemma chain_empty: chain empty.
Proof. by []. Qed.

Lemma chain_directed P: chain P -> directed P.
Proof. move=>H x y Px Py; by case:(H _ _ Px Py); eauto. Qed.

End props.

Section dual_props.
Context {X: PO.type}.
Implicit Types x y z: X. 
Implicit Types P Q: X -> Prop.

Lemma leq_from_below x y: (forall z, z <= x -> z <= y) -> x <= y.
Proof. dual @leq_from_above. Qed.
Lemma from_below x y: (forall z, z <= x <-> z <= y) -> x ≡ y.
Proof. dual @from_above. Qed.

Definition cocovered P := covered (P: dual X -> Prop).
Definition cobicovered P Q := bicovered (P: dual X -> Prop) Q.

Definition is_inf P x := forall z, z <= x <-> forall y, P y -> z <= y.
Lemma geq_is_inf P x: is_inf P x -> forall y, P y -> x <= y.
Proof. dual @leq_is_sup. Qed.
Lemma is_inf_leq P p Q q: is_inf P p -> is_inf Q q -> cocovered P Q -> q<=p.
Proof. dual @is_sup_leq. Qed.
Lemma is_inf_eqv P p Q q: is_inf P p -> is_inf Q q -> cobicovered P Q -> p≡q.
Proof. dual @is_sup_eqv. Qed.
Lemma infU (P: X -> Prop) x y: is_inf P x -> is_inf P y -> x ≡ y.
Proof. dual @supU. Qed.

Definition inf_closed (P: X -> Prop) := forall Q, Q <= P -> forall z, is_inf Q z -> P z.
Lemma inf_closed_impl (P Q: X -> Prop): Proper (leq ==> leq) P -> inf_closed Q -> inf_closed (fun x => P x -> Q x).
Proof. dual @sup_closed_impl. Qed.

Lemma inf_closed_leq (f: X -mon-> X): inf_closed (fun x => f x <= x).
Proof. exact (sup_closed_leq (dualf f)). Qed.

Definition inf_closure P: X -> Prop := sup_closure (P: dual X -> Prop).
Lemma is_inf_closure P: is_inf (inf_closure P) ≡ is_inf P.
Proof. dual @is_sup_closure. Qed.

Definition is_lfp (f: X -> X) := is_inf (fun x => f x <= x). 
Proposition lfp_fixpoint (f: X -mon-> X) x: is_lfp f x -> f x ≡ x.
Proof. apply (gfp_fixpoint (dualf f)). Qed.

Definition codirected P :=
  forall x y, P x -> P y -> exists z, P z /\ z <= x /\ z <= y.

Lemma codirected_empty: codirected empty.
Proof. by []. Qed.

Lemma chain_cochain P: chain P ≡ chain (P: dual X -> Prop).
Proof. by apply: antisym=>H x y Px Py; rewrite or_comm; apply H. Qed.

Lemma chain_codirected P: chain P -> codirected P.
Proof. rewrite chain_cochain. dual @chain_directed. Qed. 

End dual_props.


Definition image {X Y: Type} (f: X -> Y) (P: X -> Prop) y := exists x, P x /\ y = f x.
Definition image_id {X: Type} (P: X -> Prop): image types_id P ≡ P.
Proof. cbv. by firstorder subst. Qed.
Definition image_comp {X Y Z: Type} (f: Y -> Z) (g: X -> Y) (P: X -> Prop): image (types_comp f g) P ≡ image f (image g P).
Proof. cbv. firstorder subst; eauto. Qed.
Lemma in_image {X Y} (f: X -> Y) (P: X -> Prop) x: P x -> image f P (f x).
Proof. by exists x. Qed.
#[export] Hint Resolve in_image: core. 
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

(** sups can be computed pointwise in function spaces *)
Lemma dprod_sup {A} {X: A -> PO.type} (P: (forall a, X a)->Prop) (f: forall a, X a):
  (forall a, is_sup (image (fun h => h a) P) (f a)) -> is_sup P f.
Proof.
  move=>H g; split=>fg.
  - move=>h Ph. rewrite -fg=>a. apply H=>//. by exists h.
  - move=>a. apply H=>_ [h [Ph ->]]. by apply fg. 
Qed.
(** actually they *must* be computed pointwise, but not clear we can prove it without using decidability of equality on [A] *)
Lemma dprod_sup' {A} {X: A -> PO.type}
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

(** sups are computed pointwise in products
TOTHINK: get it as as special case of the above lemmas, with [A=bool]?      
 *)
Lemma prod_sup {X Y: PO.type} (P: (X*Y)->Prop) (p: X*Y):
  (is_sup (image fst P) (fst p) /\ is_sup (image snd P) (snd p)) <-> is_sup P p.
Proof.
  destruct p as [x y]. split.
  - move=>/=[H1 H2] [u v]. unfold leq=>/=. rewrite (H1 u) (H2 v)/=.
    split. move=>[F1 F2] [i j] Hij. split. apply F1. by eexists; eauto. apply F2. by eexists; eauto.
    move=>H. by split=>t [[i j] [Hij ->]]; apply H.
  - move=>H. split=>/=z.
    -- split=>E. move=>_ [[u v] [Huv ->]]/=. 
       rewrite <-E. apply (leq_is_sup H _ Huv).
       apply <- (H (z,y))=>[[u v] Puv]. split. apply E. by eexists; eauto. cbn.
       apply (leq_is_sup H _ Puv).
    -- split=>E. move=>_ [[u v] [Huv ->]]/=. 
       rewrite <-E. apply (leq_is_sup H _ Huv).
       apply <- (H (x,z))=>[[u v] Puv]. split; last first. apply E. by eexists; eauto. cbn.
       apply (leq_is_sup H _ Puv).
Qed.

(** sups can be computed as expected in sub-spaces *)
Section ks.
  Context {A} {X: PO.type} (f: A -> X) (P: kernel f->Prop) (a: kernel f).
  (* recall that [kernel f = A] *)
  Lemma kern_sup: is_sup (image f P) (f a) -> is_sup P a.
  Proof.
    move=>H b; split=>ab.
    -- move=>c Pc. rewrite -ab. by apply H; auto. 
    -- apply H=>_ [c [Pc ->]]. by apply ab.
  Qed.
End ks.


(** *  adjunctions *)
Section s.
  Context {X Y: PO.type}.
  Variables (f: X -> Y) (g: Y -> X).
  Class adjunction := adj: forall x y, f x <= y <-> x <= g y.
  
  #[local] Instance left_adjoint_leq {A: adjunction}: Proper (leq ==> leq) f.
  Proof. intros x y xy. apply adj. rewrite xy. by apply adj. Qed.
  
  #[local] Instance right_adjoint_leq {A: adjunction}: Proper (leq ==> leq) g.
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
