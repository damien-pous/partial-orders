(*

partial orders (leq, weq)
duality
monotone functions
adjoints

suprema
(infima by duality)

is_sup: (X -> Prop) -> X -> Prop 

- empty                 bot:   0            *
- singleton             id:                 *
- binary                cup:   X²           *     A->X
- finite                      (list X)      bool, A->X
- decidable                   (X->bool)     bool, F->X
- all                   sup:  (X->Prop)     Prop, A->X
- I                           (I -> X)

- directed                    {D: X->Prop | directed D}
- omega-increasing            {D: nat->X  | increasing D}
- chain                       {C: X->Prop | chain C}
- omega-chain                 {C: nat->X  | chain C}

- decidable? [X -> bool]                           bool

[below: to be linked with directed]
- chains
- omega-chains
- increasing omega-sequences


omega-increasing => omega-chain => chain => directed

classical logic: 
  omega-chain => omega-increasing
  chain-complete => directed-complete ()

Props:                                                                                closed under
chain P: forall x y, P x -> P y -> x<=y \/ y <=x                                    intersection
directed P: forall x y, P x -> P y -> exists z, P z /\ x<=z /\ y <=z                union
non-empty P: exists x, P x                                                          union
finite P: exists l, forall x, P x -> In x l                                         union, intersection

Sizes:
below T P: exists f: T -> X, P == im f
exact T P: exists f: T -> X, inj f /\ P == im f


 *)

From HB Require Import structures.
Require Import Setoid Morphisms Basics.
Require Import ssreflect.
Require Classical.              (* only to prove that the chain is a chain, which we do not use *)

Set Implicit Arguments.

(** * setoids *)

(** ** classes *)
HB.mixin Record Setoid_of_TYPE X := {
    #[canonical=no] eqv: relation X;
    #[canonical=no] Equivalence_eqv: Equivalence eqv
  }.
HB.structure Definition Setoid := { X of Setoid_of_TYPE X }.

HB.mixin Record Setoid_morphism_of_FUN (X Y: Setoid.type) (f: X -> Y) := {
    #[canonical=no] morphism_eqv: Proper (eqv ==> eqv) f
  }.
HB.structure Definition Setoid_morphism (X Y: Setoid.type) := { f of Setoid_morphism_of_FUN X Y f }.


(** ** notations *)
Infix "≡" := eqv (at level 70).
Notation "x ≡[ X ] y" := ((x: X) ≡ (y: X)) (at level 70, only parsing).
Notation "X '-eqv->' Y" := (Setoid_morphism.type X Y) (at level 99, Y at level 200).
  
(** ** properties *)
#[export] Existing Instance Equivalence_eqv.
#[export] Existing Instance morphism_eqv.
#[export] Hint Extern 0 => reflexivity: core.

(** ** instances *)
Definition eq_Setoid X := Setoid_of_TYPE.Build X eq_equivalence.
HB.instance Definition bool_Setoid := eq_Setoid bool. 
HB.instance Definition nat_Setoid := eq_Setoid nat. 

Section trivial.
 Variable (X: Type).
 Definition trivial_eqv: relation X := fun _ _ => True.
 Lemma Equivalence_trivial_eqv: Equivalence trivial_eqv.
 Proof. by constructor. Qed.
 Definition trivial_Setoid := Setoid_of_TYPE.Build X Equivalence_trivial_eqv.
End trivial.
HB.instance Definition unit_Setoid := trivial_Setoid unit. 
(* HB.instance Definition irrelevant_Setoid (P: Prop) := trivial_Setoid P.  *)

HB.instance Definition Prop_Setoid := Setoid_of_TYPE.Build Prop iff_equivalence. 

Section sumprod.
 Variables (X Y: Setoid.type).
 Definition eqv_prod: relation (X*Y) := fun x y => fst x ≡ fst y /\ snd x ≡ snd y.
 Lemma Equivalence_eqv_prod: Equivalence eqv_prod.
 Proof.
   constructor=>//.
   - by move=>??[]; split; symmetry. 
   - by move=>???[??][]; split; etransitivity; eassumption.
 Qed.
 HB.instance Definition prod_Setoid := Setoid_of_TYPE.Build _ Equivalence_eqv_prod.

 Definition eqv_sum: relation (X+Y) :=
   fun x y => match x,y with inl x,inl y | inr x,inr y => x ≡ y | _,_ => False end.
 Lemma Equivalence_eqv_sum: Equivalence eqv_sum.
 Proof.
   constructor.
   - by move=>[]//=. 
   - by move=>[?|?][?|?]//=; symmetry. 
   - by move=>[?|?][?|?][?|?]//=; etransitivity; eassumption.
 Qed.
 HB.instance Definition sum_Setoid := Setoid_of_TYPE.Build _ Equivalence_eqv_sum.
End sumprod.

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
 HB.instance Definition dprod_Setoid := Setoid_of_TYPE.Build _ Equivalence_eqv_dprod.  
End dprod.

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
 Definition kern_Setoid := Setoid_of_TYPE.Build _ Equivalence_eqv_kern.  
End kernel.
Arguments eqv_kern [_] _ _ _ _/.

HB.instance Definition sig_Setoid (X: Setoid.type) (P: X -> Prop) :=
  kern_Setoid X (@proj1_sig X P).

Goal forall (x: nat * sig (fun b: bool=> b=true)), x ≡ x.
  intros [x [b ?]]. cbv.
Abort.
Goal forall (x: nat * (bool -> nat) * {y: nat | y=5}), x ≡ x.
  intros [[x f] [p ?]]. cbv.
Abort.
(* need irrelevant_Setoid *)
Fail Check forall (x: nat * forall b: bool, nat + (b=true)), x ≡ x.


(** ** morphism instances  *)

(** identity function *)
HB.instance Definition id_Setoid_morphism {X} :=
  Setoid_morphism_of_FUN.Build X X id _. 

(** composition of functions *)
Definition comp {X Y Z} (f: Y -> Z) (g: X -> Y): X -> Z := fun x => f (g x).
Infix "°" := comp (at level 20).
Arguments comp {_ _ _} _ _ _/.
Program Definition comp_Setoid_morphism {X Y Z} (f: Y -eqv-> Z) (g: X -eqv-> Y) := 
  Setoid_morphism_of_FUN.Build X Z (f ° g) _.
Next Obligation. move=>x y xy. by do 2apply morphism_eqv. Qed. 
HB.instance Definition _ {X Y Z} f g := @comp_Setoid_morphism X Y Z f g.

HB.instance Definition _ {X Y: Setoid.type} := kern_Setoid _ (fun f: X-eqv->Y => f: X -> Y). 
#[export] Instance comp_eqv {X Y Z: Setoid.type}:
  Proper (eqv ==> eqv ==> eqv) (@comp X Y Z: (Y-eqv->Z) -> _ -> _).
Proof. move=>/=f f' ff' g g' gg' x=>/=. rewrite (gg' x). apply ff'. Qed.

Goal forall X: Setoid.type, forall f g h: X-eqv->X, f ≡ g -> f ° g ≡ h.
Proof. intros * H. Fail rewrite H. Abort. (* ARGH *)

(** constant function *)
Definition const {X Y} y: X -> Y := fun _ => y. 
Arguments const {_ _} _ _/.
HB.instance Definition const_Setoid_morphism {X Y} y :=
  Setoid_morphism_of_FUN.Build X Y (const y) (fun _ _ _ => reflexivity _). 

#[export] Instance const_eqv {X} {Y: Setoid.type}:
  Proper (eqv ==> eqv) (@const X Y).
Proof. move=>/=y y' yy x. apply yy. Qed.

Goal forall (X: Setoid.type) (f: X -eqv-> X) (x y: X), x≡y -> f (f x) ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  

(** ** duality *)
(** trivial for setoids, but required for subsequent layers *)
Definition dual (X: Type) := X.
HB.instance Definition dual_Setoid {X: Setoid.type} := Setoid_of_TYPE.Build (dual X) Equivalence_eqv.
Definition dualf {X Y: Type} (f: X -> Y): dual X -> dual Y := f.
Program Definition dual_Setoid_morphism {X Y} (f: X -eqv-> Y)
  := Setoid_morphism_of_FUN.Build (dual X) (dual Y) (dualf f) morphism_eqv.
HB.instance Definition _ {X Y} f := @dual_Setoid_morphism X Y f.

(** * partial orders *)

(** ** classes *)
HB.mixin Record PartialOrder_of_Setoid X of Setoid X := {
    #[canonical=no] leq: relation X;
    #[canonical=no] PreOrder_leq: PreOrder leq;
    #[canonical=no] eqv_of_leq: forall x y, eqv x y <-> (leq x y /\ leq y x);
}.
HB.factory Record PartialOrder_of_TYPE X := {
    #[canonical=no] leq: relation X;
    #[canonical=no] PreOrder_leq: PreOrder leq;
}.
HB.builders Context X (PO : PartialOrder_of_TYPE X).
  Definition leq_kernel (x y: X) := leq x y /\ leq y x. 
  Fact Equivalence_leq_kernel : Equivalence leq_kernel. 
  Proof.
    pose proof PreOrder_leq. unfold leq_kernel.
    constructor; repeat intro.
    - by []. 
    - tauto.
    - split; transitivity y; tauto.
  Qed.
  HB.instance
  Definition to_Setoid_of_TYPE :=
    Setoid_of_TYPE.Build X Equivalence_leq_kernel. 
  HB.instance
  Definition to_PartialOrder_of_Setoid :=
    PartialOrder_of_Setoid.Build X PreOrder_leq (fun _ _ => reflexivity _).
HB.end.
HB.structure Definition PartialOrder := { X of PartialOrder_of_TYPE X }.
(* HB.structure Definition PartialOrder := { X of PartialOrder_of_Setoid X & }. *)

Goal forall (X: PartialOrder.type) (x: nat -> X), x ≡ x.
  intros * n.  
Abort.
Goal forall A (X: A -> PartialOrder.type) (x: forall a, X a), x ≡ x. 
  intros * a.
Abort.


Lemma op_leq_eqv_1 {X Y: PartialOrder.type} {f: X -> Y} 
{Hf: Proper (leq ==> leq) f}: Proper (eqv ==> eqv) f.
Proof.
  rewrite /Proper/respectful.
  setoid_rewrite eqv_of_leq. 
  split; apply Hf; tauto.
Qed.

Lemma op_leq_eqv_2 {X Y Z: PartialOrder.type} {f: X -> Y -> Z}
  {Hf: Proper (leq ==> leq ==> leq) f}: Proper (eqv ==> eqv ==> eqv) f.
Proof.
  rewrite /Proper/respectful.
  setoid_rewrite eqv_of_leq. 
  split; apply Hf; tauto.
Qed.

HB.mixin Record PartialOrder_of_Setoid_morphism (X Y: PartialOrder.type) (f: X -eqv-> Y) := {
    #[canonical=no] morphism_leq: Proper (leq ==> leq) f
  }.
HB.factory Record PartialOrder_morphism_of_FUN (X Y: PartialOrder.type) (f: X -> Y) := {
    #[canonical=no] morphism_leq: Proper (leq ==> leq) f
  }.
HB.builders Context X Y f (F : PartialOrder_morphism_of_FUN X Y f).
  HB.instance
  Definition to_Setoid_morphism_of_FUN :=
    Setoid_morphism_of_FUN.Build X Y f (@op_leq_eqv_1 _ _ _ morphism_leq).
  HB.instance
  Definition to_PartialOrder_of_Setoid_morphism :=
    PartialOrder_of_Setoid_morphism.Build X Y _ morphism_leq.
HB.end.
(* WHY? *)
Fail HB.structure Definition PartialOrder_morphism (X Y: PartialOrder.type) := { f of PartialOrder_morphism_of_FUN X Y f }.
HB.structure Definition PartialOrder_morphism (X Y: PartialOrder.type) := { f of PartialOrder_of_Setoid_morphism X Y f & }.


(** ** notations *)
Infix "<=" := leq (at level 70).
Notation "x <=[ X ] y" := ((x: X) <= (y: X)) (at level 70, only parsing).

Definition lt {X: PartialOrder.type} (x y: X) := x<=y /\ ~y<=x.
Infix "<" := lt (at level 70).
Notation "x <[ X ] y" := ((x: X) < (y: X)) (at level 70, only parsing).

Notation "X '-mon->' Y" := (PartialOrder_morphism.type X Y) (at level 99, Y at level 200).

(** ** immediate properties *)

#[export] Existing Instance PreOrder_leq.
#[export] Existing Instance morphism_leq.
#[export] Instance PartialOrder_eqv_leq {X: PartialOrder.type}: @RelationClasses.PartialOrder X eqv _ leq _.
Proof. intros x y. apply eqv_of_leq. Qed.
#[export] Instance leq_rw {X: PartialOrder.type}: @RewriteRelation X leq := {}.

(** ** instances *)

Lemma impl_PreOrder: PreOrder impl. 
Proof. split; cbv; tauto. Qed.
HB.instance Definition Prop_PartialOrder := PartialOrder_of_Setoid.Build Prop impl_PreOrder (fun _ _ => reflexivity _).

Lemma bool_PreOrder: PreOrder Bool.le.
Admitted.
Lemma bool_eqv_of_leq (a b: bool): a=b <-> Bool.le a b /\ Bool.le b a.
Admitted.
HB.instance Definition bool_PartialOrder := PartialOrder_of_Setoid.Build bool bool_PreOrder bool_eqv_of_leq.

Lemma nat_PreOrder: PreOrder Peano.le.
Admitted.
Lemma nat_eqv_of_leq (a b: nat): a=b <-> Peano.le a b /\ Peano.le b a.
Admitted.
HB.instance Definition nat_PartialOrder := PartialOrder_of_Setoid.Build nat PeanoNat.Nat.le_preorder nat_eqv_of_leq.

Section dprod.
 Variables (A: Type) (X: A -> PartialOrder.type).
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
 HB.instance Definition dprod_PartialOrder :=
   PartialOrder_of_Setoid.Build (forall a, X a) PreOrder_leq_dprod eqv_of_leq_dprod.
End dprod.

Section kernel.
 Variables (A: Type) (X: PartialOrder.type) (f: A -> X).
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
 #[local] HB.instance Definition kern_Setoid_ := kern_Setoid X f.
 Definition kern_PartialOrder :=
   PartialOrder_of_Setoid.Build A PreOrder_leq_kern eqv_of_leq_kern.  
End kernel.
Arguments leq_kern [_] _ _ _ _/.
   
HB.instance Definition sig_PartialOrder (X: PartialOrder.type) (P: X -> Prop) :=
  kern_PartialOrder X (@proj1_sig X P).

Section discrete.
  Context {X: Setoid.type}.
  Lemma discrete_eqv_of_leq (x y: X): x ≡ y <-> x ≡ y /\ y ≡ x.
  Proof. intuition. Qed.
  (* TO UNDERSTAND *)
  Fail Definition discrete_PartialOrder :=
    PartialOrder_of_Setoid.Build X _ discrete_eqv_of_leq.
  Definition discrete_PartialOrder :=
    PartialOrder_of_TYPE.Build X (leq:=eqv) _.
End discrete.
(* commented instance below raises non-forgetful inheritance pb
   would it work with the above failing definition? *)
(* HB.instance Definition unit_PartialOrder := @discrete_PartialOrder unit. *)
HB.instance Definition unit_PartialOrder := PartialOrder_of_Setoid.Build unit _ discrete_eqv_of_leq.

(* HB.instance Definition irrelevant_PartialOrder (P: Prop) := @discrete_PartialOrder P. *)


(** ** morphism instances  *)

(** identity function *)
HB.instance Definition id_PartialOrder_morphism {X} :=
  PartialOrder_of_Setoid_morphism.Build X X id _. 

(** composition of functions *)
Program Definition comp_PartialOrder_morphism {X Y Z} (f: Y -mon-> Z) (g: X -mon-> Y) := 
  PartialOrder_of_Setoid_morphism.Build X Z (f ° g) _.
Next Obligation. move=>x y xy. by do 2apply morphism_leq. Qed. 
HB.instance Definition _ {X Y Z} f g := @comp_PartialOrder_morphism X Y Z f g.

HB.instance Definition _ {X Y: PartialOrder.type} := kern_Setoid _ (fun f: X-mon->Y => f: X -> Y). 
HB.instance Definition _ {X Y: PartialOrder.type} := kern_PartialOrder _ (fun f: X-mon->Y => f: X -> Y). 
#[export] Instance comp_leq {X Y Z: PartialOrder.type}:
  Proper (leq ==> leq ==> leq) (comp: (Y-mon->Z) -> (X->Y) -> (X->Z)).
Proof. move=>/=f f' ff' g g' gg' x=>/=. rewrite (gg' x). apply ff'. Qed.

(** constant function *)
HB.instance Definition const_PartialOrder_morphism {X Y} y :=
  PartialOrder_of_Setoid_morphism.Build X Y (const y) (fun _ _ _ => reflexivity _). 

#[export] Instance const_leq {X} {Y: PartialOrder.type}:
  Proper (leq ==> leq) (@const X Y).
Proof. move=>/=y y' yy x. apply yy. Qed.

Goal forall (X: PartialOrder.type) (f: X -mon-> X) (x y: X), x≡y -> y<=x -> f (f x) <= (f (f x)).
Proof.
  intros * H H'. rewrite {1}H H'. reflexivity.
Abort.  

(** ** duality *)

Section dual.
 Context {X: PartialOrder.type}.
 Lemma dual_eqv_of_leq (x y: dual X): x ≡ y <-> y <= x /\ x <= y.
 Proof. cbn. rewrite eqv_of_leq. tauto. Qed.
 HB.instance Definition dual_PartialOrder :=
   PartialOrder_of_Setoid.Build (dual X) (flip_PreOrder _) dual_eqv_of_leq.
End dual.
Program Definition dual_PartialOrder_morphism {X Y} (f: X -mon-> Y)
  := PartialOrder_of_Setoid_morphism.Build (dual X) (dual Y) (dualf f) _.
Next Obligation. move=>x y. apply f. Qed.
HB.instance Definition _ {X Y} f := @dual_PartialOrder_morphism X Y f.


(** ** properties *)
Section s.
Context {X: PartialOrder.type}.
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


(** trivial properties of composition *)
Lemma compA {X Y Z T} (f: Z->T) (g: Y->Z) (h: X->Y): f ° (g ° h) = (f ° g) ° h.
Proof. by []. Qed.
Lemma compIx {X Y} (f: X->Y): id ° f = f.
Proof. by []. Qed. 
Lemma compxI {X Y} (f: X->Y): f ° id = f.
Proof. by []. Qed. 
Lemma compCx {X Y Z} (f: X->Y) (z: Z): const z ° f = const z.
Proof. by []. Qed. 
Lemma compxC {X Y Z} (f: Y->Z) (y: Y): f ° @const X Y y = const (f y).
Proof. by []. Qed. 

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
Context {X: PartialOrder.type}.
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
#[export] Instance PartialOrder_covered: RelationClasses.PartialOrder bicovered covered.
Proof. by []. Qed.
(* TOTHINK: declare [subrelation] instances? *)
Lemma leq_covered P Q: P <= Q -> covered P Q.
Proof. move=>H x Px. exists x; split=>//. by apply H. Qed.
Lemma eqv_covered f g: f ≡ g -> bicovered f g.
Proof. by rewrite eqv_of_leq; move=>[??]; split; apply leq_covered. Qed.
End s.

Section s.
Context {X: PartialOrder.type}.
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
Proof. eauto using is_sup_eqv. Qed.

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

Definition downward_closed (P: X -> Prop) := Proper (leq ==> leq) P. 

Definition directed (P: X -> Prop) :=
  forall x y, P x -> P y -> exists z, P z /\ x <= z /\ y <= z.

End s.

Section s.
Context {X: PartialOrder.type}.
Implicit Types x y: X.

Lemma leq_from_below x y: (forall z, z <= x -> z <= y) -> x <= y.
Proof. apply (leq_from_above (y: dual X)). Qed.
Lemma from_below x y: (forall z, z <= x <-> z <= y) -> x ≡ y.
Proof. apply (from_above (x: dual X)). Qed.

Definition is_inf (P: X -> Prop) x := forall z, z <= x <-> forall y, P y -> z <= y.
Lemma infU (P: X -> Prop) x y: is_inf P x -> is_inf P y -> x ≡ y.
Proof. apply (supU (P:=P: dual X -> Prop)). Qed.

Definition inf_closed (P: X -> Prop) := forall Q, Q <= P -> forall z, is_inf Q z -> P z.

Lemma inf_closed_impl (P Q: X -> Prop): Proper (leq ==> leq) P -> inf_closed Q -> inf_closed (fun x => P x -> Q x).
Proof. apply (sup_closed_impl (P:=P: dual X->Prop)). Qed.

Lemma inf_closed_leq (f: X -mon-> X): inf_closed (fun x => f x <= x).
Proof. apply (sup_closed_leq (dualf f)). Qed.

End s.


Definition image {X Y: Type} (f: X -> Y) (P: X -> Prop) y := exists x, P x /\ y = f x.
Lemma forall_image {X Y: Type} (f: X -> Y) (P: X -> Prop) (Q: Y -> Prop):
  image f P <= Q <-> forall x, P x -> Q (f x).
Proof.
  split=>H.
  - move=>x Px. apply H. by exists x.
  - move=>y [x [Px ->]]; auto. 
Qed.
Section s.
Context {X: Type} {Y: PartialOrder.type}.
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

(** adjunctions *)
Section s.
  Context {X Y: PartialOrder.type}.
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

Lemma adjoint_id {X}: @adjunction X X id id.
Proof. by []. Qed.

Lemma adjoint_comp {X Y Z f g f' g'} {A: @adjunction X Y f g} {B: @adjunction Y Z f' g'}:
  adjunction (fun x => f' (f x)) (fun z => g (g' z)).
Proof. move=>x y. by rewrite 2!adj. Qed.

Lemma dual_adjunction `(A: adjunction): adjunction (g: dual Y -> dual X) (f: dual X -> dual Y).
Proof. rewrite /adjunction/= => y x. symmetry. by apply adj. Qed.

Lemma right_adjoint_inf `(A: adjunction) P y: is_inf P y -> is_inf (image g P) (g y).
Proof. apply (left_adjoint_sup (dual_adjunction A)). Qed. 

Section c.
 Context {X: PartialOrder.type}.
 Variable f: X -mon-> X.

 (** the set of all (transfinite) iterations of b 
     although this set is (classically) a chain, we never need to know it *)
 Inductive C: X -> Prop :=
 | Cf: forall x, C x -> C (f x)
 | Csup: forall P, P <= C -> forall x, is_sup P x -> C x.

 (** a type for the elements of the chain *)
 Structure Chain := chain { elem:> X; #[canonical=no] Celem: C elem}.
 Definition elem' := elem: Chain -> Setoid.sort X.
 Arguments elem' _/. 
 Coercion elem': Chain >-> Setoid.sort. 

 (** the chain is closed under [f] *)
 Canonical Structure chain_next (x: Chain) := {| elem := f x; Celem := Cf (Celem x) |}.

 (** tower induction principle (just a rephrasing of induction on the Chain predicate) *)
 Proposition tower (P: X -> Prop):
   sup_closed P ->
   (forall x: Chain, P x -> P (f x)) ->
   (forall x: Chain, P x).
 Proof.
   intros Hsup Hf [x Cx]; cbn. induction Cx as [x Cx IH|Q _ QP Px IH].
   - now apply (Hf (chain Cx)).
   - eapply Hsup. exact QP. exact IH. 
 Qed.

 (** slightly stronger version where the predicate need only be C-sup closed 
     (TOTHINK: remove?)
  *)
 Proposition tower' (P: X -> Prop):
   (forall Q, Q <= C -> Q <= P -> forall z: Chain, is_sup Q z -> P z) ->
   (forall x: Chain, P x -> P (f x)) ->
   (forall x: Chain, P x).
 Proof.
   intros Hsup Hf [x Cx]; cbn. induction Cx as [x Cx IH|Q QC QP x Px].
   - now apply (Hf (chain Cx)).
   - have Cx: C x by eapply Csup; eauto. 
     exact (Hsup _ QC QP (chain Cx) Px). 
 Qed.
 
 (** elements of the chain are post-fixpoints of [f] *)
 Lemma chain_postfixpoint: forall c: Chain, c <= f c.
 Proof.
   apply (tower (sup_closed_leq _))=>*.
   by apply f.
 Qed.

 (** they are below all pre-fixpoints of [f] *)
 Theorem chain_below_prefixpoints x: f x <= x -> forall c: Chain, c <= x.
 Proof.
   intro. apply (tower (sup_closed_leq (const x)))=>/=.
   by move=>y ->.
 Qed.
 
 (** relativised tower induction *)
 Proposition ptower (Q P: X -> Prop):
   Proper (leq --> leq) Q ->
   sup_closed P ->
   (forall x: Chain, Q x -> P x -> P (f x)) ->
   (forall x: Chain, Q x -> P x).
 Proof.
   intros Qleq Psup Pb. apply (tower (P:=fun x => Q x -> P x)). 
   - now apply sup_closed_impl.
   - intros x I H. cut (Q x); auto. revert H. apply Qleq, chain_postfixpoint. 
 Qed.

 (** if the chain contains a pre-fixpoint, then this is the least (pre-)fixpoint *)
 Theorem lpfp (c: Chain): f c <= c -> is_inf (fun x => f x <= x) c.
 Proof.
   intros Hc x. split=>H.
   - intros y Hy. rewrite H. by apply chain_below_prefixpoints.
   - by apply H.
 Qed.

 (** if the chain has a supremum, then this is the least (pre-)fixpoint *)
 Theorem lpfp' t: is_sup C t -> is_inf (fun x => f x <= x) t.
 Proof.
   intro Ht.
   have Ct: C t by eapply Csup.
   apply (lpfp (chain Ct))=>/=. 
   apply Ht=>//. by apply Cf. 
 Qed.

 (* * the chain inherits the partial order *)
 (* * deactivated: otherwise [c <= x] does no longer typecheck when [c: Chain] and [x: X] *)
 HB.instance Definition Chain_Setoid := kern_Setoid _ elem.
 HB.instance Definition Chain_PartialOrder := kern_PartialOrder _ elem.
 Lemma chain_next_leq: Proper (leq ==> leq) chain_next.
 Proof. by move =>???; apply f. Qed.
 HB.instance Definition e := PartialOrder_morphism_of_FUN.Build Chain Chain chain_next chain_next_leq. 

 Lemma id_next: @id Chain <= chain_next.
 Proof. move=>x. apply chain_postfixpoint. Qed.
 
 (* TODO: exploit Bourbaki' from there *)
 
End c.


Module Bourbaki. Section b.

 (* TODO: 
    finish to get Theorem 2.1 from [Serge Lang, Algebra, p881]
    (in two steps, for non-emptyness)
  *)

 Context {X: PartialOrder.type}.
 Implicit Types x y z: X.

 Variable next: X -eqv-> X. 
 Hypothesis tower: forall (P: X -> Prop), sup_closed P -> (forall x, P x -> P (next x)) -> forall x, P x.
 Hypothesis id_next: @id X <= next.

 (** relativised tower induction *)
 Lemma ptower (Q P: X -> Prop):
   Proper (leq --> leq) Q ->
   sup_closed P ->
   (forall x, Q x -> P x -> P (next x)) ->
   (forall x, Q x -> P x).
 Proof.
   intros Qleq Psup Pb. apply: tower. 
   - now apply sup_closed_impl.
   - intros x I H. cut (Q x); auto. revert H. apply Qleq, id_next. 
 Qed.

 Import Classical.

 (** a generic consequence of excluded-middle *)
 Lemma choose_gen (P A B: X -> Prop):
   (forall x, P x -> A x \/ B x) -> (forall x, P x -> A x) \/ (exists x, P x /\ B x).
 Proof.
   intro H. classical_left. intros x Px.
   destruct (H _ Px). assumption. exfalso; eauto. 
 Qed.

 (** a more specific consequence; 
     - we only use it with [f=id, y=y'] to get than the chain is totally ordered
     - we only use it with [f=id, y'=next y] and [f=next, y'= y] to get the stronger [total_chain_strong]
  *)
 Lemma choose (P: X -> Prop) f y y':
   (forall x, P x -> f x <= y \/ y' <= x) -> (forall x, P x -> f x <= y) \/ (exists x, P x /\ y' <= x).
 Proof. apply choose_gen. Qed.

 (** strengthening the above result as follows requires more work, but leads to a proof that [X] is a well-order *)
 Theorem total_chain_strong: forall x y, x <= y \/ next y <= x.
 Proof.
   (** this proof is inspired from Bourbaki's proof, 
       as reported in [Serge Lang, Algebra, p883]
       differences are that:
       - we use definitions that attempt to minimise the required amount of classical logic
       - we do no assume X (and thus admissible sets) to be non-empty
       - we do not start from a CPO, only from a mere partial order 
         (accordingly, the [tower] assumption requires closure under all existing suprema rather than under all directed suprema)
    *)
   (* [split x c] is [x \in M c] in the aforementioned book *)
   set split := fun x y => x <= y \/ next y <= x.
   (* [extreme c], up to classical logic, is [forall x, x < c -> next x <= c] *)
   set extreme := fun c => forall x, x <= c -> split c x. 
   (* Lemma 2.2 *)
   have M: forall c, extreme c -> forall x, split x c. {
     move=>c Ec. apply: tower.
     - move=>T IH t Ht.
       case: (choose T id c (next c)).
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

 (** an alternative formulation of the above theorem *)
 Corollary chain_extreme x y: x < next y -> x <= y.
 Proof. case: (total_chain_strong x y)=>?[]; tauto. Qed. 

 (** [X] is totally ordered, as an immediate corollary  *)
 Corollary total_chain x y: x <= y \/ y <= x.
 Proof.
   case: (total_chain_strong x y); auto=>xy.
   right. rewrite -xy. apply id_next.
 Qed.

 (** the chain is well-founded, and thus a well-order
     TOTHINK: 
     - did not see this in the litterature, any applications?
     - is there a way to get it constructively? 
       (it seems we only have to replay the [tower] assumption)
  *)
 Theorem wf_chain: @well_founded X lt.
 Proof.
   have E: forall x, (forall y, y<=x -> Acc lt y). {
     apply: tower.
     - move=>T IH t Ht y yx. constructor=>z zy. 
       have zx: z < t by apply ltle_lt with y. 
       case: (choose T id z z).
       by move=>*; apply total_chain.
       -- move=>C. apply proj2 in zx. contradict zx. by apply Ht, C. 
       -- move=>[u [Tu /=zu]]. by apply IH with u.
     - move=>x IH y yx. constructor=>z zy. apply IH.
       apply chain_extreme. eapply ltle_lt; eassumption.
   }.
   by move=>?; eauto.
 Qed.

 (** there is at most one prefixpoint, which must be a top element  *)
 Lemma prefixpoint_top x: next x <= x -> is_sup (fun _ => True) x.
 Proof.
   move=>H y. split; auto=>xy z _. rewrite -xy. clear y xy.
   revert z. apply: tower. apply (sup_closed_leq (const x)).
   move=>y yx. case: (total_chain_strong x y); auto=>xy.
   have E: y≡x by apply antisym. by rewrite E.
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

   (* excluded middle of course works *)
   Restart.
   intros. apply: classic.
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
                       
End b. End Bourbaki. 

Module Bourbaki'. Section b.

 Context {X: PartialOrder.type}.
 Implicit Types x y z: X.

 (** tower induction *)
 Variable next: X -mon-> X.
 Hypothesis tower: forall (P: X -> Prop), sup_closed P -> (forall x, P x -> P (next x)) -> forall x, P x.

 (** the function [next] must be extensive *)
 Lemma id_next: @id X <= next.
 Proof.
   apply: tower=>/=.
   - apply sup_closed_leq.
   - by move=>*; apply next.
 Qed.

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
   exact (Bourbaki.total_chain next tower id_next).
   Restart. 
   (** but the following proof is simpler and requires only [choose _ id x x] *)
   apply: tower.
   - move=>T IH t Ht y.
     case: (Bourbaki.choose T id y y). by move=>*; apply IH.
     -- move=>F. left. apply Ht=>x Tx. by apply F.
     -- move=>[x [Tx yx]]. right. rewrite yx. by apply Ht.
   - move=>x IH y.
     case: (Bourbaki.choose (fun t => next t <= y) id x x).
     by move=>t _; move: (IH t); tauto.
     -- move=>F. right. apply leq_next=>z zy. by apply F.
     -- move=>[t [ty xt]]. left. by rewrite xt.
 Qed.

 (** [X] is directed, as an immediate consequence *)
 Corollary directed_chain: directed (fun _: X => True).
 Proof. move=>x y _ _. case: (total_chain x y); eauto. Qed.
                       
End b. End Bourbaki'. 


Definition empty {X}: X -> Prop := fun _ => False. 
Definition pair {X} (x y: X): X -> Prop := fun z => z=x \/ z=y. 

Unset Implicit Arguments.  
HB.mixin Record Lattice_of_PartialOrder X of PartialOrder X := {
    #[canonical=no] bot: X;
    #[canonical=no] top: X;
    #[canonical=no] cup: X -> X -> X;
    #[canonical=no] cap: X -> X -> X;
    #[canonical=no] bot_spec: is_sup empty bot;
    #[canonical=no] top_spec: is_inf empty top;
    #[canonical=no] cup_spec: forall x y, is_sup (pair x y) (cup x y);
    #[canonical=no] cap_spec: forall x y, is_inf (pair x y) (cap x y)
}.
HB.structure Definition Lattice := { X of Lattice_of_PartialOrder X & }.

Program Definition Prop_Lattice := Lattice_of_PartialOrder.Build Prop False True or and _ _ _ _.
Next Obligation. cbv. firstorder. Qed.
Next Obligation. cbv. firstorder. Qed.
Next Obligation. cbv. firstorder subst; eauto. Qed.
Next Obligation. cbv. firstorder subst; eauto; apply H; eauto. Qed.
HB.instance Definition _ := Prop_Lattice.

Program Definition dprod_Lattice {A} {X: A -> Lattice.type} :=
  Lattice_of_PartialOrder.Build
    (forall a, X a) (fun _ => bot) (fun _ => top)
    (fun f g a => cup (f a) (g a))
    (fun f g a => cap (f a) (g a)) _ _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
HB.instance Definition _ {A} {X: A -> Lattice.type} := @dprod_Lattice A X.



HB.mixin Record CPO_of_PartialOrder X of PartialOrder X := {
    #[canonical=no] dsup: forall D: X -> Prop, directed D -> X;
    #[canonical=no] dsup_spec: forall D (DD: directed D), is_sup D (dsup D DD);
}.
HB.structure Definition CPO := { X of CPO_of_PartialOrder X & }.

Lemma leq_dsup {X: CPO.type} (P: X -> Prop) D: forall y, P y -> y <= dsup P D.
Proof. apply leq_sup, dsup_spec. Qed.

Program Definition dprod_CPO {A} (X: A -> CPO.type) :=
  CPO_of_PartialOrder.Build (forall a, X a) (fun F DF a => dsup (image (fun f => f a) F) _) _.
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
HB.instance Definition _ {A} (X: A -> CPO.type) := dprod_CPO X.


(* TOTHINK: required or not? *)
(* HB.instance Definition mon_Setoid {X Y: PartialOrder.type} := kern_Setoid _ (fun f: X-mon->Y => f: X -> Y).  *)
HB.instance Definition mon_PartialOrder {X Y: PartialOrder.type} := kern_PartialOrder _ (fun f: X-mon->Y => f: X -> Y). 
(* TODO: generic construction (via dprod_CPO) *)  
Program Definition mon_dsup {X} {Y: CPO.type} (F: (X-mon->Y) -> Prop) (DF: directed F): X -> Y :=
  fun x => dsup (image (fun f: X-mon->Y => f x) F) _.
Next Obligation.
  move=>/=_ _ [g [G ->]] [h [H ->]].
  case: (DF _ _ G H)=>/=[i [I [gi hi]]].
  exists (i x). split. by exists i. split. apply gi. apply hi.
Qed.
Lemma mon_dsup_leq {X} {Y: CPO.type} (F: (X-mon->Y) -> Prop) (DF: directed F): Proper (leq ==> leq) (mon_dsup F DF).
Proof.
  move=>x y xy. apply: is_sup_leq; try apply dsup_spec.
  apply covered_image=>//f. by apply f.
Qed.
Program Definition mon_dsup_setoid {X} {Y: CPO.type} (F: (X-mon->Y) -> Prop) (DF: directed F) :=
  Setoid_morphism_of_FUN.Build X Y (mon_dsup F DF) _.
Next Obligation. apply @op_leq_eqv_1. apply mon_dsup_leq. Qed.
HB.instance Definition _ {X Y} F DF := @mon_dsup_setoid X Y F DF.
HB.instance Definition mon_dsup_partialorder {X} {Y: CPO.type} (F: (X-mon->Y) -> Prop) (DF: directed F) :=
  PartialOrder_of_Setoid_morphism.Build X Y (mon_dsup F DF) (mon_dsup_leq F DF).
Program Definition mon_CPO {X} {Y: CPO.type} :=
  CPO_of_PartialOrder.Build (X-mon->Y) (@mon_dsup X Y) _. 
Next Obligation.
  move=>/=f. split=>H.
  - move=>g G. rewrite -H=>a. apply leq_dsup. by exists g.
  - move=>a. apply dsup_spec=>/=_ [g [G ->]]. by apply H. 
Qed.
HB.instance Definition _ {X Y} := @mon_CPO X Y.

Module P.
Section pataraia.
 Context {X: CPO.type}.
 
 Program Definition h: X-mon->X := dsup (fun f => id <=[X-mon->X] f) _.
 Next Obligation.
   (* this is indeed a directed sup *)
   move=>i j I J/=. exists (i°j)=>/=. split; last split.
   - transitivity (id ° j). apply J. by apply comp_leq.
   - intro. apply i, J.
   - intro. apply I.
   (* by rewrite -I. split. *)
   (* by rewrite -J.  *)
   (* by rewrite -I. *)
 Qed.
 
 Lemma h_ext: id <=[X-mon->X] h.
 Proof. by apply: leq_dsup. Qed.

 Lemma h_invol: h ° h <=[X-mon->X] h.
 Proof.
   apply: leq_dsup.
   change (@id X <= h°h).
   transitivity (@id X ° id)=>//.
   apply: comp_leq; apply h_ext.
   (* by rewrite -h_ext. *)
 Qed.

 Variable next: X-mon->X.
 Hypothesis id_next: id <=[X-mon->X] next. 

 Lemma next_h: next <= h.
 Proof. apply: leq_dsup. apply id_next. Qed.
 
 Lemma h_prefixpoint: next ° h <= h.
 Proof.
   etransitivity. 2: apply h_invol.
   apply comp_leq=>//. apply next_h.
 Qed.

 (* TODO: define [bot] in all CPOs *)
 Program Definition lfp := h (dsup empty _).
 Next Obligation. by []. Qed.

 Theorem next_lfp: next lfp ≡ lfp. 
 Proof. apply antisym. apply h_prefixpoint. apply id_next. Qed.

End pataraia.
End P.
