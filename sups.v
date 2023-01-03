Require Import Setoid Morphisms Basics.
Require Import ssreflect.
Require Eqdep_dec Classical.

Set Implicit Arguments.

(** * partial orders *)

Variant K := kE | kB | kA.
Definition args k X: Type :=
  match k with
  | kE => unit
  | kB => X * X
  | kA => (X -> Prop)
  end.
Definition setof X k: args k X -> X -> Prop :=
  match k with
  | kE => fun _ _ => False
  | kB => fun p => fun x => x=fst p \/ x=snd p
  | kA => fun P => P
  end.
Definition test b (X: Type) := if b then X else unit.
Definition testP b (X: Type)(P: X -> Prop): test b X -> Prop :=
  if b return test b X -> Prop then P else fun _ => True.
Definition L := K -> bool.

(** ** class *)

Structure PO (l: L) := po {
    car:> Type;
    #[canonical=no] eqv: relation car;
    #[canonical=no] leq: relation car;
    #[canonical=no] PreOrder_leq: PreOrder leq;
    #[canonical=no] eqv_of_leq: forall x y, eqv x y <-> (leq x y /\ leq y x);
    #[canonical=no] gsup: forall k, test (l k) (args k car -> car);
    #[canonical=no] is_sup (P: car -> Prop) (s: car) := forall x, leq s x <-> forall p, P p -> leq p x;
    #[canonical=no] gsup_spec: forall k, testP (l k) (fun gsup_k => forall x, is_sup (setof k x) (gsup_k x)) (gsup k)
  }.
Arguments po: clear implicits. 
Arguments eqv {_ _}. 
Arguments leq {_ _}. 
Infix "≡" := eqv (at level 70).
Infix "<=" := leq (at level 70).
Definition lt {k} {X: PO k} (x y: X) := x<=y /\ ~y<=x.
Infix "<" := lt (at level 70).
#[export] Existing Instance PreOrder_leq.
#[export] Hint Extern 0 => reflexivity: core.

(** ** basic properties *)

Section s.
 Context {l} {X: PO l}.
 Implicit Types x y: X.

 #[export] Instance Equivalence_eqv: @Equivalence X eqv.
 Proof.
    constructor.
    - move=>x. rewrite eqv_of_leq. by split. 
    - move=>x y. rewrite 2!eqv_of_leq. tauto.
    - move=>x y z. rewrite 3!eqv_of_leq. split; transitivity y; tauto.
 Qed.
 #[export] Instance PartialOrder_eqv_leq: PartialOrder eqv leq.
 Proof. intros x y. apply eqv_of_leq. Qed.
 #[export] Instance leq_rw: @RewriteRelation X leq := {}.
 
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
 #[export] Instance Transitive_lt: @Transitive X lt.
 Proof. move=>x y z [xy _]. by apply lelt_lt. Qed.
  
End s.

(** ** instances *)

Program Definition discrete_po X (e: relation X) (E: Equivalence e) := po (fun _ => false) X e e _ _ (fun _ => tt) _.
Next Obligation. cbv. by intuition symmetry. Qed.
Definition eq_discrete_po X := discrete_po (@eq_equivalence X).

Canonical Structure unit_po := eq_discrete_po unit. (* TODO: could allow any level *)

Program Canonical Structure irrelevant_po (P: Prop) := @discrete_po P (fun _ _ => True) _.
Next Obligation. by constructor. Qed.

Program Canonical Structure bool_po := po bool eq Bool.le _ _.
Admit Obligations.

Program Canonical Structure nat_po := po nat eq Peano.le _ _.
Admit Obligations.

Program Canonical Structure Prop_po := po Prop iff impl _ _.
Admit Obligations.

Program Canonical Structure prod_po (X Y: PO) :=
  po (X*Y)
     (fun p q => fst p ≡ fst q /\ snd p ≡ snd q)
     (fun p q => fst p <= fst q /\ snd p <= snd q)
     _ _.
Next Obligation.
  constructor=>//.
  by move=>???[??][]; split; etransitivity; eassumption.
Qed.
Next Obligation.
  setoid_rewrite eqv_of_leq=>/=. tauto.
Qed.

Definition lex_prod := prod.  
Program Canonical Structure lex_prod_po (X Y: PO) :=
  po (lex_prod X Y)
     (fun p q => fst p ≡ fst q /\ snd p ≡ snd q)
     (fun p q => fst p <= fst q /\ (fst q <= fst q -> snd p <= snd q))
     _ _.
Next Obligation.
  constructor=>//.
  move=>[x x'][y y'][z z']/=.
  intuition solve [transitivity y; auto|transitivity y'; auto].
Qed.
Next Obligation.
  setoid_rewrite eqv_of_leq=>/=. intuition.
Qed.
  
(* TODO: parallel and sequential sums, lists *)

Program Canonical Structure dprod_po A (X: A -> PO) :=
  po (forall a, X a)
     (fun f g => forall a, f a ≡ g a)                                          
     (fun f g => forall a, f a <= g a)
     _ _.
Next Obligation.
  constructor.
  - by move=>??. 
  - by move=>??????; etransitivity; eauto.
Qed.
Next Obligation.
  setoid_rewrite eqv_of_leq. firstorder. 
Qed.

Program Definition kern_po A (X: PO) (f: A -> X) :=
  po A (fun a b => f a ≡ f b) (fun a b => f a <= f b) _ _.
Next Obligation.
  constructor.
  - by move=>//=. 
  - by move=>?????; etransitivity; eauto.
Qed.
Next Obligation.
  apply eqv_of_leq.
Qed.

Canonical Structure sig_po (X: PO) (P: X -> Prop) :=
  kern_po X (@proj1_sig X P).

Definition dual (X: Type) := X.
Program Canonical Structure dual_po (X: PO) :=
  po (dual X) eqv (flip leq) _ _.
Next Obligation. rewrite eqv_of_leq. tauto. Qed.


Goal forall (x: nat * sig (fun b: bool=> b=true)), x ≡ x.
  intros [x [b ?]]. cbv.
Abort.
Goal forall (x: nat * (bool -> nat) * {y: nat | y=5}), x ≡ x.
  intros [[x f] [p ?]]. cbv.
Abort.
Check forall (x: nat * forall b: bool, nat * (b=true)), x ≡ x.



(** * morphisms *)

Record Morphism (X Y: PO) := {
    body:> X -> Y;
    body_leq: Proper (leq ==> leq) body;
  }.
Notation "X '-mon->' Y" := (Morphism X Y) (at level 99, Y at level 200).
#[export] Existing Instance body_leq.

(** ** basic properties *)

Lemma op_leq_eqv_1 {X Y: PO} {f: X -> Y} 
 {Hf: Proper (leq ==> leq) f}: Proper (eqv ==> eqv) f.
Proof.
  rewrite /Proper/respectful.
  setoid_rewrite eqv_of_leq. 
  split; apply Hf; tauto.
Qed.

Lemma op_leq_eqv_2 {X Y Z: PO} {f: X -> Y -> Z}
  {Hf: Proper (leq ==> leq ==> leq) f}: Proper (eqv ==> eqv ==> eqv) f.
Proof.
  rewrite /Proper/respectful.
  setoid_rewrite eqv_of_leq. 
  split; apply Hf; tauto.
Qed.

#[export] Instance body_eqv {X Y} {f: X -mon-> Y}: Proper (eqv ==> eqv) f := op_leq_eqv_1. 

Canonical Structure morphisms_po (X Y: PO) := kern_po _ (@body X Y). 


(** ** instances *)

Program Definition id {X: PO}: X-mon->X := {|body x := x|}.
Next Obligation. move=>x y xy. apply xy. Defined.
Program Definition comp {X Y Z: PO} (f: Y-mon->Z) (g: X-mon->Y): X-mon->Z := {|body x := f (g x)|}.
Next Obligation. move=>x y xy. apply f, g, xy. Defined.
Infix "°" := comp (at level 20).

Program Definition const {X Y: PO} (y: Y): X-mon->Y := {|body _ := y|}.
Next Obligation. move=>_ _ _. reflexivity. Defined.

Lemma compA {X Y Z T} (f: Z-mon->T) (g: Y-mon->Z) (h: X-mon->Y): f ° (g ° h) = (f ° g) ° h.
Proof. reflexivity. Qed.
Lemma compIx {X Y} (f: X-mon->Y): id ° f = f.
Proof. by case f. Qed.
Lemma compxI {X Y} (f: X-mon->Y): f ° id = f.
Proof. by case f. Qed.
Lemma compCx {X Y Z: PO} (f: X-mon->Y) (z: Z): const z ° f = const z.
Proof. by []. Qed.
Lemma compxC {X Y Z: PO} (f: Y-mon->Z) (y: Y): body (f ° @const X _ y) = const (f y).
Proof. by []. Qed.

(* TOTHINK: use CS inferrence just for this one? *)
Program Definition dualf {X Y: PO} (f: X -mon-> Y): dual X -mon-> dual Y := {| body := f |}.
Next Obligation. move=>x y xy. apply f, xy. Qed.

#[export] Instance comp_leq {X Y Z: PO}: Proper (leq ==> leq ==> leq) (@comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x=>/=. rewrite (gg' x). apply ff'. Qed.
#[export] Instance comp_eqv {X Y Z: PO}: Proper (eqv ==> eqv ==> eqv) (@comp X Y Z) := op_leq_eqv_2.

(** * theory *)

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
Context {X: PO}.

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

Lemma sup_closed_Proper P: sup_closed P -> Proper (eqv ==> eqv) P.
Proof.
  move=>H. suff E: Proper (eqv ==> leq) P.
   by move=>x y xy; apply: antisym; apply E=>//; symmetry. 
  move=>x y xy Px. apply (H (eq x)). by move=>?<-. 
  move: (is_sup_single x). apply Proper_is_sup=>//. by symmetry.
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
Context {X: PO}.
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
Definition image_id {X: Type} (P: X -> Prop): image Datatypes.id P ≡ P.
Proof. cbv. by firstorder subst. Qed.
Definition image_comp {X Y Z: Type} (f: Y -> Z) (g: X -> Y) (P: X -> Prop): image (fun x => f (g x)) P ≡ image f (image g P).
Proof. cbv. firstorder subst; eauto. Qed.
Lemma forall_image {X Y: Type} (f: X -> Y) (P: X -> Prop) (Q: Y -> Prop):
  image f P <= Q <-> forall x, P x -> Q (f x).
Proof.
  split=>H.
  - move=>x Px. apply H. by exists x.
  - move=>y [x [Px ->]]; auto. 
Qed.
Section s.
Context {X: Type} {Y: PO}.
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
Lemma dprod_sup {A} {X: A -> PO}
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
    }.
    rewrite -ha. apply Pf=>g Pg b.
    unfold h. case A_dec=>ab. destruct ab.
    -- apply az. by exists g.
    -- by apply Pf. 
Qed.


(** adjunctions *)
Section s.
  Context {X Y: PO}.
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

Lemma adjoint_id {X}: @adjunction X X Datatypes.id Datatypes.id.
Proof. by []. Qed.

Lemma adjoint_comp {X Y Z f g f' g'} {A: @adjunction X Y f g} {B: @adjunction Y Z f' g'}:
  adjunction (fun x => f' (f x)) (fun y => g (g' y)).
Proof. move=>x y/=. by rewrite 2!adj. Qed.

Lemma dual_adjunction `(A: adjunction): adjunction (g: dual Y -> dual X) (f: dual X -> dual Y).
Proof. rewrite /adjunction/= => y x. symmetry. by apply adj. Qed.

Lemma right_adjoint_inf `(A: adjunction) P y: is_inf P y -> is_inf (image g P) (g y).
Proof. apply (left_adjoint_sup (dual_adjunction A)). Qed. 

(** least (pre-)fixpoints of monotone functions *)
Section d.
 Context {X: PO}.
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
Set Implicit Arguments.  
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


(** * dCPOs *)

HB.mixin Record dCPO_of_PartialOrder X of PartialOrder X := {
    #[canonical=no] dsup: forall D: X -> Prop, directed D -> X;
    #[canonical=no] dsup_spec: forall D (DD: directed D), is_sup D (dsup D DD);
}.
HB.structure Definition dCPO := { X of dCPO_of_PartialOrder X & }.

Lemma leq_dsup {X: dCPO.type} (P: X -> Prop) D: forall y, P y -> y <= dsup P D.
Proof. apply leq_sup, dsup_spec. Qed.

Program Definition dprod_dCPO {A} (X: A -> dCPO.type) :=
  dCPO_of_PartialOrder.Build (forall a, X a) (fun F DF a => dsup (image (fun f => f a) F) _) _.
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

HB.mixin Record CPO_of_PartialOrder X of PartialOrder X := {
    #[canonical=no] csup: forall C: X -> Prop, chain C -> X;
    #[canonical=no] csup_spec: forall C (CC: chain C), is_sup C (csup C CC);
}.
HB.structure Definition CPO := { X of CPO_of_PartialOrder X & }.

Lemma leq_csup {X: CPO.type} (P: X -> Prop) C: forall y, P y -> y <= csup P C.
Proof. apply leq_sup, csup_spec. Qed.

Program Definition dprod_CPO {A} (X: A -> CPO.type) :=
  CPO_of_PartialOrder.Build (forall a, X a) (fun F CF a => csup (image (fun f => f a) F) _) _.
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
 #[local] HB.instance Definition _ := kern_PartialOrder X f.
 Program Definition kern_dCPO :=
   dCPO_of_PartialOrder.Build A (fun P D =>
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
 Context {X: PartialOrder.type}.
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
 HB.instance Definition Chain_PartialOrder := kern_PartialOrder _ elem.

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
 HB.instance Definition _ := Setoid_morphism_of_FUN.Build _ _ _ next_eqv.
 End d.
 
 (** when [f] is monotone (on [X]), so is [next] (on [Chain f])  *)
 Section d.
 Variable f: X -mon-> X.
 Lemma next_leq: Proper (leq ==> leq) (next f).
 Proof. by move =>???; apply f. Qed.
 HB.instance Definition _ := Setoid_morphism_of_FUN.Build _ _ _ (@op_leq_eqv_1 _ _ _ next_leq).
 HB.instance Definition _ := PartialOrder_of_Setoid_morphism.Build _ _ _ next_leq.

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
 
   
 (*   dCPO_of_PartialOrder.Build (Chain f) (fun P D => {| elem := dsup (fun c => exists Cf: C f c, P (chn Cf)) _ |}) _. *)
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
 Lemma choose (X: PartialOrder.type) (P: X -> Prop) (f: X -eqv-> X) y y':
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

 Context {C: PartialOrder.type}.
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
   }.
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

 Context {C: PartialOrder.type}.
 Implicit Types x y z: C.

 (** tower induction *)
 Variable next: C -mon-> C.
 Hypothesis tower: forall (P: C -> Prop), sup_closed P -> (forall x, P x -> P (next x)) -> forall x, P x.

 (** the function [next] must be extensive *)
 Lemma id_next: id ≦ next.
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
   apply: is_inf_eqv. apply H. apply is_least_fixpoint. by rewrite /cobicovered.
   rewrite E; clear.
   apply Csup with (C f)=>//. apply csup_spec. 
 Qed.
 
End b. 
End BourbakiWitt'. 


(** the dCPO of monotone functions *)
(* TODO: generic construction (via dprod_CPO) *)
Section s.
 Context {X: PartialOrder.type} {Y: dCPO.type}. 
 Program Definition mon_dCPO := kern_dCPO (f:=fun f: X -mon-> Y => f: X -> Y) (fun Q f D Qf => _) _.
 Next Obligation.
   have E: f ≡ dsup _ D. apply: is_sup_eqv. apply Qf. apply: dsup_spec. reflexivity.
   have I: Proper (leq ==> leq) f. {
     move=>x y xy. rewrite (E x) (E y).
     apply: is_sup_leq; try apply: dsup_spec. simpl.
     etransitivity. apply eqv_covered. apply image_comp. 
     etransitivity. 2: apply eqv_covered; symmetry; apply image_comp. 
     apply covered_image=>//g/=. by apply g.
   }.
   unshelve eexists. unshelve eexists. exact f. 
   constructor. constructor. apply op_leq_eqv_1. 
   constructor. constructor. exact I. 
 Defined.
(*
Program Definition mon_dsup (F: (X-mon->Y) -> Prop) (DF: directed F): X -> Y :=
  fun x => dsup (image (fun f: X-mon->Y => f x) F) _.
Next Obligation.
  move=>/=_ _ [g [G ->]] [h [H ->]].
  case: (DF _ _ G H)=>/=[i [I [gi hi]]].
  exists (i x). split. by exists i. split. apply gi. apply hi.
Qed.
Lemma mon_dsup_leq (F: (X-mon->Y) -> Prop) (DF: directed F): Proper (leq ==> leq) (mon_dsup DF).
Proof.
  move=>x y xy. apply: is_sup_leq; try apply dsup_spec.
  apply covered_image=>//f. by apply f.
Qed.
Program Definition mon_dsup_setoid (F: (X-mon->Y) -> Prop) (DF: directed F) :=
  Setoid_morphism_of_FUN.Build X Y (mon_dsup DF) _.
Next Obligation. apply @op_leq_eqv_1. apply mon_dsup_leq. Qed.
HB.instance Definition _ F DF := @mon_dsup_setoid F DF.
HB.instance Definition mon_dsup_partialorder (F: (X-mon->Y) -> Prop) (DF: directed F) :=
  PartialOrder_of_Setoid_morphism.Build X Y (mon_dsup DF) (mon_dsup_leq DF).
Program Definition mon_dCPO :=
  dCPO_of_PartialOrder.Build (X-mon->Y) (@mon_dsup) _. 
Next Obligation.
  move=>/=f. split=>H.
  - move=>g G. rewrite -H=>a. apply leq_dsup. by exists g.
  - move=>a. apply dsup_spec=>/=_ [g [G ->]]. by apply H. 
Qed.
 *)
 HB.instance Definition _ := mon_dCPO.
End s.

Module Pataraia. 

Section s.
 Context {C: dCPO.type}.

 (** the largest monotone and extensive function on [C] *)
 Program Definition h: C-mon->C := dsup (fun f => id ≦ f) _.
 Next Obligation.
   (* grrr: Program is unfolding things *)
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
   apply: is_inf_eqv. apply H. apply is_least_fixpoint. by rewrite /cobicovered.
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
