From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Export hb_setoid.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

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

HB.mixin Record isPO' X := {
    #[canonical=no] leq: relation X;
    #[canonical=no] PreOrder_leq: PreOrder leq;
  }.
HB.builders Context X of isPO' X.
  Definition eqv (x y: X) := leq x y /\ leq y x.
  Lemma Equivalence_eqv: Equivalence eqv.
  Proof. split. Admitted.  
  HB.instance Definition _ := isSetoid.Build X Equivalence_eqv.
  Lemma PO_axm: po_axm leq.
  Proof. split. apply PreOrder_leq. reflexivity. Qed.
  HB.instance Definition _ := isPO.Build X PO_axm.
HB.end.

(* those two projections need to be Defined in order kernel composition to behave well *)
#[export] Instance PreOrder_leq {X: PO.type}: @PreOrder X leq.
Proof. apply PO_axm. Defined.
Lemma eqv_of_leq {X: PO.type} (x y: X): x ≡ y <-> x <= y /\ y <= x. 
Proof. apply PO_axm. Defined.

(** testing that two partial orders are definitionally equal *)
Notation unify_pos X Y := (unify (X: PO.type) (Y: PO.type)).


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
(** inheritance: po morphisms are setoid morphisms *)
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
  isMonotone.Build X Z (f ∘ g) _.
Next Obligation. move=>x y xy. by do 2apply monotone. Qed. 
HB.instance Definition _ {X Y Z} f g := @po_comp X Y Z f g.

(** constant morphism *)
Program Definition po_const {X Y: PO.type} (y: Y) :=
  isMonotone.Build X Y (const y) _.
Next Obligation. move=>/=_ _ _. apply PreOrder_leq. Qed.
HB.instance Definition _ {X Y} y := @po_const X Y y.


(** ** immediate properties *)

#[export] Existing Instance monotone.
#[export] Instance PartialOrder_eqv_leq {X: PO.type}: @PartialOrder X eqv _ leq _.
Proof. intros x y. apply eqv_of_leq. Qed.
#[export] Instance leq_rw {X: PO.type}: @RewriteRelation X leq := {}.

Lemma leq_refl {X: PO.type} (x: X): x <= x.
Proof. reflexivity. Qed.


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
HB.instance Definition _ (X: Type) :=
  PO.copy (trivial X) (discrete (trivial X)).

(** trivial partial order on the unit type *)
HB.instance Definition _ :=
  PO.copy unit (discrete unit).

(** Booleans with [false ≦ true] *)
Lemma po_bool: po_axm Bool.le.
Proof.
  split. split. by case. move=>[][][]//=.
  case; case=>//=; intuition discriminate.
Qed.
HB.instance Definition _ := isPO.Build bool po_bool.

(** propositions ordered by implication *)
Lemma po_Prop: po_axm impl. 
Proof. split=>//. split; cbv; tauto. Qed.
HB.instance Definition _ := isPO.Build Prop po_Prop.

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

(** products, sums, option *)
Section s.
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
End s. 
Arguments leq_prod [_ _] _ _/.
Arguments leq_lex_prod [_ _] _ _/.
Arguments leq_parallel_sum [_ _] _ _/.
Arguments leq_sequential_sum [_ _] _ _/.
Arguments leq_option [_] _ _/.
  
(** constructing a partial order via a function into another partial order *)
Section kernel.
 Variables (A: Type) (X: PO.type) (f: A -> X).
 Definition leq_kern: relation (kernel f) := fun x y => f x <= f y.
 Lemma kern_po: po_axm leq_kern.
 Proof.
   split.
   - rewrite /leq_kern. constructor.
     -- by move=>?; reflexivity.
     -- by move=>?????; etransitivity; eauto.
   - cbn=>??. apply eqv_of_leq.
 Defined.
 HB.instance Definition _ := isPO.Build (kernel f) kern_po.  
 HB.instance Definition _ := isMonotone.Build (kernel f) X (kernelf f) (fun _ _ xy => xy). 
End kernel.
Arguments leq_kern [_ _] _ _ _/.
(* [kern_po] should be defined carefully, and left transparent, so that we have:  *)
(* Check fun (X: PO.type) (f g: X -> X) => *)
(*         unify_pos *)
(*           (kernel (X:=kernel g) f) *)
(*           (kernel (types_comp g f)). *)

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
(** notation to help typechecking morphisms comparisons *)
Infix "≦" := (@leq (_ -mon-> _)) (at level 70, only parsing). 

(* TOHINK: useful as instances? *)
Lemma types_comp_leq {X Y Z}:
  Proper (@leq (Y-mon->Z) ==> leq ==> leq) (@types_comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x=>/=. rewrite (gg' x). apply: ff'. Qed.
Lemma types_comp_leq_eqv {X Y} {Z: PO.type}: Proper (@leq (Y-eqv->Z) ==> eqv ==> leq) (@types_comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x/=. rewrite (gg' x). apply: ff'. Qed.

#[export] Instance const_leq {X} {Y: PO.type}:
  Proper (leq ==> leq) (@const Y X).
Proof. move=>/=y y' yy x. apply yy. Qed.
#[export] Instance const_leq' {X} {Y: PO.type}:
  Proper (leq ==> @leq (X-mon->Y)) const := const_leq.


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
Proof. move=>P Q H x Px. exists x; split=>//. by apply: H. Qed.
#[export] Instance eqv_covered: subrelation eqv bicovered.
Proof. move=>P Q. by rewrite eqv_of_leq; move=>[??]; split; apply leq_covered. Qed.

(* TOTHINK: infer [is_sup] using typeclasses? *)
Definition is_sup P x := forall z, x <= z <-> forall y, P y -> y <= z.

Lemma is_sup_alt P z: is_sup P z <-> (forall y, P y -> y <= z) /\ (forall z', (forall y, P y -> y <= z') -> z <= z').
Proof.
  split; intro H. by split; apply H.
  intro x. split. intros E y. by rewrite -E; apply H. apply H.
Qed.

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
  intros y Ty. apply: TPQ=>//.
  apply: HP. 2: apply Px.
  by apply Tx. 
Qed.

Lemma sup_closed_leq (f: X -mon-> X): sup_closed (fun x => x <= f x).
Proof.
  intros T HT x Tx. apply Tx=>y Ty. 
  transitivity (f y). by apply: HT.
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
  - by apply H; apply: sc_inj.
  - elim: Px=>//Q QP IH y Hy. by apply Hy, IH. 
Qed.

(** greateast (post-)fixpoints of monotone functions,
    essentially Knaster-Tarski, also known as Lambek lemma in category theory *)
Definition is_gfp (f: X -> X) := is_sup (fun x => x <= f x). 

Lemma is_gfp_alt (f: X -mon-> X) (z: X): is_gfp f z <-> z <= f z /\ forall y, y <= f y -> y <= z.
Proof.    
  rewrite /is_gfp is_sup_alt. split; move=>[H H']; split=>//. 2: firstorder.
  apply H'=>y Y. rewrite Y. by apply f, H.
Qed.

Proposition gfp_fixpoint (f: X -mon-> X) x: is_gfp f x -> f x ≡ x.
Proof.
  move=>H. symmetry; apply: antisym'.
  apply H=>y Hy. rewrite Hy. apply f. by apply H.
  move=>P. apply H=>//. by apply f.
Qed.

Lemma is_gfp_leq (f g: X -mon-> X): f <= g -> forall x y, is_gfp f x -> is_gfp g y -> x <= y.
Proof.
  intros fg x y Hx Hy. apply Hy=>//.
  rewrite -(fg _). by rewrite (gfp_fixpoint _ Hx).
Qed.

#[export] Instance is_gfp_eqv: Proper (eqv ==> eqv ==> eqv) is_gfp.
Proof.
  intros f g fg. apply: Proper_is_sup.
  split=>x Hx; exists x; split=>//. by rewrite -(fg x). by rewrite (fg x).
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
Lemma is_inf_alt P z: is_inf P z <-> (forall y, P y -> z <= y) /\ (forall z', (forall y, P y -> z' <= y) -> z' <= z).
Proof. dual @is_sup_alt. Qed.
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
Lemma is_lfp_alt (f: X -mon-> X) (z: X): is_lfp f z <-> f z <= z /\ forall y, f y <= y -> z <= y.
Proof. apply (is_gfp_alt (dualf f)). Qed.  
Proposition lfp_fixpoint (f: X -mon-> X) x: is_lfp f x -> f x ≡ x.
Proof. apply (gfp_fixpoint (dualf f)). Qed.
#[export] Instance is_lfp_eqv: Proper (eqv ==> eqv ==> eqv) is_lfp.
Proof. dual @is_gfp_eqv. Qed.
Lemma is_lfp_leq (f g: X -mon-> X): f <= g -> forall x y, is_lfp f x -> is_lfp g y -> x <= y.
Proof. intros fg x y Hx Hy. by apply (@is_gfp_leq _ (dualf g) (dualf f)). Qed.

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
Definition image_comp {X Y Z: Type} (f: Y -> Z) (g: X -> Y) (P: X -> Prop): image (f ∘ g) P ≡ image f (image g P).
Proof. cbv. firstorder subst; eauto. Qed.
Lemma in_image {X Y} (f: X -> Y) (P: X -> Prop) x: P x -> image f P (f x).
Proof. by exists x. Qed.
#[export] Hint Resolve in_image: core. 
Lemma forall_image {X Y: Type} (f: X -> Y) (P: X -> Prop) (Q: Y -> Prop):
  image f P <= Q <-> forall x, P x -> Q (f x).
Proof.
  split=>H.
  - move=>x Px. apply: H. by exists x.
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
  exists (g x); split. exists x; split=>//. by apply: PQ. by apply: fg.
Qed.  
End s.

(** sups can be computed pointwise in function spaces *)
Lemma dprod_sup {A} {X: A -> PO.type} (P: (forall a, X a)->Prop) (f: forall a, X a):
  (forall a, is_sup (image (fun h => h a) P) (f a)) -> is_sup P f.
Proof.
  move=>H g; split=>fg.
  - move=>h Ph. rewrite -fg=>a. apply H=>//. by exists h.
  - move=>a. apply H=>_ [h [Ph ->]]. by apply: fg. 
Qed.
(** actually they *must* be computed pointwise, but not clear we can prove it without using decidability of equality on [A] *)
Lemma dprod_sup' {A} {X: A -> PO.type}
      (A_dec: forall a b: A, {a=b} + {a<>b})
      (P: (forall a, X a)->Prop) (f: forall a, X a):
  is_sup P f -> forall a, is_sup (image (fun h => h a) P) (f a).
Proof.
  move=>Pf a. split=>az.
  - move=>_ [b [Pb ->]]. rewrite -az. by apply: (leq_is_sup Pf).
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
    rewrite -ha. apply: (proj2 (Pf h))=>g Pg b.
    unfold h. case A_dec=>ab. destruct ab.
    -- apply az. by exists g.
    -- by apply: (leq_is_sup Pf). 
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
