From Stdlib Require Bool.
Require Export setoid.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

(** * partial orders *)

(** ** class *)

(** PO on top of a Setoid *)
Record po_axm {X: Setoid.type} (leq: relation X) := {
    (* for involutive duality: we split the components to avoid non primitive records,
       and we duplicate the third requirement *)
  Reflexive_leq_: Reflexive leq;
  Transitive_leq_: Transitive leq;
  eqv_of_leq_: forall x y, eqv x y <-> (leq x y /\ leq y x);
  eqv_of_geq_: forall x y, eqv x y <-> (leq y x /\ leq x y);
  }.
Lemma mk_po_axm {X: Setoid.type} (leq: relation X):
  PreOrder leq -> (forall x y, eqv x y <-> (leq x y /\ leq y x)) -> po_axm leq.
Proof.
  move=>P E. split=>//. apply P. by move=>x y; rewrite and_comm.
Qed.
#[primitive]
HB.mixin Record isPO X of Setoid X := {
    #[canonical=no] leq: relation X;
    #[canonical=no] PO_axm: po_axm leq;
}.
(* #[primitive] *)
HB.structure Definition PO := { X of isPO X & }.
Infix "<=" := leq (at level 70).
Notation "x <=[ X ] y" := (@leq X x y) (at level 70, only parsing).
Notation unify_pos X Y := (same PO.type X Y).
  
(** PO from scratch, with [eqv] derived from [leq] *)
HB.factory Record Type_isPO X := {
    #[canonical=no] leq: relation X;
    #[canonical=no] PreOrder_leq: PreOrder leq;
  }.
HB.builders Context X of Type_isPO X.
  Definition eqv (x y: X) := leq x y /\ leq y x.
  Lemma Equivalence_eqv: Equivalence eqv.
  Proof.
    move: PreOrder_leq. split.
    - by split.
    - by move=>??[]; split.
    - by move=>x y z[??][??]; split; transitivity y. 
  Qed.
  HB.instance Definition _ := isSetoid.Build X Equivalence_eqv.
  Lemma PO_axm: po_axm leq.
  Proof. apply: mk_po_axm=>//. exact: PreOrder_leq. Qed.
  HB.instance Definition _ := isPO.Build X PO_axm.
HB.end.

(** ** basic properties *)

Instance PreOrder_leq {X: PO.type}: @PreOrder X leq.
Proof. split; apply PO_axm. Qed.
Lemma eqv_of_leq {X: PO.type} (x y: X): x ≡ y <-> x <= y /\ y <= x. 
Proof. apply PO_axm. Qed.

Instance PartialOrder_eqv_leq {X: PO.type}: @PartialOrder X eqv _ leq _.
Proof. exact: eqv_of_leq. Qed.
Instance leq_rw {X: PO.type}: @RewriteRelation X leq := {}.

Lemma leq_refl {X: PO.type} (x: X): x <= x.
Proof. exact: reflexivity. Qed.
Arguments leq_refl {_ _}, {_}.
Lemma eqv_trans {X: PO.type} (x y z: X): x <= y -> y <= z -> x <= z.
Proof. exact: transitivity. Qed.
Lemma eq_eqv {X: PO.type} (x y: X): x = y -> x <= y.
Proof. by move=>->. Qed.

Hint Extern 0 (_ <= _) => exact: (eqv_refl _): core.


(** ** duality *)

Section dual.
 Context {X: PO.type}.
 HB.instance Definition _ := PO.on (eta X).
 Lemma po_dual: @po_axm (dual X) (flip (@leq X)).
 Proof.
  split. exact: (Reflexive_leq_ (@PO_axm X)).
  move=>???/=+?; exact: (Transitive_leq_ (@PO_axm X)).
  exact: (eqv_of_geq_ (@PO_axm X)).
  exact: (eqv_of_leq_ (@PO_axm X)).
 Defined.
 HB.instance Definition _po_on_dual := isPO.Build (dual X) po_dual.
End dual.


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
#[primitive]
HB.mixin Record isMonotone (X Y: PO.type) (f: X -> Y) := {
    #[canonical=no] monotone: Proper (leq ==> leq) f
  }.
(** monotone functions are always extensive *)
HB.builders Context X Y f of isMonotone X Y f.
  HB.instance Definition _ :=
    isExtensional.Build X Y f (@op_leq_eqv_1 _ _ _ monotone).
HB.end.
(** thanks to the above builder, [po_morphism] inherits from [setoid_morphim] *)  
HB.structure Definition po_morphism (X Y: PO.type) := { f of isMonotone X Y f }.
Notation "X '-mon->' Y" := (po_morphism.type X Y) (at level 99, Y at level 200).
Existing Instance monotone.

Section s.
  Context {X Y: PO.type}.
  Definition mk_mon (f: X -> Y) (Hf: Proper (leq ==> leq) f) := f.
  HB.instance Definition _ f Hf := isMonotone.Build X Y (@mk_mon f Hf) Hf.
End s.
Arguments mk_mon {_ _}. 

(** identity morphism *)
HB.instance Definition _ {X} :=
  isMonotone.Build X X types_id (fun _ _ H => H).
Notation po_id := (types_id: _ -mon-> _) (only parsing). 

(** composition of morphisms *)
HB.instance Definition _ {X Y Z} (f: X-mon->Y) (g: Y-mon->Z) := 
  isMonotone.Build X Z (g ∘ f) (fun x y xy => monotone _ _ (monotone x y xy)).
Definition po_comp {X Y Z} (g: Y-mon->Z) (f: X-mon->Y) := g ∘ f: X-mon->Z.
Infix "°" := po_comp. 

(** constant morphism *)
Program Definition po_const {X Y: PO.type} (y: Y) :=
  isMonotone.Build X Y (const y) _.
Next Obligation. by move=>/=_ _ _. Qed.
HB.instance Definition _ {X Y} y := @po_const X Y y.

(** dual morphism  *)
HB.instance Definition _ {X Y} (f: X-mon->Y) :=
  isMonotone.Build (dual X) (dual Y) (dualf f) (fun x y xy => @monotone _ _ f y x xy).
HB.instance Definition _ {X Y: PO.type} (f: dual X-mon->dual Y) := 
  isMonotone.Build X Y (dualf' f) (fun x y xy => @monotone _ _ f y x xy).
(* would be definitional if po_morphism were declared #[primitive] *)
Lemma dualfE {X Y}: forall f: X-mon->Y, f = dualf' (dualf f).
Proof. by case. Qed.
(** dualising all monotone functions from the current context *)
Ltac dualf :=
  match goal with
  | f: ?X -mon-> ?Y |- _ =>
      rewrite (dualfE f);
      change (X-mon->Y) with (types_id (X-mon->Y)) in f;
      dualf;
      unfold types_id in f
  | _ => idtac
  end.

(** eta expanded morphisms *)
HB.instance Definition _ {X Y} (f: X-mon->Y) := po_morphism.on (etaf f).
(* would be definitional if po_morphism were declared #[primitive] *)
Lemma etafE {X Y}: forall f: X -mon-> Y, f = etaf f.
Proof. by case. Qed.


(** ** strict partial orders, where [eqv=eq] *)

#[primitive]
HB.structure Definition StrictPO :=
  { X of isPO X & isStrictSetoid X}.

HB.factory Record isStrictPO X := {
    #[canonical=no] leq: relation X;
    #[canonical=no] PreOrder_leq: PreOrder leq;
    #[canonical=no] antisym: antisymmetric X leq;
  }.
HB.builders Context X of isStrictPO X.
  HB.instance Definition _ := strict_setoid X.
  Lemma PO_axm: po_axm leq.
  Proof.
    move: PreOrder_leq=>P.
    apply: mk_po_axm.
    move=>x y; split.
    by move=>H; destruct H.
    case; exact: antisym. 
  Qed.
  HB.instance Definition _ := isPO.Build X PO_axm.
HB.end.


(** ** discrete partial orders, where [leq=eqv] *)

#[primitive]
HB.mixin Record isDiscrete X of PO X := {
    #[canonical=no] leq_eqv: subrelation leq (@eqv X);
  }.
HB.structure Definition DiscretePO :=
  { X of isDiscrete X & }.

HB.factory Record Setoid_isDiscretePO X of Setoid X := {}.
HB.builders Context X of Setoid_isDiscretePO X.
  Lemma po_axm: po_axm (@eqv X). 
  Proof. apply: mk_po_axm. intuition. Qed.
  HB.instance Definition _ := isPO.Build X po_axm.
  HB.instance Definition _ := isDiscrete.Build X _.
HB.end.
Definition discrete (X: Type) := X.
HB.instance Definition _ (X: Setoid.type) := Setoid.on (discrete X).
HB.instance Definition _ (X: Setoid.type) := Setoid_isDiscretePO.Build (discrete X).

HB.factory Record DiscreteThusMonotone (X: DiscretePO.type) (Y: PO.type) f of setoid_morphism X Y f := {}.
HB.builders Context X Y f of DiscreteThusMonotone X Y f.
  Lemma monotone: Proper (leq ==> leq) f.
  Proof. by move=>x y /leq_eqv/=->. Qed.
  HB.instance Definition _ := isMonotone.Build X Y f monotone. 
HB.end.
Definition discretemon {X: DiscretePO.type} {Y: PO.type} (f: X -eqv-> Y) := f: X -> Y.
HB.instance Definition _ {X: DiscretePO.type} {Y: PO.type} (f: X -eqv-> Y) :=
  setoid_morphism.on (@discretemon X Y f).
HB.instance Definition _ {X: DiscretePO.type} {Y: PO.type} (f: X -eqv-> Y) :=
  DiscreteThusMonotone.Build X Y (@discretemon X Y f).


(** ** instances *)

(** trivial partial order on trivial setoids *)
HB.instance Definition _ (X: Type) := PO.copy (trivial X) (discrete (trivial X)).

(** in particular on the empty and unit type *)
HB.instance Definition _ := DiscretePO.copy False (discrete False).
HB.instance Definition _ := DiscretePO.copy unit (discrete unit).
HB.instance Definition _ (X: PO.type) := @DiscreteThusMonotone.Build False X empty_fun.

(** Booleans with [false <= true] *)
Lemma PreOrder_bool: PreOrder Bool.le.
Proof. split. by case. by move=>[][][]. Qed.
Lemma antisym_bool: antisymmetric bool Bool.le.
Proof. by case; case. Qed.
HB.instance Definition _ := isStrictPO.Build bool PreOrder_bool antisym_bool.

(** propositions ordered by implication *)
Lemma po_Prop: po_axm impl. 
Proof. apply: mk_po_axm=>//. split; cbv; tauto. Qed.
HB.instance Definition _ := isPO.Build Prop po_Prop.

(** (dependent) function space, ordered pointwise *)
Section dprod.
 Variables (A: Type) (X: A -> PO.type).
 Definition leq_dprod: relation (forall a, X a) := fun f g => forall a, f a <= g a.
 Lemma po_dprod: po_axm leq_dprod.
 Proof.
   split. 
   - move=>f a. exact: (Reflexive_leq_ (@PO_axm (X a))).
   - move=>f g h fg gh a. exact: (Transitive_leq_ (@PO_axm (X a)) _ _ _ (fg a) (gh a)).
   - move=>f g. apply: forall_iff_and=>a. exact: (eqv_of_leq_ (@PO_axm (X a))).
   - move=>f g. apply: forall_iff_and=>a. exact: (eqv_of_geq_ (@PO_axm (X a))).
 Defined.
 HB.instance Definition _ := isPO.Build (forall a, X a) po_dprod.
End dprod.
Arguments leq_dprod {_ _} _ _/. 
HB.instance Definition _ {A} {X: A -> PO.type} (a: A) :=
  isMonotone.Build (forall a, X a) (X a) (app a) (fun f g fg => fg a).

(** products, sums, option *)
Section s.
 Variables X Y: PO.type.

 (** direct product *)
 Definition leq_prod: relation (X*Y) :=
   fun p q => fst p <= fst q /\ snd p <= snd q.
 Lemma po_prod: po_axm leq_prod.
 Proof.
   apply: mk_po_axm.
   split. split=>//.
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
 HB.instance Definition _ := Setoid.on (lex_prod X Y).
 Definition leq_lex_prod: relation (lex_prod X Y) :=
   fun p q => fst p <= fst q /\ (fst q <= fst p -> snd p <= snd q).
 Lemma po_lex_prod: po_axm leq_lex_prod.
 Proof.
   unfold leq_lex_prod.
   apply: mk_po_axm.
   - split=>//.
     move=>[x x'][y y'][z z']/=[xy xy'][yz yz']. split.
     by transitivity y.
     move=>zx. transitivity y'.
     apply: xy'. by transitivity z. 
     apply: yz'. by transitivity x.
   - move=>[??][??]. cbn. rewrite 2!eqv_of_leq. intuition.
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
   apply: mk_po_axm. split.
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
 HB.instance Definition _ := Setoid.on (sequential_sum X Y).
 Definition leq_sequential_sum: relation (sequential_sum X Y) :=
   fun p q => match p,q with
           | inl x,inl y | inr x,inr y => x<=y
           | inl _,inr _ => True
           | _,_ => False
           end.
 Lemma po_sequential_sum: po_axm leq_sequential_sum.
 Proof.
   apply: mk_po_axm. split.
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
   apply: mk_po_axm. split.
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
   rewrite /leq_kern. split.
   - by move=>?; exact: (Reflexive_leq_ (@PO_axm X)).
   - by move=>???; exact: (Transitive_leq_ (@PO_axm X)).
   - cbn=>??. exact: (eqv_of_leq_ (@PO_axm X)).
   - cbn=>??. exact: (eqv_of_geq_ (@PO_axm X)).
 Defined.
 HB.instance Definition _ := isPO.Build (kernel f) kern_po.  
 HB.instance Definition _ := isMonotone.Build (kernel f) X (kernelf f) (fun _ _ xy => xy). 
End kernel.
Arguments leq_kern [_ _] _ _ _/.

(** sub partial orders as a special case *)
HB.instance Definition _ (X: PO.type) (P: X -> Prop) :=
  PO.copy (sig P) (kernel sval).
HB.instance Definition _ (X: PO.type) (P: X -> Prop) :=
  po_morphism.copy (@proj1_sig X P) (kernelf sval).

(** extensional functions as a special case *)
HB.instance Definition _ {X: Setoid.type} {Y: PO.type} :=
  PO.copy (X-eqv->Y) (kernel (@setoid_morphism.sort X Y)).

(** monotone functions as a special case *)
HB.instance Definition _ {X Y: PO.type} :=
  PO.copy (X-mon->Y) (kernel (@po_morphism.sort X Y)).
Definition pobody {X Y} := kernelf (@po_morphism.sort X Y).
Instance po_morphism_leq {X Y}: Proper (leq ==> leq ==> leq) (@po_morphism.sort X Y).
Proof. move=>f g fg x y xy. rewrite xy. exact: fg. Qed.


(* TOHINK: useful as instances? *)
Lemma types_comp_leq {X Y Z}:
  Proper (@leq (Y-mon->Z) ==> leq ==> leq) (@types_comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x=>/=. rewrite (gg' x). apply: ff'. Qed.
Lemma types_comp_leq_eqv {X Y} {Z: PO.type}: Proper (@leq (Y-eqv->Z) ==> eqv ==> leq) (@types_comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x/=. rewrite (gg' x). apply: ff'. Qed.

Instance po_comp_leq {X Y Z: PO.type}: Proper (leq ==> leq ==> leq) (@po_comp X Y Z).
Proof. apply: types_comp_leq. Qed.
Instance po_comp_eqv {X Y Z: PO.type}: Proper (eqv ==> eqv ==> eqv) (@po_comp X Y Z) := op_leq_eqv_2.


Instance const_leq {X} {Y: PO.type}:
  Proper (leq ==> leq) (@const Y X).
Proof. move=>/=y y' yy x. apply yy. Qed.
Instance const_leq' {X} {Y: PO.type}:
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

Lemma antisym' x y: x <= y -> (x <= y -> y <= x) -> x ≡ y. (* TODO: more general? *)
Proof. intros. apply antisym; tauto. Qed.

Lemma leq_from_above x y: (forall z, y <= z -> x <= z) -> x <= y.
Proof. by auto. Qed.
Lemma from_above x y: (forall z, x <= z <-> y <= z) -> x ≡ y.
Proof. intro E. by apply antisym; apply E. Qed.

Lemma lt_le x y: x < y -> x <= y.
Proof. exact: proj1. Qed.
Lemma lt_nle x y: x < y -> ~y <= x.
Proof. exact: proj2. Qed.
Lemma lt_nlt x y: x < y -> ~y < x.
Proof. move=>xy yx. exact: (lt_nle xy (lt_le yx)). Qed.
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

Lemma Proper_eqv_leq {X: Setoid.type} {Y: PO.type}:
  Proper (@eqv X ==> @eqv Y) ≡ Proper (eqv ==> leq).
Proof.
  move=>f; split=>H x x' e.
  - apply: eqv_leq. by rewrite e.
  - apply: antisym; apply: H=>//.
Qed.

Lemma Proper_eqv_eqv_leq {X Y: Setoid.type} {Z: PO.type}:
  Proper (@eqv X ==> @eqv Y ==> @eqv Z) ≡ Proper (eqv ==> eqv ==> leq).
Proof.
  move=>f; split=>H x x' i y y' j.
  - apply: eqv_leq. by rewrite  i j.
  - apply: antisym; apply: H=>//.
Qed.

Lemma Proper_dual_leq {X Y: PO.type}:
  Proper (@leq (dual X) ==> @leq (dual Y)) ≡ Proper (@leq X ==> @leq Y).
Proof. apply: antisym=>f H x y xy; exact: H. Qed.

(* TODO: choose (above or below) *)

Lemma Proper_flip A B (R: relation A) (S: relation B): Proper (flip R ==> S) ≡ Proper (R ==> flip S).
Proof. move=>f. apply: antisym=>Hf x y xy; by apply Hf. Qed.
Lemma Proper_half X Y: Proper (@eqv X ==> @leq Y) <= Proper (@eqv X ==> @eqv Y).
Proof. move=>f H x y xy. apply: antisym; apply H=>//. Qed.

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

(** downward/upward closed subsets *)
Notation downward_closed := (Proper (leq ==> impl)). 
Notation upward_closed := (Proper (leq --> impl)). 

(** lower/upper bounds of a subset *)
(* using notations rather than definition to avoid having to unfold every now and then *)
Notation lower_bound P := (fun x => forall y, P y -> x <= y) (only parsing).
Notation upper_bound P := (fun x => forall y, P y -> y <= x) (only parsing).

Section s.

Context {X: PO.type}.
Implicit Types x y z: X. 
Implicit Types P Q: X -> Prop.

(** least/greatest elements satisfying a predicate *)
Definition least P x := P x /\ lower_bound P x.
Definition greatest P x := P x /\ upper_bound P x.

(** minimal/maximal elements satisfying a predicate
  (ie, without anyone below/above satisfying the predicate)
  we use definitions that avoid negations *)
Definition minimal P x := P x /\ forall y, P y -> y <= x -> x ≡ y.
Definition maximal P x := P x /\ forall y, P y -> x <= y -> x ≡ y.

(** least upper bounds / greatest lower bounds  *)
Definition is_sup P x := forall z, x <= z <-> upper_bound P z.
Definition is_inf P x := forall z, z <= x <-> lower_bound P z.

(** predicates closed under suprema/infima *)
Definition sup_closed P := forall Q, Q <= P -> forall z, is_sup Q z -> P z.
Definition inf_closed P := forall Q, Q <= P -> forall z, is_inf Q z -> P z.

Lemma greatest_leq P Q: P <= Q -> forall x y, greatest P x -> greatest Q y -> x <= y.
Proof. move=>PQ x y [Px _] [_ Hy]. apply: Hy. exact: PQ. Qed.

Lemma greatest_maximal P x: greatest P x -> maximal P x.
Proof. move=>[Px Hx]. split=>//y Py yx. apply: antisym=>//. by apply: Hx. Qed.

Lemma greatest_maximal_unique P x y: greatest P x -> maximal P y -> x ≡ y.
Proof. move=>[Px Hx] [Py Hy]. symmetry; auto. Qed.

Lemma greatest_unique P x y: greatest P x -> greatest P y -> x ≡ y.
Proof. move=>+/greatest_maximal. exact: greatest_maximal_unique. Qed.

Lemma is_sup_alt P z: is_sup P z <-> least (upper_bound P) z.
Proof.
  split; intro H. split; by apply H. 
  intro x. split. intros E y. by rewrite -E; apply H. apply H.
Qed.

Lemma greatest_is_sup P x: greatest P x -> is_sup P x.
Proof. move=>[Px Sx]. rewrite is_sup_alt. split=>//z Sz. by apply: Sz. Qed.

Lemma sup_closed_greatest_is_sup P: sup_closed P -> forall x, greatest P x <-> is_sup P x.
Proof.
  move=>HP x. split. exact: greatest_is_sup.
  move=>H. split. apply: HP. reflexivity. done.
  by apply H.
Qed.

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
#[export] Instance eqv_bicovered: subrelation eqv bicovered.
Proof. move=>P Q. by rewrite eqv_of_leq; move=>[??]; split; apply leq_covered. Qed.

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

End s.


Definition image {X Y: Type} (f: X -> Y) (P: X -> Prop) y := exists x, P x /\ y = f x.

Lemma image_id {X: Type} (P: X -> Prop): image types_id P ≡ P.
Proof. cbv. by firstorder subst. Qed.
Lemma image_comp {X Y Z: Type} (f: Y -> Z) (g: X -> Y) (P: X -> Prop): image (f ∘ g) P ≡ image f (image g P).
Proof. cbv. firstorder subst; eauto. Qed.
Lemma image_empty {X Y: Type} (f: X -> Y): image f empty ≡ empty.
Proof. cbv. by firstorder. Qed.
Lemma image_pair {X Y: Type} (f: X -> Y) (x x': X): image f (pair x x') ≡ pair (f x) (f x').
Proof. cbv. by firstorder subst; auto. Qed.

Lemma in_image {X Y} (f: X -> Y) (P: X -> Prop) x: P x -> image f P (f x).
Proof. by exists x. Qed.
Hint Resolve in_image: core. 

(* TODO: check usages and possibly unfold LHS *)
Lemma forall_image {X Y: Type} (f: X -> Y) (P: X -> Prop) (Q: Y -> Prop):
  image f P <= Q <-> forall x, P x -> Q (f x).
Proof.
  split=>H.
  - move=>x Px. apply: H. by exists x.
  - move=>y [x [Px ->]]; auto. 
Qed.

Lemma chain_image {X Y: PO.type} (f: X-mon->Y) P (C: chain P): chain (image f P).
Proof.
   move=>/=_ _ [x [Px ->]] [y [Py ->]].
   case: (C _ _ Px Py); [left|right]; by apply f. 
Qed.

Lemma directed_image {X Y: PO.type} (f: X-mon->Y) P (D: directed P): directed (image f P).
Proof.
   move=>/=_ _ [x [Px ->]] [y [Py ->]].
   case: (D _ _ Px Py)=>/=[z [Pz [xz yz]]].
   exists (f z). split. by exists z. by split; apply f. 
Qed.

Instance covered_image {X: Type} {Y: PO.type}: Proper (leq ==> leq ==> covered) (@image X Y).
Proof.
  move=>f g fg P Q PQ. apply forall_image=>x Px.
  exists (g x); split. exists x; split=>//. by apply: PQ. by apply: fg.
Qed.  

Instance bicovered_image {X: Type} {Y: PO.type}: Proper (eqv ==> eqv ==> bicovered) (@image X Y).
Proof.
  move=>f g fg P Q PQ. split; apply: covered_image;
  by [apply: eqv_leq | apply: eqv_geq ].
Qed.  

Section dual_props.
Context {X: PO.type}.
Implicit Types x y z: X. 
Implicit Types P Q: X -> Prop.

Lemma leq_from_below x y: (forall z, z <= x -> z <= y) -> x <= y.
Proof. dual @leq_from_above. Qed.
Lemma from_below x y: (forall z, z <= x <-> z <= y) -> x ≡ y.
Proof. dual @from_above. Qed.

Lemma least_leq P Q: Q <= P -> forall x y, least P x -> least Q y -> x <= y.
Proof. move=>PQ x y Hx Hy. dual @greatest_leq; eassumption. Qed.

Lemma least_minimal P x: least P x -> minimal P x.
Proof. dual @greatest_maximal. Qed.

Lemma least_minimal_unique P x y: least P x -> minimal P y -> x ≡ y.
Proof. dual @greatest_maximal_unique. Qed.

Lemma least_unique P x y: least P x -> least P y -> x ≡ y.
Proof. dual @greatest_unique.  Qed.

Lemma is_inf_alt P z: is_inf P z <-> greatest (lower_bound P) z.
Proof. dual @is_sup_alt. Qed.
Lemma least_is_inf P x: least P x -> is_inf P x.
Proof. dual @greatest_is_sup. Qed.
Lemma inf_closed_least_is_inf P: inf_closed P -> forall x, least P x <-> is_inf P x.
Proof. dual @sup_closed_greatest_is_sup. Qed.


Definition cocovered P Q := @covered (dual X) P Q.
Definition cobicovered P Q := @bicovered (dual X) P Q.

#[export] Instance PreOrder_cocovered: PreOrder cocovered := @PreOrder_covered (dual X).
#[export] Instance Equivalence_cobicovered: Equivalence cobicovered := @Equivalence_bicovered (dual X).
#[export] Instance PO_cocovered: PartialOrder cobicovered cocovered := @PO_covered (dual X). 
#[export] Instance leq_cocovered: subrelation leq cocovered.
Proof. exact: @leq_covered (dual X). Qed.
#[export] Instance eqv_cobicovered: subrelation eqv cobicovered.
Proof. exact: @eqv_bicovered (dual X). Qed.

Definition codirected P :=
  forall x y, P x -> P y -> exists z, P z /\ z <= x /\ z <= y.

Definition cochain P :=
  forall x y, P x -> P y -> y <= x \/ x <= y.

Lemma chain_cochain P: chain P ≡ cochain P.
Proof. by apply: antisym=>H x y Px Py; rewrite or_comm; apply H. Qed.

Lemma codirected_empty: codirected empty.
Proof. dual @directed_empty. Qed.

Lemma cochain_empty: cochain empty.
Proof. dual @chain_empty. Qed.

Lemma cochain_codirected P: cochain P -> codirected P.
Proof. dual @chain_directed. Qed. 

End dual_props.

Lemma cochain_image {X Y: PO.type} (f: X-mon->Y) P (C: cochain P): cochain (image f P).
Proof. exact: (chain_image (dualf f)). Qed.
Lemma codirected_image {X Y: PO.type} (f: X-mon->Y) P (D: codirected P): codirected (image f P).
Proof. exact: (directed_image (dualf f)). Qed.

Instance cocovered_image {X: Type} {Y: PO.type}: Proper (leq --> leq ==> cocovered) (@image X Y).
Proof. exact: (@covered_image X (dual Y)). Qed.

Instance cobicovered_image {X: Type} {Y: PO.type}: Proper (eqv ==> eqv ==> cobicovered) (@image X Y).
Proof. exact: (@bicovered_image X (dual Y)). Qed.

