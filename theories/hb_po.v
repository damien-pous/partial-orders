From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Export hb_setoid.

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

(* fails if PO.type is defined with #[primitive] *)
Goal forall X: PO.type, forall x y: X, x ≡ y -> x <= y.
  intros. rewrite H.
Abort.

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

Section s.
  Variable X: PO.type.
  Fail Check same PO.type X (dual (dual X)). (* needs PO.type to be #[primitive] *)
  Fail Check same PO.type X (eta X).         (* sad but purpose of [eta] *)
  Check same PO.type (eta X) (dual (dual X)). (* point of [eta] *)
  Check same PO.type (eta X) (eta (dual (dual X))).
End s.


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
HB.mixin Record isMonotone (X Y: PO.type) f of setoid_morphism X Y f := {
    #[canonical=no] monotone: Proper (leq ==> leq) f
  }.
(* #[primitive] *)
HB.structure Definition po_morphism (X Y: PO.type) := { f of isMonotone X Y f & }.
Notation "X '-mon->' Y" := (po_morphism.type X Y) (at level 99, Y at level 200).
Existing Instance monotone.

HB.factory Record Fun_isMonotone (X Y: PO.type) (f: X -> Y) := {
    #[canonical=no] monotone: Proper (leq ==> leq) f
  }.
HB.builders Context X Y f (F : Fun_isMonotone X Y f).
  HB.instance Definition _ :=
    isExtensional.Build X Y f (@op_leq_eqv_1 _ _ _ monotone).
  HB.instance Definition _ :=
    isMonotone.Build X Y f monotone.
HB.end.

Section s.
  Context {X Y: PO.type}.
  Definition mk_mon (f: X -> Y) (Hf: Proper (leq ==> leq) f) := f.
  HB.instance Definition _ f Hf := Fun_isMonotone.Build X Y (@mk_mon f Hf) Hf.
End s.
Arguments mk_mon {_ _}. 

(** identity morphism *)
HB.instance Definition _ {X} :=
  isMonotone.Build X X types_id (fun _ _ H => H).
Notation po_id := (types_id: _ -mon-> _) (only parsing). 

(** composition of morphisms *)
Definition po_comp {X Y Z} (g: Y-mon->Z) (f: X-mon->Y) := 
  isMonotone.Build X Z (g ∘ f) _.
HB.instance Definition _ {X Y Z} f g := @po_comp X Y Z f g.
Definition comp {X Y Z} (g: Y-mon->Z) (f: X-mon->Y) := g ∘ f: X-mon->Z.
Infix "°" := comp. 

(** constant morphism *)
Program Definition po_const {X Y: PO.type} (y: Y) :=
  isMonotone.Build X Y (const y) _.
Next Obligation. by move=>/=_ _ _. Qed.
HB.instance Definition _ {X Y} y := @po_const X Y y.

(** dual morphism  *)
Program Definition po_dualf {X Y} (f: X -mon-> Y)
  := isMonotone.Build (dual X) (dual Y) (dualf f) _.
Next Obligation. move=>x y. apply f. Qed.
HB.instance Definition _ {X Y} f := @po_dualf X Y f.

HB.instance Definition _ {X Y} (f: X-mon->Y) :=
  isMonotone.Build (eta X) (eta Y) (etaf f) (@monotone X Y f).

Section s.
  (* Variables (X Y: Setoid.type) (f: X-eqv->Y). *)
  (* Check same (X-eqv->Y) f (dualf f). *)
  Variables (X Y: PO.type) (f: X-mon->Y) (f': dual X-mon->dual Y).
  Check same PO.type (eta X) (eta (dual (dual X))).
  Fail Check unify (X-mon->Y) (dual X-mon->dual Y). (* has to fail *)
  Fail Check unify (X-mon->Y) (dual (dual X)-mon->dual (dual Y)). (* sad *)
  Check unify (eta X-mon->eta Y) (dual (dual X)-mon->dual (dual Y)). (* good *)
  Check unify (eta X-mon->eta Y) (eta (dual (dual X))-mon->eta (dual (dual Y))). (* good *)
  Check same (X-mon->Y) f (dualf f). (* triché car ramené à [X-mon->Y] *)
  Check same (X-mon->Y) f (dualf (dualf f)).
  Check same (eta X-mon->eta Y) (etaf f) (etaf (dualf f)). (* triché aussi *)
  Check same (eta X-mon->eta Y) (etaf f) (etaf (dualf (dualf f))).
  Fail Check dualf f': X-mon->Y. (* dommage *)
  Fail Check dualf f': eta X-mon->eta Y. (* dommage *)
  Fail Check etaf (dualf f'): eta X-mon->eta Y. (* dommage *)
End s.


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

Section test.
  (* above [po_dprod] lemma is defined carefully, so that we get *)
  Check fun A (X: forall a: A , PO.type) => same Setoid.type (forall a, X a) (dual (forall a, dual (X a))).
  Check fun A (X: forall a: A , PO.type) => same PO.type (forall a, X a) (dual (forall a, dual (X a))).
  Check fun (X: Type) (Y: PO.type) =>
          same PO.type
            (X -> dual Y)
            (dual (X -> Y)).
End test.

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

Section test.
  (* [kern_po] should be defined carefully, and left transparent, so that we have:  *)
  Check fun X Y (Z: PO.type) (f: X -> Y) (g: Y -> Z) =>
          same PO.type
            (kernel (X:=kernel g) f)
            (kernel (g ∘ f)).
  Check fun A (X: PO.type) (f: A -> X) =>
          same PO.type
            (kernel (f: A -> dual X))
            (dual (kernel f)).
End test.

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

Section test.
  Check fun (X: PO.type) (P: X -> Prop) =>
          same PO.type
            (sig (P: dual X -> Prop))
            (dual (sig P)).
  Check fun (X: Setoid.type) (Y: PO.type) =>
          same PO.type
            (X -eqv-> dual Y)
            (dual (X -eqv-> Y)).
  Check fun (X Y: PO.type) =>
          same PO.type
            (eta X -mon-> eta Y)
            (dual (dual X) -mon-> dual (dual Y)).
End test.


(* TOHINK: useful as instances? *)
Lemma types_comp_leq {X Y Z}:
  Proper (@leq (Y-mon->Z) ==> leq ==> leq) (@types_comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x=>/=. rewrite (gg' x). apply: ff'. Qed.

Lemma types_comp_leq_eqv {X Y} {Z: PO.type}: Proper (@leq (Y-eqv->Z) ==> eqv ==> leq) (@types_comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x/=. rewrite (gg' x). apply: ff'. Qed.

Instance comp_leq {X Y Z: PO.type}: Proper (leq ==> leq ==> leq) (@comp X Y Z).
Proof. apply: types_comp_leq. Qed.



(* Check forall X: PO.type, forall f: hom X X, f ° f ≡ f ° f. *)
(* Fail Check forall f: hom Prop Prop, True. *)
(* Check forall f: Prop -mon-> Prop, f ° f ≡ f ° f. *)
(* Check forall f: Prop -mon-> Prop, f ° f <= f ° f. *)
(* Check forall f: Prop -mon-> Prop, f ° f <= id. *)
(* Fail Check forall f: Prop -mon-> Prop, id <= f ° f. *)
(* Check forall f: Prop -mon-> Prop, id <=[_-mon->_] f ° f. *)


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


Notation downward_closed := (Proper (leq ==> impl)). 
Notation upward_closed := (Proper (leq --> impl)). 

Section s.

Context {X: PO.type}.
Implicit Types x y z: X. 
Implicit Types P Q: X -> Prop.

(* TOTHINK: infer [is_sup/is_inf] using typeclasses / declare hints  *)
Definition is_sup P x := forall z, x <= z <-> forall y, P y -> y <= z.

Lemma geq_is_sup P x: is_sup P x -> forall z, (forall y, P y -> y <= z) -> x <= z.
Proof. by move=>H z Hz; apply H. Qed.

Lemma leq_is_sup P x: is_sup P x -> forall y, P y -> y <= x.
Proof. by move=>H y Py; apply H. Qed.

Lemma is_sup_alt P z: is_sup P z <-> (forall y, P y -> y <= z) /\ (forall z', (forall y, P y -> y <= z') -> z <= z').
Proof.
  split; intro H. by split; apply H.
  intro x. split. intros E y. by rewrite -E; apply H. apply H.
Qed.

Lemma max_is_sup P x: P x -> (forall y, P y -> y <= x) -> is_sup P x.
Proof. rewrite is_sup_alt=>Px Sx. split=>//z Sz. by apply: Sz. Qed.

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

Definition is_inf P x := forall z, z <= x <-> forall y, P y -> z <= y.

Lemma leq_is_inf P x: is_inf P x -> forall z, (forall y, P y -> z <= y) -> z <= x.
Proof. dual @geq_is_sup. Qed.
Lemma geq_is_inf P x: is_inf P x -> forall y, P y -> x <= y.
Proof. dual @leq_is_sup. Qed.
Lemma is_inf_alt P z: is_inf P z <-> (forall y, P y -> z <= y) /\ (forall z', (forall y, P y -> z' <= y) -> z' <= z).
Proof. dual @is_sup_alt. Qed.
Lemma min_is_inf P x: P x -> (forall y, P y -> x <= y) -> is_inf P x.
Proof. dual @max_is_sup. Qed.

Definition cocovered P Q := @covered (dual X) P Q.
Definition cobicovered P Q := @bicovered (dual X) P Q.

#[export] Instance PreOrder_cocovered: PreOrder cocovered := @PreOrder_covered (dual X).
#[export] Instance Equivalence_cobicovered: Equivalence cobicovered := @Equivalence_bicovered (dual X).
#[export] Instance PO_cocovered: PartialOrder cobicovered cocovered := @PO_covered (dual X). 
#[export] Instance leq_cocovered: subrelation leq cocovered.
Proof. exact: @leq_covered (dual X). Qed.
#[export] Instance eqv_cobicovered: subrelation eqv cobicovered.
Proof. exact: @eqv_bicovered (dual X). Qed.

Lemma is_inf_leq P p Q q: is_inf P p -> is_inf Q q -> cocovered P Q -> q<=p.
Proof. dual @is_sup_leq. Qed.
Lemma is_inf_eqv P p Q q: is_inf P p -> is_inf Q q -> cobicovered P Q -> p≡q.
Proof. dual @is_sup_eqv. Qed.
Lemma infU (P: X -> Prop) x y: is_inf P x -> is_inf P y -> x ≡ y.
Proof. dual @supU. Qed.
Lemma is_inf_single x: is_inf (eq x) x.
Proof. dual @is_sup_single. Qed.
#[export] Instance Proper_is_inf: Proper (cobicovered ==> eqv ==> eqv) is_inf.
Proof. dual @Proper_is_sup. Qed.

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

