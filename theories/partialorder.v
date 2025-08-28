From Stdlib Require Bool.
Require Export setoid.

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


(** ** classic partial orders with EM on [leq] *)

HB.mixin Record PO_isClassic X of PO X := {
    #[canonical=no] leq_classic: forall x y: X, x <= y \/ ~ x <= y;
}.
HB.structure Definition ClassicPO := { X of PO_isClassic X & }.


(** ** chains, where all pairs of elements are comparable *)

HB.mixin Record PO_isChain X of PO X := {
    #[canonical=no] leq_chain: forall x y: X, x <= y \/ y <= x;
}.
HB.structure Definition Chain := { X of PO_isChain X & }.


(** ** (linear/total) orders *)

HB.structure Definition Order := { X of Chain X & ClassicPO X }.

HB.factory Record PO_Total X of PO X := {
    #[canonical=no] total: forall x y: X, x <= y \/ y < x;
}.
HB.builders Context X of PO_Total X.
  Implicit Types x y: X.
  Lemma chain x y: x <= y  \/  y <= x.
  Proof. case: (total x y)=>[|[? ?]]; auto. Qed.
  HB.instance Definition _ := PO_isChain.Build X chain. 
  Lemma classic x y: x <= y  \/  ~ x <= y.
  Proof. case: (total x y)=>[|[? ?]]; auto. Qed.
  HB.instance Definition _ := PO_isClassic.Build X classic.
HB.end.

Section s.
Context {X: Order.type}.
Implicit Types x y: X.
Lemma leq_total x y: x <= y  \/  y < x.
Proof.
  case: (leq_classic x y); auto.
  case: (leq_chain x y); auto.
  by right; split.
Qed.
Lemma compare x y: x < y  \/  x ≡ y  \/  y < x.
Proof.
  case: (leq_total x y)=>xy;
  case: (leq_total y x)=>yx.
  - by right; left; apply: antisym. 
  - by left.
  - by right; right.
  - exfalso. move: xy yx. exact: lt_nlt. 
Qed.
End s.


(** ** decidable partial orders, where [leq] is decidable *)

#[primitive]
HB.mixin Record PO_isDecidable X of PO X := {
  #[canonical=no] leqb: X -> X -> bool;
  #[canonical=no] leq_dec: forall x y, reflect (x <= y) (leqb x y);
  }.
(** decidable partial orders are decidable setoids *)
HB.builders Context X of PO_isDecidable X.
  Lemma classic (x y: X): x <= y \/ ~ x <= y.
  Proof. case: (leq_dec x y). by left. by right. Qed.
  HB.instance Definition _ := PO_isClassic.Build X classic.
  Definition eqvb (x y: X) := leqb x y && leqb y x.
  Lemma eqv_dec x y: reflect (x ≡ y) (eqvb x y).
  Proof.
    apply: equivP. 2: by rewrite eqv_of_leq.
    apply: andPP; exact: leq_dec. 
  Qed.
  HB.instance Definition _ := Setoid_isDecidable.Build X _ eqv_dec.
HB.end.
HB.structure Definition DecidablePO := { X of PO_isDecidable X & }.
Infix "<=?" := leqb (at level 70). 

(** getting a decidable partial order directly from a setoid *)
HB.factory Record Setoid_isDecidablePO X of Setoid X := {
  #[canonical=no] leqb: X -> X -> bool;
  #[canonical=no] eqv_of_leqb: forall x y, x ≡ y <-> leqb x y && leqb y x;
  #[canonical=no] leq_trans: forall x y z, leqb x y -> leqb y z -> leqb x z;
}.
HB.builders Context X of Setoid_isDecidablePO X.
  Definition leq (x y: X): Prop := leqb x y.
  Lemma po_axm: po_axm leq.
  Proof.
    apply: mk_po_axm. split.
    - move=>x. by move: (eqv_refl x)=>/eqv_of_leqb/andP[_].
    - exact: leq_trans.
    - move=>x y. rewrite eqv_of_leqb. exact: Bool.andb_true_iff.
  Qed.
  HB.instance Definition _ := isPO.Build X po_axm.
  HB.instance Definition _ := PO_isDecidable.Build X _ (fun _ _ => idP).
HB.end.

(** getting a decidable partial order directly from a Type *)
HB.factory Record Type_isDecidablePO X := {
  #[canonical=no] leqb: X -> X -> bool;
  #[canonical=no] leq_refl: forall x, leqb x x;
  #[canonical=no] leq_trans: forall x y z, leqb x y -> leqb y z -> leqb x z;
}.
HB.builders Context X of Type_isDecidablePO X.
  Definition leq (x y: X): Prop := leqb x y.
  Lemma PreOrder_leq: PreOrder leq.
  Proof.
    split.
    - exact: leq_refl.
    - exact: leq_trans.
  Qed.
  HB.instance Definition _ := Type_isPO.Build X PreOrder_leq.
  HB.instance Definition _ := PO_isDecidable.Build X _ (fun _ _ => idP).
HB.end.

(** ** duality / eta expansion *)

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
 HB.instance Definition _ := isPO.Build (dual X) po_dual.
End dual.

Section dual_dec.
 Context {X: DecidablePO.type}.
 HB.instance Definition _ := PO_isDecidable.Build (eta X) leqb leq_dec.
 HB.instance Definition _ := PO_isDecidable.Build (dual X) (fun x y => leqb y x) (fun x y => leq_dec y x).
End dual_dec.


(** ** morphisms *)

(** helpers to deduce extensionality out of monotonicity *)
Lemma op_leq_eqv_1 {X Y: PO.type} {f: X -> Y} 
{Hf: Proper (leq ==> leq) f}: Proper (eqv ==> eqv) f.
Proof.
  rewrite /Proper/respectful.
  setoid_rewrite eqv_of_leq. 
  split; apply Hf; tauto.
Qed.
Lemma op_leq_eqv_1' {X Y: PO.type} {f: X -> Y} 
{Hf: Proper (leq --> leq) f}: Proper (eqv ==> eqv) f.
Proof. exact: (op_leq_eqv_1 (X:=dual X)). Qed.
Lemma op_leq_eqv_2 {X Y Z: PO.type} {f: X -> Y -> Z}
  {Hf: Proper (leq ==> leq ==> leq) f}: Proper (eqv ==> eqv ==> eqv) f.
Proof.
  rewrite /Proper/respectful.
  setoid_rewrite eqv_of_leq. 
  split; apply Hf; tauto.
Qed.
Lemma op_leq_eqv_2' {X Y Z: PO.type} {f: X -> Y -> Z}
  {Hf: Proper (leq --> leq ==> leq) f}: Proper (eqv ==> eqv ==> eqv) f.
Proof. exact: (op_leq_eqv_2 (X:=dual X)). Qed.
Lemma op_leq_eqv_2'' {X Y Z: PO.type} {f: X -> Y -> Z}
  {Hf: Proper (leq ==> leq --> leq) f}: Proper (eqv ==> eqv ==> eqv) f.
Proof. exact: (op_leq_eqv_2 (Y:=dual Y)). Qed.
Lemma op_leq_eqv_2''' {X Y Z: PO.type} {f: X -> Y -> Z}
  {Hf: Proper (leq --> leq --> leq) f}: Proper (eqv ==> eqv ==> eqv) f.
Proof. exact: (op_leq_eqv_2' (Y:=dual Y)). Qed.

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
Arguments monotone {_ _} _ [_ _]. 
Arguments po_morphism.sort [_ _] _ _/: simpl nomatch. 

Section s.
  Context {X Y: PO.type}.
  Definition mk_mon' (f: X -> Y) (Hf: Proper (leq ==> leq) f) := f.
  HB.instance Definition _ f Hf := isMonotone.Build X Y (@mk_mon' f Hf) Hf.
  Definition mk_mon (f: X -> Y) Hf := @mk_mon' f Hf: X-mon->Y.
End s.
Arguments mk_mon' {_ _} _ _ _/. 
Arguments mk_mon {_ _} _ _/.
Notation "'mfun' x .. y => p" := (mk_mon (fun x => .. (mk_mon (fun y => p) _) .. ) _)
  (at level 200, x binder, right associativity).

(** identity morphism *)
HB.instance Definition _ {X} :=
  isMonotone.Build X X types_id (fun _ _ H => H).
Notation po_id := (types_id: _ -mon-> _) (only parsing). 

(** composition of morphisms *)
HB.instance Definition _ {X Y Z} (f: X-mon->Y) (g: Y-mon->Z) := 
  isMonotone.Build X Z (g ∘ f) (fun x y xy => monotone g (monotone f xy)).
Definition po_comp {X Y Z} (g: Y-mon->Z) (f: X-mon->Y) := g ∘ f: X-mon->Z.
Infix "°" := po_comp. 

(** constant morphism *)
Program Definition po_const {X Y: PO.type} (y: Y) :=
  isMonotone.Build X Y (const y) _.
Next Obligation. by move=>/=_ _ _. Qed.
HB.instance Definition _ {X Y} y := @po_const X Y y.

(** dual morphism  *)
HB.instance Definition _ {X Y} (f: X-mon->Y) :=
  isMonotone.Build (dual X) (dual Y) (dualf f) (fun _ _ xy => monotone f xy).
HB.instance Definition _ {X Y: PO.type} (f: dual X-mon->dual Y) := 
  isMonotone.Build X Y (dualf' f) (fun x y xy => monotone f xy).
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

HB.structure Definition StrictPO :=
  { X of PO X & StrictSetoid X}.

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
HB.instance Definition _ (X: DecidableSetoid.type) := PO_isDecidable.Build (discrete X) eqvb eqv_dec.

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
HB.instance Definition _ (X: Type) := DecidablePO.copy (trivial X) (discrete (trivial X)).

(** in particular on the empty and unit type *)
HB.instance Definition _ := DiscretePO.copy False (discrete False).
HB.instance Definition _ := DiscretePO.copy unit (discrete unit).
HB.instance Definition _ := DecidablePO.copy False (discrete False).
HB.instance Definition _ := DecidablePO.copy unit (discrete unit).
HB.instance Definition _ (X: PO.type) := @DiscreteThusMonotone.Build False X empty_fun.

(** Booleans with [false <= true] *)
Program Definition po_bool := Setoid_isDecidablePO.Build bool implb _ _.
Next Obligation. by case:x; case:y. Qed.
Next Obligation. by destruct x; destruct y. Qed.
HB.instance Definition _ := po_bool.
Program Definition chain_bool := PO_isChain.Build bool _.
Next Obligation. case:x; case:y; cbv; tauto. Qed.
HB.instance Definition _ := chain_bool.

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

(** direct product *)
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
End s.
Arguments leq_prod [_ _] _ _/.

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
HB.instance Definition _ (A: Type) (X: ClassicPO.type) (f: A -> X) :=
  PO_isClassic.Build (kernel f) (fun _ _ => leq_classic _ _).
HB.instance Definition _ (A: Type) (X: Chain.type) (f: A -> X) :=
  PO_isChain.Build (kernel f) (fun _ _ => leq_chain _ _).
HB.saturate kernel. 
HB.instance Definition _ (A: Type) (X: DecidablePO.type) (f: A -> X) :=
  PO_isDecidable.Build (kernel f) (fun x y => f x <=? f y) (fun _ _ => leq_dec _ _).

(** sub partial orders as a special case *)
HB.instance Definition _ (X: PO.type) (P: X -> Prop) :=
  PO.copy (sig P) (kernel sval).
HB.instance Definition _ (X: ClassicPO.type) (P: X -> Prop) :=
  ClassicPO.copy (sig P) (kernel sval).
HB.instance Definition _ (X: Chain.type) (P: X -> Prop) :=
  Chain.copy (sig P) (kernel sval).
HB.saturate sig.
HB.instance Definition _ (X: DecidablePO.type) (P: X -> Prop) :=
  DecidablePO.copy (sig P) (kernel sval).
HB.instance Definition _ (X: PO.type) (P: X -> Prop) :=
  po_morphism.copy (@proj1_sig X P) (kernelf sval).

(** extensional functions as a special case *)
HB.instance Definition _ {X: Setoid.type} {Y: PO.type} :=
  PO.copy (X-eqv->Y) (kernel (@setoid_morphism.sort X Y)).

(** sets, ordered by inclusion, as a special case *)
HB.instance Definition _ {X: Setoid.type} := PO.on (set X).

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

Lemma le_lt_or_eqv {X: ClassicPO.type} (x y: X): x<=y <-> x<y \/ x≡y.
Proof.
  split. 2: move=>[|]; [exact: lt_le | exact: eqv_leq].
  case: (leq_classic y x)=>yx.
  - right. exact: antisym.
  - by left.
Qed.

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

Lemma image_adj' {X} {Y: Setoid.type} (f: X -> Y) (P: X -> Prop) (Q: Y -> Prop):
  image f P <= Q -> P <= Q ∘ f.
Proof. exact: forall_image'. Qed.
Lemma image_adj {X} {Y: Setoid.type} (f: X -> Y) (P: X -> Prop) (Q: set Y):
  image f P <= Q <-> P <= Q ∘ f.
Proof. exact: forall_image. Qed.
Lemma image_adj'' {X} {Y: Setoid.type} (f: X -> Y) (P: X -> Prop) (Q: Y -> Prop):
  P <= Q ∘ f -> image f P <= saturate Q.
Proof. rewrite image_adj=>->x/=. exact: in_image. Qed.


(** downward/upward closed subsets *)
Notation downward_closed := (Proper (leq ==> impl)). 
Notation upward_closed := (Proper (leq --> impl)). 

Section s.

Context {X: PO.type}.
Implicit Types x y z: X. 
Implicit Types P Q: X -> Prop.
Implicit Types S T: set X.

(** upward/downward closures of an element *)
Definition upset x := fun y => x <= y.
Definition downset x := fun y => y <= x.
Arguments upset _ _/.
Arguments downset _ _/.

HB.instance Definition _ x := isExtensional.Build _ _ (upset x) _.
Program Definition _downset x := isExtensional.Build _ _ (downset x) _.
Next Obligation. move=>y z e. by rewrite /downset e. Qed.
HB.instance Definition _ x := _downset x.

#[export] Instance upset_leq: Proper (leq --> leq) upset.
Proof. move=>x x' e y/=. by rewrite e. Qed.
#[export] Instance upset_eqv: Proper (eqv ==> eqv) upset := op_leq_eqv_1'.
#[export] Instance downset_leq: Proper (leq ==> leq) downset.
Proof. move=>x x' e y/=. by rewrite e. Qed.
#[export] Instance downset_eqv: Proper (eqv ==> eqv) downset := op_leq_eqv_1.

(** upward/downward closures of sets *)
Definition up_closure P x := exists y, P y /\ y <= x.
Definition down_closure P x := exists y, P y /\ x <= y.

Program Definition _up_closure P := isExtensional.Build  _ _ (up_closure P) _.
Next Obligation. move=>x x' E/=. rewrite /up_closure. by setoid_rewrite E. Qed.
HB.instance Definition _ P := _up_closure P.
Program Definition _down_closure P := isExtensional.Build  _ _ (down_closure P) _.
Next Obligation. move=>x x' E/=. rewrite /down_closure. by setoid_rewrite E. Qed.
HB.instance Definition _ P := _down_closure P.

(** lower/upper bounds of a subset *)
Definition lower_bound P x := forall y, P y -> x <= y.
Definition upper_bound P x := forall y, P y -> y <= x.

Lemma lower_boundE P x : lower_bound P x = (P <= upset x).
Proof. done. Qed.
Lemma upper_boundE P x : upper_bound P x = (P <= downset x).
Proof. done. Qed.

Program Definition _lower_bound P := isExtensional.Build _ _ (lower_bound P) _.
Next Obligation. move=>y z e. by rewrite lower_boundE e. Qed.
HB.instance Definition _ P := _lower_bound P.
Program Definition _upper_bound P := isExtensional.Build _ _ (upper_bound P) _.
Next Obligation. move=>y z e. by rewrite upper_boundE e. Qed.
HB.instance Definition _ P := _upper_bound P.

#[export] Instance lower_bound_leq_leq: Proper (leq --> leq --> leq) lower_bound.
Proof. move=>U V H x y xy LUx z Vz/=. rewrite xy. apply: LUx. exact/H. Qed.
#[export] Instance lower_bound_eqv_eqv: Proper (eqv ==> eqv ==> eqv) lower_bound := op_leq_eqv_2'''.
#[export] Instance lower_bound_leq: Proper (leq --> leq) lower_bound.
Proof. move=>U V H x. exact/lower_bound_leq_leq. Qed.
#[export] Instance lower_bound_eqv: Proper (eqv ==> eqv) lower_bound := op_leq_eqv_1'.

#[export] Instance upper_bound_leq_leq: Proper (leq --> leq ==> leq) upper_bound.
Proof. move=>U V H x y xy LUx z Vz/=. rewrite -xy. apply: LUx. exact/H. Qed.
#[export] Instance upper_bound_eqv_eqv: Proper (eqv ==> eqv ==> eqv) upper_bound := op_leq_eqv_2'.
#[export] Instance upper_bound_leq: Proper (leq --> leq) upper_bound.
Proof. move=>U V H x. exact/upper_bound_leq_leq. Qed.
#[export] Instance upper_bound_eqv: Proper (eqv ==> eqv) upper_bound := op_leq_eqv_1'.

(** least/greatest elements satisfying a predicate *)
Definition least P x := P x /\ lower_bound P x.
Definition greatest P x := P x /\ upper_bound P x.

Program Definition _least S := isExtensional.Build _ _ (least S) _.
Next Obligation. move=>x y e. by rewrite /least e. Qed.
HB.instance Definition _ S := _least S.

Program Definition _greatest S := isExtensional.Build _ _ (greatest S) _.
Next Obligation. move=>x y e. by rewrite /greatest e. Qed.
HB.instance Definition _ S := _greatest S.  

(** minimal/maximal elements satisfying a predicate
  (ie, without anyone below/above satisfying the predicate)
  we use definitions that avoid negations *)
Definition minimal P x := P x /\ forall y, P y -> y <= x -> x ≡ y.
Definition maximal P x := P x /\ forall y, P y -> x <= y -> x ≡ y.

Program Definition _minimal S := isExtensional.Build _ _ (minimal S) _.
Next Obligation. move=>x y e. rewrite /minimal. by setoid_rewrite e. Qed.
HB.instance Definition _ S := _minimal S.

Program Definition _maximal S := isExtensional.Build _ _ (maximal S) _.
Next Obligation. move=>x y e. rewrite /maximal. by setoid_rewrite e. Qed.
HB.instance Definition _ S := _maximal S.  

(** least upper bounds / greatest lower bounds (suprema / infima)  *)
Definition is_sup P x := forall y, x <= y <-> upper_bound P y.
Definition is_inf P x := forall y, y <= x <-> lower_bound P y.

Program Definition _is_sup P := isExtensional.Build _ _ (is_sup P) _.
Next Obligation. move=>y z e. rewrite /is_sup. by setoid_rewrite e. Qed.
HB.instance Definition _ P := _is_sup P.  
Program Definition _is_inf P := isExtensional.Build _ _ (is_inf P) _.
Next Obligation. move=>y z e. rewrite /is_inf. by setoid_rewrite e. Qed.
HB.instance Definition _ P := _is_inf P.  

(** predicates closed under suprema / infima *)
Definition sup_closed P := forall Q, Q <= P -> is_sup Q <= P.
Definition inf_closed P := forall Q, Q <= P -> is_inf Q <= P.


(** properties of the above definitions *)

Lemma upper_bound_empty x: upper_bound empty x ≡ True.
Proof. exact: forall_empty. Qed.

Lemma upper_bound_single x y: upper_bound (single x) y ≡ (x <= y).
Proof. split. by apply. by move=>H z <-. Qed.

Lemma upper_bound_pair x y z: upper_bound (pair x y) z ≡ (x <= z /\ y <= z).
Proof.
  split.
  - move=>H. by split; apply: H; [left|right].
  - by case=>xz yz t [<-|<-].
Qed.

Lemma upper_bound_image {A} {f: A -> X} (P: A -> Prop) z: upper_bound (image f P) z ≡ (forall a, P a -> f a <= z).
Proof. by rewrite upper_boundE image_adj. Qed.

Lemma greatest_leq P Q: P <= Q -> forall x y, greatest P x -> greatest Q y -> x <= y.
Proof. move=>PQ x y [Px _] [_ Hy]. apply: Hy. exact: PQ. Qed.

Lemma greatest_maximal P: greatest P <= maximal P.
Proof. move=>x [Px Hx]. split=>//y Py yx. apply: antisym=>//. by apply: Hx. Qed.

Lemma greatest_maximal_unique P x y: greatest P x -> maximal P y -> x ≡ y.
Proof. move=>[Px Hx] [Py Hy]. symmetry. apply: Hy=>//. exact/Hx. Qed.

Lemma greatest_unique P x y: greatest P x -> greatest P y -> x ≡ y.
Proof. move=>+/greatest_maximal. exact: greatest_maximal_unique. Qed.

Lemma is_sup_alt P: is_sup P ≡ least (upper_bound P).
Proof.
  split=>/=H. split=>/=. exact/H. rewrite lower_boundE. exact/eqv_geq.
  move=>b; split. move=><-. by apply H.
  move:b. by apply H. 
Qed.

Lemma greatest_is_sup: greatest <= is_sup.
Proof. move=>P x [Px Sx]. rewrite (is_sup_alt P _). split=>//z Sz. by apply: Sz. Qed.

Lemma sup_closed_greatest_is_sup P: sup_closed P -> greatest P ≡ is_sup P.
Proof.
  move=>HP x. split. exact: greatest_is_sup.
  move=>H. split. apply: HP. reflexivity. done.
  by apply H.
Qed.

(** covering relation *)
Definition covered: relation (X -> Prop) := fun P Q => P <= down_closure Q.
#[export] Instance PreOrder_covered: PreOrder covered.
Proof.
  constructor.
  - move=>P x Px/=; rewrite /down_closure; eauto.
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

(** directed sets (note that we consider the empty set as directed)  *)
Definition directed P :=
  forall x y, P x -> P y -> exists z, P z /\ x <= z /\ y <= z.
Lemma directed_empty: directed empty.
Proof. by []. Qed.

(** chains (note that we consider the empty set as a chain) *)
Definition chain P :=
  forall x y, P x -> P y -> x <= y \/ y <= x.
Lemma chain_empty: chain empty.
Proof. by []. Qed.

Lemma chain_directed P: chain P -> directed P.
Proof. move=>H x y Px Py; by case:(H _ _ Px Py); eauto. Qed.


(** dual versions *)
Definition cocovered: relation (X -> Prop) := fun P Q => P <= up_closure Q.
Definition cobicovered f g := cocovered f g /\ cocovered g f.
Definition codirected P :=
  forall x y, P x -> P y -> exists z, P z /\ z <= x /\ z <= y.
Definition cochain P :=
  forall x y, P x -> P y -> y <= x \/ x <= y.

End s.
Arguments upset {_} _ _/.
Arguments downset {_} _ _/.

Lemma chain_image {X Y: PO.type} (f: X-mon->Y) P (C: chain P): chain (image f P).
Proof.
   move=>/=_ _ [x [Px ->]] [y [Py ->]].
   case: (C _ _ Px Py); [left|right]; by apply f. 
Qed.

Lemma directed_image {X Y: PO.type} (f: X-mon->Y) P (D: directed P): directed (image f P).
Proof.
   move=>/=fx fy [x [Px Ex]] [y [Py Ey]].
   case: (D _ _ Px Py)=>/=[z [Pz [xz yz]]].
   exists (f z). split. by exists z. by rewrite Ex xz Ey yz.
Qed.

Instance covered_image {X: Type} {Y: PO.type}: Proper (leq ==> leq ==> covered) (@image X Y).
Proof.
  move=>f g fg P Q PQ. apply/image_adj=>x Px.
  exists (g x); split. apply: in_image. exact: PQ. exact: fg.
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

Lemma lower_bound_empty x: lower_bound empty x ≡ True.
Proof. exact: forall_empty. Qed.

Lemma lower_bound_single x y: lower_bound (single x) y ≡ (y <= x).
Proof. exact: (@upper_bound_single (dual X)). Qed.

Lemma lower_bound_pair x y z: lower_bound (pair x y) z ≡ (z <= x /\ z <= y).
Proof. exact: (@upper_bound_pair (dual X)). Qed.

Lemma lower_bound_image {A} {f: A -> X} (P: A -> Prop) z: lower_bound (image f P) z ≡ (forall a, P a -> z <= f a).
Proof. exact: (@upper_bound_image (dual X)). Qed.

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

#[export] Instance PreOrder_cocovered: PreOrder (@cocovered X) := @PreOrder_covered (dual X).
#[export] Instance Equivalence_cobicovered: Equivalence (@cobicovered X) := @Equivalence_bicovered (dual X).
#[export] Instance PO_cocovered: PartialOrder cobicovered cocovered := @PO_covered (dual X). 
#[export] Instance leq_cocovered: subrelation leq (@cocovered X) := @leq_covered (dual X). 
#[export] Instance eqv_cobicovered: subrelation eqv (@cobicovered X) := @eqv_bicovered (dual X).

Lemma chain_cochain P: chain P ≡ cochain P.
Proof. by apply: antisym=>H x y Px Py; rewrite or_comm; apply H. Qed.

Lemma codirected_empty: @codirected X empty.
Proof. dual @directed_empty. Qed.

Lemma cochain_empty: @cochain X empty.
Proof. dual @chain_empty. Qed.

Lemma cochain_codirected P: cochain P -> codirected P.
Proof. dual @chain_directed. Qed. 

End dual_props.

Lemma cochain_image {X Y: PO.type} (f: X-mon->Y) P (C: cochain P): cochain (image f P).
Proof. exact: (chain_image (dualf f)). Defined. (* defined to help with dualities *)
Lemma codirected_image {X Y: PO.type} (f: X-mon->Y) P (D: codirected P): codirected (image f P).
Proof. exact: (directed_image (dualf f)). Defined. (* defined to help with dualities *)

Instance cocovered_image {X: Type} {Y: PO.type}: Proper (leq --> leq ==> cocovered) (@image X Y).
Proof. exact: (@covered_image X (dual Y)). Qed.

Instance cobicovered_image {X: Type} {Y: PO.type}: Proper (eqv ==> eqv ==> cobicovered) (@image X Y).
Proof. exact: (@bicovered_image X (dual Y)). Qed.

Lemma saturate_bicovered {X: PO.type} (P: X -> Prop): bicovered (saturate P) P.
Proof.
  split=>x. move=>[y [Py E]]. exists y; split=>//. exact: eqv_leq.
  exists x; split=>//. by exists x.
Qed.
Lemma saturate_cobicovered {X: PO.type} (P: X -> Prop): cobicovered (saturate P) P.
Proof. exact: (@saturate_bicovered (dual X)). Qed.

Lemma image_id' {X: PO.type} (P: X -> Prop): bicovered (image types_id P) P.
Proof. exact: saturate_bicovered. Qed.
Lemma image_id'' {X: PO.type} (P: X -> Prop): cobicovered (image types_id P) P.
Proof. exact: saturate_cobicovered. Qed.

(** * sup preserving functions *)
Definition is_sup_preserving {X Y: PO.type} (f: X -> Y) :=
  forall Z z, is_sup Z z -> is_sup (image f Z) (f z).
Lemma is_sup_preserving_monotone {X Y: PO.type} (f: X -> Y):
  is_sup_preserving f -> Proper (leq ==> leq) f.
Proof.
  move=>H x y xy.
  set Z := pair x y.
  have /H/(_ (f y)) Zy: is_sup Z y. {
    rewrite /is_sup/Z=>z.
    rewrite upper_bound_pair. intuition. by transitivity y.
  }
  apply Zy=>//.
  apply: in_image. by left. 
Qed.

HB.mixin Record isSupPreserving (X Y: PO.type) (f: X -> Y) := {
  #[canonical=no] preserves_is_sup: is_sup_preserving f    
}.
HB.builders Context {X Y} f of isSupPreserving X Y f.
HB.instance Definition _ := isMonotone.Build _ _ f (is_sup_preserving_monotone preserves_is_sup).
HB.end.
HB.structure Definition sup_morphism X Y := {f of isSupPreserving X Y f}.
Notation "X '-sup->' Y" := (sup_morphism.type X Y) (at level 99, Y at level 200).

Instance Proper_is_sup {X}: Proper (bicovered ==> eqv ==> iff) (@is_sup X).
Proof.
  rewrite /is_sup=> P Q PQ x y xy.
  apply Proper_forall=>z. apply Proper_iff. by rewrite xy.
  have E: forall P Q, covered P Q -> (forall t, Q t -> t <= z) <= (forall t, P t -> t <= z).
   clear=>P Q PQ H t Pt. by case: (PQ _ Pt)=>s [? ->]; apply H. 
  split; apply E; apply PQ. 
Qed.

Lemma is_sup_preserving_id {X}: @is_sup_preserving X X types_id.
Proof. move=>Z z. by rewrite image_id'. Qed.
Lemma is_sup_preserving_comp {X Y Z: PO.type} (f: X->Y) (g: Y-eqv->Z):
  is_sup_preserving f -> is_sup_preserving g -> is_sup_preserving (g∘f).
Proof. move=>F G S s Ss/=. rewrite image_comp/=. by apply G, F. Qed.

HB.instance Definition _ X := isSupPreserving.Build X X types_id (@is_sup_preserving_id X).
HB.instance Definition _ X Y Z (f: X-sup->Y) (g: Y-sup->Z) := 
  isSupPreserving.Build X Z (g∘f) (is_sup_preserving_comp _ preserves_is_sup preserves_is_sup).

(** partial order of sup-preserving functions *)
HB.instance Definition _ {X Y: PO.type} :=
  PO.copy (X-sup->Y) (kernel (@sup_morphism.sort X Y)).
Instance sup_morphism_leq {X Y}: Proper (leq ==> leq ==> leq) (@sup_morphism.sort X Y).
Proof. move=>f g fg x y xy. rewrite xy. exact: fg. Qed.

(** * dually, inf preserving functions *)
Definition is_inf_preserving {X Y: PO.type} (f: X -> Y) :=
  forall Z z, is_inf Z z -> is_inf (image f Z) (f z).
Lemma is_inf_preserving_monotone {X Y: PO.type} (f: X -> Y):
  is_inf_preserving f -> Proper (leq ==> leq) f.
Proof.
  move=>H. apply/Proper_dual_leq.
  by dual @is_sup_preserving_monotone.
Qed.
  
HB.mixin Record isInfPreserving (X Y: PO.type) (f: X -> Y) := {
  #[canonical=no] preserves_is_inf: is_inf_preserving f    
}.
HB.builders Context {X Y} f of isInfPreserving X Y f.
HB.instance Definition _ := isMonotone.Build _ _ f (is_inf_preserving_monotone preserves_is_inf).
HB.end.
HB.structure Definition inf_morphism X Y := {f of isInfPreserving X Y f}.
Notation "X '-inf->' Y" := (inf_morphism.type X Y) (at level 99, Y at level 200).

(** partial order of inf-preserving functions *)
HB.instance Definition _ {X Y: PO.type} :=
  PO.copy (X-inf->Y) (kernel (@inf_morphism.sort X Y)).
Instance inf_morphism_leq {X Y}: Proper (leq ==> leq ==> leq) (@inf_morphism.sort X Y).
Proof. move=>f g fg x y xy. rewrite xy. exact: fg. Qed.

(** duality *)
HB.instance Definition _ X Y (f: X-sup->Y) :=
  isInfPreserving.Build (dual X) (dual Y) (dualf f) (@preserves_is_sup X Y f).
HB.instance Definition _ X Y (f: X-inf->Y) :=
  isSupPreserving.Build (dual X) (dual Y) (dualf f) (@preserves_is_inf X Y f).

Instance Proper_is_inf {X}: Proper (cobicovered ==> eqv ==> iff) (@is_inf X).
Proof. dual @Proper_is_sup. Qed.

Lemma is_inf_preserving_id {X}: @is_inf_preserving X X types_id.
Proof. dual @is_sup_preserving_id. Qed.
Lemma is_inf_preserving_comp {X Y Z: PO.type} (f: X->Y) (g: Y-eqv->Z):
  is_inf_preserving f -> is_inf_preserving g -> is_inf_preserving (g∘f).
Proof. exact (@is_sup_preserving_comp (dual X) (dual Y) (dual Z) (dualf f) (dualf g)). Qed.

HB.instance Definition _ X := isInfPreserving.Build X X types_id (@is_inf_preserving_id X).
HB.instance Definition _ X Y Z (f: X-inf->Y) (g: Y-inf->Z) := 
  isInfPreserving.Build X Z (g∘f) (is_inf_preserving_comp _ preserves_is_inf preserves_is_inf).
