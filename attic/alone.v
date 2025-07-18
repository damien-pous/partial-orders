Require Import Setoid Morphisms Basics.
Require Import ssreflect ssrfun ssrbool .
Require Eqdep_dec Classical.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.

Definition comp {X Y Z} (f: Y -> Z) (g: X -> Y): X -> Z := fun x => f (g x).
Arguments comp {_ _ _} _ _ _/. 
Infix "°" := comp (at level 20).
Definition const {X Y} y: X -> Y := fun _ => y. 
Arguments const {_ _} _ _/.

Lemma compA {X Y Z T} (f: Z->T) (g: Y->Z) (h: X->Y): f ° (g ° h) = (f ° g) ° h.
Proof. by []. Qed.
Lemma compIx {X Y} (f: X->Y): id ° f = f.
Proof. by []. Qed.
Lemma compxI {X Y} (f: X->Y): f ° id = f.
Proof. by []. Qed.
Lemma compCx {X Y Z} (f: X->Y) (z: Z): const z ° f = const z.
Proof. by []. Qed.
Lemma compxC {X Y Z} (f: Y->Z) (y: Y): f ° @const X _ y = const (f y).
Proof. by []. Qed.

Definition empty {X}: X -> Prop := fun _ => False. 
Definition pair {X} (x y: X): X -> Prop := fun z => z=x \/ z=y. 

Notation "a &&& b" := (if a then b else false) (at level 60): bool_scope. 
Notation "a ||| b" := (if a then true else b) (at level 60): bool_scope. 
Notation "a ==> b" := (if a then b else true): bool_scope.


(** * setoids *)

(** ** class *)

Module Setoid.

Record mixin X := from_type {
    eqv: relation X;
    Equivalence_eqv: Equivalence eqv;
}.
Structure type := pack {
    sort:> Type;
    #[canonical=no] mix: mixin sort;
}.
Definition build X eq eqE := pack (@from_type X eq eqE). 
Arguments build: clear implicits. 

Structure morphism (X Y: type) := build_morphism {
    body:> X -> Y;
    #[canonical=no] body_eqv: Proper (eqv (mix X) ==> eqv (mix Y)) body;
}.
Arguments build_morphism {_ _}. 

Canonical Structure id {X: type}: morphism X X :=
  build_morphism Datatypes.id _.
Program Canonical Structure comp {X Y Z: type} (f: morphism Y Z) (g: morphism X Y): morphism X Z :=
  build_morphism (comp f g) _. 
Next Obligation. move=>x y xy. apply f, g, xy. Qed.
Program Canonical Structure const {X Y: type} (y: Y): morphism X Y :=
  build_morphism (const y) _.
Next Obligation. move=>/=_ _ _. apply Equivalence_eqv. Qed.

End Setoid.
Notation Setoid := Setoid.type. 
#[reversible] Coercion Setoid.sort: Setoid >-> Sortclass.
#[reversible] Coercion Setoid.body: Setoid.morphism >-> Funclass.
Notation "X '-eqv->' Y" := (Setoid.morphism X Y) (at level 99, Y at level 200).
Canonical Setoid.id.
Canonical Setoid.comp.
Canonical Setoid.const.
Definition eqv {X: Setoid} := Setoid.eqv (Setoid.mix X).
#[export] Instance Equivalence_eqv {X: Setoid}: @Equivalence X eqv := Setoid.Equivalence_eqv (Setoid.mix X).
#[export] Instance body_eqv {X Y} {f: X-eqv->Y}: Proper (eqv ==> eqv) f := Setoid.body_eqv f.
Definition setoid_on T (S: Setoid) (_: T -> S) := S.
Notation Setoid_on T := (@setoid_on T _ (fun x => x)).
Infix "≡" := eqv (at level 70).
Infix "≡[ X ]" := (@eqv X) (at level 70, only parsing).
#[export] Hint Extern 0 => reflexivity: core.

(** ** instances *)

Definition eq_setoid X := Setoid.build X eq eq_equivalence.

Canonical Structure unit_setoid := Eval hnf in eq_setoid unit.
Canonical Structure bool_setoid := Eval hnf in eq_setoid bool.
Canonical Structure nat_setoid := Eval hnf in eq_setoid nat.

(* Program Canonical Structure irrelevant_setoid (P: Prop) := *)
(*   Eval hnf in Setoid.build P (fun _ _ => True) _. *)
(* Next Obligation. by constructor. Qed. *)

Canonical Structure Prop_setoid := Eval hnf in Setoid.build Prop iff _.

Program Canonical Structure prod_setoid (X Y: Setoid) :=
  Eval hnf in Setoid.build (X*Y) (fun p q => fst p ≡ fst q /\ snd p ≡ snd q) _.
Next Obligation.
  constructor=>//.
  by move=>??[??]; split; symmetry; assumption.
  by move=>???[??][]; split; etransitivity; eassumption.
Qed.

Program Canonical Structure sum_setoid (X Y: Setoid) :=
  Eval hnf in Setoid.build (X+Y) (fun p q => match p,q with inl p,inl q | inr p,inr q => p ≡ q | _,_ => False end) _.
Next Obligation. constructor=>//; intuition discriminate. Qed.
  
(* TODO: lists *)

Program Canonical Structure dprod_setoid A (X: A -> Setoid) :=
  Eval hnf in Setoid.build (forall a, X a) (fun f g => forall a, f a ≡ g a) _.
Next Obligation.
  constructor.
  - by move=>??. 
  - by move=>????; symmetry. 
  - by move=>??????; etransitivity; eauto.
Qed.

Program Definition kern_setoid A (X: Setoid) (f: A -> X) :=
  Setoid.build A (fun a b => f a ≡ f b) _.
Next Obligation.
  constructor.
  - by move=>//=. 
  - by move=>???; symmetry.
  - by move=>?????; etransitivity; eauto.
Defined.
(* we are lucky here... *)
Check fun A B (X: Setoid) (f: B -> X) (g: A -> B) => eq_refl: kern_setoid (kern_setoid X f) g = kern_setoid X (f ° g).

Canonical Structure sig_setoid (X: Setoid) (P: X -> Prop) :=
  Eval hnf in kern_setoid X (@proj1_sig X P).

Canonical Structure setoid_morphisms_setoid (X Y: Setoid) :=
  Eval hnf in kern_setoid _ (@Setoid.body X Y).
(* Notation eqv_setoids := (@eqv (setoid_morphisms_setoid _ _)).  *)
(* Infix "≡[-eqv->]" := (eqv_setoids) (at level 70). *)


Definition dual (X: Type) := X.
Canonical Structure dual_setoid (X: Setoid) :=
  (* just a clone *)
  Eval hnf in Setoid.build (dual X) eqv Equivalence_eqv.

Program Canonical Structure dual_setoid_morphism {X Y: Setoid} (f: X -eqv-> Y): dual X -eqv-> dual Y :=
  Setoid.build_morphism f body_eqv.

(* most general lemma *)
Lemma comp_eqv {X Y Z}: Proper (@eqv (Y-eqv->Z) ==> eqv ==> eqv) (@comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x=>/=. rewrite (gg' x). apply ff'. Qed.
(* but only this restriction makes it possible to use [setoid_rewrite] *)
(* #[export] Instance setoid_comp_eqv {X Y Z: Setoid}: Proper (meqv ==> meqv ==> meqv) (@Setoid.comp X Y Z) := comp_eqv. *)

Check fun f: nat -eqv-> nat => f ° f. 
Check fun f: nat -eqv-> nat => f ° id ° f. 

(* Goal forall X: Setoid, forall f g h: X -eqv-> X, f ⩧ g -> f ° g ⩧ h. *)
(* Proof. *)
(*   intros * H. *)
(*   rewrite H -H. cbn.  *)
(* Abort.  *)

#[export] Instance const_eqv {X} {Y: Setoid}: Proper (eqv ==> eqv) (@const X Y).
Proof. move=>/=y y' yy' _/=. apply yy'. Qed.
#[export] Instance setoid_const_eqv {X} {Y: Setoid}: Proper (eqv ==> eqv) (@Setoid.const X Y) := const_eqv.

Goal forall X, forall h: X-eqv->X, forall x y: X, x ≡ y -> const x ≡ h.
Proof. intros * H. rewrite H -H. Abort. 
Goal forall X, forall h: X-eqv->X, forall x y: X, x ≡ y -> Setoid.const x ≡ h.
Proof. intros * H. rewrite H -H. Abort. 


Check (bool * (unit -> dual nat) * sig (fun b: bool=> b=true)  (* * True *))%type: Setoid. 
Check (nat -> nat -> Prop): Setoid. 
Check (nat -eqv-> nat -eqv-> Prop): Setoid. 


(** * partial orders *)

(** ** class *)

Module PO.
Record mixin X (M: Setoid.mixin X) := from_setoid {
    leq: relation X;
    PreOrder_leq: PreOrder leq;
    eqv_of_leq: forall x y, Setoid.eqv M x y <-> (leq x y /\ leq y x);
  }.
Structure type := pack {
    sort:> Type;
    #[canonical=no] setoid_mix: Setoid.mixin sort;
    #[canonical=no] mix: mixin setoid_mix;
}.
Canonical Structure to_Setoid (X: type) := Setoid.pack (setoid_mix X).
#[reversible] Coercion to_Setoid: type >-> Setoid.
Definition build (X: Setoid) :=
  (* fun leq H H' => @pack _ (Setoid.mix X) (@from_setoid _ (Setoid.mix X) leq H H').  *)
  let '@Setoid.pack T M := X return
                             forall leq: relation X,
                               PreOrder leq ->
                               (forall x y, Setoid.eqv (Setoid.mix X) x y <-> (leq x y /\ leq y x)) -> type in
  fun leq H H' => @pack T M (@from_setoid T M leq H H').
Arguments build [_].

(* unused (and should not be used? unless we systematically declare the resulting Setoid as canonical?) *)
Program Definition build_from_type (X: Type) (leq: relation X) (H: PreOrder leq): type :=
  let M := @Setoid.from_type X (fun x y => leq x y /\ leq y x) _ in
  @pack X M (from_setoid M H _). 
Next Obligation.
  constructor; repeat intro.
  - by []. 
  - tauto.
  - split; transitivity y; tauto.
Qed.
Arguments build_from_type: clear implicits.

Program Definition dual_mixin X M (N: @mixin X M): @mixin (dual X) M :=
  @from_setoid (dual X) M (flip (leq N)) _ _.
Next Obligation. apply flip_PreOrder, N. Qed.
Next Obligation. rewrite (eqv_of_leq N). tauto. Qed.

Structure morphism (X Y: type) := build_morphism {
    body:> X -> Y;
    #[canonical=no] body_leq: Proper (leq (mix X) ==> leq (mix Y)) body;
                                   }.
Arguments build_morphism {_ _}. 
Program Definition to_Setoid_morphism {X Y} (f: morphism X Y) :=
  Setoid.build_morphism f _.
Next Obligation. move=>x y. rewrite 2!eqv_of_leq=>xy. split; apply f; apply xy. Qed.

Canonical Structure id {X: type}: morphism X X :=
  build_morphism Datatypes.id _.
Program Canonical Structure comp {X Y Z: type} (f: morphism Y Z) (g: morphism X Y): morphism X Z :=
  build_morphism (comp f g) _. 
Next Obligation. move=>x y xy. apply f, g, xy. Defined.
Program Canonical Structure const {X Y: type} (y: Y): morphism X Y :=
  build_morphism (const y) _.
Next Obligation. move=>/=_ _ _. apply PreOrder_leq. Defined.

End PO.
Notation PO := PO.type.
Canonical PO.to_Setoid.
Canonical PO.to_Setoid_morphism.
Canonical PO.id.
Canonical PO.comp.
Canonical PO.const.
#[reversible] Coercion PO.to_Setoid: PO >-> Setoid.
#[reversible] Coercion PO.sort: PO >-> Sortclass.
#[reversible] Coercion PO.to_Setoid_morphism: PO.morphism >-> Setoid.morphism.
#[reversible] Coercion PO.body: PO.morphism >-> Funclass.
Notation "X '-mon->' Y" := (PO.morphism X Y) (at level 99, Y at level 200).
Definition leq {X: PO} := PO.leq (PO.mix X).
#[export] Instance PreOrder_leq {X: PO}: @PreOrder X leq := PO.PreOrder_leq (PO.mix X).
Definition eqv_of_leq {X: PO}: forall x y, x ≡ y <-> (leq x y /\ leq y x) := PO.eqv_of_leq (PO.mix X).
#[export] Instance body_leq {X Y} {f: X-mon->Y}: Proper (leq ==> leq) f := PO.body_leq f.
Definition po_on T (S: PO) (_: T -> S) := S.
Notation PO_on T := (@po_on T _ (fun x => x)).
Infix "<=" := leq (at level 70).
Infix "<=[ X ]" := (@leq X) (at level 70, only parsing).
Definition lt {X: PO} (x y: X) := x<=y /\ ~y<=x.
Infix "<" := lt (at level 70).
Infix "<[ X ]" := (@lt X) (at level 70, only parsing).

(** ** basic properties *)

Section s.
 Context {X: PO}.
 Implicit Types x y: X.
 #[export] Instance PartialOrder_eqv_leq: PartialOrder (A:=X) eqv leq.
 Proof. move=> x y. apply eqv_of_leq. Qed.
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
 #[export] Instance Transitive_lt: Transitive (@lt X).
 Proof. move=>x y z [xy _]. by apply lelt_lt. Qed.
End s.

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

(* #[export] Instance body_eqv' {X Y} {f: X -mon-> Y}: Proper (eqv ==> eqv) f := _.  *)


(** ** instances *)

Program Definition discrete_po (X: Setoid) := @PO.build X eqv _ _.
Next Obligation. fold (x ≡ y). by intuition symmetry. Qed.

Canonical Structure unit_po := Eval hnf in discrete_po unit.

(* this one makes [prod_po] fail below, can't see why... *)
(* Canonical Structure irrelevant_po (P: Prop) := Eval hnf in discrete_po (Setoid_on P). *)

Program Canonical Structure bool_po: PO := Eval hnf in PO.build Bool.le _ _.
Admit Obligations.

Program Canonical Structure nat_po: PO := Eval hnf in PO.build Peano.le _ _.
Admit Obligations.

Program Canonical Structure Prop_po: PO := Eval hnf in PO.build impl _ _.
Next Obligation. split; cbv; tauto. Qed.

Program Canonical Structure prod_po (X Y: PO): PO :=
  Eval hnf in PO.build (fun p q: X*Y => fst p <= fst q /\ snd p <= snd q) _ _.
Next Obligation.
  constructor=>//.
  by move=>???[??][]; split; etransitivity; eassumption.
Qed.
Next Obligation.
  rewrite 2!eqv_of_leq. tauto. 
Qed.

Definition lex_prod := prod.
Canonical Structure lex_prod_setoid (X Y: Setoid) :=
  (* a clone of [prod_setoid] *)
  Setoid.build (lex_prod X Y) (fun p q => fst p ≡ fst q /\ snd p ≡ snd q) Equivalence_eqv.
Program Canonical Structure lex_prod_po (X Y: PO): PO :=
  Eval hnf in
  PO.build (fun p q: lex_prod X Y => fst p <= fst q /\ (fst q <= fst q -> snd p <= snd q)) _ _.
Next Obligation.
  constructor=>//.
  move=>[x x'][y y'][z z']/=.
  intuition solve [transitivity y; auto|transitivity y'; auto].
Qed.
Next Obligation.
  rewrite 2!eqv_of_leq. intuition.
Qed.
  
(* TODO: parallel and sequential sums, lists *)

Program Canonical Structure dprod_po A (X: A -> PO): PO :=
  Eval hnf in PO.build (fun f g: forall a, X a => forall a, f a <= g a) _ _.
Next Obligation.
  constructor.
  - by move=>??. 
  - by move=>??????; etransitivity; eauto.
Qed.
Next Obligation.
  setoid_rewrite eqv_of_leq. firstorder. 
Qed.

Program Definition kern_po A (X: PO) (f: A -> X): PO :=
  @PO.build (kern_setoid _ f) (fun a b: A => f a <= f b) _ _.
Next Obligation.
  constructor.
  - by move=>//=. 
  - by move=>?????; etransitivity; eauto.
Defined.
Next Obligation.
  apply eqv_of_leq.
Defined.
(* lucky here too *)
Check fun A B (X: PO) (f: B -> X) (g: A -> B) => eq_refl: kern_po (kern_po X f) g = kern_po X (f ° g).

Canonical Structure sig_po (X: PO) (P: X -> Prop): PO := Eval hnf in kern_po X (@proj1_sig X P).

Canonical Structure setoid_morphisms_po X (Y: PO): PO := Eval hnf in kern_po _ (@Setoid.body X Y). 
Canonical Structure po_morphisms_setoid X Y: Setoid := Eval hnf in kern_setoid _ (@PO.body X Y). 
Canonical Structure po_morphisms_po X Y: PO := Eval hnf in kern_po _ (@PO.body X Y). 

(* Notation leq_setoids := (@leq (setoid_morphisms_po _ _)).  *)
(* Notation eqv_pos := (@eqv (po_morphisms_setoid _ _)).  *)
(* Notation leq_pos := (@leq (po_morphisms_po _ _)).  *)
(* Infix "<=[-eqv->]" := (leq_setoids) (at level 70). *)
(* Infix "≡[-mon->]" := (eqv_pos) (at level 70). *)
(* Infix "<=[-mon->]" := (leq_pos) (at level 70). *)

Program Canonical Structure dual_po (X: PO): PO :=
  Eval hnf in
  PO.build (flip leq: relation (dual X)) _ _.
Next Obligation. rewrite eqv_of_leq. tauto. Qed.

Program Canonical Structure dual_po_morphism {X Y: PO} (f: X -mon-> Y): dual X -mon-> dual Y := PO.build_morphism f _.
Next Obligation. move=>x y xy. apply f, xy. Qed.


Goal forall X: PO, forall x y: X, x <= y -> x <= y.
Proof. intros * ->. Abort.
Goal forall X: PO, forall x y: X, x ≡ y -> x <= y.
Proof. intros * ->. Abort. 
Goal forall X: PO, forall x y: nat -> X, x <= y -> x <= y.
Proof. intros * ->. Abort.
Goal forall X: PO, forall x y: nat -> X, x ≡ y -> x <= y.
Proof. intros * ->. Abort. 
Goal forall x y: nat -> Prop, x <= y -> x <= y.
Proof. intros * ->. Abort.
Goal forall x y: nat -> Prop, x ≡ y -> x <= y.
Proof. intros * ->. Abort. 

Lemma comp_leq {X Y Z}: Proper (@leq (Y-mon->Z) ==> leq ==> leq) (@comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x=>/=. rewrite (gg' x). apply ff'. Qed.
Lemma comp_leq_eqv {X Y} {Z: PO}: Proper (@leq (Y-eqv->Z) ==> eqv ==> leq) (@comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x=>/=. rewrite (gg' x). apply ff'. Qed.

#[export] Instance setoid_comp_eqv {X Y Z}: Proper (eqv ==> eqv ==> eqv) (@Setoid.comp X Y Z) := comp_eqv.
#[export] Instance setoid_comp_leq {X Y} {Z: PO}: Proper (leq ==> eqv ==> leq) (@Setoid.comp X Y Z) := comp_leq_eqv.
#[export] Instance po_comp_leq {X Y Z}: Proper (leq ==> leq ==> leq) (@PO.comp X Y Z) := comp_leq.
#[export] Instance po_comp_eqv {X Y Z}: Proper (eqv ==> eqv ==> eqv) (@PO.comp X Y Z) := op_leq_eqv_2.

(* #[export] Existing Instance comp_eqv(* _ {X Y Z : Setoid}: *) *)
(* (* Proper (meqv ==> meqv ==> meqv) (@comp X Y Z) := comp_eqv *). *)
(* #[export] Existing Instance comp_leq. *)
(* #[export] Existing Instance comp_leq_eqv. *)


Goal forall X: Setoid, forall f g h: X -eqv-> X, f ≡ g -> f ° g ≡ h.
  Fail intros * ->.
Abort.
Goal forall X: Setoid, forall f g h: X -eqv-> X, f ≡ g -> Setoid.comp f g ≡ h.
  intros * ->.
Abort.
Goal forall X: PO, forall f g h: X -eqv-> X, f ≡ g -> Setoid.comp f g <= h.
  intros * ->.
Abort.
Goal forall X: PO, forall f g h: X -mon-> X, f ≡ g -> PO.comp f g ≡ h.
  intros * ->.
Abort.
Goal forall X: PO, forall f g h: X -mon-> X, f ≡ g -> Setoid.comp f g <= h.
  Fail intros * ->.
  intros * H. rewrite (H: f≡[_-eqv->_]g). 
Abort.
Goal forall X: PO, forall f g h: X -mon-> X, f <= g -> f ° g <=[_-mon->_] h.
  Fail intros * ->.
Abort. 
Goal forall X: PO, forall f g h: X -mon-> X, f ≡ g -> f ° g <=[_-mon->_] h.
  Fail intros * ->.
Abort. 

Goal forall f g: nat -> Prop, f ≡ g -> f ≡ g.
  intros * ->.
Abort.
Goal forall f g: nat -> Prop, f <= g -> f <= g.
  intros * ->.
Abort.
Goal forall f g: nat -> Prop, f ≡ g -> f <= g.
  intros * ->.
Abort.


#[export] Instance const_leq {X} {Y: PO}: Proper (leq ==> leq) (@const X Y).
Proof. move=>/=y y' yy' _/=. apply yy'. Qed.
#[export] Instance setoid_const_leq {X} {Y: PO}: Proper (leq ==> leq) (@Setoid.const X Y) := const_leq.
#[export] Instance po_const_leq {X} {Y: PO}: Proper (leq ==> leq) (@PO.const X Y) := const_leq.
#[export] Instance po_const_eqv {X} {Y: PO}: Proper (eqv ==> eqv) (@PO.const X Y) := const_eqv.


Check nat: Setoid. 
Check nat: PO. 

Eval cbn in (5,3) <= (5,2). 
Eval cbn in ((5,3): lex_prod _ _) <= (6,2). 
Eval cbn in ((5,2): lex_prod _ (dual _)) <= (6,3). 

Goal forall (x: nat * (bool -> nat) * {y: nat | y=5}), x <= x.
  intros [[x f] [p ?]]. cbv.
Abort.
Goal forall (x: nat * sig (fun b: bool=> b=true)), x <= x.
Abort.
(* need irrelevant po *)
Fail Check forall (x: nat * forall b: bool, nat * True), x <= x.

Check fun X: PO => PO_on (dual X). 
Check fun X: PO => dual X: PO. 
Check fun (X: PO) (x: dual X) => x <= x. 
Check fun (X: PO) (f: X-mon->X) => f <= f. 
Check fun (X: PO) (f: X-mon->X) => f ≡ f. 
Check fun (X: PO) (f: X-eqv->X) => f ≡ f. 
Check fun (X: PO) (f: X-eqv->X) => f <= f. 
Check fun (X: Setoid) (f: X-eqv->X) => f ≡ f. 
Check fun (X: PO) (f: X-mon->dual X) => f <= f. 
Check fun (X: PO) (f: dual X-mon->X) => f <= f. 
Check fun (X: PO) (f: dual X-mon->dual X) => f <= f. 

Check fun (X: PO) (f: X-mon->X) => f°f <= f. 
Check fun (X: PO) (f: X-mon->X) => f°f ≡ f. 
Check fun (X: PO) (f: X-eqv->X) => f°f <= f. 
Check fun (X: PO) (f: X-eqv->X) => f°f ≡ f. 
Check fun (X: PO) (f: X->X) => f°f <= f. 
Check fun (X: PO) (f: X->X) => f°f ≡ f. 
Check fun (X: Setoid) (f: X-eqv->X) => f°f ≡ f. 
Check fun (X: Setoid) (f: X->X) => f°f ≡ f. 

Fail Check fun (X: PO) (f: X-mon->X) => id <= f. 
Check fun (X: PO) (f: X-mon->X) => Datatypes.id <=[_-mon->_] f. 
Check fun (X: PO) (f: X-mon->X) => Datatypes.id <=[_-eqv->_] f. 
Fail Check fun (X: PO) (f: X-mon->X) => id <=[_->_] f. 
Check fun (X: PO) (f: X-mon->X) => id <=[X->X] f. 
Fail Check fun (X: PO) (f: X-mon->X) => id ≡ f. 
Fail Check fun (X: PO) (f: X-eqv->X) => id <= f. 
Fail Check fun (X: PO) (f: X-eqv->X) => id ≡ f. 
Fail Check fun (X: PO) (f: X->X) => id <= f. 
Fail Check fun (X: PO) (f: X->X) => id ≡ f. 
Fail Check fun (X: Setoid) (f: X-eqv->X) => id ≡ f. 
Fail Check fun (X: Setoid) (f: X->X) => id ≡ f. 

Section s.
  Variable X: Setoid.
  Variable Y: PO.
  Check forall f g: X -eqv-> X, f ° g ≡ id.
  Check forall f g: nat -eqv-> nat, f ° g ≡ id.
  Check forall f g: nat -mon-> nat, f ° g ≡ id.
  Check forall f g: X -eqv-> Y, forall h: Y-eqv->X, f ° h ° g ≡ g.
  Check forall f g: Y -eqv-> Y, forall h: Y-mon->Y, f ° h ° g ≡ g.
  Check forall f g: Y -eqv-> Y, forall h: Y-mon->Y, f ° h ° g <= g.
  Check forall f g: Y -mon-> Y, forall h: Y-mon->Y, f ° h ° g <= g.
  Check forall f g: Y -mon-> Y, forall h: Y-eqv->Y, f ° h ° g ≡ g.
  Check forall f: Y -eqv-> Y, forall g: Y-mon->Y, f ° g ≡ id.
  Check forall f: Y -mon-> Y, forall g: Y-eqv->Y, f ° g ≡ id.
End s.

Goal forall X, forall f: X -eqv-> X, forall x y: X, x≡y -> f (f x) ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  

Goal forall X, forall f: X -eqv-> X, forall x y: X, x≡y -> (f ° f) x ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  



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


Notation downward_closed := (Proper (leq ==> impl)). 
Notation upward_closed := (Proper (leq --> impl)). 

Section s.
Context {X: PO}.
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
#[export] Instance PartialOrder_covered: RelationClasses.PartialOrder bicovered covered.
Proof. by []. Qed.
(* TOTHINK: declare [subrelation] instances? *)
Lemma leq_covered P Q: P <= Q -> covered P Q.
Proof. move=>H x Px. exists x; split=>//. by apply H. Qed.
Lemma eqv_covered f g: f ≡ g -> bicovered f g.
Proof. by rewrite eqv_of_leq; move=>[??]; split; apply leq_covered. Qed.


Definition is_sup P x := forall z, x <= z <-> forall y, P y -> y <= z.

(* infer [is_sup] using typeclasses? *)
Lemma leq_is_sup P x: is_sup P x -> forall y, P y -> y <= x.
Proof. move=>H y Py. by apply H. Qed.

Lemma is_sup_leq P p Q q: is_sup P p -> is_sup Q q -> covered P Q -> p<=q.
Proof.
  move=>Pp Qq PQ. apply Pp=>x Px.
  case: (PQ x Px)=>y [Qy ->]. by apply Qq.
Qed.

Lemma is_sup_eqv P p Q q: is_sup P p -> is_sup Q q -> bicovered P Q -> p≡q.
Proof. rewrite eqv_of_leq=>??[??]. eauto using is_sup_leq. Qed.

Lemma supU P x y: is_sup P x -> is_sup P y -> x ≡ y.
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

Definition sup_closed P := forall Q, Q <= P -> is_sup Q <= P.

Lemma sup_closed_impl P Q: upward_closed P -> sup_closed Q -> sup_closed (fun x => P x -> Q x).
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

Definition directed (P: X -> Prop) :=
  forall x y, P x -> P y -> exists z, P z /\ x <= z /\ y <= z.

Lemma directed_empty: directed empty.
Proof. by []. Qed.

Definition chain (P: X -> Prop) :=
  forall x y, P x -> P y -> x <= y \/ y <= x.

Lemma chain_empty: chain empty.
Proof. by []. Qed.

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
Lemma geq_is_inf P x: is_inf P x -> forall y, P y -> x <= y.
Proof. apply: (leq_is_sup (x:=x: dual X)). Qed.
Definition cocovered (P Q: X -> Prop) := covered (P: dual X -> _) (Q: dual X -> _).
Definition cobicovered (P Q: X -> Prop) := bicovered (P: dual X -> _) (Q: dual X -> _).
Lemma is_inf_leq P p Q q: is_inf P p -> is_inf Q q -> cocovered P Q -> q<=p.
Proof. apply: (@is_sup_leq _ (P: dual X -> Prop)). Qed.
Lemma is_inf_eqv P p Q q: is_inf P p -> is_inf Q q -> cobicovered P Q -> p≡q.
Proof. apply: (@is_sup_eqv _ (P: dual X -> Prop)). Qed.
Lemma infU (P: X -> Prop) x y: is_inf P x -> is_inf P y -> x ≡ y.
Proof. apply (supU (P:=P: dual X -> Prop)). Qed.

Definition inf_closed (P: X -> Prop) := forall Q, Q <= P -> forall z, is_inf Q z -> P z.

Lemma inf_closed_impl (P Q: X -> Prop): downward_closed P -> inf_closed Q -> inf_closed (fun x => P x -> Q x).
Proof. apply (sup_closed_impl (X:=dual_po X)). Qed.

Lemma inf_closed_leq (f: X -mon-> X): inf_closed (fun x => f x <= x).
Proof. apply (sup_closed_leq (dual_po_morphism f)). Qed.

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

(** sups can be computed pointwise in function spaces *)
Lemma dprod_sup {A} {X: A -> PO} (P: (forall a, X a)->Prop) (f: forall a, X a):
  (forall a, is_sup (image (fun h => h a) P) (f a)) -> is_sup P f.
Proof.
  move=>H g; split=>fg.
  - move=>h Ph. rewrite -fg=>a. apply H=>//. by exists h.
  - move=>a. apply H=>_ [h [Ph ->]]. by apply fg. 
Qed.
(** actually they *must* be computed pointwise, but not clear we can prove it without using decidability of equality on [A] *)
Lemma dprod_sup' {A} {X: A -> PO}
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

(** sups can be computed as expected in sub-spaces *)
Lemma kern_sup {A} {X: PO} (f: A -> X) (P: A->Prop) (a: A):
  is_sup (image f P) (f a) -> is_sup (X:=kern_po X f) P a.
Proof.
  move=>H b; split=>ab.
  -- move=>c Pc. rewrite -ab. apply H=>//. by exists c.
  -- apply H=>_ [c [Pc ->]]. by apply ab. 
Qed.


(** adjunctions *)
Section s.
  Context {X Y: PO}.
  Variables (f: X -> Y) (g: Y -> X).
  Class adjunction := adj: forall x y, f x <= y <-> x <= g y.
  
  Lemma left_adjoint_leq {A: adjunction}: Proper (leq ==> leq) f.
  Proof. intros x y xy. apply adj. rewrite xy. by apply adj. Qed.
  
  Lemma right_adjoint_leq {A: adjunction}: Proper (leq ==> leq) g.
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
  adjunction (comp f' f) (comp g g').
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



(** * partial orders with suprema *)

(*
E: empty
B: binary
C: chains    
D: directed
A: all

D=>C
A=>E,B,C,D
E+B+D=>A

real points:
E,EB,B
C,EC,(BC,EBC?)
D,ED
A

then: Distributive, Heyting, Boole

*)

Variant K := kE | kB | kC | kD | kA.
Definition args k (X: PO): Type :=
  match k with
  | kE => unit
  | kB => X * X
  | kC => sig (@chain X)
  | kD => sig (@directed X)
  | kA => (X -> Prop)
  end.
Definition setof {X: PO} k: args k X -> X -> Prop :=
  match k with
  | kE => fun _ => empty
  | kB => fun p => pair (fst p) (snd p)
  | kC => @proj1_sig _ _
  | kD => @proj1_sig _ _
  | kA => fun P => P
  end.

Section map_args.
 Context {X Y: PO}.
 Variable f: X -mon-> Y.
 Lemma image_chain P: chain P -> chain (image f P).
 Proof.
   move=>C _ _ [x [Px ->]] [y [Py ->]].
   case: (C x y Px Py)=>H; [left|right]; by apply f.
 Qed.
 Lemma image_directed P: directed P -> directed (image f P).
 Proof.
   move=>D _ _ [x [Px ->]] [y [Py ->]].
   case: (D x y Px Py)=>[z [Pz [xz yz]]].
   exists (f z). split. by exists z. split; by apply f.
 Qed.
 Definition map_args k: args k X -> args k Y :=
   match k return args k X -> args k Y with
   | kE => id
   | kB => fun '(x,y) => (f x,f y)
   | kC => fun '(exist _ P C) => exist _ (image f P) (image_chain C)
   | kD => fun '(exist _ P D) => exist _ (image f P) (image_directed D)
   | kA => image f
   end.
 Lemma setof_map_args k: forall x, setof k (map_args k x) ≡ image f (setof k x).
 Proof. case: k=>/=[_|[x x']|[P C]|[P D]|P]//=; firstorder congruence. Qed. 
End map_args.

Record prelevel := mk_prelevel { has_E: bool; has_B: bool; has_C: bool; has_D: bool}.
Definition leq_prelevel h h' :=
  let 'mk_prelevel e b c d := h in
  let 'mk_prelevel e' b' c' d' := h' in
  (e==>e' &&& b==>b' &&& c==>c' &&& d==>d')%bool.
Definition cup_prelevel h h' :=
  let 'mk_prelevel e b c d := h in
  let 'mk_prelevel e' b' c' d' := h' in
  mk_prelevel (e|||e') (b|||b') (c|||c') (d|||d').

Definition slevel := option prelevel.
Declare Scope level_scope.
Bind Scope level_scope with slevel.
Delimit Scope level_scope with level.
Definition leq_slevel (h k: slevel): bool :=
  match k,h with
  | None,_ => true
  | _,None => false
  | Some t, Some s => leq_prelevel s t
  end.
Definition cup_slevel (h k: slevel): slevel :=
  match h,k with
  | None,_ | _,None => None
  | Some s, Some t => Some (cup_prelevel s t)
  end.

Class slower h k := sLower: leq_slevel h k.
Infix "<<" := slower (at level 70). 
#[export] Instance PreOrder_slower: PreOrder slower.
Admitted.
Ltac solve_slower :=
  solve [ reflexivity | assumption |
          match goal with H: ?h << ?l |- ?k << ?l => transitivity h; [reflexivity|exact H] end].
#[export] Hint Extern 0 (_ << _) => solve_slower: typeclass_instances.
Infix "+" := cup_slevel (at level 50, left associativity): level_scope.

Section levels.
Notation "1" := true.
Notation "0" := false.
Definition plN := mk_prelevel 0 0 0 0.
Definition lE := mk_prelevel 1 0 0 0.
Definition lB := mk_prelevel 0 1 0 0.
Definition lC := mk_prelevel 1 0 1 0.
Definition lD := mk_prelevel 1 0 1 1.
Definition lF := mk_prelevel 1 1 0 0.
Definition lS k: slevel := Some k.
Definition sA: slevel := None.
End levels.
  
Coercion slevel_for k: slevel := match k with kE => Some lE | kB => Some lB | kC => Some lC | kD => Some lD | kA => None end.

Section reduce.
  Variable T: K -> Type.
  Variable f: forall k, option (T k).
  Definition slevel_of: slevel :=
    let f k := match f k with None => Some plN | Some _ => slevel_for k end
    in f kE + f kB + f kC + f kD + f kA.
  Ltac discriminate_levels :=
    (discriminate ||
       lazymatch goal with |- context [f ?k] => (* idtac k; *) case: (f k)=>[_|]; discriminate_levels end).
  Hypothesis H: forall h k: K, leq_slevel h k -> T k -> T h. 
  Definition reduce: forall k: K, leq_slevel k slevel_of -> T k.
    unfold slevel_of. 
    case.
    - case (f kE)=>[v _|]. exact v.
      case (f kA)=>[v _|]. revert v. by apply H. 
      case (f kD)=>[v _|]. revert v. by apply H. 
      case (f kC)=>[v _|]. revert v. by apply H.
      discriminate_levels. 
    - case (f kB)=>[v _|]. exact v.
      case (f kA)=>[v _|]. revert v. by apply H. 
      discriminate_levels. 
    - case (f kC)=>[v _|]. exact v.
      case (f kA)=>[v _|]. revert v. by apply H. 
      case (f kD)=>[v _|]. revert v. by apply H. 
      discriminate_levels. 
    - case (f kD)=>[v _|]. exact v.
      case (f kA)=>[v _|]. revert v. by apply H. 
      discriminate_levels.
    - case (f kA)=>[v _|]. exact v.
      discriminate_levels.
  Defined.
End reduce.
Section reduce_ops.
  Variable X: PO.
  Definition gsup_ops k := sig (fun sup: args k X -> X => forall x, is_sup (setof k x) (sup x)).
  Variable f: forall k: K, option (gsup_ops k). 
  Definition reducer: forall h k: K, leq_slevel h k -> gsup_ops k -> gsup_ops h.
    case; case=>//_ [v H].
    - exists (fun _ => v (exist _ empty chain_empty)). by move=>/=_; apply H. 
    - exists (fun _ => v (exist _ empty directed_empty)). by move=>/=_; apply H. 
    - exists (fun _ => v empty). by move=>/=_; apply H. 
    - exists (fun '(x,y) => v (pair x y)). by move=>/=[??]; apply H. 
    - exists (fun '(exist _ P C) => v (exist _ P (chain_directed C))). by move=>/=[??]; apply H. 
    - exists (fun '(exist _ P C) => v P). by move=>/=[??]; apply H. 
    - exists (fun '(exist _ P C) => v P). by move=>/=[??]; apply H. 
  Defined.
End reduce_ops.

Module SPO.

(** ** class *)

Definition mixin (l: slevel) X (M: Setoid.mixin X) (N: PO.mixin M) :=
  forall k: K, k << l -> gsup_ops (PO.pack N) k.
Structure type l := pack {
    sort:> Type;
    #[canonical=no] setoid_mix: Setoid.mixin sort;
    #[canonical=no] po_mix: PO.mixin setoid_mix;
    #[canonical=no] mix: mixin l po_mix;
}.
Canonical Structure to_PO l (X: type l): PO := PO.pack (po_mix X). 
Canonical Structure to_Setoid l (X: type l): Setoid := Setoid.pack (setoid_mix X). 
#[reversible] Coercion to_PO: type >-> PO.
#[reversible] Coercion to_Setoid: type >-> Setoid.
Definition build (l: slevel) (X: PO): (forall k: K, k << l -> gsup_ops X k) -> type l :=
  let '@PO.pack T M N := X in @pack l T M N.
Arguments build [_] _.
Definition reduced_build (X: PO) (f: forall k, option (gsup_ops X k)): type (slevel_of _ f) :=
  build X (reduce _ f (@reducer _)).
Arguments reduced_build: clear implicits.
End SPO.
Notation SPO := SPO.type.
Canonical SPO.to_PO.
Canonical SPO.to_Setoid.
#[reversible] Coercion SPO.to_Setoid: SPO >-> Setoid.
#[reversible] Coercion SPO.to_PO: SPO >-> PO.
#[reversible] Coercion SPO.sort: SPO >-> Sortclass.
Definition gsup {l} {X: SPO l} k kl: args k X -> X := proj1_sig (SPO.mix X k kl).
Arguments gsup {_ _}. 
Definition gsup_spec {l} {X: SPO l} {k kl}: forall (x: args k X), is_sup (setof k x) (gsup k kl x) :=
  proj2_sig (SPO.mix X k kl).
Definition spo_on l T (S: SPO l) (_: T -> S) := S.
Notation "'SPO[' l ']_on' T" := (@spo_on l T _ (fun x => x)) (at level 20).

Lemma leq_gsup {l} {X: SPO l} k kl x (y: X): setof k x y -> y <= gsup k kl x.
Proof. apply leq_is_sup, gsup_spec. Qed.

Definition bot {l} {X: SPO l} {L: Some lE << l}: X := gsup kE L tt. 
Definition cup {l} {X: SPO l} {L: Some lB << l} (x y: X): X := gsup kB L (x,y).
Definition csup {l} {X: SPO l} {L: Some lC << l} (P: X -> Prop) (C: chain P): X := gsup kC L (exist _ P C).
Definition dsup {l} {X: SPO l} {L: Some lD << l} (P: X -> Prop) (D: directed P): X := gsup kD L (exist _ P D). 
Definition sup {l} {X: SPO l} {L: None << l}: (X -> Prop) -> X := gsup kA L. 
Infix "⊔" := cup (left associativity, at level 50). 
Arguments csup {_ _ _}. 
Arguments dsup {_ _ _}. 

Lemma is_sup_bot {l} {X: SPO l} {L: Some lE << l}: is_sup (@empty X) bot.
Proof. apply: gsup_spec. Qed.
Lemma is_sup_cup {l} {X: SPO l} {L: Some lB << l} (x y: X): is_sup (pair x y) (x ⊔ y).
Proof. apply: gsup_spec. Qed.
Lemma is_sup_csup {l} {X: SPO l} {L: Some lC << l} (P: X -> Prop) C: is_sup P (csup P C).
Proof. apply: gsup_spec. Qed.
Lemma is_sup_dsup {l} {X: SPO l} {L: Some lD << l} (P: X -> Prop) D: is_sup P (dsup P D).
Proof. apply: gsup_spec. Qed.
Lemma is_sup_sup {l} {X: SPO l} {L: None << l} (P: X -> Prop): is_sup P (sup P).
Proof. apply: gsup_spec. Qed.

Lemma leq_csup {l} {X: SPO l} {L: lS lC << l} (P: X -> Prop) C x: P x -> x <= csup P C. 
Proof. move=>Px. by apply: leq_gsup. Qed.
Lemma leq_dsup {l} {X: SPO l} {L: lS lD << l} (P: X -> Prop) D x: P x -> x <= dsup P D. 
Proof. move=>Px. by apply leq_gsup. Qed.
Lemma leq_sup {l} {X: SPO l} {L: sA << l} (P: X -> Prop) x: P x -> x <= sup P. 
Proof. move=>Px. by apply leq_gsup. Qed.


Lemma cup_spec {l} {X: SPO l} {L: lS lB << l} (x y z: X): x ⊔ y <= z <-> x <= z /\ y <= z.
Proof. rewrite is_sup_cup /pair; intuition subst; auto. Qed.

Lemma cupA {l} {X: SPO l} {L: lS lB << l} (x y z: X): x ⊔ (y ⊔ z) ≡ x ⊔ y ⊔ z. 
Proof. apply: from_above=>t. rewrite 4!cup_spec. tauto. Qed.

Lemma csup_sup {l} {X: SPO l} {L: sA << l} P C: csup P C ≡[X] sup P.
Proof. apply: supU. apply is_sup_csup. apply is_sup_sup. Qed.
Lemma dsup_sup {l} {X: SPO l} {L: sA << l} P D: dsup P D ≡[X] sup P.
Proof. apply: supU. apply is_sup_dsup. apply is_sup_sup. Qed.

Lemma csup_empty {l} {X: SPO l} {L: lS lC << l} C: csup empty C ≡[X] bot.
Proof. apply: supU. apply is_sup_csup. apply is_sup_bot. Qed.
Lemma dsup_empty {l} {X: SPO l} {L: lS lD << l} D: dsup empty D ≡[X] bot.
Proof. apply: supU. apply is_sup_dsup. apply is_sup_bot. Qed.
Lemma sup_empty {l} {X: SPO l} {L: sA << l}: sup empty ≡[X] bot.
Proof. apply: supU. apply is_sup_sup. apply is_sup_bot. Qed.

Lemma sup_pair {l} {X: SPO l} {L: sA << l} (x y: X): sup (pair x y) ≡ x ⊔ y.
Proof. apply: supU. apply is_sup_sup. apply is_sup_cup. Qed.

Lemma directed_sup_closure {l} {X: SPO l} {L: lS lB << l} (P: X -> Prop): directed (sup_closure P).
Proof.
  move=>x y Px Py. exists (x⊔y); split. 2: by apply cup_spec.
  apply sc_sup with (pair x y). 2: apply is_sup_cup.
  by move=>z [->|->].
Qed.
Corollary sup_dsup {l} {X: SPO l} {L: sA << l} (P: X -> Prop):
  sup P ≡ dsup (sup_closure P) (directed_sup_closure (P:=P)).
Proof. rewrite dsup_sup. apply: supU. apply is_sup_sup. apply is_sup_closure, is_sup_sup. Qed.

Lemma discriminate {P: Type}: false -> P.
Proof. by []. Qed.

Program Canonical Structure bool_spo: SPO (lS lF) := Eval hnf in 
    SPO.build bool
      (fun k => match k with
             | kE => fun _ => exist _ (fun _ => false) _
             | kB => fun _ => exist _ (fun '(x,y) => orb x y) _
             | kC | kD | kA  => discriminate
             end).
Next Obligation. by case. Qed.
Next Obligation. Admitted.

Program Definition dual_bool_spo: SPO (lS lF) := Eval hnf in 
    SPO.build (dual bool)
      (fun k => match k with
             | kE => fun _ => exist _ (fun _ => true) _
             | kB => fun _ => exist _ (fun '(x,y) => andb x y) _
             | kC | kD | kA  => discriminate
             end).
Next Obligation. by case. Qed.
Next Obligation. Admitted.

Program Canonical Structure nat_spo: SPO (lS lF) := Eval hnf in 
    SPO.build nat
      (fun k => match k with
             | kE => fun _ => exist _ (fun _ => 0) _
             | kB => fun _ => exist _ (fun '(x,y) => Peano.max x y) _
             | kC | kD | kA  => discriminate
             end).
Next Obligation. Admitted.
Next Obligation. cbn. Admitted.


Program Definition dual_nat_spo: SPO (lS lB) := Eval hnf in 
    SPO.build (dual nat)
      (fun k => match k with
             | kB => fun _ => exist _ (fun '(x,y) => Peano.min x y) _
             | kE | kC | kD | kA  => discriminate
             end).
Next Obligation. cbn. Admitted.

Program Canonical Structure Prop_spo: SPO sA := Eval hnf in
  SPO.reduced_build Prop
    (fun k => match k with
           | kE => Some (exist _ (fun _ => False) _)
           | kB => Some (exist _ (fun '(p,q) => p\/q) _)
           | kC => None          (* generated *)
           | kD => None          (* generated *)
           | kA => Some (exist _ (fun P => exists2 p, P p & p) _)
           end).
Next Obligation. cbv; firstorder. Qed.
Next Obligation. cbv; firstorder subst; eauto. Qed.
Next Obligation. cbv; firstorder. Qed.

Program Definition dual_Prop_spo: SPO sA := Eval hnf in
  SPO.reduced_build (dual Prop)
    (fun k => match k with
           | kE => Some (exist _ (fun _ => True) _)
           | kB => Some (exist _ (fun '(p,q) => p/\q) _)
           | kC => None          (* generated *)
           | kD => None          (* generated *)
           | kA => Some (exist _ (fun P => forall p, P p -> p) _)
           end).
Next Obligation. cbv; firstorder. Qed.
Next Obligation. cbv; firstorder subst; eauto; apply H; eauto. Qed.
Next Obligation. cbv; firstorder. Qed.


Definition app {A} {X: A -> PO} a: (forall a, X a)-mon->X a :=
  PO.build_morphism (fun f => f a) (fun f g fg => fg a).

(** SPOs on dependent products *)
Program Canonical Structure dprod_spo {A l} (X: A -> SPO l): SPO l :=
  Eval hnf in SPO.build (forall a, X a) (fun k kl => exist _ (fun F a => gsup k kl (map_args (app a) k F)) _). 
Next Obligation.
  apply dprod_sup=>a. eapply Proper_is_sup.
  2: reflexivity. 2: apply: gsup_spec.
  apply eqv_covered. by rewrite setof_map_args. 
Qed.

Program Definition proj1_sig_mon {X: PO} (P: X -> Prop): sig P -mon-> X :=
  PO.build_morphism (@proj1_sig _ _) _.
Next Obligation. by []. Qed.

(** sub-SPOs *)
Section sub.
 Context {l} {X: SPO l}.
 Variable P: X -> Prop.
 Definition sup_closed' :=
   forall k: K, forall kl: k<<l, forall x, setof k x <= P ->  P (gsup k kl x).
 Lemma sup_closed_sup_closed': sup_closed P -> sup_closed'. 
 Proof. move=>H k kl x Hx. apply: H. apply Hx. apply gsup_spec. Qed.
 Program Definition sig_spo (Psup: sup_closed'): SPO l := Eval hnf in
   SPO.build (sig P) (fun k kl => exist _ (fun F => exist _ (gsup k kl (map_args (proj1_sig_mon P) k F)) _) _). 
 Next Obligation.
   apply: Psup. rewrite setof_map_args. 
   by move=>_ [[x Px] [_ ->]]. 
 Qed.
 Next Obligation.
   apply kern_sup=>/=. eapply Proper_is_sup.
   2: reflexivity. 2: apply: gsup_spec.
   apply eqv_covered. by rewrite setof_map_args. 
 Qed.
End sub.

(** SPOs from retractions (and thus isomorphisms given the induced order on [A]) *)
Section c.
 Context {A: Type} {l} (X: SPO l).
 Variable r: A->X.               (* retraction *)
 Variable i: X->A.               (* section *)
 Hypothesis ri: r°i ≡ id. 
 Program Let r': kern_po X r -mon-> X := PO.build_morphism r _.
 Next Obligation. by []. Qed.
 Program Definition retract_spo: SPO l := Eval hnf in 
     SPO.build (kern_po X r) (fun k kl => exist _ (fun x => i (gsup k kl (map_args r' k x))) _).
 Next Obligation.
   apply kern_sup. eapply Proper_is_sup. 2: apply ri. 2: apply: gsup_spec.
   apply eqv_covered. by rewrite setof_map_args.
 Qed.
End c.
Arguments retract_spo [_ _] _ [_ _]. 

(** altogether, we get general sub-SPOs  *)
Section c.
 Context {A: Type} {l} {X: SPO l} (P: X -> Prop).
 Variable r: A->sig P.
 Variable i: sig P->A.
 Hypothesis ri: r°i ≡ id. 
 Hypothesis Psup: sup_closed' P.
 Definition sub_spo: SPO l := Eval hnf in retract_spo (sig_spo Psup) ri. 
End c. 

(** the SPO of monotone functions *)
Section s.
 Context {X: PO} {l} {Y: SPO l}.
 Lemma po_morphism_as_sig:
   (fun f: X-mon->Y => exist (Proper (leq ==> leq)) (PO.body f) (@body_leq _ _ f))
     ° (fun f: sig (Proper (leq ==> leq)) => PO.build_morphism _ (proj2_sig f)) ≡ id.
 Proof. by case. Qed.
 Program Canonical Structure mon_spo: SPO l := Eval hnf in sub_spo po_morphism_as_sig _.
 Next Obligation.
   move=>k kl P HP x y xy.
   apply gsup_spec=>z Hz. apply setof_map_args in Hz as [f [Hf ->]].
   transitivity (f y). apply (HP _ Hf _ _ xy). apply leq_gsup. 
   apply setof_map_args. by exists f.
 Qed.
End s.

(** * partial orders with both suprema and infima *)

Variant level := lA | lSI(lS lI: prelevel).
Definition dual_level l := match l with lA => lA | lSI s i => lSI i s end.
Definition bilevel (s i: slevel): level := match s,i with Some s,Some i => lSI s i | _,_ => lA end.
Definition leq_level h h': bool :=
  match h',h with
  | lA,_ => true
  | _,lA => false
  | lSI s' i', lSI s i => leq_prelevel s s' &&& leq_prelevel i i'
  end.                                     
Definition cup_level h k: level :=
  match h,k with
  | lA,_ | _,lA => lA
  | lSI s i, lSI t j => lSI (cup_prelevel s t) (cup_prelevel i j)
  end.
Class lower h k := Lower: leq_level h k.
Infix "<<<" := lower (at level 70). 
#[export] Instance PreOrder_lower: PreOrder lower.
Admitted.
Ltac solve_lower :=
  solve [ reflexivity | assumption |
          match goal with H: ?h <<< ?l |- ?k <<< ?l => transitivity h; [reflexivity|exact H] end].
#[export] Hint Extern 0 (_ <<< _) => solve_lower: typeclass_instances.
Infix "++" := cup_level: level_scope.

(* Definition suplevel (k: level): slevel := match k with lSI s _ => Some s | lA => None end. *)
(* Definition inflevel (k: level): slevel := match k with lSI _ i => Some i | lA => None end. *)
(* Definition leq_suplevel p k := match k with lSI s _ => leq_prelevel p s | lA => true end. *)
(* Definition leq_inflevel p k := match k with lSI _ i => leq_prelevel p i | lA => true end. *)
Notation suplevel := id. 
Notation inflevel := id. 

Module GPO.

(** ** class *)

Structure type l := pack {
    sort:> Type;
    #[canonical=no] setoid_mix: Setoid.mixin sort;
    #[canonical=no] po_mix: PO.mixin setoid_mix;
    #[canonical=no] s_mix: SPO.mixin (suplevel l) po_mix;
    #[canonical=no] i_mix: SPO.mixin (inflevel l) (PO.dual_mixin po_mix);
}.
Canonical Structure to_SPO l (X: type l): SPO (suplevel l) := SPO.pack (s_mix X). 
Canonical Structure to_PO l (X: type l): PO := PO.pack (po_mix X). 
Canonical Structure to_Setoid l (X: type l): Setoid := Setoid.pack (setoid_mix X). 
#[reversible] Coercion to_SPO: type >-> SPO.
#[reversible] Coercion to_PO: type >-> PO.
#[reversible] Coercion to_Setoid: type >-> Setoid.
Definition build l (X: SPO (suplevel l)): (forall k: K, k << inflevel l -> gsup_ops (dual X) k) -> type l :=
  let '@SPO.pack _ T M N P := X in @pack l T M N P.
Arguments build [_] _.
Goal forall X M (N: @PO.mixin X M), N = PO.dual_mixin (PO.dual_mixin N). Fail reflexivity. Abort.
Goal forall X M (N: @PO.mixin X M) l, SPO.mixin l N = SPO.mixin l (PO.dual_mixin (PO.dual_mixin N)). reflexivity. Abort.
Definition dual l (X: type l): type l :=
  let '@GPO.pack _ T M N P Q := X in 
  @pack l T M (PO.dual_mixin N) Q P.
  
(* Definition reduced_build (X: PO) (f: forall k, option (gsup_ops X k)): type (slevel_of _ f) := *)
(*   build X (reduce _ f (@reducer _)). *)
(* Arguments reduced_build: clear implicits. *)
End GPO.
Notation GPO := GPO.type.
Canonical GPO.to_SPO.
Canonical GPO.to_PO.
Canonical GPO.to_Setoid.
#[reversible] Coercion GPO.to_Setoid: GPO >-> Setoid.
#[reversible] Coercion GPO.to_PO: GPO >-> PO.
#[reversible] Coercion GPO.to_SPO: GPO >-> SPO.
#[reversible] Coercion GPO.sort: GPO >-> Sortclass.



(** * chain construction *)

Module Chain.
Section c.
 Context {X: PO}.
 Section d.
 Variable f: X -> X.

 (** the set of all (transfinite) iterations of f *)
 Inductive C: X -> Prop :=
 | Cf: forall x, C x -> C (f x)
 | Csup: forall P, P <= C -> forall x, is_sup P x -> C x.
 
 (** a type for the elements of the chain *)
 Structure Chain := chn { elem:> X; #[canonical=no] Celem: C elem}.

 (** the chain inherits the partial order structure from X *)
 Canonical Structure Chain_setoid := Eval hnf in kern_setoid _ elem.
 Canonical Structure Chain_po := Eval hnf in kern_po _ elem.

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
 Program Canonical Structure next_eqv (f: X -eqv-> X) := Setoid.build_morphism (next f) _.   
 Next Obligation. by move =>???; apply f. Qed.
 
 (** when [f] is monotone (on [X]), so is [next] (on [Chain f])  *)
 Section d.
 Variable f: X -mon-> X.
 Program Canonical Structure next_leq := PO.build_morphism (next f) _.   
 Next Obligation. by move =>???; apply f. Qed.

 (** elements of the chain are post-fixpoints of [f] *)
 Lemma chain_postfixpoint: forall c: Chain f, c <= next f c.
 Proof.
   apply tower. apply: sup_closed_leq. 
   by move=>*; apply f.
 Qed.

 (** they are below all pre-fixpoints of [f] *)
 Theorem chain_below_prefixpoints x: f x <= x -> forall c: Chain f, (c: X) <= x.
 Proof.
   (* we would like to use [tower], but this requires closure under sups in [Chain f],
      and [sup_closed_leq] does not apply... *)
   move=>Hx []/=.
   induction 1 as [y Cy IH|T TC IH t Ht].
   - by rewrite IH.
   - move: T {TC} IH t Ht. apply: (sup_closed_leq (const x)). 
 Qed.

 (** if the chain contains a pre-fixpoint, then this is the least (pre-)fixpoint *)
 Theorem lpfp_of_chain_prefixpoint (c: Chain f): f c <= (c: X) -> is_lfp f c.
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
 Context {l} {X: SPO l}.
 Variable f: X->X.
 Lemma Chain_as_sig:
   (fun c: Chain f => exist (C f) (elem c) (Celem c))
     ° (fun c: sig (C f) => chn (proj2_sig c)) ≡ id.
 Proof. by case. Qed.
 Canonical Structure Chain_spo: SPO l := Eval hnf in
   sub_spo Chain_as_sig (sup_closed_sup_closed' (@Csup _ f)). 
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
 Lemma choose (X: PO) (P: X -> Prop) (f: X -eqv-> X) y y':
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

 Context {C: PO}.
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
       case: (choose T Datatypes.id c (next c)).
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
       case: (choose T Datatypes.id z z).
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
 Corollary lt_leq'' x y: next x <= y -> x < y \/ is_sup (fun _ => True) x. 
 Proof.
   move=>H. case: (lt_next x); auto=>//H'.
   left. eapply ltle_lt; eassumption. 
 Qed.   

End b.
Section b.

 Context {l} {X: SPO l} {L: lS lC<<l}.
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
   apply: leq_csup. apply Cf. apply Csup with (C f)=>//. apply is_sup_csup.
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

 Context {C: PO}.
 Implicit Types x y z: C.

 (** tower induction *)
 Variable next: C -mon-> C.
 Hypothesis tower: forall (P: C -> Prop), sup_closed P -> (forall x, P x -> P (next x)) -> forall x, P x.

 (** the function [next] must be extensive *)
 Lemma id_next: PO.id <= next.
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
     case: (choose T Datatypes.id y y). by move=>*; apply IH.
     -- move=>F. left. apply Ht=>x Tx. by apply F.
     -- move=>[x [Tx yx]]. right. rewrite yx. by apply Ht.
   - move=>x IH y.
     case: (choose (fun t => next t <= y) Datatypes.id x x).
     by move=>t _; move: (IH t); tauto.
     -- move=>F. right. apply leq_next=>z zy. by apply F.
     -- move=>[t [ty xt]]. left. by rewrite xt.
 Qed.

End b.
Section b.

 Context {l} {X: SPO l} {L: lS lC<<l}.
 Variable f: X -mon-> X. 

 Lemma chain_C: chain (C f).
 Proof.
   move=>x y Cx Cy.
   exact: (total_chain _ (tower f) (chn Cx) (chn Cy)).
 Qed.
 
 Definition lfp := csup (C f) chain_C.
 Theorem is_least_fixpoint: is_lfp f lfp.
 Proof. apply lpfp_of_chain_supremum. apply is_sup_csup. Qed.

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
   apply Csup with (C f)=>//. apply is_sup_csup. 
 Qed.
 
End b. 
End BourbakiWitt'. 

Module Pataraia. 

Section s.
 Context {l} {C: SPO l} {L: lS lD<<l}.

 (* TMP *)
 Infix "°" := (PO.comp).
 Notation id := PO.id.

 (** the largest monotone and extensive function on [C] *)
 Program Definition h: C-mon->C := dsup (fun f => id <= f) _.
 Next Obligation.
   move=>/=i j I J. exists (i°j). split; last split.
   - by rewrite -I.
   - by rewrite -J.             (* !! need [kern_po _ ° kern po _ = kern_po (_°_)] *)
   - by rewrite -I.
 Qed.
 
 Lemma h_ext: id <= h.
 Proof. by apply: leq_dsup. Qed.

 Lemma h_invol: h ° h <= h.
 Proof.
   apply: leq_dsup.
   by rewrite -h_ext.
 Qed.

 Definition extensive_fixpoint := locked (h bot).

 Variable f: C-mon->C.
 Hypothesis f_ext: id <= f. 
 
 Lemma h_prefixpoint: f ° h <= h.
 Proof. apply: leq_dsup. by rewrite -f_ext -h_ext. Qed.

 Theorem is_extensive_fixpoint: f extensive_fixpoint ≡ extensive_fixpoint. 
 Proof. apply antisym. unlock extensive_fixpoint. apply h_prefixpoint. apply f_ext. Qed.
End s.

Section s.
 Context {l} {X: SPO l} {L: lS lD<<l}.
 Variable f: X-mon->X.

 Definition lfp := locked (extensive_fixpoint (C:=Chain f): X).
   
 Theorem is_least_fixpoint: is_lfp f lfp. 
 Proof.
   unlock lfp.
   apply lpfp_of_chain_prefixpoint. 
   apply eqv_leq.
   exact (is_extensive_fixpoint (chain_postfixpoint f)).
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
   - apply H. unlock lfp. apply Celem.
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
 Corollary lfp_prop (P: X -> Prop): (forall c: Chain f, P c) -> P lfp.
 Proof.
   move=>H.
   exact (H (chn (any_lfp_in_chain is_least_fixpoint))).
 Qed.
 
End s.

End Pataraia.
End Chain.

Print Assumptions Chain.BourbakiWitt.is_fixpoint.
Print Assumptions Chain.BourbakiWitt'.is_least_fixpoint.
Print Assumptions Chain.Pataraia.is_least_fixpoint.

(* time coqc alone.v: 2.6s *)
