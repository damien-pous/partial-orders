Require Import Setoid Morphisms Basics Strings.String.
Require Import ssreflect ssrfun ssrbool.
Require Eqdep_dec Classical.

Set Implicit Arguments.
Unset Strict Implicit.
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

Definition phant_id {T} {t : T} (x : phantom _ t) := x.
Definition unify {T1 T2} (t1 : T1) (t2 : T2) (s : option string) := phantom _ t1 -> phantom _ t2.
Notation "[find v | t1 ~ t2 ] p" := (fun v (_ : unify t1 t2 None) => p) (at level 50, v name, only parsing).
Notation "[find v | t1 ~ t2 | s ] p" := (fun v (_ : unify t1 t2 (Some s)) => p) (at level 50, v name, only parsing).
Notation "'Error : t : s" := (unify _ t (Some s)) (at level 50, format "''Error' : t : s").
Open Scope string_scope.

(** * setoids *)

(** ** class *)

Module Setoid.

 Structure ops := build {
    sort:> Type;
    #[canonical=no] eqv: relation sort;
 }.
 Arguments build: clear implicits.
 Arguments eqv: clear implicits. 
 Structure laws := validate {
    lsort:> ops;
    #[canonical=no] Equivalence_eqv: Equivalence (eqv lsort);
 }.
 Arguments validate _%type: clear implicits.
 Notation cast o e := (validate o (Equivalence_eqv e)) (only parsing). 
 
 Structure morphism (X Y: ops) := build_morphism {
    body:> X -> Y;
    #[canonical=no] body_eqv: Proper (eqv X ==> eqv Y) body;
 }.
 Arguments build_morphism {_ _}. 

 Canonical Structure id {X}: morphism X X :=
   build_morphism Datatypes.id _.
 Program Canonical Structure comp {X Y Z} (f: morphism Y Z) (g: morphism X Y): morphism X Z :=
   build_morphism (comp f g) _. 
 Next Obligation. move=>x y xy. apply f, g, xy. Qed.
 Program Canonical Structure const {X} {Y: laws} (y: Y): morphism X Y :=
   build_morphism (const y) _.
 Next Obligation. move=>/=_ _ _. apply Equivalence_eqv. Qed.

End Setoid.
#[reversible] Coercion Setoid.sort: Setoid.ops >-> Sortclass.
#[reversible] Coercion Setoid.lsort: Setoid.laws >-> Setoid.ops.
#[reversible] Coercion Setoid.body: Setoid.morphism >-> Funclass.
Canonical Setoid.id.
Canonical Setoid.comp.
Canonical Setoid.const.
Notation Setoid := Setoid.laws. 
Notation "X '-eqv->' Y" := (Setoid.morphism X Y) (at level 99, Y at level 200).
Arguments Setoid.eqv {_}.
Notation eqv := Setoid.eqv.
(* #[export] Existing Instance Setoid.Equivalence_eqv. *)
#[export] Hint Extern 0 (Equivalence eqv) => apply: Setoid.Equivalence_eqv: typeclass_instances.
#[export] Existing Instance Setoid.body_eqv.
Definition setoid_ops_on T (S: Setoid.ops) (_: T -> S) := S.
Definition setoid_laws_on T (S: Setoid) (_: T -> S) := S.
Notation Setoid_ops_on T := (@setoid_ops_on T _ (fun x => x)).
Notation Setoid_laws_on T := (@setoid_laws_on T _ (fun x => x)).
Notation eqv_on T := (@eqv (Setoid_ops_on T)). 
Infix "≡" := eqv (at level 70).
Infix "≡[ X ]" := (@eqv_on X) (at level 70).
#[export] Hint Extern 0 => reflexivity: core.

(** ** instances *)

Definition eq_setoid X := Setoid.build X eq.
Definition eq_setoid_laws_ X := Setoid.validate (eq_setoid X) (@eq_equivalence X).
Notation eq_setoid_laws X := (Setoid.cast X (eq_setoid_laws_ X)).

Canonical Structure unit_setoid := Eval hnf in eq_setoid unit.
Canonical Structure unit_setoid_laws := Eval hnf in eq_setoid_laws unit.

Canonical Structure bool_setoid := Eval hnf in eq_setoid bool.
Canonical Structure bool_setoid_laws := Eval hnf in eq_setoid_laws bool.

Canonical Structure nat_setoid := Eval hnf in eq_setoid nat.
Canonical Structure nat_setoid_laws := Eval hnf in eq_setoid_laws nat.

Canonical Structure Prop_setoid := Setoid.build Prop iff.
Canonical Structure Prop_setoid_laws := Setoid.validate _ iff_equivalence.

Canonical Structure prod_setoid (X Y: Setoid.ops) :=
  Setoid.build (X*Y) (fun p q => fst p ≡ fst q /\ snd p ≡ snd q).
Program Canonical Structure prod_setoid_laws (X Y: Setoid) :=
  Eval hnf in Setoid.validate (X*Y) _.
Next Obligation.
  constructor=>//.
  by move=>??[??]; split; symmetry; assumption.
  by move=>???[??][]; split; etransitivity; eassumption.
Qed.

Canonical Structure sum_setoid (X Y: Setoid.ops) :=
  Setoid.build (X+Y) (fun p q => match p,q with inl p,inl q | inr p,inr q => p ≡ q | _,_ => False end).
Program Canonical Structure sum_setoid_laws (X Y: Setoid) :=
  Eval hnf in Setoid.validate (X+Y) _.
Next Obligation.
  constructor.
  by move=>[]/=; reflexivity. 
  by move=>[]?[]?//=; symmetry.
  by move=>[]?[]y[]?//=; transitivity y.
Qed.

(* TODO: lists *)

Canonical Structure dprod_setoid A (X: A -> Setoid.ops) :=
  Setoid.build (forall a, X a) (fun f g => forall a, f a ≡ g a).
Program Canonical Structure dprod_setoid_laws A (X: A -> Setoid) :=
  Eval hnf in Setoid.validate (forall a, X a) _.
Next Obligation.
  constructor.
  - by move=>??. 
  - by move=>????; symmetry. 
  - by move=>??????; etransitivity; eauto.
Qed.

Definition kern_setoid A (X: Setoid.ops) (f: A -> X) :=
  Setoid.build A (fun a b => f a ≡ f b).
Program Definition kern_setoid_laws_ A (X: Setoid) (f: A -> X) :=
  Setoid.validate (kern_setoid f) _.
Next Obligation.
  constructor.
  - by move=>//=. 
  - by move=>???/=; symmetry.
  - by move=>/=?????/=; etransitivity; eauto. 
Qed.
Notation kern_setoid_laws X := (Setoid.cast X (kern_setoid_laws_ _)).

Canonical Structure sig_setoid (X: Setoid.ops) (P: X -> Prop) :=
  Eval hnf in kern_setoid (@proj1_sig X P).
Canonical Structure sig_setoid_laws (X: Setoid) (P: X -> Prop) :=
  Eval hnf in kern_setoid_laws (sig P).

Canonical Structure setoid_morphisms_setoid (X Y: Setoid.ops) :=
  Eval hnf in kern_setoid (@Setoid.body X Y).
Program Canonical Structure setoid_morphisms_setoid_laws (X Y: Setoid) :=
  Eval hnf in kern_setoid_laws (X-eqv->Y).
Notation eqv_setoids := (@eqv (setoid_morphisms_setoid _ _)). 
Infix "≡[-eqv->]" := (eqv_setoids) (at level 70).


Definition dual (X: Type) := X.
Canonical Structure dual_setoid (X: Setoid.ops) :=
  (* just a clone *)
  Eval hnf in Setoid.build (dual X) eqv.
Canonical Structure dual_setoid_laws (X: Setoid) :=
  (* just a clone *)
  Eval hnf in Setoid.validate (dual_setoid X) (Setoid.Equivalence_eqv _).

Program Canonical Structure dual_setoid_morphism {X Y: Setoid} (f: X -eqv-> Y): dual X -eqv-> dual Y :=
  Setoid.build_morphism f (Setoid.body_eqv _).

(* most general lemma *)
Lemma comp_eqv {X} {Y Z: Setoid}: Proper (eqv_on (Y-eqv->Z) ==> eqv ==> eqv) (@comp X Y Z).
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

#[export] Instance const_eqv {X} {Y: Setoid.ops}: Proper (eqv ==> eqv) (@const X Y).
Proof. move=>/=y y' yy' _/=. apply yy'. Qed.
#[export] Instance setoid_const_eqv {X} {Y: Setoid}: Proper (eqv ==> eqv_setoids) (@Setoid.const X Y) := const_eqv.

Goal Equivalence (@eqv (nat -> Prop)).
Proof. typeclasses eauto. Abort. (* needs the Hint Extern for Equivalence_eqv *)
Goal forall X: Setoid, forall h: X-eqv->X, forall x y: X, x ≡ y -> const x ≡ h.
Proof. intros * H. rewrite H -H. Abort. (* idem *)
Goal forall X: Setoid, forall h: X-eqv->X, forall x y: X, x ≡ y -> const x ≡[-eqv->] h.
Proof. intros * H. rewrite H -H. Abort. 


Check (bool * (unit -> dual nat) * sig (fun b: bool=> b=true)  (* * True *))%type: Setoid. 
Check (nat -> nat -> Prop): Setoid. 
Check (nat -eqv-> nat -eqv-> Prop): Setoid. 


(** * partial orders *)

(** ** class *)

Module PO.

 Structure ops := build_ {
    sort:> Type;
    #[canonical=no] eqv: relation sort;
    #[canonical=no] leq: relation sort;
 }.
 Arguments build_: clear implicits.
 Arguments eqv: clear implicits. 
 Arguments leq: clear implicits.
 Canonical Structure to_Setoid (X: ops) := Setoid.build _ (eqv X).
 #[reversible] Coercion to_Setoid: ops >-> Setoid.ops.
 
 (* Definition packager (T: Type) (eqv: relation T) (leq: relation T) := *)
 (*  [find o | @Setoid.eqv o ~ eqv | "misses setoid ops (or wrong eqv)" ] *)
 (*  build_ T eqv leq. *)
 (* Notation build T leq := (@packager T _ leq _ phant_id). *)
 Notation build T leq := (build_ T Setoid.eqv leq).
 Notation cast T o := (build_ T (eqv o) (leq o)) (only parsing). 
 
 Structure laws := validate {
    lsort:> ops;
    #[canonical=no] PreOrder_leq: PreOrder (leq lsort);
    #[canonical=no] eqv_of_leq: forall x y, x ≡ y <-> (leq lsort x y /\ leq lsort y x)
 }.
 Arguments validate _%type: clear implicits.
 Notation cast' o e := (validate o (PreOrder_leq e) (@eqv_of_leq e)) (only parsing). 

 Program Canonical Structure to_Setoid_laws (X: laws) := Setoid.validate (to_Setoid X) _.
 Next Obligation.
   pose proof (PreOrder_leq X). 
   constructor. 
   - move=>?. by setoid_rewrite eqv_of_leq. 
   - move=>??. by setoid_rewrite eqv_of_leq; tauto.
   - move=>? y?. by setoid_rewrite eqv_of_leq; split; transitivity y; tauto.
 Qed.
 (* #[reversible] Coercion to_Setoid_laws: laws >-> Setoid.laws. *)

 Structure morphism (X Y: ops) := build_morphism_ {
    body:> X -> Y;
    #[canonical=no] body_eqv: Proper (Setoid.eqv ==> Setoid.eqv) body;
    #[canonical=no] body_leq: Proper (leq X ==> leq Y) body;
 }.
 Arguments build_morphism_ {_ _}. 
 Program Definition build_morphism {X Y: laws} (f: X -> Y) H :=
   build_morphism_ f _ H.
 Next Obligation. move=>x y. setoid_rewrite eqv_of_leq=>xy. split; apply H; apply xy. Qed.
 Arguments build_morphism {_ _}. 

 Definition to_Setoid_morphism {X Y} (f: morphism X Y) :=
   Setoid.build_morphism f (body_eqv f).

 Canonical Structure id {X}: morphism X X :=
   build_morphism_ Datatypes.id _ _.
 Program Canonical Structure comp {X Y Z} (f: morphism Y Z) (g: morphism X Y): morphism X Z :=
   build_morphism_ (comp f g) _ _. 
 Next Obligation. move=>x y xy. apply f, g, xy. Qed.
 Next Obligation. move=>x y xy. apply f, g, xy. Qed.
 Program Canonical Structure const {X} {Y: laws} (y: Y): morphism X Y :=
   build_morphism_ (const y) _ _.
 Next Obligation. move=>/=_ _ _. apply PreOrder_leq. Qed.

End PO.
Notation PO := PO.laws.
Canonical PO.to_Setoid.
Canonical PO.to_Setoid_laws.
Canonical PO.to_Setoid_morphism.
Canonical PO.id.
Canonical PO.comp.
Canonical PO.const.
#[reversible] Coercion PO.to_Setoid: PO.ops >-> Setoid.ops.
(* #[reversible] Coercion PO.to_Setoid_laws: PO.laws >-> Setoid.laws. *)
#[reversible] Coercion PO.sort: PO.ops >-> Sortclass.
#[reversible] Coercion PO.lsort: PO.laws >-> PO.ops.
#[reversible] Coercion PO.to_Setoid_morphism: PO.morphism >-> Setoid.morphism.
#[reversible] Coercion PO.body: PO.morphism >-> Funclass.
Notation "X '-mon->' Y" := (PO.morphism X Y) (at level 99, Y at level 200).
Arguments PO.leq {_}.
Notation leq := PO.leq.
Notation eqv_of_leq := PO.eqv_of_leq.
Notation PreOrder_leq := PO.PreOrder_leq.
Notation body_leq := PO.body_leq.
(* #[export] Existing Instance PO.PreOrder_leq. *)
#[export] Hint Extern 0 (PreOrder leq) => apply: PO.PreOrder_leq: typeclass_instances.
#[export] Existing Instance PO.body_leq.
#[export] Instance rew_leq (X: PO): RewriteRelation (@leq X) := {}. 
Definition po_ops_on T (S: PO.ops) (_: T -> S) := S.
Definition po_laws_on T (S: PO.laws) (_: T -> S) := S.
Notation PO_ops_on T := (@po_ops_on T _ (fun x => x)).
Notation PO_laws_on T := (@po_laws_on T _ (fun x => x)).
Notation leq_on T := (@PO.leq (PO_ops_on T)). 
Infix "<=" := leq (at level 70).
Infix "<=[ X ]" := (@leq_on X) (at level 70).
Definition lt {X: PO} (x y: X) := x<=y /\ ~y<=x.
Notation lt_on T := (@lt (PO_ops_on T)). 
Infix "<" := lt (at level 70).
Infix "<[ X ]" := (@lt_on X) (at level 70).

(** ** basic properties *)

Section s.
 Context {X: PO}.
 Implicit Types x y: X.
 #[local] Instance PartialOrder_eqv_leq: PartialOrder (A:=X) eqv leq.
 Proof. move=> x y. apply eqv_of_leq. Qed.
 
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
#[export] Hint Extern 0 (PartialOrder _ leq) => apply: PartialOrder_eqv_leq: typeclass_instances.

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

Definition discrete_po_ (X: Setoid.ops) := PO.build X eqv.
Program Definition discrete_po_laws_ (X: Setoid):= PO.validate (discrete_po_ X) _ _.
Next Obligation. typeclasses eauto. Qed.
Next Obligation. by intuition symmetry. Qed.
Notation discrete_po X := (PO.cast X (discrete_po_ _)).
Notation discrete_po_laws X := (PO.cast' X (discrete_po_laws_ X%type)).

Canonical Structure unit_po := Eval hnf in discrete_po unit. 
Canonical Structure unit_po_laws := Eval hnf in discrete_po_laws unit.

Canonical Structure bool_po := Eval hnf in PO.build bool Bool.le.
Program Canonical Structure bool_po_laws := Eval hnf in PO.validate bool _ _.
Admit Obligations.

Canonical Structure nat_po := Eval hnf in PO.build nat Peano.le.
Program Canonical Structure nat_po_laws := Eval hnf in PO.validate nat _ _.
Admit Obligations.

Canonical Structure Prop_po := Eval hnf in PO.build Prop impl.
Program Canonical Structure Prop_po_laws := Eval hnf in PO.validate Prop _ _.
Next Obligation. split; cbv; tauto. Qed.

Canonical Structure prod_po (X Y: PO.ops) :=
  PO.build (X*Y) (fun p q => fst p <= fst q /\ snd p <= snd q).
Program Canonical Structure prod_po_laws (X Y: PO) :=
  Eval hnf in PO.validate (X*Y) _ _.
Next Obligation.
  constructor=>//.
  by move=>???[??][]; split; etransitivity; eassumption.
Qed.
Next Obligation.
  setoid_rewrite eqv_of_leq. tauto. 
Qed.

(* a clone of [prod_setoid] *)
Definition lex_prod := prod.
Canonical Structure lex_prod_setoid (X Y: Setoid.ops) :=
  Setoid.build (lex_prod X Y) (fun p q => fst p ≡ fst q /\ snd p ≡ snd q).
Canonical Structure lex_prod_setoid_laws (X Y: Setoid) :=
  Eval hnf in Setoid.validate (lex_prod X Y) (Setoid.Equivalence_eqv _).
  
Canonical Structure lex_prod_po (X Y: PO.ops) :=
  Eval hnf in PO.build (lex_prod X Y) (fun p q => fst p <= fst q /\ (fst q <= fst q -> snd p <= snd q)).
Program Canonical Structure lex_prod_po_laws (X Y: PO) :=
  Eval hnf in PO.validate (lex_prod X Y) _ _. 
Next Obligation.
  constructor=>//.
  move=>[x x'][y y'][z z']/=.
  intuition solve [transitivity y; auto|transitivity y'; auto].
Qed.
Next Obligation.
  setoid_rewrite eqv_of_leq. intuition.
Qed.
  
(* TODO: parallel and sequential sums, lists *)

Canonical Structure dprod_po A (X: A -> PO.ops) :=
  Eval hnf in PO.build (forall a, X a) (fun f g => forall a, f a <= g a).
Program Canonical Structure dprod_po_laws A (X: A -> PO) :=
  Eval hnf in PO.validate (forall a, X a) _ _.
Next Obligation.
  constructor.
  - by move=>??. 
  - by move=>??????; etransitivity; eauto.
Qed.
Next Obligation.
  setoid_rewrite eqv_of_leq. firstorder. 
Qed.

Definition kern_po_ A (X: PO.ops) (f: A -> X) :=
  PO.build_ (kern_setoid f) eqv (fun a b => f a <= f b).
Program Definition kern_po_laws_ A (X: PO) (f: A -> X) :=
  PO.validate (kern_po_ f) _ _.
Next Obligation.
  constructor.
  - by move=>//=. 
  - by move=>?????; etransitivity; eauto.
Qed.
Next Obligation.
  apply eqv_of_leq.
Qed.
Notation kern_po X f := (PO.cast X (kern_po_ f)).
Notation kern_po_laws X := (PO.cast' X (kern_po_laws_ _)).

Canonical Structure sig_po (X: PO.ops) (P: X -> Prop) := Eval hnf in kern_po (sig P) (@proj1_sig X P).
Canonical Structure sig_po_laws (X: PO) (P: X -> Prop) := Eval hnf in kern_po_laws (sig P). 

Canonical Structure setoid_morphisms_po X (Y: PO.ops) := Eval hnf in kern_po (X-eqv->Y) (@Setoid.body X Y). 
Canonical Structure setoid_morphisms_po_laws X (Y: PO) := Eval hnf in kern_po_laws (X-eqv->Y). 

Canonical Structure po_morphisms_setoid X Y := Eval hnf in kern_setoid (@PO.body X Y).
Canonical Structure po_morphisms_setoid_laws X (Y: PO) := Eval hnf in kern_setoid_laws (X-mon->Y).

Canonical Structure po_morphisms_po X Y := Eval hnf in kern_po (X-mon->Y) (@PO.body X Y). 
Canonical Structure po_morphisms_po_laws X (Y: PO) := Eval hnf in kern_po_laws (X-mon->Y). 

Notation leq_setoids := (@leq (setoid_morphisms_po _ _)). 
Notation eqv_pos := (@eqv (po_morphisms_setoid _ _)). 
Notation leq_pos := (@leq (po_morphisms_po _ _)). 
Infix "<=[-eqv->]" := (leq_setoids) (at level 70).
Infix "≡[-mon->]" := (eqv_pos) (at level 70).
Infix "<=[-mon->]" := (leq_pos) (at level 70).

Canonical Structure dual_po (X: PO.ops) :=
  Eval hnf in PO.build (dual X) (flip leq).
Program Canonical Structure dual_po_laws (X: PO) :=
  Eval hnf in PO.validate (dual X) _ _.
Next Obligation. typeclasses eauto. Qed.
Next Obligation. setoid_rewrite eqv_of_leq. tauto. Qed.

Program Canonical Structure dual_po_morphism {X Y: PO.ops} (f: X -mon-> Y): dual X -mon-> dual Y := PO.build_morphism_ f _ _.
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

Lemma comp_leq {X} {Y Z: PO}: Proper (leq_on (Y-mon->Z) ==> leq ==> leq) (@comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x=>/=. rewrite (gg' x). apply ff'. Qed.
Lemma comp_leq_eqv {X Y} {Z: PO}: Proper (leq_on (Y-eqv->Z) ==> eqv ==> leq) (@comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x=>/=. rewrite ->(gg' x). apply ff'. Qed. (* why the need for -> ? *)

#[export] Instance setoid_comp_eqv {X} {Y Z: Setoid}: Proper (eqv_setoids ==> eqv_setoids ==> eqv_setoids) (@Setoid.comp X Y Z) := comp_eqv.
#[export] Instance setoid_comp_leq {X Y} {Z: PO}: Proper (leq_setoids ==> eqv_setoids ==> leq_setoids) (@Setoid.comp X Y Z) := comp_leq_eqv.
#[export] Instance po_comp_leq {X Y Z: PO}: Proper (leq_pos ==> leq_pos ==> leq_pos) (@PO.comp X Y Z) := comp_leq.
#[export] Instance po_comp_eqv {X Y Z: PO}: Proper (eqv_pos ==> eqv_pos ==> eqv_pos) (@PO.comp X Y Z) := op_leq_eqv_2.

(* #[export] Existing Instance comp_eqv(* _ {X Y Z : Setoid}: *) *)
(* (* Proper (meqv ==> meqv ==> meqv) (@comp X Y Z) := comp_eqv *). *)
(* #[export] Existing Instance comp_leq. *)
(* #[export] Existing Instance comp_leq_eqv. *)


Goal forall X: Setoid, forall f g h: X -eqv-> X, f ≡ g -> f ° g ≡ h.
  Fail intros * ->.
Abort.
Goal forall X: Setoid, forall f g h: X -eqv-> X, f ≡ g -> f ° g ≡[-eqv->] h.
  intros * ->.
Abort.
Goal forall X: PO, forall f g h: X -eqv-> X, f ≡ g -> f ° g <=[-eqv->] h.
  intros * ->.
Abort.
Goal forall X: PO, forall f g h: X -mon-> X, f ≡ g -> f ° g ≡[-mon->] h.
  intros * ->.
Abort.
Goal forall X: PO, forall f g h: X -mon-> X, f ≡ g -> f ° g <=[-eqv->] h.
  Fail intros * ->.
  intros * H. rewrite (H: f≡[-eqv->]g). 
Abort.
Goal forall X: PO, forall f g h: X -mon-> X, f <= g -> f ° g <=[-mon->] h.
  intros * ->.
Abort. 
Goal forall X: PO, forall f g h: X -mon-> X, f ≡ g -> f ° g <=[-mon->] h.
  intros * ->.
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
#[export] Instance setoid_const_leq {X} {Y: PO}: Proper (leq ==> leq_setoids) (@Setoid.const X Y) := const_leq.
#[export] Instance po_const_leq {X} {Y: PO}: Proper (leq ==> leq_pos) (@PO.const X Y) := const_leq.
#[export] Instance po_const_eqv {X} {Y: PO}: Proper (eqv ==> eqv_pos) (@PO.const X Y) := const_eqv.


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

Check fun X: PO => PO_laws_on (dual X). 
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

Fail Check fun (X: PO) (f: X-mon->X) => Datatypes.id <= f.
Check fun (X: PO) (f: X-mon->X) => Datatypes.id <=[-mon->] f. 
Check fun (X: PO) (f: X-mon->X) => Datatypes.id <=[_-eqv->_] f. 
Fail Check fun (X: PO) (f: X-mon->X) => Datatypes.id <=[_->_] f. 
Check fun (X: PO) (f: X-mon->X) => Datatypes.id <=[X->X] f. 
Fail Check fun (X: PO) (f: X-mon->X) => Datatypes.id ≡ f. 
Fail Check fun (X: PO) (f: X-eqv->X) => Datatypes.id <= f. 
Fail Check fun (X: PO) (f: X-eqv->X) => Datatypes.id ≡ f. 
Fail Check fun (X: PO) (f: X->X) => Datatypes.id <= f. 
Fail Check fun (X: PO) (f: X->X) => Datatypes.id ≡ f. 
Fail Check fun (X: Setoid) (f: X-eqv->X) => Datatypes.id ≡ f. 
Fail Check fun (X: Setoid) (f: X->X) => Datatypes.id ≡ f. 

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

Goal forall X: Setoid, forall f: X -eqv-> X, forall x y: X, x≡y -> f (f x) ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  

Goal forall X: Setoid, forall f: X -eqv-> X, forall x y: X, x≡y -> (f ° f) x ≡ f (f x).
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


Section s.

Context {X: PO.ops}.
Implicit Types x y: X.  
Implicit Types P Q: X->Prop.  

Definition directed P := forall x y, P x -> P y -> exists z, P z /\ x <= z /\ y <= z.
Definition chain P := forall x y, P x -> P y -> x <= y \/ y <= x.

Definition covered P Q := forall x, P x -> exists y, Q y /\ x <= y.
Definition bicovered P Q := covered P Q /\ covered Q P.

Definition is_sup P x := forall z, x <= z <-> forall y, P y -> y <= z.
Definition is_inf P x := forall z, z <= x <-> forall y, P y -> z <= y.

Definition sup_closed P := forall Q, Q <= P -> forall z, is_sup Q z -> P z.
Definition inf_closed P := forall Q, Q <= P -> forall z, is_inf Q z -> P z.

End s.
Definition cocovered {X: PO.ops} (P Q: X -> Prop) := @covered (dual X) P Q.
Definition cobicovered {X: PO.ops} (P Q: X -> Prop) := @bicovered (dual X) P Q.

Notation downward_closed := (Proper (leq ==> impl)). 
Notation upward_closed := (Proper (leq --> impl)). 

Section s.
Context {X: PO}.
Implicit Types x y: X.  
Implicit Types P Q: X->Prop.  

#[export] Instance PreOrder_covered: PreOrder (@covered X).
Proof.
  constructor.
  - by move=>P x Px; eauto.
  - move=>P Q R PQ QR x Hx. 
    case: (PQ x Hx)=>[y [Hy xy]]. 
    case: (QR y Hy)=>[z [Hz yz]].
    exists z. split=>//. by transitivity y.
Qed.
#[export] Instance Equivalence_bicovered: Equivalence (@bicovered X).
Proof.
  constructor.
  - split; reflexivity. 
  - move=>??. unfold bicovered; tauto.
  - move=>f g h [??] [??]. split; by transitivity g.
Qed.
#[export] Instance PartialOrder_covered: RelationClasses.PartialOrder (@bicovered X) covered.
Proof. by []. Qed.
(* TOTHINK: declare [subrelation] instances? *)
Lemma leq_covered P Q: P <= Q -> covered P Q.
Proof. move=>H x Px. exists x; split=>//. by apply H. Qed.
Lemma eqv_covered P Q: P ≡ Q -> bicovered P Q.
Proof. by rewrite eqv_of_leq; move=>[??]; split; apply leq_covered. Qed.


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

#[export] Instance Proper_is_sup: Proper (@bicovered X ==> eqv ==> eqv) is_sup.
Proof.
  rewrite /is_sup=> P Q PQ x y xy.
  apply Proper_forall=>z. apply Proper_iff. by rewrite xy.
  have E: forall P Q, covered P Q -> (forall t, Q t -> t <= z) <= (forall t, P t -> t <= z).
   clear=>P Q PQ H t Pt. by case: (PQ _ Pt)=>s [? ->]; apply H. 
  split; apply E; apply PQ. 
Qed.

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

Lemma chain_directed P: chain P -> directed P.
Proof. move=>H x y Px Py; by case:(H _ _ Px Py); eauto. Qed.

End s.

Section s.
Context {X: PO}.
Implicit Types x y: X.
Implicit Types P Q: X -> Prop.

Lemma leq_from_below x y: (forall z, z <= x -> z <= y) -> x <= y.
Proof. apply (@leq_from_above (dual X)). Qed.
Lemma from_below x y: (forall z, z <= x <-> z <= y) -> x ≡ y.
Proof. apply (@from_above (dual X)). Qed.

Lemma geq_is_inf P x: is_inf P x -> forall y, P y -> x <= y.
Proof. apply (@leq_is_sup (dual X)). Qed.
Lemma is_inf_leq P p Q q: is_inf P p -> is_inf Q q -> cocovered P Q -> q<=p.
Proof. apply (@is_sup_leq (dual X)). Qed.
Lemma is_inf_eqv P p Q q: is_inf P p -> is_inf Q q -> cobicovered P Q -> p≡q.
Proof. apply (@is_sup_eqv (dual X)). Qed.
Lemma infU P x y: is_inf P x -> is_inf P y -> x ≡ y.
Proof. apply (@supU (dual X)). Qed.

Lemma inf_closed_impl P Q: downward_closed P -> inf_closed Q -> inf_closed (fun x => P x -> Q x).
Proof. apply (@sup_closed_impl (dual X)). Qed.

Lemma inf_closed_leq (f: X -mon-> X): inf_closed (fun x => f x <= x).
Proof. apply (@sup_closed_leq (dual X) (dual_po_morphism f)). Qed.

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
  is_sup (image f P) (f a) -> is_sup (X:=kern_po_laws_ f) P a.
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

Record level := mk_level { has_E: bool; has_B: bool; has_C: bool; has_D: bool; has_A: bool}.
Declare Scope level_scope.
Bind Scope level_scope with level.
Delimit Scope level_scope with level.
Notation "a &&& b" := (if a then b else false) (at level 60): bool_scope. 
Notation "a ||| b" := (if a then true else b) (at level 60): bool_scope. 
Notation "a ==> b" := (if a then b else true): bool_scope. 
Definition leq_level h h' :=
  let 'mk_level e b c d a := h in
  let 'mk_level e' b' c' d' a' := h' in
  (e==>e' &&& b==>b' &&& c==>c' &&& d==>d' &&& a==>a')%bool.
Class lower h k := Lower: is_true (leq_level h k).
Infix "<<" := lower (at level 70). 
#[export] Instance PreOrder_lower: PreOrder lower.
Admitted.
Ltac solve_lower :=
  solve [ reflexivity | assumption |
          match goal with H: ?h << ?l |- ?k << ?l => transitivity h; [reflexivity|exact H] end].
#[export] Hint Extern 0 (_ << _) => solve_lower: typeclass_instances.
Definition cup_level h h' :=
  let 'mk_level e b c d a := h in
  let 'mk_level e' b' c' d' a' := h' in
  mk_level (e|||e') (b|||b') (c|||c') (d|||d') (a|||a').
Infix "+" := cup_level: level_scope.
Section levels.
Notation "1" := true.
Notation "0" := false.
Definition lE := mk_level 1 0 0 0 0.
Definition lB := mk_level 0 1 0 0 0.
Definition lC := mk_level 1 0 1 0 0.
Definition lD := mk_level 1 0 1 1 0.
Definition lA := mk_level 1 1 1 1 1.
End levels.

Goal lE << lA. typeclasses eauto. Qed.
Goal forall l, lE+lB << l -> lB << l. typeclasses eauto. Qed.

Variant K := kE | kB | kC | kD | kA.
Coercion level_for k := match k with kE => lE | kB => lB | kC => lC | kD => lD | kA => lA end.
Definition args k (X: PO.ops): Type :=
  match k with
  | kE => unit
  | kB => X * X
  | kC => sig (@chain X)
  | kD => sig (@directed X)
  | kA => (X -> Prop)
  end.
Definition setof {X: PO.ops} k: args k X -> X -> Prop :=
  match k with
  | kE => fun _ => empty
  | kB => fun p => pair (fst p) (snd p)
  | kC => @proj1_sig _ _
  | kD => @proj1_sig _ _
  | kA => fun P => P
  end.

Module GPO.

 Structure ops l := build_ {
    sort:> Type;
    #[canonical=no] eqv: relation sort;
    #[canonical=no] leq: relation sort;
    #[canonical=no] gsup: forall k: K, k << l -> args k (PO.build_ sort eqv leq) -> sort;
 }.
 Arguments build_ {_}.
 Arguments eqv {_}. 
 Arguments leq {_}.
 Arguments gsup {_ _}. 
 Canonical Structure to_Setoid l (X: ops l) := Setoid.build _ (eqv X).
 Canonical Structure to_PO l (X: ops l) := PO.build (@sort l X) (leq X).
 #[reversible] Coercion to_Setoid: ops >-> Setoid.ops.
 #[reversible] Coercion to_PO: ops >-> PO.ops.
 
 (* Definition packager (T: Type) (eqv: relation T) (leq: relation T) := *)
 (*  [find o | @Setoid.eqv o ~ eqv | "misses setoid ops (or wrong eqv)" ] *)
 (*  build_ T eqv leq. *)
 (* Notation build T leq := (@packager T _ leq _ phant_id). *)
 Notation build T gsup := (build_ T Setoid.eqv PO.leq gsup).
 Notation cast T o := (build_ T (eqv o) (leq o) (@gsup _ o)) (only parsing). 

 Structure laws l := validate_ {
    lsort:> ops l;
    #[canonical=no] PreOrder_leq: PreOrder (@PO.leq lsort);
    #[canonical=no] eqv_of_leq: forall x y, x ≡ y <-> (@PO.leq lsort x y /\ @PO.leq lsort y x);
    #[canonical=no] gsup_spec: forall k, forall kl, forall x: args k lsort, is_sup (setof x) (gsup k kl x)
 }.
 Arguments validate_ {_} _%type.
 Notation cast' o X := (validate_ o (@PreOrder_leq _ X) (@eqv_of_leq _ X) (@gsup_spec _ X)) (only parsing). 
 Notation validate X H := (validate_ X%type (@PO.PreOrder_leq X%type) (@PO.eqv_of_leq X%type) H).
 Notation validate' X X' H := (validate_ X' (@PO.PreOrder_leq X%type) (@PO.eqv_of_leq X%type) H).
  
 Canonical Structure to_PO_laws l (X: laws l) := PO.validate X (@PreOrder_leq _ X) (@eqv_of_leq _ X).
 Canonical Structure to_Setoid_laws l (X: laws l) := Setoid.cast X (PO.to_Setoid_laws _). 
 (* #[reversible] Coercion to_PO_laws: laws >-> PO.laws. *)
 (* #[reversible] Coercion to_Setoid_laws: laws >-> Setoid.laws. *)

(*  Definition build (l: level) (X: PO) := *)
(*   let '@PO.pack T M N := X return *)
(*                            forall gsup: (forall k: K, k << l -> args k X -> X), *)
(*                              (forall k kl x, is_sup (setof k x) (gsup k kl x)) -> type l in *)
(*   fun gsup gsup_spec => @pack l T M N (@from_po l T M N gsup gsup_spec). *)
(* Arguments build _ [_]. *)
End GPO.
Notation GPO := GPO.laws.

Canonical GPO.to_Setoid.
Canonical GPO.to_PO.
Canonical GPO.to_Setoid_laws.
Canonical GPO.to_PO_laws.
#[reversible] Coercion GPO.to_Setoid: GPO.ops >-> Setoid.ops.
#[reversible] Coercion GPO.to_PO: GPO.ops >-> PO.ops.
#[reversible] Coercion GPO.sort: GPO.ops >-> Sortclass.
#[reversible] Coercion GPO.lsort: GPO.laws >-> GPO.ops.
Definition gsup {l} {X: GPO.ops l} k kl: args k X -> X := GPO.gsup k kl.
Arguments gsup {_ _}. 
Definition gsup_spec {l} {X: GPO l} k kl: forall x: args k X, is_sup (setof x) (gsup k kl x) := GPO.gsup_spec kl.
Definition gpo_ops_on T l (S: GPO.ops l) (_: T -> S) := S.
Definition gpo_laws_on T l (S: GPO.laws l) (_: T -> S) := S.
Notation GPO_ops_on T l := (@po_ops_on T l _ (fun x => x)).
Notation GPO_laws_on T l := (@po_laws_on T l _ (fun x => x)).

Lemma leq_gsup {l} {X: GPO l} k kl x (y: X): setof x y -> y <= gsup k kl x.
Proof. apply leq_is_sup, gsup_spec. Qed.

Definition bot {l} {X: GPO.ops l} {L: lE << l}: X := gsup kE L tt. 
Definition cup {l} {X: GPO.ops l} {L: lB << l} (x y: X): X := gsup kB L (x,y).
Definition csup {l} {X: GPO.ops l} {L: lC << l} (P: X -> Prop) (C: chain P): X := gsup kC L (exist _ P C).
Definition dsup {l} {X: GPO.ops l} {L: lD << l} (P: X -> Prop) (D: directed P): X := gsup kD L (exist _ P D). 
Definition sup {l} {X: GPO.ops l} {L: lA << l}: (X -> Prop) -> X := gsup kA L. 
Infix "⊔" := cup (left associativity, at level 50). 
Arguments csup {_ _ _}. 
Arguments dsup {_ _ _}. 

Lemma is_sup_bot {l} {X: GPO l} {L: lE << l}: is_sup (@empty X) bot.
Proof. apply: gsup_spec. Qed.
Lemma is_sup_cup {l} {X: GPO l} {L: lB << l} (x y: X): is_sup (pair x y) (x ⊔ y).
Proof. apply: gsup_spec. Qed.
Lemma is_sup_csup {l} {X: GPO l} {L: lC << l} (P: X -> Prop) C: is_sup P (csup P C).
Proof. apply: gsup_spec. Qed.
Lemma is_sup_dsup {l} {X: GPO l} {L: lD << l} (P: X -> Prop) D: is_sup P (dsup P D).
Proof. apply: gsup_spec. Qed.
Lemma is_sup_sup {l} {X: GPO l} {L: lA << l} (P: X -> Prop): is_sup P (sup P).
Proof. apply: gsup_spec. Qed.

Lemma leq_csup {l} {X: GPO l} {L: lC << l} (P: X -> Prop) C x: P x -> x <= csup P C. 
Proof. move=>Px. by apply: leq_gsup. Qed.
Lemma leq_dsup {l} {X: GPO l} {L: lD << l} (P: X -> Prop) D x: P x -> x <= dsup P D. 
Proof. move=>Px. by apply leq_gsup. Qed.
Lemma leq_sup {l} {X: GPO l} {L: lA << l} (P: X -> Prop) x: P x -> x <= sup P. 
Proof. move=>Px. by apply leq_gsup. Qed.


Lemma cup_spec {l} {X: GPO l} {L: lB << l} (x y z: X): x ⊔ y <= z <-> x <= z /\ y <= z.
Proof. rewrite is_sup_cup /pair; intuition subst; auto. Qed.

Lemma cupA {l} {X: GPO l} {L: lB << l} (x y z: X): x ⊔ (y ⊔ z) ≡ x ⊔ y ⊔ z. 
Proof. apply: from_above=>t. rewrite 4!cup_spec. tauto. Qed.

Lemma csup_empty {l} {X: GPO l} {L: lC << l} C: csup empty C ≡[X] bot.
Proof. apply: supU. apply is_sup_csup. apply is_sup_bot. Qed.
Lemma dsup_empty {l} {X: GPO l} {L: lD << l} D: dsup empty D ≡[X] bot.
Proof. apply: supU. apply is_sup_dsup. apply is_sup_bot. Qed.
Lemma sup_empty {l} {X: GPO l} {L: lA << l}: sup empty ≡[X] bot.
Proof. apply: supU. apply is_sup_sup. apply is_sup_bot. Qed.
Lemma sup_pair {l} {X: GPO l} {L: lA << l} (x y: X): sup (pair x y) ≡ x ⊔ y.
Proof. apply: supU. apply is_sup_sup. apply is_sup_cup. Qed.



Lemma discriminate {P: Type}: is_true false -> P.
Proof. by []. Qed.
  
Program Canonical Structure bool_gpo: GPO.ops (lE+lB) := Eval hnf in 
  GPO.build bool
    (fun k => match k with
           | kE => fun _ _ => false
           | kB => fun _ '(x,y) => orb x y
           | kC | kD | kA  => discriminate
           end).
Program Canonical Structure bool_gpo_laws := GPO.validate bool _.
Next Obligation. revert kl x; case k=>//=_ [x y]/=. Admitted.  

Program Canonical Structure nat_gpo: GPO.ops (lE+lB) := Eval hnf in 
  GPO.build nat
    (fun k => match k with
           | kE => fun _ _ => O
           | kB => fun _ '(x,y) => Peano.max x y
           | kA | kC | kD => discriminate
           end).
Program Canonical Structure nat_gpo_laws := GPO.validate nat _.
Next Obligation.
  revert kl x; case k=>//=_.
  - move=>_. admit.
  - move=>[n m]/=. admit.
Admitted.

Program Canonical Structure Prop_gpo: GPO.ops (lE+lB+lA) := Eval hnf in 
  GPO.build Prop
    (fun k => match k with
           | kE => fun _ _ => False
           | kB => fun _ '(p,q) => p\/q
           | kC => fun _ P => exists2 p, proj1_sig P p & p
           | kD => fun _ P => exists2 p, proj1_sig P p & p
           | kA => fun _ P => exists2 p, P p & p
           end).
Program Canonical Structure Prop_gpo_laws := GPO.validate Prop _.
Next Obligation.
  revert kl x; case k=>//=_; try solve [cbv; firstorder].
  case. cbv; firstorder subst; eauto.
Qed.

Section map_args.
 Context {X Y: PO.ops}.
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
 Lemma setof_map_args k: forall x: args k X, setof (map_args x) ≡ image f (setof x).
 Proof. case: k=>/=[_|[x x']|[P C]|[P D]|P]//=; firstorder congruence. Qed. 
End map_args.

Definition app {A} {X: A -> PO.ops} a: (forall a, X a)-mon->X a :=
  PO.build_morphism_ (fun f => f a) (fun f g fg => fg a) (fun f g fg => fg a).

(** GPOs on dependent products *)
Program Canonical Structure dprod_gpo {A l} (X: A -> GPO.ops l): GPO.ops l :=
  Eval hnf in GPO.build (forall a, X a) (fun k kl F a => gsup k kl (map_args (app a) F)). 
Program Canonical Structure dprod_gpo_laws {A l} (X: A -> GPO l): GPO l :=
  Eval hnf in GPO.validate (forall a, X a) _. 
Next Obligation.
  apply: dprod_sup=>a. eapply Proper_is_sup.
  2: reflexivity. 2: apply: gsup_spec.
  apply: eqv_covered. by rewrite setof_map_args.  
Qed.

Program Definition proj1_sig_mon {X: PO.ops} (P: X -> Prop): sig P -mon-> X :=
  PO.build_morphism_ (@proj1_sig _ _) _ _.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.

(** sub-GPOs *)
Section sub.
 Context {l} {X: GPO.ops l}.
 Variable P: X -> Prop.
 Definition sup_closed' :=
   forall k: K, forall kl: k<<l, forall x: args k X, setof x <= P ->  P (gsup k kl x).
 Program Definition sig_gpo (Psup: sup_closed'): GPO.ops l := Eval hnf in
   GPO.build (sig P) (fun k kl F => exist _ (gsup k kl (map_args (proj1_sig_mon P) F)) _). 
 Next Obligation.
   apply: Psup. rewrite setof_map_args. 
   by move=>_ [[x Px] [_ ->]]. 
 Qed.
End sub. 
Section sub.
 Context {l} {X: GPO l}.
 Variable P: X -> Prop.
 Program Definition sig_gpo_laws (Psup: sup_closed' P): GPO l := Eval hnf in
   GPO.validate' (sig P) (sig_gpo Psup) _. 
 Next Obligation.
   apply: kern_sup=>/=. eapply Proper_is_sup.
   2: reflexivity. 2: apply: gsup_spec.
   apply eqv_covered. by rewrite setof_map_args. 
 Qed.
 Lemma sup_closed_sup_closed': sup_closed P -> sup_closed' P. 
 Proof. move=>H k kl x Hx. apply: H. apply Hx. apply gsup_spec. Qed.
End sub.

(** GPOs from retractions (and thus isomorphisms given the induced order on [A]) *)
Section c.
 Context {A: Type} {l} {X: GPO.ops l}.
 Variable r: A->X.               (* retraction *)
 Variable i: X->A.               (* section *)
 Program Let r': kern_po A r -mon-> X := PO.build_morphism_ r _ _.
 Next Obligation. by []. Qed.
 Next Obligation. by []. Qed.
 Program Definition retract_gpo: GPO.ops l := Eval hnf in 
     GPO.build (kern_po A r) (fun k kl x => i (gsup k kl (map_args r' x))).
End c. 
Section c.
 Context {A: Type} {l} {X: GPO l}.
 Variable r: A->X.               (* retraction *)
 Variable i: X->A.               (* section *)
 Hypothesis ri: r°i ≡ id. 
 Program Definition retract_gpo_laws: GPO l := Eval hnf in 
     GPO.validate' (kern_po_laws (kern_po A r)) (retract_gpo r i) _.
 Next Obligation.
   apply kern_sup. eapply Proper_is_sup. 2: apply ri. 2: apply: gsup_spec.
   apply eqv_covered. by rewrite setof_map_args.
 Qed.
End c.

(** altogether, we get general sub-GPOs  *)
Section c.
 Context {A: Type} {l} {X: GPO.ops l} (P: X -> Prop).
 Variable r: A->sig P.
 Variable i: sig P->A.
 Hypothesis Psup: sup_closed' P.
 Definition sub_gpo: GPO.ops l := Eval hnf in retract_gpo (X:=sig_gpo Psup) r i. 
End c. 
Section c.
 Context {A: Type} {l} {X: GPO l} (P: X -> Prop).
 Variable r: A->sig P.
 Variable i: sig P->A.
 Hypothesis ri: r°i ≡ id. 
 Hypothesis Psup: sup_closed' P.
 Definition sub_gpo_laws: GPO l := Eval hnf in retract_gpo_laws (X:=sig_gpo_laws Psup) ri. 
End c. 

(** the GPO of monotone functions *)
Section s.
 Context {X: PO} {l} {Y: GPO l}. (* TOTHINK: start from ops only? *)
 Program Canonical Structure mon_gpo: GPO.ops l :=
   Eval hnf in GPO.cast (X-mon->Y)
                 (sub_gpo (X:=X->Y)
                 (fun f: X-mon->Y => exist (Proper (leq ==> leq)) (PO.body f) (@body_leq _ _ f))
                 (fun f: sig (Proper (leq ==> leq)) => PO.build_morphism _ (proj2_sig f)) _).
 Next Obligation.
   move=>k kl P HP x y xy.
   apply gsup_spec=>z Hz. apply setof_map_args in Hz as [f [Hf ->]].
   transitivity (f y). apply (HP _ Hf _ _ xy). apply leq_gsup. 
   apply setof_map_args. by exists f.
 Qed.
 Program Canonical Structure mon_gpo_laws: GPO l :=
   Eval hnf in let e := sub_gpo_laws _ _ in GPO.cast' (X-mon->Y) e.
 Next Obligation. revert a0. by change (a≡a). Qed. (* TOFIX *)
End s.


(*
(** * dCPOs *)

Module dCPO.
Record mixin X (M: Setoid.mixin X) (N: PO.mixin M) := from_po {
    dsup: forall D: X -> Prop, @directed (PO.pack N) D -> X;
    dsup_spec: forall D DD, @is_sup (PO.pack N) D (@dsup D DD);
}.
Structure type := pack {
    sort:> Type;
    #[canonical=no] setoid_mix: Setoid.mixin sort;
    #[canonical=no] po_mix: PO.mixin setoid_mix;
    #[canonical=no] mix: mixin po_mix;
}.
Canonical Structure to_PO (X: type): PO := PO.pack (po_mix X). 
Canonical Structure to_Setoid (X: type): Setoid := Setoid.pack (setoid_mix X). 
#[reversible] Coercion to_PO: type >-> PO.
#[reversible] Coercion to_Setoid: type >-> Setoid.
Definition build (X: PO) :=
  let '@PO.pack T M N := X return
                             forall dsup: (forall D: X -> Prop, @directed X D -> X),
                              (forall D DD, @is_sup X D (@dsup D DD)) -> type in
  fun dsup dsup_spec => @pack T M N (@from_po T M N dsup dsup_spec).
Arguments build [_].
End dCPO.
Notation dCPO := dCPO.type.
Canonical dCPO.to_PO.
Canonical dCPO.to_Setoid.
#[reversible] Coercion dCPO.to_Setoid: dCPO >-> Setoid.
#[reversible] Coercion dCPO.to_PO: dCPO >-> PO.
#[reversible] Coercion dCPO.sort: dCPO >-> Sortclass.
Definition dsup {X: dCPO} := dCPO.dsup (dCPO.mix X).
Arguments dsup {_}. 
Definition dsup_spec {X: dCPO}: forall D DD, @is_sup X D (@dsup X D DD) := dCPO.dsup_spec (dCPO.mix X).
Definition dcpo_on T (S: dCPO) (_: T -> S) := S.
Notation dCPO_on T := (@dcpo_on T _ (fun x => x)).

Lemma leq_dsup {X: dCPO} (P: X -> Prop) D: forall y, P y -> y <= dsup P D.
Proof. apply leq_sup, dsup_spec. Qed.

Program Canonical Structure dprod_dCPO {A} (X: A -> dCPO) :=
  @dCPO.build (forall a, X a) (fun F DF a => dsup (image (fun f => f a) F) _) _.
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

Section c.
 Context {A: Type} {X: dCPO}.
 Variable f: A->X.
 Variable from_sup: forall (P: A -> Prop) x, directed (image f P) -> is_sup (image f P) x -> A.
 Hypothesis f_from_sup: forall P x DfP (fPx: is_sup (image f P) x), f (from_sup DfP fPx) ≡ x.
 Program Definition kern_dCPO: dCPO :=
   @dCPO.build (kern_po X f)
               (fun P D =>
                  let D' := _: directed (image f P) in
                  from_sup D' (@dsup_spec _ (image f P) D')) _.
 Next Obligation.
   move=>??[a [Pa ->]][b [Pb ->]]. case: (D _ _ Pa Pb)=>/=[c [Pc [ab ac]]].
   exists (f c). split. by exists c. by split.
 Qed.
 Next Obligation.
   move=>/=a. cbn. rewrite f_from_sup. rewrite dsup_spec=>/=. apply forall_image. 
 Qed.
End c. 


(** * CPOs *)

Module CPO.
Record mixin X (M: Setoid.mixin X) (N: PO.mixin M) := from_po {
    csup: forall D: X -> Prop, @chain (PO.pack N) D -> X;
    csup_spec: forall D DD, @is_sup (PO.pack N) D (@csup D DD);
}.
Structure type := pack {
    sort:> Type;
    #[canonical=no] setoid_mix: Setoid.mixin sort;
    #[canonical=no] po_mix: PO.mixin setoid_mix;
    #[canonical=no] mix: mixin po_mix;
}.
Canonical Structure to_PO (X: type): PO := PO.pack (po_mix X). 
Canonical Structure to_Setoid (X: type): Setoid := Setoid.pack (setoid_mix X). 
#[reversible] Coercion to_PO: type >-> PO.
#[reversible] Coercion to_Setoid: type >-> Setoid.
Definition build (X: PO) :=
  let '@PO.pack T M N := X return
                             forall csup: (forall D: X -> Prop, @chain X D -> X),
                              (forall D DD, @is_sup X D (@csup D DD)) -> type in
  fun csup csup_spec => @pack T M N (@from_po T M N csup csup_spec).
Arguments build [_].
End CPO.
Notation CPO := CPO.type.
Canonical CPO.to_PO.
Canonical CPO.to_Setoid.
#[reversible] Coercion CPO.to_Setoid: CPO >-> Setoid.
#[reversible] Coercion CPO.to_PO: CPO >-> PO.
#[reversible] Coercion CPO.sort: CPO >-> Sortclass.
Definition csup {X: CPO} := CPO.csup (CPO.mix X).
Arguments csup {_}. 
Definition csup_spec {X: CPO}: forall D DD, @is_sup X D (@csup X D DD) := CPO.csup_spec (CPO.mix X).
Definition cpo_on T (S: CPO) (_: T -> S) := S.
Notation CPO_on T := (@cpo_on T _ (fun x => x)).

Lemma leq_csup {X: CPO} (P: X -> Prop) D: forall y, P y -> y <= csup P D.
Proof. apply leq_sup, csup_spec. Qed.

Program Canonical Structure dprod_CPO {A} (X: A -> CPO) :=
  @CPO.build (forall a, X a) (fun F CF a => csup (image (fun f => f a) F) _) _.
Next Obligation.
  move=>/=_ _ [g [G ->]] [h [H ->]].
  case: (CF _ _ G H)=>E;[left|right]; apply E.
Qed.
Next Obligation.
  move=>/=f. split=>H.
  - move=>g G. rewrite -H=>a. apply leq_csup. by exists g.
  - move=>a. apply csup_spec=>/=_ [g [G ->]]. by apply H. 
Qed.
*)

(** * chain construction *)

Module Chain.
Section c.
 Context {X: PO}.               (* TOTHINK: just ops? *)
 Section d.
 Variable f: X -> X.

 (** the set of all (transfinite) iterations of f *)
 Inductive C: X -> Prop :=
 | Cf: forall x, C x -> C (f x)
 | Csup: forall P, P <= C -> forall x, is_sup P x -> C x.
 
 (** a type for the elements of the chain *)
 Structure Chain := chn { elem:> X; #[canonical=no] Celem: C elem}.

 (** the chain inherits the partial order structure from X *)
 Canonical Structure Chain_setoid := Eval hnf in kern_setoid elem.
 Canonical Structure Chain_setoid_laws := Eval hnf in kern_setoid_laws Chain.
 Canonical Structure Chain_po := Eval hnf in kern_po Chain elem.
 Canonical Structure Chain_po_laws := Eval hnf in kern_po_laws Chain.

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
   - move: (Pnext (chn Cx) (IH _)). apply sup_closed_Proper=>//. by change (f x ≡ f x). (* argh *)
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
   - move: T {TC} IH t Ht. apply: (sup_closed_leq (f:=const x)). 
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
   apply (lpfp_of_chain_prefixpoint (c:=chn Cc))=>/=. 
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
 Context {l} {X: GPO l}.
 Variable f: X->X.
 Canonical Structure Chain_gpo: GPO.ops l :=
   Eval hnf in GPO.cast (Chain f)
                 (sub_gpo (X:=X)
                 (fun c: Chain f => exist (C f) (elem c) (Celem c))
                 (fun p: sig (C f) => chn (proj2_sig p))
                 (sup_closed_sup_closed' (@Csup _ f))).
 Program Canonical Structure Chain_gpo_laws: GPO l :=
   Eval hnf in let e := sub_gpo_laws _ _ in GPO.cast' (Chain f) e.
 Next Obligation. by change (a≡a). Qed.
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
Arguments choose_gen {_}. 
Arguments choose {_}. 


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
   revert z. apply: tower. apply (sup_closed_leq (f:=const x)).
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

 Context {l} {X: GPO l} {L: lC<<l}.
 Variable f: X -eqv-> X. 
 Hypothesis f_ext: forall x, x <= f x.
 
 Lemma chain_C: chain (C f).
 Proof.
   move=>x y Cx Cy.
   apply: (total_chain (tower f) _ (chn Cx) (chn Cy)).
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
 Proof. apply (BourbakiWitt.ptower tower id_next). Qed.

 (** there is at most one prefixpoint, which must be a top element  *)
 Lemma prefixpoint_top x: next x <= x -> is_sup (fun _ => True) x.
 Proof.
   move=>H y. split; auto=>xy z _. rewrite -xy. clear y xy.
   revert z. apply: tower. apply (sup_closed_leq (f:=const x)).
   by move=>y /=->.            (* TOTHINK: avoid /= ? *)
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
   exact (BourbakiWitt.total_chain tower id_next).
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
     -- move=>[t [ty xt]]. left. by rewrite /=xt. (* TOTHINK: avoid /= ? *)
 Qed.

End b.
Section b.

 Context {l} {X: GPO l} {L: lC<<l}.
 Variable f: X -mon-> X. 

 Lemma chain_C: chain (C f).
 Proof.
   move=>x y Cx Cy.
   exact: (total_chain (tower f) (chn Cx) (chn Cy)).
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
 Context {l} {C: GPO l} {L: lD<<l}.

 (** the largest monotone and extensive function on [C] *)
 Program Definition h: C-mon->C := dsup (fun f => PO.id <= f) _.
 Next Obligation.
   change (directed (fun f => @PO.id C <= f)). (* argh: Program unfolds too much *)
   move=>i j I J. exists (PO.comp i j). split; last split.
   - by rewrite -I.
   - by rewrite -J.
   - by rewrite -I.
 Qed.
 
 Lemma h_ext: PO.id <= h.
 Proof. by apply: leq_dsup. Qed.

 Lemma h_invol: h ° h <=[-mon->] h.
 Proof.
   apply: leq_dsup.
   by rewrite -h_ext.
 Qed.

 Definition extensive_fixpoint := locked (h bot).

 Variable f: C-mon->C.
 Hypothesis f_ext: PO.id <= f. 
 
 Lemma h_prefixpoint: f ° h <=[-mon->] h.
 Proof. apply: leq_dsup. by rewrite -f_ext -h_ext. Qed.

 Theorem is_extensive_fixpoint: f extensive_fixpoint ≡ extensive_fixpoint. 
 Proof. apply antisym. unlock extensive_fixpoint. apply h_prefixpoint. apply f_ext. Qed.
End s.

Section s.
 Context {l} {X: GPO l} {L: lD<<l}.
 Variable f: X-mon->X.

 Definition lfp := locked (extensive_fixpoint (C:=Chain f): X).
   
 Theorem is_least_fixpoint: is_lfp f lfp. 
 Proof.
   unlock lfp.
   apply lpfp_of_chain_prefixpoint. 
   apply eqv_leq.
   exact (is_extensive_fixpoint (chain_postfixpoint (f:=f))).
 Qed.

 (* note: we could also prove that [C f] admits a supremum and is thus trivially directed, 
    so that we could define [lfp] as [dsup (C f) _], uniformly with the definitions in [Bourbakiwitt'.lfp]

    we proceed more directly, and prove a posteriori that [lfp] as defined above is indeed the sup of [C f] *)
 Proposition lfp_is_sup_C: is_sup (C f) lfp. 
 Proof.
   move=>x. split=>H.
   - move=>c Cc. rewrite -H.
     apply: (chain_below_prefixpoints (f:=f) _ (chn Cc)).
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

(* time coqc split.v: 4.2s *)
