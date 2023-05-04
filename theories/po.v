Require Import ssreflect ssrfun ssrbool.
Require Export setoid.
Require Eqdep_dec.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

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
Notation cast T X := (let X':=X in @pack T _ (mix X')).
Notation build T leq H H' :=
  (let X := T%type: Setoid in
   let M := Setoid.mix X in
   let leq' := leq in
  @pack T M (@from_setoid T M leq' H (H': forall x y: X, x ≡ y <-> (leq' x y /\ leq' y x)))).
(* Definition build (X: Setoid) := *)
(*   (* fun leq H H' => @pack _ (Setoid.mix X) (@from_setoid _ (Setoid.mix X) leq H H').  *) *)
(*   let '@Setoid.pack T M := X return *)
(*                              forall leq: relation X, *)
(*                                PreOrder leq -> *)
(*                                (forall x y, x ≡ y <-> (leq x y /\ leq y x)) -> type in *)
(*   fun leq H H' => @pack T M (@from_setoid T M leq H H'). *)
(* Arguments build: clear implicits. *)

(* unused (and should not be used? unless we systematically declare the resulting Setoid as canonical?) *)
Program Definition build_from_type (X: Type) (leq: relation X) (H: PreOrder leq): type :=
  let M := @Setoid.from_type X (fun x y => leq x y /\ leq y x) _ in
  @pack X M (from_setoid M H _). 
Next Obligation.
  constructor; repeat intro.
  - split; reflexivity.
  - tauto.
  - split; transitivity y; tauto.
Qed.
Next Obligation.
  reflexivity.
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
Infix "<=" := leq (at level 70).
Infix "<=[ X ]" := (@leq X) (at level 70, only parsing).
Definition lt {X: PO} (x y: X) := x<=y /\ ~y<=x.
Infix "<" := lt (at level 70).
Infix "<[ X ]" := (@lt X) (at level 70, only parsing).

(** ** basic properties *)

Lemma leq_refl {X: PO} (x: X): x <= x.
Proof. reflexivity. Defined.
#[export] Hint Extern 0 (_ <= _)=> exact: (leq_refl _): core.

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

Program Definition discrete_po (X: Setoid) := PO.build X eqv _ _.
Next Obligation. by intuition symmetry. Qed.

Canonical Structure unit_po := PO.cast unit (discrete_po _).

(* this one makes [prod_po] fail below, can't see why... *)
(* Canonical Structure irrelevant_po (P: Prop) := discrete_po P. *)

Program Canonical Structure bool_po := PO.build bool implb _ _.
Next Obligation. split. by case. move=>[][][]//=. Qed.
Next Obligation. case: x; case: y=>//=; intuition discriminate. Qed.
  

Program Canonical Structure nat_po := PO.build nat Peano.le _ _.
Admit Obligations.

Program Canonical Structure Prop_po := Eval cbn in PO.build Prop impl _ _.
Next Obligation. split; cbv; tauto. Qed.
Next Obligation. cbv; tauto. Qed.

Program Canonical Structure prod_po (X Y: PO) :=
  PO.build (prod X Y) (fun p q => fst p <= fst q /\ snd p <= snd q) _ _.
Next Obligation.
  constructor=>//.
  by move=>???[??][]; split; etransitivity; eassumption.
Qed.
Next Obligation.
  cbn. rewrite 2!eqv_of_leq. tauto. 
Qed.


Definition lex_prod := prod.
Canonical Structure lex_prod_setoid (X Y: Setoid) :=
  (* a clone of [prod_setoid] *)
  Setoid.cast (lex_prod X Y) (prod_setoid X Y). 
Program Canonical Structure lex_prod_po (X Y: PO) :=
  PO.build (lex_prod X Y) (fun p q: lex_prod X Y => fst p <= fst q /\ (fst q <= fst q -> snd p <= snd q)) _ _.
Next Obligation.
  constructor=>//.
  move=>[x x'][y y'][z z']/=.
  intuition solve [transitivity y; auto|transitivity y'; auto].
Qed.
Next Obligation.
  cbn. rewrite 2!eqv_of_leq. intuition.
Qed.

Fixpoint leq_list {X: PO} (h k: list X) :=
  match h,k with cons x h,cons y k => x<=y /\ leq_list h k | nil,_ => True | _,_ => False end.
Program Canonical Structure list_po (X: PO) :=
  PO.build (list X) leq_list _ _.
Next Obligation.
  constructor.
  by elim=>//=.
  by elim=>[|x h IH][|y k][|z l]//=[? ?][? ?]; split; try etransitivity; eauto.
Qed.
Next Obligation.
  revert y. elim: x=>[|x h IH][|y k]; cbn; try tauto.
  rewrite eqv_of_leq. setoid_rewrite IH. tauto. 
Qed.

(* with [None] as top element *)
Definition leq_option (X: PO) (p q: option X) :=
  match q,p with Some q,Some p => p<=q | None,_ => True | _,_ => False end.
Program Canonical Structure option_po (X: PO) :=
  PO.build (option X) (leq_option X) _ _.
Next Obligation.
  constructor.
  by case=>/=.
  case=>[?|]; case=>[?|]=>//=; case=>[?|]=>//=. apply transitivity.
Qed.
Next Obligation.
  case:x=>[?|]; case:y=>[?|]; cbn; rewrite ?eqv_of_leq; tauto. 
Qed.

Definition parallel_sum := sum. 
Definition leq_parallel_sum {X Y: PO} (p q: X+Y) :=
  match p,q with
  | inl x,inl y | inr x,inr y => x<=y
  | _,_ => False
  end.
Program Canonical Structure parallel_sum_po (X Y: PO) :=
  PO.build (parallel_sum X Y) leq_parallel_sum _ _.
Next Obligation.
  constructor.
  by case=>//=.
  by case=>?; case=>y; case=>?//=; transitivity y.
Qed.
Next Obligation.
  case:x=>x; case:y=>y; cbn; rewrite ?eqv_of_leq; tauto. 
Qed.

Definition sequential_sum := sum. 
Definition leq_sequential_sum {X Y: PO} (p q: X+Y) :=
  match p,q with
  | inl x,inl y | inr x,inr y => x<=y
  | inl _,inr _ => True
  | _,_ => False
  end.
Program Canonical Structure sequential_sum_po (X Y: PO) :=
  PO.build (sequential_sum X Y) leq_sequential_sum _ _.
Next Obligation.
  constructor.
  by case=>//=.
  by case=>?; case=>y; case=>?//=; transitivity y.
Qed.
Next Obligation.
  case:x=>x; case:y=>y; cbn; rewrite ?eqv_of_leq; tauto. 
Qed.

Program Canonical Structure dprod_po A (X: A -> PO) :=
  Eval cbn in PO.build (forall a, X a) (fun f g: forall a, X a => forall a, f a <= g a) _ _.
Next Obligation.
  constructor.
  - by move=>??. 
  - by move=>??????; etransitivity; eauto.
Qed.
Next Obligation.
  cbn. setoid_rewrite eqv_of_leq. firstorder; apply H. 
Qed.

Program Definition kern_po A (X: PO) (f: A -> X): PO :=
  PO.build (kern_setoid X f) (fun a b => f a <= f b) _ _.
Next Obligation.
  constructor.
  - by move=>//=. 
  - by move=>?????; etransitivity; eauto.
Defined.
Next Obligation.
  apply eqv_of_leq.
Defined.

Canonical Structure sig_po (X: PO) (P: X -> Prop): PO :=
  PO.cast (sig P) (kern_po X (@proj1_sig X P)).

Canonical Structure setoid_morphisms_po X (Y: PO): PO :=
  PO.cast (X-eqv->Y) (kern_po _ (@Setoid.body X Y)). 
Canonical Structure po_morphisms_setoid (X Y: PO): Setoid :=
  Setoid.cast (X-mon->Y) (kern_setoid (X->Y) (@PO.body X Y)). 
Canonical Structure po_morphisms_po X Y: PO := 
  PO.cast (X-mon->Y) (kern_po _ (@PO.body X Y)).

Program Canonical Structure dual_po (X: PO): PO :=
  PO.build (dual X) (flip leq: relation (dual X)) _ _.
Next Obligation. typeclasses eauto. Qed.
Next Obligation. rewrite and_comm. apply eqv_of_leq. Qed.

Program Canonical Structure dual_po_morphism {X Y: PO} (f: X -mon-> Y): dual X -mon-> dual Y := PO.build_morphism f _.
Next Obligation. move=>x y xy. apply f, xy. Qed.

Lemma comp_leq {X Y Z}: Proper (@leq (Y-mon->Z) ==> leq ==> leq) (@comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x/=. rewrite (gg' x). apply: ff'. Qed.
Lemma comp_leq_eqv {X Y} {Z: PO}: Proper (@leq (Y-eqv->Z) ==> eqv ==> leq) (@comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x/=. rewrite (gg' x). apply: ff'. Qed.

#[export] Instance setoid_comp_leq {X Y} {Z: PO}: Proper (leq ==> eqv ==> leq) (@Setoid.comp X Y Z) := comp_leq_eqv.
#[export] Instance po_comp_leq {X Y Z}: Proper (leq ==> leq ==> leq) (@PO.comp X Y Z) := comp_leq.
#[export] Instance po_comp_eqv {X Y Z}: Proper (eqv ==> eqv ==> eqv) (@PO.comp X Y Z) := op_leq_eqv_2.

(* #[export] Existing Instance comp_eqv(* _ {X Y Z : Setoid}: *) *)
(* (* Proper (meqv ==> meqv ==> meqv) (@comp X Y Z) := comp_eqv *). *)
(* #[export] Existing Instance comp_leq. *)
(* #[export] Existing Instance comp_leq_eqv. *)



#[export] Instance const_leq {X} {Y: PO}: Proper (leq ==> leq) (@const X Y).
Proof. move=>/=y y' yy' _/=. apply yy'. Qed.
#[export] Instance setoid_const_leq {X} {Y: PO}: Proper (leq ==> leq) (@Setoid.const X Y) := const_leq.
#[export] Instance po_const_leq {X} {Y: PO}: Proper (leq ==> leq) (@PO.const X Y) := const_leq.
#[export] Instance po_const_eqv {X} {Y: PO}: Proper (eqv ==> eqv) (@PO.const X Y) := const_eqv.



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


Lemma Proper_flip A B (R: relation A) (S: relation B): Proper (flip R ==> S) ≡ Proper (R ==> flip S).
Proof. move=>f. apply: antisym=>Hf x y xy; by apply Hf. Qed.
Lemma Proper_half (X Y: PO): Proper (@eqv X ==> @leq Y) <= Proper (@eqv X ==> @eqv Y).
Proof. move=>f H x y xy. apply: antisym; apply H=>//; by symmetry. Qed.


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
#[export] Instance eqv_covered: subrelation eqv bicovered.
Proof. move=>P Q. by rewrite eqv_of_leq; move=>[??]; split; apply leq_covered. Qed.


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
Proof. intros. eapply is_sup_eqv; eauto; reflexivity. Qed.

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
  move=>H. apply Proper_half=>x y xy Px. apply (H (eq x)). by move=>?<-. 
  move: (is_sup_single x). apply Proper_is_sup=>//. reflexivity.
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
Proof. dual @leq_from_above. Qed.
Lemma from_below x y: (forall z, z <= x <-> z <= y) -> x ≡ y.
Proof. dual @from_above. Qed.

Definition is_inf (P: X -> Prop) x := forall z, z <= x <-> forall y, P y -> z <= y.
Lemma geq_is_inf P x: is_inf P x -> forall y, P y -> x <= y.
Proof. dual @leq_is_sup. Qed.
Definition cocovered (P Q: X -> Prop) := covered (P: dual X -> _) (Q: dual X -> _).
Definition cobicovered (P Q: X -> Prop) := bicovered (P: dual X -> _) (Q: dual X -> _).
Lemma is_inf_leq P p Q q: is_inf P p -> is_inf Q q -> cocovered P Q -> q<=p.
Proof. dual @is_sup_leq. Qed.
Lemma is_inf_eqv P p Q q: is_inf P p -> is_inf Q q -> cobicovered P Q -> p≡q.
Proof. dual @is_sup_eqv. Qed.
Lemma infU (P: X -> Prop) x y: is_inf P x -> is_inf P y -> x ≡ y.
Proof. dual @supU. Qed.

Definition inf_closed (P: X -> Prop) := forall Q, Q <= P -> is_inf Q <= P.

Lemma inf_closed_impl (P Q: X -> Prop): downward_closed P -> inf_closed Q -> inf_closed (fun x => P x -> Q x).
Proof. dual @sup_closed_impl. Qed.

Lemma inf_closed_leq (f: X -mon-> X): inf_closed (fun x => f x <= x).
Proof. apply (sup_closed_leq (dual_po_morphism f)). Qed.

End s.


Definition image {X Y: Type} (f: X -> Y) (P: X -> Prop) y := exists x, P x /\ y = f x.
Definition image_id {X: Type} (P: X -> Prop): image Datatypes.id P ≡ P.
Proof. cbv. by firstorder subst. Qed.
Definition image_comp {X Y Z: Type} (f: Y -> Z) (g: X -> Y) (P: X -> Prop): image (f ° g) P ≡ image f (image g P).
Proof. cbv. firstorder subst; eauto. Qed.
Lemma in_image {X Y} (f: X -> Y) (P: X -> Prop) x: P x -> image f P (f x).
Proof. by exists x. Qed.
#[export] Hint Resolve in_image: core. 
Lemma forall_image {X Y: Type} (f: X -> Y) (P: X -> Prop) (Q: Y -> Prop):
  image f P <= Q <-> forall x, P x -> Q (f x).
Proof.
  split=>H.
  - move=>x Px. by apply H; auto.
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

(** sups are computed pointwise in products
TOTHINK: get it as as special case of the above lemmas, with [A=bool]?      
 *)
Lemma prod_sup {X Y: PO} (P: (X*Y)->Prop) (p: X*Y):
  (is_sup (image fst P) (fst p) /\ is_sup (image snd P) (snd p)) <-> is_sup P p.
Proof.
  destruct p as [x y]. split.
  - move=>[H1 H2] [u v]. cbn. rewrite (H1 u) (H2 v).
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
Lemma kern_sup {A} {X: PO} (f: A -> X) (P: A->Prop) (a: A):
  is_sup (image f P) (f a) -> is_sup (X:=kern_po X f) P a.
Proof.
  move=>H b; split=>ab.
  -- move=>c Pc. cbn. rewrite -ab. by apply H; auto. 
  -- apply H=>_ [c [Pc ->]]. by apply ab. 
Qed.

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
