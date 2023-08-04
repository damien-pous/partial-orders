Require Eqdep_dec.
Require Import ssreflect ssrfun ssrbool.
Require Export cs_setoid.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

(** * partial orders *)

(** ** class *)

Definition po_axm {X: Setoid.type} (leq: relation X) :=
  PreOrder leq /\ forall x y, eqv x y <-> (leq x y /\ leq y x).
Module PO.
Record mixin X (M: Setoid.mixin X) := from_setoid {
    leq: relation X;
    axm: @po_axm (Setoid.pack M) leq;
  }.
Structure type := pack {
    sort:> Type;
    #[canonical=no] setoid_mix: Setoid.mixin sort;
    #[canonical=no] mix: mixin setoid_mix;
}.
Canonical Structure to_Setoid (X: type) := Setoid.pack (setoid_mix X).
#[reversible] Coercion to_Setoid: type >-> Setoid.type.
Notation copy T X := (@pack T _ (mix X)).
Notation Build T leq H :=
  (let X := T%type: Setoid.type in
   let M := Setoid.mix X in
  @pack T M (@from_setoid T M leq H)).

(* helper to setup duality in IPO/GPOs *)
Program Definition dual_mixin X M (N: @mixin X M): @mixin (dual X) M :=
  @from_setoid (dual X) M (flip (leq N)) _.
Next Obligation.
  split. apply flip_PreOrder, N.
  intros. rewrite (proj2 (axm N)). tauto.
Qed.

End PO.
Canonical PO.to_Setoid.
#[reversible] Coercion PO.to_Setoid: PO.type >-> Setoid.type.
#[reversible] Coercion PO.sort: PO.type >-> Sortclass.
Definition leq {X: PO.type} := PO.leq (PO.mix X).
Infix "<=" := leq (at level 70).
Notation "x <=[ X ] y" := (@leq X x y) (at level 70, only parsing).

(* those two projections need to be Defined in order kernel composition to behave well *)
#[export] Instance PreOrder_leq {X: PO.type}: @PreOrder X leq.
Proof. apply PO.axm. Defined.
Lemma eqv_of_leq {X: PO.type} (x y: X): x ≡ y <-> x <= y /\ y <= x. 
Proof. apply PO.axm. Defined.

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
Structure po_morphism (X Y: PO.type) := {
    po_body:> X -> Y;
    #[canonical=no] monotone: Proper (leq ==> leq) po_body;
  }.
Arguments Build_po_morphism {_ _}. 
Arguments monotone {_ _ _}.
#[export] Existing Instance monotone.
(** inheritance: po morphisms are setoid morphisms *)
Program Canonical Structure to_setoid_morphism {X Y} (f: po_morphism X Y) :=
  Build_setoid_morphism f _.
Next Obligation. move=>x y. rewrite 2!eqv_of_leq=>xy. split; apply f; apply xy. Qed.
#[reversible] Coercion to_setoid_morphism: po_morphism >-> setoid_morphism.

Notation "X '-mon->' Y" := (po_morphism X Y) (at level 99, Y at level 200).

(** identity morphism *)
Canonical Structure po_id {X}: X-mon->X :=
  Build_po_morphism types_id _.

(** composition of morphisms *)
Program Canonical Structure po_comp {X Y Z} (f: Y-mon->Z) (g: X-mon->Y): X-mon->Z :=
  Build_po_morphism (f ∘ g) _. 

(** constant morphism *)
Program Canonical Structure po_const {X Y: PO.type} (y: Y): X-mon->Y :=
  Build_po_morphism (const y) _.
Next Obligation. by move=>/=_ _ _. Qed. (* Defined? *)


(** ** immediate properties *)

#[export] Instance PartialOrder_eqv_leq {X: PO.type}: @PartialOrder X eqv _ leq _.
Proof. intros x y. apply eqv_of_leq. Qed.
#[export] Instance leq_rw {X: PO.type}: @RewriteRelation X leq := {}.

Lemma leq_refl {X: PO.type} (x: X): x <= x.
Proof. reflexivity. Qed.

(** ** duality *)

Canonical Structure dual_po (X: PO.type): PO.type :=
  @PO.pack (dual X) _ (PO.dual_mixin (PO.mix X)). 

Program Canonical Structure dual_po_morphism {X Y: PO.type} (f: X -mon-> Y): dual X -mon-> dual Y := Build_po_morphism (dualf f) _.
Next Obligation. move=>x y xy. apply f, xy. Qed.

(** ** instances *)

(** discrete partial order on top of a setoid *)
Definition discrete (X: Type) := X.
Program Canonical Structure discrete_po (X: Setoid.type) :=
  PO.Build (discrete X) eqv _.
Next Obligation. split. typeclasses eauto. intuition. Qed.

(** trivial partial order as the discrete partial order on the trivial setoid *)
Canonical Structure trivial_po (X: Type) :=
  PO.copy (trivial X) (discrete (trivial X)).

(** trivial partial order on the unit type *)
Canonical Structure unit_po :=
  PO.copy unit (discrete unit).

(** Booleans with [false ≦ true] *)
Program Canonical Structure bool_po := PO.Build bool implb _.
Next Obligation.
  split. split. by case. move=>[][][]//=.
  case; case=>//=; intuition discriminate.
Qed.

(** propositions ordered by implication *)
Program Canonical Structure Prop_po :=
  (* Eval cbn required so that [move=>?] works better*)
  Eval cbn in PO.Build Prop impl _.
Next Obligation. split=>//. split; cbv; tauto. Qed.

(** (dependent) function space, ordered pointwise *)
Program Canonical Structure dprod_po A (X: A -> PO.type) :=
  (* Eval cbn required so that [move=>?] works better*)
  Eval cbn in PO.Build (forall a, X a) (fun f g: forall a, X a => forall a, f a <= g a) _.
Next Obligation.
  split. split.
  - by move=>??. 
  - by move=>??????; etransitivity; eauto.
  - cbn. setoid_rewrite eqv_of_leq. firstorder; apply H. 
Qed.
Canonical Structure po_app {A} {X: A -> PO.type} (a: A): (forall a, X a) -mon-> X a :=
  Build_po_morphism (app a) (fun f g fg => fg a).

(** products, sums, option *)
Section s.
 Variables X Y: PO.type.

 (** direct product *)
 Program Canonical Structure prod_po :=
   PO.Build (X*Y) (fun p q => fst p <= fst q /\ snd p <= snd q) _.
 Next Obligation.
   split. constructor=>//.
   by move=>???[??][]; split; etransitivity; eassumption.
   cbn=>??. rewrite 2!eqv_of_leq. tauto. 
 Qed.
 Canonical Structure po_fst: (prod X Y) -mon-> X :=
  Build_po_morphism fst (fun p q pq => proj1 pq).
 Canonical Structure po_snd: (prod X Y) -mon-> Y :=
  Build_po_morphism snd (fun p q pq => proj2 pq).

 (** lexicographic product *)
 (** we use an alias for product to guide structure inferrence *)
 Definition lex_prod := prod.
 Program Canonical Structure lex_prod_po :=
  PO.Build (lex_prod X Y) (fun p q: lex_prod X Y => fst p <= fst q /\ (fst q <= fst q -> snd p <= snd q)) _.
 Next Obligation.
   split. constructor=>//.
   move=>[x x'][y y'][z z']/=.
   intuition solve [transitivity y; auto|transitivity y'; auto].
   cbn=>??. rewrite 2!eqv_of_leq. intuition. 
 Qed.

 (** direct sum (called "parallel" by opposition with the sequential operation below) *)
 Definition leq_parallel_sum (p q: X+Y) :=
   match p,q with
   | inl x,inl y | inr x,inr y => x<=y
   | _,_ => False
   end.
 Program Canonical Structure parallel_sum_po :=
   PO.Build (X+Y) leq_parallel_sum _.
 Next Obligation.
   split. constructor.
   by case=>//=.
   by case=>?; case=>y; case=>?//=; transitivity y.
   case=>x; case=>y; cbn; rewrite ?eqv_of_leq; tauto. 
 Qed.
 Canonical Structure po_inl: X -mon-> (sum X Y) :=
  Build_po_morphism inl (fun p q pq => pq).
 Canonical Structure po_inr: Y -mon-> (sum X Y) :=
  Build_po_morphism inr (fun p q pq => pq).

 (** sequential sum *)
 Definition sequential_sum := sum. 
 Definition leq_sequential_sum (p q: X+Y) :=
   match p,q with
   | inl x,inl y | inr x,inr y => x<=y
   | inl _,inr _ => True
   | _,_ => False
   end.
 Program Canonical Structure sequential_sum_po :=
   PO.Build (sequential_sum X Y) leq_sequential_sum _.
 Next Obligation.
   split. constructor.
   by case=>//=.
   by case=>?; case=>y; case=>?//=; transitivity y.
   case=>x; case=>y; cbn; rewrite ?eqv_of_leq; tauto. 
 Qed.

 (** [option] type, adding [None] as top element *)
 (* TODO: propose the other variant;
    do it via sequential_sum and unit? *)
 Definition leq_option (p q: option X) :=
   match q,p with Some q,Some p => p<=q | None,_ => True | _,_ => False end.
 Program Canonical Structure option_po :=
   PO.Build (option X) leq_option _.
 Next Obligation.
   split. constructor.
   by case=>/=.
   case=>[?|]; case=>[?|]=>//=; case=>[?|]=>//=. apply transitivity.
   case=>[?|]; case=>[?|]; cbn; rewrite ?eqv_of_leq; tauto. 
 Qed.
End s.

(** constructing a partial order via a function into another partial order *)
Section kernel.
 Variables (A: Type) (X: PO.type) (f: A -> X).
 Program Canonical Structure kern_po :=
   PO.Build (kernel f) (fun a b => f a <= f b) _.
 Next Obligation.
   split.
   - constructor.
     -- by move=>?; reflexivity. 
     -- by move=>?????; etransitivity; eauto.
   - move=>??. apply eqv_of_leq.
 Defined.
 Canonical Structure setoid_kernelf: (kernel f) -mon-> X :=
   Build_po_morphism (kernelf f) (fun p q pq => pq).
End kernel.
(* [kern_po] should be defined carefully, and left transparent, so that we have:  *)
(* Check fun (X: PO.type) (f g: X -> X) => *)
(*         unify_pos *)
(*           (kernel (X:=kernel g) f) *)
(*           (kernel (types_comp g f)). *)

(** sub partial orders as a special case *)
Canonical Structure sig_po (X: PO.type) (P: X -> Prop) :=
  PO.copy (sig P) (kernel (@proj1_sig X P)).
Canonical Structure po_proj1_sig (X: PO.type) (P: X -> Prop): (sig P) -mon-> X :=
  Build_po_morphism (@proj1_sig X P) (fun p q pq => pq).

(** extensional functions as a special case (already declared as a setoid) *)
Canonical Structure setoid_morphisms_po {X} {Y: PO.type} :=
  PO.copy (X-eqv->Y) (kernel (@setoid_body X Y)).

(** monotone functions as a special case *)
Canonical Structure po_morphisms_setoid {X Y: PO.type} :=
  Setoid.copy (X-mon->Y) (kernel (@po_body X Y)).
Canonical Structure po_morphisms_po {X Y: PO.type} :=
  PO.copy (X-mon->Y) (kernel (@po_body X Y)).
(** notation to help typechecking morphisms comparisons *)
Infix "≦" := (@leq (_ -mon-> _)) (at level 70, only parsing). 

(* TOHINK: useful as instances? *)
Lemma types_comp_leq {X Y Z}: Proper (@leq (Y-mon->Z) ==> leq ==> leq) (@types_comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x/=. rewrite (gg' x). apply: ff'. Qed.
Lemma types_comp_leq_eqv {X Y} {Z: PO.type}: Proper (@leq (Y-eqv->Z) ==> eqv ==> leq) (@types_comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x/=. rewrite (gg' x). apply: ff'. Qed.

#[export] Instance const_leq {X} {Y: PO.type}:
  Proper (leq ==> leq) (@const Y X).
Proof. cbn=>y y' yy x. apply yy. Qed.
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
Definition image_comp {X Y Z: Type} (f: Y -> Z) (g: X -> Y) (P: X -> Prop): image (f ∘ g) P ≡ image f (image g P).
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
    -- move=>c Pc. cbn. rewrite -ab. by apply H; auto. 
    -- apply H=>_ [c [Pc ->]]. by apply ab.
  Qed.
End ks.



(** the following restrictions are useful for [setoid_rewrite] *)
(* TOTHINK: redundant with support to come in cs_categories? *)
#[export] Instance setoid_comp_leq {X Y} {Z: PO.type}: Proper (leq ==> eqv ==> leq) (@setoid_comp X Y Z) := types_comp_leq_eqv.
#[export] Instance po_comp_leq {X Y Z}: Proper (leq ==> leq ==> leq) (@po_comp X Y Z) := types_comp_leq.
#[export] Instance po_comp_eqv {X Y Z}: Proper (eqv ==> eqv ==> eqv) (@po_comp X Y Z) := op_leq_eqv_2.

#[export] Program Instance setoid_const_leq {X} {Y: PO.type}: Proper (leq ==> leq) (@setoid_const X Y) := const_leq.
#[export] Instance po_const_leq {X} {Y: PO.type}: Proper (leq ==> leq) (@po_const X Y) := const_leq.
#[export] Instance po_const_eqv {X} {Y: PO.type}: Proper (eqv ==> eqv) (@po_const X Y) := const_eqv.
