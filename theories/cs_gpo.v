Require Import ssreflect ssrfun ssrbool.
Require Export cs_ipo.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

(** * partial orders with suprema and infima *)


(** ** levels *)

(* isomorphic to [option (plevel*plevel)], but enabling duality *)
Record level := mk_level { suplevel: slevel; inflevel: slevel; merge_tops: suplevel=None <-> inflevel=None }.
Arguments mk_level: clear implicits.  

Definition alt_level l :=
  match suplevel l,inflevel l with
  | None,_ | _,None => None
  | Some p,Some q => Some (p,q)
  end.
Canonical Structure level_setoid := Setoid.copy level (kernel alt_level).
Canonical Structure level_po := PO.copy level (kernel alt_level).

Lemma suplevel_mon: Proper (leq ==> leq) suplevel.
Proof.
  move=>[[?|] [?|] ?] [[?|] [?|] ?] //=hk;
       try apply hk; exfalso; clear hk; intuition congruence.
Qed.
Lemma inflevel_mon: Proper (leq ==> leq) inflevel.
Proof.
  move=>[[?|] [?|] ?] [[?|] [?|] ?] //=hk;
       try apply hk; exfalso; clear hk; intuition congruence.
Qed.

Definition dual_level (l: level) := mk_level (inflevel l) (suplevel l) (symmetry (merge_tops l)).

Definition level_fun (l: level) k: SProp :=
  match k with
  | inl k => suplevel l k
  | inr k => inflevel l k
  end.
Coercion level_fun: level >-> Funclass.
(*
Check fun l: level => unify (l ∘ inl) (suplevel l). 
Check fun l: level => unify (l ∘ inr) (inflevel l). 
Check fun l: level => unify (dual_level l ∘ inr) (l ∘ inl). 
Check fun (l: level) x => unify (dual_level (dual_level l) x) (l x). 
Fail Check fun l: level => unify (dual_level (dual_level l)) l. (* ok thanks to above weaker form *)
*)
Definition lA := mk_level None None (reflexivity _).
(*
Fail Check fun l => unify (lA << l) (lA << dual_level l). (* unfortunately *)
*)
#[export] Instance lower_dual {h k} {H: dual_level h << k}: h << dual_level k.
Proof.
  revert H.
  case: h=>[[hs|] [hi|] hE]; try solve [intuition discriminate]; 
  case: k=>[[ks|] [ki|] kE]; try solve [intuition discriminate].
  cbn; simpl. tauto.
Qed.   
Program Definition lSI p q := mk_level (Some p) (Some q) _.
Next Obligation. split; discriminate. Qed.
Definition merge_slevels p q :=
  match p,q with
  | None,_ | _,None => lA
  | Some p,Some q => lSI p q
  end.

(** ** class *)

Module GPO.
 Structure type (l: level) := pack {
     sort:> Type;
     #[canonical=no] setoid_mix: Setoid.mixin sort;
     #[canonical=no] po_mix: PO.mixin setoid_mix;
     #[canonical=no] s_mix: SPO.mixin (suplevel l) po_mix;
     #[canonical=no] i_mix: IPO.mixin (inflevel l) po_mix;
 }.
 Canonical Structure to_SPO l (X: type l): SPO.type (suplevel l) := SPO.pack (s_mix X). 
 Canonical Structure to_IPO l (X: type l): IPO.type (inflevel l) := IPO.pack (i_mix X). 
 Canonical Structure to_PO l (X: type l): PO.type := PO.pack (po_mix X). 
 Canonical Structure to_Setoid l (X: type l): Setoid.type := Setoid.pack (setoid_mix X). 
 Notation cast T X := (let X':=X in @pack _ T _ _ (s_mix X') (i_mix X')).
 Notation from_PO l T S I :=
   (let X  := T%type: PO.type in
    let M := PO.setoid_mix X in
    let N := PO.mix X in
    @pack l T M N (SPO.mix S) (IPO.mix I)).
 Notation from_ISPO l T :=
   (let Xs := T%type: SPO.type (suplevel l) in
    let Xi := T%type: IPO.type (inflevel l) in
    from_PO l T Xs Xi).
End GPO.
Canonical GPO.to_SPO.
Canonical GPO.to_IPO.
Canonical GPO.to_PO.
Canonical GPO.to_Setoid.
#[reversible] Coercion GPO.to_Setoid: GPO.type >-> Setoid.type.
#[reversible] Coercion GPO.to_PO: GPO.type >-> PO.type.
#[reversible] Coercion GPO.to_SPO: GPO.type >-> SPO.type.
#[reversible] Coercion GPO.to_IPO: GPO.type >-> IPO.type.
#[reversible] Coercion GPO.sort: GPO.type >-> Sortclass.

Canonical Structure dual_gpo l (X: GPO.type l): GPO.type (dual_level l) :=
  @GPO.pack (dual_level l) (dual X) (GPO.setoid_mix X) (PO.dual_mixin (GPO.po_mix X)) (GPO.i_mix X) (GPO.s_mix X).

Ltac dual2 t :=
  match type of t with
  | forall l, forall X: GPO.type l, _ =>
      match goal with
      | X: GPO.type ?l |- _ => apply: (t _ (@dual_gpo l X))
      end
  end.
Ltac dual t ::= dual2 t || dual1 t || dual0 t.

(* lattice of booleans, complete lattice of Propositions *)
Canonical Structure bool_gpo := GPO.from_ISPO (lSI pF pF) bool. 
Canonical Structure dprod_gpo {A l} (X: A -> GPO.type l) := GPO.from_ISPO l (forall a, X a).

Section sub.
 Context {l} {X: GPO.type l}.
 Definition closed' (P: X -> Prop) := sup_closed' P /\ inf_closed' P.

 Definition closed_sig P (HP: closed' P) := sig P.
 Canonical Structure sig'_spo P (HP: closed' P) :=
   SPO.copy (closed_sig HP) (sup_closed_sig (proj1 HP)).
 Canonical Structure sig'_ipo P (HP: closed' P) :=
   IPO.copy (closed_sig HP) (inf_closed_sig (proj2 HP)).
 Canonical Structure sig_gpo P (HP: closed' P) :=
   GPO.from_ISPO l (closed_sig HP). 
End sub.

(** GPOs from retractions (and thus isomorphisms given the induced order on [A]) *)
Canonical Structure retract_gpo {A l} (X: GPO.type l) {r: A->X} {i: X->A} (ri: r ∘ i ≡ types_id) :=
  GPO.from_ISPO l (retract_of ri). 
Arguments retract_gpo [_ _] _ [_ _]. 

(** the GPO of extensive functions *)
Canonical Structure setoid_morphism_gpo {X: Setoid.type} {l} {Y: GPO.type l}
  := GPO.from_ISPO l (X-eqv->Y).

(** the GPO of monotone functions *)
Canonical Structure po_morphism_gpo {X: PO.type} {l} {Y: GPO.type l}
  := GPO.from_ISPO l (X-mon->Y).

Lemma lower_trans_sup k h l (kh: k<<suplevel h) (hl: h<<l): k<<suplevel l.
Proof. rewrite ->kh. by apply suplevel_mon. Qed.
Lemma lower_trans_inf k h l (kh: k<<inflevel h) (hl: h<<l): k<<inflevel l.
Proof. rewrite ->kh. by apply inflevel_mon. Qed.
Ltac solve_lower ::=
  solve [ reflexivity | assumption |
          match goal with
          | H: ?h << ?l |- ?k << ?l => exact: (lower_trans k h l I H)
          | H: ?h << ?l |- ?k << suplevel ?l => exact: (lower_trans_sup k h l I H)
          | H: ?h << ?l |- ?k << inflevel ?l => exact: (lower_trans_inf k h l I H)
          end
    ].

(** ** theory *)

Lemma sup_top {l} {X: GPO.type l} {L: lA<<l}: sup top ≡[X] top.
Proof. apply: antisym=>//. by apply: leq_sup. Qed.

Lemma inf_top {l} {X: GPO.type l} {L: lA<<l}: inf top ≡[X] bot.
Proof. dual @sup_top. Qed.
