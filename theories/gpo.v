Require Import ssreflect ssrfun ssrbool.
Require Export ipo.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

(** * partial orders with suprema and infima *)


(* isomorphic to [option (plevel*plevel)], but enabling duality *)
Record level := mk_level { suplevel: slevel; inflevel: slevel; merge_tops: suplevel=None <-> inflevel=None }.
Arguments mk_level: clear implicits.  

Definition alt_level l :=
  match suplevel l,inflevel l with
  | None,_ | _,None => None
  | Some p,Some q => Some (p,q)
  end.
Canonical Structure level_setoid := Eval hnf in kern_setoid _ alt_level.
Canonical Structure level_po := PO.cast level (kern_po _ alt_level).
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
Goal forall l: level, l ° inl = suplevel l. reflexivity. Qed.
Goal forall l: level, l ° inr = inflevel l. reflexivity. Qed.
Goal forall l, dual_level l ° inr = l ° inl. reflexivity. Qed.
Goal forall l x, dual_level (dual_level l) x = l x. reflexivity. Qed.
*)
Definition lA := mk_level None None (reflexivity _).
(*
Goal forall l, (lA << l) = (lA << dual_level l).
  intro. cbn.  Fail reflexivity. (* dommage *)
Abort.
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


Module GPO.
 Structure type (l: level) := pack {
     sort:> Type;
     #[canonical=no] setoid_mix: Setoid.mixin sort;
     #[canonical=no] po_mix: PO.mixin setoid_mix;
     #[canonical=no] s_mix: SPO.mixin (suplevel l) po_mix;
     #[canonical=no] i_mix: IPO.mixin (inflevel l) po_mix;
 }.
 Canonical Structure to_SPO l (X: type l): SPO (suplevel l) := SPO.pack (s_mix X). 
 Canonical Structure to_IPO l (X: type l): IPO (inflevel l) := IPO.pack (i_mix X). 
 Canonical Structure to_PO l (X: type l): PO := PO.pack (po_mix X). 
 Canonical Structure to_Setoid l (X: type l): Setoid := Setoid.pack (setoid_mix X). 
 Notation cast T X := (let X':=X in @pack _ T _ _ (s_mix X') (i_mix X')).
 Notation from_PO l T S I :=
   (let X  := T%type: PO in
    let M := PO.setoid_mix X in
    let N := PO.mix X in
    @pack l T M N (SPO.mix S) (IPO.mix I)).
 Notation from_ISPO l T :=
   (let Xs := T%type: SPO (suplevel l) in
    let Xi := T%type: IPO (inflevel l) in
    from_PO l T Xs Xi).
End GPO.
Notation GPO := GPO.type.
Canonical GPO.to_SPO.
Canonical GPO.to_IPO.
Canonical GPO.to_PO.
Canonical GPO.to_Setoid.
#[reversible] Coercion GPO.to_Setoid: GPO >-> Setoid.
#[reversible] Coercion GPO.to_PO: GPO >-> PO.
#[reversible] Coercion GPO.to_SPO: GPO >-> SPO.
#[reversible] Coercion GPO.to_IPO: GPO >-> IPO.
#[reversible] Coercion GPO.sort: GPO >-> Sortclass.
Canonical Structure dual_gpo l (X: GPO l): GPO (dual_level l) :=
  @GPO.pack (dual_level l) (dual X) (GPO.setoid_mix X) (PO.dual_mixin (GPO.po_mix X)) (GPO.i_mix X) (GPO.s_mix X).

Ltac dual2 t :=
  match type of t with
  | forall l, forall X: GPO l, _ =>
      match goal with
      | X: GPO ?l |- _ => apply: (t _ (@dual_gpo l X))
      end
  end.
Ltac dual t ::= dual2 t || dual1 t || dual0 t.

Canonical Structure bool_gpo :=
  GPO.from_ISPO (lSI pF pF) bool. 

Canonical Structure dprod_gpo {A l} (X: A -> GPO l) :=
  GPO.from_ISPO l (forall a, X a).

Section sub.
 Context {l} {X: GPO l}.
 Variable P: X -> Prop.
 Definition closed' := sup_closed' P /\ inf_closed' P.
 Definition sig_gpo (HP: closed'): GPO l :=
   GPO.from_PO l (sig P) (sig_spo (proj1 HP)) (sig_ipo (proj2 HP)). 
End sub.

(** GPOs from retractions (and thus isomorphisms given the induced order on [A]) *)
Section c.
 Context {A: Type} {l} (X: GPO l).
 Variable r: A->X.               (* retraction *)
 Variable i: X->A.               (* section *)
 Hypothesis ri: r∘i ≡ id. 
 Definition retract_gpo: GPO l :=
   GPO.from_PO _ _ (retract_spo X ri) (retract_ipo X ri). 
End c.
Arguments retract_gpo [_ _] _ [_ _]. 

(** altogether, we get general sub-GPOs  *)
Section c.
 Context {A: Type} {l} {X: GPO l} (P: X -> Prop).
 Variable r: A->sig P.
 Variable i: sig P->A.
 Hypothesis ri: r∘i ≡ id. 
 Hypothesis HP: closed' P.
 Definition sub_gpo: GPO l := retract_gpo (sig_gpo HP) ri. 
End c.

(** the GPO of monotone functions *)
Section s.
 Context {X: PO} {l} {Y: GPO l}.
 Canonical Structure mon_gpo: GPO l := GPO.from_ISPO l (X-mon->Y).
End s.

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

Lemma sup_top {l} {X: GPO l} {L: lA<<l}: sup top ≡[X] top.
Proof. apply: antisym=>//. by apply: leq_sup. Qed.

Lemma inf_top {l} {X: GPO l} {L: lA<<l}: inf top ≡[X] bot.
Proof. dual2 @sup_top. Qed.
