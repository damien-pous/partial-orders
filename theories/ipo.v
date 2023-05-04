Require Import ssreflect ssrfun ssrbool.
Require Export spo.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

(** * partial orders with infima *)

Module IPO.
 Definition mixin (l: slevel) X (M: Setoid.mixin X) (N: PO.mixin M) :=
   forall k, l k -> ginf_ops (PO.pack N) k.
 Structure type (l: slevel) := pack {
     sort:> Type;
     #[canonical=no] setoid_mix: Setoid.mixin sort;
     #[canonical=no] po_mix: PO.mixin setoid_mix;
     #[canonical=no] mix: mixin l po_mix;
 }.
 Canonical Structure to_PO l (X: type l): PO := PO.pack (po_mix X). 
 Canonical Structure to_Setoid l (X: type l): Setoid := Setoid.pack (setoid_mix X). 
 Notation cast T X := (let X':=X in @pack _ T _ _ (mix X')).
 Notation build l T f :=
   (let X := T%type: PO in
    let M := PO.setoid_mix X in
    let N := PO.mix X in
    @pack l%core T M N (f: forall k, l%core k -> ginf_ops X k)).
 Notation reduced_build l T f := (build l T (sreduce.reduce (f: forall k, option (ginf_ops _ k)))).
 Program Definition weaken (h l: slevel) (X: type l) (hl: h<=l): type h :=
   build h X (fun k hk => mix X k _).
 Next Obligation. move: hk. apply is_true'_leq, slevel_mon, hl. Qed.
 Definition dual l (X: type l): SPO l := SPO.pack (mix X). 
 Definition dual' l (X: SPO l): type l := @pack _ _ _ (PO.dual_mixin (SPO.po_mix X)) (SPO.mix X).
End IPO.
Notation IPO := IPO.type.
Canonical IPO.to_PO.
Canonical IPO.to_Setoid.
#[reversible] Coercion IPO.to_Setoid: IPO >-> Setoid.
#[reversible] Coercion IPO.to_PO: IPO >-> PO.
#[reversible] Coercion IPO.sort: IPO >-> Sortclass.
Canonical IPO.dual.
Canonical IPO.dual'. 

Ltac dual1 t :=
  match type of t with
  | forall l, forall X: SPO l, _ =>
      match goal with
      | X: IPO ?l |- _ => apply: (t l (IPO.dual X))
      end
  | forall l, forall X: IPO l, _ =>
      match goal with
      | X: SPO ?l |- _ => apply: (t l (IPO.dual' X))
      end
  end.
Ltac dual t ::= dual1 t || dual0 t.

Definition ginf {l} {X: IPO l}: forall k kl, args k (dual X) -> X := @gsup l (IPO.dual X).
Lemma ginf_spec {l} {X: IPO l} {k kl}: forall (x: args k (dual X)), is_inf (X:=X) (setof k x) (ginf k kl x).
Proof. apply: gsup_spec. Qed.
Lemma geq_ginf {l} {X: IPO l} k kl (x: args k (dual X)) (y: X): setof k x y -> ginf k kl x <= y.
Proof. apply: leq_gsup. Qed.

Program Canonical Structure bool_ipo :=
  IPO.build sF bool
    (fun k => match k with
           | kE => fun _ => exist _ (fun _ => true) _
           | kB => fun _ => exist _ (fun '(x,y) => andb x y) _
           | kC | kD | kA  => discriminate
           end).
Next Obligation. by case. Qed.
Next Obligation.
  move=>c/=. rewrite forall_pair. cbn.
  rewrite Bool.implb_andb_distrib_r.
  apply Bool.andb_true_iff.
Qed.

Program Canonical Structure Prop_ipo :=
  IPO.reduced_build sA Prop
    (fun k => match k with
           | kE => Some (exist _ (fun _ => True) _)
           | kB => Some (exist _ (fun '(p,q) => p/\q) _)
           | kC => None          (* generated *)
           | kD => None          (* generated *)
           | kA => Some (exist _ (fun '(existT _ _ (P,f)) => forall i, P i -> f i) _)
           end).
Next Obligation. firstorder. Qed.
Next Obligation. cbv; firstorder subst; eauto; apply H; eauto. Qed.
Next Obligation. destruct x as [I [P f]]; cbv. firstorder subst; apply H; eauto. Qed.

Program Canonical Structure dprod_ipo {A l} (X: A -> IPO l): IPO l :=
  IPO.cast (forall a, X a) (IPO.dual' (dprod_spo (fun a => IPO.dual (X a)))).

Section sub.
 Context {l} {X: IPO l}.
 Definition inf_closed' (P: X -> Prop) := sup_closed' (X:=IPO.dual X) P. 
 Lemma inf_closed_inf_closed': inf_closed (X:=X) <= inf_closed'.
 Proof. dual @sup_closed_sup_closed'. Qed.
 #[export] Instance inf_closed'_eqv: Proper (eqv==>eqv) inf_closed'.
 Proof. dual @sup_closed'_eqv. Qed.
 Definition sig_ipo P (Pinf: inf_closed' P): IPO l :=
   IPO.cast (sig P) (IPO.dual' (sig_spo Pinf)). 
End sub.

Section c.
 Context {A: Type} {l} (X: IPO l).
 Variable r: A->X.               (* retraction *)
 Variable i: X->A.               (* section *)
 Hypothesis ri: r°i ≡ id. 
 Definition retract_ipo: IPO l :=
   IPO.cast A (IPO.dual' (retract_spo (IPO.dual X) ri)). 
End c.
Arguments retract_ipo [_ _] _ [_ _]. 

Section c.
 Context {A: Type} {l} {X: IPO l} (P: X -> Prop).
 Variable r: A->sig P.
 Variable i: sig P->A.
 Hypothesis ri: r°i ≡ id. 
 Hypothesis Pinf: inf_closed' P.
 Definition sub_ipo: IPO l := retract_ipo (sig_ipo Pinf) ri. 
End c. 

Section s.
 Context {X: PO} {l} {Y: IPO l}.
 Lemma inf_closed'_monotone: inf_closed' (Proper (@leq X ==> @leq Y)).
 Proof.
   rewrite Proper_flip.
   apply: (@sup_closed'_monotone (dual X) _ (dual Y)).
 Qed.
 Canonical Structure mon_ipo: IPO l :=
   IPO.cast (X-mon->Y) (sub_ipo (@po_morphism_as_sig X Y) inf_closed'_monotone).
End s.

Definition top {l} {X: IPO l} {L: sE<<l}: X := ginf kE (has_slevel kE l L) tt.
Definition cap {l} {X: IPO l} {L: sB<<l} (x y: X): X := ginf kB (has_slevel kB l L) (x,y).
Definition cinf {l} {X: IPO l} {L: sEC<<l} (P: X -> Prop) (C: chain (X:=dual X) P): X := ginf kC (has_slevel kC l L) (exist _ P C).
Definition dinf {l} {X: IPO l} {L: sED<<l} (P: X -> Prop) (D: directed (X:=dual X) P): X := ginf kD (has_slevel kD l L) (exist _ P D). 
Definition iinf {l} {X: IPO l} {L: sA<<l} {I} (P: I -> Prop) (f: I -> X): X := ginf kA (has_slevel kA l L) (existT _ I (P,f)). 
Notation inf P := (iinf P id). 
Infix "⊓" := cap (left associativity, at level 50). 
Arguments cinf {_ _ _}. 
Arguments dinf {_ _ _}. 

Lemma is_inf_top {l} {X: IPO l} {L: sE<<l}: @is_inf X bot top.
Proof. apply: ginf_spec. Qed.
Lemma is_inf_cap {l} {X: IPO l} {L: sB<<l} (x y: X): is_inf (pair x y) (x ⊓ y).
Proof. apply: ginf_spec. Qed.
Lemma is_inf_cinf {l} {X: IPO l} {L: sEC<<l} (P: X -> Prop) C: is_inf P (cinf P C).
Proof. apply: ginf_spec. Qed.
Lemma is_inf_dinf {l} {X: IPO l} {L: sED<<l} (P: X -> Prop) D: is_inf P (dinf P D).
Proof. apply: ginf_spec. Qed.
Lemma is_inf_iinf {l} {X: IPO l} {L: sA<<l} I P (f: I -> X): is_inf (image f P) (iinf P f).
Proof. apply: ginf_spec. Qed.
Lemma is_inf_inf {l} {X: IPO l} {L: sA<<l} (P: X -> Prop): is_inf P (inf P).
Proof. dual @is_sup_sup. Qed.

Lemma geq_cinf {l} {X: IPO l} {L: sEC<<l}: forall (P: X -> Prop) C x, P x -> cinf P C <= x. 
Proof. dual @leq_csup. Qed.
Lemma geq_dinf {l} {X: IPO l} {L: sED<<l}: forall (P: X -> Prop) D x, P x -> dinf P D <= x. 
Proof. dual @leq_dsup. Qed.
Lemma geq_iinf {l} {X: IPO l} {L: sA<<l}: forall I (P: I -> Prop) (f: I -> X) i, P i -> iinf P f <= f i. 
Proof. dual @leq_isup. Qed.
Lemma geq_inf {l} {X: IPO l} {L: sA<<l}: forall (P: X -> Prop) x, P x -> inf P <= x. 
Proof. dual @leq_sup. Qed.


Lemma top_spec {l} {X: IPO l} {L: sE<<l} (z: X): z <= top <-> True.
Proof. dual @bot_spec. Qed.
Lemma leq_top {l} {X: IPO l} {L: sE<<l} (z: X): z <= top.
Proof. dual @leq_bot. Qed.
#[export] Hint Extern 0 (_ <= top)=> apply: leq_top: core.

Lemma cap_spec {l} {X: IPO l} {L: sB<<l} (x y z: X): z <= x ⊓ y <-> z <= x /\ z <= y.
Proof. dual @cup_spec. Qed.

Lemma capA {l} {X: IPO l} {L: sB<<l} (x y z: X): x ⊓ (y ⊓ z) ≡ x ⊓ y ⊓ z. 
Proof. dual @cupA. Qed.

Lemma cinf_inf {l} {X: IPO l} {L: sA<<l} P C: cinf P C ≡[X] inf P.
Proof. dual @csup_sup. Qed.
Lemma dinf_inf {l} {X: IPO l} {L: sA<<l} P D: dinf P D ≡[X] inf P.
Proof. dual @dsup_sup. Qed.

Lemma cinf_bot {l} {X: IPO l} {L: sEC<<l} C: cinf bot C ≡[X] top.
Proof. dual @csup_bot. Qed.
Lemma dinf_bot {l} {X: IPO l} {L: sED<<l} D: dinf bot D ≡[X] top.
Proof. dual @dsup_bot. Qed.
Lemma inf_bot {l} {X: IPO l} {L: sA<<l}: inf bot ≡[X] top.
Proof. dual @sup_bot. Qed.

Lemma inf_pair {l} {X: IPO l} {L: sA<<l} (x y: X): inf (pair x y) ≡ x ⊓ y.
Proof. dual @sup_pair. Qed.

(* TODO: etc *)

