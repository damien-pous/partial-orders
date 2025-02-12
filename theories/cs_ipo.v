Require Import ssreflect ssrfun ssrbool.
Require Export cs_spo.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

(** * partial orders with infima *)

(** generic infimum operation, given any type [A] that can be interpreted as subsets of [X] *)
Section s.
Context (X: PO.type). 
Definition gginf_op := @ggsup_op (dual X).
Definition ginf_op := @gsup_op (dual X).
Definition inf_op := @sup_op (dual X).

(** helpers to deduce some infrema out of other ones *)
Definition gginf_from: forall {A B} {Aset: A -> X -> Prop} {Bset: B -> X -> Prop},
  gginf_op Aset -> forall f: B -> A, Aset ∘ f ≡ Bset -> gginf_op Bset
  := @ggsup_from (dual X).
Arguments gginf_from {_ _ _ _}.
Definition inf_from_iinf: ginf_op kA -> inf_op := @sup_from_isup (dual X).
Definition cinf_from_inf: inf_op -> ginf_op kC := @csup_from_sup (dual X).
Definition dinf_from_inf: inf_op -> ginf_op kD := @dsup_from_sup (dual X).
Definition cinf_from_dinf: ginf_op kD -> ginf_op kC := @csup_from_dsup (dual X).
Definition top_from_cinf: ginf_op kC -> ginf_op kE := @bot_from_csup (dual X).
Definition top_from_dinf: ginf_op kD -> ginf_op kE := @bot_from_dsup (dual X).
Definition top_from_inf: inf_op -> ginf_op kE := @bot_from_sup (dual X).
Definition cap_from_inf: inf_op -> ginf_op kB := @cup_from_sup (dual X). 
Definition iinf_from_inf: inf_op -> ginf_op kA := @isup_from_sup (dual X).
Definition inf_from_cap_and_dinf: ginf_op kB -> ginf_op kD -> inf_op := @sup_from_cup_and_dsup (dual X).
End s.


(** ** class *)

Module IPO.
 Definition mixin (l: slevel) X (M: Setoid.mixin X) (N: PO.mixin M) :=
   forall k, l k -> ginf_op (PO.pack N) k.
 Structure type (l: slevel) := pack {
     sort:> Type;
     #[canonical=no] setoid_mix: Setoid.mixin sort;
     #[canonical=no] po_mix: PO.mixin setoid_mix;
     #[canonical=no] mix: mixin l po_mix;
 }.
 Canonical Structure to_PO l (X: type l) := PO.pack (po_mix X). 
 Canonical Structure to_Setoid l (X: type l) := Setoid.pack (setoid_mix X). 
 Notation copy T X := (@pack _ T _ _ (mix X)).
 Notation Build l T f :=
   (let X := T%type: PO.type in
    let M := PO.setoid_mix X in
    let N := PO.mix X in
    @pack l%core T M N f).
End IPO.
Canonical IPO.to_PO.
Canonical IPO.to_Setoid.
#[reversible] Coercion IPO.to_Setoid: IPO.type >-> Setoid.type.
#[reversible] Coercion IPO.to_PO: IPO.type >-> PO.type.
#[reversible] Coercion IPO.sort: IPO.type >-> Sortclass.

Canonical Structure dual_ipo l (X: IPO.type l) := @SPO.pack _ (dual X) _ _ (IPO.mix X). 
Canonical Structure dual_spo l (X: SPO.type l) := @IPO.pack _ (dual X) _ (PO.dual_mixin (SPO.po_mix X)) (SPO.mix X). 

Ltac dual1 t :=
  match type of t with
  | forall l, forall X: SPO.type l, _ =>
      match goal with
      | X: IPO.type ?l |- _ => apply: (t l (dual_ipo X))
      end
  | forall l, forall X: IPO.type l, _ =>
      match goal with
      | X: SPO.type ?l |- _ => apply: (t l (dual_spo X))
      end
  end.
Ltac dual t ::= dual1 t || dual0 t.

Section s.
Context {l} {X: IPO.type l}.
Definition ginf: forall k kl, args k (dual X) -> X := @gsup l (dual X). 
Lemma ginf_spec {k kl} (x: args k (dual X)): is_inf (X:=X) (setof k x) (ginf k kl x).
Proof. dual @gsup_spec. Qed.
Lemma geq_ginf k kl (x: args k (dual X)) (y: X): setof k x y -> ginf k kl x <= y.
Proof. dual @leq_gsup. Qed.
End s.


(** ** instances *)

(** unit trivial lattice *)
Program Canonical Structure unit_ipo := IPO.Build sA unit (fun k _ => exist _ (fun _ => tt) _).
Next Obligation.
  have E: forall P: unit -> Prop, (forall x, P x) <-> P tt by move=>P; split=>//?[]. 
  case=>/=. rewrite E/=. cbn. tauto.
Qed.

(** inf-semilattice of Booleans
    (infinite infima are not available constructively) *)
Program Canonical Structure bool_ipo :=
  IPO.Build sF bool
    (fun k => match k with
           | kE => fun _ => exist _ (fun _ => true) _
           | kB => fun _ => exist _ (fun '(x,y) => andb x y) _
           | kC | kD | kA  => sEmpty_rect _
           end).
Next Obligation. by case. Qed.
Next Obligation.
  move=>c/=. rewrite forall_pair. cbn.
  rewrite Bool.implb_andb_distrib_r -Bool.andb_true_iff//.
Qed.

(** complete inf-semilattice of Propositions
    (infinite suprema are available via impredicativity) *)
Program Canonical Structure Prop_ipo :=
  let iinf: ginf_op Prop kA := @exist ((sigset Prop)->Prop) _ (fun '(idx P f) => forall i, P i -> f i) _ in
  let inf:= inf_from_iinf iinf in
  IPO.Build sA Prop
    (fun k _ => match k with
        | kE => exist _ (fun _ => True) _
        | kB => exist _ (fun '(p,q) => p/\q) _
        | kC => cinf_from_inf inf
        | kD => dinf_from_inf inf
        | kA => iinf
        end).
Next Obligation. destruct a as [I P f]; cbv. firstorder subst; apply H; eauto. Qed.
Next Obligation. cbv; firstorder. Qed.
Next Obligation. cbv; firstorder subst; eauto; apply H; eauto. Qed.

(** IPOs on (dependent) function space *)
Program Canonical Structure ipo_dprod {A l} (X: A -> IPO.type l) :=
  IPO.copy (forall a, X a) (dual_spo (dprod_spo (fun a => dual_ipo (X a)))).

(** direct product of IPOs *)
(* TODO: subtyping *)
Program Canonical Structure ipo_prod {l} (X Y: IPO.type l) :=
  IPO.copy (X*Y) (dual_spo (prod (dual X) (dual Y))).

(** sub-IPOs *)
Section sub.
 Context {l} {X: IPO.type l}.
 Definition inf_closed' (P: X -> Prop) :=
   forall k: K, forall kl: l k, forall x: args k (dual X), setof k x <= P ->  P (ginf k kl x).
 Lemma inf_closed_inf_closed': inf_closed <= inf_closed'.
 Proof. dual @sup_closed_sup_closed'. Qed.
 #[export] Instance inf_closed'_eqv: Proper (eqv==>eqv) inf_closed'. 
 Proof. dual @sup_closed'_eqv. Qed.

 Definition inf_closed_sig P (HP: inf_closed' P) := sig P.
 Variables (P: X -> Prop) (HP: inf_closed' P). 
 Canonical Structure sig_ipo P (HP: inf_closed' P) :=
   IPO.copy (inf_closed_sig HP) (dual_spo (sig_spo HP)). 
End sub.

(** IPOs from retractions (and thus isomorphisms given the induced order on [A]) *)
Section c.
 Context {A l} (X: IPO.type l) {r: A->X} {i: X->A} (ri: r ∘ i ≡ types_id).
 Canonical Structure retract_ipo :=
   IPO.copy (retract_of ri) (dual_spo (retract_spo (dual X) ri)). 
End c.
Arguments retract_ipo [_ _] _ [_ _]. 

(** the IPO of extensional functions *)
Section s.
 Context {X: Setoid.type} {l} {Y: IPO.type l}.
 Lemma inf_closed'_extensional: inf_closed' (Proper (@eqv X ==> @eqv Y)).
 Proof. apply (@sup_closed'_extensional X l (dual Y)). Qed.
 Canonical Structure setoid_morphism_ipo :=
   IPO.copy (X-eqv->Y) 
     (retract_ipo (inf_closed_sig inf_closed'_extensional) (@setoid_morphism_as_sig X Y)).
End s.

(** the IPO of monotone functions *)
Section s.
 Context {X: PO.type} {l} {Y: IPO.type l}.
 Lemma inf_closed'_monotone: inf_closed' (Proper (@leq X ==> @leq Y)).
 Proof. 
   rewrite Proper_flip.
   apply (@sup_closed'_monotone (dual X) l (dual Y)).
 Qed.
 Canonical Structure po_morphism_ipo :=
   IPO.copy (X-mon->Y) 
     (retract_ipo (inf_closed_sig inf_closed'_monotone) (@po_morphism_as_sig X Y)).
End s.

(** ** theory *)

Section s.
Context {l} {X: IPO.type l}.
Definition top {L}: X := @bot l (dual X) L. 
Definition cap {L}: X -> X -> X := @cup l (dual X) L.
Definition cinf {L}: forall (P: X -> Prop) (C: chain (X:=dual X) P), X := @csup l (dual X) L.
Definition dinf {L}: forall (P: X -> Prop) (C: codirected P), X := @dsup l (dual X) L.
Definition iinf {L} {I}: forall (P: I -> Prop) (f: I -> X), X := @isup l (dual X) L I.
End s.
Arguments cinf {_ _ _}. 
Arguments dinf {_ _ _}. 
Notation inf P := (iinf P types_id). 
Infix "⊓" := cap (left associativity, at level 50). 

Section s.
Context {l} {X: IPO.type l}.

Lemma is_inf_top {L: sE<<l}: @is_inf X bot top.
Proof. apply: ginf_spec. Qed.
Lemma is_inf_cap {L: sB<<l} (x y: X): is_inf (pair x y) (x ⊓ y).
Proof. apply: ginf_spec. Qed.
Lemma is_inf_cinf {L: sEC<<l} (P: X -> Prop) C: is_inf P (cinf P C).
Proof. apply: ginf_spec. Qed.
Lemma is_inf_dinf {L: sED<<l} (P: X -> Prop) D: is_inf P (dinf P D).
Proof. apply: ginf_spec. Qed.
Lemma is_inf_iinf {L: sA<<l} I P (f: I -> X): is_inf (image f P) (iinf P f).
Proof. apply: ginf_spec. Qed.
Lemma is_inf_inf {L: sA<<l} (P: X -> Prop): is_inf P (inf P).
Proof. dual @is_sup_sup. Qed.

Lemma geq_cinf {L: sEC<<l}: forall (P: X -> Prop) C x, P x -> cinf P C <= x. 
Proof. dual @leq_csup. Qed.
Lemma geq_dinf {L: sED<<l}: forall (P: X -> Prop) D x, P x -> dinf P D <= x. 
Proof. dual @leq_dsup. Qed.
Lemma geq_iinf {L: sA<<l}: forall I (P: I -> Prop) (f: I -> X) i, P i -> iinf P f <= f i. 
Proof. dual @leq_isup. Qed.
Lemma geq_inf {L: sA<<l}: forall (P: X -> Prop) x, P x -> inf P <= x. 
Proof. dual @leq_sup. Qed.

Lemma top_spec {L: sE<<l} (z: X): z <= top <-> True.
Proof. dual @bot_spec. Qed.
Lemma leq_top {L: sE<<l} (z: X): z <= top.
Proof. dual @geq_bot. Qed.

Lemma cap_spec {L: sB<<l} (x y z: X): z <= x ⊓ y <-> z <= x /\ z <= y.
Proof. dual @cup_spec. Qed.

Lemma capA {L: sB<<l} (x y z: X): x ⊓ (y ⊓ z) ≡ x ⊓ y ⊓ z. 
Proof. dual @cupA. Qed.

Lemma cinf_inf {L: sA<<l} P C: cinf P C ≡[X] inf P.
Proof. dual @csup_sup. Qed.
Lemma dinf_inf {L: sA<<l} P D: dinf P D ≡[X] inf P.
Proof. dual @dsup_sup. Qed.

Lemma cinf_bot {L: sEC<<l} C: cinf bot C ≡[X] top.
Proof. dual @csup_bot. Qed.
Lemma dinf_bot {L: sED<<l} D: dinf bot D ≡[X] top.
Proof. dual @dsup_bot. Qed.
Lemma inf_bot {L: sA<<l}: inf bot ≡[X] top.
Proof. dual @sup_bot. Qed.

Lemma inf_pair {L: sA<<l} (x y: X): inf (pair x y) ≡ x ⊓ y.
Proof. dual @sup_pair. Qed.

End s.
#[export] Hint Extern 0 (_ <= top)=> apply: leq_top: core.

(* TODO: etc *)
