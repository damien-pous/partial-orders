From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Export hb_ipo.

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
HB.instance Definition _ := PO.copy level (kernel alt_level).
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

HB.mixin Record isGPO (l: level) X := {}.
HB.structure Definition GPO (l: level) :=
  { X of isSetoid X & isPO X & isSPO (suplevel l) X & isIPO (inflevel l) X & isGPO l X }.

HB.instance Definition _ l (X: GPO.type l) := isGPO.Build (dual_level l) (dual X). 
Ltac dual2 t :=
  match type of t with
  | forall l, forall X: GPO.type l, _ =>
      match goal with
      | X: GPO.type ?l |- _ => apply: (t _ (dual X))
      end
  end.
Ltac dual t ::= dual2 t || dual1 t || dual0 t.

(* lattice of booleans, complete lattice of Propositions *)
HB.instance Definition _ := isGPO.Build (lSI pF pF) bool.
HB.instance Definition _ := isGPO.Build lA Prop.

Section sub.
 Context {l} {X: GPO.type l}.
 Definition closed' (P: X -> Prop):= sup_closed' P /\ inf_closed' P.
 #[export] Instance closed'_eqv: Proper (eqv==>eqv) closed'.
 Proof. move=>P Q PQ. by rewrite /closed' PQ. Qed.

 Definition closed_sig P (HP: closed' P) := sig P.
 HB.instance Definition _ P HP := SPO.copy (@closed_sig P HP) (sup_closed_sig (proj1 HP)).
 HB.instance Definition _ P HP := IPO.copy (@closed_sig P HP) (inf_closed_sig (proj2 HP)).
 HB.instance Definition _ P HP := isGPO.Build l (@closed_sig P HP).
End sub.

(** GPOs from retractions (and thus isomorphisms given the induced order on [A]) *)
HB.instance Definition _ {A: Type} {l} (X: GPO.type l)
  (r: A->X) (i: X->A) (ri: r ∘ i ≡ types_id)
  := isGPO.Build l (retract_of ri). 

(* (** altogether, we get general sub-GPOs  *) *)
(* Section c. *)
(*  Context {A: Type} {l} {X: GPO l} (P: X -> Prop). *)
(*  Variable r: A->sig P. *)
(*  Variable i: sig P->A. *)
(*  Hypothesis ri: r°i ≡ id.  *)
(*  Hypothesis HP: closed' P. *)
(*  Definition sub_gpo: GPO l := retract_gpo (sig_gpo HP) ri.  *)
(* End c. *)

(** the GPO of extensive functions *)
HB.instance Definition _ {X: Setoid.type} {l} {Y: GPO.type l}
  := isGPO.Build l (X-eqv->Y).

(** the GPO of monotone functions *)
HB.instance Definition _ {X: PO.type} {l} {Y: GPO.type l}
  := isGPO.Build l (X-mon->Y).


(** ** extended level-solving tactic *)

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
