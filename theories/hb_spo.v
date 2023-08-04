From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Export hb_po.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

(** * levels & suprema types *)

(*
E: empty
B: binary
C: chains (possibly empty for now)
D: directed (possibly empty for now)
A: all

D=>C=>E
A=>E,B,C,D
B+D=>A

then: Distributive, Heyting, Boole

*)

Variant K := kE | kB | kC | kD | kA.
HB.instance Definition _ := eq_setoid K.
Definition leq_K h k :=
  match h,k with
  | _,kA
  | kE,(kE|kC|kD)
  | kB,kB
  | kC,(kC|kD)
  | kD,kD => True
  | _,_ => False
  end.
Lemma po_K: po_axm leq_K.
Proof.
  split.
  - split. by case. by do 3 (case=>//).
  - (case; case=>//=); intuition discriminate.
Qed.
HB.instance Definition _ := isPO.Build K po_K. 

Inductive sigset (X: Type) := idx: forall I: Type, (I->Prop) -> (I->X) -> sigset X.
Definition sig2set {X}: sigset X -> (X -> Prop) := fun '(idx P f) => image f P.
Definition set2sig {X}: (X -> Prop) -> sigset X := fun P => idx P (fun x => x).
Lemma set2sig2set {X} (P: X -> Prop): sig2set (set2sig P) ≡ P.
Proof. cbv; firstorder congruence. Qed.

Definition args k (X: PO.type): Type :=
  match k with
  | kE => unit
  | kB => X * X
  | kC => sig (@chain X)
  | kD => sig (@directed X)
  | kA => sigset X
  end.
Definition setof {X: PO.type} k: args k X -> X -> Prop :=
  match k with
  | kE => fun _ => empty
  | kB => fun '(x,y) => pair x y
  | kC => @proj1_sig _ _
  | kD => @proj1_sig _ _
  | kA => @sig2set X
  end.

Section map_args.
 Context {X Y: PO.type}.
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
   exists (f z). split; auto. split; by apply f.
 Qed.
 Definition map_args k: args k X -> args k Y :=
   match k return args k X -> args k Y with
   | kE => types_id
   | kB => fun '(x,y) => (f x, f y)
   | kC => fun '(exist _ P C) => exist _ (image f P) (image_chain C)
   | kD => fun '(exist _ P D) => exist _ (image f P) (image_directed D)
   | kA => fun '(idx P g) => idx P (f ∘ g)
   end.
 Lemma setof_map_args k: forall x, setof k (map_args k x) ≡ image f (setof k x).
 Proof.
   case: k=>/=[_|[x x']|[P C]|[P D]|[I P g]]//=; cbn;
           try firstorder congruence.
   apply image_comp.
 Qed. 
End map_args.

Variant plevel := pN | pE | pB | pF | pEC | pFC | pED.
HB.instance Definition _ := eq_setoid plevel.
Definition leq_plevel h k :=
  match h,k with
  | pN,_
  | pE,(pE|pF|pEC|pFC|pED)
  | pB,(pB|pF|pFC)
  | pF,(pF|pFC)
  | pFC,pFC
  | pEC,(pEC|pED|pFC)
  | pED,pED => True
  | _,_ => False
  end.
Lemma po_plevel: po_axm leq_plevel.
Proof.
  split. 
  - split. by case. by do 3 (case=>//). 
  - (case; case=>//=); intuition discriminate.
Qed.
HB.instance Definition _ := isPO.Build plevel po_plevel. 

Definition plevel_fun (l: plevel) k: bool :=
  match k,l with
  | kE,(pE|pF|pEC|pFC|pED)
  | kB,(pB|pF|pFC)
  | kC,(pEC|pFC|pED)
  | kD,(pED) => true
  | _,_ => false
  end.
Coercion plevel_fun: plevel >-> Funclass.
Lemma plevel_mon: Proper (leq ==> leq) plevel_fun.
Proof. by case; case=>//=_; case. Qed.

Definition slevel := option plevel.
Definition sN: slevel := Some pN. 
Definition sE: slevel := Some pE. 
Definition sB: slevel := Some pB. 
Definition sF: slevel := Some pF. 
Definition sEC: slevel := Some pEC. 
Definition sFC: slevel := Some pFC. 
Definition sED: slevel := Some pED. 
Definition sA: slevel := None.
Definition slevel_fun (l: slevel) k :=
  match l,k with
  | None,_ => true
  | Some p,k => p k
  end.
Lemma slevel_mon: Proper (leq ==> leq) slevel_fun.
Proof.
  case=>[p|]; case=>[q|]//=.
  move=>pq; case=>//; by apply plevel_mon.
  move=>_; case=>//; by case: p.
Qed.
Definition slevel_fun' (l: slevel): K -> SProp := fun k => is_true' (slevel_fun l k).
Coercion slevel_fun': slevel >-> Funclass.

Definition slevel_of k: slevel :=
  match k with
  | kE => sE
  | kB => sB
  | kC => sEC
  | kD => sED
  | kA => sA
  end.
Lemma has_slevel_of: forall k, slevel_of k k.
Proof. by case. Qed.
Lemma has_slevel (k: K) (l: slevel): slevel_of k <= l -> l k.
Proof.
  move=>H. move: (has_slevel_of k).
  move: (slevel_mon _ _ H k).
  rewrite /slevel_fun'. 
  case (slevel_fun (slevel_of k) k); cbn. 2: by move=>? [].
  move=>E _. by apply eq_true_is_true'. 
Qed.

Section s.
Notation "1" := true.
Notation "0" := false.
Definition slevel_for (f: K -> bool): slevel :=
  if f kA then None
  else match f kE, f kB, f kC, f kD return slevel with
       | _,1,_,1 => sA
       | 0,0,0,0 => sN
       | 1,0,0,0 => sE
       | 0,1,0,0 => sB
       | 1,1,0,0 => sF
       | _,0,1,0 => sEC
       | _,1,1,0 => sFC
       | _,0,_,1 => sED
       end.
End s.
Lemma forall_K (P: K -> Prop): (forall k, P k) <-> P kE /\ P kB /\ P kC /\ P kD /\ P kA.
Proof. split; auto=>?[]; tauto. Qed.
Lemma slevel_adj f (l: slevel): slevel_for f <= l <-> f <= slevel_fun l.
Proof.
  have I: forall b, false <= b <-> True. by case. 
  have I': forall b, b <= true <-> True. by case. 
  have E: forall b, true <= b <-> b. by case. 
  setoid_rewrite forall_K. unfold slevel_for.
  case: (f kA)=>//=. {
    case: l=>//=. cbn; intuition discriminate.
    rewrite !I'. cbn; tauto. 
  }
  case: (f kE); rewrite ?(I,I',E);
    case: (f kB); rewrite ?(I,I',E);
    case: (f kC); rewrite ?(I,I',E);
    case: (f kD); rewrite ?(I,I',E);
  case: l=>[[]|]; cbn; intuition congruence.
Qed.

Class lower {X: PO.type} (h k: X): Prop := Lower: h <= k.
Infix "<<" := lower (at level 70).
#[export] Instance PreOrder_lower {X}: PreOrder (@lower X).
Proof. apply PreOrder_leq. Qed.
Lemma lower_trans {X: PO.type} (k h l: X) (kh: k<<h) (hl: h<<l): k<<l.
Proof. etransitivity; eassumption. Qed.
Ltac solve_lower :=
  solve [ reflexivity | assumption |
          match goal with H: ?h << ?l |- ?k << ?l => exact: (@lower_trans _ k h l I H) end].
#[export] Hint Extern 0 (lower _ _) => solve_lower: typeclass_instances.

(** generic supremum operation, given any type [A] that can be interpreted as subsets of [X] *)
Section s.
Context (X: PO.type). 
Definition ggsup_op {A} (setof: A -> X -> Prop) :=
  {sup: A -> X | forall a, is_sup (setof a) (sup a)}.
Definition gsup_op k := (ggsup_op (setof k)).
Definition sup_op := (ggsup_op types_id).

(** helpers to deduce some suprema out of other ones *)
Definition ggsup_from {A B} {Aset: A -> X -> Prop} {Bset: B -> X -> Prop}:
  ggsup_op Aset -> forall f: B -> A, Aset ∘ f ≡ Bset -> ggsup_op Bset.
  move=>sup f Hf. eexists (fun b => proj1_sig sup (f b)).
  abstract by move=>b; rewrite -(Hf b); apply (proj2_sig sup).
Defined.
Arguments ggsup_from {_ _ _ _}.
Program Definition sup_from_isup (isup: gsup_op kA): sup_op := ggsup_from isup set2sig set2sig2set.
Program Definition csup_from_sup (sup: sup_op): gsup_op kC := ggsup_from sup (@proj1_sig _ _) _.
Program Definition dsup_from_sup (sup: sup_op): gsup_op kD := ggsup_from sup (@proj1_sig _ _) _.
Program Definition csup_from_dsup (dsup: gsup_op kD): gsup_op kC :=
  ggsup_from dsup (fun '(exist _ P C) => exist _ P (chain_directed C)) _.
Next Obligation. by move=>[]. Qed.
Program Definition bot_from_csup (csup: gsup_op kC): gsup_op kE :=
  ggsup_from csup (fun _: unit => exist _ _ chain_empty) _.
Program Definition bot_from_dsup (dsup: gsup_op kD): gsup_op kE :=
  ggsup_from dsup (fun _: unit => exist _ _ directed_empty) _.
Program Definition bot_from_sup (sup: sup_op): gsup_op kE :=
  ggsup_from sup (fun _: unit => empty) _.
Program Definition cup_from_sup (sup: sup_op): gsup_op kB :=
  ggsup_from sup (fun '(x,y) => pair x y) _.
Next Obligation. by move=>[]. Qed.
(* TOREPORT: strangely, using the same pattern to obtain the lemma below universe-conflicts with [sup_from_isup]  *)
(* Program Definition isup_from_sup (sup: sup_op): gsup_op kA := ggsup_from sup sig2set _. *)
(* fortunately, unfolding its resulting def leaves the universes untouched *)
(* Print Universes Subgraph (sigset.u0 sig2set.u0 set2sig.u0). *)
Definition isup_from_sup (sup: sup_op): gsup_op kA.
  exists (fun P => proj1_sig sup (sig2set P)).
  abstract by move=>?; apply (proj2_sig sup).
Defined.
(* Print Universes Subgraph (sigset.u0 sig2set.u0 set2sig.u0). *)
Definition sup_from_cup_and_dsup: gsup_op kB -> gsup_op kD -> sup_op.
  move=>cup dsup.
  unshelve eexists (fun P => proj1_sig dsup (exist _ (sup_closure P) _)).
  abstract (move=>x y Px Py; exists (proj1_sig cup (x,y)); split; [
                (apply: sc_sup; [|apply (proj2_sig cup)])=>_[->|->]// |
                move: (proj1 (proj2_sig cup (x,y) (proj1_sig cup (x,y))))=>H; split; apply H=>//=; rewrite /pair; auto ]).
  abstract (move=>P; apply is_sup_closure, (proj2_sig dsup)).
Defined.
End s.

(** * partial orders with suprema *)

(** ** class *)

Definition spo_ops (l: slevel) X := (forall k, l k -> gsup_op X k).
HB.mixin Record isSPO (l: slevel) X of PO X := {
    #[canonical=no] SPO_ops: spo_ops l (X: PO.type)
}.
HB.structure Definition SPO (l: slevel) := { X of isSPO l X & }.

Definition gsup {l} {X: SPO.type l} k kl: args k X -> X :=
  proj1_sig (SPO_ops k kl).
Definition gsup_spec {l} {X: SPO.type l} {k kl}:
  forall x: args k X, is_sup (setof k x) (gsup k kl x) :=
  proj2_sig (SPO_ops k kl).
Lemma leq_gsup {l} {X: SPO.type l} k kl x (y: X): setof k x y -> y <= gsup k kl x.
Proof. apply leq_is_sup, gsup_spec. Qed.

(** ** instances *)

(** unit *)
Program Definition spo_unit: spo_ops sA unit := fun k _ => exist _ (fun _ => tt) _.
Next Obligation.
  have E: forall P: unit -> Prop, (forall x, P x) <-> P tt by move=>P; split=>//?[]. 
  case=>/=. rewrite E/=. cbn. tauto.
Qed.
HB.instance Definition _ := isSPO.Build sA unit spo_unit. 

(** sup-semilattice of Booleans
    (infinite suprema are not available constructively) *)
Program Definition spo_bool: spo_ops sF bool := 
  fun k => match k with
        | kE => fun _ => exist _ (fun _ => false) _
        | kB => fun _ => exist _ (fun '(x,y) => orb x y) _
        | kC | kD | kA  => sEmpty_rect _
        end.
Next Obligation. by case. Qed.
Next Obligation. 
  move=>c/=. rewrite forall_pair. cbn.
  rewrite !Bool.le_implb Bool.implb_orb_distrib_l Bool.andb_true_iff//.
Qed.
HB.instance Definition _ := isSPO.Build sF bool spo_bool. 

(** complete sup-semilattice of Propositions
    (infinite suprema are available via impredicativity) *)
Definition spo_Prop: spo_ops sA Prop.
  unshelve refine (
  let isup: gsup_op Prop kA := exist _ (fun '(idx P f) => exists2 i, P i & f i) _ in
  let sup:= sup_from_isup isup in
  (* let sup: sup_op Prop := exist _ (fun P => exists2 p, P p & p) _ in *)
  (* let isup:= isup_from_sup sup in *)
  fun k _ => match k with
        | kE => exist _ (fun _ => False) _
        | kB => exist _ (fun '(p,q) => p\/q) _
        | kC => csup_from_sup sup
        | kD => dsup_from_sup sup
        | kA => isup
        end).
  all: abstract by try clear isup sup; move=>[]; cbv; firstorder subst; eauto.
Defined.
HB.instance Definition _ := isSPO.Build sA Prop spo_Prop. 

(** SPOs on (dependent) function space *)
Program Definition spo_dprod {A l} {X: A -> SPO.type l}: spo_ops l (forall a, X a) :=
  fun k kl => exist _ (fun F a => gsup k kl (map_args (app a) k F)) _.
Next Obligation.
  apply dprod_sup=>a'. eapply Proper_is_sup.
  2: reflexivity. 2: apply: gsup_spec.
  apply eqv_covered. by rewrite setof_map_args. 
Qed.
HB.instance Definition _ A l (X: A -> SPO.type l) :=
  isSPO.Build l (forall a, X a) (@spo_dprod A l X). 

(** direct product of SPOs *)
Section prod.
 Context {l} {X Y: SPO.type l}.
 Program Definition spo_prod: spo_ops l (prod X Y) :=
  fun k kl => exist _ (fun F => (gsup k kl (map_args fst k F), gsup k kl (map_args snd k F))) _.
(* alternatively, via [dprod_sup] below, with [A=bool] *)
 Next Obligation.
   apply prod_sup; split; (eapply Proper_is_sup; [apply eqv_covered|reflexivity|apply gsup_spec]).
   all: by rewrite setof_map_args. 
 Qed.
 HB.instance Definition _ :=
   isSPO.Build l (prod X Y) spo_prod.
End prod.

(* TODO: option (with None above or below) ? *)

(** sub-SPOs *)
Section sub.
 Context {l} {X: SPO.type l}.
 Definition sup_closed' (P: X -> Prop) :=
   forall k: K, forall kl: l k, forall x, setof k x <= P ->  P (gsup k kl x).
 Lemma sup_closed_sup_closed': sup_closed <= sup_closed'. 
 Proof. move=>P H k kl x Hx. apply: H. apply Hx. apply gsup_spec. Qed.
 #[export] Instance sup_closed'_eqv: Proper (eqv==>eqv) sup_closed'.
 Proof. apply Proper_half=>P Q H HP k kl x E. apply H. apply HP. by rewrite H. Qed.
 
 Definition sup_closed_sig P (HP: sup_closed' P) := sig P.
 Variables (P: X -> Prop) (HP: sup_closed' P). 
 Program Definition spo_sig: spo_ops l (sup_closed_sig HP) := 
   fun k kl => exist _ (fun F => exist _ (gsup k kl (map_args (@proj1_sig X P) k F)) _) _. 
 Next Obligation.
   apply: HP. rewrite setof_map_args. 
   by move=>_ [[x Px] [_ ->]]. 
 Qed.
 Next Obligation.
   apply kern_sup=>/=. eapply Proper_is_sup.
   2: reflexivity. 2: apply: gsup_spec.
   apply eqv_covered. by rewrite setof_map_args. 
 Qed.
 (* TO ASK: the following instance does not seem necessary to me:
    [sub_closed_sig] is already recognised as a Setoid/PO, by unfolding to [sig] 
    Check (sup_closed_sig HP: Setoid.type).  
    Check (sup_closed_sig HP: PO.type).      
    But if we don't mark this instance explicitly, then the second (new) declaration does not declare the expected CS *)
 HB.instance Definition _ := PO.copy (sup_closed_sig HP) (sig P).
 HB.instance Definition _ := isSPO.Build l (sup_closed_sig HP) spo_sig.
End sub.

(** SPOs from retractions (and thus isomorphisms given the induced order on [A]) *)
Definition retract_of {A} {X: Setoid.type}
  (r: A->X) (i: X->A) (ri: r ∘ i ≡ types_id) := kernel r.
(* TOFIX: like above, the following two declarations should not be necessary *)
HB.instance Definition _ A X r i ri := Setoid.copy (@retract_of A X r i ri) (kernel r).
HB.instance Definition _ A (X: PO.type) r i ri := PO.copy (@retract_of A X r i ri) (kernel r).
Section c.
 Context {A: Type} {l} (X: SPO.type l).
 Variables (r: A->X) (i: X->A) (ri: r ∘ i ≡ types_id).
 Program Definition spo_retract: spo_ops l (@retract_of A X r i ri) := 
   fun k kl => exist _ (fun x => i (gsup k kl (map_args (kernelf r) k x))) _.
 Next Obligation.
   apply kern_sup. eapply Proper_is_sup. 2: apply: ri. 2: apply: gsup_spec.
   apply eqv_covered. by rewrite setof_map_args.
 Qed.
 HB.instance Definition _ := isSPO.Build l (retract_of ri) spo_retract.
End c.

(** the SPO of extensional functions *)
Section s.
 Context {X: Setoid.type}.
 Section s'.
 Context {Y: Setoid.type}.
 Definition setoid_morphism_to_sig (f: X-eqv->Y): sig (Proper (eqv==>eqv)) :=
   exist (Proper (eqv ==> eqv)) f extensional.
 Definition sig_to_setoid_morphism (f: sig (Proper (eqv==>eqv))): X-eqv->Y :=
   (* TODO nicer way? *)
   @setoid_morphism.pack_ X Y (proj1_sig f) (isExtensional.Axioms_ _ _ (proj2_sig f)).
 Lemma setoid_morphism_as_sig:
  setoid_morphism_to_sig ∘ sig_to_setoid_morphism ≡ types_id. 
 Proof. by case. Qed.
 End s'.
 Context {l} {Y: SPO.type l}.
 Lemma sup_closed'_extensional: sup_closed' (Proper (@eqv X ==> @eqv Y)).
 Proof.
   move=>k kl P HP. apply Proper_half=>x y xy.
   apply gsup_spec=>z Hz. apply setof_map_args in Hz as [f [Hf ->]].
   transitivity (f y). apply eqv_leq, (HP _ Hf _ _ xy). apply leq_gsup. 
   apply setof_map_args. by exists f.
 Qed.
 (* NOTE: we need kernel compositions to behave well in order the following instance to typecheck *)
 HB.instance Definition _ :=
   SPO.copy (X-eqv->Y)
     (* TOTHINK: if the aforementioned superfluous-looking instances are not declared, we need the SPO type annotation below *)
     (retract_of (X:=sup_closed_sig sup_closed'_extensional(* : SPO.type _ *)) (@setoid_morphism_as_sig Y)).
End s.

(** the SPO of monotone functions *)
Section s.
 Context {X: PO.type}.
 Section s'.
 Context {Y: PO.type}.
 Definition po_morphism_to_sig (f: X-mon->Y): sig (Proper (leq==>leq)) :=
   exist (Proper (leq ==> leq)) f monotone.
 Definition sig_to_po_morphism (f: sig (Proper (leq==>leq))): X-mon->Y :=
   (* TODO nicer way? *)
   @po_morphism.pack_ X Y (proj1_sig f) (isMonotone.Axioms_ _ _ (proj2_sig f))
     (isExtensional.Axioms_ _ _ (op_leq_eqv_1 (Hf:=proj2_sig f))).
 Lemma po_morphism_as_sig:
  po_morphism_to_sig ∘ sig_to_po_morphism ≡ types_id. 
 Proof. by case. Qed.
 End s'.
 Context {l} {Y: SPO.type l}.
 Lemma sup_closed'_monotone: sup_closed' (Proper (@leq X ==> @leq Y)).
 Proof.
   move=>k kl P HP x y xy.
   apply gsup_spec=>z Hz. apply setof_map_args in Hz as [f [Hf ->]].
   transitivity (f y). apply (HP _ Hf _ _ xy). apply leq_gsup. 
   apply setof_map_args. by exists f.
 Qed.
 (* NOTE: we need kernel compositions to behave well in order the following instance to typecheck *)
 HB.instance Definition _ :=
   SPO.copy (X-mon->Y)
     (retract_of (X:=sup_closed_sig sup_closed'_monotone(* : SPO.type _ *)) (@po_morphism_as_sig Y)).
End s.

(** ** theory  *)


Section s.
Context {l} {X: SPO.type l}.
Definition bot {L: sE<<l}: X := gsup kE (has_slevel kE l L) tt.
Definition cup {L: sB<<l} (x y: X): X := gsup kB (has_slevel kB l L) (x,y).
Definition csup {L: sEC<<l} (P: X -> Prop) (C: chain P): X := gsup kC (has_slevel kC l L) (exist _ P C).
Definition dsup {L: sED<<l} (P: X -> Prop) (D: directed P): X := gsup kD (has_slevel kD l L) (exist _ P D). 
Definition isup {L: sA<<l} {I} (P: I -> Prop) (f: I -> X): X := gsup kA (has_slevel kA l L) (idx P f).
End s.
Arguments csup {_ _ _}. 
Arguments dsup {_ _ _}. 
Notation sup P := (isup P (fun x => x)).
Infix "⊔" := cup (left associativity, at level 50). 

Section s.
Context {l} {X: SPO.type l}.
Lemma is_sup_bot {L: sE<<l}: @is_sup X bot bot.
Proof. apply: gsup_spec. Qed.
Lemma is_sup_cup {L: sB<<l} (x y: X): is_sup (pair x y) (x ⊔ y).
Proof. apply: gsup_spec. Qed.
Lemma is_sup_csup {L: sEC<<l} (P: X -> Prop) C: is_sup P (csup P C).
Proof. apply: gsup_spec. Qed.
Lemma is_sup_dsup {L: sED<<l} (P: X -> Prop) D: is_sup P (dsup P D).
Proof. apply: gsup_spec. Qed.
Lemma is_sup_isup {L: sA<<l} I P (f: I -> X): is_sup (image f P) (isup P f).
Proof. apply: gsup_spec. Qed.
Lemma is_sup_sup {L: sA<<l} (P: X -> Prop): is_sup P (sup P).
Proof. rewrite -{1}(image_id P). apply: is_sup_isup. Qed.

Lemma leq_csup {L: sEC<<l} (P: X -> Prop) C x: P x -> x <= csup P C. 
Proof. move=>Px. by apply: leq_gsup. Qed.
Lemma leq_dsup {L: sED<<l} (P: X -> Prop) D x: P x -> x <= dsup P D. 
Proof. move=>Px. by apply leq_gsup. Qed.
Lemma leq_isup {L: sA<<l} I (P: I -> Prop) (f: I -> X) i: P i -> f i <= isup P f. 
Proof. move=>Pi. by apply leq_gsup=>/=; auto. Qed.
Lemma leq_sup {L: sA<<l} (P: X -> Prop) x: P x -> x <= sup P. 
Proof. apply: leq_isup. Qed.

Lemma bot_spec {L: sE<<l} (z: X): bot <= z <-> True.
Proof. rewrite is_sup_bot. cbn. firstorder. Qed.
Lemma geq_bot {L: sE<<l} (z: X): bot <= z.
Proof. by apply bot_spec. Qed.

Lemma cup_spec {L: sB<<l} (x y z: X): x ⊔ y <= z <-> x <= z /\ y <= z.
Proof. rewrite is_sup_cup /pair; intuition subst; auto. Qed.

Lemma cupA {L: sB<<l} (x y z: X): x ⊔ (y ⊔ z) ≡ x ⊔ y ⊔ z. 
Proof. apply: from_above=>t. rewrite 4!cup_spec. tauto. Qed.
(* TODO: etc... *)

Lemma csup_sup {L: sA<<l} P C: csup P C ≡[X] sup P.
Proof. apply: supU. apply is_sup_csup. apply is_sup_sup. Qed.
Lemma dsup_sup {L: sA<<l} P D: dsup P D ≡[X] sup P.
Proof. apply: supU. apply is_sup_dsup. apply is_sup_sup. Qed.

Lemma csup_bot {L: sEC<<l} C: csup bot C ≡[X] bot.
Proof. apply: supU. apply is_sup_csup. apply is_sup_bot. Qed.
Lemma dsup_bot {L: sED<<l} D: dsup bot D ≡[X] bot.
Proof. apply: supU. apply is_sup_dsup. apply is_sup_bot. Qed.
Lemma sup_bot {L: sA<<l}: sup bot ≡[X] bot.
Proof. apply: supU. apply is_sup_sup. apply is_sup_bot. Qed.

Lemma sup_pair {L: sA<<l} (x y: X): sup (pair x y) ≡ x ⊔ y.
Proof. apply: supU. apply is_sup_sup. apply is_sup_cup. Qed.

Lemma directed_sup_closure {L: sB<<l} (P: X -> Prop): directed (sup_closure P).
Proof.
  (* TODO: use in [sup_from_cup_and_dsup] *)
  move=>x y Px Py. exists (x⊔y); split. 2: by apply cup_spec.
  apply sc_sup with (pair x y). 2: apply is_sup_cup.
  by move=>z [->|->].
Qed.
Corollary sup_dsup {L: sA<<l} (P: X -> Prop):
  sup P ≡ dsup (sup_closure P) (directed_sup_closure (P:=P)).
Proof. rewrite dsup_sup. apply: supU. apply is_sup_sup. apply is_sup_closure, is_sup_sup. Qed.

End s.
#[export] Hint Extern 0 (bot <= _)=> apply: geq_bot: core.


(** ** optimised constructor *)
(** TOTHINK: is it really useful?  *)
Module sreduce.
  Section s.
  Variable T: K -> Type.
  Variable f: forall k, option (T k).
  Coercion option_bool {A} (x: option A) := match x with None => false | Some _ => true end.
  Ltac discriminate_levels :=
    (by move=>[] ||
       lazymatch goal with |- context [f ?k] => (* idtac k; *) case: (f k)=>[/=_|]; discriminate_levels end).
  Hypothesis H: forall h k: K, h <= k -> T k -> T h.
  Hypothesis H': T kB -> T kD -> T kA. 
  Definition abstract_reduce: forall k: K, slevel_for f k -> T k.
    unfold slevel_for. case.
    - case (f kE)=>[//|]. 
      case (f kA)=>[v _|]. revert v. by apply H. 
      case (f kD)=>[v _|]. revert v. by apply H. 
      case (f kC)=>[v _|]. revert v. by apply H.
      discriminate_levels. 
    - case (f kB)=>[//|]. 
      case (f kA)=>[v _|]. revert v. by apply H. 
      discriminate_levels. 
    - case (f kC)=>[//|]. 
      case (f kA)=>[v _|]. revert v. by apply H. 
      case (f kD)=>[v _|]. revert v. by apply H. 
      discriminate_levels. 
    - case (f kD)=>[//|]. 
      case (f kA)=>[v _|]. revert v. by apply H. 
      discriminate_levels.
    - case (f kA)=>[//|/=]. 
      case (f kE)=>/=[_|];
        (case (f kB)=>/=[vB|]; [|discriminate_levels]); 
        case (f kC)=>/=[_|]; case (f kD)=>/=[vD _|//]; by auto. 
  Defined.
  End s.
  Section s.
  Variable X: PO.type.
  Definition reducer: forall h k: K, h <= k -> gsup_op X k -> gsup_op X h.
    case; case=>//_ s.
    - by apply bot_from_csup.
    - by apply bot_from_dsup.
    - by apply bot_from_sup, sup_from_isup.
    - by apply cup_from_sup, sup_from_isup.
    - by apply csup_from_dsup.
    - by apply csup_from_sup, sup_from_isup.
    - by apply dsup_from_sup, sup_from_isup.
  Defined.
  Definition reduce f :=
    abstract_reduce _ f reducer (fun cup dsup => isup_from_sup (sup_from_cup_and_dsup cup dsup)). 
  End s.
End sreduce.
