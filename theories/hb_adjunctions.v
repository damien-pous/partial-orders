From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Export hb_po.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.

(** * adjunctions *)

Definition adjunction {X Y: PO.type} l r := forall (x: X) (y: Y), l x <= y <-> x <= r y.

(** we index adjunctions by the left adjoint *)
HB.mixin Record isLeftAdjoint X Y f of po_morphism X Y f :=
  { #[canonical=no] radj: Y -> X; 
    #[canonical=no] adj: adjunction f radj }.
HB.structure Definition Adjunction X Y := {f of isLeftAdjoint X Y f & }.
Notation ladj := Adjunction.sort.
Arguments radj {_ _}.
Infix "⊣" := Adjunction.type (at level 79).

HB.mixin Record Fun_isLeftAdjoint (X Y: PO.type) (f: X -> Y) :=
  { #[canonical=no] radj: Y -> X; 
    #[canonical=no] adj: adjunction f radj }.
HB.builders Context (X Y: PO.type) f of Fun_isLeftAdjoint X Y f.
  Lemma monotone: Proper (leq ==> leq) f.
  Proof. move=>x y xy. apply/adj. rewrite xy. by apply/adj. Qed.
  HB.instance Definition _ := Fun_isMonotone.Build X Y f monotone.
  HB.instance Definition _ := isLeftAdjoint.Build X Y f adj.
HB.end.

(** identity *)
Lemma adj_id {X}: @adjunction X X types_id types_id.
Proof. done. Qed.
HB.instance Definition _ {X} := isLeftAdjoint.Build X X types_id adj_id. 

(** composition *)
Lemma adj_comp {X Y Z} (xy: X ⊣ Y) (yz: Y ⊣ Z):
  adjunction (ladj yz ∘ ladj xy) (radj xy ∘ radj yz).
Proof. move=>x y. by rewrite 2!adj. Qed.
HB.instance Definition _ {X Y Z} (xy: X ⊣ Y) (yz: Y ⊣ Z) :=
  isLeftAdjoint.Build X Z (yz ∘ xy) (adj_comp xy yz). 

(** basic properties *)
Section s.
  Context {X Y} (f: X ⊣ Y).

  Definition adj_monad := radj f ∘ ladj f.
  
  Lemma adj_unit: @types_id X <= adj_monad.
  Proof. move=>x/=. by rewrite -adj. Qed.

  Lemma adj_lrl: f ∘ adj_monad ≡ f.
  Proof. apply: antisym=>x/=. exact/adj. by rewrite -(adj_unit x). Qed.

  Lemma adj_mult: adj_monad ∘ adj_monad <= adj_monad.
  Proof. rewrite /adj_unit=>x/=. apply/adj. by do 2 setoid_rewrite (adj_lrl _). Qed.

  (** left adjoints preserve sups *)
  Lemma adjoint_sup P (x: X): is_sup P x -> is_sup (image f P) (f x).
  Proof.
    move=>H y. rewrite adj H.
    setoid_rewrite forall_image. apply: forall_iff=>z. 
    by rewrite adj. 
  Qed.
End s.

(** dual adjunction *)
Definition dual_adj {X Y} (f: X ⊣ Y): dual Y -> dual X := radj f.
Lemma dual_adj_ {X Y} (f: X ⊣ Y): @adjunction (dual Y) (dual X) (dual_adj f) (ladj f).
Proof. split; apply adj. Qed.
HB.instance Definition _ {X Y} (f: X ⊣ Y) :=
  Fun_isLeftAdjoint.Build (dual Y) (dual X) (dual_adj f) (dual_adj_ f).

(** dual properties *)
Section s.
  Context {X Y} (f: X ⊣ Y).
  
  Lemma radj_leq: Proper (leq ==> leq) (radj f).
  Proof. apply/Proper_dual_leq. exact: (@monotone _ _ (dual_adj f)). Qed.
  HB.instance Definition _ := Fun_isMonotone.Build Y X (radj f) radj_leq.

  Definition adj_comonad := ladj f ∘ radj f.
  
  Lemma adj_counit: adj_comonad <= types_id.
  Proof. exact: (adj_unit (dual_adj f)). Qed.
  
  Lemma adj_rlr: radj f ∘ adj_comonad ≡ radj f.
  Proof. exact: (adj_lrl (dual_adj f)). Qed.

  Lemma adj_comult: adj_comonad <= adj_comonad ∘ adj_comonad.
  Proof. exact: (adj_mult (dual_adj f)). Qed.
  
  (* right adjoints preserve infs *)
  Lemma adjoint_inf P (y: Y): is_inf P y -> is_inf (image (radj f) P) (radj f y).
  Proof. exact: (adjoint_sup (dual_adj f)). Qed.
End s.

(** * (co)monadic adjunctions *)

HB.mixin Record isMonadic X Y f of Adjunction X Y f := {
    #[canonical=no] monadic: adj_monad f ≡ types_id
  }.
HB.structure Definition MonadicAdjunction X Y := {f of isMonadic X Y f &}.
Infix "·⊣" := MonadicAdjunction.type (at level 79).

HB.mixin Record isCoMonadic X Y f of Adjunction X Y f := {
    #[canonical=no] comonadic: adj_comonad f ≡ types_id
  }.
HB.structure Definition CoMonadicAdjunction X Y := {f of isCoMonadic X Y f &}.
Infix "⊣·" := CoMonadicAdjunction.type (at level 79).

(** duality *)
HB.instance Definition _ X Y (f: X ·⊣ Y) :=
  isCoMonadic.Build (dual Y) (dual X) (dual_adj f) (@monadic _ _ f).
HB.instance Definition _ X Y (f: X ⊣· Y) :=
  isMonadic.Build (dual Y) (dual X) (dual_adj f) (@comonadic _ _ f).

(** monadic adjunctions create infs *)
Lemma monadic_inf {X Y} (f: X ·⊣ Y) P (y: Y):
  is_inf (image f P) y -> is_inf P (radj f y).
Proof.
  move=>H x. rewrite -adj H.
  setoid_rewrite forall_image. apply: forall_iff=>z.    
  rewrite adj. by setoid_rewrite (monadic z). 
Qed.

(** comonadic adjunctions create sups *)
Lemma comonadic_sup {X Y} (f: X ⊣· Y) P (x: X):
  is_sup (image (radj f) P) x -> is_sup P (f x).
(* Proof. exact: (monadic_inf (dual_adj f)). Qed. *)
Proof.
  move=>H y. rewrite adj H.
  setoid_rewrite forall_image. apply: forall_iff=>z.    
  rewrite -adj. by setoid_rewrite (comonadic z). 
Qed.


(** * isomorphisms *)
HB.structure Definition Iso X Y := {i of Adjunction X Y i & isMonadic X Y i & isCoMonadic X Y i }.
Infix "≃" := Iso.type (at level 70).
Definition inv {X Y} (i: X ≃ Y) := radj i. 
Notation "i ^-1" := (inv i).

HB.factory Record isIso (X Y: PO.type) (i: X -> Y) := {
    bwd: Y -> X;
    fwd_bwd: adjunction i bwd;
    bwd_fwd: adjunction bwd i;
  }.
HB.builders Context X Y i of isIso X Y i.
  HB.instance Definition _ := Fun_isLeftAdjoint.Build X Y i fwd_bwd.
  Lemma monadic: adj_monad i ≡ types_id.
  Proof. apply: antisym=>x/=. by rewrite bwd_fwd. by rewrite -fwd_bwd. Qed.
  HB.instance Definition _ := isMonadic.Build X Y i monadic.
  Lemma comonadic: adj_comonad i ≡ types_id.
  Proof. apply: antisym=>x/=. by rewrite fwd_bwd. by rewrite -bwd_fwd. Qed.
  HB.instance Definition _ := isCoMonadic.Build X Y i comonadic.
HB.end.

Lemma radj_iso_ladj {X Y} (i: X ≃ Y) : adjunction i^-1 i.
Proof.
  move=>y x. setoid_rewrite <-(@monadic _ _ i x) at 1.
  rewrite -adj. by setoid_rewrite (comonadic y).
Qed.
HB.instance Definition _ {X Y} (i: X ≃ Y) := Fun_isLeftAdjoint.Build Y X (i^-1) (radj_iso_ladj i).
HB.instance Definition _ X Y (i: X ≃ Y) := isCoMonadic.Build Y X (i^-1) (@monadic _ _ i).
HB.instance Definition _ X Y (i: X ≃ Y) := isMonadic.Build Y X (i^-1) (@comonadic _ _ i).
Check fun X Y (i: X ≃ Y) => i^-1: Y -mon-> X. 
Check fun X Y (i: X ≃ Y) => i^-1: Y ≃ X.

Lemma isoK {X Y: PO.type} (i: X ≃ Y): i ∘ i^-1 ≡ types_id.
Proof. exact: monadic. Qed.
Lemma isoK' {X Y: PO.type} (i: X ≃ Y): i^-1 ∘ i ≡ types_id.
Proof. exact: comonadic. Qed.

Lemma monadic_id {X}: @adj_monad X X types_id ≡ types_id.
Proof. done. Qed.
HB.instance Definition _ X := isMonadic.Build X X types_id monadic_id.
Lemma comonadic_id {X}: @adj_comonad X X types_id ≡ types_id.
Proof. done. Qed.
HB.instance Definition _ X := isCoMonadic.Build X X types_id comonadic_id.
Check fun X: PO.type => @types_id X: X ≃ X. 

(* sadly *)
Fail HB.instance Definition iso_comp_ {X Y Z: PO.type} (i: X ≃ Y) (j: Y ≃ Z) :=
  @isIso.Build X Z (j ∘ i) (i^-1 ∘ j^-1) adj adj.
Program Definition comp_iso_monadic {X Y Z: PO.type} (i: X ≃ Y) (j: Y ≃ Z) :=
  isMonadic.Build X Z (j ∘ i) _.
Next Obligation.
  rewrite /adj_monad=>x. change (i^-1 ((j^-1 ∘ j) (i x)) ≡ x). 
  rewrite (isoK' j _). exact: isoK.
Qed.
HB.instance Definition _ {X Y Z: PO.type} (i: X ≃ Y) (j: Y ≃ Z) := comp_iso_monadic i j.
Program Definition comp_iso_comonadic {X Y Z: PO.type} (i: X ≃ Y) (j: Y ≃ Z) :=
  isCoMonadic.Build X Z (j ∘ i) _.
Next Obligation. 
  rewrite /adj_comonad=>z. change (j ((i ∘ i^-1) (j^-1 z)) ≡ z). 
  rewrite (isoK i _). exact: isoK'.
Qed.
HB.instance Definition _ {X Y Z: PO.type} (i: X ≃ Y) (j: Y ≃ Z) := comp_iso_comonadic i j.
Check fun {X Y Z: PO.type} (i: X ≃ Y) (j: Z ≃ Y) => j^-1 ∘ i: X ≃ Z.

Definition mk_iso (X Y: PO.type) (f: X -> Y) (g: Y -> X) (fg: adjunction f g) (gf: adjunction g f) := f.
Arguments mk_iso {_ _}.
HB.instance Definition _ X Y f g fg gf := @isIso.Build X Y (@mk_iso X Y f g fg gf) g fg gf.

Program Definition iso_eta X: X ≃ eta X :=
  @mk_iso X (eta X) types_id types_id _ _. 
Next Obligation. done. Qed.
Next Obligation. done. Qed.

Definition dualI (X: PO.type): X ≃ dual (dual X) := iso_eta X.

Program Definition iso_retract A (X: PO.type) (r: A -> X) (i: X -> A) (ri: r ∘ i ≡ types_id): X ≃ kernel r :=
  @mk_iso X (kernel r) i r _ _.
Next Obligation. move=>??; cbn; by setoid_rewrite (ri _). Qed.
Next Obligation. move=>??; cbn; by setoid_rewrite (ri _). Qed.

Program Definition iso_dual_mon (X Y: PO.type): (X -mon-> Y) ≃ dual (dual X -mon-> dual Y) :=
  @mk_iso (X -mon-> Y) (dual (dual X -mon-> dual Y))
    dualf (fun f => mk_mon (f: X -> Y) _) _ _.
Next Obligation. by apply/Proper_dual_leq. Qed.
Next Obligation. done. Qed.
Next Obligation. done. Qed.

Section s.
 Context {X: Setoid.type} {Y: PO.type}.
 Definition setoid_morphism_to_sig (f: X-eqv->Y): sig (Proper (eqv==>eqv)) :=
   exist (Proper (eqv ==> eqv)) f extensional.
 Definition sig_to_setoid_morphism (f: sig (Proper (eqv==>eqv))): X-eqv->Y :=
   mk_ext (sval f) (proj2_sig f).
 Program Definition setoid_morphism_as_sig: (sig (Proper (@eqv X==>@eqv Y))) ≃ (X-eqv->Y) :=
   mk_iso sig_to_setoid_morphism setoid_morphism_to_sig _ _.
 Next Obligation. done. Qed.
 Next Obligation. done. Qed.
End s.

Section s.
 Context {X Y: PO.type}.
 Definition po_morphism_to_sig (f: X-mon->Y): sig (Proper (leq==>leq)) :=
   exist (Proper (leq ==> leq)) f monotone.
 Definition sig_to_po_morphism (f: sig (Proper (leq==>leq))): X-mon->Y :=
   mk_mon (sval f) (proj2_sig f).
 Program Definition po_morphism_as_sig: (sig (Proper (@leq X==>@leq Y))) ≃ (X-mon->Y) :=
   mk_iso sig_to_po_morphism po_morphism_to_sig _ _.
 Next Obligation. done. Qed.
 Next Obligation. done. Qed.
End s.

Section prod_dprod_bool.
  Context {X Y: PO.type}.
  Definition bool_dfun (x: X) (y: Y): PO.sort (forall b, bool_fun X Y b) :=
    fun b => if b return bool_fun X Y b then y else x.
  Program Definition prod_as_dprod_bool: prod X Y ≃ forall b, bool_fun X Y b :=
    mk_iso (fun p => bool_dfun p.1 p.2) (fun h => (h false, h true)) _ _.
  Next Obligation.
    move=>p h. split=>H.
    split. exact: (H false). exact: (H true).
    by case; apply H.
  Qed.
  Next Obligation.
    move=>h p. split=>H. 
    by case; apply H.
    split. exact: (H false). exact: (H true).
  Qed.
End prod_dprod_bool.
