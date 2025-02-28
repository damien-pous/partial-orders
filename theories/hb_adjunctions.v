From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Export hb_po.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.

Definition adjunction {X Y: PO.type} l r := forall (x: X) (y: Y), l x <= y <-> x <= r y.

Class Adjunction (X Y: PO.type) := {
    ladj: X -> Y;
    radj: Y -> X;
    adj:> adjunction ladj radj;
  }.
Arguments ladj {_ _}.
Arguments radj {_ _}.
Infix "⊣" := Adjunction (at level 79).

Program Definition dual_adj {X Y} (A: X ⊣ Y): dual Y ⊣ dual X :=
  {|
    ladj := radj A;
    radj := ladj A;
  |}.
Next Obligation. split; apply adj. Defined.

Definition adj_id {X}: X ⊣ X :=
  {|
    ladj := types_id;
    radj := types_id;
    adj x y := iff_refl _;
  |}.

Program Definition adj_comp {X Y Z} (xy: X ⊣ Y) (yz: Y ⊣ Z): X ⊣ Z :=
  {|
    ladj := ladj yz ∘ ladj xy;
    radj := radj xy ∘ radj yz;
  |}.
Next Obligation. rewrite /adjunction=>x y. by rewrite 2!adj. Qed.

Section s.
  Context {X Y: PO.type} (A: X ⊣ Y).

  Lemma ladj_leq: Proper (leq ==> leq) (ladj A).
  Proof. move=>x y xy. apply/adj. rewrite xy. by apply/adj. Qed.
  HB.instance Definition _ := isMonotone.Build X Y (ladj A) ladj_leq. 

  Definition adj_unit := radj A ∘ ladj A.
  
  Lemma adj_unit_refl: @types_id X <= adj_unit.
  Proof. move=>x/=. exact/adj. Qed.

  Lemma adj_lrl: ladj A ∘ adj_unit ≡ ladj A.
  Proof. apply: antisym=>x/=. exact/adj. by rewrite -(adj_unit_refl x). Qed.

  Lemma adj_unit_trans: adj_unit ∘ adj_unit <= adj_unit.
  Proof. rewrite /adj_unit=>x/=. apply/adj. by do 2 setoid_rewrite (adj_lrl _). Qed.

  (* left adjoints preserve sups *)
  Lemma adjoint_sup P (x: X): is_sup P x -> is_sup (image (ladj A) P) (ladj A x).
  Proof.
    move=>H y. rewrite adj H.
    setoid_rewrite forall_image. apply: forall_iff=>z. 
    by rewrite adj. 
  Qed.
End s.
Section s.
  Context {X Y: PO.type} (A: X ⊣ Y).
  
  Lemma radj_leq: Proper (leq ==> leq) (radj A).
  Proof. apply/Proper_dual_leq. exact: (ladj_leq (dual_adj A)). Qed.
  HB.instance Definition _ := isMonotone.Build Y X (radj A) radj_leq.

  Definition adj_counit := ladj A ∘ radj A.
  
  Lemma adj_counit_corefl: adj_counit <= types_id.
  Proof. exact: (adj_unit_refl (dual_adj A)). Qed.
  
  Lemma adj_rlr: radj A ∘ adj_counit ≡ radj A.
  Proof. exact: (adj_lrl (dual_adj A)). Qed.

  Lemma adj_counit_cotrans: adj_counit <= adj_counit ∘ adj_counit.
  Proof. exact: (adj_unit_trans (dual_adj A)). Qed.
  
  (* right adjoints preserve infs *)
  Lemma adjoint_inf P (y: Y): is_inf P y -> is_inf (image (radj A) P) (radj A y).
  Proof. exact: (adjoint_sup (dual_adj A)). Qed.
End s.

(* monadic adjunctions actually create sups/infs *)
Lemma madjoint_sup {X Y: PO.type} (A: X ⊣ Y) P (x: X):
  adj_counit A ≡ types_id -> is_sup (image (radj A) P) x -> is_sup P (ladj A x).
Proof.
  move=>U H y. rewrite adj H.
  setoid_rewrite forall_image. apply: forall_iff=>z.    
  rewrite -adj. by setoid_rewrite (U z). 
Qed.
Lemma madjoint_inf {X Y: PO.type} (A: X ⊣ Y) P (y: Y):
  adj_unit A ≡ types_id -> is_inf (image (ladj A) P) y -> is_inf P (radj A y).
Proof. exact: (madjoint_sup (A:=dual_adj A)). Qed.


(** isomorphisms *)
Class Iso (X Y: PO.type) := {
    fwd: X -> Y;
    bwd: Y -> X;
    fwd_bwd: adjunction fwd bwd;
    bwd_fwd: adjunction bwd fwd;
  }.
Arguments fwd {_ _}.
Arguments bwd {_ _}.
Infix "≃" := Iso (at level 70). 

Coercion Iso_adj {X Y} (i: X ≃ Y): X ⊣ Y.
econstructor; apply i.
Defined.
Definition Iso_adj' {X Y} (i: X ≃ Y): Y ⊣ X.
econstructor; apply i.
Defined.
HB.instance Definition _ X Y (i: X ≃ Y) := po_morphism.copy (fwd i) (ladj i). 
HB.instance Definition _ X Y (i: X ≃ Y) := po_morphism.copy (bwd i) (radj i). 

Definition iso_id {X: PO.type}: X ≃ X.
  by exists types_id types_id.
Defined.

Definition iso_sym {X Y: PO.type}: X ≃ Y -> Y ≃ X.
  move=>i. econstructor; apply i.
Defined.
Notation "i ^-1" := (iso_sym i).

Definition iso_trans {X Y Z: PO.type}: X ≃ Y -> Y ≃ Z -> X ≃ Z.
  move=>i j. exists (fwd j ∘ fwd i) (bwd i ∘ bwd j).
  apply: (adj_comp i j). 
  apply: (adj_comp (j^-1) (i^-1)). 
Defined.

Lemma isoK {X Y: PO.type} (i: X ≃ Y): fwd i ∘ bwd i ≡ types_id.
Proof. apply: antisym=>x/=. by rewrite fwd_bwd. by rewrite -bwd_fwd. Qed.

Lemma isoK' {X Y: PO.type} (i: X ≃ Y): bwd i ∘ fwd i ≡ types_id.
Proof. exact: isoK (i^-1). Qed.

Lemma iso_counit {X Y: PO.type} (i: X ≃ Y): adj_counit i ≡ types_id.
Proof. exact: isoK. Qed.

Lemma iso_unit {X Y: PO.type} (i: X ≃ Y): adj_unit i ≡ types_id.
Proof. exact: isoK'. Qed.

Definition etaI (X: PO.type): X ≃ eta X.
  unshelve eexists. 1,2: exact types_id. all: exact: adj_id.
Defined.

Definition dualI (X: PO.type): dual (dual X) ≃ X.
  unshelve eexists. 1,2: exact types_id. all: exact: adj_id. 
Defined.

Definition mon_alt (X Y: PO.type): dual (dual X -mon-> dual Y) ≃ (X -mon-> Y).
  unshelve eexists. 2: exact: dualf. 
  move=>f. apply: (mk_mon (f: X -> Y)). by apply/Proper_dual_leq.
  1,2: done.
Defined.

Definition iso_retract A (X: PO.type) (r: A -> X) (i: X -> A) (ri: r ∘ i ≡ types_id):
  X ≃ kernel r.
  exists i r=>??; cbn; by setoid_rewrite (ri _).
Defined.




(* Definition bool_dfun {X Y: Setoid.type} (x: X) (y: Y): forall b, bool_fun X Y b := fun b => if b return bool_fun X Y b then y else x. *)
(* Section prod_dprod_bool. *)
(*   Context {X Y: Setoid.type}. *)
(*   Program Definition iso_prod_dprod_bool: prod X Y ≃[SETOIDS] forall b, bool_fun X Y b := *)
(*     {| *)
(*       fwd := mk_ext (fun p => (bool_dfun p.1 p.2)) _; *)
(*       bwd := mk_ext (fun h => (h false, h true)) _; *)
(*     |}. *)
(*   Next Obligation. by move=>p q [??][]. Qed. *)
(*   Next Obligation. by move=>h g; split; apply: H. Qed. *)
(*   Next Obligation. by move => ?[]. Qed. *)
(*   Next Obligation. by split. Qed. *)
(* End prod_dprod_bool. *)
