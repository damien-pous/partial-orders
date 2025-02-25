From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Export hb_po.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

(** *  adjunctions *)
Section s.
  Context {X Y: PO.type}.
  Variables (f: X -> Y) (g: Y -> X).
  Class adjunction := adj: forall x y, f x <= y <-> x <= g y.
  
  #[local] Instance left_adjoint_leq {A: adjunction}: Proper (leq ==> leq) f.
  Proof. intros x y xy. apply adj. rewrite xy. by apply adj. Qed.
  
  #[local] Instance right_adjoint_leq {A: adjunction}: Proper (leq ==> leq) g.
  Proof. intros x y xy. apply adj. rewrite -xy. by apply adj. Qed.
  
  Lemma left_adjoint_sup (A: adjunction) P x: is_sup P x -> is_sup (image f P) (f x).
  Proof.
    unfold is_sup. intros H y. rewrite adj H.
    setoid_rewrite <-adj. symmetry. apply forall_image.
  Qed.
End s.

Lemma adjoint_id {X}: @adjunction X X types_id types_id.
Proof. by []. Qed.

Lemma adjoint_comp {X Y Z f g f' g'} {A: @adjunction X Y f g} {B: @adjunction Y Z f' g'}:
  adjunction (f' ∘ f) (g ∘ g').
Proof. move=>x y/=. by rewrite 2!adj. Qed.

Lemma dual_adjunction `(A: adjunction): adjunction (g: dual Y -> dual X) (f: dual X -> dual Y).
Proof. rewrite /adjunction/= => y x. symmetry. by apply adj. Qed.

Lemma right_adjoint_inf `(A: adjunction) P y: is_inf P y -> is_inf (image g P) (g y).
Proof. apply (left_adjoint_sup (dual_adjunction A)). Qed. 



(** class of left adjoints *)
HB.mixin Record hasRightAdjoint (X Y: PO.type) (f: X -> Y) := {
    #[canonical=no] right_adjoint: Y -> X;
    #[canonical=no] lr_adjoint: adjunction f right_adjoint;
  }.
HB.builders Context X Y f of hasRightAdjoint X Y f.
  Lemma monotone: Proper (leq ==> leq) f.
  Proof. apply: left_adjoint_leq. exact: lr_adjoint. Qed.
  HB.instance Definition _ := isMonotone.Build X Y f monotone.
HB.end.
HB.structure Definition leftAdjoint (X Y: PO.type) := { f of hasRightAdjoint X Y f }.

(** dually, class of right adjoints *)
HB.mixin Record hasLeftAdjoint (X Y: PO.type) (f: Y -> X) := {
    #[canonical=no] left_adjoint: X -> Y;
    #[canonical=no] rl_adjoint: adjunction left_adjoint f;
  }.
HB.builders Context X Y f of hasLeftAdjoint X Y f.
  Lemma monotone: Proper (leq ==> leq) f.
  Proof. apply: right_adjoint_leq. exact: rl_adjoint. Qed.
  HB.instance Definition _ := isMonotone.Build Y X f monotone.
HB.end.
HB.structure Definition rightAdjoint (X Y: PO.type) := { f of hasLeftAdjoint X Y f }.

Program Definition lr_ X Y (f: leftAdjoint.type X Y) := @hasLeftAdjoint.Build _ _ (@right_adjoint _ _ f) f _.
Next Obligation. exact: lr_adjoint. Qed.
HB.instance Definition _ X Y f := @lr_ X Y f.

Program Definition rl_ X Y (f: rightAdjoint.type X Y) := @hasRightAdjoint.Build _ _ (@left_adjoint _ _ f) f _.
Next Obligation. exact: rl_adjoint. Qed.
HB.instance Definition _ X Y f := @rl_ X Y f.

(** class of partial order isomorphisms *)
HB.mixin Record is_POiso (X Y: PO.type) f of @leftAdjoint X Y f := {
    #[canonical=no] inverse_adjoint: adjunction (@right_adjoint _ _ f) f
  }.
(* HB.builders Context X Y f of is_POiso X Y f. *)
(*   HB.instance Definition _ := @hasLeftAdjoint.Build _ _ (@inverse_adjoint _ _ f _. *)
(* HB.end. *)
HB.structure Definition po_isomorphism (X Y: PO.type) := { f of is_POiso X Y f & }.
