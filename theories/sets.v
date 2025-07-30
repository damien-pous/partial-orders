Require Import lattice.

(** * complete lattice of sets over a setoid *)

Section s.
Context {A: Setoid.type}. 
Implicit Types a b c: A.

(** we want sets to be consistent with the setoid structure on [A] *)
Definition set := A -eqv-> Prop.
Implicit Types U V W: set.

(* HB.instance Definition _ := supCL.on set.  *)
(* HB.instance Definition _ := infCL.on set. *)

Definition mem U a := U a.
Notation "a ∈ U" := (mem U a) (at level 20). 

#[export] Instance mem_eqv: Proper (eqv ==> eqv ==> eqv) mem.
Proof. move=>U V UV a b ab. rewrite /mem. by rewrite (UV a) ab. Qed.

Definition single a: set := mk_ext (eqv a) _.
Lemma mem_single a: mem (single a) ≡ (eqv a).
Proof. done. Qed.

Definition add a U: set := cup (single a) U.
Lemma mem_add a U: mem (add a U) ≡ cup (eqv a) (mem U).
Proof. done. Qed.

Definition pair a b: set := cup (single a) (single b).
Lemma mem_pair a b: mem (pair a b) ≡ cup (eqv a) (eqv b).
Proof. done. Qed.

Lemma mem_bot: mem bot ≡ bot.
Proof. done. Qed.

Lemma mem_cup U V: mem (cup U V) ≡ cup (mem U) (mem V).
Proof. done. Qed.

Lemma mem_top: mem top ≡ top.
Proof. done. Qed.

Lemma mem_cap U V: mem (cap U V) ≡ cap (mem U) (mem V).
Proof. done. Qed.

End s.
Arguments set: clear implicits. 
Notation "a ∈ U" := (mem U a) (at level 20). 

Section image.
Context {X Y: Setoid.type}.
    
Program Definition image (f: X->Y) (U: set X): set Y :=
  mk_ext (fun y => exists x, x ∈ U /\ y ≡ f x) _.
Next Obligation. move=>y z yz. by setoid_rewrite yz. Qed.
Arguments image: simpl never.

Lemma in_image (f: X -> Y) (P: set X) x: x ∈ P -> f x ∈ image f P.
Proof. by exists x. Qed.

Lemma forall_image (f: X -> Y) (P: set X) (Q: set Y):
  image f P <= Q <-> P <=[X->Prop] Q ∘ f.
Proof.
  split=>H.
  - move=>x Px. apply: H. exact: in_image. 
  - move=>y [x [Px ->]]. exact: H.
Qed.

Lemma image_bot (f: X -> Y): image f bot ≡ bot.
Proof. apply: leq_bot. exact/forall_image. Qed.
Lemma image_cup (f: X -> Y) (U V: set X): image f (cup U V) ≡ cup (image f U) (image f V).
Proof.
  apply: from_above=>/=W.
  by rewrite cup_spec 3!forall_image cup_spec. 
Qed.
Lemma image_isup (f: X -> Y) I P (h: I -> set X): image f (isup P h) ≡ isup P (fun i => image f (h i)).
Proof.
  apply: from_above=>/=W.
  rewrite isup_spec forall_image isup_spec/=.
  by setoid_rewrite forall_image. 
Qed.
Lemma image_sup (f: X -> Y) (P: set X -> Prop): image f (sup P) ≡ isup P (image f).
Proof. exact: image_isup. Qed.

Lemma image_single (f: X -eqv-> Y) x: image f (single x) ≡ single (f x).
Proof.
  apply: antisym.
  apply/forall_image. exact: extensional.
  move=>y <-. exact/in_image.
Qed.
Lemma image_pair (f: X -eqv-> Y) (x x': X): image f (pair x x') ≡ pair (f x) (f x').
Proof. by rewrite image_cup 2!image_single. Qed.

End image.

Lemma image_id {X: Setoid.type} (P: set X): image types_id P ≡ P.
Proof.
  apply: antisym.
  exact/forall_image. 
  exact/in_image.
Qed.

Lemma image_comp {X Y Z: Setoid.type} (f: Y -eqv-> Z) (g: X -> Y) (P: set X): image (f ∘ g) P ≡ image f (image g P).
Proof.
  intro z; split.
  - move=>[x [Px ->]]. apply: in_image. exact: in_image.
  - move=>[y [[x [Px xy]] ->]].
    exists x; split=>//. by rewrite xy.
Qed.
