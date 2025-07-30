Require Import sups.
From Stdlib Require Import List.

(** * (bot,join) semilattice of finite sets over a setoid *)

Section s.
Context {A: Setoid.type}. 
Implicit Types a b c: A.

Definition fset := list A.
Implicit Types U V W: fset.

Definition mem U a := exists b, In b U /\ a ≡ b.
Notation "a ∈ U" := (mem U a) (at level 20). 

HB.instance Definition _ := PO.copy fset (kernel mem). 
#[export] Instance mem_eqv: Proper (eqv ==> eqv ==> eqv) mem.
Proof.
  move=>U V UV a b ab. rewrite (UV a).
  rewrite /mem. by setoid_rewrite ab.
Qed.

Definition fset_empty: fset := nil.
Definition fset_add: A -> fset -> fset := cons.
Definition fset_single (a: A): fset := fset_add a fset_empty.
Definition fset_union: fset -> fset -> fset := @app _.

Lemma mem_empty: mem fset_empty ≡ bot.
Proof. apply: leq_bot=>x [? [[]]]. Qed.

Lemma mem_add a U: mem (fset_add a U) ≡ cup (eqv a) (mem U).
Proof.
  cbn=>b. rewrite {1}/mem/=. cbn.
  firstorder subst; auto. eexists; auto. 
Qed.

Lemma mem_single x: mem (fset_single x) ≡ eqv x.
Proof. by rewrite mem_add mem_empty cupxb. Qed.

Lemma mem_union U V: mem (fset_union U V) ≡ cup (mem U) (mem V).
Proof.
  cbn=>x. rewrite /mem.  
  setoid_rewrite in_app_iff.
  firstorder. 
Qed.

Program Definition _fset_bot := @PO_bot.Build fset fset_empty _.
Next Obligation. apply/is_sup_empty=>/=U x. by rewrite (mem_empty x). Qed.
HB.instance Definition _ := _fset_bot. 

Program Definition _fset_cup := @PO_cup.Build fset (@app _) (fun U V => _).
Next Obligation.
  apply/is_sup_pair=>/=W. cbn. 
  setoid_rewrite (mem_union U V _). cbn. 
  firstorder. 
Qed.
HB.instance Definition _ := _fset_cup. 

(** [fset A] is the free (bot,join)-semilattice over A *)
Section free.
  
  Context {X: botjoinSemiLattice.type}.
  Variable f: A -eqv-> X.
  Definition eval: fset -> X := List.fold_right (fun a => cup (f a)) bot.
  Hypothesis f_eqv: Proper (eqv ==> eqv) f. 
  Lemma eval_sup_spec U: is_sup (image f (mem U)) (eval U).
  Proof.
    elim: U=>[|a U IH].
    - rewrite mem_empty image_empty. exact: bot_sup_spec.  
    - rewrite mem_add image_cup/=. apply: is_sup_cup=>//. clear.
      move=>x. split.
      -- move=>H _ [b [E ->]]. by rewrite -E.
      -- apply. exact: in_image.
  Qed.

  #[export] Instance eval_eqv: Proper (eqv ==> eqv) eval.
  Proof.
    move=>U V UV. apply: is_sup_unique. exact: eval_sup_spec.
    rewrite (UV: mem U ≡ mem V). exact: eval_sup_spec.
  Qed.
  Lemma eval_bot: eval bot ≡ bot.
  Proof. done. Qed.
  Lemma eval_add a U: eval (fset_add a U) ≡ cup (f a) (eval U).
  Proof. done. Qed.
  Lemma eval_single a: eval (fset_single a) ≡ f a.
  Proof. exact: cupxb. Qed.
  Lemma eval_cup U V: eval (cup U V) ≡ cup (eval U) (eval V).
  Proof.
    apply: is_sup_unique. exact: eval_sup_spec.
    rewrite mem_union image_cup. apply: is_sup_cup; exact: eval_sup_spec. 
  Qed.
  Variable e: fset -> X.
  Hypothesis ef: forall a, e (fset_single a) ≡ f a.
  Hypothesis e_eqv: Proper (eqv ==> eqv) e.
  Hypothesis e_bot: e bot ≡ bot.
  Hypothesis e_cup: forall U V, e (cup U V) ≡ cup (e U) (e V).
  Lemma evalU: e ≡ eval.
  Proof.
    have e_add: forall a U, e (fset_add a U) ≡ cup (f a) (e U).
    { move=>a U. by rewrite -ef -e_cup. }
    elim=>[|a U IH]/=. exact: e_bot. by rewrite e_add IH. 
  Qed.
  
End free.
End s.

Arguments fset: clear implicits.
Notation "a ∈ U" := (mem U a).

