Require Import lattice.

(** * complete lattice of sets over a setoid *)

Section s.
Context {A: Setoid.type}. 
Implicit Types a b c: A.
Implicit Types U V W: set A.

HB.instance Definition _ := supCL.on (set A).
HB.instance Definition _ := infCL.on (set A).

Definition add a U: set A := cup (single a) U.
Lemma mem_add a U: mem (add a U) ≡ cup (eqv a) (mem U).
Proof. done. Qed.

Lemma mem_bot: mem bot ≡[A->Prop] bot.
Proof. done. Qed.

Lemma mem_cup U V: mem (cup U V) ≡ cup (mem U) (mem V).
Proof. done. Qed.

Lemma mem_top: mem top ≡[A->Prop] top.
Proof. done. Qed.

Lemma mem_cap U V: mem (cap U V) ≡ cap (mem U) (mem V).
Proof. done. Qed.

End s.
