From Stdlib Require Import Arith.
Require Export partialorder_instances lattice.

(** ** empty *)

Lemma empty_cup_spec (x y: False): is_sup (pair x y) x.
Proof. done. Qed.
Lemma empty_cap_spec (x y: False): is_inf (pair x y) x.
Proof. done. Qed.
HB.instance Definition _ := PO_cup.Build False _ empty_cup_spec.
HB.instance Definition _ := PO_cap.Build False _ empty_cap_spec.
HB.instance Definition _ := ChainLattice_isDistributive.Build False.

(** ** unit *)

Lemma unit_sup_spec P: is_sup P tt.
Proof. done. Qed.
HB.instance Definition _ := PO_sup.Build unit _ unit_sup_spec.
HB.instance Definition _ := CL_isup.Build unit.
HB.instance Definition _ := ChainLattice_isDistributive.Build unit.

(** ** Booleans *)

Lemma bool_bot_spec: is_sup empty false.
Proof. cbv. done. Qed. 
Lemma bool_top_spec: is_inf empty true.
Proof. cbv. by case. Qed. 
Lemma bool_cup_spec b c: is_sup (pair b c) (b || c).
Proof. rewrite is_sup_pair/=. case; case:b; case:c; cbn; intuition discriminate. Qed. 
Lemma bool_cap_spec b c: is_inf (pair b c) (b && c).
Proof. rewrite is_inf_pair/=. case; case:b; case:c; cbn; intuition discriminate. Qed. 
HB.instance Definition _ := PO_bot.Build bool bool_bot_spec.
HB.instance Definition _ := PO_top.Build bool bool_top_spec.
HB.instance Definition _ := PO_cup.Build bool _ bool_cup_spec.
HB.instance Definition _ := PO_cap.Build bool _ bool_cap_spec.
HB.instance Definition _ := ChainLattice_isDistributive.Build bool.

(** ** natural numbers *)

HB.instance Definition _ := isStrictPO.Build nat _ Nat.le_antisymm.
HB.instance Definition _ := PO_isDecidable.Build nat leb Nat.leb_spec0.
HB.instance Definition _ := PO_isChain.Build nat Nat.le_ge_cases.

Lemma nat_bot_spec: is_sup empty 0.
Proof. rewrite is_sup_empty/=. exact: le_0_n. Qed.
Lemma nat_cup_spec n m: is_sup (pair n m) (max n m).
Proof. rewrite is_sup_pair/=. exact: Nat.max_lub_iff. Qed.
Lemma nat_cap_spec n m: is_inf (pair n m) (min n m).
Proof. rewrite is_inf_pair/=. exact: Nat.min_glb_iff. Qed.
HB.instance Definition _ := PO_bot.Build nat nat_bot_spec.
HB.instance Definition _ := PO_cup.Build nat max nat_cup_spec.
HB.instance Definition _ := PO_cap.Build nat min nat_cap_spec.
HB.instance Definition _ := ChainLattice_isDistributive.Build nat.

(** ** extensional functions on Types *)
(** NB: different from extensional functions between setoids (setoid_morphisms), here we use [eq] on the codomain *)
Definition extfun X Y := arrow X Y.
Definition extid {X}: extfun X X := types_id. 
HB.instance Definition _ X Y :=
  isSetoid.Build (extfun X Y) (@Equivalence.pointwise_equivalence X Y eq eq_equivalence). 

(** ** direct product *)

Section s.
Context {X Y: botPO.type}.
Definition prod_bot: X * Y := (bot, bot).
Lemma prod_bot_spec: is_sup empty prod_bot.
Proof. apply/prod_sup. rewrite 2!image_empty. split; exact/bot_sup_spec. Qed.
HB.instance Definition _ := PO_bot.Build (X*Y)%type prod_bot_spec.
End s.

Section s.
Context {X Y: joinSemiLattice.type}.
Definition prod_cup (p q: X * Y): X * Y := (cup p.1 q.1, cup p.2 q.2).
Lemma prod_cup_spec (p q: X * Y): is_sup (pair p q) (prod_cup p q).
Proof. apply/prod_sup. rewrite 2!image_pair. split; exact/cup_sup_spec. Qed.
HB.instance Definition _ := PO_cup.Build (X*Y)%type _ prod_cup_spec.
End s.

Section s.
Context {X Y: CPO.type}.
Definition prod_csup (P: X * Y -> Prop) (C: chain P): X * Y :=
  (csup (image fst P) (chain_image fst C), csup (image snd P) (chain_image snd C)). 
Lemma prod_csup_spec (P: X * Y -> Prop) (C: chain P): is_sup P (prod_csup C).
Proof. apply/prod_sup. split; exact/csup_spec. Qed.
HB.instance Definition _ := PO_csup.Build (X*Y)%type _ prod_csup_spec.
End s.

Section s.
Context {X Y: dCPO.type}.
Definition prod_dsup (P: X * Y -> Prop) (D: directed P): X * Y :=
  (dsup (image fst P) (directed_image fst D), dsup (image snd P) (directed_image snd D)). 
Lemma prod_dsup_spec (P: X * Y -> Prop) (D: directed P): is_sup P (prod_dsup D).
Proof. apply/prod_sup. split; exact/dsup_spec. Qed.
HB.instance Definition _ := PO_dsup.Build (X*Y)%type _ prod_dsup_spec.
End s.

Section s.
Context {X Y: supCL.type}.
Definition prod_isup I (P: I -> Prop) (f: I -> X * Y): X * Y :=
  (isup P (fst ∘ f), isup P (snd ∘ f)). 
Lemma prod_isup_spec I (P: I -> Prop) (f: I -> X * Y): is_sup (image f P) (prod_isup P f).
Proof. apply/prod_sup. rewrite -2!image_comp. split; exact/isup_sup_spec. Qed.
HB.instance Definition _ := PO_isup.Build (X*Y)%type _ prod_isup_spec.
End s.

Section s.
Context {X Y: topPO.type}.
Definition prod_top: X * Y := (top, top).
Lemma prod_top_spec: is_inf empty prod_top.
Proof. apply/prod_inf. rewrite 2!image_empty. split; exact/top_inf_spec. Qed.
HB.instance Definition _ := PO_top.Build (X*Y)%type prod_top_spec.
End s.

Section s.
Context {X Y: meetSemiLattice.type}.
Definition prod_cap (p q: X * Y): X * Y := (cap p.1 q.1, cap p.2 q.2).
Lemma prod_cap_spec (p q: X * Y): is_inf (pair p q) (prod_cap p q).
Proof. apply/prod_inf. rewrite 2!image_pair. split; exact/cap_inf_spec. Qed.
HB.instance Definition _ := PO_cap.Build (X*Y)%type _ prod_cap_spec.
End s.

Section s.
Context {X Y: CPO'.type}.
Definition prod_cinf (P: X * Y -> Prop) (C: cochain P): X * Y :=
  (cinf (image fst P) (cochain_image fst C), cinf (image snd P) (cochain_image snd C)). 
Lemma prod_cinf_spec (P: X * Y -> Prop) (C: cochain P): is_inf P (prod_cinf C).
Proof. apply/prod_inf. split; exact/cinf_spec. Qed.
HB.instance Definition _ := PO_cinf.Build (X*Y)%type _ prod_cinf_spec.
End s.

Section s.
Context {X Y: dCPO'.type}.
Definition prod_dinf (P: X * Y -> Prop) (D: codirected P): X * Y :=
  (dinf (image fst P) (codirected_image fst D), dinf (image snd P) (codirected_image snd D)). 
Lemma prod_dinf_spec (P: X * Y -> Prop) (D: codirected P): is_inf P (prod_dinf D).
Proof. apply/prod_inf. split; exact/dinf_spec. Qed.
HB.instance Definition _ := PO_dinf.Build (X*Y)%type _ prod_dinf_spec.
End s.

Section s.
Context {X Y: infCL.type}.
Definition prod_iinf I (P: I -> Prop) (f: I -> X * Y): X * Y :=
  (iinf P (fst ∘ f), iinf P (snd ∘ f)). 
Lemma prod_iinf_spec I (P: I -> Prop) (f: I -> X * Y): is_inf (image f P) (prod_iinf P f).
Proof. apply/prod_inf. rewrite -2!image_comp. split; exact/iinf_inf_spec. Qed.
HB.instance Definition _ := PO_iinf.Build (X*Y)%type _ prod_iinf_spec.
End s.

HB.saturate prod.


(** ** lexicographic product *)

Section s.
Context {X Y: botPO.type}.
Definition lex_prod_bot: lex_prod X Y := (bot, bot).
Lemma lex_prod_bot_spec: is_sup empty lex_prod_bot.
Proof. apply/is_sup_empty. cbn. auto with lattice. Qed.
HB.instance Definition _ := PO_bot.Build (lex_prod X Y) lex_prod_bot_spec.
End s.

Section s.
Context {X Y: topPO.type}.
Definition lex_prod_top: lex_prod X Y := (top, top).
Lemma lex_prod_top_spec: is_inf empty lex_prod_top.
Proof. apply/is_inf_empty. cbn. auto with lattice. Qed.
HB.instance Definition _ := PO_top.Build (lex_prod X Y)%type lex_prod_top_spec.
End s.

HB.instance Definition _ (X Y: DecidableOrder.type) := DecidableOrder_isLattice.Build (lex_prod X Y). 

(* TOHINK: more? *)

(* TODO: lexicographic lists, sequential sum *)
