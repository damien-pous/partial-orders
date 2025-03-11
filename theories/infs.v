Require Export sups.
Require Import adjunction.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

(** * infima in partial orders *)

(** ** general properties of infima *)
(** (by duality with suprema) *)

Section s.
  
Context {X: PO.type}.
Implicit Types x y z: X. 
Implicit Types P Q: X -> Prop.

Lemma leq_is_inf P x: is_inf P x -> forall z, (forall y, P y -> z <= y) -> z <= x.
Proof. dual @geq_is_sup. Qed.
Lemma geq_is_inf P x: is_inf P x -> forall y, P y -> x <= y.
Proof. dual @leq_is_sup. Qed.

Lemma is_inf_leq P p Q q: is_inf P p -> is_inf Q q -> cocovered P Q -> q<=p.
Proof. dual @is_sup_leq. Qed.
Lemma is_inf_eqv P p Q q: is_inf P p -> is_inf Q q -> cobicovered P Q -> p≡q.
Proof. dual @is_sup_eqv. Qed.
Lemma is_inf_unique (P: X -> Prop) x y: is_inf P x -> is_inf P y -> x ≡ y.
Proof. dual @is_sup_unique. Qed.
Lemma is_inf_single x: is_inf (eq x) x.
Proof. dual @is_sup_single. Qed.
#[export] Instance Proper_is_inf: Proper (cobicovered ==> eqv ==> eqv) (@is_inf X).
Proof. dual @Proper_is_sup. Qed.

Lemma inf_closed_impl (P Q: X -> Prop): Proper (leq ==> leq) P -> inf_closed Q -> inf_closed (fun x => P x -> Q x).
Proof. dual @sup_closed_impl. Qed.
Lemma inf_closed_leq (f: X -mon-> X): inf_closed (fun x => f x <= x).
Proof. exact: (sup_closed_leq (dualf f)). Qed.
Lemma inf_closed_Proper P: inf_closed P -> Proper (eqv ==> eqv) P.
Proof. dual @sup_closed_Proper. Qed.

Definition inf_closure P: X -> Prop := sup_closure (P: dual X -> Prop).
Lemma is_inf_closure P: is_inf (inf_closure P) ≡ is_inf P.
Proof. dual @is_sup_closure. Qed.

Lemma is_inf_image {A} (f: A -> X) (P: A -> Prop) x:
  is_inf (image f P) x <-> forall z, z <= x <-> forall a, P a -> z <= f a.
Proof. dual @is_sup_image. Qed.
  
End s.

(** infs can be computed pointwise in function spaces *)
Lemma dprod_inf {A} {X: A -> PO.type} (P: (forall a, X a) -> Prop) (f: forall a, X a):
  (forall a, is_inf (image (app a) P) (f a)) -> is_inf P f.
Proof. exact: (@dprod_sup A (fun a => dual (X a))). Qed.
(** infs being unique, they *must* be computed pointwise if they can
    (i.e., when there are enough infs in X) *)
Lemma dprod_inf' {A} {X: A -> PO.type} (P: (forall a, X a) -> Prop) (f g: forall a, X a):
  (forall a, is_inf (image (app a) P) (f a)) -> 
  is_inf P g -> forall a, is_inf (image (app a) P) (g a).
Proof. exact: (@dprod_sup' A (fun a => dual (X a))). Qed.
(** alternatively, they *must* be computed pointwise when [A] is decidable *)
Lemma dprod_inf'' {A} {X: A -> PO.type}
      (A_dec: forall a b: A, {a=b} + {a<>b})
      (P: (forall a, X a) -> Prop) (f: forall a, X a):
  is_inf P f -> forall a, is_inf (image (app a) P) (f a).
Proof. exact: (@dprod_sup'' A (fun a => dual (X a))). Qed.

  
(** infs are computed pointwise in products *)
Lemma prod_inf {X Y: PO.type} (P: X*Y -> Prop) (p: X*Y):
  (is_inf (image fst P) (fst p) /\ is_inf (image snd P) (snd p)) <-> is_inf P p.
Proof. exact: (@prod_sup (dual X) (dual Y)). Qed.

(** infs can be computed as expected in sub-spaces *)
(* recall that [kernel f = A] *)
Lemma kern_inf {A} {X: PO.type} (f: A -> X) (P: kernel f -> Prop) (a: kernel f):
  is_inf (image f P) (f a) -> is_inf P a.
Proof. exact: (@kern_sup A (dual X)). Qed.

Definition po_morphism' (X Y: PO.type) := po_morphism.type (dual X) (dual Y).
Notation "X -mon'-> Y" := (po_morphism' X Y) (at level 99, Y at level 200).

(** pointwise sups of monotone functions yield monotone functions *)
Lemma pointwise_inf_mon' {X Y} (F: (X-mon'-> Y) -> Prop) (g: X -> Y):
  (forall x, @is_inf Y(image (app x ∘ pobody) F) (g x)) ->
  Proper (flip leq ==> flip leq) g.
Proof. exact: (@pointwise_sup_mon (dual X) (dual Y)). Qed.
  


(** ** generic infimum operation *)

HB.mixin Record PO_ginf (k: gkind) X of PO X := {
    #[canonical=no] ginf: forall I P, k I P -> (I -mon-> dual X) -> X;
    #[canonical=no] ginf_spec: forall I P kIP (h: I -mon-> dual X), @is_inf X (image h P) (ginf I P kIP h);
  }.
HB.structure Definition ginfPO k := {X of PO_ginf k X & }.

(** duality with generic suprema *)
HB.instance Definition _ k (X: ginfPO.type k) := @PO_gsup.Build k (dual X) (@ginf k X) (@ginf_spec k X).
HB.instance Definition _ k (X: gsupPO.type k) := @PO_ginf.Build k (dual X) (@gsup k X) (@gsup_spec k X).

(** infs of a given kind are closed under dependent product formations *)
HB.instance Definition _ k A (X: A -> ginfPO.type k) := ginfPO.copy (forall a, X a) (dual (forall a, dual (X a))).

(** infs from monadic adjunctions *)
HB.factory Record monadic_ginf (k: gkind) Y of PO Y := {
    X: ginfPO.type k;
    a: Y ·⊣ X;
  }.
HB.builders Context k Y of monadic_ginf k Y.
 Definition ginf I P kIP (h: I -mon-> dual Y): Y :=
   radj a (@ginf k X I P kIP (dualf a ∘ h)).
 Lemma ginf_spec I P kIP (h: I -mon-> dual Y):
   @is_inf Y (image h P) (@ginf I P kIP h).
 Proof. apply: monadic_inf. rewrite -image_comp. exact: ginf_spec. Qed.
 HB.instance Definition _ := PO_ginf.Build k Y (@ginf) (@ginf_spec).
HB.end.

(** infs on sub-spaces *)
Section sub.
 Context {k} {X: ginfPO.type k}.
 Definition ginf_closed (P: X -> Prop) := forall I Q (kIQ: k I Q) (h: I -mon-> dual X), image h Q <= P -> P (ginf I Q kIQ h). 
 Lemma inf_ginf_closed: inf_closed <= ginf_closed. 
 Proof. exact: (@sup_gsup_closed k (dual X)). Qed.
 #[export] Instance ginf_closed_eqv: Proper (eqv==>eqv) ginf_closed.
 Proof. exact: (@gsup_closed_eqv k (dual X)). Qed.
 
 Definition inf_closed_sig P (HP: ginf_closed P) := sig P.
 Variables (P: X -> Prop) (HP: ginf_closed P). 
 HB.instance Definition _ := ginfPO.copy (inf_closed_sig HP) (dual (@sup_closed_sig k (dual X) P HP)).
End sub.
Arguments ginf_closed _ {_}. 

(** infs of monotone functions *)
Section s.
 Context {X: PO.type} {k} {Y: ginfPO.type k}.
 Lemma ginf_closed_monotone: ginf_closed k (Proper (@leq X ==> @leq Y)).
 Proof.
   rewrite -Proper_dual_leq.
   exact: (@gsup_closed_monotone k (dual X) (dual Y)).
 Qed.
 HB.instance Definition _ := monadic_ginf.Build k (X-mon->Y) (iso_dual_mon X Y).
End s.

(** infs of extensional functions *)
Section s.
 Context {X: Setoid.type} {k} {Y: ginfPO.type k}.
 Lemma ginf_closed_extensional: ginf_closed k (Proper (@eqv X ==> @eqv Y)).
 Proof.
   rewrite Proper_eqv_leq. 
   exact: (@ginf_closed_monotone (discrete X) k Y). 
 Qed.
 HB.instance Definition _ := ginfPO.copy (X-eqv->Y) (dual (X-eqv->dual Y)).
End s.



(** ** standard infimum operations *)


HB.mixin Record PO_top X of PO X := {
    #[canonical=no] top: X;
    #[canonical=no] top_spec: is_inf empty top;
  }.
HB.structure Definition topPO := {X of PO_top X & }.

HB.mixin Record PO_cap X of PO X := {
    #[canonical=no] cap: X -> X -> X;
    #[canonical=no] cap_spec: forall x y: X, is_inf (pair x y) (cap x y);
  }.
HB.structure Definition meetSemiLattice := {X of PO_cap X & }.
HB.structure Definition topmeetSemiLattice := {X of PO_top X & meetSemiLattice X }.

HB.mixin Record PO_cinf X of PO X := {
    #[canonical=no] cinf: forall P: X -> Prop, cochain P -> X;
    #[canonical=no] cinf_spec: forall (P: X -> Prop) C, is_inf P (cinf P C);
  }.
HB.builders Context X of PO_cinf X.
  HB.instance Definition _ := PO_top.Build X (cinf_spec cochain_empty).
HB.end.
HB.structure Definition CPO' := {X of PO_cinf X & }.

HB.mixin Record PO_dinf X of PO X := {
    #[canonical=no] dinf: forall P: X -> Prop, codirected P -> X;
    #[canonical=no] dinf_spec: forall (P: X -> Prop) D, is_inf P (dinf P D);
  }.
HB.builders Context X of PO_dinf X.
  HB.instance Definition _ := PO_cinf.Build X _ (fun P C => dinf_spec (cochain_codirected C)).
HB.end.
HB.structure Definition dCPO' := {X of PO_dinf X & }.

HB.mixin Record PO_iinf X of PO X := {
    #[canonical=no] iinf: forall I, (I -> Prop) -> (I -> X) -> X;
    #[canonical=no] iinf_spec: forall I P (h: I -> X), is_inf (image h P) (iinf I P h);
  }.
HB.builders Context X of PO_iinf X.
  Definition inf (P: X -> Prop) := iinf P types_id.
  Lemma inf_spec (P: X -> Prop): is_inf P (inf P).
  Proof. move: (iinf_spec P types_id). by rewrite image_id. Qed.
  HB.instance Definition _ := PO_cap.Build X _ (fun x y => inf_spec (pair x y)).
  HB.instance Definition _ := PO_dinf.Build X _ (fun D _ => inf_spec D).
HB.end.
HB.structure Definition infCL := {X of PO_iinf X & }.

HB.factory Record PO_inf X of PO X := {
    #[canonical=no] inf: (X -> Prop) -> X;
    #[canonical=no] inf_spec: forall P: X -> Prop, is_inf P (inf P);
  }.
HB.builders Context X of PO_inf X.
  Definition iinf I P (h: I -> X) := inf (image h P).
  Lemma iinf_spec I P h: is_inf (image h P) (@iinf I P h).
  Proof. apply: inf_spec. Qed.
  HB.instance Definition _ := PO_iinf.Build X _ iinf_spec.
HB.end.

(** ** duality *)

(** due to a bug in HB, needs
    https://github.com/Tragicus/hierarchy-builder/tree/uniq-mixin    
 *)

HB.instance Definition _ (X: botPO.type) := PO_top.Build (dual X) bot_spec. 
HB.instance Definition _ (X: topPO.type) := PO_bot.Build (dual X) top_spec. 

HB.instance Definition _ (X: joinSemiLattice.type) := PO_cap.Build (dual X) _ cup_spec.
HB.instance Definition _ (X: meetSemiLattice.type) := PO_cup.Build (dual X) _ cap_spec.

HB.instance Definition _ (X: CPO.type) := PO_cinf.Build (dual X) _ csup_spec.
HB.instance Definition _ (X: CPO'.type) := PO_csup.Build (dual X) _ cinf_spec.

HB.instance Definition _ (X: dCPO.type) := PO_dinf.Build (dual X) _ dsup_spec.
HB.instance Definition _ (X: dCPO'.type) := PO_dsup.Build (dual X) _ dinf_spec. 

HB.instance Definition _ (X: supCL.type) := PO_iinf.Build (dual X) _ isup_spec.
HB.instance Definition _ (X: infCL.type) := PO_isup.Build (dual X) _ iinf_spec.


(** ** theory *)

Notation inf P := (iinf _ P types_id).
Lemma inf_spec (X: infCL.type) (P: X -> Prop): is_inf P (inf P).
Proof. exact: (@sup_spec (dual X)). Qed. 

Lemma leq_top {X: topPO.type} (x: X): x <= top.
Proof. exact: (@geq_bot (dual X)). Qed.
Lemma geq_top {X: topPO.type} (x: X): top <= x -> x ≡ top.
Proof. exact: (@leq_bot (dual X)). Qed.

Lemma leq_cap {X: meetSemiLattice.type} (x y z: X): z <= x -> z <= y -> z <= cap x y.
Proof. exact: (@geq_cup (dual X)). Qed.
Lemma geq_cap_l {X: meetSemiLattice.type} (x y z: X): x <= z -> cap x y <= z.
Proof. exact: (@leq_cup_l (dual X)). Qed.
Lemma geq_cap_r {X: meetSemiLattice.type} (x y z: X): y <= z -> cap x y <= z.
Proof. exact: (@leq_cup_r (dual X)). Qed.

Lemma leq_cinf {X: CPO'.type} (P: X -> Prop) C (z: X): (forall x, P x -> z <= x) -> z <= cinf P C.
Proof. exact: (@geq_csup (dual X)). Qed.
Lemma geq_cinf {X: CPO'.type} (P: X -> Prop) C: forall z, P z -> cinf P C <= z.
Proof. exact: (@leq_csup (dual X)). Qed.

Lemma leq_dinf {X: dCPO'.type} (P: X -> Prop) D (z: X): (forall x, P x -> z <= x) -> z <= dinf P D.
Proof. exact: (@geq_dsup (dual X)). Qed.
Lemma geq_dinf {X: dCPO'.type} (P: X -> Prop) D: forall z, P z -> dinf P D <= z.
Proof. exact: (@leq_dsup (dual X)). Qed.

Lemma leq_iinf {X: infCL.type} I (P: I -> Prop) (h: I -> X) (z: X): (forall i, P i -> z <= h i) -> z <= iinf I P h.
Proof. exact: (@geq_isup (dual X)). Qed.
Lemma geq_iinf {X: infCL.type} I (P: I -> Prop) (h: I -> X) i: P i -> iinf I P h <= h i.
Proof. exact: (@leq_isup (dual X)). Qed.

Lemma leq_inf {X: infCL.type} (P: X -> Prop) (z: X): (forall y, P y -> z <= y) -> z <= inf P.
Proof. exact: (@geq_isup (dual X)). Qed.
Lemma geq_inf {X: infCL.type} (P: X -> Prop): forall z, P z -> inf P <= z.
Proof. exact: (@leq_isup (dual X)). Qed.

(* TODO: much more *)


(** ** concrete instances *)

Lemma unit_inf_spec P: is_inf P tt.
Proof. done. Qed.
HB.instance Definition _ := PO_iinf.Build unit _ (fun I P h => unit_inf_spec (image h P)).

Lemma bool_top_spec: is_inf empty true.
Proof. by case. Qed. 
Lemma bool_cap_spec b c: is_inf (pair b c) (b && c).
Proof. move=>d. rewrite forall_pair. case:b; case:c; case:d; cbn; intuition discriminate. Qed. 

HB.instance Definition _ := PO_top.Build bool bool_top_spec.
HB.instance Definition _ := PO_cap.Build bool _ bool_cap_spec.

Lemma Prop_top_spec: is_inf empty True.
Proof. cbv; tauto. Qed. 
Lemma Prop_cap_spec (P Q: Prop): is_inf (pair P Q) (P /\ Q).
Proof. move=>R. rewrite forall_pair. cbv; tauto. Qed. 
Lemma Prop_iinf_spec I P (h: I -> Prop): is_inf (image h P) (forall i, P i -> h i).
Proof. rewrite is_inf_image. cbv; firstorder. Qed.
HB.instance Definition _ := PO_top.Build Prop Prop_top_spec.
HB.instance Definition _ := PO_cap.Build Prop _ Prop_cap_spec.
HB.instance Definition _ := PO_iinf.Build Prop _ Prop_iinf_spec.


(** liftings to dependent products [forall i, X i], by duality *)
HB.instance Definition _ I (X: I -> topPO.type) := topPO.copy (forall i, X i) (dual (forall i, dual (X i))). 
HB.instance Definition _ I (X: I -> meetSemiLattice.type) := meetSemiLattice.copy (forall i, X i) (dual (forall i, dual (X i))). 
HB.instance Definition _ I (X: I -> CPO'.type) := CPO'.copy (forall i, X i) (dual (forall i, dual (X i))). 
HB.instance Definition _ I (X: I -> dCPO'.type) := dCPO'.copy (forall i, X i) (dual (forall i, dual (X i))). 
HB.instance Definition _ I (X: I -> infCL.type) := infCL.copy (forall i, X i) (dual (forall i, dual (X i))). 

(** restriction to extensive functions, by duality *)
HB.instance Definition _ (X: Setoid.type) (Y: topPO.type) := topPO.copy (X -eqv-> Y) (dual (X -eqv-> dual Y)).
HB.instance Definition _ (X: Setoid.type) (Y: meetSemiLattice.type) := meetSemiLattice.copy (X -eqv-> Y) (dual (X -eqv-> dual Y)).
HB.instance Definition _ (X: Setoid.type) (Y: CPO'.type) := CPO'.copy (X -eqv-> Y) (dual (X -eqv-> dual Y)).
HB.instance Definition _ (X: Setoid.type) (Y: dCPO'.type) := dCPO'.copy (X -eqv-> Y) (dual (X -eqv-> dual Y)).
HB.instance Definition _ (X: Setoid.type) (Y: infCL.type) := infCL.copy (X -eqv-> Y) (dual (X -eqv-> dual Y)).

(** restriction to monotone functions cannot be done as above,
    because [dual (X -mon-> dual Y)] is not definitionally equivalent to [X -mon-> Y]
 *)


(** ** link between generic and standard operations *)

(** *** top elements as generic infs over empty domains *)
Definition top_gen (X: Type) := X.
HB.instance Definition _ (X: PO.type) := PO.on (top_gen X).
Section s.
 Context {X: ginfPO.type empty_kind}.
 Definition ginf_top: X := ginf False empty False_empty_kind empty_fun.
 Lemma ginf_top_spec: is_inf empty ginf_top.
 Proof.
   rewrite -(image_empty_kind False_empty_kind empty_fun).
   exact: ginf_spec.
 Qed.
 HB.instance Definition _ := PO_top.Build (top_gen X) ginf_top_spec.
End s.
Section s.
 Context {X: topPO.type}.
 Section t. 
  Variables (I: PO.type) (P: I -> Prop) (H: empty_kind I P) (h: I -mon-> dual X). 
  Lemma top_ginf_spec: @is_inf X (image h P) top.
  Proof. rewrite (image_empty_kind (X:=X) H). exact: top_spec. Qed.
 End t.
 HB.instance Definition _ := PO_ginf.Build empty_kind (top_gen X) _ top_ginf_spec. 
End s.

Lemma top_ginf_closed {X: topPO.type} (P: X -> Prop) (Ptop: P top): @ginf_closed empty_kind (top_gen X) P.
Proof. done. Qed.

HB.factory Record monadic_top Y of PO Y := { X: topPO.type; f: Y ·⊣ X; }.
HB.builders Context Y of monadic_top Y.
 HB.instance Definition _ := monadic_ginf.Build empty_kind Y (X:=top_gen X) f.
 HB.instance Definition _ := topPO.copy Y (top_gen Y).
HB.end.

(** *** binary meets as generic infs over 2-element domains *)
Definition cap_gen (X: Type) := X.
HB.instance Definition _ (X: PO.type) := PO.on (cap_gen X).
Section s.
 Context {X: ginfPO.type pair_kind}.
 Section s.
  Variables x y: X. 
  Definition ginf_cap := ginf (discrete bool) full bool_pair_kind (@discretemon (discrete bool) (dual X) (bool_fun x y)).
  Lemma ginf_cap_spec: is_inf (pair x y) ginf_cap.
  Proof.
    rewrite -(image_pair_kind bool_pair_kind (bool_fun x y)).
    exact: ginf_spec.
  Qed.
 End s.
 HB.instance Definition _ := PO_cap.Build (cap_gen X) _ ginf_cap_spec.
End s.
Section s.
 Context {X: meetSemiLattice.type}.
 Section t. 
  Variables (I: PO.type) (P: I -> Prop) (H: pair_kind I P) (h: I -mon-> dual X). 
  Definition cap_ginf: X := cap (h (elem1 H)) (h (elem2 H)).
  Lemma cap_ginf_spec: @is_inf X (image h P) cap_ginf.
  Proof. rewrite (image_pair_kind H (X:=X)). exact: cap_spec. Qed.
 End t.
 HB.instance Definition _ := PO_ginf.Build pair_kind (cap_gen X) _ cap_ginf_spec. 
End s.

Lemma cap_ginf_closed {X: meetSemiLattice.type} (P: X -> Prop) (Pcap: forall x y, P x -> P y -> P (cap x y)):
  @ginf_closed pair_kind (cap_gen X) P.
Proof. move=>I Q kIQ h /forall_image H. apply: Pcap; apply: H; apply kIQ. Qed.

HB.factory Record monadic_cap Y of PO Y := { X: meetSemiLattice.type; f: Y ·⊣ X }.
HB.builders Context Y of monadic_cap Y.
 HB.instance Definition _ := monadic_ginf.Build pair_kind Y (X:=cap_gen X) f.
 HB.instance Definition _ := meetSemiLattice.copy Y (cap_gen Y).
HB.end.

(** *** chain infs as generic infs over chain domains *)
Definition cinf_gen (X: Type) := X.
HB.instance Definition _ (X: PO.type) := PO.on (cinf_gen X).
Section s.
 Context {X: ginfPO.type (@chain)}.
 Section s.
  Variables (P: X -> Prop) (D: cochain P). 
  Definition ginf_cinf := ginf (dual X) P D types_id.
  Lemma ginf_cinf_spec: @is_inf X P ginf_cinf.
  Proof. move: (ginf_spec (dual X) P D types_id). by rewrite (image_id (X:=X)). Qed.
 End s.
 HB.instance Definition _ := PO_cinf.Build (cinf_gen X) _ ginf_cinf_spec.
End s.
Section s.
 Context {X: CPO'.type}.
 Section t. 
  Variables (I: PO.type) (P: I -> Prop) (D: chain P) (h: I -mon-> dual X). 
  Definition cinf_ginf: X := cinf (image h P) (chain_image h D).
  Lemma cinf_ginf_spec: @is_inf X (image h P) cinf_ginf.
  Proof. exact: cinf_spec. Qed.
 End t.
 HB.instance Definition _ := PO_ginf.Build (@chain) (cinf_gen X) _ cinf_ginf_spec. 
End s.

Lemma cinf_ginf_closed {X: CPO'.type} (P: X -> Prop) (Pcinf: forall Q (C: cochain Q), Q <= P -> P (cinf Q C)):
  @ginf_closed (@chain) (cinf_gen X) P.
Proof. move=>I Q kIQ h H. exact: Pcinf. Qed.

HB.factory Record monadic_cinf Y of PO Y := { X: CPO'.type; f: Y ·⊣ X; }.
HB.builders Context Y of monadic_cinf Y.
 HB.instance Definition _ := monadic_ginf.Build (@chain) Y (X:=cinf_gen X) f.
 HB.instance Definition _ := CPO'.copy Y (cinf_gen Y).
HB.end.

(** *** directed infs as generic infs over directed domains *)
Definition dinf_gen (X: Type) := X.
HB.instance Definition _ (X: PO.type) := PO.on (dinf_gen X).
Section s.
 Context {X: ginfPO.type (@directed)}.
 Section s.
  Variables (P: X -> Prop) (D: codirected P). 
  Definition ginf_dinf := ginf (dual X) P D types_id.
  Lemma ginf_dinf_spec: @is_inf X P ginf_dinf.
  Proof. move: (ginf_spec (dual X) P D types_id). by rewrite (image_id (X:=X)). Qed.
 End s.
 HB.instance Definition _ := PO_dinf.Build (dinf_gen X) _ ginf_dinf_spec.
End s.
Section s.
 Context {X: dCPO'.type}.
 Section t. 
  Variables (I: PO.type) (P: I -> Prop) (D: directed P) (h: I -mon-> dual X). 
  Definition dinf_ginf: X := dinf (image h P) (directed_image h D).
  Lemma dinf_ginf_spec: @is_inf X (image h P) dinf_ginf.
  Proof. exact: dinf_spec. Qed.
 End t.
 HB.instance Definition _ := PO_ginf.Build (@directed) (dinf_gen X) _ dinf_ginf_spec. 
End s.

Lemma dinf_ginf_closed {X: dCPO'.type} (P: X -> Prop) (Pdinf: forall Q (D: codirected Q), Q <= P -> P (dinf Q D)):
  @ginf_closed (@directed) (dinf_gen X) P.
Proof. move=>I Q kIQ h H. exact: Pdinf. Qed.

HB.factory Record monadic_dinf Y of PO Y := { X: dCPO'.type; f: Y ·⊣ X }.
HB.builders Context Y of monadic_dinf Y.
 HB.instance Definition _ := monadic_ginf.Build (@directed) Y (X:=dinf_gen X) f.
 HB.instance Definition _ := dCPO'.copy Y (dinf_gen Y).
HB.end.

(** *** indexed arbitrary infs as generic infs of arbitrary kind *)
Definition iinf_gen (X: Type) := X.
HB.instance Definition _ (X: PO.type) := PO.on (iinf_gen X).
Section s.
 Context {X: ginfPO.type any_kind}.
 Section s.
  Variables (I: Type) (P: I -> Prop) (h: I -> X). 
  Definition ginf_iinf :=
    ginf (discrete (strict I)) P Logic.I
      (@mk_mon (discrete (strict I)) (dual X) h _).
  Lemma ginf_iinf_spec: @is_inf X (image h P) ginf_iinf.
  Proof. exact: ginf_spec. Qed.
 End s.
 HB.instance Definition _ := PO_iinf.Build (iinf_gen X) _ ginf_iinf_spec.
End s.
Section s.
 Context {X: infCL.type}.
 Section t. 
  Variables (I: PO.type) (P: I -> Prop) (kIP: any_kind I P) (h: I -mon-> dual X). 
  Definition iinf_ginf: X := let _ := kIP in iinf I P h.
  Lemma iinf_ginf_spec: is_inf (X:=X) (image h P) iinf_ginf.
  Proof. exact: iinf_spec. Qed.
 End t.
 HB.instance Definition _ := PO_ginf.Build any_kind (iinf_gen X) _ iinf_ginf_spec. 
End s.

Lemma iinf_ginf_closed {X: infCL.type} (P: X -> Prop) (Piinf: forall I Q h, image h Q <= P -> P (iinf I Q h)):
  @ginf_closed any_kind (iinf_gen X) P.
Proof. move=>I Q kIQ h H; exact: Piinf. Qed.

HB.factory Record monadic_iinf Y of PO Y := { X: infCL.type; f: Y ·⊣ X }.
HB.builders Context Y of monadic_iinf Y.
 HB.instance Definition _ := monadic_ginf.Build any_kind Y (X:=iinf_gen X) f.
 HB.instance Definition _ := infCL.copy Y (iinf_gen Y).
HB.end.

(** restriction to monotone functions follow generically *)
HB.instance Definition _ (X: PO.type) (Y: topPO.type) := topPO.copy (X -mon-> Y) (top_gen (X -mon-> top_gen Y)).
HB.instance Definition _ (X: PO.type) (Y: meetSemiLattice.type) := meetSemiLattice.copy (X -mon-> Y) (cap_gen (X -mon-> cap_gen Y)).
HB.instance Definition _ (X: PO.type) (Y: CPO'.type) := CPO'.copy (X -mon-> Y) (cinf_gen (X -mon-> cinf_gen Y)).
HB.instance Definition _ (X: PO.type) (Y: dCPO'.type) := dCPO'.copy (X -mon-> Y) (dinf_gen (X -mon-> dinf_gen Y)).
HB.instance Definition _ (X: PO.type) (Y: infCL.type) := infCL.copy (X -mon-> Y) (iinf_gen (X -mon-> iinf_gen Y)).

(** ALTERNATIVE: by explicit duality *)
(* HB.instance Definition _ (X: PO.type) (Y: topPO.type) := monadic_top.Build (X -mon-> Y) (iso_dual_mon X Y). *)
(* HB.instance Definition _ (X: PO.type) (Y: meetSemiLattice.type) := monadic_cap.Build (X -mon-> Y) (iso_dual_mon X Y). *)
(* HB.instance Definition _ (X: PO.type) (Y: CPO'.type) := monadic_cinf.Build (X -mon-> Y) (iso_dual_mon X Y). *)
(* HB.instance Definition _ (X: PO.type) (Y: dCPO'.type) := monadic_dinf.Build (X -mon-> Y) (iso_dual_mon X Y). *)
(* HB.instance Definition _ (X: PO.type) (Y: infCL.type) := monadic_iinf.Build (X -mon-> Y) (iso_dual_mon X Y). *)

(* Check ((nat->bool)-mon->(nat->Prop)): infCL.type. *)
