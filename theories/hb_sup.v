From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Export hb_po.
Require Import hb_adjunctions.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

(** * suprema in partial orders *)

(** ** general properties of suprema *)

Section s.

Context {X: PO.type}.
Implicit Types x y z: X. 
Implicit Types P Q: X -> Prop.

Definition sup_closed (P: X -> Prop) := forall Q, Q <= P -> forall z, is_sup Q z -> P z.

Lemma sup_closed_impl (P Q: X -> Prop): Proper (leq --> leq) P -> sup_closed Q -> sup_closed (fun x => P x -> Q x).
Proof.
  intros HP HQ T TPQ x Tx Px.
  eapply HQ. 2: apply Tx.
  intros y Ty. apply: TPQ=>//.
  apply: HP. 2: apply Px.
  by apply Tx. 
Qed.

Lemma sup_closed_leq (f: X -mon-> X): sup_closed (fun x => x <= f x).
Proof.
  intros T HT x Tx. apply Tx=>y Ty. 
  transitivity (f y). by apply: HT.
  by apply f, Tx.
Qed.

Lemma sup_closed_Proper P: sup_closed P -> Proper (eqv ==> eqv) P.
Proof.
  move=>H. apply/Proper_eqv_leq. 
  move=>x y xy Px. apply: (H (eq x)). by move=>?<-. 
  move: (is_sup_single x). by apply Proper_is_sup. 
Qed.

Inductive sup_closure P: X -> Prop :=
| sc_inj: P <= sup_closure P
| sc_sup: sup_closed (sup_closure P).

Lemma is_sup_closure P: is_sup (sup_closure P) ≡ is_sup P.
Proof.
  move=>x. 
  apply: Proper_forall=>z.
  apply: Proper_iff=>//{x}.
  split=>H x Px.
  - by apply H; apply: sc_inj.
  - elim: Px=>//Q QP IH y Hy. by apply Hy, IH. 
Qed.

Lemma is_sup_image {A} (f: A -> X) (P: A -> Prop) x:
  is_sup (image f P) x <-> forall z, x <= z <-> forall a, P a -> f a <= z.
Proof.
  change ((forall z, x <= z <-> (image f P <= (fun y => y <= z))) <->
            (forall z, x <= z <-> (forall a, P a -> f a <= z))).        
  by setoid_rewrite forall_image.
Qed.

End s.

(** sups can be computed pointwise in function spaces *)
Lemma dprod_sup {A} {X: A -> PO.type} (P: (forall a, X a) -> Prop) (f: forall a, X a):
  (forall a, is_sup (image (app a) P) (f a)) -> is_sup P f.
Proof.
  move=>H g; split=>fg.
  - move=>h Ph. rewrite -fg=>a. apply H=>//. by exists h.
  - move=>a. apply H=>_ [h [Ph ->]]. by apply: fg. 
Qed.
(** sups being unique, they *must* be computed pointwise if they can
    (i.e., when there are enough sups in X) *)
Lemma dprod_sup' {A} {X: A -> PO.type} (P: (forall a, X a) -> Prop) (f g: forall a, X a):
  (forall a, is_sup (image (app a) P) (f a)) -> 
  is_sup P g -> forall a, is_sup (image (app a) P) (g a).
Proof.
  move=>Pf Pg.
  have Pf': is_sup P f by apply: dprod_sup.
  have fg: f ≡ g by apply: is_sup_eqv.
  move=>a. by rewrite -(fg a).
Qed.
(** alternatively, they *must* be computed pointwise when [A] is decidable *)
Lemma dprod_sup'' {A} {X: A -> PO.type}
      (A_dec: forall a b: A, {a=b} + {a<>b})
      (P: (forall a, X a) -> Prop) (f: forall a, X a):
  is_sup P f -> forall a, is_sup (image (app a) P) (f a).
Proof.
  move=>Pf a. split=>az.
  - move=>_ [b [Pb ->]]. rewrite -az. by apply: (leq_is_sup Pf).
  - set h := fun b =>
               match A_dec a b return X b with
               | left E => match E in _=c return X c with
                          | eq_refl _ => z
                          end
               | _ => f b
               end.
    have ha: h a = z. {
      unfold h. case A_dec=>//e.
      have E: e = eq_refl by apply Eqdep_dec.UIP_dec.
      by rewrite E.
    }
    rewrite -ha. apply: (proj2 (Pf h))=>g Pg b.
    unfold h. case A_dec=>ab. destruct ab.
    -- apply az. by exists g.
    -- by apply: (leq_is_sup Pf). 
Qed.

(** sups are computed pointwise in products
    TOTHINK: get it as as special case of [dprod_sup''], with [A=bool]?      
 *)
Lemma prod_sup {X Y: PO.type} (P: X*Y -> Prop) (p: X*Y):
  (is_sup (image fst P) (fst p) /\ is_sup (image snd P) (snd p)) <-> is_sup P p.
Proof.
  destruct p as [x y]. split.
  - move=>/=[H1 H2] [u v]. unfold leq=>/=. rewrite (H1 u) (H2 v)/=.
    split. move=>[F1 F2] [i j] Hij. split. apply F1. by eexists; eauto. apply F2. by eexists; eauto.
    move=>H. by split=>t [[i j] [Hij ->]]; apply H.
  - move=>H. split=>/=z.
    -- split=>E. move=>_ [[u v] [Huv ->]]/=. 
       rewrite -E. apply (leq_is_sup H _ Huv).
       apply <- (H (z,y))=>[[u v] Puv]. split. apply E. by eexists; eauto. cbn.
       apply (leq_is_sup H _ Puv).
    -- split=>E. move=>_ [[u v] [Huv ->]]/=. 
       rewrite -E. apply (leq_is_sup H _ Huv).
       apply <- (H (x,z))=>[[u v] Puv]. split; last first. apply E. by eexists; eauto. cbn.
       apply (leq_is_sup H _ Puv).
Qed.

(** sups can be computed as expected in sub-spaces *)
(* recall that [kernel f = A] *)
Lemma kern_sup {A} {X: PO.type} (f: A -> X) (P: kernel f->Prop) (a: kernel f):
  is_sup (image f P) (f a) -> is_sup P a.
Proof.
  move=>H b; split=>ab.
  -- move=>c Pc. rewrite -ab. by apply H; auto. 
  -- apply H=>_ [c [Pc ->]]. by apply ab.
Qed.

(** pointwise sups of monotone functions yield monotone functions *)
(* can be skipped, cf. only occurrence below *)
Lemma pointwise_sup_mon {X Y} (F: (X-mon->Y) -> Prop) (g: X -> Y):
  (forall x, is_sup (image (app x ∘ pobody) F) (g x)) ->
  Proper (leq ==> leq) g.
Proof.
  move=>Fg x y xy.
  apply: (geq_is_sup (Fg _))=>z [f [Ff ->{z}]].
  rewrite /app/pobody/=xy.
  apply: (leq_is_sup (Fg _)).
  exact: in_image.
Qed.


(** ** generic supremum operation *)

Definition gkind := forall X: PO.type, (X -> Prop) -> Type.

HB.mixin Record PO_gsup (k: gkind) X of PO X := {
    #[canonical=no] gsup: forall I P, k I P -> (I -mon-> X) -> X;
    #[canonical=no] gsup_spec: forall I P kIP (h: I -mon-> X), is_sup (image h P) (gsup I P kIP h);
  }.
HB.structure Definition gsupPO k := {X of PO_gsup k X & }.

(** sups of a given kind are closed under dependent product formations *)
Program Definition dprod_gsup k A (X: A -> gsupPO.type k)
  := PO_gsup.Build k (forall a, X a) (fun I P kIP h a => gsup I P kIP (app a ∘ h)) _.
Next Obligation. 
  apply: dprod_sup=>a. rewrite -image_comp. exact: gsup_spec. 
Qed.
HB.instance Definition _ k A X := @dprod_gsup k A X.

(** sups from comonadic adjunctions *)
HB.factory Record comonadic_gsup (k: gkind) Y of PO Y := {
    X: gsupPO.type k;
    f: X ⊣· Y;
  }.
HB.builders Context k Y of comonadic_gsup k Y.
 Definition gsup I P kIP (h: I -mon-> Y): Y :=
   f (@gsup k X I P kIP (radj f ∘ h)).
 Lemma gsup_spec I P kIP (h: I -mon-> Y):
   is_sup (image h P) (@gsup I P kIP h).
 Proof. apply: comonadic_sup. rewrite -image_comp. exact: gsup_spec. Qed.
 HB.instance Definition _ := PO_gsup.Build k Y (@gsup) (@gsup_spec).
HB.end.

(** sups on sub-spaces *)
Section sub.
 Context {k} {X: gsupPO.type k}.
 Definition gsup_closed (P: X -> Prop) := forall I Q (kIQ: k I Q) (h: I -mon-> X), image h Q <= P -> P (gsup I Q kIQ h). 
 Lemma sup_gsup_closed: sup_closed <= gsup_closed. 
 Proof. move=>P HP I Q kIQ h hQP. apply: HP. exact: hQP. exact: gsup_spec. Qed.
 #[export] Instance gsup_closed_eqv: Proper (eqv==>eqv) gsup_closed.
 Proof.
   apply/Proper_eqv_leq=>P P' PP' HP I Q kIQ h hQP'.
   apply/PP'. apply: HP. by rewrite hQP' PP'.
 Qed.
 
 Definition sup_closed_sig P (HP: gsup_closed P) := sig P.
 Variables (P: X -> Prop) (HP: gsup_closed P). 
 Program Definition sig_gsup I Q (kIQ: k I Q) (h: I -mon-> sig P): sig P :=
   exist P (gsup I Q kIQ (sval ∘ h)) _.
 Next Obligation. apply: HP. apply/forall_image=>i Qi. exact: proj2_sig. Qed.
 Lemma sig_gsup_spec I Q kIQ (h: I -mon-> sig P):
   is_sup (image h Q) (@sig_gsup I Q kIQ h).
 Proof. apply: kern_sup=>/=. rewrite -image_comp. exact: gsup_spec. Qed.
 HB.instance Definition _ := PO.on (sup_closed_sig HP).
 HB.instance Definition _ := PO_gsup.Build k (sup_closed_sig HP) _ sig_gsup_spec.
End sub.
Arguments gsup_closed _ {_}. 

(** sups of monotone functions *)
Section s.
 Context {k} {X: PO.type} {Y: gsupPO.type k}.
 Lemma gsup_closed_monotone: gsup_closed k (Proper (@leq X ==> @leq Y)).
 Proof.
   (* proof with [pointwise_sup_mon] *)
   move=>I Q kIQ h hQ.
   apply: (pointwise_sup_mon (F:=image h Q ∘ pobody))=>x. 
   eapply Proper_is_sup. 2: reflexivity. 2: exact: gsup_spec.
   split.
   - move=>? [g [[i [Qi E]] ->]]. eexists; split. exists i; split=>//. by rewrite /app/= E.
   - move=>? [i [Qi ->]].
     have E: Proper (leq ==> leq) (h i) by apply: hQ; exact: in_image.
     eexists; split. exists (mk_mon _ E); split=>//. exists i; split=>//. reflexivity.
   (* direct proof *)
   Restart.
   move=>I Q kIQ h hQ x y xy.
   rewrite gsup_spec=>z [i [Qi ->]].
   transitivity (h i y).
   have E: Proper (leq ==> leq) (h i) by apply: hQ; exact: in_image.
   by rewrite -xy.
   apply: leq_is_sup. apply gsup_spec. exact: in_image. 
 Qed.
 (* NOTE: we need kernel compositions to behave well in order the following instance to typecheck *)
 HB.instance Definition _ :=
   comonadic_gsup.Build k (X-mon->Y) (X:=sup_closed_sig gsup_closed_monotone) po_morphism_as_sig. 
End s.

(** sups of extensional functions *)
Section s.
 Context {k} {X: Setoid.type} {Y: gsupPO.type k}.
 Lemma gsup_closed_extensional: gsup_closed k (Proper (@eqv X ==> @eqv Y)).
 Proof.
   rewrite Proper_eqv_leq. 
   exact: (@gsup_closed_monotone k (discrete X) Y). 
 Qed.
 (* NOTE: we need kernel compositions to behave well in order the following instance to typecheck *)
 HB.instance Definition _ :=
   comonadic_gsup.Build k (X-eqv->Y) (X:=sup_closed_sig gsup_closed_extensional) setoid_morphism_as_sig. 
End s.

(** left adjunctions preserve sups *)
Lemma adj_gsup {k} {X Y: gsupPO.type k} (f: X ⊣ Y) I P kIP h:
  f (@gsup k X I P kIP h) ≡ gsup I P kIP (f ∘ h). 
Proof.
  apply: from_above=>y.
  rewrite adj 2!gsup_spec.
  setoid_rewrite forall_image.
  apply: forall_iff=>i.
  by rewrite -adj. 
Qed.

(** ** standard supremum operations *)

(** *** bottom element *)
HB.mixin Record PO_bot X of PO X := {
    #[canonical=no] bot: X;
    #[canonical=no] bot_spec: is_sup empty bot;
  }.
HB.structure Definition botPO := {X of PO_bot X & }.

(** *** binary joins *)
HB.mixin Record PO_cup X of PO X := {
    #[canonical=no] cup: X -> X -> X;
    #[canonical=no] cup_spec: forall x y: X, is_sup (pair x y) (cup x y);
  }.
HB.structure Definition joinSemiLattice := {X of PO_cup X & }.
HB.structure Definition botjoinSemiLattice := {X of PO_bot X & joinSemiLattice X }.

(** *** chain suprema (CPOs) *)
HB.mixin Record PO_csup X of PO X := {
    #[canonical=no] csup: forall P: X -> Prop, chain P -> X;
    #[canonical=no] csup_spec: forall (P: X -> Prop) C, is_sup P (csup P C);
  }.
HB.builders Context X of PO_csup X.
  HB.instance Definition _ := PO_bot.Build X (csup_spec chain_empty).
HB.end.
HB.structure Definition CPO := {X of PO_csup X & }.

(** *** directed suprema (dCPOs) *)
HB.mixin Record PO_dsup X of PO X := {
    #[canonical=no] dsup: forall P: X -> Prop, directed P -> X;
    #[canonical=no] dsup_spec: forall (P: X -> Prop) D, is_sup P (dsup P D);
  }.
HB.builders Context X of PO_dsup X.
  HB.instance Definition _ := PO_csup.Build X _ (fun P C => dsup_spec (chain_directed C)).
HB.end.
HB.structure Definition dCPO := {X of PO_dsup X & }.

(** *** all suprema (complete lattices -- derivable infima arrive later, in po_inf.v and then po_lattice.v) *)
(** using `indexed' sups, which is convenient in practice *)
HB.mixin Record PO_isup X of PO X := {
    #[canonical=no] isup: forall I, (I -> Prop) -> (I -> X) -> X;
    #[canonical=no] isup_spec: forall I P (h: I -> X), is_sup (image h P) (isup I P h);
  }.
HB.builders Context X of PO_isup X.
  Definition sup (P: X -> Prop) := isup P types_id.
  Lemma sup_spec (P: X -> Prop): is_sup P (sup P).
  Proof. move: (isup_spec P types_id). by rewrite image_id. Qed.
  HB.instance Definition _ := PO_cup.Build X _ (fun x y => sup_spec (pair x y)).
  HB.instance Definition _ := PO_dsup.Build X _ (fun D _ => sup_spec D).
HB.end.
HB.structure Definition supCL := {X of PO_isup X & }.

(** non-indexed sups are equivalent to indexed sups *)
HB.factory Record PO_sup X of PO X := {
    #[canonical=no] sup: (X -> Prop) -> X;
    #[canonical=no] sup_spec: forall P: X -> Prop, is_sup P (sup P);
  }.
HB.builders Context X of PO_sup X.
  Definition isup I P (h: I -> X) := sup (image h P).
  Lemma isup_spec I P h: is_sup (image h P) (@isup I P h).
  Proof. apply: sup_spec. Qed.
  HB.instance Definition _ := PO_isup.Build X _ isup_spec.
HB.end.



(** ** theory *)

Notation sup P := (isup _ P types_id).
Lemma sup_spec (X: supCL.type) (P: X -> Prop): is_sup P (sup P).
Proof. move: (isup_spec X P types_id). by rewrite image_id. Qed.

Lemma geq_bot {X: botPO.type} (z: X): bot <= z.
Proof. by rewrite bot_spec forall_empty. Qed.
Lemma leq_bot {X: botPO.type} (z: X): z <= bot -> z ≡ bot. (* iff, reversed? *)
Proof. move=>H. apply: antisym=>//. apply: geq_bot. Qed.
Lemma adj_bot {X Y: botPO.type} (f: X ⊣ Y): f bot ≡ bot. 
Proof.
  apply: from_above=>y.
  by rewrite adj 2!bot_spec 2!forall_empty.
Qed.

Lemma geq_cup {X: joinSemiLattice.type} (x y z: X): x <= z -> y <= z -> cup x y <= z.
Proof. move=>xz yz. apply/geq_is_sup. exact:cup_spec. by rewrite forall_pair. Qed.
Lemma leq_cup_l {X: joinSemiLattice.type} (x y z: X): z <= x -> z <= cup x y.
Proof. move=>->. apply/leq_is_sup. exact: cup_spec. by left. Qed.
Lemma leq_cup_r {X: joinSemiLattice.type} (x y z: X): z <= y -> z <= cup x y.
Proof. move=>->. apply/leq_is_sup. exact: cup_spec. by right. Qed.
Lemma adj_cup {X Y: joinSemiLattice.type} (f: X ⊣ Y) (x y: X): f (cup x y) ≡ cup (f x) (f y). 
Proof.
  apply: from_above=>z.
  by rewrite adj 2!cup_spec 2!forall_pair -2!adj.
Qed.

Lemma geq_csup {X: CPO.type} (P: X -> Prop) C (z: X): (forall x, P x -> x <= z) -> csup P C <= z.
Proof. apply geq_is_sup, csup_spec. Qed.
Lemma leq_csup {X: CPO.type} (P: X -> Prop) C: forall z, P z -> z <= csup P C.
Proof. apply leq_is_sup, csup_spec. Qed.
Lemma adj_csup {X Y: CPO.type} (f: X ⊣ Y) (P: X -> Prop) C: f (csup P C) ≡ csup (image f P) (chain_image f C). 
Proof.
  apply: from_above=>y.
  rewrite adj 2!csup_spec /=.
  setoid_rewrite forall_image.
  apply: forall_iff=>x.
  by rewrite -adj.
Qed.

Lemma geq_dsup {X: dCPO.type} (P: X -> Prop) D (z: X): (forall y, P y -> y <= z) -> dsup P D <= z.
Proof. apply geq_is_sup, dsup_spec. Qed.
Lemma leq_dsup {X: dCPO.type} (P: X -> Prop) D: forall z, P z -> z <= dsup P D.
Proof. apply leq_is_sup, dsup_spec. Qed.
Lemma adj_dsup {X Y: dCPO.type} (f: X ⊣ Y) (P: X -> Prop) D: f (dsup P D) ≡ dsup (image f P) (directed_image f D). 
Proof.
  apply: from_above=>y.
  rewrite adj 2!dsup_spec /=.
  setoid_rewrite forall_image.
  apply: forall_iff=>x.
  by rewrite -adj.
Qed.
  
Lemma geq_isup {X: supCL.type} I (P: I -> Prop) (h: I -> X) (z: X): (forall i, P i -> h i <= z) -> isup I P h <= z.
Proof. move=>H. apply: geq_is_sup. exact: isup_spec. by setoid_rewrite forall_image. Qed.
Lemma leq_isup {X: supCL.type} I (P: I -> Prop) (h: I -> X) i: P i -> h i <= isup I P h.
Proof. move=>Pi. apply: leq_is_sup. exact: isup_spec. exact: in_image. Qed.
Lemma adj_isup {X Y: supCL.type} (f: X ⊣ Y) I P h:
  f (isup I P h) ≡ isup I P (f ∘ h). 
Proof.
  apply: from_above=>y.
  rewrite adj 2!isup_spec/=.
  setoid_rewrite forall_image.
  apply: forall_iff=>i.
  by rewrite -adj. 
Qed.

Lemma geq_sup {X: supCL.type} (P: X -> Prop) (z: X): (forall y, P y -> y <= z) -> sup P <= z.
Proof. apply geq_isup. Qed.
Lemma leq_sup {X: supCL.type} (P: X -> Prop): forall z, P z -> z <= sup P.
Proof. apply leq_isup. Qed.
Lemma adj_sup {X Y: supCL.type} (f: X ⊣ Y) P:
  f (sup P) ≡ isup X P f. 
Proof. exact: adj_isup. Qed.


(** ** concrete instances *)

Lemma unit_sup_spec P: is_sup P tt.
Proof. done. Qed.
HB.instance Definition _ := PO_sup.Build unit _ unit_sup_spec.

Lemma bool_bot_spec: is_sup empty false.
Proof. done. Qed. 
Lemma bool_cup_spec b c: is_sup (pair b c) (b || c).
Proof. move=>d. rewrite forall_pair. case:b; case:c; case:d; cbn; intuition discriminate. Qed. 
HB.instance Definition _ := PO_bot.Build bool bool_bot_spec.
HB.instance Definition _ := PO_cup.Build bool _ bool_cup_spec.

Lemma Prop_bot_spec: is_sup empty False.
Proof. cbv; tauto. Qed. 
Lemma Prop_cup_spec (P Q: Prop): is_sup (pair P Q) (P \/ Q).
Proof. move=>R. rewrite forall_pair. cbv; tauto. Qed. 
Lemma Prop_isup_spec I P (h: I -> Prop): is_sup (image h P) (exists2 i, P i & h i).
Proof. rewrite is_sup_image. cbv; firstorder. Qed.
HB.instance Definition _ := PO_bot.Build Prop Prop_bot_spec.
HB.instance Definition _ := PO_cup.Build Prop _ Prop_cup_spec.
HB.instance Definition _ := PO_isup.Build Prop _ Prop_isup_spec.


(* direct proofs that we can lift dependent products to PO with various sups
   (can be removed thanks to the generic machinery)
 *)
Module DIRECT_DPROD.
Section dprod.
 Variable A: Type.

 Program Definition dprod_bot (X: A -> botPO.type) :=
   @PO_bot.Build (forall a, X a) (fun _ => bot) _. 
 Next Obligation.
   apply: dprod_sup=>a. rewrite image_empty. exact: bot_spec.
 Qed.
 HB.instance Definition _ X := dprod_bot X.

 Program Definition dprod_cup (X: A -> joinSemiLattice.type) :=
   PO_cup.Build (forall a, X a) (fun f g a => cup (f a) (g a)) _. 
 Next Obligation.
   apply: dprod_sup=>a. rewrite image_pair. exact: cup_spec.
 Qed.  
 HB.instance Definition _ X := dprod_cup X.

 Program Definition dprod_csup (X: A -> CPO.type) :=
   PO_csup.Build (forall a, X a) (fun F DF a => csup (image (app a) F) (chain_image _ DF)) _.
 Next Obligation. apply: dprod_sup=>a. exact: csup_spec. Qed.
 HB.instance Definition _ X := dprod_csup X. 

 Program Definition dprod_dsup (X: A -> dCPO.type) :=
   PO_dsup.Build (forall a, X a) (fun F DF a => dsup (image (app a) F) (directed_image _ DF)) _.
 Next Obligation. apply: dprod_sup=>a. exact: dsup_spec. Qed.
 HB.instance Definition _ X := dprod_dsup X. 

 Program Definition dprod_isup (X: A -> supCL.type) :=
   PO_isup.Build (forall a, X a) (fun I P F a => isup I P (app a ∘ F)) _. 
 Next Obligation. apply: dprod_sup=>a. rewrite -image_comp. exact: isup_spec. Qed.
 HB.instance Definition _ X := dprod_isup X. 
 
End dprod.
End DIRECT_DPROD.


(** ** link between generic and standard operations *)

(** *** bottom elements as generic sups over empty domains *)
Definition empty_kind: gkind := fun X _ => X -> False.
Definition False_empty_kind: empty_kind False empty.
Proof. done. Defined.
Lemma image_empty_kind I P (H: empty_kind I P) X (f: I -> X): image f P ≡ empty.
Proof. split=>//[[? _]]. exact: H. Qed. 
HB.factory Record PO_gbot X of gsupPO empty_kind X := {}.
HB.builders Context X of PO_gbot X.
 Section s.
  Definition bot: X := gsup False empty False_empty_kind empty_fun.
  Lemma bot_spec: is_sup empty bot.
  Proof.
    rewrite -(image_empty_kind False_empty_kind empty_fun).
    exact: gsup_spec.
  Qed.
 End s.
 HB.instance Definition _ := PO_bot.Build X bot_spec.
HB.end.
Definition bot_gen (X: Type) := X.
HB.instance Definition _ (X: PO.type) := PO.on (bot_gen X).
Section s.
 Context {X: botPO.type}.
 Section t. 
  Variables (I: PO.type) (P: I -> Prop) (H: empty_kind I P) (h: I -mon-> X). 
  Lemma bot_gsup_spec: is_sup (image h P) bot.
  Proof. rewrite (image_empty_kind H). exact: bot_spec. Qed.
 End t.
 Definition __bot_gen := PO_gsup.Build empty_kind X _ bot_gsup_spec.
 HB.instance Definition _bot_gen := PO_gsup.Build empty_kind (bot_gen X) _ bot_gsup_spec.
End s.
Notation "[gbot_for X ]" := (HB.pack_for (gsupPO.type empty_kind) X (@__bot_gen X)) (only parsing).
Lemma bot_gsup_closed {X: botPO.type} (P: X -> Prop) (Pbot: P bot): @gsup_closed empty_kind (bot_gen X) P.
Proof. done. Qed.
HB.factory Record comonadic_bot Y of PO Y := { X: botPO.type; f: X ⊣· Y; }.
HB.builders Context Y of comonadic_bot Y.
 HB.instance Definition _ := comonadic_gsup.Build empty_kind Y (X:=bot_gen X) f.
 HB.instance Definition _ := PO_gbot.Build Y.
HB.end.


(** *** binary joins as generic sups over 2-element domains *)
Record pair_kind (X: PO.type) (P: X -> Prop): Type :=
  indeed_pair { elem1; elem2; Pelem1: P elem1; Pelem2: P elem2;
                all_there: forall z: X, z=elem1 \/ z=elem2 }.
Definition bool_pair_kind: pair_kind (discrete bool) full.
Proof. exists false true=>//. by case; auto. Defined.
Lemma image_pair_kind I P (H: pair_kind I P) X (f: I -> X): image f P ≡ pair (f (elem1 H)) (f (elem2 H)).
Proof.
  split.
  - move=>[i [Pi ->]]. rewrite /pair; case: (all_there H i)=>->; auto.
  - move=>[->|->]; apply: in_image; apply H.
Qed. 
HB.factory Record PO_gcup X of gsupPO pair_kind X := {}.
HB.builders Context X of PO_gcup X.
 Section s.
  Variables x y: X.
  Definition cup := gsup (discrete bool) full bool_pair_kind (@discretemon (discrete bool) X (bool_fun x y)).
  Lemma cup_spec: is_sup (pair x y) cup.
  Proof.
    rewrite -(image_pair_kind bool_pair_kind (bool_fun x y)).
    exact: gsup_spec.
  Qed.
 End s.
 HB.instance Definition _ := PO_cup.Build X _ cup_spec.
HB.end.
Definition cup_gen (X: Type) := X.
HB.instance Definition _ (X: PO.type) := PO.on (cup_gen X).
Section s.
 Context {X: joinSemiLattice.type}.
 Section t. 
  Variables (I: PO.type) (P: I -> Prop) (H: pair_kind I P) (h: I -mon-> X). 
  Definition cup_gsup: X := cup (h (elem1 H)) (h (elem2 H)).
  Lemma cup_gsup_spec: is_sup (image h P) cup_gsup.
  Proof. rewrite image_pair_kind. exact: cup_spec. Qed.
 End t.
 HB.instance Definition _ := PO_gsup.Build pair_kind (cup_gen X) _ cup_gsup_spec. 
End s.
Lemma cup_gsup_closed {X: joinSemiLattice.type} (P: X -> Prop) (Pcup: forall x y, P x -> P y -> P (cup x y)):
  @gsup_closed pair_kind (cup_gen X) P.
Proof. move=>I Q kIQ h /forall_image H. apply: Pcup; apply: H; apply kIQ. Qed.
HB.factory Record comonadic_cup Y of PO Y := { X: joinSemiLattice.type; f: X ⊣· Y; }.
HB.builders Context Y of comonadic_cup Y.
 HB.instance Definition _ := comonadic_gsup.Build pair_kind Y (X:=cup_gen X) f.
 HB.instance Definition _ := PO_gcup.Build Y.
HB.end.

(** *** chain sups as generic sups over chain domains *)
HB.factory Record PO_gcsup X of gsupPO (@chain) X := {}.
HB.builders Context X of PO_gcsup X.
 Section s.
  Variables (P: X -> Prop) (D: chain P). 
  Definition csup := gsup X P D types_id.
  Lemma csup_spec: is_sup P csup.
  Proof. move: (gsup_spec X P D types_id). by rewrite image_id. Qed.
 End s.
 HB.instance Definition _ := PO_csup.Build X _ csup_spec.
HB.end.
Definition csup_gen (X: Type) := X.
HB.instance Definition _ (X: PO.type) := PO.on (csup_gen X).
Section s.
 Context {X: CPO.type}.
 Section t. 
  Variables (I: PO.type) (P: I -> Prop) (D: (@chain) I P) (h: I -mon-> X). 
  Definition csup_gsup: X := csup (image h P) (chain_image _ D).
  Lemma csup_gsup_spec: is_sup (image h P) csup_gsup.
  Proof. exact: csup_spec. Qed.
 End t.
 HB.instance Definition _ := PO_gsup.Build (@chain) (csup_gen X) _ csup_gsup_spec. 
End s.
Lemma csup_gsup_closed {X: CPO.type} (P: X -> Prop) (Pcsup: forall Q (C: chain Q), Q <= P -> P (csup Q C)):
  @gsup_closed (@chain) (csup_gen X) P.
Proof. move=>I Q kIQ h H. exact: Pcsup. Qed.
HB.factory Record comonadic_csup Y of PO Y := { X: CPO.type; f: X ⊣· Y; }.
HB.builders Context Y of comonadic_csup Y.
 HB.instance Definition _ := comonadic_gsup.Build (@chain) Y (X:=csup_gen X) f.
 HB.instance Definition _ := PO_gcsup.Build Y.
HB.end.

(** *** directed sups as generic sups over directed domains *)
HB.factory Record PO_gdsup X of gsupPO (@directed) X := {}.
HB.builders Context X of PO_gdsup X.
 Section s.
  Variables (P: X -> Prop) (D: directed P). 
  Definition dsup := gsup X P D types_id.
  Lemma dsup_spec: is_sup P dsup.
  Proof. move: (gsup_spec X P D types_id). by rewrite image_id. Qed.
 End s.
 HB.instance Definition _ := PO_dsup.Build X _ dsup_spec.
HB.end.
Definition dsup_gen (X: Type) := X.
HB.instance Definition _ (X: PO.type) := PO.on (dsup_gen X).
Section s.
 Context {X: dCPO.type}.
 Section t. 
  Variables (I: PO.type) (P: I -> Prop) (D: (@directed) I P) (h: I -mon-> X). 
  Definition dsup_gsup: X := dsup (image h P) (directed_image _ D).
  Lemma dsup_gsup_spec: is_sup (image h P) dsup_gsup.
  Proof. exact: dsup_spec. Qed.
 End t.
 HB.instance Definition _ := PO_gsup.Build (@directed) (dsup_gen X) _ dsup_gsup_spec. 
End s.
Lemma dsup_gsup_closed {X: dCPO.type} (P: X -> Prop) (Pdsup: forall Q (D: directed Q), Q <= P -> P (dsup Q D)):
  @gsup_closed (@directed) (dsup_gen X) P.
Proof. move=>I Q kIQ h H. exact: Pdsup. Qed.
HB.factory Record comonadic_dsup Y of PO Y := { X: dCPO.type; f: X ⊣· Y; }.
HB.builders Context Y of comonadic_dsup Y.
 HB.instance Definition _ := comonadic_gsup.Build (@directed) Y (X:=dsup_gen X) f.
 HB.instance Definition _ := PO_gdsup.Build Y.
HB.end.

(** *** indexed arbitrary sups as generic sups of arbitrary kind *)
Definition any_kind: gkind := fun _ _ => True.
HB.factory Record PO_gisup X of gsupPO any_kind X := {}.
HB.builders Context X of PO_gisup X.
 Section s.
  Variables (I: Type) (P: I -> Prop) (h: I -> X). 
  Definition isup :=
    gsup (discrete (strict I)) P Logic.I
      (@mk_mon (discrete (strict I)) X h _).
  Lemma isup_spec: is_sup (image h P) isup.
  Proof. exact: gsup_spec. Qed.
 End s.
 HB.instance Definition _ := PO_isup.Build X _ isup_spec.
HB.end.
Definition isup_gen (X: Type) := X.
HB.instance Definition _ (X: PO.type) := PO.on (isup_gen X).
Section s.
 Context {X: supCL.type}.
 Section t. 
  Variables (I: PO.type) (P: I -> Prop) (kIP: any_kind I P) (h: I -mon-> X). 
  Definition isup_gsup: X := let _ := kIP in isup I P h.
  Lemma isup_gsup_spec: is_sup (image h P) isup_gsup.
  Proof. exact: isup_spec. Qed.
 End t.
 HB.instance Definition _ := PO_gsup.Build any_kind (isup_gen X) _ isup_gsup_spec. 
End s.
Lemma isup_gsup_closed {X: supCL.type} (P: X -> Prop) (Pisup: forall I Q h, image h Q <= P -> P (isup I Q h)):
  @gsup_closed any_kind (isup_gen X) P.
Proof. move=>I Q kIQ h H; exact: Pisup. Qed.
HB.factory Record comonadic_isup Y of PO Y := { X: supCL.type; f: X ⊣· Y; }.
HB.builders Context Y of comonadic_isup Y.
 HB.instance Definition _ := comonadic_gsup.Build any_kind Y (X:=isup_gen X) f.
 HB.instance Definition _ := PO_gisup.Build Y.
HB.end.

(* TODO: below, we should to avoid that *_gen decorations escape instance definitions.
   we could use HB.pack (cf [gbot_for X] notation above, but a bug makes it painful:
   we have to first make a definition and then HB.instance it, otherwise we get
   Error: Not Yet Implemented: (glob)HOAS for GGenarg
 *)
Fail HB.instance Definition _ I (X: I -> botPO.type) := PO_gbot.Build (forall i, [gbot_for X i]).

(** liftings to dependent products [forall i, X i] follow generically *)
HB.instance Definition _ I (X: I -> botPO.type) := PO_gbot.Build (forall i, bot_gen (X i)).
HB.instance Definition _ I (X: I -> joinSemiLattice.type) := PO_gcup.Build (forall i, cup_gen (X i)). 
HB.instance Definition _ I (X: I -> CPO.type) := PO_gcsup.Build (forall i, csup_gen (X i)). 
HB.instance Definition _ I (X: I -> dCPO.type) := PO_gdsup.Build (forall i, dsup_gen (X i)). 
HB.instance Definition _ I (X: I -> supCL.type) := PO_gisup.Build (forall i, isup_gen (X i)). 

(** restriction to extensive functions follow generically *)
HB.instance Definition _ (X: Setoid.type) (Y: botPO.type) := PO_gbot.Build (X -eqv-> bot_gen Y). 
HB.instance Definition _ (X: Setoid.type) (Y: joinSemiLattice.type) := PO_gcup.Build (X -eqv-> cup_gen Y). 
HB.instance Definition _ (X: Setoid.type) (Y: CPO.type) := PO_gcsup.Build (X -eqv-> csup_gen Y). 
HB.instance Definition _ (X: Setoid.type) (Y: dCPO.type) := PO_gdsup.Build (X -eqv-> dsup_gen Y). 
HB.instance Definition _ (X: Setoid.type) (Y: supCL.type) := PO_gisup.Build (X -eqv-> isup_gen Y). 

(** restriction to monotone functions follow generically *)
HB.instance Definition _ (X: PO.type) (Y: botPO.type) := PO_gbot.Build (X -mon-> bot_gen Y). 
HB.instance Definition _ (X: PO.type) (Y: joinSemiLattice.type) := PO_gcup.Build (X -mon-> cup_gen Y). 
HB.instance Definition _ (X: PO.type) (Y: CPO.type) := PO_gcsup.Build (X -mon-> csup_gen Y). 
HB.instance Definition _ (X: PO.type) (Y: dCPO.type) := PO_gdsup.Build (X -mon-> dsup_gen Y). 
HB.instance Definition _ (X: PO.type) (Y: supCL.type) := PO_gisup.Build (X -mon-> isup_gen Y). 


(* Check ((nat->bool)-mon->(nat->Prop)): supCL.type. *)
