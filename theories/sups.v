From Stdlib Require Eqdep_dec.
Require Export adjunction.

(** * suprema in partial orders *)

(** ** general properties of suprema *)

Section s.

Context {X: PO.type}.
Implicit Types x y z: X. 
Implicit Types P Q: X -> Prop.

Lemma geq_is_sup P x: is_sup P x -> forall z, (forall y, P y -> y <= z) -> x <= z.
Proof. by move=>H z Hz; apply H. Qed.

Lemma leq_is_sup P x: is_sup P x -> forall y, P y -> y <= x.
Proof. move=>H y Py. by apply H. Qed.

Lemma is_sup_leq P p Q q: is_sup P p -> is_sup Q q -> covered P Q -> p<=q.
Proof.
  move=>Pp Qq PQ. apply Pp=>x Px/=.
  case: (PQ x Px)=>y [Qy ->]. by apply Qq.
Qed.

Lemma is_sup_eqv P p Q q: is_sup P p -> is_sup Q q -> bicovered P Q -> p≡q.
Proof. rewrite eqv_of_leq=>??[??]. eauto using is_sup_leq. Qed.

Lemma is_sup_unique (P: X -> Prop) x y: is_sup P x -> is_sup P y -> x ≡ y.
Proof. intros; eapply is_sup_eqv; eauto. Qed.

Lemma is_sup_eq x: is_sup (eq x) x.
Proof. move=>/=. rewrite /upper_bound. by firstorder subst. Qed.

#[export] Instance Proper_is_sup: Proper (bicovered ==> eqv ==> iff) (@is_sup X).
Proof.
  rewrite /is_sup=> P Q PQ x y xy.
  apply Proper_forall=>z. apply Proper_iff. by rewrite xy.
  have E: forall P Q, covered P Q -> (forall t, Q t -> t <= z) <= (forall t, P t -> t <= z).
   clear=>P Q PQ H t Pt. by case: (PQ _ Pt)=>s [? ->]; apply H. 
  split; apply E; apply PQ. 
Qed.

Lemma sup_closed_impl (P Q: X -> Prop): Proper (leq --> leq) P -> sup_closed Q -> sup_closed (fun x => P x -> Q x).
Proof.
  intros HP HQ T TPQ x Tx Px.
  apply: HQ. 2: apply Tx.
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
  move: (is_sup_eq x). by apply Proper_is_sup. 
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
  - elim: Px=>//Q QP IH y Hy. apply Hy. exact: IH.
Qed.


#[export] Instance sup_closure_set P: Proper (eqv ==> eqv) (sup_closure P).
Proof. apply: sup_closed_Proper. exact/sc_sup. Qed.
HB.instance Definition _ P := isExtensional.Build _ _ (sup_closure P) (sup_closure_set P).

Lemma is_sup_empty z: is_sup empty z <-> forall t, z <= t.
Proof.
  rewrite /is_sup. setoid_rewrite upper_bound_empty.
  firstorder.
Qed.

Lemma is_sup_single x y: is_sup (single x) y ≡ (x ≡ y).
Proof.
  rewrite /is_sup. setoid_rewrite upper_bound_single.
  split. symmetry. exact/from_above.
  move=>e?. by rewrite e.
Qed.

Lemma is_sup_pair x y z:
  is_sup (pair x y) z <-> forall t, z <= t <-> x <= t /\ y <= t.
Proof. rewrite /is_sup. by setoid_rewrite upper_bound_pair. Qed.

Lemma is_sup_image {A} (f: A -> X) (P: A -> Prop) z:
  is_sup (image f P) z <-> forall t, z <= t <-> forall a, P a -> f a <= t.
Proof. rewrite /is_sup. by setoid_rewrite upper_bound_image. Qed.

End s.

(** sups can be computed pointwise in function spaces *)
Lemma dprod_sup {A} {X: A -> PO.type} (P: (forall a, X a) -> Prop) (f: forall a, X a):
  (forall a: A, is_sup (image (app a) P) (f a)) -> is_sup P f.
Proof.
  move=>H g; split=>fg.
  - move=>h Ph. rewrite -fg=>a. apply H=>//. by exists h.
  - move=>a. apply H=>_ [h [Ph ->]]. by apply: fg. 
Qed.
(** sups being unique, they *must* be computed pointwise if they can
    (i.e., when there are enough sups in X) *)
Lemma dprod_sup' {A} {X: A -> PO.type} (P: (forall a, X a) -> Prop) (f g: forall a, X a):
  (forall a: A, is_sup (image (app a) P) (f a)) -> 
  is_sup P g -> forall a: A, is_sup (image (app a) P) (g a).
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
  is_sup P f -> forall a: A, is_sup (image (app a) P) (f a).
Proof.
  move=>Pf a z. split=>az.
  - move=>_ [b [Pb ->]]. rewrite -az. by apply: (leq_is_sup Pf).
  - set h := fun b =>
               match A_dec a b return X b with
               | left E => match E in _=c return X c with
                          | eq_refl => z
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
  -- move=>c Pc. rewrite -ab. by apply H, in_image. 
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
    f: Y ⊢· X;
  }.
HB.builders Context k Y of comonadic_gsup k Y.
 Definition gsup I P kIP (h: I -mon-> Y): Y :=
   ladj f (@gsup k X I P kIP (f ∘ h)).
 Lemma gsup_spec I P kIP (h: I -mon-> Y):
   is_sup (image h P) (@gsup I P kIP h).
 Proof. apply: comonadic_sup. rewrite -image_comp. exact: gsup_spec. Qed.
 HB.instance Definition _ := PO_gsup.Build k Y (@gsup) (@gsup_spec).
HB.end.

(** sups on sub-spaces *)
Section sub.
 Context {k} {X: gsupPO.type k}.
 (* TOTHINK: restrict to [P: set X] ? *)
 Definition gsup_closed (P: X -> Prop) := forall I Q (kIQ: k I Q) (h: I -mon-> X), Q <= P ∘ h -> P (gsup I Q kIQ h). 
 Lemma sup_gsup_closed: sup_closed <= gsup_closed. 
 Proof.
   move=>P HP. move: (sup_closed_Proper HP)=>HP' I Q kIQ h hQP.
   apply: HP. 2: exact: gsup_spec. by apply (image_adj h _ (mk_set HP')).
 Qed.
 #[export] Instance gsup_closed_eqv: Proper (eqv==>eqv) gsup_closed.
 Proof.
   apply/Proper_eqv_leq=>P P' PP' HP I Q kIQ h hQP'.
   apply/PP'. apply: HP. rewrite hQP'. apply: eqv_geq=>i. exact/PP'.
 Qed. 
 
 Definition sup_closed_sig P (HP: gsup_closed P) := sig P.
 Variables (P: X -> Prop) (HP: gsup_closed P). 
 Program Definition sig_gsup I Q (kIQ: k I Q) (h: I -mon-> sig P): sig P :=
   exist P (gsup I Q kIQ (sval ∘ h)) _.
 Next Obligation. apply: HP=>i Qi/=. exact: proj2_sig. Qed.
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
   - move=>? [g [[i [Qi E]] ->]]. eexists; split. exists i; split=>//. by rewrite /app/= (E x).
   - move=>? [i [Qi ->]].
     have E: Proper (leq ==> leq) (h i) by apply: hQ. 
     eexists; split. exists (mk_mon _ E); split=>//. exists i; split=>//. reflexivity.
   (* direct proof *)
   Restart.
   move=>I Q kIQ h hQ x y xy.
   rewrite gsup_spec=>z [i [Qi ->]].
   transitivity (h i y).
     have E: Proper (leq ==> leq) (h i) by apply: hQ. 
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
  rewrite adj 2!gsup_spec 2!upper_bound_image.
  apply: forall_iff=>i.
  by rewrite -adj.
Qed.

(** ** standard supremum operations *)

(** *** bottom element *)
HB.mixin Record PO_bot X of PO X := {
    #[canonical=no] bot: X;
    #[canonical=no] bot_sup_spec: is_sup empty bot;
  }.
HB.structure Definition botPO := {X of PO_bot X & }.

(** *** binary joins *)
HB.mixin Record PO_cup X of PO X := {
    #[canonical=no] cup: X -> X -> X;
    #[canonical=no] cup_sup_spec: forall x y: X, is_sup (pair x y) (cup x y);
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
    #[canonical=no] isup_sup_spec: forall I P (h: I -> X), is_sup (image h P) (isup I P h);
  }.
HB.builders Context X of PO_isup X.
  Definition sup (P: X -> Prop) := isup P types_id.
  Lemma sup_spec (P: X -> Prop): is_sup P (sup P).
  Proof. move: (isup_sup_spec P types_id)=>/=. by rewrite image_id'. Qed.
  HB.instance Definition _ := PO_cup.Build X _ (fun x y => sup_spec (pair x y)).
  HB.instance Definition _ := PO_dsup.Build X _ (fun D _ => sup_spec D).
HB.end.
HB.structure Definition supCL := {X of PO_isup X & }.
Arguments isup {_ _}. 


(** ** theory *)

Notation sup P := (isup P types_id).
Lemma sup_spec (X: supCL.type) (P: X -> Prop): is_sup P (sup P).
Proof. move: (isup_sup_spec X P types_id). by rewrite image_id'. Qed.

Section bot.
Context {X: botPO.type}.
Implicit Types x y z: X.  
Lemma bot_spec z: bot <= z <-> True.
Proof. by rewrite bot_sup_spec/upper_bound/=. Qed.
Lemma geq_bot z: bot <= z.
Proof. by rewrite bot_spec. Qed.
Lemma leq_bot z: z <= bot -> z ≡ bot. (* iff, reversed? *)
Proof. move=>H. apply: antisym=>//. apply: geq_bot. Qed.
End bot.
#[export] Hint Immediate geq_bot: lattice.
Lemma adj_bot {X Y: botPO.type} (f: X ⊣ Y): f bot ≡ bot. 
Proof.
  apply: from_above=>y.
  by rewrite adj 2!bot_spec.
Qed.

Section cup.
Context {X: joinSemiLattice.type}.
Implicit Types x y z: X.  
Lemma cup_spec x y z: cup x y <= z <-> x <= z /\ y <= z.
Proof. by rewrite cup_sup_spec upper_bound_pair. Qed.
Lemma geq_cup x y z: x <= z -> y <= z -> cup x y <= z.
Proof. move=>xz yz. by rewrite cup_spec. Qed.
Lemma leq_cup_l x y z: z <= x -> z <= cup x y.
Proof. move=>->. apply/leq_is_sup. exact: cup_sup_spec. by left. Qed.
Lemma leq_cup_r x y z: z <= y -> z <= cup x y.
Proof. move=>->. apply/leq_is_sup. exact: cup_sup_spec. by right. Qed.
Lemma cup_l x y: x <= cup x y.
Proof. exact: leq_cup_l. Qed.
Lemma cup_r x y: y <= cup x y.
Proof. exact: leq_cup_r. Qed.
#[export] Instance cup_leq: Proper (leq ==> leq ==> leq) (@cup X).
Proof. intros x x' xx y y' yy. by rewrite cup_spec xx yy -cup_spec. Qed.
#[export] Instance cup_eqv: Proper (eqv ==> eqv ==> eqv) (@cup X) := op_leq_eqv_2.
Lemma cupA x y z: cup x (cup y z) ≡ cup (cup x y) z.
Proof. apply: from_above=>t. rewrite 4!cup_spec. tauto. Qed.
Lemma cupC x y: cup x y ≡ cup y x.
Proof. apply: from_above=>t. rewrite 2!cup_spec. tauto. Qed.
Lemma cupI x: cup x x ≡ x.
Proof. apply: from_above=>t. rewrite cup_spec. tauto. Qed.
Lemma leq_of_cup x y: x <= y <-> cup x y ≡ y.
Proof.
  split=>H. apply: antisym.
  - by rewrite H cupI.
  - exact: leq_cup_r.
  - rewrite -H. exact: leq_cup_l.
Qed.
Lemma directed_sup_closure (P: X -> Prop): directed (sup_closure P).
Proof.
  move=>x y Px Py. exists (cup x y). split.
  - apply: sc_sup. 2: exact: cup_sup_spec. by move=>t [<-|<-].
  - exact/cup_spec.
Qed.
End cup.
#[export] Hint Resolve leq_cup_l leq_cup_r: lattice.
Lemma adj_cup {X Y: joinSemiLattice.type} (f: X ⊣ Y) (x y: X): f (cup x y) ≡ cup (f x) (f y). 
Proof.
  apply: from_above=>z.
  by rewrite adj 2!cup_spec -2!adj.
Qed.

Section bcup.
Context {X: botjoinSemiLattice.type}.
Implicit Types x y z: X.  
Lemma cupbx x: cup bot x ≡ x.
Proof. apply: from_above=>z. rewrite cup_spec bot_spec. tauto. Qed.
Lemma cupxb x: cup x bot ≡ x.
Proof. by rewrite cupC cupbx. Qed.
End bcup.

Section cpo.
Context {X: CPO.type}.
Implicit Types x y z: X.  
Lemma geq_csup (P: X -> Prop) C z: (forall x, P x -> x <= z) -> csup P C <= z.
Proof. apply geq_is_sup, csup_spec. Qed.
Lemma leq_csup (P: X -> Prop) C: forall z, P z -> z <= csup P C.
Proof. apply leq_is_sup, csup_spec. Qed.
Lemma csup_leq (P Q: X -> Prop) CP CQ: covered P Q -> csup P CP <= csup Q CQ.
Proof. apply: is_sup_leq; exact: csup_spec. Qed.
Lemma csup_eqv (P Q: X -> Prop) CP CQ: bicovered P Q -> csup P CP ≡ csup Q CQ.
Proof. apply: is_sup_eqv; exact: csup_spec. Qed.
End cpo.
Lemma adj_csup {X Y: CPO.type} (f: X ⊣ Y) (P: X -> Prop) C: f (csup P C) ≡ csup (image f P) (chain_image f C). 
Proof.
  apply: from_above=>y.
  rewrite adj 2!csup_spec upper_bound_image.
  apply: forall_iff=>x.
  by rewrite -adj.
Qed.

Section dcpo.
Context {X: dCPO.type}.
Implicit Types x y z: X.  
Lemma geq_dsup (P: X -> Prop) D z: (forall y, P y -> y <= z) -> dsup P D <= z.
Proof. apply geq_is_sup, dsup_spec. Qed.
Lemma leq_dsup (P: X -> Prop) D: forall z, P z -> z <= dsup P D.
Proof. apply leq_is_sup, dsup_spec. Qed.
Lemma dsup_leq (P Q: X -> Prop) DP DQ: covered P Q -> dsup P DP <= dsup Q DQ.
Proof. apply: is_sup_leq; exact: dsup_spec. Qed.
Lemma dsup_eqv (P Q: X -> Prop) CP CQ: bicovered P Q -> dsup P CP ≡ dsup Q CQ.
Proof. apply: is_sup_eqv; exact: dsup_spec. Qed.
End dcpo.
Lemma adj_dsup {X Y: dCPO.type} (f: X ⊣ Y) (P: X -> Prop) D: f (dsup P D) ≡ dsup (image f P) (directed_image f D). 
Proof.
  apply: from_above=>y.
  rewrite adj 2!dsup_spec upper_bound_image.
  apply: forall_iff=>x.
  by rewrite -adj.
Qed.

Section isup.
Context {X: supCL.type}.
Implicit Types x y z: X.  
Lemma isup_spec I (P: I -> Prop) (h: I -> X) z: isup P h <= z <-> forall i, P i -> h i <= z.
Proof. by rewrite isup_sup_spec upper_bound_image. Qed.
Lemma geq_isup I (P: I -> Prop) (h: I -> X) (z: X): (forall i, P i -> h i <= z) -> isup P h <= z.
Proof. move=>H. by rewrite isup_spec. Qed.
Lemma leq_isup I (P: I -> Prop) (h: I -> X) i: P i -> h i <= isup P h.
Proof. move=>Pi. eapply isup_spec; eauto. Qed.
#[export] Instance isup_leq {I}: Proper (leq ==> leq ==> leq) (@isup X I).
Proof.
  move=>P Q pq h k hk. apply: is_sup_leq.
  1,2: exact: isup_sup_spec.
  exact: covered_image. 
Qed.
#[export] Instance isup_eqv {I}: Proper (eqv ==> eqv ==> eqv) (@isup X I) := op_leq_eqv_2.

Lemma geq_sup (P: X -> Prop) z: (forall y, P y -> y <= z) -> sup P <= z.
Proof. exact: geq_isup. Qed.
Lemma leq_sup (P: X -> Prop): forall z, P z -> z <= sup P.
Proof. exact: leq_isup. Qed.
Lemma sup_leq: Proper (leq ==> leq) (@isup X X^~ id).
Proof. move=>P Q pq. exact: isup_leq. Qed.
Lemma sup_eqv: Proper (eqv ==> eqv) (@isup X X^~ id).
Proof. move=>P Q pq. exact: isup_eqv. Qed.
End isup.
Lemma adj_isup {X Y: supCL.type} (f: X ⊣ Y) I (P: I -> Prop) h:
  f (isup P h) ≡ isup P (f ∘ h). 
Proof.
  apply: from_above=>y.
  rewrite adj 2!isup_spec/=. 
  apply: forall_iff=>i.
  by rewrite -adj. 
Qed.
Lemma adj_sup {X Y: supCL.type} (f: X ⊣ Y) P:
  f (sup P) ≡ isup P f. 
Proof. exact: adj_isup. Qed.

(** ** concrete instances *)

Lemma Prop_bot_spec: is_sup empty False.
Proof. cbv; tauto. Qed. 
Lemma Prop_cup_spec (P Q: Prop): is_sup (pair P Q) (P \/ Q).
Proof. rewrite is_sup_pair. cbv; tauto. Qed. 
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
   apply: dprod_sup=>a. rewrite image_empty. exact: bot_sup_spec.
 Qed.
 HB.instance Definition _ X := dprod_bot X.

 Program Definition dprod_cup (X: A -> joinSemiLattice.type) :=
   PO_cup.Build (forall a, X a) (fun f g a => cup (f a) (g a)) _. 
 Next Obligation.
   apply: dprod_sup=>a. rewrite image_pair. exact: cup_sup_spec.
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
   PO_isup.Build (forall a, X a) (fun I P F a => isup P (app a ∘ F)) _. 
 Next Obligation. apply: dprod_sup=>a. rewrite -image_comp. exact: isup_sup_spec. Qed.
 HB.instance Definition _ X := dprod_isup X. 
 
End dprod.
End DIRECT_DPROD.


(** ** link between generic and standard operations *)

(** *** bottom elements as generic sups over empty domains *)
Definition empty_kind: gkind := fun X _ => X -> False.
Definition False_empty_kind: empty_kind False empty.
Proof. done. Defined.
Lemma image_empty_kind I P (H: empty_kind I P) {X: Setoid.type} (f: I -> X): image f P ≡ empty.
Proof. split=>//[[? _]]. exact: H. Qed. 

Definition bot_gen (X: Type) := X.
HB.instance Definition _ (X: PO.type) := PO.on (bot_gen X).
Section s.
 Context {X: gsupPO.type empty_kind}.
 Definition gsup_bot: X := gsup False empty False_empty_kind empty_fun. 
 Lemma gsup_bot_spec: is_sup empty gsup_bot.
 Proof.
   rewrite -(image_empty_kind False_empty_kind empty_fun).
   exact: gsup_spec.
 Qed.
 HB.instance Definition _ := PO_bot.Build (bot_gen X) gsup_bot_spec.
End s.
Section s.
 Context {X: botPO.type}.
 Section t. 
  Variables (I: PO.type) (P: I -> Prop) (H: empty_kind I P) (h: I -mon-> X). 
  Lemma bot_gsup_spec: is_sup (image h P) bot.
  Proof. rewrite (image_empty_kind H). exact: bot_sup_spec. Qed.
 End t.
 Definition __bot_gen := PO_gsup.Build empty_kind X _ bot_gsup_spec.
 HB.instance Definition _ := PO_gsup.Build empty_kind (bot_gen X) _ bot_gsup_spec.
End s.
Notation "[gbot_for X ]" := (HB.pack_for (gsupPO.type empty_kind) X (@__bot_gen X)) (only parsing).

Lemma bot_gsup_closed {X: botPO.type} (P: X -> Prop) (Pbot: P bot): @gsup_closed empty_kind (bot_gen X) P.
Proof. done. Qed.

HB.factory Record comonadic_bot Y of PO Y := { X: botPO.type; f: Y ⊢· X }.
HB.builders Context Y of comonadic_bot Y.
 HB.instance Definition _ := comonadic_gsup.Build empty_kind Y (X:=bot_gen X) f.
 HB.instance Definition _ := botPO.copy Y (bot_gen Y).
HB.end.

(** *** binary joins as generic sups over 2-element domains *)
Record pair_kind (X: PO.type) (P: X -> Prop): Type :=
  (* TOTHINK: use setoid pairs? *)
  indeed_pair { elem1; elem2; Pelem1: P elem1; Pelem2: P elem2;
                all_there: forall z: X, z=elem1 \/ z=elem2 }.
Definition bool_pair_kind: pair_kind (discrete bool) full.
Proof. exists false true=>//. by case; auto. Defined.
Lemma image_pair_kind I P (H: pair_kind I P) {X: Setoid.type} (f: I -> X): image f P ≡ pair (f (elem1 H)) (f (elem2 H)).
Proof.
  split.
  - move=>[i [Pi ->]]. rewrite /pair; case: (all_there H i)=>/=->; auto.
  - case=>/=<-; apply: in_image; apply H.
Qed.

Definition cup_gen (X: Type) := X.
HB.instance Definition _ (X: PO.type) := PO.on (cup_gen X).
Section s.
 Context {X: gsupPO.type pair_kind}.
 Section s.
  Variables x y: X.
  Definition gsup_cup := gsup (discrete bool) full bool_pair_kind (@discretemon (discrete bool) X (bool_fun x y)).
  Lemma gsup_cup_spec: is_sup (pair x y) gsup_cup.
  Proof.
    rewrite -(image_pair_kind bool_pair_kind (bool_fun x y)).
    exact: gsup_spec.
  Qed.
 End s.
 HB.instance Definition _ := PO_cup.Build (cup_gen X) _ gsup_cup_spec.
End s.
Section s.
 Context {X: joinSemiLattice.type}.
 Section t. 
  Variables (I: PO.type) (P: I -> Prop) (H: pair_kind I P) (h: I -mon-> X). 
  Definition cup_gsup: X := cup (h (elem1 H)) (h (elem2 H)).
  Lemma cup_gsup_spec: is_sup (image h P) cup_gsup.
  Proof. rewrite image_pair_kind. exact: cup_sup_spec. Qed.
 End t.
 HB.instance Definition _ := PO_gsup.Build pair_kind (cup_gen X) _ cup_gsup_spec. 
End s.

Lemma cup_gsup_closed {X: joinSemiLattice.type} (P: X -> Prop) (Pcup: forall x y, P x -> P y -> P (cup x y)):
  @gsup_closed pair_kind (cup_gen X) P.
Proof. move=>I Q kIQ h H. apply: Pcup; apply: H; apply kIQ. Qed.

HB.factory Record comonadic_cup Y of PO Y := { X: joinSemiLattice.type; f: Y ⊢· X }.
HB.builders Context Y of comonadic_cup Y.
 HB.instance Definition _ := comonadic_gsup.Build pair_kind Y (X:=cup_gen X) f.
 HB.instance Definition _ := joinSemiLattice.copy Y (cup_gen Y).
HB.end.

(** *** chain sups as generic sups over chain domains *)
Definition csup_gen (X: Type) := X.
HB.instance Definition _ (X: PO.type) := PO.on (csup_gen X).
Section s.
 Context {X: gsupPO.type (@chain)}.
 Section s.
  Variables (P: X -> Prop) (D: chain P). 
  Definition gsup_csup := gsup X P D types_id.
  Lemma gsup_csup_spec: is_sup P gsup_csup.
  Proof. move: (gsup_spec X P D types_id). by rewrite image_id'. Qed.
 End s.
 HB.instance Definition _ := PO_csup.Build (csup_gen X) _ gsup_csup_spec.
End s.
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

Lemma csup_gsup_closed {X: CPO.type} (P: X -> Prop) (Pcsup: forall Q (C: chain Q), Q <= saturate P -> P (csup Q C)):
  @gsup_closed (@chain) (csup_gen X) P.
Proof. move=>I Q kIQ h H. apply: Pcsup. exact/image_adj''. Qed.

(** *** directed sups as generic sups over directed domains *)
Definition dsup_gen (X: Type) := X.
HB.instance Definition _ (X: PO.type) := PO.on (dsup_gen X).
Section s.
 Context {X: gsupPO.type (@directed)}.
 Section s.
  Variables (P: X -> Prop) (D: directed P). 
  Definition gsup_dsup := gsup X P D types_id.
  Lemma gsup_dsup_spec: is_sup P gsup_dsup.
  Proof. move: (gsup_spec X P D types_id). by rewrite image_id'. Qed.
 End s.
 HB.instance Definition _ := PO_dsup.Build (dsup_gen X) _ gsup_dsup_spec.
End s.
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

Lemma dsup_gsup_closed {X: dCPO.type} (P: X -> Prop) (Pdsup: forall Q (D: directed Q), Q <= saturate P -> P (dsup Q D)):
  @gsup_closed (@directed) (dsup_gen X) P.
Proof. move=>I Q kIQ h H. apply: Pdsup. exact/image_adj''. Qed.

(** *** indexed arbitrary sups as generic sups of arbitrary kind *)
Definition any_kind: gkind := fun _ _ => True.

Definition isup_gen (X: Type) := X.
HB.instance Definition _ (X: PO.type) := PO.on (isup_gen X).
Section s.
 Context {X: gsupPO.type any_kind}.
 Section s.
  Variables (I: Type) (P: I -> Prop) (h: I -> X). 
  Definition gsup_isup :=
    gsup (discrete (strict I)) P Logic.I
      (@mk_mon (discrete (strict I)) X h _).
  Lemma gsup_isup_spec: is_sup (image h P) gsup_isup.
  Proof. exact: gsup_spec. Qed.
 End s.
 HB.instance Definition _ := PO_isup.Build (isup_gen X) _ gsup_isup_spec.
End s.
Section s.
 Context {X: supCL.type}.
 Section t. 
  Variables (I: PO.type) (P: I -> Prop) (kIP: any_kind I P) (h: I -mon-> X). 
  Definition isup_gsup: X := let _ := kIP in isup P h.
  Lemma isup_gsup_spec: is_sup (image h P) isup_gsup.
  Proof. exact: isup_sup_spec. Qed.
 End t.
 HB.instance Definition _ := PO_gsup.Build any_kind (isup_gen X) _ isup_gsup_spec. 
End s.

Lemma isup_gsup_closed {X: supCL.type} (P: X -> Prop) (Pisup: forall I (Q: I -> Prop) h, image h Q <= saturate P -> P (isup Q h)):
  @gsup_closed any_kind (isup_gen X) P.
Proof. move=>I Q kIQ h H; apply: Pisup. exact/image_adj''. Qed.

(** liftings to dependent products [forall i, X i] follow generically *)
(* HB.instance Definition _ I (X: I -> botPO.type) := botPO.copy (forall i, X i) (bot_gen (forall i, [gbot_for (X i)])). *)
HB.instance Definition _ I (X: I -> botPO.type) := botPO.copy (forall i, X i) (bot_gen (forall i, bot_gen (X i))).
HB.instance Definition _ I (X: I -> joinSemiLattice.type) := joinSemiLattice.copy (forall i, X i) (cup_gen (forall i, cup_gen (X i))).
HB.instance Definition _ I (X: I -> CPO.type) := CPO.copy (forall i, X i) (csup_gen (forall i, csup_gen (X i))).
HB.instance Definition _ I (X: I -> dCPO.type) := dCPO.copy (forall i, X i) (dsup_gen (forall i, dsup_gen (X i))).
HB.instance Definition _ I (X: I -> supCL.type) := supCL.copy (forall i, X i) (isup_gen (forall i, isup_gen (X i))).

(** restriction to extensive functions follow generically *)
HB.instance Definition _ (X: Setoid.type) (Y: botPO.type) := botPO.copy (X -eqv-> Y) (bot_gen (X -eqv-> bot_gen Y)).
HB.instance Definition _ (X: Setoid.type) (Y: joinSemiLattice.type) := joinSemiLattice.copy (X -eqv-> Y) (cup_gen (X -eqv-> cup_gen Y)).
HB.instance Definition _ (X: Setoid.type) (Y: CPO.type) := CPO.copy (X -eqv-> Y) (csup_gen (X -eqv-> csup_gen Y)).
HB.instance Definition _ (X: Setoid.type) (Y: dCPO.type) := dCPO.copy (X -eqv-> Y) (dsup_gen (X -eqv-> dsup_gen Y)).
HB.instance Definition _ (X: Setoid.type) (Y: supCL.type) := supCL.copy (X -eqv-> Y) (isup_gen (X -eqv-> isup_gen Y)).

(** restriction to monotone functions follow generically *)
HB.instance Definition _ (X: PO.type) (Y: botPO.type) := botPO.copy (X -mon-> Y) (bot_gen (X -mon-> bot_gen Y)).
HB.instance Definition _ (X: PO.type) (Y: joinSemiLattice.type) := joinSemiLattice.copy (X -mon-> Y) (cup_gen (X -mon-> cup_gen Y)).
HB.instance Definition _ (X: PO.type) (Y: CPO.type) := CPO.copy (X -mon-> Y) (csup_gen (X -mon-> csup_gen Y)).
HB.instance Definition _ (X: PO.type) (Y: dCPO.type) := dCPO.copy (X -mon-> Y) (dsup_gen (X -mon-> dsup_gen Y)).
HB.instance Definition _ (X: PO.type) (Y: supCL.type) := supCL.copy (X -mon-> Y) (isup_gen (X -mon-> isup_gen Y)).

(** ** additional lemmas using suprema on subsets *)

Lemma image_bot {X} {Y: Setoid.type} (f: X -> Y): image f bot ≡ bot.
Proof. exact: image_empty. Qed.
Lemma image_cup {X} {Y: Setoid.type} (f: X -> Y) (U V: X -> Prop): image f (cup U V) ≡ cup (image f U) (image f V).
Proof. cbv. by firstorder. Qed.
Lemma image_isup {X} {Y: Setoid.type} (f: X -> Y) I P (h: I -> X -> Prop): image f (isup P h) ≡ isup P (fun i => image f (h i)).
Proof. cbv. by firstorder. Qed.
Lemma image_sup {X} {Y: Setoid.type} (f: X -> Y) (P: (X -> Prop) -> Prop): image f (sup P) ≡ isup P (image f).
Proof. exact: image_isup. Qed.

Lemma is_sup_cup {X: joinSemiLattice.type} U V (u v: X):
  is_sup U u -> is_sup V v -> is_sup (cup U V) (cup u v).
Proof. move=>Uu Vv z. rewrite cup_spec Uu Vv. cbn. firstorder. Qed.
