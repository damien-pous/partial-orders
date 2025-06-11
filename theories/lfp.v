From Stdlib Require Classical.
Require Export sups adjunction.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

(** * least fixpoint theorems *)

Section s.
Context {X: PO.type}.
Implicit Types x y z: X.
Implicit Types f g: X -> X.

(** pre-fixpoints *)
Definition is_prefp f x := f x <= x.

(** fixpoints *)
Definition is_fp f x := f x ≡ x.

(** least (pre-)fixpoints *)
Definition is_lfp f := least (is_prefp f). 

Lemma is_lfp_leq f g: f <= g -> forall x y, is_lfp f x -> is_lfp g y -> x <= y.
Proof.
  move=>fg. apply: least_leq.
  rewrite /is_prefp=>x Hx. by rewrite (fg x). 
Qed.

Lemma lfp_unique f: forall x y, is_lfp f x -> is_lfp f y -> x ≡ y.
Proof. exact: least_unique. Qed.

(** second half of Knaster-Tarski theorem on montone functions,
    also known as Lambek lemma in category theory *)
Proposition is_lfp_fixpoint (f: X -mon-> X) x: is_lfp f x -> is_fp f x.
Proof.
  move=>[H H']. apply: antisym'=>//_.
  apply: H'. exact: monotone.
Qed.

(** for monotone functions, pre-fixpoints are closed under infima *)
Lemma inf_closed_prefp (f: X-mon->X): inf_closed (is_prefp f).
Proof.
  move=>P HP z Hz. rewrite /is_prefp Hz=>y Py.
  rewrite -(HP _ Py). apply: monotone. by apply Hz.
Qed.

(** characterisation as the infimum of all pre-fixpoints (again, for monotone functions) *)
Proposition is_lfp_inf (f: X -mon-> X) (z: X): is_lfp f z <-> is_inf (is_prefp f) z.
Proof. apply inf_closed_least_is_inf, inf_closed_prefp. Qed.

End s.

(** partial orders with a least fixpoint operator for monotone functions
    (in fact, equivalent to CPOs)
    later we equip all dCPOs with such a structure
    (as well as all CPOs, using classical logic, cf. [Bourbakiwitt.v]
 *)
HB.mixin Record PO_lfp X of PO X := {
    #[canonical=no] lfp: (X-mon->X) -> X;
    #[canonical=no] lfpE: forall f: X-mon->X, is_lfp f (lfp f);
  }.
HB.structure Definition lfpPO := {X of PO_lfp X &}. 

(** theory of such least fixpoint operators *)

Lemma lfp_pfp {X: lfpPO.type} (f: X -mon-> X): is_prefp f (lfp f).
Proof. apply lfpE. Qed.

Lemma lfp_ind {X: lfpPO.type} (f: X -mon-> X) x: f x <= x -> lfp f <= x.
Proof. apply lfpE. Qed.

Lemma lfp_fixpoint {X: lfpPO.type} (f: X -mon-> X): is_fp f (lfp f).
Proof. apply: is_lfp_fixpoint. exact: lfpE. Qed.

Instance lfp_leq {X}: Proper (leq ==> leq) (@lfp X).
Proof. move=>f g fg. apply: (is_lfp_leq fg); exact: lfpE. Qed.
Instance lfp_eqv {X}: Proper (eqv ==> eqv) (@lfp X) := op_leq_eqv_1.

Lemma geq_mon_lfp {X Y: lfpPO.type} (f: X-mon->Y) (g: X-mon->X) (h: Y-mon->Y) :
  h ∘ f <= f ∘ g -> lfp h <= f (lfp g).
Proof.
  move=>hf. apply: lfp_ind. 
  setoid_rewrite (hf _)=>/=.
  apply: monotone. 
  exact: lfp_pfp.
Qed.

Lemma rolling_lfp {X Y: lfpPO.type} (f: X-mon->Y) (g: Y-mon->X):
  g (lfp (f ∘ g)) ≡ lfp (g ∘ f).
Proof.
  apply: antisym.
  - rewrite -(lfp_fixpoint (g∘f)). apply: monotone. apply: lfp_ind=>/=.
    by rewrite -{2}(lfp_fixpoint (g∘f)).
  - exact: geq_mon_lfp. 
Qed.

Lemma leq_adj_lfp {X Y: lfpPO.type} (f: X ⊣ Y) (g: X-mon->X) (h: Y-mon->Y) :
  f ∘ g <= h ∘ f -> f (lfp g) <= lfp h.
Proof.
  rewrite adj=>fg. apply: lfp_ind.
  rewrite -adj. setoid_rewrite (fg _)=>/=.
  setoid_rewrite (ladj_counit f _).
  exact: lfp_pfp.
Qed.

Lemma adj_lfp {X Y: lfpPO.type} (f: X ⊣ Y) (g: X-mon->X) (h: Y-mon->Y) :
  f ∘ g ≡ h ∘ f -> f (lfp g) ≡ lfp h.
Proof.
  move=>/eqv_of_leq[fg hf]. apply: antisym.
  exact: leq_adj_lfp. exact: geq_mon_lfp. 
Qed.

Lemma exchange_lfp_leq {X Y: lfpPO.type} (f: X ⊣ Y) (g: X-mon->Y) (h: Y-mon->X):
  f ∘ h ∘ g <= g ∘ h ∘ f -> lfp (f ∘ h) <= lfp (g ∘ h).
Proof. move=>H. apply: lfp_ind=>/=. rewrite rolling_lfp. exact: leq_adj_lfp. Qed.
Lemma exchange_lfp_leq' {X Y: lfpPO.type} (f: X ⊣ Y) (g: X-mon->Y) (h: Y-mon->X):
  f ∘ h ∘ g <= g ∘ h ∘ f -> lfp (h ∘ f) <= lfp (h ∘ g).
Proof.
  move=>H. rewrite -(rolling_lfp g h) -(rolling_lfp f h).
  apply: monotone. exact: exchange_lfp_leq.
Qed.
Lemma exchange_lfp_eqv {X Y: lfpPO.type} (f g: X ⊣ Y) (h: Y-mon->X):
  f ∘ h ∘ g ≡ g ∘ h ∘ f -> lfp (f ∘ h) ≡ lfp (g ∘ h).
Proof. move=>/eqv_of_leq[H H']. apply: antisym; exact: exchange_lfp_leq. Qed.
Lemma exchange_lfp_eqv' {X Y: lfpPO.type} (f g: X ⊣ Y) (h: Y-mon->X):
  f ∘ h ∘ g ≡ g ∘ h ∘ f -> lfp (h ∘ f) ≡ lfp (h ∘ g).
Proof. move=>/eqv_of_leq[H H']. apply: antisym; exact: exchange_lfp_leq'. Qed.

 
(** * chain construction *)

Section c.
 Context {X: PO.type}.
 Section d.
 Variable f: X -> X.

 (** the set of all (transfinite) iterations of f *)
 Inductive C: X -> Prop :=
 | Cf: forall x, C x -> C (f x)
 | Csup: sup_closed C.

 (** a type for the elements of the chain *)
 Definition Chain := sig C.
 Definition chn c (Cc: C c): Chain := exist _ c Cc.
 Arguments chn: clear implicits.
 Lemma Celem (c: Chain): C (sval c).
 Proof. exact: proj2_sig. Qed.

 (** the chain is closed under [f] *)
 Definition next (x: Chain) := chn (f (sval x)) (Cf (Celem x)).

 (** the chain is closed under (existing) sups *)
 Lemma Csup' (P: Chain -> Prop) (x: X): is_sup (fun x => exists Cx, P (chn x Cx)) x -> C x.
 Proof. move=>H. by apply: (Csup _ H)=>y [Cy _]. Qed.

 (** the chain is inductively generated *)
 Proposition tower: forall (P: Chain -> Prop), sup_closed P -> (forall x, P x -> P (next x)) -> forall x, P x.
 Proof.
   move=>P Psup Pnext.
   suff H: forall x, C x -> forall Cx, P (chn x Cx). by move=>[??]; apply H.
   induction 1 as [x Cx IH|T TC IH t Ht]=>[Cfx|Ct].
   - move: (Pnext (chn x Cx) (IH _)). by apply sup_closed_Proper.
   - apply (Psup (fun t => T (sval t))).
     -- move=>[x Cx] Tx. by apply IH.
     -- move=>/=[x Cx]. etransitivity. apply Ht.
        split. clear; firstorder.
        move=>H y Ty. by apply (H (chn _ (TC _ Ty))).
 Qed.

 (** the chain is equivalence preserving *)
 #[export] Instance C_eqv: Proper (eqv ==> eqv) C.
 Proof. apply sup_closed_Proper. apply: Csup. Qed.
 (* TODO: strengthen to Proper (eqv ==> eqv ==> eqv) *)
 
 End d.
 Arguments next: clear implicits.

 (** when [f] is eqv-preserving (on [X]), so is [next] (on [Chain f])  *)
 Lemma next_eqv (f: X -eqv-> X): Proper (eqv ==> eqv) (next f).   
 Proof. by move =>???; apply f. Qed.
 Arguments next_eqv: clear implicits.
 HB.instance Definition _ (f: X -eqv-> X) := isExtensional.Build _ _ _ (next_eqv f).
 
 (** when [f] is monotone (on [X]), so is [next] (on [Chain f])  *)
 Section d.
 Variable f: X -mon-> X.
 Lemma next_leq: Proper (leq ==> leq) (next f).   
 Proof. by move =>???; apply f. Qed.
 HB.instance Definition _ := isMonotone.Build _ _ (next f) next_leq.

 (** elements of the chain are post-fixpoints of [f] *)
 Lemma chain_postfixpoint: forall c: Chain f, c <= next f c.
 Proof.
   apply tower. apply: sup_closed_leq. 
   by move=>*; apply f.
 Qed.

 (** they are below all pre-fixpoints of [f] *)
 Theorem chain_below_prefixpoints x: f x <= x -> forall c: Chain f, sval c <= x.
 Proof.
   (* we would like to use [tower], but this requires closure under sups in [Chain f],
      and [sup_closed_leq] does not apply... *)
   move=>Hx []/=.
   induction 1 as [y Cy IH|T TC IH t Ht].
   - by rewrite IH.
   - move: T {TC} IH t Ht. exact: (sup_closed_leq (const x)). 
 Qed.

 (** if the chain contains a pre-fixpoint, then this is the least (pre-)fixpoint *)
 Theorem lfp_of_chain_prefixpoint (c: Chain f): f (sval c) <= sval c -> is_lfp f (sval c).
 Proof.
   move=>Hc. split=>//x H.
   exact: chain_below_prefixpoints.
 Qed.

 (** if the chain has a supremum, then this is the least (pre-)fixpoint *)
 Theorem lfp_of_chain_supremum x: is_sup (C f) x -> is_lfp f x.
 Proof.
   intro Hc.
   have Cc: C f x by eapply Csup.
   apply (@lfp_of_chain_prefixpoint (chn Cc))=>/=. 
   apply Hc=>//. by apply Cf. 
 Qed.

 (** not clear whether the chain always contains the potential least fixpoint 
     - true (classically) in CPOs (cf [BourbakiWitt] below)
     - true (constructively) in dCPOs (cf [Pataraia] below)
  *)
 Fact any_lfp_in_chain: forall x, is_lfp f x -> C f x.
 Abort.
 End d.
End c.
Arguments tower {_}.  
Arguments next {_}.

(** being sup-closed, the chain inherits sups from the starting partial order *)
HB.instance Definition _ k {X: gsupPO.type k} (f: X -> X) :=
  gsupPO.copy (Chain f) (sup_closed_sig (@sup_gsup_closed _ X (C f) (@Csup _ f))).
HB.instance Definition _ {X: botPO.type} (f: X -> X) :=
  botPO.copy (Chain f) (bot_gen (@Chain (bot_gen X) f)). 
HB.instance Definition _ {X: joinSemiLattice.type} (f: X -> X) :=
  joinSemiLattice.copy (Chain f) (cup_gen (@Chain (cup_gen X) f)). 
HB.instance Definition _ {X: CPO.type} (f: X -> X) :=
  CPO.copy (Chain f) (csup_gen (@Chain (csup_gen X) f)). 
HB.instance Definition _ {X: dCPO.type} (f: X -> X) :=
  dCPO.copy (Chain f) (dsup_gen (@Chain (dsup_gen X) f)). 
HB.instance Definition _ {X: supCL.type} (f: X -> X) :=
  supCL.copy (Chain f) (isup_gen (@Chain (isup_gen X) f)). 


(** partial orders where the chain of every monotone function is topped *)
HB.mixin Record Chain_lfp X of PO X := {
    #[canonical=no] chain_lfp: (X-mon->X) -> X;
    #[canonical=no] chain_lfpE: forall f: X-mon->X, is_sup (C f) (chain_lfp f);
  }.
(** hence where every monotone function has a least fixpoint *)
HB.builders Context X of Chain_lfp X.
  HB.instance Definition _ := PO_lfp.Build X chain_lfp (fun f => lfp_of_chain_supremum f (chain_lfpE f)).
HB.end.
(** we do not develop the theory of this class yet; still, the idea is that this subclass of PO with least fixpoints of monotone functions supports tower induction, and hence nice up-to techniques for induction *)


(** * Pataria's fixpoint theorem on dCPOs: every monotone function has a least (pre)fixpoint *)

Module Pataraia. 
Section s.
 Context (C: dCPO.type).

 Notation id := po_id.

 (** the largest monotone and extensive function on [C] *)
 Program Definition h: C-mon->C := locked (dsup (fun f => id <= f) _).
 Next Obligation.
   move=>/=f g I J. exists (f°g). split; last split.
   - by rewrite -I.
   - by rewrite -J.
   - by rewrite -I.
 Qed.
 
 Lemma h_ext: id <= h.
 Proof. unlock h. by apply: leq_dsup. Qed.

 Variable f: C-mon->C.
 Hypothesis f_ext: id <= f. 

 Lemma ext_h: f ° h <= h.
 Proof. unlock {2}h. apply: leq_dsup. by rewrite -f_ext -h_ext. Qed.
 
 Lemma h_prefixpoint: forall c, f (h c) <= h c.
 Proof. exact: ext_h. Qed.
 
End s.

Section s.
 Context {X: dCPO.type}.
 Variable f: X-mon->X.

 Definition lfp := locked (sval (h (Chain f) bot)).

 Fact Clfp: C f lfp.
 Proof. unlock lfp. exact: Celem. Qed.
 
 Theorem is_least_fixpoint: is_lfp f lfp. 
 Proof.
   unlock lfp.
   apply: lfp_of_chain_prefixpoint.
   exact: (h_prefixpoint (chain_postfixpoint f)).
 Qed.
 
 Proposition lfp_is_sup_C: is_sup (C f) lfp.
 Proof.
   apply: greatest_is_sup. split. exact: Clfp. 
   move=>c Cc. 
     apply: (chain_below_prefixpoints f _ _ (chn Cc)).
     apply eqv_leq, is_lfp_fixpoint, is_least_fixpoint.
 Qed.

 Corollary Cdirected: directed (C f).
 Proof.
   move=>c c' Cc Cc'. exists lfp; split. exact: Clfp.
   split; by apply: (leq_is_sup lfp_is_sup_C).
 Qed.
End s.

End Pataraia.


(** * Bournaki-Witt fixpoint theorems in CPOs *) 

Module BourbakiWitt.
Import Classical.

(** a generic consequence of excluded-middle *)
Lemma choose_gen (X: Type) (P A B: X -> Prop):
  (forall x, P x -> A x \/ B x) -> (forall x, P x -> A x) \/ (exists x, P x /\ B x).
Proof.
  intro H. classical_left. intros x Px.
  destruct (H _ Px). assumption. exfalso; eauto. 
Qed.

(** a more specific consequence; 
    - we only use it with [f=id, y=y'] to get than the chain is linearly ordered
    - we only use it with [f=id, y'=next y] and [f=next, y'= y] to get the stronger [linear_chain_strong]
 *)
Lemma choose (X: PO.type) (P: X -> Prop) (f: X -eqv-> X) y y':
  (forall x, P x -> f x <= y \/ y' <= x) -> (forall x, P x -> f x <= y) \/ (exists x, P x /\ y' <= x).
Proof. apply choose_gen. Qed.


(** ** first Bourbaki-Witt theorem: every extensive function on a CPO has a fixpoint 
    requires classical logic; more precisely, the above lemma [choose] 
    the fixpoint is obtained as [sup (C f)], 
    the difficulty consists in proving that [C f] is a chain so that it's sup exists
 *)

Section b.

 Context {C: PO.type}.
 Implicit Types x y z: C.
 
 Variable next: C -eqv-> C. 
 Hypothesis tower: forall P, sup_closed P -> (forall x, P x -> P (next x)) -> forall x, P x.
 Hypothesis id_next: forall x, x <= next x.
 
 (** relativised tower induction *)
 (* unused for now *)
 Lemma ptower (Q P: C -> Prop):
   Proper (leq --> leq) Q -> 
   sup_closed P ->
   (forall x, Q x -> P x -> P (next x)) ->
   (forall x, Q x -> P x).
 Proof.
   intros HQ Psup Pb. apply: tower. 
   - by apply sup_closed_impl.
   - intros x I H. cut (Q x); auto. revert H. apply HQ, id_next. 
 Qed.
 
 
 (** direct proof??? *)
 Lemma next_leq: Proper (leq ==> leq) next. 
 Proof.
   move=>x y. revert y. apply: tower.
   (* ?? *)
 Abort.
 
 (** the chain is linearly ordered, and [next] acts as a successor
     (proved twice for now, cf comments in the proof)
  *)
 Theorem linear_chain_strong: forall x y, x <= y \/ next y <= x.
 Proof.
   (** this first proof is inspired from Bourbaki's proof, 
       as reported in [Serge Lang, Algebra, p883]
       differences are that:
       - we use definitions that attempt to minimise the required amount of classical logic
       - we do not assume X (and thus admissible sets) to be non-empty
       - we do not start from a CPO, only from a mere partial order 
         (accordingly, the [tower] assumption requires closure under all existing suprema rather than under all directed suprema)
    *)
   (* [split c x] is [x \in M c] in the aforementioned book *)
   set split := fun c x => x <= c \/ next c <= x.
   (* [extreme c], up to classical logic, is [forall x, x < c -> next x <= c] *)
   set extreme := fun c => forall x, x <= c -> split x c. 
   (* Lemma 2.2 *)
   have M: forall c, extreme c -> forall x, split c x. {
     move=>c Ec. apply: tower.
     - move=>T IH t Ht.
       case: (choose T Datatypes.id c (next c)).
         by move=>x Tx; apply: IH.
       -- move=>F. left. by apply Ht.
       -- move=>[x [Tx xc]]. right. rewrite xc. by apply Ht. 
     - move=>x [xc|cx].
       -- case: (Ec _ xc)=>cx. 2: by left.
          have E: x≡c by apply antisym. by right; rewrite E. 
       -- right. rewrite cx. apply id_next. 
   }
   (* Lemma 2.3 *)
   have N: forall c, extreme c. {
     apply: tower.
     - move=>T IH b Hb x xb.
       case: (choose T next x x).
         move=>z Tz. rewrite or_comm. apply M=>//. by apply: IH.
       -- move=>F. left. apply Hb=>y Ty. rewrite ->(id_next y). by apply F.
       -- move=>[c [Tc xc]].
          case: (IH _ Tc x xc)=>cx; swap 1 2.
          right. rewrite cx. by apply Hb.
          case: (M _ (IH _ Tc) b)=>bc.
          left. by transitivity c.
          right. have E: x≡c by apply antisym. by rewrite E. 
     - move=>c IH x xc'.
       case: (M c IH x)=>[xc|cx]. right.
        case: (IH _ xc)=>cx. have E: x≡c by apply antisym. by rewrite E. 
        by rewrite cx; apply id_next.  
       by left. 
   }
   move=>??. by apply M, N.
   Fail idtac "done". 
   (** this second proof is inspired from Jules Jacobs' one, it requires only [choose id] *)
   Restart.
   apply: tower.
   - move=>T IH t Ht c.
       case: (choose T Datatypes.id c (next c)).
         by move=>x Tx; apply: IH.
       -- move=>F. left. by apply Ht.
       -- move=>[x [Tx xc]]. right. rewrite xc. by apply Ht. 
   - move=>x IHx y. 
     have H: next x <= y \/ y <= x. {
       revert y. apply: tower.
       -- move=>T IH t Ht. case: (choose T Datatypes.id x (next x)).
          by move=>y Ty/=; rewrite or_comm; apply: IH.
          --- move=>F. right. by apply Ht.
          --- move=>[y [Ty xy]]. left. rewrite xy. by apply Ht. 
       -- move=>y IHy. case: (IHx y); auto=>xy. left. 
          case: IHy=>yx. by rewrite yx.
          by apply eqv_leq, next, antisym. 
     }
     case: H; auto=>yx. right. case: (IHx y)=>xy.
     by apply eqv_leq, next, antisym.
     by rewrite xy.
 Qed.
 
 Corollary lt_leq x y: x < next y -> x <= y.
 Proof. case: (linear_chain_strong x y)=>?[]; tauto. Qed. 
 Corollary lt_leq' x y: x < y -> next x <= y.
 Proof. case=>_ yx. case: (linear_chain_strong y x) =>//. Qed.   
 
 (** [C] is indeed a chain, as an immediate corollary  *)
 Corollary linear_chain x y: x <= y \/ y <= x.
 Proof.
   case: (linear_chain_strong x y); auto=>xy.
   right. rewrite -xy. apply id_next.
 Qed.
 
 (** and [next] must actually be monotone *)
 Corollary next_leq: Proper (leq ==> leq) next. 
 Proof.
   move=>x y xy. case: (linear_chain_strong y x)=>yx.
   by apply eqv_leq, next, antisym.
   by rewrite yx.
 Qed.
 
 (** there is at most one prefixpoint, which must be a top element  *)
 Lemma prefixpoint_top x: next x <= x -> is_inf empty x.
 Proof.
   move=>H y. split=>//_. revert y.
   apply: tower. apply (sup_closed_leq (const x)).
   move=>y yx. case: (linear_chain_strong x y); auto=>xy.
   have E: y≡x by apply antisym. by rewrite E.
 Qed.
 
 (** the chain is well-founded, and thus a well-order
     TOTHINK: 
     - did not see this in the litterature, any applications?
     - is there a way to get it constructively? 
       (it seems we only have to replay the [tower] assumption, 
        but we probably have to use a weaker definition of [lt])
  *)
 Theorem wf_chain: @well_founded C lt.
 Proof.
   have E: forall x, (forall y, y<=x -> Acc lt y). {
     apply: tower.
     - move=>T IH t Ht y yx. constructor=>z zy. 
       have zx: z < t by apply ltle_lt with y. 
       case: (choose T Datatypes.id z z).
       by move=>*; apply linear_chain.
       -- move=>H. apply proj2 in zx. contradict zx. by apply Ht, H. 
       -- move=>[u [Tu /=zu]]. by apply: (IH u).
     - move=>x IH y yx. constructor=>z zy. apply IH.
       apply lt_leq. eapply ltle_lt; eassumption.
   }
   by move=>?; eauto.
 Qed.
 
 (** not clear [choose/choose_gen] is enough to entail decidability *)
 Lemma chain_dec: forall x y, x <= y \/ ~ x <= y.
 Proof.
   apply: tower.
   - move=>T IH t Ht y.
     case: (choose_gen T (fun x => x <= y) (fun x => ~ x <= y)).
       by move=>*; apply: IH. 
     -- move=>F. left. by apply Ht, F.
     -- move=>[x [Tx xy]]. right. contradict xy. rewrite -xy. by apply Ht.
   - move=>x IH y.
     case: (linear_chain_strong (next x) y); auto=>yn.
     case: (IH y)=>xy; swap 1 2.
     right. contradict xy. rewrite -xy. by apply id_next.
     (* ?? *)
 
   (* excluded middle of course works *)
   Restart.
   intros. apply: Classical_Prop.classic.
 Qed.
 
 Corollary chain_le_lt_dec x y: x <= y \/ y < x.
 Proof.
   case: (linear_chain x y); auto=>yx. 
   case: (chain_dec x y); auto=>xy.
   by right.
 Qed.
 
 (** [next] is strictly increasing, except possibly on the top element *)
 Corollary lt_next x: x < next x \/ is_inf empty x.
 Proof.
   case: (chain_le_lt_dec (next x) x); auto.
   by right; apply prefixpoint_top.
 Qed.
 
 (** [x<y] is almost equivalent to [next x<=y] *)
 Corollary lt_leq'' x y: next x <= y -> x < y \/ is_inf empty x. 
 Proof.
   move=>H. case: (lt_next x); auto=>//H'.
   left. eapply ltle_lt; eassumption. 
 Qed.   

End b.

Section b.

 Context {X: CPO.type}.
 Variable f: X -eqv-> X. 
 Hypothesis f_ext: forall x, x <= f x.
 
 Lemma chain_C: chain (C f).
 Proof.
   move=>x y Cx Cy.
   apply: (linear_chain _ (tower f) _ (chn Cx) (chn Cy)).
   move=>*; apply f_ext.
 Qed.
 
 Definition fixpoint := csup (C f) chain_C.
 Theorem is_fixpoint: f fixpoint ≡ fixpoint.
 Proof.
   apply: antisym=>//.
   apply: leq_csup. apply: Cf. apply Csup with (C f)=>//. exact: csup_spec.
 Qed.

 (** note: 
    our definition of CPO implicitly requires a least element (since the empty set is a chain) 
    we can drop this assumption assuming [X] contains some element x: 
    { y: X | x <= y } is a CPO with least element x.
    (TODO?)
  *)
 
End b. 


(** * second Bournaki-Witt therorem: every monotone function on a CPO has a least (pre-)fixpoint 
      still requires classical logic, but slightly less: only [forall T x, choose T id x x] 
      the fixpoint is obtained as [sup (C f)],     
      the difficulty consists in proving that [C f] is a chain so that it's sup exists

      When moving to dCPOs, we can get a constructive proof (cf. Pataraia below): 
      we can prove constructively that [C f] is directed.
 *)
Section b.

 Context {C: PO.type}.
 Implicit Types x y z: C.
 
 (** tower induction *)
 Variable next: C -mon-> C.
 Hypothesis tower: forall (P: C -> Prop), sup_closed P -> (forall x, P x -> P (next x)) -> forall x, P x.
 
 (** the function [next] must be extensive *)
 Lemma id_next: po_id <= next.
 Proof.
   apply: tower=>/=.
   - apply sup_closed_leq.
   - by move=>*; apply next.
 Qed.
 
 (** thus we have relativised tower induction  *)
 Lemma ptower' (Q P: C -> Prop):
   Proper (leq --> leq) Q -> 
   sup_closed P ->
   (forall x, Q x -> P x -> P (next x)) ->
   (forall x, Q x -> P x).
 Proof. apply (ptower _ tower id_next). Qed.
 
 (** there is at most one prefixpoint, which must be a top element  *)
 Lemma prefixpoint_top' x: next x <= x -> is_inf empty x.
 Proof.
   move=>H y. split=>//_. revert y.
   apply: tower. apply (sup_closed_leq (const x)).
   by move=>y ->.
 Qed.
 
 (** a helper for the proof of [linear_chain] *)
 Lemma leq_next: forall x y, (forall z, next z <= x -> z <= y) -> x <= next y.
 Proof.
   apply: tower.
   - move=>T IH t Ht y H. apply Ht=>x Tx. apply: IH=>//z zx.
     apply H. rewrite zx. by apply Ht.
   - move=>x IH y H. by apply next, H.
 Qed.
 
 (** [X] is linearly ordered *)
 Theorem linear_chain': forall x y, x <= y \/ y <= x.
 Proof.
   (** actually an instance of [Bourbaki.linear_chain] *)
   exact (linear_chain next tower id_next).
   Restart. 
   (** but the following proof is simpler and requires only [choose _ id x x] *)
   apply: tower.
   - move=>T IH t Ht y.
     case: (choose T Datatypes.id y y). by move=>*; apply: IH.
     -- move=>F. left. apply Ht=>x Tx. by apply F.
     -- move=>[x [Tx yx]]. right. rewrite yx. by apply Ht.
   - move=>x IH y.
     case: (choose (fun t => next t <= y) Datatypes.id x x).
     by move=>t _; move: (IH t); tauto.
     -- move=>F. right. apply leq_next=>z zy. by apply F.
     -- move=>[t [ty xt]]. left. by rewrite xt.
 Qed.

End b.
Section b.

 Context {X: CPO.type}.
 Variable f: X -mon-> X. 
 
 Lemma chain_C': chain (C f).
 Proof.
   move=>x y Cx Cy.
   exact: (linear_chain' _ (tower f) (chn Cx) (chn Cy)).
 Qed.
 
 Definition lfp := csup (C f) chain_C'.

 Fact lfp_is_sup_C: is_sup (C f) lfp.
 Proof. exact: csup_spec. Qed.

 Theorem is_least_fixpoint: is_lfp f lfp.
 Proof. apply lfp_of_chain_supremum, lfp_is_sup_C. Qed.
 
 (** note: 
    our definition of CPO implicitly requires a least element (since the empty set is a chain) 
    we can drop this assumption assuming [X] contains some element x: 
    { y: X | x <= y } is a CPO with least element x.
  *)

End b.

End BourbakiWitt.


(** * Extending structures to implement late inheritance *)

(** we have shown above that
     - [dCPO X] implies [Chain_lfp X] (module [Pataraia])
     - [CPO X] implies [Chain_lfp X] (with excluded middle, second part of module [BourbakiWitt])

    We setup and override structures as follows:

                    lfpPO
                      |
      (Bourbaki-Witt) |
    *CPO  ·····> Chain_lfp
      | \       /   |  ^
      |  lfpCPO     |  ·
      |     |  \    | · (Pataraia)
    *dCPO···|···\···|·
      |  \  |    \  |
      |  *dCPO   *CPO
      |     |
   *supCL   |
        \   |
         *supCL

    Structures on the left are those defined in [sups.v], where they were (easily) proved closed under dependent products [forall X, X i] and taking monotone functions [X-mon->X], whence the [*] on their left --- we just say "closed" in the sequel.

    We override them here so that they include [Chain_lfp] (and thus [lfpPO]).
    This is justified by Pataraia and Bourbaki-Witt theorems: we do not change the classes when doing so, and they are still closed.

    However, Bourbaki-Witt theorem requires excluded middle, and we do not want to pull this dependency at places where Pataria's theorem gives an axiom-free solution.

    To comply with HB's inheritance scheme,
    - we introduce the join structure [lfpCPO], which we do not declare as closed
    - we tag this structure to obtain the new [CPO], which we prove closed via Bourbaki-Witt
    - we prove the new [dCPO] and [supCL] closed via Pataraia

    The downside of this pattern is that [dCPO/supCL] do not inherit from [CPO] (but still from [sups.CPO]).

    Note that we really need the initial structure [sups.dCPO] and its closure properties to prove Pataraia's theorem (which goes through considerations about the dCPO of monotone functions on a sub-dCPO). Thus we cannot put the [Chain_lfp] mixin in [sups.dCPO].

    Bourbaki-Witt's theorem is more involved but does not require such constructions, so that we could imagine to put the [Chain_lfp] mixin in [sups.CPO]. But this would bring EM everywhere.

    In contrast, we could avoid the duplication of [supCL], by defining it directly in the present file rather than in [sups], on top of the present [dCPO]. This would however make it less obvious that [supCL] is defined along the same pattern as the other structures in [sups.v], and thus less natural to maintain.

 *)
HB.structure Definition lfpCPO := {X of sups.CPO X & Chain_lfp X }.
HB.structure Definition dCPO := {X of sups.dCPO X & Chain_lfp X }. 
HB.structure Definition supCL := {X of sups.supCL X & Chain_lfp X }. 

HB.mixin Record EMTag X := {}.
HB.structure Definition CPO := {X of lfpCPO X & EMTag X }.


(** empty factory to upgrade [sups.dCPO] to [dCPO], via Pataraia *)
HB.factory Record dCPO_lfp X of sups.dCPO X := {}.
HB.builders Context X of dCPO_lfp X.
HB.instance Definition _ := Chain_lfp.Build X Pataraia.lfp Pataraia.lfp_is_sup_C.
HB.end.

(** empty factory to upgrade [sups.CPO] to [CPO], via BourbakiWitt *)
HB.factory Record CPO_lfp X of sups.CPO X := {}.
HB.builders Context X of CPO_lfp X.
HB.instance Definition _ := Chain_lfp.Build X BourbakiWitt.lfp BourbakiWitt.lfp_is_sup_C.
HB.instance Definition _ := EMTag.Build X.
HB.end.

(** we need to redeclare/upgrade all previously known instances of [dCPO] *)
HB.instance Definition _ := dCPO_lfp.Build Prop.
HB.instance Definition _ I (X: I -> sups.dCPO.type) := dCPO_lfp.Build (forall i, X i).
HB.instance Definition _ (X: Setoid.type) (Y: sups.dCPO.type) := dCPO_lfp.Build (X -eqv-> Y).
HB.instance Definition _ (X: PO.type) (Y: sups.dCPO.type) := dCPO_lfp.Build (X -mon-> Y).
HB.instance Definition _ (X: sups.dCPO.type) (f: X -> X) := dCPO_lfp.Build (Chain f). 
HB.builders Context Y of comonadic_dsup Y.
 HB.instance Definition _ := comonadic_gsup.Build (@directed) Y (X:=dsup_gen X) f.
 HB.instance Definition _ := sups.dCPO.copy Y (dsup_gen Y).
 HB.instance Definition _ := dCPO_lfp.Build Y.
HB.end.

(** similarly for [CPO] (we do it after the ones for [dCPO] so that the latter, which are axiom-free, take precedence)*)
HB.instance Definition _ := CPO_lfp.Build Prop.
HB.instance Definition _ I (X: I -> sups.CPO.type) := CPO_lfp.Build (forall i, X i).
HB.instance Definition _ (X: Setoid.type) (Y: sups.CPO.type) := CPO_lfp.Build (X -eqv-> Y).
HB.instance Definition _ (X: PO.type) (Y: sups.CPO.type) := CPO_lfp.Build (X -mon-> Y).
HB.instance Definition _ (X: sups.CPO.type) (f: X -> X) := CPO_lfp.Build (Chain f).
HB.builders Context Y of comonadic_csup Y.
 HB.instance Definition _ := comonadic_gsup.Build (@chain) Y (X:=csup_gen X) f.
 HB.instance Definition _ := sups.CPO.copy Y (csup_gen Y).
 HB.instance Definition _ := CPO_lfp.Build Y.
HB.end.

(** similarly for [supCL] *)
HB.instance Definition _ I (X: I -> supCL.type) := dCPO_lfp.Build (forall i, X i).
HB.instance Definition _ (X: Setoid.type) (Y: supCL.type) := dCPO_lfp.Build (X -eqv-> Y).
HB.instance Definition _ (X: PO.type) (Y: supCL.type) := dCPO_lfp.Build (X -mon-> Y).
HB.instance Definition _ (X: supCL.type) (f: X -> X) := dCPO_lfp.Build (Chain f). 
HB.builders Context Y of comonadic_isup Y.
 HB.instance Definition _ := comonadic_gsup.Build any_kind Y (X:=isup_gen X) f.
 HB.instance Definition _ := sups.supCL.copy Y (isup_gen Y).
 HB.instance Definition _ := dCPO_lfp.Build Y.
HB.end.
