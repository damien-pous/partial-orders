Require Export partialorder.

(** * adjunctions *)

Definition adjunction {X Y: PO.type} l r := forall (x: X) (y: Y), l x <= y <-> x <= r y.

Lemma adj_id {X}: @adjunction X X types_id types_id.
Proof. done. Qed.

Lemma adj_comp {X Y Z}
  l r (lr: @adjunction X Y l r)
  k s (ks: @adjunction Y Z k s)
  : adjunction (k ∘ l) (r ∘ s).
Proof. move=>x z. by rewrite ks lr. Qed.


(** we would like to index adjunctions by both underlying functions, but HB only supports one index
    we duplicate structures to use inferrence on both functions *)

(** ** indexed by the left adjoint *)
HB.mixin Record isLeftAdjoint (X Y: PO.type) (f: X -> Y) :=
  { #[canonical=no] radj: Y -> X; 
    #[canonical=no] adj: adjunction f radj }.
(** adjoints are automatically monotone *)
HB.builders Context (X Y: PO.type) f of isLeftAdjoint X Y f.
  Lemma monotone: Proper (leq ==> leq) f.
  Proof. move=>x y xy. apply/adj. rewrite xy. by apply/adj. Qed.
  HB.instance Definition _ := isMonotone.Build X Y f monotone.
HB.end.
HB.structure Definition leftAdjunction X Y := {f of isLeftAdjoint X Y f }.
Arguments radj {_ _}.
Infix "⊣" := leftAdjunction.type (at level 79).

(** alternative presentation, via unit and counit *)
HB.factory Record isLeftAdjoint' (X Y: PO.type) f of po_morphism X Y f := 
  { #[canonical=no] f': Y -mon-> X; 
    #[canonical=no] adj_unit: @types_id X <= f' ∘ f;
    #[canonical=no] adj_counit: f ∘ f' <= types_id }.
HB.builders Context (X Y: PO.type) f of isLeftAdjoint' X Y f.
  Lemma adj: adjunction f f'.
  Proof.
    move=>x y. split=>H.
    - setoid_rewrite (adj_unit x)=>/=. exact: monotone.
    - setoid_rewrite <-(adj_counit y). exact: monotone.
  Qed.
  HB.instance Definition _ := isLeftAdjoint.Build X Y f adj.
HB.end.

(** ** indexed by the right adjoint *)
HB.mixin Record isRightAdjoint (X Y: PO.type) (f: X -> Y) :=
  { #[canonical=no] ladj: Y -> X; 
    #[canonical=no] adj': adjunction ladj f }.
(** adjoints are automatically monotone *)
HB.builders Context (X Y: PO.type) f of isRightAdjoint X Y f.
  Lemma monotone: Proper (leq ==> leq) f.
  Proof. move=>x y xy. apply/adj'. rewrite -xy. by apply/adj'. Qed.
  HB.instance Definition _ := isMonotone.Build X Y f monotone.
HB.end.
HB.structure Definition rightAdjunction X Y := {f of isRightAdjoint X Y f }.
Arguments ladj {_ _}.
Infix "⊢" := rightAdjunction.type (at level 79).

(** alternative presentation, via unit and counit *)
HB.factory Record isRightAdjoint' (X Y: PO.type) f of po_morphism X Y f := 
  { #[canonical=no] f': Y -mon-> X; 
    #[canonical=no] adj_unit: @types_id Y <= f ∘ f';
    #[canonical=no] adj_counit: f' ∘ f <= types_id }.
HB.builders Context (X Y: PO.type) f of isRightAdjoint' X Y f.
  Lemma adj: adjunction f' f.
  Proof.
    move=>x y. split=>H.
    - setoid_rewrite (adj_unit x)=>/=. exact: monotone. 
    - setoid_rewrite <-(adj_counit y). exact: monotone.
  Qed.
  HB.instance Definition _ := isRightAdjoint.Build X Y f adj.
HB.end.

(** ** cross-instances, for jumping from one index to the other *)
HB.instance Definition _ X Y (f: X ⊣ Y) := isRightAdjoint.Build Y X (radj f) (@adj _ _ f).
HB.instance Definition _ X Y (f: X ⊢ Y) := isLeftAdjoint.Build Y X (ladj f) (@adj' _ _ f).

(** ** duality (note the difference with cross-instances) *)
Lemma dual_adjunction {X Y l r}: @adjunction X Y l r -> @adjunction (dual Y) (dual X) r l.
Proof. move=>H x y. apply: iff_sym. exact: H. Defined.
Lemma dual_adjunction' {X Y: PO.type} {l r}: @adjunction (dual Y) (dual X) r l -> @adjunction X Y l r.
Proof. move=>H x y. apply: iff_sym. exact: H. Defined.
HB.instance Definition _ X Y (f: X ⊣ Y) :=
  @isRightAdjoint.Build (dual X) (dual Y) (dualf f) (dualf (radj f)) (dual_adjunction (@adj _ _ f)).
HB.instance Definition _ X Y (f: X ⊢ Y) :=
  @isLeftAdjoint.Build (dual X) (dual Y) (dualf f) (dualf (ladj f)) (dual_adjunction (@adj' _ _ f)).

(** ** operations *)

(** identity *)
HB.instance Definition _ {X} := isLeftAdjoint.Build X X types_id adj_id. 
HB.instance Definition _ {X} := isRightAdjoint.Build X X types_id adj_id. 

(** composition *)
HB.instance Definition _ {X Y Z} (xy: X ⊣ Y) (yz: Y ⊣ Z) :=
  isLeftAdjoint.Build X Z (yz ∘ xy) (adj_comp adj adj).
HB.instance Definition _ {X Y Z} (xy: X ⊢ Y) (yz: Y ⊢ Z) :=
  isRightAdjoint.Build X Z (yz ∘ xy) (adj_comp adj' adj'). 

(** ** properties *)

(** basic properties  *)
Section s.
  Context {X Y} (f: X ⊣ Y).

  Definition ladj_monad := radj f ∘ f.
  
  Lemma ladj_unit: @types_id X <= ladj_monad.
  Proof. move=>x/=. by rewrite -adj. Qed.

  Lemma ladj_lrl: f ∘ ladj_monad ≡ f.
  Proof. apply: antisym=>x/=. exact/adj. by rewrite -(ladj_unit x). Qed.

  Lemma ladj_mult: ladj_monad ∘ ladj_monad <= ladj_monad.
  Proof. move=>x/=. apply/adj. by do 2 setoid_rewrite (ladj_lrl _). Qed.

  (** left adjoints preserve sups *)
  Lemma adjoint_sup P (x: X): is_sup P x -> is_sup (image f P) (f x).
  Proof.
    move=>H y/=. rewrite adj H.
    rewrite (upper_boundE _ y).
    setoid_rewrite image_adj.
    apply: forall_iff=>z/=. 
    by rewrite adj. 
  Qed.

  (** functional version of the adjunction  *)
  Lemma fadj {Z} h (k: Z -mon-> Y): f ∘ h <= k <-> h <= radj f ∘ k.
  Proof. cbn. by setoid_rewrite (adj _). Qed.

End s.

(** dual properties *)
Section s.
  Context {X Y} (f: X ⊢ Y).

  Definition radj_comonad := ladj f ∘ f.
  
  Lemma radj_counit: radj_comonad <= types_id.
  Proof. exact: (ladj_unit (dualf f)). Qed.
  
  Lemma radj_rlr: f ∘ radj_comonad ≡ f.
  Proof. exact: (ladj_lrl (dualf f)). Qed.

  Lemma radj_comult: radj_comonad <= radj_comonad ∘ radj_comonad.
  Proof. exact: (ladj_mult (dualf f)). Qed.
  
  (** right adjoints preserve infs *)
  Lemma adjoint_inf P (x: X): is_inf P x -> is_inf (image f P) (f x).
  Proof. exact: (adjoint_sup (dualf f)). Qed.

  Lemma fadj' {Z} h (k: Z -mon-> Y): k <=[Z->Y] f ∘ h <-> ladj f ∘ k <= h.
  Proof. exact: (fadj (dualf f) (Z:=dual Z) h (dualf k)). Qed.
  
End s.

(** cross properties (unfortunately, those have to be duplicated) *)
Section s.
  Context {X Y} (f: X ⊣ Y).

  Definition ladj_comonad := f ∘ radj f.
  
  Lemma ladj_counit: ladj_comonad <= types_id.
  Proof. exact: (radj_counit (radj f)). Qed.

  Lemma ladj_rlr: radj f ∘ ladj_comonad ≡ radj f.
  Proof. exact: (radj_rlr (radj f)). Qed.

  Lemma ladj_comult: ladj_comonad <= ladj_comonad ∘ ladj_comonad.
  Proof. exact: (radj_comult (radj f)). Qed.
End s.

(** dual cross properties *)
Section s.
  Context {X Y} (f: X ⊢ Y).

  Definition radj_monad := f ∘ ladj f.
  
  Lemma radj_unit: @types_id Y <= radj_monad.
  Proof. exact: (ladj_counit (dualf f)). Qed.
  
  Lemma radj_lrl: ladj f ∘ radj_monad ≡ ladj f.
  Proof. exact: (ladj_rlr (dualf f)). Qed.

  Lemma radj_mult: radj_monad ∘ radj_monad <= radj_monad.
  Proof. exact: (ladj_comult (dualf f)). Qed.
End s.


(** * (co)monadic adjunctions *)

(** here we do not duplicate (yet?)
    - we use [Monadic] to indicate that *left* adjoint takes part into a monadic adjunction
    - we use [CoMonadic] to indicate that *right* adjoint takes part into a comonadic adjunction
 *)
HB.mixin Record isMonadic X Y f of leftAdjunction X Y f := {
    #[canonical=no] monadic: ladj_monad f ≡ types_id
  }.
HB.structure Definition MonadicAdjunction X Y := {f of isMonadic X Y f &}.
Infix "·⊣" := MonadicAdjunction.type (at level 79).

HB.mixin Record isCoMonadic X Y f of rightAdjunction X Y f := {
    #[canonical=no] comonadic: radj_comonad f ≡ types_id
  }.
HB.structure Definition CoMonadicAdjunction X Y := {f of isCoMonadic X Y f &}.
Infix "⊢·" := CoMonadicAdjunction.type (at level 79).

(** duality *)
HB.instance Definition _ X Y (f: X ·⊣ Y) :=
  isCoMonadic.Build (dual X) (dual Y) (dualf f) (@monadic _ _ f).
HB.instance Definition _ X Y (f: X ⊢· Y) :=
  isMonadic.Build (dual X) (dual Y) (dualf f) (@comonadic _ _ f).

(** identities *)
HB.instance Definition _ X := isMonadic.Build X X types_id eqv_refl. 
HB.instance Definition _ X := isCoMonadic.Build X X types_id eqv_refl.

(** monadic adjunctions create infs *)
Lemma monadic_inf {X Y} (f: X ·⊣ Y) P (y: Y):
  is_inf (image f P) y -> is_inf P (radj f y).
Proof.
  move=>H x. rewrite -adj H lower_boundE.  
  setoid_rewrite image_adj. apply: forall_iff=>z/=.
  rewrite adj. by setoid_rewrite (monadic z). 
Qed.

(** comonadic adjunctions create sups *)
Lemma comonadic_sup {X Y} (f: X ⊢· Y) P (y: Y):
  is_sup (image f P) y -> is_sup P (ladj f y).
Proof. exact: (monadic_inf (dualf f)). Qed.


(** * isomorphisms *)

(** An isomorphism (of partial orders) is a pair (f,g) of inverse po_morphisms which cancel each other.
    This is equivalent to asserting that (f,g) is a monadic adunction and (g,f) is a comonadic adunction.

    To comply with HB's non forgetful inheritance, we use this latter definition.
    Below:
    - f is the left adjoint of a monadic adjunction [f, radj f]
    - f is the right adjoint of a comonadic adjunction [ladj f, f]
    and we need to ask that [ladj f] and [radj f] are the same    
 *)
HB.mixin Record biadj_isIso X Y f of leftAdjunction X Y f & rightAdjunction X Y f := 
  { #[canonical=no] radj_ladj: radj f ≡ ladj f }.
HB.builders Context X Y i of biadj_isIso X Y i.
  Lemma monadic: ladj_monad i ≡ types_id.
  Proof.
    apply: antisym=>x. 2: exact: ladj_unit. 
    rewrite /ladj_monad/=(radj_ladj (i x)). exact: ladj_counit.
  Qed.
  HB.instance Definition _ := isMonadic.Build X Y i monadic.
  Lemma comonadic: radj_comonad i ≡ types_id.
  Proof.
    apply: antisym=>x/=. exact: radj_counit. 
    rewrite /radj_comonad/=-(radj_ladj (i x)). exact: radj_unit.
  Qed.
  HB.instance Definition _ := isCoMonadic.Build X Y i comonadic.
HB.end. 
HB.structure Definition Iso X Y := {i of biadj_isIso X Y i & }.
Infix "≃" := Iso.type (at level 70).
Definition inv {X Y} (i: X ≃ Y) := radj i. 
Notation "i ^-1" := (inv i).

(** reflexivity *)
HB.instance Definition _ X := biadj_isIso.Build X X types_id eqv_refl. 

(** alternative factory, where we `manually' provide the two adjunctions *)
HB.factory Record isIso (X Y: PO.type) (i: X -> Y) := {
    j: Y -> X;
    ij: adjunction i j;
    ji: adjunction j i;
  }.
HB.builders Context X Y i of isIso X Y i.
  HB.instance Definition _ := isLeftAdjoint.Build X Y i ij.
  HB.instance Definition _ := isRightAdjoint.Build X Y i ji.
  HB.instance Definition _ := biadj_isIso.Build X Y i eqv_refl.
HB.end.

Lemma inv_alt {X Y: PO.type} (i: X ≃ Y): i^-1 ≡ ladj i.
Proof. exact: radj_ladj. Qed. 

Lemma isoK {X Y: PO.type} (i: X ≃ Y): i ∘ i^-1 ≡ types_id.
Proof.
  apply: antisym. exact: ladj_counit.
  move=>y/=. rewrite (inv_alt i y). exact: ladj_unit. 
Qed.
Lemma isoK' {X Y: PO.type} (i: X ≃ Y): i^-1 ∘ i ≡ types_id.
Proof. exact: monadic. Qed.

(** symmetry *)
Lemma adj_iso_inv {X Y} (i: X ≃ Y) : adjunction i^-1 i.
Proof. move=>y x. rewrite (inv_alt i y). exact: adj'. Qed.
HB.instance Definition _ X Y (i: X ≃ Y) := @isIso.Build Y X (i^-1) i (adj_iso_inv i) adj.

(** transitivity *)
Lemma iso_comp_radj_ladj {X Y Z: PO.type} (i: X ≃ Y) (j: Y ≃ Z): radj (j ∘ i) ≡ ladj (j ∘ i).
Proof. cbn=>x. rewrite (radj_ladj x). exact: radj_ladj. Qed.
HB.instance Definition _ {X Y Z: PO.type} (i: X ≃ Y) (j: Y ≃ Z) :=
  @biadj_isIso.Build X Z (j ∘ i) (iso_comp_radj_ladj i j).

(** helper to construct isomorphisms with the last factory [isIso.Build] *)
Definition mk_iso (X Y: PO.type) (f: X -> Y) (g: Y -> X) (fg: adjunction f g) (gf: adjunction g f) := f.
Arguments mk_iso {_ _}.
HB.instance Definition _ X Y f g fg gf := @isIso.Build X Y (@mk_iso X Y f g fg gf) g fg gf.

(** ** concrete isomorphisms *)

(** eta expansion of a partial order (HB/structures specific)  *)
Program Definition iso_eta X: X ≃ eta X :=
  @mk_iso X (eta X) types_id types_id adj adj.

(** pseudo involutivity of duality *)
Definition dualI (X: PO.type): X ≃ dual (dual X) := iso_eta X.

(** retractions yielding isomorphisms  *)
Program Definition iso_retract A (X: PO.type) (r: A -> X) (i: X -> A) (ri: r ∘ i ≡ types_id): X ≃ kernel r :=
  @mk_iso X (kernel r) i r _ _.
Next Obligation. move=>??; cbn; by setoid_rewrite (ri _). Qed.
Next Obligation. move=>??; cbn; by setoid_rewrite (ri _). Qed.

(** alternative presentation of monotone functions
    (useful for constructing infs on monotone functions by duality with sups)  *)
Program Definition iso_dual_mon (X Y: PO.type): (X -mon-> Y) ≃ dual (dual X -mon-> dual Y) :=
  @mk_iso (X -mon-> Y) (dual (dual X -mon-> dual Y))
    dualf (fun f => mk_mon (f: X -> Y) _) _ _.
Next Obligation. by apply/Proper_dual_leq. Qed.
Next Obligation. done. Qed.
Next Obligation. done. Qed.

(** extensional functions as a sig type
    (useful to apply generic lemmas about sig types to extensional functions) *)
Section s.
 Context {X: Setoid.type} {Y: PO.type}.
 Definition setoid_morphism_to_sig (f: X-eqv->Y): sig (Proper (eqv==>eqv)) :=
   exist (Proper (eqv ==> eqv)) f (extensional f).
 Definition sig_to_setoid_morphism (f: sig (Proper (eqv==>eqv))): X-eqv->Y :=
   mk_ext' (sval f) (proj2_sig f).
 Program Definition setoid_morphism_as_sig: (X-eqv->Y) ≃ (sig (Proper (@eqv X==>@eqv Y))) :=
   mk_iso setoid_morphism_to_sig sig_to_setoid_morphism _ _.
 Next Obligation. done. Qed.
 Next Obligation. done. Qed.
End s.

(** monotone functions as a sig type
    (useful to apply generic lemmas about sig types to monotone functions) *)
Section s.
 Context {X Y: PO.type}.
 Definition po_morphism_to_sig (f: X-mon->Y): sig (Proper (leq==>leq)) :=
   exist (Proper (leq ==> leq)) f (monotone f).
 Definition sig_to_po_morphism (f: sig (Proper (leq==>leq))): X-mon->Y :=
   mk_mon (sval f) (proj2_sig f).
 Program Definition po_morphism_as_sig: (X-mon->Y) ≃ (sig (Proper (@leq X==>@leq Y))) :=
   mk_iso po_morphism_to_sig sig_to_po_morphism _ _.
 Next Obligation. done. Qed.
 Next Obligation. done. Qed.
End s.

(** binary products as dependent products on [bool] (not used yet) *)
Section prod_dprod_bool.
  Context {X Y: PO.type}.
  Definition bool_dfun (x: X) (y: Y): PO.sort (forall b, bool_fun X Y b) :=
    fun b => if b return bool_fun X Y b then y else x.
  Program Definition prod_as_dprod_bool: prod X Y ≃ forall b, bool_fun X Y b :=
    mk_iso (fun p => bool_dfun p.1 p.2) (fun h => (h false, h true)) _ _.
  Next Obligation.
    move=>p h. split=>H.
    split. exact: (H false). exact: (H true).
    by case; apply H.
  Qed.
  Next Obligation.
    move=>h p. split=>H. 
    by case; apply H.
    split. exact: (H false). exact: (H true).
  Qed.
End prod_dprod_bool.
