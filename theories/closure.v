From Stdlib Require Import Psatz.
Require Export lattice.

(** * closures *)

#[primitive]
HB.mixin Record isClosure (X: PO.type) (c: X -> X) := {
    #[canonical=no] extensive: @types_id X <= c;
    #[canonical=no] idempotent_: c ∘ c <= c;
  }.
#[short(type="closure")]
HB.structure Definition Closure X :=
  { c of po_morphism X X c & isClosure X c }.
Arguments extensive {_}. 

Lemma idempotent {X} (c: closure X): c ∘ c ≡ c.
Proof.
  apply: antisym.
  exact/idempotent_.
  (* by rewrite -{2}(extensive c).  *)
  transitivity (c ∘ types_id). done.
  apply: types_comp_leq. done.
  exact/extensive.
Qed.

(** identity closure *)
HB.instance Definition _ X := isClosure.Build X types_id leq_refl leq_refl.

(** composition of closures (under distributivity assumption) *)
Definition closure_comp {X} (c d: closure X) (H: d∘c <= c∘d) := c∘d.
Program Definition _closure_comp X c d H := isClosure.Build X (closure_comp c d H) _ _.
Next Obligation. rewrite (extensive c)=>x. apply c. exact/extensive. Qed.
Next Obligation.
  move=>x. rewrite /closure_comp/=. 
  setoid_rewrite (H _)=>/=. 
  setoid_rewrite (idempotent c _). 
  setoid_rewrite (idempotent d _).
  done.
Qed.
HB.instance Definition _ X c d H := po_morphism.on (@closure_comp X c d H). 
HB.instance Definition _ X c d H := @_closure_comp X c d H. 
Arguments closure_comp {_} _ _ _/.

(** closures from adjunctions *)
HB.instance Definition _ {X Y} (f: X ⊣ Y) := po_morphism.on (ladj_monad f).
HB.instance Definition _ {X Y} (f: X ⊣ Y) := isClosure.Build _ (ladj_monad f) (ladj_unit f) (ladj_mult f).
HB.instance Definition _ {X Y} (f: X ⊢ Y) := po_morphism.on (radj_monad f).
HB.instance Definition _ {X Y} (f: X ⊢ Y) := isClosure.Build _ (radj_monad f) (radj_unit f) (radj_mult f).


(** ** least closures *)
Section s.
Context {X: CompleteLattice.type}.

Section lcl.  
Variable s: X -mon-> X.

Definition lcl (x: X) := (* locked *) (lfp (@cup (X-mon->X) (const x) s)).

Lemma lcl_ext x: x <= lcl x.
Proof. unlock lcl. rewrite -lfp_pfp/=. exact/cup_l. Qed.

Lemma lcl_ext': @types_id X <= lcl.
Proof. exact/lcl_ext. Qed.

Lemma lcl_closed x: s (lcl x) <= lcl x.
Proof. unlock lcl. rewrite -{2}lfp_pfp/=. exact/cup_r. Qed.

Lemma lcl_closed': s ∘ lcl <= lcl.
Proof. exact/lcl_closed. Qed.

Lemma lcl_ind x y: x <= y -> s y <= y -> lcl x <= y.
Proof. intros. unlock lcl. apply: lfp_ind=>/=. exact/geq_cup. Qed.

Lemma lcl_idem x: lcl (lcl x) <= lcl x.
Proof. apply: lcl_ind=>//. exact/lcl_closed. Qed.

Lemma _lcl_leq: Proper (leq ==> leq) lcl.
Proof. move=>x y xy. unlock lcl. apply: lfp_leq. exact/cup_leq. Qed.

HB.instance Definition _ := isMonotone.Build X X lcl _lcl_leq.
HB.instance Definition _ := isClosure.Build X lcl lcl_ext lcl_idem.

Lemma lcl_above: s <=[X->X] lcl.
Proof. rewrite -lcl_closed'=>x. apply s. exact/lcl_ext. Qed.

Lemma lcl_least_closure (c: closure X): s <= c -> lcl <= c.
Proof.
  move=>sc x. apply: lcl_ind.
  exact/extensive.
  rewrite sc. exact/idempotent_.
Qed.

Lemma lcl_leq_iff x y: lcl x <= lcl y <-> x <= lcl y.
Proof.
  split=>H.
  rewrite -H. exact/lcl_ext.
  rewrite H. exact/idempotent_. 
Qed.

Lemma lcl_eqv_iff x y: lcl x ≡ lcl y <-> x <= lcl y /\ y <= lcl x.
Proof. rewrite eqv_of_leq. by rewrite ->2lcl_leq_iff. Qed.
      
End lcl.
Notation "s ^*" := (lcl s).

#[export] Instance lcl_leq: Proper (leq ==> leq ==> leq) lcl.
Proof. move=>s t st x y xy. unlock lcl. apply: lfp_leq. exact/cup_leq. Qed.
#[export] Instance lcl_eqv: Proper (eqv ==> eqv ==> eqv) lcl := op_leq_eqv_2.

#[export] Instance lcl_leq': Proper (leq ==> leq) lcl.
Proof. move=>s t st x. exact/lcl_leq. Qed.
#[export] Instance lcl_eqv': Proper (eqv ==> eqv) lcl := op_leq_eqv_1.
(* TOTHINK: cooperation between [lcl_leq] and [lcl_leq'] *)

Lemma lcl_cup_ s t: s^* ∘ t^* <= (cup s t)^*.
Proof.
  transitivity ((cup s t)^* ∘ (cup s t)^* ). 2: exact/idempotent_.
  apply: types_comp_leq; apply: lcl_leq'; [exact/cup_l|exact/cup_r]. 
Qed.

Proposition lcl_cup s t: s^* ∘ t^* <= t^* ∘ s^* -> (cup s t)^* ≡ t^* ∘ s^*.
Proof.
  intro st. apply: antisym.
  - change ((cup s t)^* <= closure_comp _ _ st). 
    apply: lcl_least_closure=>x/=. apply: geq_cup.
    rewrite -(lcl_ext t). exact/lcl_above.
    rewrite -(lcl_ext s). exact/lcl_above.
  - rewrite cupC. exact/lcl_cup_. 
Qed.
Proposition lcl_cup_iff s t: (cup s t)^* ≡ t^* ∘ s^* <-> s^* ∘ t^* <= t^* ∘ s^*.
Proof.
  split. 2: exact/lcl_cup. 
  move=>st. etransitivity. exact/lcl_cup_. exact: eqv_leq.  
Qed.

Lemma lcl_idm s: s^*^* ≡ s^*.
Proof.
  apply: antisym.
  exact/lcl_least_closure. 
  exact/lcl_above.
Qed.

Lemma lcl_bot: bot^* ≡ types_id.
Proof.
  apply: antisym.
  apply: lcl_least_closure. exact: geq_bot.
  exact/extensive.
Qed.

Lemma lcl_id: types_id^* ≡ types_id.
Proof.
  apply: antisym.
  exact/lcl_least_closure.
  exact/lcl_above.
Qed.

Lemma lcl_const x: (const x)^* ≡ cup (const x) types_id.
Proof.
  apply: antisym.
  - move=>y. apply: lcl_ind=>/=. exact/cup_r. exact/cup_l.
  - apply: geq_cup. exact:lcl_above. exact/lcl_ext.
Qed.

Section t.
  Variable s: nat -> X -mon-> X.
  Let c j := (s j)^*.

  (* s_<j, c_<j *)
  Let s' :=
        fix s' n :=
          match n with
          | O => bot
          | S n => cup (s' n) (s n)
          end.
  (* Let s' j := isup (fun i => i < j)%nat s. *)
  Let c' j := (s' j)^*.


  (* c_{n-1} ° ... ° c_0 *)
  Let c'' :=
        fix c'' n :=
          match n with
          | O => po_id
          | S n => (c n)^* ° c'' n
          end.
  
  Proposition lcl_cups n:
    (forall j, (j<n)%nat -> c' j ∘ c j <= c j ∘ c' j) -> c' n ≡ c'' n.
  Proof.
    elim:n=>[|n IH] H/=.
    - exact: lcl_bot. 
    - rewrite /c'/= lcl_cup. apply: types_comp_eqv=>/=.
      symmetry; exact/lcl_idm. apply:IH.
      move=>j ij. apply: H. lia.
      apply: H. lia. 
  Qed.
End t.
End s.
Opaque lcl.
Notation "s ^*" := (lcl s).

Lemma lcl_ind' {X} {Y: CompleteLattice.type} (s: Y -mon-> Y) (f g: X -> Y):
  f <= g -> s ∘ g <= g -> s^* ∘ f <= g.
Proof. move=>H H' x/=. apply: lcl_ind. exact/H. exact/H'. Qed.

Proposition lcl_move_l {X} {Y: CompleteLattice.type} (s: Y -mon-> Y) (f: X -mon-> Y) (c: closure X):
  s ∘ f <= f ∘ c -> s^* ∘ f <= f ∘ c.
Proof.
  move=>sf. apply: lcl_ind'.
  - move=>x. apply f. exact/extensive.
  - move=>x/=. setoid_rewrite (sf _). apply f. exact/idempotent_. 
Qed.

Proposition lcl_move_r {X} {Y: CompleteLattice.type} (s: Y -mon-> Y) (f: Y ⊣ X) (c: closure X):
  f ∘ s <= c ∘ f -> f ∘ s^* <= c ∘ f.
Proof.
  move=>sf.
  rewrite fadj. apply: lcl_ind'. 
  rewrite -fadj=>y/=. exact (extensive c _).
  rewrite -fadj=>y/=. setoid_rewrite (sf _)=>/=.
  setoid_rewrite (ladj_counit f _). exact/idempotent_. 
Qed.


(** * coclosures (dual of closures) *)

#[primitive]
HB.mixin Record isCoClosure (X: PO.type) (c: X -> X) := {
    #[canonical=no] contractive: c <= types_id;
    #[canonical=no] coidempotent_: c <= c ∘ c;
  }.
#[short(type="coclosure")]
HB.structure Definition CoClosure X :=
  { c of po_morphism X X c & isCoClosure X c }.

(** duality *)
HB.instance Definition _ X (c: Closure.type X) :=
  isCoClosure.Build (dual X) (dualf c) (@extensive _ c) (@idempotent_ _ c).
HB.instance Definition _ X (c: CoClosure.type X) :=
  isClosure.Build (dual X) (dualf c) (@contractive _ c) (@coidempotent_ _ c).

Lemma coidempotent {X} (c: coclosure X): c ∘ c ≡ c.
Proof. exact (idempotent (dualf c)). Qed.

(** identity coclosure *)
HB.instance Definition _ X := isCoClosure.Build X types_id leq_refl leq_refl.

(** composition of coclosures (under distributivity assumption) *)
Definition coclosure_comp {X} (c d: coclosure X) (H: c∘d <= d∘c) := c∘d.
Lemma _coclosure_comp X c d H: isCoClosure.axioms_ X (@coclosure_comp X c d H).
Proof. case: (@_closure_comp (dual X) (dualf c) (dualf d) H). by split. Qed.
HB.instance Definition _ X c d H := po_morphism.on (@coclosure_comp X c d H). 
HB.instance Definition _ X c d H := @_coclosure_comp X c d H. 
Arguments coclosure_comp {_} _ _ _/.

(** coclosures from adjunctions *)
HB.instance Definition _ {X Y} (f: X ⊣ Y) := po_morphism.on (ladj_comonad f).
HB.instance Definition _ {X Y} (f: X ⊣ Y) := isCoClosure.Build _ (ladj_comonad f) (ladj_counit f) (ladj_comult f).
HB.instance Definition _ {X Y} (f: X ⊢ Y) := po_morphism.on (radj_comonad f).
HB.instance Definition _ {X Y} (f: X ⊢ Y) := isCoClosure.Build _ (radj_comonad f) (radj_counit f) (radj_comult f).


(** ** greateast coclosures *)

Section s.
Context {X: CompleteLattice.type}.

Section gcc.  
Variable s: X -mon-> X.

Definition gcc: X -> X := @lcl (dual X) (dualf s).

Lemma gcc_coext x: gcc x <= x.
Proof. exact: (@lcl_ext (dual X) (dualf s)). Qed.

Lemma gcc_coext': gcc <= types_id.
Proof. exact/gcc_coext. Qed.

Lemma gcc_closed x: gcc x <= s (gcc x).
Proof. exact: (@lcl_closed (dual X) (dualf s)). Qed.

Lemma gcc_closed': gcc <= s ∘ gcc.
Proof. exact/gcc_closed. Qed.

Lemma gcc_ind x y: x <= y -> x <= s x -> x <= gcc y.
Proof. exact: (@lcl_ind (dual X) (dualf s)). Qed.

Lemma gcc_coidem x: gcc x <= gcc (gcc x).
Proof. move: (@lcl_idem (dual X) (dualf s) x). cbn. exact. Qed. (* TOFIX: hangs without cbn *)

Lemma _gcc_leq: Proper (leq ==> leq) gcc.
Proof. apply/Proper_dual_leq. exact: (@_lcl_leq (dual X) (dualf s)). Qed.

HB.instance Definition _ := isMonotone.Build X X gcc _gcc_leq.
HB.instance Definition _ := isCoClosure.Build X gcc gcc_coext gcc_coidem.

Lemma gcc_below: gcc <= s.
Proof. exact: (@lcl_above (dual X) (dualf s)). Qed.

Lemma gcc_greatest_coclosure (c: coclosure X): c <=[X->X] s -> c <=[X->X] gcc.
Proof. exact: (@lcl_least_closure (dual X) (dualf s) (dualf c)). Qed.

Lemma gcc_geq_iff x y: gcc x <= gcc y <-> gcc x <= y.
Proof. move: (@lcl_leq_iff (dual X) (dualf s) y x). cbn. exact. Qed. (* TOFIX: hangs without cbn *)

Lemma gcc_eqv_iff x y: gcc x ≡ gcc y <-> gcc x <= y /\ gcc y <= x.
Proof. rewrite (@lcl_eqv_iff (dual X) (dualf s)). tauto. Qed.
      
End gcc.
Notation "s ^°" := (gcc s).

#[export] Instance gcc_leq: Proper (leq ==> leq ==> leq) gcc.
Proof.
  move=>s t st x y xy.
  move: (@lcl_leq (dual X) (dualf t) (dualf s) st (y: dual X) (x: dual X) xy).
  cbn.
  exact. (* TOFIX: hangs without cbn *)
Qed.
#[export] Instance gcc_eqv: Proper (eqv ==> eqv ==> eqv) gcc := op_leq_eqv_2.

#[export] Instance gcc_leq': Proper (leq ==> leq) gcc.
Proof. move=>s t st x. exact/gcc_leq. Qed.
#[export] Instance gcc_eqv': Proper (eqv ==> eqv) gcc := op_leq_eqv_1.
(* TOTHINK: cooperation between [gcc_leq] and [gcc_leq'] *)

Lemma gcc_id: types_id^° ≡ types_id.
Proof. exact: (@lcl_id (dual X)). Qed.

(* TOFIX: we have some unfolding problems with monotone functions,
   so that we need to temporarily declare some symbols as opaque *)
Opaque cap.
Proposition gcc_cap s t: t^° ∘ s^° <= s^° ∘ t^° -> (cap s t)^° ≡ t^° ∘ s^°.
Proof.
  move: (@lcl_cup (dual X) (dualf s) (dualf t)).
  rewrite (lcl_eqv' (cup_dualf s t)).
  cbn. exact. 
Qed.
Proposition gcc_cap_iff s t: (cap s t)^° ≡ t^° ∘ s^° <-> t^° ∘ s^° <= s^° ∘ t^°.
Proof.
  move: (@lcl_cup_iff (dual X) (dualf s) (dualf t)).
  rewrite (lcl_eqv' (cup_dualf s t)).
  cbn. exact. 
Qed.
Lemma gcc_const x: (const x)^° ≡ cap (const x) types_id.
Proof.
  move: (@lcl_const (dual X) x).
  rewrite (lcl_eqv' (const_dualf x)).
  cbn. exact. 
Qed.
Transparent cap.

Lemma gcc_idm s: s^°^° ≡ s^°.
Proof.
  move: (@lcl_idm (dual X) (dualf s))=>H.
  etransitivity. 2: exact/H. clear H. 
  cbn=>x. apply: lcl_eqv'. done. 
Qed.

(* TOFIX: idem *)
Opaque top.
Lemma gcc_top: top^° ≡ types_id.
Proof.
  move: (@lcl_bot (dual X)).
  rewrite (lcl_eqv' bot_dualf).
  cbn. exact.
Qed.
Transparent top.

End s.
Notation "s ^°" := (gcc s).

Lemma gcc_ind' {X} {Y: CompleteLattice.type} (s: Y -mon-> Y) (f g: X -> Y):
  f <= g -> f <= s ∘ f -> f <= s^° ∘ g.
Proof. exact: (@lcl_ind' X (dual Y) (dualf s)). Qed.

Proposition gcc_move_l {X} {Y: CompleteLattice.type} (s: Y -mon-> Y) (f: X -mon-> Y) (c: coclosure X):
  f ∘ c <= s ∘ f -> f ∘ c <= s^° ∘ f.
Proof.
  exact: (@lcl_move_l (dual X) (dual Y) (dualf s) (dualf f) (dualf c)).
Qed.

Proposition gcc_move_r {X} {Y: CompleteLattice.type} (s: Y -mon-> Y) (f: Y ⊢ X) (c: coclosure X):
  c ∘ f <= f ∘ s -> c ∘ f <= f ∘ s^° .
Proof.
  exact: (@lcl_move_r (dual X) (dual Y) (dualf s) (dualf f) (dualf c)).
Qed.

Opaque gcc.

(** adjunctions between least closures and greateast coclosures *)

Lemma xadjunction_lcl_gcc1 (X: CompleteLattice.type) (s t: X -mon-> X) (st: adjunction s t):
  forall x y, s^* x <= y -> s^* x <= t^° y. 
Proof. move=>x y H. apply: gcc_ind=>//. apply/st. exact/lcl_closed. Qed.

Lemma xadjunction_lcl_gcc2 (X: CompleteLattice.type) (s t: X -mon-> X) (st: adjunction s t):
  forall x y, x <= t^° y -> s^* x <= t^° y. 
Proof. move=>x y H. apply: lcl_ind=>//. apply/st. exact/gcc_closed. Qed.

Lemma adjunction_lcl_gcc (X: CompleteLattice.type) (s t: X -mon-> X) (st: adjunction s t):
  adjunction s^* t^°.
Proof.
  move=>x y; split=>H.
  - transitivity (s^* x). exact/extensive. exact/xadjunction_lcl_gcc1.
  - transitivity (t^° y). exact/xadjunction_lcl_gcc2. exact/contractive. 
Qed.

HB.instance Definition _ (X: CompleteLattice.type) (s: X ⊣ X) :=
  @isLeftAdjoint.Build X X s^* (radj s)^° (adjunction_lcl_gcc s (radj s) adj). 
HB.instance Definition _ (X: CompleteLattice.type) (s: X ⊢ X) :=
  @isRightAdjoint.Build X X s^° (ladj s)^* (adjunction_lcl_gcc (ladj s) s adj). 
