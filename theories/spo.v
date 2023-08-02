Require Import ssreflect ssrfun ssrbool.
Require Import StrictProp.
Require Export po.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.


(** * partial orders with suprema *)

(*
E: empty
B: binary
C: chains (possibly empty for now)
D: directed (possibly empty for now)
A: all

D=>C=>E
A=>E,B,C,D
B+D=>A

then: Distributive, Heyting, Boole

*)

Variant K := kE | kB | kC | kD | kA.
Canonical Structure K_setoid := Eval hnf in eq_setoid K.
Definition leq_K h k :=
  match h,k with
  | _,kA
  | kE,(kE|kC|kD)
  | kB,kB
  | kC,(kC|kD)
  | kD,kD => True
  | _,_ => False
  end.
Program Canonical Structure K_po := PO.build K leq_K _ _.
Next Obligation. split. by case. by do 3 (case=>//). Qed.
Next Obligation. (case x; case y=>//=); intuition discriminate. Qed.

Definition sigset X := sigT (fun I => (I -> Prop) * (I -> X))%type.
Definition sig2set {X}: sigset X -> (X -> Prop) := fun '(existT _ _ (P,f)) => image f P.
Definition set2sig {X}: (X -> Prop) -> sigset X := fun P => existT _ _ (P,id).
Lemma set2sig2set {X} (P: X -> Prop): sig2set (set2sig P) ≡ P.
Proof. cbv; firstorder congruence. Qed.

Definition args k (X: PO): Type :=
  match k with
  | kE => unit
  | kB => X * X
  | kC => sig (@chain X)
  | kD => sig (@directed X)
  | kA => sigset X
  end.
Definition setof {X: PO} k: args k X -> X -> Prop :=
  match k with
  | kE => fun _ => empty
  | kB => fun p => pair (fst p) (snd p)
  | kC => @proj1_sig _ _
  | kD => @proj1_sig _ _
  | kA => @sig2set X
  end.

Section map_args.
 Context {X Y: PO}.
 Variable f: X -mon-> Y.
 Lemma image_chain P: chain P -> chain (image f P).
 Proof.
   move=>C _ _ [x [Px ->]] [y [Py ->]].
   case: (C x y Px Py)=>H; [left|right]; by apply f.
 Qed.
 Lemma image_directed P: directed P -> directed (image f P).
 Proof.
   move=>D _ _ [x [Px ->]] [y [Py ->]].
   case: (D x y Px Py)=>[z [Pz [xz yz]]].
   exists (f z). split; auto. split; by apply f.
 Qed.
 Definition map_args k: args k X -> args k Y :=
   match k return args k X -> args k Y with
   | kE => id
   | kB => fun '(x,y) => (f x,f y)
   | kC => fun '(exist _ P C) => exist _ (image f P) (image_chain C)
   | kD => fun '(exist _ P D) => exist _ (image f P) (image_directed D)
   | kA => fun '(existT _ _ (P,g)) => existT _ _ (P, f∘g)
   end.
 Lemma setof_map_args k: forall x, setof k (map_args k x) ≡ image f (setof k x).
 Proof.
   case: k=>/=[_|[x x']|[P C]|[P D]|[I [P g]]]//=;
           try firstorder congruence.
   apply image_comp.
 Qed. 
End map_args.

Variant plevel := pN | pE | pB | pF | pEC | pFC | pED.
Canonical Structure plevel_setoid := Eval hnf in eq_setoid plevel.
Definition leq_plevel h k :=
  match h,k with
  | pN,_
  | pE,(pE|pF|pEC|pFC|pED)
  | pB,(pB|pF|pFC)
  | pF,(pF|pFC)
  | pFC,pFC
  | pEC,(pEC|pED|pFC)
  | pED,pED => True
  | _,_ => False
  end.
Program Canonical Structure plevel_po := PO.build plevel leq_plevel _ _.
Next Obligation. split. by case. by do 3 (case=>//). Qed.
Next Obligation. (case x; case y=>//=); intuition discriminate. Qed.

Definition plevel_fun (l: plevel) k: bool :=
  match k,l with
  | kE,(pE|pF|pEC|pFC|pED)
  | kB,(pB|pF|pFC)
  | kC,(pEC|pFC|pED)
  | kD,(pED) => true
  | _,_ => false
  end.
Coercion plevel_fun: plevel >-> Funclass.
Lemma plevel_mon: Proper (leq ==> leq) plevel_fun.
Proof. by case; case=>//=_; case. Qed.

Definition slevel := option plevel.
Definition sN: slevel := Some pN. 
Definition sE: slevel := Some pE. 
Definition sB: slevel := Some pB. 
Definition sF: slevel := Some pF. 
Definition sEC: slevel := Some pEC. 
Definition sFC: slevel := Some pFC. 
Definition sED: slevel := Some pED. 
Definition sA: slevel := None.
Definition slevel_fun (l: slevel) k :=
  match l,k with
  | None,_ => true
  | Some p,k => p k
  end.
Lemma slevel_mon: Proper (leq ==> leq) slevel_fun.
Proof.
  case=>[p|]; case=>[q|]//=.
  move=>pq; case=>//; by apply plevel_mon.
  move=>_; case=>//; by case: p.
Qed.
Definition slevel_fun' (l: slevel): K -> SProp := fun k => is_true' (slevel_fun l k).
Coercion slevel_fun': slevel >-> Funclass.

Definition slevel_of k: slevel :=
  match k with
  | kE => sE
  | kB => sB
  | kC => sEC
  | kD => sED
  | kA => sA
  end.
Lemma has_slevel_of: forall k, slevel_of k k.
Proof. by case. Qed.
Lemma has_slevel (k: K) (l: slevel): slevel_of k <= l -> l k.
Proof.
  move=>H. move: (has_slevel_of k).
  move: (slevel_mon _ _ H k).
  rewrite /slevel_fun'. 
  case (slevel_fun (slevel_of k) k); cbn. 2: by move=>? [].
  move=>E _. by apply eq_true_is_true'. 
Qed.

Section s.
Notation "1" := true.
Notation "0" := false.
Definition slevel_for (f: K -> bool): slevel :=
  if f kA then None
  else match f kE, f kB, f kC, f kD return slevel with
       | _,1,_,1 => sA
       | 0,0,0,0 => sN
       | 1,0,0,0 => sE
       | 0,1,0,0 => sB
       | 1,1,0,0 => sF
       | _,0,1,0 => sEC
       | _,1,1,0 => sFC
       | _,0,_,1 => sED
       end.
End s.
Lemma forall_K (P: K -> Prop): (forall k, P k) <-> P kE /\ P kB /\ P kC /\ P kD /\ P kA.
Proof. split; auto=>?[]; tauto. Qed.
Lemma slevel_adj f (l: slevel): slevel_for f <= l <-> f <= slevel_fun l.
Proof.
  have I: forall b, false <= b <-> True. by case. 
  have I': forall b, b <= true <-> True. by case. 
  have E: forall b, true <= b <-> b. by case. 
  setoid_rewrite forall_K. unfold slevel_for.
  case: (f kA)=>//=. {
    case: l=>//=. cbn; intuition discriminate.
    rewrite !I'. cbn; tauto. 
  }
  case: (f kE); rewrite ?(I,I',E);
    case: (f kB); rewrite ?(I,I',E);
    case: (f kC); rewrite ?(I,I',E);
    case: (f kD); rewrite ?(I,I',E);
  case: l=>[[]|]; cbn; intuition congruence.
Qed.

Definition gsup_ops (X: PO) k := sig (fun sup: args k X -> X => forall x, is_sup (setof k x) (sup x)).
Definition ginf_ops (X: PO) := gsup_ops (dual X).

Module sreduce.
  Section s.
  Variable T: K -> Type.
  Variable f: forall k, option (T k).
  Coercion option_bool {A} (x: option A) := match x with None => false | Some _ => true end.
  Ltac discriminate_levels :=
    (by move=>[] ||
       lazymatch goal with |- context [f ?k] => (* idtac k; *) case: (f k)=>[/=_|]; discriminate_levels end).
  Hypothesis H: forall h k: K, h <= k -> T k -> T h.
  Hypothesis H': T kB -> T kD -> T kA. 
  Definition abstract_reduce: forall k: K, slevel_for f k -> T k.
    unfold slevel_for. case.
    - case (f kE)=>[//|]. 
      case (f kA)=>[v _|]. revert v. by apply H. 
      case (f kD)=>[v _|]. revert v. by apply H. 
      case (f kC)=>[v _|]. revert v. by apply H.
      discriminate_levels. 
    - case (f kB)=>[//|]. 
      case (f kA)=>[v _|]. revert v. by apply H. 
      discriminate_levels. 
    - case (f kC)=>[//|]. 
      case (f kA)=>[v _|]. revert v. by apply H. 
      case (f kD)=>[v _|]. revert v. by apply H. 
      discriminate_levels. 
    - case (f kD)=>[//|]. 
      case (f kA)=>[v _|]. revert v. by apply H. 
      discriminate_levels.
    - case (f kA)=>[//|/=]. 
      case (f kE)=>/=[_|];
        (case (f kB)=>/=[vB|]; [|discriminate_levels]); 
        case (f kC)=>/=[_|]; case (f kD)=>/=[vD _|//]; by auto. 
  Defined.
  End s.
  Section s.
  Variable X: PO.
  Definition reducer: forall h k: K, h <= k -> gsup_ops X k -> gsup_ops X h.
    case; case=>//_ [v H].
    - exists (fun _ => v (exist _ empty chain_empty)). by move=>/=_; apply H. 
    - exists (fun _ => v (exist _ empty directed_empty)). by move=>/=_; apply H. 
    - exists (fun _ => v (set2sig empty)). by move=>/=_; rewrite -{1}(set2sig2set empty); apply H. 
    - exists (fun '(x,y) => v (set2sig (pair x y))). by move=>[??]/=; rewrite -{1}(set2sig2set (pair _ _)); apply H. 
    - exists (fun '(exist _ P C) => v (exist _ P (chain_directed C))). by move=>/=[??]; apply H. 
    - exists (fun '(exist _ P C) => v (set2sig P)). by move=>[P?]/=; rewrite -{1}(set2sig2set P); apply H. 
    - exists (fun '(exist _ P C) => v (set2sig P)). by move=>[P?]/=; rewrite -{1}(set2sig2set P); apply H. 
  Defined.
  Definition reducer': gsup_ops X kB -> gsup_ops X kD -> gsup_ops X kA.
    move=>[cup cup_spec] [dsup dsup_spec].
    unshelve eexists (fun P => dsup (exist _ (sup_closure (sig2set P)) _)).
    (* TOTHINK: how to perform such proofs in a nice conext? *)
    abstract (move=>x y Px Py; exists (cup (x,y)); split; [
    (apply: sc_sup; [|apply cup_spec])=>_[->|->]// |
    move: (proj1 (cup_spec (x,y) (cup (x,y))))=>H; split; apply H=>//=; rewrite /pair; auto ]).
    abstract (move=>P; apply is_sup_closure, dsup_spec).
  Defined.
  Definition reduce f := abstract_reduce _ f reducer reducer'. 
  End s.    
End sreduce.

Module SPO.
 Definition mixin (l: slevel) X (M: Setoid.mixin X) (N: PO.mixin M) :=
   forall k, l k -> gsup_ops (PO.pack N) k.
 Structure type (l: slevel) := pack {
     sort:> Type;
     #[canonical=no] setoid_mix: Setoid.mixin sort;
     #[canonical=no] po_mix: PO.mixin setoid_mix;
     #[canonical=no] mix: mixin l po_mix;
 }.
 Canonical Structure to_PO l (X: type l): PO := PO.pack (po_mix X). 
 Canonical Structure to_Setoid l (X: type l): Setoid := Setoid.pack (setoid_mix X). 
 Notation cast T X := (let X':=X in @pack _ T _ _ (mix X')).
 Notation build l T f :=
   (let X := T%type: PO in
    let M := PO.setoid_mix X in
    let N := PO.mix X in
    @pack l%core T M N (f: forall k, l%core k -> gsup_ops X k)).
 Notation reduced_build l T f := (build l T (sreduce.reduce f)).
 Program Definition weaken (h l: slevel) (X: type l) (hl: h<=l): type h :=
   build h X (fun k hk => mix X k _).
 Next Obligation. move: hk. apply is_true'_leq, slevel_mon, hl. Qed.
End SPO.
Notation SPO := SPO.type.
Canonical SPO.to_PO.
Canonical SPO.to_Setoid.
#[reversible] Coercion SPO.to_Setoid: SPO >-> Setoid.
#[reversible] Coercion SPO.to_PO: SPO >-> PO.
#[reversible] Coercion SPO.sort: SPO >-> Sortclass.
Definition gsup {l} {X: SPO l} k kl: args k X -> X := proj1_sig (SPO.mix X k kl).
Arguments gsup {_ _}. 
Definition gsup_spec {l} {X: SPO l} {k kl}: forall (x: args k X), is_sup (setof k x) (gsup k kl x) :=
  proj2_sig (SPO.mix X k kl).
Lemma leq_gsup {l} {X: SPO l} k kl x (y: X): setof k x y -> y <= gsup k kl x.
Proof. apply leq_is_sup, gsup_spec. Qed.

Lemma discriminate {P: Type}: sEmpty -> P.
Proof. by []. Qed.

Program Canonical Structure bool_spo := 
  SPO.build sF bool 
    (fun k => match k with
           | kE => fun _ => exist _ (fun _ => false) _
           | kB => fun _ => exist _ (fun '(x,y) => orb x y) _
           | kC | kD | kA  => discriminate
           end).
Next Obligation. by case. Qed.
Next Obligation. 
  move=>c/=. rewrite forall_pair. cbn.
  rewrite Bool.implb_orb_distrib_l.
  apply Bool.andb_true_iff.
Qed.

Program Canonical Structure Prop_spo :=
  SPO.reduced_build sA Prop
    (fun k => match k with
           | kE => Some (exist _ (fun _ => False) _)
           | kB => Some (exist _ (fun '(p,q) => p\/q) _)
           | kC => None          (* generated *)
           | kD => None          (* generated *)
           | kA => Some (exist _ (fun '(existT _ _ (P,f)) => exists2 i, P i & f i) _)
           end).
Next Obligation. firstorder. Qed.
Next Obligation. cbv; firstorder subst; eauto. Qed.
Next Obligation. destruct x as [I [P f]]; cbv. firstorder subst; eauto. Qed.

Canonical Structure fst_mon {X Y: PO}: (prod X Y)-mon->X :=
  PO.build_morphism fst (fun p q pq => proj1 pq).
Canonical Structure snd_mon {X Y: PO}: (prod X Y)-mon->Y :=
  PO.build_morphism snd (fun p q pq => proj2 pq).

Program Canonical Structure prod_spo {l} (X Y: SPO l) :=
  SPO.build l (X*Y) (fun k kl => exist _ (fun F => (gsup k kl (map_args fst k F), gsup k kl (map_args snd k F))) _).
(* alternatively, via [dprod_sup] below, with [A=bool] *)
Next Obligation.
  apply prod_sup; split; (eapply Proper_is_sup; [apply eqv_covered|reflexivity|apply gsup_spec]).
  all: by rewrite setof_map_args. 
Qed.


Definition app {A} {X: A -> PO} a: (forall a, X a)-mon->X a :=
  PO.build_morphism (fun f => f a) (fun f g fg => fg a).

(** SPOs on dependent products *)
Program Canonical Structure dprod_spo {A l} (X: A -> SPO l) :=
  SPO.build l (forall a, X a) (fun k kl => exist _ (fun F a => gsup k kl (map_args (app a) k F)) _). 
Next Obligation.
  apply dprod_sup=>a. eapply Proper_is_sup.
  2: reflexivity. 2: apply: gsup_spec.
  apply eqv_covered. by rewrite setof_map_args. 
Qed.

Program Definition proj1_sig_mon {X: PO} (P: X -> Prop): sig P -mon-> X :=
  PO.build_morphism (@proj1_sig _ _) _.
Next Obligation. by []. Qed.

(** sub-SPOs *)
Section sub.
 Context {l} {X: SPO l}.
 Definition sup_closed' (P: X -> Prop) :=
   forall k: K, forall kl: l k, forall x, setof k x <= P ->  P (gsup k kl x).
 Lemma sup_closed_sup_closed': sup_closed <= sup_closed'. 
 Proof. move=>P H k kl x Hx. apply: H. apply Hx. apply gsup_spec. Qed.
 #[export] Instance sup_closed'_eqv: Proper (eqv==>eqv) sup_closed'.
 Proof. apply Proper_half=>P Q H HP k kl x E. apply H. apply HP. by rewrite H. Qed.
 Program Definition sig_spo P (Psup: sup_closed' P) := 
   SPO.build l (sig P) (fun k kl => exist _ (fun F => exist _ (gsup k kl (map_args (proj1_sig_mon P) k F)) _) _). 
 Next Obligation.
   apply: Psup. rewrite setof_map_args. 
   by move=>_ [[x Px] [_ ->]]. 
 Qed.
 Next Obligation.
   apply kern_sup=>/=. eapply Proper_is_sup.
   2: reflexivity. 2: apply: gsup_spec.
   apply eqv_covered. by rewrite setof_map_args. 
 Qed.
End sub.

(** SPOs from retractions (and thus isomorphisms given the induced order on [A]) *)
Section c.
 Context {A: Type} {l} (X: SPO l).
 Variable r: A->X.               (* retraction *)
 Variable i: X->A.               (* section *)
 Hypothesis ri: r∘i ≡ id. 
 Program Let r': kern_po X r -mon-> X := PO.build_morphism r _.
 Next Obligation. by []. Qed.
 Program Definition retract_spo := 
   SPO.build l (kern_po X r) (fun k kl => exist _ (fun x => i (gsup k kl (map_args r' k x))) _).
 Next Obligation.
   apply kern_sup. eapply Proper_is_sup. 2: apply: ri. 2: apply: gsup_spec.
   apply eqv_covered. by rewrite setof_map_args.
 Qed.
End c.
Arguments retract_spo [_ _] _ [_ _]. 

(** altogether, we get general sub-SPOs  *)
Section c.
 Context {A: Type} {l} {X: SPO l} (P: X -> Prop).
 Variable r: A->sig P.
 Variable i: sig P->A.
 Hypothesis ri: r∘i ≡ id. 
 Hypothesis Psup: sup_closed' P.
 Definition sub_spo: SPO l := retract_spo (sig_spo Psup) ri. 
End c. 

(** the SPO of monotone functions *)
Lemma po_morphism_as_sig {X Y: PO}:
  (fun f: X-mon->Y => exist (Proper (leq ==> leq)) (PO.body f) (@body_leq _ _ f))
    ∘ (fun f: sig (Proper (leq ==> leq)) => PO.build_morphism _ (proj2_sig f)) ≡ id.
Proof. by case. Qed.
Section s.
 Context {X: PO} {l} {Y: SPO l}.
 Lemma sup_closed'_monotone: sup_closed' (Proper (@leq X ==> @leq Y)).
 Proof.
   move=>k kl P HP x y xy.
   apply gsup_spec=>z Hz. apply setof_map_args in Hz as [f [Hf ->]].
   transitivity (f y). apply (HP _ Hf _ _ xy). apply leq_gsup. 
   apply setof_map_args. by exists f.
 Qed.
 Canonical Structure mon_spo: SPO l :=
   SPO.cast (X-mon->Y) (sub_spo (@po_morphism_as_sig X Y) sup_closed'_monotone).
End s.


Class lower {X: PO} (h k: X): Prop := Lower: h <= k.
Infix "<<" := lower (at level 70).
#[export] Instance PreOrder_lower {X}: PreOrder (@lower X).
Proof. apply PreOrder_leq. Qed.
Lemma lower_trans {X: PO} (k h l: X) (kh: k<<h) (hl: h<<l): k<<l.
Proof. etransitivity; eassumption. Qed.
Ltac solve_lower :=
  solve [ reflexivity | assumption |
          match goal with H: ?h << ?l |- ?k << ?l => exact: (@lower_trans _ k h l I H) end].
#[export] Hint Extern 0 (lower _ _) => solve_lower: typeclass_instances.

(*
Goal forall l, sA<<l -> sE <<l.
  intros l L. solve_lower. 
Qed.
*)

(* TOTHINK: should we move this theory directly to GPOs ? *)

Definition bot {l} {X: SPO l} {L: sE<<l}: X := gsup kE (has_slevel kE l L) tt.
Definition cup {l} {X: SPO l} {L: sB<<l} (x y: X): X := gsup kB (has_slevel kB l L) (x,y).
Definition csup {l} {X: SPO l} {L: sEC<<l} (P: X -> Prop) (C: chain P): X := gsup kC (has_slevel kC l L) (exist _ P C).
Definition dsup {l} {X: SPO l} {L: sED<<l} (P: X -> Prop) (D: directed P): X := gsup kD (has_slevel kD l L) (exist _ P D). 
Definition isup {l} {X: SPO l} {L: sA<<l} {I} (P: I -> Prop) (f: I -> X): X := gsup kA (has_slevel kA l L) (existT _ I (P,f)). 
Notation sup P := (isup P id). 
Infix "⊔" := cup (left associativity, at level 50). 
Arguments csup {_ _ _}. 
Arguments dsup {_ _ _}. 

Lemma is_sup_bot {l} {X: SPO l} {L: sE<<l}: @is_sup X bot bot.
Proof. apply: gsup_spec. Qed.
Lemma is_sup_cup {l} {X: SPO l} {L: sB<<l} (x y: X): is_sup (pair x y) (x ⊔ y).
Proof. apply: gsup_spec. Qed.
Lemma is_sup_csup {l} {X: SPO l} {L: sEC<<l} (P: X -> Prop) C: is_sup P (csup P C).
Proof. apply: gsup_spec. Qed.
Lemma is_sup_dsup {l} {X: SPO l} {L: sED<<l} (P: X -> Prop) D: is_sup P (dsup P D).
Proof. apply: gsup_spec. Qed.
Lemma is_sup_isup {l} {X: SPO l} {L: sA<<l} I P (f: I -> X): is_sup (image f P) (isup P f).
Proof. apply: gsup_spec. Qed.
Lemma is_sup_sup {l} {X: SPO l} {L: sA<<l} (P: X -> Prop): is_sup P (sup P).
Proof. rewrite -{1}(image_id P). apply: is_sup_isup. Qed.

Lemma leq_csup {l} {X: SPO l} {L: sEC<<l} (P: X -> Prop) C x: P x -> x <= csup P C. 
Proof. move=>Px. by apply: leq_gsup. Qed.
Lemma leq_dsup {l} {X: SPO l} {L: sED<<l} (P: X -> Prop) D x: P x -> x <= dsup P D. 
Proof. move=>Px. by apply leq_gsup. Qed.
Lemma leq_isup {l} {X: SPO l} {L: sA<<l} I (P: I -> Prop) (f: I -> X) i: P i -> f i <= isup P f. 
Proof. move=>Pi. by apply leq_gsup=>/=; auto. Qed.
Lemma leq_sup {l} {X: SPO l} {L: sA<<l} (P: X -> Prop) x: P x -> x <= sup P. 
Proof. apply: leq_isup. Qed.

Lemma bot_spec {l} {X: SPO l} {L: sE<<l} (z: X): bot <= z <-> True.
Proof. rewrite is_sup_bot. firstorder. Qed.
Lemma leq_bot {l} {X: SPO l} {L: sE<<l} (z: X): bot <= z.
Proof. by apply bot_spec. Qed.
#[export] Hint Extern 0 (bot <= _)=> apply: leq_bot: core.

Lemma cup_spec {l} {X: SPO l} {L: sB<<l} (x y z: X): x ⊔ y <= z <-> x <= z /\ y <= z.
Proof. rewrite is_sup_cup /pair; intuition subst; auto. Qed.

Lemma cupA {l} {X: SPO l} {L: sB<<l} (x y z: X): x ⊔ (y ⊔ z) ≡ x ⊔ y ⊔ z. 
Proof. apply: from_above=>t. rewrite 4!cup_spec. tauto. Qed.
(* TODO: etc... *)

Lemma csup_sup {l} {X: SPO l} {L: sA<<l} P C: csup P C ≡[X] sup P.
Proof. apply: supU. apply is_sup_csup. apply is_sup_sup. Qed.
Lemma dsup_sup {l} {X: SPO l} {L: sA<<l} P D: dsup P D ≡[X] sup P.
Proof. apply: supU. apply is_sup_dsup. apply is_sup_sup. Qed.

Lemma csup_bot {l} {X: SPO l} {L: sEC<<l} C: csup bot C ≡[X] bot.
Proof. apply: supU. apply is_sup_csup. apply is_sup_bot. Qed.
Lemma dsup_bot {l} {X: SPO l} {L: sED<<l} D: dsup bot D ≡[X] bot.
Proof. apply: supU. apply is_sup_dsup. apply is_sup_bot. Qed.
Lemma sup_bot {l} {X: SPO l} {L: sA<<l}: sup bot ≡[X] bot.
Proof. apply: supU. apply is_sup_sup. apply is_sup_bot. Qed.

Lemma sup_pair {l} {X: SPO l} {L: sA<<l} (x y: X): sup (pair x y) ≡ x ⊔ y.
Proof. apply: supU. apply is_sup_sup. apply is_sup_cup. Qed.

Lemma directed_sup_closure {l} {X: SPO l} {L: sB<<l} (P: X -> Prop): directed (sup_closure P).
Proof.
  (* TODO: use in [reducer.reduce] *)
  move=>x y Px Py. exists (x⊔y); split. 2: by apply cup_spec.
  apply sc_sup with (pair x y). 2: apply is_sup_cup.
  by move=>z [->|->].
Qed.
Corollary sup_dsup {l} {X: SPO l} {L: sA<<l} (P: X -> Prop):
  sup P ≡ dsup (sup_closure P) (directed_sup_closure (P:=P)).
Proof. rewrite dsup_sup. apply: supU. apply is_sup_sup. apply is_sup_closure, is_sup_sup. Qed.


(** more SPO instances *)

(*
  option (l -> sE+l)

  lex_prod? (E,_->E; B,E->B; C,C->C; D,D->D; A,A->A)
  sequential_sum? (E,_->E; B,B->B; others need emptyness checking)
  parallel_sum? no

  list  (E,B->B)
 *)
