From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Export hb_spo hb_categories.

(* sanity checks for the HB based library
   TODO: cleanup, reorder, remove duplicates *)

(* kernel compositions should behave well:
   taking two successive kernels should be definitionally equivalent to taking a composite one
   crucial from some inheritance paths to be equivalent, e.g.,
   (X-eqv->Y) -> (sig (Proper ...)) -> X->Y
          \____________________________/
 *)
Check fun (X: Setoid.type) (f g: X -> X) =>
        unify_setoids
          (kernel (X:=kernel g) f)
          (kernel (types_comp g f)).
Check fun (X: PO.type) (f g: X -> X) =>
        unify_pos
          (kernel (X:=kernel g) f)
          (kernel (types_comp g f)).
Check unify_pos (discrete unit) (trivial unit). 


Check fun X: Type => trivial X: Setoid.type.
Fail Check fun X: Type => discrete X: Setoid.type. (* should indeed fail *)
Check fun X: Setoid.type => discrete X: PO.type.
Check fun X: Type => discrete (trivial X): PO.type.
Check fun X: Type => trivial X: PO.type.

Goal forall a b: nat*Prop*unit, a≡b.
  move=>[[a a'] a''] [[b b'] b'']/=. cbn.
Abort.
Goal forall (x: nat * sig (fun b: bool=> b=true)), x ≡ x.
  intros [x [b ?]]. cbn.
Abort.
Goal forall (x: nat * (bool -> nat) * {y: nat | y=5}), x ≡ x.
  intros [[x f] [p ?]]. cbv.
Abort.
Check forall X: Setoid.type, forall f: X -eqv-> prod nat X, f ≡ f.
(* below: need setoid of irrelevant propositions *)
(* Goal forall a b: nat*True, a≡b. *)
(*   move=>[a a'] [b b']/=. cbn. *)
(* Abort. *)
(* Check forall (x: nat * forall b: bool, nat + (b=true)), x ≡ x. *)
Goal forall X: Setoid.type, forall f g: X-eqv->X, forall x y: X, f ≡ g -> x ≡ y -> f x ≡ g y /\ types_comp f (const x) ≡[X->X] const (g y) /\ const x ≡[X->X] const y.
Proof.
  intros X f g x y fg xy. repeat split.
  rewrite xy. by apply fg.
  2: by rewrite xy. 
  Fail rewrite fg.            (* dommage *)
Abort.  


Check forall X (f: X -eqv-> X), f ° f ≡ f.
Check forall X (f: X -eqv-> X), id ° f ≡ id. 
Check forall X (f: X -eqv-> X), f ≡ id.
Check fun X => (id: X -eqv-> X). 
Check forall X (f: X -eqv-> X), id ≡ f. 
Goal forall X, forall f g h: X-eqv->X, f ≡ g -> f ° g ≡ h.
Proof. intros * H. rewrite H. rewrite -H. Abort.
Goal forall X (f: X -eqv-> X) (x y: X), x≡y -> f (f x) ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  
Goal forall X (f: X -eqv-> X) (x y: X), x≡y -> (f ° f) x ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  
Goal forall X: Setoid.type, forall f g: X-eqv->X, forall x y: X, f ≡ g -> x ≡ y -> f x ≡ g y /\ f ° const x ≡[X-eqv->X] const (g y) /\ const x ≡[X->X] const y.
Proof.
  intros X f g x y fg xy. repeat split.
  Fail rewrite fg.              (* fair enough *)
  rewrite xy. by apply fg.
  2: by rewrite xy.
  rewrite fg.
  by rewrite xy.                (* thanks to [const_eqv'] *)
Abort.  
Goal forall X: Setoid.type, forall f g: X-eqv->X, f ≡ g -> f ° g ≡ g ° g.
Proof. by move=>X f g ->. Abort.

Check fun f: bool -eqv-> bool => f ≡ id. 
Check fun f: bool -eqv-> bool => f ≡ types_id. 
Check fun f: bool -eqv-> bool => id ≡ f. 
Fail Check fun f: bool -eqv-> bool => types_id ≡ f. 
Check fun f: bool -eqv-> bool => @types_id bool ≡ f. 
Check fun f: bool -eqv-> bool => f ≡ Datatypes.id. 
Fail Check fun f: bool -eqv-> bool => Datatypes.id ≡ f. 
Check fun f: bool -eqv-> bool => @Datatypes.id bool ≡ f. 
Fail Check fun f: bool -eqv-> bool => id ≡[bool->bool] f. (* fair enough *)
Check fun f: bool -eqv-> bool => f ≡[bool->bool] types_id. 
Check fun f: bool -eqv-> bool => f ° f. 
Check fun f: bool -eqv-> bool => f ° id ° f. 

Goal forall X, forall f g h: X -eqv-> X, f ≡ g -> f ° g ≡ h.
Proof. intros * H. rewrite H -H. Abort.

Goal forall X, forall h: X-eqv->X, forall x y: X, x ≡ y -> const x ≡ h.
Proof. intros * H. rewrite H -H. Abort. 

Check bool: Setoid.type. 
Check (bool * (unit -> dual bool) * sig (fun b: bool=> b=true)  (* * True *))%type: Setoid.type. 
Check (bool -> bool -> Prop): Setoid.type. 
Check (bool -eqv-> bool -eqv-> Prop): Setoid.type. 

Goal forall f: nat -> Prop, f ≡ f.
  move=>f x.
Abort.
Goal forall X, forall f g h: X -eqv-> X, f ≡ g -> f ° g ≡ h.
  intros * ->.
Abort.
Goal forall X, forall f g h: X -eqv-> X, f ≡ g -> types_comp f g ≡ h.
  Fail intros * ->.              (* fair enough *)
Abort.
Goal forall f g: nat -> Prop, f ≡ g -> f ≡ g.
  intros * ->.
Abort.

Section s.
  Variable X: Setoid.type.
  Check forall f g: X -eqv-> X, f ° g ≡ id.
  Check forall f g: bool -eqv-> bool, f ° g ≡ id.
End s.

Goal forall X, forall f: X -eqv-> X, forall x y: X, x≡y -> f (f x) ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  

Goal forall X, forall f: X -eqv-> X, forall x y: X, x≡y -> (f ° f) x ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  




Goal forall (X: PO.type) (x: nat -> X), x ≡ x.
  intros * n.  
Abort.
Goal forall A (X: A -> PO.type) (x: forall a, X a), x ≡ x. 
  intros * a.
Abort.
Check fun X: PO.type => @types_id X: X-mon->X. 
Check fun (X: PO.type) (f g: X -mon-> X) => types_comp f g: X -mon->X. 
Check fun (X: PO.type) (f g: X -mon-> X) => f: X -eqv->X. 


Check unify (tt <= tt) True.

Check forall (X: PO.type) (f: X -mon-> X), id ° f <= id. 
Check forall (X: PO.type) (f: X -eqv-> X), f <= id.
Check forall (X: PO.type) (f: X -mon-> X), f <= id.
Check forall (X: PO.type) (f: X -mon-> X), f ≡ id.
Check forall (X: PO.type) (f: X -mon-> X), id ≡ f. 

(* this one fails, but we have the three alternatives below *)
Fail Check forall (X: PO.type) (f: X -mon-> X), id <= f. 
Check forall (X: PO.type) (f: X -mon-> X), po_id <= f. 
Check forall (X: PO.type) (f: X -mon-> X), id <=[X-mon->X] f.
Check forall (X: PO.type) (f: X -mon-> X), id ≦ f. 

Goal forall X: PO.type, forall f g h: X-mon->X, f ≡ g -> f ° g ≡ h.
Proof. intros * H. rewrite H. rewrite -H. Abort.
Goal forall (X: PO.type) (f: X -mon-> X) (x y: X), x≡y -> y<=x -> f (f x) <= (f (f x)).
Proof. intros * H H'. rewrite {1}H H'. reflexivity. Abort.  
Goal forall (X: PO.type) (f g: X -mon-> X) (x y: X), x≡y -> y<=x -> f <= g -> (f ° f) x <= (f ° f) x /\ f ° f <= g ° g.
Proof.
  intros * H H' H''. rewrite {1}H H'. split=>//.
  rewrite {2}H''. 
Abort.


(** complexity issue *)

Time Goal
  let T := ((bool -> bool -> bool -> bool -> Prop)) in
  let T' := (T: PO.type) in
  let T'' := (T: SPO.type sA) in
  let X := ((T-mon->T): SPO.type _) in (* fast *)
  let X' := ((T'-mon->T'): SPO.type _) in (* fast *)
  let X'' := ((T''-mon->T''): SPO.type _) in (* fast *)
  True.
intros.
cbn in *.
Abort.


(** * levels  *)

Check fun l: level => unify (types_comp l inl) (suplevel l). 
Check fun l: level => unify (types_comp l inr) (inflevel l). 
Check fun l: level => unify (types_comp (dual_level l) inr) (types_comp l inl). 
Fail Check fun l: level => unify (dual_level (dual_level l)) l. (* dommage, but ok with behaviour below *)
Check fun (l: level) x => unify (dual_level (dual_level l) x) (l x). 
Fail Check fun l => unify (lA << l) (lA << dual_level l). (* dommage *)

Goal forall l, sA<<l -> sE <<l.
  intros l L. solve_lower. 
Qed.

(** * GPOs  *)

Compute fun P: (nat -> nat -> Prop) -> Prop => inf P. (* nice thanks to indexed sups *)
Compute fun P: nat -> nat -> Prop => P⊔P.
Compute fun P: nat -> nat -> Prop => P⊓P.
