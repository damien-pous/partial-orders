From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Export hb_po hb_categories.

(* kernel compositions should behave well:
   taking two successive kernels should be definitionally equivalent to taking a composite one
   crucial from some inheritance paths to be equivalent, e.g.,
   (X-eqv->Y) -> (sig (Proper ...)) -> X->Y
          \____________________________/
 *)
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


Goal forall X (f: X -eqv-> X) (x y: X), x≡y -> (f ° f) x ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  
Goal forall X: Setoid.type, forall f g: X-eqv->X, forall x y: X, f ≡ g -> x ≡ y -> f x ≡ g y /\ f ° const x ≡[X-eqv->X] const (g y) /\ const x ≡[X->X] const y.
Proof.
  intros X f g x y fg xy. repeat split.
  Fail rewrite fg.              (* fair enough *)
  rewrite xy. by apply: fg.
  2: by rewrite xy.
  rewrite fg.                   (* need the category notation *)
  Fail by rewrite xy.                (* was working before, thanks to [const_eqv'] *)
Abort.  
Goal forall X: Setoid.type, forall f g: X-eqv->X, f ≡ g -> f ° g ≡ g ° g.
Proof. by move=>X f g ->. Abort.


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

Fail Check forall (X: PO.type) (f: X -mon-> X), id ° f <= id. 
Check forall (X: PO.type) (f: X -eqv-> X), f <= id.
Fail Check forall (X: PO.type) (f: X -mon-> X), f <= id.
Fail Check forall (X: PO.type) (f: X -mon-> X), f ≡ id.
Fail Check forall (X: PO.type) (f: X -mon-> X), id ≡ f. 

(* this one fails, but we have the three alternatives below *)
Fail Check forall (X: PO.type) (f: X -mon-> X), id <= f. 
Check forall (X: PO.type) (f: X -mon-> X), po_id <= f. 
Fail Check forall (X: PO.type) (f: X -mon-> X), id <=[X-mon->X] f.
Fail Check forall (X: PO.type) (f: X -mon-> X), id ≦ f. 

Fail Goal forall X: PO.type, forall f g h: X-mon->X, f ≡ g -> f ° g ≡ h.
Fail Qed.
(* Proof. intros * H. rewrite H. rewrite -H. Abort. *)
Goal forall (X: PO.type) (f: X -mon-> X) (x y: X), x≡y -> y<=x -> f (f x) <= (f (f x)).
Proof. intros * H H'. rewrite {1}H H'. reflexivity. Abort.
Fail Goal forall (X: PO.type) (f g: X -mon-> X) (x y: X), x≡y -> y<=x -> f <= g -> (f ° f) x <= (f ° f) x /\ f ° f <= g ° g.
Fail Qed.
(* Proof. *)
(*   intros * H H' H''. rewrite {1}H H'. split=>//. *)
(*   rewrite {2}H''. *)
(* Abort. *)



Check fun f: bool -eqv-> bool => f ≡ id. 
Check fun f: bool -eqv-> bool => id ≡ f. 
Fail Check fun f: bool -eqv-> bool => id ≡[bool->bool] f. (* fair enough *)
Check fun f: bool -eqv-> bool => f ° f. 
Check fun f: bool -eqv-> bool => f ° id ° f. 
Goal forall X, forall f g h: X -eqv-> X, f ≡ g -> f ° g ≡ h.
Proof. intros * H. rewrite H -H. Abort.

Goal forall X, forall f g h: X -eqv-> X, f ≡ g -> f ° g ≡ h.
  intros * ->.
Abort.
