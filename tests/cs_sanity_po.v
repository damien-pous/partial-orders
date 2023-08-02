Require Import ssreflect ssrfun ssrbool.
From PartialOrders Require Import cs_po.

Goal nat -> True <= True.
  move=>n x.                     (* requires Eval hnf/cbn in [Prop_po] *)
Abort.

Goal nat -> (true,false) <= (false,true) -> True.
  move=>n [/=a b].
Abort.

Goal forall f: nat -> Prop, f ≡ f.
  move=>f x.
Abort.
Goal forall f: nat -> Prop, f <= f.
  move=>f x.                     (* requires Eval hnf/cbn in [dprod_po] *)
Abort.


(* lucky here too *)
Check fun A B (X: PO) (f: B -> X) (g: A -> B) =>
        unify (kern_po (kern_po X f) g) (kern_po X (f ∘ g)).



Check forall X Y: PO, forall f: X -> Y, f ≡ f.
Check forall X Y: PO, ((X->Y) : Setoid).



Goal forall X: PO, forall x y: X, x <= y -> x <= y.
Proof. intros * ->. Abort.
Goal forall X: PO, forall x y: X, x ≡ y -> x <= y.
Proof. intros * ->. Abort. 
Goal forall X: PO, forall x y: nat -> X, x <= y -> x <= y.
Proof. intros * ->. Abort.
Goal forall X: PO, forall x y: nat -> X, x ≡ y -> x <= y.
Proof. intros * ->. Abort. 
Goal forall x y: nat -> Prop, x <= y -> x <= y.
Proof. intros * ->. Abort.
Goal forall x y: nat -> Prop, x ≡ y -> x <= y.
Proof. intros * ->. Abort. 


Goal forall X: Setoid, forall f g h: X -eqv-> X, f ≡ g -> f ∘ g ≡ h.
  Fail intros * ->.
Abort.
Goal forall X: Setoid, forall f g h: X -eqv-> X, f ≡ g -> Setoid.comp f g ≡ h.
  intros * ->.
Abort.
Goal forall X: PO, forall f g h: X -eqv-> X, f ≡ g -> Setoid.comp f g <= h.
  intros * ->.
Abort.
Goal forall X: PO, forall f g h: X -mon-> X, f ≡ g -> PO.comp f g ≡ h.
  intros * ->.
Abort.
Goal forall X: PO, forall f g h: X -mon-> X, f ≡ g -> Setoid.comp f g <= h.
  Fail intros * ->.
  intros * H. rewrite (H: f≡[_-eqv->_]g). 
Abort.
Goal forall X: PO, forall f g h: X -mon-> X, f <= g -> f ∘ g <=[_-mon->_] h.
  intros * ->.
Abort. 
Goal forall X: PO, forall f g h: X -mon-> X, f ≡ g -> f ∘ g <=[_-mon->_] h.
  intros * ->.
Abort. 

Goal forall f g: nat -> Prop, f ≡ g -> f ≡ g.
  intros * ->.
Abort.
Goal forall f g: nat -> Prop, f <= g -> f <= g.
  intros * ->.
Abort.
Goal forall f g: nat -> Prop, f ≡ g -> f <= g.
  intros * ->.
Abort.


Check bool: Setoid. 
Check bool: PO. 

Eval cbn in (true,false) <= (false,true). 
Eval cbn in ((true,false): lex_prod _ _) <= (false,true). 
Eval cbn in ((true,false): lex_prod _ (dual _)) <= (false,true). 

Goal forall (x: bool * (bool -> bool) * {y: bool | y=true}), x <= x.
  intros [[x f] [p ?]]. cbv.
Abort.
Goal forall (x: bool * sig (fun b: bool=> b=true)), x <= x.
Abort.
(* need irrelevant po *)
Fail Check forall (x: bool * forall b: bool, bool * True), x <= x.

Check fun X: PO => dual X: PO. 
Check fun (X: PO) (x: dual X) => x <= x. 
Check fun (X: PO) (f: X-mon->X) => f <= f. 
Check fun (X: PO) (f: X-mon->X) => f ≡ f. 
Check fun (X: PO) (f: X-eqv->X) => f ≡ f. 
Check fun (X: PO) (f: X-eqv->X) => f <= f. 
Check fun (X: Setoid) (f: X-eqv->X) => f ≡ f. 
Check fun (X: PO) (f: X-mon->dual X) => f <= f. 
Check fun (X: PO) (f: dual X-mon->X) => f <= f. 
Check fun (X: PO) (f: dual X-mon->dual X) => f <= f. 

Check fun (X: PO) (f: X-mon->X) => f∘f <= f. 
Check fun (X: PO) (f: X-mon->X) => f∘f ≡ f. 
Check fun (X: PO) (f: X-eqv->X) => f∘f <= f. 
Check fun (X: PO) (f: X-eqv->X) => f∘f ≡ f. 
Check fun (X: PO) (f: X->X) => f∘f <= f. 
Check fun (X: PO) (f: X->X) => f∘f ≡ f. 
Check fun (X: Setoid) (f: X-eqv->X) => f∘f ≡ f. 
Check fun (X: Setoid) (f: X->X) => f∘f ≡ f. 

Check fun (X: PO) (f: X-mon->X) => id <= f. 
Check fun (X: PO) (f: X-mon->X) => Datatypes.id <= f. 
Fail Check fun (X: PO) (f: X-mon->X) => id <=[_->_] f. 
Check fun (X: PO) (f: X-mon->X) => id <=[X->X] f. 
Fail Check fun (X: PO) (f: X-mon->X) => id ≡ f. 
Check fun (X: PO) (f: X-eqv->X) => id <= f. 
Fail Check fun (X: PO) (f: X-eqv->X) => id ≡ f. 
Check fun (X: PO) (f: X->X) => id <= f. 
Fail Check fun (X: PO) (f: X->X) => id ≡ f. 
Check fun (X: Setoid) (f: X-eqv->X) => id ≡ f. 
Check fun (X: Setoid) (f: X->X) => id ≡ f. 

Section s.
  Variable X: Setoid.
  Variable Y: PO.
  Check forall f g: X -eqv-> X, f ∘ g ≡ id.
  Check forall f g: bool -eqv-> bool, f ∘ g ≡ id.
  Check forall f g: bool -mon-> bool, f ∘ g ≡ id.
  Check forall f g: X -eqv-> Y, forall h: Y-eqv->X, f ∘ h ∘ g ≡ g.
  Check forall f g: Y -eqv-> Y, forall h: Y-mon->Y, f ∘ h ∘ g ≡ g.
  Check forall f g: Y -eqv-> Y, forall h: Y-mon->Y, f ∘ h ∘ g <= g.
  Check forall f g: Y -mon-> Y, forall h: Y-mon->Y, f ∘ h ∘ g <= g.
  Check forall f g: Y -mon-> Y, forall h: Y-eqv->Y, f ∘ h ∘ g ≡ g.
  Check forall f: Y -eqv-> Y, forall g: Y-mon->Y, f ∘ g ≡ id.
  Check forall f: Y -mon-> Y, forall g: Y-eqv->Y, f ∘ g ≡ id.
End s.

Goal forall X, forall f: X -eqv-> X, forall x y: X, x≡y -> f (f x) ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  

Goal forall X, forall f: X -eqv-> X, forall x y: X, x≡y -> (f ∘ f) x ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  


Check fun X => unify (@inf_closed X) (@sup_closed (dual X)).
