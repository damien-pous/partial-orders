Require Import ssreflect ssrfun ssrbool.
From PartialOrders Require Import cs_setoid.

(* we are lucky here... *)
Check fun A B (X: Setoid) (f: B -> X) (g: A -> B) =>
        unify (kern_setoid (kern_setoid X f) g) (kern_setoid X (f ∘ g)).

Fail Check fun f: bool -eqv-> bool => f ≡ id. 
Fail Check fun f: bool -eqv-> bool => f ≡ @id bool. 
Fail Check fun f: bool -eqv-> bool => id ≡ f. 
Check fun f: bool -eqv-> bool => @id bool ≡ f. 
Check fun f: bool -eqv-> bool => f ≡ Datatypes.id. 
Fail Check fun f: bool -eqv-> bool => Datatypes.id ≡ f. 
Check fun f: bool -eqv-> bool => id ≡[bool->bool] f. 
Check fun f: bool -eqv-> bool => f ≡[bool->bool] id. 
Check fun f: bool -eqv-> bool => f ∘ f. 
Check fun f: bool -eqv-> bool => f ∘ id ∘ f. 

Goal forall X: Setoid, forall f g h: X -eqv-> X, f ≡ g -> f ∘ g ≡ h.
Proof.
  intros * H.
  Fail rewrite H -H.
  change (f ∘ g ≡[_-eqv->_] h).
  rewrite H -H.  
Abort.

Goal forall X, forall h: X-eqv->X, forall x y: X, x ≡ y -> const x ≡ h.
Proof. intros * H. rewrite H -H. Abort. 
Goal forall X, forall h: X-eqv->X, forall x y: X, x ≡ y -> Setoid.const x ≡ h.
Proof. intros * H. rewrite H -H. Abort. 

Check (bool * (unit -> dual bool) * sig (fun b: bool=> b=true)  (* * True *))%type: Setoid. 
Check (bool -> bool -> Prop): Setoid. 
Check (bool -eqv-> bool -eqv-> Prop): Setoid. 
