Require Import ssreflect ssrfun ssrbool.
From PartialOrders Require Import setoid.

(* we are lucky here... *)
Check fun A B (X: Setoid) (f: B -> X) (g: A -> B) =>
        unify (kern_setoid (kern_setoid X f) g) (kern_setoid X (f ° g)).

Fail Check fun f: nat -eqv-> nat => f ≡ id. 
Fail Check fun f: nat -eqv-> nat => f ≡ @id nat. 
Fail Check fun f: nat -eqv-> nat => id ≡ f. 
Check fun f: nat -eqv-> nat => @id nat ≡ f. 
Check fun f: nat -eqv-> nat => f ≡ Datatypes.id. 
Fail Check fun f: nat -eqv-> nat => Datatypes.id ≡ f. 
Check fun f: nat -eqv-> nat => id ≡[nat->nat] f. 
Check fun f: nat -eqv-> nat => f ≡[nat->nat] id. 
Check fun f: nat -eqv-> nat => f ° f. 
Check fun f: nat -eqv-> nat => f ° id ° f. 

Goal forall X: Setoid, forall f g h: X -eqv-> X, f ≡ g -> f ° g ≡ h.
Proof.
  intros * H.
  Fail rewrite H -H.
  change (f ° g ≡[_-eqv->_] h).
  rewrite H -H.  
Abort.

Goal forall X, forall h: X-eqv->X, forall x y: X, x ≡ y -> const x ≡ h.
Proof. intros * H. rewrite H -H. Abort. 
Goal forall X, forall h: X-eqv->X, forall x y: X, x ≡ y -> Setoid.const x ≡ h.
Proof. intros * H. rewrite H -H. Abort. 

Check (bool * (unit -> dual nat) * sig (fun b: bool=> b=true)  (* * True *))%type: Setoid. 
Check (nat -> nat -> Prop): Setoid. 
Check (nat -eqv-> nat -eqv-> Prop): Setoid. 
