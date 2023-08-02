From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Export hb_setoid.

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

Check fun X: Type => trivial X: Setoid.type.
Goal forall X (f: X -eqv-> X) (x y: X), x≡y -> (f ∘ f) x ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  
Goal forall X: Setoid.type, forall f g: X-eqv->X, forall x y: X, f ≡ g -> x ≡ y -> f x ≡ g y /\ f ∘ const x ≡[X-eqv->X] const (g y) /\ const x ≡[X->X] const y.
Proof.
  intros X f g x y fg xy. repeat split.
  Fail rewrite fg.              (* fair enough *)
  rewrite xy. by apply fg.
  2: by rewrite xy.
  Fail rewrite fg.              (* need the category notation *)
  (* by rewrite xy.  *)               (* thanks to [const_eqv'] *)
Abort.  

Check fun f: bool -eqv-> bool => f ≡ types_id. 
Fail Check fun f: bool -eqv-> bool => types_id ≡ f. 
Check fun f: bool -eqv-> bool => @types_id bool ≡ f. 
Check fun f: bool -eqv-> bool => f ≡ Datatypes.id. 
Fail Check fun f: bool -eqv-> bool => Datatypes.id ≡ f. 
Check fun f: bool -eqv-> bool => @Datatypes.id bool ≡ f. 
Check fun f: bool -eqv-> bool => f ≡[bool->bool] types_id. 

Goal forall X, forall h: X-eqv->X, forall x y: X, x ≡ y -> const x ≡ h.
Proof. intros * H. rewrite H -H. Abort. 

Check bool: Setoid.type. 
Check (bool * (unit -> dual bool) * sig (fun b: bool=> b=true)  (* * True *))%type: Setoid.type. 
Check (bool -> bool -> Prop): Setoid.type. 
Check (bool -eqv-> bool -eqv-> Prop): Setoid.type. 

Goal forall f: nat -> Prop, f ≡ f.
  move=>f x.
Abort.


Goal forall X, forall f g h: X -eqv-> X, f ≡ g -> f ∘ g ≡ h.
  Fail intros * ->.              (* fair enough *)
Abort.
Goal forall f g: nat -> Prop, f ≡ g -> f ≡ g.
  intros * ->.
Abort.

Section s.
  Variable X: Setoid.type.
  Check forall f g: X -eqv-> X, f ∘ g ≡ id.
  Check forall f g: bool -eqv-> bool, f ∘ g ≡ id.
End s.

Goal forall X, forall f: X -eqv-> X, forall x y: X, x≡y -> f (f x) ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  

Goal forall X, forall f: X -eqv-> X, forall x y: X, x≡y -> (f ∘ f) x ≡ f (f x).
Proof. intros * H. rewrite H. rewrite -H. reflexivity. Abort.  



