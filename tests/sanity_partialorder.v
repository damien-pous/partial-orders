From PartialOrders Require Import partialorder.

(* basic instances *)
Check fun X: Type => discrete (trivial X): PO.type.
Check fun X: Setoid.type => discrete X: PO.type.
Check False: StrictPO.type.
Check False: DiscretePO.type.
Check unit: StrictPO.type.
Check unit: DiscretePO.type.
Check bool: StrictPO.type.
Check (bool->bool): PO.type.  
Check (bool * (unit -> dual bool) * sig (fun b: bool=> b=true))%type: PO.type. 
Check (bool -> bool -> Prop): PO.type. 
Check (bool -eqv-> bool -eqv-> Prop): PO.type. 
Check (bool -eqv-> bool -mon-> Prop): PO.type. 
Check (bool -mon-> bool -eqv-> Prop): PO.type. 

Section s.
  Variables X Y: PO.type.

  (* duality on partial orders in involutive only up to eta *)
  (* would need #[primitive] PO.type to get it definitionally
     but this is considered fragile for canonical structure inferrence
     https://github.com/math-comp/math-comp/pull/462
     same problem in mathcomp:
     https://github.com/math-comp/math-comp/pull/464
   *)
  Fail Check same PO.type X (dual (dual X)). 
  Check same PO.type (eta X) (dual (dual X)).
  Fail Check same PO.type (X-mon->Y) (dual X-mon->dual Y). (* has to fail *)
  Fail Check same PO.type (X-mon->Y) (dual (dual X)-mon->dual (dual Y)). (* sad *)
  Check same PO.type (X -> dual Y) (dual (X -> Y)).

  (* kernel compositions behave well:
     taking two successive kernels is definitionally equivalent to taking a composite one
     crucial from some inheritance paths to be equivalent, e.g.,
     (X-mon->Y) -> (sig (Proper ...)) -> X->Y
   *)
  Variables (A B: Type) (f: A -> B) (g: B -> X).
  Check same PO.type
    (kernel (X:=kernel g) f)
    (kernel (g∘f)).
  Check same PO.type
    (kernel (g: B -> dual X))
    (dual (kernel g)).

  (* fails if PO.type is defined with #[primitive] *)
  Goal forall x y: X, x ≡ y -> x <= y.
    intros. rewrite H.
  Abort.
End s.


(* duality on po morphisms is definitionally involutive up to eta *)
Section s.
  Variables (X Y: PO.type) (f: X-mon->Y) (g: Y-mon->X).
  Fail Check same (X-mon->Y) f (dualf' (dualf f)).
  Check same (X-mon->Y) (etaf f) (dualf' (dualf f)).
  (* even through composition *)
  Check same (Y-mon->Y) (f ∘ g) (dualf' (dualf f ∘ dualf g)).

  Check X-mon->Y: Setoid.type.
  
  (* one could only dream of this one *)
  Fail Check same PO.type (X-mon->X) (dual X-mon->dual X).
  Fail Check same PO.type (eta (X-mon->X)) (dual X-mon->dual X).  

  Fail Check same PO.type (X-mon->Y) (dual (dual X)-mon->dual (dual Y)). (* dommage *)
  Check same PO.type (eta X-mon->eta Y) (dual (dual X)-mon->dual (dual Y)). (* good *)
  
  Variable f': dual X-mon->dual Y.
  Check dualf' f': X-mon->Y. (* dommage *)
  Check dualf' f': eta X-mon->eta Y. (* good *)
  
  Check types_id: X-mon->X.
  Check g ∘ f: X-mon->X.
End s.


Section dprod.
  Variables (A: Type) (X: forall a: A , PO.type).
  Check same Setoid.type (forall a, X a) (dual (forall a, dual (X a))).
  Check same PO.type (forall a, X a) (dual (forall a, dual (X a))).
End dprod.


Section sig.
  Check fun (X: PO.type) (P: X -> Prop) =>
          same PO.type
            (sig (P: dual X -> Prop))
            (dual (sig P)).
  Check fun (X: Setoid.type) (Y: PO.type) =>
          same PO.type
            (X -eqv-> dual Y)
            (dual (X -eqv-> Y)).
  Check fun (X Y: PO.type) =>
          same PO.type
            (eta X -mon-> eta Y)
            (dual (dual X) -mon-> dual (dual Y)).
End sig.


Section rewriting.

  Variables (X: PO.type) (f g: X -mon-> X) (x y: X)
    (fg: f <= g)
    (fg': f <=[X-mon->X] g)
    (fgE: f ≡ g)
    (xy: x <= y)
    (xyE: x ≡ y).

  Goal (f ∘ f) x <= f (f x).
  Proof. rewrite {1}xy. rewrite -xyE. Abort.

  Goal const x <= g.
  Proof.
    rewrite xy -xyE.
  Abort.

  Goal const x <=[X-mon->X] g.
  Proof.
    (* fails because here the goal is an equality of setoid_moprhisms *)
    Fail rewrite xy.
    Fail rewrite xyE.
    move=>x'/=.
    rewrite xy -xyE.
    Restart.
    change (const x <=[X->X] g).
    rewrite xy -xyE. 
  Abort.
  
  Goal (f ∘ g) x <= x.
  Proof.
    rewrite fg. Restart.
    Fail rewrite fgE. Restart.
    (* surprising that it works here, given that it fails in sanity_setoid *)     
    rewrite fg'. Restart.
    (* fails for lack of a match *)
    Fail rewrite (fg _).
    Fail rewrite (fgE _).
    Fail rewrite (fg' _).
    setoid_rewrite (fg _). 
  Abort.
  
  Goal (g ∘ f) x <= x.
  Proof.
    rewrite fg. Restart.
    Fail rewrite fgE. Restart.
    (* idem *)    
    rewrite fg'. Restart.
    (* fails for lack of a match *)
    Fail rewrite (fg _).
    Fail rewrite (fgE _).
    Fail rewrite (fg' _).
  Abort.

  Goal f (f x) <= x.
  Proof.
    rewrite fg. Restart. 
    Fail rewrite fgE. Restart. 
    (* idem *)    
    rewrite fg'. Restart.
    rewrite 2!(fg _). Restart.
    rewrite 2!(fg' _). Restart.
  Abort.
  
  Goal f ∘ g <= types_id.
  Proof.
    Fail rewrite fg.
    Fail rewrite fgE.
    Fail rewrite fg'.
  Abort.

  Goal f ∘ g <=[X->X] types_id.
  Proof.
    Fail rewrite fg.
    Fail rewrite fgE.
    Fail rewrite fg'. 
  Abort.

  (* note the upper ° (vs ∘) *)
  Goal f ° g <= types_id.
  Proof.
    rewrite fg. Restart.
    rewrite fgE. Restart.
    (* idem *)
    rewrite fg'. Restart.
  Abort.

  Goal f ° g <=[X->X] types_id.
  Proof.
    Fail rewrite fg.
    Fail rewrite fgE.
    Fail rewrite fg'.
  Abort.
  
End rewriting.

Goal forall (X: PO.type) (x: nat -> X), x ≡ x.
  intros * n.  
Abort.
Goal forall A (X: A -> PO.type) (x: forall a, X a), x ≡ x. 
  intros * a.
Abort.
Check fun X: PO.type => @types_id X: X-mon->X. 
Check fun (X: PO.type) (f g: X -mon-> X) => f: X -eqv->X. 

Check unify (tt <= tt) true.
Check unify (false <= true) true.

Check forall (X: PO.type) (f: X -mon-> X), types_id ° f <= types_id. 
Check forall (X: PO.type) (f: X -eqv-> X), f <= types_id.
Check forall (X: PO.type) (f: X -mon-> X), f <= types_id.
Fail Check forall (X: PO.type) (f: X -mon-> X), types_id <= f.
Check forall (X: PO.type) (f: X -mon-> X), po_id <= f.
Check forall (X: PO.type) (f: X -mon-> X), f ≡ types_id.
Fail Check forall (X: PO.type) (f: X -mon-> X), types_id ≡ f. 
Check forall (X: PO.type) (f: X -mon-> X), po_id ≡ f.

Goal forall X: PO.type, forall f g h: X-mon->X, f ≡ g -> f ° g ≡ h.
Proof. intros * H. rewrite H. Abort.
Goal forall X: PO.type, forall f g h: X-mon->X, f <= g -> f ° g <= h.
Proof. intros * H. rewrite H. Abort.

Goal forall (X: PO.type) (f: X -mon-> X) (x y: X), x≡y -> y<=x -> f (f x) <= (f (f x)).
Proof. intros * H H'. rewrite {1}H H'. reflexivity. Qed.
Goal forall (X: PO.type) (f g: X -mon-> X) (x y: X), x≡y -> y<=x -> f <= g -> (f ° f) x <= (f ° f) x /\ f ° f <= g ° g.
Proof.
  intros * H H' H''. rewrite {1}H H'. split=>//.
  rewrite H''//.
Qed.
Goal forall (X: PO.type) (f g: X -mon-> X) (x y: X), x≡y -> y<=x -> f <= g -> (f ∘ f) x <= (f ∘ f) x /\ f ∘ f <= g ∘ g.
Proof.
  intros * H H' H''. rewrite {1}H H'. split=>//.
  Fail rewrite H''.
Abort.
