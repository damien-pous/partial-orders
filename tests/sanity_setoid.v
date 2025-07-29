From PartialOrders Require Import setoid.

(* basic instances *)
Check fun X: Type => trivial X: Setoid.type.
Check fun X: Type => strict X: Setoid.type.
Check False: StrictSetoid.type.
Check unit: StrictSetoid.type.
Check bool: StrictSetoid.type.
HB.instance Definition _ := strict_setoid nat.
Check nat: StrictSetoid.type.
Check (nat->bool): Setoid.type.  
Check (bool * (unit -> dual bool) * sig (fun b: bool=> b=true)  (* * True *))%type: Setoid.type. 
Check (bool -> bool -> Prop): Setoid.type. 
Check (bool -eqv-> bool -eqv-> Prop): Setoid.type. 
  
Section s.
  Variables X Y: Setoid.type.

  (* duality on setoids in involutive only up to eta *)
  (* would need #[primitive] Setoid.type to get it definitionally
     but this is considered fragile for canonical structure inferrence
     https://github.com/math-comp/math-comp/pull/462
     same problem in mathcomp:
     https://github.com/math-comp/math-comp/pull/464
   *)
  Fail Check same Setoid.type X (dual (dual X)). 
  Check same Setoid.type (eta X) (dual (dual X)).
  (* at the setoid level, dual is actually the identity up to eta *)
  Check same Setoid.type (eta X) (dual X).

  (* kernel compositions behave well:
     taking two successive kernels is definitionally equivalent to taking a composite one
     crucial from some inheritance paths to be equivalent, e.g.,
     (X-eqv->Y) -> (sig (Proper ...)) -> X->Y
   *)
  Variables (A B: Type) (f: A -> B) (g: B -> X).
  Check same Setoid.type
    (kernel (X:=kernel g) f)
    (kernel (g∘f)).  
End s.


(* duality on setoid morphisms is definitionally involutive up to eta *)
Section s.
  Variables (X Y: Setoid.type) (f: X-eqv->Y) (g: Y-eqv->X).
  Fail Check same (X-eqv->Y) f (dualf' (dualf f)).
  Check same (X-eqv->Y) (etaf f) (dualf' (dualf f)).
  (* even through composition *)
  Check same (Y-eqv->Y) (f ∘ g) (dualf' (dualf f ∘ dualf g)).

  Check X-eqv->Y: Setoid.type.
  
  (* one could hope for this one *)
  Fail Check same Setoid.type (X-eqv->X) (dual X-eqv->dual X).
  Check same Setoid.type (eta X-eqv->eta X) (dual X-eqv->dual X).  

  Check types_id: X-eqv->X.
  Check g ∘ f: X-eqv->X.
End s.

Check fun f: bool -eqv-> bool => f ≡ types_id. 
Check fun f: bool -eqv-> bool => f ≡[bool->bool] types_id. 
Fail Check fun f: bool -eqv-> bool => types_id ≡ f. 
Check fun f: bool -eqv-> bool => @types_id bool ≡ f. 
Check fun f: bool -eqv-> bool => types_id ≡[bool->bool] f. 
Check fun f: bool -eqv-> bool => types_id ≡[bool-eqv->bool] f. 

(* those additional instance do not help *)

(* Existing Instance types_comp_eqv. *)
(* Instance setoid_comp_eqv' {X Y Z: Setoid.type}: Proper (eqv ==> eqv ==> eqv ==> eqv) (@setoid_comp X Y Z). *)
(* Admitted. *)

Section rewriting.

  Variables (X: Setoid.type) (f g: X -eqv-> X) (x y: X)
    (fg: f ≡ g)
    (fg': f ≡[X->X] g)
    (xy: x ≡ y).

  Goal (f ∘ f) x ≡ f (f x).
  Proof. rewrite xy. rewrite -xy. reflexivity. Qed.  

  Goal const x ≡ g.
  Proof.
    rewrite xy -xy.
  Abort.

  Goal const x ≡[X-eqv->X] g.
  Proof.
    (* fails because here the goal is an equality of setoid_moprhisms *)
    Fail rewrite xy.
    move=>x'/=.
    rewrite xy.
    Restart.
    change (const x ≡[X->X] g).
    rewrite xy.    
  Abort.
  
  Goal (f ∘ g) x ≡ x.
  Proof.
    rewrite fg. Restart.
    (* fails because fg' is an equality of functions *)    
    Fail rewrite fg'.
    (* fails for lack of a match *)
    Fail rewrite (fg _).
    Fail rewrite (fg' _).
    setoid_rewrite (fg _). 
  Abort.
  
  Goal (g ∘ f) x ≡ x.
  Proof.
    rewrite fg. Restart.
    (* fails because fg' is an equality of functions *)    
    Fail rewrite fg'. 
    (* fails for lack of a match *)
    Fail rewrite (fg _).
    Fail rewrite (fg' _).
  Abort.

  Goal f (f x) ≡ x.
  Proof.
    rewrite fg. Restart. 
    (* fails because fg' is an equality of functions *)    
    Fail rewrite fg'. 
    rewrite 2!(fg _). Restart.
    rewrite 2!(fg' _). Restart.
  Abort.
  
  Goal f ∘ g ≡ types_id.
  Proof.
    Fail rewrite fg.
    Fail rewrite fg'.
  Abort.

  Goal f ∘ g ≡[X->X] types_id.
  Proof.
    Fail rewrite fg.
    Fail rewrite fg'. 
  Abort.
  
  Goal setoid_comp f g ≡ types_id.
  Proof.
    rewrite fg. Restart.
    setoid_rewrite fg. Restart.
    (* no match *)
    Fail rewrite fg'. 
  Abort.

  Goal setoid_comp f g ≡[X->X] types_id.
  Proof.
    Fail rewrite fg.
    Fail rewrite fg'. 
  Abort.

End rewriting.
