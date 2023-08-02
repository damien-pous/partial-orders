Require Import ssreflect ssrfun ssrbool.
Require Import StrictProp.
From PartialOrders Require Import spo.

Set Implicit Arguments.
Set Primitive Projections.

Module Failed_CS_level_inheritance_attempts.
  
Definition bot {X: SPO sE}: X := @gsup _ X kE stt tt. 
Fail Check bot: bool. 

Definition bot' {X: SPO sF}: X := @gsup _ X kE stt tt. 
Check bot': bool. 

Module A. 
Structure coercer (l: slevel) := c {
    ck: slevel;
    #[canonical=no] ckl: l <= ck;
  }.
Canonical Structure cEF := c sE sF I.
Structure SPO' l := {
    get:> SPO l;
    coe: coercer l;
  }.
Canonical Structure coercion l (coe: coercer l) (X: SPO (ck coe)): SPO' l :=
  Eval hnf in
  {| coe := coe; get := SPO.weaken _ X (ckl coe) |}.

Definition bot {X: SPO' sE}: X := @gsup _ (get X) kE stt tt. 
Fail Check bot: nat. 
Check @bot (@coercion _ cEF bool_spo): bool.
Check @bot (@coercion _ _ _): bool. 
End A.

Module B. 
Structure coercer (l: slevel) := c {
    ck: slevel;
    #[canonical=no] ckl: ck <= l;
}.
Notation "h <: k" := (c k h I) (at level 80). 
Canonical Structure cEF := sE <: sF.
Canonical Structure cEC := sE <: sEC. (* argh *)
Definition SPO' l := SPO l.
Coercion sort' l (X: SPO' l): Type := X.
Canonical Structure coercion l (X: SPO l) (coe: coercer l): SPO' (ck coe) :=
  Eval hnf in @SPO.pack (ck coe) (sort' X) _ _ (SPO.mix (SPO.weaken _ X (ckl coe))).
Definition bot {X: SPO' sE}: X := @gsup _ X kE stt tt. 
Fail Check bot: bool. 
Check @bot (@coercion _ bool_spo cEF): bool.
Check @bot (@coercion _ _ _): bool.
Check forall X: SPO' sF, forall (x: X), bot ≡ x. 
Check forall X: SPO' sE, forall (x: X), bot ≡ x. 
End B.

Module C.
  Module N.  Structure coercer := c { k; #[canonical=no] ck: k <= sN  }. End N.
  Module E.  Structure coercer := c { k; #[canonical=no] ck: k <= sE  }. End E.
  Module B.  Structure coercer := c { k; #[canonical=no] ck: k <= sB  }. End B.
  Module F.  Structure coercer := c { k; #[canonical=no] ck: k <= sF  }. End F.
  Module EC. Structure coercer := c { k; #[canonical=no] ck: k <= sEC }. End EC.
  Module FC. Structure coercer := c { k; #[canonical=no] ck: k <= sFC }. End FC.
  Module ED. Structure coercer := c { k; #[canonical=no] ck: k <= sED }. End ED.
  Module A.  Structure coercer := c { k; #[canonical=no] ck: k <= sA  }. End A.
  Definition coercer l :=
    match l with
    | Some pN => N.coercer
    | Some pE => E.coercer
    | Some pB => B.coercer
    | Some pF => F.coercer
    | Some pEC => EC.coercer
    | Some pFC => FC.coercer
    | Some pED => ED.coercer
    | None => A.coercer
    end.
  Definition k l: coercer l -> slevel :=
    match l with
    | Some pN => N.k
    | Some pE => E.k
    | Some pB => B.k
    | Some pF => F.k
    | Some pEC => EC.k
    | Some pFC => FC.k
    | Some pED => ED.k
    | None => A.k
    end.
  Definition ck l: forall x: coercer l, k l x <= l :=
    match l with
    | Some pN => N.ck
    | Some pE => E.ck
    | Some pB => B.ck
    | Some pF => F.ck
    | Some pEC => EC.ck
    | Some pFC => FC.ck
    | Some pED => ED.ck
    | None => A.ck
    end.
  Definition c l: forall k, k <= l -> coercer l :=
    match l with
    | Some pN => N.c
    | Some pE => E.c
    | Some pB => B.c
    | Some pF => F.c
    | Some pEC => EC.c
    | Some pFC => FC.c
    | Some pED => ED.c
    | None => A.c
    end.
  Notation "h <: k" := (c k h I) (at level 80).
  (* also N? *)
  Canonical Structure cEF   : coercer _ := Eval hnf in sE <: sF.
  Canonical Structure cEEC  : coercer _ := Eval hnf in sE <: sEC.
  Canonical Structure cEFC  : coercer _ := Eval hnf in sE <: sFC.
  Canonical Structure cEED  : coercer _ := Eval hnf in sE <: sED.
  Canonical Structure cBF   : coercer _ := Eval hnf in sB <: sF.
  Canonical Structure cBFC  : coercer _ := Eval hnf in sB <: sFC.
  Canonical Structure cFFC  : coercer _ := Eval hnf in sF <: sFC.
  Canonical Structure cECFC : coercer _ := Eval hnf in sEC <: sFC.
  Canonical Structure cECED : coercer _ := Eval hnf in sEC <: sED.
  Canonical Structure c_A p := Eval hnf in Some p <: sA.
  
  Definition SPO' l := SPO l.
  Coercion sort' l (X: SPO' l): Type := X.
  Canonical Structure coercion l (X: SPO l) (coe: coercer l): SPO' (k l coe) :=
    Eval hnf in @SPO.pack (k l coe) (sort' X) _ _ (SPO.mix (SPO.weaken _ X (ck l coe))).
  Definition bot {X: SPO' sE}: X := @gsup _ X kE stt tt. 
  Fail Check bot: bool. 
  Check @bot (@coercion _ bool_spo cEF): bool.
  Check @bot (@coercion _ _ cEF): bool.
  Fail Check @bot (@coercion _ bool_spo _): bool.
  Fail Check @bot (@coercion _ _ _): bool.
  Check forall X: SPO' sE, forall (x: X), bot ≡ x.
  Fail Check forall X: SPO' sF, forall (x: X), bot ≡ x. 
End C.

End Failed_CS_level_inheritance_attempts.



(* for GPO levels *)

Module IDEAL.
Definition level := option (plevel * plevel).
Definition suplevel: level -> slevel := option_map fst.
Definition inflevel: level -> slevel := option_map snd.
Definition dual_level: level -> level := option_map (fun p => (snd p,fst p)).
Definition level_fun (l: level) k: SProp :=
  match k with
  | inl k => suplevel l k
  | inr k => inflevel l k
  end.
Coercion level_fun: level >-> Funclass.
(* Lemma level_mon: Proper (leq ==> leq) level_fun. *)
(* Proof. *)
(*   case=>[[p q]|]; case=>[[p' q']|]=>//=H[k|k]/=; *)
(*     try apply implybT; apply plevel_mon=>//=; apply H. *)
(* Qed. *)
Goal forall l: level, l ∘ inl = suplevel l. reflexivity. Qed.
Goal forall l: level, l ∘ inr = inflevel l. reflexivity. Qed.
Goal forall l, dual_level l ∘ inr = l ∘ inl. Fail reflexivity. Abort. 
Goal forall l k, dual_level (dual_level l) k = l k. Fail reflexivity. Abort. 
End IDEAL.

Module EXTENDEDPAIRS.
Record level := mk_level { suplevel: slevel; inflevel: slevel; more: bool}.
Definition dual_level (l: level) := mk_level (inflevel l) (suplevel l) (more l).
Definition level_fun (l: level) k: SProp :=
  match k with
  | inl k => suplevel l k
  | inr k => inflevel l k
  end.
Coercion level_fun: level >-> Funclass.
Goal forall l: level, l ∘ inl = suplevel l. reflexivity. Qed.
Goal forall l: level, l ∘ inr = inflevel l. reflexivity. Qed.
Goal forall l, dual_level l ∘ inr = l ∘ inl. reflexivity. Qed.
Goal forall l x, dual_level (dual_level l) x = l x. reflexivity. Qed.
End EXTENDEDPAIRS.
