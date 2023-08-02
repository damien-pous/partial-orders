Require Import ssreflect ssrfun ssrbool.
Require Import hb.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Local Unset Transparent Obligations.
Set Primitive Projections.

(** * categories *)
#[universes(polymorphic=yes)] Structure CATEGORY := {
    ob: Type;
    hom:> ob -> ob -> Setoid.type;
#[canonical=no] id: forall {A}, hom A A;
#[canonical=no] comp: forall {A B C}, hom B C -> hom A B -> hom A C;
#[canonical=no] comp_eqv:: forall {A B C}, Proper (eqv ==> eqv ==> eqv) (@comp A B C);
#[canonical=no] idl: forall {A B} f, @comp A A B f id ≡ f;
#[canonical=no] idr: forall {A B} f, @comp B A A id f ≡ f;
#[canonical=no] compA: forall {A B C D} f g h, @comp A B D (@comp B C D h g) f ≡ @comp A C D h (@comp A B C g f)
  }.
Arguments id {_ _}.
Arguments comp {_ _ _ _}.
Infix "°" := comp.

(** the category of types and extensional functions (unused so far) *)
(** yields universe inconsistencies... *)
(* Program Canonical Structure TYPES := *)
(*   {| *)
(*     ob := Type; *)
(*     hom := efun; *)
(*     comp := @types_comp; *)
(*     id := @types_id; *)
(*   |}. *)
(* Next Obligation. move=>f f' ff g g' gg x/=. by rewrite ff gg. Qed. *)
  
(** the category of setoids and extensional functions *)
Program Canonical Structure SETOIDS :=
  {|
    ob := Setoid.type;
    hom X Y := X -eqv-> Y;
    comp := @types_comp;
    id := @types_id;
    comp_eqv := @types_comp_eqv;
  |}.

(** the category of partial orders and monotone functions *)
Program Canonical Structure POS :=
  {|
    ob := PO.type;
    hom X Y := X -mon-> Y;
    comp := @types_comp;
    id := @types_id;
    comp_eqv := @types_comp_eqv;    
  |}.

(* this instance of [types_comp_leq] needs to be explicited to be useful for setoid-rewriting *)
(* TOTHINK: declare the pure [eqv] versions? *)
#[export] Instance po_comp_leq {X Y Z: PO.type}:
  Proper (leq ==> leq ==> leq) (@comp POS X Y Z) := types_comp_leq.
(* idem for this one? *)
#[export] Instance setoid_comp_leq {X: Setoid.type} {Y Z: PO.type}:
  Proper (leq ==> eqv ==> leq) (@comp SETOIDS X Y Z) := types_comp_leq_eqv.
