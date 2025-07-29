Require Export partialorder.

(** * chains & total orders

chain: forall x y, x<=y \/ y<=x
classic: forall x y, x<=y \/ ~x<=y
total: forall x y, x<=y \/ y<x

total <-> classic chain

 *)

HB.mixin Record isChain X of PO X := {
    #[canonical=no] chain: forall x y: X, x <= y \/ y <= x;
}.
HB.structure Definition Chain := { X of isChain X & }.
HB.structure Definition Order := { X of Chain X & ClassicPO X }.

HB.factory Record PO_Total X of PO X := {
    #[canonical=no] total: forall x y: X, x <= y \/ y < x;
}.
HB.builders Context X of PO_Total X.
  Implicit Types x y: X.
  Lemma chain x y: x <= y  \/  y <= x.
  Proof. case: (total x y)=>[|[? ?]]; auto. Qed.
  HB.instance Definition _ := isChain.Build X chain. 
  Lemma classic x y: x <= y  \/  ~ x <= y.
  Proof. case: (total x y)=>[|[? ?]]; auto. Qed.
  HB.instance Definition _ := isClassicPO.Build X classic.
HB.end.

Section s.
Context {X: Order.type}.
Implicit Types x y: X.
Lemma total x y: x <= y  \/  y < x.
Proof.
  case: (classic x y); auto.
  case: (chain x y); auto.
  by right; split.
Qed.
Lemma compare x y: x < y  \/  x ≡ y  \/  y < x.
Proof.
  case: (total x y)=>xy;
  case: (total y x)=>yx.
  - by right; left; apply: antisym. 
  - by left.
  - by right; right.
  - exfalso. move: xy yx. exact: lt_nlt. 
Qed.
End s.

