# FILES

orders.v    with HB
alone.v     without HB
alone_fun.v without HB, SPO,IPO,GPO duality, etc
split.v     split operations/laws
split_tc.v  idem, with TC for laws

# TODO

smart constructor for GPO 

direct sub-GPO construct?
GPO products/sums

resplit ops and laws ??
merge Setoid and PO ??

distributive, Heyting, Boolean

more on adjunctions

cast_setoid

strong eqc
decidable eqv, leq
finite


## later
non-empty chains/directed/arbitrary?
and/or I-indexed variants? (omega)

in classical logic, 
 chain-complete => directed-complete


# MISC

- split ops and laws:
  + was forced in relation aglebra?
  + less unification problems?
  - less mathematical
  - more arguments
  - laws come into the way anyways, for building the GPO of monotone functions

- laws via CS vs. laws via TC
  - with CS, cannot mix derived ops/concepts and lemmas in the same section
  - faster with TC (for now)

- separate setoid from PO:
  + same equality structure for prod and lex_prod
  - one more layer

- separate PO from SI-PO ?
  + PO remains without level arguments
  - one more layer

- levels and inheritance
  concrete instances could be polymorphic, but not abstract assumptions
  -> anticipate coercions in all lemma statements
  
  concrete instances with a fixed concrete level
  definitions and lemmas explicitly upward closed (forall l, k<<l -> )

- SPO, IPO (by duality), GPO ?  (in that case, remove slevel sN)


- duality: difficulty with monotone functions: [X-mon->Y] =/= [dual X-mon-> dual Y] due to the switch in monotonicity statement proofs 



suprema
(infima by duality)

is_sup: (X -> Prop) -> X -> Prop 

- empty                 bot:   0            *
- singleton             id:                 *
- binary                cup:   X²           *     A->X
- finite                      (list X)      bool, A->X
- decidable                   (X->bool)     bool, F->X
- all                   sup:  (X->Prop)     Prop, A->X
- I                           (I -> X)

- directed                    {D: X->Prop | directed D}
- omega-increasing            {D: nat->X  | increasing D}
- chain                       {C: X->Prop | chain C}
- omega-chain                 {C: nat->X  | chain C}

- decidable? [X -> bool]                           bool

[below: to be linked with directed]
- chains
- omega-chains
- increasing omega-sequences


omega-increasing => omega-chain => chain => directed

classical logic: 
  omega-chain => omega-increasing
  chain-complete => directed-complete ()

Props:                                                                                closed under
chain P: forall x y, P x -> P y -> x<=y \/ y <=x                                    intersection
directed P: forall x y, P x -> P y -> exists z, P z /\ x<=z /\ y <=z                union
non-empty P: exists x, P x                                                          union
finite P: exists l, forall x, P x -> In x l                                         union, intersection

Sizes:
below T P: exists f: T -> X, P == im f
exact T P: exists f: T -> X, inj f /\ P == im f


=================

(X,≡) setoid 
 -> unit, nat, bool, Prop, +, *, list, forall, 
 -> category of setoids and setoid-morphisms

(X,≡,<=) partial order
 -> unit, nat, bool, Prop, +, +', *, *', list, forall, 
 -> po-enriched category of pos and monotone functions
    (a sub-category of the above one)

(X,≡,<=,infs,sups) I,S-complete partial order (cpo) [with I,S: (X->Prop)->Type]
 -> some instances
 -> infs and sups in the above po-enriched category (for some I,S at least)
 -> sub-category of I,S-preserving monotone functions


[S-sup: forall (P: X -> Prop), S P -> X]

[S P = empty P]                     -> bot
[S P = { x,y: X | P ≡ pair x y }]   -> cup
[S P = { l: list X | P ≡ In l }]    -> fcup
[S P = chain P]                     -> csup
[S P = directed P]                  -> dsup
[S P = True]                          -> sup
[S P = decidable P] 
[S P = { f: X -> bool| reflect f P }]

[S_h P = forall b, b\in h -> S_b P]








(X,≡,<=) partial order 
 -> unit, nat, bool, Prop, +, +', *, *', forall, 
 



(X,≡) setoid
(X,≡,<=) partial order  (po)
(X,≡,<=,gsup,gsinf) S,I-complete po

setoid-morphisms
po-morphisms
S,I-po-morphisms


Hom    Type Setoid PO S,I-PO
Type        Setoid PO S,I-PO
Setoid        ^.   ^.   ^.
PO            ^    ^.   ^.
S,I-PO        ^    ^    ^.

comp   Type Setoid PO     S,I-PO
Type   Type Type   Type   Type
Setoid Type Setoid Setoid Setoid
PO     Type Setoid PO     PO
S,I-PO Type Setoid PO     S,I-PO

comp: eqv/Setoid => eqv => eqv
comp: leq/Setoid => eqv => leq
comp: leq/PO     => leq => leq

