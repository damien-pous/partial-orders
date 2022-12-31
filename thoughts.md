
partial orders (leq, weq)
duality
monotone functions
adjoints

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
 

