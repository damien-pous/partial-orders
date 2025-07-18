A Rocq library about partial orders and related structures (CPOs, complete lattices, etc).

# REQUIREMENTS

- rocq-prover 9.0 (see branch 8.20 for backports)
- rocq-mathcomp-ssreflect 

# AUTHORS

Damien Pous (CNRS, Plume team, LIP, ENS de Lyon)

# LICENSE

GNU LGPL3+

# MENU

preliminaries
 
setoids
 strict [dec]
 setoid morphisms
 instances (trivial (0,1), strict (2,nat), Prop, dprod, +, *, sig, sigT?, extfun)
 
partial orders
 discrete
 po morphisms
 instances (discrete (0,1), 2, nat, Prop, dprod, +s, *s, sig, sigT?, extfun, monfun)
 duality
 chains, directed sets

total
 chain classic [dec]

adjunctions
 
sups (colimits in categories)
 is_sup
 generic sups and their constructions
 {bot,cup,csup,dsup,isup}

infs (by duality)
 is_inf
 generic infs and their constructions
 {top,cap,cinf,dinf,iinf}
 
lattices
 [modular, distributive, residuated, completely distributive]

fixpoints (lfp/gfp)
 Bourbaki-Witt, Pataria
			
# FILES

- theories/preliminaries.v   elementary helpers
- theories/setoid.v          setoids
- theories/partialorder.v    partial orders
- theories/totalorder.v      chains & total orders
- theories/adjunction.v      adjunctions & isomorphisms
- theories/sups.v            suprema
- theories/infs.v            infima
- theories/lfp.v             least fixpoints 
- theories/gfp.v             greatest fixpoints 
- theories/lattice.v         complete lattices and mixed infs/sups structures
- theories/instances.v       various instances

sanity checks
- tests/*.v

# HIERARCHY OF MORE OR LESS COMPLETE PARTIAL ORDERS

Mathematically, we have the following picture

 ·     ·       ·
CL -- dCPO -- CPO --------------------\
       ^ \       \(EM)                 \
       |  \-- Chain_lfp_PO -- lfp_PO -- botPO
       \----------(AC)---------/          ·

bot_PO: partial orders with a bottom element
lfp_PO: every monotone function has a least fixpoint
Chain_lfp: every monotone function has a leas fixpoint, obtained as the top element of its chain
CPO: every chain has a least upper bound
dCPO: every directed set has least upper bound
CL: every set has least upper bound

Dotted structures are those preserved by taking products and monotone functions.

dCPO inherits from Chain_lfp by Pataria fixpoint theorem, but not in a forgetful way.
similarly for CPO, but only classically, by Bourbaki-Witt's theorem.

This raises difficulties when using HB structures, which we solve using the following hierarchy
(more comments in file [theories/sups.v])

    ·CL
	 |
   ·dCPO   ·CPO
	  \    /
      lfpCPO
	 /     \
    /       \
·sups.CPO  Chain_lfp
    \       /
     \   lfp_PO 
      \   /
     ·botPO


# DUALITY/GENERICITY

- for setoid/partial orders/... dual is involutive only up to eta
- idem for morphisms (otherwise we loose some ssreflect rewriting)

in sup,    gsup    <=> std sups
            dprod       +
            mon/ext     + 

in inf,    gsup    <-> ginf (ok but for gdual gdual + difficulty of dual_mon functions)
            dprod      (copypaste)
			mon/ext    (copypaste)
			
           std sup <-> std inf
		    dprod       +
			mon/ext     ?
			
		   ginf    <=> std inf (boring, unless duality)
			dprod       +
			mon/ext     +

# TODO

closures 
decidable eqv, leq
modular,distributive,residuated
more on adjunctions

rethink:
- use of categories / comp ° \circ

rework&sync sanity checks

don't use HB for morphisms? (or use them more)

lattice tactics


## LATER

finite structures

Heyting/Boolean algebras

non-empty chains/directed/arbitrary?
and/or I-indexed variants? (omega)

setoid_congruence tactic


Non constructive arguments:
- chain-complete => directed-complete (e.g., CPO => dCPO)
https://topology.lmf.cnrs.fr/markowsky-or-cohn/
https://topology.lmf.cnrs.fr/iwamuras-lemma-kowalskys-theorem-and-ordinals/
George Markowsky, Chain-complete posets and directed sets with applications, 1976

- BourbakiWitt + AC => ZL (already in coq-zorns-lemma)


# MISC THOUGHTS

- efficiency: 
  HB needs 15s where CS only needs 4s, 
  but HB seems faster on the user side: hb_chain needs 2.1s where chain needs 2.5s

- merge Setoid and PO ??  (probably not: lex_prod and prod share setoid their setoid structure)

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

