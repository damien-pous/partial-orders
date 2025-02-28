# MENU

preliminaries
 
setoids
 strict [dec]
 setoid morphism
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
 
sups (colimites en catégories)
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

closures

# DUALITY/GENERICITY

in sup,    gsup    <=> std sups
            dprod       +
            mon/ext     + 

in inf,    gsup    <-> ginf (ok but for gdual gdual + difficulty of dual_mon functions)
            dprod      (copypaste)
			mon/ext    (copypaste)
			
           std sup <-> std inf (easy but HB bug)
		    dprod       +
			mon/ext     ?
			
		   ginf    <=> std inf (boring, unless duality)
			dprod       +
			mon/ext     +
			
# FILES

- theories/preliminaries.v   elementary helpers
- theories/--_setoid.v          setoids
- theories/--_po.v              partial orders
- theories/--_sup.v             partial orders with (some) supremums
- theories/--_inf.v             partial orders with (some) infimums
- theories/--_lattice.v         partial orders with (some) supremums & infimums 
- theories/--_lfp.v             least fixpoint theorems, study of the chain of a function (BourbakiWitt/Pataraia)
- theories/--_gfp.v             greatest fixpoint theorems, by duality
- theories/--_adjunctions.v     adjunctions
- theories/--_instances.v       instances (e.g, natural numbers with min, max, 0)

previous:
- theories/preliminaries.v   elementary helpers
- theories/--_setoid.v          setoids
- theories/--_po.v              partial orders
- theories/--_spo.v             partial orders with (some) supremums
- theories/--_ipo.v             partial orders with (some) infimums
- theories/--_gpo.v             partial orders with (some) supremums & infimums 
- theories/--_chain.v           study of the chain of a function (BourbakiWitt/Pataraia)
- theories/--_adjunctions.v     adjunctions
- theories/--_nat.v             the partial order of natural numbers (with min, max, 0)

where -- is
- hb for the HB based version
- cs for the homemade CS based one
- tc for the homemade TC based one (not yet)
- mx for the homemade CS+TC based one (not yet)

- theories/hb_chain_alt.v      alternative version of hb_chain, defining its own hierarchy on top of hb_po.v

sanity checks
- tests/*.v

old attempts
- attic/alone.v     without HB
- attic/split.v     split operations/laws
- attic/split_tc.v  idem, with TC for laws
- attic/level_attempts.v  unsuccessful experiments with levels

# TODO

rethink:
- use of categories / comp ° \circ
- isomorphisms


rework&sync sanity checks

don't use HB for morphisms?

revive the mixed cs+tc (split_tc.v)
do a pure typeclass attempt?

smart constructor for SPO/IPO/GPO ?
GPO products/sums/option

distributive GPO 
Heyting algebras ? (on top of SPO sB or ???)
Boolean algebras ? (on top of GPO (sB,sB), or ???)

setoid_congruence tactic
lattice tactics
more on adjunctions

cast_setoid

strong setoids (where eqv=eq)
decidable eqv, leq
finite


## later
non-empty chains/directed/arbitrary?
and/or I-indexed variants? (omega)

in classical logic, 
 chain-complete => directed-complete


# MISC

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

