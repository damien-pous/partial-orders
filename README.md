A Rocq library about partial orders and related structures (CPOs, complete lattices, etc).

# REQUIREMENTS

- rocq-prover 9.0 (see branch 8.20 for backports)
- rocq-mathcomp-ssreflect 

# AUTHORS

Damien Pous (CNRS, Plume team, LIP, ENS de Lyon)

# LICENSE

GNU LGPL3+

# MENU

setoids
 trivial, strict, decidable
 setoid morphisms (extfun)

(partial) orders
 discrete, classic, decidable, chain
 po morphisms (monfun)
 duality
 chains, directed sets, suprema&infima

adjunctions & isomoprhisms
 
sups (colimits in categories)
 is_sup
 generic sups and their constructions
 {bot,cup,csup,dsup,isup}

infs (by duality)
 is_inf
 generic infs and their constructions
 {top,cap,cinf,dinf,iinf}
 
lattices
 complete
 TODO: modular, distributive, residuated, completely distributive

fixpoints
 lfp/gfp and their theory
 Bourbaki-Witt, Pataria

instances:
 0, 1, 2, nat, Prop, dprod, *, +, option, sig, extfun, monfun, fset
 lex_prod, sequential_sum, list, lex_list, option
TODO: 
 finite dprod
 finite multisets


# FILES

- theories/preliminaries.v   		 elementary helpers
- theories/setoid.v          		 setoids
- theories/partialorder.v    		 partial orders
- theories/partialorder_instances.v  partial orders instances
- theories/totalorder.v      		 chains & total orders
- theories/adjunction.v      		 adjunctions & isomorphisms
- theories/sups.v            		 suprema
- theories/infs.v            		 infima
- theories/lfp.v             		 least fixpoints 
- theories/gfp.v             		 greatest fixpoints 
- theories/lattice.v         		 complete lattices and mixed infs/sups structures
- theories/instances.v       		 instances
- theories/sets.v       		     complete lattice of sets over a setoid
- theories/fsets.v       		     join semilattice of finite sets over a setoid

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


# DUALITY

We exploit duality to factor arguments about suprema/infima:

if [X] has some structure then [dual X] has the dual one

This duality is involutive only up to eta, otherwise we loose some ssreflect rewriting.
This is fine almost all the time, but requires specific tricks at a few places.

Consider duality for morphisms for instance,
if [f] is morphism between some structures X and Y, then [dualf f] is a morphism between [dual X] and [dual Y]

If X and Y are concrete, then [dualf (dualf f)] is again a morphism between X and Y
But if X and Y are abstract (not eta-expanded), then this is only a morphism between [dual (dual X)] and [dual (dual Y)].

Whence the need for a second operator, [dualf'], mapping a morphism from [dual X] to [dual Y] to a morphism from [X] to [Y].
Again, [dualf' (dual f)] = [f] only up to eta


# GENERICITY

We define various kinds of suprema:
- bot        : supremum of the empty set, i.e., bottom element
- cup x y    : supremum of the pair {x,y}, i.e., join
- csup P C   : supremum of the chain X (C being the proof that P is a chain) 
- dsup P D   : supremum of the directed set X (D being the proof that P is directed) 
- isup I P f : supremum of { f i / i \in I, P i }
- sup P      : supremum of P  (sup P = isup X P id)
and dually for infima:
- bot        : infimum of the empty set, i.e., top element
- cap x y    : infimum of the pair {x,y}, i.e., meet
- cinf P C   : infimum of the chain X (C being the proof that P is a chain) 
- dinf P D   : infimum of the directed set X (D being the proof that P is directed) 
- iinf I P f : infimum of { f i / i \in I, P i }
- inf P      : infimum of P  (inf P = iinf X P id)


In order to factor some aguments, we use a *generic* operators:
- gsup k     : supremum operation of kind k
- ginf k     : infimum operation of kind k 
where k is an "informative predicate on subsets", for instance
- k P = is_empty P   for bottom/top elements
- k P = is_pair P    for binary joins/meet
- k P = chain P      for chain sups 
- k P = cochain P    for (co)chain infs (cochain is only equivalent to chain, not equal, unfortunately)
- k P = directed P   for directed sups 
- k P = codirected P for (co)directed infs 
- k P = True         for arbitrary sups/infs


The construction of dependent product spaces and spaces of extensive/monotone functions are carried out once and for all on generic sups/infs, and then transported to the various structures automatically


# DECIDABILITY, TOTALITY, CLASSICAL LOGIC

A partial order is 
- decidable when the relation [<=] is decidable
- classic when [forall x y, x <= y \/ ~ y <= x]
- a chain when [forall x y, x <= y \/ y <= x]
- total (or linear) when [forall x y, x <= y \/ y < x]
  (with x<y if x<=y /\ ~ y<=x)

We have the following implications (top-down):

decidable
   \        total
    \      /     \
    classic     chain

In fact, a partial order is total iff it is both classic and a chain
