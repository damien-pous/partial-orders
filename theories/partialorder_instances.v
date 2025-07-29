Require Export partialorder.

Local Obligation Tactic := idtac. (* mitigate painful behaviour or [Program] *)


(** * instance constructors for partial orders *)
  
Section s.
 Variables X Y: PO.type.

 (** lexicographic ordering on pairs *)
 (** we use an alias for product to guide structure inferrence *)
 (** TOREPORT? we need to eta expand this alias otherwise we run into universe problems later on... *)
 Definition lex_prod X Y := prod X Y. 
 HB.instance Definition _ := Setoid.on (lex_prod X Y).
 Definition leq_lex_prod: relation (lex_prod X Y) :=
   fun p q => p.1 <= q.1 /\ (q.1 <= p.1 -> p.2 <= q.2).
 Lemma po_lex_prod: po_axm leq_lex_prod.
 Proof.
   unfold leq_lex_prod.
   apply: mk_po_axm.
   - split=>//.
     move=>[x x'][y y'][z z']/=[xy xy'][yz yz']. split.
     by transitivity y.
     move=>zx. transitivity y'.
     apply: xy'. by transitivity z. 
     apply: yz'. by transitivity x.
   - move=>[??][??]. cbn. rewrite 2!eqv_of_leq. intuition.
 Qed.
 HB.instance Definition _ := isPO.Build (lex_prod X Y) po_lex_prod.

 (** direct sum (called "parallel" by opposition with the sequential operation below) *)
 Definition leq_parallel_sum: relation (X+Y) :=
   fun p q => match p,q with
           | inl x,inl y | inr x,inr y => x<=y
           | _,_ => False
           end.
 Lemma po_parallel_sum: po_axm leq_parallel_sum.
 Proof.
   apply: mk_po_axm. split.
   by case=>//=.
   by case=>?; case=>y; case=>?//=; transitivity y.
   case=>x; case=>y; cbn; rewrite ?eqv_of_leq; tauto. 
 Qed.
 HB.instance Definition _ :=
   isPO.Build (sum X Y) po_parallel_sum.
 HB.instance Definition _ :=
   isMonotone.Build X (sum X Y) inl (fun p q pq => pq).
 HB.instance Definition _ :=
   isMonotone.Build Y (sum X Y) inr (fun p q pq => pq).

 (** sequential sum *)
 Definition sequential_sum := sum. 
 HB.instance Definition _ := Setoid.on (sequential_sum X Y).
 Definition leq_sequential_sum: relation (sequential_sum X Y) :=
   fun p q => match p,q with
           | inl x,inl y | inr x,inr y => x<=y
           | inl _,inr _ => True
           | _,_ => False
           end.
 Lemma po_sequential_sum: po_axm leq_sequential_sum.
 Proof.
   apply: mk_po_axm. split.
   by case=>//=.
   by case=>?; case=>y; case=>?//=; transitivity y.
   case=>x; case=>y; cbn; rewrite ?eqv_of_leq; tauto. 
 Qed.
 HB.instance Definition _ := isPO.Build (sequential_sum X Y) po_sequential_sum.

 (** pointwise ordering on lists (of the same length) *)
 Fixpoint leq_list (h k: list X) :=
   match h,k with nil,nil => True | cons x h,cons y k => x<=y /\ leq_list h k | _,_ => False end.
 Lemma po_list: po_axm leq_list.
 Proof.
  apply: mk_po_axm. split. 
   - by elim=>//.
   - elim=>[//|a h IH] [//|b k] [//|c l] //= [ab hk] [bc kl]. split.
     by transitivity b.
     by apply IH with k.
   - cbn. elim=>[|a h IH] [|b k]/=; try tauto.
     rewrite IH eqv_of_leq. tauto.
 Qed.
 HB.instance Definition _ := isPO.Build (list X) po_list.

 (** lexicographic ordering on lists *)
 Definition lex_list X := list X. 
 HB.instance Definition _ := Setoid.on (lex_list X).
 Fixpoint leq_lex_list (h k: lex_list X) :=
   match h,k with nil,_ => True | cons x h,cons y k => x<=y /\ (y<=x -> leq_lex_list h k) | _,_ => False end.
 Lemma po_lex_list: po_axm leq_lex_list.
 Proof.
  apply: mk_po_axm. split. 
   - by elim=>//.
   - elim=>[//|a h IH] [//|b k] [//|c l] /=[ab hk] [bc kl]. split.
     by transitivity b.
     move=>ca. apply IH with k.
     apply: hk. by transitivity c. 
     apply: kl. by transitivity a.
   - cbn. elim=>[|a h IH] [|b k]/=; try tauto.
     rewrite IH eqv_of_leq. tauto.
 Qed.
 HB.instance Definition _ := isPO.Build (lex_list X) po_lex_list.
 
 (** [option] type, adding [None] as bottom element *)
 (* TODO: propose the other variant;
    do it via sequential_sum and unit? *)
 Definition leq_option (p q: option X) :=
  match p,q with Some p,Some q => p<=q | None,_ => True | _,_ => False end.
 Lemma po_option: po_axm leq_option.
 Proof.
   apply: mk_po_axm. split.
   by move=>[?|]//=. 
   by move=>[?|][y|][?|]??//=; transitivity y. 
   case=>[?|]; case=>[?|]; cbn; rewrite ?eqv_of_leq; tauto.
 Qed.
 HB.instance Definition _ := isPO.Build (option X) po_option.
End s. 
Arguments leq_lex_prod [_ _] _ _/.
Arguments leq_parallel_sum [_ _] _ _/.
Arguments leq_sequential_sum [_ _] _ _/.
Arguments leq_list [_] _ _/.
Arguments leq_lex_list [_] _ _/.
Arguments leq_option [_] _ _/.

Lemma leq_lex_alt {X: ClassicPO.type} {Y: PO.type} (p q: lex_prod X Y):
  p <= q <-> p.1 < q.1 \/ p.1 ≡ q.1 /\ p.2 <= q.2.
Proof.
  case: p=>[x y]. case: q=>[x' y']. cbn.
  rewrite (le_lt_or_eqv x x'). split.
  - move=>[[H|H] H']. tauto. right. split=>//. apply: H'. exact: eqv_geq.
  - move=>[H|[H H']]. 2: tauto. split. by left.
    move=>H'. exfalso. exact: (lt_nle H H'). 
Qed.

(** * instance constructors for classic partial orders *)
  
Section s.
 Variables X Y: ClassicPO.type.

 (** direct product *)
 Program Definition classic_po_prod := PO_isClassic.Build (prod X Y) _.
 Next Obligation.
   intros p q. cbn. 
   destruct (leq_classic p.1 q.1); destruct (leq_classic p.2 q.2); tauto.
 Qed.
 HB.instance Definition _ := classic_po_prod. 
 
 (** lexicographic ordering on pairs *)
 Program Definition classic_po_lex_prod := PO_isClassic.Build (lex_prod X Y) _.
 Next Obligation.
   intros p q. cbn.
   destruct (leq_classic p.1 q.1); destruct (leq_classic p.2 q.2); try tauto.
   destruct (leq_classic q.1 p.1); tauto.
 Qed.
 HB.instance Definition _ := classic_po_lex_prod. 

 (** direct (or parallel) sum *)
 Program Definition classic_po_sum := PO_isClassic.Build (sum X Y) _.
 Next Obligation.
   move=> [x|y] [x'|y']; cbn; try tauto; exact: leq_classic.
 Qed.
 HB.instance Definition _ := classic_po_sum. 

 (** sequential sum *)
 Program Definition classic_po_sequential_sum := PO_isClassic.Build (sequential_sum X Y) _.
 Next Obligation.
   move=> [x|y] [x'|y']; cbn; try tauto; exact: leq_classic.
 Qed.
 HB.instance Definition _ := classic_po_sequential_sum. 

 (** list type *)
 Program Definition classic_po_list := PO_isClassic.Build (list X) _.
 Next Obligation.
   elim=> [|a h IH] [|b k].
   - by left. 
   - by right. 
   - by right.
   - case: (leq_classic a b). 2: cbn; tauto.
     case: (IH k). by left. cbn; tauto. 
 Qed.
 HB.instance Definition _ := classic_po_list. 

 (** lexicographic list type *)
 Program Definition classic_po_lex_list := PO_isClassic.Build (lex_list X) _.
 Next Obligation.
   elim=> [|a h IH]. by left.
   case=>[|b k]. by right. 
   - case: (leq_classic a b). 2: cbn; tauto.
     case: (leq_classic b a). 2: cbn; tauto.
     case: (IH k). 2: cbn; tauto. by left.
 Qed.
 HB.instance Definition _ := classic_po_lex_list. 

 (** option type *)
 Program Definition classic_po_option := PO_isClassic.Build (option X) _.
 Next Obligation.
   move=> [x|] [x'|]; cbn; try tauto; exact: leq_classic. 
 Qed.
 HB.instance Definition _ := classic_po_option. 
End s. 

(** * instance constructors for decidable partial orders *)

Section s.
 Variables X Y: DecidablePO.type.

 (** direct product *)
 Definition leqb_prod (p q: prod X Y) := (p.1 <=? q.1) && (p.2 <=? q.2).
 Program Definition dpo_prod := PO_isDecidable.Build (prod X Y) leqb_prod _.
 Next Obligation. move=>/=x y. apply: andPP; exact: leq_dec. Qed.
 HB.instance Definition _ := dpo_prod.

 (** lexicographic product *)
 Definition leqb_lex_prod (p q: lex_prod X Y) := (p.1 <=? q.1) && ((q.1 <=? p.1) ==> (p.2 <=? q.2)).
 Program Definition dpo_lex_prod := PO_isDecidable.Build (lex_prod X Y) leqb_lex_prod _.
 Next Obligation.
   move=>/=x y. apply: andPP.
   exact: leq_dec.
   apply: implyPP; exact: leq_dec.
 Qed.
 HB.instance Definition _ := dpo_lex_prod.

 (** direct (parallel) sum *)
 Definition leqb_parallel_sum (p q: X+Y) :=
   match p,q with
   | inl x,inl y | inr x,inr y => x<=?y
   | _,_ => false
   end.
 Program Definition dpo_sum := PO_isDecidable.Build (sum X Y) leqb_parallel_sum _.
 Next Obligation.
   move=>/=[x|y] [x'|y']; cbn; by [ exact: leq_dec | exact: ReflectF ].
 Qed.
 HB.instance Definition _ := dpo_sum.

 (** sequential sum *)
 Definition leqb_sequential_sum (p q: sequential_sum X Y) :=
   match p,q with
   | inl x,inl y | inr x,inr y => x<=?y
   | inl _,inr _ => true
   | _,_ => false
   end.
 Program Definition dpo_sequential_sum := PO_isDecidable.Build (sequential_sum X Y) leqb_sequential_sum _.
 Next Obligation.
   move=>/=[x|y] [x'|y']; cbn; by [exact: leq_dec | exact: ReflectF | exact: ReflectT].
 Qed.
 HB.instance Definition _ := dpo_sequential_sum.

 (** pointwise ordering on lists *)
 Fixpoint leqb_list (h k: list X) :=
   match h,k with nil,nil => true | cons x h,cons y k => (x<=?y) && leqb_list h k | _,_ => false end.
 Program Definition dpo_list := PO_isDecidable.Build (list X) leqb_list _.
 Next Obligation.
   elim=>[|a h IH] [|b k]. exact: ReflectT. exact: ReflectF. exact: ReflectF.
   apply: andPP. exact: leq_dec. exact: IH. 
 Qed.
 HB.instance Definition _ := dpo_list.

 (** lexicographic ordering on lists *)
 Fixpoint leqb_lex_list (h k: lex_list X) :=
   match h,k with nil,_ => true | cons x h,cons y k => (x<=?y) && ((y<=?x) ==> leqb_lex_list h k) | _,_ => false end.
 Program Definition dpo_lex_list := PO_isDecidable.Build (lex_list X) leqb_lex_list _.
 Next Obligation.
   elim=>[|a h IH]. intro. exact: ReflectT.
   case=>[|b k]. exact: ReflectF.
   apply: andPP. exact: leq_dec. apply: implyPP. exact: leq_dec. exact: IH. 
 Qed.
 HB.instance Definition _ := dpo_lex_list.

 (** option type *)
 Definition leqb_option (p q: option X) :=
   match p,q with
   | Some x,Some y => x<=?y
   | None, _ => true
   | _,_ => false
   end.
 Program Definition dpo_option := PO_isDecidable.Build (option X) leqb_option _.
 Next Obligation.
   move=>/=[x|] [x'|]; cbn; by [exact: leq_dec | exact: ReflectF | exact: ReflectT].
 Qed.
 HB.instance Definition _ := dpo_option.

End s. 
Arguments leqb_prod [_ _] _ _/.
Arguments leqb_lex_prod [_ _] _ _/.
Arguments leqb_parallel_sum [_ _] _ _/.
Arguments leqb_sequential_sum [_ _] _ _/.
Arguments leqb_list [_] _ _/.
Arguments leqb_lex_list [_] _ _/.
Arguments leqb_option [_] _ _/.
HB.saturate prod. 
HB.saturate sum. 
HB.saturate list. 
HB.saturate option. 


(** * instance constructors for chains (and thus total orders) *)

(** lexicographic product *)
Program Definition chain_lex_prod (X: Order.type) (Y: Chain.type) :=
  PO_isChain.Build (lex_prod X Y) _.
Next Obligation.
  intros X Y [x y] [x' y'].
  rewrite 2!leq_lex_alt/=.
  move: (compare x x')=>[xx'|[xx'|xx']]. 1,3: tauto.
  case: (leq_chain y y').  
  - tauto.
  - symmetry in xx'. tauto.
Qed.
HB.instance Definition _ X Y := chain_lex_prod X Y.
HB.saturate lex_prod. 

(** sequential sum *)
Program Definition chain_sequential_sum (X Y: Chain.type) :=
  PO_isChain.Build (sequential_sum X Y) _.
Next Obligation.
  intros X Y [x|y] [x'|y']; cbn; try tauto; exact: leq_chain.
Qed.
HB.instance Definition _ X Y := chain_sequential_sum X Y.
HB.saturate sequential_sum. 
 
(** lexicographic ordering on lists *)
Program Definition chain_lex_list (X: Order.type) := PO_isChain.Build (lex_list X) _.
Next Obligation.
  intros X. 
  elim=>[|a h IH]. by left.
  case=>[|b k]. by right.
  case: (compare a b)=>[ab|[ab|ab]].
  - left. split. exact: lt_le. move=>ba. exfalso. exact: (lt_nle ab ba).
  - case: (IH k).
    -- left. split. exact: eqv_leq. done.
    -- right. split. exact: eqv_geq. done.
  - right. split. exact: lt_le. move=>ba. exfalso. exact: (lt_nle ab ba).
Qed.
HB.instance Definition _ X := chain_lex_list X. 

(** option type *)
Program Definition chain_option (X: Chain.type) :=
  PO_isChain.Build (option X) _.
Next Obligation.
  intros X [x|] [x'|]; cbn; try tauto; exact: leq_chain.
Qed.
HB.instance Definition _ X := chain_option X.
HB.saturate option. 
