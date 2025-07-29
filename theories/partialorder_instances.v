Require Export totalorder.

(** products, sums, option *)
Section s.
 Variables X Y: PO.type.

 (** lexicographic product *)
 (** we use an alias for product to guide structure inferrence *)
 (** TOREPORT? we need to eta expand this alias otherwise we run into universe problems later on... *)
 Definition lex_prod X Y := prod X Y. 
 HB.instance Definition _ := Setoid.on (lex_prod X Y).
 Definition leq_lex_prod: relation (lex_prod X Y) :=
   fun p q => fst p <= fst q /\ (fst q <= fst p -> snd p <= snd q).
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

 (** [option] type, adding [None] as top element *)
 (* TODO: propose the other variant;
    do it via sequential_sum and unit? *)
 Definition leq_option (p q: option X) :=
  match q,p with Some q,Some p => p<=q | None,_ => True | _,_ => False end.
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
Arguments leq_option [_] _ _/.
