From PartialOrders Require Import gfp.

Print Assumptions BourbakiWitt.is_fixpoint.
Print Assumptions BourbakiWitt.is_greatest_fixpoint.
Print Assumptions Pataraia.is_greatest_fixpoint.


(* SANITY *)
Check Prop: infCL.type.
Check Prop: CPO'.type.
Check nat -> Prop: dCPO'.type.
Check nat -> Prop: CPO'.type.
Check fun X: dCPO'.type => (X-mon->X): dCPO'.type. 
Check fun X: CPO'.type => (X-mon->X): CPO'.type. 
Check fun X: CPO'.type => (nat -> X): CPO'.type. 
Check fun X: CPO'.type => ((nat -> X) -mon-> (nat -> X)): CPO'.type. 
Check fun X: infCL.type => (X-mon->X): infCL.type. 
Check fun X: dCPO'.type => (X-mon->X): CPO'.type.

Check fun X: dCPO'.type => fun f: X-mon->X => gfp f: X.
Check fun X: CPO'.type => fun f: X-mon->X => gfp f: X.
Check fun X: infCL.type => fun f: X-mon->X => gfp f: X.
Check let X := (nat->bool->Prop) in fun f: X-mon->X => gfp f: X.

Check fun X: dCPO'.type => let X := nat -> X in fun f: X-mon->X => gfp f: X. (* A *)
Fail Check fun X: CPO'.type => let X := nat -> X in fun f: X-mon->X => gfp f: X. (* B *)
(* the above line fails because the canonical way to get a [gfpPO] on [nat->X] is to look for a dCPO' structure on [X] ; looking for a CPO' on X (thus eventuelly using EM) would be legitimate, though
   (if we had declared the previous instances in the other order we would have let B pass and A fail)
 *)
Check fun X: infCL.type => let X := nat -> X in fun f: X-mon->X => gfp f: X.

Definition testX: dCPO'.type := nat->bool->Prop.
Print Assumptions testX.        (* closed *)

Definition testX': CPO'.type := nat->bool->Prop.
Print Assumptions testX'.       (* EM *)

Definition test (f: (nat->bool->Prop) -mon-> (nat->bool->Prop)) := gfp f. 
Print Assumptions test.         (* closed *)

Definition test' (X: CPO'.type) (f: X -mon-> X) := gfp f. 
Print Assumptions test'.        (* closed *)
