Require Import Setoid Morphisms Basics.
Require Import ssreflect ssrfun ssrbool.
Require Import Classical.

Set Implicit Arguments.


Parameter C: Type.
Parameter leq: relation C.
Infix "<=" := leq (at level 70).
Parameter PreOrder_leq: PreOrder leq.
Parameter antisym: forall x y, x <= y -> y <= x -> x = y. 
#[export] Existing Instance PreOrder_leq.
#[export] Hint Extern 0 => reflexivity: core.
#[export] Instance rew_leq: RewriteRelation leq := {}.


Parameter sup: (C -> Prop) -> C.
Parameter sup_spec: forall P z, sup P <= z <-> forall x, P x -> x <= z.

Implicit Types x y z c: C.
Implicit Types P Q: C -> Prop.

Lemma leq_sup: forall P x, P x -> x <= sup P. 
Proof. now intros ??; apply sup_spec. Qed.
#[export] Hint Resolve leq_sup: core.

Lemma eq_leq: forall x y, x = y -> x <= y.
Proof. by move=>??<-. Qed.

Definition sup_closed P := forall Q, (forall x, Q x -> P x) -> P (sup Q).

#[export] Instance sup_closed_iff: Proper (pointwise_relation _ iff ==> iff) sup_closed.
Proof.
  suff E: Proper (pointwise_relation _ iff ==> impl) sup_closed.
  by move=>P Q PQ; split; apply E=>//; symmetry. 
  move=>P Q PQ HP T TQ. apply PQ. by apply HP=>x Tx; apply PQ, TQ.
Qed.


Definition choose x y := forall P, (forall p, P p -> p <= x \/ y <= p) -> sup P <= x \/ y <= sup P.
(* a weak consequence of EM *)
Lemma choose1: forall x y, x <= y -> choose x y. (* only used with y=f x *)
Proof.
  move=>x y _ P HP.
  classical_left. apply sup_spec=>z Pz. case: (HP z Pz)=>//yz.
  contradict H. rewrite yz; auto. 
Qed.
(* a possibly even weaker one *)
Lemma choose2: forall x, choose x x.
Proof. intro. by apply choose1. Qed.
Lemma choose2': forall x P, (forall p, P p -> p <= x \/ x <= p) -> sup P <= x \/ exists z, P z /\ x <= z.
Proof.                          (* stronger than choose2? *)
  move=>x P HP.
  classical_left. apply sup_spec=>z Pz. case: (HP z Pz)=>//yz.
  contradict H. eauto. 
Qed.

Parameter f: C -> C.
Parameter tower: forall P, sup_closed P -> (forall x, P x -> P (f x)) -> forall x, P x.

Section s.
  Hypothesis Hf: forall x, x <= f x.
  Theorem strong_chain: forall x y, x <= y \/ f y <= x.
  Proof.
   (* essentially your (Jules) proof *)
   apply: tower. 
   - intros T IH c. by apply choose1; auto.
   - intros x IHx y. 
     have H: f x <= y \/ y <= x. {
       revert y. apply: tower.
       -- setoid_rewrite or_comm=>T IH. by apply choose1. 
       -- move=>y IHy. case: (IHx y); auto=>xy. left. 
          case: IHy=>yx. by rewrite yx.
          by apply eq_leq, f_equal, antisym.  
     }
     case: H; auto=>yx. right. case: (IHx y)=>xy.
     by apply eq_leq, f_equal, antisym.  
     by rewrite xy.
  Qed.
  (* is there a more direct proof of this corollary? *)
  Corollary ext_implies_mon: Proper (leq ==> leq) f. 
  Proof.
    move=>x y xy. case: (strong_chain y x)=>yx.
    by apply eq_leq, f_equal, antisym.
    by rewrite yx.
  Qed.
  Corollary chain: forall x y, x <= y \/ y <= x.
  Proof.
    move=>x y. case: (strong_chain x y); auto=>xy.
    by right; rewrite -xy.
  Qed.

  Definition inf P := sup (fun x => forall y, P y -> x <= y).
  Lemma inf_spec: forall P z, z <= inf P <-> forall x, P x -> z <= x.
  Proof.
    split=>[H x Px|H].
    by rewrite H; apply sup_spec; auto.
    by apply leq_sup.
  Qed.
  Lemma geq_inf: forall P x, P x -> inf P <= x. 
  Proof. now intros ??; apply inf_spec. Qed.
  Hint Resolve geq_inf: core.

  Definition up P := fun y => exists x, P x /\ x <= y.
  Lemma up_up_closed P: Proper (leq ==> impl) (up P).
  Proof. move=>x y xy [z [Pz xz]]. by exists z; split=>//; transitivity x. Qed.
  Lemma up_ext P x: P x -> up P x.
  Proof. move=>Px. by exists x; split. Qed.
  Lemma inf_up P: inf P = inf (up P).
  Proof.
    apply antisym.
    apply inf_spec=>x [y [Py <-]]. eapply inf_spec; eauto.
    apply inf_spec=>x Px. eapply inf_spec; eauto using up_ext.
  Qed.
  
  Proposition wf1: forall P x, P x -> P (inf P).
  Proof.
    have E: forall x P, Proper (leq ==> impl) P -> P x -> P (inf P). {
    apply: tower.
    - move=>Q IH P uP iP.
      case: (classic (exists x, Q x /\ P x))=>[[x [Qx Px]]|N]. by eapply IH; eauto.
      replace (inf P) with (sup Q)=>//. apply antisym; auto.
      apply sup_spec=>x Qx.
      apply inf_spec=>y Py.
      case: (chain x y); auto=>yQ.
      contradict N. exists x; split=>//; eapply uP; eauto.
    - move=>x IH P uP iP. 
      case: (classic (P x))=>[Px|nPx]. by apply IH.
      replace (inf P) with (f x)=>//.
      apply antisym; auto.
      apply inf_spec=>z Pz.
      case: (strong_chain z x); auto=>Px. 
      contradict nPx. eapply uP; eauto.
    }      
    move=>P x Px.
    case: (E x (up P)). by apply up_up_closed. by apply up_ext.
    move=>y [Py Hy].
    replace (inf P) with y=>//. apply antisym; auto.
    by rewrite inf_up.
  Qed.
  
  Definition lt x y := x <= y /\ ~ y <= x.
  Infix "<" := lt.
  Lemma ltle_lt x y z: x < y -> y <= z -> x < z.
  Proof.
    move=>[xy yx] yz. split. by transitivity y.
    contradict yx. by transitivity z.
  Qed.
  Corollary lt_leq x y: x < f y -> x <= y.
  Proof. case: (strong_chain x y)=>?[]; tauto. Qed. 

  Theorem wf2: well_founded lt.
  Proof.
    have E: forall x, (forall y, y<=x -> Acc lt y). {
      apply: tower.
      - move=>T IH y yx. constructor=>z zy. 
        have zx: z < sup T by apply ltle_lt with y.
        case: (choose1 yx T). 
        by move=>*; apply chain.
        (* case: (@choose2 z T). *)
        (* by move=>*; apply chain. *)
        (* -- move=>H. apply proj2 in zx. tauto. *)
        (* -- move=>[u [Tu /=zu]]. by apply IH with u. *)
      - move=>x IH y yx. constructor=>z zy. apply IH.
        apply lt_leq. eapply ltle_lt; eassumption.
    }
    by move=>?; eauto.
  Qed.
  
End s. 

Section t.
  (* a stronger hypothesis *)
  Hypothesis Hf: Proper (leq ==> leq) f.
  Lemma mon_implies_ext: forall x, x <= f x.
  Proof.
    apply: tower.
    - move=>Q HQ. apply sup_spec=>x Qx. rewrite (HQ _ Qx). by apply Hf; auto.
    - intros. by apply Hf.
  Qed.
  (* yielding a weaker result, but using less classical logic ([choose2] vs [choose1]) *)
  Lemma chain': forall x y, x <= y \/ y <= x.
  Proof.
    apply: tower.
    - move=>T IH y. by apply choose2; auto.
    - move=>x IH.
      apply: tower.
      -- setoid_rewrite or_comm=>T IH'. by apply choose2. 
      -- move=>y _. by case: (IH y); [left|right]; apply Hf.
  Qed.
  (* not used anymore *)
  Lemma leq_next: forall x y, (forall z, f z <= x -> z <= y) -> x <= f y.
  Proof.
    apply: tower.
    - move=>T IH y H. apply sup_spec=>x Tx. apply IH=>//z zx.
      apply H. rewrite zx; auto.
    - move=>x IH y H. by apply Hf, H.
  Qed.
End t. 
