(* Full safety for STLC *)

(*

STLC, binary logical relation, contextual equivalence.

Includes a proof of beta equivalence.

*)

Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Lists.List.
Require Import Psatz.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Require Import tactics.
Require Import env.

Module STLC.

(* ---------- language syntax ---------- *)

Definition id := nat.

Inductive ty : Type :=
  | TBool  : ty
  | TFun   : ty -> ty -> ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tapp : tm -> tm -> tm (* f(x) *)
  | tabs : tm -> tm (* \f x.y *)
.

Inductive vl : Type :=
| vbool : bool -> vl
| vabs  : list vl -> tm -> vl
.

Definition venv := list vl.
Definition tenv := list ty.

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.


(* ---------- syntactic typing rules ---------- *)

Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
           has_type env ttrue TBool
| t_false: forall env,
           has_type env tfalse TBool
| t_var: forall x env T1,
           indexr x env = Some T1 ->
           has_type env (tvar x) T1
| t_app: forall env f x T1 T2,
           has_type env f (TFun T1 T2) ->
           has_type env x T1 ->
           has_type env (tapp f x) T2
| t_abs: forall env y T1 T2,
           has_type (T1::env) y T2 -> 
           has_type env (tabs y) (TFun T1 T2)
.


(* ---------- operational semantics ---------- *)

(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
*)

Fixpoint teval(n: nat)(env: venv)(t: tm){struct n}: option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | ttrue      => Some (Some (vbool true))
        | tfalse     => Some (Some (vbool false))
        | tvar x     => Some (indexr x env)
        | tabs y     => Some (Some (vabs env y))
        | tapp ef ex   =>
          match teval n env ef with
            | None => None
            | Some None => Some None
            | Some (Some (vbool _)) => Some None
            | Some (Some (vabs env2 ey)) =>
              match teval n env ex with
                | None => None
                | Some None => Some None
                | Some (Some vx) =>
                  teval n (vx::env2) ey
              end
          end
      end
  end.


Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).


(* ---------- LR definitions  ---------- *)

Fixpoint val_type v1 v2 T : Prop := match v1, v2, T with
| vbool b1, vbool b2, TBool => b1 = b2
| vabs G1 ty1, vabs G2 ty2, TFun T1 T2 => 
  (forall vx1 vx2, 
     val_type vx1 vx2 T1 ->  
     exists vy1 vy2, 
       tevaln (vx1::G1) ty1 vy1 /\
       tevaln (vx2::G2) ty2 vy2 /\
       val_type vy1 vy2 T2) 
| _,_,_ => False
end.

Definition exp_type H1 H2 t1 t2 T :=
  exists v1 v2,
    tevaln H1 t1 v1 /\  
    tevaln H2 t2 v2 /\ 
    val_type v1 v2 T.

Definition env_type H1 H2 G := 
  length H1 = length G /\
  length H2 = length G /\
  forall x T,
    indexr x G = Some T ->
    exists v1 v2,
      indexr x H1 = Some v1 /\
      indexr x H2 = Some v2 /\
      val_type v1 v2 T.

Definition sem_type G e1 e2 T:=
  forall H1 H2,
    env_type H1 H2 G ->
    exp_type H1 H2 e1 e2 T.


#[global] Hint Constructors ty: core.
#[global] Hint Constructors tm: core.
#[global] Hint Constructors vl: core.


#[global] Hint Constructors has_type: core.

#[global] Hint Constructors option: core.
#[global] Hint Constructors list: core.

(* ---------- LR helper lemmas  ---------- *)

Lemma envt_empty:
    env_type [] [] [].
Proof.
  intros. split. 2: split.
  eauto. eauto. intros. inversion H. 
Qed.

Lemma envt_extend: forall E1 E2 G v1 v2 T,
    env_type E1 E2 G ->
    val_type v1 v2 T ->
    env_type (v1::E1) (v2::E2) (T::G).
Proof.
  intros. 
  remember H as WFE. clear HeqWFE.
  destruct H as (L1 & L2 & ?). split. 2: split.
  simpl. eauto. simpl. eauto.
  intros x T' IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX. subst T.
    exists v1, v2. split. 2: split.
    rewrite <- L1. rewrite indexr_head. eauto.
    rewrite <- L2. rewrite indexr_head. eauto.
    eauto.
  - rewrite indexr_skip in IX; eauto.
    eapply WFE in IX as IX. destruct IX as (v1' & v2' & ? & ? & ?).
    exists v1', v2'. split. 2: split.
    rewrite indexr_skip; eauto. lia.
    rewrite indexr_skip; eauto. lia.
    eauto.
Qed.

  
(* ---------- LR compatibility lemmas  ---------- *)

Lemma exp_true: forall H1 H2,
    exp_type H1 H2 ttrue ttrue TBool.
Proof.
  intros. 
  exists (vbool true). exists (vbool true). split. 2: split. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto.
Qed.

Lemma exp_false: forall H1 H2,
    exp_type H1 H2 tfalse tfalse TBool.
Proof.
  intros.
  exists (vbool false). exists (vbool false). split. 2: split. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto.
Qed.

Lemma exp_var: forall H1 H2 x1 x2 v1 v2 T,
    indexr x1 H1 = Some v1 ->
    indexr x2 H2 = Some v2 ->
    val_type v1 v2 T ->
    exp_type H1 H2 (tvar x1) (tvar x2) T.
Proof.
  intros ? ? ? ? ? ? ? IX1 IX2.
  exists v1. exists v2. split. 2: split. 
  - exists 0. intros. destruct n. lia. simpl. rewrite IX1. eauto.
  - exists 0. intros. destruct n. lia. simpl. rewrite IX2. eauto. 
  - eauto.
Qed.

Lemma exp_app: forall H1 H2 f1 f2 t1 t2 T1 T2,
    exp_type H1 H2 f1 f2 (TFun T1 T2) ->
    exp_type H1 H2 t1 t2  T1 ->
    exp_type H1 H2 (tapp f1 t1) (tapp f2 t2) T2.
Proof.
  intros ? ? ? ? ? ? ? ? E1 E2.
  destruct E1 as (vf1 & vf2 & STF1 & STF2 & VF).
  destruct E2 as (vx1 & vx2 & STX1 & STX2 & VX).
  destruct vf1, vf2; simpl in VF; intuition.
  edestruct VF as (vy1 & vy2 & STY1 & STY2 & VY). eauto. 
  exists vy1, vy2. split. 2: split. 
  - destruct STF1 as (n1 & STF1).
    destruct STX1 as (n2 & STX1).
    destruct STY1 as (n3 & STY1).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite STF1, STX1, STY1. 2,3,4: lia.
    eauto.
  - destruct STF2 as (n1 & STF2).
    destruct STX2 as (n2 & STX2).
    destruct STY2 as (n3 & STY2).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite STF2, STX2, STY2. 2,3,4: lia.
    eauto.
  - eauto.
Qed.

Lemma exp_abs: forall H1 H2 t1 t2 T1 T2,
    (forall vx1 vx2,
        val_type vx1 vx2 T1 ->
        exp_type (vx1 :: H1) (vx2 :: H2) t1 t2 T2) ->
    exp_type H1 H2 (tabs t1) (tabs t2) (TFun T1 T2).
Proof.
  intros ? ? ? ? ? ? HY. 
  exists (vabs H1 t1). exists (vabs H2 t2). split. 2: split. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros. eapply HY. eauto.
Qed.


Lemma sem_true: forall G,
    sem_type G ttrue ttrue TBool.
Proof.
  intros. intros H1 H2 WFE. eapply exp_true. 
Qed.

Lemma sem_false: forall G,
    sem_type G tfalse tfalse TBool.
Proof.
  intros. intros H1 H2 WFE. eapply exp_false.
Qed.

Lemma sem_var: forall G x T,
    indexr x G = Some T ->
    sem_type G (tvar x) (tvar x) T.
Proof.
  intros. intros H1 H2 WFE.
  eapply WFE in H as IX. destruct IX as (v1 & v2 & IX1 & IX2 & VX).
  eapply exp_var; eauto. 
Qed.

Lemma sem_app: forall G f1 f2 t1 t2 T1 T2,
    sem_type G f1 f2 (TFun T1 T2) ->
    sem_type G t1 t2  T1 ->
    sem_type G (tapp f1 t1) (tapp f2 t2) T2.
Proof.
  intros ? ? ? ? ? ? ? HF HX. intros E1 E2 WFE.
  eapply exp_app. eapply HF; eauto. eapply HX; eauto. 
Qed.

Lemma sem_abs: forall G t1 t2 T1 T2,
    sem_type (T1::G) t1 t2 T2 ->
    sem_type G (tabs t1) (tabs t2) (TFun T1 T2).
Proof.
  intros ? ? ? ? ? HY. intros E1 E2 WFE.
  assert (length E1 = length G) as L1. eapply WFE.
  assert (length E2 = length G) as L2. eapply WFE.
  eapply exp_abs. intros. eapply HY. eapply envt_extend. eauto. eauto.
Qed.


(* ---------- LR fundamental property  ---------- *)

Theorem fundamental : forall e G T,
    has_type G e T ->
    sem_type G e e T.
Proof.
  intros ? ? ? W. 
  induction W.
  - eapply sem_true; eauto.
  - eapply sem_false; eauto.
  - eapply sem_var; eauto.
  - eapply sem_app; eauto. 
  - eapply sem_abs; eauto.
Qed.

Corollary safety: forall t T,
  has_type [] t T ->
  exp_type [] [] t t T.
Proof. 
  intros. eapply fundamental in H as ST; eauto.
  destruct (ST [] []) as (v1 & v2 & ? & ? & ?).
  eapply envt_empty.
  exists v1, v2. intuition.
Qed.


(* ---------- LR contextual equivalence  ---------- *)

(* Define typed contexts and prove that the binary logical
   relation implies contextual equivalence (congruency wrt
   putting expressions in context *)

(* Q: Do we need to prove a theorem that these are all
   possible contexts? Do we need to consider only one-hole
   contexts or also (fun x => tapp x x)? *)

Inductive ctx_type : (tm -> tm) -> tenv -> ty -> tenv -> ty -> Prop :=
| c_top: forall G T,
    ctx_type (fun x => x) G T G T
| c_app1: forall e2 G T1 T2,
    has_type G e2 T1 ->
    ctx_type (fun x => tapp x e2) G (TFun T1 T2) G T2
| c_app2: forall e1 G T1 T2,
    has_type G e1 (TFun T1 T2) ->
    ctx_type (fun x => tapp e1 x) G T1 G T2
| c_abs: forall G T1 T2,
    ctx_type (fun x => tabs x) (T1::G) T2 G (TFun T1 T2).

Theorem congr:
  forall C G1 T1 G2 T2,
    ctx_type C G1 T1 G2 T2 ->
  forall e e',
    sem_type G1 e e' T1 ->
    sem_type G2 (C e) (C e') T2.
Proof.
  intros ? ? ? ? ? CX.
  induction CX; intros.
  - eauto.
  - eapply sem_app. eauto. eapply fundamental. eauto.
  - eapply sem_app. eapply fundamental. eauto. eauto.
  - eapply sem_abs. eauto.
Qed.

Lemma adequacy: forall e e' T,
  sem_type [] e e' T ->
  (exists v, tevaln [] e v) <-> 
  (exists v', tevaln [] e' v').
Proof. 
  intros. 
  assert (env_type [] [] []) as WFE. { unfold env_type; intuition. inversion H0. }
  unfold sem_type in H. specialize (H [] [] WFE). 
  destruct H as [? [? [? [? ?]]]].
  split. 
  + intros. exists x0. intuition.
  + intros. exists x. intuition.
Qed.

Definition context_equiv G t1 t2 T1 :=
  has_type G t1 T1 ->
  has_type G t2 T1 ->
  forall C,
    ctx_type C G T1 [] TBool ->
    (exists v1, tevaln [] (C t1) v1) <->
    (exists v2, tevaln [] (C t2) v2).

(* soundness of binary logical relations *)
Theorem soundess: forall G t1 t2 T,
  sem_type G t1 t2 T ->
  context_equiv G t1 t2 T.
Proof.
  intros. unfold context_equiv. intros.
  assert (sem_type [] (C t1) (C t2) TBool). {
    specialize (congr C G  T [] TBool); intuition.
  }
  eapply adequacy; eauto. 
Qed.


(* ---------- LR beta equivalence  ---------- *)

Fixpoint splice_tm (t: tm)(i: nat) (n:nat) : tm := 
  match t with 
  | ttrue         => ttrue
  | tfalse        => tfalse
  | tvar x        => tvar (if x <? i then x else x + n)
  | tapp t1 t2    => tapp (splice_tm t1 i n) (splice_tm t2 i n)
  | tabs t        => tabs (splice_tm t i n)
end.

Fixpoint subst_tm (t: tm)(i: nat) (u:tm) : tm := 
  match t with 
  | ttrue         => ttrue
  | tfalse        => tfalse
  | tvar x        => if i =? x then u else if i <? x then (tvar (pred x)) else (tvar x)   
  | tapp t1 t2    => tapp (subst_tm t1 i u) (subst_tm t2 i u)
  | tabs t        => tabs (subst_tm t i (splice_tm u i 1)) 
end.

(* We don't have locally nameless here, just regular DeBruijn levels. This 
   means substitution under binders (i.e. tabs) needs to shift the term by 1 *)


Lemma splice_acc: forall e1 a b c,
  splice_tm (splice_tm e1 a b) a c =
  splice_tm e1 a (c+b).
Proof. induction e1; intros; simpl; intuition.
  + bdestruct (i <? a); intuition.  
    bdestruct (i <? a); intuition.
    bdestruct (i + b <? a); intuition.   
  + specialize (IHe1_1 a b c). specialize (IHe1_2 a b c).
    rewrite IHe1_1. rewrite IHe1_2. auto.
  + specialize (IHe1 a b c).
    rewrite IHe1. auto. 
Qed.
  
Lemma splice_zero: forall e1 a,
  (splice_tm e1 a 0) = e1.
Proof. intros. induction e1; simpl; intuition.
  + bdestruct (i <? a); intuition.
  + rewrite IHe1_1. rewrite IHe1_2. auto.
  + rewrite IHe1. auto.
Qed.

Lemma indexr_splice_gt: forall{X} x (G1 G3: list X) T ,
  indexr x (G3 ++ G1) = Some T ->
  x >= length G1 ->
  forall G2, 
  indexr (x + (length G2))(G3 ++ G2 ++ G1) = Some T.
Proof. 
  intros.
  induction G3; intros; simpl in *.
  + apply indexr_var_some' in H as H'. intuition.
  + bdestruct (x =? length (G3 ++ G1)); intuition.
    - subst. inversion H. subst.
      bdestruct (length (G3 ++ G1) + length G2 =? length (G3 ++ G2 ++ G1)); intuition.
      repeat rewrite app_length in H1.
      intuition.
    - bdestruct (x + length G2 =? length (G3 ++ G2 ++ G1)); intuition.
      apply indexr_var_some' in H2. intuition.
Qed.      

Lemma indexr_splice: forall{X} (H2' H2 HX: list X) x,
  indexr (if x <? length H2 then x else x + length HX) (H2' ++ HX ++ H2) =
  indexr x (H2' ++ H2).
Proof.
  intros.
  bdestruct (x <? length H2); intuition.
  repeat rewrite indexr_skips; auto. rewrite app_length. lia.
  bdestruct (x <? length (H2' ++ H2)).
  apply indexr_var_some in H0 as H0'.
  destruct H0' as [T H0']; intuition.
  rewrite H0'. apply indexr_splice_gt; auto.
  apply indexr_var_none in H0 as H0'. rewrite H0'.
  assert (x + length HX >= (length (H2' ++ HX ++ H2))). {
    repeat rewrite app_length in *. lia.
  }
  rewrite indexr_var_none. auto.
Qed.

Lemma indexr_splice1: forall{X} (H2' H2: list X) x y,
  indexr (if x <? length H2 then x else (S x)) (H2' ++ y :: H2) =
  indexr x (H2' ++ H2).
Proof.
  intros.
  specialize (indexr_splice H2' H2 [y] x); intuition.
  simpl in *. replace (x +1) with (S x) in H. auto. lia.
Qed.


Lemma indexr_shift : forall{X} (H H': list X) x vx v,
  x > length H  ->
  indexr x (H' ++ vx :: H) = Some v <->
  indexr (pred x) (H' ++ H) = Some v.
Proof. 
  intros. split; intros.
  + destruct x; intuition.  simpl.
  rewrite <- indexr_insert_ge  in  H1; auto. lia.
  + destruct x; intuition. simpl in *.
    assert (x >= length H). lia.
    specialize (indexr_splice_gt x H H' v); intuition.
    specialize (H3  [vx]); intuition. simpl in H3.
    replace (x + 1) with (S x) in H3. auto. lia.
Qed. 



Lemma st_weaken: forall e1 T1 G
  (W: has_type G e1 T1),
  forall H1 H2 H2' HX,
    env_type H1 (H2'++H2) G ->
    exp_type H1 (H2'++HX++H2) e1 (splice_tm e1 (length H2) (length HX)) T1.
Proof.
  intros ? ? ? W. induction W; intros ? ? ? ? WFE.
  - eapply exp_true.
  - eapply exp_false.
  - eapply WFE in H. destruct H as (v1 & v2 & IX1 & IX2 & VX).
    eapply exp_var. eauto. rewrite indexr_splice. eauto. eauto. 
  - eapply exp_app; eauto.
  - eapply exp_abs. intros.
    eapply envt_extend in WFE; eauto.
    replace (vx2 :: H2' ++ H2) with ((vx2 :: H2') ++ H2) in WFE. 2: simpl; eauto.
    eapply IHW in WFE; eauto.
Qed.

(* Tweak the signature. To use st_subst from the main beta lemma,
   we need weakening results of the form:

   exists v1, tevaln e1 v1 ->
   forall HX,
   exists v2, tevaln (splice .. e1) v2 /\ val_type v1 v2 T
*)

Lemma tevaln_unique: forall H1 e1 v1 v1',
    tevaln H1 e1 v1 ->
    tevaln H1 e1 v1' ->
    v1 = v1'.
Proof.
  intros.
  destruct H as [n1 ?].
  destruct H0 as [n2 ?].
  assert (1+n1+n2 > n1) as A1. lia.
  assert (1+n1+n2 > n2) as A2. lia.
  specialize (H _ A1).
  specialize (H0 _ A2).
  congruence.
Qed.

Lemma st_weaken1: forall e1 T1 G
  (W: has_type G e1 T1),
  forall H1 H2 H2',
    env_type H1 (H2'++H2) G ->
    exists v1, tevaln H1 e1 v1 /\ forall HX, exists v2, tevaln (H2'++HX++H2) (splice_tm e1 (length H2) (length HX)) v2 /\ val_type v1 v2 T1.
Proof.
  intros.
  assert (exp_type H1 (H2'++H2) e1 e1 T1). eapply fundamental; eauto.
  destruct H0 as [v1 [v2 [? ?]]].
  exists v1. split. eapply H0.
  intros. 
  eapply st_weaken in W; eauto.
  destruct W as [v1' [v2' [? [? ?]]]].
  exists v2'. split. eauto.
  assert (v1 = v1'). eapply tevaln_unique; eauto.
  subst v1. eauto.
Qed.



Lemma st_subst : forall e2 T2 G0
                        (W: has_type G0 e2 T2),
  forall G' G T1, G0 = G'++T1::G ->
  forall H1 H1' H2 H2' e1 v1,
    env_type (H1'++H1) (H2'++H2) (G'++G) ->
    length H1 = length G ->
    length H2 = length G ->
    tevaln H1 e1 v1 ->
    (forall H2', exists v2, (* via st_weaken *)
        tevaln (H2'++H2) (splice_tm e1 (length H2) (length H2')) v2 /\
        val_type v1 v2 T1) -> 
    exp_type (H1'++v1::H1) (H2'++H2) e2 (subst_tm e2 (length H2) (splice_tm e1 (length H2) (length H2'))) T2.
Proof.
  intros ? ? ? W. induction W; simpl; intros ? ? ? ? ? ? ? ? ? ? WFE ? ? ? ?.
  - eapply exp_true.
  - eapply exp_false.
  - destruct (H6 H2') as [v2 [? ?]]. subst env.
    bdestruct (length H2 =? x).
    + exists v1, v2. split. 2: split.
      exists 1. intros. destruct n. lia. simpl.
      subst x. rewrite H4, <-H3. rewrite indexr_insert. eauto. eauto. 
      subst x. rewrite H4 in H. rewrite indexr_insert in H. congruence.
    + bdestruct (length H2 <? x).
      * destruct x. lia.
        erewrite <-indexr_insert_ge in H. 2: lia. simpl.
        eapply WFE in H. destruct H as (v1' & v2' & IX1 & IX2 & VX).
        eapply exp_var; eauto. rewrite <-indexr_insert_ge. eauto. lia.
      * rewrite <-indexr_insert_lt in H. 2: lia.
        eapply WFE in H. destruct H as (v1' & v2' & IX1 & IX2 & VX).
        eapply exp_var; eauto. rewrite <-indexr_insert_lt. eauto. lia.
  - eapply exp_app; eauto.
  - eapply exp_abs. intros. subst env. 
    eapply envt_extend in WFE; eauto.
    replace (vx1 :: H1' ++ H1) with ((vx1 :: H1') ++ H1) in WFE. 2: simpl; eauto.
    replace (vx2 :: H2' ++ H2) with ((vx2 :: H2') ++ H2) in WFE. 2: simpl; eauto.
    rewrite splice_acc. 
    eapply IHW with (H1':=(vx1::H1')) (H2':=(vx2::H2')).
    replace (T1 :: G' ++ T0 :: G) with ((T1 :: G') ++ T0 :: G). 2: simpl; eauto.
    eauto. eauto. eauto. eauto. eauto. eauto. 
Qed.

Lemma st_subst1 : forall e1 e2 G T1 T2 H1 H2 v1,
    has_type (T1::G) e2 T2 ->
    env_type H1 H2 G ->
    tevaln H1 e1 v1 ->
    (forall H2', exists v2, (* via st_weaken *)
        tevaln (H2'++H2) (splice_tm e1 (length H2) (length H2')) v2 /\
        val_type v1 v2 T1) -> 
    exp_type (v1::H1) H2 e2 (subst_tm e2 (length H2) (splice_tm e1 (length H2) 0)) T2.
Proof.
  intros. eapply st_subst with (G':=[]) (H1':=[]) (H2':=[]); eauto. eauto.
  eapply H0. eapply H0. 
Qed.


Lemma beta_equivalence: forall e1 e2 G T1 T2,
  has_type (T1::G) e2 T2 ->
  has_type G e1 T1 ->
  sem_type G (tapp (tabs e2) e1) (subst_tm e2 (length G) e1) T2.
Proof. 
  intros. intros H1 H2 WFE.
  assert (length G = length H2) as L. symmetry. eapply WFE. 
  eapply st_weaken1 with (H2':=[]) in H0 as A; eauto.
  destruct A as [v1 [? ?]].
  
  specialize (st_subst1 e1 e2 G T1 T2 H1 H2 v1) as ST; eauto.
  destruct ST as [v1' [v2' [? [? ?]]]]; eauto. 

  assert (exp_type H1 H2 (tabs e2) (tabs e2) (TFun T1 T2)) as C.
  eapply fundamental. econstructor. eauto. eauto.
  destruct C as [vf [vf' [? [? ?]]]].
  
  exists v1', v2'. rewrite L. intuition.
  destruct H3 as [n1 ?].
  destruct H8 as [n2 ?].
  destruct H5 as [n3 ?].
  exists ((S (n1+n2+n3))). intros.
  destruct n. lia. simpl. 
  rewrite H3; try lia.
  destruct vf; destruct vf'; simpl in H11; try contradiction.
  rewrite H8; try lia.
  assert (S n2 > n2) as D. eauto. 
  specialize (H8 (S n2) D). simpl in H8. inversion H8. subst.
  rewrite H5. eauto. lia. 

  rewrite splice_zero in H6. eauto.
Qed.



End STLC.



