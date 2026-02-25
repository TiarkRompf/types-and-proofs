(* Full safety for STLC *)

(*

STLC, binary logical relation, contextual equivalence.

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

Lemma sem_true: forall G,
    sem_type G ttrue ttrue TBool.
Proof.
  intros. intros H1 H2 WFE.
  exists (vbool true). exists (vbool true). split. 2: split. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto.
Qed.

Lemma sem_false: forall G,
    sem_type G tfalse tfalse TBool.
Proof.
  intros. intros H1 H2 WFE.
  exists (vbool false). exists (vbool false). split. 2: split. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto.
Qed.

Lemma sem_var: forall G x T,
    indexr x G = Some T ->
    sem_type G (tvar x) (tvar x) T.
Proof.
  intros. intros H1 H2 WFE.
  eapply WFE in H as IX. destruct IX as (v1 & v2 & IX1 & IX2 & VX).
  exists v1. exists v2. split. 2: split. 
  - exists 0. intros. destruct n. lia. simpl. rewrite IX1. eauto.
  - exists 0. intros. destruct n. lia. simpl. rewrite IX2. eauto. 
  - eauto.
Qed.

Lemma sem_app: forall G f1 f2 t1 t2 T1 T2,
    sem_type G f1 f2 (TFun T1 T2) ->
    sem_type G t1 t2  T1 ->
    sem_type G (tapp f1 t1) (tapp f2 t2) T2.
Proof.
  intros ? ? ? ? ? ? ? HF HX. intros E1 E2 WFE.
  destruct (HF E1 E2 WFE) as (vf1 & vf2 & STF1 & STF2 & VF).
  destruct (HX E1 E2 WFE) as (vx1 & vx2 & STX1 & STX2 & VX).
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

Lemma sem_abs: forall G t1 t2 T1 T2,
    sem_type (T1::G) t1 t2 T2 ->
    sem_type G (tabs t1) (tabs t2) (TFun T1 T2).
Proof.
  intros ? ? ? ? ? HY. intros E1 E2 WFE.
  assert (length E1 = length G) as L1. eapply WFE.
  assert (length E2 = length G) as L2. eapply WFE.
  exists (vabs E1 t1). exists (vabs E2 t2). split. 2: split. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros. eapply HY. eapply envt_extend; eauto.
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


(* ---------- LR symmetry, transitivity, etc  ---------- *)

Lemma tevaln_det: forall G e v1 v2,
    tevaln G e v1 ->
    tevaln G e v2 ->
    v1 = v2.
Proof.
  intros. destruct H, H0.
  assert (1+x+x0 > x). lia.
  assert (1+x+x0 > x0). lia.
  eapply H in H1. eapply H0 in H2.
  congruence. 
Qed.

Lemma valt_symm: forall T v1 v2,
    val_type v1 v2 T ->
    val_type v2 v1 T.
Proof.
  intros T. induction T; intros.
  - destruct v1,v2; simpl in *; try contradiction. eauto.
  - destruct v1,v2; simpl in *; try contradiction. eauto.
    intros. eapply IHT1 in H0. eapply H in H0.
    destruct H0 as (?&?&?&?&?).
    eexists _,_. split. eauto. split. eauto.
    eapply IHT2. eauto. 
Qed.

Lemma valt_trans: forall T v1 v2 v3,
    val_type v1 v2 T ->
    val_type v2 v3 T ->
    val_type v1 v3 T.
Proof.
  intros T. induction T; intros.
  - destruct v1,v2,v3; simpl in *; try contradiction. eauto.
  - destruct v1,v2,v3; simpl in *; try contradiction.
    intros vx1 vx3 VT13.
    assert (val_type vx1 vx1 T1) as VT11. {
      eapply IHT1. eauto. eapply valt_symm. eauto. }
    eapply H in VT11.
    eapply H0 in VT13.
    destruct VT13 as (vy1 & vy3 & TE1 & TE2A & VY13).
    destruct VT11 as (vy1' & vy3' & TE1' & TE2B & VY13').
    assert (vy1 = vy3'). eapply tevaln_det; eauto. subst vy3'.
    eexists _, _. split. eauto. split. eauto.
    eapply IHT2. eauto. eauto. 
Qed.

Lemma valt_regular: forall T v1 v2,
    val_type v1 v2 T ->
    val_type v1 v1 T /\ val_type v2 v2 T.
Proof.
  intros. split.
  eapply valt_trans. eauto. eapply valt_symm; eauto.
  eapply valt_trans. eapply valt_symm; eauto. eauto.
Qed.

Lemma expt_symm: forall T H1 H2 t1 t2,
    exp_type H1 H2 t1 t2 T ->
    exp_type H2 H1 t2 t1 T.
Proof.
  intros. destruct H as (?&?&?&?&?).
  eexists _,_. split. 2: split.
  eauto. eauto. eapply valt_symm; eauto. 
Qed.

Lemma expt_trans: forall T H1 H2 H3 t1 t2 t3,
    exp_type H1 H2 t1 t2 T ->
    exp_type H2 H3 t2 t3 T ->
    exp_type H1 H3 t1 t3 T.
Proof.
  intros.
  destruct H as (?&?&?&?&?).
  destruct H0 as (?&?&?&?&?).
  assert (x0 = x1). eapply tevaln_det; eauto. subst x1.
  eexists _,_. split. 2: split.
  eauto. eauto. eapply valt_trans; eauto. 
Qed.

Lemma expt_regular: forall T H1 H2 t1 t2,
    exp_type H1 H2 t1 t2 T ->
    exp_type H1 H1 t1 t1 T /\ exp_type H2 H2 t2 t2 T.
Proof.
  intros. split.
  eapply expt_trans. eauto. eapply expt_symm; eauto.
  eapply expt_trans. eapply expt_symm; eauto. eauto.
Qed.

Lemma envt_symm: forall G H1 H2,
    env_type H1 H2 G ->
    env_type H2 H1 G.
Proof.
  intros. destruct H as (?&?&?).
  split. 2: split. eauto. eauto.
  intros. edestruct H3 as (?&?&?&?&?). eauto. 
  eexists _,_. split. 2: split.
  eauto. eauto. eapply valt_symm; eauto. 
Qed.

Lemma envt_trans: forall G H1 H2 H3,
    env_type H1 H2 G ->
    env_type H2 H3 G ->
    env_type H1 H3 G.
Proof.
  intros.
  destruct H as (?&?&?).
  destruct H0 as (?&?&?).
  split. 2: split. eauto. eauto.
  intros.
  edestruct H5 as (?&?&?&?&?). eauto.
  edestruct H7 as (?&?&?&?&?). eauto.
  assert (x1 = x2). congruence. subst x2. 
  eexists _,_. split. 2: split.
  eauto. eauto. eapply valt_trans; eauto. 
Qed.

Lemma envt_regular: forall G H1 H2,
    env_type H1 H2 G ->
    env_type H1 H1 G /\ env_type H2 H2 G.
Proof.
  intros. split.
  eapply envt_trans. eauto. eapply envt_symm; eauto.
  eapply envt_trans. eapply envt_symm; eauto. eauto.
Qed.

Lemma semt_symm: forall T G t1 t2,
    sem_type G t1 t2 T ->
    sem_type G t2 t1 T.
Proof.
  intros. intros ?? WFE.
  eapply expt_symm. eapply H.
  eapply envt_symm. eapply WFE.
Qed.

Lemma semt_trans: forall T G t1 t2 t3,
    sem_type G t1 t2 T ->
    sem_type G t2 t3 T ->
    sem_type G t1 t3 T.
Proof.
  intros. intros ?? WFE.
  eapply expt_trans. eapply H. 2: eapply H0.
  eapply envt_trans. eauto. eapply envt_symm. eauto. eauto.
Qed.

Lemma semt_regular: forall T G t1 t2,
    sem_type G t1 t2 T ->
    sem_type G t1 t1 T /\ sem_type G t2 t2 T.
Proof.
  intros. split.
  eapply semt_trans. eauto. eapply semt_symm; eauto.
  eapply semt_trans. eapply semt_symm; eauto. eauto.
Qed.


(* ---------- LR contextual equivalence  ---------- *)

(* Define typed contexts and prove that the binary logical
   relation implies contextual equivalence (congruency wrt
   putting expressions in context *)

(* NB: one could add a lemma showing that these are all
   possible contexts. *)

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


Definition kleene_equiv e e' :=
  forall b,
    tevaln [] e (vbool b) <-> tevaln [] e' (vbool b).

Lemma adequacy: forall e e' T,
  sem_type [] e e' T ->
  kleene_equiv e e'.
Proof. 
  intros. 
  destruct (H [] []) as (v & v' & TE1 & TE2 & VT).
  split. 2: split. eauto. eauto. intros. inversion H0.
  destruct TE1 as (n1 & TE1).
  destruct TE2 as (n2 & TE2).
  split. 
  + intros (n1' & TE1'). remember (S (n1+n2+n1')) as n.
    assert (n > n1) as N1. lia. specialize (TE1 n N1).
    assert (n > n1') as N1'. lia. specialize (TE1' n N1').
    rewrite TE1 in TE1'. inversion TE1'. subst v.
    destruct v', T; simpl in VT; try contradiction. subst b.
    eexists n. intros. eapply TE2. lia. 
  + intros (n2' & TE2'). remember (S (n1+n2+n2')) as n.
    assert (n > n2) as N2. lia. specialize (TE2 n N2).
    assert (n > n2') as N2'. lia. specialize (TE2' n N2').
    rewrite TE2 in TE2'. inversion TE2'. subst v'.
    destruct v, T; simpl in VT; try contradiction. subst b.
    eexists n. intros. eapply TE1. lia. 
Qed.


Definition context_equiv G t1 t2 T1 :=
  forall C,
    ctx_type C G T1 [] TBool ->
    kleene_equiv (C t1) (C t2).

(* soundness of binary logical relations wrt contextual equivalence *)
Theorem soundess: forall G t1 t2 T,
  sem_type G t1 t2 T ->
  context_equiv G t1 t2 T.
Proof.
  intros. intros ? HC.
  eapply adequacy.
  eapply congr; eauto. 
Qed.



End STLC.



