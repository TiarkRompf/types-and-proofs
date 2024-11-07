(* Full safety for STLC *)

(*

An LR-based termination and semantic soundness proof for STLC.

This file: assume a small-step substitution-based semantics,
and call-by-name reduction.

Goal: may need something similar at the type level for Fw or
full call-dependent types.

Another idea is to establish equivalence between cbv and cbn reduction directly.

*)

Require Import Coq.Lists.List.
Require Import Psatz.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.

Import ListNotations.

Require Import tactics.
Require Import env.
Require Import qualifiers.

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
  | tvarB : id -> tm (* var bound in tabs *)
  | tapp : tm -> tm -> tm
  | tabs : tm -> tm
.


Definition tenv := list ty.
Definition venv := list tm.

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.


(* ---------- locally nameless ---------- *)

(* t1 [var 0 -> t2] *)
Fixpoint open t1 n t2: tm :=
  match t1 with
  | ttrue => ttrue
  | tfalse => tfalse
  | tvarB m => if n =? m then t2 else if n <? m then tvarB (m-1) else tvarB m
  | tvar n => tvar n
  | tapp t11 t12 => tapp (open t11 n t2) (open t12 n t2)
  | tabs t1 => tabs (open t1 (S n) t2)
  end.

Fixpoint closed t n :=
  match t with
  | ttrue => True
  | tfalse => True
  | tvar x => x < n
  | tvarB x => True
  | tapp t1 t2 => closed t1 n /\ closed t2 n
  | tabs t => closed t n
  end.

Fixpoint closedB t n :=
  match t with
  | ttrue => True
  | tfalse => True
  | tvar x => True
  | tvarB x => x < n
  | tapp t1 t2 => closedB t1 n /\ closedB t2 n
  | tabs t => closedB t (S n)
  end.

(* ---------- syntactic typing rules ---------- *)

Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
    has_type env ttrue TBool
| t_false: forall env,
    has_type env tfalse TBool
| t_var: forall x env T,
    indexr x env = Some T ->
    has_type env (tvar x) T
| t_app: forall env f t T1 T2,
    has_type env f (TFun T1 T2) ->
    has_type env t T1 ->
    has_type env (tapp f t) T2
| t_abs: forall env t T1 T2,
    has_type (T1::env) (open t 0 (tvar (length env))) T2 ->
    closed t (length env) -> 
    has_type env (tabs t) (TFun T1 T2)
.

(* ---------- operational semantics ---------- *)

Inductive value : tm -> Prop :=
| v_true : value (ttrue)
| v_false : value (tfalse)
| v_abs : forall t, value (tabs t)
.

Fixpoint subst H t :=
  match t with
  | ttrue => ttrue
  | tfalse => tfalse
  | tvar x =>
      match indexr x H with
      | Some t => t
      | None => tvar x
      end
  | tvarB x => tvarB x
  | tapp t1 t2 => tapp (subst H t1) (subst H t2)
  | tabs t => tabs (subst H t)
  end.



Inductive step : tm -> tm -> Prop :=
| step_beta : forall t v,
      step (tapp (tabs t) v) (open t 0 v)  (* alt: (subst [v] (open t (tvar 0))) *)
| step_app_l : forall t1 t1' t2,
    step t1 t1' ->
    step (tapp t1 t2) (tapp t1' t2)
| step_app_r : forall t1 t2 t2',
    step t2 t2' ->
    step (tapp t1 t2) (tapp t1 t2')
.

Inductive stepn : tm -> tm -> Prop :=
| step_0: forall t,
    stepn t t
| step_1: forall t1 t2 t3,
    stepn t1 t2 ->
    step t2 t3 ->
    stepn t1 t3
.


Fixpoint val_type t T : Prop :=
  match t, T with
  | ttrue, TBool =>      
      True
  | tfalse, TBool =>
      True
  | tabs t2, TFun T1 T2 =>
      forall t1 v1,
        closedB t1 0 ->
        stepn t1 v1 ->
        val_type v1 T1 ->
        exists v2,
          stepn (open t2 0 t1) v2 /\
          val_type v2 T2
  | _,_ =>
      False
  end.


Definition exp_type t T :=
  exists v,
    stepn t v /\
    val_type v T.

Definition env_type (H: list tm) (G: tenv) :=
  length H = length G /\
    forall T x,
      indexr x G = Some T ->
      exists t v,
        indexr x H = Some t /\
          closedB t 0 /\
          stepn t v /\
          val_type v T.

Definition sem_type G t T :=
  forall H,
    closedB t 0 ->
    env_type H G ->
    exp_type (subst H t) T.


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.

#[export] Hint Constructors has_type: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.


(* ---------- locally nameless  ---------- *)

Lemma closed_inc: forall t n n1,
    closedB t n -> n <= n1 ->
    closedB t n1.
Proof.
  intros t. induction t; intros; simpl in *; eauto.
  - lia.
  - intuition eauto.
  - eapply IHt. eauto. lia.
Qed.

Lemma closed_open_id: forall t t2 n,
    closedB t n -> 
    open t n t2 = t.
Proof.
  intros t. induction t; intros; unfold open in *; simpl in *; eauto.
  - bdestruct (n =? i). lia.
    bdestruct (n <? i). lia.
    eauto. 
  - destruct H. erewrite IHt1, IHt2; eauto.
  - erewrite IHt; eauto. 
Qed.

Lemma closed_open_id': forall t t2 n n1,
    closedB t n -> n <= n1 ->
    open t n1 t2 = t.
Proof.
  intros t. induction t; intros; unfold open in *; simpl in *; eauto.
  - bdestruct (i <? n). 2: lia.
    bdestruct (n1 =? i). lia.
    bdestruct (n1 <? i). lia.
    eauto. 
  - destruct H. erewrite IHt1, IHt2; eauto.
  - erewrite IHt; eauto. lia. 
Qed.

Lemma open_closed: forall t n m,
    closedB t (S m) -> 
    closedB (open t m (tvar n)) m.
Proof.
  intros t. induction t; intros; unfold open in *; simpl in *; eauto.
  - bdestruct (m =? i). simpl. eauto.
    bdestruct (m <? i). simpl. lia.
    simpl. lia. 
  - destruct H. eauto. 
Qed.

Lemma open_closed': forall t n m,
    closedB (open t m (tvar n)) m ->
    closedB t (S m).
Proof.
  intros t. induction t; intros; unfold open in *; simpl in *; eauto.
  - bdestruct (m =? i). lia. 
    bdestruct (m <? i). simpl in H. lia.
    simpl in H. lia. 
  - destruct H. eauto. 
Qed.

Lemma subst_open_commute: forall t t1 E n,
    closed t (length E) ->
    (forall x t1, indexr x E = Some t1 -> closedB t1 0) ->
    subst (t1 :: E) (open t n (tvar (length E))) = (open (subst E t) n t1).
Proof.
  intros. generalize dependent n. induction t; intros.
  - simpl. unfold open. eauto.
  - simpl. unfold open. eauto.
  - assert (i < length E). simpl in H. eauto.
    simpl. bdestruct (i =? length E).
    + lia. 
    + eapply indexr_var_some in H1. destruct H1. simpl. rewrite H1.
      eapply H0 in H1.
      symmetry. unfold open. erewrite closed_open_id. eauto. eapply closed_inc. eauto. lia.
  - simpl. unfold open.
    bdestruct (n =? i).
    + simpl. bdestruct (length E =? length E). eauto. contradiction.
    + bdestruct (n <? i).
      * simpl. eauto.
      * simpl. eauto.
  - simpl in H.
    destruct H. simpl. rewrite IHt1, IHt2; eauto.
  - simpl in H.
    simpl. erewrite IHt; eauto.
Qed.

Lemma subst_closed_commute: forall t E n,
    (forall x t1, indexr x E = Some t1 -> closedB t1 0) ->
    (closedB t n) -> (closedB (subst E t) n).
Proof.
  intros. generalize dependent n. induction t; intros; eauto.
  - simpl. remember (indexr i E) as v. destruct v.
    symmetry in Heqv. eapply H in Heqv.
    eapply closed_inc. eauto. lia. 
    eauto. 
  - simpl in *. destruct H0. split.
    eapply IHt1; eauto. eapply IHt2; eauto. 
  - simpl in *. simpl in H.
    eapply IHt; eauto. 
Qed.

Lemma subst_empty: forall t,
    subst [] t = t.
Proof.
  intros. induction t; simpl; eauto. 
  - rewrite IHt1, IHt2. eauto. 
  - rewrite IHt. eauto. 
Qed.



(* ---------- operational semantics  ---------- *)

Lemma stepn_app_l : forall t1 t1' t2,
    stepn t1 t1' ->
    stepn (tapp t1 t2) (tapp t1' t2).
Proof.
  intros. induction H.
  - eapply step_0.
  - eapply step_1. eauto.
    eapply step_app_l. eauto. 
Qed.

Lemma stepn_app_r : forall t1 t2 t2',
    stepn t2 t2' ->
    stepn (tapp t1 t2) (tapp t1 t2').
Proof.
  intros. induction H.
  - eapply step_0.
  - eapply step_1. eauto.
    eapply step_app_r. eauto. 
Qed.

Lemma stepn_trans : forall t1 t2 t3,
    stepn t1 t2 ->
    stepn t2 t3 ->
    stepn t1 t3.
Proof.
  intros. induction H0.
  - eauto. 
  - eapply step_1. eapply IHstepn. eauto. eauto. 
Qed.


(* ---------- LR helper lemmas  ---------- *)

Lemma envt_closed: forall E G,
    env_type E G ->
    forall x t1, indexr x E = Some t1 -> closedB t1 0.
Proof.
  intros. destruct H.
  assert (x < length E). eapply indexr_var_some. eexists. eauto.
  rewrite H in H2.
  eapply indexr_var_some in H2.
  destruct H2. eapply H1 in H2.
  destruct H2 as (t & v & ? & ? & ? & ?).
  rewrite H0 in H2. inversion H2. subst t1. eauto.
Qed.
  
Lemma envt_extend: forall E G t1 v1 T1,
    env_type E G ->
    closedB t1 0 ->
    stepn t1 v1 ->
    val_type v1 T1 ->
    env_type (t1::E) (T1::G).
Proof.
  intros. 
  remember H as WFE. clear HeqWFE.
  destruct H. split. simpl. eauto.
  intros T x IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX. subst T1.
    exists t1, v1. rewrite <- H. rewrite indexr_head. eauto.
  - rewrite indexr_skip in IX; eauto.
    eapply WFE in IX as IX. destruct IX as (t2 & v2 & ? & ? & ?).
    exists t2, v2. rewrite indexr_skip; eauto. lia.
Qed.


(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_true: forall G,
    sem_type G ttrue TBool.
Proof.
  intros. intros E WFE. 
  exists ttrue. split. econstructor. simpl. eauto.
Qed.

Lemma sem_false: forall G,
    sem_type G tfalse TBool.
Proof.
  intros. intros E WFE. 
  exists tfalse. split. econstructor. simpl. eauto.
Qed.

Lemma sem_var: forall G x T,
    indexr x G = Some T ->
    sem_type G (tvar x) T.
Proof.
  intros. intros E C WFE.
  eapply WFE in H as IX. destruct IX as (t & v & IX & VX).
  exists v. split. 2: eauto. 
  simpl. rewrite IX. eapply VX. eapply VX.
Qed.

Lemma sem_app: forall G f t T1 T2,
    sem_type G f (TFun T1 T2) ->
    sem_type G t T1 ->
    sem_type G (tapp f t) T2.
Proof.
  intros ? ? ? ? ? HF HX. intros E C WFE.
  simpl in C. destruct C as (CF & CX).
  destruct (HF E CF WFE) as (vf & STF & VF).
  destruct (HX E CX WFE) as (vx & STX & VX).
  destruct vf; simpl in VF; intuition.
  edestruct VF as (vy & STY & VY).
  2: eapply STX. 2: eapply VX.
  eapply subst_closed_commute. eapply envt_closed; eauto. eauto. 
  exists vy. split. 2: eauto.
  simpl. 
  eapply stepn_trans. 2: eapply stepn_trans.
  eapply stepn_app_l. eauto.
  eapply step_1. eapply step_0. eapply step_beta.
  eapply STY.
Qed.

Lemma sem_abs: forall G t T1 T2,
    sem_type (T1::G) (open t 0 (tvar (length G))) T2 ->
    closed t (length G) ->
    sem_type G (tabs t) (TFun T1 T2).
Proof.
  intros ? ? ? ? HY CL. intros E C WFE.
  assert (length E = length G) as L. eapply WFE. 
  exists (subst E (tabs t)). split.
  eapply step_0. simpl.
  intros. 
  edestruct (HY) as (vy & STY & VY).
  simpl in C. eapply open_closed. eauto.
  eapply envt_extend; eauto.
  exists vy. split. 2: eapply VY.
  rewrite <-L in STY. unfold open in *. 
  rewrite subst_open_commute in STY.
  eauto. rewrite L. eauto.
  eapply envt_closed. eauto. 
Qed.


                                                       
(* ---------- LR fundamental property  ---------- *)

Theorem fundamental: forall G t T,
    has_type G t T ->
    sem_type G t T.
Proof.
  intros ? ? ? W. 
  induction W.
  - eapply sem_true; eauto.
  - eapply sem_false; eauto.
  - eapply sem_var; eauto.
  - eapply sem_app; eauto. 
  - eapply sem_abs; eauto.
Qed.

Lemma hast_closed: forall G t T,
    has_type G t T ->
    closedB t 0.
Proof.
  intros. induction H; simpl; eauto.
  eapply open_closed'. eauto. 
Qed.

Lemma envt_empty:
    env_type [] [].
Proof.
  intros. split. eauto. intros. inversion H. 
Qed.

Corollary safety: forall t T,
  has_type [] t T ->
  exp_type t T.
Proof. 
  intros. eapply fundamental in H as ST; eauto.
  destruct (ST []) as (v & ? & ?).
  eapply hast_closed; eauto.
  eapply envt_empty.
  rewrite subst_empty in H0. 
  exists v. intuition.
Qed.

End STLC.
