(* Full safety for STLC *)

(*

An LR-based termination and semantic soundness proof for STLC.

Includes subtyping and type TAny.

Canonical big-step cbv semantics.

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
  | TAny   : ty
  | TBool  : ty
  | TFun   : ty -> ty -> ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : tm -> tm
.

Inductive vl: Type :=
| vbool :  bool -> vl
| vabs  :  list vl -> tm -> vl 
.

Definition venv := list vl.
Definition tenv := list ty.

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.


(* ---------- syntactic typing rules ---------- *)

Inductive stp : ty -> ty -> Prop :=
| s_any: forall T,
    stp T TAny
| s_bool:
    stp TBool TBool
| s_fun: forall T1 T2 T3 T4,
    stp T3 T1 ->
    stp T2 T4 ->
    stp (TFun T1 T2) (TFun T3 T4)
.
        
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
    has_type (T1::env) t T2 ->
    has_type env (tabs t) (TFun T1 T2)
| t_sub: forall env t T1 T2,
    has_type env t T1 ->
    stp T1 T2 ->
    has_type env t T2
.

(* ---------- operational semantics ---------- *)

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

Fixpoint val_type v T : Prop :=
  match v, T with
  | _, TAny =>
      True
  | vbool b, TBool =>  
      True
  | vabs H ty, TFun T1 T2 =>
      forall vx,
        val_type vx T1 ->
        exists vy,
          tevaln (vx::H) ty vy /\
          val_type vy T2
  | _,_ =>
      False
  end.


Definition exp_type H t T :=
  exists v,
    tevaln H t v /\
    val_type v T.

Definition env_type (H: venv) (G: tenv) :=
  length H = length G /\
    forall x T,
      indexr x G = Some T ->
      exists v,
        indexr x H = Some v /\
        val_type v T.

Definition sem_stp T1 T2 :=
  forall v,
    val_type v T1 ->
    val_type v T2.

Definition sem_type G t T :=
  forall H,
    env_type H G ->
    exp_type H t T.


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: core.

#[export] Hint Constructors has_type: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.




(* ---------- LR helper lemmas  ---------- *)

Lemma envt_empty:
    env_type [] [].
Proof.
  intros. split. eauto. intros. inversion H. 
Qed.

Lemma envt_extend: forall E G v1 T1,
    env_type E G ->
    val_type v1 T1 ->
    env_type (v1::E) (T1::G).
Proof.
  intros. 
  remember H as WFE. clear HeqWFE.
  destruct H. split. simpl. eauto.
  intros x T IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX. subst T1.
    exists v1. rewrite <- H. rewrite indexr_head. eauto.
  - rewrite indexr_skip in IX; eauto.
    eapply WFE in IX as IX. destruct IX as (v2 & ? & ?).
    exists v2. rewrite indexr_skip; eauto. lia.
Qed.


(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_true: forall G,
    sem_type G ttrue TBool.
Proof.
  intros. intros E WFE. 
  exists (vbool true). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto. 
Qed.

Lemma sem_false: forall G,
    sem_type G tfalse TBool.
Proof.
  intros. intros E WFE. 
  exists (vbool false). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto. 
Qed.

Lemma sem_var: forall G x T,
    indexr x G = Some T ->
    sem_type G (tvar x) T.
Proof.
  intros. intros E WFE.
  eapply WFE in H as IX. destruct IX as (v & IX & VX).
  exists v. split. 
  - exists 0. intros. destruct n. lia. simpl. rewrite IX. eauto.
  - eauto. 
Qed.

Lemma sem_app: forall G f t T1 T2,
    sem_type G f (TFun T1 T2) ->
    sem_type G t T1 ->
    sem_type G (tapp f t) T2.
Proof.
  intros ? ? ? ? ? HF HX. intros E WFE.
  destruct (HF E WFE) as (vf & STF & VF).
  destruct (HX E WFE) as (vx & STX & VX).
  destruct vf; simpl in VF; intuition.
  edestruct VF as (vy & STY & VY). eauto. 
  exists vy. split.
  - destruct STF as (n1 & STF).
    destruct STX as (n2 & STX).
    destruct STY as (n3 & STY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite STF, STX, STY. 2,3,4: lia.
    eauto.
  - eauto.
Qed.

Lemma sem_abs: forall G t T1 T2,
    sem_type (T1::G) t T2 ->
    sem_type G (tabs t) (TFun T1 T2).
Proof.
  intros ? ? ? ? HY. intros E WFE.
  assert (length E = length G) as L. eapply WFE.
  exists (vabs E t). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros. eapply HY. eapply envt_extend; eauto.
Qed.

(* ---------- LR subtyping compatibility lemmas  ---------- *)

Lemma sem_stp_any: forall T,
  sem_stp T TAny.
Proof.
  intros ? ? V1. destruct v; simpl; eauto.
Qed.

Lemma sem_stp_bool:
  sem_stp TBool TBool.
Proof.
  intros ? V1. eauto.
Qed.

Lemma sem_stp_fun: forall T1 T2 T3 T4,
  sem_stp T3 T1 ->
  sem_stp T2 T4 ->
  sem_stp (TFun T1 T2) (TFun T3 T4).
Proof.
  intros ? ? ? ? ST31 ST24. intros ? V1.
  destruct v; simpl in *; eauto; intros.
  destruct (V1 vx) as (vy & EY & VY).
  eapply ST31. eauto.
  eexists vy. split. eauto.
  eapply ST24. eauto. 
Qed.

Theorem stp_fundamental: forall T1 T2,
    stp T1 T2 ->
    sem_stp T1 T2.
Proof.
  intros. induction H.
  - eapply sem_stp_any; eauto. 
  - eapply sem_stp_bool; eauto. 
  - eapply sem_stp_fun; eauto.
Qed.


Lemma sem_sub: forall G t T1 T2,
    sem_type G t T1 ->
    sem_stp T1 T2 ->
    sem_type G t T2.
Proof.
  intros ? ? ? ? H1 ST12. intros E WFE.
  destruct (H1 E) as (vy & ? & VY). eauto.
  eexists. split. eauto. eapply ST12. eauto.
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
  - eapply sem_sub; eauto.
    eapply stp_fundamental; eauto.    
Qed.

Corollary safety: forall t T,
  has_type [] t T ->
  exp_type [] t T.
Proof. 
  intros. eapply fundamental in H as ST; eauto.
  destruct (ST []) as (v & ? & ?).
  eapply envt_empty.
  exists v. intuition.
Qed.

End STLC.
