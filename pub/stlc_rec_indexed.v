(* Full safety for STLC *)

(*

An LR-based semantic soundness proof for STLC.

Big-step cbv semantics.

Step-indexed LR: soundness only, no termination.

Functions may be recursive: every application includes
an implicit self-application.

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
    has_type (T1::(TFun T1 T2)::env) t T2 ->
    has_type env (tabs t) (TFun T1 T2)
.

(* ---------- operational semantics ---------- *)

(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
*)

(* this step-indexed version returns the number of steps taken (always <= fuel) *)

Fixpoint teval(n: nat)(env: venv)(t: tm){struct n}: (nat * option (option vl)) :=
  match n with
    | 0 => (0,None)
    | S n =>
      match t with
        | ttrue                                => (1, Some (Some (vbool true)))
        | tfalse                               => (1, Some (Some (vbool false)))
        | tvar x                               => (1, Some (indexr x env))
        | tabs y                               => (1, Some (Some (vabs env y)))
        | tapp ef ex                           =>
          match teval n env ef with
            | (df, None)                       => (1+df, None)
            | (df, Some None)                  => (1+df, Some None)
            | (df, Some (Some (vbool _)))      => (1+df, Some None)
            | (df, Some (Some (vabs env2 ey))) =>
              match teval (n-df) env ex with
                | (dx, None)                   => (1+df+dx, None)
                | (dx, Some None)              => (1+df+dx, Some None)
                | (dx, Some (Some vx))         =>  
                    match teval (n-df-dx) (vx::(vabs env2 ey)::env2) ey with 
                        | (dy, res)            => (1+ df+dx+dy, res)
                    end
              end
          end
      end
end.

Lemma eval_deterministic: forall m n, n < m -> forall H t n1 r j,
  teval n H t = (n1, Some r) -> j >= n -> (* alt: j >= n1 ? *)
  teval j H t = (n1, Some r).
Proof.
  intros m. induction m. intros. inversion H.
  intros. destruct n. inversion H1. destruct j. inversion H2.
  destruct t; simpl; simpl in H1; try eauto.
  remember (teval n H0 t1) as tf. destruct tf as [nf [rf|]].
  rewrite IHm with (n:=n) (n1:=nf) (r:=rf).
  destruct rf; try destruct v; try solve [inversion H1; eauto]. 
  remember (teval (n-nf) H0 t2) as tx. destruct tx as [nx [rx|]].
  rewrite IHm with (n:=n-nf) (n1:=nx) (r:=rx).
  destruct rx; try solve [destruct v; inversion H1; eauto].
  remember (teval (n-nf-nx) (v :: vabs l t :: l) t) as ty. destruct ty as [ny [ry|]].
  rewrite IHm with (n:=n-nf-nx) (n1:=ny) (r:=ry).

  eauto. lia. eauto. lia.
  inversion H1. inversion H1.
  eauto. lia. eauto. lia.
  inversion H1.
  lia. eauto. lia.
  inversion H1.
Qed.

Lemma eval_bounded: forall m n, n < m -> forall H t n1 r,
    teval n H t = (n1, Some r) ->
    1 <= n1 /\ n1 <= n.
Proof.
  intros m. induction m. intros. inversion H.
  intros. destruct n. inversion H1.
  destruct t; simpl in *; inversion H1; try lia.
  remember (teval n H0 t1) as tf. destruct tf as [nf [rf|]]. 2: { inversion H1. }
  symmetry in Heqtf. eapply IHm with (n:=n) (n1:=nf) (r:=rf) in Heqtf as HF1. 2: lia.
  destruct rf. 2: { inversion H1. lia. } destruct v. inversion H1. lia.
  remember (teval (n-nf) H0 t2) as tx. destruct tx as [nx [rx|]]. 2: inversion H1.
  symmetry in Heqtx. eapply IHm in Heqtx as HX1. 2: lia.
  destruct rx. 2: { inversion H1. lia. } 
  remember (teval (n-nf-nx) (v :: vabs l t :: l) t) as ty. destruct ty as [ny [ry|]].
  symmetry in Heqty. eapply IHm in Heqty as HY1. 2: lia. 2: inversion H1. 
  inversion H1. lia. 
Qed.


(* ---------- LR definitions  ---------- *)

Fixpoint val_type n t T {struct n}: Prop :=
  match n with
  | 0 => True
  | S n =>
      match t, T with
      | vbool b, TBool =>  
          True
      | vabs H ty, TFun T1 T2 =>  
          forall nx vx, 
            val_type (n-nx) vx T1 ->
            forall ny ry,
              teval (n-nx) (vx::vabs H ty::H) ty = (ny, (Some ry)) ->
              exists vy,
                ry = Some vy /\
                val_type (n-nx-ny) vy T2
      | _,_ =>
          False
      end
  end.


Definition exp_type n H t T :=
  forall n1 r,
    teval n H t = (n1, Some r) ->
    exists v,
      r = Some v /\
      val_type (n-n1) v T.

Definition env_type n (H: venv) (G: tenv) :=
  length H = length G /\
    forall T x,
      indexr x G = Some T ->
      exists v,
        indexr x H = Some v /\
        val_type n v T.

Definition sem_type G t T :=
  forall n H,
    env_type n H G ->
    exp_type n H t T.


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: core.

#[export] Hint Constructors has_type: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.




(* ---------- LR helper lemmas  ---------- *)

Lemma envt_empty: forall n,
    env_type n [] [].
Proof.
  intros. split. eauto. intros. inversion H. 
Qed.

Lemma envt_extend: forall n E G v1 T1,
    env_type n E G ->
    val_type n v1 T1 ->
    env_type n (v1::E) (T1::G).
Proof.
  intros. 
  remember H as WFE. clear HeqWFE.
  destruct H. split. simpl. eauto.
  intros T x IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX. subst T1.
    exists v1. rewrite <- H. rewrite indexr_head. eauto.
  - rewrite indexr_skip in IX; eauto.
    eapply WFE in IX as IX. destruct IX as (v2 & ? & ?).
    exists v2. rewrite indexr_skip; eauto. lia.
Qed.


Lemma valt_dec: forall m n, n < m -> forall n1 v1 T1,
    val_type n v1 T1 -> n1 <= n ->
    val_type n1 v1 T1.
Proof.
  intros m. induction m. lia. intros. destruct n; destruct n1. eauto. lia. simpl. eauto. 
  destruct v1, T1; simpl in H0; try contradiction.
  - simpl. eauto.
  - simpl. intros.
    edestruct H0 with (nx:=n-n1+nx). eapply IHm. 2: eauto. lia. lia.
    eapply eval_deterministic. 2: eauto. eauto. lia. 
    eexists. split. eapply H4. eapply IHm. 2: eapply H4. lia. lia. 
Qed.

Lemma envt_dec: forall n n1 H G,
    env_type n H G -> n1 <= n ->
    env_type n1 H G.
Proof.
  intros. destruct H0. split. eauto.
  intros. eapply H2 in H3. destruct H3. eexists. intuition eauto.
  eapply valt_dec; eauto. 
Qed.


(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_true: forall G,
    sem_type G ttrue TBool.
Proof.
  intros. intros n E WFE. intros ? ? EV.
  destruct n; inversion EV. 
  exists (vbool true). split. 
  - eauto. 
  - destruct n; simpl; eauto. 
Qed.

Lemma sem_false: forall G,
    sem_type G tfalse TBool.
Proof.
  intros. intros n E WFE. intros ? ? EV.
  destruct n; inversion EV. 
  exists (vbool false). split.
  - eauto. 
  - destruct n; simpl; eauto.
Qed.

Lemma sem_var: forall G x T,
    indexr x G = Some T ->
    sem_type G (tvar x) T.
Proof.
  intros. intros n E WFE. intros ? ? EV.
  eapply WFE in H as IX. destruct IX as (v & IX & VX).
  destruct n; inversion EV. 
  exists v. split. 
  - congruence.
  - eapply valt_dec. eauto. eauto. lia.
Qed.

Lemma sem_app: forall G f t T1 T2,
    sem_type G f (TFun T1 T2) ->
    sem_type G t T1 ->
    sem_type G (tapp f t) T2.
Proof.
  intros ? ? ? ? ? HF HX. intros n E WFE. intros n3 r3 EV.
  destruct n. { simpl in EV. inversion EV. } simpl in EV. 

  (* function evaluates *)
  remember (teval n E f) as tf. symmetry in Heqtf. destruct tf as [nf [rf|]]. 2: inversion EV.
  edestruct (HF (S n) E) as (vf & STF & VF). eauto. eapply eval_deterministic. eauto. eauto. lia. 
  eapply eval_bounded in Heqtf as BF; eauto.
  remember (S n - nf) as nf1. destruct nf1. lia.
  subst rf.

  (* result is a function value *)
  simpl in VF. destruct vf. contradiction.

  (* argument evaluates *)
  remember (teval (n-nf) E t) as tx. symmetry in Heqtx. destruct tx as [nx [rx|]]. 2: inversion EV.
  edestruct (HX (S n) E) as (vx & STX & VX). eauto. eapply eval_deterministic. eauto. eauto. lia.
  eapply eval_bounded in Heqtx as BX; eauto.
  remember (S n - nx) as nx1. destruct nx1. lia.
  subst rx. 

  (* function body evaluates *)
  remember (teval (n-nf-nx) (vx :: vabs l t0 :: l) t0) as ty. symmetry in Heqty. destruct ty as [ny [ry|]]. 2: inversion EV.
  eapply eval_bounded in Heqty as BY; eauto.
  inversion EV. 
  subst ry.

  (* from function LR: function body result is well-typed *)
  assert (nf1 = n - nf). lia. subst nf1. 
  edestruct VF with (nx:=nx) as [vy [? VY]]. eapply valt_dec; eauto. lia. eauto.
  subst r3.

  (* return result *)
  exists vy. split. eauto. eapply valt_dec. eauto. eapply VY. lia. 
Qed.

Lemma sem_abs: forall G t T1 T2,
    sem_type (T1::(TFun T1 T2)::G) t T2 ->
    sem_type G (tabs t) (TFun T1 T2).
Proof.
  intros ? ? ? ? HY. intros n E WFE. intros ? ? EV.
  destruct n; inversion EV.
  exists (vabs E t). split.
  - eauto.
  - replace (S n - 1) with n. 2: lia. clear EV. 
    induction n. simpl. eauto. 
    simpl. intros. unfold sem_type in HY. 
    edestruct (HY). 2: eapply H2.
    eapply envt_extend. eapply envt_extend. eapply envt_dec. eapply WFE. lia. 
    (* val_type (vabs E t) at lower index *)
    eapply valt_dec. 2: eapply IHn. eauto. eapply envt_dec. eapply WFE. lia. lia.
    (* val_type vx *)
    eauto.
    (* val_type vy *)
    eexists. eauto.
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

Corollary safety: forall t T,
  has_type [] t T ->
  forall n, exp_type n [] t T.
Proof. 
  intros. intros ? ? EV.
  eapply fundamental in H as ST; eauto.
  edestruct (ST n []) as (v & ? & ?).
  eapply envt_empty. eauto. 
  eexists v. intuition.
Qed.

End STLC.
