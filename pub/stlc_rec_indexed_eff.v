(* Full safety for STLC *)

(*

An LR-based semantic soundness proof for STLC.

Big-step cbv semantics.

Functions may be recursive: every application includes
an implicit self-application.

Add an effect system that distinguishes terminating
expressions from potentially nonterminating ones.

Combine type-indexed and step-indexed LR:
termination for pure code, soundness only for impure.

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
  | TFun   : ty -> ty -> bool -> ty
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

Inductive has_type : tenv -> tm -> ty -> bool -> Prop :=
| t_true: forall env,
    has_type env ttrue TBool false
| t_false: forall env,
    has_type env tfalse TBool false
| t_var: forall x env T,
    indexr x env = Some T ->
    has_type env (tvar x) T false
| t_app: forall env f t T1 T2 e1 e2 e3,
    has_type env f (TFun T1 T2 e3) e1 ->
    has_type env t T1 e2 ->
    has_type env (tapp f t) T2 (e1 || e2 || e3)
| t_abs: forall env t T1 T2 e,
    has_type (T1::(TFun T1 T2 true)::env) t T2 e -> (* self-ref is effectful *)
    has_type env (tabs t) (TFun T1 T2 e) false
| t_sub_eff: forall env t T,
    has_type env t T false ->
    has_type env t T true
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

Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = (nm, Some (Some v)).


(* ---------- LR definitions  ---------- *)

Fixpoint val_type n t T {struct T}: Prop :=
  match t, T with
  | vbool b, TBool =>  
      True
  | vabs H ty, TFun T1 T2 false => (* pure, terminating *)
      forall nx vx, 
        val_type (n-nx) vx T1 ->
        exists vy,
          tevaln (vx::vabs H ty::H) ty vy /\
            val_type (n-nx) vy T2
  | vabs H ty, TFun T1 T2 true => (* impure, potentially diverging *)
      match n with
      | 0 => True
      | S n =>
          forall nx vx, 
            val_type (n-nx) vx T1 ->
            forall ny ry,
              teval (n-nx) (vx::vabs H ty::H) ty = (ny, (Some ry)) ->
              exists vy,
                ry = Some vy /\
                  val_type (n-nx-ny) vy T2
      end
  | _,_ =>
      False
  end.


Definition exp_type_pure n H t T :=
  exists v,
    tevaln H t v /\
    val_type n v T.
    

Definition exp_type_impure n H t T :=
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

Definition sem_type G t T (e:bool) :=
  forall n H,
    env_type n H G ->
    if e then exp_type_impure n H t T else exp_type_pure n H t T. (* /\
    (e = false -> exp_type_pure n H t T). *)


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

(*
Lemma valt_dec: forall m n, n < m -> forall n1 v1 T1,
    val_type n v1 T1 -> n1 <= n ->
    val_type n1 v1 T1.
Proof. 
  intros m. induction m. lia. intros. 
  destruct v1, T1; simpl in H0; try contradiction.
  - simpl. eauto.
  - destruct b.
    + destruct n1. simpl. eauto. destruct n. lia. simpl. intros. 
      edestruct H0 with (nx:=n-n1+nx). eapply IHm. 2: eauto. lia. lia.
      eapply eval_deterministic. 2: eauto. eauto. lia. 
      eexists. split. eapply H4. eapply IHm. 2: eapply H4. lia. lia.
    + simpl. intros. edestruct H0 as (? & ? & ?). eauto.
      eexists. split; eauto. eapply IHm. 2: eauto. 
Qed.*)

Lemma valt_dec: forall T1 n n1 v1,
    val_type n v1 T1 -> n1 <= n ->
    val_type n1 v1 T1.
Proof. 
  intros T1. induction T1; intros. 
  - simpl. eauto.
  - destruct v1, b; simpl in H; try contradiction.
    + destruct n1. simpl. eauto. destruct n. lia. simpl. intros. 
      edestruct H with (nx:=n-n1+nx). eapply IHT1_1. eauto. lia. 
      eapply eval_deterministic. 2: eauto. eauto. lia. 
      eexists. split. eapply H3. eapply IHT1_2. eapply H3. lia. 
    + simpl. intros. edestruct H with (nx:=n-n1+nx) as (? & ? & ?).
      replace (n - (n - n1 + nx)) with (n1-nx). 2: lia. eauto. 
      eexists. split; eauto.
      replace (n - (n - n1 + nx)) with (n1-nx) in H3. 2: lia. eauto. 
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
    sem_type G ttrue TBool false.
Proof.
  intros. intros E WFE. 
  exists (vbool true). split.
  - exists 1. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto. 
Qed.

Lemma sem_false: forall G,
    sem_type G tfalse TBool false.
Proof.
  intros. intros E WFE. 
  exists (vbool false). split.
  - exists 1. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto. 
Qed.

Lemma sem_var: forall G x T,
    indexr x G = Some T ->
    sem_type G (tvar x) T false.
Proof.
  intros. intros n E WFE.
  eapply WFE in H as IX. destruct IX as (v & IX & VX).
  exists v. split. 
  - exists 1. intros. destruct n0. lia. simpl. rewrite IX. eauto.
  - eauto. 
Qed.


Lemma sem_sub_eff: forall G t T,
    sem_type G t T false ->
    sem_type G t T true.
Proof.
  intros ? ? ? HY. intros n E WFE. intros ? ? EV.
  edestruct HY as (? & ? & ?); eauto.
  destruct H as (nx & ?).
  assert (1+n+nx > nx). lia. specialize (H _ H1).
  eapply eval_deterministic with (j:=1+n+nx) in EV. 2: eauto. 2: lia.
  rewrite EV in H. inversion H. subst. 
  eexists. split. eauto. eapply valt_dec. eauto. lia. 
Qed.

Lemma valt_fun_sub_eff: forall n v T1 T2,
    val_type n v (TFun T1 T2 false) ->
    val_type n v (TFun T1 T2 true).
Proof.
  intros. destruct n,v; try contradiction. simpl. eauto. 
  simpl in *. intros. edestruct H with (nx:=S nx) as (v & ? & ?). eauto.
  destruct H2 as (ny' & ?). assert (1+(n-nx)+ny' > ny'). lia. specialize (H2 _ H4).
  eapply eval_deterministic with (j:=1+(n-nx)+ny') in H1. 2: eauto. 2: lia.
  rewrite H1 in H2. inversion H2. subst. 
  eexists. split. eauto. eapply valt_dec. eauto. lia. 
Qed.

Lemma sem_sub_fun_eff: forall G t T1 T2,
    sem_type G t (TFun T1 T2 false) true ->
    sem_type G t (TFun T1 T2 true) true.
Proof.
  intros. intros n E WFE. intros ? ? EV. 
  edestruct (H n E WFE _ _ EV) as (v & RT & VT).
  eapply valt_fun_sub_eff in VT.
  eexists. split; eauto. 
Qed.


Lemma sem_app_pure: forall G f t T1 T2,
    sem_type G f (TFun T1 T2 false) false ->
    sem_type G t T1 false ->
    sem_type G (tapp f t) T2 false.
Proof.
  intros ? ? ? ? ? HF HX. intros n E WFE.
  destruct (HF n E WFE) as (vf & STF & VF).
  destruct (HX n E WFE) as (vx & STX & VX).
  destruct vf; simpl in VF; intuition.
  edestruct (VF 0) as (vy & STY & VY). replace (n-0) with n. 2: lia. eauto. 
  exists vy. split.
  - destruct STF as (n1 & STF).
    destruct STX as (n2 & STX).
    destruct STY as (n3 & STY).
    exists (1+n1+n2+n3). intros. destruct n0. lia.
    simpl. rewrite STF, STX, STY. 2,3,4: lia.
    eauto.
  - replace (n-0) with n in VY. 2: lia. eauto. 
Qed.


Lemma sem_app_impure: forall G f t T1 T2,
    sem_type G f (TFun T1 T2 true) true ->
    sem_type G t T1 true ->
    sem_type G (tapp f t) T2 true.
Proof.
  intros ? ? ? ? ? HF HX. intros n E WFE.

  intros n3 r3 EV.
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
  exists vy. split. eauto. eapply valt_dec. eauto. lia. 
Qed.



Lemma sem_app: forall G f t T1 T2 e1 e2 e3,
    sem_type G f (TFun T1 T2 e3) e1 ->
    sem_type G t T1 e2 ->
    sem_type G (tapp f t) T2 (e1 || e2 || e3).
Proof.
  intros. remember (e1 || e2 || e3) as e. destruct e.
  - eapply sem_app_impure.
    destruct e1,e3; try eapply sem_sub_eff in H; try eapply sem_sub_fun_eff in H; eauto.
    destruct e2; try eapply sem_sub_eff in H0; eauto.
  - eapply sem_app_pure.
    destruct e1,e2,e3; try inversion Heqe; eauto.
    destruct e1,e2,e3; try inversion Heqe; eauto. 
Qed.


Lemma sem_abs_impure: forall G t T1 T2,
    sem_type (T1::(TFun T1 T2 true)::G) t T2 true ->
    sem_type G (tabs t) (TFun T1 T2 true) false.
Proof.
  intros ? ? ? ? HY. intros n E WFE. 
  exists (vabs E t). split.
  - exists 1. intros. destruct n0. lia. eauto.
  - replace (S n - 1) with n. 2: lia. 
    induction n. simpl. eauto. 
    simpl. intros. unfold sem_type in HY. 
    edestruct (HY). 2: eapply H0.
    eapply envt_extend. eapply envt_extend. eapply envt_dec. eapply WFE. lia. 
    (* val_type (vabs E t) at lower index *)
    eapply valt_dec. eapply IHn. eapply envt_dec. eapply WFE. lia.
    lia.
    (* val_type vx *)
    eauto.
    (* val_type vy *)
    eexists. eauto.
Qed.

Lemma sem_abs_pure: forall G t T1 T2,
    sem_type (T1::(TFun T1 T2 true)::G) t T2 false ->
    sem_type G (tabs t) (TFun T1 T2 false) false.
Proof.
  intros ? ? ? ? HY. intros n E WFE.
  assert (length E = length G) as L. eapply WFE.
  exists (vabs E t). split.
  - exists 1. intros. destruct n0. lia. simpl. eauto.
  - simpl. intros. eapply HY. eapply envt_extend; eauto. eapply envt_extend; eauto.
    eapply envt_dec. eauto. lia.
    (* recursive function: use impure lemma *)
    edestruct (sem_abs_impure) as (? & ? & ?). eapply sem_sub_eff. eauto. eauto.
    destruct H0. assert (S x0 > x0). lia. specialize (H0 _ H2). simpl in H0. inversion H0. subst x.
    eapply valt_dec. eauto. lia. 
Qed.

Lemma sem_abs: forall G t T1 T2 e,
    sem_type (T1::(TFun T1 T2 true)::G) t T2 e ->
    sem_type G (tabs t) (TFun T1 T2 e) false.
Proof.
  intros. destruct e.
  - eapply sem_abs_impure; eauto.
  - eapply sem_abs_pure; eauto. 
Qed.


                                                       
(* ---------- LR fundamental property  ---------- *)

Theorem fundamental: forall G t T e,
    has_type G t T e ->
    sem_type G t T e.
Proof.
  intros ? ? ? ? W. 
  induction W.
  - eapply sem_true; eauto.
  - eapply sem_false; eauto.
  - eapply sem_var; eauto.
  - eapply sem_app; eauto. 
  - eapply sem_abs; eauto. 
  - eapply sem_sub_eff; eauto. 
Qed.

Corollary safety: forall t T e,
  has_type [] t T e ->
  forall n, exp_type_impure n [] t T.
Proof. 
  intros. intros ? ? EV.
  assert (sem_type [] t T true) as ST. {
    eapply fundamental in H as ST; eauto.
    destruct e. eauto. eapply sem_sub_eff; eauto. }  
  edestruct (ST n []) as (v & ? & ?).
  eapply envt_empty. eauto. 
  eexists v. intuition.
Qed.

Corollary safety_termination: forall t T,
  has_type [] t T false ->
  exists v, tevaln [] t v.
Proof. 
  intros. 
  eapply fundamental in H as ST; eauto.
  edestruct (ST 0 []) as (v & ? & ?).
  eapply envt_empty. 
  eexists v. intuition.
Qed.


End STLC.
