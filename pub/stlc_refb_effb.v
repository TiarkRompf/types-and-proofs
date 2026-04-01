(* Full safety for STLC *)

(*

An LR-based termination and semantic soundness proof for STLC.

Add first-order mutable references (restricted to TBool)

Add simple yes/no effect annotations.

Unary logical relation.

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
  | TRef   : ty
  | TFun   : ty -> ty -> bool -> ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tref : tm -> tm
  | tget : tm -> tm
  | tput : tm -> tm -> tm
  | tapp : tm -> tm -> tm
  | tabs : tm -> tm
.

Inductive vl: Type :=
| vbool :  bool -> vl
| vref  :  id -> vl
| vabs  :  list vl -> tm -> vl
.

Definition venv := list vl.
Definition tenv := list ty.

Definition stor := list vl.

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.
#[global] Hint Unfold stor.


(* ---------- syntactic typing rules ---------- *)

Inductive has_type : tenv -> tm -> ty -> bool -> Prop :=
| t_true: forall env,
    has_type env ttrue TBool false
| t_false: forall env,
    has_type env tfalse TBool false
| t_var: forall x env T,
    indexr x env = Some T ->
    has_type env (tvar x) T false
| t_ref: forall t env e,
    has_type env t TBool e ->
    has_type env (tref t) TRef e
| t_get: forall t env e,
    has_type env t TRef e ->
    has_type env (tget t) TBool true
| t_put: forall t t2 env e e2,
    has_type env t TRef e ->
    has_type env t2 TBool e2 ->
    has_type env (tput t t2) TBool true
| t_app: forall env f t T1 T2 e1 e2 e3,
    has_type env f (TFun T1 T2 e3) e1 ->
    has_type env t T1 e2 ->
    has_type env (tapp f t) T2 (e1 || e2 || e3)
| t_abs: forall env t T1 T2 e,
    has_type (T1::env) t T2 e ->
    has_type env (tabs t) (TFun T1 T2 e) false
| t_sub_eff: forall env t T,
    has_type env t T false ->
    has_type env t T true
.

(* ---------- operational semantics ---------- *)

Fixpoint teval(n: nat)(M:stor)(env: venv)(t: tm){struct n}: stor * option (option vl) :=
  match n with
    | 0 => (M, None)
    | S n =>
      match t with
        | ttrue      => (M, Some (Some (vbool true)))
        | tfalse     => (M, Some (Some (vbool false)))
        | tvar x     => (M, Some (indexr x env))
        | tref ex    =>
          match teval n M env ex with
            | (M', None)           => (M', None)
            | (M', Some None)      => (M', Some None)
            | (M', Some (Some vx)) => (vx::M', Some (Some (vref (length M'))))
          end
        | tget ex    =>
          match teval n M env ex with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vabs _ _))) => (M', Some None)
            | (M', Some (Some (vref x))) => (M', Some (indexr x M'))
          end
        | tput er ex    =>
          match teval n M env er with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vabs _ _))) => (M', Some None)
            | (M', Some (Some (vref x))) =>
              match teval n M' env ex with
                | (M'', None) => (M'', None)
                | (M'', Some None) => (M'', Some None)
                | (M'', Some (Some vx)) =>
                    match indexr x M'' with
                    | Some v => (update M'' x vx, Some (Some (vbool true)))
                    | _ => (M'', Some None)
                    end
              end
          end
        | tabs y     => (M, Some (Some (vabs env y)))
        | tapp ef ex =>
          match teval n M env ef with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vref _))) => (M', Some None)
            | (M', Some (Some (vabs env2 ey))) =>
              match teval n M' env ex with
                | (M'', None) => (M'', None)
                | (M'', Some None) => (M'', Some None)
                | (M'', Some (Some vx)) =>
                  teval n M'' (vx::env2) ey
              end
          end
      end
  end.

Definition tevaln M env e M' v :=
  exists nm,
  forall n,
    n > nm ->
    teval n M env e = (M', Some (Some v)).


(* ---------- LR definitions  ---------- *)

Definition stty := nat.

Definition store_type (S: stor) (M: stty) :=
  length S = M /\
    forall i,
      i < M ->
      exists b, indexr i S = Some (vbool b).

Definition st_chain (M:stty) (M1:stty) :=
  M <= M1.

Fixpoint val_type M v T : Prop :=
  match v, T with
  | vbool _, TBool =>
      True
  | vref l, TRef =>
      l < M
  | vabs H ty, TFun T1 T2 _ =>
      forall S' M' vx,
        st_chain M M' ->
        store_type S' M' ->
        val_type M' vx T1 ->
        exists S'' M'' vy,
          st_chain M' M'' /\
          tevaln S' (vx::H) ty S'' vy /\
          store_type S'' M'' /\
          val_type M'' vy T2
  | _,_ =>
      False
  end.

Definition exp_type S M H t T :=
  exists S' M' v,
    st_chain M M' /\
    tevaln S H t S' v /\
    store_type S' M' /\
    val_type M' v T.

Definition env_type M (H: venv) (G: tenv) :=
  length H = length G /\
    forall x T,
      indexr x G = Some T ->
      exists v,
        indexr x H = Some v /\
        val_type M v T.

Definition sem_type G t T (e: bool) :=
  forall S M H,
    env_type M H G ->
    store_type S M ->
    exp_type S M H t T.


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: core.

#[export] Hint Constructors has_type: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.


(* ---------- LR helper lemmas  ---------- *)

Lemma stchain_refl: forall M,
    st_chain M M.
Proof.
  intros. intuition.
Qed.

Lemma envt_empty:
    env_type 0 [] [].
Proof.
  intros. split. eauto. intros. inversion H.
Qed.

Lemma envt_extend: forall M E G v1 T1,
    env_type M E G ->
    val_type M v1 T1 ->
    env_type M (v1::E) (T1::G).
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

Lemma storet_empty:
    store_type [] 0.
Proof.
  intros. split. eauto. intros. inversion H.
Qed.

Lemma storet_extend: forall S M vx,
    store_type S M ->
    val_type M vx TBool ->
    store_type (vx :: S) (1 + M).
Proof.
  intros. destruct H. split.
  - simpl. lia.
  - intros. bdestruct (i <? M).
    eapply H1 in H3 as H4. destruct H4. exists x. rewrite indexr_skip. eauto. lia.
    destruct vx; inversion H0. exists b. replace i with (length S).
    rewrite indexr_head. eauto. lia.
Qed.

Lemma valt_store_extend: forall M M' vx T,
    val_type M vx T ->
    st_chain M M' ->
    val_type M' vx T.
Proof.
  intros M M' vx T VT SC.
  destruct vx; destruct T; simpl in VT; try contradiction.
  - exact I.
  - eapply Nat.lt_le_trans; eauto.
  - intros S' M'' vx' SC' ST VX.
    destruct (VT S' M'' vx' ltac:(unfold st_chain in *; lia) ST VX) as (S'' & M''' & vy & SC'' & TY & STY & VY).
    exists S'', M''', vy. intuition.
Qed.

Lemma envt_store_extend: forall M M' H G,
    env_type M H G ->
    st_chain M M' ->
    env_type M' H G.
Proof.
  intros. destruct H0 as (L & IX). split.
  - eauto.
  - intros. edestruct IX as (v & IX' & VX). eauto.
    exists v. split. eauto. eapply valt_store_extend; eauto.
Qed.


(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_sub_eff: forall G t T,
    sem_type G t T false ->
    sem_type G t T true.
Proof.
  intros. eauto.
Qed.

Lemma sem_true: forall G,
    sem_type G ttrue TBool false.
Proof.
  intros. intros S M E WFE ST.
  exists S, M, (vbool true).
  split. 2: split. 3: split.
  - eapply stchain_refl.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
  - simpl. eauto.
Qed.

Lemma sem_false: forall G,
    sem_type G tfalse TBool false.
Proof.
  intros. intros S M E WFE ST.
  exists S, M, (vbool false).
  split. 2: split. 3: split.
  - eapply stchain_refl.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
  - simpl. eauto.
Qed.

Lemma sem_var: forall G x T,
    indexr x G = Some T ->
    sem_type G (tvar x) T false.
Proof.
  intros. intros S M E WFE ST.
  eapply WFE in H as IX. destruct IX as (v & IX & VX).
  exists S, M, v.
  split. 2: split. 3: split.
  - eapply stchain_refl.
  - exists 0. intros. destruct n. lia. simpl. rewrite IX. eauto.
  - eauto.
  - eauto.
Qed.

Lemma sem_ref: forall G t e,
    sem_type G t TBool e ->
    sem_type G (tref t) TRef e.
Proof.
  intros. intros S M E WFE ST.
  destruct (H S M E WFE ST) as (S' & M' & vx & SC & TX & ST' & VX).
  exists (vx::S'), (1+M'), (vref (length S')).
  split. 2: split. 3: split.
  - unfold st_chain in *. lia.
  - destruct TX as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. eauto. lia.
  - eapply storet_extend. eauto. eauto.
  - simpl. destruct ST'. lia.
Qed.

Lemma sem_get: forall G t e,
    sem_type G t TRef e ->
    sem_type G (tget t) TBool true.
Proof.
  intros. intros S M E WFE ST.
  destruct (H S M E WFE ST) as (S' & M' & vx & SC & TX & ST' & VX).
  destruct vx; simpl in VX; intuition.
  destruct ST' as (L & B). subst M'.
  eapply indexr_var_some in VX as VX'. destruct VX' as (vx & IX).
  exists S', (length S'), vx.
  split. 2: split. 3: split.
  - eauto.
  - destruct TX as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. rewrite IX. eauto. lia.
  - unfold store_type. eauto.
  - edestruct B as (b & IX'). eauto. rewrite IX in IX'. inversion IX'. simpl. eauto.
Qed.

Lemma sem_put: forall G t t2 e1 e2,
    sem_type G t TRef e1 ->
    sem_type G t2 TBool e2 ->
    sem_type G (tput t t2) TBool true.
Proof.
  intros. intros S M E WFE ST.
  destruct (H S M E WFE ST) as (S' & M' & vx & SC & TX & ST' & VX).
  eapply envt_store_extend in WFE as WFE'. 2: eauto.
  destruct (H0 S' M' E WFE' ST') as (S'' & M'' & vy & SC' & TY & ST'' & VY).
  eapply valt_store_extend in VX. 2: eauto.
  destruct vx; simpl in VX; intuition.
  destruct vy; simpl in VY; intuition.
  destruct ST'' as (L & B). subst M''.
  eapply indexr_var_some in VX as VX'. destruct VX' as (vx & IX).
  exists (update S'' i (vbool b)), (length S''), (vbool true).
  split. 2: split. 3: split.
  - unfold st_chain in *. lia.
  - destruct TX as (n1 & TX).
    destruct TY as (n2 & TY).
    exists (1+n1+n2). intros. destruct n. lia. simpl. rewrite TX, TY, IX. eauto. lia. lia.
  - split. rewrite <-update_length. eauto. intros.
    bdestruct (i0 =? i). subst i0. exists b. rewrite update_indexr_hit; eauto.
    edestruct B. eauto. exists x. rewrite update_indexr_miss; eauto.
  - simpl. eauto.
Qed.

Lemma sem_app: forall G f t T1 T2 e1 e2 e3,
    sem_type G f (TFun T1 T2 e3) e1 ->
    sem_type G t T1 e2 ->
    sem_type G (tapp f t) T2 (e1 || e2 || e3).
Proof.
  intros ? ? ? ? ? ? ? ? HF HX. intros S M E WFE ST.
  destruct (HF S M E WFE ST) as (S' & M' & vf & SC & TF & ST' & VF).
  eapply envt_store_extend in WFE as WFE'. 2: eauto.
  destruct (HX S' M' E WFE' ST') as (S'' & M'' & vx & SC' & TX & ST'' & VX).
  destruct vf; simpl in VF; intuition.
  edestruct VF as (S''' & M''' & vy & SC'' & TY & ST''' & VY). eauto. eauto. eauto.
  exists S''', M''', vy.
  split. 2: split. 3: split.
  - unfold st_chain in *. lia.
  - destruct TF as (n1 & TF).
    destruct TX as (n2 & TX).
    destruct TY as (n3 & TY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite TF, TX, TY. 2,3,4: lia.
    eauto.
  - eauto.
  - eauto.
Qed.

Lemma sem_abs: forall G t T1 T2 e,
    sem_type (T1::G) t T2 e ->
    sem_type G (tabs t) (TFun T1 T2 e) false.
Proof.
  intros ? ? ? ? ? HY. intros S M E WFE ST.
  assert (length E = length G) as L. eapply WFE.
  exists S, M, (vabs E t).
  split. 2: split. 3: split.
  - eapply stchain_refl.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
  - simpl. intros. eapply HY. eapply envt_extend; eauto. eapply envt_store_extend; eauto. eauto.
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
  - eapply sem_ref; eauto.
  - eapply sem_get; eauto.
  - eapply sem_put; eauto.
  - eapply sem_app; eauto.
  - eapply sem_abs; eauto.
  - eapply sem_sub_eff; eauto.
Qed.

Corollary safety: forall t T e,
  has_type [] t T e ->
  exp_type [] 0 [] t T.
Proof.
  intros. eapply fundamental in H as ST; eauto.
  destruct (ST [] 0 []) as (S' & M' & v & ? & ? & ? & ?).
  eapply envt_empty.
  eapply storet_empty.
  exists S', M', v. intuition.
Qed.

Theorem store_invariance: forall t G T,
    sem_type G t T false ->
    forall H,
      env_type 0 H G ->
      exp_type [] 0 H t T.
Proof.
  intros. eapply H; eauto. eapply storet_empty.
Qed.

End STLC.
