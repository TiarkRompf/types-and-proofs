(* Full safety for STLC *)

(*

An LR-based termination and semantic soundness proof for STLC.

Add first-order mutable references (restricted to TBool)

Binary logical relation with contextual equivalence.

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
  | TFun   : ty -> ty -> ty
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

Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
    has_type env ttrue TBool
| t_false: forall env,
    has_type env tfalse TBool
| t_var: forall x env T,
    indexr x env = Some T ->
    has_type env (tvar x) T
| t_ref: forall t env,
    has_type env t TBool ->
    has_type env (tref t) TRef
| t_get: forall t env,
    has_type env t TRef ->
    has_type env (tget t) TBool
| t_put: forall t t2 env,
    has_type env t TRef ->
    has_type env t2 TBool ->
    has_type env (tput t t2) TBool
| t_app: forall env f t T1 T2,
    has_type env f (TFun T1 T2) ->
    has_type env t T1 ->
    has_type env (tapp f t) T2
| t_abs: forall env t T1 T2,
    has_type (T1::env) t T2 ->
    has_type env (tabs t) (TFun T1 T2)
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

(* value interpretation of terms *)
Definition tevaln M env e M' v :=
  exists nm,
  forall n,
    n > nm ->
    teval n M env e = (M', Some (Some v)).


(* ---------- LR definitions  ---------- *)

Definition stty: Type := (nat -> nat -> Prop). (* partial bijection *)

Definition strel (M: stty) := M.

Definition st_empty: stty := (fun i j => False).

Definition st_extend L1 L2 (M: stty) :=
  fun l1 l2 =>
    (l1 = L1 /\ l2 = L2) \/
      (l1 <> L1 /\ l2 <> L2 /\ strel M l1 l2).


Definition store_type (S1 S2: stor) (M: stty) :=
  (forall l1 l2,
      strel M l1 l2 ->
      exists b,
        indexr l1 S1 = Some (vbool b) /\
        indexr l2 S2 = Some (vbool b)) /\
  (* enforce that strel is a partial bijection *)
  (forall l1 l2 l2',
      strel M l1 l2 ->
      strel M l1 l2' ->
      l2 = l2') /\
  (forall l1 l1' l2,
      strel M l1 l2 ->
      strel M l1' l2 ->
      l1 = l1').

Definition st_chain (M:stty) (M1:stty) :=
  (forall l1 l2,
      strel M l1 l2 ->
      strel M1 l1 l2).

Fixpoint val_type M v1 v2 T : Prop :=
  match v1, v2, T with
  | vbool b1, vbool b2, TBool =>  
      b1 = b2
  | vref l1, vref l2, TRef => 
      strel M l1 l2
  | vabs H1 ty1, vabs H2 ty2, TFun T1 T2 =>
      forall S1' S2' M' vx1 vx2,
        st_chain M M' ->
        store_type S1' S2' M' ->
        val_type M' vx1 vx2 T1 ->
        exists S1'' S2'' M'' vy1 vy2,
          st_chain M' M'' /\
          tevaln S1' (vx1::H1) ty1 S1'' vy1 /\
          tevaln S2' (vx2::H2) ty2 S2'' vy2 /\
          store_type S1'' S2'' M'' /\
          val_type M'' vy1 vy2 T2
  | _,_,_ =>
      False
  end.


Definition exp_type S1 S2 M H1 H2 t1 t2 T :=
  exists S1' S2' M' v1 v2,
    st_chain M M' /\
    tevaln S1 H1 t1 S1' v1 /\
    tevaln S2 H2 t2 S2' v2 /\
    store_type S1' S2' M' /\
    val_type M' v1 v2 T.

Definition env_type M (H1 H2: venv) (G: tenv) :=
  length H1 = length G /\
  length H2 = length G /\
    forall x T,
      indexr x G = Some T ->
      exists v1 v2,
        indexr x H1 = Some v1 /\
        indexr x H2 = Some v2 /\
        val_type M v1 v2 T.

Definition sem_type G t1 t2 T :=
  forall S1 S2 M H1 H2,
    env_type M H1 H2 G ->
    store_type S1 S2 M ->
    exp_type S1 S2 M H1 H2 t1 t2 T.


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
  intros. unfold st_chain. eauto. 
Qed.

Lemma stchain_extend: forall S1 S2 M,
    store_type S1 S2 M ->
    st_chain M (st_extend (length S1) (length S2) M).
Proof.
  intros.
  unfold st_chain, st_extend. intros. unfold strel at 1.
  right. destruct H as (L1 & L2 & L3). 
  edestruct L1 as (? & ? & ?). eauto.
  eapply indexr_var_some' in H, H1. intuition.
Qed.

Lemma stchain_chain: forall M1 M2 M3,
    st_chain M1 M2 ->
    st_chain M2 M3 ->
    st_chain M1 M3.
Proof.
  intros. unfold st_chain in *. 
  intuition. 
Qed.

Lemma envt_empty:
    env_type st_empty [] [] [].
Proof.
  intros. split. 2: split.
  eauto. eauto.
  intros. inversion H. 
Qed.

Lemma envt_extend: forall M H1 H2 G v1 v2 T1,
    env_type M H1 H2 G ->
    val_type M v1 v2 T1 ->
    env_type M (v1::H1) (v2::H2) (T1::G).
Proof.
  intros. 
  remember H as WFE. clear HeqWFE.
  destruct H as (L1 & L2 & ?). split. 2: split.
  simpl. eauto. simpl. eauto. 
  intros x T IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX. subst T1.
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

Lemma storet_empty:
    store_type [] [] st_empty.
Proof.
  intros. split. 2: split. 
  - intros. inversion H.
  - intros. inversion H.
  - intros. simpl in *. intuition.
Qed.

Lemma storet_extend: forall S1 S2 M vx1 vx2,
    store_type S1 S2 M ->
    val_type M vx1 vx2 TBool ->
    store_type (vx1 :: S1) (vx2 :: S2) (st_extend (length S1) (length S2) M).
Proof.
  intros. destruct H as (L1 & L2 & L3).
  split. 2: split. 
  - intros. destruct vx1, vx2; inversion H0.
      subst b0. simpl in H. destruct H.
    + exists b. destruct H. subst l1 l2.
      rewrite indexr_head, indexr_head; eauto. 
    + edestruct L1 as (? & ? & ?). eapply H. 
      exists x. rewrite indexr_skip, indexr_skip; intuition. 
  - intros. destruct H, H1; intuition.
    eapply L2; eauto.
  - intros. destruct H, H1; intuition.
    eapply L3; eauto. 
Qed.

Lemma storet_update: forall S1 S2 M l1 l2 vx1 vx2,
    store_type S1 S2 M ->
(*    l1 < length1 M ->
    l2 < length2 M -> *)
    strel M l1 l2 ->
    val_type M vx1 vx2 TBool ->
    store_type (update S1 l1 vx1) (update S2 l2 vx2) M.
Proof.
  intros. destruct H as (L1 & L2 & L3 ).
  destruct vx1, vx2; inversion H1.
  split. 2: split. 
  - intros. bdestruct (l0 =? l1); bdestruct (l3 =? l2).
    + subst l0 l3. eexists. rewrite update_indexr_hit, update_indexr_hit; intuition.
      edestruct L1 as (? & ? & ?). eauto. eapply indexr_var_some'. eauto.
      edestruct L1 as (? & ? & ?). eauto. eapply indexr_var_some'. eauto. 
    + subst l0. destruct H4. eapply L2; eauto.
    + subst l3. destruct H3. eapply L3; eauto.
    + rewrite update_indexr_miss, update_indexr_miss; eauto.
  - eauto.
  - eauto. 
Qed.


Lemma valt_store_extend: forall M M' vx1 vx2 T,
    val_type M vx1 vx2 T ->
    st_chain M M' ->
    val_type M' vx1 vx2 T.
Proof.
  intros. destruct vx1, vx2, T; simpl in H; try contradiction.
  - simpl. eauto.
  - simpl. intuition. 
  - simpl. intros. destruct (H S1' S2' M'0 vx1 vx2); eauto.
    eapply stchain_chain; eauto. 
Qed.

Lemma envt_store_extend: forall M M' H1 H2 G,
    env_type M H1 H2 G ->
    st_chain M M' ->
    env_type M' H1 H2 G.
Proof.
  intros. destruct H as (L1 & L2 & IX).
  split. 2: split. 
  - eauto.
  - eauto. 
  - intros. edestruct IX as (v1 & v2 & IX1' & IX2' & VX). eauto.
    exists v1, v2. split. 2: split.
    eauto. eauto. eapply valt_store_extend; eauto.
Qed.


(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_true: forall G,
    sem_type G ttrue ttrue TBool.
Proof.
  intros. intros S1 S2 M H1 H2 WFE ST.
  exists S1, S2, M, (vbool true), (vbool true).
  split. 2: split. 3: split. 4: split. 
  - eapply stchain_refl. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto. 
  - simpl. eauto. 
Qed.

Lemma sem_false: forall G,
    sem_type G tfalse tfalse TBool.
Proof.
  intros. intros S1 S2 M H1 H2 WFE ST.
  exists S1, S2, M, (vbool false), (vbool false).
  split. 2: split. 3: split. 4: split. 
  - eapply stchain_refl. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
  - simpl. eauto. 
Qed.

Lemma sem_var: forall G x T,
    indexr x G = Some T ->
    sem_type G (tvar x) (tvar x) T.
Proof.
  intros. intros S1 S2 M H1 H2 WFE ST.
  eapply WFE in H as IX. destruct IX as (v1 & v2 & IX1 & IX2 & VX).
  exists S1, S2, M, v1, v2.
  split. 2: split. 3: split. 4: split. 
  - eapply stchain_refl. 
  - exists 0. intros. destruct n. lia. simpl. rewrite IX1. eauto.
  - exists 0. intros. destruct n. lia. simpl. rewrite IX2. eauto.
  - eauto.
  - eauto. 
Qed.

Lemma sem_ref: forall G t1 t2,
    sem_type G t1 t2 TBool ->
    sem_type G (tref t1) (tref t2) TRef.
Proof.
  intros. intros S1 S2 M H1 H2 WFE ST.
  destruct (H S1 S2 M H1 H2 WFE ST) as (S1' & S2' & M' & vx1 & vx2 & SC & TX1 & TX2 & ST' & VX).
  exists (vx1::S1'), (vx2::S2'), (st_extend (length S1') (length S2') M'), (vref (length S1')), (vref (length S2')).
  split. 2: split. 3: split. 4: split. 
  - eapply stchain_chain; eauto.
    eapply stchain_extend; eauto.
  - destruct TX1 as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. eauto. lia.
  - destruct TX2 as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. eauto. lia.
  - eapply storet_extend. eauto. eauto. 
  - simpl. destruct ST' as (L1 & L2 & L3).
    unfold strel, st_extend in *. simpl. left. intuition. 
Qed.

Lemma sem_get: forall G t1 t2,
    sem_type G t1 t2 TRef ->
    sem_type G (tget t1) (tget t2) TBool.
Proof.
  intros. intros S1 S2 M H1 H2 WFE ST.
  destruct (H S1 S2 M H1 H2 WFE ST) as (S1' & S2' & M' & vx1 & vx2 & SC & TX1 & TX2 & ST' & VX).
  destruct vx1, vx2; simpl in VX; intuition.
  destruct ST' as (L1 & L2 & L3).
  destruct (L1 _ _ VX) as (b & IX1 & IX2).
  exists S1', S2', M', (vbool b), (vbool b).
  split. 2: split. 3: split. 4: split. 
  - eauto. 
  - destruct TX1 as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. rewrite IX1. eauto. lia.
  - destruct TX2 as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. rewrite IX2. eauto. lia.
  - repeat split; eauto. 
  - simpl. eauto. 
Qed.

Lemma sem_put: forall G t1 t2 t1' t2',
    sem_type G t1 t2 TRef ->
    sem_type G t1' t2' TBool ->
    sem_type G (tput t1 t1') (tput t2 t2') TBool.
Proof.
  intros. intros S1 S2 M E1 E2 WFE ST.
  destruct (H S1 S2 M E1 E2 WFE ST) as (S1' & S2' & M' & vx1 & vx2 & SC & TX1 & TX2 & ST' & VX).
  eapply envt_store_extend in WFE as WFE'. 2: eauto.
  destruct (H0 S1' S2' M' E1 E2 WFE' ST') as (S1'' & S2'' & M'' & vy1 & vy2 & SC' & TY1 & TY2 & ST'' & VY).
  eapply valt_store_extend in VX. 2: eauto. 
  destruct vx1, vx2; simpl in VX; intuition.
  destruct vy1, vy2; simpl in VY; intuition.
  destruct ST'' as (L1 & L2 & L3).
  destruct (L1 _ _ VX) as (b1 & IX1 & IX2). 
  exists (update S1'' i (vbool b)), (update S2'' i0 (vbool b0)), M'', (vbool true), (vbool true).
  split. 2: split. 3: split. 4: split. 
  - eapply stchain_chain; eauto. 
  - destruct TX1 as (n1 & TX).
    destruct TY1 as (n2 & TY).
    exists (1+n1+n2). intros. destruct n. lia. simpl. rewrite TX, TY, IX1. eauto. lia. lia. 
  - destruct TX2 as (n1 & TX).
    destruct TY2 as (n2 & TY).
    exists (1+n1+n2). intros. destruct n. lia. simpl. rewrite TX, TY, IX2. eauto. lia. lia. 
  - eapply storet_update; eauto. repeat split; eauto. 
  - simpl. eauto. 
Qed.

Lemma sem_app: forall G f1 f2 t1 t2 T1 T2,
    sem_type G f1 f2 (TFun T1 T2) ->
    sem_type G t1 t2 T1 ->
    sem_type G (tapp f1 t1) (tapp f2 t2) T2.
Proof.
  intros ? ? ? ? ? ? ? HF HX. intros S1 S2 M E1 E2 WFE ST.
  destruct (HF S1 S2 M E1 E2 WFE ST) as (S1' & S2' & M' & vf1 & vf2 & SC & TF1 & TF2 & ST' & VF).
  eapply envt_store_extend in WFE as WFE'. 2: eauto.
  destruct (HX S1' S2' M' E1 E2 WFE' ST') as (S1'' & S2'' & M'' & vx1 & vx2 & SC' & TX1 & TX2 & ST'' & VX).
  destruct vf1, vf2; simpl in VF; intuition.
  edestruct VF as (S1''' & S2''' & M'''& vy1 & vy2 & SC'' & TY1 & TY2 & ST''' & VY). eauto. eauto. eauto. 
  exists S1''', S2''', M''', vy1, vy2.
  split. 2: split. 3: split. 4: split. 
  - eapply stchain_chain. eauto. eapply stchain_chain; eauto. 
  - destruct TF1 as (n1 & TF).
    destruct TX1 as (n2 & TX).
    destruct TY1 as (n3 & TY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite TF, TX, TY. 2,3,4: lia.
    eauto.
  - destruct TF2 as (n1 & TF).
    destruct TX2 as (n2 & TX).
    destruct TY2 as (n3 & TY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite TF, TX, TY. 2,3,4: lia.
    eauto.
  - eauto. 
  - eauto.
Qed.

Lemma sem_abs: forall G t1 t2 T1 T2,
    sem_type (T1::G) t1 t2 T2 ->
    sem_type G (tabs t1) (tabs t2) (TFun T1 T2).
Proof.
  intros ? ? ? ? ? HY. intros S1 S2 M E1 E2 WFE ST.
  assert (length E1 = length G) as L1. eapply WFE.
  assert (length E2 = length G) as L2. eapply WFE.
  exists S1, S2, M, (vabs E1 t1), (vabs E2 t2).
  split. 2: split. 3: split. 4: split. 
  - eapply stchain_refl. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto. 
  - simpl. intros. eapply HY. eapply envt_extend; eauto. eapply envt_store_extend; eauto. eauto.
Qed.


                                                       
(* ---------- LR fundamental property  ---------- *)

Theorem fundamental: forall G t T,
    has_type G t T ->
    sem_type G t t T.
Proof.
  intros ? ? ? W. 
  induction W.
  - eapply sem_true; eauto.
  - eapply sem_false; eauto.
  - eapply sem_var; eauto.
  - eapply sem_ref; eauto.
  - eapply sem_get; eauto.
  - eapply sem_put; eauto.
  - eapply sem_app; eauto. 
  - eapply sem_abs; eauto.
Qed.

Corollary safety: forall t T,
  has_type [] t T ->
  exp_type [] [] st_empty [] [] t t T.
Proof. 
  intros. eapply fundamental in H as ST; eauto.
  destruct (ST [] [] st_empty [] []) as (S1' & S2' & M' & v1 & v2 & ? & ? & ? & ? & ?).
  eapply envt_empty.
  eapply storet_empty.
  exists S1', S2', M', v1, v2. intuition.
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


(* semantic equivalence between contexts *)
Definition sem_ctx_type C C' G1 T1 G2 T2 :=
  forall e e',
    sem_type G1 e e' T1 ->
    sem_type G2 (C e) (C' e') T2.

(* congruence *)
Theorem congr:
  forall C G1 T1 G2 T2,
    ctx_type C G1 T1 G2 T2 ->
    sem_ctx_type C C G1 T1 G2 T2.
Proof.
  intros ? ? ? ? ? CX.
  induction CX; intros ? ? ?.
  - eauto.
  - eapply sem_app. eauto. eapply fundamental. eauto.
  - eapply sem_app. eapply fundamental. eauto. eauto.
  - eapply sem_abs. eauto.
Qed.


Lemma adequacy: forall e e',
  sem_type [] e e' TBool ->
  exists S S' v,
    tevaln [] [] e S v /\
    tevaln [] [] e' S' v.
Proof. 
  intros. 
  assert (env_type st_empty [] [] []) as WFE. { unfold env_type; intuition. inversion H0. }
  unfold sem_type in H. specialize (H [] [] st_empty [] [] WFE). 
  destruct H as (? & ? & ? & ? & ? & ?). eapply storet_empty. 
  intuition. destruct x2, x3; inversion H4. subst b0.
  eexists _,_,_. split; eauto. 
Qed.

(* contextual equivalence: no boolean context can detect a difference *)
Definition contextual_equiv G t1 t2 T1 :=
  forall C,
    ctx_type C G T1 [] TBool ->
    exists S1 S2 v,
      tevaln [] [] (C t1) S1 v /\
      tevaln [] [] (C t2) S2 v.

(* soundness of binary logical relation: implies contextual equivalence *)
Theorem soundess: forall G t1 t2 T,
  sem_type G t1 t2 T ->
  contextual_equiv G t1 t2 T.
Proof.
  intros. intros ? ?.
  eapply adequacy.
  eapply congr; eauto. 
Qed.


End STLC.
