(* Full safety for STLC *)

(*

An LR-based termination and semantic soundness proof for STLC.

Add first-order mutable references (restricted to TBool)

Binary logical relation with contextual equivalence.

Add simple yes/no effect tracking, prove store invariance.

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
  | TFun   : ty -> ty -> Prop -> ty
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

Inductive has_type : tenv -> tm -> ty -> Prop -> Prop :=
| t_true: forall env,
    has_type env ttrue TBool False
| t_false: forall env,
    has_type env tfalse TBool False
| t_var: forall x env T,
    indexr x env = Some T ->
    has_type env (tvar x) T False
| t_ref: forall t env e,
    has_type env t TBool e ->
    has_type env (tref t) TRef e
| t_get: forall t env e,
    has_type env t TRef e ->
    has_type env (tget t) TBool True
| t_put: forall t t2 env e e2,
    has_type env t TRef e ->
    has_type env t2 TBool e2 ->
    has_type env (tput t t2) TBool True
| t_app: forall env f t T1 T2 e1 e2 e3,
    has_type env f (TFun T1 T2 e3) e1 ->
    has_type env t T1 e2 ->
    has_type env (tapp f t) T2 (e1 \/ e2 \/ e3)
| t_abs: forall env t T1 T2 e,
    has_type (T1::env) t T2 e ->
    has_type env (tabs t) (TFun T1 T2 e) False
| t_sub_eff: forall env t T,
    has_type env t T False ->
    has_type env t T True
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

Definition st_chain (M:stty) (M1:stty) (u: Prop) :=
  u -> (forall l1 l2,
      strel M l1 l2 ->
      strel M1 l1 l2).

Fixpoint val_type M v1 v2 (u: Prop) T : Prop :=
  match v1, v2, T with
  | vbool b1, vbool b2, TBool =>  
      b1 = b2
  | vref l1, vref l2, TRef => 
      u -> strel M l1 l2
  | vabs H1 ty1, vabs H2 ty2, TFun T1 T2 e2 =>
      forall S1' S2' M' vx1 vx2 (uy:Prop),
        (uy \/ e2 -> u) ->
        st_chain M M' (uy \/ e2) ->
        store_type S1' S2' M' ->
        val_type M' vx1 vx2 (uy \/ e2) T1 ->
        exists S1'' S2'' M'' vy1 vy2,
          st_chain M' M'' (uy) /\
          tevaln S1' (vx1::H1) ty1 S1'' vy1 /\
          tevaln S2' (vx2::H2) ty2 S2'' vy2 /\
          store_type S1'' S2'' M'' /\
          val_type M'' vy1 vy2 uy T2
  | _,_,_ =>
      False
  end.


Definition exp_type S1 S2 M H1 H2 t1 t2 u T :=
  exists S1' S2' M' v1 v2,
    st_chain M M' u /\
    tevaln S1 H1 t1 S1' v1 /\
    tevaln S2 H2 t2 S2' v2 /\
    store_type S1' S2' M' /\
    val_type M' v1 v2 u T.

Definition env_type M (H1 H2: venv) u (G: tenv) :=
  length H1 = length G /\
  length H2 = length G /\
    forall x T,
      indexr x G = Some T ->
      exists v1 v2,
        indexr x H1 = Some v1 /\
        indexr x H2 = Some v2 /\
        val_type M v1 v2 u T.

Definition sem_type G t1 t2 e T :=
  forall S1 S2 M H1 H2 u,
    env_type M H1 H2 (u \/ e) G ->
    store_type S1 S2 M ->
    exp_type S1 S2 M H1 H2 t1 t2 u T.


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: core.

#[export] Hint Constructors has_type: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.




(* ---------- LR helper lemmas  ---------- *)

Lemma stchain_refl: forall M u,
    st_chain M M u.
Proof.
  intros. unfold st_chain. eauto. 
Qed.

Lemma stchain_extend: forall S1 S2 M u,
    store_type S1 S2 M ->
    st_chain M (st_extend (length S1) (length S2) M) u.
Proof.
  intros.
  unfold st_chain, st_extend. intros U. intros. unfold strel at 1.
  right. destruct H as (L1 & L2 & L3). 
  edestruct L1 as (? & ? & ?). eauto.
  eapply indexr_var_some' in H, H1. intuition.
Qed.

Lemma stchain_chain': forall M1 M2 M3 u1 u2,
    st_chain M1 M2 u1 ->
    st_chain M2 M3 u2 ->
    st_chain M1 M3 (u1 /\ u2).
Proof.
  intros. unfold st_chain in *. 
  intuition. 
Qed.

Lemma stchain_chain: forall M1 M2 M3 u,
    st_chain M1 M2 u ->
    st_chain M2 M3 u ->
    st_chain M1 M3 u.
Proof.
  intros. unfold st_chain in *. 
  intuition. 
Qed.

Lemma stchain_eff: forall M1 M2 (u u': Prop),
    st_chain M1 M2 u ->
    (u' -> u) ->
    st_chain M1 M2 u'.
Proof.
  intros. unfold st_chain in *. 
  intuition. 
Qed.


Lemma envt_empty: forall u,
    env_type st_empty [] [] u [].
Proof.
  intros. split. 2: split.
  eauto. eauto.
  intros. inversion H. 
Qed.

Lemma envt_extend: forall M H1 H2 G v1 v2 T1 u,
    env_type M H1 H2 u G ->
    val_type M v1 v2 u T1 ->
    env_type M (v1::H1) (v2::H2) u (T1::G).
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

Lemma storet_extend: forall S1 S2 M vx1 vx2 u,
    store_type S1 S2 M ->
    val_type M vx1 vx2 u TBool ->
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

Lemma storet_update: forall S1 S2 M l1 l2 vx1 vx2 u,
    store_type S1 S2 M ->
    strel M l1 l2 ->
    val_type M vx1 vx2 u TBool ->
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


Lemma valt_store_extend': forall M M' vx1 vx2 T u u',
    val_type M vx1 vx2 u T ->
    st_chain M M' u' -> (u' -> u) ->
    val_type M' vx1 vx2 u' T.
Proof.
  intros. destruct vx1, vx2, T; simpl in H; try contradiction.
  - simpl. eauto.
  - simpl. intuition. 
  - simpl. intros. destruct (H S1' S2' M'0 vx1 vx2 uy); eauto.
    eapply stchain_eff. eapply stchain_chain'. eapply H0. eapply H3. intuition. 
    (*destruct H6 as (? & ? & ? & ? & ?). intuition.
    eexists _, _, _, _, _. intuition.
    eapply stchain_eff. all: eauto. *)
Qed.

Lemma envt_store_extend': forall M M' H1 H2 G u u',
    env_type M H1 H2 u G ->
    st_chain M M' u' -> (u' -> u) ->
    env_type M' H1 H2 u' G.
Proof.
  intros. destruct H as (L1 & L2 & IX).
  split. 2: split. 
  - eauto.
  - eauto. 
  - intros. edestruct IX as (v1 & v2 & IX1' & IX2' & VX). eauto.
    exists v1, v2. split. 2: split.
    eauto. eauto. eapply valt_store_extend'; eauto.
Qed.

Lemma valt_store_extend: forall M M' vx1 vx2 T u,
    val_type M vx1 vx2 u T ->
    st_chain M M' u -> 
    val_type M' vx1 vx2 u T.
Proof. 
  intros. eapply valt_store_extend'; eauto.
Qed.

Lemma envt_store_extend: forall M M' H1 H2 G u,
    env_type M H1 H2 u G ->
    st_chain M M' u ->
    env_type M' H1 H2 u G.
Proof.
  intros. eapply envt_store_extend'; eauto.
Qed.

Lemma valt_eff: forall M vx1 vx2 T (u u': Prop),
    val_type M vx1 vx2 u T -> (u' -> u) ->
    val_type M vx1 vx2 u' T.
Proof. 
  intros. eapply valt_store_extend'; eauto. eapply stchain_refl. 
Qed.

Lemma envt_eff: forall M H1 H2 G (u u': Prop),
    env_type M H1 H2 u G -> (u' -> u) ->
    env_type M H1 H2 u' G.
Proof.
  intros. eapply envt_store_extend'; eauto. eapply stchain_refl. 
Qed.


(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_sub_eff: forall G t1 t2 T,
    sem_type G t1 t2 False T ->
    sem_type G t1 t2 True T.
Proof.
  intros. intros S1 S2 M H1 H2 u WFE ST.
  eapply envt_store_extend' with (u':=u \/ False) in WFE as WFE1.
  2: eapply stchain_refl. 
  2: eauto. 
  destruct (H S1 S2 M H1 H2 u WFE1 ST) as (S1' & S2' & M' & vx1 & vx2 & SC & TX1 & TX2 & ST' & VX).
  
  exists S1', S2', M', vx1, vx2.
  split. 2: split. 3: split. 4: split. 
  - eauto.
  - eauto. 
  - eauto.
  - eauto. 
  - eauto. 
Qed.

Lemma sem_true: forall G,
    sem_type G ttrue ttrue False TBool.
Proof.
  intros. intros S1 S2 M H1 H2 u WFE ST.
  exists S1, S2, M, (vbool true), (vbool true).
  split. 2: split. 3: split. 4: split. 
  - eapply stchain_refl. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto. 
  - simpl. eauto. 
Qed.

Lemma sem_false: forall G,
    sem_type G tfalse tfalse False TBool.
Proof.
  intros. intros S1 S2 M H1 H2 u WFE ST.
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
    sem_type G (tvar x) (tvar x) False T.
Proof.
  intros. intros S1 S2 M H1 H2 u WFE ST.
  eapply WFE in H as IX. destruct IX as (v1 & v2 & IX1 & IX2 & VX).
  exists S1, S2, M, v1, v2.
  split. 2: split. 3: split. 4: split. 
  - eapply stchain_refl. 
  - exists 0. intros. destruct n. lia. simpl. rewrite IX1. eauto.
  - exists 0. intros. destruct n. lia. simpl. rewrite IX2. eauto.
  - eauto.
  - eapply valt_store_extend'. eauto. eapply stchain_refl; eauto. eauto. 
Qed.

(* tref looks pure! *)
Lemma sem_ref: forall G t1 t2 e1,
    sem_type G t1 t2 e1 TBool ->
    sem_type G (tref t1) (tref t2) e1 TRef.
Proof.
  intros. intros S1 S2 M H1 H2 u WFE ST.
  destruct (H S1 S2 M H1 H2 u WFE ST) as (S1' & S2' & M' & vx1 & vx2 & SC & TX1 & TX2 & ST' & VX).
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

(* tget effectful *)
Lemma sem_get: forall G t1 t2 e1,
    sem_type G t1 t2 e1 TRef ->
    sem_type G (tget t1) (tget t2) True TBool.
Proof.
  intros. intros S1 S2 M H1 H2 u WFE ST.
  eapply envt_eff with (u':=True\/e1) in WFE as WFE1; eauto. 
  destruct (H S1 S2 M H1 H2 _ WFE1 ST) as (S1' & S2' & M' & vx1 & vx2 & SC & TX1 & TX2 & ST' & VX).
  destruct vx1, vx2; simpl in VX; intuition. rename H0 into VX.
  destruct ST' as (L1 & L2 & L3).
  destruct (L1 _ _ VX) as (b & IX1 & IX2).
  exists S1', S2', M', (vbool b), (vbool b).
  split. 2: split. 3: split. 4: split. 
  - eapply stchain_eff. eauto. eauto. 
  - destruct TX1 as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. rewrite IX1. eauto. lia.
  - destruct TX2 as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. rewrite IX2. eauto. lia.
  - repeat split; eauto. 
  - simpl. eauto. 
Qed.

Lemma sem_put: forall G t1 t2 t1' t2' e1 e2,
    sem_type G t1 t2 e1 TRef ->
    sem_type G t1' t2' e2 TBool ->
    sem_type G (tput t1 t1') (tput t2 t2') True TBool.
Proof.
  intros. intros S1 S2 M E1 E2 u WFE ST.
  eapply envt_eff with (u':=True\/e1) in WFE as WFE1; eauto. 
  destruct (H S1 S2 M E1 E2 _ WFE1 ST) as (S1' & S2' & M' & vx1 & vx2 & SC & TX1 & TX2 & ST' & VX).
  eapply envt_store_extend' with (u':=True\/e2) in WFE as WFE'.
  2: { eapply stchain_eff; eauto. }
  2: { eauto. }
  destruct (H0 S1' S2' M' E1 E2 _ WFE' ST') as (S1'' & S2'' & M'' & vy1 & vy2 & SC' & TY1 & TY2 & ST'' & VY).
  eapply valt_store_extend in VX. 2: eauto. 
  destruct vx1, vx2; simpl in VX; intuition. rename H1 into VX.
  destruct vy1, vy2; simpl in VY; intuition.
  destruct ST'' as (L1 & L2 & L3).
  destruct (L1 _ _ VX) as (b1 & IX1 & IX2). 
  exists (update S1'' i (vbool b)), (update S2'' i0 (vbool b0)), M'', (vbool true), (vbool true).
  split. 2: split. 3: split. 4: split. 
  - eapply stchain_chain; eapply stchain_eff; eauto. 
  - destruct TX1 as (n1 & TX).
    destruct TY1 as (n2 & TY).
    exists (1+n1+n2). intros. destruct n. lia. simpl. rewrite TX, TY, IX1. eauto. lia. lia. 
  - destruct TX2 as (n1 & TX).
    destruct TY2 as (n2 & TY).
    exists (1+n1+n2). intros. destruct n. lia. simpl. rewrite TX, TY, IX2. eauto. lia. lia. 
  - eapply storet_update; eauto. repeat split; eauto. 
  - simpl. eauto.
    Unshelve.
    apply True.
Qed.

Lemma sem_app: forall G f1 f2 t1 t2 T1 T2 e1 e2 e3,
    sem_type G f1 f2 e1 (TFun T1 T2 e3) ->
    sem_type G t1 t2 e2 T1 ->
    sem_type G (tapp f1 t1) (tapp f2 t2) (e1 \/ e2 \/ e3) T2.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? HF HX. intros S1 S2 M E1 E2 u WFE ST.
  edestruct (HF S1 S2 M E1 E2) as (S1' & S2' & M' & vf1 & vf2 & SC & TF1 & TF2 & ST' & VF).
  eapply envt_eff. eapply WFE. intuition. eauto. eauto. 
  edestruct (HX S1' S2' M' E1 E2) as (S1'' & S2'' & M'' & vx1 & vx2 & SC' & TX1 & TX2 & ST'' & VX).
  eapply envt_eff. eapply envt_store_extend. eauto. eauto. intuition. eauto. eauto. 
  destruct vf1, vf2; simpl in VF; intuition.
  edestruct VF as (S1''' & S2''' & M'''& vy1 & vy2 & SC'' & TY1 & TY2 & ST''' & VY).
  intuition. eauto. eapply stchain_eff. eauto. intuition. eauto.
  eapply valt_eff. eauto. intuition. 
  exists S1''', S2''', M''', vy1, vy2.
  split. 2: split. 3: split. 4: split. 
  - eapply stchain_eff. eapply stchain_chain'. eauto. eapply stchain_chain'; eauto. intuition.
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
  - eapply valt_eff. eauto. intuition. 
Qed.

Lemma sem_abs: forall G t1 t2 T1 T2 e2,
    sem_type (T1::G) t1 t2 e2 T2 ->
    sem_type G (tabs t1) (tabs t2) False (TFun T1 T2 e2).
Proof.
  intros ? ? ? ? ? ? HY. intros S1 S2 M E1 E2 u WFE ST.
  assert (length E1 = length G) as L1. eapply WFE.
  assert (length E2 = length G) as L2. eapply WFE.
  exists S1, S2, M, (vabs E1 t1), (vabs E2 t2).
  split. 2: split. 3: split. 4: split. 
  - eapply stchain_refl. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto. 
  - simpl. intros.
    edestruct (HY). eapply envt_extend. 
    eapply envt_store_extend'. eapply envt_eff. eauto. 2: eauto. 2: eapply H. eauto.
    eauto. eauto. eauto. 
Qed.


                                                       
(* ---------- LR fundamental property  ---------- *)

Theorem fundamental: forall G t T e,
    has_type G t T e ->
    sem_type G t t e T.
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
  exp_type [] [] st_empty [] [] t t True T.
Proof. 
  intros. eapply fundamental in H as ST; eauto.
  destruct (ST [] [] st_empty [] [] True) as (S1' & S2' & M' & v1 & v2 & ? & ? & ? & ? & ?).
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

Inductive ctx_type : (tm -> tm) -> tenv -> ty -> Prop -> tenv -> ty -> Prop -> Prop :=
| c_top: forall G T e,
    ctx_type (fun x => x) G T e G T e
| c_app1: forall t2 G T1 T2 e1 e2 e3,
    has_type G t2 T1 e2 ->
    ctx_type (fun x => tapp x t2) G (TFun T1 T2 e3) e1 G T2 (e1 \/ e2 \/ e3)
| c_app2: forall t1 G T1 T2 e1 e2 e3,
    has_type G t1 (TFun T1 T2 e3) e1 ->
    ctx_type (fun x => tapp t1 x) G T1 e2 G T2 (e1 \/ e2 \/ e3)
| c_abs: forall G T1 T2 e2,
    ctx_type (fun x => tabs x) (T1::G) T2 e2 G (TFun T1 T2 e2) False.
(* TODO: positions in ref, get, filter, ... *)


(* semantic equivalence between contexts *)
Definition sem_ctx_type C C' G1 T1 e1 G2 T2 e2 :=
  forall t t',
    sem_type G1 t t' e1 T1 ->
    sem_type G2 (C t) (C' t') e2 T2.

(* congruence *)
Theorem congr:
  forall C G1 T1 e1 G2 T2 e2,
    ctx_type C G1 T1 e1 G2 T2 e2 ->
    sem_ctx_type C C G1 T1 e1 G2 T2 e2.
Proof.
  intros ? ? ? ? ? ? ? CX.
  induction CX; intros ? ? ?.
  - eauto.
  - eapply sem_app. eauto. eapply fundamental. eauto.
  - eapply sem_app. eapply fundamental. eauto. eauto.
  - eapply sem_abs. eauto.
Qed.


Lemma adequacy: forall t t' e,
  sem_type [] t t' e TBool ->
  exists S S' v,
    tevaln [] [] t S v /\
    tevaln [] [] t' S' v.
Proof.
  intros. 
  assert (env_type st_empty [] [] True []) as WFE. { unfold env_type; intuition. inversion H0. }
  unfold sem_type in H. specialize (H [] [] st_empty [] [] True). 
  destruct H as (? & ? & ? & ? & ? & ?).
  eapply envt_eff. eauto. intuition. 
  eapply storet_empty. 
  intuition. destruct x2, x3; inversion H4. subst b0.
  eexists _,_,_. split; eauto. 
Qed.

(* contextual equivalence: no boolean context can detect a difference *)
Definition contextual_equiv G t1 t2 T1 e1 :=
  forall C,
    ctx_type C G T1 e1 [] TBool True ->
    exists S1 S2 v,
      tevaln [] [] (C t1) S1 v /\
      tevaln [] [] (C t2) S2 v.

(* soundness of binary logical relation: implies contextual equivalence *)
Theorem soundess: forall G t1 t2 T e,
  sem_type G t1 t2 e T ->
  contextual_equiv G t1 t2 T e.
Proof.
  intros. intros ? ?.
  eapply adequacy.
  eapply congr; eauto. 
Qed.


(* ---------- LR effect interpretation  ---------- *)

(* store invariance:
   - every pure expression can be evaluated in empty stores
     (in fact arbitrary S1, S2), to equivalent values.
   - caveat: the evaluation result will not be "useable"
     for effects (since no store access)
 *)

Theorem store_invariance : forall t G T
  (W: sem_type G t t False T),
  forall H1 H2 M,
    env_type M H1 H2 False G ->
  exp_type [] [] st_empty H1 H2 t t False T.
Proof.
  intros.
  edestruct (W [] [] st_empty H1 H2 False).
  eapply envt_store_extend. 
  eapply envt_eff. eauto. intuition. intros ?. intuition. 
  eapply storet_empty. 
  destruct H0 as (? & ? & ? & ? & ? & ? & ? & ? & ?).
  eexists _,_,_,_,_. intuition eauto. 
Qed.


(* NOTE: a number of programs can be given a semantically pure type,
   even if this isn't justified by the static typing rules. Example: *)
Lemma pure_typing_ex1 : forall G,
  sem_type G (tget (tref ttrue)) (tget (tref ttrue)) False TBool.
Proof.
  intros. intros ? ? ? ? ? ? WFE ST.
  eexists _,_,M,_,_. intuition.
  - intros ?. intuition.
  - exists 3. intros. destruct n. lia. destruct n. lia. destruct n. lia. simpl.
    bdestruct (length S1 =? length S1). eauto. lia. 
  - exists 3. intros. destruct n. lia. destruct n. lia. destruct n. lia. simpl.
    bdestruct (length S2 =? length S2). eauto. lia. 
  - destruct ST as (? & ? & ?). 
    split. 2: split.
    + intros. edestruct H as (? & ? & ?). eauto.
      exists x. rewrite indexr_skip. 2: { eapply indexr_var_some' in H5. lia. }.
      rewrite indexr_skip. 2: { eapply indexr_var_some' in H6. lia. }.
      intuition.
    + intuition.
    + intuition. 
  - simpl. eauto.
Qed.
  



End STLC.
