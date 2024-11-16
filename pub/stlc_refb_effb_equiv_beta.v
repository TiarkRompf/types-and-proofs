(* Full safety for STLC *)

(*

An LR-based termination and semantic soundness proof for STLC.

Add first-order mutable references (restricted to TBool)

Binary logical relation with contextual equivalence.

Add simple yes/no effect tracking, prove store invariance.

Prove beta equivalence for pure function arguments.

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
    has_type env (tref t) TRef true
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
| t_sub_eff: forall env t T e,
    has_type env t T e ->
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

(* value interpretation of terms *)
Definition tevaln M env e M' v :=
  exists nm,
  forall n,
    n > nm ->
    teval n M env e = (M', Some (Some v)).


(* ---------- LR definitions  ---------- *)

Definition stty: Type := (nat * nat * (nat -> nat -> Prop)). (* partial bijection *)

Definition strel (M: stty) := snd M.

Definition st_len1 (M: stty) := fst (fst M).
Definition st_len2 (M: stty) := snd (fst M).


Definition st_empty: stty := (0, 0, (fun i j => False)).

Definition st_extend' L1 L2 (M: stty): stty := (S L1, S L2, 
  fun l1 l2 =>
    (l1 = L1 /\ l2 = L2) \/
      (l1 < L1 /\ l2 < L2 /\ strel M l1 l2)).

Definition st_extend (M: stty): stty :=
  st_extend' (st_len1 M) (st_len2 M) M.


Definition st_pad L1 L2 (M: stty): stty :=
  (L1 + (st_len1 M), L2 + (st_len2 M), (strel M)).



Definition stty_wellformed (M: stty) :=
  (forall l1 l2,
      strel M l1 l2 ->
      l1 < st_len1 M /\
      l2 < st_len2 M) /\
  (* enforce that strel is a partial bijection *)
  (forall l1 l2 l2',
      strel M l1 l2 ->
      strel M l1 l2' ->
      l2 = l2') /\
  (forall l1 l1' l2,
      strel M l1 l2 ->
      strel M l1' l2 ->
      l1 = l1').

Definition store_type (S1 S2: stor) (M: stty) :=
  length S1 = st_len1 M /\
  length S2 = st_len2 M /\
  (forall l1 l2,
      strel M l1 l2 ->
      exists b,
        indexr l1 S1 = Some (vbool b) /\
        indexr l2 S2 = Some (vbool b)).

    
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
  | vabs H1 ty1, vabs H2 ty2, TFun T1 T2 false => (* pure *)
      forall M' vx1 vx2,
        st_chain M M' ->
        val_type M' vx1 vx2 T1 ->
        exists vy1 vy2 SD1 SD2,
          (forall S1', tevaln S1' (vx1::H1) ty1 (SD1++S1') vy1) /\
          (forall S2', tevaln S2' (vx2::H2) ty2 (SD2++S2') vy2) /\
          val_type M' vy1 vy2 T2
  | vabs H1 ty1, vabs H2 ty2, TFun T1 T2 true => (* latent effect *)
      forall S1' S2' M' vx1 vx2,
        st_chain M M' ->
        stty_wellformed M' ->
        store_type S1' S2' M' ->
        val_type M' vx1 vx2 T1 ->
        exists S1'' S2'' M'' vy1 vy2,
          st_chain M' M'' /\
          stty_wellformed M'' /\
          tevaln S1' (vx1::H1) ty1 S1'' vy1 /\
          tevaln S2' (vx2::H2) ty2 S2'' vy2 /\
          store_type S1'' S2'' M'' /\
          val_type M'' vy1 vy2 T2
  | _,_,_ =>
      False
  end.




Definition exp_type_pure_xxx M H1 H2 t1 t2 T :=
  exists v1 v2,
    forall S1 S2, exists S1' S2', (* goal: <-- supoort allocation *)
      tevaln S1 H1 t1 S1' v1 /\
      tevaln S2 H2 t2 S2' v2 /\
      val_type M v1 v2 T.


Definition exp_type_pure M H1 H2 t1 t2 T :=
  exists v1 v2 SD1 SD2,
    (forall S1, tevaln S1 H1 t1 (SD1++S1) v1) /\ (* xx: support store extension *)
    (forall S2, tevaln S2 H2 t2 (SD2++S2) v2) /\
    val_type M v1 v2 T.


Definition exp_type1 S1 S2 M H1 H2 t1 t2 S1' S2' M' T :=
    exists v1 v2,
      st_chain M M' /\
      stty_wellformed M' /\
        tevaln S1 H1 t1 S1' v1 /\
        tevaln S2 H2 t2 S2' v2 /\
        store_type S1' S2' M' /\
        val_type M' v1 v2 T.

Definition exp_type S1 S2 M H1 H2 t1 t2 T :=
  exists S1' S2' M',
    exp_type1 S1 S2 M H1 H2 t1 t2 S1' S2' M' T.

Definition env_type M (H1 H2: venv) (G: tenv) :=
  length H1 = length G /\
  length H2 = length G /\
    forall x T,
      indexr x G = Some T ->
      exists v1 v2,
        indexr x H1 = Some v1 /\
        indexr x H2 = Some v2 /\
        val_type M v1 v2 T.


Definition sem_type_pure G t1 t2 T :=
  forall M H1 H2,
    env_type M H1 H2 G ->
    exp_type_pure M H1 H2 t1 t2 T.


Definition sem_type_impure G t1 t2 T :=
  forall M H1 H2,
    env_type M H1 H2 G ->
    stty_wellformed M ->
    forall S1 S2,
      store_type S1 S2 M ->
      exp_type S1 S2 M H1 H2 t1 t2 T.


Definition exp_type_impure M H1 H2 t1 t2 T :=
  stty_wellformed M ->
  forall S1 S2,
    store_type S1 S2 M ->
    exp_type S1 S2 M H1 H2 t1 t2 T.


Definition exp_type_eff M H1 H2 t1 t2 T e :=
    exp_type_impure M H1 H2 t1 t2 T /\
    (e = false -> exp_type_pure M H1 H2 t1 t2 T).


Definition sem_type_eff G t1 t2 T e :=
  forall M H1 H2,
    env_type M H1 H2 G ->
    exp_type_eff M H1 H2 t1 t2 T e.
    


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

Lemma stchain_extend: forall M,
    stty_wellformed M ->
    st_chain M (st_extend M).
Proof.
  intros.
  unfold st_chain, st_extend. intros U. intros. unfold strel at 1.
  right. destruct H as (L1 & L2 & L3). 
  edestruct L1 as (? & ?). eauto. intuition. 
Qed.

Lemma stchain_pad: forall L1 L2 M,
    st_chain M (st_pad L1 L2 M).
Proof.
  intros.
  unfold st_chain, st_pad. intros. unfold strel at 1.
  simpl. eauto. 
Qed.

Lemma stchain_pad': forall L1 L2 M,
    st_chain (st_pad L1 L2 M) M.
Proof.
  intros.
  unfold st_chain, st_pad. intros. unfold strel at 1.
  simpl. eauto. 
Qed.


Lemma stchain_chain': forall M1 M2 M3,
    st_chain M1 M2 ->
    st_chain M2 M3 ->
    st_chain M1 M3.
Proof.
  intros. unfold st_chain in *. 
  intuition. 
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


Lemma sttyw_empty:
    stty_wellformed st_empty.
Proof.
  intros. split. 2: split.
  - intros. inversion H.
  - intros. inversion H.
  - intros. inversion H. 
Qed.

Lemma storet_empty: 
    store_type [] [] st_empty .
Proof.
  intros. split. 2: split.
  - eauto.
  - eauto.
  - intros. inversion H. 
Qed.

Lemma sttyw_extend: forall M,
    stty_wellformed M ->
    stty_wellformed (st_extend M).
Proof.
  intros. destruct H as (L1 & L2 & L3).
  split. 2: split. 
  - intros. unfold st_len1, st_len2, st_extend, st_extend'. simpl. destruct H; lia. 
  - intros. destruct H, H0; intuition. eapply L2; eauto.
  - intros. destruct H, H0; intuition. eapply L3; eauto. 
Qed.

Lemma storet_extend: forall S1 S2 M vx1 vx2,
    store_type S1 S2 M ->
    val_type M vx1 vx2 TBool ->
    store_type (vx1 :: S1) (vx2 :: S2) (st_extend M).
Proof.
  intros. destruct H as (L1 & L2 & L3).
  split. 2: split.
  - simpl. rewrite L1. unfold st_len1, st_extend, st_extend'. eauto.
  - simpl. rewrite L2. unfold st_len2, st_extend, st_extend'. eauto. 
  - intros. destruct vx1, vx2; inversion H0.
      subst b0. simpl in H. destruct H.
    + exists b. destruct H. subst l1 l2.
      rewrite <-L1, <-L2, indexr_head, indexr_head; eauto.
    + edestruct L3 as (? & ? & ?). eauto. eapply H. 
      exists x. rewrite indexr_skip, indexr_skip; intuition. 
Qed.

Lemma sttyw_pad: forall L1 L2 M,
    stty_wellformed M ->
    stty_wellformed (st_pad L1 L2 M).
Proof.
  intros. destruct H as (F1 & F2 & F3).
  split. 2: split. 
  - intros. unfold st_pad, st_len1, st_len2, st_pad, strel in *. simpl in *.
    edestruct F1. eauto. split; lia. 
  - intros. eapply F2; eauto.
  - intros. eapply F3; eauto. 
Qed.

Lemma storet_pad: forall SD1 SD2 S1 S2 M,
    store_type S1 S2 M ->
    store_type (SD1++S1) (SD2++S2) (st_pad (length SD1) (length SD2) M).
Proof.
  intros. destruct H as (F1 & F2 & F3).
  split. 2: split.
  - rewrite app_length. unfold st_pad, st_len1, st_len2 in *. simpl. lia.
  - rewrite app_length. unfold st_pad, st_len1, st_len2 in *. simpl. lia. 
  - intros. simpl in *. eapply F3 in H. destruct H as (b & IX1 & IX2).
    exists b. rewrite indexr_skips. rewrite indexr_skips. intuition.
    eapply indexr_var_some' in IX2. eauto.
    eapply indexr_var_some' in IX1. eauto. 
Qed.




Lemma storet_update: forall S1 S2 M l1 l2 vx1 vx2,
    stty_wellformed M ->
    store_type S1 S2 M ->
    strel M l1 l2 ->
    val_type M vx1 vx2 TBool ->
    store_type (update S1 l1 vx1) (update S2 l2 vx2) M.
Proof.
  intros.
  destruct H as (F1 & F2 & F3 ).
  destruct H0 as (L1 & L2 & L3 ).
  destruct vx1, vx2; inversion H2.
  split. 2: split.
  - rewrite <-update_length. eauto.
  - rewrite <-update_length. eauto. 
  - intros. bdestruct (l0 =? l1); bdestruct (l3 =? l2).
    + subst l0 l3. eexists. rewrite update_indexr_hit, update_indexr_hit; intuition.
      eapply F1 in H0. rewrite L2. eapply H0.
      eapply F1 in H0. rewrite L1. eapply H0. 
      (* edestruct H3 as (? & ? & ?). eauto. eauto. eapply indexr_var_some'. eauto.
      edestruct H4 as (? & ? & ?). eauto. eapply indexr_var_some'. eauto. *)
    + subst l0. destruct H4. eapply F2; eauto.
    + subst l3. destruct H3. eapply F3; eauto.
    + rewrite update_indexr_miss, update_indexr_miss; eauto.
Qed.


Lemma valt_store_extend': forall M M' vx1 vx2 T,
    val_type M vx1 vx2 T ->
    st_chain M M' ->
    val_type M' vx1 vx2 T.
Proof.
  intros. destruct vx1, vx2, T; simpl in H; try contradiction.
  - simpl. eauto.
  - simpl. intuition. 
  - destruct b.
    + simpl. intros. destruct (H S1' S2' M'0 vx1 vx2); eauto.
      eapply stchain_chain'. eapply H0. eapply H1. 
    + simpl. intros. destruct (H M'0 vx1 vx2); eauto.
      eapply stchain_chain'. eapply H0. eapply H1. 
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
    eauto. eauto. eapply valt_store_extend'; eauto.
Qed.

Lemma valt_store_extend: forall M M' vx1 vx2 T,
    val_type M vx1 vx2 T ->
    st_chain M M' -> 
    val_type M' vx1 vx2 T.
Proof. 
  intros. eapply valt_store_extend'; eauto.
Qed.

(* ---------- LR compatibility lemmas  ---------- *)

Lemma exp_sub_eff: forall M H1 H2 t1 t2 T,
    exp_type_pure M H1 H2 t1 t2 T ->
    stty_wellformed M ->
    forall S1 S2,
      store_type S1 S2 M -> 
      exp_type S1 S2 M H1 H2 t1 t2 T.
Proof.
  intros. destruct H as (v1 & v2 & SD1 & SD2 & ? & ? & ?).
  exists (SD1++S1), (SD2++S2), (st_pad (length SD1) (length SD2) M), v1, v2.
  split. 2: split. 3: split. 4: split. 5: split.
  - eapply stchain_pad. 
  - eapply sttyw_pad. eauto. 
  - eauto. 
  - eauto.
  - eapply storet_pad. eauto. 
  - eapply valt_store_extend. eauto.
    eapply stchain_pad. 
Qed.


Lemma exp_true: forall M H1 H2,
    exp_type_pure M H1 H2 ttrue ttrue TBool.
Proof.
  intros. 
  exists (vbool true), (vbool true), [], [].
  split. 2: split. 3: split. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
Qed.

Lemma exp_false: forall M H1 H2,
    exp_type_pure M H1 H2 tfalse tfalse TBool.
Proof.
  intros. 
  exists (vbool false), (vbool false), [], [].
  split. 2: split. 3: split. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
Qed.

Lemma exp_var: forall M H1 H2 x1 x2 v1 v2 T,
    indexr x1 H1 = Some v1 ->
    indexr x2 H2 = Some v2 ->
    val_type M v1 v2 T ->
    exp_type_pure M H1 H2 (tvar x1) (tvar x2) T.
Proof.
  intros ???????? IX1 IX2 VX. 
  exists v1, v2, [], [].
  split. 2: split.
  - exists 0. intros. destruct n. lia. simpl. rewrite IX1. eauto.
  - exists 0. intros. destruct n. lia. simpl. rewrite IX2. eauto.
  - eauto.
Qed.

Lemma exp_ref: forall S1 S2 M H1 H2 t1 t2,
    exp_type S1 S2 M H1 H2 t1 t2 TBool ->
    exp_type S1 S2 M H1 H2 (tref t1) (tref t2) TRef.
Proof.
  intros ??????? HX. 
  destruct HX as (S1' & S2' & M' & vx1 & vx2 & SC' & SW' & TX1 & TX2 & ST' & VX).
  exists (vx1::S1'), (vx2::S2'), (st_extend M'), (vref (length S1')), (vref (length S2')).
  split. 2: split. 3: split. 4: split. 5: split. 
  - eapply stchain_chain; eauto.
    eapply stchain_extend; eauto.
  - eapply sttyw_extend; eauto.
  - destruct TX1 as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. eauto. lia.
  - destruct TX2 as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. eauto. lia.
  - eapply storet_extend. eauto. eauto. 
  - simpl. destruct ST' as (L1 & L2 & L3).
    unfold strel, st_extend in *. simpl. left. intuition. 
Qed.

Lemma exp_get: forall S1 S2 M H1 H2 t1 t2,
    exp_type S1 S2 M H1 H2 t1 t2 TRef ->
    exp_type S1 S2 M H1 H2 (tget t1) (tget t2) TBool.
Proof.
  intros ??????? HX. 
  destruct HX as (S1' & S2' & M' & vx1 & vx2 & SC' & SW' & TX1 & TX2 & ST' & VX).
  destruct vx1, vx2; simpl in VX; intuition. 
  destruct ST' as (L1 & L2 & L3).
  destruct (L3 _ _ VX) as (b & IX1 & IX2).
  exists S1', S2', M', (vbool b), (vbool b).
  split. 2: split. 3: split. 4: split. 5: split. 
  - eauto.
  - eauto. 
  - destruct TX1 as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. rewrite IX1. eauto. lia.
  - destruct TX2 as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. rewrite IX2. eauto. lia.
  - repeat split; eauto. 
  - simpl. eauto. 
Qed.

Lemma exp_put: forall S1 S2 M S1' S2' M' H1 H2 t1 t2 t1' t2',
    exp_type1 S1 S2 M H1 H2 t1 t2 S1' S2' M' TRef ->
    exp_type S1' S2' M' H1 H2 t1' t2' TBool ->
    exp_type S1 S2 M H1 H2 (tput t1 t1') (tput t2 t2') TBool.
Proof.
  intros ???????????? HX HY. 
  destruct HX as (vx1 & vx2 & SC' & SW' & TX1 & TX2 & ST' & VX).
  destruct HY as (S1'' & S2'' & M'' & vy1 & vy2 & SC'' & SW'' & TY1 & TY2 & ST'' & VY).
  eapply valt_store_extend in VX. 2: eauto. 
  destruct vx1, vx2; simpl in VX; intuition. 
  destruct vy1, vy2; simpl in VY; intuition.
  destruct ST'' as (L1 & L2 & L3).
  destruct (L3 _ _ VX) as (b1 & IX1 & IX2). 
  exists (update S1'' i (vbool b)), (update S2'' i0 (vbool b0)), M'', (vbool true), (vbool true).
  split. 2: split. 3: split. 4: split. 5: split. 
  - eapply stchain_chain; eauto.
  - eauto. 
  - destruct TX1 as (n1 & TX).
    destruct TY1 as (n2 & TY).
    exists (1+n1+n2). intros. destruct n. lia. simpl. rewrite TX, TY, IX1. eauto. lia. lia. 
  - destruct TX2 as (n1 & TX).
    destruct TY2 as (n2 & TY).
    exists (1+n1+n2). intros. destruct n. lia. simpl. rewrite TX, TY, IX2. eauto. lia. lia. 
  - eapply storet_update; eauto. repeat split; eauto. 
  - simpl. eauto.
Qed.

Lemma exp_app_pure: forall M H1 H2 f1 f2 t1 t2 T1 T2,
    exp_type_pure M H1 H2 f1 f2 (TFun T1 T2 false) -> 
    exp_type_pure M H1 H2 t1 t2 T1 ->
    exp_type_pure M H1 H2 (tapp f1 t1) (tapp f2 t2) T2.
Proof.
  intros ????????? HF HX. 
  edestruct HF as (vf1 & vf2 & SDF1 & SDF2 & TF1 & TF2 & VF). 
  edestruct HX as (vx1 & vx2 & SDX1 & SDX2 & TX1 & TX2 & VX).
  destruct vf1, vf2; simpl in VF; intuition.
  edestruct (VF M) as (vy1 & vy2 & SDY1 & SDY2 & TY1 & TY2 & VY).
  eapply stchain_refl. eapply VX.
  exists vy1, vy2, (SDY1++SDX1++SDF1), (SDY2++SDX2++SDF2). 
  split. 2: split. (* --- HERE --- *)
  - intros. 
    edestruct TF1 as (n1 & TF).
    edestruct TX1 as (n2 & TX).
    edestruct TY1 as (n3 & TY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite TF, TX, TY. 2,3,4: lia.
    eauto. repeat rewrite app_assoc. eauto. 
  - intros.
    edestruct TF2 as (n1 & TF).
    edestruct TX2 as (n2 & TX).
    edestruct TY2 as (n3 & TY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite TF, TX, TY. 2,3,4: lia.
    eauto. repeat rewrite app_assoc. eauto. 
  - eauto. 
Qed.

Lemma exp_app: forall S1 S2 M S1' S2' M' H1 H2 f1 f2 t1 t2 T1 T2,
    exp_type1 S1 S2 M H1 H2 f1 f2 S1' S2' M' (TFun T1 T2 true) -> 
    exp_type S1' S2' M' H1 H2 t1 t2 T1 ->
    exp_type S1 S2 M H1 H2 (tapp f1 t1) (tapp f2 t2) T2.
Proof.
  intros ?????????????? HF HX. 
  edestruct HF as (vf1 & vf2 & SC' & SW' & TF1 & TF2 & ST' & VF).
  edestruct HX as (S1'' & S2'' & M'' & vx1 & vx2 & SC'' & SW'' & TX1 & TX2 & ST'' & VX).
  destruct vf1, vf2; simpl in VF; intuition.
  edestruct VF as (S1''' & S2''' & M'''& vy1 & vy2 & SC''' & SW''' & TY1 & TY2 & ST''' & VY).
  eauto. eauto. eauto. eauto.
  exists S1''', S2''', M''', vy1, vy2.
  split. 2: split. 3: split. 4: split. 5: split.
  - eapply stchain_chain'. eauto. eapply stchain_chain'; eauto.
  - eauto.
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


Lemma exp_abs_pure: forall M H1 H2 t1 t2 T1 T2,
    (forall M' vx1 vx2,
        st_chain M M' ->
        val_type M' vx1 vx2 T1 ->
        exp_type_pure M' (vx1 :: H1) (vx2 :: H2) t1 t2 T2) ->
    exp_type_pure M H1 H2 (tabs t1) (tabs t2) (TFun T1 T2 false).
Proof.
  intros ??????? HY.
  exists (vabs H1 t1), (vabs H2 t2), [], [].
  split. 2: split. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros.
    eapply HY; eauto. 
Qed.

Lemma exp_abs: forall M H1 H2 t1 t2 T1 T2,
    (forall S1' S2' M' vx1 vx2,
        st_chain M M' ->
        stty_wellformed M' ->
        store_type S1' S2' M' ->
        val_type M' vx1 vx2 T1 ->
        exp_type S1' S2' M' (vx1 :: H1) (vx2 :: H2) t1 t2 T2) ->
    exp_type_pure M H1 H2 (tabs t1) (tabs t2) (TFun T1 T2 true).
Proof.
  intros ??????? HY.
  exists (vabs H1 t1), (vabs H2 t2), [], [].
  split. 2: split. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros.
    eapply HY; eauto. 
Qed.


Lemma exp_sub_fun_eff1: forall S1 S2 M S1' S2' M' H1 H2 t1 t2 T1 T2 e,
    exp_type1 S1 S2 M H1 H2 t1 t2 S1' S2' M' (TFun T1 T2 e) ->
    exp_type1 S1 S2 M H1 H2 t1 t2 S1' S2' M' (TFun T1 T2 true).
Proof.
  intros. destruct H as (v1 & v2 & ? & ? & ? & ? & ? & ?).
  exists v1, v2. split. 2: split. 3: split. 4: split. 5: split.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - destruct v1, v2, e; simpl; try contradiction; intuition. 
    eapply exp_sub_eff; eauto. simpl in H6. eapply H6. eauto. eauto.
Qed.

Lemma exp_sub_fun_eff: forall S1 S2 M H1 H2 t1 t2 T1 T2 e,
    exp_type S1 S2 M H1 H2 t1 t2 (TFun T1 T2 e) ->
    exp_type S1 S2 M H1 H2 t1 t2 (TFun T1 T2 true).
Proof.
  intros. destruct H as (S1' & S2' & M' & v1 & v2 & ? & ? & ? & ? & ? & ?).
  exists S1', S2', M', v1, v2. split. 2: split. 3: split. 4: split. 5: split.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - destruct v1, v2, e; simpl; try contradiction; intuition. 
    eapply exp_sub_eff; eauto. simpl in H6. eapply H6. eauto. eauto.
Qed.




Theorem fundamental: forall G t T e,
    has_type G t T e ->
    sem_type_eff G t t T e.
Proof.
  intros ? ? ? ? W. 
  induction W; intros ??? WFE; split.  
  - intros SW ?? ST. eapply exp_sub_eff; eauto. eapply exp_true; eauto.
  - intros. eapply exp_true; eauto.
  - intros SW ?? ST. eapply exp_sub_eff; eauto. eapply exp_false; eauto.
  - intros. eapply exp_false; eauto.
  - intros SW ?? ST. eapply WFE in H. destruct H as (v1 & v2 & IX1 & IX2 & VX).
    eapply exp_sub_eff; eauto. eapply exp_var; eauto.
  - intros. eapply WFE in H. destruct H as (v1 & v2 & IX1 & IX2 & VX).
    eapply exp_var; eauto.
  - intros SW ?? ST. eapply exp_ref; eauto. eapply IHW; eauto.
  - intros. inversion H. 
  - intros SW ?? ST. eapply exp_get; eauto.  eapply IHW; eauto.
  - intros. inversion H.
  - intros SW ?? ST. edestruct IHW1 as ((S1' & S2' & M' & ?) & ?); eauto. 
    eapply exp_put; eauto.
    destruct H as (? & ? & ? & ? & ? & ? & ? & ?).
    eapply IHW2; eauto. eapply envt_store_extend; eauto.
  - intros. inversion H.
  - intros SW ?? ST. destruct (IHW1 M H1 H2 WFE). specialize (H SW S1 S2 ST). 
    assert (exp_type S1 S2 M H1 H2 f f (TFun T1 T2 true)). {
      destruct e3. eauto. eapply exp_sub_fun_eff. eauto. }    
    destruct H3 as (S1' & S2' & M' & ?).
    eapply exp_app. eauto.  
    destruct H3 as (? & ? & ? & ? & ? & ? & ? & ?).
    eapply IHW2; eauto. eapply envt_store_extend; eauto.
  - intros. assert (e1 = false /\ e2 = false /\ e3 = false) as E. destruct e1,e2,e3; intuition.
    destruct E as (E1 & E2 & E3). subst e1 e2 e3. clear H.
    destruct (IHW1 M H1 H2) as (IHW11 & IHW12). eauto.
    destruct (IHW2 M H1 H2) as (IHW21 & IHW22). eauto.
    eapply exp_app_pure; eauto.
  - intros SW ?? ST. eapply exp_sub_eff; eauto. destruct e.
    + eapply exp_abs; eauto. intros.
      eapply IHW. eapply envt_extend. eapply envt_store_extend.
      eauto. eauto. eauto. eauto. eauto.
    + eapply exp_abs_pure; eauto. intros.
      eapply IHW. eapply envt_extend. eapply envt_store_extend.
      eauto. eauto. eauto. eauto.
  - intros. destruct e.
    + eapply exp_abs; eauto. intros.
      eapply IHW. eapply envt_extend. eapply envt_store_extend.
      eauto. eauto. eauto. eauto. eauto.
    + eapply exp_abs_pure; eauto. intros.
      eapply IHW. eapply envt_extend. eapply envt_store_extend.
      eauto. eauto. eauto. eauto.
  - eapply IHW; eauto.
  - intros. inversion H. 
Qed.


                                                       
(* ---------- LR fundamental property  ---------- *)

(*
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
Qed.*)

Corollary safety: forall t T e,
  has_type [] t T e ->
  exp_type [] [] st_empty [] [] t t T.
Proof. 
  intros. eapply fundamental in H as ST; eauto.
  edestruct ST as (ST1 & ST2).
  eapply envt_empty.
  edestruct (ST1) as (S1' & S2' & M' & v1 & v2 & ? & ? & ? & ? & ?).
  eapply sttyw_empty.
  eapply storet_empty.
  exists S1', S2', M', v1, v2. intuition.
Qed.

Corollary safety_pure: forall t T,
  has_type [] t T false ->
  exp_type_pure st_empty [] [] t t T.
Proof. 
  intros. eapply fundamental in H as ST; eauto.
  edestruct ST as (ST1 & ST2).
  eapply envt_empty.
  edestruct (ST2) as (v1 & v2 & SD1 & SD2 & ?). eauto.
  exists v1, v2, SD1, SD2. intuition.
Qed.



(* ---------- LR contextual equivalence  ---------- *)

(* Define typed contexts and prove that the binary logical
   relation implies contextual equivalence (congruency wrt
   putting expressions in context *)

(* Q: Do we need to prove a theorem that these are all
   possible contexts? Do we need to consider only one-hole
   contexts or also (fun x => tapp x x)? *)

Inductive ctx_type : (tm -> tm) -> tenv -> ty -> bool -> tenv -> ty -> bool -> Prop :=
| c_top: forall G T e,
    ctx_type (fun x => x) G T e G T e
| c_app1: forall t2 G T1 T2 e1 e2 e3,
    has_type G t2 T1 e2 ->
    ctx_type (fun x => tapp x t2) G (TFun T1 T2 e3) e1 G T2 (e1 || e2 || e3)
| c_app2: forall t1 G T1 T2 e1 e2 e3,
    has_type G t1 (TFun T1 T2 e3) e1 ->
    ctx_type (fun x => tapp t1 x) G T1 e2 G T2 (e1 || e2 || e3)
| c_abs: forall G T1 T2 e2,
    ctx_type (fun x => tabs x) (T1::G) T2 e2 G (TFun T1 T2 e2) false.
(* TODO: positions in ref, get, filter, ... *)


(* semantic equivalence between contexts *)
Definition sem_ctx_type C C' G1 T1 e1 G2 T2 e2 :=
  forall t t',
    sem_type_eff G1 t t' T1 e1 ->
    sem_type_eff G2 (C t) (C' t') T2 e2.

(* congruence *)
Theorem congr:
  forall C G1 T1 e1 G2 T2 e2,
    ctx_type C G1 T1 e1 G2 T2 e2 ->
    sem_ctx_type C C G1 T1 e1 G2 T2 e2.
Proof.
  intros ? ? ? ? ? ? ? CX.
  induction CX; intros ? ? ?.
  - eauto.
  - intros ? ? ? WFE. edestruct H0; eauto. split.
    + intros SW ?? ST.
      destruct (H3 SW S1 S2 ST) as (S1' & S2' & M' & ?).
      assert (exp_type1 S1 S2 M H1 H2 t t' S1' S2' M' (TFun T1 T2 true)). {
        destruct e3. eauto. eapply exp_sub_fun_eff1. eauto. }
      eapply exp_app. eauto.
      destruct H6 as (? & ? & ? & ? & ? & ? & ? & ?).
      eapply fundamental; eauto. eapply envt_store_extend; eauto.
    + intros C.
      assert (e1 = false /\ e2 = false /\ e3 = false). destruct e1,e2,e3; eauto.
      intuition. subst e1 e2 e3. 
      eapply exp_app_pure. eauto. eapply fundamental; eauto.
  - intros ? ? ? WFE. split. 
    + intros SW ?? ST.
      eapply fundamental in H. edestruct H; eauto. 
      destruct (H3 SW S1 S2 ST) as (S1' & S2' & M' & ?).
      assert (exp_type1 S1 S2 M H1 H2 t1 t1 S1' S2' M' (TFun T1 T2 true)). {
        destruct e3. eauto. eapply exp_sub_fun_eff1. eauto. }
      eapply exp_app. eauto.
      destruct H6 as (? & ? & ? & ? & ? & ? & ? & ?).
      edestruct H0. eapply envt_store_extend; eauto. 
      eapply H12; eauto.
    + intros C.
      assert (e1 = false /\ e2 = false /\ e3 = false). destruct e1,e2,e3; eauto.
      intuition. subst e1 e2 e3. 
      eapply exp_app_pure. eapply fundamental; eauto.
      eapply H0; eauto.
  - intros ? ? ? WFE. split.
    + intros SW ?? ST. eapply exp_sub_eff; eauto. destruct e2.
      * eapply exp_abs. intros. edestruct H.
        eapply envt_extend. eapply envt_store_extend.
        eauto. eauto. eauto. eauto.
      * eapply exp_abs_pure. intros. edestruct H.
        eapply envt_extend. eapply envt_store_extend.
        eauto. eauto. eauto. eauto.
    + intros. destruct e2.
      * eapply exp_abs. intros. edestruct H.
        eapply envt_extend. eapply envt_store_extend.
        eauto. eauto. eauto. eauto.
      * eapply exp_abs_pure. intros. edestruct H.
        eapply envt_extend. eapply envt_store_extend.
        eauto. eauto. eauto. eauto.
Qed.
    

Lemma adequacy: forall t t' e,
  sem_type_eff [] t t' TBool e ->
  exists S S' v,
    tevaln [] [] t S v /\
    tevaln [] [] t' S' v.
Proof.
  intros. edestruct H. eapply envt_empty.
  edestruct H0 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
  eapply sttyw_empty. eapply storet_empty.
  destruct x2,x3; simpl in H7; inversion H7. subst b0. 
  eexists. eexists. eexists. split; eauto.
Qed.

(* contextual equivalence: no boolean context can detect a difference *)
Definition contextual_equiv G t1 t2 T1 e1 :=
  forall C,
    ctx_type C G T1 e1 [] TBool true ->
    exists S1 S2 v,
      tevaln [] [] (C t1) S1 v /\
      tevaln [] [] (C t2) S2 v.

(* soundness of binary logical relation: implies contextual equivalence *)
Theorem soundess: forall G t1 t2 T e,
  sem_type_eff G t1 t2 T e ->
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
 *)

Theorem store_invariance : forall t G T
  (W: sem_type_eff G t t T false),
  forall H1 H2 M,
    env_type M H1 H2 G ->
    exists v1 v2 SD1 SD2,
      (forall S1 : stor, tevaln S1 H1 t (SD1 ++ S1) v1) /\
      (forall S2 : stor, tevaln S2 H2 t (SD2 ++ S2) v2) /\
      val_type M v1 v2 T.
Proof.
  intros.
  edestruct (W). eauto. destruct H3 as (? & ? & ? & ? & ?). eauto.
  eexists. eexists. eexists. eexists. eauto. 
Qed.


(* NOTE: a number of programs can be given a semantically pure type,
   even if this isn't justified by the static typing rules. Example: *)
Lemma pure_typing_ex1 : forall G,
  sem_type_pure G (tget (tref ttrue)) (tget (tref ttrue)) TBool.
Proof.
  intros. intros ? ? ? WFE.
  eexists _,_,[vbool true],[vbool true]. intuition.
  - exists 3. intros. destruct n. lia. destruct n. lia. destruct n. lia. simpl.
    bdestruct (length S1 =? length S1). eauto. lia. 
  - exists 3. intros. destruct n. lia. destruct n. lia. destruct n. lia. simpl.
    bdestruct (length S2 =? length S2). eauto. lia. 
  - simpl. eauto. 
Qed.
  


(* ---------- LR beta-equivalence  ---------- *)


Fixpoint splice_tm (t: tm)(i: nat) (n:nat) : tm := 
  match t with 
  | ttrue         => ttrue
  | tfalse        => tfalse
  | tvar x        => tvar (if x <? i then x else x + n)
  | tref t        => tref (splice_tm t i n)
  | tget t        => tget (splice_tm t i n)
  | tput t1 t2    => tput (splice_tm t1 i n) (splice_tm t2 i n)
  | tapp t1 t2    => tapp (splice_tm t1 i n) (splice_tm t2 i n)
  | tabs t        => tabs (splice_tm t i n)
end.

Fixpoint subst_tm (t: tm)(i: nat) (u:tm) : tm := 
  match t with 
  | ttrue         => ttrue
  | tfalse        => tfalse
  | tvar x        => if i =? x then u else if i <? x then (tvar (pred x)) else (tvar x)   
  | tref t        => tref (subst_tm t i u)
  | tget t        => tget (subst_tm t i u)
  | tput t1 t2    => tput (subst_tm t1 i u) (subst_tm t2 i u)
  | tapp t1 t2    => tapp (subst_tm t1 i u) (subst_tm t2 i u)
  | tabs t        => tabs (subst_tm t i (splice_tm u i 1)) 
end.

(* We don't have locally nameless here, just regular DeBruijn levels. This 
   means substitution under binders (i.e. tabs) needs to shift the term by 1 *)


Lemma splice_acc: forall e1 a b c,
  splice_tm (splice_tm e1 a b) a c =
  splice_tm e1 a (c+b).
Proof.
  induction e1; intros; simpl; intuition.
  + bdestruct (i <? a); intuition.  
    bdestruct (i <? a); intuition.
    bdestruct (i + b <? a); intuition.
  + erewrite IHe1. eauto.
  + erewrite IHe1. eauto.
  + erewrite IHe1_1, IHe1_2. eauto.
  + erewrite IHe1_1, IHe1_2. eauto.
  + erewrite IHe1. eauto.
Qed.
  
Lemma splice_zero: forall e1 a,
  (splice_tm e1 a 0) = e1.
Proof.
  intros. induction e1; simpl; intuition.
  + bdestruct (i <? a); intuition.
  + rewrite IHe1. eauto.
  + rewrite IHe1. eauto. 
  + rewrite IHe1_1. rewrite IHe1_2. auto.
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



Lemma st_weaken: forall t1 e T1 G
  (W: has_type G t1 T1 e),
  forall M H1 H2 H2' HX,
    env_type M H1 (H2'++H2) G ->
    exp_type_eff M H1 (H2'++HX++H2) t1 (splice_tm t1 (length H2) (length HX)) T1 e.
Proof.
  intros ? ? ? ? W. 
  induction W; intros ????? WFE; split.  
  - intros SW ?? ST. eapply exp_sub_eff; eauto. eapply exp_true; eauto.
  - intros. eapply exp_true; eauto.
  - intros SW ?? ST. eapply exp_sub_eff; eauto. eapply exp_false; eauto.
  - intros. eapply exp_false; eauto.
  - intros SW ?? ST. eapply WFE in H. destruct H as (v1 & v2 & IX1 & IX2 & VX).
    eapply exp_sub_eff; eauto. eapply exp_var. eauto.
    rewrite indexr_splice. eauto. eauto. 
  - intros. eapply WFE in H. destruct H as (v1 & v2 & IX1 & IX2 & VX).
    eapply exp_var. eauto.
    rewrite indexr_splice. eauto. eauto. 
  - intros SW ?? ST. eapply exp_ref; eauto. eapply IHW; eauto.
  - intros. inversion H. 
  - intros SW ?? ST. eapply exp_get; eauto.  eapply IHW; eauto.
  - intros. inversion H.
  - intros SW ?? ST. edestruct IHW1 as ((S1' & S2' & M' & ?) & ?); eauto. 
    eapply exp_put; eauto.
    destruct H as (? & ? & ? & ? & ? & ? & ? & ?).
    eapply IHW2; eauto. eapply envt_store_extend; eauto.
  - intros. inversion H.
  - intros SW ?? ST. destruct (IHW1 M H1 H2 H2' HX WFE). specialize (H SW S1 S2 ST). 
    assert (exp_type S1 S2 M H1 (H2'++HX++H2) f (splice_tm f (length H2) (length HX)) (TFun T1 T2 true)). {
      destruct e3. eauto. eapply exp_sub_fun_eff. eauto. }
    destruct H3 as (S1' & S2' & M' & ?).
    eapply exp_app. eauto.  
    destruct H3 as (? & ? & ? & ? & ? & ? & ? & ?).
    eapply IHW2; eauto. eapply envt_store_extend; eauto.
  - intros. assert (e1 = false /\ e2 = false /\ e3 = false) as E. destruct e1,e2,e3; intuition.
    destruct E as (E1 & E2 & E3). subst e1 e2 e3. clear H.
    destruct (IHW1 M H1 H2 H2' HX) as (IHW11 & IHW12). eauto.
    destruct (IHW2 M H1 H2 H2' HX) as (IHW21 & IHW22). eauto.
    eapply exp_app_pure; eauto.
  - intros SW ?? ST. eapply exp_sub_eff; eauto. destruct e.
    + eapply exp_abs; eauto. intros.
      eapply envt_store_extend in WFE; eauto.
      eapply envt_extend in WFE; eauto.
      replace (vx2 :: H2' ++ H2) with ((vx2 :: H2') ++ H2) in WFE. 2: simpl; eauto.
      edestruct IHW as (IHW1 & IHW2). eapply WFE. 
      eapply IHW1. eauto. eauto. 
    + eapply exp_abs_pure; eauto. intros.
      eapply envt_store_extend in WFE; eauto.
      eapply envt_extend in WFE; eauto.
      replace (vx2 :: H2' ++ H2) with ((vx2 :: H2') ++ H2) in WFE. 2: simpl; eauto.
      edestruct IHW as (IHW1 & IHW2). eapply WFE. 
      eapply IHW2. eauto. 
  - intros. destruct e.
    + eapply exp_abs; eauto. intros.
      eapply envt_store_extend in WFE; eauto.
      eapply envt_extend in WFE; eauto.
      replace (vx2 :: H2' ++ H2) with ((vx2 :: H2') ++ H2) in WFE. 2: simpl; eauto.
      edestruct IHW as (IHW1 & IHW2). eapply WFE. 
      eapply IHW1. eauto. eauto. 
    + eapply exp_abs_pure; eauto. intros.
      eapply envt_store_extend in WFE; eauto.
      eapply envt_extend in WFE; eauto.
      replace (vx2 :: H2' ++ H2) with ((vx2 :: H2') ++ H2) in WFE. 2: simpl; eauto.
      edestruct IHW as (IHW1 & IHW2). eapply WFE. 
      eapply IHW2. eauto. 
  - eapply IHW; eauto.
  - intros. inversion H. 
Qed.


(* Tweak the signature. To use st_subst from the main beta lemma,
   we need weakening results of the form:

   exists v1, tevaln e1 v1 ->
   forall HX,
   exists v2, tevaln (splice .. e1) v2 /\ val_type v1 v2 T
*)

Lemma tevaln_unique: forall S1 S1' S1'' H1 e1 v1 v1',
    tevaln S1 H1 e1 S1' v1 ->
    tevaln S1 H1 e1 S1'' v1' ->
    S1' = S1'' /\ v1 = v1'.
Proof.
  intros.
  destruct H as [n1 ?].
  destruct H0 as [n2 ?].
  assert (1+n1+n2 > n1) as A1. lia.
  assert (1+n1+n2 > n2) as A2. lia.
  specialize (H _ A1).
  specialize (H0 _ A2).
  split; congruence.
Qed.

(* NOTE: We need this form only for pure expressions, but it
   should be provable also for impure ones. *)
Lemma st_weaken1: forall t1 T1 G
  (W: has_type G t1 T1 false),
  forall M H1 H2 H2',
    env_type M H1 (H2'++H2) G ->
    exists S1' v1,
      (forall S1, tevaln S1 H1 t1 (S1'++S1) v1) /\
      forall HX,
        exists S2' v2,
          (forall S2, tevaln S2 (H2'++HX++H2) (splice_tm t1 (length H2) (length HX)) (S2'++S2) v2) /\
          val_type M v1 v2 T1.
Proof.
  intros.
  assert (exp_type_pure M H1 (H2'++H2) t1 t1 T1). eapply fundamental; eauto.
  destruct H0 as (v1 & v2 & SD1 & SD2 & TX1 & TX2 & VX). 
  exists SD1, v1. split. eapply TX1.
  intros. 
  eapply st_weaken in W; eauto.
  destruct W as (W1 & W2). 
  destruct W2 as (v1' & v2' & SD1' & SD2' & TX1' & TX2' & VX'). eauto.
  exists SD2', v2'. split. eauto.
  assert (SD1 = SD1' /\ v1 = v1') as R. eapply tevaln_unique; eauto.
  specialize (TX1 []). rewrite app_nil_r in TX1. eapply TX1.
  specialize (TX1' []). rewrite app_nil_r in TX1'. eapply TX1'.
  destruct R. congruence. 
Qed.


(* Full substitution only works for pure expressions, which are store-invariant. *)

Lemma st_subst: forall t2 e T2 G0
                        (W: has_type G0 t2 T2 e),
  forall G' G T1, G0 = G'++T1::G ->
  forall M H1 H1' H2 H2' t1 v1,
    env_type M (H1'++H1) (H2'++H2) (G'++G) ->
    length H1 = length G ->
    length H2 = length G ->
    (* (forall S1, tevaln S1 H1 t1 S1 v1) -> *)
    (forall H2',
      exists S2' v2, (* via st_weaken *)
        (forall S2, tevaln S2 (H2'++H2) (splice_tm t1 (length H2) (length H2')) (S2'++S2) v2) /\
        val_type M v1 v2 T1) -> 
    exp_type_eff M
      (H1'++v1::H1) (H2'++H2)
      t2 (subst_tm t2 (length H2) (splice_tm t1 (length H2) (length H2'))) T2 e.
Proof.
  intros ? ? ? ? W. 
  induction W; simpl; intros ??????????? WFE ?? WK; split.
  - intros SW ?? ST. eapply exp_sub_eff; eauto. eapply exp_true; eauto.
  - intros. eapply exp_true; eauto.
  - intros SW ?? ST. eapply exp_sub_eff; eauto. eapply exp_false; eauto.
  - intros. eapply exp_false; eauto.

  - intros SW ?? ST. 
    destruct (WK H2') as (SD2 & v2 & TX2 & VX2). eauto. subst env.
    bdestruct (length H2 =? x).
    + exists S1, (SD2++S2), (st_pad 0 (length SD2) M), v1, v2. split. 2: split. 3: split. 4: split. 5: split. 
      * eapply stchain_pad.
      * eapply sttyw_pad. eauto. 
      * exists 1. intros. destruct n. lia. simpl.
        subst x. rewrite H4, <-H3. rewrite indexr_insert. eauto.
      * eapply TX2.
      * eapply (storet_pad [] SD2) in ST. simpl in ST. eapply ST.
      * subst x. rewrite H4 in H. rewrite indexr_insert in H. inversion H. subst T1.
        eapply valt_store_extend. eapply VX2. eapply stchain_pad. 
    + bdestruct (length H2 <? x).
      * destruct x. lia.
        erewrite <-indexr_insert_ge in H. 2: lia. simpl.
        eapply WFE in H. destruct H as (v1' & v2' & IX1 & IX2 & VX).
        eapply exp_sub_eff; eauto. eapply exp_var; eauto. rewrite <-indexr_insert_ge. eauto. lia.
      * rewrite <-indexr_insert_lt in H. 2: lia.
        eapply WFE in H. destruct H as (v1' & v2' & IX1 & IX2 & VX).
        eapply exp_sub_eff; eauto. eapply exp_var; eauto. rewrite <-indexr_insert_lt. eauto. lia.
  - intros. 
    destruct (WK H2') as (SD2 & v2 & TX2 & VX2). eauto. subst env.
    bdestruct (length H2 =? x).
    + exists v1, v2, [], SD2. split. 2: split. 
      * intros. exists 1. intros. destruct n. lia. simpl.
        subst x. rewrite H4, <-H3. rewrite indexr_insert. eauto.
      * eapply TX2.
      * subst x. rewrite H4 in H. rewrite indexr_insert in H. inversion H. subst T1.
        eapply valt_store_extend. eapply VX2. eapply stchain_pad. 
    + bdestruct (length H2 <? x).
      * destruct x. lia.
        erewrite <-indexr_insert_ge in H. 2: lia. simpl.
        eapply WFE in H. destruct H as (v1' & v2' & IX1 & IX2 & VX).
        eapply exp_var; eauto. rewrite <-indexr_insert_ge. eauto. lia.
      * rewrite <-indexr_insert_lt in H. 2: lia.
        eapply WFE in H. destruct H as (v1' & v2' & IX1 & IX2 & VX).
        eapply exp_var; eauto. rewrite <-indexr_insert_lt. eauto. lia.
  - intros SW ?? ST. eapply exp_ref; eauto. eapply IHW; eauto.
  - intros C. inversion C. 
  - intros SW ?? ST. eapply exp_get; eauto.  eapply IHW; eauto.
  - intros C. inversion C.
  - intros SW ?? ST. edestruct IHW1 as ((S1' & S2' & M' & HH) & ?); eauto. 
    eapply exp_put; eauto.
    destruct HH as (? & ? & ? & ? & ? & ? & ? & ?).
    eapply IHW2; eauto. eapply envt_store_extend; eauto.
    intros HX. destruct (WK HX) as (SD2 & v2 & TX2 & VX2).
    exists SD2, v2. split. eapply TX2. eapply valt_store_extend; eauto.
  - intros C. inversion C.
  - intros SW ?? ST. edestruct IHW1 as ((S1' & S2' & M' & HH) & ?); eauto.
    assert (exp_type S1 S2 M (H1' ++ v1 :: H1) (H2' ++ H2) f
              (subst_tm f (length H2) (splice_tm t1 (length H2) (length H2')))
              (TFun T1 T2 true)) as HY. {
      destruct e3. eexists _,_,_. eauto. eapply exp_sub_fun_eff. eexists _,_,_. eauto. }
    destruct HY as (S1'' & S2'' & M'' & HY).
    eapply exp_app. eauto.
    destruct HY as (v1' & v2' & ? & ? & ? & ? & ? & ?).
    eapply IHW2; eauto. eapply envt_store_extend; eauto.
    intros HX. destruct (WK HX) as (SD2 & v2 & TX2 & VX2).
    exists SD2, v2. split. eapply TX2. eapply valt_store_extend; eauto.
  - intros HE. assert (e1 = false /\ e2 = false /\ e3 = false) as E. destruct e1,e2,e3; intuition.
    destruct E as (E1 & E2 & E3). subst e1 e2 e3. clear HE.
    edestruct (IHW1 _ _ _ H M H1 H1' H2 H2') as (IHW11 & IHW12); eauto.
    edestruct (IHW2 _ _ _ H M H1 H1' H2 H2') as (IHW21 & IHW22); eauto.
    eapply exp_app_pure; eauto.
  - intros SW ?? ST. eapply exp_sub_eff; eauto. destruct e.
    + eapply exp_abs; eauto. intros.
      eapply envt_store_extend in WFE; eauto.
      eapply envt_extend in WFE; eauto.
      replace (vx1 :: H1' ++ H1) with ((vx1 :: H1') ++ H1) in WFE. 2: simpl; eauto.
      replace (vx2 :: H2' ++ H2) with ((vx2 :: H2') ++ H2) in WFE. 2: simpl; eauto.
      rewrite splice_acc. 
      eapply IHW with (H1':=(vx1::H1')) (H2':=(vx2::H2')) (G':=(T1::G')); eauto.
      simpl. subst env. eauto.
      intros HX. destruct (WK HX) as (SD2 & v2 & TX2 & VX2).
      exists SD2, v2. split. eapply TX2. eapply valt_store_extend; eauto.
    + eapply exp_abs_pure; eauto. intros.
      eapply envt_store_extend in WFE; eauto.
      eapply envt_extend in WFE; eauto.
      replace (vx1 :: H1' ++ H1) with ((vx1 :: H1') ++ H1) in WFE. 2: simpl; eauto.
      replace (vx2 :: H2' ++ H2) with ((vx2 :: H2') ++ H2) in WFE. 2: simpl; eauto.
      rewrite splice_acc. 
      eapply IHW with (H1':=(vx1::H1')) (H2':=(vx2::H2')) (G':=(T1::G')); eauto.
      simpl. subst env. eauto.
      intros HX. destruct (WK HX) as (SD2 & v2 & TX2 & VX2).
      exists SD2, v2. split. eapply TX2. eapply valt_store_extend; eauto.
  - intros. destruct e.
    + eapply exp_abs; eauto. intros.
      eapply envt_store_extend in WFE; eauto.
      eapply envt_extend in WFE; eauto.
      replace (vx1 :: H1' ++ H1) with ((vx1 :: H1') ++ H1) in WFE. 2: simpl; eauto.
      replace (vx2 :: H2' ++ H2) with ((vx2 :: H2') ++ H2) in WFE. 2: simpl; eauto.
      rewrite splice_acc. 
      eapply IHW with (H1':=(vx1::H1')) (H2':=(vx2::H2')) (G':=(T1::G')); eauto.
      simpl. subst env. eauto.
      intros HX. destruct (WK HX) as (SD2 & v2 & TX2 & VX2).
      exists SD2, v2. split. eapply TX2. eapply valt_store_extend; eauto.
    + eapply exp_abs_pure; eauto. intros.
      eapply envt_store_extend in WFE; eauto.
      eapply envt_extend in WFE; eauto.
      replace (vx1 :: H1' ++ H1) with ((vx1 :: H1') ++ H1) in WFE. 2: simpl; eauto.
      replace (vx2 :: H2' ++ H2) with ((vx2 :: H2') ++ H2) in WFE. 2: simpl; eauto.
      rewrite splice_acc. 
      eapply IHW with (H1':=(vx1::H1')) (H2':=(vx2::H2')) (G':=(T1::G')); eauto.
      simpl. subst env. eauto.
      intros HX. destruct (WK HX) as (SD2 & v2 & TX2 & VX2).
      exists SD2, v2. split. eapply TX2. eapply valt_store_extend; eauto.
  - eapply IHW; eauto.
  - intros C. inversion C.
Unshelve. 
  apply 0. apply 0.
Qed.


Lemma st_subst1 : forall M t1 t2 G T1 T2 H1 H2 v1 e,
    has_type (T1::G) t2 T2 e ->
    env_type M H1 H2 G ->
    (forall H2',
      exists S2' v2, (* via st_weaken *)
        (forall S2, tevaln S2 (H2'++H2) (splice_tm t1 (length H2) (length H2')) (S2'++S2) v2) /\
        val_type M v1 v2 T1) -> 
    exp_type_eff M (v1::H1) H2 t2 (subst_tm t2 (length H2) (splice_tm t1 (length H2) 0)) T2 e.
Proof.
  intros. eapply st_subst with (G':=[]) (H1':=[]) (H2':=[]); eauto. eauto. 
  eapply H0. eapply H0. 
Qed.


Lemma beta_equivalence: forall t1 t2 G T1 T2 e,
  has_type (T1::G) t2 T2 e ->
  has_type G t1 T1 false ->
  sem_type_eff G (tapp (tabs t2) t1) (subst_tm t2 (length G) t1) T2 e.
Proof. 
  intros. intros M H1 H2 WFE.
  assert (length G = length H2) as L. symmetry. eapply WFE.

  assert (exp_type_pure M H1 H2 (tabs t2) (tabs t2) (TFun T1 T2 e)) as C.
  eapply fundamental. econstructor. eauto. eauto. eauto. 
  destruct C as (vf1 & vf2 & SDF1 & SDF2 & TF1 & TF2 & VF).

  assert (SDF1 = [] /\ vf1 = (vabs H1 t2)). {
    destruct (TF1 []) as [n1 TF]. assert (S n1 > n1) as D. lia.
    specialize (TF (S n1) D). simpl in TF. inversion TF.
    rewrite app_nil_r in H4. eauto.
  }
  assert (SDF2 = [] /\ vf2 = (vabs H2 t2)). {
    destruct (TF2 []) as [n1 TF]. assert (S n1 > n1) as D. lia.
    specialize (TF (S n1) D). simpl in TF. inversion TF.
    rewrite app_nil_r in H5. eauto.
  }
  destruct H3, H4. subst SDF1 SDF2 vf1 vf2. simpl in TF1, TF2. 

  specialize st_weaken1 with (H2':=[]) as A. specialize (A _ _ _ H0). 
  edestruct A as (SDX1 & v1 & TX1 & WK2). eapply WFE. 
  
  specialize (st_subst1 (st_pad (length (SDX1)) 0 M) t1 t2 G T1 T2 H1 H2 v1) as SUBST; eauto.
  edestruct (SUBST e H) as (IH1 & IH2). 
  eapply envt_store_extend. eapply WFE. eapply stchain_pad.
  intros HX. destruct (WK2 HX) as (SD2 & v2 & TX2 & VX2).
  exists SD2, v2. split. eapply TX2. eapply valt_store_extend. eauto.
  eapply stchain_pad.

  split.
  - intros SW ?? ST.
    edestruct IH1 as (S1'' & S2'' & M'' & v1' & v2' & ? & ? & TY1 & TY2 & ? & ?).
    eapply sttyw_pad. eauto.
    eapply storet_pad with (SD2:=[]) in ST. eapply ST. 
    
    exists S1'', S2'', M'', v1', v2'. rewrite L.
    split. 2: split. 3: split. 4: split. 5: split.
    + eauto.
    + eauto.
    + destruct (TF1 S1) as [n1 TF].
      destruct (TX1 S1) as [n2 TX].
      destruct TY1 as [n3 TY]. 
      exists (S (n1+n2+n3)). intros.
      destruct n. lia. simpl. 
      rewrite TF. 2: lia. 
      rewrite TX. 2: lia.
      rewrite TY. 2: lia.
      eauto.
    + rewrite splice_zero in TY2. eauto.
    + eauto.
    + eauto.
  - intros C. 
    edestruct IH2 as (v1' & v2' & SDY1 & SDY2 & TY1 & TY2 & ?). eauto.
    exists v1', v2', (SDY1++SDX1), (SDY2). rewrite L.
    split. 2: split. 
    + intros S1.
      destruct (TF1 S1) as [n1 TF].
      destruct (TX1 S1) as [n2 TX].
      destruct (TY1 (SDX1++S1)) as [n3 TY]. 
      exists (S (n1+n2+n3)). intros.
      destruct n. lia. simpl. 
      rewrite TF. 2: lia. 
      rewrite TX. 2: lia.
      rewrite TY. 2: lia.
      rewrite app_assoc. eauto.
    + rewrite splice_zero in TY2. eauto.
    + eapply valt_store_extend. eauto. eapply stchain_pad'. 
Qed.


End STLC.
