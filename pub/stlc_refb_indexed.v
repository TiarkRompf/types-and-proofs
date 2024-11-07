(* Full safety for STLC *)

(*

An LR-based semantic soundness proof for STLC.

Add first-order mutable references (restricted to TBool)

Step-indexed LR: soundness only, no termination.

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

Fixpoint teval(n: nat)(M:stor)(env: venv)(t: tm){struct n}: nat * stor * option (option vl) :=
  match n with
    | 0 => (0, M, None)
    | S n =>
      match t with
        | ttrue      => (1, M, Some (Some (vbool true)))
        | tfalse     => (1, M, Some (Some (vbool false)))
        | tvar x     => (1, M, Some (indexr x env))
        | tref ex    =>
          match teval n M env ex with
            | (dx, M', None)           => (1+dx, M', None)
            | (dx, M', Some None)      => (1+dx, M', Some None)
            | (dx, M', Some (Some vx)) => (1+dx, vx::M', Some (Some (vref (length M'))))
          end
        | tget ex    =>
          match teval n M env ex with
            | (dx, M', None)                     => (1+dx, M', None)
            | (dx, M', Some None)                => (1+dx, M', Some None)
            | (dx, M', Some (Some (vbool _)))    => (1+dx, M', Some None)
            | (dx, M', Some (Some (vabs _ _))) => (1+dx, M', Some None)
            | (dx, M', Some (Some (vref x)))     => (1+dx, M', Some (indexr x M'))
          end
        | tput er ex    =>
          match teval n M env er with
            | (dr, M', None)                     => (1+dr, M', None)
            | (dr, M', Some None)                => (1+dr, M', Some None)
            | (dr, M', Some (Some (vbool _)))    => (1+dr, M', Some None)
            | (dr, M', Some (Some (vabs _ _))) => (1+dr, M', Some None)
            | (dr, M', Some (Some (vref x))) =>
              match teval (n-dr) M' env ex with
                | (dx, M'', None)                => (1+dr+dx, M'', None)
                | (dx, M'', Some None)           => (1+dr+dx, M'', Some None)
                | (dx, M'', Some (Some vx)) =>
                    match indexr x M'' with
                    | Some v => (1+dr+dx, update M'' x vx, Some (Some (vbool true)))
                    | _      => (1+dr+dx, M'', Some None)
                    end
              end
          end
        | tabs y   => (1, M, Some (Some (vabs env y)))
        | tapp ef ex =>
          match teval n M env ef with
            | (df, M', None)                  => (1+df, M', None)
            | (df, M', Some None)             => (1+df, M', Some None)
            | (df, M', Some (Some (vbool _))) => (1+df, M', Some None)
            | (df, M', Some (Some (vref _)))  => (1+df, M', Some None)
            | (df, M', Some (Some (vabs env2 ey))) =>
              match teval (n-df) M' env ex with
                | (dx, M'', None)           => (1+df+dx, M'', None)
                | (dx, M'', Some None)      => (1+df+dx, M'', Some None)
                | (dx, M'', Some (Some vx)) =>
                  match teval (n-df-dx) M'' (vx::env2) ey with
                    | (dy, M''', ry) => (1+df+dx+dy, M''', ry)
                  end
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

Lemma eval_deterministic: forall m n, n < m -> forall S S1 H t n1 r j,
  teval n S H t = (n1, S1, Some r) -> j >= n -> (* alt: j >= n1 ? *)
  teval j S H t = (n1, S1, Some r).
Proof.
  intros m. induction m. intros. inversion H.
  intros. destruct n. inversion H1. destruct j. inversion H2.
  destruct t; simpl; simpl in H1; try eauto.
  - remember (teval n S H0 t) as tf. destruct tf as [[nf Sf] [rf|]].
    rewrite IHm with (n:=n) (n1:=nf) (r:=rf) (S1:=Sf).
    destruct rf; try destruct v; try solve [inversion H1; eauto].
    lia. eauto. lia.
    inversion H1. 
  - remember (teval n S H0 t) as tf. destruct tf as [[nf Sf] [rf|]].
    rewrite IHm with (n:=n) (n1:=nf) (r:=rf) (S1:=Sf).
    destruct rf; try destruct v; try solve [inversion H1; eauto].
    lia. eauto. lia.
    inversion H1. 
  - remember (teval n S H0 t1) as tf. destruct tf as [[nf Sf] [rf|]].
    rewrite IHm with (n:=n) (n1:=nf) (r:=rf) (S1:=Sf).
    destruct rf; try destruct v; try solve [inversion H1; eauto]. 
    remember (teval (n-nf) Sf H0 t2) as tx. destruct tx as [[nx Sx] [rx|]].
    rewrite IHm with (n:=n-nf) (n1:=nx) (r:=rx) (S1:=Sx).
    destruct rx; try solve [destruct v; inversion H1; eauto].
    eauto. lia. eauto. lia.
    inversion H1. inversion H1.
    lia. eauto. lia.
    inversion H1.
  - remember (teval n S H0 t1) as tf. destruct tf as [[nf Sf] [rf|]].
    rewrite IHm with (n:=n) (n1:=nf) (r:=rf) (S1:=Sf).
    destruct rf; try destruct v; try solve [inversion H1; eauto]. 
    remember (teval (n-nf) Sf H0 t2) as tx. destruct tx as [[nx Sx] [rx|]].
    rewrite IHm with (n:=n-nf) (n1:=nx) (r:=rx) (S1:=Sx).
    destruct rx; try solve [destruct v; inversion H1; eauto].
    remember (teval (n-nf-nx) Sx (v :: l) t) as ty. destruct ty as [[ny Sy] [ry|]].
    rewrite IHm with (n:=n-nf-nx) (n1:=ny) (r:=ry) (S1:=Sy).
    eauto. lia. eauto. lia.
    inversion H1. inversion H1.
    eauto. lia. eauto. lia.
    inversion H1.
    lia. eauto. lia.
    inversion H1.
Qed.

Lemma eval_bounded: forall m n, n < m -> forall S S1 H t n1 r,
    teval n S H t = (n1, S1, Some r) ->
    1 <= n1 /\ n1 <= n.
Proof.
  intros m. induction m. intros. inversion H.
  intros. destruct n. inversion H1.
  destruct t; simpl in *; inversion H1; try lia.
  - remember (teval n S H0 t) as tf. destruct tf as [[nf Sf] [rf|]]. 2: { inversion H1. }
    symmetry in Heqtf. eapply IHm with (n:=n) (n1:=nf) (r:=rf) in Heqtf as HF1. 2: lia.
    destruct rf. 2: { inversion H1. lia. } inversion H1. lia. 
  - remember (teval n S H0 t) as tf. destruct tf as [[nf Sf] [rf|]]. 2: { inversion H1. }
    symmetry in Heqtf. eapply IHm with (n:=n) (n1:=nf) (r:=rf) in Heqtf as HF1. 2: lia.
    destruct rf. 2: { inversion H1. lia. } destruct v; inversion H1; lia. 
  - remember (teval n S H0 t1) as tf. destruct tf as [[nf Sf] [rf|]]. 2: { inversion H1. }
    symmetry in Heqtf. eapply IHm with (n:=n) (n1:=nf) (r:=rf) in Heqtf as HF1. 2: lia.
    destruct rf. 2: { inversion H1. lia. } destruct v. inversion H1. lia.
    remember (teval (n-nf) Sf H0 t2) as tx. destruct tx as [[nx Sx] [rx|]]. 2: inversion H1.
    symmetry in Heqtx. eapply IHm in Heqtx as HX1. 2: lia.
    destruct rx. 2: { inversion H1. lia. }
    remember (indexr i Sx). destruct o. inversion H1. lia. inversion H1. lia. inversion H1. lia. 
  - remember (teval n S H0 t1) as tf. destruct tf as [[nf Sf] [rf|]]. 2: { inversion H1. }
    symmetry in Heqtf. eapply IHm with (n:=n) (n1:=nf) (r:=rf) in Heqtf as HF1. 2: lia.
    destruct rf. 2: { inversion H1. lia. } destruct v; inversion H1; try lia.
    remember (teval (n-nf) Sf H0 t2) as tx. destruct tx as [[nx Sx] [rx|]]. 2: inversion H1. 
    symmetry in Heqtx. eapply IHm in Heqtx as HX1. 2: lia.
    destruct rx. 2: { inversion H1. lia. } inversion H1. 
    remember (teval (n-nf-nx) Sx (v :: l) t) as ty. destruct ty as [[ny Sy] [ry|]].
    symmetry in Heqty. eapply IHm in Heqty as HY1. 2: lia. 2: inversion H1. 
    inversion H1. lia. 
Qed.




(* ---------- LR definitions  ---------- *)

Definition stty := nat. (* length of store *)

Definition store_type (S: stor) (M: stty) :=
  length S = M /\
    forall i,
      i < M ->
      exists b, indexr i S = Some (vbool b).

Definition st_chain (M:stty) (M1:stty) :=
  M <= M1.


Fixpoint val_type n M v T {struct n}: Prop :=
  match n with
  | 0 => True
  | S n =>
      match v, T with
      | vbool b, TBool =>  
          True
      | vref l, TRef => 
          l < M
      | vabs H ty, TFun T1 T2 =>
          forall S' M' nx vx,
            st_chain M M' ->
            store_type S' M' ->
            val_type (n-nx) M' vx T1 ->
            forall S'' ny ry,
              teval (n-nx) S' (vx::H) ty = (ny, S'', (Some ry)) ->
              exists M'' vy,
                st_chain M' M'' /\
                store_type S'' M'' /\
                ry = Some vy /\
                val_type (n-nx-ny) M'' vy T2
      | _,_ =>
          False
      end
  end.


Definition exp_type n S M H t T :=
  forall n' S' r,
    teval n S H t = (n', S', Some r) ->
    exists M' v,
      st_chain M M' /\
      store_type S' M' /\
      r = Some v /\
      val_type (n-n') M' v T.

Definition env_type n M (H: venv) (G: tenv) :=
  length H = length G /\
    forall x T,
      indexr x G = Some T ->
      exists v,
        indexr x H = Some v /\
        val_type n M v T.

Definition sem_type G t T :=
  forall n S M H,
    env_type n M H G ->
    store_type S M ->
    exp_type n S M H t T.


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


Lemma envt_empty: forall n,
    env_type n 0 [] [].
Proof.
  intros. split. eauto. intros. inversion H. 
Qed.

Lemma envt_extend: forall n M E G v1 T1,
    env_type n M E G ->
    val_type n M v1 T1 ->
    env_type n M (v1::E) (T1::G).
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

Lemma valt_dec: forall m n, n < m -> forall n1 v1 M T1,
    val_type n M v1 T1 -> n1 <= n ->
    val_type n1 M v1 T1.
Proof.
  intros m. induction m. lia. intros. destruct n; destruct n1. eauto. lia. simpl. eauto. 
  destruct v1, T1; simpl in H0; try contradiction.
  - simpl. eauto.
  - simpl. eauto. 
  - simpl. intros.
    edestruct H0 with (nx:=n-n1+nx). eauto. eauto.  eapply IHm. 2: eauto. lia. lia.
    eapply eval_deterministic. 2: eauto. eauto. lia.
    edestruct H6 as (? & ? & ? & ? & ?). 
    eexists _, _. split. 2: split. 3: split.
    eauto. eauto. eauto. eapply IHm. 2: eapply H10. lia. lia. 
Qed.

Lemma envt_dec: forall n n1 M H G,
    env_type n M H G -> n1 <= n ->
    env_type n1 M H G.
Proof.
  intros. destruct H0. split. eauto.
  intros. eapply H2 in H3. destruct H3. eexists. intuition eauto.
  eapply valt_dec; eauto. 
Qed.

Lemma storet_empty:
    store_type [] 0.
Proof.
  intros. split. eauto. intros. inversion H. 
Qed.

Lemma storet_extend: forall n S M vx,
    store_type S M ->
    val_type (1+n) M vx TBool ->
    store_type (vx :: S) (1 + M).
Proof.
  intros. destruct H. split.
  - simpl. lia.
  - intros. bdestruct (i <? M).
    eapply H1 in H3 as H4. destruct H4. exists x. rewrite indexr_skip. eauto. lia.
    destruct vx; inversion H0. exists b. replace i with (length S).
    rewrite indexr_head. eauto. lia. 
Qed.

Lemma valt_store_extend: forall n M M' vx T,
    val_type n M vx T ->
    st_chain M M' ->
    val_type n M' vx T.
Proof.
  intros. destruct n, vx, T; simpl in *; eauto; try contradiction.
  - simpl. unfold st_chain in *. lia.
  - simpl. intros. edestruct (H S' M'0 nx vx); eauto.
    unfold st_chain in *. lia.
Qed.

Lemma envt_store_extend: forall n M M' H G,
    env_type n M H G ->
    st_chain M M' ->
    env_type n M' H G.
Proof.
  intros. destruct H0 as (L & IX). split. 
  - eauto.
  - intros. edestruct IX as (v & IX' & VX). eauto.
    exists v. split. eauto. eapply valt_store_extend; eauto.
Qed.


(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_true: forall G,
    sem_type G ttrue TBool.
Proof.
  intros. intros n S M E WFE ST. intros ? ? ? EV.
  destruct n; inversion EV. subst n' S' r.
  exists M, (vbool true).
  split. 2: split. 3: split.
  - eapply stchain_refl.
  - eauto.
  - eauto.
  - destruct n; simpl; eauto. 
Qed.

Lemma sem_false: forall G,
    sem_type G tfalse TBool.
Proof.
  intros. intros n S M E WFE ST. intros ? ? ? EV.
  destruct n; inversion EV. subst n' S' r.
  exists M, (vbool false).
  split. 2: split. 3: split.
  - eapply stchain_refl. 
  - eauto.
  - eauto.
  - destruct n; simpl; eauto. 
Qed.

Lemma sem_var: forall G x T,
    indexr x G = Some T ->
    sem_type G (tvar x) T.
Proof.
  intros. intros n S M E WFE ST. intros ? ? ? EV.
  destruct n; inversion EV. subst n' S' r.                                    
  eapply WFE in H as IX. destruct IX as (v & IX & VX).
  exists M, v.
  split. 2: split. 3: split.
  - eapply stchain_refl. 
  - eauto.
  - eauto.
  - eapply valt_dec. eauto. eauto. lia. 
Qed.

Lemma sem_ref: forall G t,
    sem_type G t TBool ->
    sem_type G (tref t) TRef.
Proof.
  intros ? ? HX. intros n S M E WFE ST. intros n1 S1 r1 EV.
  destruct n; simpl in EV. inversion EV.
  
  remember (teval n S E t) as tx. symmetry in Heqtx. destruct tx as [[nx S'] [rx|]]. 2: inversion EV.
  edestruct (HX (1+n) S M E) as (M' & vx & SC' & ST' & RX & VX). eauto. eauto. eapply eval_deterministic. eauto. eauto. lia. 
  eapply eval_bounded in Heqtx as BX; eauto.
  subst rx.

  inversion EV. subst n1 S1 r1. 
  
  exists (1+M'), (vref (length S')).
  split. 2: split. 3: split.
  - unfold st_chain in *. lia.
  - eapply storet_extend with (n:=0). eauto. eapply valt_dec; eauto. lia.
  - eauto.
  - simpl. remember (n - nx) as nx1. destruct nx1.
    simpl. eauto.
    simpl. destruct ST'. lia. 
Qed.

Lemma sem_get: forall G t,
    sem_type G t TRef ->
    sem_type G (tget t) TBool.
Proof.
  intros ? ? HX. intros n S M E WFE ST. intros n1 S1 r1 EV.
  destruct n. inversion EV. simpl in EV. 

  remember (teval n S E t) as tx. symmetry in Heqtx. destruct tx as [[nx S'] [rx|]]. 2: inversion EV.
  edestruct (HX (1+n) S M E) as (M' & vx & SC' & ST' & RX & VX). eauto. eauto. eapply eval_deterministic. eauto. eauto. lia. 
  eapply eval_bounded in Heqtx as BX; eauto.
  subst rx.

  remember (1 + n - nx) as nx1. destruct nx1. lia. 
  simpl in VX. destruct vx; try contradiction. 
  
  inversion EV. subst n1 S1 r1. 

  destruct ST' as (L & B). subst M'.
  eapply indexr_var_some in VX as VX'. destruct VX' as (vx & IX).
  edestruct B. eauto. rewrite H in IX. inversion IX. subst vx. 
  exists (length S') (*M'*), (vbool x).
  split. 2: split. 3: split.
  - eauto. 
  - split; eauto. 
  - eauto. 
  - simpl. remember (n-nx) as nx2. destruct nx2.
    simpl. eauto.
    simpl. eauto.
Qed.

Lemma sem_put: forall G t t2,
    sem_type G t TRef ->
    sem_type G t2 TBool ->
    sem_type G (tput t t2) TBool.
Proof.
  intros ? ? ? HX HY. intros n S M E WFE ST. intros n3 S3 r3 EV.
  destruct n. inversion EV. simpl in EV. 

  remember (teval n S E t) as tx. symmetry in Heqtx. destruct tx as [[nx S1] [rx|]]. 2: inversion EV.
  edestruct (HX (1+n) S M E) as (M1 & vx & SC1 & ST1 & RX & VX). eauto. eauto. eapply eval_deterministic. eauto. eauto. lia. 
  eapply eval_bounded in Heqtx as BX; eauto.
  subst rx.

  remember (1 + n - nx) as nx1. destruct nx1. lia. 
  simpl in VX. destruct vx; try contradiction.

  remember (teval (n-nx) S1 E t2) as ty. symmetry in Heqty. destruct ty as [[ny S2] [ry|]]. 2: inversion EV.
  edestruct (HY (1+n) S1 M1 E) as (M2 & vy & SC2 & ST2 & RY & VY). eapply envt_store_extend. eauto. eauto. eauto. eapply eval_deterministic. 2: eauto. eauto. lia. 
  eapply eval_bounded in Heqty as BY; eauto.
  subst ry.

  remember (1 + n - ny) as ny1. destruct ny1. lia. 
  simpl in VY. destruct vy; try contradiction.
  
  destruct ST1 as (L1 & B1). subst M1.
  destruct ST2 as (L2 & B2). subst M2.
  assert (i < length S2) as VX'. unfold st_chain in *. lia. 
  eapply indexr_var_some in VX'. destruct VX' as (vx & IX).
  rewrite IX in EV. inversion EV. subst n3 S3 r3.

  exists (length S2), (vbool true).
  split. 2: split. 3: split.
  - unfold st_chain in *. lia. 
  - split. rewrite <-update_length. eauto. intros. 
    bdestruct (i0 =? i). subst i0. exists b. rewrite update_indexr_hit; eauto.
    edestruct B2. eauto. exists x. rewrite update_indexr_miss; eauto. 
  - simpl. eauto.
  - simpl. remember (n - (nx + ny)) as ny2. destruct ny2.
    simpl. eauto.
    simpl. eauto. 
Qed.

Lemma sem_app: forall G f t T1 T2,
    sem_type G f (TFun T1 T2) ->
    sem_type G t T1 ->
    sem_type G (tapp f t) T2.
Proof.
  intros ? ? ? ? ? HF HX. intros n S M E WFE ST. intros n3' S3' r3' EV.
  destruct n. inversion EV. simpl in EV. 

  (* function evaluates *)
  remember (teval n S E f) as tf. symmetry in Heqtf. destruct tf as [[nf S1] [rf|]]. 2: inversion EV.
  edestruct (HF (1+n) S M E) as (M1 & vf & SC1 & ST1 & RF & VF). eauto. eauto. eapply eval_deterministic. 2: eauto. eauto. lia. 
  eapply eval_bounded in Heqtf as BF; eauto.
  remember (1+n-nf) as nf1. destruct nf1. lia.
  subst rf.

  (* result is a function value *)
  simpl in VF. destruct vf; try contradiction.

  (* argument evaluates *)
  remember (teval (n-nf) S1 E t) as tx. symmetry in Heqtx. destruct tx as [[nx S2] [rx|]]. 2: inversion EV.
  edestruct (HX (1+n) S1 M1 E) as (M2 & vx & SC2 & ST2 & RX & VX). eapply envt_store_extend. eauto. eauto. eauto. eapply eval_deterministic. 2: eauto. eauto. lia.
  eapply eval_bounded in Heqtx as BX; eauto.
  remember (1+n-nx) as nx1. destruct nx1. lia.
  subst rx. 

  (* function body evaluates *)
  remember (teval (n-nf-nx) S2 (vx :: l) t0) as ty. symmetry in Heqty. destruct ty as [[ny S3] [ry|]]. 2: inversion EV.
  eapply eval_bounded in Heqty as BY; eauto.
  inversion EV. subst n3' S3' r3'. 

  (* from function LR: function body result is well-typed *)
  assert (nf1 = n-nf). lia. subst nf1. 
  edestruct (VF S2 M2 nx vx) as (M3 & vy & SC3 & ST3 & RY & VY).
  unfold st_chain in *. lia.
  eauto. 
  eapply valt_dec; eauto. lia.
  eauto.
  subst ry.

  (* return result *)
  exists M3, vy. split. 2: split. 3: split.
  - unfold st_chain in *. lia.
  - eauto.
  - eauto. 
  - eapply valt_dec. 2: eauto. eauto. lia. 
Qed.

Lemma sem_abs: forall G t T1 T2,
    sem_type (T1::G) t T2 ->
    sem_type G (tabs t) (TFun T1 T2).
Proof.
  intros ? ? ? ? HY. intros n S M E WFE ST. intros n1 S1 r1 EV.
  destruct n. inversion EV. simpl in EV.

  inversion EV. subst n1 S1 r1.
  
  exists M, (vabs E t). split. 2: split. 3: split. 
  - eapply stchain_refl.
  - eauto.
  - eauto. 
  - simpl. remember (n-0) as n'. destruct n'.
    simpl. eauto.
    simpl. intros S1 M1 nx vx SC1 ST1 VX S2 ny ry EVY.
    remember (n'-nx) as nx'. destruct nx'. inversion EVY. 
    eapply HY. 
    + eapply envt_extend.
      eapply envt_store_extend.
      eapply envt_dec. eauto. lia. eauto. eauto.
    + eauto.
    + eauto. 
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
  - eapply sem_ref; eauto.
  - eapply sem_get; eauto.
  - eapply sem_put; eauto.
  - eapply sem_app; eauto. 
  - eapply sem_abs; eauto.
Qed.

Corollary safety: forall t T,
  has_type [] t T ->
  forall n, exp_type n [] 0 [] t T.
Proof. 
  intros. intros ? ? ? EV.
  eapply fundamental in H as ST; eauto.
  edestruct (ST n [] 0 []) as (M' & v & SC' & ST' & R & V).
  eapply envt_empty.
  eapply storet_empty.
  eauto. 
  exists M', v. intuition.
Qed.

End STLC.
