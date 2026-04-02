(* Full safety for System F<: *)

(*

An LR-based termination and semantic soundness proof.

Canonical big-step cbv semantics.

Type abstraction and application (System F<:)

Notes:

- We use de Bruijn levels to model bindings, both for
  terms and also for types. Substitution needs to adjust
  levels when going under binders.

- We have different environments for terms (G) and types (J).


THIS FILE (via stlc_tabs_stp.v):
- add boolean refs and binary effects
- store size (M) as Kripke world

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
  | TRef   : ty
  | TVar   : id -> ty
  | TFun   : ty -> ty -> bool -> ty
  | TAll   : ty -> ty -> bool -> ty
.

Inductive tm : Type :=
  | ttrue  : tm
  | tfalse : tm
  | tvar   : id -> tm
  | tref   : tm -> tm
  | tget   : tm -> tm
  | tput   : tm -> tm -> tm
  | tapp   : tm -> tm -> tm
  | tabs   : tm -> tm
  | ttapp  : tm -> ty -> tm
  | ttabs  : tm -> tm
.

Inductive vl: Type :=
  | vbool  :  bool -> vl
  | vref   :  id -> vl
  | vabs   :  list vl -> tm -> vl
  | vtabs  :  list vl -> tm -> vl
.

Definition venv := list vl.
Definition tenv := list (ty).
Definition kenv := list (ty).
Definition stor := list vl.

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.
#[global] Hint Unfold kenv.
#[global] Hint Unfold stor.


(* ---------- locally nameless ---------- *)

Fixpoint closed T n :=
  match T with
  | TAny => True
  | TBool => True
  | TRef => True
  | TVar x => x < n
  | TFun T3 T4 _ => closed T3 n /\ closed T4 n
  | TAll T3 T4 _ => closed T3 n /\ closed T4 (S n)
  end.

Fixpoint splice n l (T : ty) {struct T} : ty :=
  match T with
  | TAny => TAny
  | TBool => TBool
  | TRef => TRef
  | TVar x => TVar (if x <? n then x else l+x)
  | TFun T3 T4 e => TFun (splice n l T3) (splice n l T4) e
  | TAll T3 T2 e => TAll (splice n l T3) (splice n l T2) e
  end.

Fixpoint subst T1 n T2 {struct T1} : ty :=
  match T1 with
  | TAny => TAny
  | TBool => TBool
  | TRef => TRef
  | TVar x => if x =? n then T2 else if x <? n then TVar x else TVar (x-1)
  | TFun T3 T4 e => TFun (subst T3 n T2) (subst T4 n T2) e
  | TAll T3 T4 e => TAll (subst T3 n T2) (subst T4 n (splice n 1 T2)) e
  end.


(* ---------- syntactic typing rules ---------- *)

Definition bsub a b := a = true -> b = true.

Inductive stp : kenv -> ty -> ty -> Prop :=
| s_any: forall J T,
    stp J T TAny
| s_bool: forall J,
    stp J TBool TBool
| s_ref: forall J,
    stp J TRef TRef
| s_fun: forall J T1 T2 T3 T4 e1 e2,
    stp J T3 T1 ->
    stp J T2 T4 ->
    bsub e1 e2 ->
    stp J (TFun T1 T2 e1) (TFun T3 T4 e2)
| s_varx: forall J x,
    stp J (TVar x) (TVar x)
| s_var: forall J x U T,
    indexr x J = Some U ->
    stp J U T ->
    stp J (TVar x) T
| s_all: forall J T1 T2 T3 T4 e1 e2,
    stp J T3 T1 ->
    stp (map (splice (length J) 1) (T3::J)) T2 T4 ->
    closed T3 (length J) ->
    bsub e1 e2 ->
    stp J (TAll T1 T2 e1) (TAll T3 T4 e2)
.

Inductive has_type : tenv -> kenv -> tm -> ty -> bool -> Prop :=
| t_true: forall env J,
    has_type env J ttrue TBool false
| t_false: forall env J,
    has_type env J tfalse TBool false
| t_var: forall x env J T,
    indexr x env = Some T ->
    has_type env J (tvar x) T false
| t_ref: forall env J t e,
    has_type env J t TBool e ->
    has_type env J (tref t) TRef e
| t_get: forall env J t e,
    has_type env J t TRef e ->
    has_type env J (tget t) TBool true
| t_put: forall env J t t2 e1 e2,
    has_type env J t TRef e1 ->
    has_type env J t2 TBool e2 ->
    has_type env J (tput t t2) TBool true
| t_app: forall env J f t T1 T2 e1 e2 e3,
    has_type env J f (TFun T1 T2 e3) e1 ->
    has_type env J t T1 e2 ->
    has_type env J (tapp f t) T2 (e1 || e2 || e3)
| t_abs: forall env J t T1 T2 e,
    has_type (T1::env) J t T2 e ->
    closed T1 (length J) ->
    has_type env J (tabs t) (TFun T1 T2 e) false
| t_tapp: forall env J f T1 T2 e1 e2,
    has_type env J f (TAll T1 T2 e2) e1 ->
    closed T1 (length J) ->
    has_type env J (ttapp f T1) (subst T2 (length J) T1) (e1 || e2)
| t_tabs: forall env J t T1 T2 e,
    has_type (map (splice (length J) 1) env) (map (splice (length J) 1) (T1::J)) t T2 e ->
    closed T1 (length J) ->
    has_type env J (ttabs t) (TAll T1 T2 e) false
| t_sub: forall env J t T1 T2 e1 e2,
    has_type env J t T1 e1 ->
    stp J T1 T2 ->
    bsub e1 e2 ->
    closed T2 (length J) ->
    has_type env J t T2 e2
| t_sub_eff: forall env J t T,
    has_type env J t T false ->
    has_type env J t T true
.


(* ---------- operational semantics ---------- *)

Fixpoint teval(n: nat)(M: stor)(env: venv)(t: tm){struct n}: stor * option (option vl) :=
  match n with
    | 0 => (M, None)
    | S n =>
      match t with
        | ttrue      => (M, Some (Some (vbool true)))
        | tfalse     => (M, Some (Some (vbool false)))
        | tvar x     => (M, Some (indexr x env))
        | tref ex    =>
          match teval n M env ex with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some vx)) => (vx::M', Some (Some (vref (length M'))))
          end
        | tget ex    =>
          match teval n M env ex with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vref x))) => (M', Some (indexr x M'))
            | (M', Some (Some (vabs _ _))) => (M', Some None)
            | (M', Some (Some (vtabs _ _))) => (M', Some None)
          end
        | tput er ex =>
          match teval n M env er with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vabs _ _))) => (M', Some None)
            | (M', Some (Some (vtabs _ _))) => (M', Some None)
            | (M', Some (Some (vref x))) =>
              match teval n M' env ex with
                | (M'', None) => (M'', None)
                | (M'', Some None) => (M'', Some None)
                | (M'', Some (Some vx)) =>
                  match indexr x M'' with
                    | Some _ => (update M'' x vx, Some (Some (vbool true)))
                    | _ => (M'', Some None)
                  end
              end
          end
        | tabs y     => (M, Some (Some (vabs env y)))
        | ttabs y    => (M, Some (Some (vtabs env y)))
        | tapp ef ex   =>
          match teval n M env ef with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vref _))) => (M', Some None)
            | (M', Some (Some (vtabs _ _))) => (M', Some None)
            | (M', Some (Some (vabs env2 ey))) =>
              match teval n M' env ex with
                | (M'', None) => (M'', None)
                | (M'', Some None) => (M'', Some None)
                | (M'', Some (Some vx)) =>
                  teval n M'' (vx::env2) ey
              end
          end
        | ttapp ef T1   =>
          match teval n M env ef with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vref _))) => (M', Some None)
            | (M', Some (Some (vabs _ _))) => (M', Some None)
            | (M', Some (Some (vtabs env2 ey))) =>
                teval n M' env2 ey
          end
      end
  end.

Definition tevaln M env e M' v :=
  exists nm, forall n, n > nm -> teval n M env e = (M', Some (Some v)).


(* ---------- LR definitions  ---------- *)

Definition stty := nat.

Definition store_type (S: stor) (M: stty) :=
  length S = M /\
    forall i,
      i < M ->
      exists b, indexr i S = Some (vbool b).

Definition st_chain (M:stty) (M1:stty) := M <= M1.

Definition vtype := stty -> vl -> Prop.

Definition vt_mono (vt: vtype) := 
  forall M M' v, st_chain M M' -> vt M v -> vt M' v.

Definition vt_sub (vt1 vt2: vtype) :=
  forall M v, vt1 M v -> vt2 M v.
  

Fixpoint val_type (V: list vtype) M v T {struct T}: Prop :=
  match T, v with
  | TAny, _ =>
      True
  | TBool, vbool _ =>
      True
  | TRef, vref l =>
      l < M
  | TVar x, v =>
      exists vt,
      indexr x V = Some vt /\ vt M v
  | TFun T1 T2 _, vabs H ty =>
      forall S' M' vx,
        st_chain M M' ->
        store_type S' M' ->
        val_type V M' vx T1 ->
        exists S'' M'' vy,
          st_chain M' M'' /\
          tevaln S' (vx::H) ty S'' vy /\
          store_type S'' M'' /\
          val_type V M'' vy T2
  | TAll T1 T2 _, vtabs H ty =>
      forall S' M' (vt: vtype),
        vt_mono vt ->
        st_chain M M' ->
        store_type S' M' ->
        vt_sub vt (fun M v => val_type V M v T1) ->
        exists S'' M'' vy,
          st_chain M' M'' /\
          tevaln S' H ty S'' vy /\
          store_type S'' M'' /\
          val_type (vt::V) M'' vy T2
  | _,_ =>
      False
  end.

Definition exp_type S M H V t T :=
  exists S' M' v,
    st_chain M M' /\
    tevaln S H t S' v /\
    store_type S' M' /\
    val_type V M' v T.


Definition env_type M (H: venv) (G: tenv) (V: list vtype) (J: kenv) :=
  length H = length G /\
  length V = length J /\
    (forall x T,
      indexr x G = Some T ->
      exists v,
        indexr x H = Some v /\
        val_type V M v T) /\
    (forall x T,
      indexr x J = Some T ->
      closed T (length J) /\
      exists vt,
        indexr x V = Some vt /\
        vt_mono vt /\
        vt_sub vt (fun M v => val_type V M v T)).

Definition env_type1 (V: list vtype) (J: kenv) :=
  length V = length J /\
    (forall x T,
      indexr x J = Some T ->
      closed T (length J) /\
      exists vt,
        indexr x V = Some vt /\
        vt_mono vt /\
        vt_sub vt (fun M v => val_type V M v T)).


Definition sem_stp (J: kenv) T1 T2 :=
  forall M V v,
    env_type1 V J ->
    val_type V M v T1 -> val_type V M v T2.

Definition sem_type G J t T (e: bool) :=
  forall S M H V,
    env_type M H G V J ->
    store_type S M ->
    exp_type S M H V t T.


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: core.

#[export] Hint Constructors has_type: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.




(* ---------- helper lemmas: tsize, closed/splice/subst  ---------- *)

Lemma closedt_extend: forall T1 n n1,
    closed T1 n -> n <= n1 ->
    closed T1 n1.
Proof.
  intros T1. induction T1; simpl in *; eauto.
  - lia.
  - intuition. eapply IHT1_1 in H1; eauto. eapply IHT1_2 in H2; eauto.
  - intuition. eapply IHT1_1 in H1; eauto. eapply IHT1_2 in H2; eauto. lia.
Qed.

Lemma closedt_splice: forall T1 n l n1,
    closed T1 n1 ->
    closed (splice n l T1) (l+n1).
Proof.
  intros T1. induction T1; intros; simpl in *; eauto.
  - bdestruct (i <? n). simpl. lia. simpl. lia.
  - intuition.
  - replace (S (l+n1)) with (l+(S n1)). intuition. lia.
Qed.

Lemma closedt_subst: forall T2 T1 n n1,
    closed T1 n ->
    closed T2 (S n) ->
    n1 <= n ->
    closed (subst T2 n1 T1) n.
Proof.
  intros T2.
  induction T2; intros; simpl in *; eauto.
  - bdestruct (i =? n1). eauto.
    bdestruct (i <? n1); intuition.
    simpl. lia. simpl. lia.
  - intuition.
  - intuition. eapply IHT2_2. eapply closedt_splice. eauto. eauto. lia.
Qed.


Lemma splice_acc: forall e1 a k c,
  splice a c (splice a k e1) =
  splice a (c+k) e1.
Proof. induction e1; intros; simpl; intuition.
  + bdestruct (i <? a); intuition.
    bdestruct (i <? a); intuition.
    bdestruct (k+i <? a); intuition.
  + specialize (IHe1_1 a k c). specialize (IHe1_2 a k c).
    rewrite IHe1_1. rewrite IHe1_2. auto.
  + specialize (IHe1_1 a k c). specialize (IHe1_2 a k c).
    rewrite IHe1_1. rewrite IHe1_2. auto.
Qed.

Lemma splice_acc': forall e1 a k c,
  splice (k+a) c (splice a k e1) =
  splice a (c+k) e1.
Proof. induction e1; intros; simpl; intuition.
  + bdestruct (i <? a); intuition.
    bdestruct (i <? a); intuition.
    bdestruct (i <? k+a); intuition.
    bdestruct (k + i <? k + a); intuition.
  + specialize (IHe1_1 a k c). specialize (IHe1_2 a k c).
    rewrite IHe1_1. rewrite IHe1_2. auto.
  + specialize (IHe1_1 a k c). specialize (IHe1_2 a k c).
    rewrite IHe1_1. rewrite IHe1_2. auto.
Qed.

Lemma splice_zero: forall e1 a,
  (splice a 0 e1) = e1.
Proof. intros. induction e1; simpl; intuition.
  + bdestruct (i <? a); intuition.
  + rewrite IHe1_1. rewrite IHe1_2. auto.
  + rewrite IHe1_1. rewrite IHe1_2. auto.
Qed.



(* ---------- LR helper lemmas  ---------- *)

Lemma indexr_map: forall {A B} (M: list A) x v (f: A -> B),
    indexr x M = v ->
    indexr x (map f M) = (match v with Some v => Some (f v) | None => None end).
Proof.
  intros ? ? M. induction M; intros.
  simpl. destruct v; intuition. inversion H.
  simpl in *. rewrite map_length.
  bdestruct (x =? length M). subst v. congruence. eauto.
Qed.

Lemma indexr_map': forall {A B} (M: list A) x v (f: A -> B),
    indexr x (map f M) = Some v ->
    exists v', indexr x M = Some v' /\ v = f v'.
Proof.
  intros. erewrite indexr_map in H.
  2: { eapply indexr_var_some' in H. rewrite map_length in H.
       eapply indexr_var_some in H. destruct H. eauto. }
  remember (indexr x M). destruct o. inversion H.
  eexists. intuition. inversion H.
Qed.

Lemma stchain_refl: forall M,
    st_chain M M.
Proof.
  intros. unfold st_chain. lia.
Qed.

Lemma storet_empty:
    store_type [] 0.
Proof.
  split. eauto. intros. inversion H.
Qed.

Lemma storet_extend: forall S M vx,
    store_type S M ->
    val_type [] M vx TBool ->
    store_type (vx :: S) (1 + M).
Proof.
  intros. destruct H as (L & B). split.
  - simpl. lia.
  - intros. bdestruct (i <? M).
    + edestruct B as (b & IX). eauto. exists b. rewrite indexr_skip; eauto. lia.
    + destruct vx; inversion H0. exists b. replace i with (length S) by lia. rewrite indexr_head. eauto.
Qed.


Lemma valt_store_extend: forall V J M M' vx T,
    env_type1 V J ->
    val_type V M vx T ->
    st_chain M M' ->
    val_type V M' vx T.
Proof. 
  intros V J M M' vx T WFE VT SC.
  revert M' SC.
  induction T; intros M' SC.
  - simpl in *. auto.
  - destruct vx; simpl in *; try contradiction; auto.
  - destruct vx; simpl in *; try contradiction. eapply Nat.lt_le_trans; eauto.
  - destruct VT as (vt & IX & HV).
    destruct WFE as (L2 & W2).
    eapply indexr_var_some' in IX as IX'. rewrite L2 in IX'. eapply indexr_var_some in IX'. destruct IX' as (T&?).
    edestruct W2 as (CL & vt' & IX' & VTM & VTS). eauto.
    rewrite IX in IX'. inversion IX'. subst. 
    simpl. exists vt'. split. eauto. eapply VTM. eauto. eauto. 
  - destruct vx; simpl in *; try contradiction.
    intros S' M'' vx' SC' ST VX.
    destruct (VT S' M'' vx' ltac:(unfold st_chain in *; lia) ST VX) as (S'' & M''' & vy & SC'' & TY & STY & VY).
    exists S'', M''', vy. intuition.
  - destruct vx; simpl in *; try contradiction.
    intros S' M'' vt VTM SC' ST VTS.
    destruct (VT S' M'' vt VTM ltac:(unfold st_chain in *; lia) ST VTS) as (S'' & M''' & vy & SC'' & TY & STY & VY).
    exists S'', M''', vy. intuition.
Qed.

Lemma valt_weaken: forall T V V1 vt M v,
    val_type (V1++V) M v T <-> val_type (V1++vt::V) M v (splice (length V) 1 T).
Proof.
  induction T; intros V V1 vt M v; simpl.
  - tauto.
  - destruct v; split; auto.
  - destruct v; split; auto.
  - bdestruct (i <? length V); split; intros HV; auto.
    + erewrite <- indexr_insert_lt; eauto.
    + erewrite <- indexr_insert_lt in HV; eauto.
    + erewrite <- indexr_insert_ge; eauto.
    + erewrite <- indexr_insert_ge in HV; eauto.
  - destruct v; split; intros HV; try contradiction.
    + intros S' M' vx SC ST VX.
      apply (proj2 (IHT1 V V1 vt M' vx)) in VX.
      destruct (HV S' M' vx SC ST VX) as (S'' & M'' & vy & SC'' & TY & STY & VY).
      apply (proj1 (IHT2 V V1 vt M'' vy)) in VY.
      exists S'', M'', vy. split; [exact SC''|]. split; [exact TY|]. split; [exact STY|exact VY].
    + intros S' M' vx SC ST VX.
      apply (proj1 (IHT1 V V1 vt M' vx)) in VX.
      destruct (HV S' M' vx SC ST VX) as (S'' & M'' & vy & SC'' & TY & STY & VY).
      apply (proj2 (IHT2 V V1 vt M'' vy)) in VY.
      exists S'', M'', vy. split; [exact SC''|]. split; [exact TY|]. split; [exact STY|exact VY].
  - destruct v; split; intros HV; try contradiction.
    + intros S' M' vt0 vtm SC ST BND.
      destruct (HV S' M' vt0 vtm SC ST) as (S'' & M'' & vy & SC'' & TY & STY & VY). eauto. 
      intros ???. eapply IHT1. eapply BND. eauto. 
      apply (proj1 (IHT2 V (vt0::V1) vt M'' vy)) in VY.
      exists S'', M'', vy. split; [exact SC''|]. split; [exact TY|]. split; [exact STY|exact VY].
    + intros S' M' vt0 vtm SC ST BND.
      destruct (HV S' M' vt0 vtm SC ST) as (S'' & M'' & vy & SC'' & TY & STY & VY).
      intros ???. eapply IHT1. eapply BND. eauto.
      apply (proj2 (IHT2 V (vt0::V1) vt M'' vy)) in VY.
      exists S'', M'', vy. split; [exact SC''|]. split; [exact TY|]. split; [exact STY|exact VY].
Qed.

Lemma valt_shrink: forall V vt M v T,
    val_type (vt::V) M v (splice (length V) 1 T) -> val_type V M v T.
Proof.
  intros. pose proof (valt_weaken T V (@nil vtype) vt M v) as W.
  simpl in W. tauto.
Qed.

Lemma valt_extend: forall V vt M v T,
    val_type V M v T -> val_type (vt::V) M v (splice (length V) 1 T).
Proof.
  intros. pose proof (valt_weaken T V (@nil vtype) vt M v) as W.
  simpl in W. tauto.
Qed.

Lemma valt_shrink_mult: forall V1 V M v T,
    val_type (V1++V) M v (splice (length V) (length V1) T) -> val_type V M v T.
Proof.
  intros V1. induction V1; intros. simpl in *. rewrite splice_zero in H. eauto.
  eapply IHV1. eapply valt_shrink. eauto.
  rewrite app_length. erewrite splice_acc'. eauto.
Qed.

Lemma valt_extend_mult: forall V1 V M v T,
    val_type V M v T -> val_type (V1++V) M v (splice (length V) (length V1) T).
Proof.
  intros V1. induction V1; intros. simpl in *. rewrite splice_zero. eauto.
  eapply IHV1 in H. eapply valt_extend in H.
  rewrite app_length in H. erewrite splice_acc' in H. eauto.
Qed.


Lemma valt_subst_gen: forall T2 T1 v (vt: vtype) V V1 M,
    vt = (fun M v => val_type V M v T1) ->
    val_type (V1 ++ vt :: V) M v T2 <->
      val_type (V1++V) M v (subst T2 (length V) (splice (length V) (length V1) T1)).
Proof.
  intros T2. induction T2; intros.
  - simpl in *; split; eauto.
  - destruct v; simpl in *; split; eauto.
  - destruct v; simpl in *; split; eauto.
  - simpl in *. bdestruct (i =? length V); eauto; split; intros; eauto.
    (* Todo: annoying duplication due to destructing v *)
    + destruct v; subst vt; destruct H1 as (? & H2 & H3).
      * rewrite indexr_skips in H2. subst i. rewrite indexr_head in H2. inversion H2; subst x; eauto.
        eapply valt_extend_mult. eauto.
        simpl. lia.
      * rewrite indexr_skips in H2. subst i. rewrite indexr_head in H2. inversion H2; subst x; eauto.
        eapply valt_extend_mult. eauto.
        simpl. lia.
      * rewrite indexr_skips in H2. subst i. rewrite indexr_head in H2. inversion H2; subst x; eauto.
        eapply valt_extend_mult. eauto.
        simpl. lia.
      * rewrite indexr_skips in H2. subst i. rewrite indexr_head in H2. inversion H2; subst x; eauto.
        eapply valt_extend_mult. eauto.
        simpl. lia.
    + destruct v; exists vt; subst vt; eauto.
      * rewrite indexr_skips. subst i. rewrite indexr_head. split. eauto.
        eapply valt_shrink_mult. eauto. eauto.
        simpl. lia.
      * rewrite indexr_skips. subst i. rewrite indexr_head. split. eauto.
        eapply valt_shrink_mult. eauto. eauto.
        simpl. lia.
      * rewrite indexr_skips. subst i. rewrite indexr_head. split. eauto.
        eapply valt_shrink_mult. eauto. eauto.
        simpl. lia.
      * rewrite indexr_skips. subst i. rewrite indexr_head. split. eauto.
        eapply valt_shrink_mult. eauto. eauto.
        simpl. lia.
    + bdestruct (i <? length V). {
        erewrite <-indexr_insert_lt in H1; simpl; try lia. eauto.
      } {
        simpl. destruct i. lia. erewrite <-indexr_insert_ge in H1. 2: lia.
        replace (S i - 1) with i. 2: lia. eauto.
      }
    + bdestruct (i <? length V). {
        erewrite <-indexr_insert_lt; eauto.
      } {
        simpl in H1. destruct i. lia. erewrite <-indexr_insert_ge. 2: lia.
        replace (S i - 1) with i in H1. 2: lia. eauto.
      }
  - destruct v; simpl in *; split; intros; eauto.
    + destruct (H0 S' M' vx) as (S'' & M'' & vy & ? & ? & ? & VY). eauto. eauto. eapply IHT2_1; eauto.
      exists S'', M'', vy. split. 2: split. 3: split. eauto. eauto. eauto. eapply IHT2_2; eauto.
    + destruct (H0 S' M' vx) as (S'' & M'' & vy & ? & ? & ? & VY). eauto. eauto. eapply IHT2_1; eauto.
      exists S'', M'', vy. split. 2: split. 3: split. eauto. eauto. eauto. eapply IHT2_2; eauto.
  - destruct v; simpl in *; split; intros; eauto.
    + destruct (H0 S' M' vt0) as (S'' & M'' & vy & ? & ? & ? & VY). eauto. eauto. eauto. 
      { intros ???. eapply IHT2_1; eauto. }
      exists S'', M'', vy. split. 2: split. 3: split. eauto. eauto. eauto. edestruct IHT2_2 with (V1:=vt0::V1); eauto.
      clear H9. eapply H8 in VY. clear H8. simpl in VY.
      rewrite splice_acc. eauto.
    + destruct (H0 S' M' vt0) as (S'' & M'' & vy & ? & ? & ? & VY). eauto. eauto. eauto. 
      { intros ???. eapply IHT2_1; eauto. }
      exists S'', M'', vy. split. 2: split. 3: split. eauto. eauto. eauto. edestruct IHT2_2 with (V1:=vt0::V1); eauto.
      rewrite splice_acc in VY.
      clear H8. eapply H9 in VY. simpl in VY.
      eauto.
Qed.


Lemma valt_subst: forall V vt M v T1 T2,
    vt = (fun M v => val_type V M v T1) ->
    val_type (vt::V) M v T2 ->
    val_type V M v (subst T2 (length V) T1).
Proof.
  intros.
  edestruct valt_subst_gen with (V:=V) (V1:=@nil vtype) (M:=M).
  eauto. simpl in *. eapply H1 in H0. rewrite splice_zero in H0. eauto.
Qed.

Lemma envt_empty:
    env_type 0 [] [] [] [].
Proof.
  split.
  - eauto.
  - split.
    + eauto.
    + split.
      * intros x T IX. inversion IX.
      * intros x T IX. inversion IX.
Qed.

Lemma envt_extend: forall M E G V J v1 T1,
    env_type M E G V J ->
    val_type V M v1 T1 ->
    env_type M (v1::E) (T1::G) V J.
Proof.
  intros.
  remember H as WFE. clear HeqWFE.
  destruct H as (HL & HV & HG & HJ). split. 2: split. 3: split.
  - simpl. eauto.
  - eauto.
  - intros x T IX. bdestruct (x =? length G).
    + subst x. rewrite indexr_head in IX. inversion IX. subst T.
      exists v1. split. rewrite <- HL. rewrite indexr_head. eauto. eauto.
    + rewrite indexr_skip in IX; eauto.
      eapply WFE in IX as IX. destruct IX as (v2 & IX' & VX).
      exists v2. split. rewrite indexr_skip; eauto. lia. eauto.
  - eauto.
Qed.

Lemma envt_store_extend: forall M M' H G V J,
    env_type M H G V J ->
    st_chain M M' ->
    env_type M' H G V J.
Proof.
  intros M M' H G V J WFE SC.
  destruct WFE as [HL WFE1].
  destruct WFE1 as [HV WFE2].
  destruct WFE2 as [HG HJ].
  split.
  - exact HL.
  - split.
    + exact HV.
    + split.
      * intros x T IX.
        edestruct HG as (v & IX' & VX). eauto.
        exists v. split. exact IX'. eapply valt_store_extend; eauto. split; eauto. 
      * intros x T IX.
        edestruct HJ as (CL & vt & IX' & BOUND). eauto.
        split. exact CL.
        exists vt. split. exact IX'.
        exact BOUND.
Qed.

Lemma envt_extend_tabs: forall M E G V J (vt1: vtype) T1,
    env_type M E G V J ->
    vt_mono vt1 ->
    vt_sub vt1 (fun Mx v => val_type V Mx v T1) ->
    closed T1 (length J) ->
    env_type M E (map (splice (length J) 1) G) (vt1::V) (map (splice (length J) 1) (T1::J)).
Proof.
  intros.
  remember H as WFE. clear HeqWFE.
  destruct H as (HL & HV & HG & HJ). split. 2: split. 3: split.
  - rewrite map_length. eauto.
  - simpl. rewrite map_length. eauto.
  - intros x T IX.
    eapply indexr_map' in IX. destruct IX as (T' & IX & ->).
    eapply WFE in IX as IX. destruct IX as (v2 & IXH & VX).
    exists v2. split. eauto. rewrite <- HV. eapply valt_extend. eauto.
  - intros x T IX.
    eapply indexr_map' in IX. destruct IX as (T' & IX & ->).
    bdestruct (x =? length J).
    + subst x. rewrite indexr_head in IX. inversion IX. subst T'.
      split. rewrite map_length. eapply closedt_splice. eauto.
      exists vt1. rewrite <- HV, indexr_head. split. 2: split. eauto. eauto.
      intros ???. eapply valt_extend. eapply H1. eauto. 
    + rewrite indexr_skip in IX; eauto.
      edestruct HJ as (CL & vt' & IX' & VTM & BOUND). eauto.
      split. rewrite map_length. eapply closedt_splice. eauto.
      exists vt'. split. 2: split. rewrite indexr_skip. eauto. lia. eauto.
      intros ???. rewrite <- HV. eapply valt_extend. eapply BOUND. eauto.
Qed.

Lemma envt1_extend_tabs: forall V J (vt1: vtype) T1,
    env_type1 V J ->
    vt_mono vt1 ->
    vt_sub vt1 (fun Mx v => val_type V Mx v T1) ->
    closed T1 (length J) ->
    env_type1 (vt1::V) (map (splice (length V) 1) (T1::J)).
Proof.
  intros.
  remember H as WFE. clear HeqWFE.
  destruct H as (HV & HJ). split. 
  simpl. rewrite map_length. eauto. 
  (* type env *)
  intros x T IX.
  eapply indexr_map' in IX. destruct IX as (T' & IX & ->).
    bdestruct (x =? length J).
    + subst x. rewrite indexr_head in IX. inversion IX. subst T'.
      split. rewrite map_length. eapply closedt_splice. eauto.
      exists vt1. rewrite <- HV, indexr_head. split. 2: split. eauto. eauto.
      intros ???. eapply valt_extend. eapply H1. eauto. 
    + rewrite indexr_skip in IX; eauto.
      edestruct HJ as (CL & vt' & IX' & VTM & BOUND). eauto.
      split. rewrite map_length. eapply closedt_splice. eauto.
      exists vt'. split. 2: split. rewrite indexr_skip. eauto. lia. eauto.
      intros ???. eapply valt_extend. eapply BOUND. eauto.
Qed.

(* ---------- LR compatibility lemmas  ---------- *)
Lemma sem_true: forall G J,
    sem_type G J ttrue TBool false.
Proof.
  intros. intros S M E V WFE ST.
  exists S, M, (vbool true). split. 2: split. 3: split.
  - eapply stchain_refl.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
  - simpl. eauto.
Qed.

Lemma sem_false: forall G J,
    sem_type G J tfalse TBool false.
Proof.
  intros. intros S M E V WFE ST.
  exists S, M, (vbool false). split. 2: split. 3: split.
  - eapply stchain_refl.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
  - simpl. eauto.
Qed.

Lemma sem_var: forall G J x T,
    indexr x G = Some T ->
    sem_type G J (tvar x) T false.
Proof.
  intros. intros S M E V WFE ST.
  destruct WFE as (_ & _ & HG & _).
  eapply HG in H as IX. destruct IX as (v & IX & VX).
  exists S, M, v. split. 2: split. 3: split.
  - eapply stchain_refl.
  - exists 0. intros. destruct n. lia. simpl. rewrite IX. eauto.
  - eauto.
  - eauto.
Qed.

Lemma sem_ref: forall G J t e,
    sem_type G J t TBool e ->
    sem_type G J (tref t) TRef e.
Proof.
  intros. intros S M E V WFE ST.
  destruct (H S M E V WFE ST) as (S' & M' & vx & SC & TX & ST' & VX).
  exists (vx::S'), (1+M'), (vref (length S')). split. 2: split. 3: split.
  - unfold st_chain in *. lia.
  - destruct TX as (n1 & TX). exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. eauto. lia.
  - eapply storet_extend. eauto. destruct vx; simpl in VX; try contradiction; eauto.
  - simpl. destruct ST' as (L & _). lia.
Qed.

Lemma sem_get: forall G J t e,
    sem_type G J t TRef e ->
    sem_type G J (tget t) TBool true.
Proof.
  intros. intros S M E V WFE ST.
  destruct (H S M E V WFE ST) as (S' & M' & vx & SC & TX & ST' & VX).
  destruct vx; simpl in VX; try contradiction.
  destruct ST' as (L & B). subst M'. eapply indexr_var_some in VX as VX'. destruct VX' as (vx & IX).
  exists S', (length S'), vx. split. 2: split. 3: split.
  - eauto.
  - destruct TX as (n1 & TX). exists (1+n1). intros. destruct n. lia. simpl. rewrite TX, IX. eauto. lia.
  - split; eauto.
  - edestruct B as (b & IX'). eauto. rewrite IX in IX'. inversion IX'. simpl. eauto.
Qed.

Lemma sem_put: forall G J t t2 e1 e2,
    sem_type G J t TRef e1 ->
    sem_type G J t2 TBool e2 ->
    sem_type G J (tput t t2) TBool true.
Proof.
  intros. intros S M E V WFE ST.
  destruct (H S M E V WFE ST) as (S' & M' & vx & SC & TX & ST' & VX).
  eapply envt_store_extend in WFE as WFE'. 2: eauto.
  destruct (H0 S' M' E V WFE' ST') as (S'' & M'' & vy & SC' & TY & ST'' & VY).
  eapply valt_store_extend in VX. 2: split; eapply WFE'. 2: eauto. 
  destruct vx; simpl in VX; try contradiction.
  destruct vy; simpl in VY; try contradiction.
  destruct ST'' as (L & B). subst M''.
  eapply indexr_var_some in VX as VX'. destruct VX' as (vx & IX).
  exists (update S'' i (vbool b)), (length S''), (vbool true). split. 2: split. 3: split.
  - unfold st_chain in *. lia.
  - destruct TX as (n1 & TX). destruct TY as (n2 & TY).
    exists (1+n1+n2). intros. destruct n. lia. simpl. rewrite TX, TY, IX. eauto. lia. lia.
  - split. rewrite <- update_length. eauto. intros.
    bdestruct (i0 =? i). subst i0. exists b. rewrite update_indexr_hit; eauto.
    edestruct B. eauto. exists x. rewrite update_indexr_miss; eauto.
  - simpl. eauto.
Qed.

Lemma sem_app: forall G J f t T1 T2 e1 e2 e3,
    sem_type G J f (TFun T1 T2 e3) e1 ->
    sem_type G J t T1 e2 ->
    sem_type G J (tapp f t) T2 (e1 || e2 || e3).
Proof.
  intros ? ? ? ? ? ? ? ? ? HF HX. intros S M E V WFE ST.
  destruct (HF S M E V WFE ST) as (S' & M' & vf & SC & TF & ST' & VF).
  eapply envt_store_extend in WFE as WFE'. 2: eauto.
  destruct (HX S' M' E V WFE' ST') as (S'' & M'' & vx & SC' & TX & ST'' & VX).
  destruct vf; simpl in VF; try contradiction.
  edestruct VF as (S''' & M''' & vy & SC'' & TY & ST''' & VY). eauto. eauto. eauto.
  exists S''', M''', vy. split. 2: split. 3: split.
  - unfold st_chain in *. lia.
  - destruct TF as (n1 & TF). destruct TX as (n2 & TX). destruct TY as (n3 & TY).
    exists (1+n1+n2+n3). intros. destruct n. lia. simpl. rewrite TF, TX, TY. 2,3,4: lia. eauto.
  - eauto.
  - eauto.
Qed.

Lemma sem_abs: forall G J t T1 T2 e,
    sem_type (T1::G) J t T2 e ->
    sem_type G J (tabs t) (TFun T1 T2 e) false.
Proof.
  intros ? ? ? ? ? ? HY. intros S M E V WFE ST.
  assert (length E = length G) as L. eapply WFE.
  exists S, M, (vabs E t). split. 2: split. 3: split.
  - eapply stchain_refl.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
  - simpl. intros. eapply HY. eapply envt_extend; eauto. eapply envt_store_extend; eauto. eauto.
Qed.

Lemma sem_tapp: forall G J f T1 T2 e1 e2,
    sem_type G J f (TAll T1 T2 e2) e1 ->
    sem_type G J (ttapp f T1) (subst T2 (length J) T1) (e1 || e2).
Proof.
  intros ? ? ? ? ? ? ? HF. intros S M E V WFE ST.
  assert (length E = length G) as L. eapply WFE.
  assert (length V = length J) as LV. eapply WFE.
  destruct (HF S M E V WFE) as (S' & M' & vf & SC & EF & ST' & VF). eauto. 
  destruct vf; simpl in VF; try contradiction.
  edestruct (VF S' M' (fun M v => val_type V M v T1)) as (S'' & M'' & vy & SC' & EY & ST'' & VY).
  unfold vt_mono. intros. eapply valt_store_extend. split; eapply WFE. eauto. eauto. 
  unfold st_chain. eauto.
  eauto. 
  unfold vt_sub. eauto. 
  exists S'', M'', vy. split. 2: split. 3: split.
  - unfold st_chain in *. lia. 
  - destruct EF as (n1 & EF).
    destruct EY as (n3 & EY).
    exists (1+n1+n3). intros. destruct n. lia.
    simpl. rewrite EF, EY. 2,3: lia.
    eauto.
  - eauto. 
  - rewrite <- LV. eapply valt_subst. reflexivity. eauto.
Qed.

Lemma sem_tabs: forall G J t T1 T2 e,
    sem_type (map (splice (length J) 1) G) (map (splice (length J) 1) (T1::J)) t T2 e ->
    closed T1 (length J) ->
    sem_type G J (ttabs t) (TAll T1 T2 e) false.
Proof.
  intros ? ? ? ? ? ? HY CL. intros S M E V WFE ST.
  assert (length V = length J) as LV. eapply WFE.
  exists S, M, (vtabs E t). split. 2: split. 3: split.
  - eapply stchain_refl.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
  - simpl. intros S' M' vt SC ST' BND VTS.
    edestruct (HY S' M' E (vt::V)) as (S'' & M'' & vy & SC' & TY & ST'' & VY).
    + assert (WFE' : env_type M' E G V J).
      { eapply envt_store_extend; eauto. }
      replace (map (splice (length V) 1) G) with (map (splice (length J) 1) G).
      2: { rewrite LV. reflexivity. }
      replace (map (splice (length V) 1) (T1::J)) with (map (splice (length J) 1) (T1::J)).
      2: { rewrite LV. reflexivity. }
      eapply (envt_extend_tabs M' E G V J vt T1); eauto.
    + eauto.
    + exists S'', M'', vy. eauto.
Qed.

Lemma sem_stp_any: forall J T,
  sem_stp J T TAny.
Proof.
  intros ? ? ? ? ? WFE V1. simpl. eauto.
Qed.

Lemma sem_stp_bool: forall J,
  sem_stp J TBool TBool.
Proof.
  intros ? ? ? ? WFE V1. eauto.
Qed.

Lemma sem_stp_ref: forall J,
  sem_stp J TRef TRef.
Proof.
  intros ? ? ? ? WFE V1. eauto.
Qed.

Lemma sem_stp_fun: forall J T1 T2 T3 T4 e1 e2,
  sem_stp J T3 T1 ->
  sem_stp J T2 T4 ->
  sem_stp J (TFun T1 T2 e1) (TFun T3 T4 e2).
Proof.
  intros ? ? ? ? ? ? ? ST31 ST24. intros ? V v WFE V1.
  destruct v; simpl in *; eauto; intros S' M' vx SC ST VX.
  eapply ST31 in VX; eauto. 
  destruct (V1 S' M' vx SC ST VX) as (S'' & M'' & vy & SC'' & EY & STY & VY).
  exists S'', M'', vy.
  split. 2: split. 3: split.
  eauto. eauto. eauto. eapply ST24; eauto.
Qed.

Lemma sem_stp_varx: forall J x,
  sem_stp J (TVar x) (TVar x).
Proof.
  intros ? ? ? ? ? WFE V1. eauto.
Qed.

Lemma sem_stp_var: forall J x U T,
    indexr x J = Some U ->
    sem_stp J U T ->
    sem_stp J (TVar x) T.
Proof.
  intros ? ? ? ? IX STU. intros M V v WFE VT.
  simpl in VT. destruct VT as (vt & IX' & VTv).
  remember WFE as WFE'. clear HeqWFE'.
  destruct WFE as (? & ?).
  edestruct H0 as (CL & vt' & IX'' & ? & ?). eauto.
  rewrite IX'' in IX'. inversion IX'. subst vt'.
  eapply STU; eauto.
Qed.

Lemma sem_stp_all: forall J T1 T2 T3 T4 e1 e2,
  sem_stp J T3 T1 ->
  sem_stp (map (splice (length J) 1) (T3::J)) T2 T4 ->
  closed T3 (length J) ->
  sem_stp J (TAll T1 T2 e1) (TAll T3 T4 e2).
Proof.
  intros ? ? ? ? ? ? ? ST31 ST24 CL3. intros M V v WFE VT.
  destruct v; simpl in *; try contradiction.
  intros S' M' vt VTM SC ST VTS.
  assert (VTS': vt_sub vt (fun Mx v0 => val_type V Mx v0 T1)).
  { intros ???. eapply ST31. eauto. eauto. }
  destruct (VT S' M' vt VTM SC ST VTS') as (S'' & M'' & vy & SC' & STY & ST'' & VY).
  exists S'', M'', vy. split. 2: split. 3: split. 
  - eauto. 
  - eauto.
  - eauto.
  - eapply ST24. 2: eapply VY.
    rewrite <- map_cons. rewrite <-(proj1 WFE).
    eapply envt1_extend_tabs; eauto. 
Qed.

Lemma sem_sub: forall G J t T1 T2 e,
    sem_type G J t T1 e ->
    sem_stp J T1 T2 ->
    sem_type G J t T2 e.
Proof.
  intros ? ? ? ? ? ? H1 ST12. intros S M E V WFE ST.
  destruct (H1 S M E V WFE ST) as (S' & M' & vy & SC & TY & STY & VY).
  exists S', M', vy. split. 2: split. 3: split.
  - eauto.
  - eauto.
  - eauto.
  - eapply ST12. split; eapply WFE. eauto. 
Qed.

Lemma stp_fundamental: forall J T1 T2,
    stp J T1 T2 ->
    sem_stp J T1 T2.
Proof.
  intros ? ? ? H. induction H; intros.
  - eapply sem_stp_any; eauto.
  - eapply sem_stp_bool; eauto.
  - eapply sem_stp_ref; eauto.
  - eapply sem_stp_fun; eauto.
  - eapply sem_stp_varx; eauto.
  - eapply sem_stp_var; eauto.
  - eapply sem_stp_all; eauto.
Qed.

Theorem fundamental: forall G J t T e,
    has_type G J t T e ->
    sem_type G J t T e.
Proof.
  intros ? ? ? ? ? W.
  induction W.
  - eapply sem_true.
  - eapply sem_false.
  - eapply sem_var; eauto.
  - eapply sem_ref; eauto.
  - eapply sem_get; eauto.
  - eapply sem_put; eauto.
  - eapply sem_app; eauto.
  - eapply sem_abs; eauto.
  - eapply sem_tapp; eauto.
  - eapply sem_tabs; eauto.
  - eapply sem_sub; eauto. eapply stp_fundamental; eauto.
  - eapply IHW.
Qed.

Corollary safety: forall t T e,
  has_type [] [] t T e ->
  exp_type [] 0 [] [] t T.
Proof.
  intros. eapply fundamental in H as ST; eauto.
  destruct (ST [] 0 [] []) as (S' & M' & v & ? & ? & ? & ?).
  eapply envt_empty.
  eapply storet_empty.
  exists S', M', v. intuition.
Qed.


End STLC.
