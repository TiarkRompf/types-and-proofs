(* Full safety for STLC *)

(*

An LR-based termination and semantic soundness proof for STLC.

Canonical big-step cbv semantics.

Type abstraction and application (System F<:)

Notes:

- We use de Bruijn levels to model bindings, both for
  terms and also for types. Substitution needs to adjust
  levels when going under binders.


THIS FILE (via stlc_tabs3.v):
- add subtyping (TAny top type, bounded TAll)

THIS FILE (via stlc_tabs2.v):
- switch from locally nameless to pure de Bruijn levels

THIS FILE (via stlc_tabs.v):
- split single env into term (G) and type (J) env


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
  | TVar   : id -> ty
  | TFun   : ty -> ty -> ty
  | TAll   : ty -> ty -> ty
.

Inductive tm : Type :=
  | ttrue  : tm
  | tfalse : tm
  | tvar   : id -> tm
  | tapp   : tm -> tm -> tm
  | tabs   : tm -> tm
  | ttapp  : tm -> ty -> tm
  | ttabs  : tm -> tm
.

Inductive vl: Type :=
  | vbool  :  bool -> vl
  | vabs   :  list vl -> tm -> vl
  | vtabs  :  list vl -> tm -> vl
.

Definition venv := list vl.
Definition tenv := list (ty).
Definition kenv := list (ty).

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.
#[global] Hint Unfold kenv.


(* ---------- locally nameless ---------- *)

Fixpoint closed T n :=
  match T with
  | TAny => True
  | TBool => True
  | TVar x => x < n
  | TFun T3 T4 => closed T3 n /\ closed T4 n
  | TAll T3 T4 => closed T3 n /\ closed T4 (S n)
  end.

Fixpoint splice n l (T : ty) {struct T} : ty :=
  match T with
  | TAny => TAny
  | TBool => TBool
  | TVar x => TVar (if x <? n then x else l+x)
  | TFun T3 T4 => TFun (splice n l T3) (splice n l T4)
  | TAll T3 T2   => TAll (splice n l T3) (splice n l T2)
  end.

Fixpoint subst T1 n T2 {struct T1} : ty :=
  match T1 with
  | TAny => TAny
  | TBool => TBool
  | TVar x => if x =? n then T2 else if x <? n then TVar x else TVar (x-1)
  | TFun T3 T4 => TFun (subst T3 n T2) (subst T4 n T2)
  | TAll T3 T4 => TAll (subst T3 n T2) (subst T4 n (splice n 1 T2))
  end.


(* ---------- syntactic typing rules ---------- *)

Inductive stp : kenv -> ty -> ty -> Prop :=
| s_any: forall J T,
    stp J T TAny
| s_bool: forall J,
    stp J TBool TBool
| s_fun: forall J T1 T2 T3 T4,
    stp J T3 T1 ->
    stp J T2 T4 ->
    stp J (TFun T1 T2) (TFun T3 T4)
| s_varx: forall J x,
    stp J (TVar x) (TVar x)
| s_var: forall J x U T,
    indexr x J = Some U ->
    stp J U T ->
    stp J (TVar x) T
| s_all: forall J T1 T2 T3 T4,
    stp J T3 T1 ->
    stp (map (splice (length J) 1) (T3::J)) T2 T4 ->
    closed T3 (length J) ->
    stp J (TAll T1 T2) (TAll T3 T4)
.

Inductive has_type : tenv -> kenv -> tm -> ty -> Prop :=
| t_true: forall env J,
    has_type env J ttrue TBool
| t_false: forall env J,
    has_type env J tfalse TBool
| t_var: forall x env J T,
    indexr x env = Some T ->
    has_type env J (tvar x) T
| t_app: forall env J f t T1 T2,
    has_type env J f (TFun T1 T2) ->
    has_type env J t T1 ->
    has_type env J (tapp f t) T2
| t_abs: forall env J t T1 T2,
    has_type (T1::env) J t T2 ->
    closed T1 (length J) ->
    has_type env J (tabs t) (TFun T1 T2)
| t_tapp: forall env J f T1 T2,
    has_type env J f (TAll T1 T2) ->
    closed T1 (length J) ->
    has_type env J (ttapp f T1) (subst T2 (length J) T1)
| t_tabs: forall env J t T1 T2,
    has_type (map (splice (length J) 1) env) (map (splice (length J) 1) (T1::J)) t T2 ->
    closed T1 (length J) ->
    has_type env J (ttabs t) (TAll T1 T2)
| t_sub: forall env J t T1 T2,
    has_type env J t T1 ->
    stp J T1 T2 ->
    closed T2 (length J) ->
    has_type env J t T2
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
        | ttabs y    => Some (Some (vtabs env y))
        | tapp ef ex   =>
          match teval n env ef with
            | None => None
            | Some None => Some None
            | Some (Some (vbool _)) => Some None
            | Some (Some (vtabs env2 ey)) => Some None
            | Some (Some (vabs env2 ey)) =>
              match teval n env ex with
                | None => None
                | Some None => Some None
                | Some (Some vx) =>
                  teval n (vx::env2) ey
              end
          end
        | ttapp ef T1   =>
          match teval n env ef with
            | None => None
            | Some None => Some None
            | Some (Some (vbool _)) => Some None
            | Some (Some (vabs env2 ey)) => Some None
            | Some (Some (vtabs env2 ey)) =>
                teval n env2 ey
          end
      end
  end.

Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).


(* ---------- LR definitions  ---------- *)

Definition vtype := vl -> Prop.

Fixpoint val_type (V: list vtype) v T {struct T}: Prop :=
  match T, v with
  | TAny, _ =>
      True
  | TBool, vbool b =>
      True
  | TVar x, v =>
      exists vt,
      indexr x V = Some vt /\ vt v
  | TFun T1 T2, vabs H ty =>
      forall vx,
        val_type V vx T1 ->
        exists vy,
          tevaln (vx::H) ty vy /\
          val_type V vy T2
  | TAll T1 T2, vtabs H ty =>
      forall (vt: vtype),
        (forall v, vt v -> val_type V v T1) ->
        exists vy,
          tevaln H ty vy /\
          val_type (vt::V) vy T2
  | _,_ =>
      False
  end.

Definition exp_type H V t T :=
  exists v,
    tevaln H t v /\
    val_type V v T.


Definition env_type (H: venv) (G: tenv) (V: list vtype) (J: kenv) :=
  length H = length G /\
  length V = length J /\
    (forall x T,
      indexr x G = Some T ->
      exists v,
        indexr x H = Some v /\
        val_type V v T) /\
    (forall x T,
      indexr x J = Some T ->
      closed T (length J) /\
      exists vt,
        indexr x V = Some vt /\
        (forall v, vt v -> val_type V v T)).


Definition sem_stp G (J: kenv) T1 T2 :=
  forall H V v,
    env_type H G V J ->
    val_type V v T1 -> val_type V v T2.

Definition sem_type G J t T :=
  forall H V,
    env_type H G V J ->
    exp_type H V t T.


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


Lemma splice_acc: forall e1 a b c,
  splice a c (splice a b e1) =
  splice a (c+b) e1.
Proof. induction e1; intros; simpl; intuition.
  + bdestruct (i <? a); intuition.
    bdestruct (i <? a); intuition.
    bdestruct (b+i <? a); intuition.
  + specialize (IHe1_1 a b c). specialize (IHe1_2 a b c).
    rewrite IHe1_1. rewrite IHe1_2. auto.
  + specialize (IHe1_1 a b c). specialize (IHe1_2 a b c).
    rewrite IHe1_1. rewrite IHe1_2. auto.
Qed.

Lemma splice_acc': forall e1 a b c,
  splice (b+a) c (splice a b e1) =
  splice a (c+b) e1.
Proof. induction e1; intros; simpl; intuition.
  + bdestruct (i <? a); intuition.
    bdestruct (i <? a); intuition.
    bdestruct (i <? b+a); intuition.
    bdestruct (b + i <? b + a); intuition.
  + specialize (IHe1_1 a b c). specialize (IHe1_2 a b c).
    rewrite IHe1_1. rewrite IHe1_2. auto.
  + specialize (IHe1_1 a b c). specialize (IHe1_2 a b c).
    rewrite IHe1_1. rewrite IHe1_2. auto.
Qed.

Lemma splice_zero: forall e1 a,
  (splice a 0 e1) = e1.
Proof. intros. induction e1; simpl; intuition.
  + bdestruct (i <? a); intuition.
  + rewrite IHe1_1. rewrite IHe1_2. auto.
  + rewrite IHe1_1. rewrite IHe1_2. auto.
Qed.



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


(* ---------- helper lemmas: valt_weaken, subst, open  ---------- *)

Lemma valt_weaken: forall T V V1 vt v,
    val_type (V1++V) v T <-> val_type (V1++vt::V) v (splice (length V) 1 T).
Proof.
  intros T. induction T; intros.
  - simpl in *. split; eauto.
  - destruct v; simpl in *; split; eauto.
  - simpl in *. bdestruct (i <? length V); eauto; split; intros; eauto.
    + erewrite <-indexr_insert_lt. eauto. eauto.
    + erewrite <-indexr_insert_lt in H0. eauto. eauto.
    + erewrite <-indexr_insert_ge. eauto. eauto.
    + erewrite <-indexr_insert_ge in H0. eauto. eauto.
  - destruct v; simpl in *; split; intros; eauto.
    + destruct (H vx) as (vy & ? & VY). eapply IHT1; eauto.
      exists vy. split. eauto. eapply IHT2; eauto.
    + destruct (H vx) as (vy & ? & VY). eapply IHT1; eauto.
      exists vy. split. eauto. eapply IHT2; eauto.
  - destruct v; simpl in *; split; intros; eauto.
    + destruct (H vt0) as (vy & ? & VY).
      { intros. eapply IHT1. eapply H0. eauto. }
      exists vy. split. eauto. eapply IHT2 with (V1:=vt0::V1); eauto.
    + destruct (H vt0) as (vy & ? & VY).
      { intros. eapply IHT1. eapply H0. eauto. }
      exists vy. split. eauto. eapply IHT2 with (V1:=vt0::V1); eauto.
Qed.

Lemma valt_shrink: forall V vt v T,
    val_type (vt::V) v (splice (length V) 1 T) -> val_type V v T.
Proof.
  intros. eapply valt_weaken with (V:=V) (V1:=@nil vtype). eauto.
Qed.

Lemma valt_extend: forall V vt v T,
    val_type V v T -> val_type (vt::V) v (splice (length V) 1 T).
Proof.
  intros. edestruct valt_weaken with (V:=V) (V1:=@nil vtype). eauto.
Qed.

Lemma valt_shrink_mult: forall V1 V v T,
    val_type (V1++V) v (splice (length V) (length V1) T) -> val_type V v T.
Proof.
  intros V1. induction V1; intros. simpl in *. rewrite splice_zero in H. eauto.
  eapply IHV1. eapply valt_shrink. eauto.
  rewrite app_length. erewrite splice_acc'. eauto.
Qed.

Lemma valt_extend_mult: forall V1 V v T,
    val_type V v T -> val_type (V1++V) v (splice (length V) (length V1) T).
Proof.
  intros V1. induction V1; intros. simpl in *. rewrite splice_zero. eauto.
  eapply IHV1 in H. eapply valt_extend in H.
  rewrite app_length in H. erewrite splice_acc' in H. eauto.
Qed.


Lemma valt_subst_gen: forall T2 T1 v vt V V1,
    vt = (fun v => val_type V v T1) ->
    val_type (V1 ++ vt :: V) v T2 <->
      val_type (V1++V) v (subst T2 (length V) (splice (length V) (length V1) T1)).
Proof.
  intros T2. induction T2; intros.
  - simpl in *; split; eauto.
  - destruct v; simpl in *; split; eauto.
  - simpl in *. bdestruct (i =? length V); eauto; split; intros; eauto.
    (* Todo: annoying duplication due to destructing v *)
    + subst vt. destruct v; destruct H1 as (? & H2 & H3).
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
    + destruct (H0 vx) as (vy & ? & VY). eapply IHT2_1; eauto.
      exists vy. split. eauto. eapply IHT2_2; eauto.
    + destruct (H0 vx) as (vy & ? & VY). eapply IHT2_1; eauto.
      exists vy. split. eauto. eapply IHT2_2; eauto.
  - destruct v; simpl in *; split; intros; eauto.
    + destruct (H0 vt0) as (vy & ? & VY).
      { intros. eapply IHT2_1; eauto. }
      exists vy. split. eauto. edestruct IHT2_2 with (V1:=vt0::V1); eauto.
      clear H4. eapply H3 in VY. clear H3. simpl in VY.
      rewrite splice_acc. eauto.
    + destruct (H0 vt0) as (vy & ? & VY).
      { intros. eapply IHT2_1; eauto. }
      exists vy. split. eauto. edestruct IHT2_2 with (V1:=vt0::V1); eauto.
      rewrite splice_acc in VY.
      clear H3. eapply H4 in VY. simpl in VY.
      eauto.
Qed.

Lemma valt_subst: forall V vt v T1 T2,
    vt = (fun v => val_type V v T1) ->
    val_type (vt::V) v T2 -> val_type V v (subst T2 (length V) T1).
Proof.
  intros.
  edestruct valt_subst_gen with (V:=V) (V1:=@nil vtype).
  eauto. simpl in *. eapply H1 in H0. rewrite splice_zero in H0.
  eauto.
Qed.


(* ---------- LR helper lemmas  ---------- *)

Lemma envt_empty:
    env_type [] [] [] [].
Proof.
  intros. split. 2: split. 3: split.
  eauto. eauto. intros. inversion H. intros. inversion H.
Qed.

Lemma envt_extend: forall E G V J v1 T1,
    env_type E G V J ->
    val_type V v1 T1 ->
    env_type (v1::E) (T1::G) V J.
Proof.
  intros.
  remember H as WFE. clear HeqWFE.
  destruct H as (? & ? & ? & ?). split. 2: split. 3: split.
  simpl. eauto. simpl. eauto.
  intros x T IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX. subst T1.
    exists v1. split. rewrite <- H. rewrite indexr_head. eauto.
    eauto.
  - rewrite indexr_skip in IX; eauto.
    eapply WFE in IX as IX. destruct IX as (v2 & ? & ?).
    exists v2. split. rewrite indexr_skip; eauto. lia.
    eauto.
  - eauto.
Qed.

Lemma envt_extend_tabs: forall E G V J (vt1: vtype) T1,
    env_type E G V J ->
    (forall v, vt1 v -> val_type V v T1) ->
    closed T1 (length J) ->
    env_type E (map (splice (length V) 1) G) (vt1::V) (map (splice (length V) 1) (T1::J)).
Proof.
  intros.
  remember H as WFE. clear HeqWFE.
  destruct H as (HL & HV & HG & HJ). split. 2: split. 3: split.
  rewrite map_length. eauto. simpl. rewrite map_length. eauto.
  (* term env *)
  intros x T IX.
  eapply indexr_map' in IX. destruct IX as (T' & IX & ?).
  eapply WFE in IX as IX. destruct IX as (v2 & ? & ?).
  exists v2. split. eauto. subst T.
  eapply valt_extend in H3. eauto.
  (* type env *)
  intros x T IX.
  eapply indexr_map' in IX. destruct IX as (T' & IX & ?).
  subst T.
  bdestruct (x =? length J).
  - subst x. rewrite indexr_head in IX. inversion IX. subst T'.
    split. rewrite map_length. eapply closedt_splice. eauto.
    exists vt1. rewrite <-HV, indexr_head. split. eauto.
    intros. eapply valt_extend. eauto.
  - rewrite indexr_skip in IX; eauto.
    edestruct HJ as (CL & vt' & IX' & BOUND). eauto.
    split. rewrite map_length. eapply closedt_splice. eauto.
    exists vt'. split. rewrite indexr_skip. eauto. lia.
    intros. eapply valt_extend. eapply BOUND. eauto.
Qed.


(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_true: forall G J,
    sem_type G J ttrue TBool.
Proof.
  intros. intros E V WFE.
  exists (vbool true). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto.
Qed.

Lemma sem_false: forall G J,
    sem_type G J tfalse TBool.
Proof.
  intros. intros E V WFE.
  exists (vbool false). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto.
Qed.

Lemma sem_var: forall G J x T,
    indexr x G = Some T ->
    sem_type G J (tvar x) T.
Proof.
  intros. intros E V WFE.
  eapply WFE in H as IX. destruct IX as (v & IX & VX).
  exists v. split.
  - exists 0. intros. destruct n. lia. simpl. rewrite IX. eauto.
  - eauto.
Qed.

Lemma sem_app: forall G J f t T1 T2,
    sem_type G J f (TFun T1 T2) ->
    sem_type G J t T1 ->
    sem_type G J (tapp f t) T2.
Proof.
  intros ? ? ? ? ? ? HF HX. intros E V WFE.
  destruct (HF E V WFE) as (vf & STF & VF).
  destruct (HX E V WFE) as (vx & STX & VX).
  destruct vf; simpl in VF; try contradiction.
  edestruct (VF vx) as (vy & STY & VY). eauto.
  exists vy. split.
  - destruct STF as (n1 & STF).
    destruct STX as (n2 & STX).
    destruct STY as (n3 & STY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite STF, STX, STY. 2,3,4: lia.
    eauto.
  - eauto.
Qed.

Lemma sem_abs: forall G J t T1 T2,
    sem_type (T1::G) J t T2 ->
    sem_type G J (tabs t) (TFun T1 T2).
Proof.
  intros ? ? ? ? ? HY. intros E V WFE.
  assert (length E = length G) as L. eapply WFE.
  assert (length V = length J) as LV. eapply WFE.
  exists (vabs E t). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros ? VX.
    edestruct HY as (? & ? & ?). eapply envt_extend; eauto.
    eexists. split. eauto. eauto.
Qed.

Lemma sem_tapp: forall G J f T1 T2,
    sem_type G J f (TAll T1 T2) ->
    sem_type G J (ttapp f T1) (subst T2 (length J) T1).
Proof.
  intros ? ? ? ? ? HF. intros E V WFE.
  assert (length E = length G) as L. eapply WFE.
  assert (length V = length J) as LV. eapply WFE.
  destruct (HF E V WFE) as (vf & STF & VF).
  destruct vf; simpl in VF; try contradiction.
  edestruct (VF (fun v => val_type V v T1)) as (vy & STY & VY).
  { intros v0 Hv0. eauto. }
  exists vy. split.
  - destruct STF as (n1 & STF).
    destruct STY as (n3 & STY).
    exists (1+n1+n3). intros. destruct n. lia.
    simpl. rewrite STF, STY. 2,3: lia.
    eauto.
  - rewrite <- LV. eapply valt_subst. reflexivity. eauto.
Qed.


Lemma sem_tabs: forall G J t T1 T2,
    sem_type (map (splice (length J) 1) G) (map (splice (length J) 1) (T1::J)) t T2 ->
    closed T1 (length J) ->
    sem_type G J (ttabs t) (TAll T1 T2).
Proof.
  intros ? ? ? ? ? HY CL. intros E V WFE.
  assert (length E = length G) as L. eapply WFE.
  assert (length V = length J) as LV. eapply WFE.
  exists (vtabs E t). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros vt BOUND.
    destruct (HY E (vt::V)) as (? & ? & ?).
    rewrite <-LV. eapply envt_extend_tabs; eauto.
    eexists. split. eauto. eauto.
Qed.

(* ---------- LR subtyping compatibility lemmas  ---------- *)

Lemma sem_stp_any: forall G J T,
  sem_stp G J T TAny.
Proof.
  intros ? ? ? ? ? ? WFE V1. simpl. eauto.
Qed.

Lemma sem_stp_bool: forall G J,
  sem_stp G J TBool TBool.
Proof.
  intros ? ? ? ? ? WFE V1. eauto.
Qed.

Lemma sem_stp_fun: forall G J T1 T2 T3 T4,
  sem_stp G J T3 T1 ->
  sem_stp G J T2 T4 ->
  sem_stp G J (TFun T1 T2) (TFun T3 T4).
Proof.
  intros ? ? ? ? ? ? ST31 ST24. intros ? ? ? WFE V1.
  destruct v; simpl in *; eauto; intros.
  destruct (V1 vx) as (vy & EY & VY).
  eapply ST31; eauto.
  eexists vy. split. eauto.
  eapply ST24; eauto.
Qed.

Lemma sem_stp_varx: forall G J x,
  sem_stp G J (TVar x) (TVar x).
Proof.
  intros ? ? ? ? ? ? WFE V1. eauto.
Qed.

Lemma sem_stp_var: forall G J x U T,
    indexr x J = Some U ->
    sem_stp G J U T ->
    sem_stp G J (TVar x) T.
Proof.
  intros ? ? ? ? ? IX STU. intros H V v WFE VT.
  simpl in VT. destruct VT as (vt & IX' & VTv).
  remember WFE as WFE'. clear HeqWFE'.
  destruct WFE as (? & ? & ? & BOUNDS).
  edestruct BOUNDS as (CL & vt' & IX'' & BOUND). eauto.
  rewrite IX'' in IX'. inversion IX'. subst vt'.
  eapply STU; eauto.
Qed.

Lemma sem_stp_all: forall G J T1 T2 T3 T4,
  sem_stp G J T3 T1 ->
  sem_stp (map (splice (length J) 1) G) (map (splice (length J) 1) (T3::J)) T2 T4 ->
  closed T3 (length J) ->
  sem_stp G J (TAll T1 T2) (TAll T3 T4).
Proof.
  intros ? ? ? ? ? ? ST31 ST24 CL3. intros H V v WFE VT.
  destruct v; simpl in *; try contradiction.
  intros vt BOUND3.
  assert (BOUND1: forall v0, vt v0 -> val_type V v0 T1). {
    intros. eapply ST31; eauto.
  }
  edestruct VT as (vy & STY & VY). eauto.
  exists vy. split. eauto.
  assert (length V = length J) as LV. eapply WFE.
  eapply ST24; eauto.
  rewrite <-LV. eapply envt_extend_tabs; eauto.
Qed.


Lemma sem_sub: forall G J t T1 T2,
    sem_type G J t T1 ->
    sem_stp G J T1 T2 ->
    sem_type G J t T2.
Proof.
  intros ? ? ? ? ? H1 ST12. intros E V WFE.
  destruct (H1 E V) as (vy & ? & VY). eauto.
  eexists. split. eauto. eapply ST12; eauto.
Qed.

(* ---------- LR fundamental property  ---------- *)

Theorem stp_fundamental: forall G J T1 T2,
    stp J T1 T2 ->
    sem_stp G J T1 T2.
Proof.
  intros ? ? ? ? H. revert G. induction H; intros.
  - eapply sem_stp_any; eauto.
  - eapply sem_stp_bool; eauto.
  - eapply sem_stp_fun; eauto.
  - eapply sem_stp_varx; eauto.
  - eapply sem_stp_var; eauto.
  - eapply sem_stp_all; eauto.
Qed.

Theorem fundamental: forall G J t T,
    has_type G J t T ->
    sem_type G J t T.
Proof.
  intros ? ? ? ? W.
  induction W.
  - eapply sem_true; eauto.
  - eapply sem_false; eauto.
  - eapply sem_var; eauto.
  - eapply sem_app; eauto.
  - eapply sem_abs; eauto.
  - eapply sem_tapp; eauto.
  - eapply sem_tabs; eauto.
  - eapply sem_sub; eauto. eapply stp_fundamental; eauto.
Qed.

Corollary safety: forall t T,
  has_type [] [] t T ->
  exp_type [] [] t T.
Proof.
  intros. eapply fundamental in H as ST; eauto.
  destruct (ST [] []) as (v & ? & ?).
  eapply envt_empty.
  exists v. intuition.
Qed.


(* ---------- other properties  ---------- *)


(* Note: the 'closed' predicate is not used in the proofs, but we find
   it still useful to guarantee that types are syntactically well-formed *)

Lemma hast_closed: forall G J t T,
    (forall x T1, indexr x G = Some T1 -> closed T1 (length J)) ->
    has_type G J t T ->
    closed T (length J).
Proof.
  intros. induction H0; simpl in *; eauto.
  - eapply IHhas_type1. eauto.
  - split. eauto. eapply IHhas_type. intros.
    bdestruct (x =? length env). inversion H2. subst. eauto.
    eapply H. eauto.
  - eapply closedt_subst. eauto. eapply IHhas_type. eauto. eauto.
  - split. eauto.
    rewrite map_length in IHhas_type.
    eapply IHhas_type. intros. eapply indexr_map' in H2.
    destruct H2 as (?&?&?). subst.
    eapply closedt_splice. eauto.
Qed.



(* ---------- examples  ---------- *)

(* polymorphic id function: [T<:Any](x:T) -> T  *)

Definition polyId := ttabs (tabs (tvar 0)).

Definition polyIdType := TAll TAny (TFun (TVar 0) (TVar 0)).

Lemma polyIdHasType:
  has_type [] [] polyId polyIdType.
Proof.
  eapply t_tabs. eapply t_abs. eapply t_var.
  simpl. eauto. simpl. eauto. simpl. eauto.
Qed.

Lemma polyIdAppliedHasType:
  has_type [] [] (ttapp polyId TBool) (TFun TBool TBool).
Proof.
  replace (TFun TBool TBool) with (subst (TFun (TVar 0) (TVar 0)) 0 TBool).
  eapply t_tapp.
  eapply t_sub. eapply polyIdHasType.
  eapply s_all. eapply s_any.
  simpl. eapply s_fun; eapply s_varx.
  simpl. eauto.
  simpl. eauto.
  simpl. eauto.
  simpl. eauto.
Qed.


End STLC.
