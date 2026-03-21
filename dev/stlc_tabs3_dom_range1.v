(* Full safety for STLC *)

(*

An LR-based termination and semantic soundness proof for STLC.

Canonical big-step cbv semantics.

Type abstraction and application (System F)

Notes:

- We use de Bruijn levels to model bindings, both for
  terms and also for types. Substitution needs to adjust
  levels when going under binders.


THIS FILE (via stlc_tabs3.v):
- add TDom, TRange plus associated t_app_dom_range, 
  t_stp_dom, t_stp_range rules
- val_type is parameterized with a selector string to 
  pick the dom/range components of a function type.
  This follows the design here: 
    https://github.com/TiarkRompf/minidot/blob/master/ecoop17/dsubsup_total.v#L325
- an alternative design would be this:
    https://github.com/TiarkRompf/minidot/blob/master/ecoop17/dsubsup_total_rec.v#L412

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
  | TDom   : ty -> ty
  | TRange : ty -> ty
  | TImg   : ty -> ty -> ty
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
  | TDom T4 => closed T4 n
  | TRange T4 => closed T4 n
  | TImg T3 T4 => closed T3 n /\ closed T4 n
  end.

Fixpoint splice n l (T : ty) {struct T} : ty :=
  match T with
  | TAny => TAny
  | TBool => TBool
  | TVar x => TVar (if x <? n then x else l+x)
  | TFun T3 T4 => TFun (splice n l T3) (splice n l T4)
  | TAll T3 T2   => TAll (splice n l T3) (splice n l T2)
  | TDom T2 => TDom (splice n l T2)
  | TRange T2 => TRange (splice n l T2)
  | TImg T3 T4 => TImg (splice n l T3) (splice n l T4)
  end.

Fixpoint subst T1 n T2 {struct T1} : ty :=
  match T1 with
  | TAny => TAny
  | TBool => TBool
  | TVar x => if x =? n then T2 else if x <? n then TVar x else TVar (x-1)
  | TFun T3 T4 => TFun (subst T3 n T2) (subst T4 n T2)
  | TAll T3 T4 => TAll (subst T3 n T2) (subst T4 n (splice n 1 T2))
  | TDom T4 => TDom (subst T4 n T2)
  | TRange T4 => TRange (subst T4 n T2)
  | TImg T3 T4 => TImg (subst T3 n T2) (subst T4 n T2)
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
(* non-standard rules: *)
| s_dom_sub_right: forall J T1 T2,
    stp J T1 (TDom (TFun T1 T2))
| s_dom_sub_left: forall J T1 T2,
    stp J (TDom (TFun T1 T2)) T1
| s_range_sub_right: forall J T1 T2,
    stp J T2 (TRange (TFun T1 T2))
| s_range_sub_left: forall J T1 T2,
    stp J (TRange (TFun T1 T2)) T2
| s_dom_congr: forall J T1 T2,
    stp J T1 T2 ->
    stp J (TDom T2) (TDom T1)
| s_range_congr: forall J T1 T2,
    stp J T1 T2 ->
    stp J (TRange T1) (TRange T2)
. (* TODO *)

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
| t_tapp: forall env J f (* t *) T1 T2,
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
(* non-standard rules: *)
| t_app_dom_range: forall env J f t TF,
    has_type env J f TF ->
    has_type env J t (TDom TF) ->
    has_type env J (tapp f t) (TRange TF)
| t_stp_dom: forall env J t T1 T2,
    has_type env J t T1 ->
    closed T2 (length J) ->
    has_type env J t (TDom (TFun T1 T2))
| t_stp_range: forall env J t T1 T2,
    has_type env J t (TRange (TFun T1 T2)) ->
    has_type env J t T2
(* preliminary rules for TImg: *)
| t_app_dom_img: forall env J f t TF T1,
    has_type env J f TF ->
    has_type env J t T1 ->
    stp J T1 (TDom TF) ->
    has_type env J (tapp f t) (TImg TF T1)
| t_stp_img: forall env J t T1 T1' T2,
    has_type env J t (TImg (TFun T1 T2) T1') ->
    has_type env J t (TRange (TFun T1 T2))
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

Inductive sel: Type :=
| sl_dom: sel
| sl_range: sel
.

Fixpoint pos s :=
  match s with
    | nil => true
    | sl_range :: i => pos i
    | sl_dom :: i => negb (pos i)
  end.


Definition vtype := vl -> list sel -> Prop.


Definition likeFunctionType (vt: vtype) :=
  forall i v,
    vt v i ->
    forall vx,
      vt vx (i++[sl_dom]) ->
      exists H' ty', v = vabs H' ty' /\
      exists vy,
        tevaln (vx::H') ty' vy /\
          vt vy (i++[sl_range]).


(* --- alternative: this is not quite right yet --- *)

Definition vt_fun (vt1 vt2: vtype): vtype :=
  fun v i =>
    match i, v with
    | sl_root, vabs H' ty' =>
        forall vx,
          vt1 vx sl_root  ->
          exists vy,
            tevaln (vx::H') ty' vy /\
              vt2 vy sl_root
    | sl_dom:: i, v =>
        vt1 v i
    | sl_range:: i, v =>
        vt2 v i
    | _, _ => False
    end.

Definition vt_dom (vt1: vtype): vtype :=
  fun v i =>
    vt1 v (sl_dom::i).

Definition vt_range (vt1: vtype): vtype :=
  fun v i =>
    vt1 v (sl_range::i).

Definition likeFunctionType1 (vt: vtype) :=
  forall v i, vt_fun (vt_dom vt) (vt_range vt) v i -> vt v i.

(* --- end alternative --- *)


Fixpoint val_type (V: list vtype) v T i {struct T}: Prop :=
  match T, i, v with
  | TBool, nil, vbool b =>  
      True
  | TVar x, i, v =>
      exists vt, 
      indexr x V = Some vt /\ vt v i
  | TFun T1 T2, nil, vabs H ty =>
      forall vx,
        val_type V vx T1 nil ->
        exists vy,
          tevaln (vx::H) ty vy /\
          val_type V vy T2 nil
  | TAll T1 T2, nil, vtabs H ty =>
      forall vt,
        likeFunctionType vt ->
        exists vy,
          tevaln H ty vy /\
          val_type (vt::V) vy T2 nil
  | TDom TF, i, v =>
      val_type V v TF (sl_dom::i)
  | TRange TF, i, v =>
      val_type V v TF (sl_range::i)
  | TImg TF T1, i, v =>
      (* TODO: T1? *)
      val_type V v TF (sl_range::i)
  | TFun T1 T2, sl_dom:: k, v =>
      val_type V v T1 k
  | TFun T1 T2, sl_range:: k, v =>
      val_type V v T2 k
  | TAny, i, v =>
      pos i = true
  | TBool, nil, v =>
      False
  | TAll T1 T2, nil, v =>
      False
  | TBool, i, v =>  
      pos i = true
  | TAll T1 T2, i, v =>  
      pos i = true
  | _,_,_ =>
      False
  end.

Definition exp_type H V t T :=
  exists v,
    tevaln H t v /\
    val_type V v T nil.


Definition env_type (H: venv) (G: tenv) (V: list vtype) (J: kenv) :=
  length H = length G /\
  length V = length J /\
    (forall x T,
      indexr x G = Some T ->
      exists v,
        indexr x H = Some v /\
        val_type V v T nil) /\
    (forall x T,
      indexr x J = Some T ->
      closed T (length J) /\
      exists vt,
        indexr x V = Some vt /\
        likeFunctionType vt /\
        (forall v, vt v nil -> val_type V v T nil)).


Definition sem_stp G (J: kenv) T1 T2 :=
  forall H V v i,
    env_type H G V J ->
    if (pos i) then
      val_type V v T1 i -> val_type V v T2 i
    else
      val_type V v T2 i -> val_type V v T1 i.

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
  - intuition. eapply IHT1_1 in H1; eauto. eapply IHT1_2 in H2; eauto. 
Qed.

Lemma closedt_splice: forall T1 n l n1,
    closed T1 n1 -> 
    closed (splice n l T1) (l+n1).
Proof.
  intros T1. induction T1; intros; simpl in *; eauto.
  - bdestruct (i <? n). simpl. lia. simpl. lia.
  - intuition.
  - replace (S (l+n1)) with (l+(S n1)). intuition. lia.
  - intuition. 
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
  - intuition.
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
  + specialize (IHe1 a b c).
    rewrite IHe1. eauto.
  + specialize (IHe1 a b c).
    rewrite IHe1. eauto.
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
  + specialize (IHe1 a b c).
    rewrite IHe1. auto.
  + specialize (IHe1 a b c).
    rewrite IHe1. auto.
  + specialize (IHe1_1 a b c). specialize (IHe1_2 a b c).
    rewrite IHe1_1. rewrite IHe1_2. auto.
Qed.

Lemma splice_zero: forall e1 a,
  (splice a 0 e1) = e1.
Proof. intros. induction e1; simpl; intuition.
  + bdestruct (i <? a); intuition.
  + rewrite IHe1_1. rewrite IHe1_2. auto.
  + rewrite IHe1_1. rewrite IHe1_2. auto.
  + rewrite IHe1. auto.
  + rewrite IHe1. auto.
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

Lemma valt_weaken: forall T V V1 vt v k,
    val_type (V1++V) v T k <-> val_type (V1++vt::V) v (splice (length V) 1 T) k.
Proof.
  intros T. induction T; intros. 
  - destruct v; simpl in *; split; eauto.
  - destruct v; simpl in *; split; eauto.
  - simpl in *. bdestruct (i <? length V); eauto; split; intros; eauto.
    + erewrite <-indexr_insert_lt. eauto. eauto. 
    + erewrite <-indexr_insert_lt in H0. eauto. eauto. 
    + erewrite <-indexr_insert_ge. eauto. eauto.
    + erewrite <-indexr_insert_ge in H0. eauto. eauto.
  - destruct k; simpl in *. {
    destruct v; simpl in *; split; intros; eauto.
    + destruct (H vx) as (vy & ? & VY). eapply IHT1; eauto. 
      exists vy. split. eauto. eapply IHT2; eauto. 
    + destruct (H vx) as (vy & ? & VY). eapply IHT1; eauto.
      exists vy. split. eauto. eapply IHT2; eauto. }
    destruct s. destruct v; eapply IHT1; eauto.
    destruct v; eapply IHT2; eauto. 
  - destruct v,k; simpl in *; split; intros; eauto.
    + destruct (H vt0) as (vy & ? & VY). eauto.
      exists vy. split. eauto. eapply IHT2 with (V1:=vt0::V1); eauto. 
    + destruct (H vt0) as (vy & ? & VY). eauto. 
      exists vy. split. eauto. eapply IHT2 with (V1:=vt0::V1); eauto. 
  - destruct v; simpl in *; eapply IHT; eauto. 
  - destruct v; simpl in *; eapply IHT; eauto. 
  - destruct v; simpl in *; eapply IHT1; eauto. 
Qed.

Lemma valt_shrink: forall V vt v T k,
    val_type (vt::V) v (splice (length V) 1 T) k -> val_type V v T k.
Proof.
  intros. eapply valt_weaken with (V:=V) (V1:=@nil vtype). eauto.
Qed.

Lemma valt_extend: forall V vt v T k,
    val_type V v T k -> val_type (vt::V) v (splice (length V) 1 T) k.
Proof.
  intros. edestruct valt_weaken with (V:=V) (V1:=@nil vtype). eauto.
Qed.

Lemma valt_shrink_mult: forall V1 V v T k,
    val_type (V1++V) v (splice (length V) (length V1) T) k -> val_type V v T k.
Proof.
  intros V1. induction V1; intros. simpl in *. rewrite splice_zero in H. eauto.
  eapply IHV1. eapply valt_shrink. eauto. 
  rewrite app_length. erewrite splice_acc'. eauto. 
Qed.

Lemma valt_extend_mult: forall V1 V v T k,
    val_type V v T k -> val_type (V1++V) v (splice (length V) (length V1) T) k.
Proof.
  intros V1. induction V1; intros. simpl in *. rewrite splice_zero. eauto.
  eapply IHV1 in H. eapply valt_extend in H.
  rewrite app_length in H. erewrite splice_acc' in H. eauto. 
Qed.


Lemma valt_subst_gen: forall T2 T1 v vt V V1 k,
    vt = (fun v k => val_type V v T1 k) ->
    val_type (V1 ++ vt :: V) v T2 k <->
      val_type (V1++V) v (subst T2 (length V) (splice (length V) (length V1) T1)) k.
Proof.
  intros T2. induction T2; intros. 
  - destruct v; simpl in *; split; eauto.
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
  - destruct k. destruct v; simpl in *; split; intros; eauto.
    + destruct (H0 vx) as (vy & ? & VY). eapply IHT2_1; eauto.
      exists vy. split. eauto. eapply IHT2_2; eauto.
    + destruct (H0 vx) as (vy & ? & VY). eapply IHT2_1; eauto.
      exists vy. split. eauto. eapply IHT2_2; eauto.
    + destruct s; simpl.
      destruct v; eapply IHT2_1; eauto.
      destruct v; eapply IHT2_2; eauto.
  - destruct k. destruct v; simpl in *; split; intros; eauto.
    + destruct (H0 vt0) as (vy & ? & VY). eauto.
      exists vy. split. eauto. edestruct IHT2_2 with (V1:=vt0::V1); eauto.
      clear H4. eapply H3 in VY. clear H3. simpl in VY.
      rewrite splice_acc. eauto.
    + destruct (H0 vt0) as (vy & ? & VY). eauto.
      exists vy. split. eauto. edestruct IHT2_2 with (V1:=vt0::V1); eauto.
      rewrite splice_acc in VY. 
      clear H3. eapply H4 in VY. simpl in VY.
      eauto.
    + destruct s; simpl.
      destruct v; simpl; intuition.
      destruct v; simpl; intuition.
  - destruct v; simpl in *; eapply IHT2; eauto. 
  - destruct v; simpl in *; eapply IHT2; eauto. 
  - destruct v; simpl in *; eapply IHT2_1; eauto. 
Qed.

Lemma valt_subst: forall V vt v T1 T2 k,
    vt = (fun v k => val_type V v T1 k) ->
    val_type (vt::V) v T2 k -> val_type V v (subst T2 (length V) T1) k.
Proof.
  intros.
  edestruct valt_subst_gen with (V:=V) (V1:=@nil vtype).
  eauto. simpl in *. eapply H1 in H0. rewrite splice_zero in H0.
  eauto.
Qed.

Lemma pos_app: forall i,
    pos (i++[sl_dom]) = negb (pos i).
Proof.
  intros i. induction i.
  - simpl. eauto.
  - simpl. destruct a. simpl.
    rewrite IHi. eauto. eauto.
Qed.

Lemma valt_functionally: forall T H G V J,
    env_type H G V J ->
    likeFunctionType (fun v i => val_type V v T i).
Proof.
  intros. induction T; simpl; intros ?????.
  - (* any *)
    rewrite pos_app in *. rewrite H1 in H2. inversion H2. 
  - (* bool *)
    destruct i; simpl in *. inversion H2. 
    destruct s; rewrite pos_app, H1 in H2; inversion H2.
  - (* var *)
    destruct H1 as (?&?&?). destruct H2 as (?&?&?).
    assert (length V = length J). eapply H0. 
    assert (i < length J). eapply indexr_var_some' in H1. lia.
    eapply indexr_var_some in H6. destruct H6 as (T & ?).
    eapply H0 in H6. destruct H6 as (vt & ? & IF).
    rewrite H6 in H2, H1. inversion H1. inversion H2. subst x x0.
    edestruct IF as (?&?&?&?&?&?). 2: eauto. eauto.
    eexists _,_. split. eauto. eexists. split. eauto. eexists. split. eauto. eauto.
  - (* fun *)
    destruct i. {destruct v; try contradiction.
    eexists _,_. split. eauto. eauto.}

    simpl in *. destruct s.
    eapply IHT1. eauto. eauto.
    eapply IHT2. eauto. eauto.
  - (* all *)
    destruct i; simpl in *. inversion H2. 
    destruct s; rewrite pos_app, H1 in H2; inversion H2.
  - (* dom *)
    edestruct IHT as (?&?&?&?). eapply H1. eauto.
    eexists _,_. split. eauto. eauto. 
  - (* range *)
    edestruct IHT as (?&?&?&?). eapply H1. eauto.
    eexists _,_. split. eauto. eauto. 
  - (* range *)
    edestruct IHT1 as (?&?&?&?). eapply H1. eauto.
    eexists _,_. split. eauto. eauto. 
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
    val_type V v1 T1 nil ->
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

Lemma envt_extend_tabs: forall E G V J vt1 T1,
    env_type E G V J ->
    likeFunctionType vt1 ->
    (forall v, vt1 v nil -> val_type V v T1 nil) ->
    closed T1 (length J) ->
    env_type E (map (splice (length J) 1) G) (vt1::V) (map (splice (length J) 1) (T1::J)).
Proof.
  intros. 
  remember H as WFE. clear HeqWFE.
  destruct H as (? & ? & ? & ?). split. 2: split. 3: split.
  rewrite map_length. eauto. simpl. eauto. 
  intros x T IX.
  eapply indexr_map' in IX. destruct IX as (T' & IX & ?). 
  eapply WFE in IX as IX. destruct IX as (v2 & ? & ?).
  exists v2. split. eauto. subst T. 
  eapply valt_extend in H6. eauto.
  intros. bdestruct (x =? length J).
  subst x. exists vt1. rewrite <-H1, indexr_head. split; eauto.
  rewrite indexr_skip in H4. rewrite indexr_skip. eapply H3. eauto. lia. lia. 
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

Lemma sem_app_range: forall G J f t T1 T2,
    sem_type G J f (TFun T1 T2) ->
    sem_type G J t (TDom (TFun T1 T2)) ->
    sem_type G J (tapp f t) (TRange (TFun T1 T2)).
Proof.
  intros ? ? ? ? ? ? HF HX. intros E V WFE.
  destruct (HF E V WFE) as (vf & STF & VF).
  destruct (HX E V WFE) as (vx & STX & VX).
  destruct vf; simpl in VF; try contradiction.
  simpl in VX. 
  edestruct (VF vx) as (vy & STY & VY). destruct vx; eapply VX.
  exists vy. split.
  - destruct STF as (n1 & STF).
    destruct STX as (n2 & STX).
    destruct STY as (n3 & STY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite STF, STX, STY. 2,3,4: lia.
    eauto.
  - simpl. destruct vy; eauto.
Qed.

Lemma sem_app_dom_img: forall G J f t TF T1,
    sem_type G J f TF ->
    sem_type G J t T1 ->
    sem_stp G J T1 (TDom TF) ->
    sem_type G J (tapp f t) (TImg TF T1).
Proof.
  intros ? ? ? ? ? ? HF HX STPF. intros E V WFE.
  destruct (HF E V WFE) as (vf & STF & VF).
  destruct (HX E V WFE) as (vx & STX & VX).

  specialize (STPF _ _ vx [] WFE). simpl in STPF.
  
  eapply STPF in VX. simpl in VX.

  edestruct valt_functionally. eauto.
  eapply VF. eapply VX.

  destruct H as (?&?& vy & STY & VY). subst vf. 
  
  exists vy. split. 
  - destruct STF as (n1 & STF).
    destruct STX as (n2 & STX).
    destruct STY as (n3 & STY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite STF, STX, STY. 2,3,4: lia.
    eauto.
  - simpl. eapply VY.
Qed.

Lemma sem_app_dom_range: forall G J f t TF,
    sem_type G J f TF ->
    sem_type G J t (TDom TF) ->
    sem_type G J (tapp f t) (TRange TF).
Proof.
  intros ? ? ? ? ? HF HX. intros E V WFE.
  destruct (HF E V WFE) as (vf & STF & VF).
  destruct (HX E V WFE) as (vx & STX & VX).

  simpl in VX.

  edestruct valt_functionally. eauto.
  eapply VF. eapply VX.

  destruct H as (?&?& vy & STY & VY). subst vf. 
  
  exists vy. split. 
  - destruct STF as (n1 & STF).
    destruct STX as (n2 & STX).
    destruct STY as (n3 & STY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite STF, STX, STY. 2,3,4: lia.
    eauto.
  - simpl. eapply VY.
Qed.

Lemma sem_stp_dom: forall G J t T1 T2,
    sem_type G J t T1 ->
    sem_type G J t (TDom (TFun T1 T2)).
Proof.
  intros ? ? ? ? ? HX. intros E V WFE.
  destruct (HX E V WFE) as (vx & STX & VX).
  exists vx. split. eauto. simpl. eauto. 
Qed.

Lemma sem_stp_range: forall G J t T1 T2,
    sem_type G J t (TRange (TFun T1 T2)) ->
    sem_type G J t T2.
Proof.
  intros ? ? ? ? ? HX. intros E V WFE.
  destruct (HX E V WFE) as (vx & STX & VX).
  exists vx. split. eauto.
  destruct vx; eapply VX.
Qed.

Lemma sem_stp_img: forall G J t T1 T1' T2,
    sem_type G J t (TImg (TFun T1 T2) T1') ->
    sem_type G J t (TRange (TFun T1 T2)).
Proof.
  intros ? ? ? ? ? ? HX. intros E V WFE.
  destruct (HX E V WFE) as (vx & STX & VX).
  exists vx. split. eauto.
  destruct vx; eapply VX.
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

Lemma sem_tapp: forall G J f (* t *) T1 T2,
    sem_type G J f (TAll T1 T2) ->
    closed T1 (length J) ->
    sem_type G J (ttapp f T1) (subst T2 (length J) T1).
Proof. 
  intros ? ? ? ? ? HF CL1. intros E V WFE.
  assert (length E = length G) as L. eapply WFE.
  assert (length V = length J) as LV. eapply WFE.
  destruct (HF E V WFE) as (vf & STF & VF).
  destruct vf; simpl in VF; try contradiction.
  edestruct VF as (vy & STY & VY).
  eapply valt_functionally. eauto. eauto. 
  exists vy. split.
  - destruct STF as (n1 & STF).
    destruct STY as (n3 & STY).
    exists (1+n1+n3). intros. destruct n. lia.
    simpl. rewrite STF, STY. 2,3: lia.
    eauto.
  - rewrite <- LV. eapply valt_subst. reflexivity. eauto. 
Qed.


Lemma sem_tabs: forall G J t T1 T2,
    sem_type (map (splice (length J) 1) G) (T1::J) t T2 ->
    sem_type G J (ttabs t) (TAll T1 T2).
Proof.
  intros ? ? ? ? ? HY. intros E V WFE.
  assert (length E = length G) as L. eapply WFE.
  assert (length V = length J) as LV. eapply WFE.
  exists (vtabs E t). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros. 
    destruct (HY E (vt::V)) as (? & ? & ?).
    rewrite <-LV. eapply envt_extend_tabs; eauto.
    eexists. split. eauto. eauto. 
Qed.

(* ---------- LR subtyping compatibility lemmas  ---------- *)

Lemma sem_stp_any: forall G J T,
  sem_stp G J T TAny.
Proof.
  intros ? ? ? ? ? ? ? WFE. remember (pos i). destruct b; intros V1. 
  - simpl. eauto.
  - simpl in V1. congruence. 
Qed.

Lemma sem_stp_bool: forall G J,
  sem_stp G J TBool TBool.
Proof.
  intros ? ? ? ? ? ? WFE. remember (pos i). destruct b; intros V1; eauto.
Qed.

Lemma sem_stp_fun: forall G J T1 T2 T3 T4,
  sem_stp G J T3 T1 ->
  sem_stp G J T2 T4 ->
  sem_stp G J (TFun T1 T2) (TFun T3 T4).
Proof.
  intros ? ? ? ? ? ? ST31 ST24. intros ? ? ? ? WFE.
  destruct i; try destruct s; simpl; try intros V1.
  - destruct v; simpl in *; eauto; intros.
    destruct (V1 vx) as (vy & EY & VY).
    eapply (ST31 _ _ _ []); eauto.
    eexists vy. split. eauto.
    eapply (ST24 _ _ _ []); eauto.
  - specialize (ST31 _ _ v i WFE). destruct (pos i); simpl; eapply ST31.
  - eapply ST24. eauto. 
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

Lemma sem_stp_dom_sub_right: forall G J T1 T2,
  sem_stp G J T1 (TDom (TFun T1 T2)).
Proof.
  intros ? ? ? ?. intros ? ? ? ? WFE.
  simpl. destruct (pos i); eauto.
Qed.

Lemma sem_stp_dom_sub_left: forall G J T1 T2,
  sem_stp G J (TDom (TFun T1 T2)) T1.
Proof.
  intros ? ? ? ?. intros ? ? ? ? WFE.
  simpl. destruct (pos i); eauto.
Qed.

Lemma sem_stp_range_sub_left: forall G J T1 T2,
  sem_stp G J (TRange (TFun T1 T2)) T2.
Proof.
  intros ? ? ? ?. intros ? ? ? ? WFE.
  simpl. destruct (pos i); eauto.
Qed.

Lemma sem_stp_range_sub_right: forall G J T1 T2,
  sem_stp G J T2 (TRange (TFun T1 T2)).
Proof.
  intros ? ? ? ?. intros ? ? ? ? WFE.
  simpl. destruct (pos i); eauto.
Qed.

Lemma sem_stp_dom_congr: forall G J T1 T2,
  sem_stp G J T1 T2 ->
  sem_stp G J (TDom T2) (TDom T1).

Proof.
  intros ? ? ? ? ST12. intros ? ? ? ? WFE.
  specialize (ST12 _ _ v (sl_dom::i) WFE). simpl in *.
  destruct (pos i); eapply ST12. 
Qed.

Lemma sem_stp_range_congr: forall G J T1 T2,
  sem_stp G J T1 T2 ->
  sem_stp G J (TRange T1) (TRange T2).
Proof.
  intros ? ? ? ? ST12. intros ? ? ? ? WFE.
  specialize (ST12 _ _ v (sl_range::i) WFE). simpl in *.
  destruct (pos i); eapply ST12. 
Qed.


Theorem stp_fundamental: forall G J T1 T2,
    stp J T1 T2 ->
    sem_stp G J T1 T2.
Proof.
  intros. induction H.
  - eapply sem_stp_any; eauto. 
  - eapply sem_stp_bool; eauto. 
  - eapply sem_stp_fun; eauto.
  - eapply sem_stp_dom_sub_right; eauto.
  - eapply sem_stp_dom_sub_left; eauto.
  - eapply sem_stp_range_sub_right; eauto. 
  - eapply sem_stp_range_sub_left; eauto. 
  - eapply sem_stp_dom_congr; eauto.
  - eapply sem_stp_range_congr; eauto. 
Qed.


Lemma sem_sub: forall G J t T1 T2,
    sem_type G J t T1 ->
    sem_stp G J T1 T2 ->
    sem_type G J t T2.
Proof.
  intros ? ? ? ? ? H1 ST12. intros E V WFE.
  destruct (H1 E V) as (vy & ? & VY). eauto.
  eexists. split. eauto. eapply (ST12 _ _ _ []). eapply WFE. eauto. 
Qed.

(* ---------- LR fundamental property  ---------- *)

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
  - eapply sem_app_dom_range; eauto.
  - eapply sem_stp_dom; eauto.
  - eapply sem_stp_range; eauto.
  - eapply sem_app_dom_img; eauto. eapply stp_fundamental; eauto.
  - eapply sem_stp_img; eauto. 
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
  - split. eauto. eapply IHhas_type. intros. eapply indexr_map' in H2.
    destruct H2 as (?&?&?). subst.
    eapply closedt_splice. eauto.
  - eapply IHhas_type. eauto. 
  - eapply IHhas_type. eauto. 
Qed.



(* ---------- examples  ---------- *)

(* polymorphic id function: [T:*](x:T) -> T  *)

Definition polyId := ttabs (tabs (tvar 0)). 

Definition polyIdType := TAll TBool(* TODO: TAny!*) (TFun (TVar 0) (TVar 0)). 

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
  eapply t_tapp. eapply polyIdHasType. simpl. eauto. simpl. eauto.
Qed.


(* polymorphic eta expansion with dom and range: [F:*](f: F)(x: dom(F)) -> range(F)  *)

Definition idFun := tabs (tvar 0).

Definition etaFun := ttabs (tabs (tabs (tapp (tvar 0) (tvar 1)))).

Definition etaFunType' := TFun (TVar 0) (TFun (TDom (TVar 0)) (TRange (TVar 0))).

Definition etaFunType := TAll (TFun TBool TBool)(* TODO TAny! *) etaFunType'.

Lemma etaHasType:
  has_type [] [] etaFun etaFunType.
Proof.
  eapply t_tabs. eapply t_abs. eapply t_abs.
  eapply t_app_dom_range. eapply t_var. simpl. eauto. eapply t_var. simpl. eauto. 
  simpl. eauto. simpl. eauto. simpl. eauto.
Qed.

Lemma etaAppliedHasType:
  has_type [] [] (ttapp etaFun (TFun TBool TBool)) (subst etaFunType' 0 (TFun TBool TBool)).
Proof.
  eapply t_tapp. eapply etaHasType. simpl. eauto. 
Qed.

Lemma etaWithArgHasType:
  has_type [] [] (tapp (tapp (ttapp etaFun (TFun TBool TBool)) idFun) ttrue) TBool.
Proof.
  eapply t_stp_range. 
  eapply t_app. 2: { eapply t_stp_dom with (T2:=TBool). eapply t_true. simpl. eauto. }
  eapply t_app. 2: { eapply t_abs with (T1:=TBool). eapply t_var. simpl. eauto. simpl. eauto. }
  specialize etaAppliedHasType. intros. simpl in H. eauto. 
Qed.


End STLC.
