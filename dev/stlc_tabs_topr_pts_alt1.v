(* Full safety for System F-Omega (PTS-style) *)

(*

An LR-based termination and semantic soundness proof.

Canonical big-step cbv semantics.

Combining type abstraction and type operators (System F-Omega).


THIS FILE (via stlc_tabs_topr.v):
- eliminate separate kn and ty types, merge into tm
- TStar : ty (replaces KTpe), TBox : ty (sort of kinds)
- TKArr : ty -> ty -> ty (replaces KArr)
- val_sort replaces val_kind, recurses on ty syntax

A FEW GLITCHES:
- tm:ttapp needs to carry the kind of the argument type (T1:K1)
- has_type:t_tapp needs to carry has_kind (TAll T1 T2) TStar
- eq_typeq_beta needs has_kind (ttabs K1 T1 (TFun K1 K2)
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

Module STLC.

(* ---------- language syntax ---------- *)

Definition id := nat.

Inductive tm : Type :=
  | TStar  : tm
  | TBox   : tm

  | TBool  : tm
  | TVar   : id -> tm
  | TFun   : tm -> tm -> tm  
  | TAll   : tm -> tm -> tm

(*| TKArr  : tm -> tm -> tm  (* TFun *)
  | TTAbs  : tm -> tm -> tm  (* tabs *)
  | TTApp  : tm -> tm -> tm  (* tapp *) *)

  | ttrue  : tm
  | tfalse : tm
  | tvar   : id -> tm
  | tapp   : tm -> tm -> tm
  | tabs   : tm -> tm
  | ttapp  : tm -> tm(*ty!*) -> tm(*kn*)  -> tm (* K is temporary!*)
  | ttabs  : tm -> tm -> tm
.

Inductive vl: Type :=
  | vbool  :  bool -> vl
  | vabs   :  list vl -> tm -> vl
  | vtabs  :  list vl -> tm -> vl
.

(* the interpretation of kind, which defines the set at * *)
Definition tpe := vl -> Prop.
Definition venv := list vl.
Definition tenv := list tm. (*ty*)
Definition kenv := list tm. (*ty*)

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.
#[global] Hint Unfold kenv.


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
      | ttabs _ y    => Some (Some (vtabs env y))
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
      | ttapp ef T1 _  =>
          match teval n env ef with
          | None => None
          | Some None => Some None
          | Some (Some (vbool _)) => Some None
          | Some (Some (vabs env2 ey)) => Some None
          | Some (Some (vtabs env2 ey)) =>
              teval n env2 ey
          end
      | _ => Some None
      end
  end.

Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).


(* ---------- substitution on types ---------- *)

Fixpoint splice (i: nat) (n:nat) (t: tm): tm :=
  match t with
  | TStar         => TStar
  | TBox          => TBox
  | TBool         => TBool
  | TVar x        => TVar (if x <? i then x else x + n)
  | TFun t1 t2    => TFun (splice i n t1) (splice i n t2)
  | TAll k t      => TAll k (splice i n t)
(*| TKArr t1 t2   => TKArr (splice i n t1) (splice i n t2)
  | TTAbs k t     => TTAbs k (splice i n t)
  | TTApp t1 t2   => TTApp (splice i n t1) (splice i n t2) *)
  | ttrue         => ttrue
  | tfalse        => tfalse
  | tvar x        => tvar x
  | tapp t1 t2    => tapp (splice i n t1) (splice i n t2)
  | tabs t1       => tabs (splice i n t1)
  | ttapp t1 t2 k  => ttapp (splice i n t1) (splice i n t2) k
  | ttabs t1 t2   => ttabs t1(*?*) (splice i n t2)
  end.

Fixpoint subst (t: tm) (i: nat) (u:tm): tm :=
  match t with
  | TStar         => TStar
  | TBox          => TBox
  | TBool         => TBool
  | TVar x        => if Nat.eq_dec x i then u else TVar (if x <? i then x else x-1)
  | TFun t1 t2    => TFun (subst t1 i u) (subst t2 i u)
  | TAll k t      => TAll k (subst t i (splice i 1 u))
(*| TKArr t1 t2   => TKArr (subst t1 i u) (subst t2 i u)
  | TTAbs k t     => TTAbs k (subst t i (splice i 1 u))
  | TTApp t1 t2   => TTApp (subst t1 i u) (subst t2 i u)*)
  | ttrue         => ttrue
  | tfalse        => tfalse
  | tvar x        => tvar x
  | tapp t1 t2    => tapp (subst t1 i u) (subst t2 i u)
  | tabs t1       => tabs (subst t1 i u)
  | ttapp t1 t2 k  => ttapp (subst t1 i u) (subst t2 i u) k
  | ttabs t1 t2   => ttabs t1(*?*) (subst t2 i (splice i 1 u))
end.

(* ---------- LR definitions for types : kinds  ---------- *)

Inductive has_kind J : tm -> tm -> Type :=
| k_star:
    has_kind J TStar TBox
| k_bool:
    has_kind J TBool TStar
| k_var: forall x K,
    indexr x J = Some K ->
    has_kind J (TVar x) K
| k_fun: forall T1 T2, (* (term -> term): type *)
    has_kind J T1 TStar ->
    has_kind J T2 TStar ->
    has_kind J (TFun T1 T2) TStar
| k_all: forall K1 T2, (* (type -> term): type *)
    has_kind (K1::J) T2 TStar ->
    has_kind J (TAll K1 T2) TStar
| k_karr: forall K1 K2, (* (type -> type): kind *)
    has_kind J K1 TBox ->
    has_kind J K2 TBox ->
    has_kind J (TFun K1 K2) TBox
| k_tabs: forall K1 T2 K2,
    has_kind (K1::J) T2 K2 ->
    has_kind J (ttabs K1 T2) (TFun K1 K2) (* (tabs K1 T2) (TPi K1 K2) *)
| k_tapp: forall TF TX K1 K2,
    has_kind J TF (TFun K1 K2) ->
    has_kind J TX K1 ->
    has_kind J (ttapp TF TX K1) K2
.

(* note: we can either include kn in the definition, or derive it later *)
Inductive eq_type : kenv -> tm -> tm -> tm -> Type :=
| q_refl: forall J T K,
    eq_type J T T K (* add has_kind? *)
| q_symm: forall J T1 T2 K,
    eq_type J T1 T2 K ->
    eq_type J T2 T1 K
| q_trans: forall J T1 T2 T3 K,
    eq_type J T1 T2 K ->
    eq_type J T2 T3 K ->
    eq_type J T1 T3 K
| q_fun: forall J T1 T2 T1' T2',
    eq_type J T1 T1' TStar ->
    eq_type J T2 T2' TStar ->
    eq_type J (TFun T1 T2) (TFun T1' T2') TStar
| q_tall : forall J T2 T2' K1,
    eq_type (K1::J) T2 T2' TStar ->
    eq_type J (TAll K1 T2) (TAll K1 T2') TStar
| q_tabs: forall J T2 T2' K1 K2,
    eq_type (K1::J) T2 T2' K2 ->
    eq_type J (ttabs K1 T2) (ttabs K1 T2') (TFun K1 K2)
| q_tapp: forall J T1 T2 T1' T2' K1 K2,
    eq_type J T1 T1' (TFun K1 K2) ->
    eq_type J T2 T2' K1 ->
    eq_type J (ttapp T1 T2 K1) (ttapp T1' T2' K1) K2
| q_beta: forall J T1 T2 K1 K2,
    has_kind J (ttabs K1 T2) (TFun K1 K2) ->
    has_kind J T1 K1 ->
    eq_type J (ttapp (ttabs K1 T2) T1 K1) (subst T2 (length J) T1) K2
.

Inductive has_type : tenv -> kenv -> tm -> tm -> Type :=
| t_true: forall G J,
    has_type G J ttrue TBool
| t_false: forall G J,
    has_type G J tfalse TBool
| t_var: forall x G J T,
    indexr x G = Some T ->
    has_type G J (tvar x) T

| t_abs: forall G J t T1 T2,
    has_type (T1::G) J t T2 ->
    has_kind J T1 TStar ->
    has_kind J T2 TStar ->
    has_type G J (tabs t) (TFun T1 T2)
| t_app: forall G J f t T1 T2,
    has_type G J f (TFun T1 T2) ->
    has_type G J t T1 ->
    has_type G J (tapp f t) T2

| t_tabs: forall G J t K1 T2,
    has_type (map (splice (length J) 1) G) (K1::J) t T2 ->
    has_kind (K1::J) T2 TStar ->
    has_type G J (ttabs K1 t) (TAll K1 T2)
| t_tapp: forall G J f K1 T1 T2,
    has_type G J f (TAll K1 T2) ->
    has_kind J (TAll K1 T2) TStar -> (* TEMP *)
    has_kind J T1 K1 ->
    has_type G J (ttapp f T1 K1) (subst T2 (length J) T1)

| t_equiv: forall G J t T1 T2,
    has_type G J t T1 ->
    eq_type J T1 T2 TStar ->
    (* has_kind J T2 TStar -> *)
    has_type G J t T2
.

#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.


(* ---------- other helper lemmas  ---------- *)

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

Lemma map_map: forall {A B C} (M: list A) (f: A -> B) (g: B -> C),
    map g (map f M) = map (fun vt => g(f(vt))) M.
Proof.
  intros ? ? ? M. induction M. intros. simpl. eauto.
  intros. simpl in *. rewrite IHM. eauto.
Qed.

Lemma indexr_splice_gt: forall{X} x (G1 G3: list X) T ,
  indexr x (G3 ++ G1) = Some T ->
  x >= length G1 ->
  forall G2,
  indexr (x + (length G2))(G3 ++ G2 ++ G1) = Some T.
Proof.
  intros.
  induction G3; intros; simpl in *.
  + apply indexr_var_some' in H as H'. lia.
  + bdestruct (x =? length (G3 ++ G1)); intuition.
    - subst. inversion H. subst.
      bdestruct (length (G3 ++ G1) + length G2 =? length (G3 ++ G2 ++ G1)); intuition.
      repeat rewrite app_length in H1. lia.
    - bdestruct (x + length G2 =? length (G3 ++ G2 ++ G1)); intuition.
      apply indexr_var_some' in H2. lia.
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

Lemma indexr_splice2: forall{X} (H2' H2: list X) x y,
  x <> length H2 ->
  indexr x (H2' ++ y :: H2) =
  indexr (if x <? length H2 then x else x-1) (H2' ++ H2).
Proof.
  intros.
  specialize (indexr_splice H2' H2 [y] (if x <? length H2 then x else x -1)); intuition. simpl in *.
  bdestruct (x <? length H2). eauto.
  bdestruct (x <? length H2). eauto. lia.
  bdestruct (x-1 <? length H2). lia.
  replace x with (x-1+1) at 1. 2: lia. eauto.
Qed.

Lemma indexr_hit: forall {T} J' J (K:T) ,
    indexr (length J) (J' ++ K :: J) = Some K.
Proof.
  intros. rewrite indexr_skips. rewrite indexr_head. eauto. simpl. eauto.
Qed.

Lemma splice_acc: forall e1 a b c,
  splice a c (splice a b e1) =
  splice a (c+b) e1.
Proof.
  induction e1; intros; simpl; try reflexivity.
  - bdestruct (i <? a); simpl; [bdestruct (i <? a); [auto | lia] | bdestruct (i+b <? a); [lia | f_equal; lia]].
  - rewrite IHe1_1, IHe1_2. auto.
  - rewrite IHe1_2. auto.
  - rewrite IHe1_1, IHe1_2. auto.
(*- rewrite IHe1_2. auto.
  - rewrite IHe1_1, IHe1_2. auto.
  - rewrite IHe1_1, IHe1_2. auto.*)
  - rewrite IHe1. auto.
  - rewrite IHe1_1, IHe1_2. auto.
  - rewrite IHe1_2. auto. 
Qed.

Lemma splice_acc': forall e1 a b c,
  splice (b+a) c (splice a b e1) =
  splice a (c+b) e1.
Proof.
  induction e1; intros; simpl; try reflexivity.
  - bdestruct (i <? a); simpl.
    + bdestruct (i <? a); [|lia]. bdestruct (i <? b+a); [|lia]. auto.
    + bdestruct (i + b <? b + a); [lia|]. f_equal. lia.
  - rewrite IHe1_1, IHe1_2. auto.
  - rewrite IHe1_2. auto.
  - rewrite IHe1_1, IHe1_2. auto.
(*- rewrite IHe1_2. auto.
  - rewrite IHe1_1, IHe1_2. auto.
  - rewrite IHe1_1, IHe1_2. auto.*)
  - rewrite IHe1. auto.
  - rewrite IHe1_1, IHe1_2. auto.
  - rewrite IHe1_2. auto.
Qed.

Lemma splice_zero: forall e1 a,
  (splice a 0 e1) = e1.
Proof.
  intros. induction e1; simpl; try reflexivity.
  - bdestruct (i <? a); f_equal; lia.
  - rewrite IHe1_1, IHe1_2. auto.
  - rewrite IHe1_2. auto.
  - rewrite IHe1_1, IHe1_2. auto.
(*- rewrite IHe1_2. auto.
  - rewrite IHe1_1, IHe1_2. auto.
  - rewrite IHe1_1, IHe1_2. auto.*)
  - rewrite IHe1. auto.
  - rewrite IHe1_1, IHe1_2. auto.
  - rewrite IHe1_2. auto.
Qed.


(* ---------- other helper lemmas (semantics)  ---------- *)

Lemma tevaln_unique: forall H1 e1 v1 v1',
    tevaln H1 e1 v1 ->
    tevaln H1 e1 v1' ->
    v1 = v1'.
Proof.
  intros.
  destruct H as [n1 ?].
  destruct H0 as [n2 ?].
  assert (1+n1+n2 > n1) as A1. lia.
  assert (1+n1+n2 > n2) as A2. lia.
  specialize (H _ A1).
  specialize (H0 _ A2).
  congruence.
Qed.


(* ---------- LR definitions for types : kinds  ---------- *)

Definition vt_none: tpe :=
  fun v => False.

Definition vt_any: tpe :=
  fun v => True.

Definition vt_bool: tpe :=
  fun v =>
    match v with
    | vbool v => True
    | _ => False
    end.

Definition vt_pi (T1: tpe) (T2: vl -> tpe): tpe :=
  fun v =>
    match v with
    | vabs H ty =>
        forall vx,
          T1 vx ->
          exists vy,
            tevaln (vx::H) ty vy /\
            T2 vx vy
    | _ => False
    end.

Definition vt_all A (TF: A -> tpe): tpe :=
  fun v =>
    match v with
    | vtabs H ty =>
        forall T1,
          exists vy,
            tevaln H ty vy /\
            (TF T1) vy
    | _ => False
    end.



Fixpoint val_sort (K: tm) : Type :=
  match K with
  | TStar => tpe
  | TFun K1 K2 => val_sort K1 -> val_sort K2
  | _ => unit
  end.


Fixpoint bottom (K: tm): val_sort K :=
  match K with
  | TStar => fun v => False
  | TFun K1 K2 => fun vx => bottom K2
  | _ => tt
  end.

Lemma tm_eq_dec: forall (K' K: tm), {K' = K} + {K' <> K}.
Proof.
  intros. decide equality. decide equality. decide equality. 
Qed.

Definition broaden (K: tm) (V: val_sort K) (K': tm): val_sort K'.
  assert ({K' = K} + {K' <> K}). eapply tm_eq_dec.
  destruct H. subst. eauto.
  eapply bottom. 
Defined.

Fixpoint val_type (W: list (forall K, val_sort K)) T K {struct T}: val_sort K :=
  match T, K return val_sort K with
  | TBool, TStar =>
      vt_bool
  | TVar x, K =>
      match (indexr x W) with
      | Some vt => vt K
      | None => bottom K
      end
  | TFun T1 T2, TStar =>
      vt_pi (val_type W T1 TStar) (fun vx => val_type W T2 TStar)
  | TAll K1 T2, TStar =>
      vt_all (val_sort K1) (fun VT1 => val_type ((broaden _ VT1)::W) T2 TStar)
  | ttabs K1 T2, TFun K1' K2 =>
      (* TODO: K1 = K1' ? *)
      (fun VT1 => val_type ((broaden _ VT1)::W) T2 K2)
  | ttapp TF TX K1(*!*), K2 =>
      (* let K1 := TStar in (* TODO! *) *)
      val_type W TF (TFun K1 K2) (val_type W TX K1)
  | _, K =>
      bottom K
  end.


Definition exp_type H W t T :=
  exists v,
    tevaln H t v /\
    val_type W T TStar v.

Definition env_type (H: venv) (G: tenv) V (J: kenv) :=
  length H = length G /\
  length V = length J /\
  forall x T,
    indexr x G = Some T ->
    exists v,
      indexr x H = Some v /\
      val_type V T TStar v.

Definition sem_type G (J:kenv) t T :=
  forall H V,
    env_type H G V J ->
    exp_type H V t T.


(* ---------- helper lemmas: valt_weaken, subst, open  ---------- *)

Lemma valt_weaken: forall T K V V1 vt,
    val_type (V1++V) T K = val_type (V1++vt::V) (splice (length V) 1 T) K.
Proof.
  intros T. induction T; intros.
  - simpl. eauto.
  - simpl. eauto.
  - (* TBool *) simpl. eauto.
  - (* TVar *) simpl in *. bdestruct (i <? length V); eauto. 
    + erewrite indexr_insert_lt. eauto. eauto. 
    + erewrite indexr_insert_ge. replace (i+1) with (S i). eauto. lia. eauto. 
  - (* TFun *) simpl. destruct K; eauto.
    erewrite IHT1, IHT2. eauto. 
  - (* TAll *) simpl. destruct K; eauto.
    unfold vt_all. eapply functional_extensionality. intros v.
    destruct v; eauto. eapply propositional_extensionality.
    split; intros. 
    + edestruct H as (vy & ? & VY). 
      exists vy. split. eauto.
      replace (broaden T1 T0 :: V1 ++ vt :: V) with ((broaden T1 T0 :: V1) ++ vt :: V).
      rewrite <-IHT2. eauto. eauto. 
    + edestruct H as (vy & ? & VY). 
      exists vy. split. eauto. 
      replace (broaden T1 T0 :: V1 ++ V) with (((broaden T1 T0) :: V1) ++ V).
      erewrite IHT2. eauto. eauto.
  - simpl. eauto.
  - simpl. eauto.
  - simpl. eauto.
  - simpl. eauto.
  - simpl. eauto.
  - (* ttapp *)
    simpl. erewrite IHT1 with (vt:=vt). erewrite IHT2 with (vt:=vt). eauto.
  - (* ttabs *)
    simpl. destruct K; eauto.
    eapply functional_extensionality. intros VT1.
    replace ((broaden K1 VT1) :: V1 ++ V) with (((broaden K1 VT1) :: V1) ++ V).
    erewrite IHT2. simpl. eauto. eauto. 
Qed.

Lemma valt_extend: forall V vt T K,
    val_type V T K = val_type (vt::V) (splice (length V) 1 T) K.
Proof.
  intros. eapply valt_weaken with (V:=V) (V1:=nil). 
Qed.

Lemma valt_extend_mult: forall V1 V T K,
    val_type V T K = val_type (V1++V) (splice (length V) (length V1) T) K.
Proof.
  intros. induction V1; intros. simpl in *. rewrite splice_zero. eauto.
  rewrite IHV1. erewrite valt_extend. 
  rewrite app_length. erewrite splice_acc'. simpl. eauto. 
Qed.

(* this version is too simple (unused, might keep as demonstration) *)
Lemma valt_subst_gen: forall T2 T1 vt V V1 K2,
    vt = (fun K1 => (val_type V T1 K1)) ->
    val_type (V1 ++ vt :: V) T2 K2 =
      val_type (V1++V) (subst T2 (length V) (splice (length V) (length V1) T1)) K2.
Proof.
  intros T2. induction T2; intros.
  - simpl. eauto.
  - simpl. eauto.
  - simpl. eauto.
  - simpl in *. bdestruct (i =? length V); eauto. 
    + rewrite indexr_skips. subst i. rewrite indexr_head. subst vt.
      remember (Nat.eq_dec _ _). destruct s. 2: lia.      
      eapply valt_extend_mult. simpl. lia. 
    + bdestruct (i <? length V). {
        erewrite <-indexr_insert_lt; eauto.
        remember (Nat.eq_dec _ _). destruct s. lia.
        eauto.         
      } {
        destruct i. lia. erewrite <-indexr_insert_ge. 2: lia.
        remember (Nat.eq_dec _ _). destruct s. lia.
        simpl. replace (i-0) with i. eauto. lia. 
      }
  - simpl. destruct K2; eauto.
    erewrite IHT2_1, IHT2_2. eauto. eauto. eauto. 
  - (* TAll *) simpl. destruct K2; eauto.
    unfold vt_all. eapply functional_extensionality. intros v.
    destruct v; eauto. eapply propositional_extensionality.
    split; intros. 
    + edestruct H0 as (vy & ? & VY). 
      exists vy. split. eauto.
      replace (broaden T2_1 T0 :: V1 ++ V) with ((broaden T2_1 T0 :: V1) ++ V).
      rewrite splice_acc. 
      erewrite <-IHT2_2. eauto. eauto. eauto. 
    + edestruct H0 as (vy & ? & VY). 
      exists vy. split. eauto. 
      replace (broaden T2_1 T0 :: V1 ++ vt :: V) with ((broaden T2_1 T0 :: V1) ++ vt :: V).
      erewrite IHT2_2. rewrite splice_acc in VY. eauto. eauto. eauto.
  - simpl. eauto.
  - simpl. eauto.
  - simpl. eauto.
  - simpl. eauto.
  - simpl. eauto.
  - (* ttapp *)
    simpl. erewrite IHT2_1 with (vt:=vt). erewrite IHT2_2 with (vt:=vt).
    eauto. eauto. eauto.
  - (* ttabs *)
    simpl. destruct K2; eauto.
    eapply functional_extensionality. intros VT1.
    replace (broaden K2_1 VT1 :: V1 ++ vt :: V) with ((broaden K2_1 VT1 :: V1) ++ vt :: V).
    erewrite IHT2_2. simpl. rewrite splice_acc with (c:=1). simpl. eauto. eauto. eauto. 
Qed.

Lemma valt_subst: forall V vt T1 T2 K2,
    vt = (fun K => val_type V T1 K) ->
    val_type (vt::V) T2 K2 = val_type V (subst T2 (length V) T1) K2.
Proof.
  intros.
  specialize valt_subst_gen with (V:=V) (V1:=nil). intros. 
  eauto. simpl in *. erewrite H0. rewrite splice_zero.
  eauto. eauto.
Qed.


Lemma valt_subst_gen1: forall T2 T1 vt V V1 G G1 K1 K2,
    has_kind (G1 ++ K1 :: G) T2 K2 ->
    length V = length G ->
    length V1 = length G1 ->
    vt = (broaden K1 (val_type V T1 K1)) ->
    val_type (V1 ++ vt :: V) T2 K2 =
      val_type (V1++V) (subst T2 (length V) (splice (length V) (length V1) T1)) K2.
Proof.
  intros T2. induction T2; intros.
  - simpl. eauto.
  - simpl. eauto.
  - simpl. eauto.
  - simpl in *. inversion H. subst x K. 
    bdestruct (i =? length V); eauto. 
    + rewrite indexr_skips. subst i. rewrite indexr_head. subst vt.
      remember (Nat.eq_dec _ _). destruct s. 2: lia.
      rewrite indexr_skips in H4. rewrite H0 in H4. rewrite indexr_head in H4.
      inversion H4. subst K1. 
      unfold broaden. destruct (tm_eq_dec K2 K2). unfold eq_rect_r, eq_rect, eq_sym.
      destruct e0. 
      eapply valt_extend_mult. simpl. contradiction. simpl. lia. simpl. lia. 
    + bdestruct (i <? length V). {
        erewrite <-indexr_insert_lt; eauto.
        remember (Nat.eq_dec _ _). destruct s. lia.
        eauto.
      } {
        destruct i. lia. erewrite <-indexr_insert_ge. 2: lia.
        remember (Nat.eq_dec _ _). destruct s. lia.
        simpl. replace (i-0) with i. eauto. lia. 
      }
  - simpl. destruct K2; eauto. inversion H. 
    erewrite IHT2_1, IHT2_2; eauto. 
  - (* TAll *) simpl. destruct K2; eauto. inversion H. subst T2_1 T2_2.
    unfold vt_all. eapply functional_extensionality. intros v.
    destruct v; eauto. eapply propositional_extensionality.
    split; intros. 
    + edestruct H3 as (vy & ? & VY). 
      exists vy. split. eauto.
      replace (broaden K0 T0 :: V1 ++ V) with ((broaden K0 T0 :: V1) ++ V).
      replace (K0 :: G1 ++ K1 :: G) with ((K0 :: G1) ++ K1 :: G) in H4.
      rewrite splice_acc. 
      erewrite <-IHT2_2; eauto. simpl. eauto. simpl. eauto. simpl. eauto. 
    + edestruct H3 as (vy & ? & VY). 
      exists vy. split. eauto. 
      replace (broaden K0 T0 :: V1 ++ vt :: V) with ((broaden K0 T0 :: V1) ++ vt :: V).
      replace (K0 :: G1 ++ K1 :: G) with ((K0 :: G1) ++ K1 :: G) in H4.
      erewrite IHT2_2. rewrite splice_acc in VY. eauto. eauto. eauto.
      simpl. eauto. simpl. eauto. simpl. eauto. simpl. eauto. 
  - simpl. eauto.
  - simpl. eauto.
  - simpl. eauto.
  - simpl. eauto.
  - simpl. eauto.
  - (* ttapp *)
    inversion H. subst T2_1 T2_2 T2_3 K3. simpl.
    erewrite IHT2_1 with (vt:=vt); eauto.
    erewrite IHT2_2 with (vt:=vt); eauto.
  - (* ttabs *)
    inversion H. subst T2_1 T2_2 K2. 
    simpl. 
    eapply functional_extensionality. intros VT1.
    replace (broaden K0 VT1 :: V1 ++ vt :: V) with ((broaden K0 VT1 :: V1) ++ vt :: V).
    replace (K0 :: G1 ++ K1 :: G) with ((K0 :: G1) ++ K1 :: G) in H6. 
    erewrite IHT2_2; eauto. simpl. rewrite splice_acc with (c:=1). simpl. eauto. simpl. eauto. simpl. eauto. simpl. eauto.     
Qed.

Lemma valt_subst1: forall V vt T1 T2 K1 K2 G,
    has_kind (K1 :: G) T2 K2 ->
    length V = length G ->
    vt = (broaden K1 (val_type V T1 K1)) ->
    val_type (vt::V) T2 K2 = val_type V (subst T2 (length V) T1) K2.
Proof.
  intros.
  specialize valt_subst_gen1 with (V:=V) (V1:=nil) (G:=G) (G1:=nil). intros. 
  eauto. simpl in *. erewrite H2. rewrite splice_zero.
  eauto. eauto. eauto. eauto. eauto. 
Qed.


(* ---------- env extension lemmas  ---------- *)

Lemma envt_empty: 
    env_type [] [] [] [].
Proof.
  intros. split. 2: split.
  eauto. eauto. intros. inversion H.
Qed.

Lemma envt_extend: forall E G V J v1 T1,
    env_type E G V J ->
    val_type V T1 TStar v1 ->
    env_type (v1::E) (T1::G) V J.
Proof.
  intros.
  remember H as WFE. clear HeqWFE.
  destruct H as (? & ? & ?). split. 2: split.
  simpl. eauto. simpl. eauto. 
  intros x T IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX. subst T1.
    exists v1. rewrite <- H. rewrite indexr_head. eauto.
  - rewrite indexr_skip in IX; eauto.
    eapply WFE in IX as IX. destruct IX as (v2 & ? & ?).
    exists v2. rewrite indexr_skip; eauto. lia.
Qed.

Lemma envt_extendk: forall E G V J vt1 K1,
    env_type E G V J ->
    env_type E (map (splice (length V) 1) G) (vt1::V) (K1::J).
Proof.
  intros.
  remember H as WFE. clear HeqWFE.
  destruct H as (? & ? & ?). split. 2: split. 
  rewrite map_length. eauto. simpl. eauto. 
  intros x T IX.
  eapply indexr_map' in IX. destruct IX as (T' & IX & ?).
  eapply WFE in IX as IX. destruct IX as (v2 & ? & ?).
  exists v2. split. eauto. subst T.
  rewrite <-valt_extend. eauto.
Qed.


(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_true: forall G J,
    sem_type G J ttrue TBool.
Proof.
  intros.
  intros E WFJ WFE.
  exists (vbool true).
  split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto.
Qed.

Lemma sem_false: forall G J,
    sem_type G J tfalse TBool.
Proof.
  intros.
  intros E WFJ WFE.
  exists (vbool false).
  split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto.
Qed.

Lemma sem_var: forall G J x T,
    indexr x G = Some T ->
    sem_type G J (tvar x) T.
Proof.
  intros.
  intros E WFJ WFE.
  eapply WFE in H as IX. destruct IX as (v & IX & VX).
  exists v.
  split.
  - exists 0. intros. destruct n. lia. simpl. rewrite IX. eauto.
  - eauto.
Qed.

Lemma sem_abs: forall G J t T1 T2,
    sem_type (T1::G) J t T2 ->
    has_kind J T1 TStar ->
    has_kind J T2 TStar ->
    sem_type G J (tabs t) (TFun T1 T2).
Proof.
  intros ? ? ? ? ? HY W1 W2. intros E WFJ WFE.
  eexists _.
  split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros vx VX.
    edestruct HY as (vy & ? & ?). eapply envt_extend; eauto.
    exists vy. split. eauto. eauto. 
Qed.

Lemma sem_app: forall G J f t T1 T2,
    sem_type G J f (TFun T1 T2) ->
    sem_type G J t T1 ->
    sem_type G J (tapp f t) T2.
Proof.
  intros ? ? ? ? ? ? HF HX. intros H WFJ WFE.
  destruct (HF H WFJ WFE) as (vf & STF & VF).
  destruct (HX H WFJ WFE) as (vx & STX & VX).
  destruct vf; simpl in VF; intuition.
  edestruct VF as (vy & STY & VY). eauto.
  exists vy.
  split.
  - destruct STF as (n1 & STF).
    destruct STX as (n2 & STX).
    destruct STY as (n3 & STY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite STF, STX, STY. 2,3,4: lia.
    eauto.
  - eauto.
Qed.

Lemma sem_tabs: forall G J t K1 T2,
    sem_type (map (splice (length J) 1) G) (K1::J) t T2 ->
    has_kind (K1::J) T2 TStar ->
    sem_type G J (ttabs K1 t) (TAll K1 T2).
Proof.
  intros ? ? ? ? ? HY W2. intros E V WFE.
  assert (length E = length G) as L. eapply WFE.
  assert (length V = length J) as LV. eapply WFE.
  exists (vtabs E t). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros VK1.
    edestruct (HY E (broaden _ VK1::V)) as (vy & ? & ?).
    rewrite <-LV. eapply envt_extendk in WFE. eauto. 
    exists vy. split. eauto. eauto.
Qed.

Lemma sem_tapp: forall G J t K1 T1 T2,
    sem_type G J t (TAll K1 T2) ->
    has_kind J (TAll K1 T2) TStar ->
    has_kind J T1 K1 ->
    sem_type G J (ttapp t T1 K1) (subst T2 (length J) T1).
Proof.
  intros ? ? ? ? ? ? HF HA HX. intros E V WFE.
  assert (length E = length G) as L. eapply WFE.
  assert (length V = length J) as LV. eapply WFE.
  destruct (HF E V WFE) as (vf & STF & VF).
  destruct vf; simpl in VF; intuition.
  remember (val_type V T1 K1) as T1K.
  edestruct (VF T1K) as (vy & STY & VY).
  exists vy. split.
  - destruct STF as (n1 & STF).
    destruct STY as (n2 & STY).
    exists (1+n1+n2). intros. destruct n. lia.
    simpl. rewrite STF, STY. 2,3: lia. eauto.
  - erewrite valt_subst1 in VY. rewrite <-LV. eauto.
    inversion HA. eauto. eauto. subst. eauto. 
Qed.


(* ---------- LR fundamental property of equiv ---------- *)

Lemma val_type_equiv : forall J T1 T2 K V,
  length J = length V ->
  eq_type J T1 T2 K ->
  val_type V T1 K = val_type V T2 K.
Proof.
  intros. generalize dependent V.
  induction H0; intros.
  - eauto.
  - rewrite IHeq_type; eauto. 
  - rewrite IHeq_type1, IHeq_type2; eauto.
  - simpl. rewrite IHeq_type1, IHeq_type2; eauto.
  - simpl. 
    unfold vt_all. eapply functional_extensionality. intros v.
    destruct v; eauto. eapply propositional_extensionality.
    split; intros. 
    + edestruct H1 as (vy & ? & VY). 
      exists vy. split. eauto.
      erewrite <-IHeq_type; eauto. simpl. eauto. 
    + edestruct H1 as (vy & ? & VY). 
      exists vy. split. eauto. 
      erewrite IHeq_type. eauto. simpl. eauto. 
  - simpl. 
    eapply functional_extensionality. intros VT1.
    erewrite IHeq_type; eauto. simpl. eauto. 
  - simpl. rewrite IHeq_type1, IHeq_type2; eauto.
  - simpl. erewrite valt_subst1. rewrite H. eauto.
    inversion h. eauto. eauto. eauto. 
Qed.

Lemma sem_equiv: forall G J t T1 T2,
    eq_type J T1 T2 TStar ->
    sem_type G J t T1 ->
    sem_type G J t T2.
Proof.
  intros ???? KX HK HX. intros H V WFE.
  edestruct HX as (vx & A & VX). eauto.
  eexists vx.
  split.
  - eauto.
  - erewrite <- val_type_equiv; eauto.
    symmetry. eapply WFE. 
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
  - eapply sem_abs; eauto.
  - eapply sem_app; eauto.
  - eapply sem_tabs; eauto.
  - eapply sem_tapp; eauto.    
  - eapply sem_equiv; eauto.
Qed.

Corollary safety: forall t T,
  has_type [] [] t T ->
  exp_type [] [] t T.
Proof.
  intros. eapply fundamental in H as ST; eauto.
  edestruct (ST []) as (v & ? & ?). eapply envt_empty.
  exists v. intuition. 
Qed.

End STLC.
