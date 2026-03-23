(* Full safety for System F-Omega *)

(*

An LR-based termination and semantic soundness proof.

Canonical big-step cbv semantics.

Cmbining type abstraction and type operators (System F-Omega).


THIS FILE (via stlc_tabs_topr.v):
- add subtyping (TAny top type, bounded TAll)

THIS FILE (via stlc_tabs.v):
- add type operators (TTAbs, TTApp) and type equivalence (eq_type)

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

Inductive kn : Type :=
  | KTpe : kn
  | KArr : kn -> kn -> kn
.

(*
  In the thesis version, Top is encoded as kn -> ty, while in TaPL, Top[K] is just a macro: Top[K1 => K2] := λX::K1 . Top[K2]
  We should choose the macro version because of:
    - otherwise we need to define the interpretation of Top[K], which we only vt_any only works for *
    - TODO: the stp should ensure any type T :: K <: Top[K] 
    - we don't have higher-kind bounds, i.e. λX::K <: U . T, we don't have <: inside the TTAbs, so we don't really need the more complicated Top[K]
*)
Inductive ty : Type :=
  | TBool  : ty
  | TTop   : ty       (* Top[K] *)
  | TVar   : id -> ty
  | TFun   : ty -> ty -> ty
  | TAll   : ty -> ty -> ty (* ∀X <: T. T *)
  | TTAbs  : kn -> ty -> ty (* λX :: K. T *)
  | TTApp  : ty -> ty -> ty
.

(* Top[K]: the top type for kind K *)
Fixpoint TopK (K : kn) : ty :=
  match K with
  | KTpe => TTop
  | KArr K1 K2 => TTAbs K1 (TopK K2)
  end
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

(* the interpretation of kind, which defines the set at * *)
Definition tpe := vl -> Prop.
Definition venv := list vl.
Definition tenv := list ty.

(* type context is split to store upper bounds and kinds *)
Definition ktenv := list ty.  (* upper bound *)
Definition kkenv := list kn.  (* kind *)

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.
#[global] Hint Unfold ktenv.
#[global] Hint Unfold kkenv.


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


(* ---------- substitution on types ---------- *)

Fixpoint splice (i: nat) (n:nat) (t: ty): ty :=
  match t with
  | TBool         => TBool
  | TTop          => TTop
  | TVar x        => TVar (if x <? i then x else x + n)
  | TFun t1 t2    => TFun (splice i n t1) (splice i n t2)
  | TAll t1 t2    => TAll (splice i n t1) (splice i n t2)
  | TTAbs k t     => TTAbs k (splice i n t)
  | TTApp t1 t2   => TTApp (splice i n t1) (splice i n t2)
end.

Fixpoint subst (t: ty) (i: nat) (u:ty): ty :=
  match t with
  | TBool         => TBool
  | TTop          => TTop
  | TVar x        => if Nat.eq_dec x i then u else TVar (if x <? i then x else x-1)
  | TFun t1 t2    => TFun (subst t1 i u) (subst t2 i u)
  | TAll t1 t2    => TAll (subst t1 i u) (subst t2 i (splice i 1 u))
  | TTAbs k t     => TTAbs k (subst t i (splice i 1 u))
  | TTApp t1 t2   => TTApp (subst t1 i u) (subst t2 i u)
end.

(* ---------- LR definitions for types : kinds  ---------- *)

(* upper-bound context not needed here *)
Inductive has_kind JK : ty -> kn -> Type :=
| k_bool:
    has_kind JK TBool KTpe
| k_top:
    has_kind JK (TTop) KTpe
| k_var: forall x K,
    indexr x JK = Some K ->
    has_kind JK (TVar x) K
| k_fun: forall T1 T2,
    has_kind JK T1 KTpe ->
    has_kind JK T2 KTpe ->
    has_kind JK (TFun T1 T2) KTpe
| k_all: forall T1 T2 K1,
    has_kind JK T1 K1 ->
    has_kind (K1 :: JK) T2 KTpe ->  (* T1 is the bound, K1 is its kind *)
    has_kind JK (TAll T1 T2) KTpe
| k_tabs: forall K1 T2 K2,
    has_kind ((K1) :: JK) T2 K2 ->
    has_kind JK (TTAbs K1 T2) (KArr K1 K2)
| k_tapp: forall TF TX K1 K2,
    has_kind JK TF (KArr K1 K2) ->
    has_kind JK TX K1 ->
    has_kind JK (TTApp TF TX) K2
.

(* type equivalence *)
Inductive eq_type J : ty -> ty -> Type :=
| q_refl: forall T,
    eq_type J T T
| q_symm: forall T1 T2,
    eq_type J T1 T2 ->
    eq_type J T2 T1
| q_trans: forall T1 T2 T3,
    eq_type J T1 T2 ->
    eq_type J T2 T3 ->
    eq_type J T1 T3
| q_fun: forall T1 T2 T1' T2',
    eq_type J T1 T1' ->
    eq_type J T2 T2' ->
    eq_type J (TFun T1 T2) (TFun T1' T2')
| q_tall : forall T1 T1' T2 T2' K1,
    eq_type J T1 T1' ->
    has_kind J T1 K1 ->
    eq_type (K1::J) T2 T2' ->
    eq_type J (TAll T1 T2) (TAll T1' T2')
| q_tabs: forall T2 T2' K1,
    eq_type (K1 :: J) T2 T2' ->
    eq_type J (TTAbs K1 T2) (TTAbs K1 T2')
| q_tapp: forall T1 T2 T1' T2',
    eq_type J T1 T1' ->
    eq_type J T2 T2' ->
    eq_type J (TTApp T1 T2) (TTApp T1' T2')
| q_beta: forall T1 T2 K1,
    has_kind J T1 K1 ->
    eq_type J (TTApp (TTAbs K1 T2) T1) (subst T2 (length J) (splice (length J) 0 T1))
.

(* subtyping relation *)
Inductive stp JT JK : ty -> ty -> Type :=
| s_bool :
    stp JT JK TBool TBool
| s_trans: forall T1 T2 T3 K,
    stp JT JK T1 T2 ->
    stp JT JK T2 T3 ->
    has_kind JK T2 K ->
    stp JT JK T1 T3
| s_top : forall T,
  (* the rule in TaPL is only for star, see the thesis version *)
    has_kind JK T KTpe ->
    stp JT JK T (TTop)
| s_fun : forall S1 S2 T1 T2,
    stp JT JK T1 S1 ->
    stp JT JK S2 T2 ->
    stp JT JK (TFun S1 S2) (TFun T1 T2)
| s_var_refl : forall x,
    stp JT JK (TVar x) (TVar x)
| s_var: forall x T K,
    indexr x JT = Some T ->
    has_kind JK T K ->
    stp JT JK (TVar x) T
| s_all: forall U K1 S2 T2,
    has_kind JK U K1 ->
    stp (map (splice (length JT) 1) (U :: JT)) (K1 :: JK) S2 T2 ->
    stp JT JK (TAll U S2) (TAll U T2)
| s_abs: forall K1 S2 T2,
    stp (map (splice (length JT) 1) ((TopK K1) :: JT)) (K1 :: JK) S2 T2 ->
    stp JT JK (TTAbs K1 S2) (TTAbs K1 T2)
| s_app: forall S1 T1 U,
    stp JT JK S1 T1 ->
    stp JT JK (TTApp S1 U) (TTApp T1 U)
| s_eq: forall K T1 T2,
    has_kind JK T1 K ->
    has_kind JK T2 K ->
    eq_type (JK) T1 T2 ->
    stp JT JK T1 T2
.

(* type assignment relation *)
Inductive has_type : tenv -> ktenv -> kkenv -> tm -> ty -> Type :=
| t_true: forall G JT JK,
    has_type G JT JK ttrue TBool
| t_false: forall G JT JK,
    has_type G JT JK tfalse TBool
| t_var: forall x G JT JK T,
    indexr x G = Some T ->
    has_type G JT JK (tvar x) T

| t_abs: forall G JT JK t T1 T2,
    has_type (T1 :: G) JT JK t T2 ->
    has_kind JK T1 KTpe ->
    has_kind JK T2 KTpe ->
    has_type G JT JK (tabs t) (TFun T1 T2)
| t_app: forall G JT JK f t T1 T2,
    has_type G JT JK f (TFun T1 T2) ->
    has_type G JT JK t T1 ->
    has_type G JT JK (tapp f t) T2

| t_tabs: forall G JT JK t U K1 T2,
    has_type (map (splice (length JT) 1) G) (map (splice (length JT) 1) (U :: JT)) (K1 :: JK) t T2 ->
    has_kind JK U K1 ->
    has_kind (K1 :: JK) T2 KTpe ->
    has_type G JT JK (ttabs t) (TAll U T2)

| t_tapp: forall G JT JK f U T1 T2,
    has_type G JT JK f (TAll U T2) ->
    (* has_kind J T1 K1 -> *)
    stp JT JK T1 U ->
    has_type G JT JK (ttapp f T1) (subst T2 (length JT) T1)

(* | t_equiv: forall G J t T1 T2, <--- now part of subtyping!
    has_type G J t T1 ->
    eq_type J T1 T2 ->
    has_kind J T2 KTpe ->
    has_type G J t T2 *)
| t_sub : forall G JT JK t T1 T2,
    has_type G JT JK t T1 ->
    stp JT JK T1 T2 ->
    has_kind JK T2 KTpe ->
    has_type G JT JK t T2
.

#[export] Hint Constructors ty: core.
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

Lemma indexr_map'': forall {A B} (M: list A) x v (f: A -> B),
    indexr x (map f M) = Some v ->
    { v' : A | indexr x M = Some v' /\ v = f v' }.
Proof.
  intros. erewrite indexr_map in H.
  2: { eapply indexr_var_some' in H. rewrite map_length in H.
       eapply indexr_var_some in H. destruct H. eauto. }
  remember (indexr x M). destruct o. inversion H.
  exists a. intuition. inversion H.
Defined.

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

Lemma splice_acc: forall e1 a b c,
  splice a c (splice a b e1) =
  splice a (c+b) e1.
Proof. induction e1; intros; simpl; intuition.
  + bdestruct (i <? a); intuition.
    bdestruct (i <? a); intuition.
    bdestruct (i+b <? a); intuition.
  + specialize (IHe1_1 a b c). specialize (IHe1_2 a b c).
    rewrite IHe1_1. rewrite IHe1_2. auto.
  + specialize (IHe1_1 a b c). specialize (IHe1_2 a b c).
    rewrite IHe1_2. rewrite IHe1_1. auto.
  + specialize (IHe1 a b c).
    rewrite IHe1. auto.
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
    bdestruct (i + b <? b + a); intuition.
  + specialize (IHe1_1 a b c). specialize (IHe1_2 a b c).
    rewrite IHe1_1. rewrite IHe1_2. auto.
  + specialize (IHe1_2 a b c).
    rewrite IHe1_2. rewrite IHe1_1. auto.
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
  + rewrite IHe1_1. rewrite IHe1_2. auto.
Qed.



(* ---------- other helper lemmas  ---------- *)

Require Import Coq.Program.Equality.

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

Lemma hask_TopK K: forall J,
  has_kind J (TopK K) K.
Proof.
  induction K; intros; simpl. constructor. constructor. auto.
Qed.

Lemma TopK_splice : forall K a b,
  TopK K = splice a b (TopK K).
Proof.
  induction K; intros. simpl; auto.
  simpl. f_equal. apply IHK2.
Qed.

Lemma stp_refl T : forall JT JK K,
  has_kind JK T K -> (* we need a witness for TAll *)
  stp JT JK T T.
Proof.
  induction T; intros; simpl.
  - constructor.
  - constructor. constructor.
  - constructor.
  - dependent destruction H. constructor; auto. apply IHT1 with (K:=KTpe); auto. apply IHT2 with (K:=KTpe); auto.
  - dependent destruction H. apply s_all with (K1:=K1); auto. apply IHT2 with (K:=KTpe); auto.
  - dependent destruction H. apply s_abs. apply IHT with (K:=K2); auto.
  - apply s_app. dependent destruction H. apply IHT1 with (K:=(KArr K1 K2)); auto.
Qed.



(* uniqueness, prove irrelevance lemmas *)

Lemma hk_unique': forall GV T K1
  (a: has_kind GV T K1) K2
  (b: has_kind GV T K2), K1 = K2.
Proof.
  intros GV T K1 a.
  induction a; intros K2' b; inversion b; subst; intros.
  - eauto.
  - congruence.
  - congruence.
  - eauto.
  - eauto.
  - specialize (IHa _ H2).
    subst. eauto.
  - specialize (IHa2 _ H3).
    subst.
    specialize (IHa1 _ H1).
    congruence.
Qed.

Lemma indexr_unique: forall {A} {J : list A} {x T T'} 
  (a: indexr x J = Some T) (b: indexr x J = Some T'),
  T = T'.
Proof.
  intros. rewrite a in b. congruence.
Qed.


Lemma hk_unique: forall GV T K
  (a b: has_kind GV T K), a = b.
Proof.
  intros GV T K a.
  induction a; intros b; dependent destruction b.
  - eauto.
  - congruence.
  - specialize (indexr_unique e e0). intros. subst. f_equal. eapply proof_irrelevance. 
  - specialize (IHa1 b1).
    specialize (IHa2 b2).
    subst. eauto.
  - specialize (hk_unique' _ _ _ a1 _ b1). intros. subst.
    specialize (IHa1 b1). specialize (IHa2 b2). congruence.
  - specialize (IHa b).
    subst. eauto.
  - specialize (hk_unique' _ _ _ a2 _ b2). intros. subst.
    specialize (IHa2 b2). subst.
    specialize (IHa1 b1). subst.
    eauto.
Qed.

(* ---------- Syntactic Weakening ----------------- *)

(*
  Given a context [TAll $1 $3, Top, Top], say that we weaken the context to [_, Top, T0, Top], so the _ type should be: TAll $2 $4, which is one splice 1 1
*)

Lemma indexr_splice1_map : forall i J' J T1 T,
  indexr i (J' ++ J) = Some T ->
  indexr (if i <? length J then i else 1 + i) (map (splice (length J) 1) (J' ++ T1 :: J)) = Some (splice (length J) 1 T).
Proof.
  intros. rewrite <- indexr_splice1 with (y:=T1) in H. apply indexr_map with (f:= splice (length J) 1) in H. auto.
Qed.

Lemma splice_splice : forall t a b, 
  splice a 1 (splice (b + a) 1 t) = splice (b + S (a)) 1 (splice (a) 1 t).
Proof.
  induction t; intros; simpl; intuition.
  - bdestruct (i <? b + a); intuition. 
    bdestruct (i <? a); intuition. bdestruct (i <? b + S a); intuition. bdestruct (i + 1 <? b + S a); intuition.
    bdestruct (i + 1 <? a); intuition. bdestruct (i <? a); intuition. bdestruct (i + 1 <? b + S a); intuition.
  - rewrite IHt1. rewrite IHt2. auto.
  - rewrite IHt1. rewrite IHt2. auto.
  - rewrite IHt. auto.
  - rewrite IHt1. rewrite IHt2. auto.
Qed.

Lemma splice_splice' : forall a b, 
  (fun t => splice a 1 (splice (b + a) 1 t)) = (fun t => splice (b + S (a)) 1 (splice (a) 1 t)).
Proof.
  intros. apply functional_extensionality. intros. apply splice_splice.
Qed.


Lemma haskind_weaken: forall T J' J K K1,
    has_kind (J' ++ J) T K ->
    has_kind (J' ++ K1 :: J) (splice (length J) 1 T) K.
Proof.
  intros T. induction T; intros; inversion H; subst; simpl in *.
  - eapply k_bool.
  - eapply k_top.
  - eapply k_var. replace (i+1) with (1+i). 2: lia.
    erewrite indexr_splice1. eauto.
  - eapply k_fun. eauto. eauto.
  - eapply k_all with (K1:=K0). eapply IHT1; auto. eapply IHT2 with (J':=K0::J'). eauto.
  - eapply k_tabs. eapply IHT with (J':=k::J'). eauto.
  - eapply k_tapp. eauto. eauto.
Defined.


Lemma haskind_extend: forall T J K K1,
    has_kind J T K ->
    has_kind (K1 :: J) (splice (length J) 1 T) K.
Proof.
  intros. eapply haskind_weaken with (J':=[]). eauto.
Defined.

Fixpoint haskind_extend_mult J': forall T J K,
    has_kind J T K ->
    has_kind (J'++ J) (splice (length J) (length J') T) K.
Proof.
  destruct J'; intros; simpl in *.
  - rewrite splice_zero. eapply H.
  - eapply haskind_extend_mult in H. eapply haskind_extend in H.
    rewrite app_length in H. rewrite splice_acc' in H. eapply H.
Defined.




(* ---------- LR definitions for types : kinds  ---------- *)

Fixpoint val_kind K :=
  match K with
  | KTpe => tpe
  | KArr K1 K2 => val_kind K1 -> val_kind K2
  end.

(* semantic interpretation of subtyping *)
Fixpoint vstp (K : kn) : (val_kind K) -> (val_kind K) -> Prop :=
  match K with
  | KTpe => 
      fun vt1 vt2 => forall v, vt1 v -> vt2 v
  | KArr K1 K2 => 
      fun vt1 vt2 => forall vt (*: val_kind K1 *),
        vstp K2 (vt1 vt) (vt2 vt)
  end.

Lemma vstp_refl : forall K VT,
  vstp K VT VT.
Proof.
  intros. induction K; auto. simpl; auto.
  simpl. intros; eauto.
Qed.

Lemma vstp_trans : forall K VT1 VT2 VT3,
  vstp K VT1 VT2 -> vstp K VT2 VT3 -> vstp K VT1 VT3.
Proof.
  intros. induction K.
  - simpl. intros. auto.
  - simpl. intros. eauto.
Qed.


(* Semantic interpretation of typing *)

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

Definition vt_fun (T1 T2: tpe): tpe :=
  fun v =>
    match v with
    | vabs H ty =>
        forall vx,
          T1 vx ->
          exists vy,
            tevaln (vx::H) ty vy /\
            T2 vy
    | _ => False
    end.

(* we need to take a subtyping semantic interpretation
  a conversion from A to upper bound

  T1 should include a witness on how to convert to the upper bound, and that's what we need to store in the invariant

  look at the F-sub LR
*)


(* NOTE: we cannot define it like this: taking a val_type of T1
  A is val_kind K1, and T1 : A here is an instance of val_kind, probably a val_type or env_kv lookup
  However, the problem is: ttabs simply abstracts a type bound of some kind, and the type bound has no has_type judgement, which means we cannot use induction hypothesis in fundamental to generate a sem_type including val_type for type bound T1
*)


Definition vt_all K (TU : val_kind K) (TF : forall (VT1: val_kind K) (h: vstp K VT1 TU), tpe ) : tpe :=
  fun v =>
    match v with
    | vtabs H ty =>
        forall T1 h,
          exists vy,
            tevaln H ty vy /\
            (TF T1 h) vy
    | _ => False
    end.


(*
  The val_kind only relies on kn, and val_type is dependent on the has_kind, and has_kind does not rely on JT
  Thus, we say the LR is dependent on only JK, and leave the JT and wf_delta to the syntactic parts.
*)
Definition env_kv JK :=
  forall x K, indexr x JK = Some K -> val_kind K.

Lemma envkv_nil:
  env_kv nil.
Proof.
  intros ???. inversion H.
Defined.

Lemma envkv_cons: forall J K,
    val_kind K ->
    env_kv J ->
    env_kv (K::J).
Proof.
  intros. intros ???.
  destruct (Nat.eq_dec x (length J)). subst.
  rewrite indexr_head in H. inversion H. subst. eauto.
  rewrite indexr_skip in H. eapply X0. eauto. eauto.
Defined.


Print envkv_cons.




(*
Definition envkv_cons' J K (vk : val_kind K) (h2 : env_kv J) : env_kv (K::J) :=
  fun x K' =>
    match Nat.eq_dec x (length J) with
    | left e =>
        match e in _ = y return (indexr x (K::J) = Some K' -> val_kind K') with
        | eq_refl =>
            fun H =>
              match indexr_head in _ = y return (match y with Some K0 => val_kind K0 | _ => unit end) with
              | eq_refl => vk
              end
        end
    | right ne => h2 _ _ (indexr_skip _ _ ne)
    end.
*)


Require Import Coq.Arith.Compare_dec.

Lemma indexr_hit: forall {T} J' J (K:T) ,
    indexr (length J) (J' ++ K :: J) = Some K.
Proof.
  intros. rewrite indexr_skips. rewrite indexr_head. eauto. simpl. eauto.
Qed.

Lemma envkv_weaken: forall J' J K,
    val_kind K ->
    env_kv (J'++J) ->
    env_kv (J'++K::J).
Proof.
  intros. intros ???.
  destruct (Nat.eq_dec x (length J)). subst.
  rewrite indexr_hit in H. inversion H. subst. eauto.
  rewrite indexr_splice2 in H; eauto.
Defined.

Fixpoint val_type {JK T K} (h : has_kind JK T K) (W : env_kv JK) {struct h}: val_kind K :=
  match h, T, K return val_kind K with
  | k_bool _, _, _ =>
      vt_bool
  | k_var _ x K IX, _, _ =>
      W x K IX
  | k_fun _ T1 T2 h1 h2, _, _ =>
      vt_fun (val_type h1 W) (val_type h2 W)
  | k_all _ T1 T2 K1 h1 h, _, _ =>
    (* because we have added a constraint in env_type, the VT1 cannot be arbitrary, and we need to put the contraint here
    *)
      vt_all (K1) (val_type h1 W) (fun VT1 wff => val_type h (envkv_cons _ _ VT1 W)) (* then we should have a weaken_env_dt taking wff *)
  | k_tabs _ K1 T2 K2 h, _, _ =>
      (fun VT1 => val_type h (envkv_cons _ _ VT1 W))
  | k_tapp _ TF TX K1 K2 hf hx, _, _ =>
      val_type hf W (val_type hx W)
  | k_top _, _, _ =>
      vt_any
  end.


(* envk_wf is of type Set! (not entirely clear if it has to be) *)
Definition envk_wf JT JK := 
  prod (length JT = length JK) 
  (forall x T, indexr x JT = Some T ->
    { K : kn & prod
      (indexr x JK = Some K)
      (has_kind JK T K) }).

(* subtyping context interpretation *)
Definition env_dt JT JK (WFJ : env_kv JK) :=
  forall x T K (ht: indexr x JT = Some T) (hidx: indexr x JK = Some K) (hk: has_kind JK T K),
    vstp K (WFJ x K hidx) (val_type hk WFJ). (*vstp*)


Definition exp_type H J (h2: env_kv J) t T :=
  exists v (h1: has_kind J T KTpe),
    tevaln H t v /\
    val_type h1 h2 v.

(*
  forall (val_kind K) in h2[x], JT[x] = T -> val_type (has_kind JK T K) h2
  this is just env_dt

  because K can be higher-kind, we cannot simply do -> .., but need a relation of higher-kind, namely vstp

  This encodes V in LR
*)
Definition env_type (H: venv) (G: tenv) (JT:ktenv) (JK: kkenv) (h2: env_kv JK):=
  length H = length G /\
  env_dt JT JK h2 /\  (* the subtyping context, semantic bound *)
  forall x T,
    indexr x G = Some T ->
    exists v (h1: has_kind JK T KTpe),
      indexr x H = Some v /\
      val_type h1 h2 v.

(*
  envk_wf is of type Set, so we cannot do envk_wf /\ something,
  so we take envk_wf as an argument, and this is one of the semantic interpretation
  of the context, i.e. well-formed type context
*)
Definition sem_type G JT JK t T :=
  forall H (h2: env_kv JK) (hd: envk_wf JT JK) (* syntax regulation *),
    env_type H G JT JK h2 ->
    exp_type H JK h2 t T.


(* ---------- LR helper lemmas  ---------- *)

Lemma envk_wf_weaken JT JK (wf : envk_wf JT JK) : forall T K,
  has_kind JK T K ->
  envk_wf (map (splice (length JT) 1) (T :: JT)) (K :: JK).
Proof.
  intros. unfold envk_wf in *. destruct wf as [wfL wf]. 
  split. simpl. rewrite map_length. congruence. 
  intros x T' Hidx.
  bdestruct (x =? length JK); subst.
  rewrite <- wfL in Hidx. rewrite map_cons in Hidx. rewrite <- map_length with (f:=splice (length JT) 1) in Hidx at 1. rewrite indexr_head in Hidx. rewrite indexr_head. exists K. split; auto. inversion Hidx; subst. rewrite wfL. apply haskind_extend. auto.
  rewrite map_cons in Hidx. rewrite indexr_skip in Hidx. 2: rewrite map_length; lia. apply indexr_map'' in Hidx. destruct Hidx as [Tx [? ?]]. subst T'. destruct (wf x Tx H1) as [Kx [? ?]].
    rewrite indexr_skip; auto. exists Kx. split; auto. rewrite wfL. apply haskind_extend; auto.
Qed.


(* weakening *)


Lemma aux0: forall i i' J K
  (eq: i = i')
  (h2: forall i K, indexr i (J) = Some K -> val_kind K)
  (h2A: indexr i (J) = Some K -> val_kind K)
  (h2B: indexr i' (J) = Some K -> val_kind K)
  (eq2A: h2A = h2 i K)
  (eq2B: h2B = h2 i' K)
  eA eB,
    h2A eA = h2B eB.
Proof.
  intros. subst i'. subst. (* note: subst i' works, but not rewrite *)
  replace eA with eB. eauto. eapply proof_irrelevance.
Qed.

Lemma envkv_cons_head: forall J K1 vk h2 IX,
    envkv_cons J K1 vk h2 (length J) K1 IX = vk.
Proof.
  intros J K1 vk h2 IX.
  unfold envkv_cons.
  destruct (Nat.eq_dec (length J) (length J)) as [Heq | Hneq].
  - dependent destruction Heq.
    remember indexr_head. replace IX with e. 2: eapply proof_irrelevance.
    cbn.
    remember (eq_ind (if length J =? length J then Some K1 else indexr (length J) J)
      (fun o : option kn => o = Some K1) e (Some K1) e).
    simpl in e0.
    dependent destruction e0.
    cbn. eauto.
  - congruence.
Qed.

Lemma envkv_cons_skip: forall J K1 K i vk (h2:env_kv J) IX IX',
    i < length J ->
    envkv_cons J K1 vk h2 i K IX' = h2 i K IX.
Proof.
  intros.
  unfold envkv_cons.
  destruct (Nat.eq_dec i (length J)) as [Heq | Hneq].
  - lia.
  - eapply aux0. eauto. eauto. eauto.
Qed.


Lemma envkv_weaken_hit: forall J' J K1 vk h2 IX,
    envkv_weaken J' J K1 vk h2 (length J) K1 IX = vk.
Proof.
  intros.
  unfold envkv_weaken.
  destruct (Nat.eq_dec (length J) (length J)) as [Heq | Hneq].
  - dependent destruction Heq.
    remember (indexr_hit J' J K1). replace IX with e. 2: eapply proof_irrelevance.
    cbn.
    remember (eq_ind (indexr (length J) (J' ++ K1 :: J))
      (fun o : option kn => o = Some K1) e (Some K1) e).
    simpl in e0.
    dependent destruction e0.
    cbn. eauto.
  - congruence.
Qed.


Lemma envkv_weaken_lt: forall J' J K1 K i vk h2 IX IX',
    i < length J ->
    envkv_weaken J' J K1 vk h2 i K IX' = h2 i K IX.
Proof.
  intros.
  unfold envkv_weaken.
  destruct (Nat.eq_dec i (length J)) as [Heq | Hneq].
  - lia.
  - eapply aux0. bdestruct (i <? length J). eauto. lia. eauto. eauto.
Qed.

Lemma envkv_weaken_ge: forall J' J K1 K i i' vk h2 IX IX',
    i >= length J ->
    i' = i+1 ->
    envkv_weaken J' J K1 vk h2 i' K IX' = h2 i K IX.
Proof.
  intros.
  unfold envkv_weaken.
  destruct (Nat.eq_dec i' (length J)) as [Heq | Hneq].
  - lia.
  - eapply aux0. bdestruct (i' <? length J). lia. lia. eauto. eauto.
Qed.


Lemma aux1: forall J' J (h2 : env_kv (J' ++ J)) i K e K1 vk e1,
    h2 i K e = (envkv_weaken J' J K1 vk h2) (if i <? length J then i else i+1) K e1.
Proof.
  intros.
  bdestruct (i <? length J).
  - unfold envkv_weaken.
    remember (Nat.eq_dec i (length J)). destruct s. lia.
    remember (h2 i K) as h2A.
    remember (h2 (if i <? length J then i else i - 1) K) as h2B.
    unfold eq_ind.
    remember (indexr_splice2 J' J i K1 n) as IS.
    assert ((if i <? length J then i else i - 1) = i) as RW. bdestruct (i <? length J); lia.

    (* challenge: we need to show that
         h2A = h2B
       and
         e = e1
       but this is difficult, because h2A and h2B do not have the same type!

       we cannot state the equality directly:
         assert (h2A = h2B).  (* error *)

       we cannot rewrite:
        rewrite RW in Heqh2B.  (* error *)
     *)

    (* but using a helper lemma seems to work! *)
    eapply aux0. eauto. eauto. eauto.

  - unfold envkv_weaken.
    remember (Nat.eq_dec (i+1) (length J)). destruct s. lia.
    remember (h2 i K) as h2A.
    remember (h2 (if i + 1 <? length J then i + 1 else i + 1 - 1) K) as h2B.
    unfold eq_ind.
    remember (indexr_splice2 J' J (i + 1) K1 n) as IS.
    assert ((if i+1 <? length J then i+1 else i+1-1) = i) as RW. bdestruct (i+1 <? length J); lia.
    eapply aux0. eauto. eauto. eauto.
Qed.

Lemma aux2: forall J' J K1 k vk h2 VT1,
    (envkv_cons (J' ++ K1 :: J) k VT1 (envkv_weaken J' J K1 vk h2)) =
      (envkv_weaken (k :: J') J K1 vk (envkv_cons (J' ++ J) k VT1 h2)).
Proof.
  intros.
  eapply functional_extensionality_dep. intros i.
  eapply functional_extensionality_dep. intros K.
  eapply functional_extensionality_dep. intros IX.
  assert (indexr i (k :: J' ++ K1 :: J) = Some K) as IX'. eapply IX.
  bdestruct (i =? length J).
  - remember (envkv_weaken J' J K1 vk h2).
    remember (envkv_cons (J' ++ J) k VT1 h2).
    assert (K = K1). subst i. replace (k :: J' ++ K1 :: J) with ((k :: J') ++ K1 :: J) in IX'.
    rewrite indexr_hit in IX'. inversion IX'. eauto. eauto.
    subst i K. erewrite envkv_weaken_hit. erewrite envkv_cons_skip.
    2: { rewrite app_length. simpl. lia. }
    Unshelve. 2: rewrite indexr_hit; eauto.
    subst e.
    erewrite envkv_weaken_hit. eauto.
  - bdestruct (i <? length J).
    erewrite envkv_cons_skip. erewrite envkv_weaken_lt.
    erewrite envkv_weaken_lt. erewrite envkv_cons_skip.
    eauto.
    rewrite app_length. lia. eauto. eauto. rewrite app_length. simpl. lia.
    assert (i > length J). lia.
    assert (i-1 >= length J). lia.
    assert (i = i-1+1). lia.
    bdestruct (i =? length (J'++K1::J)).
    + subst i.
      assert (K = k). rewrite indexr_head in IX'. inversion IX'. eauto.
      subst K.
      erewrite envkv_cons_head. erewrite envkv_weaken_ge. erewrite envkv_cons_head. eauto.
      rewrite app_length. lia. rewrite app_length, app_length. simpl. lia.
    + erewrite envkv_weaken_ge. 3: eauto. 2: lia.
      erewrite envkv_cons_skip. 2: { eapply indexr_var_some' in IX'. simpl in *. rewrite app_length in *. simpl in *. lia. }
      erewrite envkv_weaken_ge. 3: eauto. 2: lia.
      erewrite envkv_cons_skip. eauto. eapply indexr_var_some' in IX'. simpl in *. rewrite app_length in *. simpl in *. lia.
      Unshelve.
      rewrite indexr_skip in IX'. eauto.
      rewrite app_length. simpl. lia.
      rewrite indexr_skips. rewrite indexr_skip, indexr_skips, indexr_skip in IX'; eauto.
      simpl. eauto. rewrite app_length. simpl. lia. eauto.
      rewrite indexr_skips. rewrite indexr_skip, indexr_skips, indexr_skip in IX'; eauto.
      simpl. eauto. rewrite app_length. simpl. lia. eauto.
      replace (((k :: J') ++ J)) with (k::J'++J). rewrite indexr_head in *. eauto. eauto.
      eapply indexr_var_some' in IX'. rewrite indexr_skips'.
      replace (k :: J' ++ K1 :: J) with ((k::J') ++ (K1::J)) in IX.
      rewrite indexr_skips' in IX. replace (i - length (K1::J)) with (i-1-length J) in IX. eauto.
      simpl. lia. simpl. lia. eauto. eauto.
      rewrite indexr_skip in IX'. eauto. eauto.
      rewrite indexr_skip in IX'. rewrite indexr_skips' in IX'. rewrite indexr_skips'.
      replace (i - length (K1::J)) with (i-1-length J) in IX'. eauto.
      simpl. lia. eauto. simpl. eauto. eauto.
Qed.

Lemma envkv_weaken_eq_extend: forall J K1 vk h2,
    envkv_weaken [] J K1 vk h2 = envkv_cons J K1 vk h2.
Proof.
  intros.
  eapply functional_extensionality_dep. intros i.
  eapply functional_extensionality_dep. intros K.
  eapply functional_extensionality_dep. intros IX.
  simpl in *.
  assert ((if i =? length J then Some K1 else indexr i J) = Some K). eapply IX.
  bdestruct (i =? length J).
  - inversion H. subst.
    rewrite envkv_cons_head, envkv_weaken_hit. eauto.
  - eapply indexr_var_some' in H as LT.
    erewrite envkv_cons_skip, envkv_weaken_lt; eauto.
    Unshelve. simpl. eauto.
Qed.


Lemma fun2_extensionality_transport
  {A : Type}
  {F F' : A -> Type}
  (Heq : forall a, F a = F' a)
  {T : A -> Type}
  (t1 : forall a, F a -> T a)
  (t2 : forall a, F' a -> T a)
  (Hbody :
     forall a (f : F a),
       t1 a f =
       t2 a (eq_rect _ (fun X => X) f _ (Heq a))) :
  (fun a f => t1 a f)
  =
  (fun a f => t2 a
      (eq_rect _ (fun X => X) f _ (Heq a))).
Proof.
  eapply functional_extensionality_dep; intro a.
  apply functional_extensionality_dep; intro f.
  apply Hbody.
Qed.

Lemma valt_weaken: forall T J' J K1 K vk (h1: has_kind (J'++J) T K) h2,
    val_type h1 h2 =
    val_type (haskind_weaken T J' J K K1 h1)
    (envkv_weaken J' J K1 vk h2).
Proof.
  intros T. induction T; intros; inversion h1; subst.
  - dependent destruction h1.
    simpl. split; eauto.
  - dependent destruction h1. simpl. auto.
  - dependent destruction h1.
    remember (k_var (J'++J) i K e) as hx1.
    remember ((haskind_weaken (TVar i) J' J K K1 hx1)) as hx1'.
    remember ((envkv_weaken J' J K1 vk h2)) as h2'.
    dependent destruction hx1. inversion Heqhx1. rewrite Heqhx1 in *.
    dependent destruction hx1'.
    simpl.
    subst h2'. eapply aux1.
  - (* TFun *)
    dependent destruction h1.
    simpl in *.
    assert (val_type h1_1 h2 = val_type (haskind_weaken T1 J' J KTpe K1 h1_1) (envkv_weaken J' J K1 vk h2)). eapply IHT1.
    assert (val_type h1_2 h2 = val_type (haskind_weaken T2 J' J KTpe K1 h1_2) (envkv_weaken J' J K1 vk h2)). eapply IHT2.
    rewrite H, H0. eauto.
  - (* TAll *)
    dependent destruction h1. simpl.
    specialize (hk_unique' _ _ _ h1_1 _ H1). intros. subst.
    specialize (hk_unique _ _ _ h1_2 H3). specialize (hk_unique _ _ _ h1_1 H1). intros; subst.
    rewrite IHT1 with (K1 := K1) (vk := vk). f_equal.
    apply functional_extensionality_dep. intros VT1.
    apply functional_extensionality. intros. 
    {
      specialize IHT2 with (J':=K2::J') (J:=J) (vk:=vk) (h1:=H3) (h2:=(envkv_cons (J'++J) K2 VT1 h2)).
      rewrite aux2.
      eapply IHT2.
    }
  - (* TTAbs *)
    dependent destruction h1.
    remember (k_tabs (J' ++ J) k T K2 h1) as h1'.
    dependent destruction h1'.
    simpl in *. eapply functional_extensionality.
    intros.
    specialize IHT with (J':=k::J') (h1:=h1') (h2:=(envkv_cons (J' ++ J) k x h2)) (vk:=vk).
    rewrite aux2. eapply IHT.
  - (* TTApp *)
    dependent destruction h1. simpl.
    specialize (IHT1) with (h1:=h1_1) (h2:=h2).
    erewrite IHT1.
    specialize (IHT2) with (h1:=h1_2) (h2:=h2).
    erewrite IHT2.
    eauto.
Qed.


Lemma valt_extend: forall T J K1 vk (h1: has_kind J T KTpe) h2 v2,
    val_type h1 h2 v2 <->
    val_type (haskind_extend T J KTpe K1 h1)
    (envkv_cons J K1 vk h2) v2.
Proof.
  intros.
  specialize valt_weaken with (J':=[]). simpl. intros. unfold haskind_extend.
  replace (envkv_cons J K1 vk h2) with (envkv_weaken [] J K1 vk h2).
  erewrite H. 2: eapply envkv_weaken_eq_extend. split; eauto.
Qed.


(* substitution *)

Lemma xxx4: forall J T1 K1 K2,
  has_kind J T1 K1 ->
  K1 = K2 ->
  has_kind J T1 K2.
Proof.
  intros.
  congruence.
Defined.


Lemma xxx3: forall (J' J: kkenv) K1 K2 i,
  i = length J ->
  indexr i (J' ++ K1 :: J) = Some K2 ->
  K1 = K2.
Proof.
  intros. subst i.
  erewrite indexr_skips in H0.
  erewrite indexr_head in H0.
  congruence.
  simpl. eauto.
Defined.


Fixpoint hask_subst T2: forall J' J T1 K1 K2,
    has_kind (J' ++ K1 :: J) T2 K2 ->
    has_kind J T1 K1 ->
    has_kind (J'++J) (subst T2 (length J) (splice (length J) (length J') T1)) K2.
Proof.
  destruct T2; intros; inversion H; subst; simpl in *.
  - eapply k_bool.
  - eapply k_top.
  - destruct (Nat.eq_dec i (length J)) as [Heq | Hneq].
    + eapply haskind_extend_mult. eapply xxx4. eauto. eapply xxx3; eauto.
    + eapply k_var.
      rewrite indexr_splice2 in H2. eapply H2. eauto.
  - eapply k_fun. eauto. eauto.
  - eapply k_all. eauto. rewrite splice_acc. 
    eapply hask_subst with (J':=K0::J'). eauto. eauto.
  - eapply k_tabs. rewrite splice_acc.
    eapply hask_subst with (J':=k::J'). eauto. eauto.
  - eapply k_tapp. eauto. eauto.
Defined.

Lemma hask_subst1: forall J T2 T1 K1,
    has_kind (K1 :: J) T2 KTpe ->
    has_kind J T1 K1 ->
    has_kind J (subst T2 (length J) T1) KTpe.
Proof.
  intros. eapply hask_subst with (J':=[]) in H0.
  simpl in H0. rewrite splice_zero in H0. eauto.
  simpl. eauto.
Defined.

Lemma hask_subst1': forall J T2 T1 K1 K,
    has_kind (K1 :: J) T2 K ->
    has_kind J T1 K1 ->
    has_kind J (subst T2 (length J) T1) K.
Proof.
  intros. apply hask_subst with (J':=[]) (T2:=T2) (K2:=K) in H0; auto.
  simpl in H0. rewrite splice_zero in H0; auto.
Defined.


Lemma aux1b: forall J' J K1 T1K WFJ i e0 e1 vy,
    i <> length J ->
    (envkv_weaken J' J K1 T1K WFJ) i KTpe e0 vy = WFJ (if i <? length J then i else i - 1) KTpe e1 vy.
Proof.
  intros.
  bdestruct (i <? length J).
  erewrite envkv_weaken_lt. eauto. eauto.
  erewrite envkv_weaken_ge. eauto. lia. lia.
Qed.

Lemma aux1b': forall J' J K1 T1K WFJ i e0 e1,
    i <> length J ->
    (envkv_weaken J' J K1 T1K WFJ) i KTpe e0 = WFJ (if i <? length J then i else i - 1) KTpe e1.
Proof.
  intros.
  bdestruct (i <? length J).
  erewrite envkv_weaken_lt. eauto. eauto.
  erewrite envkv_weaken_ge. eauto. lia. lia.
Qed.

Lemma aux1b'': forall J' J K1 K T1K WFJ i e0 e1,
    i <> length J ->
    (envkv_weaken J' J K1 T1K WFJ) i K e0 = WFJ (if i <? length J then i else i - 1) K e1.
Proof.
  intros.
  bdestruct (i <? length J).
  erewrite envkv_weaken_lt. eauto. eauto.
  erewrite envkv_weaken_ge. eauto. lia. lia.
Qed.

Lemma valt_extend': forall T J K1 K vk (h1: has_kind J T K) h2,
    val_type h1 h2 =
    val_type (haskind_extend T J K K1 h1)
    (envkv_cons J K1 vk h2).
Proof.
  intros.
  specialize valt_weaken with (J':=[]). simpl. intros. unfold haskind_extend.
  replace (envkv_cons J K1 vk h2) with (envkv_weaken [] J K1 vk h2).
  erewrite H. 2: eapply envkv_weaken_eq_extend. split; eauto.
Qed.

Lemma valt_extend'': forall T J K1 K vk (h1: has_kind J T K) (h' : has_kind (K1 ::J) (splice (length J) 1 T) K) h2,
    val_type h1 h2 =
    val_type h'
    (envkv_cons J K1 vk h2).
Proof.
  intros. pose ((haskind_extend T J K K1 h1)) as hk. specialize (hk_unique _ _ _ hk h'). intros; subst. apply valt_extend'.
Qed.


Lemma valt_subst: forall T2 J' J K1 K2 T1K WFJ T1 (h1f : has_kind (J'++K1 :: J) T2 K2) HK1,
    T1K = val_type (haskind_extend_mult J' T1 J K1 HK1) WFJ ->
    val_type h1f (envkv_weaken J' J K1 T1K WFJ) =
    val_type (hask_subst T2 J' J T1 K1 K2 h1f HK1) WFJ.
Proof.
  intros T2. induction T2; intros; inversion h1f.
  - dependent destruction h1f.
    simpl. eauto.
  - dependent destruction h1f. simpl. auto. 
  - dependent destruction h1f.
    remember (k_var (J' ++ K1 :: J) i K e) as hx1.
    remember (hask_subst (TVar i) J' J T1 K1 K hx1 HK1) as hx1'.
    remember (envkv_weaken J' J K1 T1K WFJ) as h2'.
    dependent destruction hx1. simpl.

    simpl in *. remember (Nat.eq_dec i (length J)).
    destruct s.
    + subst i.
      simpl in *.
      assert (K1 = K). eapply xxx3; eauto.
      subst K1.
      remember (haskind_extend_mult J' T1 J K).
      remember (xxx3 J' J K K x e1).
      remember (xxx4 J T1 K K HK1).
      compute in Heqhx1'.
      assert (h0 (e2 e0) = HK1). {
        subst h0. compute. remember (e2 e0).
        dependent destruction e3. eauto.
      }
      rewrite H0 in Heqhx1'. subst h2' h hx1'.
      subst x. rewrite envkv_weaken_hit.
      subst T1K. eauto.

    + dependent destruction hx1'.
      simpl. subst h2'. eapply aux1b''. eauto.

  - (*TFun*) dependent destruction h1f. simpl.
    assert (H21: val_type h1f1 (envkv_weaken J' J K1 T1K WFJ) = val_type (hask_subst T2_1 J' J T1 K1 KTpe h1f1 HK1) WFJ). apply IHT2_1. auto. rewrite H21.
    assert (H22: val_type h1f2 (envkv_weaken J' J K1 T1K WFJ) = val_type (hask_subst T2_2 J' J T1 K1 KTpe h1f2 HK1) WFJ). apply IHT2_2. auto. rewrite H22. auto.
  - (*TAll*) 
    dependent destruction h1f. simpl.
    specialize (hk_unique' _ _ _ H2 _ h1f1). intros; subst K2. specialize (hk_unique _ _ _ h1f1 H2). specialize (hk_unique _ _ _ h1f2 H4). intros; subst h1f2 h1f1.
    rewrite IHT2_1 with (T1:=T1) (HK1:=HK1); auto. f_equal; auto.
    apply functional_extensionality_dep. intros VT1. 
    apply functional_extensionality. intros. 
    assert (HVT: forall VT1, val_type (haskind_extend_mult (K0 :: J') T1 J K1 HK1) (envkv_cons (J' ++ J) K0 VT1 WFJ) = val_type (haskind_extend_mult J' T1 J K1 HK1) WFJ). { intros.
      simpl. elim_eq_rect. simpl. elim_eq_rect. simpl.
      rewrite <- valt_extend'. reflexivity.
    }    
    {
      rewrite splice_acc. rewrite aux2.
      specialize (IHT2_2 (K0 :: J') J K1 KTpe T1K (envkv_cons (J' ++ J) K0 VT1 WFJ) T1 H4 HK1).
      specialize (HVT VT1). rewrite <- HVT in H.
      specialize (IHT2_2 H). auto.
    }
  - (*TTAbs*) dependent destruction h1f. remember (k_tabs (J' ++ K1 :: J) k T2 K2 h1f) as h1f'.
    dependent destruction h1f'. simpl. rewrite splice_acc.
    apply functional_extensionality. intro vk.
    rewrite aux2.
    assert (HT1K: val_type (haskind_extend_mult (k :: J') T1 J K1 HK1) (envkv_cons (J' ++ J) k vk WFJ) = val_type (haskind_extend_mult J' T1 J K1 HK1) WFJ). { intros.
      simpl. elim_eq_rect. simpl. elim_eq_rect. simpl.
      rewrite <- valt_extend'. reflexivity.
    } rewrite <- HT1K in H.
    specialize (IHT2 (k :: J')) with (h1f := h1f') (WFJ := (envkv_cons (J' ++ J) k vk WFJ)) (T1K := T1K). specialize (IHT2 T1 HK1 H).
    replace (val_type h1f' (envkv_weaken (k :: J') J K1 T1K (envkv_cons (J' ++ J) k vk WFJ))) with (val_type (hask_subst T2 (k :: J') J T1 K1 K2 h1f' HK1) (envkv_cons (J' ++ J) k vk WFJ)). (*using IHT2*)
    auto.
  - (*TTApp*) dependent destruction h1f. simpl.
    specialize (IHT2_2) with (h1f := h1f2). specialize (IHT2_2 T1K WFJ T1 HK1 H). rewrite IHT2_2.
    remember ((val_type (hask_subst T2_2 J' J T1 K1 K0 h1f2 HK1) WFJ)) as VT2.
    specialize (IHT2_1) with (h1f := h1f1). specialize (IHT2_1 T1K WFJ T1 HK1 H). rewrite IHT2_1. auto.
Qed.


Lemma valt_subst1: forall T2 J K1 T1K WFJ T1 (h1f : has_kind (K1 :: J) T2 KTpe) HK1 vy,
  T1K = val_type HK1 WFJ ->
  val_type h1f (envkv_cons J K1 T1K WFJ) vy =
  val_type (hask_subst1 J T2 T1 K1 h1f HK1) WFJ vy.
Proof.
  intros.
  specialize valt_subst with (J':=[]). simpl. intros. unfold hask_subst1.
  unfold eq_rect. remember (splice_zero T1 (length J)).
  clear Heqe.
  dependent destruction e.
  replace (envkv_cons J K1 T1K WFJ) with (envkv_weaken [] J K1 T1K WFJ).
  erewrite H0 with (T1:=T1) (HK1:=HK1). eauto. 2: eapply envkv_weaken_eq_extend.
  unfold eq_rec_r, eq_rec, eq_rect.
  remember (eq_sym (splice_zero T1 (length J))). clear Heqe. dependent destruction e.
  eauto.
Qed.

Lemma valt_subst1': forall T2 J K K1 T1K WFJ T1 (h1f : has_kind (K1 :: J) T2 K) HK1 ,
  T1K = val_type HK1 WFJ ->
  val_type h1f (envkv_cons J K1 T1K WFJ) =
  val_type (hask_subst1' J T2 T1 K1 K h1f HK1) WFJ .
Proof.
  intros.
  specialize valt_subst with (J':=[]). simpl. intros. unfold hask_subst1'.
  unfold eq_rect. remember (splice_zero T1 (length J)).
  clear Heqe.
  dependent destruction e.
  replace (envkv_cons J K1 T1K WFJ) with (envkv_weaken [] J K1 T1K WFJ).
  erewrite H0 with (T1:=T1) (HK1:=HK1). eauto. 2: eapply envkv_weaken_eq_extend.
  unfold eq_rec_r, eq_rec, eq_rect.
  remember (eq_sym (splice_zero T1 (length J))). clear Heqe. dependent destruction e.
  eauto.
Qed.



(* ---------- env extension lemmas  ---------- *)

Lemma envdt_empty : forall W,
  env_dt [] [] W.
Proof.
  intros. unfold env_dt; intros. inversion ht.
Qed.

Lemma envt_empty: forall W,
    env_type [] [] [] [] W.
Proof.
  intros. split. eauto. split. apply envdt_empty. intros. inversion H.
Qed.

Lemma envt_extend: forall E G JT JK h2 v1 T1 (h1: has_kind JK T1 KTpe),
    env_type E G JT JK h2 ->
    val_type h1 h2 v1 ->
    env_type (v1::E) (T1::G) JT JK h2.
Proof.
  intros.
  remember H as WFE. clear HeqWFE.
  destruct H as (? & Wfdt & ?). split. simpl. eauto.
  split. auto.
  intros x T IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX. subst T1.
    exists v1. rewrite <- H. rewrite indexr_head. eauto.
  - rewrite indexr_skip in IX; eauto.
    eapply WFE in IX as IX. destruct IX as (v2 & ? & ?).
    exists v2. rewrite indexr_skip; eauto. lia.
Qed.

Lemma envdt_extend : forall JT JK U K1 (vk : val_kind K1) (hk : has_kind JK U K1) WFJ,
  env_dt JT JK WFJ ->
  envk_wf JT JK ->
  vstp K1 vk (val_type hk WFJ) ->
  env_dt (map (splice (length JT) 1) (U :: JT)) (K1 :: JK) (envkv_cons JK K1 vk WFJ).
Proof.
  intros. unfold env_dt. intros. 
  bdestruct (x =? length JK); subst.
  - pose hidx as hidx'. rewrite indexr_head in hidx'. inversion hidx'; subst. clear hidx'. rewrite envkv_cons_head.
    rewrite map_cons in ht. destruct H0 as [HL ?]. rewrite <- HL in ht. rewrite <- map_length with (f := splice (length JT) 1) in ht at 1. rewrite indexr_head in ht. rewrite HL in ht. inversion ht; subst; clear ht.
    specialize (valt_extend' U JK K K vk hk WFJ). intros. remember ((haskind_extend U JK K K hk)) as hext. specialize (hk_unique _ _ _ hext hk0). intros; subst.
    congruence.
  - rewrite map_cons in ht. destruct H0 as [HL ?]. rewrite HL in ht. rewrite indexr_skip in ht. 2: rewrite map_length; congruence.
    apply indexr_map' in ht. destruct ht as [T' [? ?]]. subst. specialize (s x T' H0). destruct s as [K' [? ?]]. 
    pose hidx as hidx'. rewrite indexr_skip in hidx'; auto. rewrite e in hidx'. inversion hidx'; subst. clear hidx'.
    specialize (valt_extend' T' JK K1 K vk h WFJ). intros. remember ((haskind_extend T' JK K K1 h)) as hext. specialize (hk_unique _ _ _ hext hk0). intros; subst. rewrite <- H3.
    rewrite envkv_cons_skip with (IX := e). auto.
    apply indexr_var_some' in hidx. simpl in hidx. lia.
Qed.

Lemma envt_extendk: forall E G JT JK h2 K1 (vk: val_kind K1) U
    (hk: has_kind JK U K1) (Wfd : envk_wf JT JK), 
    env_type E G JT JK h2 ->
    vstp K1 vk (val_type hk h2) ->
    env_type E (map (splice (length JK) 1) G) (map (splice (length JT) 1) (U :: JT)) (K1::JK) (envkv_cons JK K1 vk h2).
Proof.
  intros.
  remember H as WFE. clear HeqWFE.
  destruct H as (?& Wfdt & ?). 
  split. rewrite map_length. eauto.
  split. eapply envdt_extend; eauto. 
  intros x T IX.
  eapply indexr_map' in IX. destruct IX as (T' & IX & ?).
  eapply WFE in IX as IX. destruct IX as (v2 & ? & ? & ?).
  exists v2. subst T.
  exists (haskind_extend _ _ _ _ x0).
  split. eauto.
  edestruct valt_extend. eauto.
Qed.


(* equivalence *)

Lemma has_kind_subst_inverse : forall T2 J J' T1 K1 K2,
    has_kind (J'++J) (subst T2 (length J) (splice (length J) (length J') T1)) K2 ->
    has_kind J T1 K1 ->
    has_kind (J' ++ K1 :: J) T2 K2.
Proof.
  induction T2; intros; simpl in H.
  - dependent destruction H. constructor.
  - dependent destruction H. constructor.
  - destruct (Nat.eq_dec i (length J)); subst.
      constructor. rewrite indexr_skips; auto. rewrite indexr_head.
      apply (haskind_extend_mult J') in H0. specialize (hk_unique' _ _ _ H0 _ H); intros. congruence.
    dependent destruction H. bdestruct (i <? (length J)). constructor.
      rewrite indexr_skips; auto. rewrite indexr_skips in e; auto. rewrite indexr_skip; auto. simpl; lia.
      constructor. replace i with (S (i - 1)). rewrite <- indexr_insert_ge. auto. lia. lia.
  - dependent destruction H. constructor; auto. eapply IHT2_1; eauto. eapply IHT2_2; eauto.
  - dependent destruction H. apply k_all with (K1:=K0). eapply IHT2_1; eauto. specialize (IHT2_2 J (K0 :: J') T1 K1 KTpe). apply IHT2_2; auto. simpl. rewrite splice_acc in H0. auto.
  - dependent destruction H. constructor; auto. specialize (IHT2 J (k :: J') T1 K1 K2). apply IHT2; auto. simpl. rewrite splice_acc in H. auto.
  - dependent destruction H. apply k_tapp with (K1 := K0). eapply IHT2_1; eauto. eapply IHT2_2; eauto.
Qed.

(* syntactic shape before substitution, anti-substitution lemma *)
Lemma has_kind_subst1_inverse : forall J T1 T2 K1 K,
    has_kind J T1 K1 ->
    has_kind J (subst T2 (length J) T1) K ->
    has_kind (K1 :: J) T2 K.
Proof.
  intros. specialize (has_kind_subst_inverse T2 J [] T1 K1 K). simpl. rewrite splice_zero. auto.
Qed.

(* ty_preservation *)
Lemma eq_type_preserve_kind : forall J T1 T2 K (heq: eq_type J T1 T2),
  (has_kind J T1 K -> has_kind J T2 K) * (has_kind J T2 K -> has_kind J T1 K).
Proof.
  intros. generalize dependent K. induction heq; auto; intros.
  - specialize (IHheq K); destruct IHheq. auto.
  - specialize (IHheq1 K); destruct IHheq1. auto. specialize (IHheq2 K); destruct IHheq2. auto.
  - specialize (IHheq1 K); destruct IHheq1. auto. specialize (IHheq2 K); destruct IHheq2. auto. split; intros.
    dependent destruction H. constructor; auto.
    dependent destruction H. constructor; auto.
  - split; intros. dependent destruction H.
    specialize (IHheq1 K1); destruct IHheq1. auto. specialize (IHheq2 KTpe ); destruct IHheq2. apply k_all with (K1 := K1); auto. 
    specialize (hk_unique' _ _ _ H _ h); intros; subst. auto. 
    dependent destruction H. 
    specialize (IHheq1 K1); destruct IHheq1. auto. specialize (IHheq2 KTpe ); destruct IHheq2. apply k_all with (K1 := K1); auto.
    apply h3. apply h0 in h. specialize (hk_unique' _ _ _ h _ H). intros; subst; congruence.
  - split; intros.
    dependent destruction H. constructor. specialize (IHheq K2); destruct IHheq.  auto.
    dependent destruction H. constructor. specialize (IHheq K2); destruct IHheq. auto.
  - split; intros; dependent destruction H.
    apply k_tapp with (K1 := K1). specialize (IHheq1 (KArr K1 K2)); destruct IHheq1. auto. auto. specialize (IHheq2 K1); destruct IHheq2; auto.  
    apply k_tapp with (K1 := K1). specialize (IHheq1 (KArr K1 K2)); destruct IHheq1. auto. auto. specialize (IHheq2 K1); destruct IHheq2; auto.
  - subst. split; intros. 
    dependent destruction H. dependent destruction H. apply hask_subst1' with (K1 := K0); auto. rewrite splice_zero; auto.
    (* we need a witness for T1 :: K1, but do we really need this lemma? according to the stp rule *)
    apply (k_tapp) with (K1:=K1); auto. constructor. rewrite splice_zero in H.
    eapply has_kind_subst1_inverse; eauto.
Defined.

Lemma eq_type_preserve_kind' : forall {J T1 T2 K},
  eq_type J T1 T2 ->
  has_kind J T1 K -> has_kind J T2 K.
Proof.
  intros. specialize (eq_type_preserve_kind _ _ _ K H). intros. destruct H1; auto.
Qed.


Lemma stp_preserve_kind : forall JT JK T1 T2 K,
  envk_wf JT JK ->
  stp JT JK T1 T2 ->
  (has_kind JK T1 K -> has_kind JK T2 K) * (has_kind JK T2 K -> has_kind JK T1 K).
Proof.
  intros. rename H into Hwf. generalize dependent K. induction H0; intros; simpl.
  - split; intros; auto.
  - destruct (IHstp1 Hwf K0). destruct (IHstp2 Hwf K0). auto.
  - split; intros. specialize (hk_unique' _ _ _ h _ H); intros. subst. constructor. dependent destruction H. auto.
  - destruct (IHstp1 Hwf K). destruct (IHstp2 Hwf K). split; intros. dependent destruction H; constructor; auto. dependent destruction H; constructor; auto.
  - split; auto.
  - split; intros. 
    dependent destruction H. destruct Hwf as [HL Hwf]. destruct (Hwf x T e) as [Kx [? ?]]. specialize (indexr_unique e0 e1). intros; subst. auto.
    constructor. destruct Hwf as [HL Hwf]. destruct (Hwf x T e) as [Kx [? ?]]. specialize (hk_unique' _ _ _ H _ h0). intros; subst. auto.  
  - assert (envk_wf (map (splice (length JT) 1) (U :: JT)) (K1 :: JK)). apply envk_wf_weaken; auto.
    split; intros. 
    dependent destruction H1. apply k_all with (K1 := K1); auto. specialize (hk_unique' _ _ _ h _ H1_); intros; subst. destruct (IHstp H KTpe); auto.
    dependent destruction H1. apply k_all with (K1 := K0); auto. specialize (hk_unique' _ _ _ h _ H1_); intros; subst. destruct (IHstp H KTpe); auto.
  - assert (envk_wf (map (splice (length JT) 1) ((TopK K1) :: JT)) (K1 :: JK)). apply envk_wf_weaken; auto. apply hask_TopK.
    split; intros. 
    dependent destruction H1. constructor. destruct (IHstp H K2); auto. 
    dependent destruction H1. constructor. destruct (IHstp H K2); auto.
  - split; intros; dependent destruction H.
    apply k_tapp with (K1:=K1); auto. destruct (IHstp Hwf (KArr K1 K2)); auto.
    apply k_tapp with (K1:=K1); auto. destruct (IHstp Hwf (KArr K1 K2)); auto.
  - (*eq_type_preserve*) intros. split; intros. 
    specialize (hk_unique' _ _ _ h _ H); intros; congruence.
    specialize (hk_unique' _ _ _ h0 _ H); intros; congruence.
Defined.

Lemma stp_preserve_kind' : forall {JT JK T1 T2 K},
  envk_wf JT JK ->
  stp JT JK T1 T2 ->
  has_kind JK T1 K -> has_kind JK T2 K.
Proof.
  intros. specialize (stp_preserve_kind _ _ _ _ K H H0). intros. destruct H2; auto.
Qed.


(* ---------- LR fundamental property of equiv, stp ---------- *)

Lemma val_type_irrel : forall J T K (WFJ: env_kv J) (h1 h2: has_kind J T K),
  val_type h1 WFJ = val_type h2 WFJ.
Proof.
  intros. specialize (hk_unique J T K h1 h2); intros; subst; auto.
Qed.

Lemma vstp_top : forall K (VT : val_kind K) JK WFJ (hk : has_kind JK (TopK K) K),
  vstp K VT (val_type hk WFJ).
Proof.
  induction K; intros.
  - simpl; intros.  dependent destruction hk. simpl. unfold vt_any; auto.
  - simpl in VT. intros vt. fold val_kind in vt.
    dependent destruction hk. simpl. apply IHK2.
Qed.


Lemma val_type_equiv : forall J T1 T2 K (h1: has_kind J T1 K) (h2: has_kind J T2 K) (WFJ : env_kv J),
  eq_type (J) T1 T2 ->
  val_type h1 WFJ = val_type h2 WFJ.
Proof.
  intros. generalize dependent K. induction H; intros.
  - apply val_type_irrel; auto.
  - specialize (IHeq_type WFJ _ h2 h1). destruct IHeq_type. split; auto.
  - specialize (eq_type_preserve_kind' H h1). intros. specialize (IHeq_type2 WFJ K H1 h2). specialize (IHeq_type1 WFJ K h1 H1). rewrite IHeq_type1. auto.
  - dependent destruction h1. dependent destruction h2. simpl. f_equal.
    apply IHeq_type1. apply IHeq_type2.
  - dependent destruction h1. dependent destruction h2. simpl. f_equal.
    apply functional_extensionality. intros.
    specialize (hk_unique' _ _ _ h _ h1_1); intros; subst.
    specialize (eq_type_preserve_kind' H h); intros. specialize (hk_unique' _ _ _ H1 _ h2_1); intros; subst. 
    rewrite IHeq_type1 with (h2:=h2_1). f_equal. 
    apply functional_extensionality_dep. intros vt2. apply functional_extensionality. intros.
    apply IHeq_type2.
  - dependent destruction h1. dependent destruction h2. simpl.
    apply functional_extensionality. intros.
    specialize (IHeq_type (envkv_cons J K1 x WFJ) K2 h1 h2). auto.
  - dependent destruction h1. dependent destruction h2. simpl.
    specialize (eq_type_preserve_kind' H0 h1_2); intros. specialize (hk_unique' _ _ _ h2_2 _ H1). clear H1. intros; subst.
    specialize (IHeq_type1 WFJ (KArr K1 K2) h1_1 h2_1). specialize (IHeq_type2 WFJ (K1) h1_2 h2_2).
    rewrite IHeq_type2. rewrite IHeq_type1. auto.
  - dependent destruction h1. simpl. dependent destruction h1_1. simpl. erewrite valt_subst1'; eauto. unfold hask_subst1'.
    unfold eq_rect. remember (splice_zero T1 (length J)).
    clear Heqe.
    dependent destruction e.
    apply val_type_irrel.
Defined.

Lemma vstp_stp : forall JK JT K T1 T2 WFJ (WFD : env_dt JT JK WFJ) (wfd: envk_wf JT JK) (h1: has_kind JK T1 K) (h2: has_kind JK T2 K), 
  stp JT JK T1 T2 ->
  vstp K (val_type h1 WFJ) (val_type h2 WFJ).
Proof.
  intros. generalize dependent K. generalize dependent wfd. induction H; intros.
  - dependent destruction h1. dependent destruction h2. simpl; auto.
  - specialize (stp_preserve_kind' wfd H h1). intros. 
    specialize (IHstp1 WFJ WFD wfd K0 h1 H1). specialize (IHstp2 WFJ WFD wfd K0 H1 h2). eapply vstp_trans; eauto.
  - dependent destruction h2. simpl. intros. unfold vt_any. auto.
  - dependent destruction h1. dependent destruction h2. simpl. intros. dependent destruction v; auto. simpl; intros.
    specialize (H1 vx). 
    specialize (IHstp1 WFJ WFD wfd KTpe h2_1 h1_1 vx H2). specialize (H1 IHstp1). destruct H1 as [vy [? ?]]. 
    exists vy. split; auto.
    specialize (IHstp2 WFJ WFD wfd KTpe h1_2 h2_2 vy). auto.
  - specialize (hk_unique _ _ _ h1 h2). intros; subst. apply vstp_refl.
  - dependent destruction h1; simpl. unfold env_dt in WFD. apply WFD. auto.
  - dependent destruction h1. dependent destruction h2. specialize (hk_unique' _ _ _ h1_1 _ h2_1); intros; subst. specialize (hk_unique _ _ _ h1_1 h2_1); intros; subst. 
    simpl; intros. dependent destruction v; auto. simpl in H0. simpl.
    intros. specialize (H0 T1 h0). destruct H0 as [vy [? ?]].
    exists vy. split; auto.
    specialize (hk_unique' _ _ _ h _ h2_1); intros; subst K2. 
    pose (envkv_cons JK K1 T1 WFJ) as HEK.
    assert (HED : env_dt (map (splice (length JT) 1) (U :: JT)) (K1 :: JK) HEK). { apply envdt_extend with (hk:=h2_1); auto. }
    pose (envk_wf_weaken JT JK wfd U K1 h2_1) as HEd.
    specialize (IHstp HEK HED HEd KTpe h1_2 h2_2 vy). auto.
  - dependent destruction h1. dependent destruction h2. intros VT. simpl. 
    pose ((envkv_cons JK K1 VT WFJ)) as HEK.
    pose (envkv_cons JK K1 (val_type (hask_TopK K1 JK) WFJ) WFJ) as HEK'.
    assert (HED : env_dt (map (splice (length JT) 1) ((TopK K1) :: JT)) (K1 :: JK) HEK). { apply envdt_extend with (hk:=(hask_TopK K1 JK)); auto. apply vstp_top. }
    pose (envk_wf_weaken JT JK wfd (TopK K1) K1 (hask_TopK K1 JK)) as HEd.
    specialize (IHstp HEK HED HEd K2 h1 h2). auto. 
  - dependent destruction h1. dependent destruction h2. simpl.
    specialize (hk_unique' _ _ _ h1_2 _ h2_2); intros; subst. specialize (hk_unique _ _ _ h1_2 h2_2); intros; subst.
    specialize (IHstp WFJ WFD wfd (KArr K0 K2) h1_1 h2_1). apply IHstp.
  - rewrite val_type_equiv with (h2:=h2); auto. apply vstp_refl.  
Qed.

(* this can be derived from general vstp *)
Lemma val_type_stp : forall JT JK T1 T2 (hs: stp JT JK T1 T2) (h1: has_kind JK T1 KTpe) (h2: has_kind JK T2 KTpe) (WFJ : env_kv JK) (WFD: env_dt JT JK WFJ) (wfd : envk_wf JT JK) vx,
  val_type h1 WFJ vx -> val_type h2 WFJ vx.
Proof.
  intros. specialize (vstp_stp JK JT KTpe T1 T2 WFJ WFD wfd h1 h2 hs).
  intros. simpl in H0. auto.
Qed. 



(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_true: forall G JT JK,
    sem_type G JT JK ttrue TBool.
Proof.
  intros.
  intros E WFJ WFE.
  exists (vbool true).
  exists (k_bool JK).
  split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto.
Qed.

Lemma sem_false: forall G JT JK,
    sem_type G JT JK tfalse TBool.
Proof.
  intros.
  intros E WFJ WFE.
  exists (vbool false).
  exists (k_bool JK).
  split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto.
Qed.

Lemma sem_var: forall G JT JK x T,
    indexr x G = Some T ->
    sem_type G JT JK (tvar x) T.
Proof.
  intros.
  intros E WFJ WFΔ WFE.
  eapply WFE in H as IX. destruct IX as (v & h1 & IX & VX).
  exists v.
  eexists h1.
  split.
  - exists 0. intros. destruct n. lia. simpl. rewrite IX. eauto.
  - eauto.
Qed.

Lemma sem_abs: forall G JT JK t T1 T2,
    sem_type (T1::G) JT JK t T2 ->
    has_kind JK T1 KTpe ->
    has_kind JK T2 KTpe ->
    sem_type G JT JK (tabs t) (TFun T1 T2).
Proof.
  intros ? ? ? ? ? ? HY W1 W2. intros E WFJ WFΔ WFE.
  eexists _.
  exists (k_fun _ _ _ W1 W2).
  split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros vx VX.
    edestruct HY as (vy & ? & ? & ? ). auto. eauto. eapply envt_extend; eauto.
    specialize (hk_unique _ _ _ W2 x). intros. subst.
    exists vy. split. eauto. eauto.
Qed.

Lemma sem_app: forall G JT JK f t T1 T2,
    sem_type G JT JK f (TFun T1 T2) ->
    sem_type G JT JK t T1 ->
    sem_type G JT JK (tapp f t) T2.
Proof.
  intros ? ? ? ? ? ? ? HF HX. intros H WFJ WFΔ WFE.
  destruct (HF H WFJ WFΔ WFE) as (vf & h1f & STF & VF).
  destruct (HX H WFJ WFΔ WFE) as (vx & h1x & STX & VX).
  dependent destruction h1f.
  destruct vf; simpl in VF; intuition.
  replace h1x with h1f1 in *. 2: eapply hk_unique.
  edestruct VF as (vy & STY & VY). eauto.
  exists vy.
  exists h1f2.
  split.
  - destruct STF as (n1 & STF).
    destruct STX as (n2 & STX).
    destruct STY as (n3 & STY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite STF, STX, STY. 2,3,4: lia.
    eauto.
  - eauto.
Qed.

Lemma sem_tabs: forall G JT JK t K1 U T2,
    sem_type (map (splice (length JK) 1) G) (map (splice (length JT) 1) (U :: JT)) (K1::JK) t T2 ->
    has_kind JK U K1 ->
    has_kind (K1::JK) T2 KTpe ->
    sem_type G JT JK (ttabs t) (TAll U T2).
Proof.
  intros ? ? ? ? ? ? ? HY W1 W2. intros E WFJ WFΔ WFE.
  eexists _.
  eexists (k_all _ _ _ _ W1 W2).
  split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros VK1 VStp. 
    edestruct HY as (vy & ? & ? & ?). apply envk_wf_weaken; auto. eapply envt_extendk; eauto.
    specialize (hk_unique _ _ _ W2 x). intros. subst.
    exists vy. split. eauto. eauto.
Qed.

Lemma sem_tapp: forall G JT JK t T1 T2 U,
    sem_type G JT JK t (TAll U T2) ->
    stp JT JK T1 U ->
    sem_type G JT JK (ttapp t T1) (subst T2 (length JT) T1).
Proof.
  intros ? ? ? ? ? ? ? HF HX. intros E WFJ WFΔ WFE.
  destruct (HF E WFJ WFΔ WFE) as (vf & h1f & STF & VF).
  dependent destruction h1f.
  destruct vf; simpl in VF; intuition.
  assert (length JK = length JT). { destruct WFΔ. auto. } rewrite <- H.
  specialize (stp_preserve_kind _ _ _ _ K1 WFΔ HX). intro Hkp. destruct Hkp as [Hkp1 Hkp2]. specialize (Hkp2 h1f1). 
  remember (val_type h1f1 WFJ) as T1K. remember (val_type Hkp2 WFJ) as UK.
  (* edestruct (VF T1K) as (vy & STY & VY). {
    subst. admit.
  } *)
  edestruct (VF UK) as (vy & STY & VY). { subst. destruct WFE as [? [WFD ?]]. eapply vstp_stp; eauto. }
  exists vy.
  exists (hask_subst1 _ _ _ _ h1f2 Hkp2).
  split.
  - destruct STF as (n1 & STF).
    destruct STY as (n2 & STY).
    exists (1+n1+n2). intros. destruct n. lia. simpl. rewrite STF, STY. 2,3: lia. eauto.
  - erewrite <-valt_subst1. 2: eauto. auto.
Qed.

Lemma sem_stp: forall G JT JK t T1 T2, stp JT JK T1 T2 ->
    has_kind JK T2 KTpe ->
    has_type G JT JK t T1 ->
    sem_type G JT JK t T1 ->
    sem_type G JT JK t T2.
Proof.
  intros ?????? HS HK HW HX. intros H WFJ Hwf WFE.
  edestruct HX as (vx & h1 & A & VX). auto. eauto.
  eexists vx.
  exists HK.
  split.
  - eauto.
  - eapply val_type_stp; eauto. destruct WFE as [? [? ?]]; auto.
Qed. 

(* ---------- LR fundamental property  ---------- *)

Theorem fundamental: forall G JT JK t T,
    has_type G JT JK t T ->
    sem_type G JT JK t T.
Proof.
  intros ? ? ? ? ? W.
  induction W.
  - eapply sem_true; eauto.
  - eapply sem_false; eauto.
  - eapply sem_var; eauto.
  - eapply sem_abs; eauto.
  - eapply sem_app; eauto.
  - eapply sem_tabs; eauto. 
    { intros ? ? ? ?. pose hd as hd'. destruct hd' as [HL ?]. rewrite map_length in HL. simpl in HL. inversion HL. rewrite H2 in *. apply IHW; auto. } 
  - eapply sem_tapp; eauto.
  - eapply sem_stp; eauto.
Qed.

Corollary safety: forall t T,
  has_type [] [] [] t T ->
  exp_type [] [] (envkv_nil) t T.
Proof.
  intros. eapply fundamental in H as ST; eauto.
  edestruct (ST []) as (v & ? & ? & ?). 
  unfold envk_wf. split; auto. intros. inversion H0.
  eapply envt_empty.
  exists v, x. intuition. eapply H1.
Qed.

End STLC.
