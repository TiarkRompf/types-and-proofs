(* Full safety for System F-Omega (PTS-style) *)

(*

An LR-based termination and semantic soundness proof.

Canonical big-step cbv semantics.

Combining type abstraction and type operators (System F-Omega).


THIS FILE (via stlc_tabs_topr_pts.v):
- add dependent application TPi

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
  | TPi    : tm -> tm -> tm

(*| TKArr  : tm -> tm -> tm  (* TFun *)
  | TTAbs  : tm -> tm -> tm  (* tabs *)
  | TTApp  : tm -> tm -> tm  (* tapp *) *)

  | ttrue  : tm
  | tfalse : tm
  | tvar   : id -> tm
  | tapp   : tm -> tm -> tm
  | tabs   : tm -> tm
  | ttapp  : tm -> tm(*ty!*) -> tm
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
Definition kenv := list (bool * tm). (*ty*)

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
      | ttapp ef T1   =>
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
  | TAll k t      => TAll k(*!*) (splice i n t)
  | TPi t1 t2     => TPi t1(*!*) (splice i n t2)
(*| TKArr t1 t2   => TKArr (splice i n t1) (splice i n t2)
  | TTAbs k t     => TTAbs k (splice i n t)
  | TTApp t1 t2   => TTApp (splice i n t1) (splice i n t2) *)
  | ttrue         => ttrue
  | tfalse        => tfalse
  | tvar x        => tvar x
  | tapp t1 t2    => tapp (splice i n t1) (splice i n t2)
  | tabs t1       => tabs (splice i n t1)
  | ttapp t1 t2   => ttapp (splice i n t1) (splice i n t2)
  | ttabs t1 t2   => ttabs t1(*?*) (splice i n t2)
  end.

Fixpoint subst (t: tm) (i: nat) (u:tm): tm :=
  match t with
  | TStar         => TStar
  | TBox          => TBox
  | TBool         => TBool
  | TVar x        => if Nat.eq_dec x i then u else TVar (if x <? i then x else x-1)
  | TFun t1 t2    => TFun (subst t1 i u) (subst t2 i u)
  | TAll k t      => TAll k(*!*) (subst t i (splice i 1 u))
  | TPi t1 t2     => TPi t1(*!*) (subst t2 i (splice i 1 u))
(*| TKArr t1 t2   => TKArr (subst t1 i u) (subst t2 i u)
  | TTAbs k t     => TTAbs k (subst t i (splice i 1 u))
  | TTApp t1 t2   => TTApp (subst t1 i u) (subst t2 i u)*)
  | ttrue         => ttrue
  | tfalse        => tfalse
  | tvar x        => tvar x
  | tapp t1 t2    => tapp (subst t1 i u) (subst t2 i u)
  | tabs t1       => tabs (subst t1 i u)
  | ttapp t1 t2   => ttapp (subst t1 i u) (subst t2 i u)
  | ttabs t1 t2   => ttabs t1(*?*) (subst t2 i (splice i 1 u))
end.

(* ---------- LR definitions for types : kinds  ---------- *)

(* kinds: * | K -> K *)

Inductive has_kind J : tm -> tm -> Type :=
| k_star:
    has_kind J TStar TBox
| k_bool:
    has_kind J TBool TStar
| k_var1: forall x T, (* is this needed? unclear ... *)
    indexr x J = Some (false,T) ->
    has_kind J (TVar x) TStar
| k_var: forall x K,
    indexr x J = Some (true,K) ->
    has_kind J (TVar x) K
| k_fun: forall T1 T2, (* (term -> term): type *)
    has_kind J T1 TStar ->
    has_kind J T2 TStar ->
    has_kind J (TFun T1 T2) TStar
| k_all: forall K1 T2, (* (type -> term): type *)
    has_kind ((true,K1)::J) T2 TStar ->
    has_kind J (TAll K1 T2) TStar
| k_pi1: forall T1 T2, (* (term -> term): type *)
    has_kind J T1 TStar ->
    has_kind ((false,T1)::J) T2 TStar ->
    has_kind J (TPi T1 T2) TStar
(* | k_pi2: forall T1 T2, (* (term -> type): type *)
    has_kind J T1 TStar ->
    has_kind (T1::J) T2 TBox ->
    has_kind J (TPi T1 T2) TBox *)
| k_karr: forall K1 K2, (* (type -> type): kind *)
    has_kind J K1 TBox ->
    has_kind J K2 TBox ->
    has_kind J (TFun K1 K2) TBox
| k_tabs: forall K1 T2 K2,
    has_kind ((true,K1)::J) T2 K2 ->
    has_kind J (ttabs K1 T2) (TFun K1 K2) (* (tabs K1 T2) (TPi K1 K2) *)
| k_tapp: forall TF TX K1 K2,
    has_kind J TF (TFun K1 K2) ->
    has_kind J TX K1 ->
    has_kind J (ttapp TF TX) K2
.

(* note: we can either include kn in the definition, or derive it later *)
Inductive eq_type : kenv -> tm -> tm -> Type :=
| q_refl: forall J T,
    eq_type J T T
| q_symm: forall J T1 T2,
    eq_type J T1 T2 ->
    eq_type J T2 T1
| q_trans: forall J T1 T2 T3,
    eq_type J T1 T2 ->
    eq_type J T2 T3 ->
    eq_type J T1 T3
(*| q_pi: forall J T1 T2 T1' T2',
    eq_type J T1 T1' ->
    eq_type J T2 T2' ->
    eq_type J (TPi T1 T2) (TPi T1' T2')*)
| q_fun: forall J T1 T2 T1' T2',
    eq_type J T1 T1' ->
    eq_type J T2 T2' ->
    eq_type J (TFun T1 T2) (TFun T1' T2')
| q_tall : forall J T2 T2' K1,
    eq_type ((true,K1)::J) T2 T2' ->
    eq_type J (TAll K1 T2) (TAll K1 T2')
| q_tabs: forall J T2 T2' K1,
    eq_type ((true,K1)::J) T2 T2' ->
    eq_type J (ttabs K1 T2) (ttabs K1 T2')
| q_tapp: forall J T1 T2 T1' T2',
    eq_type J T1 T1' ->
    eq_type J T2 T2' ->
    eq_type J (ttapp T1 T2) (ttapp T1' T2')
| q_beta: forall J T1 T2 K1,
    has_kind J T1 K1 ->
    eq_type J (ttapp (ttabs K1 T2) T1) (subst T2 (length J) T1)
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

(*| t_abs_pi: forall G J t T1 T2,
    has_type (T1::G) J t T2 ->
    has_kind J T1 TStar ->
    has_kind J T2 TStar ->
    has_type G J (tabs t) (TFun T1 T2)
| t_app: forall G J f t T1 T2,
    has_type G J f (TFun T1 T2) ->
    has_type G J t T1 ->
    has_type G J (tapp f t) T2*)

| t_tabs: forall G J t K1 T2,
    has_type (map (splice (length J) 1) G) ((true,K1)::J) t T2 ->
    has_kind ((true,K1)::J) T2 TStar ->
    has_type G J (ttabs K1 t) (TAll K1 T2)
| t_tapp: forall G J f K1 T1 T2,
    has_type G J f (TAll K1 T2) ->
    has_kind J T1 K1 ->
    has_type G J (ttapp f T1) (subst T2 (length J) T1)

| t_equiv: forall G J t T1 T2,
    has_type G J t T1 ->
    eq_type J T1 T2 ->
    has_kind J T2 TStar ->
    has_type G J t T2
.

#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.


(* Example 1: a function from TBool to Type *)

Example boolToTypeCoq: bool -> Type := fun (x: bool) => bool. (* could dispatch with if/else *)

(* Example 2: a function from TBool to (Example 1 applied to arg) *)

Example boolToTypeCoq2: forall x: bool, boolToTypeCoq x := fun x => x. 


(* Example 1: a function from TBool to Type *)

Example boolToType := tabs (*TBool*) TBool. 

Example typed1 : has_type [] [] boolToType (TFun TBool TStar).
Proof. Admitted.

Example typed2 : has_type [] [] (tapp boolToType ttrue) TStar. 
Proof. Admitted.

Example typed3 : has_type [] [] ttrue (tapp boolToType ttrue).
Proof. Admitted.


(* Example 2: a function from TBool to (Example 1 applied to arg) *)

(* TODO *)



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

Lemma splice_acc: forall e1 a b c,
  splice a c (splice a b e1) =
  splice a (c+b) e1.
Proof.
  induction e1; intros; simpl; try reflexivity.
  - bdestruct (i <? a); simpl; [bdestruct (i <? a); [auto | lia] | bdestruct (i+b <? a); [lia | f_equal; lia]].
  - rewrite IHe1_1, IHe1_2. auto.
  - rewrite IHe1_2. eauto. 
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

Definition vt_fun (T1: tpe) (T2: tpe): tpe :=
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

Fixpoint val_sort1 (K: bool * tm) : Type :=
  match K with
  | (false, T) => tpe
  | (true, K) => val_sort K
  end.


Definition env_kv J :=
  forall x K, indexr x J = Some K -> val_sort1 K. 

Lemma envkv_nil:
  env_kv nil.
Proof.
  intros ???. inversion H.
Defined.

Lemma envkv_cons: forall J K,
    val_sort1 K ->
    env_kv J ->
    env_kv (K::J).
Proof.
  intros. intros ???.
  destruct (Nat.eq_dec x (length J)). subst.
  rewrite indexr_head in H. inversion H. subst. eauto.
  rewrite indexr_skip in H. eapply X0. eauto. eauto.
Defined.


Require Import Coq.Arith.Compare_dec.

Lemma indexr_hit: forall {T} J' J (K:T) ,
    indexr (length J) (J' ++ K :: J) = Some K.
Proof.
  intros. rewrite indexr_skips. rewrite indexr_head. eauto. simpl. eauto.
Qed.

Lemma envkv_weaken: forall J' J K,
    val_sort1 K ->
    env_kv (J'++J) ->
    env_kv (J'++K::J).
Proof.
  intros. intros ???.
  destruct (Nat.eq_dec x (length J)). subst.
  rewrite indexr_hit in H. inversion H. subst. eauto.
  rewrite indexr_splice2 in H; eauto.
Defined.


Fixpoint val_type {J T K} (h : has_kind J T K) (W : env_kv J) {struct h}: val_sort K :=
  match h, T, K return val_sort K with
  | k_star _, _, _ =>
      tt
  | k_bool _, _, _ =>
      vt_bool
  | k_var1 _ x K IX, _, _ =>
      W x _ IX
  | k_var _ x K IX, _, _ =>
      W x (true,K) IX
  | k_fun _ T1 T2 h1 h2, _, _ =>
      vt_fun (val_type h1 W) (val_type h2 W)
  | k_pi1 _ T1 T2 h1 h2, _, _ => (* ?? *)
      vt_pi (val_type h1 W) (fun vx => val_type h2 (envkv_cons _ _ ((fun x => x = vx):val_sort1 (false,T1)) W))
  | k_all _ K1 T2 h, _, _ =>
      vt_all (val_sort K1) (fun VT1 => val_type h (envkv_cons _ _ (VT1:val_sort1 (true,K1)) W))
  | k_karr _ _ _ K1 K2, _, _ =>
      tt
  | k_tabs _ K1 T2 K2 h, _, _ =>
      (fun VT1 => val_type h (envkv_cons _ _ (VT1: val_sort1 (true,K1)) W))
  | k_tapp _ TF TX K1 K2 hf hx, _, _ =>
      val_type hf W (val_type hx W)
  end.



Definition exp_type H J (h2: env_kv J) t T :=
  exists v (h1: has_kind J T TStar),
    tevaln H t v /\
    val_type h1 h2 v.

Definition env_type (H: venv) (G: tenv) (J: kenv) (h2: env_kv J):=
  length H = length G /\
  forall x T,
    indexr x G = Some T ->
    exists v (h1: has_kind J T TStar),
      indexr x H = Some v /\
      val_type h1 h2 v.

Definition sem_type G J t T :=
  forall H (h2: env_kv J),
    env_type H G J h2 ->
    exp_type H J h2 t T.


(* ---------- LR helper lemmas  ---------- *)

Require Import Coq.Program.Equality.

(* uniqueness *)

Lemma hk_unique': forall GV T K1
  (a: has_kind GV T K1) K2
  (b: has_kind GV T K2), K1 = K2.
Proof.
  intros GV T K1 a.
  induction a; intros K2' b; inversion b; subst; intros.
  - eauto.
  - eauto.
  - congruence.
  - congruence.
  - congruence.
  - congruence. 
  - eauto.
  - eauto.
  - eauto.
  - eauto. 
  - specialize (IHa1 _ H1).
    subst. eauto.
  - eauto.
  - specialize (IHa _ H2).
    subst. eauto.
  - specialize (IHa2 _ H3).    
    subst.
    specialize (IHa1 _ H1).
    congruence.
Qed.


Lemma hk_unique: forall GV T K
  (a b: has_kind GV T K), a = b.
Proof.
  intros GV T K a.
  induction a; intros b; dependent destruction b.
  - eauto.
  - eauto.
  - assert (T = T0). congruence. subst. 
    eapply f_equal. eapply proof_irrelevance.
  - assert (true = false). congruence. inversion H.
  - assert (true = false). congruence. inversion H. 
  - eapply f_equal. eapply proof_irrelevance.
  - specialize (IHa1 b1).
    specialize (IHa2 b2).
    subst. eauto.
  - specialize (IHa b).
    subst. eauto.
  - specialize (IHa1 b1).
    specialize (IHa2 b2).
    subst. eauto. 
  - specialize (IHa1 b1).
    specialize (IHa2 b2).
    subst. eauto. 
  - specialize (IHa b).
    subst. eauto.
  - specialize (hk_unique' _ _ _ a2 _ b2). intros. subst.
    specialize (IHa2 b2). subst.
    specialize (IHa1 b1). subst.
    eauto.
Qed.


(* weakening *)

Lemma SHOTGUN: False. Admitted. 

Fixpoint haskind_weaken1 T: forall J' J K K1,
    has_kind (J' ++ J) T K ->
    has_kind (J' ++ K1 :: J) (splice (length J) 1 T) K.
Proof.
  destruct T; intros; simpl in *.
  - (* TStar *) inversion H; subst. eapply k_star.
  - (* TBox *) inversion H.
  - (* TBool *) inversion H; subst. eapply k_bool.
  - (* TVar *) inversion H; subst.
    + eapply k_var1. replace (i+1) with (1+i). 2: lia.
      erewrite indexr_splice1. eauto.
    + eapply k_var. replace (i+1) with (1+i). 2: lia.
      erewrite indexr_splice1. eauto.
  - (* TFun *) inversion H; subst. eapply k_fun. eauto. eauto.
    (* TKArr *) eapply k_karr. eauto. eauto. 
  - (* TAll *) inversion H; subst. eapply k_all. eauto. 
    eapply haskind_weaken1 with (J':=(true,T1)::J'). eauto.
  - (* TPi *) inversion H; subst. eapply k_pi1. 
    exfalso. eapply SHOTGUN. (* eapply haskind_weaken1 with (J':=K1::J'). eauto. *)
    eapply haskind_weaken1 with (J':=(false,T1)::J'). eauto.
  - (* TTAbs *) inversion H; subst. 
  - (* TTApp *) inversion H; subst. 
  - inversion H.
  - inversion H.
  - inversion H.
  - (* TTApp *) inversion H; subst. eapply k_tapp. eauto. eauto.
  - (* TTAbs *) inversion H; subst. eapply k_tabs. eapply haskind_weaken1 with (J':=(true,T1)::J'). eauto.
Defined. (* Admitted! *)


Lemma haskind_extend: forall T J K K1,
    has_kind J T K ->
    has_kind (K1 :: J) (splice (length J) 1 T) K.
Proof.
  intros. eapply haskind_weaken1 with (J':=[]). eauto.
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

Lemma aux0: forall i i' J K
  (eq: i = i')
  (h2: forall i K, indexr i (J) = Some (K) -> val_sort1 K)
  (h2A: indexr i (J) = Some (K) -> val_sort1 K)
  (h2B: indexr i' (J) = Some (K) -> val_sort1 K)
  (eq2A: h2A = h2 i K)
  (eq2B: h2B = h2 i' K)
  eA eB,
    h2A eA = h2B eB.
Proof.
  intros. subst i'. subst.
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
      (fun o : option (bool*tm) => o = Some K1) e (Some K1) e).
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
    remember (indexr_hit J' J (K1)). replace IX with e. 2: eapply proof_irrelevance.
    cbn.
    remember (eq_ind (indexr (length J) (J' ++ (K1) :: J))
      (fun o : option (bool*tm) => o = Some (K1)) e (Some (K1)) e).
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
    remember (indexr_splice2 J' J i (K1) n) as IS.
    assert ((if i <? length J then i else i - 1) = i) as RW. bdestruct (i <? length J); lia.
    eapply aux0. eauto. eauto. eauto.

  - unfold envkv_weaken.
    remember (Nat.eq_dec (i+1) (length J)). destruct s. lia.
    remember (h2 i K) as h2A.
    remember (h2 (if i + 1 <? length J then i + 1 else i + 1 - 1) K) as h2B.
    unfold eq_ind.
    remember (indexr_splice2 J' J (i + 1) (K1) n) as IS.
    assert ((if i+1 <? length J then i+1 else i+1-1) = i) as RW. bdestruct (i+1 <? length J); lia.
    eapply aux0. eauto. eauto. eauto.
Qed.

Lemma aux2: forall J' J K1 k vk h2 VT1,
    (envkv_cons (J' ++ (K1) :: J) k VT1 (envkv_weaken J' J K1 vk h2)) =
      (envkv_weaken ((k) :: J') J K1 vk (envkv_cons (J' ++ J) k VT1 h2)).
Proof.
  intros.
  eapply functional_extensionality_dep. intros i.
  eapply functional_extensionality_dep. intros K.
  eapply functional_extensionality_dep. intros IX.
  assert (indexr i ((k) :: J' ++ (K1) :: J) = Some (K)) as IX'. eapply IX.
  bdestruct (i =? length J).
  - remember (envkv_weaken J' J K1 vk h2).
    remember (envkv_cons (J' ++ J) k VT1 h2).
    assert (K = K1). subst i. replace ((k) :: J' ++ (K1) :: J) with (((k) :: J') ++ (K1) :: J) in IX'.
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
    bdestruct (i =? length (J'++(K1)::J)).
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
      replace ((((k) :: J') ++ J)) with ((k)::J'++J). rewrite indexr_head in *. eauto. eauto.
      eapply indexr_var_some' in IX'. rewrite indexr_skips'.
      replace ((k) :: J' ++ (K1) :: J) with (((k)::J') ++ ((K1)::J)) in IX.
      rewrite indexr_skips' in IX. replace (i - length ((K1)::J)) with (i-1-length J) in IX. eauto.
      simpl. lia. simpl. lia. eauto. eauto.
      rewrite indexr_skip in IX'. eauto. eauto.
      rewrite indexr_skip in IX'. rewrite indexr_skips' in IX'. rewrite indexr_skips'.
      replace (i - length ((K1)::J)) with (i-1-length J) in IX'. eauto.
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
  assert ((if i =? length J then Some (K1) else indexr i J) = Some (K)). eapply IX.
  bdestruct (i =? length J).
  - inversion H. subst.
    rewrite envkv_cons_head, envkv_weaken_hit. eauto.
  - eapply indexr_var_some' in H as LT.
    erewrite envkv_cons_skip, envkv_weaken_lt; eauto.
    Unshelve. simpl. eauto.
Qed.

Lemma valt_weaken: forall T J' J K1 K vk (h1: has_kind (J'++J) T K) h2,
    val_type h1 h2 =
    val_type (haskind_weaken1 T J' J K (K1) h1)
    (envkv_weaken J' J K1 vk h2).
Proof.
  intros T. induction T; intros; simpl in *.
  - (* TStar *)
    dependent destruction h1.
    simpl. eauto.
  - (* TBox *)
    inversion h1.
  - (* TBool *)
    dependent destruction h1.
    simpl. split; eauto.
  - (* TVar *)
    dependent destruction h1.
    + remember (k_var1 (J'++J) i T e) as hx1.
    remember ((haskind_weaken1 (TVar i) J' J _ K1 hx1)) as hx1'.
    remember ((envkv_weaken J' J K1 vk h2)) as h2'.
    dependent destruction hx1; inversion Heqhx1. rewrite Heqhx1 in *. subst T0. 
    dependent destruction hx1'; inversion Heqhx1'.
    simpl.
    subst h2'. erewrite aux1. eauto. 
    + remember (k_var (J'++J) i K e) as hx1.
    remember ((haskind_weaken1 (TVar i) J' J K K1 hx1)) as hx1'.
    remember ((envkv_weaken J' J K1 vk h2)) as h2'.
    dependent destruction hx1; inversion Heqhx1. rewrite Heqhx1 in *.
    dependent destruction hx1'; inversion Heqhx1'.
    simpl.
    subst h2'. erewrite aux1. eauto.
  - (* TFun *)
    dependent destruction h1.
    + simpl in *.
    assert (val_type h1_1 h2 = val_type (haskind_weaken1 T1 J' J TStar (K1) h1_1) (envkv_weaken J' J K1 vk h2)). eapply IHT1.
    assert (val_type h1_2 h2 = val_type (haskind_weaken1 T2 J' J TStar (K1) h1_2) (envkv_weaken J' J K1 vk h2)). eapply IHT2.
    rewrite H, H0. eauto.
    + (* TKArr *)
    simpl. eauto.
  - (* TAll *)
    dependent destruction h1. simpl.
    assert (forall (VT1: val_sort (T1)), val_type h1 (envkv_cons (J'++J) (true,T1) VT1 h2) =
                          val_type (haskind_weaken1 T2 ((true,T1)::J') J TStar (K1) h1) (envkv_weaken ((true,T1)::J') J K1 vk (envkv_cons (J'++J) (true,T1) VT1 h2))). {
    intros.
    specialize IHT2 with (J':=(true,T1)::J') (J:=J) (vk:=vk) (h1:=h1) (h2:=(envkv_cons (J'++J) (true,T1) VT1 h2)).
    eapply IHT2. }
    eapply functional_extensionality in H.
    rewrite H.
    assert (forall (VT1: val_sort T1),
     val_type (haskind_weaken1 T2 ((true,T1) :: J') J TStar (K1) h1) (envkv_weaken ((true,T1) :: J') J K1 vk (envkv_cons (J' ++ J) (true,T1) VT1 h2)) = val_type (haskind_weaken1 T2 ((true,T1) :: J') J TStar (K1) h1) (envkv_cons (J' ++ (K1) :: J) (true,T1) VT1 (envkv_weaken J' J K1 vk h2))).
    intros. rewrite aux2. eauto.
    eapply functional_extensionality in H0.
    rewrite H0. eauto.
  - (* TPi *)
    dependent destruction h1. simpl.
    exfalso. eapply SHOTGUN. 
  - inversion h1. (* TKArr *)
  - inversion h1. (* TTAbs *)
  - inversion h1. (* TTApp *)
  - inversion h1.
  - inversion h1. 
  - (* TTApp *)
    dependent destruction h1. simpl.
    specialize (IHT1) with (h1:=h1_1) (h2:=h2).
    erewrite IHT1.
    specialize (IHT2) with (h1:=h1_2) (h2:=h2).
    erewrite IHT2.
    eauto.
  - (* TTAbs *)
    dependent destruction h1.
    remember (k_tabs (J' ++ J) T1 T2 K2 h1) as h1'.
    dependent destruction h1'.
    replace h1 with h1' in * by (eapply hk_unique).
    simpl in *. eapply functional_extensionality.
    intros.
    specialize IHT2 with (J':=(true,T1)::J') (h1:=h1') (h2:=(envkv_cons (J' ++ J) (true,T1) x h2)) (vk:=vk).
    rewrite aux2. eapply IHT2. 
Qed.


Lemma valt_extend: forall T J K1 vk (h1: has_kind J T TStar) h2 v2,
    val_type h1 h2 v2 <->
    val_type (haskind_extend T J TStar (K1) h1)
    (envkv_cons J K1 vk h2) v2.
Proof.
  intros.
  specialize valt_weaken with (J':=[]). simpl. intros. unfold haskind_extend.
  replace (envkv_cons J K1 vk h2) with (envkv_weaken [] J K1 vk h2).
  erewrite H. 2: eapply envkv_weaken_eq_extend. split; eauto.
Qed.

Lemma valt_extend': forall T J K1 K vk (h1: has_kind J T K) h2,
    val_type h1 h2 =
    val_type (haskind_extend T J K (K1) h1)
    (envkv_cons J K1 vk h2).
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


Lemma xxx3: forall (J' J: kenv) K1 K2 i,
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


Fixpoint hask_subst T2: forall J' J T1 K1 K2 b,
    has_kind (J' ++ (b,K1) :: J) T2 K2 ->
    has_kind J T1 K1 ->
    has_kind (J'++J) (subst T2 (length J) (splice (length J) (length J') T1)) K2.
Proof.
  destruct T2; intros; simpl in *.
  - (* TStar *) inversion H; subst. eapply k_star.
  - (* TBox *) inversion H.
  - (* TBool *) inversion H; subst. eapply k_bool.
  - (* TVar *)
    inversion H; subst.
    + exfalso. eapply SHOTGUN. (* XXX admit! *)
    + destruct (Nat.eq_dec i (length J)) as [Heq | Hneq].
      * eapply haskind_extend_mult. eapply xxx4. eauto.
        eapply xxx3 in H2; eauto. congruence. 
      * eapply k_var.
        rewrite indexr_splice2 in H2. eapply H2. eauto.
  - (* TFun *) inversion H; subst.
    + eapply k_fun. eauto. eauto.
    + (* TKArr *) eapply k_karr. eauto. eauto. 
  - (* TAll *) inversion H; subst. eapply k_all. rewrite splice_acc.
    eapply hask_subst with (J':=(true,T2_1)::J'). eauto. eauto.
  - (* TPi *)
    inversion H; subst. eapply k_pi1.
    exfalso. eapply SHOTGUN. 
    rewrite splice_acc. eapply hask_subst with (J':=(false,T2_1)::J'). eauto. eauto.
  - (* TKArr *) inversion H; subst. (* eapply k_karr. eauto. eauto. *)
  - (* TTAbs *) inversion H; subst. (*eapply k_tabs. rewrite splice_acc.
    eapply hask_subst with (J':=T2_1::J'). eauto. eauto.*)
  - inversion H. 
  - inversion H. 
  - inversion H. 
  - (* TTApp *) inversion H; subst. eapply k_tapp. eauto. eauto.
  - (* TTAbs *) inversion H; subst. eapply k_tabs. rewrite splice_acc.
    eapply hask_subst with (J':=(true,T2_1)::J'). eauto. eauto.
Defined.

Lemma hask_subst1: forall J T2 T1 K1 b,
    has_kind ((b,K1) :: J) T2 TStar ->
    has_kind J T1 K1 ->
    has_kind J (subst T2 (length J) T1) TStar.
Proof.
  intros. eapply hask_subst with (J':=[]) in H0.
  simpl in H0. rewrite splice_zero in H0. eauto.
  simpl. eauto.
Defined.

Lemma hask_subst1': forall J T2 T1 K1 K b,
    has_kind ((b,K1) :: J) T2 K ->
    has_kind J T1 K1 ->
    has_kind J (subst T2 (length J) T1) K.
Proof.
  intros. eapply hask_subst with (J':=[]) (T2:=T2) (K2:=K) (b:=b) in H0; auto.
  simpl in H0. rewrite splice_zero in H0; auto.
Defined.


Lemma aux1b'': forall J' J K1 K T1K WFJ i e0 e1,
    i <> length J ->
    (envkv_weaken J' J K1 T1K WFJ) i K e0 = WFJ (if i <? length J then i else i - 1) K e1.
Proof.
  intros.
  bdestruct (i <? length J).
  erewrite envkv_weaken_lt. eauto. eauto.
  erewrite envkv_weaken_ge. eauto. lia. lia.
Qed.

Lemma valt_subst: forall T2 J' J K1 K2 T1K WFJ T1 (h1f : has_kind (J'++(true,K1) :: J) T2 K2) HK1,
    T1K = val_type (haskind_extend_mult J' T1 J K1 HK1) WFJ ->
    val_type h1f (envkv_weaken J' J (true,K1) T1K WFJ) =
    val_type (hask_subst T2 J' J T1 K1 K2 true h1f HK1) WFJ.
Proof.
  intros T2. induction T2; intros; simpl in *.
  - (* TStar *) dependent destruction h1f. simpl. eauto.
  - (* TBox *) inversion h1f.
  - (* TBool *) dependent destruction h1f. simpl. eauto.
  - (* TVar *)
    dependent destruction h1f. admit. (* var1 *)
    remember (k_var (J' ++ (true,K1) :: J) i K e) as hx1.
    remember (hask_subst (TVar i) J' J T1 K1 K true hx1 HK1) as hx1'.
    remember (envkv_weaken J' J (true,K1) T1K WFJ) as h2'.
    dependent destruction hx1. inversion Heqhx1. simpl.

    simpl in *. remember (Nat.eq_dec i (length J)).
    destruct s.
    + subst i.
      simpl in *.
      assert (HK1EQ': (true,K1) = (true,K)). eapply xxx3; eauto.
      assert (HK1EQ: K1 = K). congruence. 
      subst K1.
      (* Goal: val_type hx1 h2' = val_type hx1' WFJ
         where hx1 is (k_var ... e0), h2' = envkv_weaken ...,
         and hx1' = hask_subst (TVar (length J)) ... *)
      subst h2'.
      simpl. rewrite envkv_weaken_hit.
      subst T1K.
      (* Goal: val_type (haskind_extend_mult ...) WFJ = val_type hx1' WFJ *)
      f_equal. eapply hk_unique.

    + dependent destruction hx1'. inversion Heqhx1'.
      simpl. subst h2'. erewrite aux1b''. eauto. eauto. 

  - (*TFun*) dependent destruction h1f; simpl.
    + assert (H21: val_type h1f1 (envkv_weaken J' J (true,K1) T1K WFJ) = val_type (hask_subst T2_1 J' J T1 (K1) TStar true h1f1 HK1) WFJ). apply IHT2_1. auto. rewrite H21.
    assert (H22: val_type h1f2 (envkv_weaken J' J (true,K1) T1K WFJ) = val_type (hask_subst T2_2 J' J T1 K1 TStar true h1f2 HK1) WFJ). apply IHT2_2. auto. rewrite H22. auto.
    + (*TKArr*) eauto. 
  - (*TAll*) dependent destruction h1f. simpl.
    assert (HVT: forall VT1, val_type (haskind_extend_mult ((true,T2_1) :: J') T1 J (K1) HK1) (envkv_cons (J' ++ J) (true,T2_1) VT1 WFJ) = val_type (haskind_extend_mult J' T1 J (K1) HK1) WFJ). { intros.
      simpl. elim_eq_rect. simpl. elim_eq_rect. simpl.
      rewrite <- valt_extend'. reflexivity.
    }
    assert (HV: forall (VT1: val_sort T2_1), val_type h1f (envkv_cons (J' ++ (true,K1) :: J) (true,T2_1) VT1 (envkv_weaken J' J (true,K1) T1K WFJ)) =
      val_type (eq_rec_r (fun t : tm => has_kind ((true,T2_1) :: J' ++ J) (subst T2_2 (length J) t) TStar) (hask_subst T2_2 ((true,T2_1) :: J') J T1 K1 TStar true h1f HK1) (splice_acc T1 (length J) (length J') 1))
      (envkv_cons (J' ++ J) (true,T2_1) VT1 WFJ)). { intros.
      rewrite splice_acc. rewrite aux2.
      specialize (IHT2_2 ((true,T2_1) :: J') J K1 TStar T1K (envkv_cons (J' ++ J) (true,T2_1) VT1 WFJ) T1 h1f HK1).
      specialize (HVT VT1). rewrite <- HVT in H.
      specialize (IHT2_2 H). auto.
    }
    eapply functional_extensionality in HV. rewrite HV. auto.
  - (* TPi *)
    inversion h1f. admit. 
  - inversion h1f. (*TKArr*) 
  - inversion h1f.
  - inversion h1f.
  - inversion h1f.
  - inversion h1f.
  - (*TTApp*) dependent destruction h1f. simpl.
    specialize (IHT2_2) with (h1f := h1f2). specialize (IHT2_2 T1K WFJ T1 HK1 H). rewrite IHT2_2.
    remember ((val_type (hask_subst T2_2 J' J T1 K1 K0 true h1f2 HK1) WFJ)) as VT2.
    specialize (IHT2_1) with (h1f := h1f1). specialize (IHT2_1 T1K WFJ T1 HK1 H). rewrite IHT2_1. auto.
  - (*TTAbs*) dependent destruction h1f. remember (k_tabs (J' ++ (true,K1) :: J) T2_1 T2_2 K2 h1f) as h1f'.
    dependent destruction h1f'.
    replace h1f with h1f' in * by (eapply hk_unique).
    simpl. rewrite splice_acc.
    apply functional_extensionality. intro vk.
    rewrite aux2.
    assert (HT1K: val_type (haskind_extend_mult ((true,T2_1) :: J') T1 J K1 HK1) (envkv_cons (J' ++ J) (true,T2_1) vk WFJ) = val_type (haskind_extend_mult J' T1 J K1 HK1) WFJ). { intros.
      simpl. elim_eq_rect. simpl. elim_eq_rect. simpl.
      rewrite <- valt_extend'. reflexivity.
    } rewrite <- HT1K in H.
    specialize (IHT2_2 ((true,T2_1) :: J')) with (h1f := h1f') (WFJ := (envkv_cons (J' ++ J) (true,T2_1) vk WFJ)) (T1K := T1K). specialize (IHT2_2 T1 HK1 H).
    replace (val_type h1f' (envkv_weaken ((true,T2_1) :: J') J (true,K1) T1K (envkv_cons (J' ++ J) (true,T2_1) vk WFJ))) with (val_type (hask_subst T2_2 ((true,T2_1) :: J') J T1 K1 K2 true h1f' HK1) (envkv_cons (J' ++ J) (true,T2_1) vk WFJ)). (*using IHT2_2*)
    auto.
Admitted.


Lemma valt_subst1: forall T2 J K1 T1K WFJ T1 (h1f : has_kind ((true,K1) :: J) T2 TStar) HK1 vy,
  T1K = val_type HK1 WFJ ->
  val_type h1f (envkv_cons J (true,K1) T1K WFJ) vy =
  val_type (hask_subst1 J T2 T1 K1 true h1f HK1) WFJ vy.
Proof.
  intros.
  specialize valt_subst with (J':=[]). simpl. intros. unfold hask_subst1.
  unfold eq_rect. remember (splice_zero T1 (length J)).
  clear Heqe.
  dependent destruction e.
  replace (envkv_cons J (true,K1) T1K WFJ) with (envkv_weaken [] J (true,K1) T1K WFJ).
  erewrite H0 with (T1:=T1) (HK1:=HK1). eauto. 2: eapply envkv_weaken_eq_extend.
  unfold eq_rec_r, eq_rec, eq_rect.
  remember (eq_sym (splice_zero T1 (length J))). clear Heqe. dependent destruction e.
  eauto.
Qed.

Lemma valt_subst1': forall T2 J K K1 T1K WFJ T1 (h1f : has_kind ((true,K1) :: J) T2 K) HK1 ,
  T1K = val_type HK1 WFJ ->
  val_type h1f (envkv_cons J (true,K1) T1K WFJ) =
  val_type (hask_subst1' J T2 T1 K1 K true h1f HK1) WFJ .
Proof.
  intros.
  specialize valt_subst with (J':=[]). simpl. intros. unfold hask_subst1'.
  unfold eq_rect. remember (splice_zero T1 (length J)).
  clear Heqe.
  dependent destruction e.
  replace (envkv_cons J (true,K1) T1K WFJ) with (envkv_weaken [] J (true,K1) T1K WFJ).
  erewrite H0 with (T1:=T1) (HK1:=HK1). eauto. 2: eapply envkv_weaken_eq_extend.
  unfold eq_rec_r, eq_rec, eq_rect.
  remember (eq_sym (splice_zero T1 (length J))). clear Heqe. dependent destruction e.
  eauto.
Qed.



(* ---------- env extension lemmas  ---------- *)

Lemma envt_empty: forall W,
    env_type [] [] [] W.
Proof.
  intros. split. eauto. intros. inversion H.
Qed.

Lemma envt_extend: forall E G J h2 v1 T1 (h1: has_kind J T1 TStar),
    env_type E G J h2 ->
    val_type h1 h2 v1 ->
    env_type (v1::E) (T1::G) J h2.
Proof.
  intros.
  remember H as WFE. clear HeqWFE.
  destruct H as (?&?). split. simpl. eauto.
  intros x T IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX. subst T1.
    exists v1. rewrite <- H. rewrite indexr_head. eauto.
  - rewrite indexr_skip in IX; eauto.
    eapply WFE in IX as IX. destruct IX as (v2 & ? & ?).
    exists v2. rewrite indexr_skip; eauto. lia.
Qed.

Lemma envt_extendk: forall E G J h2 K1 (vk: val_sort1 K1),
    env_type E G J h2 ->
    env_type E (map (splice (length J) 1) G) ((K1)::J) (envkv_cons J K1 vk h2).
Proof.
  intros.
  remember H as WFE. clear HeqWFE.
  destruct H as (?&?). split.
  rewrite map_length. eauto.
  intros x T IX.
  eapply indexr_map' in IX. destruct IX as (T' & IX & ?).
  eapply WFE in IX as IX. destruct IX as (v2 & ? & ? & ?).
  exists v2. subst T.
  exists (haskind_extend _ _ _ _ x0).
  split. eauto.
  edestruct valt_extend. eauto.
Qed.


(* ---------- equivalence ---------- *)

Lemma has_kind_subst_inverse : forall T2 J J' T1 K1 K2,
    has_kind (J'++J) (subst T2 (length J) (splice (length J) (length J') T1)) K2 ->
    has_kind J T1 K1 ->
    has_kind (J' ++ (true,K1) :: J) T2 K2.
Proof.
  induction T2; intros; simpl in H.
  - dependent destruction H. constructor.
  - inversion H.
  - dependent destruction H. constructor.
  - destruct (Nat.eq_dec i (length J)); subst.
      eapply k_var. rewrite indexr_skips; auto. rewrite indexr_head.
      apply (haskind_extend_mult J') in H0. specialize (hk_unique' _ _ _ H0 _ H); intros. congruence.
      dependent destruction H.
      bdestruct (i <? (length J)). eapply k_var1.
      rewrite indexr_skips; auto. rewrite indexr_skips in e; auto. rewrite indexr_skip; auto. eauto. simpl; lia.
      eapply k_var1. replace i with (S (i - 1)). rewrite <- indexr_insert_ge. eauto. lia. lia.

      bdestruct (i <? (length J)). eapply k_var.
      rewrite indexr_skips; auto. rewrite indexr_skips in e; auto. rewrite indexr_skip; auto. eauto. simpl; lia.
      eapply k_var. replace i with (S (i - 1)). rewrite <- indexr_insert_ge. eauto. lia. lia.
      
  - dependent destruction H.
    + constructor; auto. eapply IHT2_1; eauto. eapply IHT2_2; eauto.
    + constructor. eapply IHT2_1; eauto. eapply IHT2_2; eauto.
  - dependent destruction H. constructor; auto. specialize (IHT2_2 J ((true,T2_1) :: J') T1 K1 TStar). apply IHT2_2; auto. simpl. rewrite splice_acc in H. auto.
  - admit. 
  - inversion H.
  - inversion H. 
  - inversion H. 
  - inversion H. 
  - inversion H. 
  - dependent destruction H. apply k_tapp with (K1 := K0). eapply IHT2_1; eauto. eapply IHT2_2; eauto.
  - dependent destruction H. constructor; auto. specialize (IHT2_2 J ((true,T2_1) :: J') T1 K1 K2). apply IHT2_2; auto. simpl. rewrite splice_acc in H. auto.
Admitted.

Lemma has_kind_subst1_inverse : forall J T1 T2 K1 K,
    has_kind J T1 K1 ->
    has_kind J (subst T2 (length J ) T1) K ->
    has_kind ((true,K1) :: J) T2 K.
Proof.
  intros. specialize (has_kind_subst_inverse T2 J [] T1 K1 K). simpl. rewrite splice_zero. auto.
Qed.

Lemma eq_type_preserve_kind : forall J T1 T2 K (heq: eq_type J T1 T2),
  (has_kind J T1 K -> has_kind J T2 K) * (has_kind J T2 K -> has_kind J T1 K).
Proof.
  intros. generalize dependent K. induction heq; auto; intros.
  - specialize (IHheq K); destruct IHheq. split; auto.
  - specialize (IHheq1 K); destruct IHheq1. specialize (IHheq2 K); destruct IHheq2. split; auto.
  - specialize (IHheq1 K); destruct IHheq1. specialize (IHheq2 K); destruct IHheq2. split; intros.
    dependent destruction H. constructor; auto. constructor; auto.
    dependent destruction H. constructor; auto. constructor; auto.
  - specialize (IHheq K); destruct IHheq. split; intros.
    dependent destruction H. constructor; auto.
    dependent destruction H. constructor; auto.
  - split; intros.
    dependent destruction H. constructor. specialize (IHheq K2); destruct IHheq. auto.
    dependent destruction H. constructor. specialize (IHheq K2); destruct IHheq. auto.
  - split; intros; dependent destruction H.
    apply k_tapp with (K1 := K1). specialize (IHheq1 (TFun K1 K2)); destruct IHheq1. auto. specialize (IHheq2 K1); destruct IHheq2; auto.
    apply k_tapp with (K1 := K1). specialize (IHheq1 (TFun K1 K2)); destruct IHheq1. auto. specialize (IHheq2 K1); destruct IHheq2; auto.
  - split; intros.
    dependent destruction H. dependent destruction H. eapply hask_subst1' with (K1 := K0); eauto.
    eapply (k_tapp) with (K1:=K1); auto. constructor.
    eapply has_kind_subst1_inverse; eauto.
Qed.

Lemma eq_type_preserve_kind' : forall {J T1 T2 K},
  eq_type J T1 T2 ->
  has_kind J T1 K -> has_kind J T2 K.
Proof.
  intros. specialize (eq_type_preserve_kind _ _ _ K H). intros. destruct H1; auto.
Qed.


(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_true: forall G J,
    sem_type G J ttrue TBool.
Proof.
  intros.
  intros E WFJ WFE.
  exists (vbool true).
  exists (k_bool J).
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
  exists (k_bool J).
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
  eapply WFE in H as IX. destruct IX as (v & h1 & IX & VX).
  exists v.
  eexists h1.
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
  exists (k_fun _ _ _ W1 W2).
  split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros vx VX.
    edestruct HY as (vy & ? & ? & ?). eapply envt_extend; eauto.
    specialize (hk_unique _ _ _ W2 x). intros. subst.
    exists vy. split. eauto. eauto.
Qed.

Lemma sem_app: forall G J f t T1 T2,
    sem_type G J f (TFun T1 T2) ->
    sem_type G J t T1 ->
    sem_type G J (tapp f t) T2.
Proof.
  intros ? ? ? ? ? ? HF HX. intros H WFJ WFE.
  destruct (HF H WFJ WFE) as (vf & h1f & STF & VF).
  destruct (HX H WFJ WFE) as (vx & h1x & STX & VX).
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

Lemma sem_tabs: forall G J t K1 T2,
    sem_type (map (splice (length J) 1) G) ((true,K1)::J) t T2 ->
    has_kind ((true,K1)::J) T2 TStar ->
    sem_type G J (ttabs K1 t) (TAll K1 T2).
Proof.
  intros ? ? ? ? ? HY W2. intros E WFJ WFE.
  eexists _.
  eexists (k_all _ _ _ W2).
  split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros VK1.
    edestruct HY as (vy & ? & ? & ?). eapply envt_extendk; eauto.
    specialize (hk_unique _ _ _ W2 x). intros. subst.
    exists vy. split. eauto. eauto.
Qed.


Lemma sem_tapp: forall G J t K1 T1 T2,
    sem_type G J t (TAll K1 T2) ->
    has_kind J T1 K1 ->
    sem_type G J (ttapp t T1) (subst T2 (length J) T1).
Proof.
  intros ? ? ? ? ? ? HF HX. intros E WFJ WFE.
  destruct (HF E WFJ WFE) as (vf & h1f & STF & VF).
  dependent destruction h1f.
  destruct vf; simpl in VF; intuition.
  remember (val_type HX WFJ) as T1K.
  edestruct (VF T1K) as (vy & STY & VY).
  exists vy.
  exists (hask_subst1 _ _ _ _ _ h1f HX).
  split.
  - destruct STF as (n1 & STF).
    destruct STY as (n2 & STY).
    exists (1+n1+n2). intros. destruct n. lia. simpl. rewrite STF, STY. 2,3: lia. eauto.
  - erewrite <-valt_subst1. eauto. eauto.
Qed.


(* ---------- LR fundamental property of equiv ---------- *)

Lemma val_type_irrel : forall J T K (WFJ: env_kv J) (h1 h2: has_kind J T K),
  val_type h1 WFJ = val_type h2 WFJ.
Proof.
  intros. specialize (hk_unique J T K h1 h2); intros; subst; auto.
Qed.

Lemma val_type_equiv : forall J T1 T2 K (h1: has_kind J T1 K) (h2: has_kind J T2 K) (WFJ : env_kv J),
  eq_type J T1 T2 ->
  val_type h1 WFJ = val_type h2 WFJ.
Proof.
  intros. generalize dependent K. induction H; intros.
  - apply val_type_irrel; auto.
  - specialize (IHeq_type WFJ _ h2 h1). destruct IHeq_type. split; auto.
  - specialize (eq_type_preserve_kind' H h1). intros. specialize (IHeq_type2 WFJ K H1 h2). specialize (IHeq_type1 WFJ K h1 H1). rewrite IHeq_type1. auto.
  - dependent destruction h1; dependent destruction h2; simpl. 2: eauto. f_equal.
    eapply IHeq_type1.
    eapply functional_extensionality. intros ?. erewrite IHeq_type2. eauto. 
  - dependent destruction h1. dependent destruction h2. simpl. f_equal.
    apply functional_extensionality. intros.
    specialize (IHeq_type (envkv_cons J (true,K1) x WFJ) TStar h1 h2). auto.
  - dependent destruction h1. dependent destruction h2. simpl.
    apply functional_extensionality. intros.
    specialize (IHeq_type (envkv_cons J (true,K1) x WFJ) K2 h1 h2). auto.
  - dependent destruction h1. dependent destruction h2. simpl.
    specialize (eq_type_preserve_kind' H0 h1_2); intros. specialize (hk_unique' _ _ _ h2_2 _ H1). clear H1. intros; subst.
    specialize (IHeq_type1 WFJ (TFun K1 K2) h1_1 h2_1). specialize (IHeq_type2 WFJ (K1) h1_2 h2_2).
    rewrite IHeq_type2. rewrite IHeq_type1. auto.
  - remember (subst T2 (length J) T1).
    replace T1 with ((splice (length J) 0 T1)) in Heqt. 2: eapply splice_zero.
    dependent destruction h1. simpl. dependent destruction h1_1. simpl. erewrite valt_subst1'; eauto. unfold hask_subst1'.
    unfold eq_rect. remember (splice_zero T1 (length J)).
    clear Heqe.
    dependent destruction e.
    subst t. eapply val_type_irrel.
Qed.

Lemma sem_equiv: forall G J t T1 T2, eq_type J T1 T2 ->
    has_kind J T2 TStar ->
    sem_type G J t T1 ->
    sem_type G J t T2.
Proof.
  intros ????? KX HK HX. intros H WFJ WFE.
  edestruct HX as (vx & h1 & A & VX). eauto.
  eexists vx.
  exists HK.
  split.
  - eauto.
  - erewrite <- val_type_equiv; eauto.
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
  exp_type [] [] (envkv_nil) t T.
Proof.
  intros. eapply fundamental in H as ST; eauto.
  edestruct (ST []) as (v & ? & ? & ?). eapply envt_empty.
  exists v, x. intuition. eapply H1.
Qed.

End STLC.
