(* Full safety for STLC *)

(*

An LR-based termination and semantic soundness proof for STLC.

Canonical big-step cbv semantics.

Prototype for Fw, combining type abstraction and
type operators. 


TODO:

- weakening for has_kind, val_type

- substitution for has_kind, val_type

- bring back type equiv judgment and
  proper conversion rule (how: need binary LR?
  or just rely on valt_subst?)


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

Inductive kn : Type :=
  | KTpe : kn
  | KArr : kn -> kn -> kn
.

Inductive ty : Type :=
  | TBool  : ty
  | TVar   : id -> ty
  | TFun   : ty -> ty -> ty
  | TAll   : kn -> ty -> ty
  | TTAbs  : kn -> ty -> ty
  | TTApp  : ty -> ty -> ty
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

Definition tpe := vl -> Prop.


Definition venv := list vl.
Definition tenv := list ty.
Definition kenv := list kn.

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
  | TVar x        => TVar (if x <? i then x else x + n)
  | TFun t1 t2    => TFun (splice i n t1) (splice i n t2)
  | TAll k t      => TAll k (splice i n t)
  | TTAbs k t     => TTAbs k (splice i n t)
  | TTApp t1 t2   => TTApp (splice i n t1) (splice i n t2)
end.

Fixpoint subst (t: ty) (i: nat) (u:ty): ty := 
  match t with 
  | TBool         => TBool
  | TVar x        => if i =? x then u else if i <? x then (TVar (pred x)) else (TVar x)   
  | TFun t1 t2    => TFun (subst t1 i u) (subst t2 i u)
  | TAll k t      => TAll k (subst t i (splice i 1 u)) 
  | TTAbs k t     => TTAbs k (subst t i (splice i 1 u)) 
  | TTApp t1 t2   => TTApp (subst t1 i u) (subst t2 i u)
end.


(* ---------- LR definitions for types : kinds  ---------- *)

Inductive has_kind J : ty -> kn -> Type :=
| k_bool:
    has_kind J TBool KTpe
| k_var: forall x K,
    indexr x J = Some K ->
    has_kind J (TVar x) K
| k_fun: forall T1 T2,
    has_kind J T1 KTpe ->
    has_kind J T2 KTpe ->
    has_kind J (TFun T1 T2) KTpe
| k_all: forall K1 T2,
    has_kind (K1::J) T2 KTpe ->
    has_kind J (TAll K1 T2) KTpe
| k_tabs: forall K1 T2 K2,
    has_kind (K1::J) T2 K2 ->
    has_kind J (TTAbs K1 T2) (KArr K1 K2)
| k_tapp: forall TF TX K1 K2,
    has_kind J TF (KArr K1 K2) ->
    has_kind J TX K1 ->
    has_kind J (TTApp TF TX) K2
.

Inductive has_type : tenv -> kenv -> tm -> ty -> Type :=
| t_true: forall G J,
    has_type G J ttrue TBool
| t_false: forall G J,
    has_type G J tfalse TBool
| t_var: forall x G J T,
    indexr x G = Some T ->
    has_type G J (tvar x) T

| t_abs: forall G J t T1 T2,
    has_type (T1::G) J t T2 ->
    has_kind J T1 KTpe ->
    has_kind J T2 KTpe ->
    has_type G J (tabs t) (TFun T1 T2)
| t_app: forall G J f t T1 T2,
    has_type G J f (TFun T1 T2) ->
    has_type G J t T1 ->
    has_type G J (tapp f t) T2

| t_tabs: forall G J t K1 T2,
    has_type (map (splice (length J) 1) G) (K1::J) t T2 ->
    has_kind (K1::J) T2 KTpe ->
    has_type G J (ttabs t) (TAll K1 T2)
| t_tapp: forall G J f K1 T1 T2,
    has_type G J f (TAll K1 T2) ->
    has_kind J T1 K1 ->
    has_type G J (ttapp f T1) (subst T2 (length J) T1)

| t_equiv: forall G J t T1 T2,
    has_type G J t T1 ->
    T1 = T2 ->  (* XXX add proper eq predicate (see ..equiv_opr2.v) ! *)
    has_kind J T2 KTpe ->
    has_type G J t T2
.

#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.


(* example *)

(*
Example ex1: has_type [] [] (tapp (tabs (tvar 0)) ttrue) TBool.
Proof.
  econstructor. econstructor. econstructor. econstructor.
  simpl. eauto.
  2: { econstructor. econstructor.
       eexists. split. eauto.
       eexists. split. 2: eapply treify_bool. eauto. }
  eexists. eauto.
  eexists. split. eexists. eauto. eauto.
Qed.
*)




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

Lemma splice_acc: forall e1 a b c,
  splice a c (splice a b e1) =
  splice a (c+b) e1.
Proof. induction e1; intros; simpl; intuition.
  + bdestruct (i <? a); intuition.  
    bdestruct (i <? a); intuition.
    bdestruct (i+b <? a); intuition.   
  + specialize (IHe1_1 a b c). specialize (IHe1_2 a b c).
    rewrite IHe1_1. rewrite IHe1_2. auto.
  + specialize (IHe1 a b c).
    rewrite IHe1. auto.
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
  + rewrite IHe1. auto.
  + rewrite IHe1. auto.
  + rewrite IHe1_1. rewrite IHe1_2. auto.
Qed.




(* ---------- LR definitions for values : types  ---------- *)

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



Fixpoint val_kind K :=
  match K with
  | KTpe => tpe
  | KArr K1 K2 => val_kind K1 -> val_kind K2
  end.


Definition env_kv J :=
  forall x K, indexr x J = Some K -> val_kind K.

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

Require Import Coq.Arith.Compare_dec.

Lemma envkv_weaken: forall J' J K,
    val_kind K ->
    env_kv (J'++J) ->
    env_kv (J'++K::J).
Proof.
  intros. intros ???.  
  destruct (Nat.eq_dec x (length J)). subst.
  rewrite indexr_skips in H. rewrite indexr_head in H. inversion H. subst. eauto.
  simpl. eauto.
  destruct (lt_dec x (length J)). 
  rewrite indexr_skips in H. rewrite indexr_skip in H. eapply X0.
  rewrite indexr_skips. eauto. eapply indexr_var_some' in H. eauto.
  eauto. simpl. eauto.
  remember (x-1) as y. 
  replace x with (if y <? length J then y else (S y)) in H.
  rewrite indexr_splice1 in H.
  eapply X0. eauto.
  bdestruct (y <? length J). lia. lia. 
Defined.



(*
Fixpoint val_type0 {J T K} (h : has_kindv J T K) (W : env_kv J) {struct h}: val_kind K :=
  match h, T, K return val_kind K with
  | kv_bool _, _, _ => vt_bool
  | kv_var _ x K IX, _, _ => W x K IX
  | kv_fun _ T1 T2 h1 h2, _, _ => vt_fun (val_type0 h1 W) (val_type0 h2 W)
  | kv_all _ K T2 h, _, _ => vt_all (val_kind K) (fun VT1 => val_type0 h (envkv_cons _ _ VT1 W))
  end.
*)


Fixpoint val_type {J T K} (h : has_kind J T K) (W : env_kv J) {struct h}: val_kind K :=
  match h, T, K return val_kind K with
  | k_bool _, _, _ =>
      vt_bool
  | k_var _ x K IX, _, _ =>
      W x K IX
  | k_fun _ T1 T2 h1 h2, _, _ =>
      vt_fun (val_type h1 W) (val_type h2 W)
  | k_all _ K1 T2 h, _, _ =>
      vt_all (val_kind K1) (fun VT1 => val_type h (envkv_cons _ _ VT1 W))
  | k_tabs _ K1 T2 K2 h, _, _ =>
      (fun VT1 => val_type h (envkv_cons _ _ VT1 W))
  | k_tapp _ TF TX K1 K2 hf hx, _, _ =>
      val_type hf W (val_type hx W)
  end.



Definition exp_type H J (h2: env_kv J) t T :=
  exists v (h1: has_kind J T KTpe),
    tevaln H t v /\
    val_type h1 h2 v.

Definition env_type (H: venv) (G: tenv) (J: kenv) (h2: env_kv J):=
  length H = length G /\
  forall x T,
    indexr x G = Some T ->
    exists v (h1: has_kind J T KTpe),
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


Lemma hk_unique: forall GV T K
  (a b: has_kind GV T K), a = b.
Proof. 
  intros GV T K a.
  induction a; intros b; dependent destruction b.
  - eauto. 
  - eapply f_equal. eapply proof_irrelevance.
  - specialize (IHa1 b1).
    specialize (IHa2 b2).
    subst. eauto.
  - specialize (IHa b).
    subst. eauto.
  - specialize (IHa b).
    subst. eauto.
  - specialize (hk_unique' _ _ _ a2 _ b2). intros. subst. 
    specialize (IHa2 b2). subst. 
    specialize (IHa1 b1). subst. 
    eauto.
Qed.


(* weakening *)

Lemma haskind_weaken: forall T J' J K K1,
    has_kind (J' ++ J) T K ->
    has_kind (J' ++ K1 :: J) (splice (length J) 1 T) K.
Proof.
  intros T. induction T; intros; inversion H; subst; simpl in *. 
  - eapply k_bool.
  - eapply k_var. replace (i+1) with (1+i). 2: lia. 
    erewrite indexr_splice1. eauto. 
  - eapply k_fun. eauto. eauto.
  - eapply k_all. eapply IHT with (J':=k::J'). eauto.
  - eapply k_tabs. eapply IHT with (J':=k::J'). eauto.
  - eapply k_tapp. eauto. eauto. 
Defined.

Fixpoint haskind_weaken1 T: forall J' J K K1,
    has_kind (J' ++ J) T K ->
    has_kind (J' ++ K1 :: J) (splice (length J) 1 T) K.
Proof.
  destruct T; intros; inversion H; subst; simpl in *. 
  - eapply k_bool.
  - eapply k_var. replace (i+1) with (1+i). 2: lia. 
    erewrite indexr_splice1. eauto. 
  - eapply k_fun. eauto. eauto.
  - eapply k_all. eapply haskind_weaken1 with (J':=k::J'). eauto.
  - eapply k_tabs. eapply haskind_weaken1 with (J':=k::J'). eauto.
  - eapply k_tapp. eauto. eauto. 
Defined.


Lemma haskind_extend: forall T J K K1,
    has_kind J T K ->
    has_kind (K1 :: J) (splice (length J) 1 T) K.
Proof.
  intros. eapply haskind_weaken1 with (J':=[]). eauto. 
Defined.


(* TODO: env_kv helper lemmas *)

Lemma envkv_weaken_eq_extend: forall J K1 vk h2,
      envkv_weaken [] J K1 vk h2 = envkv_cons J K1 vk h2.
Proof.
Admitted.


Lemma aux1: forall J' J (h2 : env_kv (J' ++ J)) i K e K1 vk e1,
    
    h2 i K e = (envkv_weaken J' J K1 vk h2) (if i <? length J then i else i+1) K e1.
Proof.
  intros.
  unfold envkv_weaken. bdestruct (i <? length J).
  remember (Nat.eq_dec i (length J)).
  destruct s. lia.
  remember (lt_dec i (length J)).
  destruct s.
  simpl. 
Admitted.

Lemma aux2: forall J' J K1 k vk h2 VT1,
    (envkv_cons (J' ++ K1 :: J) k VT1 (envkv_weaken J' J K1 vk h2)) =
      (envkv_weaken (k :: J') J K1 vk (envkv_cons (J' ++ J) k VT1 h2)).
Proof.
  intros.
Admitted. 


Lemma valt_weaken: forall T J' J K1 K vk (h1: has_kind (J'++J) T K) h2,
    val_type h1 h2 =
    val_type (haskind_weaken1 T J' J K K1 h1)
    (envkv_weaken J' J K1 vk h2).
Proof.
  intros T. induction T; intros; inversion h1; subst.
  - dependent destruction h1.
    simpl. split; eauto.
  - dependent destruction h1.
    remember (k_var (J'++J) i K e) as hx1.
    remember ((haskind_weaken1 (TVar i) J' J K K1 hx1)) as hx1'.
    remember ((envkv_weaken J' J K1 vk h2)) as h2'.
    dependent destruction hx1. inversion Heqhx1. rewrite Heqhx1 in *.
    dependent destruction hx1'.
    simpl.
    subst h2'. eapply aux1.
  - (* TFun *)
    dependent destruction h1.
    simpl in *. 
    assert (val_type h1_1 h2 = val_type (haskind_weaken1 T1 J' J KTpe K1 h1_1) (envkv_weaken J' J K1 vk h2)). eapply IHT1. 
    assert (val_type h1_2 h2 = val_type (haskind_weaken1 T2 J' J KTpe K1 h1_2) (envkv_weaken J' J K1 vk h2)). eapply IHT2. 
    rewrite H, H0. eauto.
  - (* TAll *)
    dependent destruction h1. simpl.
    assert (forall VT1, val_type h1 (envkv_cons (J'++J) k VT1 h2) =
                          val_type (haskind_weaken1 T (k::J') J KTpe K1 h1) (envkv_weaken (k::J') J K1 vk (envkv_cons (J'++J) k VT1 h2))). {
    intros. 
    specialize IHT with (J':=k::J') (J:=J) (vk:=vk) (h1:=h1) (h2:=(envkv_cons (J'++J) k VT1 h2)).
    eapply IHT.}
    eapply functional_extensionality in H.
    rewrite H.
    assert (forall VT1,
     val_type (haskind_weaken1 T (k :: J') J KTpe K1 h1) (envkv_weaken (k :: J') J K1 vk (envkv_cons (J' ++ J) k VT1 h2)) = val_type (haskind_weaken1 T (k :: J') J KTpe K1 h1) (envkv_cons (J' ++ K1 :: J) k VT1 (envkv_weaken J' J K1 vk h2))).
    intros. rewrite aux2. eauto.
    eapply functional_extensionality in H0.
    rewrite H0. eauto.
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
  erewrite H. 2: 
  eapply envkv_weaken_eq_extend. split; eauto. 
Qed.



(* substitution *)

Lemma hask_subst: forall J T2 T1 K1,
    has_kind (K1 :: J) T2 KTpe ->
    has_kind J T1 K1 ->
    has_kind J (subst T2 (length J) T1) KTpe.
Proof.
Admitted.

Lemma valt_subst: forall J K1 T1K WFJ T2' T1' (h1f : has_kind (K1 :: J) T2' KTpe) HK1 vy,
  val_type h1f (envkv_cons J K1 T1K WFJ) vy <-> 
  val_type (hask_subst J T2' T1' K1 h1f HK1) WFJ vy.
Proof.
Admitted.


(* ---------- env extension lemmas  ---------- *)

Lemma envt_empty: forall W,
    env_type [] [] [] W.
Proof.
  intros. split. eauto. intros. inversion H. 
Qed.

Lemma envt_extend: forall E G J h2 v1 T1 (h1: has_kind J T1 KTpe),
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

Lemma envt_extendk: forall E G J h2 K1 (vk: val_kind K1),
    env_type E G J h2 ->
    env_type E (map (splice (length J) 1) G) (K1::J) (envkv_cons J K1 vk h2).
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
    has_kind J T1 KTpe ->
    has_kind J T2 KTpe ->
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
    sem_type (map (splice (length J) 1) G) (K1::J) t T2 ->
    has_kind (K1::J) T2 KTpe ->
    sem_type G J (ttabs t) (TAll K1 T2).
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
  exists (hask_subst _ _ _ _ h1f HX).
  split.
  - destruct STF as (n1 & STF).
    destruct STY as (n2 & STY). 
    exists (1+n1+n2). intros. destruct n. lia. simpl. rewrite STF, STY. 2,3: lia. eauto.
  - eapply valt_subst. eauto. 
Qed.
  

Lemma sem_equiv: forall G J t T1 T2,
    sem_type G J t T1 ->
    has_kind J T2 KTpe ->
    sem_type G J t T2.
Proof.
  intros ????? HX KX. intros H WFJ WFE.
  edestruct HX as (vx & h1 & A & VX). eauto. 
  eexists vx.
  eexists KX.
  split. 
  - eauto.
  - admit.
Admitted.

                                                       
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
