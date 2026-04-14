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
(*  | TVar   : id -> tm   <--- now using tvar x! (alias below) *)
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
  | ttapp  : tm -> tm(*ty!*) -> tm
  | ttabs  : tm -> tm -> tm
.

Inductive vl: Type :=
  | vbool  :  bool -> vl
  | vabs   :  list vl -> tm -> vl
  | vtabs  :  list vl -> tm -> vl
.

Definition ty := tm.
Definition TVar x := tvar x.


Definition binding := (bool * tm)%type.

(* the interpretation of kind, which defines the set at * *)
Definition tpe := vl -> Prop.
Definition venv := list vl.
Definition tenv := list binding.
Definition kenv := tenv.

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
              teval n ((vbool false)::env2) ey
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
  | tvar x        => tvar (if x <? i then x else x + n)
  | TFun t1 t2    => TFun (splice i n t1) (splice i n t2)
  | TAll k t      => TAll (splice i n k) (splice i n t)
  | ttrue         => ttrue
  | tfalse        => tfalse
  | tapp t1 t2    => tapp (splice i n t1) (splice i n t2)
  | tabs t1       => tabs (splice i n t1)
  | ttapp t1 t2   => ttapp (splice i n t1) (splice i n t2)
  | ttabs t1 t2   => ttabs (splice i n t1) (splice i n t2)
  end.

Fixpoint subst (t: tm) (i: nat) (u:tm): tm :=
  match t with
  | TStar         => TStar
  | TBox          => TBox
  | TBool         => TBool
  | tvar x        => if Nat.eq_dec x i then u else tvar (if x <? i then x else x-1)
  | TFun t1 t2    => TFun (subst t1 i u) (subst t2 i u)
  | TAll k t      => TAll (subst k i u) (subst t i (splice i 1 u))
  | ttrue         => ttrue
  | tfalse        => tfalse
  | tapp t1 t2    => tapp (subst t1 i u) (subst t2 i u)
  | tabs t1       => tabs (subst t1 i (splice i 1 u))
  | ttapp t1 t2   => ttapp (subst t1 i u) (subst t2 i u)
  | ttabs t1 t2   => ttabs (subst t1 i u) (subst t2 i (splice i 1 u))
  end.

Definition bsplice i n (b: binding) : binding :=
  match b with
  | (is_ty, T) => (is_ty, splice i n T)
  end.



Definition bind_tm (T: tm) : binding := (false, T).
Definition bind_ty (K: tm) : binding := (true, K).
Definition ext (b: binding) (G: tenv) : tenv := map (bsplice (length G) 1) (b :: G).

(* multi-extension: fold ext over a list of bindings *)
Fixpoint mext (bs: list binding) (G: tenv) : tenv :=
  match bs with
  | [] => G
  | b :: bs' => ext b (mext bs' G)
  end.

Lemma mext_length: forall bs G,
    length (mext bs G) = length bs + length G.
Proof.
  induction bs; intros; simpl.
  - lia.
  - unfold ext. rewrite map_length. simpl. rewrite IHbs. lia.
Qed.


(* ---------- LR definitions for types : kinds  ---------- *)

Inductive has_kind J : tm -> tm -> Type :=
| k_star:
    has_kind J TStar TBox
| k_bool:
    has_kind J TBool TStar
| k_var: forall x K,
    indexr x J = Some (true, K) ->
    has_kind J (TVar x) K
| k_fun: forall T1 T2, (* (term -> term): type *)
    has_kind J T1 TStar ->
    has_kind J T2 TStar ->
    has_kind J (TFun T1 T2) TStar
| k_all: forall K1 T2, (* (type -> term): type *)
    has_kind (ext (bind_ty K1) J) T2 TStar ->
    has_kind J (TAll K1 T2) TStar
| k_karr: forall K1 K2, (* (type -> type): kind *)
    has_kind J K1 TBox ->
    has_kind J K2 TBox ->
    has_kind J (TFun K1 K2) TBox
| k_tabs: forall K1 T2 K2,
    has_kind (ext (bind_ty K1) J) T2 K2 ->
    has_kind J (ttabs K1 T2) (TFun K1 K2) (* (tabs K1 T2) (TPi K1 K2) *)
| k_tapp: forall TF TX K1 K2,
    has_kind J TF (TFun K1 K2) ->
    has_kind J TX K1 ->
    has_kind J (ttapp TF TX) K2
.

Inductive eq_type : tenv -> tm -> tm -> Type :=
| q_refl: forall J T,
    eq_type J T T
| q_symm: forall J T1 T2,
    eq_type J T1 T2 ->
    eq_type J T2 T1
| q_trans: forall J T1 T2 T3,
    eq_type J T1 T2 ->
    eq_type J T2 T3 ->
    eq_type J T1 T3
| q_fun: forall J T1 T2 T1' T2',
    eq_type J T1 T1' ->
    eq_type J T2 T2' ->
    eq_type J (TFun T1 T2) (TFun T1' T2')
| q_tall : forall J T2 T2' K1,
    eq_type (ext (bind_ty K1) J) T2 T2' ->
    eq_type J (TAll K1 T2) (TAll K1 T2')
| q_tabs: forall J T2 T2' K1,
    eq_type (ext (bind_ty K1) J) T2 T2' ->
    eq_type J (ttabs K1 T2) (ttabs K1 T2')
| q_tapp: forall J T1 T2 T1' T2',
    eq_type J T1 T1' ->
    eq_type J T2 T2' ->
    eq_type J (ttapp T1 T2) (ttapp T1' T2')
| q_beta: forall J T1 T2 K1,
    has_kind J T1 K1 ->
    eq_type J (ttapp (ttabs K1 T2) T1) (subst T2 (length J) T1)
.

Inductive has_type : tenv -> tm -> tm -> Type :=
| t_true: forall G,
    has_type G ttrue TBool
| t_false: forall G,
    has_type G tfalse TBool
| t_var: forall x G T,
    indexr x G = Some (false, T) ->
    has_type G (tvar x) T

| t_abs: forall G t T1 T2,
    has_type (ext (bind_tm T1) G) t (splice (length G) 1 T2) ->
    has_kind G T1 TStar ->
    has_kind G T2 TStar ->
    has_type G (tabs t) (TFun T1 T2)
| t_app: forall G f t T1 T2,
    has_type G f (TFun T1 T2) ->
    has_type G t T1 ->
    has_type G (tapp f t) T2

| t_tabs: forall G t K1 T2,
    has_type (ext (bind_ty K1) G) t T2 ->
    has_kind (ext (bind_ty K1) G) T2 TStar ->
    has_type G (ttabs K1 t) (TAll K1 T2)
| t_tapp: forall G f K1 T1 T2,
    has_type G f (TAll K1 T2) ->
    has_kind G T1 K1 ->
    has_type G (ttapp f T1) (subst T2 (length G) T1)

| t_equiv: forall G t T1 T2,
    has_type G t T1 ->
    eq_type G T1 T2 ->
    has_kind G T2 TStar ->
    has_type G t T2
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

Lemma indexr_map'': forall {A B} (M: list A) x v (f: A -> B),
    indexr x (map f M) = Some v ->
    {v' & indexr x M = Some v' & v = f v'}.
Proof.
  intros. erewrite indexr_map in H.
  2: { eapply indexr_var_some' in H. rewrite map_length in H.
       eapply indexr_var_some in H. destruct H. eauto. }
  remember (indexr x M). destruct o. inversion H.
  eexists. eauto. eauto. inversion H.
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
  - rewrite IHe1_1, IHe1_2. auto.
  - rewrite IHe1_1, IHe1_2. auto.
  - bdestruct (i <? a); simpl.
    + bdestruct (i <? a); [auto | lia].
    + bdestruct (i + b <? a); [lia | f_equal; lia].
  - rewrite IHe1_1, IHe1_2. auto.
  - rewrite IHe1. auto.
  - rewrite IHe1_1, IHe1_2. auto.
  - rewrite IHe1_1, IHe1_2. auto.
Qed.

Lemma splice_acc': forall e1 a b c,
  splice (b+a) c (splice a b e1) =
  splice a (c+b) e1.
Proof.
  induction e1; intros; simpl; try reflexivity.
  - rewrite IHe1_1, IHe1_2. auto.
  - rewrite IHe1_1, IHe1_2. auto.
  - bdestruct (i <? a); simpl.
    + bdestruct (i <? a); [|lia]. bdestruct (i <? b+a); [|lia]. auto.
    + bdestruct (i + b <? b + a); [lia|]. f_equal. lia.
  - rewrite IHe1_1, IHe1_2. auto.
  - rewrite IHe1. auto.
  - rewrite IHe1_1, IHe1_2. auto.
  - rewrite IHe1_1, IHe1_2. auto.
Qed.

Lemma splice_zero: forall e1 a,
  (splice a 0 e1) = e1.
Proof.
  intros. induction e1; simpl; try reflexivity.
  - rewrite IHe1_1, IHe1_2. auto.
  - rewrite IHe1_1, IHe1_2. auto.
  - bdestruct (i <? a); f_equal; lia.
  - rewrite IHe1_1, IHe1_2. auto.
  - rewrite IHe1. auto.
  - rewrite IHe1_1, IHe1_2. auto.
  - rewrite IHe1_1, IHe1_2. auto.
Qed.

Lemma splice_var_comm: forall i a c b d,
    a <= b ->
    (if (if i <? b then i else i + d) <? a
     then (if i <? b then i else i + d)
     else (if i <? b then i else i + d) + c) =
    (if (if i <? a then i else i + c) <? b + c
     then (if i <? a then i else i + c)
     else (if i <? a then i else i + c) + d).
Proof.
  intros.
  bdestruct (i <? b); bdestruct (i <? a).
  - bdestruct (i <? a); [|lia]. bdestruct (i <? b + c); [|lia]. lia.
  - bdestruct (i <? a); [lia|].
    destruct (Nat.ltb_spec (i+c) (b+c)); lia.
  - lia.
  - destruct (Nat.ltb_spec (i+d) a); [lia|].
    destruct (Nat.ltb_spec (i+c) (b+c)); [lia|]. lia.
Qed.

Lemma splice_comm: forall e1 a c b d,
    a <= b ->
    splice a c (splice b d e1) = splice (b+c) d (splice a c e1).
Proof.
  induction e1; intros; simpl; try reflexivity;
    try (rewrite IHe1_1, IHe1_2; auto; fail);
    try (rewrite IHe1; auto; fail).
  - f_equal. apply splice_var_comm. auto.
Qed.

Lemma bsplice_comm: forall (b: binding) a c i d,
    a <= i ->
    bsplice a c (bsplice i d b) = bsplice (i+c) d (bsplice a c b).
Proof.
  intros [? ?]; simpl; intros; f_equal; apply splice_comm; auto.
Qed.

Lemma map_bsplice_comm: forall G a c i d,
    a <= i ->
    map (bsplice a c) (map (bsplice i d) G) = map (bsplice (i+c) d) (map (bsplice a c) G).
Proof.
  induction G; simpl; intros; [auto|].
  rewrite bsplice_comm; auto. f_equal. apply IHG; auto.
Qed.

Lemma ext_map_bsplice: forall b n m G,
    n <= m ->
    m = length G ->
    map (bsplice n 1) (bsplice m 1 b :: map (bsplice m 1) G) =
    map (bsplice (m+1) 1) (bsplice n 1 b :: map (bsplice n 1) G).
Proof.
  intros. simpl. f_equal.
  - apply bsplice_comm; auto.
  - apply map_bsplice_comm; auto.
Qed.

(* key lemma: when IH uses bsplice m 1 K1 as weakening binding,
   the double-map on the full list commutes via map_bsplice_comm *)
Lemma weaken_ext_comm: forall b J' J K1,
    let n := length J in
    let m := length (J' ++ J) in
    map (bsplice n 1) (map (bsplice m 1) (b :: J' ++ K1 :: J)) =
    map (bsplice (m+1) 1) (map (bsplice n 1) (b :: J' ++ K1 :: J)).
Proof.
  intros. subst n m. apply map_bsplice_comm. rewrite app_length. lia.
Qed.


(* substitution on bindings *)
Definition bsubst i u (b: binding) : binding :=
  match b with (is_ty, T) => (is_ty, subst T i u) end.

(* position-dependent substitution of each entry in J'.
   Entry b at depth k (with k entries below it in J') is substituted
   with splice i k T1, because there are k bindings between it and the base env. *)
Fixpoint msubst (J': list binding) (i: nat) (T1: tm) : list binding :=
  match J' with
  | [] => []
  | b :: bs => bsubst i (splice i (length bs) T1) b :: msubst bs i T1
  end.

Lemma msubst_length: forall J' i T1,
    length (msubst J' i T1) = length J'.
Proof.
  induction J'; intros; simpl; auto.
Qed.

(* key identity: substituting after a splice that created the variable cancels to a smaller splice *)
Fixpoint subst_splice_cancel (e: tm) : forall n m u,
    subst (splice n (S m) e) n u = splice n m e.
Proof.
  destruct e; intros; simpl;
    try reflexivity;
    try (rewrite ?subst_splice_cancel; reflexivity);
    try (rewrite ?subst_splice_cancel; rewrite ?subst_splice_cancel; reflexivity);
    (* TVar *)
    try (bdestruct (i <? n); simpl;
         [destruct (Nat.eq_dec i n); [lia|]; bdestruct (i <? n); [reflexivity|lia]
         |destruct (Nat.eq_dec (i + S m) n); [lia|]; bdestruct (i + S m <? n); [lia|f_equal; lia]]).
Defined.

Lemma bsubst_bsplice_cancel: forall b i m u,
    bsubst i u (bsplice i (S m) b) = bsplice i m b.
Proof.
  intros [b0 t]. intros. simpl. rewrite subst_splice_cancel. reflexivity.
Qed.

(* ---------- env extension lemmas  ---------- *)


Lemma ext_length: forall b G,
    length (ext b G) = S (length G).
Proof.
  intros. simpl. rewrite map_length. eauto.
Qed.

Lemma ext_unfold: forall b G,
    ext b G = (bsplice (length G) 1 b) :: map (bsplice (length G) 1) G.
Proof.
  intros. unfold ext. simpl. eauto. 
Qed.

Lemma indexr_head_ext: forall b G,
    indexr (length G) (ext b G) = Some (bsplice (length G) 1 b).
Proof.
  intros. 
  unfold ext. remember (map _ _) as G'.
  simpl in HeqG'. subst G'. remember (map _ _) as G''.
  replace (length G) with (length G''). rewrite indexr_head. eauto.
  subst G''. rewrite map_length. eauto.
Qed.

Check indexr_skip. 

Lemma indexr_skip_ext: forall i b G,
    i <> length G ->
    indexr i (ext b G) = indexr i (map (bsplice (length G) 1) G).
Proof.
  intros. 
  unfold ext. remember (map _ _) as G'.
  simpl in HeqG'. subst G'. remember (map _ _) as G''.
  rewrite indexr_skip. eauto.  
  subst G''. rewrite map_length. eauto.
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
            tevaln (vbool false::H) ty vy /\
            (TF T1) vy
    | _ => False
    end.



Fixpoint val_sort (K: tm) : Type :=
  match K with
  | TStar => tpe
  | TFun K1 K2 => val_sort K1 -> val_sort K2
  | _ => unit
  end.

Fixpoint val_sort1 (b: binding) : Type :=
  match b with
  | (false, _) => unit
  | (true, K) => val_sort K
  end.


Fixpoint val_sort_splice (K: tm) : forall i n,
    val_sort (splice i n K) = val_sort K.
Proof.
  destruct K; intros; simpl; try reflexivity.
  - rewrite val_sort_splice, val_sort_splice. reflexivity.
Defined.

Lemma val_sort1_bsplice: forall b i n,
    val_sort1 (bsplice i n b) = val_sort1 b.
Proof.
  intros [is_ty T] i n. destruct is_ty; simpl.
  - rewrite val_sort_splice. reflexivity.
  - reflexivity.
Defined.

Definition vs_cast {K} (i n: nat) (v: val_sort (splice i n K)) : val_sort K :=
  eq_rect _ (fun T => T) v _ (val_sort_splice K i n).

Definition vs_uncast {K} (i n: nat) (v: val_sort K) : val_sort (splice i n K) :=
  eq_rect _ (fun T => T) v _ (eq_sym (val_sort_splice K i n)).

Definition vs1_uncast {K} (i n: nat) (v: val_sort1 K) : val_sort1 (bsplice i n K) :=
  eq_rect _ (fun T => T) v _ (eq_sym (val_sort1_bsplice K i n)).

Lemma vs_cast_uncast: forall K i n (v: val_sort K),
    vs_cast i n (vs_uncast i n v) = v.
Proof.
  intros. unfold vs_cast, vs_uncast.
  generalize (val_sort_splice K i n).
  intros e. destruct e. reflexivity.
Defined.

Lemma vs_uncast_cast: forall K i n (v: val_sort (splice i n K)),
    vs_uncast i n (vs_cast i n v) = v.
Proof.
  intros. unfold vs_cast, vs_uncast.
  generalize (val_sort_splice K i n).
  intros e. destruct e. reflexivity.
Defined.

Lemma vs_uncast_fun: forall K1 K2 i n (f: val_sort K1 -> val_sort K2)
    (x: val_sort (splice i n K1)),
    (vs_uncast (K:=TFun K1 K2) i n f) x = vs_uncast i n (f (vs_cast i n x)).
Proof.
  intros. unfold vs_cast, vs_uncast.
  simpl. unfold eq_sym, eq_ind_r, eq_rect, eq_ind.
  generalize (val_sort_splice K1 i n).
  generalize (val_sort_splice K2 i n).
  intros e2 e1. destruct e1, e2. reflexivity.
Defined.

Lemma vs_cast_fun: forall K1 K2 i n (f: val_sort (splice i n K1) -> val_sort (splice i n K2))
    (x: val_sort K1),
    vs_cast i n (f (vs_uncast i n x)) = (vs_cast (K:=TFun K1 K2) i n f) x.
Proof.
  intros. unfold vs_cast, vs_uncast.
  simpl. unfold eq_sym, eq_ind_r, eq_rect, eq_ind.
  generalize (val_sort_splice K1 i n).
  generalize (val_sort_splice K2 i n).
  intros e2 e1. destruct e1, e2. reflexivity.
Defined.

Lemma vt_all_cast: forall K i n (F1: val_sort K -> tpe) (F2: val_sort (splice i n K) -> tpe),
    (forall x, F1 x = F2 (vs_uncast i n x)) ->
    vt_all (val_sort K) F1 = vt_all (val_sort (splice i n K)) F2.
Proof.
  intros K i n F1 F2 HF.
  unfold vt_all. apply functional_extensionality. intros v.
  destruct v; try reflexivity.
  apply propositional_extensionality.
  split; intros Hall.
  - intros T1.
    specialize (Hall (vs_cast i n T1)). destruct Hall as [vy [? ?]].
    exists vy. split. auto.
    pose proof (HF (vs_cast i n T1)) as E.
    rewrite E in H0. rewrite (vs_uncast_cast K i n) in H0. exact H0.
  - intros T1.
    specialize (Hall (vs_uncast i n T1)). destruct Hall as [vy [? ?]].
    exists vy. split. auto.
    pose proof (HF T1) as E. rewrite E. exact H0.
Defined.

Definition env_kv J :=
  forall x b, indexr x J = Some b -> val_sort1 b.

Lemma envkv_nil:
  env_kv nil.
Proof.
  intros ???. inversion H.
Defined.

Lemma envkv_cons: forall J b,
    val_sort1 b ->
    env_kv J ->
    env_kv (b::J).
Proof.
  intros. intros ???.
  destruct (Nat.eq_dec x (length J)). subst.
  rewrite indexr_head in H. inversion H. subst. eauto.
  rewrite indexr_skip in H. eapply X0. eauto. eauto.
Defined.

Lemma indexr_hit: forall {T} J' J (K:T) ,
    indexr (length J) (J' ++ K :: J) = Some K.
Proof.
  intros. rewrite indexr_skips. rewrite indexr_head. eauto. simpl. eauto.
Qed.

Lemma envkv_weaken: forall J' J b,
    val_sort1 b ->
    env_kv (J'++J) ->
    env_kv (J'++b::J).
Proof.
  intros. intros ???.
  destruct (Nat.eq_dec x (length J)). subst.
  rewrite indexr_hit in H. inversion H. subst. eauto.
  rewrite indexr_splice2 in H; eauto.
Defined.

Lemma envkv_splice: forall i n J,
    env_kv J ->
    env_kv (map (bsplice i n) J).
Proof.
  intros. intros ???.
  eapply indexr_map'' in H. destruct H. subst b.
  eapply vs1_uncast. eapply X. eauto. 
Defined.

Lemma envkv_cons2: forall J b,
    val_sort1 b ->
    env_kv J ->
    env_kv (map (bsplice (length J) 1) (b::J)).
Proof.
  intros. eapply envkv_splice. eapply envkv_cons. eauto. eauto. 
Defined.

Lemma envkv_weaken2: forall J' J b,
    val_sort1 b ->
    env_kv (J'++J) ->
    env_kv (map (bsplice (length J) 1) (J'++b::J)).
Proof.
  intros. eapply envkv_splice. eapply envkv_weaken. eauto. eauto. 
Defined.




Fixpoint val_type {J T K} (h : has_kind J T K) (W : env_kv J) {struct h}: val_sort K :=
  match h, T, K return val_sort K with
  | k_star _, _, _ =>
      tt
  | k_bool _, _, _ =>
      vt_bool
  | k_var _ x K IX, _, _ =>
      W x (true, K) IX
  | k_fun _ T1 T2 h1 h2, _, _ =>
      vt_pi (val_type h1 W) (fun vx => val_type h2 W)
  | k_all _ K1 T2 h, _, _ =>
      vt_all (val_sort K1) (fun VT1 => val_type h (envkv_cons2 _ _ (VT1 : val_sort1 (true, K1)) W))
  | k_karr _ _ _ K1 K2, _, _ =>
      tt
  | k_tabs _ K1 T2 K2 h, _, _ =>
      (fun VT1 => val_type h (envkv_cons2 _ _ (VT1 : val_sort1 (true, K1)) W))
  | k_tapp _ TF TX K1 K2 hf hx, _, _ =>
      val_type hf W (val_type hx W)
  end.



Definition exp_type H G (h2: env_kv G) t T :=
  exists v (h1: has_kind G T TStar),
    tevaln H t v /\
    val_type h1 h2 v.

Definition env_type (H: venv) (G: tenv) (h2: env_kv G):=
  length H = length G /\
  forall x T,
    indexr x G = Some (false, T) ->
    exists v (h1: has_kind G T TStar),
      indexr x H = Some v /\
      val_type h1 h2 v.

Definition sem_type G t T :=
  forall H (h2: env_kv G),
    env_type H G h2 ->
    exp_type H G h2 t T.


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
  - unfold bind_ty in *. congruence.
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
  - eapply f_equal. eapply proof_irrelevance.
  - specialize (IHa1 b1).
    specialize (IHa2 b2).
    subst. eauto.
  - specialize (IHa b).
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

Fixpoint haskind_weaken1 T: forall J' J K K1,
    has_kind (J' ++ J) T K ->
    has_kind (map (bsplice (length J) 1) (J' ++ K1 :: J)) (splice (length J) 1 T) (splice (length J) 1 K).
Proof.
  destruct T; intros; simpl in *.
  - (* TStar *) inversion H; subst. eapply k_star.
  - (* TBox *) inversion H.
  - (* TBool *) inversion H; subst. eapply k_bool.
  - (* TFun *) inversion H; subst.
    + eapply k_fun.
      eapply (haskind_weaken1 T1 J' J TStar K1 H2).
      eapply (haskind_weaken1 T2 J' J TStar K1 H4).
    + eapply k_karr. 
      eapply (haskind_weaken1 T1 J' J TBox K1 H2).
      eapply (haskind_weaken1 T2 J' J TBox K1 H4).
  - (* TAll *) inversion H; subst. eapply k_all.
    (* H3: has_kind (ext (bind_ty T1) (J'++J)) T2 TStar *)
    unfold ext in H3.
    replace (bind_ty T1 :: J' ++ J) with ((bind_ty T1 :: J') ++ J) in H3 by reflexivity.
    rewrite map_app in H3.
    eapply haskind_weaken1 with (K1 := bsplice (length (J'++J)) 1 K1) in H3.
    rewrite map_length in H3.
    (* Reassemble inner list *)
    change (bsplice (length (J' ++ J)) 1 K1 :: map (bsplice (length (J' ++ J)) 1) J)
      with (map (bsplice (length (J' ++ J)) 1) (K1 :: J)) in H3.
    rewrite <- map_app in H3. simpl app in H3.
    (* H3: has_kind (map (bsplice (length J) 1) (map (bsplice (length (J'++J)) 1) (bind_ty T1 :: J' ++ K1 :: J)))
                     (splice (length J) 1 T2) TStar *)
    (* Use weaken_ext_comm to commute the double map *)
    rewrite weaken_ext_comm in H3.
    (* Now match the goal *)
    unfold ext.
    change (bind_ty (splice (length J) 1 T1)) with (bsplice (length J) 1 (bind_ty T1)).
    change (bsplice (length J) 1 (bind_ty T1) :: map (bsplice (length J) 1) (J' ++ K1 :: J))
      with (map (bsplice (length J) 1) (bind_ty T1 :: J' ++ K1 :: J)).
    rewrite map_length, app_length. simpl length.
    rewrite app_length in H3.
    replace (length J' + S (length J)) with (length J' + length J + 1) by lia.
    eapply H3.
  - inversion H.
  - inversion H.
  - (* TVar *) inversion H; subst. eapply k_var.
    replace (i + 1) with (S i) by lia.
    erewrite indexr_map. (* with (v := Some (true, K)). *)
    2: { erewrite indexr_splice1. eauto. }
    simpl. reflexivity.
  - inversion H.
  - inversion H.
  - (* TTApp *) inversion H; subst; simpl.
    exact (k_tapp _ _ _ _ _ (haskind_weaken1 T1 J' J _ K1 H2) (haskind_weaken1 T2 J' J _ K1 H4)).
  - (* TTAbs *) inversion H; subst. eapply k_tabs.
    unfold ext in H3.
    replace (bind_ty T1 :: J' ++ J) with ((bind_ty T1 :: J') ++ J) in H3 by reflexivity.
    rewrite map_app in H3.
    eapply haskind_weaken1 with (K1 := bsplice (length (J'++J)) 1 K1) in H3.
    rewrite map_length in H3.
    change (bsplice (length (J' ++ J)) 1 K1 :: map (bsplice (length (J' ++ J)) 1) J)
      with (map (bsplice (length (J' ++ J)) 1) (K1 :: J)) in H3.
    rewrite <- map_app in H3. simpl app in H3.
    rewrite weaken_ext_comm in H3.
    unfold ext.
    change (bind_ty (splice (length J) 1 T1)) with (bsplice (length J) 1 (bind_ty T1)).
    change (bsplice (length J) 1 (bind_ty T1) :: map (bsplice (length J) 1) (J' ++ K1 :: J))
      with (map (bsplice (length J) 1) (bind_ty T1 :: J' ++ K1 :: J)).
    rewrite map_length, app_length. simpl length.
    rewrite app_length in H3.
    replace (length J' + S (length J)) with (length J' + length J + 1) by lia.
    eapply H3.
Defined.


Lemma haskind_extend: forall T J K K1,
    has_kind J T K ->
    has_kind (ext K1 J) (splice (length J) 1 T) (splice (length J) 1 K).
Proof.
  intros. unfold ext. eapply haskind_weaken1 with (J':=[]). eauto.
Defined.

Fixpoint haskind_extend_mult J': forall T J K,
    has_kind J T K ->
    has_kind (mext J' J) (splice (length J) (length J') T) (splice (length J) (length J') K).
Proof.
  destruct J'; intros; simpl in *.
  - rewrite !splice_zero. eapply H.
  - eapply haskind_extend_mult in H. eapply haskind_extend in H.
    rewrite mext_length in H. rewrite !splice_acc' in H. eapply H.
Defined.

Lemma aux0: forall i i' J K
  (eq: i = i')
  (h2: forall i K, indexr i J = Some K -> val_sort1 K)
  (h2A: indexr i J = Some K -> val_sort1 K)
  (h2B: indexr i' J = Some K -> val_sort1 K)
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
      (fun o : option binding => o = Some K1) e (Some K1) e).
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

Lemma envkv_cons2_head: forall J K1 vk h2 IX,
    envkv_cons2 J K1 vk h2 (length J) K1 IX ~= (vs1_uncast (length J) 1 vk).
Proof.
  intros J K1 vk h2 IX.
  unfold envkv_cons2. unfold envkv_splice.
  remember (indexr_map'' _ _ _ _ _). destruct s.
  remember (envkv_cons _ _ _ _ _ _ _). 
  symmetry in Heqv. 
  (* want to use envkv_cons_head *)
Admitted.

Lemma envkv_cons2_skip: forall J K1 K i vk (h2:env_kv J) IX IX',
    i < length J ->
    envkv_cons2 J K1 vk h2 i K IX' = h2 i K IX. (* ??? *)
Proof.
  intros.
  unfold envkv_cons2. unfold envkv_splice. 
Admitted. 


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
      (fun o : option binding => o = Some K1) e (Some K1) e).
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

Lemma envkv_weaken_eq_extend2: forall J K1 vk h2,
    envkv_weaken2 [] J K1 vk h2 = envkv_cons2 J K1 vk h2.
Proof.
  intros.
  eapply functional_extensionality_dep. intros i.
  eapply functional_extensionality_dep. intros K.
  eapply functional_extensionality_dep. intros IX.
  simpl in *.
  assert ((if i =? length (map (bsplice (length J) 1) J)
        then Some (bsplice (length J) 1 K1)
        else indexr i (map (bsplice (length J) 1) J)) = Some K). eapply IX.
  bdestruct (i =? length (map (bsplice (length J) 1) J)).
  - inversion H. subst.
    admit. 
  - admit.
Admitted.

(* TODO: valt_weaken, valt_extend, valt_extend' need updating for ext-based environments.
   Commented out temporarily to focus on syntactic lemmas first. *)
(*
Lemma valt_weaken: ...
Lemma valt_extend: ...
Lemma valt_extend': ...
*)

Lemma valt_weaken: forall T J' J K1 K vk (h1: has_kind (app J' J) T K) h2,
      val_type h1 h2 ~=
      val_type (haskind_weaken1 T J' J _ K1 h1)
         (envkv_weaken2 J' J K1 vk h2).
Proof.
  intros T. induction T; intros; simpl in *.
  - dependent destruction h1. reflexivity.
  - inversion h1.
  - dependent destruction h1. reflexivity.
  - dependent destruction h1.
    + simpl.
      rewrite (IHT1 J' J K1 TStar vk h1_1 h2).
      rewrite (IHT2 J' J K1 TStar vk h1_2 h2).
      reflexivity.
    + simpl. reflexivity.
  - dependent destruction h1. simpl.
    admit. (* f_equal.
    apply functional_extensionality. intros VT1.
    specialize (IHT2 (bind_ty T1 :: J') J K1 TStar vk h1
      (envkv_cons (J' ++ J) (bind_ty T1) (VT1 : val_sort1 (bind_ty T1)) h2)).
    rewrite aux2. exact IHT2. *)
  - inversion h1.
  - inversion h1.
  - dependent destruction h1.
    remember (k_var (J' ++ J) i K e) as hx1.
    remember (haskind_weaken1 (TVar i) J' J K K1 hx1) as hx1'.
    remember (envkv_weaken J' J K1 vk h2) as h2'.
    dependent destruction hx1. inversion Heqhx1. rewrite Heqhx1 in *.
    dependent destruction hx1'. simpl.
    subst h2'.
    admit. (* match goal with
    | |- _ = envkv_weaken _ _ _ _ _ _ _ ?pf =>
        replace pf with e1 by apply proof_irrelevance
    end.
    exact (aux1 J' J h2 i (bind_ty K) e K1 vk e1).*)
  - inversion h1.
  - inversion h1.
  - dependent destruction h1. simpl.
    admit. (*
    rewrite (IHT1 J' J K1 _ vk h1_1 h2).
    rewrite (IHT2 J' J K1 _ vk h1_2 h2).
    reflexivity. *)
  - dependent destruction h1.
    remember (k_tabs (J' ++ J) T1 T2 K2 h1) as h1'.
    dependent destruction h1'.
    replace h1 with h1' in * by (eapply hk_unique).
    simpl.
    admit. (*
    apply functional_extensionality. intros VT1.
    specialize (IHT2 (bind_ty T1 :: J') J K1 K2 vk h1'
      (envkv_cons (J' ++ J) (bind_ty T1) (VT1 : val_sort1 (bind_ty T1)) h2)).
    rewrite aux2. exact IHT2. *)
Admitted.


Lemma valt_extend: forall T J K1 vk (h1: has_kind J T TStar) h2 v2,
    val_type h1 h2 v2 <->
    val_type (haskind_extend T J TStar K1 h1)
    (envkv_cons2 J K1 vk h2) v2.
Proof. 
  intros.
  specialize valt_weaken with (J':=[]). simpl. intros. unfold haskind_extend.
  specialize (H _ _ _ _ vk h1 h2). rewrite H. 
  rewrite envkv_weaken_eq_extend2. split; eauto.
Qed.


Lemma valt_extend': forall T J K1 K vk (h1: has_kind J T K) h2,
    val_type h1 h2 ~=
    val_type (haskind_extend T J K K1 h1)
    (envkv_cons2 J K1 vk h2).
Proof.
  intros.
  specialize valt_weaken with (J':=[]). simpl. intros. unfold haskind_extend.
  replace (envkv_cons2 J K1 vk h2) with (envkv_weaken2 [] J K1 vk h2).
  erewrite H. 2: eapply envkv_weaken_eq_extend2. split; eauto.
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


(*
Fixpoint hask_subst T2: forall J' J T1 K1 K2,
    has_kind (mext J' (ext (bind_ty K1) J)) T2 K2 ->
    has_kind J T1 K1 ->
    has_kind (mext (msubst J' (length J) T1) J)
             (subst T2 (length J) (splice (length J) (length J') T1))
             (subst K2 (length J) (splice (length J) (length J') T1)).
Proof.
  destruct T2; intros J' J T1 K1 K2 HK HT1.
  - (* TStar *) simpl in *. inversion HK; subst. simpl. eapply k_star.
  - (* TBox *) inversion HK.
  - (* TBool *) simpl in *. inversion HK; subst. simpl. eapply k_bool.
  - (* TFun *) simpl in *. inversion HK; subst; simpl.
    + eapply k_fun. 
      eapply (hask_subst T2_1 J' J T1 K1 TStar H1 HT1).
      eapply (hask_subst T2_2 J' J T1 K1 TStar H3 HT1).
    + eapply k_karr.
      eapply (hask_subst T2_1 J' J T1 K1 TBox H1 HT1).
      eapply (hask_subst T2_2 J' J T1 K1 TBox H3 HT1).
  - (* TAll *) simpl in *. inversion HK; subst. simpl. eapply k_all. rewrite splice_acc.
    change (ext (bind_ty (subst T2_1 (length J) (splice (length J) (length J') T1)))
                (mext (msubst J' (length J) T1) J))
      with (mext (msubst (bind_ty T2_1 :: J') (length J) T1) J).
    eapply hask_subst with (J':=bind_ty T2_1::J') (K2:=TStar); eauto.
  - inversion HK.
  - inversion HK.
  - (* TVar *)
    inversion HK; subst.
    destruct (Nat.eq_dec i (length J)) as [Heq | Hneq].
    + (* i = n: substitute *)
      subst i.
      assert (HIX := indexr_mext_ext_hit J' J K1).
      cbv zeta in HIX.
      change (@indexr (prod bool tm)) with (@indexr binding) in H0.
      rewrite HIX in H0. inversion H0; subst.
      simpl.
      destruct (Nat.eq_dec (length J) (length J)); [| congruence].
      rewrite subst_splice_cancel.
      eapply haskind_extend_mult_msubst; eauto.
    + (* i <> n: shift *)
      simpl.
      destruct (Nat.eq_dec i (length J)); [congruence |].
      change (@indexr (prod bool tm)) with (@indexr binding) in H0.
      pose proof (indexr_mext_ext_subst J' J T1 K1 i K2 Hneq H0 HT1 HFC) as HIX.
      cbv zeta in HIX.
      eapply k_var. exact HIX.
  - inversion HK.
  - inversion HK.
  - (* TTApp *) simpl in *. inversion HK; subst. simpl.
    exact (k_tapp _ _ _ _ _ (hask_subst T2_1 J' J T1 K1 (TFun K0 K2) H1 HT1 HFC)
                            (hask_subst T2_2 J' J T1 K1 K0 H3 HT1 HFC)).
  - (* TTAbs *) simpl in *. inversion HK; subst. simpl.
    eapply k_tabs. rewrite splice_acc.

    change (ext (bind_ty (subst T2_1 (length J) (splice (length J) (length J') T1)))
                (mext (msubst J' (length J) T1) J))
      with (mext (msubst (bind_ty T2_1 :: J') (length J) T1) J).
    (* IH: subst K3 n (splice n (S m) T1). Goal: subst K3 n (splice n m T1).
       Both = K3 when fclosed K3 (length J). *)
    assert (HFC3: fclosed K3 (length J)). admit.
    pose proof (hask_subst T2_2 (bind_ty T2_1::J') J T1 K1 K3 H2 HT1 HFC) as IH.
    simpl length in IH.
    rewrite (subst_fclosed K3 (length J) (length J) (splice (length J) (S (length J')) T1) HFC3 (Nat.le_refl _)) in IH.
    rewrite (subst_fclosed K3 (length J) (length J) (splice (length J) (length J') T1) HFC3 (Nat.le_refl _)).
    exact IH.
Admitted.*)

Lemma hask_subst1: forall J T2 T1 K1,
    has_kind (ext (bind_ty K1) J) T2 TStar ->
    has_kind J T1 K1 ->
    has_kind J (subst T2 (length J) T1) TStar.
Proof. (*
  intros. eapply hask_subst with (J':=[]) in H0.
  simpl in H0. rewrite splice_zero in H0. eauto.
  simpl. eauto. eauto. *)
Admitted.

Lemma hask_subst1': forall J T2 T1 K1 K,
    has_kind (ext (bind_ty K1) J) T2 K ->
    has_kind J T1 K1 ->
    has_kind J (subst T2 (length J) T1) (subst K (length J) T1).
Proof. (*
  intros. apply hask_subst with (J':=[]) (T2:=T2) (K2:=K) in H0; auto.
  simpl in H0. rewrite splice_zero in H0; auto. *)
Admitted.


Lemma aux1b'': forall J' J K1 K T1K WFJ i e0 e1,
    i <> length J ->
    (envkv_weaken J' J K1 T1K WFJ) i K e0 = WFJ (if i <? length J then i else i - 1) K e1.
Proof.
  intros.
  bdestruct (i <? length J).
  erewrite envkv_weaken_lt. eauto. eauto.
  erewrite envkv_weaken_ge. eauto. lia. lia.
Qed.

(* TODO: valt_subst and all downstream LR lemmas need ext-based updating.
   Commented out to focus on syntactic hask_subst first. *)
(*
    T1K = val_type (haskind_extend_mult J' T1 J K1 HK1) WFJ ->
    val_type h1f (envkv_weaken J' J (bind_ty K1) T1K WFJ) =
    val_type (hask_subst T2 J' J T1 K1 K2 h1f HK1) WFJ.
Proof.
  intros T2. induction T2; intros; simpl in *.
  - (* TStar *) dependent destruction h1f. simpl. eauto.
  - (* TBox *) inversion h1f.
  - (* TBool *) dependent destruction h1f. simpl. eauto.
  - (* TFun *) dependent destruction h1f; simpl.
    + assert (H21: val_type h1f1 (envkv_weaken J' J (bind_ty K1) T1K WFJ) = val_type (hask_subst T2_1 J' J T1 K1 TStar h1f1 HK1) WFJ). apply IHT2_1. auto. rewrite H21.
      assert (H22: val_type h1f2 (envkv_weaken J' J (bind_ty K1) T1K WFJ) = val_type (hask_subst T2_2 J' J T1 K1 TStar h1f2 HK1) WFJ). apply IHT2_2. auto. rewrite H22. auto.
    + (* TKArr *) eauto.
  - (* TAll *) dependent destruction h1f. simpl.
    assert (HVT: forall VT1, val_type (haskind_extend_mult (bind_ty T2_1 :: J') T1 J K1 HK1) (envkv_cons (J' ++ J) (bind_ty T2_1) VT1 WFJ) = val_type (haskind_extend_mult J' T1 J K1 HK1) WFJ). { intros.
      simpl. elim_eq_rect. simpl. elim_eq_rect. simpl.
      rewrite <- valt_extend'. reflexivity.
    }
    assert (HV: forall VT1, val_type h1f (envkv_cons (J' ++ bind_ty K1 :: J) (bind_ty T2_1) VT1 (envkv_weaken J' J (bind_ty K1) T1K WFJ)) =
      val_type (eq_rec_r (fun t : tm => has_kind (bind_ty T2_1 :: J' ++ J) (subst T2_2 (length J) t) TStar) (hask_subst T2_2 (bind_ty T2_1 :: J') J T1 K1 TStar h1f HK1) (splice_acc T1 (length J) (length J') 1))
      (envkv_cons (J' ++ J) (bind_ty T2_1) VT1 WFJ)). { intros.
      rewrite splice_acc. rewrite aux2.
      specialize (IHT2_2 (bind_ty T2_1 :: J') J K1 TStar T1K (envkv_cons (J' ++ J) (bind_ty T2_1) VT1 WFJ) T1 h1f HK1).
      specialize (HVT VT1). rewrite <- HVT in H.
      specialize (IHT2_2 H). auto.
    }
    f_equal.
    apply functional_extensionality_dep. intro VT1.
    exact (HV VT1).
  - inversion h1f.
  - inversion h1f.
  - (* TVar *)
    dependent destruction h1f.
    remember (k_var (J' ++ bind_ty K1 :: J) i K e) as hx1.
    remember (hask_subst (TVar i) J' J T1 K1 K hx1 HK1) as hx1'.
    remember (envkv_weaken J' J (bind_ty K1) T1K WFJ) as h2'.
    dependent destruction hx1. simpl.
    simpl in *. remember (Nat.eq_dec i (length J)) as s.
    destruct s.
    + subst i.
      simpl in *.
      assert (HK1EQ': bind_ty K1 = bind_ty K). eapply xxx3; eauto.
      assert (HK1EQ: K1 = K). inversion HK1EQ'. reflexivity.
      subst K1.
      subst h2'.
      simpl. rewrite envkv_weaken_hit.
      subst T1K.
      f_equal. eapply hk_unique.
    + dependent destruction hx1'.
      simpl. subst h2'.
      match goal with
      | |- _ = WFJ _ _ ?pf =>
          replace pf with e1 by apply proof_irrelevance
      end.
      exact (aux1b'' J' J (bind_ty K1) (bind_ty K) T1K WFJ i e0 e1 n).
  - inversion h1f.
  - inversion h1f.
  - (* TTApp *) dependent destruction h1f. simpl.
    specialize (IHT2_2) with (h1f := h1f2). specialize (IHT2_2 T1K WFJ T1 HK1 H). rewrite IHT2_2.
    remember ((val_type (hask_subst T2_2 J' J T1 K1 K0 h1f2 HK1) WFJ)) as VT2.
    specialize (IHT2_1) with (h1f := h1f1). specialize (IHT2_1 T1K WFJ T1 HK1 H). rewrite IHT2_1. auto.
  - (* TTAbs *) dependent destruction h1f. remember (k_tabs (J' ++ bind_ty K1 :: J) T2_1 T2_2 K2 h1f) as h1f'.
    dependent destruction h1f'.
    replace h1f with h1f' in * by (eapply hk_unique).
    simpl. rewrite splice_acc.
    apply functional_extensionality. intro vk.
    rewrite aux2.
    assert (HT1K: val_type (haskind_extend_mult (bind_ty T2_1 :: J') T1 J K1 HK1) (envkv_cons (J' ++ J) (bind_ty T2_1) vk WFJ) = val_type (haskind_extend_mult J' T1 J K1 HK1) WFJ). { intros.
      simpl. elim_eq_rect. simpl. elim_eq_rect. simpl.
      rewrite <- valt_extend'. reflexivity.
    } rewrite <- HT1K in H.
    specialize (IHT2_2 (bind_ty T2_1 :: J')) with (h1f := h1f') (WFJ := (envkv_cons (J' ++ J) (bind_ty T2_1) vk WFJ)) (T1K := T1K). specialize (IHT2_2 T1 HK1 H).
    replace (val_type h1f' (envkv_weaken (bind_ty T2_1 :: J') J (bind_ty K1) T1K (envkv_cons (J' ++ J) (bind_ty T2_1) vk WFJ))) with (val_type (hask_subst T2_2 (bind_ty T2_1 :: J') J T1 K1 K2 h1f' HK1) (envkv_cons (J' ++ J) (bind_ty T2_1) vk WFJ)). (*using IHT2_2*)
    auto.
Qed.
*)

Lemma valt_subst1: forall T2 J K1 T1K WFJ T1 (h1f : has_kind (ext (bind_ty K1) J) T2 TStar) HK1 vy,
  T1K = val_type HK1 WFJ ->
  val_type h1f (envkv_cons2 J (bind_ty K1) T1K WFJ) vy =
  val_type (hask_subst1 J T2 T1 K1 h1f HK1) WFJ vy.
Proof. (*
  intros.
  specialize valt_subst with (J':=[]). simpl. intros. unfold hask_subst1.
  unfold eq_rect. remember (splice_zero T1 (length J)).
  clear Heqe.
  dependent destruction e.
  replace (envkv_cons J (bind_ty K1) T1K WFJ) with (envkv_weaken [] J (bind_ty K1) T1K WFJ).
  erewrite H0 with (T1:=T1) (HK1:=HK1). eauto. 2: eapply envkv_weaken_eq_extend.
  unfold eq_rec_r, eq_rec, eq_rect.
  remember (eq_sym (splice_zero T1 (length J))). clear Heqe. dependent destruction e.
  eauto. *)
Admitted.

(*
Lemma valt_subst1': forall T2 J K K1 T1K WFJ T1 (h1f : has_kind (ext (bind_ty K1) J) T2 K) HK1 ,
  T1K = val_type HK1 WFJ ->
  val_type h1f (envkv_cons2 J (bind_ty K1) T1K WFJ) =
  val_type (hask_subst1' J T2 T1 K1 K h1f HK1) WFJ .
Proof.
  intros.
  specialize valt_subst with (J':=[]). simpl. intros. unfold hask_subst1'.
  unfold eq_rect. remember (splice_zero T1 (length J)).
  clear Heqe.
  dependent destruction e.
  replace (envkv_cons J (bind_ty K1) T1K WFJ) with (envkv_weaken [] J (bind_ty K1) T1K WFJ).
  erewrite H0 with (T1:=T1) (HK1:=HK1). eauto. 2: eapply envkv_weaken_eq_extend.
  unfold eq_rec_r, eq_rec, eq_rect.
  remember (eq_sym (splice_zero T1 (length J))). clear Heqe. dependent destruction e.
  eauto.
Qed.
*)

(* ---------- env extension lemmas  ---------- *)


Lemma envt_empty: forall W,
    env_type [] [] W.
Proof.
  intros. split. eauto. intros. inversion H.
Qed.

Lemma envt_extend: forall E (G:tenv) h2 v1 T1 (h1: has_kind G T1 TStar) vk,
    env_type E G h2 ->
    val_type h1 h2 v1 ->
    env_type (v1::E) (ext (bind_tm T1) G) (envkv_cons2 G (bind_tm T1) vk h2).
Proof.
  intros.
  remember H as WFE. clear HeqWFE.
  destruct H as (?&?). split. rewrite ext_length. simpl. eauto.
  intros x T IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head_ext in IX. inversion IX. subst T.
    exists v1.
    exists (haskind_extend _ _ _ _ h1).
    split. rewrite <- H. rewrite indexr_head. eauto.
    eapply valt_extend in H0. eapply H0. 
  - rewrite indexr_skip_ext in IX; eauto.
    eapply indexr_map' in IX. destruct IX as (T' & IX & ?).
    destruct T'. simpl in H3. inversion H3. subst. 
    eapply WFE in IX as IX. destruct IX as (v2' & ? & ? & ?).
    exists v2'.
    exists (haskind_extend _ _ _ _ x0). split. 
    rewrite indexr_skip; eauto. lia.
    eapply valt_extend in H5. eapply H5.     
Qed.

Lemma envt_extendk: forall E G h2 K1 (vk: val_sort K1),
    env_type E G h2 ->
    env_type (vbool false::E) (ext (bind_ty K1) G) (envkv_cons2 G (bind_ty K1) vk h2).
Proof.
  intros.
  remember H as WFE. clear HeqWFE.
  destruct H as (?&?). split. rewrite ext_length. simpl. eauto. 
  intros x T IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head_ext in IX. inversion IX.
  - rewrite indexr_skip_ext in IX; eauto.
    eapply indexr_map' in IX. destruct IX as (T' & IX & ?).
    destruct T'. simpl in H2. inversion H2. subst. 
    eapply WFE in IX as IX. destruct IX as (v2' & ? & ? & ?).
    exists v2'.
    exists (haskind_extend _ _ _ _ x0). split. 
    rewrite indexr_skip; eauto. lia.
    eapply valt_extend in H4. eapply H4.
Qed.


(* ---------- equivalence ---------- *)

(*
Lemma has_kind_subst_inverse : forall T2 J J' T1 K1 K2,
    has_kind (J'++J) (subst T2 (length J) (splice (length J) (length J') T1)) K2 ->
    has_kind J T1 K1 ->
    has_kind (J' ++ K1 :: J) T2 K2.
Proof.
  induction T2; intros; simpl in H.
  - dependent destruction H. constructor.
  - inversion H.
  - dependent destruction H. constructor.
  - destruct (Nat.eq_dec i (length J)); subst.
      constructor. rewrite indexr_skips; auto. rewrite indexr_head.
      apply (haskind_extend_mult J') in H0. specialize (hk_unique' _ _ _ H0 _ H); intros. congruence.
    dependent destruction H. bdestruct (i <? (length J)). constructor.
      rewrite indexr_skips; auto. rewrite indexr_skips in e; auto. rewrite indexr_skip; auto. simpl; lia.
      constructor. replace i with (S (i - 1)). rewrite <- indexr_insert_ge. auto. lia. lia.
  - dependent destruction H.
    + constructor; auto. eapply IHT2_1; eauto. eapply IHT2_2; eauto.
    + constructor. eapply IHT2_1; eauto. eapply IHT2_2; eauto.
  - dependent destruction H. constructor; auto. specialize (IHT2_2 J (T2_1 :: J') T1 K1 TStar). apply IHT2_2; auto. simpl. rewrite splice_acc in H. auto.
  - inversion H.
  - inversion H.
  - inversion H. 
  - inversion H. 
  - inversion H. 
  - dependent destruction H. apply k_tapp with (K1 := K0). eapply IHT2_1; eauto. eapply IHT2_2; eauto.
  - dependent destruction H. constructor; auto. specialize (IHT2_2 J (T2_1 :: J') T1 K1 K2). apply IHT2_2; auto. simpl. rewrite splice_acc in H. auto.
Qed.

Lemma has_kind_subst1_inverse : forall J T1 T2 K1 K,
    has_kind J T1 K1 ->
    has_kind J (subst T2 (length J ) T1) K ->
    has_kind (K1 :: J) T2 K.
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
    dependent destruction H. dependent destruction H. apply hask_subst1' with (K1 := K0); auto.
    apply (k_tapp) with (K1:=K1); auto. constructor.
    eapply has_kind_subst1_inverse; eauto.
Qed.

Lemma eq_type_preserve_kind' : forall {J T1 T2 K},
  eq_type J T1 T2 ->
  has_kind J T1 K -> has_kind J T2 K.
Proof.
  intros. specialize (eq_type_preserve_kind _ _ _ K H). intros. destruct H1; auto.
Qed.
*)

(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_true: forall G,
    sem_type G ttrue TBool.
Proof.
  intros.
  intros E WFJ WFE.
  exists (vbool true).
  exists (k_bool G).
  split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto.
Qed.

Lemma sem_false: forall G,
    sem_type G tfalse TBool.
Proof.
  intros.
  intros E WFJ WFE.
  exists (vbool false).
  exists (k_bool G).
  split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto.
Qed.

Lemma sem_var: forall G x T,
    indexr x G = Some (bind_tm T) ->
    sem_type G (tvar x) T.
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

Lemma sem_abs: forall G t T1 T2,
    sem_type (ext (bind_tm T1) G) t (splice (length G) 1 T2) ->
    has_kind G T1 TStar ->
    has_kind G T2 TStar ->
    sem_type G (tabs t) (TFun T1 T2).
Proof.
  intros ? ? ? ? HY W1 W2. intros E WFJ WFE.
  eexists _.
  exists (k_fun _ _ _ W1 W2).
  split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros vx VX.
    edestruct HY as (vy & ? & ? & ?). eapply envt_extend; eauto.

    specialize (hk_unique _ _ _ (haskind_extend _ _ _ _ W2) x). intros. subst.
                                                 
    exists vy. split. eauto. eauto. eapply valt_extend. eauto.

    Unshelve.
    apply tt. 
Qed.

Lemma sem_app: forall G f t T1 T2,
    sem_type G f (TFun T1 T2) ->
    sem_type G t T1 ->
    sem_type G (tapp f t) T2.
Proof.
  intros ? ? ? ? ? HF HX. intros H WFJ WFE.
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

Lemma sem_tabs: forall G t K1 T2,
    sem_type (ext (bind_ty K1) G) t T2 ->
    has_kind (ext (bind_ty K1) G) T2 TStar ->
    sem_type G (ttabs K1 t) (TAll K1 T2).
Proof.
  intros ? ? ? ? HY W2. intros E WFJ WFE.
  eexists _.
  eexists (k_all _ _ _ W2).
  split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros VK1.
    edestruct HY as (vy & ? & ? & ?). eapply envt_extendk; eauto.
    specialize (hk_unique _ _ _ W2 x). intros. subst.
    exists vy. split. eauto. eauto.
Qed.


Lemma sem_tapp: forall G t K1 T1 T2,
    sem_type G t (TAll K1 T2) ->
    has_kind G T1 K1 ->
    sem_type G (ttapp t T1) (subst T2 (length G) T1).
Proof.
  intros ? ? ? ? ? HF HX. intros E WFJ WFE.
  destruct (HF E WFJ WFE) as (vf & h1f & STF & VF).
  dependent destruction h1f.
  destruct vf; simpl in VF; intuition.
  remember (val_type HX WFJ) as T1K.
  edestruct (VF T1K) as (vy & STY & VY).
  exists vy. (* TODO: subst *)
  exists (hask_subst1 _ _ _ _ h1f HX).
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
Proof. (*
  intros. generalize dependent K. induction H; intros.
  - apply val_type_irrel; auto.
  - specialize (IHeq_type WFJ _ h2 h1). destruct IHeq_type. split; auto.
  - specialize (eq_type_preserve_kind' H h1). intros. specialize (IHeq_type2 WFJ K H1 h2). specialize (IHeq_type1 WFJ K h1 H1). rewrite IHeq_type1. auto.
  - dependent destruction h1; dependent destruction h2; simpl. 2: eauto. f_equal.
    apply IHeq_type1.
    apply functional_extensionality. intros _. apply IHeq_type2.
  - dependent destruction h1. dependent destruction h2. simpl. f_equal.
    apply functional_extensionality. intros.
    specialize (IHeq_type (envkv_cons J K1 x WFJ) TStar h1 h2). auto.
  - dependent destruction h1. dependent destruction h2. simpl.
    apply functional_extensionality. intros.
    specialize (IHeq_type (envkv_cons J K1 x WFJ) K2 h1 h2). auto.
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
Qed.*)
Admitted.

Lemma sem_equiv: forall G t T1 T2,
    eq_type G T1 T2 ->
    has_kind G T2 TStar ->
    sem_type G t T1 ->
    sem_type G t T2.
Proof.
  intros ???? KX HK HX. intros H WFJ WFE.
  edestruct HX as (vx & h1 & A & VX). eauto.
  eexists vx.
  exists HK.
  split.
  - eauto.
  - erewrite <- val_type_equiv; eauto.
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
  - eapply sem_abs; eauto.
  - eapply sem_app; eauto.
  - eapply sem_tabs; eauto.
  - eapply sem_tapp; eauto.
  - eapply sem_equiv; eauto.
Qed.

Corollary safety: forall t T,
  has_type [] t T ->
  exp_type [] [] (envkv_nil) t T.
Proof.
  intros. eapply fundamental in H as ST; eauto.
  edestruct (ST []) as (v & ? & ? & ?). eapply envt_empty.
  exists v, x. intuition. eapply H1.
Qed.


End STLC.
