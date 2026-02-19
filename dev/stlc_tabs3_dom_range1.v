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
  | TBool  : ty
  | TVar   : id -> ty
  | TFun   : ty -> ty -> ty
  | TAll   : ty -> ty
  | TDom   : ty -> ty
  | TRange : ty -> ty
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
Definition kenv := list (unit). (* could just be a nat *)

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.
#[global] Hint Unfold kenv.


(* ---------- locally nameless ---------- *)

Fixpoint closed T n :=
  match T with
  | TBool => True
  | TVar x => x < n
  | TFun T3 T4 => closed T3 n /\ closed T4 n
  | TAll T4 => closed T4 (S n)
  | TDom T4 => closed T4 n
  | TRange T4 => closed T4 n
  end.

Fixpoint splice n l (T : ty) {struct T} : ty :=
  match T with
  | TBool => TBool
  | TVar x => TVar (if x <? n then x else l+x)
  | TFun T3 T4 => TFun (splice n l T3) (splice n l T4)
  | TAll T2   => TAll (splice n l T2)
  | TDom T2 => TDom (splice n l T2)
  | TRange T2 => TRange (splice n l T2)
  end.

Fixpoint subst T1 n T2 {struct T1} : ty :=
  match T1 with
  | TBool => TBool
  | TVar x => if x =? n then T2 else if x <? n then TVar x else TVar (x-1)
  | TFun T3 T4 => TFun (subst T3 n T2) (subst T4 n T2)
  | TAll T4 => TAll (subst T4 n (splice n 1 T2))
  | TDom T4 => TDom (subst T4 n T2)
  | TRange T4 => TRange (subst T4 n T2)
  end.


(* ---------- syntactic typing rules ---------- *)

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
    has_type env J f (TAll T2) ->
    closed T1 (length J) ->
    has_type env J (ttapp f T1) (subst T2 (length J) T1)
| t_tabs: forall env J t T2,
    has_type (map (splice (length J) 1) env) (tt::J) t T2 ->
    has_type env J (ttabs t) (TAll T2)
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
| sl_root: sel
| sl_dom: sel -> sel
| sl_range: sel -> sel
.

Definition vtype := vl -> sel -> Prop.

Fixpoint val_type (V: list vtype) v T i {struct T}: Prop :=
  match v, T, i with
  | vbool b, TBool, sl_root =>  
      True
  | v, TVar x, i =>
      exists vt, 
      indexr x V = Some vt /\ vt v i
  | vabs H ty, TFun T1 T2, sl_root =>
      forall vx,
        val_type V vx T1 sl_root ->
        exists vy,
          tevaln (vx::H) ty vy /\
          val_type V vy T2 sl_root
  | vtabs H ty, TAll T2, sl_root =>
      forall vt,
        exists vy,
          tevaln H ty vy /\
          val_type (vt::V) vy T2 sl_root
  | v, TDom TF, i =>
     val_type V v TF (sl_dom i) /\
       forall vf, val_type V vf TF i ->
                      exists H ty vy, vf = vabs H ty /\
          tevaln (v::H) ty vy /\
          val_type V vy TF (sl_range i)
  | v, TRange TF, i =>
      val_type V v TF (sl_range i)
  | v, TFun T1 T2, sl_dom k =>
      val_type V v T1 k
  | v, TFun T1 T2, sl_range k =>
      val_type V v T2 k
  | _,_,_ =>
      False
  end.

Definition exp_type H V t T :=
  exists v,
    tevaln H t v /\
    val_type V v T sl_root.

Definition env_type (H: venv) (G: tenv) (V: list vtype) (J: kenv) :=
  length H = length G /\
  length V = length J /\
    forall x T,
      indexr x G = Some T ->
      exists v,
        indexr x H = Some v /\
        val_type V v T sl_root.

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
  - intuition. eapply IHT1 in H. eauto. lia. 
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
  - eapply IHT2. eapply closedt_splice. eauto. eauto. lia.
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
  + specialize (IHe1 a b c).
    rewrite IHe1. auto.
  + specialize (IHe1 a b c).
    rewrite IHe1. eauto.
  + specialize (IHe1 a b c).
    rewrite IHe1. eauto. 
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
  + specialize (IHe1 a b c).
    rewrite IHe1. auto.
  + specialize (IHe1 a b c).
    rewrite IHe1. auto.
  + specialize (IHe1 a b c).
    rewrite IHe1. auto.
Qed.

Lemma splice_zero: forall e1 a,
  (splice a 0 e1) = e1.
Proof. intros. induction e1; simpl; intuition.
  + bdestruct (i <? a); intuition.
  + rewrite IHe1_1. rewrite IHe1_2. auto.
  + rewrite IHe1. auto.
  + rewrite IHe1. auto.
  + rewrite IHe1. auto.
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
    destruct v; eapply IHT1; eauto.
    destruct v; eapply IHT2; eauto. 
  - destruct v,k; simpl in *; split; intros; eauto.
    + destruct (H vt0) as (vy & ? & VY). 
      exists vy. split. eauto. eapply IHT with (V1:=vt0::V1); eauto. 
    + destruct (H vt0) as (vy & ? & VY). 
      exists vy. split. eauto. eapply IHT with (V1:=vt0::V1); eauto. 
  - split; destruct v.
    + intros. simpl in *. destruct H. split. eapply IHT; eauto.
      intros. eapply IHT in H1; eauto. destruct (H0 _ H1) as (?&?&?&?&?&?).
      eexists _,_,_. split. eauto. split. eauto. eapply IHT; eauto. 
    + intros. simpl in *. destruct H. split. eapply IHT; eauto.
      intros. eapply IHT in H1; eauto. destruct (H0 _ H1) as (?&?&?&?&?&?).
      eexists _,_,_. split. eauto. split. eauto. eapply IHT; eauto. 
    + intros. simpl in *. destruct H. split. eapply IHT; eauto.
      intros. eapply IHT in H1; eauto. destruct (H0 _ H1) as (?&?&?&?&?&?).
      eexists _,_,_. split. eauto. split. eauto. eapply IHT; eauto. 
    + intros. simpl in *. destruct H. split. eapply IHT; eauto.
      intros. eapply IHT in H1; eauto. destruct (H0 _ H1) as (?&?&?&?&?&?).
      eexists _,_,_. split. eauto. split. eauto. eapply IHT; eauto. 
    + intros. simpl in *. destruct H. split. eapply IHT; eauto.
      intros. eapply IHT in H1; eauto. destruct (H0 _ H1) as (?&?&?&?&?&?).
      eexists _,_,_. split. eauto. split. eauto. eapply IHT; eauto. 
    + intros. simpl in *. destruct H. split. eapply IHT; eauto.
      intros. eapply IHT in H1; eauto. destruct (H0 _ H1) as (?&?&?&?&?&?).
      eexists _,_,_. split. eauto. split. eauto. eapply IHT; eauto. 
  - destruct v; simpl in *; eapply IHT; eauto. 
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
    + destruct v; eapply IHT2_1; eauto.
    + destruct v; eapply IHT2_2; eauto.
  - destruct k. destruct v; simpl in *; split; intros; eauto.
    + destruct (H0 vt0) as (vy & ? & VY).
      exists vy. split. eauto. edestruct IHT2 with (V1:=vt0::V1); eauto.
      clear H3. eapply H2 in VY. clear H2. simpl in VY.
      rewrite splice_acc. eauto.
    + destruct (H0 vt0) as (vy & ? & VY).
      exists vy. split. eauto. edestruct IHT2 with (V1:=vt0::V1); eauto.
      rewrite splice_acc in VY. 
      clear H2. eapply H3 in VY. simpl in VY.
      eauto.
    + destruct v; simpl; intuition.
    + destruct v; simpl; intuition.
  - split; destruct v.
    + intros. simpl in *. destruct H0. split. eapply IHT2; eauto.
      intros. eapply IHT2 in H2; eauto. destruct (H1 _ H2) as (?&?&?&?&?&?).
      eexists _,_,_. split. eauto. split. eauto. eapply IHT2; eauto. 
    + intros. simpl in *. destruct H0. split. eapply IHT2; eauto.
      intros. eapply IHT2 in H2; eauto. destruct (H1 _ H2) as (?&?&?&?&?&?).
      eexists _,_,_. split. eauto. split. eauto. eapply IHT2; eauto. 
    + intros. simpl in *. destruct H0. split. eapply IHT2; eauto.
      intros. eapply IHT2 in H2; eauto. destruct (H1 _ H2) as (?&?&?&?&?&?).
      eexists _,_,_. split. eauto. split. eauto. eapply IHT2; eauto. 
    + intros. simpl in *. destruct H0. split. eapply IHT2; eauto.
      intros. eapply IHT2 in H2; eauto. destruct (H1 _ H2) as (?&?&?&?&?&?).
      eexists _,_,_. split. eauto. split. eauto. eapply IHT2; eauto. 
    + intros. simpl in *. destruct H0. split. eapply IHT2; eauto.
      intros. eapply IHT2 in H2; eauto. destruct (H1 _ H2) as (?&?&?&?&?&?).
      eexists _,_,_. split. eauto. split. eauto. eapply IHT2; eauto. 
    + intros. simpl in *. destruct H0. split. eapply IHT2; eauto.
      intros. eapply IHT2 in H2; eauto. destruct (H1 _ H2) as (?&?&?&?&?&?).
      eexists _,_,_. split. eauto. split. eauto. eapply IHT2; eauto. 
  - destruct v; simpl in *; eapply IHT2; eauto. 
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


(* ---------- LR helper lemmas  ---------- *)

Lemma envt_empty:
    env_type [] [] [] [].
Proof.
  intros. split. 2: split.
  eauto. eauto. intros. inversion H. 
Qed.

Lemma envt_extend: forall E G V J v1 T1,
    env_type E G V J ->
    val_type V v1 T1 sl_root ->
    env_type (v1::E) (T1::G) V J.
Proof.
  intros. 
  remember H as WFE. clear HeqWFE.
  destruct H as (? & ? & ?). split. 2: split.
  simpl. eauto. simpl. eauto. 
  intros x T IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX. subst T1.
    exists v1. split. rewrite <- H. rewrite indexr_head. eauto.
    eauto.
  - rewrite indexr_skip in IX; eauto.
    eapply WFE in IX as IX. destruct IX as (v2 & ? & ?).
    exists v2. split. rewrite indexr_skip; eauto. lia.
    eauto.
Qed.

Lemma envt_extend_tabs: forall E G V J vt1,
    env_type E G V J ->
    env_type E (map (splice (length V) 1) G) (vt1::V) (tt::J).
Proof.
  intros. 
  remember H as WFE. clear HeqWFE.
  destruct H as (? & ? & ?). split. 2: split.
  rewrite map_length. eauto. simpl. eauto. 
  intros x T IX.
  eapply indexr_map' in IX. destruct IX as (T' & IX & ?). 
  eapply WFE in IX as IX. destruct IX as (v2 & ? & ?).
  exists v2. split. eauto. subst T. 
  eapply valt_extend in H4. eauto. 
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

Lemma sem_app_dom_range: forall G J f t TF,
    sem_type G J f TF ->
    sem_type G J t (TDom TF) ->
    sem_type G J (tapp f t) (TRange TF).
Proof.
  intros ? ? ? ? ? HF HX. intros E V WFE.
  destruct (HF E V WFE) as (vf & STF & VF).
  destruct (HX E V WFE) as (vx & STX & VX).

  destruct vx; simpl in VX. { (* XXX duplication! *)
  destruct VX as (VX & VFF).
  destruct (VFF vf VF) as (H & ty & vy & EVY & STY & VY).
  subst vf. 
  
  exists vy. split. 
  - destruct STF as (n1 & STF).
    destruct STX as (n2 & STX).
    destruct STY as (n3 & STY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite STF, STX, STY. 2,3,4: lia.
    eauto.
  - simpl. destruct vy; eauto. } {
  destruct VX as (VX & VFF).
  destruct (VFF vf VF) as (H & ty & vy & EVY & STY & VY).
  subst vf. 
  
  exists vy. split. 
  - destruct STF as (n1 & STF).
    destruct STX as (n2 & STX).
    destruct STY as (n3 & STY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite STF, STX, STY. 2,3,4: lia.
    eauto.
  - simpl. destruct vy; eauto. } {
  destruct VX as (VX & VFF).
  destruct (VFF vf VF) as (H & ty & vy & EVY & STY & VY).
  subst vf. 
  
  exists vy. split. 
  - destruct STF as (n1 & STF).
    destruct STX as (n2 & STX).
    destruct STY as (n3 & STY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite STF, STX, STY. 2,3,4: lia.
    eauto.
  - simpl. destruct vy; eauto. }
Qed.

Lemma sem_stp_dom: forall G J t T1 T2,
    sem_type G J t T1 ->
    sem_type G J t (TDom (TFun T1 T2)).
Proof.
  intros ? ? ? ? ? HX. intros E V WFE.
  destruct (HX E V WFE) as (vx & STX & VX).
  exists vx. split. eauto.
  destruct vx. {
  split. eapply VX. intros.
  destruct vf; simpl in H; try contradiction.
  destruct (H _ VX) as (vy & ? & ?).
  eexists l, t0, vy. split. eauto. split. eauto.
  simpl. destruct vy; eauto.
  } {
  split. eapply VX. intros.
  destruct vf; simpl in H; try contradiction.
  destruct (H _ VX) as (vy & ? & ?).
  eexists l0, t1, vy. split. eauto. split. eauto.
  simpl. destruct vy; eauto.
  } {
  split. eapply VX. intros.
  destruct vf; simpl in H; try contradiction.
  destruct (H _ VX) as (vy & ? & ?).
  eexists l0, t1, vy. split. eauto. split. eauto.
  simpl. destruct vy; eauto.
  }
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
    sem_type G J f (TAll T2) ->
    sem_type G J (ttapp f T1) (subst T2 (length J) T1).
Proof. 
  intros ? ? ? ? ? HF. intros E V WFE.
  assert (length E = length G) as L. eapply WFE.
  assert (length V = length J) as LV. eapply WFE.
  destruct (HF E V WFE) as (vf & STF & VF).
  destruct vf; simpl in VF; try contradiction.
  edestruct VF as (vy & STY & VY). 
  exists vy. split.
  - destruct STF as (n1 & STF).
    destruct STY as (n3 & STY).
    exists (1+n1+n3). intros. destruct n. lia.
    simpl. rewrite STF, STY. 2,3: lia.
    eauto.
  - rewrite <- LV. eapply valt_subst. reflexivity. eauto. 
Qed.


Lemma sem_tabs: forall G J t T2,
    sem_type (map (splice (length J) 1) G) (tt::J) t T2 ->
    sem_type G J (ttabs t) (TAll T2).
Proof.
  intros ? ? ? ? HY. intros E V WFE.
  assert (length E = length G) as L. eapply WFE.
  assert (length V = length J) as LV. eapply WFE.
  exists (vtabs E t). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros. 
    destruct (HY E (vt::V)) as (? & ? & ?).
    rewrite <-LV. eapply envt_extend_tabs; eauto.
    eexists. split. eauto. eauto. 
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
  - eapply sem_app_dom_range; eauto.
  - eapply sem_stp_dom; eauto.
  - eapply sem_stp_range; eauto.
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
  - eapply closedt_subst. eauto. eauto. eauto. 
  - eapply IHhas_type. intros. eapply indexr_map' in H1.
    destruct H1 as (?&?&?). subst.
    eapply closedt_splice. eauto. 
  - eapply IHhas_type. eauto. 
Qed.



(* ---------- examples  ---------- *)

(* polymorphic id function: [T:*](x:T) -> T  *)

Definition polyId := ttabs (tabs (tvar 0)). 

Definition polyIdType := TAll (TFun (TVar 0) (TVar 0)). 

Lemma polyIdHasType:
  has_type [] [] polyId polyIdType.
Proof.
  eapply t_tabs. eapply t_abs. eapply t_var.
  simpl. eauto. simpl. eauto. 
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

Definition etaFunType := TAll etaFunType'.

Lemma etaHasType:
  has_type [] [] etaFun etaFunType.
Proof.
  eapply t_tabs. eapply t_abs. eapply t_abs.
  eapply t_app_dom_range. eapply t_var. simpl. eauto. eapply t_var. simpl. eauto. 
  simpl. eauto. simpl. eauto. 
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
