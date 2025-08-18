(* Full safety for STLC *)

(*

An LR-based termination and semantic soundness proof for STLC.

Canonical big-step cbv semantics.

In this file, we explore a type system that includes
a form of type equivalence, expressed through type
normalization.

Two types are equivalent if they normalize to the
same normal form. A type is well-formed if it
has a normal form.

Type normalization is implemented as normalization
by evaluation ("evaluate" a type, then reify back).

The semantic interpretation of types, i.e., the
logical relation defining semantically well-typed
values and terms only needs to be defined for types
in formal form.

The type syntax includes type operators, i.e., 
abstraction and application with a kinding system. 
The language corresponds to TAPL, Chapter 29.
Terms can depend on terms (regular lambda and
application), and types can depend on types.

Compared to Fw, this version is still missing a form 
for terms to depend on types. This requires a 
generalization of the LR definition for terms, with a 
result domain that depends on the kind.

(Like Fw and in contrast to CC, there is also no form 
for types to depend on terms).

Like in file "stlc_type_equiv.v", we also implement 
a non-standard function application rule that uses type 
operators "dom T" and "range T" to extract the domain 
and range of the function's type.

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
  | TAll   : ty -> ty
  | TTAbs  : ty -> ty
  | TTApp  : ty -> ty -> ty
  | TDom   : ty -> ty
  | TRange : ty -> ty
  | TTImg  : ty -> ty -> ty
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

Inductive ty_vl : Type :=
  | TVBool : ty_vl
  | TVFun  : ty_vl -> ty_vl -> ty_vl
  | TVAbs  : list ty_vl -> ty -> ty_vl
  | TVSym  : ty -> ty_vl
.


Definition venv := list vl.
Definition tenv := list ty.
Definition tvenv := list ty_vl.
Definition kenv := list kn.

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.
#[global] Hint Unfold tvenv.
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


(* ---------- type normalization rules ---------- *)

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

Definition vt_all (TF: tpe -> tpe): tpe :=
  fun v =>
    match v with
    | vtabs H ty =>
        forall T1,
          exists vy,
            tevaln H ty vy /\
            (TF T1) vy
    | _ => False
    end.

(*
Fixpoint val_type T {struct T}: tpe :=
  match T with
  | TVBool => vt_bool
  | TVFun T1 T2 => vt_fun (val_type T1) (val_type T2)
  | TVAll GV T2 => vt_all (fun T1 => )
  | _ => vt_none
  end.
*)

Inductive type_eval : tvenv -> ty -> ty_vl -> Prop :=
| teval_bool: forall env,
    type_eval env TBool TVBool
| teval_tvar: forall env x VX,
    indexr x env = Some VX ->
    type_eval env (TVar x) VX
| teval_fun: forall env T1 T2 V1 V2,
    type_eval env T1 V1 ->
    type_eval env T2 V2 ->
    type_eval env (TFun T1 T2) (TVFun V1 V2)
| teval_tabs: forall env T2,
    type_eval env (TTAbs T2) (TVAbs env T2)

| teval_dom: forall env TF V1 V2,
    type_eval env TF (TVFun V1 V2) ->
    type_eval env (TDom TF) V1
| teval_range: forall env TF V1 V2,
    type_eval env TF (TVFun V1 V2) ->
    type_eval env (TRange TF) V2
| teval_ttapp: forall env G TF T1 T2 V1 V2,
    type_eval env TF (TVAbs G T2) ->
    type_eval env T1 V1 ->
    type_eval (V1 :: G) T2 V2 ->
    type_eval env (TTApp TF T1) V2
              
| teval_dom_sym: forall env TF TF',
    type_eval env TF (TVSym TF') ->
    type_eval env (TDom TF) (TVSym (TDom TF'))
| teval_range_sym: forall env TF TF',
    type_eval env TF (TVSym TF') ->
    type_eval env (TRange TF) (TVSym (TRange TF'))
| teval_ttapp_sym: forall env TF T1 V1 TF' T1',
    type_eval env TF (TVSym TF') ->
    type_eval env T1 V1 ->
    type_reify V1 T1' ->
    type_eval env (TTApp TF T1) (TVSym (TTApp TF' T1'))

with type_reify : ty_vl -> ty -> Prop :=
| treify_bool: 
    type_reify TVBool TBool
| treify_fun: forall V1 V2 T1' T2',
    type_reify V1 T1' ->
    type_reify V2 T2' ->
    type_reify (TVFun V1 V2) (TFun T1' T2')
| treify_tabs: forall G T2 V2 T2',
    type_eval (TVSym (TVar (length G)) ::G) T2 V2 ->
    type_reify V2 T2' ->
    type_reify (TVAbs G T2) (TTAbs T2')
| treify_sym: forall T,
    type_reify (TVSym T) T
.

Definition type_normalize env T T': Prop := 
  exists V, type_eval env T V /\ type_reify V T'.

Definition type_equiv env T1 T2: Prop :=
  exists T', type_normalize env T1 T' /\ type_normalize env T2 T'.

Definition type_wf env T1: Prop := 
  exists T', type_normalize env T1 T'.


(* ---------- syntactic term typing rules ---------- *)

Inductive has_kind : kenv -> ty -> kn -> Prop :=
| k_bool: forall J,
    has_kind J TBool KTpe
| k_var: forall J x K,
    indexr x J = Some K ->
    has_kind J (TVar x) K
| k_fun: forall J T1 T2,
    has_kind J T1 KTpe ->
    has_kind J T2 KTpe ->
    has_kind J (TFun T1 T2) KTpe
| k_tabs: forall J T2 K1 K2,
    has_kind (K1::J) T2 K2 ->
    has_kind J (TTAbs T2) (KArr K1 K2)
| k_tapp: forall J TF TX K1 K2,
    has_kind J TF (KArr K1 K2) ->
    has_kind J TX K1 ->
    has_kind J (TTApp TF TX) K2
.


Inductive has_type : tenv -> kenv -> tm -> ty -> Prop :=
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
    type_wf [] T1 ->
    has_type G J (tabs t) (TFun T1 T2)
| t_app: forall G J f t TF,
    has_type G J f TF ->
    has_type G J t (TDom TF) ->
    has_type G J (tapp f t) (TRange TF)

(*             
| t_tabs: forall G J t T2,
    has_type G J t T2 ->
    has_type G J (ttabs t) (TAll T2)
| t_tapp: forall G V f TF T1,
    has_type G V f TF ->
    has_kind T1 K1 ->
    has_type G V (ttapp f) (TTImg TF T1)
*)

| t_equiv: forall G J V t T1 T2,
    has_type G V t T1 ->
    type_equiv [] T1 T2 ->
    has_kind J T2 KTpe ->
    has_type G V t T2
.

#[export] Hint Constructors ty: core.
#[export] Hint Constructors ty_vl: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: core.

#[export] Hint Constructors type_eval: core.
#[export] Hint Constructors type_reify: core.
#[export] Hint Unfold type_normalize: core.

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



(* ---------- LR definitions for types : kinds  ---------- *)

Fixpoint type_kind T K {struct K}: Prop :=
  match T, K with
  | TVBool, KTpe =>  
      True
  | TVFun T1 T2, KTpe =>
      True
  | TVAbs H TE2, KArr K1 K2 =>
      forall T1 T1',
        type_kind T1 K1 ->
        type_reify T1 T1' ->
        exists T2 T2',
          type_eval (T1::H) TE2 T2 /\
          type_kind T2 K2 /\
          type_reify T2 T2'  
  | TVSym T, _ =>
      True
  | _,_ =>
      False
  end.

Definition exp_kind H t T :=
  exists v t',
    type_eval H t v /\
    type_kind v T /\
    type_reify v t'.  

Definition env_kind (H: tvenv) (G: kenv) :=
  length H = length G /\
    forall x T,
      indexr x G = Some T ->
      exists v t',
        indexr x H = Some v /\
        type_kind v T /\
        type_reify v t'.

Definition sem_kind G t T :=
  forall H,
    env_kind H G ->
    exp_kind H t T.

Lemma envk_empty:
    env_kind [] [].
Proof.
  intros. split. eauto. intros. inversion H. 
Qed.

Lemma envk_extend: forall E G v1 t1 T1,
    env_kind E G ->
    type_kind v1 T1 ->
    type_reify v1 t1 ->
    env_kind (v1::E) (T1::G).
Proof.
  intros. 
  remember H as WFE. clear HeqWFE.
  destruct H. split. simpl. eauto.
  intros x T IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX. subst T1.
    exists v1, t1. rewrite <- H. rewrite indexr_head. eauto.
  - rewrite indexr_skip in IX; eauto.
    eapply WFE in IX as IX. destruct IX as (v2 & t2 & ? & ?).
    exists v2, t2. rewrite indexr_skip; eauto. lia.
Qed.


Lemma sem_bool: forall G,
    sem_kind G TBool KTpe.
Proof.
  intros. intros E WFE. 
  exists TVBool, TBool. split. 2: split. 
  - eauto. 
  - simpl. eauto.
  - eauto.
Qed.

Lemma sem_tvar: forall J x K,
    indexr x J = Some K ->
    sem_kind J (TVar x) K.
Proof.
  intros. intros E WFE.
  eapply WFE in H as IX. destruct IX as (v & t & IX & VX & TX).
  exists v, t. split. 2: split. 
  - eauto. 
  - eauto.
  - eauto.
Qed.

Lemma sem_fun: forall G T1 T2,
    sem_kind G T1 KTpe ->
    sem_kind G T2 KTpe ->
    sem_kind G (TFun T1 T2) KTpe.
Proof.
  intros ? ? ? H1 H2. intros E WFE.
  edestruct H1 as (v1 & t1' & ? & ? & ?). eauto. 
  edestruct H2 as (v2 & t2' & ? & ? & ?). eauto. 
  exists (TVFun v1 v2) , (TFun t1' t2'). split. 2: split. 
  - eauto. 
  - simpl. eauto.
  - eauto.
Qed.

Lemma sem_tabs: forall G T2 K1 K2 ,
    sem_kind (K1::G) T2 K2 ->
    sem_kind G (TTAbs T2) (KArr K1 K2).
Proof.
  intros ? ? ? ? HY. intros E WFE.
  assert (length E = length G) as L. eapply WFE.
  edestruct HY as (v & t' & STY & VY & TY). {
    eapply envk_extend with (v1:=TVSym (TVar (length E))).
    eauto. destruct K1; simpl; intuition; inversion H. 
    eauto. 
  }
  exists (TVAbs E T2), (TTAbs t'). split. 2: split. 
  - eauto.
  - simpl. intros. eapply HY. eapply envk_extend; eauto. 
  - eauto. 
Qed.

Lemma sem_tapp: forall G TF T1 K1 K2,
    sem_kind G TF (KArr K1 K2) ->
    sem_kind G T1 K1 ->
    sem_kind G (TTApp TF T1) K2.
Proof.
  intros ? ? ? ? ? HF HX. intros E WFE.
  destruct (HF E WFE) as (vf & tf' & STF & VF & TRF).
  destruct (HX E WFE) as (vx & tx' & STX & VX & TRX).
  destruct vf; simpl in VF; intuition. {
    edestruct VF as (vy & ty' & STY & VY & RTY). eauto. eauto. 
    exists vy, ty'. split. 2: split. 
    - eauto. 
    - eauto.
    - eauto.
  } {
    eexists _,_. split. 2: split. 
    - eauto. 
    - destruct K2; eauto.
    - eauto. 
  }
Qed.

Theorem has_kind_fundamental: forall J T K,
    has_kind J T K ->
    sem_kind J T K.
Proof.
  intros ? ? ? W. 
  induction W.
  - eapply sem_bool; eauto.
  - eapply sem_tvar; eauto.
  - eapply sem_fun; eauto.
  - eapply sem_tabs; eauto. 
  - eapply sem_tapp; eauto.
Qed.



(* ---------- LR definitions for values : types  ---------- *)

Fixpoint val_type v T {struct T}: Prop :=
  match v, T with
  | vbool b, TBool =>  
      True
  | vabs H ty, TFun T1' T2' =>
      forall vx,
        val_type vx T1' ->
        exists vy,
          tevaln (vx::H) ty vy /\
          val_type vy T2'
  | _,_ =>
      False
  end.

Definition exp_type H V t T :=
  exists v T',
    tevaln H t v /\
    type_normalize V T T' /\
    val_type v T'.

Definition env_wf (G: tenv) (V: tvenv) :=
    forall x T,
      indexr x G = Some T ->
      type_wf V T.

Definition env_type (H: venv) (G: tenv) (V: tvenv) :=
  length H = length G /\
  forall x T,
    indexr x G = Some T ->
    exists v T',
      indexr x H = Some v /\
      type_normalize V T T' /\
      val_type v T'.

Definition sem_type G V t T :=
  env_wf G V ->
  type_wf V T /\
  forall H,
    env_type H G V ->
    exp_type H V t T.


(* ---------- properties of type normalization and equivalence ---------- *)

Lemma type_reify_unique': forall T V1,
    type_reify T V1 ->
    forall V2, type_reify T V2 ->
    V1 = V2.
Proof.
Admitted. (* TODO: mutual induction *)

Lemma type_eval_unique: forall GV T V1,
    type_eval GV T V1 ->
    forall V2, type_eval GV T V2 ->
    V1 = V2.
Proof. 
  intros G T V1 H. induction H; intros.
  - inversion H. eauto.
  - inversion H0. congruence.
  - inversion H1. subst. erewrite IHtype_eval1, IHtype_eval2; eauto.
  - inversion H. subst. eauto. 
  - inversion H0; subst.
    + assert (TVFun V1 V2 = TVFun V0 V4). erewrite IHtype_eval; eauto.
      inversion H1. eauto.
    + assert (TVFun V1 V2 = (TVSym TF')). erewrite IHtype_eval; eauto.
      inversion H1. 
  - inversion H0; subst.
    + assert (TVFun V1 V2 = TVFun V3 V0). erewrite IHtype_eval; eauto.
      inversion H1. eauto.
    + assert (TVFun V1 V2 = (TVSym TF')). erewrite IHtype_eval; eauto.
      inversion H1. 
  - inversion H2; subst.
    + eapply IHtype_eval1 in H5. inversion H5. subst.
      eapply IHtype_eval2 in H7. subst.
      eapply IHtype_eval3 in H9. eauto.
    + eapply IHtype_eval1 in H5. inversion H5. 
  - inversion H0; subst.
    + eapply IHtype_eval in H3. inversion H3.
    + eapply IHtype_eval in H3. congruence.
  - inversion H0; subst.
    + eapply IHtype_eval in H3. inversion H3.
    + eapply IHtype_eval in H3. congruence.
  - inversion H2; subst.
    + eapply IHtype_eval1 in H5. inversion H5.
    + eapply IHtype_eval1 in H5. inversion H5. subst.
      eapply IHtype_eval2 in H7. subst.
      assert (T1' = T1'0). eapply type_reify_unique'; eauto. 
      subst. eauto.
Qed.
    
Lemma type_reify_unique: forall T V1,
    type_reify T V1 ->
    forall V2, type_reify T V2 ->
    V1 = V2.
Proof. 
  intros T V1 H. induction H; intros.
  - inversion H. eauto.
  - inversion H1. subst.
    eapply IHtype_reify1 in H4. subst.
    eapply IHtype_reify2 in H6. subst. eauto.
  - inversion H1. subst.
    assert (V1 = V2). eapply type_eval_unique; eauto. subst. 
    eapply IHtype_reify in H6. subst. eauto.
  - inversion H. eauto. 
Qed.

Lemma type_normalize_unique: forall GV T V1,
    type_normalize GV T V1 ->
    forall V2, type_normalize GV T V2 ->
    V1 = V2.
Proof. 
  intros.
  destruct H as (?&?&?).
  destruct H0 as (?&?&?).
  assert (x = x0). eapply type_eval_unique; eauto. 
  subst. eapply type_reify_unique; eauto. 
Qed.

Lemma type_equiv_refl: forall GV T,
    type_wf GV T ->
    type_equiv GV T T.
Proof.
  intros. destruct H. eexists. split; eauto.
Qed.

Lemma type_equiv_trans: forall GV T1 T2 T3,
    type_equiv GV T1 T2 ->
    type_equiv GV T2 T3 ->
    type_equiv GV T1 T3.
Proof.
  intros.
  destruct H as (?&?&?).
  destruct H0 as (?&?&?).
  assert (x = x0). eapply type_normalize_unique; eauto.
  subst. eexists. split; eauto.
Qed.



(* ---------- LR helper lemmas  ---------- *)

Lemma envw_empty:
    env_wf [] [].
Proof.
  intros ???. inversion H. 
Qed.

Lemma envw_extend: forall G V T1,
    env_wf G V ->
    type_wf V T1 ->
    env_wf (T1::G) V.
Proof. 
  intros.  intros x T IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX.
    subst. eauto. 
  - rewrite indexr_skip in IX; eauto.
Qed.


Lemma envt_empty:
    env_type [] [] [].
Proof.
  intros. split. eauto. intros. inversion H. 
Qed.

Lemma envt_extend: forall E G V v1 T1 T1',
    env_type E G V ->
    type_normalize V T1 T1' ->
    val_type v1 T1' ->
    env_type (v1::E) (T1::G) V.
Proof. 
  intros. 
  remember H as WFE. clear HeqWFE.
  destruct H. split. simpl. eauto.
  intros x T IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX. subst T1.
    exists v1, T1'. rewrite <- H. rewrite indexr_head. eauto.
  - rewrite indexr_skip in IX; eauto.
    eapply WFE in IX as IX. destruct IX as (v2 & ? & ?).
    exists v2. rewrite indexr_skip; eauto. lia.
Qed.


(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_true: forall G V,
    sem_type G V ttrue TBool.
Proof.
  intros. intros WFG. split. eexists. eauto. 
  intros E WFE. exists (vbool true), TBool. split. 2: split. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
  - simpl. eauto.
Qed.

Lemma sem_false: forall G V,
    sem_type G V tfalse TBool.
Proof.
  intros. intros WFG. split. eexists. eauto. 
  intros E WFE. exists (vbool false), TBool. split. 2: split. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
  - simpl. eauto.
Qed.

Lemma sem_var: forall G V x T,
    indexr x G = Some T ->
    sem_type G V (tvar x) T.
Proof.
  intros. intros WFG. split. eapply WFG. eauto. 
  intros E WFE.
  eapply WFE in H as IX. destruct IX as (v & T' & IX & NX & VX).
  exists v, T'. split. 2: split. 
  - exists 0. intros. destruct n. lia. simpl. rewrite IX. eauto.
  - eauto. 
  - eauto. 
Qed.

(*
sem_app, traditional form:

Lemma sem_app: forall G f t T1 T2,
    sem_type G f (TTFun T1 T2) ->
    sem_type G t T1 ->
    sem_type G (tapp f t) T2.
Proof.
  intros ? ? ? ? ? HF HX. intros E WFE.
  destruct (HF E WFE) as (vf & STF & VF).
  destruct (HX E WFE) as (vx & STX & VX).
  destruct vf; simpl in VF; intuition.
  edestruct VF as (vy & STY & VY). eauto. 
  exists vy. split.
  - destruct STF as (n1 & STF).
    destruct STX as (n2 & STX).
    destruct STY as (n3 & STY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite STF, STX, STY. 2,3,4: lia.
    eauto.
  - eauto.
Qed.

*)

Lemma sem_app: forall G V f t TF,
    sem_type G V f TF ->
    sem_type G V t (TDom TF) ->
    sem_type G V (tapp f t) (TRange TF).
Proof.
  intros ? ? ? ? ? HF HX. intros WFG. 
  specialize (HF WFG) as (WF & HF).
  specialize (HX WFG) as (WX & HX).
  assert (type_wf V (TRange TF)) as WY. {
    clear HF HX.
    destruct WX as (TX' & VX & NX1 & NX2).
    destruct WF as (TF' & VF & NF1 & NF2).
    inversion NX1.
    - subst.
      assert (VF = TVFun VX V2). eapply type_eval_unique; eauto. subst.
      inversion NF2. subst. 
      eexists _,_. split. econstructor; eauto. eauto.
    - subst. 
      eexists. eexists. split. eauto. eauto. 
  }
  split. eauto. intros E WFE.
  destruct (HF E WFE) as (vf & TF' & STF & NF & VF).
  destruct (HX E WFE) as (vx & TX' & STX & NX & VX).
  destruct NF as (NF' & NF1 & NF2).
  destruct NX as (NX' & NX1 & NX2).
  inversion NX1. subst.
  assert (NF' = TVFun NX' V2). eapply type_eval_unique; eauto. subst.
  destruct vf, TF'; simpl in VF; intuition.
  - inversion NF2. 
  - inversion NF2. subst.
    assert (TF'1 = TX'). eapply type_reify_unique; eauto. subst.
    edestruct VF as (vy & STY & VY). eauto. 
    exists vy. exists TF'2. split. 2: split. 
    + destruct STF as (n1 & STF).
      destruct STX as (n2 & STX).
      destruct STY as (n3 & STY).
      exists (1+n1+n2+n3). intros. destruct n. lia.
      simpl. rewrite STF, STX, STY. 2,3,4: lia.
      eauto.
    + econstructor. split. eauto. eauto.
    + eauto. 
  - subst. 
    assert (NF' = TVSym TF'0). eapply type_eval_unique; eauto. subst.
    inversion NX2. subst. destruct vx; simpl in VX; contradiction.
Qed.

Lemma sem_abs: forall G V t T1 T2,
    sem_type (T1::G) V t T2 ->
    type_wf V T1 ->
    sem_type G V (tabs t) (TFun T1 T2).
Proof.
  intros ? ? ? ? ? HY W1. intros WFG.
  destruct HY as (W2 & HY). eapply envw_extend; eauto.
  destruct W1 as (T1' & V1 & N1E & N1R).
  destruct W2 as (T2' & V2 & N2E & N2R). 
  assert (type_normalize V (TFun T1 T2) (TFun T1' T2')). {
    eexists. split; eauto.
  }
  split. eexists. eauto. intros E WFE.
  assert (length E = length G) as L. eapply WFE.
  exists (vabs E t). exists (TFun T1' T2'). split. 2: split. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto. 
  - simpl. intros.
    edestruct HY as (vy & TY' & ? & ? & ?). eapply envt_extend; eauto.
    assert (TY' = T2'). eapply type_normalize_unique; eauto.
    subst. exists vy. eauto. 
Qed.

Lemma sem_equiv: forall G V t T1 T2,
    sem_type G V t T1 ->
    type_equiv V T1 T2 ->
    sem_type G V t T2.
Proof.
  intros. intros WFG.
  destruct H as (W1 & H). eauto. 
  destruct H0 as (T' & N1 & N2).
  split. eexists. eauto. intros E WFE.
  edestruct H as (v & T1' & ? & ? & ?). eauto.
  assert (T1' = T'). eapply type_normalize_unique; eauto. 
  subst. eexists _,_. split. 2: split.
  - eauto.
  - eauto.
  - eauto. 
Qed.

                                                       
(* ---------- LR fundamental property  ---------- *)

Theorem fundamental: forall G J t T,
    has_type G J t T ->
    sem_type G [] t T.
Proof.
  intros ? ? ? ? W. 
  induction W.
  - eapply sem_true; eauto.
  - eapply sem_false; eauto.
  - eapply sem_var; eauto.
  - eapply sem_abs; eauto.
  - eapply sem_app; eauto. 
  - eapply sem_equiv; eauto.
Qed.

Corollary safety: forall t T,
  has_type [] [] t T ->
  exp_type [] [] t T.
Proof. 
  intros. eapply fundamental in H as ST; eauto.
  destruct ST as (? & ST). eapply envw_empty. 
  destruct (ST []) as (v & T' & ? & ?). eapply envt_empty.
  exists v, T'. intuition.
Qed.

End STLC.
