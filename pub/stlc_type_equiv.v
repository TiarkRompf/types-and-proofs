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

As a case study, we implement a non-standard
function application rule that uses type operators
"dom T" and "range T" to extract the domain and
range of the function's type.

The semantic interpretation of types, i.e., the
logical relation definin semantically well-typed
values and terms only needs to be defined for types
in formal form.

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
  | TFun   : ty -> ty -> ty
  | TDom   : ty -> ty
  | TRange : ty -> ty
.

Inductive ty_vl : Type :=
  | TVBool  : ty_vl
  | TVFun   : ty_vl -> ty_vl -> ty_vl
.


Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : tm -> tm
.

Inductive vl: Type :=
| vbool :  bool -> vl
| vabs  :  list vl -> tm -> vl 
.

Definition venv := list vl.
Definition tenv := list ty.

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.


(* ---------- type normalization rules ---------- *)

Inductive type_eval : ty -> ty_vl -> Prop :=
| teval_bool: 
    type_eval TBool TVBool
| teval_fun: forall T1 T2 V1 V2,
    (* NOTE: there is a choice whether to eval T1,T2
       here or in type_reify *)
    type_eval T1 V1 ->
    type_eval T2 V2 ->
    type_eval (TFun T1 T2) (TVFun V1 V2)
| teval_dom: forall TF V1 V2,
    type_eval TF (TVFun V1 V2) ->
    type_eval (TDom TF) V1
| teval_img: forall TF V1 V2,
    type_eval TF (TVFun V1 V2) ->
    type_eval (TRange TF) V2
.

Inductive type_reify : ty_vl -> ty -> Prop :=
| treify_bool: 
    type_reify TVBool TBool
| treify_fun: forall V1 V2 T1' T2',
    type_reify V1 T1' ->
    type_reify V2 T2' ->
    type_reify (TVFun V1 V2) (TFun T1' T2')
.

Definition type_normalize T T': Prop := 
  exists V, type_eval T V /\ type_reify V T'.

Definition type_equiv T1 T2: Prop :=
  exists T', type_normalize T1 T' /\ type_normalize T2 T'.

Definition type_wf T1: Prop := 
  exists T', type_normalize T1 T'.


(* ---------- syntactic term typing rules ---------- *)

Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
    has_type env ttrue TBool
| t_false: forall env,
    has_type env tfalse TBool
| t_var: forall x env T,
    indexr x env = Some T ->
    has_type env (tvar x) T
| t_app: forall env f t TF,
    has_type env f TF ->
    has_type env t (TDom TF) ->
    has_type env (tapp f t) (TRange TF)
| t_abs: forall env t T1 T2,
    has_type (T1::env) t T2 ->
    type_wf T1 ->
    has_type env (tabs t) (TFun T1 T2)
| t_equiv: forall env t T1 T2,
    has_type env t T1 ->
    type_equiv T1 T2 ->
    has_type env t T2
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

Example ex1: has_type [] (tapp (tabs (tvar 0)) ttrue) TBool.
Proof.
  econstructor. econstructor. econstructor. econstructor.
  simpl. eauto.
  2: econstructor. 2: econstructor.
  2: { eexists. split. eauto. eexists. eauto. }
  eexists. eauto.
  eexists. split. eexists. eauto. eauto.
Qed.


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
        | tapp ef ex   =>
          match teval n env ef with
            | None => None
            | Some None => Some None
            | Some (Some (vbool _)) => Some None
            | Some (Some (vabs env2 ey)) =>
              match teval n env ex with
                | None => None
                | Some None => Some None
                | Some (Some vx) =>
                  teval n (vx::env2) ey
              end
          end
      end
  end.

Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).


(* ---------- LR definitions  ---------- *)

Fixpoint val_type v T {struct T}: Prop :=
  match v, T with
  | vbool b, TBool =>  
      True
  | vabs H ty, TFun T1 T2 =>
      forall vx,
        val_type vx T1 ->
        exists vy,
          tevaln (vx::H) ty vy /\
          val_type vy T2
  | _,_ =>
      False
  end.

Definition exp_type H t T :=
  exists v T',
    tevaln H t v /\
    type_normalize T T' /\
    val_type v T'.

Definition env_wf (G: tenv) :=
    forall x T,
      indexr x G = Some T ->
      type_wf T.

Definition env_type (H: venv) (G: tenv) :=
  length H = length G /\
  forall x T,
    indexr x G = Some T ->
    exists v T',
      indexr x H = Some v /\
      type_normalize T T' /\
      val_type v T'.

Definition sem_type G t T :=
  env_wf G ->
  type_wf T /\
  forall H,
    env_type H G ->
    exp_type H t T.


(* ---------- properties of type normalization and equivalence ---------- *)

Lemma type_eval_unique: forall T V1,
    type_eval T V1 ->
    forall V2, type_eval T V2 ->
    V1 = V2.
Proof.
  intros T V1 H. induction H; intros.
  - inversion H. eauto.
  - inversion H1. subst. erewrite IHtype_eval1, IHtype_eval2; eauto.
  - inversion H0. subst.
    assert (TVFun V1 V2 = TVFun V0 V4). erewrite IHtype_eval; eauto.
    inversion H1. eauto. 
  - inversion H0. subst.
    assert (TVFun V1 V2 = TVFun V3 V0). erewrite IHtype_eval; eauto.
    inversion H1. eauto. 
Qed.

Lemma type_reify_unique: forall T V1,
    type_reify T V1 ->
    forall V2, type_reify T V2 ->
    V1 = V2.
Proof.
  intros T V1 H. induction H; intros.
  - inversion H. eauto.
  - inversion H1. subst. erewrite IHtype_reify1, IHtype_reify2; eauto. 
Qed.

Lemma type_normalize_unique: forall T V1,
    type_normalize T V1 ->
    forall V2, type_normalize T V2 ->
    V1 = V2.
Proof.
  intros.
  destruct H as (?&?&?).
  destruct H0 as (?&?&?).
  assert (x = x0). eapply type_eval_unique; eauto. 
  subst. eapply type_reify_unique; eauto. 
Qed.

Lemma type_equiv_refl: forall T,
    type_wf T ->
    type_equiv T T.
Proof.
  intros. destruct H. eexists. split; eauto.
Qed.

Lemma type_equiv_trans: forall T1 T2 T3,
    type_equiv T1 T2 ->
    type_equiv T2 T3 ->
    type_equiv T1 T3.
Proof.
  intros.
  destruct H as (?&?&?).
  destruct H0 as (?&?&?).
  assert (x = x0). eapply type_normalize_unique; eauto.
  subst. eexists. split; eauto.
Qed.



(* ---------- LR helper lemmas  ---------- *)

Lemma envw_empty:
    env_wf [].
Proof.
  intros ???. inversion H. 
Qed.

Lemma envw_extend: forall G T1,
    env_wf G ->
    type_wf T1 ->
    env_wf (T1::G).
Proof. 
  intros.  intros x T IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX.
    subst. eauto. 
  - rewrite indexr_skip in IX; eauto.
Qed.


Lemma envt_empty:
    env_type [] [].
Proof.
  intros. split. eauto. intros. inversion H. 
Qed.

Lemma envt_extend: forall E G v1 T1 T1',
    env_type E G ->
    type_normalize T1 T1' ->
    val_type v1 T1' ->
    env_type (v1::E) (T1::G).
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

Lemma sem_true: forall G,
    sem_type G ttrue TBool.
Proof.
  intros. intros WFG. split. eexists. eauto. 
  intros E WFE. exists (vbool true), TBool. split. 2: split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
  - simpl. eauto.
Qed.

Lemma sem_false: forall G,
    sem_type G tfalse TBool.
Proof.
  intros. intros WFG. split. eexists. eauto. 
  intros E WFE. exists (vbool false), TBool. split. 2: split. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
  - simpl. eauto.
Qed.

Lemma sem_var: forall G x T,
    indexr x G = Some T ->
    sem_type G (tvar x) T.
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

Lemma sem_app: forall G f t TF,
    sem_type G f TF ->
    sem_type G t (TDom TF) ->
    sem_type G (tapp f t) (TRange TF).
Proof.
  intros ? ? ? ? HF HX. intros WFG. 
  specialize (HF WFG) as (WF & HF).
  specialize (HX WFG) as (WX & HX).
  assert (type_wf (TRange TF)) as WY. {
    clear HF HX.
    destruct WX as (TX' & VX & NX1 & NX2).
    destruct WF as (TF' & VF & NF1 & NF2).
    inversion NX1. subst.
    assert (VF = TVFun VX V2). eapply type_eval_unique; eauto. subst.
    inversion NF2. subst. 
    eexists _,_. split. econstructor; eauto. eauto.
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
Qed.

Lemma sem_abs: forall G t T1 T2,
    sem_type (T1::G) t T2 ->
    type_wf T1 ->
    sem_type G (tabs t) (TFun T1 T2).
Proof.
  intros ? ? ? ? HY W1. intros WFG.  
  destruct HY as (W2 & HY). eapply envw_extend; eauto.
  destruct W1 as (T1' & V1 & N1E & N1R).
  destruct W2 as (T2' & V2 & N2E & N2R).
  assert (type_normalize (TFun T1 T2) (TFun T1' T2')). {
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

Lemma sem_equiv: forall G t T1 T2,
    sem_type G t T1 ->
    type_equiv T1 T2 ->
    sem_type G t T2.
Proof.
  intros. intros WFG.
  destruct H as (W1 & H). eauto. 
  destruct H0 as (T' & N1 & N2).
  split. eexists. eauto. intros E WFE.
  edestruct H as (v & T1'' & ? & ? & ?). eauto.
  assert (T1'' = T'). eapply type_normalize_unique; eauto.
  subst. eexists _,_. split. 2: split.
  - eauto.
  - eauto.
  - eauto. 
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
  - eapply sem_app; eauto. 
  - eapply sem_abs; eauto.
  - eapply sem_equiv; eauto.
Qed.

Corollary safety: forall t T,
  has_type [] t T ->
  exp_type [] t T.
Proof. 
  intros. eapply fundamental in H as ST; eauto.
  destruct ST as (? & ST). eapply envw_empty. 
  destruct (ST []) as (v & T' & ? & ?). eapply envt_empty.
  exists v, T'. intuition.
Qed.

End STLC.
