(* Full safety for STLC *)

(*

An LR-based normalization and semantic soundness proof for STLC.

Normalization by evaluation, based on standard cbv semantics.

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
| vsym  :  tm -> vl
.

Definition venv := list vl.
Definition tenv := list ty.

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.


(* ---------- syntactic typing rules ---------- *)

Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
    has_type env ttrue TBool
| t_false: forall env,
    has_type env tfalse TBool
| t_var: forall x env T,
    indexr x env = Some T ->
    has_type env (tvar x) T
| t_app: forall env f t T1 T2,
    has_type env f (TFun T1 T2) ->
    has_type env t T1 ->
    has_type env (tapp f t) T2
| t_abs: forall env t T1 T2,
    has_type (T1::env) t T2 ->
    has_type env (tabs t) (TFun T1 T2)
.


Inductive normal : tm -> Prop :=
| nf_true:
    normal ttrue
| nf_false:
    normal tfalse
| nf_var: forall x,
    normal (tvar x)
| nf_app: forall f t,
    normal f ->
    normal t ->
    (forall t', f <> tabs t') ->
    normal (tapp f t)
| nf_abs: forall t,
    normal t ->
    normal (tabs t)
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
      | tapp ef ex   =>
          match teval n env ef with
          | None => None
          | Some None => Some None
          | Some (Some (vbool _)) => Some None
          | Some (Some (vsym tf)) =>
              match teval n env ex with
              | None => None
              | Some None => Some None
              | Some (Some vx) =>
                  match treify n vx with
                  | None => None
                  | Some None => Some None
                  | Some (Some tx) =>
                      Some (Some (vsym (tapp tf tx)))
                  end
              end
          | Some (Some (vabs env2 ey)) =>
              match teval n env ex with
              | None => None
              | Some None => Some None
              | Some (Some vx) =>
                  teval n (vx::env2) ey
              end
          end
      end
  end
with treify n v: option (option tm) :=
  match n with
  | 0 => None
  | S n =>         
      match v with
      | vbool true => Some (Some ttrue)
      | vbool false => Some (Some tfalse)
      | vsym t => Some (Some t)
      | vabs env2 ey =>
          match teval n ((vsym (tvar (length env2)))::env2) ey with
          | None => None
          | Some None => Some None
          | Some (Some v) =>
              match treify n v with
              | None => None
              | Some None => Some None
              | Some (Some t) => Some (Some (tabs t))
              end
          end
      end
  end.

Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).

Definition treifyn v e := exists nm, forall n, n > nm -> treify n v = Some (Some e).

Definition tnormn env e e' := exists v, tevaln env e v /\ treifyn v e'.


Example ex1 := (tapp (tabs (tvar 0)) tfalse).

Example ex2 := (tabs ex1).

Eval cbv in (teval 10 [] ex2).

Example ex3 := (vabs [] (tapp (tabs (tvar 0)) tfalse)).

Eval cbv in (treify 10 ex3).



(* ---------- LR definitions  ---------- *)

Fixpoint val_type v T : Prop :=
  match v, T with
  | vbool b, TBool =>  
      True
  | vabs H ty, TFun T1 T2 =>
      forall vx tx',
        val_type vx T1 ->
        treifyn vx tx' ->
        normal tx' ->
        exists vy ty',
          tevaln (vx::H) ty vy /\
          val_type vy T2 /\
          treifyn vy ty' /\
          normal ty'
  | vsym t, _ =>
      normal t /\ (forall t', t <> tabs t')
  | _,_ =>
      False
  end.


Definition exp_type H t T :=
  exists v t',
    tevaln H t v /\
    val_type v T /\
    treifyn v t' /\
    normal t'.

Definition env_type (H: venv) (G: tenv) :=
  length H = length G /\
    forall x T,
      indexr x G = Some T ->
      exists v t',
        indexr x H = Some v /\
        val_type v T /\
        treifyn v t' /\
        normal t'.

Definition sem_type G t T :=
  forall H,
    env_type H G ->
    exp_type H t T.


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: core.

#[export] Hint Constructors has_type: core.
#[export] Hint Constructors normal: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.




(* ---------- LR helper lemmas  ---------- *)

Lemma envt_empty:
    env_type [] [].
Proof.
  intros. split. eauto. intros. inversion H. 
Qed.

Lemma envt_extend: forall E G v1 t1 T1,
    env_type E G ->
    val_type v1 T1 ->
    treifyn v1 t1 ->
    normal t1 ->
    env_type (v1::E) (T1::G).
Proof.
  intros. 
  remember H as WFE. clear HeqWFE.
  destruct H. split. simpl. eauto.
  intros x T IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX. subst T1.
    exists v1, t1. rewrite <- H. rewrite indexr_head. eauto.
  - rewrite indexr_skip in IX; eauto.
    eapply WFE in IX as IX. destruct IX as (v2 & t2 & ? & ? & ? & ?).
    exists v2, t2. rewrite indexr_skip; eauto. lia.
Qed.


(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_true: forall G,
    sem_type G ttrue TBool.
Proof.
  intros. intros E WFE. 
  exists (vbool true), ttrue. split. 2: split. 3: split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto. 
Qed.

Lemma sem_false: forall G,
    sem_type G tfalse TBool.
Proof.
  intros. intros E WFE. 
  exists (vbool false), tfalse. split. 2: split. 3: split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
Qed.

Lemma sem_var: forall G x T,
    indexr x G = Some T ->
    sem_type G (tvar x) T.
Proof.
  intros. intros E WFE.
  eapply WFE in H as IX. destruct IX as (v & t & IX & VX & TX & HTX).
  exists v, t. split. 2: split. 3: split.
  - exists 0. intros. destruct n. lia. simpl. rewrite IX. eauto.
  - eauto.
  - eauto.
  - eauto.
Qed.

Lemma sem_app: forall G f t T1 T2,
    sem_type G f (TFun T1 T2) ->
    sem_type G t T1 ->
    sem_type G (tapp f t) T2.
Proof.
  intros ? ? ? ? ? HF HX. intros E WFE.
  destruct (HF E WFE) as (vf & tf' & STF & VF & TF & HTF).
  destruct (HX E WFE) as (vx & tx' & STX & VX & TX & HTX).
  destruct vf; simpl in VF; intuition. {
    edestruct VF as (vy & ty' & STY & VY & TY & HTY). eauto. eauto. eauto.
    exists vy, ty'. split. 2: split. 3: split. 
    - destruct STF as (n1 & STF).
      destruct STX as (n2 & STX).
      destruct STY as (n3 & STY).
      exists (1+n1+n2+n3). intros. destruct n. lia.
      simpl. rewrite STF, STX, STY. 2,3,4: lia.
      eauto.
    - eauto.
    - eauto.
    - eauto.
  } {
    eexists _,_. split. 2: split. 3: split.
    - destruct STF as (n1 & STF).
      destruct STX as (n2 & STX).
      destruct TX as (n3 & TX).
      exists (1+n1+n2+n3). intros. destruct n. lia.
      simpl. rewrite STF, STX, TX. 2,3,4: lia.
      eauto.
    -  destruct T2; simpl; intuition; inversion H1. 
    - exists 0. intros. destruct n. lia.
      simpl. eauto.
    - eauto. 
  }
Qed.

Lemma sem_abs: forall G t T1 T2,
    sem_type (T1::G) t T2 ->
    sem_type G (tabs t) (TFun T1 T2).
Proof.
  intros ? ? ? ? HY. intros E WFE.
  assert (length E = length G) as L. eapply WFE.
  edestruct HY as (v & t' & STY & VY & TY & HTY). {
    eapply envt_extend with (v1:=vsym (tvar (length E))).
    eauto. destruct T1; simpl; intuition; inversion H. 
    exists 0. intros. destruct n. lia. simpl. eauto.
    eauto. 
  }
  exists (vabs E t), (tabs t'). split. 2: split. 3: split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros. eapply HY. eapply envt_extend; eauto.
  - destruct STY as (n1 & STY).
    destruct TY as (n2 & TY).
    exists (1+n1+n2). intros. destruct n. lia.
    simpl. rewrite STY, TY. 2,3: lia.
    eauto.
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
Qed.

Corollary safety: forall t T,
  has_type [] t T ->
  exp_type [] t T.
Proof. 
  intros. eapply fundamental in H as ST; eauto.
  destruct (ST []) as (v & t' & ? & ? & ?).
  eapply envt_empty.
  exists v, t'. intuition.
Qed.

Corollary normalization: forall t T,
  has_type [] t T ->
  exists t',
    tnormn [] t t' /\ normal t'.
Proof. 
  intros. eapply fundamental in H as ST; eauto.
  destruct (ST []) as (v & t' & ? & ? & ? & ?).
  eapply envt_empty.
  exists t'. split. exists v. intuition. eauto.
Qed.

End STLC.
