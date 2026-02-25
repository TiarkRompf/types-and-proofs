(* Full safety for STLC *)

(*

An LR-based semantic soundness proof for STLC.

Big-step cbv semantics.

Step-indexed LR: soundness only, no termination.

Binary logical relation, contextual equivalence.

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

(* ---------- operational semantics ---------- *)

(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
*)

(* this step-indexed version returns the number of steps taken (always <= fuel) *)

Fixpoint teval(n: nat)(env: venv)(t: tm){struct n}: (nat * option (option vl)) :=
  match n with
    | 0 => (0,None)
    | S n =>
      match t with
        | ttrue                                => (1, Some (Some (vbool true)))
        | tfalse                               => (1, Some (Some (vbool false)))
        | tvar x                               => (1, Some (indexr x env))
        | tabs y                               => (1, Some (Some (vabs env y)))
        | tapp ef ex                           =>
          match teval n env ef with
            | (df, None)                       => (1+df, None)
            | (df, Some None)                  => (1+df, Some None)
            | (df, Some (Some (vbool _)))      => (1+df, Some None)
            | (df, Some (Some (vabs env2 ey))) =>
              match teval (n-df) env ex with
                | (dx, None)                   => (1+df+dx, None)
                | (dx, Some None)              => (1+df+dx, Some None)
                | (dx, Some (Some vx))         =>  
                    match teval (n-df-dx) (vx::env2) ey with 
                        | (dy, res)            => (1+ df+dx+dy, res)
                    end
              end
          end
      end
end.

Lemma eval_deterministic: forall m n, n < m -> forall H t n1 r j,
  teval n H t = (n1, Some r) -> j >= n -> (* alt: j >= n1 ? *)
  teval j H t = (n1, Some r).
Proof.
  intros m. induction m. intros. inversion H.
  intros. destruct n. inversion H1. destruct j. inversion H2.
  destruct t; simpl; simpl in H1; try eauto.
  remember (teval n H0 t1) as tf. destruct tf as [nf [rf|]].
  rewrite IHm with (n:=n) (n1:=nf) (r:=rf).
  destruct rf; try destruct v; try solve [inversion H1; eauto]. 
  remember (teval (n-nf) H0 t2) as tx. destruct tx as [nx [rx|]].
  rewrite IHm with (n:=n-nf) (n1:=nx) (r:=rx).
  destruct rx; try solve [destruct v; inversion H1; eauto].
  remember (teval (n-nf-nx) (v :: l) t) as ty. destruct ty as [ny [ry|]].
  rewrite IHm with (n:=n-nf-nx) (n1:=ny) (r:=ry).

  eauto. lia. eauto. lia.
  inversion H1. inversion H1.
  eauto. lia. eauto. lia.
  inversion H1.
  lia. eauto. lia.
  inversion H1.
Qed.

Lemma eval_bounded: forall m n, n < m -> forall H t n1 r,
    teval n H t = (n1, Some r) ->
    1 <= n1 /\ n1 <= n.
Proof.
  intros m. induction m. intros. inversion H.
  intros. destruct n. inversion H1.
  destruct t; simpl in *; inversion H1; try lia.
  remember (teval n H0 t1) as tf. destruct tf as [nf [rf|]]. 2: { inversion H1. }
  symmetry in Heqtf. eapply IHm with (n:=n) (n1:=nf) (r:=rf) in Heqtf as HF1. 2: lia.
  destruct rf. 2: { inversion H1. lia. } destruct v. inversion H1. lia.
  remember (teval (n-nf) H0 t2) as tx. destruct tx as [nx [rx|]]. 2: inversion H1.
  symmetry in Heqtx. eapply IHm in Heqtx as HX1. 2: lia.
  destruct rx. 2: { inversion H1. lia. } 
  remember (teval (n-nf-nx) (v :: l) t) as ty. destruct ty as [ny [ry|]].
  symmetry in Heqty. eapply IHm in Heqty as HY1. 2: lia. 2: inversion H1. 
  inversion H1. lia. 
Qed.


(* ---------- LR definitions  ---------- *)

Fixpoint val_type n v1 v2 T {struct n}: Prop :=
  match n with
  | 0 => True
  | S n =>
      match v1, v2, T with
      | vbool b1, vbool v2, TBool =>  
          True
      | vabs H1 ty1, vabs H2 ty2, TFun T1 T2 =>  
          forall nx vx1 vx2, 
            val_type (n-nx) vx1 vx2 T1 ->
            forall ny1 ry1,
              teval (n-nx) (vx1::H1) ty1 = (ny1, (Some ry1)) ->
              exists ny2 ry2, teval ny2 (vx2::H2) ty2 = (ny2, (Some ry2)) /\
              exists vy1 vy2,
                ry1 = Some vy1 /\
                ry2 = Some vy2 /\
                val_type (n-nx-ny1) vy1 vy2 T2
      | _,_,_ =>
          False
      end
  end.


Definition exp_type n H1 H2 t1 t2 T :=
  forall n1 r1,
    teval n H1 t1 = (n1, Some r1) ->
    exists n2 r2, teval n2 H2 t2 = (n2, Some r2) /\
    exists v1 v2,
      r1 = Some v1 /\
      r2 = Some v2 /\
      val_type (n-n1) v1 v2 T.

Definition env_type n (H1 H2: venv) (G: tenv) :=
  length H1 = length G /\
  length H2 = length G /\
    forall T x,
      indexr x G = Some T ->
      exists v1 v2,
        indexr x H1 = Some v1 /\
        indexr x H2 = Some v2 /\
        val_type n v1 v2 T.

Definition sem_type G t1 t2 T :=
  forall n H1 H2,
    env_type n H1 H2 G ->
    exp_type n H1 H2 t1 t2 T.


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: core.

#[export] Hint Constructors has_type: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.




(* ---------- LR helper lemmas  ---------- *)

Lemma envt_empty: forall n,
    env_type n [] [] [].
Proof.
  intros. split. 2: split.
  eauto. eauto. intros. inversion H. 
Qed.

Lemma envt_extend: forall n E1 E2 G v1 v2 T1,
    env_type n E1 E2 G ->
    val_type n v1 v2 T1 ->
    env_type n (v1::E1) (v2::E2) (T1::G).
Proof.
  intros. 
  remember H as WFE. clear HeqWFE.
  destruct H as (L1 & L2 & ?). split. 2: split.
  simpl. eauto. simpl. eauto. 
  intros T x IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX. subst T1.
    exists v1, v2. split. 2: split.
    rewrite <- L1. rewrite indexr_head. eauto.
    rewrite <- L2. rewrite indexr_head. eauto.
    eauto.
  - rewrite indexr_skip in IX; eauto.
    eapply WFE in IX as IX. destruct IX as (v1' & v2' & ? & ? & ?).
    exists v1', v2'. split. 2: split.
    rewrite indexr_skip; eauto. lia.
    rewrite indexr_skip; eauto. lia.
    eauto.
Qed.


Lemma valt_dec: forall m n, n < m -> forall n1 v1 v2 T1,
    val_type n v1 v2 T1 -> n1 <= n ->
    val_type n1 v1 v2 T1.
Proof.
  intros m. induction m. lia. intros. destruct n; destruct n1. eauto. lia. simpl. eauto. 
  destruct v1, v2, T1; simpl in H0; try contradiction.
  - simpl. eauto.
  - simpl. intros.
    edestruct H0 with (nx:=n-n1+nx) as (?&?&?&?&?&?&?&?). eapply IHm. 2: eauto. lia. lia.
    eapply eval_deterministic. 2: eauto. eauto. lia.
    eexists _,_. split. 
    eapply eval_deterministic. 2: eauto. eauto. lia. 
    eexists _,_. split. 2: split. eauto. eauto.
    eapply IHm. 2: eapply H7. lia. lia. 
Qed.

Lemma envt_dec: forall n n1 H1 H2 G,
    env_type n H1 H2 G -> n1 <= n ->
    env_type n1 H1 H2 G.
Proof.
  intros. destruct H as (?&?&?). split. 2: split.
  eauto. eauto.
  intros. eapply H4 in H5. destruct H5 as (?&?&?&?&?).
  eexists _,_. split. 2: split.
  eauto. eauto. eapply valt_dec; eauto. 
Qed.


(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_true: forall G,
    sem_type G ttrue ttrue TBool.
Proof.
  intros. intros n H1 H2 WFE. intros ? ? TE1.
  destruct n; inversion TE1.
  eexists 1,_. split. simpl. eauto. 
  exists (vbool true), (vbool true). split. 2: split.
  - eauto.
  - eauto.
  - destruct n; simpl; eauto.
Qed.

Lemma sem_false: forall G,
    sem_type G tfalse tfalse TBool.
Proof.
  intros. intros n H1 H2 WFE. intros ? ? TE1.
  destruct n; inversion TE1.
  eexists 1, _. split. simpl. eauto. 
  exists (vbool false), (vbool false). split. 2: split. 
  - eauto.
  - eauto.
  - destruct n; simpl; eauto.
Qed.

Lemma sem_var: forall G x T,
    indexr x G = Some T ->
    sem_type G (tvar x) (tvar x) T.
Proof.
  intros. intros n H1 H2 WFE. intros ? ? TE1.
  eapply WFE in H as IX. destruct IX as (v1 & v2 & IX1 & IX2 & VX).
  destruct n; inversion TE1.
  eexists 1,_. split. simpl. eauto. 
  exists v1, v2. split. 2: split. 
  - eauto.
  - eauto.
  - eapply valt_dec. eauto. eauto. lia.
Qed.

Lemma sem_app: forall G f1 f2 t1 t2 T1 T2,
    sem_type G f1 f2 (TFun T1 T2) ->
    sem_type G t1 t2 T1 ->
    sem_type G (tapp f1 t1) (tapp f2 t2) T2.
Proof.
  intros ? ? ? ? ? ? ? HF HX. intros n H1 H2 WFE. intros n1 r1 TE1.
  destruct n. { simpl in TE1. inversion TE1. } simpl in TE1.

  (* eexists _,_. simpl. *)
  
  (* function evaluates *)
  remember (teval n H1 f1) as tf1. symmetry in Heqtf1. destruct tf1 as [nf1 [rf1|]]. 2: inversion TE1.
  edestruct (HF (S n) H1 H2) as (nf2 & rf2 & TF2 & (vf1 & vf2 & RF1 & RF2 & VF)). eapply envt_dec; eauto. eauto.
  eapply eval_deterministic. eauto. eauto. lia.
  eapply eval_bounded in Heqtf1 as BF1; eauto.
  remember (S n - nf1) as nf'. destruct nf'. lia.
  subst rf1 rf2.

  (* result is a function value *)
  simpl in VF. destruct vf1, vf2; try contradiction.

  (* argument evaluates *)
  remember (teval (n-nf1) H1 t1) as tx1. symmetry in Heqtx1. destruct tx1 as [nx1 [rx1|]]. 2: inversion TE1. 
  edestruct (HX (S n) H1 H2) as (nx2 & rx2 & TX2 & (vx1 & vx2 & RX1 & RX2 & VX)). eauto.
  eapply eval_deterministic. eauto. eauto. lia.
  eapply eval_bounded in Heqtx1 as BX1; eauto.
  remember (S n - nx1) as nx'. destruct nx'. lia.
  subst rx1 rx2. 

  (* function body evaluates *)
  remember (teval (n-nf1-nx1) (vx1 :: l) t) as ty1. symmetry in Heqty1. destruct ty1 as [ny1 [ry1|]]. 2: inversion TE1.
  eapply eval_bounded in Heqty1 as BY1; eauto.
  inversion TE1. 
  subst ry1.

  (* from function LR: function body result is well-typed *)
  assert (nf' = n - nf1). lia. subst nf'. 
  edestruct VF with (nx:=nx1) as (ny2 & ry2 & TY2 & (vy1 & vy2 & RY1 & RY2 & VY)).
  eapply valt_dec; eauto. lia.
  eapply eval_deterministic. 2: eauto. eauto. lia.

  eexists (S (nf2+nx2+ny2)),ry2. split. simpl.
  eapply eval_deterministic in TF2. rewrite TF2.
  eapply eval_deterministic in TX2. rewrite TX2.
  eapply eval_deterministic in TY2. rewrite TY2.
  eauto. eauto. lia. eauto. lia. eauto. lia. 

  (* return result *)
  exists vy1, vy2. split. 2: split.
  eauto. eauto. eapply valt_dec. eauto. eapply VY. lia.
Qed.

Lemma sem_abs: forall G t1 t2 T1 T2,
    sem_type (T1::G) t1 t2 T2 ->
    sem_type G (tabs t1) (tabs t2) (TFun T1 T2).
Proof.
  intros ? ? ? ? ? HY. intros n H1 H2 WFE. intros ? ? TE1.
  destruct n; inversion TE1.
  eexists 1, _. split. simpl. eauto. 
  exists (vabs H1 t1), (vabs H2 t2). split. 2: split. 
  - eauto.
  - eauto.
  - simpl. destruct n; simpl; eauto. intros.
    edestruct (HY) as (ny2 & ry2 & TY1 & ?). eapply envt_extend.
    eapply envt_dec. eauto. 2: eauto. lia. eauto. eauto.
Qed.


                                                       
(* ---------- LR fundamental property  ---------- *)

Theorem fundamental: forall G t T,
    has_type G t T ->
    sem_type G t t T.
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
  forall n, exp_type n [] [] t t T.
Proof. 
  intros. intros ? ? TE1.
  eapply fundamental in H as ST; eauto.
  edestruct (ST n [] []) as (? & ? & ? & ?).
  eapply envt_empty. eapply TE1. 
  eexists _,_. split. eauto. eauto.
Qed.


(* ---------- LR contextual approximation and equivalence  ---------- *)

(* Define typed contexts and prove that the binary logical
   relation implies contextual equivalence (congruency wrt
   putting expressions in context *)

(* NB: one could add a lemma showing that these are all
   possible contexts. *)

Inductive ctx_type : (tm -> tm) -> tenv -> ty -> tenv -> ty -> Prop :=
| c_top: forall G T,
    ctx_type (fun x => x) G T G T
| c_app1: forall e2 G T1 T2,
    has_type G e2 T1 ->
    ctx_type (fun x => tapp x e2) G (TFun T1 T2) G T2
| c_app2: forall e1 G T1 T2,
    has_type G e1 (TFun T1 T2) ->
    ctx_type (fun x => tapp e1 x) G T1 G T2
| c_abs: forall G T1 T2,
    ctx_type (fun x => tabs x) (T1::G) T2 G (TFun T1 T2).

Theorem congr:
  forall C G1 T1 G2 T2,
    ctx_type C G1 T1 G2 T2 ->
  forall e e',
    sem_type G1 e e' T1 ->
    sem_type G2 (C e) (C e') T2.
Proof.
  intros ? ? ? ? ? CX.
  induction CX; intros.
  - eauto.
  - eapply sem_app. eauto. eapply fundamental. eauto.
  - eapply sem_app. eapply fundamental. eauto. eauto.
  - eapply sem_abs. eauto.
Qed.


Definition tevaln env e v := exists n n', teval n env e = (n',Some (Some v)).

Definition kleene_approx e e' :=
   (exists v, tevaln [] e v) -> (exists v', tevaln [] e' v').

(* NOTE: it may be desirable to also prove the following property *)
Definition kleene_approx2 e e' :=
   forall b, tevaln [] e (vbool b) -> tevaln [] e' (vbool b).


Lemma adequacy: forall e e' T,
  sem_type [] e e' T ->
  kleene_approx e e'.
Proof. 
  intros. intros [v1 [n1 [n1' TE1]]].
  edestruct (H n1 [] []) as (n2 & r2 & TE2 & (v1' & v2' & R1 & R2 & VT)).
  split. 2: split. eauto. eauto. intros. inversion H0.
  eauto.
  subst r2. eexists _,_,_. eauto. 
Qed.


Definition context_approx G t1 t2 T1 :=
  forall C,
    ctx_type C G T1 [] TBool ->
    kleene_approx (C t1) (C t2).

(* soundness of binary logical relations wrt contextual approximation *)
Theorem soundess: forall G t1 t2 T,
  sem_type G t1 t2 T ->
  context_approx G t1 t2 T.
Proof.
  intros. intros ? HC.
  eapply adequacy.
  eapply congr; eauto. 
Qed.


(* ---- from approximation to equivalence ---- *)

Definition sem_type2 G e e' T :=
  sem_type G e e' T /\
  sem_type G e' e T.

Theorem fundamental2: forall G t T,
    has_type G t T ->
    sem_type2 G t t T.
Proof.
  intros ? ? ? W.
  split; eapply fundamental; eauto.
Qed.

Theorem congr2:
  forall C G1 T1 G2 T2,
    ctx_type C G1 T1 G2 T2 ->
  forall e e',
    sem_type2 G1 e e' T1 ->
    sem_type2 G2 (C e) (C e') T2.
Proof.
  intros ? ? ? ? ? CX.
  induction CX; intros. 
  - eauto.
  - destruct H0. split.
    eapply sem_app. eauto. eapply fundamental. eauto.
    eapply sem_app. eauto. eapply fundamental. eauto.
  - destruct H0. split.
    eapply sem_app. eapply fundamental. eauto. eauto. 
    eapply sem_app. eapply fundamental. eauto. eauto.
  - destruct H. split.
    eapply sem_abs. eauto.
    eapply sem_abs. eauto.
Qed.

Definition kleene_equiv e e' :=
  kleene_approx e e' /\
  kleene_approx e' e.

Definition context_equiv G t1 t2 T1 :=
  forall C,
    ctx_type C G T1 [] TBool ->
    kleene_equiv (C t1) (C t2).

Lemma adequacy2: forall e e' T,
  sem_type2 [] e e' T ->
  kleene_equiv e e'.
Proof.
  intros. destruct H. split.
  eapply adequacy; eauto.
  eapply adequacy; eauto.
Qed.

(* soundness of binary logical relations wrt contextual approximation *)
Theorem soundess2: forall G t1 t2 T,
  sem_type2 G t1 t2 T ->
  context_equiv G t1 t2 T.
Proof.
  intros. intros ? HC.
  eapply adequacy2.
  eapply congr2; eauto. 
Qed.



End STLC.
