(* Full safety for STLC *)

(*

An LR-based termination and semantic soundness proof for STLC.

Canonical big-step cbv semantics.

This version includes a built-in list datatype, with nil and
cons as introduction forms and fold-right as elimination form
(supporting primitive recursion).

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
  | TList  : ty -> ty
  | TFun   : ty -> ty -> ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tnil : tm
  | tvar : id -> tm
  | tcons : tm -> tm -> tm
  | tfold : tm -> tm -> tm -> tm
  | tapp : tm -> tm -> tm
  | tabs : tm -> tm
.

Inductive vl: Type :=
| vbool :  bool -> vl
| vlist :  list vl -> vl
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
| t_nil: forall env T1,
    has_type env tnil (TList T1)
| t_cons: forall env h t T1,
    has_type env h T1 ->
    has_type env t (TList T1) ->
    has_type env (tcons h t) (TList T1)
| t_fold: forall env f z t T1 T2, (* e.g. fold (x,acc => ..) z xs *)
    has_type (T2::T1::env) f T2 ->
    has_type env z T2 ->
    has_type env t (TList T1) ->
    has_type env (tfold f z t) T2
| t_app: forall env f t T1 T2,
    has_type env f (TFun T1 T2) ->
    has_type env t T1 ->
    has_type env (tapp f t) T2
| t_abs: forall env t T1 T2,
    has_type (T1::env) t T2 ->
    has_type env (tabs t) (TFun T1 T2)
.

(* ---------- operational semantics ---------- *)

Fixpoint teval(n: nat)(env: venv)(t: tm){struct n}: option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | ttrue      => Some (Some (vbool true))
        | tfalse     => Some (Some (vbool false))
        | tnil       => Some (Some (vlist nil))
        | tvar x     => Some (indexr x env)
        | tcons ehd etl   =>
          match teval n env ehd with
            | None => None
            | Some None => Some None
            | Some (Some vhd) => 
              match teval n env etl with
                | None => None
                | Some None => Some None
                | Some (Some (vbool _)) => Some None
                | Some (Some (vabs _ _)) => Some None
                | Some (Some (vlist vtl)) => Some (Some (vlist (vhd::vtl)))
              end
          end
        | tfold ef ez els   =>
          match teval n env ez with
            | None => None
            | Some None => Some None
            | Some (Some vz) => 
              match teval n env els with
                | None => None
                | Some None => Some None
                | Some (Some (vbool _)) => Some None
                | Some (Some (vabs _ _)) => Some None
                | Some (Some (vlist vls)) =>
                    let f := fun hd tl =>
                               match tl with
                               | None => None
                               | Some None => Some None
                               | Some (Some vtl) =>
                                   teval n (vtl::hd::env) ef
                               end in
                    fold_right f (Some (Some vz)) vls
              end
          end
        | tabs y       => Some (Some (vabs env y))
        | tapp ef ex   =>
          match teval n env ef with
            | None => None
            | Some None => Some None
            | Some (Some (vbool _)) => Some None
            | Some (Some (vlist _)) => Some None
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

Fixpoint val_type v T : Prop :=
  match v, T with
  | vbool b, TBool =>  
      True
  | vlist vs, TList T1 =>  
      Forall (fun v => val_type v T1) vs 
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
  exists v,
    tevaln H t v /\
    val_type v T.

Definition env_type (H: venv) (G: tenv) :=
  length H = length G /\
    forall x T,
      indexr x G = Some T ->
      exists v,
        indexr x H = Some v /\
        val_type v T.

Definition sem_type G t T :=
  forall H,
    env_type H G ->
    exp_type H t T.


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: core.

#[export] Hint Constructors has_type: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.




(* ---------- LR helper lemmas  ---------- *)

Lemma envt_empty:
    env_type [] [].
Proof.
  intros. split. eauto. intros. inversion H. 
Qed.

Lemma envt_extend: forall E G v1 T1,
    env_type E G ->
    val_type v1 T1 ->
    env_type (v1::E) (T1::G).
Proof.
  intros. 
  remember H as WFE. clear HeqWFE.
  destruct H. split. simpl. eauto.
  intros x T IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX. subst T1.
    exists v1. rewrite <- H. rewrite indexr_head. eauto.
  - rewrite indexr_skip in IX; eauto.
    eapply WFE in IX as IX. destruct IX as (v2 & ? & ?).
    exists v2. rewrite indexr_skip; eauto. lia.
Qed.


(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_true: forall G,
    sem_type G ttrue TBool.
Proof.
  intros. intros E WFE. 
  exists (vbool true). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto. 
Qed.

Lemma sem_false: forall G,
    sem_type G tfalse TBool.
Proof.
  intros. intros E WFE. 
  exists (vbool false). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto. 
Qed.

Lemma sem_nil: forall G T1,
    sem_type G tnil (TList T1).
Proof.
  intros. intros E WFE. 
  exists (vlist nil). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto. 
Qed.

Lemma sem_var: forall G x T,
    indexr x G = Some T ->
    sem_type G (tvar x) T.
Proof.
  intros. intros E WFE.
  eapply WFE in H as IX. destruct IX as (v & IX & VX).
  exists v. split. 
  - exists 0. intros. destruct n. lia. simpl. rewrite IX. eauto.
  - eauto. 
Qed.

Lemma sem_cons: forall G h t T1,
    sem_type G h T1 ->
    sem_type G t (TList T1) ->
    sem_type G (tcons h t) (TList T1).
Proof.
  intros ? ? ? ? HH HT. intros E WFE.
  destruct (HH E WFE) as (vh & STH & VH).
  destruct (HT E WFE) as (vt & STT & VT).
  destruct vt; simpl in VT; intuition.
  exists (vlist (vh::l)). split.
  - destruct STH as (n1 & STH).
    destruct STT as (n2 & STT).
    exists (1+n1+n2). intros. destruct n. lia.
    simpl. rewrite STH, STT. 2,3: lia.
    eauto.
  - simpl. econstructor; eauto. 
Qed.

Lemma sem_fold: forall G f z t T1 T2,
    sem_type (T2::T1::G) f T2 ->
    sem_type G z T2 ->
    sem_type G t (TList T1) ->
    sem_type G (tfold f z t) T2.
Proof.
  intros ? ? ? ? ? ? HF HZ HT. intros E WFE.
  destruct (HZ E WFE) as (vz & STZ & VZ).
  destruct (HT E WFE) as (vt & STT & VT).
  destruct vt; simpl in VT; intuition.

  assert (forall vt vh,
      val_type vh T1 -> val_type vt T2 ->
      exists v2, tevaln (vt::vh::E) f v2 /\ val_type v2 T2) as HFF. {
    intros.
    edestruct (HF ((vt::vh::E))) as (v2 & ST2 & V2).
    eapply envt_extend. eapply envt_extend. eauto. eauto. eauto. 
    eexists. split. eauto. eauto. 
  }

  remember (fun n => fun (hd:vl) (tl:option (option vl)) =>
    match tl with
    | Some (Some vtl) => teval n (vtl :: hd :: E) f
    | Some None => Some None
    | None => None
    end) as ff.
  
  assert (exists v2,
      (exists nm, forall n, n > nm ->
        fold_right (ff n) (Some (Some vz)) l = Some (Some v2)) /\
      val_type v2 T2) as FOLD. {
    clear STT. induction l. exists vz. split. exists 0. intros. simpl. eauto. eauto.
    inversion VT. subst x l0. destruct IHl as (v2' & (n2' & ?) & ?). eauto.
    simpl. edestruct HFF as (v1' & (n1' & ?) & ?); eauto.  
    exists v1'. split. exists (n1'+n2'). 2: eauto. intros. rewrite H. 2: lia.
    subst ff. eapply H3. lia.
  }
    
  destruct FOLD as (v2 & ST2 & V2).
  
  eexists v2. split.
  - destruct STZ as (n1 & STZ).
    destruct STT as (n2 & STT).
    destruct ST2 as (n3 & ST2).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite STZ, STT. 2,3: lia. subst ff. rewrite ST2. eauto. lia.
  - eauto. 
Qed.

Lemma sem_app: forall G f t T1 T2,
    sem_type G f (TFun T1 T2) ->
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

Lemma sem_abs: forall G t T1 T2,
    sem_type (T1::G) t T2 ->
    sem_type G (tabs t) (TFun T1 T2).
Proof.
  intros ? ? ? ? HY. intros E WFE.
  assert (length E = length G) as L. eapply WFE.
  exists (vabs E t). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros. eapply HY. eapply envt_extend; eauto.
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
  - eapply sem_nil; eauto.
  - eapply sem_cons; eauto.
  - eapply sem_fold; eauto.
  - eapply sem_app; eauto. 
  - eapply sem_abs; eauto.
Qed.

Corollary safety: forall t T,
  has_type [] t T ->
  exp_type [] t T.
Proof. 
  intros. eapply fundamental in H as ST; eauto.
  destruct (ST []) as (v & ? & ?).
  eapply envt_empty.
  exists v. intuition.
Qed.

End STLC.
