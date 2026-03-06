(* Full safety for STLC *)

(*

An proof that CPS conversion of STLC preserves types (modulo conversion).

The transformation uses a dedicated sublanguage (cvar, capp, cabs, clet)
for terms introduced by the transformation.

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
  (* ----- *)                       
  | CAns   : ty
  | CFun   : ty -> ty -> ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : tm -> tm
  (* ----- *)                       
  | cvar : id -> tm
  | capp : tm -> tm -> tm
  | cabs : tm -> tm
  | clet : tm -> tm -> tm
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

(* typing pre-transformation *)
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

(* typing post-transformation *)
Inductive has_type1 : tenv -> tenv -> tm -> ty -> Prop :=
| t1_true: forall env cnv,
    has_type1 env cnv ttrue TBool
| t1_false: forall env cnv,
    has_type1 env cnv tfalse TBool
| t1_var: forall x env cnv T,
    indexr x env = Some T ->
    has_type1 env cnv (tvar x) T
| t1_app: forall env cnv f t T1 T2,
    has_type1 env cnv f (TFun T1 T2) ->
    has_type1 env cnv t T1 ->
    has_type1 env cnv (tapp f t) T2
| t1_abs: forall env cnv t T1 T2,
    has_type1 (T1::env) cnv t T2 ->
    has_type1 env cnv (tabs t) (TFun T1 T2)
(* ----- *)
| c1_var: forall x env cnv T,
    indexr x cnv = Some T ->
    has_type1 env cnv (cvar x) T
| c1_app: forall env cnv f t T1 T2,
    has_type1 env cnv f (CFun T1 T2) ->
    has_type1 env cnv t T1 ->
    has_type1 env cnv (capp f t) T2
| c1_abs: forall env cnv t T1 T2,
    has_type1 env (T1::cnv) t T2 ->
    has_type1 env cnv (cabs t) (CFun T1 T2)
| c1_let: forall env cnv t1 t2 T1 T2,
    has_type1 env cnv t1 T1 ->
    has_type1 env (T1::cnv) t2 T2 ->
    has_type1 env cnv (clet t1 t2) T2
.


(* ---------- first-order cps transform ---------- *)

Fixpoint cps (d: nat) (t: tm) (c: nat): tm :=
  match t with
  | ttrue  => capp (cvar c) ttrue
  | tfalse => capp (cvar c) tfalse
  | tvar x => capp (cvar c) (tvar x)
  | tapp f t =>
      let cf := d in let vf := cvar d in
      let ct := (S d) in let vt := cvar (S d) in
      (clet (*cf*) (cabs (*vf*) (
        (clet (*ct*) (cabs (*vt*) 
          (capp (tapp vf vt) (cvar c)))
          (cps (S ct) t ct))))
        (cps (S cf) f cf))
  | tabs t =>
      capp (cvar c) (tabs (cabs (cps (S d) t d)))
  | _ => t
  end.


Fixpoint cps_ty T :=
  match T with
  | TFun T1 T2 => TFun (cps_ty T1) (CFun (CFun (cps_ty T2) CAns) CAns)
  | T => T
  end.



(* ---------- result: cps transform is well-typed  ---------- *)

Lemma indexr_map: forall {A B} (M: list A) x (f: A -> B),
    indexr x (map f M) = option_map f (indexr x M).
Proof.
  intros ? ? M. induction M; intros; simpl in *. eauto. 
  rewrite map_length. bdestruct (x =? length M); eauto. 
Qed.


Theorem cps_well_typed: forall G t T,
    has_type G t T ->
    forall c H,
      indexr c H = Some (CFun (cps_ty T) CAns) ->
      has_type1 (map cps_ty G) H (cps (length H) t c) CAns.
Proof.
  intros ??? H.
  induction H; intros.
  - simpl. eapply c1_app. eapply c1_var. eauto. eapply t1_true.
  - simpl. eapply c1_app. eapply c1_var. eauto. eapply t1_false.
  - simpl. eapply c1_app. eapply c1_var. eauto. eapply t1_var. rewrite indexr_map, H. eauto. 
  - simpl. eapply c1_let.
    2: {
      eapply IHhas_type1. rewrite indexr_head. eauto.
    } {
      eapply c1_abs. eapply c1_let.
      2: {
        remember (_::H1) as H1'. replace (S (length H1)) with (length H1').
        eapply IHhas_type2. rewrite indexr_head. eauto.
        subst. simpl. lia.
      }
      eapply c1_abs. eapply c1_app. eapply t1_app. eapply c1_var.
      rewrite indexr_skip. rewrite indexr_head. simpl. eauto. simpl. lia.
      eapply c1_var. remember (_::H1) as H1'. replace (S (length H1)) with (length H1').
      rewrite indexr_head. eauto. subst. simpl. eauto. 
      eapply c1_var. eapply indexr_var_some' in H2 as H2'.
      rewrite indexr_skip. rewrite indexr_skip. eauto. lia. simpl. lia.
    }
  - simpl. eapply c1_app. eapply c1_var. eauto.
    simpl. eapply t1_abs. eapply c1_abs.
    remember (_::H0) as H0'. replace (S (length H0)) with (length H0').
    eapply IHhas_type. subst. rewrite indexr_head. eauto.
    subst. simpl. eauto. 
Qed.

(* at the top level, we assume a continuation for the entire
   program is given in environment slot 0 (this could be done
   differently) *)
Corollary cps_wt_closed: forall t T,
    has_type [] t T ->
    has_type1 [] [CFun (cps_ty T) CAns] (cps 1 t 0) CAns.
Proof.
  intros. 
  remember [_]. replace 1 with (length l). 2: subst;eauto. 
  eapply cps_well_typed  in H. simpl in H. eapply H.
  subst l. replace 0 with (length (@nil ty)).
  rewrite indexr_head. eauto. eauto. 
Qed.

End STLC.
