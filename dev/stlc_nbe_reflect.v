(* Full safety for STLC *)

(*

An LR-based normalization and semantic soundness proof for STLC.

Normalization by evaluation, based on standard cbv semantics.

Reflecting semantic types directly to Coq values/functions.

NOTE: not correct yet!

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

Definition tenv := list ty.

#[global] Hint Unfold tenv.


(* ---------- syntactic typing rules ---------- *)


Inductive has_type (env: tenv): tm -> ty -> Type :=
| t_true: 
    has_type env ttrue TBool
| t_false: 
    has_type env tfalse TBool
| t_var: forall x T,
    indexr x env = Some T ->
    has_type env (tvar x) T
| t_app: forall f t T1 T2,
    has_type env f (TFun T1 T2) ->
    has_type env t T1 ->
    has_type env (tapp f t) T2
| t_abs: forall t T1 T2,
    has_type (T1::env)  t T2 ->
    has_type env (tabs t) (TFun T1 T2)
.


(* ---------- evaluator ---------- *)

Fixpoint sem_ty (A: ty): Type :=
  match A with
  | TBool => bool
  | TFun T1 T2 => sem_ty T1 -> sem_ty T2
  end.

Definition envt (G: tenv) := forall x T,
    indexr x G = Some T -> sem_ty T.

Lemma envkv_nil:
  envt nil.
Proof.
  intros ???. inversion H.
Defined.
  
Fixpoint envkv_cons J: forall K,
    sem_ty K ->
    envt J ->
    envt (K::J).
Proof.
  intros. intros ???. 
  destruct (Nat.eq_dec x (length J)). subst.
  rewrite indexr_head in H. inversion H. subst. eauto.
  rewrite indexr_skip in H. eapply X0. eauto. eauto. 
Defined.


Fixpoint eval (G: tenv) (t: tm) (T: ty) (h: has_type G t T) (h2: envt G): sem_ty T := 
  match h, T return sem_ty T with
  | t_true _, _ => true
  | t_false _, _ => false
  | t_var _ x T0 IX, _ => h2 _ _ IX
  | t_app _ f t T1 T2 EF EX, _ => (eval _ _ _  EF h2) (eval _ _ _  EX h2)
  | t_abs _ t T1 T2 EY, _ => (fun x => eval _ _ _ EY (envkv_cons _ _ x h2))
  end.


Example t1 := (tabs (tapp (tvar 0) (ttrue))).

Lemma t1t: has_type [] t1 (TFun (TFun TBool TBool) TBool).
Proof.
  repeat econstructor.
Defined.

Example v1 := eval [] t1 _ t1t envkv_nil.

Compute (v1 (fun x => x)). 

Require Import Coq.Program.Equality.


(* ---------- normalizer ---------- *)


Inductive evl (A: Type): Type :=
| ev_cst: A -> evl A
| ev_sym: tm -> evl A
.

Fixpoint sem_ty1' (A: ty): Type := 
  match A with
  | TBool => bool
  | TFun T1 T2 => evl (sem_ty1' T1) -> tenv -> evl (sem_ty1' T2)
  end.

Definition sem_ty1 (A: ty): Type := evl (sem_ty1' A).

Definition envt1 (G: tenv) := forall x T,
    indexr x G = Some T -> sem_ty1 T.

Lemma envkv_nil1:
  envt nil.
Proof.
  intros ???. inversion H.
Defined.
  
Fixpoint envkv_cons1 J: forall K,
    sem_ty1 K ->
    envt1 J ->
    envt1 (K::J).
Proof.
  intros. intros ???. 
  destruct (Nat.eq_dec x (length J)). subst.
  rewrite indexr_head in H. inversion H. subst. eauto.
  rewrite indexr_skip in H. eapply X0. eauto. eauto. 
Defined.

Fixpoint reify1 T (h: sem_ty1 T) (J: tenv): tm :=
  match T, h return tm with
  | TBool, ev_cst _ true => ttrue
  | TBool, ev_cst _ false => tfalse
  | TFun T1 T2, ev_cst _ f =>
      tabs (reify1 _ (f(ev_sym _ (tvar (length J))) (T1::J)) (T1::J))
  | _, ev_sym _ t => t
  end.


(*
Fixpoint reify T (h: sem_ty1 T) (J: tenv): { t: tm & has_type J t T } :=
  match T, h return { t: tm & has_type J t T } with
  | TBool, ev_cst _ true => existT _ ttrue (t_true J)
  | TBool, ev_cst _ false => existT _ tfalse (t_false J)
  | TFun T1 T2, ev_cst _ f =>
      match (reify _ (f(ev_sym _ (tvar (length J))) (T1::J)) (T1::J)) with
      | existT _ t ht => existT _ (tabs t) (t_abs J t T1 T2 ht)
      end
  | _, ev_sym _ t => existT _ t _
  end.*)

(*
Definition reify' T (h: sem_ty1 T) (J: tenv): tm :=
  match reify T h J with
  | { a & b } => a
  end.
*)


Fixpoint eval1 (G: tenv) (t: tm) (T: ty) (h: has_type G t T) (h2: envt1 G) n {struct h}: sem_ty1 T := 
  match h, T return sem_ty1 T with
  | t_true _, _ => ev_cst _ true
  | t_false _, _ => ev_cst _ false
  | t_var _ x T0 IX, _ => h2 _ _ IX
  | t_app _ f t T1 T2 EF EX, _ =>
      match (eval1 _ _ _  EF h2 n) return sem_ty1 T2 with
      | ev_cst _ f => f (eval1 _ _ _ EX h2 n) n
      | ev_sym _ tf => ev_sym _ (tapp tf (reify1 _ (eval1 _ _ _ EX h2 n) n))
      end
  | t_abs _ t T1 T2 EY, _ => ev_cst _ (fun x J' => eval1 _ _ _ EY (envkv_cons1 _ _ x h2) J')
  end.




(* ---------- XXXX: trying to generate a proof of well_typedness -- doesn't work yet  ---------- *)


Fixpoint sem_ty2' (G:tenv) (A: ty): Type := 
  match A with
  | TBool => bool
  | TFun T1 T2 => forall G', evl (sem_ty2' (G'++G) T1) -> evl (sem_ty2' (G'++G) T2)
  end.

Definition sem_ty2 (G: tenv) (A: ty): Type := evl (sem_ty2' G A).


Lemma semt_extend: forall A G T,
    sem_ty2 G A ->
    sem_ty2 (T::G) A.
Proof.
  intros A. induction A; intros.
  - inversion X. eauto. eauto.
  - inversion X. eapply ev_cst. simpl in *.
    intros. replace (G' ++ T :: G) with ((G'++[T])++G). 
    eapply X0. rewrite <-app_assoc. eauto.
    rewrite <-app_assoc. simpl. eauto. 

(*    eapply X0. eapply IHA2. eauto. eapply X0.
    replace (G'++T::G) with ((G'++[T])++G) in X1.
    2: { rewrite <-app_assoc. simpl. eauto. }
    eauto. *)
    eapply ev_sym. eauto. 
Qed.


Definition envt2 (G: tenv) := forall x T,
    indexr x G = Some T -> sem_ty2 G T.

Lemma envkv_nil2:
  envt2 nil.
Proof.
  intros ???. inversion H.
Defined.
  
Fixpoint envkv_cons2 J: forall K,
    sem_ty2 J K ->
    envt2 J ->
    envt2 (K::J).
Proof.
  intros. intros ???. 
  destruct (Nat.eq_dec x (length J)). subst.
  rewrite indexr_head in H. inversion H. subst. eapply semt_extend. eauto. 
  rewrite indexr_skip in H. eapply semt_extend. eapply X0. eauto. eauto. 
Defined.

Fixpoint reify20 T J (h: sem_ty2 J T): tm :=
  match T, h return tm with
  | TBool, ev_cst _ true => ttrue
  | TBool, ev_cst _ false => tfalse
  | TFun T1 T2, ev_cst _ f =>
      tabs (reify20 _ _ (f [T1] (ev_sym _ (tvar (length J)))))
  | _, ev_sym _ t => t
  end.

(*
Fixpoint eeval2 (G: tenv) (t: tm) (T: ty) (h: has_type G t T) (h2: envt2 G) n {struct h}: sem_ty2 G T := 
  match h, T return sem_ty2 G T with
  | t_true _, _ => ev_cst _ true
  | t_false _, _ => ev_cst _ false
  | t_var _ x T0 IX, _ => h2 _ _ IX
  | t_app _ f t T1 T2 EF EX, _ =>
      match (eeval2 _ _ _  EF h2 n) return sem_ty2 G T2 with
      | ev_cst _ f => f [] (eeval2 _ _ _ EX h2 n)
      | ev_sym _ tf => ev_sym _ (tapp tf (reify20 _ _ (eeval2 _ _ _ EX h2 n)))
      end
  | t_abs _ t T1 T2 EY, _ =>
      ev_cst _ (fun J' y => eeval2 _ _ _ EY (envkv_cons2 _ _ y h2) n)
  end.
*)

Fixpoint eeval (G: tenv) (t: tm) (T: ty) (h: has_type G t T) (h2: envt G): sem_ty T := 
  match h, T return sem_ty T with
  | t_true _, _ => true
  | t_false _, _ => false
  | t_var _ x T0 IX, _ => h2 _ _ IX
  | t_app _ f t T1 T2 EF EX, _ => (eeval _ _ _  EF h2) (eeval _ _ _  EX h2)
  | t_abs _ t T1 T2 EY, _ => (fun x => eeval _ _ _ EY (envkv_cons _ _ x h2))
  end.


Fixpoint reify2 T (h: sem_ty1 T) (J: tenv): { t: tm & has_type J t T } :=
  match T, h return { t: tm & has_type J t T } with
  | TBool, ev_cst _ true => existT _ ttrue (t_true J)
  | TBool, ev_cst _ false => existT _ tfalse (t_false J)
  | TFun T1 T2, ev_cst _ f =>
      match (reify2 _ (f(ev_sym _ (tvar (length J))) (T1::J)) (T1::J)) with
      | existT _ t ht => existT _ (tabs t) (t_abs J t T1 T2 ht)
      end
  | _, ev_sym _ t => existT _ t _
  end.




