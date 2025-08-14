(* Full safety for STLC *)

(*

An LR-based termination and semantic soundness proof for STLC.

Canonical big-step cbv semantics.

In this file, we explore a type system that includes
a form of type equivalence, this time expressed
through a formal equivalence judgment.

We include type operators, abstraction and application
with a kinding system. The language corresponds to
TAPL, Chapter 29.

TODO:
- add proof of beta equivalence of types
- fundamental: subsume env_kind into sem_type
- full Fw: TAll, ttapp, ttabs

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
(*| TAll   : ty -> ty *)
  | TTAbs  : ty -> ty
  | TTApp  : ty -> ty -> ty
.

Inductive tm : Type :=
  | ttrue  : tm
  | tfalse : tm
  | tvar   : id -> tm
  | tapp   : tm -> tm -> tm
  | tabs   : tm -> tm
(*| ttapp  : tm -> ty -> tm *)
(*| ttabs  : tm -> tm *)
.

Inductive vl: Type :=
  | vbool  :  bool -> vl
  | vabs   :  list vl -> tm -> vl 
(*| vtabs  :  list vl -> tm -> vl *)
.

Definition tpe := vl -> Prop.

Inductive ty_vl : Type :=
  | TVBool : ty_vl
  | TVFun  : ty_vl -> ty_vl -> ty_vl
  | TVAbs  : list ty_vl -> ty -> ty_vl
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
      (*| ttabs y    => Some (Some (vtabs env y))*)
        | tapp ef ex   =>
          match teval n env ef with
            | None => None
            | Some None => Some None
            | Some (Some (vbool _)) => Some None
          (*| Some (Some (vtabs env2 ey)) => Some None*)
            | Some (Some (vabs env2 ey)) =>
              match teval n env ex with
                | None => None
                | Some None => Some None
                | Some (Some vx) =>
                  teval n (vx::env2) ey
              end
          end
        (*| ttapp ef T1   =>
          match teval n env ef with
            | None => None
            | Some None => Some None
            | Some (Some (vbool _)) => Some None
            | Some (Some (vabs env2 ey)) => Some None
            | Some (Some (vtabs env2 ey)) =>
                teval n env2 ey
          end*)
      end
  end.

Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).


(* ---------- type normalization rules ---------- *)

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
| teval_ttabs: forall env T2,
    type_eval env (TTAbs T2) (TVAbs env T2)
| teval_ttapp: forall env G TF T1 T2 V1 V2,
    type_eval env TF (TVAbs G T2) ->
    type_eval env T1 V1 ->
    type_eval (V1 :: G) T2 V2 ->
    type_eval env (TTApp TF T1) V2
.

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

Inductive eq_type : kenv -> ty -> ty -> kn -> Prop :=
| q_refl: forall J T K,
    has_kind J T K ->
    eq_type J T T K
| q_symm: forall J T1 T2 K,
    eq_type J T1 T2 K ->
    eq_type J T2 T1 K
| q_trans: forall J T1 T2 T3 K,
    eq_type J T1 T2 K ->
    eq_type J T2 T3 K ->
    eq_type J T1 T3 K
| q_fun: forall J T1 T2 T1' T2',
    eq_type J T1 T1' KTpe ->
    eq_type J T2 T2' KTpe ->
    eq_type J (TFun T1 T2) (TFun T1' T2') KTpe
| q_tabs:  forall J T2 T2' K1 K2,
    eq_type (K1::J) T2 T2' K2 ->
    eq_type J (TTAbs T2) (TTAbs T2') (KArr K1 K2)
| q_tapp:  forall J T1 T2 T1' T2' K1 K2,
    eq_type J T1 T1' (KArr K1 K2) ->
    eq_type J T2 T2' K1 ->
    eq_type J (TTApp T1 T2) (TTApp T1' T2') K2
(* TODO: beta *)
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
    has_kind J T2 KTpe ->
    has_type G J (tabs t) (TFun T1 T2)
| t_app: forall G J f t T1 T2,
    has_type G J f (TFun T1 T2) ->
    has_type G J t T1 ->
    has_type G J (tapp f t) T2

(*             
| t_tabs: forall G J t T2,
    has_type G J t T2 ->
    has_type G J (ttabs t) (TAll T2)
| t_tapp: forall G V f TF T1,
    has_type G V f TF ->
    has_kind T1 K1 ->
    has_type G V (ttapp f) (TTImg TF T1)
*)

| t_equiv: forall G V t T1 T2,
    has_type G V t T1 ->
    eq_type V T1 T2 KTpe ->
    has_type G V t T2
.

#[export] Hint Constructors ty: core.
#[export] Hint Constructors ty_vl: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: core.

#[export] Hint Constructors type_eval: core.

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

Lemma type_eval_unique: forall GV T V1,
    type_eval GV T V1 ->
    forall V2,
      type_eval GV T V2 ->
      V1 = V2.
  Proof. 
  intros G T V1 H. induction H; intros.
  - inversion H. eauto.
  - inversion H0. congruence. 
  - inversion H1. subst. erewrite IHtype_eval1, IHtype_eval2; eauto.
  - inversion H. subst. eauto. 
  - inversion H2; subst.
    eapply IHtype_eval1 in H5. inversion H5. subst.
    eapply IHtype_eval2 in H7. subst.
    eapply IHtype_eval3 in H9. eauto.
Qed.

(* ---------- LR definitions for types : kinds  ---------- *)

Fixpoint base_kind TL TR {struct TL}: Prop :=
  match TL, TR with
  | TVBool, TVBool =>  
      True
  | TVFun TL1 TL2, TVFun TR1 TR2 =>
      base_kind TL1 TR1 /\
      base_kind TL2 TR2
  | _,_ =>
      False
  end.

Fixpoint type_kind TL TR K {struct K}: Prop :=
  match K with
  | KTpe =>  
      base_kind TL TR
  | KArr K1 K2 =>
      match TL, TR with
        TVAbs HL TEL2, TVAbs HR TER2 =>
          forall TL1 TR1,
            type_kind TL1 TR1 K1 ->
            exists TL2 TR2,
              type_eval (TL1::HL) TEL2 TL2 /\
                type_eval (TR1::HR) TER2 TR2 /\
                type_kind TL2 TR2 K2
      | _,_ =>
          False
      end
  end.

Definition exp_kind HL HR tl tr K :=
  exists vl vr,
    type_eval HL tl vl /\
    type_eval HR tr vr /\
    type_kind vl vr K.

Definition env_kind (HL HR: tvenv) (G: kenv) :=
  length HL = length G /\
  length HR = length G /\
  forall x K,
    indexr x G = Some K ->
    exists vl vr,
      indexr x HL = Some vl /\
      indexr x HR = Some vr /\
      type_kind vl vr K.

Definition sem_kind G tl tr K :=
  forall HL HR,
    env_kind HL HR G ->
    exp_kind HL HR tl tr K.

Lemma envk_empty:
    env_kind [] [] [].
Proof.
  intros. split. 2: split.
  eauto. eauto.
  intros. inversion H. 
Qed.

Lemma envk_extend: forall HL HR G vl1 vr1 K1,
    env_kind HL HR G ->
    type_kind vl1 vr1 K1 ->
    env_kind (vl1::HL) (vr1::HR) (K1::G).
Proof.
  intros. 
  remember H as WFE. clear HeqWFE.
  destruct H as (?&?&?). split. 2: split. simpl. eauto. simpl. eauto.
  intros x K IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX. subst K.
    exists vl1, vr1. split.
    rewrite <-H. rewrite indexr_head. eauto.
    rewrite <-H1. rewrite indexr_head. eauto.
  - rewrite indexr_skip in IX; eauto.
    eapply WFE in IX as IX. destruct IX as (vl2 & vr2 & ? & ?).
    exists vl2, vr2. rewrite indexr_skip, indexr_skip; eauto. lia. lia.
Qed.

Lemma basek_symm: forall TL TR,
    base_kind TL TR ->
    base_kind TR TL.
Proof.
  intros TL. induction TL; intros; destruct TR; eauto; simpl in *.
  - intuition.
Qed.

Lemma typek_symm: forall K TL TR,
    type_kind TL TR K ->
    type_kind TR TL K.
Proof.
  intros K. induction K; intros.
  - destruct TL, TR; simpl in *; eauto.
    intuition eauto using basek_symm. 
  - destruct TL, TR; simpl in *; eauto.
    intros. edestruct H as (?&?&?&?&?).
    eapply IHK1. eauto.
    eexists _,_. split. 2: split.
    eauto. eauto.
    eapply IHK2. eauto.
Qed.

Lemma basek_trans: forall TL TM TR,
    base_kind TL TM ->
    base_kind TM TR ->
    base_kind TL TR.
Proof.
  intros TL. induction TL; intros; destruct TM, TR; simpl in *; intuition.
  eapply IHTL1. eauto. eauto.
  eapply IHTL2. eauto. eauto. 
Qed.

Lemma typek_trans: forall K TL TM TR,
    type_kind TL TM K ->
    type_kind TM TR K ->
    type_kind TL TR K.
Proof.
  intros K. induction K; intros.
  - destruct TL, TM, TR; simpl in *; try contradiction; eauto.
    intuition eauto using basek_trans.
  - destruct TL, TM, TR; simpl in *; try contradiction.
    intros.
    assert (type_kind TL1 TL1 K1). {
      eapply IHK1. eauto. eapply typek_symm. eauto. }   
    edestruct H as (?&?&?&?&?). eapply H2.
    edestruct H0 as (?&?&?&?&?). eapply H1.
    eexists _,_. split. 2: split.
    eauto. eauto.
    assert (x0 = x1). {
      eapply type_eval_unique; eauto. }
    subst x0. eapply IHK2. eauto. eauto.
Qed.


Lemma sem_bool: forall G,
    sem_kind G TBool TBool KTpe.
Proof.
  intros. intros E WFE. 
  exists TVBool, TVBool. split. 2: split. 
  - eauto. 
  - eauto.
  - simpl. eauto.
Qed.

Lemma sem_tvar: forall J x K,
    indexr x J = Some K ->
    sem_kind J (TVar x) (TVar x) K.
Proof.
  intros. intros HL HR  WFE.
  eapply WFE in H as IX. destruct IX as (vl & vr & IXL & IXR & KX).
  exists vl, vr. split. 2: split. 
  - eauto. 
  - eauto.
  - eauto.
Qed.

Lemma sem_fun: forall G TL1 TR1 TL2 TR2,
    sem_kind G TL1 TR1 KTpe ->
    sem_kind G TL2 TR2 KTpe ->
    sem_kind G (TFun TL1 TL2) (TFun TR1 TR2) KTpe.
Proof.
  intros ? ? ? ? ? H1 H2. intros HL HR WFE.
  edestruct H1 as (vl1 & vr1 & ? & ? & ?). eauto.
  edestruct H2 as (vl2 & vr2 & ? & ? & ?). eauto.
  exists (TVFun vl1 vl2), (TVFun vr1 vr2). split. 2: split. 
  - eauto. 
  - eauto.
  - simpl. eauto.
Qed.

Lemma sem_tabs: forall G TL2 TR2 K1 K2,
    sem_kind (K1::G) TL2 TR2 K2 ->
    sem_kind G (TTAbs TL2) (TTAbs TR2) (KArr K1 K2).
Proof.
  intros ? ? ? ? ? HY. intros HL HR WFE.
  assert (length HL = length G) as LL. eapply WFE.
  assert (length HR = length G) as LR. eapply WFE.
  exists (TVAbs HL TL2), (TVAbs HR TR2). split. 2: split. 
  - eauto.
  - eauto.
  - simpl. intros. 
    edestruct HY as (vl & vr & STY & VYL & VYR). {
      eapply envk_extend. eauto. eauto. 
    }
    eauto. 
Qed.

Lemma sem_tapp: forall G TFL TFR T1L T1R K1 K2,
    sem_kind G TFL TFR (KArr K1 K2) ->
    sem_kind G T1L T1R K1 ->
    sem_kind G (TTApp TFL T1L) (TTApp TFR T1R) K2.
Proof.
  intros ? ? ? ? ? ? ? HF HX. intros HL HR WFE.
  destruct (HF HL HR WFE) as (vfl & vfr & EFL & EFR & VF).
  destruct (HX HL HR WFE) as (vxl & vxr & EXL & EXR & VX).
  destruct vfl, vfr; simpl in VF; intuition.
  edestruct VF as (vyl & vyr & EYL & EYR & VY). eauto. 
  exists vyl, vyr. split. 2: split. 
  - eauto. 
  - eauto.
  - eauto.
Qed.

Theorem has_kind_fundamental: forall J T K,
    has_kind J T K ->
    sem_kind J T T K.
Proof.
  intros ? ? ? W. 
  induction W.
  - eapply sem_bool; eauto.
  - eapply sem_tvar; eauto.
  - eapply sem_fun; eauto.
  - eapply sem_tabs; eauto. 
  - eapply sem_tapp; eauto.
Qed.


Lemma eq_refl: forall J T K,
    has_kind J T K ->
    sem_kind J T T K.
Proof.
  intros. eapply has_kind_fundamental. eauto. 
Qed.

Lemma eq_symm: forall J T1 T2 K,
    sem_kind J T1 T2 K ->
    sem_kind J T2 T1 K.
Proof.
  intros ??????? WFE.
  edestruct H as (vl & vr &?&?&?). { (* envt_symm *)
    destruct WFE as (LL & LR & WF).
    split. 2: split. eapply LR. eapply LL. intros.
    edestruct WF as (vl & vr & IXL & IXR & ?). eauto. 
    eexists vr, vl. split. 2: split.
    eauto. eauto.
    eapply typek_symm. eauto.
  }
  eexists vr, vl. split. 2: split.
  eauto. eauto.
  eapply typek_symm. eauto. 
Qed.

Lemma eq_trans: forall J T1 T2 T3 K,
    sem_kind J T1 T2 K ->
    sem_kind J T2 T3 K ->
    sem_kind J T1 T3 K.
Proof.
  intros ????? H1 H2.
  eapply eq_symm in H1 as H1'. 
  intros ?? WFE.
  edestruct H1 as (?&?&?&?&?). eauto.
  edestruct H2 as (?&?&?&?&?). {
    destruct WFE as (LL & LR & WF). split. 2: split.
    eapply LR. eapply LR. intros.
    edestruct WF as (?&vr&?&?&?). eauto.
    eexists vr,vr. split. 2: split.
    eauto. eauto. eapply typek_trans. eapply typek_symm. eauto. eauto. }
  assert (x0 = x1). eapply type_eval_unique; eauto. subst. 
  eexists _,_. split. 2: split.
  eauto. eauto.
  eapply typek_trans. eauto. eauto. 
Qed.

Theorem eq_type_fundamental: forall J T1 T2 K,
    eq_type J T1 T2 K ->
    sem_kind J T1 T2 K.
Proof.
  intros ? ? ? ? W. 
  induction W.
  - eapply eq_refl. eauto.
  - eapply eq_symm. eauto.
  - eapply eq_trans; eauto. 
  - eapply sem_fun; eauto. 
  - eapply sem_tabs; eauto. 
  - eapply sem_tapp; eauto.
Qed.


(* ---------- LR definitions for values : types  ---------- *)

Fixpoint val_type v T {struct T}: Prop :=
  match v, T with
  | vbool b, TVBool =>  
      True
  | vabs H ty, TVFun T1' T2' =>
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
    type_eval V T T' /\
    val_type v T'.

Definition env_type (H: venv) (G: tenv) (V: tvenv) :=
  length H = length G /\
  forall x T,
    indexr x G = Some T ->
    exists v T',
      indexr x H = Some v /\
      type_eval V T T' /\
      val_type v T'.

Definition sem_type G V t T :=
  forall H,
    env_type H G V ->
    exp_type H V t T.


(* ---------- LR helper lemmas  ---------- *)

Lemma envt_empty:
    env_type [] [] [].
Proof.
  intros. split. eauto. intros. inversion H. 
Qed.

Lemma envt_extend: forall E G V v1 T1 T1',
    env_type E G V ->
    type_eval V T1 T1' ->
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
  intros. (* intros WFG. split. eexists. eauto. *)
  intros E WFE. exists (vbool true), TVBool. split. 2: split. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
  - simpl. eauto.
Qed.

Lemma sem_false: forall G V,
    sem_type G V tfalse TBool.
Proof.
  intros. (* intros WFG. split. eexists. eauto. *)
  intros E WFE. exists (vbool false), TVBool. split. 2: split. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
  - simpl. eauto.
Qed.

Lemma sem_var: forall G V x T,
    indexr x G = Some T ->
    sem_type G V (tvar x) T.
Proof.
  intros. (* intros WFG. split. eapply WFG. eauto. *)
  intros E WFE.
  eapply WFE in H as IX. destruct IX as (v & T' & IX & NX & VX).
  exists v, T'. split. 2: split. 
  - exists 0. intros. destruct n. lia. simpl. rewrite IX. eauto.
  - eauto. 
  - eauto. 
Qed.

(*
sem_app, traditional form:
 *)

Lemma sem_app: forall G V f t T1 T2,
    sem_type G V f (TFun T1 T2) ->
    sem_type G V t T1 ->
    sem_type G V (tapp f t) T2.
Proof.
  intros ? ? ? ? ? ? HF HX. intros H WFE.
  destruct (HF H WFE) as (vf & TVF & STF & TEF & VF).
  destruct (HX H WFE) as (vx & TVX & STX & TEX & VX).
  inversion TEF. subst. 
  destruct vf; simpl in VF; intuition.
  eapply type_eval_unique in TEX; eauto. subst V1.
  edestruct VF as (vy & STY & VY). eauto. 
  exists vy, V2. split. 2: split. 
  - destruct STF as (n1 & STF).
    destruct STX as (n2 & STX).
    destruct STY as (n3 & STY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite STF, STX, STY. 2,3,4: lia.
    eauto.
  - eauto.
  - eauto.
Qed.


Lemma sem_abs: forall G V J t T1 T2,
    sem_type (T1::G) V t T2 ->
    sem_kind J T1 T1 KTpe ->
    sem_kind J T2 T2 KTpe ->
    env_kind V V J ->
    sem_type G V (tabs t) (TFun T1 T2).
Proof.
  intros ? ? ? ? ? ? HY W2 W1 WKE. intros H WFE.
  edestruct W1 as (T1' & V1 & N1L & N1R & VK). eauto. 
  edestruct W2 as (T2' & V2 & N2L & N2R & VK2). eauto. 
  eapply type_eval_unique in N1L. 2: eauto. subst. 
  eapply type_eval_unique in N2L. 2: eauto. subst. 
  eexists _,_. split. 2: split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - econstructor. eauto. eauto.
  - simpl. intros vx VX.
    edestruct HY as (vy & TY' & ? & ? & ?). eapply envt_extend; eauto.
    eapply type_eval_unique in N1R. 2: eauto. subst.     
    exists vy. split. eauto. eauto. 
Qed.


Lemma valt_equiv: forall T1 T2 v,
    type_kind T1 T2 KTpe ->
    val_type v T1 <-> val_type v T2.
Proof.
  intros T1. induction T1; destruct v,T2; simpl in *; intuition; try contradiction.
  - edestruct H as (?&?&?). eapply IHT1_1. eauto. eauto.
    eexists. split. eauto. eapply IHT1_2. eauto. eauto. 
  - edestruct H as (?&?&?). eapply IHT1_1. eauto. eauto.
    eexists. split. eauto. eapply IHT1_2. eauto. eauto. 
Qed.

Lemma sem_equiv: forall G V J t T1 T2,
    sem_type G V t T1 ->
    sem_kind J T1 T2 KTpe ->
    env_kind V V J ->
    sem_type G V t T2.
Proof.
  intros ?????? HX KX WKE. intros H WFE.
  edestruct HX as (vx & T1' & A & B & VX). eauto.
  edestruct KX as (T1'' & T2' & ? & ? & ?). eauto.
  eapply type_eval_unique in B; eauto. subst.   
  eexists vx, T2'. split. 2: split. 
  - eauto.
  - eauto.
  - eapply valt_equiv in H2. eapply H2. eauto.
Qed.

                                                       
(* ---------- LR fundamental property  ---------- *)

Theorem fundamental: forall G V J t T,
    has_type G J t T ->
    env_kind V V J ->
    sem_type G V t T.
Proof.
  intros ? ? ? ? ? W U. 
  induction W.
  - eapply sem_true; eauto.
  - eapply sem_false; eauto.
  - eapply sem_var; eauto.
  - eapply sem_abs; eauto.
    eapply has_kind_fundamental. eauto.
    eapply has_kind_fundamental. eauto. 
  - eapply sem_app; eauto. 
  - eapply sem_equiv; eauto.
    eapply eq_type_fundamental. eauto.
Qed.

Corollary safety: forall t T,
  has_type [] [] t T ->
  exp_type [] [] t T.
Proof. 
  intros. eapply fundamental in H as ST; eauto.
  edestruct (ST []) as (v & T' & ? & ?). eapply envt_empty.
  exists v, T'. intuition. eapply envk_empty. 
Qed.

End STLC.
