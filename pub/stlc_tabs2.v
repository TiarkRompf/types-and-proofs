(* Full safety for STLC *)

(*

An LR-based termination and semantic soundness proof for STLC.

Canonical big-step cbv semantics.

Type abstraction and application (System F)

Notes:

- has_type does not guarantee closedness of T (this is not
  necessary in the proof, but would be cleaner to add)

- val_type needs a size measure on types (due to substitution)
  This can be done using Coq's Program Fixpoint or Function,
  or in a more pedestrian way as done here

- Weakening and substitution can probably be simplified


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
  | TVarB  : id -> ty (* var bound in TAll *)
  | TFun   : ty -> ty -> ty
  | TAll   : ty -> ty
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
Definition tenv := list (ty). (* None means type variable, Some T means term variable *)
Definition kenv := list (unit). (* None means type variable, Some T means term variable *)

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.
#[global] Hint Unfold kenv.


(* ---------- locally nameless ---------- *)

(* T1 [TVar 0 -> T2] *)
Fixpoint open T1 n T2: ty :=
  match T1 with
  | TBool => TBool
  | TVar m => TVar m
  | TVarB m => if n =? m then T2 else if n <? m then TVarB (m-1) else TVarB m
  | TFun T3 T4 => TFun (open T3 n T2) (open T4 n T2)
  | TAll T4 => TAll (open T4 (S n) T2)
  end.

Fixpoint closed T n :=
  match T with
  | TBool => True
  | TVar x => x < n
  | TVarB x => True
  | TFun T3 T4 => closed T3 n /\ closed T4 n
  | TAll T4 => closed T4 n
  end.

Fixpoint closedB T n :=
  match T with
  | TBool => True
  | TVar x => True
  | TVarB x => x < n
  | TFun T3 T4 => closedB T3 n /\ closedB T4 n
  | TAll T4 => closedB T4 (S n)
  end.

Fixpoint splice n (T : ty) {struct T} : ty :=
  match T with
  | TBool => TBool
  | TVar x => if n <=? x then TVar (S x) else TVar x
  | TVarB x => TVarB x
  | TFun T3 T4 => TFun (splice n T3) (splice n T4)
  | TAll T2   => TAll (splice n T2)
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
    closed T2 (length J) -> (* TODO: get from first? *)
    has_type env J (tabs t) (TFun T1 T2)
| t_tapp: forall env J f (* t *) T1 T2,
    has_type env J f (TAll T2) ->
    closed T1 (length J) ->
    closedB T1 0 ->
    has_type env J (ttapp f T1) (open T2 0 T1)
| t_tabs: forall env J t T2,
    has_type env (tt::J) t (open T2 0 (TVar (length J))) ->
    closed T2 (length J) -> (* TODO: get from first? *)
    has_type env J (ttabs t) (TAll T2)
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

Fixpoint tsize T :=
  match T with
  | TBool => 1
  | TVar x => 1
  | TVarB x => 1
  | TFun T1 T2 => 1+tsize T1 + tsize T2
  | TAll T2 => 1+tsize T2
  end.


Definition vtype := vl -> Prop.

Definition vtnone: vtype := fun v => False. 


Fixpoint val_typen n (V: list vtype) v T {struct n}: Prop :=
  match v, T, n with
  | vbool b, TBool, S n =>  
      True
  | v, TVar x, S n =>
      exists vt, 
      indexr x V = Some vt /\ vt v
  | vabs H ty, TFun T1 T2, S n =>
      closed T1 (length V) /\
      closed T2 (length V) /\
      forall vx nx,
        n-nx = tsize T1 ->
        val_typen (n-nx) V vx T1 ->
        exists vy ny,
          tevaln (vx::H) ty vy /\
          n-ny = tsize T2 /\
          val_typen (n-ny) V vy T2
  | vtabs H ty, TAll T2, S n =>
      closed T2 (length V) /\
      forall vt,
        exists vy ny,
          tevaln H ty vy /\
          n-ny = tsize T2 /\
          val_typen (n-ny) (vt::V) vy (open T2 0 (TVar (length V)))
  | _,_, n =>
      False
  end.

Definition val_type V v T := exists n, n = tsize T /\ val_typen n V v T.


Definition exp_type H V t T :=
  exists v,
    tevaln H t v /\
    val_type V v T.

Definition env_type (H: venv) (G: tenv) (V: list vtype) (J: kenv) :=
  length H = length G /\
  length V = length J /\
    forall x T,
      indexr x G = Some T ->
      exists v,
        indexr x H = Some v /\
        val_type V v T.

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




(* ---------- helper lemmas: tsize, open/close/subst  ---------- *)

Lemma tsize_non_zero: forall T2,
    tsize T2 > 0.
Proof.
  induction T2; intros; simpl; eauto. lia. 
Qed.

Lemma tsize_open: forall T2 n x,
    tsize T2 = tsize (open T2 n (TVar x)).
Proof.
  induction T2; intros; simpl; eauto.
  bdestruct (n =? i); simpl; eauto.
  bdestruct (n <? i); simpl; eauto.
Qed.

Lemma tsize_splice: forall T2 n,
    tsize T2 = tsize (splice n T2).
Proof.
  induction T2; intros; simpl; eauto.
  bdestruct (n <=? i); simpl; eauto.
Qed.

Lemma tsize_open': forall T2 T1 n,
    tsize T2 <= tsize (open T2 n T1).
Proof.
  intros T2. induction T2; intros; simpl; eauto.
  - bdestruct (n =? i). assert (forall n, n > 0 -> 1 <= n). intros. lia.
    eapply H0. eapply tsize_non_zero.
    bdestruct (n <? i). simpl. eauto. simpl. eauto. 
  - specialize (IHT2_1 T1 n). specialize (IHT2_2 T1 n). lia. 
  - specialize (IHT2 T1 (S n)). lia. 
Qed.


Lemma valt_closed: forall n V v T,
    val_typen n V v T -> closed T (length V).
Proof.
  intros.
  destruct n, v, T; simpl in *; try contradiction; eauto.
  - destruct H as (? & ? & ?).
    eapply indexr_var_some'. eauto.
  - destruct H as (? & ? & ?).
    eapply indexr_var_some'. eauto.
  - intuition.
  - destruct H as (? & ? & ?).
    eapply indexr_var_some'. eauto.
  - intuition.
Qed.


Lemma closedt_extend: forall T1 n n1,
    closed T1 n -> n <= n1 ->
    closed T1 n1.
Proof.
  intros. induction T1; simpl in *; eauto. 
  - lia. 
  - intuition.
Qed.

Lemma closedB_extend: forall T1 n n1,
    closedB T1 n -> n <= n1 ->
    closedB T1 n1.
Proof.
  intros T1. induction T1; intros; simpl in *; eauto. 
  - lia. 
  - intuition eauto. 
  - eapply IHT1. eauto. lia. 
Qed.

Lemma closedt_splice: forall T1 n n1,
    closed T1 n1 -> 
    closed (splice n T1) (S n1).
Proof.
  intros. induction T1; simpl in *; eauto.
  - bdestruct (n <=? i). simpl. lia. simpl. lia.
  - intuition.
Qed.

Lemma closedt_open'': forall T1 T2 n n1,
    closed (open T1 n T2) n1 ->
    closed T1 n1.
Proof.
  intros T1. induction T1; simpl in *; eauto.
  - intuition. eapply IHT1_1. eauto. eapply IHT1_2. eauto. 
Qed.

Lemma splice_open: forall T1 n2 n1 T2,
    splice n1 (open T1 n2 T2) = open (splice n1 T1) n2 (splice n1 T2).
Proof.
  intros T1. induction T1; intros; simpl in *; eauto.
  - bdestruct (n1 <=? i). simpl. eauto. simpl. eauto.
  - bdestruct (n2 =? i). eauto.
    bdestruct (n2 <? i). simpl. eauto. simpl. eauto.
  - rewrite IHT1_1, IHT1_2. eauto.
  - rewrite IHT1. eauto.
Qed.

Lemma closedB_open: forall T1 n1 T2,
    closedB T1 n1 ->
    (open T1 n1 T2) = T1.
Proof.
  intros T1. induction T1; intros; simpl in *; eauto.
  - bdestruct (n1 =? i). lia. 
    bdestruct (n1 <? i). lia. eauto. 
  - intuition. rewrite IHT1_1, IHT1_2; eauto.
  - rewrite IHT1; eauto. 
Qed.

Lemma closed_open: forall T1 n1 n2 T2,
    closed T1 n1 ->
    closed T2 n1 ->
    closed (open T1 n2 T2) n1.
Proof.
  intros T1. induction T1; intros; simpl in *; eauto.
  - bdestruct (n2 =? i). eauto.
    bdestruct (n2 <? i). eauto. eauto.
  - intuition.
Qed.

Lemma closed_splice: forall T1 n1 n2,
    closed T1 n1 ->
    n1 <= n2 ->
    splice n2 T1 = T1.
Proof.
  intros T1. induction T1; intros; simpl in *; eauto.
  - bdestruct (n2 <=? i). lia. eauto.
  - intuition. erewrite IHT1_1, IHT1_2. eauto.
    eauto. eauto. eauto. eauto.
  - erewrite IHT1. eauto. eauto. eauto.
Qed.

Lemma open_comm: forall T1 T2 T3 n,
    closedB T3 n -> 
    closedB T2 n -> 
    open (open T1 (S n) T2) n T3 = open (open T1 n T3) n T2.
Proof.
  intros T1. induction T1; intros; simpl in *; eauto.
  - simpl. destruct i. simpl.
    + bdestruct (n =? 0). 
      rewrite closedB_open. eauto. eapply closedB_extend. eauto. eauto.
      simpl. bdestruct (n =? 0). lia. eauto.
    + bdestruct (n =? i); bdestruct (n =? S i); try lia.
      * bdestruct (n <? S i). 2: lia. simpl. 
        bdestruct (n =? i-0). 2: lia.
        rewrite closedB_open. eauto. eapply closedB_extend. eauto. eauto.
      * bdestruct (S n <? S i). lia. simpl.
        bdestruct (n =? S i). 2: lia.
        rewrite closedB_open. eauto. eapply closedB_extend. eauto. eauto.
      * bdestruct (S n <? S i); bdestruct (n <? S i); try lia. simpl. 
        bdestruct (n =? i-0). lia.
        bdestruct (n <? i-0). 2: lia. eauto. simpl.
        bdestruct (n =? S i). lia.
        bdestruct (n <? S i). lia. eauto.
  - erewrite IHT1_1, IHT1_2; eauto.
  - erewrite IHT1; eauto. eapply closedB_extend; eauto. eapply closedB_extend; eauto. 
Qed.



(* ---------- helper lemmas: valt_weaken, subst, open  ---------- *)

(* we prove several different variations *)

Lemma valt_weaken: forall m, forall n, n < m -> forall V V1 vt v T,
    closed T (length (V1++V)) -> 
    val_typen n (V1++V) v T <-> val_typen n (V1++vt::V) v (splice (length V) T).
Proof.
  intros m. induction m; intros. lia. destruct n.
  destruct v,T; simpl in *; intuition.
  bdestruct (length V <=? i); eauto.
  bdestruct (length V <=? i); eauto.
  bdestruct (length V <=? i); eauto. 
  destruct T.
  - destruct v; simpl in *; split; eauto.
  - simpl in *. bdestruct (length V <=? i); eauto; split; intros; eauto.
    + replace (i+1) with (S i). 2: lia. erewrite <-indexr_insert_ge. 2: simpl; lia. eauto.
    + replace (i+1) with (S i) in H2. 2: lia. erewrite <-indexr_insert_ge in H2. 2: simpl; lia. eauto.
    + erewrite <-indexr_insert_lt. 2: eauto. eauto.
    + erewrite <-indexr_insert_lt in H2. 2: eauto. eauto.
  - simpl in *. split; eauto.
  - destruct v; simpl in *; split; intros; eauto.
    + replace (length (V1 ++ vt :: V)) with (S (length (V1++V))).
      2: { repeat rewrite app_length. simpl. lia. }
      intuition.
      eapply closedt_splice. eauto. 
      eapply closedt_splice. eauto.
      destruct (H5 vx nx) as (vy & ny & ? & ? & VY). erewrite tsize_splice. eauto. 
      assert (n-nx < m) as LT. lia. 
      edestruct (IHm (n-nx) LT V V1 vt vx T1) as (IH1 & IH2); eauto.
      exists vy, ny. split. 2: split. eauto. rewrite <-tsize_splice. eauto. 
      assert (n-ny < m) as LT. lia. 
      edestruct (IHm (n-ny) LT V (V1) vt vy T2) as (IH1 & IH2); eauto.
    + replace (length (V1 ++ vt :: V)) with (S (length (V1++V))) in H1.
      2: { repeat rewrite app_length. simpl. lia. }
      intuition.
      destruct (H5 vx nx) as (vy & ny & ? & ? & VY). erewrite <-tsize_splice. eauto. 
      assert (n-nx < m) as LT. lia. 
      edestruct (IHm (n-nx) LT V V1 vt vx T1) as (IH1 & IH2); eauto.
      exists vy, ny. split. 2: split. eauto. erewrite tsize_splice. eauto. 
      assert (n-ny < m) as LT. lia. 
      edestruct (IHm (n-ny) LT V (V1) vt vy T2) as (IH1 & IH2); eauto.
  - destruct v; simpl in *; split; intros; eauto.
    + replace (length (V1 ++ vt :: V)) with (S (length (V1++V))).
      2: { repeat rewrite app_length. simpl. lia. }
      intuition.
      eapply closedt_splice. eauto. 
      destruct (H3 vt0) as (vy & ny & ? & ? & VY). 
      exists vy, ny. split. 2: split. eauto. erewrite <-tsize_splice. eauto. 
      assert (n-ny < m) as LT. lia. 
      edestruct (IHm (n-ny) LT V (vt0::V1) vt vy) as (IH1 & IH2).
      2: { eapply IH1 in VY. rewrite splice_open in VY. simpl in VY.
           bdestruct (length V <=? length (V1 ++ V)).
           2: { rewrite app_length in H5. simpl in H5. lia. }
           eapply VY. }
      eapply closed_open. eapply closedt_extend. eauto. simpl. lia. simpl. lia.
    + replace (length (V1 ++ vt :: V)) with (S (length (V1++V))) in H1.
      2: { repeat rewrite app_length. simpl. lia. }
      intuition.
      destruct (H3 vt0) as (vy & ny & ? & ? & VY). 
      exists vy, ny. split. 2: split. eauto. erewrite tsize_splice. eauto. 
      assert (n-ny < m) as LT. lia. 
      edestruct (IHm (n-ny) LT V (vt0::V1) vt vy) as (IH1 & IH2).
      2: { eapply IH2. erewrite splice_open. simpl.
           bdestruct (length V <=? length (V1 ++ V)).
           2: { rewrite app_length in H5. simpl in H5. lia. }
           eapply VY. }
      eapply closed_open. eapply closedt_extend. eauto. simpl. lia. simpl. lia.
Qed.


Lemma valt_shrink: forall V vt v T,
    closed T (length V) -> 
    val_type (vt::V) v T -> val_type V v T.
Proof.
  intros. destruct H0 as (n & ? & ?).
  edestruct valt_weaken with (V:=V) (V1:=@nil vtype).
  2: { simpl. eauto. } eauto.
  eexists. split. eauto. simpl in *. eapply H3. erewrite closed_splice.
  eauto. eauto. eauto. 
Qed.

Lemma valt_extend: forall V vt v T,
    val_type V v T -> val_type (vt::V) v T.
Proof.
  intros. destruct H as (n & ? & ?). eapply valt_closed in H0 as CL.
  edestruct valt_weaken with (V:=V) (V1:=@nil vtype).
  2: { simpl. eauto. } eauto.
  eexists. split. eauto. simpl in *. erewrite <-closed_splice. eapply H1. 
  eauto. eauto. eauto. 
Qed.

(*
Lemma valt_shrink_mult: forall V V1 v T,
    closed T (length V) ->
    val_type (V1++V) v T -> val_type V v T.
Proof.
  intros. induction V1. eauto. eapply IHV1. eapply valt_shrink.
  eapply closedt_extend. eauto. eauto. eauto. 
Qed.

Lemma valt_extend_mult: forall V V1 v T,
    val_type V v T -> val_type (V1++V) v T.
Proof.
  intros. induction V1. eauto. simpl. eapply valt_extend. eauto. 
Qed.
*)


(* we also show a direct proof of substitution expressed via opening.
   note that this one leaves the environment unmodified, whereas
   valt_subst removed the substituted element from the environment. *)
Lemma valt_subst_open_gen: forall m, forall n1 n2, n1 < m -> n2 < m -> forall V vt v x T1 T2,
    n1 = tsize (open T2 0 (TVar x)) ->
    n2 = tsize (open T2 0 T1) ->
    vt = (fun v => val_type V v T1) ->
    closed T1 (length V) -> 
    closed T2 (length V) -> 
    closedB T1 0 ->
    indexr x V = Some vt -> 
    val_typen n1 V v (open T2 0 (TVar x)) <->
    val_typen n2 V v (open T2 0 T1).
Proof.
  intros m. induction m; intros. lia.
  destruct T2; subst n1 n2.
  - destruct v; simpl; split; eauto.
  - simpl. split; eauto.
  - destruct i; simpl.
    + rewrite H7. subst vt. split; intros.
      * destruct v; destruct H1 as (vt' & EQ & VT); inversion EQ; subst;
          destruct VT as (nx' & ? & ?); subst nx'; eauto.
      * destruct v; eexists; split; eauto; simpl; eexists; split; eauto. 
    + split; eauto. 
  - assert (vt = (fun v : vl => val_type (V) v T1)) as VT. {
      eapply functional_extensionality. intros.
      eapply propositional_extensionality. split; intros.
      subst vt. (*eapply valt_extend.*) eauto.
      subst vt. (*eapply valt_shrink in H1;*) eauto.
    }
    simpl. destruct v; split; intros; eauto.
    + destruct H1 as (CL1 & CL2 & HVY). split. 2: split.
      * eapply closed_open. 2: eauto. eapply closedt_open''. eauto.
      * eapply closed_open. 2: eauto. eapply closedt_open''. eauto.
      * intros. destruct (HVY vx (tsize (open T2_2 0 (TVar x)))) as (vy & ny & ? & ? & ?).
        -- lia.
        -- repeat erewrite <-tsize_open in *. simpl in H, H0. 
           edestruct IHm as (IH1 & IH2).
           10: { eapply IH2. eapply H2. }
           lia. lia. erewrite <-tsize_open. lia. lia.
           eauto. eauto. eapply closedt_open''. eauto. eauto. eauto. 
        -- exists vy, (tsize (open T2_1 0 T1)). split. 2: split.
           eauto. lia.
           repeat erewrite <-tsize_open in *. simpl in H, H0. 
           edestruct IHm as (IH1 & IH2).
           10: { eapply IH1. eapply H10. }
           lia. lia. erewrite <-tsize_open. lia. lia.
           reflexivity. eapply closedt_extend. eauto. simpl. eauto. 
           eapply closedt_extend. eapply closedt_open''. eauto. simpl. eauto.
           eauto. (*rewrite indexr_skip.*)
           rewrite <-VT. eauto. (*eapply indexr_var_some' in H7. lia.*)
    + eapply indexr_var_some' in H7 as H8. 
      destruct H1 as (CL1 & CL2 & HVY). split. 2: split.
      * eapply closed_open. eapply closedt_open''. eauto. simpl. eauto. 
      * eapply closed_open. eapply closedt_open''. eauto. simpl. eauto. 
      * intros. destruct (HVY vx (tsize (open T2_2 0 T1))) as (vy & ny & ? & ? & ?).
        -- lia.
        -- repeat erewrite <-tsize_open in *. simpl in H, H0. 
           edestruct IHm as (IH1 & IH2).
           10: { eapply IH1. eapply H2. }
           lia. lia. erewrite <-tsize_open. lia. lia.
           eauto. eauto. eapply closedt_open''. eauto. eauto. eauto. 
        -- exists vy, (tsize (open T2_1 0 (TVar x))). split. 2: split.
           eauto. lia.
           repeat erewrite <-tsize_open in *. simpl in H, H0. 
           edestruct IHm as (IH1 & IH2).
           10: { eapply IH2. eapply H11. }
           lia. lia. erewrite <-tsize_open. lia. lia.
           reflexivity. eapply closedt_extend. eauto. simpl. eauto. 
           eapply closedt_extend. eapply closedt_open''. eauto. simpl. eauto.
           eauto. (*rewrite indexr_skip.*)
           rewrite <-VT. eauto. (*lia.*)
  - simpl. destruct v; split; intros; eauto.
    + destruct H1 as (CL1 & HVY). split.
      * eapply closed_open. eauto. eauto.
      * intros.
        assert (vt = (fun v : vl => val_type (vt0 :: V) v T1)) as VT. {
          eapply functional_extensionality. intros.
          eapply propositional_extensionality. split; intros.
          subst vt. eapply valt_extend. eauto.
          subst vt. eapply valt_shrink in H1; eauto.
        }
        destruct (HVY vt0) as (vy & ny & ? & ? & ?).
        exists vy, 0. split. 2: split.
        eauto. lia.       
        edestruct IHm as (IH1 & IH2).
        10: {
          rewrite open_comm. 2: simpl; eauto. 2: eauto.
          rewrite open_comm in H8. 2: simpl; eauto. 2: simpl; eauto.
          eapply IH1. eapply H8. }
        erewrite <-tsize_open in *. simpl in H, H0. lia. 
        erewrite <-tsize_open in *. simpl in H, H0. lia.
        repeat erewrite <-tsize_open in *. lia.
        erewrite <-open_comm.         
        erewrite <-tsize_open in *. lia.
        simpl. eauto. eauto.
        reflexivity.
        eapply closedt_extend. eauto. simpl. eauto. 
        eapply closed_open. eapply closedt_extend. eauto. simpl. eauto.
        simpl. eauto. eauto. rewrite indexr_skip. rewrite <-VT. eauto.
        eapply indexr_var_some' in H7. lia.
    + eapply indexr_var_some' in H7 as H8.
      destruct H1 as (CL1 & HVY). split.
      * eapply closed_open. simpl in H5. eauto. simpl. eauto. 
      * intros.
        assert (vt = (fun v : vl => val_type (vt0 :: V) v T1)) as VT. {
          eapply functional_extensionality. intros.
          eapply propositional_extensionality. split; intros.
          subst vt. eapply valt_extend. eauto.
          subst vt. eapply valt_shrink in H1; eauto.
        }
        destruct (HVY vt0) as (vy & ny & ? & ? & ?).
        exists vy, 0. split. 2: split.
        eauto. lia.       
        edestruct IHm as (IH1 & IH2).
        10: {
          rewrite open_comm. 2: simpl; eauto. 2: simpl; eauto.
          rewrite open_comm in H9. 2: simpl; eauto. 2: simpl; eauto.
          eapply IH2. eapply H9. }
        erewrite <-tsize_open in *. simpl in H, H0. lia. 
        erewrite <-tsize_open in *. simpl in H, H0. lia.
        repeat erewrite <-tsize_open in *. lia.
        erewrite <-open_comm.         
        erewrite <-tsize_open in *. lia.
        simpl. eauto. eauto.
        reflexivity.
        eapply closedt_extend. eauto. simpl. eauto. 
        eapply closed_open. eapply closedt_extend. eauto. simpl. eauto.
        simpl. eauto. eauto. rewrite indexr_skip. rewrite <-VT. eauto. lia. 
Qed.


Lemma valt_subst_open: forall V vt v T1 T2,
    vt = (fun v => val_type V v T1) ->
    closed T1 (length V) -> 
    closed T2 (length V) -> 
    closedB T1 0 ->
    val_type (vt :: V) v (open T2 0 (TVar (length V))) ->
    val_type V v (open T2 0 T1).
Proof.
  intros. destruct H3 as (n & ? & ?).
  eapply valt_shrink. eapply closed_open; eauto. 
  eexists. split. eauto. eapply valt_subst_open_gen.
  10: { eapply H4. }
  9: { eapply indexr_head. }
  3: eauto. 3: eauto. 6: eauto. 2: eauto.
  subst n. erewrite <-tsize_open.
  assert (tsize T2 <= (tsize (open T2 0 T1))).
  eapply tsize_open'. lia.
  {
    eapply functional_extensionality. intros.
    eapply propositional_extensionality. split; intros.
    subst vt. eapply valt_extend. eauto.
    subst vt. eapply valt_shrink in H5; eauto.
  }
  eapply closedt_extend. eauto. simpl. eauto.
  eapply closedt_extend. eauto. simpl. eauto. 
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
    val_type V v1 T1 ->
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
    env_type E G (vt1::V) (tt::J).
Proof.
  intros. 
  remember H as WFE. clear HeqWFE.
  destruct H as (? & ? & ?). split. 2: split.
  simpl. eauto. simpl. eauto.
  intros x T IX. 
    eapply WFE in IX as IX. destruct IX as (v2 & ? & ?).
    exists v2. split. eauto. 
    eapply valt_extend. eauto. 
Qed.

(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_true: forall G J,
    sem_type G J ttrue TBool.
Proof.
  intros. intros E V WFE. 
  exists (vbool true). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eexists. split. eauto. simpl. eauto. 
Qed.

Lemma sem_false: forall G J,
    sem_type G J tfalse TBool.
Proof.
  intros. intros E V WFE. 
  exists (vbool false). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eexists. split. eauto. simpl. eauto. 
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

Lemma sem_app: forall G J f t T1 T2,
    sem_type G J f (TFun T1 T2) ->
    sem_type G J t T1 ->
    sem_type G J (tapp f t) T2.
Proof.
  intros ? ? ? ? ? ? HF HX. intros E V WFE.
  destruct (HF E V WFE) as (vf & STF & VF).
  destruct (HX E V WFE) as (vx & STX & VX).
  destruct vf; destruct VF as ([|nf] & ? & VF); simpl in VF; try contradiction.
  destruct VF as (CL1 & CL2 & VF). 
  destruct VX as (nx & ? & VX). 
  edestruct (VF vx (tsize T2)) as (vy & ny & STY & SZY & VY).
  simpl in H. lia. 
  replace nx with (nf - (tsize T2)) in VX.
  2: { simpl in H. lia. } eapply VX.
  exists vy. split.
  - destruct STF as (n1 & STF).
    destruct STX as (n2 & STX).
    destruct STY as (n3 & STY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite STF, STX, STY. 2,3,4: lia.
    eauto.
  - eexists. split; eauto. 
Qed.

Lemma sem_abs: forall G J t T1 T2,
    sem_type (T1::G) J t T2 ->
    closed T1 (length J) ->
    closed T2 (length J) -> (* TODO: get from HY ? *)
    sem_type G J (tabs t) (TFun T1 T2).
Proof.
  intros ? ? ? ? ? HY CL1 CL2. intros E V WFE.
  assert (length E = length G) as L. eapply WFE.
  assert (length V = length J) as LV. eapply WFE.
  exists (vabs E t). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eexists. split. eauto. split. 2: split.
    rewrite LV. eauto. rewrite LV. eauto. 
    intros ? ? ? ?.
    edestruct HY as (? & ? & ?). eapply envt_extend; eauto.
    eexists. split. eauto. eauto.
    destruct H2 as (? & ? & ?).
    eexists. exists (tsize T1). split. 2: split.
    eauto. lia. subst x0.
    replace (0 + tsize T1 + tsize T2 - tsize T1) with (tsize T2). 2: lia.
    eauto.
Qed.

Lemma sem_tapp: forall G J f (* t *) T1 T2,
    sem_type G J f (TAll T2) ->
    closed T1 (length J) ->
    closedB T1 0 ->
    sem_type G J (ttapp f T1) (open T2 0 T1).
Proof. 
  intros ? ? ? ? ? HF CL1 CLB1. intros E V WFE.
  destruct (HF E V WFE) as (vf & STF & VF).
  destruct vf; destruct VF as ([|nf] & ? & VF); simpl in VF; try contradiction.
  destruct VF as (CL2 & VF). 
  edestruct VF as (vy & ny & STY & SZY & VY). 
  exists vy. split.
  - destruct STF as (n1 & STF).
    destruct STY as (n3 & STY).
    exists (1+n1+n3). intros. destruct n. lia.
    simpl. rewrite STF, STY. 2,3: lia.
    eauto.
  - eapply valt_subst_open. reflexivity.
    replace (length V) with (length J). eauto. symmetry. eapply WFE. eauto. eauto.
    eexists. split. eauto.
    erewrite <-tsize_open, <-SZY. eapply VY. 
Qed.


Lemma sem_tabs: forall G J t T2,
    sem_type G (tt::J) t (open T2 0 (TVar (length J))) ->
    closed T2 (length J) ->
    sem_type G J (ttabs t) (TAll T2).
Proof.
  intros ? ? ? ? HY CL2. intros E V WFE.
  assert (length E = length G) as L. eapply WFE.
  assert (length V = length J) as LV. eapply WFE.
  exists (vtabs E t). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eexists. split. eauto. simpl. split. rewrite LV. eauto. intros.
    destruct (HY (E) (vt::V)) as (? & ? & ?). eapply envt_extend_tabs; eauto.
    destruct H0 as (? & ? & ?).
    eexists. exists 0. split. 2: split.
    eauto. lia.
    replace (tsize T2 - 0) with (tsize T2). 2: lia.
    replace (tsize T2) with (tsize (open T2 0 (TVar (length J)))). 2: { symmetry. eapply tsize_open. }
    subst x0. rewrite LV. eauto. 
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


(* ---------- examples  ---------- *)

(* polymorphic id function: [T:*](x:T) -> T  *)

Definition polyId := ttabs (tabs (tvar 0)). 

Definition polyIdType := TAll (TFun (TVarB 0) (TVarB 0)). 

Lemma polyIdHasType:
  has_type [] [] polyId polyIdType.
Proof.
  eapply t_tabs. eapply t_abs. eapply t_var.
  simpl. eauto. simpl. eauto. simpl. eauto. simpl. eauto.
Qed.

Lemma polyIdAppliedHasType:
  has_type [] [] (ttapp polyId TBool) (TFun TBool TBool).
Proof.
  replace (TFun TBool TBool) with (open (TFun (TVarB 0) (TVarB 0)) 0 TBool). 
  eapply t_tapp. eapply polyIdHasType. simpl. eauto. simpl. eauto.
  simpl. eauto.
Qed.


End STLC.
