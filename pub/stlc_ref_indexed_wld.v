(* Full safety for STLC *)

(*

An LR-based semantic soundness proof for STLC.

Step-indexed LR: soundness only, no termination.

Full higher-order mutable references (TRef T, for any T)

This is a variant of stlc_ref_indexed.v. The language, the typing rules
and the evaluator are the same. The logical relation uses a different
model of store typings: the finite stratified tower of Ahmed (2004).

  stty 0     = unit
  stty (S k) = stty k * list (stty k -> vl -> Prop)

A world at level k holds one store typing for each level below k. A
semantic type at level S k is a predicate over worlds at level k.
To approximate a world one level down, take its first component
(stty_pred). This is exact, so the model needs no physical/logical
approximation functions and no coherence conditions (istypeC,
isstoretypeD). It also needs no axioms (no functional or propositional
extensionality).

  - st_chain k M j M'     : M' (at level j <= k) extends M.
  - store_type k M S      : the store S is well-formed for M, at every level.
  - val_type T k M v      : value interpretation, by structural recursion on T.
  - stty_has k M l A      : location l has type A at every level of M.

A reference value pins its store entry separately at every level j < k:
in every extension M' of M at level S j, the entry is exactly
val_type A j. This takes the place of vtyp_equiv and istypeC.

*)

Require Import Coq.Lists.List.
Require Import Psatz.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Require Import tactics.
Require Import env.

Module STLC.

(* ---------- language syntax ---------- *)

Definition id := nat.

Inductive ty : Type :=
  | TBool  : ty
  | TRef   : ty -> ty
  | TFun   : ty -> ty -> ty
.


Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tref : tm -> tm
  | tget : tm -> tm
  | tput : tm -> tm -> tm
  | tapp : tm -> tm -> tm
  | tabs : tm -> tm
.

Inductive vl: Type :=
| vbool :  bool -> vl
| vref  :  id -> vl
| vabs  :  list vl -> tm -> vl 
.

Definition venv := list vl.
Definition tenv := list ty.

Definition stor := list vl.

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.
#[global] Hint Unfold stor.


(* ---------- syntactic typing rules ---------- *)

Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
    has_type env ttrue TBool
| t_false: forall env,
    has_type env tfalse TBool
| t_var: forall x env T,
    indexr x env = Some T ->
    has_type env (tvar x) T
| t_ref: forall t env T,
    has_type env t T ->
    has_type env (tref t) (TRef T)
| t_get: forall t env T,
    has_type env t (TRef T) ->
    has_type env (tget t) T
| t_put: forall t t2 env T,
    has_type env t (TRef T) ->
    has_type env t2 T ->
    has_type env (tput t t2) TBool
| t_app: forall env f t T1 T2,
    has_type env f (TFun T1 T2) ->
    has_type env t T1 ->
    has_type env (tapp f t) T2
| t_abs: forall env t T1 T2,
    has_type (T1::env) t T2 ->
    has_type env (tabs t) (TFun T1 T2)
.

(* ---------- operational semantics ---------- *)

Fixpoint teval(n: nat)(M:stor)(env: venv)(t: tm){struct n}: nat * stor * option (option vl) :=
  match n with
    | 0 => (0, M, None)
    | S n =>
      match t with
        | ttrue      => (1, M, Some (Some (vbool true)))
        | tfalse     => (1, M, Some (Some (vbool false)))
        | tvar x     => (1, M, Some (indexr x env))
        | tref ex    =>
          match teval n M env ex with
            | (dx, M', None)           => (1+dx, M', None)
            | (dx, M', Some None)      => (1+dx, M', Some None)
            | (dx, M', Some (Some vx)) => (1+dx, vx::M', Some (Some (vref (length M'))))
          end
        | tget ex    =>
          match teval n M env ex with
            | (dx, M', None)                     => (1+dx, M', None)
            | (dx, M', Some None)                => (1+dx, M', Some None)
            | (dx, M', Some (Some (vbool _)))    => (1+dx, M', Some None)
            | (dx, M', Some (Some (vabs _ _)))   => (1+dx, M', Some None)
            | (dx, M', Some (Some (vref x)))     => (1+dx, M', Some (indexr x M'))
          end
        | tput er ex    =>
          match teval n M env er with
            | (dr, M', None)                     => (1+dr, M', None)
            | (dr, M', Some None)                => (1+dr, M', Some None)
            | (dr, M', Some (Some (vbool _)))    => (1+dr, M', Some None)
            | (dr, M', Some (Some (vabs _ _)))   => (1+dr, M', Some None)
            | (dr, M', Some (Some (vref x))) =>
              match teval (n-dr) M' env ex with
                | (dx, M'', None)                => (1+dr+dx, M'', None)
                | (dx, M'', Some None)           => (1+dr+dx, M'', Some None)
                | (dx, M'', Some (Some vx)) =>
                    match indexr x M'' with
                    | Some v => (1+dr+dx, update M'' x vx, Some (Some (vbool true)))
                    | _      => (1+dr+dx, M'', Some None)
                    end
              end
          end
        | tabs y   => (1, M, Some (Some (vabs env y)))
        | tapp ef ex =>
          match teval n M env ef with
            | (df, M', None)                  => (1+df, M', None)
            | (df, M', Some None)             => (1+df, M', Some None)
            | (df, M', Some (Some (vbool _))) => (1+df, M', Some None)
            | (df, M', Some (Some (vref _)))  => (1+df, M', Some None)
            | (df, M', Some (Some (vabs env2 ey))) =>
              match teval (n-df) M' env ex with
                | (dx, M'', None)           => (1+df+dx, M'', None)
                | (dx, M'', Some None)      => (1+df+dx, M'', Some None)
                | (dx, M'', Some (Some vx)) =>
                  match teval (n-df-dx) M'' (vx::env2) ey with
                    | (dy, M''', ry) => (1+df+dx+dy, M''', ry)
                  end
              end
          end
      end
  end.


(* value interpretation of terms *)
Definition tevaln M env e M' v :=
  exists nm,
  forall n,
    n > nm ->
    teval n M env e = (M', Some (Some v)).

Lemma eval_deterministic: forall m n, n < m -> forall S S1 H t n1 r j,
  teval n S H t = (n1, S1, Some r) -> j >= n -> (* alt: j >= n1 ? *)
  teval j S H t = (n1, S1, Some r).
Proof.
  intros m. induction m. intros. inversion H.
  intros. destruct n. inversion H1. destruct j. inversion H2.
  destruct t; simpl; simpl in H1; try eauto.
  - remember (teval n S H0 t) as tf. destruct tf as [[nf Sf] [rf|]].
    rewrite IHm with (n:=n) (n1:=nf) (r:=rf) (S1:=Sf).
    destruct rf; try destruct v; try solve [inversion H1; eauto].
    lia. eauto. lia.
    inversion H1. 
  - remember (teval n S H0 t) as tf. destruct tf as [[nf Sf] [rf|]].
    rewrite IHm with (n:=n) (n1:=nf) (r:=rf) (S1:=Sf).
    destruct rf; try destruct v; try solve [inversion H1; eauto].
    lia. eauto. lia.
    inversion H1. 
  - remember (teval n S H0 t1) as tf. destruct tf as [[nf Sf] [rf|]].
    rewrite IHm with (n:=n) (n1:=nf) (r:=rf) (S1:=Sf).
    destruct rf; try destruct v; try solve [inversion H1; eauto]. 
    remember (teval (n-nf) Sf H0 t2) as tx. destruct tx as [[nx Sx] [rx|]].
    rewrite IHm with (n:=n-nf) (n1:=nx) (r:=rx) (S1:=Sx).
    destruct rx; try solve [destruct v; inversion H1; eauto].
    eauto. lia. eauto. lia.
    inversion H1. inversion H1.
    lia. eauto. lia.
    inversion H1.
  - remember (teval n S H0 t1) as tf. destruct tf as [[nf Sf] [rf|]].
    rewrite IHm with (n:=n) (n1:=nf) (r:=rf) (S1:=Sf).
    destruct rf; try destruct v; try solve [inversion H1; eauto]. 
    remember (teval (n-nf) Sf H0 t2) as tx. destruct tx as [[nx Sx] [rx|]].
    rewrite IHm with (n:=n-nf) (n1:=nx) (r:=rx) (S1:=Sx).
    destruct rx; try solve [destruct v; inversion H1; eauto].
    remember (teval (n-nf-nx) Sx (v :: l) t) as ty. destruct ty as [[ny Sy] [ry|]].
    rewrite IHm with (n:=n-nf-nx) (n1:=ny) (r:=ry) (S1:=Sy).
    eauto. lia. eauto. lia.
    inversion H1. inversion H1.
    eauto. lia. eauto. lia.
    inversion H1.
    lia. eauto. lia.
    inversion H1.
Qed.

Lemma eval_bounded: forall m n, n < m -> forall S S1 H t n1 r,
    teval n S H t = (n1, S1, Some r) ->
    1 <= n1 /\ n1 <= n.
Proof.
  intros m. induction m. intros. inversion H.
  intros. destruct n. inversion H1.
  destruct t; simpl in *; inversion H1; try lia.
  - remember (teval n S H0 t) as tf. destruct tf as [[nf Sf] [rf|]]. 2: { inversion H1. }
    symmetry in Heqtf. eapply IHm with (n:=n) (n1:=nf) (r:=rf) in Heqtf as HF1. 2: lia.
    destruct rf. 2: { inversion H1. lia. } inversion H1. lia. 
  - remember (teval n S H0 t) as tf. destruct tf as [[nf Sf] [rf|]]. 2: { inversion H1. }
    symmetry in Heqtf. eapply IHm with (n:=n) (n1:=nf) (r:=rf) in Heqtf as HF1. 2: lia.
    destruct rf. 2: { inversion H1. lia. } destruct v; inversion H1; lia. 
  - remember (teval n S H0 t1) as tf. destruct tf as [[nf Sf] [rf|]]. 2: { inversion H1. }
    symmetry in Heqtf. eapply IHm with (n:=n) (n1:=nf) (r:=rf) in Heqtf as HF1. 2: lia.
    destruct rf. 2: { inversion H1. lia. } destruct v. inversion H1. lia.
    remember (teval (n-nf) Sf H0 t2) as tx. destruct tx as [[nx Sx] [rx|]]. 2: inversion H1.
    symmetry in Heqtx. eapply IHm in Heqtx as HX1. 2: lia.
    destruct rx. 2: { inversion H1. lia. }
    remember (indexr i Sx). destruct o. inversion H1. lia. inversion H1. lia. inversion H1. lia. 
  - remember (teval n S H0 t1) as tf. destruct tf as [[nf Sf] [rf|]]. 2: { inversion H1. }
    symmetry in Heqtf. eapply IHm with (n:=n) (n1:=nf) (r:=rf) in Heqtf as HF1. 2: lia.
    destruct rf. 2: { inversion H1. lia. } destruct v; inversion H1; try lia.
    remember (teval (n-nf) Sf H0 t2) as tx. destruct tx as [[nx Sx] [rx|]]. 2: inversion H1. 
    symmetry in Heqtx. eapply IHm in Heqtx as HX1. 2: lia.
    destruct rx. 2: { inversion H1. lia. } inversion H1. 
    remember (teval (n-nf-nx) Sx (v :: l) t) as ty. destruct ty as [[ny Sy] [ry|]].
    symmetry in Heqty. eapply IHm in Heqty as HY1. 2: lia. 2: inversion H1. 
    inversion H1. lia. 
Qed.


Lemma eval_mono: forall n S H t n1 S1 r,
    teval n S H t = (n1, S1, Some r) ->
    forall j, j >= n ->
    teval j S H t = (n1, S1, Some r).
Proof.
  intros. eapply (eval_deterministic (Datatypes.S n) n); eauto.
Qed.

Lemma eval_bound: forall n S H t n1 S1 r,
    teval n S H t = (n1, S1, Some r) ->
    1 <= n1 /\ n1 <= n.
Proof.
  intros. eapply (eval_bounded (Datatypes.S n) n); eauto.
Qed.


(* ---------- store typings: stratified worlds ---------- *)

Fixpoint stty (k: nat): Type :=
  match k with
  | 0 => unit
  | S k => prod (stty k) (list (stty k -> vl -> Prop))
  end.

(* the store typing one level down *)
Definition stty_pred {k} (M: stty (S k)): stty k :=
  @fst (stty k) (list (stty k -> vl -> Prop)) M.

(* the semantic types of the locations, at the top level *)
Definition stty_top {k} (M: stty (S k)): list (stty k -> vl -> Prop) :=
  @snd (stty k) (list (stty k -> vl -> Prop)) M.

(* stores and store typings grow at the head (see indexr) *)
Definition stext {A} (L L': list A) := exists t, L' = t ++ L.

(* st_chain k M j M': M' is an extension of (the level-j part of) M *)
Inductive st_chain: forall k, stty k -> forall j, stty j -> Prop :=
| stchain_zero: forall k (M: stty k) (M': stty 0),
    st_chain k M 0 M'
| stchain_same: forall k (M M': stty (S k)),
    st_chain k (stty_pred M) k (stty_pred M') ->
    stext (stty_top M) (stty_top M') ->
    st_chain (S k) M (S k) M'
| stchain_down: forall k j (M: stty (S k)) (M': stty j),
    st_chain k (stty_pred M) j M' ->
    st_chain (S k) M j M'.

Lemma stchain_refl: forall k (M: stty k), st_chain k M k M.
Proof.
  induction k; intros.
  - apply stchain_zero.
  - apply stchain_same. apply IHk. exists []. reflexivity.
Qed.

Lemma stchain_pred: forall k (M: stty (S k)), st_chain (S k) M k (stty_pred M).
Proof.
  intros. apply stchain_down. apply stchain_refl.
Qed.

Lemma stchain_le: forall k M j M', st_chain k M j M' -> j <= k.
Proof.
  induction 1; lia.
Qed.

(* Small inversion for a source world at level S k. This avoids
   dependent equalities (and the axioms that come with them). *)
Definition stchain_S_motive k: stty k -> forall i, stty i -> Prop :=
  match k with
  | 0 => fun _ _ _ => True
  | S k => fun M i M3 =>
      forall P: forall i, stty i -> Prop,
        (forall M3: stty 0, P 0 M3) ->
        (forall M3: stty (S k),
            st_chain k (stty_pred M) k (stty_pred M3) ->
            stext (stty_top M) (stty_top M3) -> P (S k) M3) ->
        (forall i (M3: stty i), st_chain k (stty_pred M) i M3 -> P i M3) ->
        P i M3
  end.

Lemma stchain_inv: forall k M i M3, st_chain k M i M3 -> stchain_S_motive k M i M3.
Proof.
  intros k M i M3 H. destruct H as [k M M' | k M M' H1 H2 | k j M M' H1].
  - destruct k. exact I. intros P A _ _. apply A.
  - intros P _ B _. apply B; auto.
  - intros P _ _ C. apply C; auto.
Qed.

Lemma stchain_trans: forall k M1 j M2, st_chain k M1 j M2 ->
    forall i M3, st_chain j M2 i M3 -> st_chain k M1 i M3.
Proof.
  induction 1 as [k M M' | k M M' H IH Hs | k j M M' H IH]; intros i M3 H23.
  - assert (i = 0) by (apply stchain_le in H23; lia). subst i. apply stchain_zero.
  - apply (stchain_inv _ _ _ _ H23 (fun i M3 => st_chain (S k) M i M3)).
    + intros. apply stchain_zero.
    + intros M3' H1 H2. apply stchain_same. eapply IH; eauto.
      destruct Hs as [t1 E1]. destruct H2 as [t2 E2].
      exists (t2 ++ t1). rewrite E2, E1, app_assoc. reflexivity.
    + intros i' M3' H1. apply stchain_down. eapply IH; eauto.
  - apply stchain_down. eapply IH; eauto.
Qed.


(* ---------- well-formed stores ---------- *)

(* a semantic type is closed under extension of the store typing
   (the same-level counterpart of istypeA in stlc_ref_indexed.v) *)
Definition istypeA k (vt: stty k -> vl -> Prop) :=
  forall (M1 M2: stty k), st_chain k M1 k M2 -> forall v, vt M1 v -> vt M2 v.

(* At every level S k: the store has exactly the locations of the world,
   each stored semantic type is closed under extension, and each
   stored value inhabits its type at level k. *)
Fixpoint store_type (k: nat): stty k -> stor -> Prop :=
  match k return stty k -> stor -> Prop with
  | 0 => fun _ _ => True
  | S k => fun M S =>
      store_type k (stty_pred M) S /\
      length S = length (stty_top M) /\
      forall l vt, indexr l (stty_top M) = Some vt ->
        istypeA k vt /\
        exists v, indexr l S = Some v /\ vt (stty_pred M) v
  end.

Lemma storet_restrict: forall k (M: stty k) S, store_type k M S ->
    forall j, j <= k -> exists M', st_chain k M j M' /\ store_type j M' S.
Proof.
  induction k; intros M S H j Hj.
  - assert (j = 0) by lia. subst j. exists M. split. apply stchain_refl. auto.
  - destruct (Nat.eq_dec j (Datatypes.S k)).
    + subst j. exists M. split. apply stchain_refl. auto.
    + destruct H as [H _]. destruct (IHk _ _ H j ltac:(lia)) as (M' & Hx & Hok).
      exists M'. split. apply stchain_down. auto. auto.
Qed.


(* ---------- LR definitions ---------- *)

(* Structural recursion on T. A reference pins its store entry at every
   level j < k, in every extension of M. *)
Fixpoint val_type (T: ty) (k: nat) (M: stty k) (v: vl) {struct T}: Prop :=
  match T, v with
  | TBool, vbool b =>
      True
  | TRef A, vref l =>
      forall j, j < k -> forall (M': stty (S j)), st_chain k M (S j) M' ->
        indexr l (stty_top M') = Some (fun M'' v' => val_type A j M'' v')
  | TFun A B, vabs H e =>
      forall j, j < k -> forall (M': stty j), st_chain k M j M' ->
      forall vx, val_type A j M' vx ->
      forall S, store_type j M' S ->
      forall n' S' r, teval j S (vx::H) e = (n', S', Some r) ->
        exists M'' vy,
          st_chain j M' (j - n') M'' /\
          store_type (j - n') M'' S' /\
          r = Some vy /\
          val_type B (j - n') M'' vy
  | _, _ =>
      False
  end.

Definition exp_type T k (M: stty k) (H: venv) S t :=
  forall n' S' r,
    teval k S H t = (n', S', Some r) ->
    exists M' v,
      st_chain k M (k - n') M' /\
      store_type (k - n') M' S' /\
      r = Some v /\
      val_type T (k - n') M' v.

Definition env_type k (M: stty k) (H: venv) (G: tenv) :=
  length H = length G /\
    forall x T,
      indexr x G = Some T ->
      exists v,
        indexr x H = Some v /\
        val_type T k M v.

Definition sem_type G t T :=
  forall k (M: stty k) H S,
    env_type k M H G ->
    store_type k M S ->
    exp_type T k M H S t.


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: core.

#[export] Hint Constructors has_type: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.


(* ---------- monotonicity (Kripke + step index, in one lemma) ---------- *)

Lemma valt_mono: forall T k j (M: stty k) (M': stty j),
    st_chain k M j M' ->
    forall v, val_type T k M v -> val_type T j M' v.
Proof.
  intros T k j M M' Hx v Hv. pose proof (stchain_le _ _ _ _ Hx).
  destruct T, v; simpl in *; try contradiction.
  - auto.
  - intros j' Hj' M'' Hx'. apply Hv. lia. eapply stchain_trans; eauto.
  - intros j' Hj' M'' Hx'. apply Hv. lia. eapply stchain_trans; eauto.
Qed.

Lemma envt_mono: forall k j (M: stty k) (M': stty j) H G,
    env_type k M H G ->
    st_chain k M j M' ->
    env_type j M' H G.
Proof.
  intros. destruct H0 as [Hlen Hf]. split. auto.
  intros x T IX. destruct (Hf x T IX) as (v & ? & ?).
  exists v. split. auto. eapply valt_mono; eauto.
Qed.

Lemma envt_empty: forall k M,
    env_type k M [] [].
Proof.
  intros. split. auto. intros. inversion H.
Qed.

Lemma envt_extend: forall k M E G v T,
    env_type k M E G ->
    val_type T k M v ->
    env_type k M (v::E) (T::G).
Proof.
  intros k M E G v T [Hlen Hf] Hv. split. simpl. auto.
  intros x T' IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX. subst T'.
    exists v. rewrite <- Hlen, indexr_head. auto.
  - rewrite indexr_skip in IX. 2: auto.
    destruct (Hf x T' IX) as (v' & ? & ?).
    exists v'. rewrite indexr_skip. auto. lia.
Qed.

(* a result in a world M1 at level m is also good at any lower level j *)
Lemma res_down: forall T k (M: stty k) m (M1: stty m) S r v j,
    st_chain k M m M1 ->
    store_type m M1 S ->
    r = Some v ->
    val_type T m M1 v ->
    j <= m ->
    exists M' v',
      st_chain k M j M' /\
      store_type j M' S /\
      r = Some v' /\
      val_type T j M' v'.
Proof.
  intros. destruct (storet_restrict m M1 S H0 j H3) as (M' & Hx & Hok).
  exists M', v. split. eapply stchain_trans; eauto. split. auto. split. auto.
  eapply valt_mono; eauto.
Qed.


(* ---------- extension and update ---------- *)

(* add a fresh location of type A, at every level *)
Fixpoint stty_extend (k: nat): stty k -> ty -> stty k :=
  match k return stty k -> ty -> stty k with
  | 0 => fun M _ => M
  | S k => fun M A =>
      @pair (stty k) (list (stty k -> vl -> Prop))
        (stty_extend k (stty_pred M) A)
        ((fun M'' v => val_type A k M'' v) :: stty_top M)
  end.

Lemma stchain_extend: forall k M A, st_chain k M k (stty_extend k M A).
Proof.
  induction k; intros.
  - apply stchain_zero.
  - apply stchain_same. exact (IHk (stty_pred M) A).
    exists [fun M'' v => val_type A k M'' v]. reflexivity.
Qed.

Lemma storet_extend: forall k M S A v,
    store_type k M S ->
    val_type A k M v ->
    store_type k (stty_extend k M A) (v :: S).
Proof.
  induction k; intros M S A v H Hv.
  - exact I.
  - destruct H as (HS & Hlen & HS').
    assert (Hx: st_chain k (stty_pred M) k (stty_extend k (stty_pred M) A))
      by apply stchain_extend.
    split. 2: split.
    + exact (IHk _ _ _ _ HS (valt_mono _ _ _ _ _ (stchain_pred _ M) _ Hv)).
    + simpl. unfold stty_top in *. lia.
    + intros l vt Hl.
      change (indexr l ((fun M'' v => val_type A k M'' v) :: stty_top M) = Some vt) in Hl.
      change (istypeA k vt /\
              exists w, indexr l (v :: S) = Some w /\ vt (stty_extend k (stty_pred M) A) w).
      bdestruct (l =? length (stty_top M)).
      * subst l. rewrite indexr_head in Hl. inversion Hl. subst vt.
        split. intros M1 M2 H12 v'. eapply valt_mono; eauto.
        exists v. rewrite <- Hlen, indexr_head. split. auto.
        eapply valt_mono. 2: eauto. apply stchain_down. auto.
      * rewrite indexr_skip in Hl. 2: auto.
        destruct (HS' l vt Hl) as (Hm & w & Hw & Hvt).
        split. auto. exists w. split.
        rewrite indexr_skip. auto. lia.
        eapply Hm; eauto.
Qed.

(* location l has type A at every level of M *)
Fixpoint stty_has (k: nat): stty k -> nat -> ty -> Prop :=
  match k return stty k -> nat -> ty -> Prop with
  | 0 => fun _ _ _ => True
  | S k => fun M l A =>
      stty_has k (stty_pred M) l A /\
      indexr l (stty_top M) = Some (fun M'' v => val_type A k M'' v)
  end.

Lemma stchain_has: forall k M j M', st_chain k M j M' ->
    forall l A, stty_has k M l A -> stty_has j M' l A.
Proof.
  induction 1 as [k M M' | k M M' H IH Hs | k j M M' H IH]; intros l A Hl.
  - exact I.
  - destruct Hl as [Hl1 Hl2]. split. eapply IH; eauto.
    destruct Hs as [t Ht]. rewrite Ht, indexr_skips. exact Hl2.
    eapply indexr_var_some'. eauto.
  - destruct Hl as [Hl1 _]. eapply IH; eauto.
Qed.

Lemma stty_has_ref: forall k M l A,
    stty_has k M l A ->
    val_type (TRef A) k M (vref l).
Proof.
  intros k M l A H j Hj M' Hx.
  destruct (stchain_has _ _ _ _ Hx l A H) as [_ H']. exact H'.
Qed.

(* the fresh location has type A at every level *)
Lemma stty_extend_hit: forall k M S A,
    store_type k M S ->
    stty_has k (stty_extend k M A) (length S) A.
Proof.
  induction k; intros M S A H.
  - exact I.
  - destruct H as (HS & Hlen & _). split.
    + exact (IHk _ _ A HS).
    + change (indexr (length S) ((fun M'' v => val_type A k M'' v) :: stty_top M)
              = Some (fun M'' v => val_type A k M'' v)).
      rewrite Hlen. apply indexr_head.
Qed.

(* same as env.update_indexr_hit, but without axioms *)
Lemma update_hit: forall {A} (S: list A) l v,
    l < length S -> indexr l (update S l v) = Some v.
Proof.
  induction S; simpl; intros. lia.
  destruct (Nat.eqb l (length S)) eqn:E; simpl.
  - rewrite E. auto.
  - rewrite <- update_length, E. apply IHS. apply Nat.eqb_neq in E. lia.
Qed.

Lemma storet_update: forall k M S A l v,
    store_type k M S ->
    val_type (TRef A) k M (vref l) ->
    val_type A k M v ->
    store_type k M (update S l v).
Proof.
  induction k; intros M S A l v H Hr Hv.
  - exact I.
  - destruct H as (HS & Hlen & HS').
    split. 2: split.
    + eapply IHk. eauto.
      eapply valt_mono. apply stchain_pred. eauto.
      eapply valt_mono. apply stchain_pred. eauto.
    + rewrite <- update_length. auto.
    + intros l' vt Hl'. destruct (HS' l' vt Hl') as (Hm & w & Hw & Hvt).
      split. auto.
      bdestruct (l =? l').
      * subst l'.
        assert (htop := Hr k (Nat.lt_succ_diag_r k) M (stchain_refl _ M)).
        rewrite htop in Hl'. injection Hl'. intros. subst vt.
        exists v. split. apply update_hit. eapply indexr_var_some'. eauto.
        eapply valt_mono. apply stchain_pred. eauto.
      * exists w. rewrite update_indexr_miss; auto.
Qed.


(* ---------- LR compatibility lemmas ---------- *)

Lemma sem_true: forall G,
    sem_type G ttrue TBool.
Proof.
  intros G k M E S WFE ST n1 S1 r EV.
  destruct k as [|n]; inversion EV. subst.
  eapply res_down with (M1 := M).
  - apply stchain_refl.
  - eauto.
  - reflexivity.
  - exact I.
  - lia.
Qed.

Lemma sem_false: forall G,
    sem_type G tfalse TBool.
Proof.
  intros G k M E S WFE ST n1 S1 r EV.
  destruct k as [|n]; inversion EV. subst.
  eapply res_down with (M1 := M).
  - apply stchain_refl.
  - eauto.
  - reflexivity.
  - exact I.
  - lia.
Qed.

Lemma sem_var: forall G x T,
    indexr x G = Some T ->
    sem_type G (tvar x) T.
Proof.
  intros G x T IX k M E S WFE ST n1 S1 r EV.
  destruct k as [|n]; inversion EV. subst.
  destruct WFE as [_ WFE]. destruct (WFE x T IX) as (v & IXv & Hv).
  eapply res_down with (M1 := M).
  - apply stchain_refl.
  - eauto.
  - eauto.
  - eauto.
  - lia.
Qed.

Lemma sem_ref: forall G t T,
    sem_type G t T ->
    sem_type G (tref t) (TRef T).
Proof.
  intros G t T HX k M E S WFE ST n1 S1 r1 EV.
  destruct k as [|n]. inversion EV. simpl in EV.
  destruct (teval n S E t) as [[nx Sx] [rx|]] eqn:EVx. 2: inversion EV.
  pose proof (eval_bound _ _ _ _ _ _ _ EVx) as BX.
  destruct (HX (Datatypes.S n) M E S WFE ST nx Sx rx
              (eval_mono _ _ _ _ _ _ _ EVx (Datatypes.S n) ltac:(lia)))
    as (M1 & vx & Hx1 & ST1 & -> & VX).
  inversion EV. subst.
  eapply res_down with (M1 := stty_extend _ M1 T).
  - eapply stchain_trans. eauto. apply stchain_extend.
  - apply storet_extend; auto.
  - reflexivity.
  - apply stty_has_ref. apply stty_extend_hit. auto.
  - lia.
Qed.

Lemma sem_get: forall G t T,
    sem_type G t (TRef T) ->
    sem_type G (tget t) T.
Proof.
  intros G t T HX k M E S WFE ST n1 S1 r1 EV.
  destruct k as [|n]. inversion EV. simpl in EV.
  destruct (teval n S E t) as [[nx Sx] [rx|]] eqn:EVx. 2: inversion EV.
  pose proof (eval_bound _ _ _ _ _ _ _ EVx) as BX.
  destruct (HX (Datatypes.S n) M E S WFE ST nx Sx rx
              (eval_mono _ _ _ _ _ _ _ EVx (Datatypes.S n) ltac:(lia)))
    as (M1 & vx & Hx1 & ST1 & -> & VX).
  destruct vx as [b|l|Hc e]; try (simpl in VX; contradiction).
  inversion EV. subst.
  (* the store entry is good at level n - nx, one below the reference *)
  destruct (storet_restrict _ M1 _ ST1 (Datatypes.S (n - nx)) ltac:(lia))
    as (M1' & Hx1' & ST1').
  assert (htop := VX (n - nx) ltac:(lia) M1' Hx1').
  destruct ST1' as (ST1'' & _ & Hall).
  destruct (Hall l _ htop) as (_ & w & Hw & Hvt).
  eapply res_down with (M1 := stty_pred M1').
  - eapply stchain_trans. eauto. eapply stchain_trans. eauto. apply stchain_pred.
  - eauto.
  - eauto.
  - exact Hvt.
  - lia.
Qed.

Lemma sem_put: forall G t t2 T,
    sem_type G t (TRef T) ->
    sem_type G t2 T ->
    sem_type G (tput t t2) TBool.
Proof.
  intros G t t2 T HX HY k M E S WFE ST n3 S3 r3 EV.
  destruct k as [|n]. inversion EV. simpl in EV.
  destruct (teval n S E t) as [[nx Sx] [rx|]] eqn:EVx. 2: inversion EV.
  pose proof (eval_bound _ _ _ _ _ _ _ EVx) as BX.
  destruct (HX (Datatypes.S n) M E S WFE ST nx Sx rx
              (eval_mono _ _ _ _ _ _ _ EVx (Datatypes.S n) ltac:(lia)))
    as (M1 & vx & Hx1 & ST1 & -> & VX).
  pose proof VX as VX0.
  destruct vx as [b|l|Hc e]; try (simpl in VX; contradiction).
  destruct (teval (n - nx) Sx E t2) as [[ny Sy] [ry|]] eqn:EVy. 2: inversion EV.
  pose proof (eval_bound _ _ _ _ _ _ _ EVy) as BY.
  destruct (HY (Datatypes.S n - nx) M1 E Sx (envt_mono _ _ _ _ _ _ WFE Hx1) ST1 ny Sy ry
              (eval_mono _ _ _ _ _ _ _ EVy (Datatypes.S n - nx) ltac:(lia)))
    as (M2 & vy & Hx2 & ST2 & -> & VY).
  (* the location is in the store, at level n - nx - ny *)
  destruct (storet_restrict _ M2 Sy ST2 (Datatypes.S (n - nx - ny)) ltac:(lia))
    as (M2' & Hx2' & ST2').
  assert (htop := VX (n - nx - ny) ltac:(lia) M2' (stchain_trans _ _ _ _ Hx2 _ _ Hx2')).
  assert (l < length Sy) as Hlt.
  { destruct ST2' as (_ & Hlen & _). rewrite Hlen. eapply indexr_var_some'. eauto. }
  destruct (proj2 (indexr_var_some (xs := Sy)) Hlt) as (w & Hw).
  simpl in EV. rewrite Hw in EV. inversion EV. subst.
  eapply res_down with (M1 := M2').
  - eapply stchain_trans. eauto. eapply stchain_trans; eauto.
  - eapply storet_update. eauto.
    eapply valt_mono. 2: eauto. eapply stchain_trans; eauto.
    eapply valt_mono; eauto.
  - reflexivity.
  - exact I.
  - lia.
Qed.

Lemma sem_app: forall G f t T1 T2,
    sem_type G f (TFun T1 T2) ->
    sem_type G t T1 ->
    sem_type G (tapp f t) T2.
Proof.
  intros G f t T1 T2 HF HX k M E S WFE ST n3 S3 r3 EV.
  destruct k as [|n]. inversion EV. simpl in EV.
  (* function *)
  destruct (teval n S E f) as [[nf S1] [rf|]] eqn:EVf. 2: inversion EV.
  pose proof (eval_bound _ _ _ _ _ _ _ EVf) as BF.
  destruct (HF (Datatypes.S n) M E S WFE ST nf S1 rf
              (eval_mono _ _ _ _ _ _ _ EVf (Datatypes.S n) ltac:(lia)))
    as (M1 & vf & Hx1 & ST1 & -> & VF).
  destruct vf as [b|l|Hc e]; try (simpl in VF; contradiction).
  (* argument *)
  destruct (teval (n - nf) S1 E t) as [[nx S2] [rx|]] eqn:EVx. 2: inversion EV.
  pose proof (eval_bound _ _ _ _ _ _ _ EVx) as BX.
  destruct (HX (Datatypes.S n - nf) M1 E S1 (envt_mono _ _ _ _ _ _ WFE Hx1) ST1 nx S2 rx
              (eval_mono _ _ _ _ _ _ _ EVx (Datatypes.S n - nf) ltac:(lia)))
    as (M2 & vx & Hx2 & ST2 & -> & VX).
  (* body *)
  simpl in EV.
  destruct (teval (n - nf - nx) S2 (vx :: Hc) e) as [[ny S4] ry] eqn:EVy.
  inversion EV. subst.
  destruct (storet_restrict _ M2 S2 ST2 (n - nf - nx) ltac:(lia)) as (M2' & Hx2' & ST2').
  destruct (VF (n - nf - nx) ltac:(lia) M2' (stchain_trans _ _ _ _ Hx2 _ _ Hx2')
              vx (valt_mono _ _ _ _ _ Hx2' _ VX) _ ST2' _ _ _ EVy)
    as (M3 & vy & Hx3 & ST3 & -> & VY).
  eapply res_down with (M1 := M3).
  - eapply stchain_trans. eauto. eapply stchain_trans. eauto. eapply stchain_trans; eauto.
  - eauto.
  - reflexivity.
  - eauto.
  - lia.
Qed.

Lemma sem_abs: forall G t T1 T2,
    sem_type (T1::G) t T2 ->
    sem_type G (tabs t) (TFun T1 T2).
Proof.
  intros G t T1 T2 HY k M E S WFE ST n1 S1 r1 EV.
  destruct k as [|n]; inversion EV. subst.
  eapply res_down with (M1 := M).
  - apply stchain_refl.
  - eauto.
  - reflexivity.
  - intros j Hj M' Hx vx Hvx S' HS' n' S'' r EVy.
    exact (HY j M' (vx::E) S' (envt_extend _ _ _ _ _ _ (envt_mono _ _ _ _ _ _ WFE Hx) Hvx)
              HS' n' S'' r EVy).
  - lia.
Qed.


(* ---------- LR fundamental property ---------- *)

Theorem fundamental: forall G t T,
    has_type G t T ->
    sem_type G t T.
Proof.
  intros ? ? ? W.
  induction W.
  - eapply sem_true; eauto.
  - eapply sem_false; eauto.
  - eapply sem_var; eauto.
  - eapply sem_ref; eauto.
  - eapply sem_get; eauto.
  - eapply sem_put; eauto.
  - eapply sem_app; eauto.
  - eapply sem_abs; eauto.
Qed.

Fixpoint stty_empty (k: nat): stty k :=
  match k with
  | 0 => tt
  | S k => @pair (stty k) (list (stty k -> vl -> Prop)) (stty_empty k) []
  end.

Lemma storet_empty: forall k, store_type k (stty_empty k) [].
Proof.
  induction k.
  - exact I.
  - split. exact IHk. split. reflexivity. intros l vt H. inversion H.
Qed.

Corollary safety: forall t T,
  has_type [] t T ->
  forall n, exp_type T n (stty_empty n) [] [] t.
Proof.
  intros. eapply fundamental; eauto.
  eapply envt_empty. eapply storet_empty.
Qed.

(* A closed, well-typed term never gets stuck. *)
Corollary safety': forall t T,
  has_type [] t T ->
  forall n n' S' r, teval n [] [] t = (n', S', Some r) -> exists v, r = Some v.
Proof.
  intros. edestruct (safety t T H n) as (M' & v & _ & _ & ? & _). eauto. eauto.
Qed.

Print Assumptions safety'.

End STLC.
