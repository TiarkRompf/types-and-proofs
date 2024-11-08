(* Full safety for STLC *)

(*

An LR-based semantic soundness proof for STLC.

Step-indexed LR: soundness only, no termination.

Full higher-order mutable references (TRef T, for any T)

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

Lemma indexr_map: forall {A B} (M: list A) x v (f: A -> B),
    indexr x M = v ->
    indexr x (map f M) = (match v with Some v => Some (f v) | None => None end).
Proof.
  intros ? ? M. induction M; intros.
  simpl. destruct v; intuition. inversion H. 
  simpl in *. rewrite map_length.
  bdestruct (x =? length M). subst v. congruence. eauto.
Qed.

Lemma map_map: forall {A B C} (M: list A) (f: A -> B) (g: B -> C),
    map g (map f M) = map (fun vt => g(f(vt))) M.
Proof.
  intros ? ? ? M. induction M. intros. simpl. eauto.
  intros. simpl in *. rewrite IHM. eauto. 
Qed.

Lemma map_eq_f: forall {A B} (f1 f2: A -> B) M,
    f1 = f2 ->
    map f1 M = map f2 M.
Proof.
  intros. congruence.
Qed.


(* ---------- LR definitions  ---------- *)


(* Type approximation machinery:

    We want semantic types to represent sets of values, each
    coupled with a store typing.

    So roughly, the definitions should be like this:

      Definition vtype := stty -> vl -> Prop

      Definition stty := list vtype

    But this doesn't work due to the obvious circularity.
    Instead, we define an indexed approximation, i.e. roughly:

      Fixpoint vtypen (n+1) := list (vtypen n) -> vl -> Prop

    This again needs to be a little bit more flexible, so we
    settle on the definitions below.

*)


(* definition of indexed types and store typings *)
Fixpoint vtypen n: Type :=
  match n with
  | 0 => Prop
  | S n => forall (nx: nat) (M: list (vtypen (n-nx))) (v: vl), Prop
  end.

(* alternative:

  | S n => forall (j: nat) (M: list (vtypen (n-(n-j)))) (v: vl), Prop

 *)

Definition sttyn n := list (vtypen n).


(* semantic types are the set of all finite approximations *)
Definition vtype := forall n, vtypen n.

Definition stty := list vtype.


(* the empty type *)
Definition vtnone n: vtypen n :=
  match n with
  | 0 => False
  | S n => fun nx (M: list (vtypen (n-nx))) (v: vl) => False
  end.

Check vtnone: vtype.


(* every indexed type can be approximated with a lower index (vt_dec) *)

Lemma aux_lt1: forall n, S n <= 0 -> False. lia. Qed.

Lemma aux_lt2: forall n j nx, S j <= S n -> (j-nx = n - (n-j+nx)). intros. lia. Qed.


Definition vtn_aux_eq: forall n1 n2 (q: n1 = n2), vtypen n1 -> vtypen n2.
Proof. intros. subst n2. eauto.
Defined.

Definition sttyn_aux_eq: forall n1 n2 (q: n1 = n2) (vt: list (vtypen n1)), list (vtypen n2).
Proof. intros. rewrite q in *. eauto.
Defined.


Lemma vt_dec: forall n j, j <= n -> vtypen n -> vtypen j.
Proof.
  intros n. intros.
  destruct n, j. eauto. edestruct aux_lt1. eapply H. simpl. eapply True.
  simpl in *. intros. eapply (X (n-j+nx)).
  eapply sttyn_aux_eq. eapply aux_lt2. eauto. eauto. eauto. 
Defined.

Print vt_dec.


(* physical approximation *)

Definition vt_wrap n (vt: vtypen n): vtype :=
  fun n1 =>
    match le_dec n1 n with
    | left a => vt_dec _ _ a vt
    | _ => vtnone n1
    end.

Definition vt_pick n (vt: vtype): vtypen n :=
  vt n.

Definition vt_apprx n (vt: vtype): vtype :=
  vt_wrap n (vt n). 


Definition stty_wrap n (M: sttyn n): stty :=
  map (fun vt => vt_wrap n vt) M. 

Definition stty_pick n (M: stty): sttyn n :=
  map (fun vt => vt _) M. 

Definition stty_apprx n (M: stty): stty :=
  stty_wrap n (stty_pick n M).
  (* map (fun vt => vt_apprx n vt) M. *)



(* logical approximation *)

Definition vt_approx n (vt: vtype): vtype :=
  fun n1 =>
    match lt_dec n1 n with
    | left a => vt n1
    | _ => vtnone n1
    end.

Definition stty_approx n (M: stty): stty :=
  map (fun vt => vt_approx n vt) M. 



(* lifting element access to the logical level:
   vtyp_elem reconstructs the abstraction of vtype
   as set of (nat, stty, vl) elements
*)

Definition vt_elem n nx (vt: vtypen n) (M: stty) (v: vl) :=
  match n, vt, M with
  | 0, _, _ => vt
  | S n, vt, M => vt nx (stty_pick _  M) v
  end.

Definition vtyp_elem n (vt: vtype) (M: stty) (v: vl) :=
  forall nx, vt_elem n nx (vt n) M v. 



(* equivalence on vtype up to n-approximation *)

Definition vtyp_equiv n (vt1 vt2: vtype) :=
  (vt_approx n vt1) = (vt_approx n vt2).


Definition istypeC nu (vt: vtype) :=     
  forall j,
    j < nu ->
    (vt_apprx j vt) = (vt_approx (S j) vt).

Definition isstoretypeD nu (M: list vtype) :=
  forall j,
    j < nu ->
    (stty_apprx j M) = (stty_approx (S j) M).


Definition st_chain n j (M:stty) (M1:stty) :=
    j <= n /\ length M <= length M1 /\
      forall i vt,
        indexr i M = Some vt ->
        exists vt',
          indexr i M1 = Some vt' /\
            vtyp_equiv j vt vt'.

Definition istypeA (vt: vtype) := forall n j M M' v,
    isstoretypeD n M ->
    isstoretypeD j M' ->
    st_chain n j M M' -> 
    vtyp_elem n vt M v -> vtyp_elem j vt M' v.


Definition vtyp_elem_approx n vt M v :=
  forall j,
    j < n ->
    vtyp_elem j (vt_approx n vt) (stty_approx j M) v.

Definition store_type n S M: Prop := 
  length S = length M /\
    forall i vt,
      indexr i M = Some vt ->
      istypeA vt /\
      istypeC n vt /\
      exists v,
        indexr i S = Some v /\
          vtyp_elem_approx n vt M v.


Definition vt_wrap1 (vt: nat -> stty -> vl -> Prop): vtype :=
  fun j =>
    match j return vtypen j with
    | 0 => True
    | S j => fun nx M vx => vt (S j-nx) (stty_wrap (j-nx) M) vx
    end.

Fixpoint val_type n (M: stty) v T {struct T}: Prop :=
  match n, M with
  | 0, M => True
  | S n, M => 
      match v, T with
      | vbool b, TBool =>  
          True
      | vref l, TRef T => 
          exists vt,
          indexr l M = Some vt /\
            vtyp_equiv (S n) vt
                       (vt_wrap1 (fun n M v => val_type n M v T))

      | vabs H ty, TFun T1 T2 =>
          forall S' nx M' vx,
            st_chain (S n) (n-nx) M M' ->
            store_type (n-nx) S' M' ->
            val_type (n-nx) M' vx T1 ->
            forall S'' ny ry,
              teval (n-nx) S' (vx::H) ty = (ny, S'', (Some ry)) ->
              exists M'' vy,
                st_chain (n-nx) (n-nx-ny) M' M'' /\
                store_type (n-nx-ny) S'' M'' /\
                ry = Some vy /\
                val_type (n-nx-ny) M'' vy T2
      | _,_ =>
          False
      end
  end.


Definition exp_type n S M H t T :=
  forall n' S' r,
    teval n S H t = (n', S', Some r) ->
    exists M' v,
      st_chain n (n-n') M M' /\
      store_type (n-n') S' M' /\
      r = Some v /\
      val_type (n-n') M' v T.

Definition env_type n M (H: venv) (G: tenv) :=
  length H = length G /\
    forall x T,
      indexr x G = Some T ->
      exists v,
        indexr x H = Some v /\
        val_type n M v T.

Definition sem_type G t T :=
  forall n S M H,
    env_type n M H G ->
    store_type n S M ->
    exp_type n S M H t T.


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: core.

#[export] Hint Constructors has_type: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.



(* ---------- helper lemmas: vtype, vtyp_equiv, etc  ---------- *)


Lemma vt_approx_comm: forall n1 n2 vt,    
    (vt_approx n1 (vt_approx n2 vt)) = (vt_approx n2 (vt_approx n1 vt)).
Proof.
  intros.
  extensionality nx.
  unfold vt_approx.
  destruct (lt_dec nx n1), (lt_dec nx n2); eauto. 
Qed.

Lemma vt_approx_neutral: forall n1 n2 vt,
    n1 <= n2 ->
    (vt_approx n1 (vt_approx n2 vt)) = (vt_approx n1 vt).
Proof.
  intros.
  extensionality nx.
  unfold vt_approx.
  destruct (lt_dec nx n1), (lt_dec nx n2); eauto. lia. 
Qed.

Lemma stty_approx_neutral: forall n1 n2 M,
    n1 <= n2 ->
    (stty_approx n1 (stty_approx n2 M)) = (stty_approx n1 M).
Proof.
  intros. unfold stty_approx. rewrite map_map. eapply map_eq_f.
  extensionality vt. eapply vt_approx_neutral. eauto.
Qed.


Lemma vtyp_approx_equiv: forall j (vt1 vt2: vtype),
  vt1 = vt2 ->
  vtyp_equiv j (vt1) (vt2).
Proof.
  intros. congruence. 
Qed.

Lemma vtyp_equiv_dec: forall n j (vt1 vt2: vtype),
  vtyp_equiv n vt1 vt2 -> j <= n ->
  vtyp_equiv j (vt1) (vt2).
Proof.
  intros. unfold vtyp_equiv in *.
  intros. unfold vt_approx, vtyp_elem in *.
  extensionality n1.
  eapply equal_f_dep with (x:=n1) in H. 
  destruct (lt_dec n1 j), (lt_dec n1 n); eauto. lia.
Qed.


Lemma vte_approx: forall n n1 vt M v,
    vtyp_elem_approx n vt M v ->
    n1 <= n ->
    vtyp_elem_approx n1 vt M v.
Proof.
  intros. unfold vtyp_elem_approx, vtyp_elem in *. 
  intros. unfold vt_elem in *.
  destruct j.

  specialize (H 0). simpl in H.
  unfold vt_approx in *.
  destruct (lt_dec 0 n1). 2: lia.
  destruct (lt_dec 0 n). 2: lia. eauto. 
  
  unfold vt_approx in *.
  remember (lt_dec (S j) n1). destruct s. 2: lia.
  specialize (H (S j)).
  remember (lt_dec (S j) n). destruct s. 2: lia.
  eapply H. eauto. 
Qed.



(* ---------- LR helper lemmas  ---------- *)

Lemma stchain_refl: forall n M,
    st_chain n n M M.
Proof.
  intros. 
  split. 2: split. eauto. eauto.
  intros. exists vt. split. eauto.
  intuition. 
Qed.

Lemma stchain_refl': forall n n1 M,
    n1 <= n ->
    st_chain n n1 M M.
Proof.
  intros. 
  split. 2: split. lia. eauto. 
  intros. exists vt. split. eauto.
  intuition.
Qed.

Lemma stchain_extend': forall n n1 vt M,
    n1 <= n ->
    st_chain n n1 M (vt::M).
Proof.
  intros. 
  split. 2: split. eauto. simpl. lia. 
  intros. exists vt0. split. eapply indexr_extend1 in H0. eapply H0. 
  intuition.
Qed.


Lemma stchain_chain: forall n1 n2 n3 M1 M2 M3,
    st_chain n1 n2 M1 M2 ->
    st_chain n2 n3 M2 M3 ->
    st_chain n1 n3 M1 M3.
Proof.
  intros.
  destruct H as (? & ? & ?).
  destruct H0 as (? & ? & ?).
  split. 2: split.
  - lia.
  - lia.
  - intros i vt1 IX1.
    edestruct H2 as (vt2 & IX2 & ?). eapply IX1.
    edestruct H4 as (vt3 & IX3 & ?). eapply IX2.
    eexists. split. eapply IX3.
    eapply vtyp_equiv_dec in H5. 
    unfold vtyp_equiv in *. rewrite H5. eauto. eauto. 
Qed.

Lemma stchain_step': forall n n1 n' M M1,
    st_chain n n1 M M1 ->
    n <= n' ->
    st_chain n' n1 M M1.
Proof.
  intros.
  eapply stchain_chain. 
  eapply stchain_refl'.
  2: eauto. eauto. 
Qed.

Lemma stchain_step'': forall n n1 n2 M M1,
    st_chain n n1 M M1 ->
    n2 <= n1 ->
    st_chain n n2 M M1.
Proof.
  intros.
  eapply stchain_chain. eauto.
  eapply stchain_refl'. eauto. 
Qed.

Lemma stchain_approx: forall n j M,
    j < n ->
    st_chain n j M (stty_approx j M).
Proof.
  intros. split. 2: split.
  lia. unfold stty_approx. rewrite map_length. eauto.
  intros. eapply indexr_map in H0.
  eexists. split. unfold stty_approx. eapply H0.
  unfold vtyp_equiv. rewrite vt_approx_neutral; eauto. 
Qed.

Lemma stchain_approx'': forall n j nx M M',
    st_chain (S n) (S j) M M' ->
    st_chain (S n - nx) (S j - nx)
      (stty_approx (S (n - nx)) M)
      (stty_approx (S (j - nx)) M').
Proof.
  intros. destruct H as (? & ? & ?).
  split. 2: split.
  lia. unfold stty_approx. rewrite map_length, map_length. eauto.
  
  intros. unfold stty_approx in *.
  eapply indexr_var_some' in H2 as IX1. rewrite map_length in IX1.
  eapply indexr_var_some in IX1 as IX2. destruct IX2 as (vt1 & IX2).
  eapply H1 in IX2 as IX4. destruct IX4 as (vt2 & IX4 & EQ2). 
  eapply indexr_map in IX4 as IX5.

  eapply indexr_map in IX2 as IX6. rewrite IX6 in H2.
  inversion H2. subst vt. 

  eexists. split. eapply IX5.
  unfold vtyp_equiv. repeat rewrite vt_approx_neutral; eauto.
  eapply vtyp_equiv_dec. eauto. lia. lia. lia. 
Qed.

Lemma stchain_apprx: forall n j nx M M',
    isstoretypeD (S n) M ->
    isstoretypeD (S j) M' ->
    st_chain (S n) (S j) M M' ->
    st_chain (S n - nx) (S j - nx)
      (stty_apprx (n - nx) M)
      (stty_apprx (j - nx) M').
Proof.
  intros.
  destruct H1 as (? & ? & ?).
  rewrite H, H0.
  eapply stchain_approx''. split; eauto. lia. lia. 
Qed.



Lemma envt_empty: forall n M,
    env_type n M [] [].
Proof.
  intros. split. eauto. intros. inversion H. 
Qed.

Lemma envt_extend: forall n M E G v1 T1,
    env_type n M E G ->
    val_type n M v1 T1 ->
    env_type n M (v1::E) (T1::G).
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

Lemma valt_zero: forall M vx T,
    val_type 0 M vx T.
Proof.
  intros. destruct vx, T; simpl; eauto.
Qed.

Lemma valt_step: forall m n, n < m -> forall n1 v1 M M1 T1,
    val_type n M v1 T1 ->
    st_chain n n1 M M1 -> 
    val_type n1 M1 v1 T1.
Proof.
  intros m. induction m. lia. intros.
  remember H1 as SC. 
  destruct H1 as (A & B & C).

  destruct n1. destruct v1, T1; simpl in H0; simpl; eauto. destruct n. lia. 
  destruct v1, T1; simpl in H0; try contradiction.
  - simpl. eauto.
  - simpl. intros.
    edestruct H0 as (vt & ? & ?).
    eapply C in H1 as XX. destruct XX as (vt' & ? & ?).

    exists vt'. split. eauto.
    eapply vtyp_equiv_dec with (j:= S n1) in H2. 2: lia.
    unfold vtyp_equiv in *. congruence.

  - simpl. intros.
    
    assert (n-(n-n1+nx) = n1-nx) as R. lia. 
    specialize H0 with (nx:=n-n1+nx).
    rewrite R in H0. eapply H0; eauto.
    eapply stchain_chain. eauto. eauto.
Qed.

Lemma valt_step': forall n n1 v1 M T1,
    val_type n M v1 T1 ->
    n1 <= n ->
    val_type n1 M v1 T1.
Proof.
  intros. eapply valt_step. 2: eauto. eauto.
  eapply stchain_refl'. eauto. 
Qed.

Lemma envt_step: forall n n1 M M1 H G,
    env_type n M H G ->
    st_chain n n1 M M1 ->     
    env_type n1 M1 H G.
Proof.
  intros. destruct H0. split. eauto.
  intros. eapply H2 in H3. destruct H3. eexists. intuition eauto.
  eapply valt_step; eauto. 
Qed.


Lemma ista_valt: forall T,
  istypeA (vt_wrap1 (fun (n : nat) (M : stty) (v : vl) => val_type n M v T)).
Proof.
  intros. intros ? ? ? ? ? ? ? ? ? ?.
  unfold vtyp_elem, vt_elem in *.
  specialize (H2 nx).
  destruct j. simpl. eauto. 
  destruct n. destruct H1. lia.
  eapply valt_step. 2: eauto. eauto.
  eapply stchain_apprx. eauto. eauto. eauto. 
Qed.


(* 
How to deal with equalities that can't be destructed - see:
http://adam.chlipala.net/cpdt/html/Cpdt.Equality.html

(In the end this wasn't necessary)

Import Eqdep.

Check UIP_refl. (* see http://adam.chlipala.net/cpdt/html/Cpdt.Equality.html *)
Check eq_rect_eq.

Lemma aa1: forall n1 (q1:n1=n1) (vt1: vtypen n1), 
    vt1 = a1 n1 n1 q1 vt1.
Proof.
  intros.
  assert (q1 = eq_refl). eapply UIP_refl.
  unfold a1, eq_rect. rewrite H. eauto. 
Qed. 

*)

Lemma sttyw_eq: forall n1 n2 M1 (q: n1 = n2),
    stty_wrap n1 M1 = stty_wrap n2 (sttyn_aux_eq _ _ q M1).
Proof.
  intros. subst n1.
  unfold sttyn_aux_eq, eq_rect.
  eauto.
Qed.

Lemma istc_valt: forall nu T,
  istypeC nu (vt_wrap1 (fun (n : nat) (M : stty) (v : vl) => val_type n M v T)).
Proof.
  intros. unfold istypeC. intros.
  extensionality n1.
  unfold vt_approx, vt_apprx, vt_wrap, vt_wrap1.
  destruct (le_dec n1 j).
  destruct (lt_dec n1 (S j)). 2: lia.
  destruct j, n1. simpl. eauto. simpl.
  destruct (aux_lt1 n1 l). simpl. eauto.

  extensionality nz.
  extensionality M.
  extensionality vz.
  unfold vt_dec. 
  erewrite <-sttyw_eq.
  assert ((S j - (j - n1 + nz)) = (S n1 -nz)). lia. rewrite H0. eauto.

  destruct (lt_dec n1 (S j)). destruct n1. lia. lia. eauto. 
Qed.

Lemma ista_approx: forall n vt,
    istypeA vt ->
    istypeA (vt_approx n vt).
Proof.
  intros. intros ? ? ? ? ? IM IM' ? ? .
  eapply H in H0 as H2. destruct H0 as (? & ? & ?). clear l0 e.

  unfold vtyp_elem in *.  
  intros. 
  unfold vt_approx in *.
  destruct (lt_dec n0 n). 2: { destruct n0,H1; eauto. }
  destruct (lt_dec j n). 2: lia. eauto.
  eauto. eauto. 
Qed.


Lemma istc_step': forall nu n vt,
    istypeC nu vt ->
    n <= nu ->
    istypeC n vt.
Proof.
  intros. intros ? ?. eapply H. lia. 
Qed.


Lemma istc_approx: forall nu n vt,
    istypeC nu vt ->
    n <= nu ->
    istypeC n (vt_approx n vt).
Proof.
  intros. unfold istypeC in *. intros.  
  assert (j < nu). lia.
  extensionality n1.
  specialize (H j). eapply equal_f_dep with (x:=n1) in H. 2: lia. 
  unfold vt_approx, vt_apprx, vt_wrap in *.
  destruct (le_dec n1 j). 
  destruct (lt_dec n1 (S j)). 2: lia. 
  destruct (lt_dec j n). 2: lia. 
  destruct (lt_dec n1 n). 2: lia. eauto. 
  destruct (lt_dec n1 (S j)). 2: eauto.
  destruct (lt_dec n1 n). eauto. eauto.
Qed.


Definition isstoretypeC nu (M: list vtype) :=
  forall x vt, indexr x M = Some vt -> istypeC nu vt.

Lemma isstc_to_d: forall n1 M,
  isstoretypeC n1 M ->     
  isstoretypeD n1 M.
Proof.
  intros. intros ? ?. unfold isstoretypeC in H. 
  unfold stty_apprx, stty_approx, stty_wrap, stty_pick.
  rewrite map_map. induction M.
  simpl. eauto. simpl.
  rewrite IHM. rewrite <-H. eauto. eapply indexr_head. eauto.
  intros. eapply H. rewrite indexr_skip. eauto. eapply indexr_var_some' in H1. lia. 
Qed.

Lemma isstd_approx: forall nu n M,
    isstoretypeD nu M ->
    n <= nu ->
    isstoretypeD n (stty_approx n M).
Proof.
  intros. unfold isstoretypeD in *. intros.
  assert (j < nu). lia.
  specialize (H j H2). rewrite stty_approx_neutral, <-H.
  unfold stty_apprx, stty_wrap, stty_pick, stty_approx.
  repeat rewrite map_map. eapply map_eq_f.
  extensionality vt.
  unfold vt_wrap, vt_approx.
  extensionality n1.
  destruct (le_dec n1 j). 2: eauto.
  destruct (lt_dec j n). 2: lia. eauto. lia. 
Qed.





Lemma storet_empty: forall n,
    store_type n [] [].
Proof.
  intros. split. eauto. intros. inversion H. 
Qed.

Lemma storet_step': forall n n1 S M,
      store_type n S M ->
      n1 <= n ->
      store_type n1 S M.
Proof.
  intros. destruct H. split. eauto.
  intros. edestruct H1 as (TY & TYB & v & ? & ?). eauto.
  split. 2: split. eapply TY. eapply istc_step'. eapply TYB. lia. exists v. split. eauto.
  bdestruct (n1 =? n). subst n1. eauto. 
  eapply vte_approx. eauto. eauto. 
Qed.

Lemma storet_approx: forall n n1 S M,
      store_type n S M ->
      n1 < n ->
      store_type n1 S (stty_approx n1 M).
Proof.
  intros. destruct H. split. unfold stty_approx. rewrite map_length. eauto.
  intros. unfold stty_approx in H2.
  eapply indexr_var_some' in H2 as H3. rewrite map_length in H3.
  eapply indexr_var_some in H3. destruct H3.
  eapply indexr_map in H3 as H4. rewrite H2 in H4.
  inversion H4. subst vt. clear H4.

  edestruct H1 as (TY & TYB & v & ? & ?). eauto.
  split. 2: split.
  eapply ista_approx. eapply TY.
  eapply istc_approx. eapply TYB. lia. 
  exists v. split. eauto.
  intros ? ?. rewrite vt_approx_neutral, stty_approx_neutral. 2,3: lia.
  eapply vte_approx. eauto. 1,2: lia.
Qed.



Lemma storet_extend: forall n S M vx vt,
    store_type (n) S M ->
    istypeA vt ->
    istypeC n vt ->
    vtyp_elem_approx n vt (vt::M) vx ->
    store_type (n) (vx :: S) (vt :: M). 
Proof.
  intros. destruct H. split.
  - simpl. lia.
  - intros. bdestruct (i <? length M).
    + rewrite indexr_skip in H4. 2: lia. eapply H3 in H4.
      destruct H4 as (TY & TYB & v & ? & ?).
      split. 2: split.
      eapply TY. eapply TYB. exists v. split. rewrite indexr_skip. 2: lia. eauto.
      assert (istypeA (vt_approx n vt0)). eapply ista_approx; eauto.
      intros ? ?. eapply H7. 4: eauto.
      eapply isstd_approx. eapply isstc_to_d. intros ? ? IX. eapply H3 in IX. eapply IX. lia.
      eapply isstd_approx. eapply isstc_to_d. intros ? ? IX. bdestruct (x =? length M).
      subst x. rewrite indexr_head in IX. inversion IX. subst vt. eauto.
      rewrite indexr_skip in IX. 2: eauto. eapply H3 in IX. eapply IX. lia. 
      simpl. 
      eapply stchain_extend'. eauto. 
    + eapply indexr_var_some' in H4 as IL. simpl in IL. 
      replace i with (length S). 2: lia. rewrite indexr_head. 
      replace i with (length M) in H4. 2: lia. rewrite indexr_head in H4.
      inversion H4. subst vt0.
      split. 2: split. eauto. eauto. exists vx. split. eauto. eauto.
Qed.


Lemma storet_isstd: forall n S M,
    store_type n S M ->
    isstoretypeD n M.
Proof.
  intros. eapply isstc_to_d. intros ? ? ?. eapply H in H0. eapply H0.
Qed.




(* ---------- vtype/stchain conversion helper lemmas  ---------- *)

Lemma stchain_aux_ref': forall n2 j nx0 M',
    isstoretypeD n2 M' ->
    S j < n2 ->
    st_chain n2 (S j - nx0)
      (stty_approx n2 M')
      (stty_apprx (j - nx0) (stty_approx (S j) (stty_approx n2 M'))).
Proof.
  intros. 
  rewrite stty_approx_neutral.
  eapply isstd_approx in H.
  erewrite H. 
  rewrite stty_approx_neutral. 2-5: lia.

  replace (stty_approx (S (j - nx0)) M') with ((stty_approx (S (j - nx0)) (stty_approx n2 M'))). 2: { rewrite stty_approx_neutral. eauto. lia. }
  
  eapply stchain_step''. eapply stchain_approx. lia. lia. 
Qed.

Lemma stchain_aux_ref: forall n2 j nx0 M' vt,
    isstoretypeD n2 M' ->
    S j < n2 ->
    st_chain n2 (S j - nx0)
      (stty_approx n2 M')
      (stty_apprx (j - nx0) (stty_approx (S j) (vt :: (stty_approx n2 M')))).
Proof.
  intros. remember (S j - nx0).
  unfold stty_approx, stty_apprx, stty_wrap, stty_pick. simpl. subst n. 
  eapply stchain_chain. 2: eapply stchain_extend'. 2: eauto. 
  eapply stchain_aux_ref'. eauto. eauto.
Qed.

Lemma stchain_aux_get: forall nx1 M',
    isstoretypeD (S nx1) M' ->

    st_chain (S nx1) (S nx1)
      (stty_apprx (nx1 - 0) (stty_approx (S nx1) M'))
      (stty_approx (S nx1) M').    
Proof. 
  intros. replace (nx1 - 0) with nx1. 2: lia. 
  eapply isstd_approx in H.
  erewrite H, stty_approx_neutral.
  eapply stchain_refl. all: lia. 
Qed.

Lemma stchain_aux_put: forall ny1 nx0 j M2,
    isstoretypeD (S ny1) M2 ->
    j < ny1 ->
    st_chain (Datatypes.S ny1) (Datatypes.S j - nx0)
      M2
      (stty_apprx (j - nx0) (stty_approx (Datatypes.S j) M2)).
Proof.
  intros.
  eapply isstd_approx in H.
  erewrite H, stty_approx_neutral.
  eapply stchain_step''. eapply stchain_approx. all: lia. 
Qed.


(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_true: forall G,
    sem_type G ttrue TBool.
Proof.
  intros. intros n S M E WFE ST. intros ? ? ? EV.
  destruct n; inversion EV. subst n' S' r.
  assert (Datatypes.S n - 1 = n) as R. lia. 
  exists M, (vbool true).
  split. 2: split. 3: split.
  - rewrite R. eapply stchain_refl'. lia. 
  - rewrite R. eapply storet_step'; eauto. 
  - eauto.
  - destruct n; simpl; eauto. 
Qed.

Lemma sem_false: forall G,
    sem_type G tfalse TBool.
Proof.
  intros. intros n S M E WFE ST. intros ? ? ? EV.
  destruct n; inversion EV. subst n' S' r.
  assert (Datatypes.S n - 1 = n) as R. lia. 
  exists M, (vbool false).
  split. 2: split. 3: split.
  - rewrite R. eapply stchain_refl'. lia. 
  - rewrite R. eapply storet_step'; eauto. 
  - eauto.
  - destruct n; simpl; eauto. 
Qed.

Lemma sem_var: forall G x T,
    indexr x G = Some T ->
    sem_type G (tvar x) T.
Proof.
  intros. intros n S M E WFE ST. intros ? ? ? EV.
  destruct n; inversion EV. subst n' S' r.
  eapply WFE in H as IX. destruct IX as (v & IX & VX).
  assert (Datatypes.S n - 1 = n) as R. lia. 
  exists M, v.
  split. 2: split. 3: split.
  - rewrite R. eapply stchain_refl'. lia. 
  - rewrite R. eapply storet_step'; eauto.
  - eauto.
  - eapply valt_step'. eauto. eauto. lia. 
Qed.

Lemma sem_ref: forall G t T,
    sem_type G t T ->
    sem_type G (tref t) (TRef T).
Proof.
  intros ? ? ? HX. intros n S M E WFE ST. intros n1 S1 r1 EV.
  destruct n; simpl in EV. inversion EV.
  
  remember (teval n S E t) as tx. symmetry in Heqtx. destruct tx as [[nx S'] [rx|]]. 2: inversion EV.
  edestruct (HX (1+n) S M E) as (M' & vx & SC' & ST' & RX & VX). eauto. eauto. eapply eval_deterministic. eauto. eauto. lia. 
  eapply eval_bounded in Heqtx as BX; eauto.
  subst rx.

  inversion EV. subst n1 S1 r1.

  replace (Datatypes.S n - Datatypes.S nx) with (n-nx) in *. 2: lia.
  remember (n-nx) as n2. 
  remember (n2-1) as n3. 

  remember (vt_wrap1 (fun n M v => val_type n M v T)) as vt. 
  remember (stty_approx (n2) M') as MA.
  remember (vt_approx (n2) vt) as vta. 
  
  assert (st_chain (1+n-nx) (n2) M' MA) as SCA. {
    subst MA. eapply stchain_approx. lia. }

  assert (st_chain (1+n-nx) n2 M' (vta::MA)) as SCAE. {
    subst MA. eapply stchain_chain. 2: eapply stchain_extend'. eauto. lia.  }

  
  assert (val_type n2 MA vx T). {
    eapply valt_step; eauto. (* destruct n2. replace n3 with 0. eauto. 
    eapply stchain_step''. eauto. lia.*) }
  
  exists (vta :: MA), (vref (length S')).
  split. 2: split. 3: split.
  - subst MA. 
    eapply stchain_chain. eauto. eapply stchain_chain.
    2: { eapply stchain_extend'. eauto. } eapply SCA. 
  - eapply storet_extend. subst MA. eapply storet_approx. eauto. lia.
    subst vt vta. eapply ista_approx. eapply ista_valt.
    subst vt vta. eapply istc_approx. eapply istc_valt. eauto. 

    intros. unfold vtyp_elem_approx, vtyp_elem, vt_approx. 

    intros. 
    remember (lt_dec j n2). destruct s. 2: lia.

    subst vta vt MA. 

    unfold vt_approx.
    unfold vtyp_elem, vt_elem.
    unfold vt_wrap1.

    rewrite <-Heqs. 

    destruct j. eauto. 
    eapply valt_step. 2: eauto. eauto.
    eapply stchain_aux_ref. eapply storet_isstd. eapply storet_step'. eauto. lia. eauto. 
    
  - eauto.
  - simpl. destruct n2. eauto. 
    subst MA. unfold stty_approx. rewrite map_length. 
    destruct ST'.
    exists vta. bdestruct (length S' =? length M'). 2: lia.
    split. eauto.
    subst vta vt.
    unfold vtyp_equiv. rewrite vt_approx_neutral. eauto. eauto.
Qed.

Lemma sem_get: forall G t T,
    sem_type G t (TRef T) ->
    sem_type G (tget t) T.
Proof.
  intros ? ? ? HX. intros n S0 M E WFE ST. intros n1 S1 r1 EV.
  destruct n. inversion EV. simpl in EV. 

  remember (teval n S0 E t) as tx. symmetry in Heqtx. destruct tx as [[nx S'] [rx|]]. 2: inversion EV.
  edestruct (HX (1+n) S0 M E) as (M' & vx & SC' & ST' & RX & VX). eauto. eauto. eapply eval_deterministic. eauto. eauto. lia. 
  eapply eval_bounded in Heqtx as BX; eauto.
  subst rx.

  remember (1 + n - nx) as nx1. destruct nx1. lia. 
  simpl in VX. destruct vx; try contradiction. 
  
  inversion EV. subst n1 S1 r1. 

  destruct VX as (vt & IX & ?).
  destruct ST' as (L & B). eapply B in IX as IX1.
  destruct IX1 as (TY & TYB & vx & ? & AB). 

  exists (stty_approx (n-nx) M'), vx. 
  split. 2: split. 3: split.
  - eapply stchain_chain. eauto. eapply stchain_approx. lia. 
  - eapply storet_approx. split; eauto. lia. 
  - eauto.
  - unfold vtyp_elem_approx in AB. 
    assert (nx1 = n-nx). lia.
    replace ((S n - S nx)) with nx1 in *.
    rewrite <-H1 in *. 

    unfold vtyp_equiv in H. rewrite H in AB. 

    assert (nx1 < S nx1). lia. 
    eapply AB in H2.
    
    unfold vtyp_elem, vt_elem, vt_approx, vt_wrap1 in H2.
    destruct nx1. eapply valt_zero.

    remember (lt_dec (nx1) (S nx1)). destruct s. 2: lia.
    remember (lt_dec (S nx1) (S (S nx1))). destruct s. 2: lia.

    specialize (H2 0). 
    replace (S nx1 - 0) with (S nx1) in *. 2: lia.
    
    eapply valt_step. 2: eauto. eauto.
    eapply stchain_aux_get. eapply storet_isstd. eapply storet_step'. split; eauto. lia. 
Qed.


Lemma sem_put: forall G t t2 T,
    sem_type G t (TRef T) ->
    sem_type G t2 T ->
    sem_type G (tput t t2) TBool.
Proof.
  intros ? ? ? ? HX HY. intros n S M E WFE ST. intros n3 S3 r3 EV.
  destruct n. inversion EV. simpl in EV. 

  remember (teval n S E t) as tx. symmetry in Heqtx. destruct tx as [[nx S1] [rx|]]. 2: inversion EV.
  edestruct (HX (1+n) S M E) as (M1 & vx & SC1 & ST1 & RX & VX). eauto. eauto. eapply eval_deterministic. eauto. eauto. lia. 
  eapply eval_bounded in Heqtx as BX; eauto.
  subst rx.

  remember (1 + n - nx) as nx1. destruct nx1. lia. 
  simpl in VX. destruct vx; try contradiction.

  remember (teval (n-nx) S1 E t2) as ty. symmetry in Heqty. destruct ty as [[ny S2] [ry|]]. 2: inversion EV.
  edestruct (HY (1+n-nx) S1 M1 E) as (M2 & vy & SC2 & ST2 & RY & VY).
  eapply envt_step. eauto. eauto.
  rewrite Heqnx1 in SC1. eapply SC1.
  rewrite Heqnx1 in ST1. eapply ST1. 
  eapply eval_deterministic. 2: eauto. eauto. lia. 
  eapply eval_bounded in Heqty as BY; eauto.
  subst ry.

  remember (1+n-nx-ny) as ny1. destruct ny1. lia.
  simpl in VX. destruct VX as (vtx & IX1 & EQ). 
  
  destruct ST1 as (L1 & B1). 
  destruct ST2 as (L2 & B2). 
  eapply SC2 in IX1. destruct IX1 as (vtx2 & IX2 & EQ2). 
  eapply indexr_var_some' in IX2 as IX3. 
  assert (i < length S2) as VX'. lia. 
  eapply indexr_var_some in VX'. destruct VX' as (vx & IX).
  rewrite IX in EV. inversion EV. subst n3 S3 r3.

  eapply B2 in IX2 as IX4. destruct IX4 as (TY & TYB & vtx' & ? & AB).
  rewrite IX in H. inversion H. subst vtx'. 
  
  exists (stty_approx (n-nx-ny) M2), (vbool true). 
  split. 2: split. 3: split.
  - eapply stchain_chain. eauto. eapply stchain_chain. 
    eapply stchain_step'. eauto. lia.
    eapply stchain_step''. eapply stchain_approx. lia. lia. 
  - eapply storet_step'. eapply storet_approx. split; eauto.
    rewrite <-update_length. eauto. intros.
    bdestruct (i0 =? i).
    + subst i0. rewrite IX2 in H0. inversion H0. subst vt.
      split. 2: split. eauto. eauto. 
      exists vy. rewrite update_indexr_hit; eauto. 2: lia. 
      split. eauto. 

      unfold vtyp_equiv in *. 
      intros ? ?. rewrite <-EQ2. eapply vtyp_equiv_dec in EQ. rewrite EQ. 2: lia. 
      intros ?. unfold vt_approx. 
      remember (lt_dec (j) (Datatypes.S ny1)). destruct s. 2: lia.
      unfold vt_elem, vt_wrap1.

      destruct j. eauto. 
      eapply valt_step. 2: eauto. eauto.
      eapply stchain_aux_put. eapply storet_isstd. split. eauto. eauto. lia. 
    + eapply B2 in H0 as IX5.
      rewrite update_indexr_miss; eauto.
    + lia.
    + lia. 
      
  - simpl. eauto.
  - simpl. remember (n - (nx + ny)) as ny2. destruct ny2.
    simpl. eauto.
    simpl. eauto. 
Qed.

Lemma sem_app: forall G f t T1 T2,
    sem_type G f (TFun T1 T2) ->
    sem_type G t T1 ->
    sem_type G (tapp f t) T2.
Proof.
  intros ? ? ? ? ? HF HX. intros n S M E WFE ST. intros n3' S3' r3' EV.
  destruct n. inversion EV. simpl in EV. 

  (* function evaluates *)
  remember (teval n S E f) as tf. symmetry in Heqtf. destruct tf as [[nf S1] [rf|]]. 2: inversion EV.
  edestruct (HF (1+n) S M E) as (M1 & vf & SC1 & ST1 & RF & VF). eauto. eauto. eapply eval_deterministic. 2: eauto. eauto. lia. 
  eapply eval_bounded in Heqtf as BF; eauto.
  remember (1+n-nf) as nf1. destruct nf1. lia.
  subst rf.

  (* result is a function value *)
  simpl in VF. destruct vf; try contradiction.

  (* argument evaluates *)
  remember (teval (n-nf) S1 E t) as tx. symmetry in Heqtx. destruct tx as [[nx S2] [rx|]]. 2: inversion EV.
  edestruct (HX (1+n-nf) S1 M1 E) as (M2 & vx & SC2 & ST2 & RX & VX).
  eapply envt_step. eauto.
  rewrite Heqnf1 in SC1. eapply SC1. 
  rewrite Heqnf1 in ST1. eapply ST1. 
  eapply eval_deterministic. 2: eauto. eauto. lia.
  eapply eval_bounded in Heqtx as BX; eauto.
  remember (1+n-nx) as nx1. destruct nx1. lia.
  subst rx. 

  (* function body evaluates *)
  remember (teval (n-nf-nx) S2 (vx :: l) t0) as ty. symmetry in Heqty. destruct ty as [[ny S3] [ry|]]. 2: inversion EV.
  eapply eval_bounded in Heqty as BY; eauto.
  inversion EV. subst n3' S3' r3'. 

  (* from function LR: function body result is well-typed *)
  assert (nf1 = n-nf). lia. subst nf1.
  assert (Datatypes.S (n-nf) = 1+n-nf) as R1. lia.
  assert (n - nf - (nx - 1) = 1+n-nf-nx) as R2. lia. 
  edestruct (VF S2 (nx-1) M2 vx) as (M3 & vy & SC3 & ST3 & RY & VY).
  rewrite R1,R2. eapply SC2.
  rewrite R2. eapply ST2.
  rewrite R2. eapply VX.
  rewrite R2. eapply eval_deterministic. 2: eauto. eauto. lia. 
  subst ry.

  (* return result *)
  exists M3, vy. split. 2: split. 3: split.
  - eapply stchain_chain. eauto.
    eapply stchain_chain. rewrite R1. eauto.
    eapply stchain_chain. rewrite R2 in SC3. eapply SC3.
    eapply stchain_refl'. lia. 
  - eapply storet_step'. eauto. lia. 
  - eauto. 
  - eapply valt_step'. eauto. lia. 
Qed.

Lemma sem_abs: forall G t T1 T2,
    sem_type (T1::G) t T2 ->
    sem_type G (tabs t) (TFun T1 T2).
Proof.
  intros ? ? ? ? HY. intros n S M E WFE ST. intros n1 S1 r1 EV.
  destruct n. inversion EV. simpl in EV.

  inversion EV. subst n1 S1 r1.
  
  exists M, (vabs E t). split. 2: split. 3: split. 
  - eapply stchain_refl'. lia. 
  - eapply storet_step'. eauto. lia. 
  - eauto. 
  - simpl. remember (n-0) as n'. destruct n'.
    simpl. eauto.
    simpl. intros S1 nx M1 vx SC1 ST1 VX S2 ny ry EVY.
    remember (n'-nx) as nx'. destruct nx'. inversion EVY. 
    eapply HY. 
    + eapply envt_extend.
      eapply envt_step. eauto. eapply stchain_chain. eapply stchain_refl'. 2: eauto. lia. 
      eauto. 
    + eauto.
    + eauto. 
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
  - eapply sem_ref; eauto.
  - eapply sem_get; eauto.
  - eapply sem_put; eauto.
  - eapply sem_app; eauto. 
  - eapply sem_abs; eauto.
Qed.

Corollary safety: forall t T,
  has_type [] t T ->
  forall n, exp_type n [] [] [] t T.
Proof. 
  intros. intros ? ? ? EV.
  eapply fundamental in H as ST; eauto.
  edestruct (ST n [] [] []) as (M' & v & SC' & ST' & R & V).
  eapply envt_empty.
  eapply storet_empty.
  eauto. 
  exists M', v. intuition.
Qed.

End STLC.
