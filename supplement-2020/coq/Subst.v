
Require Import Arith.
Require Import Omega.
Require Import Tactics.
Require Export Syntax.


(* Generic development: parameterized over Syntax:SYNTAX, where: *)


Module Type SYNTAX.

(* Renamed because an inductive type cannot instantiate a parameter. *)
Parameter termx : Set.
Parameter varx : nat -> termx.


Parameter traverse : forall S:Set, (S -> S) -> (S -> nat -> termx) -> S -> termx -> termx.

Axiom traverse_var :
  forall S enter resolve s i,
    traverse S enter resolve s (varx i) = resolve s i.

Axiom traverse_parametric :
  forall (S:Set) (S':Set) (R : S -> S' -> Prop) enter enter' resolve resolve' s s' t,
    (forall s s', R s s' -> R (enter s) (enter' s'))
    -> (forall s s' i, R s s' -> resolve s i = resolve' s' i)
    -> R s s'
    -> traverse S enter resolve s t = traverse S' enter' resolve' s' t.

Axiom traverse_id :
  forall (S:Set) (R : S -> Prop) enter resolve s t,
    (forall s, R s -> R (enter s))
    -> (forall s i, R s -> resolve s i = varx i)
    -> R s
    -> traverse S enter resolve s t = t.

Axiom traverse_compose :
  forall (S:Set) (S':Set) enter enter' resolve resolve' s s' t,
    traverse S enter resolve s (traverse S' enter' resolve' s' t)
    = traverse (S * S')
      (fun p => let (s, s') := p in (enter s, enter' s'))
      (fun p i => let (s, s') := p in traverse S enter resolve s (resolve' s' i))
      (s, s') t.

End SYNTAX.


(* Verify that Syntax satisfies SYNTAX. *)
Module TermCheck <: SYNTAX := Syntax.

Goal Syntax.termx = Syntax.term.
Proof. auto. Qed.

Goal Syntax.varx = Syntax.var.
Proof. auto. Qed.


(* Hold Syntax.traverse mostly abstract in proofs.
   (This keeps Syntax.traverse from being unfolded under most
   circumstances, but unfortunately still allows it to be unfolded for
   conversion checks.)
*)
Opaque Syntax.traverse.


Inductive sub : Set :=
| dot : term -> sub -> sub
| sh : nat -> sub.


Fixpoint trunc (n : nat) (s : sub) {struct n} : sub :=
  (match n with
   | 0 => s
   | S n' =>
       (match s with
        | sh m => sh (m + n)
        | dot _ s' => trunc n' s'
        end)
   end).


Definition project (s : sub) (n : nat) : term :=
  (match trunc n s with
   | dot t _ => t
   | sh i => var i
   end).


Definition shift_var (n : nat) (i : nat) : term :=
  if lt_dec i n then
    var i
  else
    var (S i).


Definition shift_term (n : nat) (t : term) :=
  traverse nat S shift_var n t.


Fixpoint shift_sub (s : sub) {struct s} : sub :=
  (match s with
   | dot t s' =>
       dot (shift_term 0 t) (shift_sub s')
   | sh m =>
       sh (S m)
   end).


Definition subst : sub -> term -> term :=
  traverse sub (fun s' => dot (var 0) (shift_sub s')) project.


Definition id : sub := sh 0.
Definition sh1 : sub := sh 1.
Definition subst1 (t : term) : term -> term := subst (dot t id).
Definition shift1 : term -> term := subst sh1.



Fixpoint compose (s1 : sub) (s2 : sub) {struct s1} : sub :=
  (match s1 with
   | dot t s1' => dot (subst s2 t) (compose s1' s2)
   | sh n => trunc n s2
   end).


Fixpoint under (n : nat) (s : sub) {struct n} : sub :=
  (match n with
   | 0 => s
   | S n' =>
       dot (var 0) (shift_sub (under n' s))
   end).


Lemma subst_eq_traverse :
  forall s t,
    subst s t = traverse sub (under 1) project s t.
Proof.
auto.
Qed.


Ltac omega_contra := exfalso; omega.


Lemma shift_term_var :
  forall n i,
    shift_term n (var i) = shift_var n i.
Proof.
intros n i.
apply traverse_var.
Qed.


Lemma subst_var : forall s i,
  subst s (var i) = project s i.
Proof.
intros s i.
unfold subst.
apply traverse_var.
Qed.


Lemma shift_var_lt :
  forall n i,
    i < n -> shift_var n i = var i.
Proof.
intros n i H.
unfold shift_var.
destruct (lt_dec i n); [| omega_contra ].
reflexivity.
Qed.


Lemma shift_var_ge :
  forall n i,
    i >= n -> shift_var n i = var (S i).
Proof.
intros n i H.
unfold shift_var.
destruct (lt_dec i n); [ omega_contra |].
reflexivity.
Qed.


Lemma trunc_dot :
  forall n t s,
    trunc (S n) (dot t s) = trunc n s.
Proof.
intros n t s.
reflexivity.
Qed.


Lemma trunc_sh :
  forall m n,
    trunc m (sh n) = sh (m+n).
Proof.
intros m n.
destruct m.
reflexivity.
simpl.
f_equal.
omega.
Qed.


Lemma project_zero :
  forall t s,
    project (dot t s) 0 = t.
Proof.
auto.
Qed.


Lemma project_dot :
  forall t s i,
    project (dot t s) (S i) = project s i.
Proof.
intros t s i.
unfold project.
simpl.
reflexivity.
Qed.


Lemma project_sh :
  forall n i,
    project (sh n) i = var (n+i).
Proof.
intros n i.
unfold project.
rewrite -> trunc_sh.
f_equal; omega.
Qed.


Lemma trunc_shift_sub :
  forall n s,
    trunc n (shift_sub s) = shift_sub (trunc n s).
Proof.
intros n.
induction n.
auto.
intro s; destruct s.
simpl.
apply IHn.
reflexivity.
Qed.


(* Technical device: trunc1 *)

Definition trunc1 (s : sub) :=
  (match s with
   | dot _ s' => s'
   | sh n => sh (S n)
   end).


Lemma trunc_succ_outer :
  forall n s,
    trunc (S n) s = trunc1 (trunc n s).
Proof.
intro n.
induction n.

(* 0 *)
intro s.
destruct s.

  (* dot *)
  simpl.
  reflexivity.

  (* sh *)
  simpl.
  replace (n+1) with (S n); [reflexivity | omega].

(* S *)
intro s.
destruct s.

  (* dot *)
  replace (trunc (S (S n)) (dot t s)) with (trunc (S n) s) by reflexivity.
  replace (trunc (S n) (dot t s)) with (trunc n s) by reflexivity.
  apply IHn.

  (* sh *)
  simpl.
  f_equal.
  omega.

Qed.


Lemma trunc_sum :
  forall m n s,
    trunc m (trunc n s) = trunc (m+n) s.
Proof.
intros m n s.
induction m.
simpl; reflexivity.
replace (S m + n) with (S (m + n)); [ | auto].
rewrite -> trunc_succ_outer.
rewrite -> trunc_succ_outer.
f_equal.
assumption.
Qed.


Lemma trunc_succ_inner :
  forall n s,
    trunc (S n) s = trunc n (trunc1 s).
Proof.
intros n s.
replace (S n) with (n+1); [| omega].
rewrite <- (trunc_sum n 1).
f_equal.
unfold trunc1.
destruct s.
reflexivity.
simpl.
f_equal; omega.
Qed.


Lemma trunc1_under :
  forall n s,
    n >= 1
    -> trunc1 (under n s) = shift_sub (under (n-1) s).
Proof.
intros n s H.
destruct n.
omega_contra.
simpl.
replace (n-0) with n by omega.
reflexivity.
Qed.


(* Techical device: nshift *)

Fixpoint nshift_term (n : nat) (t : term) {struct n} : term :=
  (match n with
   | 0 => t
   | S n' => shift_term 0 (nshift_term n' t)
   end).


Fixpoint nshift_sub (n : nat) (s : sub) {struct n} : sub :=
  (match n with
   | 0 => s
   | S n' => shift_sub (nshift_sub n' s)
   end).


Lemma nshift_sub_sum :
  forall m n s,
    nshift_sub m (nshift_sub n s) = nshift_sub (m+n) s.
Proof.
intros m n s.
induction m.
reflexivity.
simpl.
rewrite -> IHm.
reflexivity.
Qed.


Corollary nshift_sub_succ_inner :
  forall n s,
    nshift_sub (S n) s = nshift_sub n (shift_sub s).
Proof.
intros n s.
replace (S n) with (n+1) by omega.
rewrite <- nshift_sub_sum.
reflexivity.
Qed.


Lemma nshift_term_sum :
  forall m n s,
    nshift_term m (nshift_term n s) = nshift_term (m+n) s.
Proof.
intros m n s.
induction m.
reflexivity.
simpl.
rewrite -> IHm.
reflexivity.
Qed.


Corollary nshift_term_succ_inner :
  forall n s,
    nshift_term (S n) s = nshift_term n (shift_term 0 s).
Proof.
intros n s.
replace (S n) with (n+1) by omega.
rewrite <- nshift_term_sum.
reflexivity.
Qed.


Lemma trunc_nshift_sub :
  forall n m s,
    trunc n (nshift_sub m s) = nshift_sub m (trunc n s).
Proof.
intros n m s.
induction m.
reflexivity.
simpl.
rewrite -> trunc_shift_sub.
f_equal.
apply IHm.
Qed.


Lemma trunc_under :
  forall m n s,
    m <= n
    -> trunc m (under n s) = nshift_sub m (under (n-m) s).
Proof.
intros m.
induction m.

(* 0 *)
intros n s H.
simpl.
replace (n-0) with n by omega.
reflexivity.

(* S *)
intros n s H.
rewrite -> trunc_succ_inner.
rewrite -> trunc1_under.
2: omega.
rewrite -> trunc_shift_sub.
rewrite -> IHm.
2: omega.
simpl.
replace (n-1-m) with (n - S m) by omega.
reflexivity.
Qed.


Lemma trunc_under_more :
  forall m n s,
    m >= n
    -> trunc m (under n s) = trunc (m-n) (nshift_sub n s).
Proof.
intros m n s H.
replace m with ((m-n)+n) by omega.
rewrite <- trunc_sum.
f_equal.
omega.
rewrite -> trunc_under.
replace (n-n) with 0 by omega.
reflexivity.
auto.
Qed.


Lemma nshift_term_var :
  forall n i,
    nshift_term n (var i) = var (n+i).
Proof.
intros n i.
induction n.
reflexivity.
simpl.
rewrite -> IHn.
rewrite -> shift_term_var.
unfold shift_var.
destruct (lt_dec (n+1) 0).
omega_contra.
reflexivity.
Qed.


Lemma nshift_sub_dot :
  forall n t s,
    nshift_sub n (dot t s) = dot (nshift_term n t) (nshift_sub n s).
Proof.
intros n t s.
induction n.
reflexivity.
simpl.
rewrite -> IHn.
reflexivity.
Qed.


Lemma nshift_sub_sh :
  forall m n,
    nshift_sub m (sh n) = sh (m+n).
Proof.
intros m n.
induction m.
reflexivity.
simpl.
rewrite -> IHm.
reflexivity.
Qed.


Lemma project_under_lt :
  forall n s i,
    i < n
    -> project (under n s) i = var i.
Proof.
intros n s i H.
unfold project.
rewrite -> trunc_under.
2: omega.
remember (n-i) as x; destruct x.
omega_contra.
simpl.
rewrite -> nshift_sub_dot.
rewrite -> nshift_term_var.
replace (i+0) with i by omega.
reflexivity.
Qed.


Lemma project_under_ge_nshift :
  forall n s i,
    i >= n
    -> project (under n s) i = nshift_term n (project s (i-n)).
Proof.
intros n s i H.
unfold project.
rewrite -> trunc_under_more.
rewrite -> trunc_nshift_sub.
destruct (trunc (i-n) s).
3: omega.
rewrite -> nshift_sub_dot.
reflexivity.
rewrite -> nshift_sub_sh.
rewrite -> nshift_term_var.
reflexivity.
Qed.


Lemma shift_term_eq_subst_under_sh :
  forall t n,
    shift_term n t = subst (under n (sh 1)) t.
Proof.
intros t n.
unfold shift_term.
unfold subst.
apply (traverse_parametric nat sub (fun n s => s = under n (sh 1))).

(* enter *)
clear t n.
intros n s Heq.
subst s.
reflexivity.

(* resolve *)
clear t n.
intros n s i Heq.
subst s.
unfold shift_var.
destruct (lt_dec i n).

  (* i < n *)
  symmetry; apply project_under_lt; auto.

  (* i >= n *)
  rewrite -> project_under_ge_nshift by omega.
  rewrite -> project_sh.
  rewrite -> nshift_term_var.
  f_equal; omega.

(* base *)
reflexivity.
Qed.


Corollary shift_term_eq_sh :
  forall t,
    shift_term 0 t = subst (sh 1) t.
Proof.
intro t.
apply shift_term_eq_subst_under_sh.
Qed.


Corollary shift_sub_eq_compose_sh :
  forall s,
    shift_sub s = compose s (sh 1).
Proof.
intro s.
induction s.

  (* dot *)
  simpl.
  f_equal.
  apply shift_term_eq_sh.
  apply IHs.

  (* sh *)
  simpl.
  rewrite -> trunc_sh.
  f_equal; omega.
Qed.


Lemma under_zero :
  forall s, under 0 s = s.
Proof.
auto.
Qed.

Lemma under_succ :
  forall n s,
    under (S n) s = dot (var 0) (compose (under n s) (sh 1)).
Proof.
intros n s.
unfold under.
rewrite -> shift_sub_eq_compose_sh.
reflexivity.
Qed.


Lemma compose_sh :
  forall n s,
    compose (sh n) s = trunc n s.
Proof.
auto.
Qed.


Lemma trunc_compose :
  forall i s1 s2,
    trunc i (compose s1 s2) = compose (trunc i s1) s2.
Proof.
intro i.
induction i.

(* 0 *)
intros; reflexivity.

(* S *)
intros s1 s2.
destruct s1.

  (* dot *)
  simpl.
  apply IHi.

  (* sh *)
  rewrite -> trunc_sh.
  rewrite -> compose_sh.
  rewrite -> compose_sh.
  apply trunc_sum.
Qed.


Corollary project_compose :
  forall i s1 s2,
    project (compose s1 s2) i = subst s2 (project s1 i).
Proof.
intros i s1 s2.
unfold project.
rewrite -> trunc_compose.
destruct (trunc i s1).
reflexivity.
unfold subst.
rewrite -> traverse_var.
reflexivity.
Qed.


Lemma shift_term_commute :
  forall n t,
    shift_term (S n) (shift_term 0 t) = shift_term 0 (shift_term n t).
Proof.
intros n t.
unfold shift_term.
rewrite -> traverse_compose.
rewrite -> traverse_compose.
apply (traverse_parametric (nat * nat) (nat * nat)
       (fun p p' => let (m, i) := p in
        let (i', m') := p' in
                         i = i' /\ m = i+1+n /\ m' = i+n)).

(* enter *)
intros p p'.
destruct p as (m, i).
destruct p' as (i', m').
omega.

(* resolve *)
clear t.
intros p p' j H.
destruct p as (m, i).
destruct p' as (i', m').
destruct H as (H1 & H2 & H3).
subst i' m m'.
change (shift_term (i+1+n) (shift_var i j) = shift_term i (shift_var (i+n) j)).
unfold shift_var.
destruct (lt_dec j i).

  (* j < i *)
  destruct (lt_dec j (i+n)); [| omega_contra ].
  rewrite -> shift_term_var.
  rewrite -> shift_term_var.
  rewrite -> shift_var_lt by omega.
  rewrite -> shift_var_lt by omega.
  reflexivity.

  (* j >= i *)
  destruct (lt_dec j (i+n)).

    (* i <= j < i+n *)
    rewrite -> shift_term_var.
    rewrite -> shift_term_var.
    rewrite -> shift_var_lt by omega.
    rewrite -> shift_var_ge by omega.
    reflexivity.

    (* j >= i+n *)
    rewrite -> shift_term_var.
    rewrite -> shift_term_var.
    rewrite -> shift_var_ge by omega.
    rewrite -> shift_var_ge by omega.
    reflexivity.

(* base *)
omega.
Qed.


Lemma nshift_term_commute :
  forall m n t,
    m >= n
    -> shift_term m (nshift_term n t) = nshift_term n (shift_term (m-n) t).
Proof.
intros m n.
generalize dependent m.
induction n.

intros m t H.
replace (m-0) with m by omega.
reflexivity.

intros m t H.
simpl.
replace m with (S (m-1)) by omega.
rewrite -> shift_term_commute.
f_equal.
rewrite -> (IHn (m-1)) by omega.
f_equal.
Qed.


Corollary nshift_term_commute_eq :
  forall n t,
    shift_term n (nshift_term n t) = nshift_term (S n) t.
Proof.
intros n t.
rewrite -> nshift_term_succ_inner.
replace 0 with (n-n) by omega.
apply nshift_term_commute.
omega.
Qed.


Lemma subst_shift_sub :
  forall s t,
    subst (shift_sub s) t = shift_term 0 (subst s t).
Proof.
intros s t.
unfold subst.
unfold shift_term.
rewrite -> traverse_compose.
apply (traverse_parametric sub (nat * sub)
       (fun s1 p => let (n, s2) := p in s1 = under n (shift_sub s) /\ s2 = under n s)).

(* enter *)
clear t.
intros s1 (n, s2) (H1, H2).
subst s1 s2; auto.

(* resolve *)
clear t.
intros s1 (n, s2) i (H1, H2).
subst s1 s2.
destruct (lt_dec i n).

  (* i < n *)
  rewrite -> project_under_lt.
  2: omega.
  rewrite -> project_under_lt.
  2: omega.
  rewrite -> traverse_var.
  unfold shift_var.
  destruct (lt_dec i n).
  reflexivity.
  omega_contra.

  (* i >= n *)
  unfold project.
  rewrite -> trunc_under_more by omega.
  rewrite -> trunc_under_more by omega.
  rewrite -> trunc_nshift_sub.
  rewrite -> trunc_nshift_sub.
  rewrite -> trunc_shift_sub.
  rewrite <- nshift_sub_succ_inner.
  destruct (trunc (i-n) s).

  rewrite -> nshift_sub_dot.
  rewrite -> nshift_sub_dot.
  fold (shift_term n (nshift_term n t)).
  symmetry; apply nshift_term_commute_eq.

  rewrite -> nshift_sub_sh.
  rewrite -> nshift_sub_sh.
  simpl.
  rewrite -> traverse_var.
  unfold shift_var.
  destruct (lt_dec (n+n1) n).
  omega_contra.
  reflexivity.

(* base *)
auto.
Qed.


Lemma shift_sub_trunc :
  forall s n,
    shift_sub (trunc n s) = trunc n (shift_sub s).
Proof.
intro s.
induction s.

(* dot *)
intro n.
destruct n.
reflexivity.
apply IHs.

(* sh *)
intro m.
simpl.
rewrite -> trunc_sh.
rewrite -> trunc_sh.
simpl.
f_equal; omega.
Qed.


Lemma compose_shift_sub_left :
  forall s1 s2,
    compose s1 (shift_sub s2) = shift_sub (compose s1 s2).
Proof.
intros s1 s2.
induction s1.
simpl.
f_equal.
apply subst_shift_sub.
apply IHs1.
simpl.
symmetry.
apply shift_sub_trunc.
Qed.


Lemma subst_dot_shift_term :
  forall t s t',
    subst (dot t s) (shift_term 0 t') = subst s t'.
Proof.
intros t s t'.
unfold subst; unfold shift_term.
rewrite -> traverse_compose.
apply (traverse_parametric (sub * nat) sub
         (fun p s2 => let (s1, i) := p in s1 = under i (dot t s) /\ s2 = under i s)).

(* enter *)
clear t'.
intros p s2 H.
destruct p as (s1, i).
destruct H.
subst s1 s2.
auto.

(* resolve *)
clear t'.
intros p s2 j H.
destruct p as (s1, i).
destruct H.
subst s1 s2.
fold (subst (under i (dot t s)) (shift_var i j)).
unfold shift_var.
destruct (lt_dec j i).

  (* j < i *)
  rewrite -> subst_var.
  rewrite -> project_under_lt by assumption.
  rewrite -> project_under_lt by assumption.
  reflexivity.

  (* j >= i *)
  rewrite -> subst_var.
  rewrite -> project_under_ge_nshift by omega.
  rewrite -> project_under_ge_nshift by omega.
  f_equal.
  replace (S j - i) with (S (j-i)) by omega.
  rewrite -> project_dot.
  reflexivity.

(* base *)
auto.
Qed.


Lemma compose_shift_sub_right :
  forall s1 s2 t,
    compose (shift_sub s1) (dot t s2) = compose s1 s2.
Proof.
intros s1 s2 t.
induction s1.

(* dot *)
simpl.
f_equal.
apply subst_dot_shift_term.
apply IHs1.
reflexivity.
Qed.


Lemma subst_compose :
  forall t s1 s2,
    subst (compose s2 s1) t = subst s1 (subst s2 t).
Proof.
intros t s1 s2.
unfold subst.
rewrite -> traverse_compose.
apply (traverse_parametric sub (sub * sub) (fun s p => let (s1, s2) := p in s = compose s2 s1)).

(* enter *)
clear t s1 s2.
intros s p H.
destruct p as (s1, s2).
subst s.
simpl.
f_equal.
rewrite <- compose_shift_sub_left.
rewrite -> compose_shift_sub_right.
reflexivity.

(* resolve *)
clear t s1 s2.
intros s p i H.
destruct p as (s1, s2).
subst s.
apply project_compose.

(* base *)
reflexivity.
Qed.


Lemma compose_assoc :
  forall s1 s2 s3,
    compose (compose s1 s2) s3 = compose s1 (compose s2 s3).
Proof.
intros s1 s2 s3.
symmetry.
induction s1.

(* dot *)
simpl.
f_equal.
apply subst_compose.
apply IHs1.

(* sh *)
rewrite -> compose_sh.
rewrite -> compose_sh.
apply trunc_compose.
Qed.


Lemma compose_dot :
  forall t s1 s2,
    compose (dot t s1) s2 = dot (subst s2 t) (compose s1 s2).
Proof.
auto.
Qed.


Lemma compose_sh_0 :
  forall s,
    compose (sh 0) s = s.
Proof.
auto.
Qed.


Lemma compose_sh_succ_dot :
  forall t s n,
    compose (sh (S n)) (dot t s) = compose (sh n) s.
Proof.
auto.
Qed.


Lemma compose_sh_sh :
  forall m n,
    compose (sh m) (sh n) = sh (m+n).
Proof.
intros m n.
simpl.
rewrite -> trunc_sh.
f_equal.
Qed.


Corollary compose_id_left :
  forall s,
    compose id s = s.
Proof.
apply compose_sh_0.
Qed.


Lemma subst_under_id :
  forall n t,
    subst (under n id) t = t.
Proof.
intros m t.
unfold subst.
apply (traverse_id sub (fun s => exists n, s = under n id)).

(* enter *)
clear t.
intros s (n, H).
subst s.
exists (S n).
reflexivity.

(* resolve *)
clear t.
intros s i (n, H).
subst s.
destruct (lt_dec i n).

  (* i < n *)
  apply project_under_lt; assumption.

  (* i >= n *)
  rewrite -> project_under_ge_nshift by omega.
  unfold id.
  rewrite -> project_sh.
  rewrite -> nshift_term_var.
  f_equal.
  omega.

(* base *)
exists m.
reflexivity.
Qed.


Corollary subst_id :
  forall t,
    subst id t = t.
Proof.
intro t.
change (subst (under 0 id) t = t).
apply subst_under_id.
Qed.


Lemma compose_id_right :
  forall s,
    compose s id = s.
Proof.
intro s.
induction s.
simpl.
f_equal.
apply subst_id.
apply IHs.
simpl.
unfold id.
rewrite -> trunc_sh.
f_equal; omega.
Qed.


Lemma trunc_eq_compose_sh :
  forall n s,
    trunc n s = compose (sh n) s.
Proof.
intros n s.
destruct n; auto.
Qed.


Corollary subst1_shift1 :
  forall t t', subst1 t (shift1 t') = t'.
Proof.
intros t t'.
unfold subst1.
unfold shift1.
rewrite <- subst_compose.
unfold sh1.
rewrite -> compose_sh_succ_dot.
rewrite -> compose_sh_0.
apply subst_id.
Qed.


Lemma dist_compose_under :
  forall n s1 s2,
    compose (under n s1) (under n s2) = under n (compose s1 s2).
Proof.
intros n s1 s2.
induction n.
(* 0 *)
rewrite -> !under_zero.
reflexivity.

(* S *)
rewrite -> !under_succ.
rewrite -> compose_dot.
f_equal.
rewrite -> compose_assoc.
rewrite -> compose_sh_succ_dot.
rewrite -> compose_sh_0.
rewrite <- compose_assoc.
rewrite -> IHn.
reflexivity.
Qed.


Hint Unfold id sh1 shift1 subst1 : subst.
Hint Rewrite project_zero project_dot project_sh : subst.
Hint Rewrite subst_id subst1_shift1 : subst.
Hint Rewrite compose_dot compose_sh_0 compose_sh_succ_dot compose_sh_sh compose_id_left compose_id_right : subst.
Hint Rewrite compose_assoc : subst.
Hint Rewrite <- subst_compose : subst.
Hint Rewrite under_zero under_succ dist_compose_under : subst.
Hint Rewrite shift_sub_eq_compose_sh : subst.


(* Now that we're done, we'll allow traverse to be transparent. *)
Transparent traverse.


Ltac fold_subst1
  :=
  repeat
  (match goal with
   | |- appcontext [subst (dot ?t id)] => fold (subst1 t)
   end).


Tactic Notation "fold_subst1" "in" hyp(H)
  :=
  repeat
  (match type of H with
   | appcontext [subst (dot ?t id)] => fold (subst1 t) in H
   end).


Ltac reduce_subst
  :=
  progress (unfold subst; cbv beta iota delta [traverse]; repeat (fold traverse); repeat (fold subst)).


Tactic Notation "reduce_subst" "in" hyp(H)
  :=
  progress (unfold subst in H; cbv beta iota delta [traverse] in H |-; repeat (fold traverse in H); repeat (fold subst in H)).


Ltac reduce_sub
  :=
  try (repeat (autounfold with subst
               || autorewrite with subst 
               || reduce_subst)).


Tactic Notation "reduce_sub" "in" hyp(H)
  :=
  try (repeat (autounfold with subst in H
               || autorewrite with subst in H
               || reduce_subst in H)).


Ltac cleanup_sub
  :=
  repeat (fold id); repeat (fold sh1); repeat (fold shift1); repeat fold_subst1; repeat calculate.


Tactic Notation "cleanup_sub" "in" hyp(H)
  :=
  repeat (fold id in H); repeat (fold sh1 in H); repeat (fold shift1 in H); repeat (fold_subst1 in H); repeat (calculate in H).


Ltac simp_sub
  :=
  reduce_sub; cleanup_sub.


Tactic Notation "simp_sub" "in" hyp(H)
  :=
  reduce_sub in H; cleanup_sub in H.


Corollary subst_bind :
  forall s t1 t2,
    subst (dot (subst s t1) s) t2 = subst1 (subst s t1) (subst (dot (var 0) (compose s sh1)) t2).
Proof.
intros s t1 t2.
simp_sub.
auto.
Qed.


Lemma subst_sh_invert :
  forall n t t',
    subst (sh n) t = subst (sh n) t'
    -> t = t'.
Proof.
intros n t t' H.
induction n.
simp_sub in H.
auto.

assert (subst (dot nonsense id) (subst (sh (S n)) t) = subst (dot nonsense id) (subst (sh (S n)) t')) as H' by (f_equal; auto).
simp_sub in H'.
apply IHn; auto.
Qed.


Corollary nshift_term_eq_sh :
  forall n t,
    nshift_term n t = subst (sh n) t.
Proof.
intros n t.
induction n.
(* 0 *)
simp_sub.
auto.

(* S *)
simpl.
rewrite -> IHn.
rewrite -> shift_term_eq_sh.
simp_sub.
reflexivity.
Qed.


Corollary project_under_ge :
  forall n s i,
    i >= n
    -> project (under n s) i = subst (sh n) (project s (i-n)).
Proof.
intros.
rewrite -> project_under_ge_nshift; [| auto].
rewrite -> nshift_term_eq_sh.
auto.
Qed.


Lemma unshift_var :
  forall i m n t,
    var i = subst (under m (sh n)) t
    -> (i < m /\ t = var i)
       \/ (i >= m+n /\ t = var (i-n)).
Proof.
intros i m n t Heq.
assert (forall u, (i < m /\ t = var i) \/ (i >= m /\ i < m+n /\ t=subst (sh m) u) \/ (i >= m+n /\ t = var (i-n))) as Htri.
  (* prove assertion *)
  intro u.
  set (f := (fix f (j:nat) := match j with 0 => id | S j' => dot u (f j') end)).
  assert (subst (under m (f n)) (var i) = subst (under m (f n)) (subst (under m (sh n)) t))
      as Heqt by (f_equal; auto).
  clear Heq.
  simp_sub in Heqt.
  assert (compose (sh n) (f n) = id) as Heqf.
    toshow (compose (sh n) (f n) = id).
    clear Heqt.
    induction n.
    (* 0 *)
    simp_sub; auto.

    (* S *)
    replace (f (S n)) with (dot u (f n)) by auto.
    simp_sub; auto.
  have (compose (sh n) (f n) = id) as Heqf.
  rewrite -> Heqf in Heqt.
  clear Heqf.
  rewrite -> subst_under_id in Heqt.
  destruct (lt_dec i m) as [Hltm | Hgem].
    have (i < m) as Hltm.
    left.
    split; auto.
    toshow (t = var i).
    rewrite -> project_under_lt in Heqt; auto.

    have (~ i < m) as Hgem.
    right.
    rewrite -> project_under_ge in Heqt; [| omega].
    destruct (lt_dec i (m+n)) as [Hltmn | Hgemn].
      have (i < m + n) as Hltmn.
      left.
      do 2 (split; [omega |]).
      subst t.
      toshow (subst (sh m) (project (f n) (i - m)) = subst (sh m) u).
      assert (i - m < n) as Hlt by omega.
      clear Hgem Hltmn.
      revert n Hlt.
      generalize (i-m) as j.
      intro j.
      induction j.
      (* 0 *)
      intros.
      have (0 < n) as Hlt.
      toshow (subst (sh m) (project (f n) 0) = subst (sh m) u).
      replace n with (S (n-1)) by omega.
      auto.

      (* S *)
      intros.
      have (S j < n) as Hlt.
      have (forall n : nat,
            j < n -> subst (sh m) (project (f n) j) = subst (sh m) u) as IHj.
      toshow (subst (sh m) (project (f n) (S j)) = subst (sh m) u).
      replace n with (S (n-1)) by omega.
      simpl.
      rewrite -> project_dot.
      apply IHj.
      omega.

      have (~ i < m + n) as Hgemn.
      clear Hgem.
      right.
      split; [omega |].
      toshow (t = var (i - n)).
      replace (project (f n) (i-m)) with (var (i-m-n)) in Heqt.
        have (subst (sh m) (var (i - m - n)) = t) as Heqt.
        subst t.
        simp_sub.
        f_equal.
        omega.

        toshow (var (i - m - n) = project (f n) (i - m)).
        assert (i-m >= n) as Hge by omega.
        clear Heqt Hgemn.
        revert Hge.
        generalize (i-m) as j.
        induction n.
        (* 0 *)
        intros.
        toshow (var (j - 0) = project (f 0) j).
        simpl.
        unfold id.
        rewrite -> project_sh.
        f_equal; omega.

        (* S *)
        intros.
        have (j >= S n) as Hge.
        have (forall j : nat, j >= n -> var (j - n) = project (f n) j) as IHn.
        toshow (var (j - S n) = project (f (S n)) j).
        replace j with (S (j-1)) by omega.
        simpl.
        rewrite -> project_dot.
        apply IHn.
        omega.

  have (forall u : term,
        i < m /\ t = var i \/
        i >= m /\ i < m + n /\ t = subst (sh m) u \/
        i >= m + n /\ t = var (i - n)) as Htri.
  (* two distinct terms *)
  set (u1 := var 0).
  set (u2 := var 1).
  destruct (Htri u1) as [Hleft | [Hmid | Hright]].
    left; auto.

    have (i >= m /\ i < m + n /\ t = subst (sh m) u1) as Hmid.
    destruct Hmid as (_ & _ & H1).
    destruct (Htri u2) as [Hleft | [Hmid' | Hright]].
      left; auto.

      have (i >= m /\ i < m + n /\ t = subst (sh m) u2) as Hmid'.
      destruct Hmid' as (_ & _ & H2).
      subst u1 u2 t.
      simp_sub in H2.
      injection H2.
      intro.
      exfalso; omega.

      right; auto.

    right; auto.
Qed.


Lemma under_succ2 :
  forall n s,
    under (S (S n)) s = dot (var 0) (dot (var 1) (compose (under n s) (sh 2))).
Proof.
intros n s.
rewrite -> !under_succ.
simp_sub.
reflexivity.
Qed.


Lemma compose_sh_under :
  forall m n s,
    m <= n
    -> compose (sh m) (under n s) = compose (under (n-m) s) (sh m).
Proof.
intros m n s Hlt.
revert n Hlt.
induction m.
(* 0 *)
intros.
replace (n-0) with n by omega.
simp_sub.
reflexivity.

(* S *)
intros.
replace n with (S (n-1)) by omega.
rewrite -> under_succ.
rewrite -> compose_sh_succ_dot.
rewrite <- compose_assoc.
rewrite -> IHm; [| omega].
rewrite -> compose_assoc.
rewrite -> compose_sh_sh.
f_equal; f_equal; omega.
Qed.


Corollary compose_sh_under_all :
  forall n s,
    compose (sh n) (under n s) = compose s (sh n).
Proof.
intros n s.
rewrite -> compose_sh_under; [| omega].
replace (n-n) with 0 by omega.
rewrite -> under_zero.
reflexivity.
Qed.


Corollary compose_sh_under_more :
  forall m n s,
    m >= n
    -> compose (sh m) (under n s) = compose (compose (sh (m-n)) s) (sh n).
Proof.
intros m n s Hge.
repl m with ((m-n)+n) at 1 by omega.
rewrite <- compose_sh_sh.
rewrite -> !compose_assoc.
f_equal.
apply compose_sh_under_all.
Qed.


Corollary compose_sh_under2 :
  forall m n s,
    compose (sh m) (under (m+n) s) = compose (under n s) (sh m).
Proof.
intros m n s.
rewrite -> compose_sh_under; [| omega].
replace (m+n-m) with n by omega.
reflexivity.
Qed.


Corollary shift1_subst_under :
  forall n s t,
    shift1 (subst (under n s) t) = subst (under (S n) s) (shift1 t).
Proof.
intros n s t.
unfold shift1, sh1.
rewrite <- !subst_compose.
rewrite <- compose_sh_under2.
reflexivity.
Qed.


Corollary under_plus2 :
  forall n s,
    under (2 + n) s = dot (var 0) (dot (var 1) (compose (under n s) (sh 2))).
Proof.
intros n s.
replace (2 + n) with (S (S n)) by omega.
simp_sub.
reflexivity.
Qed.


Fixpoint unsh (n : nat) {struct n} : sub :=
  (match n with
   | 0 => sh 0
   | S n' => dot nonsense (unsh n')
   end).


Lemma compose_sh_unsh : 
  forall n,
    compose (sh n) (unsh n) = id.
Proof.
intro n.
induction n.
(* 0 *)
unfold unsh.
rewrite -> compose_sh_sh.
reflexivity.

(* S *)
simpl unsh.
rewrite -> compose_sh_succ_dot.
assumption.
Qed.


Definition closed (t : term) := shift1 t = t.
Definition closedn (n : nat) (t : term) := subst (under n sh1) t = t.


Lemma closed_closedn :
  forall t,
    closed t <-> closedn 0 t.
Proof.
intro t.
split.
  intro H.
  unfold closedn.
  simp_sub.
  assumption.

  intro H.
  unfold closedn in H.
  simp_sub in H.
  assumption.
Qed.


Lemma closedn_subst :
  forall n t s,
    closedn n t
    -> subst (under n s) t = t.
Proof.
intros n t s Hclo.
induction s as [t' s | m].
(* dot *)
repl t with (subst (under n sh1) t) at 1 by (exact Hclo).
simp_sub.
assumption.

(* sh *)
induction m as [| m IH].
  (* 0 *)
  simp_sub.
  rewrite -> subst_under_id.
  reflexivity.

  (* S *)
  repl t with (subst (under n sh1) t) in IH at 1 by (exact Hclo).
  simp_sub in IH.
  calculate.
  assumption.
Qed.


Lemma closed_subst :
  forall t s,
    closed t
    -> subst s t = t.
Proof.
intros t s Hclo.
repl s with (under 0 s) by auto.
apply closedn_subst.
assumption.
Qed.


Lemma subst_closed :
  forall s t,
    closed t
    -> closed (subst s t).
Proof.
intros s t Hclosed.
unfold closed.
simp_sub.
rewrite -> !closed_subst; auto.
Qed.


Lemma closedn_var :
  forall i n,
    closedn n (var i)
    -> i < n.
Proof.
intros i n Hclo.
unfold closedn in Hclo.
simp_sub in Hclo.
so (lt_dec i n) as [Hlt | Hgeq]; auto; [].
exfalso.
rewrite -> project_under_ge in Hclo; [| omega].
simp_sub in Hclo.
injection Hclo.
omega.
Qed.


Lemma open_var :
  forall i, ~ closed (var i).
Proof.
intros i Hclo.
assert (i < 0); [| omega].
apply closedn_var.
exact (closed_closedn _ andel Hclo).
Qed.


Tactic Notation "reduce_closed" "in" hyp(H)
  :=
  (lazymatch type of H with
   | closed _ => idtac 
   | closedn _ _ => idtac 
   | _ => fail
   end);
  unfold closed, closedn in H;
  simp_sub in H;
  injection H;
  clear H;
  repeat (match goal with
          | |- context [ shift1 ?t = ?t ] => fold (closed t)
          | |- context [ subst (under ?n sh1) ?t = ?t ] => fold (closedn n t)
          end).


Tactic Notation "reduce_closed"
  :=
  (lazymatch goal with
   | |- closed _ => idtac 
   | |- closedn _ _ => idtac 
   | |- _ => fail
   end);
  unfold closed, closedn;
  simp_sub;
  f_equal;
  repeat (match goal with
          | |- context [ shift1 ?t = ?t ] => fold (closed t)
          | |- context [ subst (under ?n sh1) ?t = ?t ] => fold (closedn n t)
          end).
