Require Import Tactics.
Require Export List.
Require Import PreSyntax.
Require Import Decidable.
Require Import Omega.

(* General list facts *)

Lemma app_eq_cons :
  forall (A : Type) (x : A) l l1 l2,
    x :: l = l1 ++ l2
    -> (exists l1',
          l1 = x :: l1'
          /\ l = l1' ++ l2)
       \/ (l1 = nil
           /\ l2 = x :: l).
Proof.
intros A x l l1 l2 Heq.
destruct l1 as [| y l1'].
(* nil *)
have (x :: l = nil ++ l2) as Heq.
right.
split; auto.

(* cons *)
have (x :: l = (y :: l1') ++ l2) as Heq.
left.
simpl in Heq.
injection Heq; intros.
exists l1'; split; auto.
f_equal; auto.
Qed.


Lemma app_eq_app :
  forall (A : Type) (l1 l2 l1' l2' : list A),
    l1 ++ l2 = l1' ++ l2'
    -> (exists x l,
          l1 = l1' ++ x :: l
          /\ x :: l ++ l2 = l2')
       \/ (l1 = l1' /\ l2 = l2')
       \/ (exists x l,
             l1 ++ x :: l = l1'
             /\ l2 = x :: l ++ l2').
Proof.
intros A l1 l2 l1' l2' Heq.
revert l1' Heq.
induction l1 as [| x l].
(* nil *)
intros.
destruct l1' as [| x l].
  (* nil *)
  simpl in Heq.
  right; left.
  split; auto.

  (* cons *)
  simpl in Heq.
  right; right.
  exists x, l.
  simpl; auto.

(* cons *)
intros.
destruct l1' as [| x' l'].
  (* nil *)
  simpl in Heq.
  left.
  exists x, l.
  simpl; auto.

  (* cons *)
  simpl in Heq.
  injection Heq.
  intros Heqapp Heqx.
  subst x'.
  destruct (IHl l' Heqapp) as [(y & ll & Heql & Heqr) | [(Heql & Heqr) | (y & ll & Heql & Heqr)]].
    left.
    exists y, ll.
    simpl.
    split.
      f_equal; auto.

      auto.

    right; left.
    split.
      f_equal; auto.

      auto.

    right; right.
    exists y, ll.
    simpl.
    split.
      f_equal; auto.

      auto.
Qed.


Lemma app_eq_app2 :
  forall (A : Type) (l1 l2 l1' l2' : list A),
    l1 ++ l2 = l1' ++ l2'
    -> (exists x l,
          l1 = l1' ++ x :: l
          /\ x :: l ++ l2 = l2')
       \/ (exists l,
             l1 ++ l = l1'
             /\ l2 = l ++ l2').
Proof.
intros A l1 l2 l1' l2' Heq.
pose proof (app_eq_app _#5 Heq) as [(x & l & Heq1 & Heq2) | [(Heq1 & Heq2) | (x & l & Heq1 & Heq2)]].
  left.
  do 2 eexists; eauto.

  right.
  exists nil.
  split.
    rewrite -> app_nil_r.
    auto.

    simpl; auto.

  right.
  eexists; eauto.
Qed.


Lemma app_nonempty_eq_cons :
  forall (A : Type) (x : A) l l1 l2,
    x :: l = l1 ++ l2
    -> length l1 > 0
    -> In x l1.
Proof.
intros A x l l1 l2 Heq Hlen.
destruct l1.
  simpl in Hlen.
  omega.

  simpl in Heq.
  injection Heq; intros.
  subst x.
  left.
  reflexivity.
Qed.


Import ListNotations.


Lemma list_invert_snoc :
  forall (A : Type) (l : list A),
    l = nil \/ (exists t x, l = t ++ [x]).
Proof.
intros A l.
induction l.

(* nil *)
left; reflexivity.

(* cons *)
right.
destruct IHl as [-> | (t & x & ->)].
  exists nil, a.
  reflexivity.

  exists (a :: t), x.
  reflexivity.
Qed.


Lemma app_eq_snoc :
  forall (A : Type) (x : A) l l1 l2,
    l ++ [x] = l1 ++ l2
    -> (exists l2',
          l2 = l2' ++ [x]
          /\ l = l1 ++ l2')
       \/ (l2 = nil
           /\ l1 = l ++ [x]).
Proof.
intros A x l l1 l2 Heq.
f_apply (@rev A) in Heq as Heq'.
rewrite -> rev_unit, -> rev_app_distr in Heq'.
so (app_eq_cons _#5 Heq') as [(l2r & Heq2 & Heq'') | (Heq2 & Heq1)].
  left.
  exists (rev l2r).
  split.
    rewrite <- (rev_involutive l2r), <- rev_unit in Heq2.
    f_apply (@rev A) in Heq2 as Heq2'.
    rewrite -> !rev_involutive in Heq2'.
    assumption.

    rewrite <- (rev_involutive l2r), <- rev_app_distr in Heq''.
    f_apply (@rev A) in Heq'' as Heq'''.
    rewrite -> !rev_involutive in Heq'''.
    assumption.

  right.
  split.
    f_apply (@rev A) in Heq2 as Heq2'.
    rewrite -> rev_involutive in Heq2'.
    simpl in Heq2'.
    assumption.

    rewrite <- rev_unit in Heq1.
    f_apply (@rev A) in Heq1 as Heq1'.
    rewrite -> !rev_involutive in Heq1'.
    assumption.
Qed.


Lemma first_neq_middle_invert :
  forall (A : Type) (x y : A) l l1 l2,
    x :: l = l1 ++ y :: l2
    -> x <> y
    -> exists l1',
         l1 = x :: l1'
         /\ l = l1' ++ y :: l2.
Proof.
intros A x y l l1 l2 Heq Hneqxy.
so (app_eq_cons _#5 Heq) as [? | (_ & Heq')].
  assumption.

  injection Heq'; intros _ Heqyx.
  findcontra.
Qed.


Lemma middle_ordering :
  forall (A : Type) (l l1 l2 l3 l4 : list A) (x y : A),
    l = l1 ++ x :: l2
    -> l = l3 ++ y :: l4
    -> x <> y
    -> ~ In y l2
    -> exists l5,
         l1 = l3 ++ y :: l5
         /\ l5 ++ x :: l2 = l4.
Proof.
intros A l l1 l2 l3 l4 x y -> Heq Hneq Hnin.
so (app_eq_app2 _#5 Heq) as [(z & l5 & Heq1 & Heq4) | (l6 & _ & Heq2)].
  injection Heq4; clear Heq4.
  intros Heq4' ->.
  exists l5.
  split; auto; done.

  so (first_neq_middle_invert _#6 Heq2 Hneq) as (l7 & _ & Heq2').
  destruct Hnin.
  subst l2.
  apply in_or_app; right; left; reflexivity.
Qed.


Lemma app_eq_cons_invert :
  forall (A : Type) (x : A) l l',
    x :: l = l' ++ l
    -> l' = x :: nil.
Proof.
intros A x l l' Heq.
replace (x :: l) with ((x :: nil) ++ l) in Heq by auto.
symmetry.
eapply app_inv_tail; eauto.
Qed.


Lemma Forall_map :
  forall (A B : Type) (P : B -> Prop) (f : A -> B) (l : list A),
    Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
intros A B P f l.
split.
  intro Hall.
  induction l.
    apply Forall_nil; done.

    invert Hall; intros.
    apply Forall_cons; auto; done.

  intro Hall.
  induction Hall.
    apply Forall_nil; done.

    apply Forall_cons; auto; done.
Qed.


Lemma Forall_map_weaken :
  forall (A B : Type) (P : B -> Prop) (f : A -> B) (l : list A),
    (forall x, P (f x))
    -> Forall P (map f l).
Proof.
intros A B P f l H.  
induction l.
apply Forall_nil.

apply Forall_cons.
  apply H.

  auto.
Qed.


Lemma Forall_universal :
  forall (T : Set) (P : T -> Prop) (l : list T),
    (forall x, P x)
    -> Forall P l.
Proof.
intros T P l H.
induction l.
  apply Forall_nil; done.

  apply Forall_cons; auto; done.
Qed.


Lemma Forall_not_Exists :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Forall (fun x => ~ P x) l
    -> ~ Exists P l.
Proof.
intros A P l Hall.
induction l.
(* nil *)
intro H.
invert H; done.

(* cons *)
intro H.
invert Hall; intros Ha' Hl.
invert H; intros Ha.
  contradict Ha'; auto.

  revert Ha.
  apply IHl.
  auto.
Qed.


Lemma Forall_app :
  forall (T : Type) (P : T -> Prop) (l1 l2 : list T),
    Forall P l1
    -> Forall P l2
    -> Forall P (l1 ++ l2).
Proof.
intros T P l1 l2 H1 H2.
induction l1.
(* nil *)
simpl; auto.

(* cons *)
simpl.
invert H1; intros.
apply Forall_cons; auto.
Qed.


Lemma Forall_impl_2 :
  forall (T : Set) (P Q R : T -> Prop),
    (forall x, P x -> Q x -> R x)
    -> forall l, Forall P l -> Forall Q l -> Forall R l.
Proof.
intros T P Q R Himp l HP HQ.
induction l.
  apply Forall_nil; done.

  invert HP; invert HQ; intros.
  apply Forall_cons; auto; done.
Qed.


Lemma Forall_cdr :
  forall (A : Type) (P : A -> Prop) x l,
    Forall P (x :: l) -> Forall P l.
Proof.
intros A P x l H.
invert H; auto.
Qed.


Lemma In_ind :
  forall (T : Set) (P : T -> list T -> Prop),
    (forall t l, P t (t :: l))
    -> (forall t t' l, In t l -> P t l -> P t (t' :: l))
    -> forall t l, In t l -> P t l.
Proof.
intros T P Hhit Hmiss t l Hin.
revert Hin.
elim l; clear l.
(* nil *)
intro Hin.
invert Hin; done.

(* cons *)
intros t' l IH Hin.
destruct Hin as [Heq | Hin'].
  have (t' = t) as Heq.
  subst t'.
  apply Hhit.

  apply Hmiss; auto.
Qed.

      
Lemma in_split_2 :
  forall (A : Type) (x y : A) l,
    In x l
    -> In y l
    -> (exists l1 l2 l3, l = l1 ++ x :: l2 ++ y :: l3)
       \/ (x = y /\ exists l1 l2, l = l1 ++ x :: l2)
       \/ (exists l1 l2 l3, l = l1 ++ y :: l2 ++ x :: l3).
Proof.
intros A x y l Hinx Hiny.
pose proof (in_split _#3 Hinx) as (l1 & l2 & Heq).
rewrite -> Heq in Hiny.
destruct (in_app_or _#4 Hiny) as [Hiny' | Hiny'].
  right; right.
  pose proof (in_split _#3 Hiny') as (l3 & l4 & Heq').
  exists l3, l4, l2.
  rewrite -> Heq' in Heq.
  rewrite <- app_assoc in Heq.
  rewrite <- app_comm_cons in Heq.
  assumption.

  simpl in Hiny'.
  destruct Hiny' as [Heqxy | Hiny''].
    right; left.
    split; auto.
    exists l1, l2.
    assumption.

    left.
    pose proof (in_split _#3 Hiny'') as (l3 & l4 & Heq').
    exists l1, l3, l4.
    rewrite <- Heq'.
    assumption.
Qed.


Lemma app_eq_length :
  forall (T : Set) (l1 l2 l1' l2' : list T),
    l1 ++ l2 = l1' ++ l2'
    -> length l1 = length l1'
    -> l1 = l1' /\ l2 = l2'.
Proof.
intros T l1 l2 l1' l2' Heq Hlen.
revert l1' Heq Hlen.
induction l1.
(* nil *)
intros.
destruct l1'.
  auto.

  discriminate Hlen.

(* cons *)
intros.
destruct l1'.
  discriminate Hlen.

  destruct (IHl1 l1').
    injection Heq; auto.

    injection Hlen; auto.
  split; auto.
  f_equal; auto.
  injection Heq; auto.
Qed.


Lemma split_app_length :
  forall (T : Set) (l1 l2 l1' l2' : list T),
    length l1 = length l1'
    -> l1 ++ l2 = l1' ++ l2'
    -> l1 = l1' /\ l2 = l2'.
Proof.
intros T l1 l2 l1' l2'.
revert l1'.
induct l1.
(* nil *)
intros.
destruct l1'; try discriminate.
auto; done.

(* cons *)
intros x l IH l1' Hlen Happ.
destruct l1' as [| x' l']; try discriminate.
injection Hlen; clear Hlen; intro Hlen.
injection Happ; clear Happ; intros Happ Heqx.
subst x'.
so (IH l' Hlen Happ) as (Heql & Heql2).
split; f_equal; auto.
Qed.


Hint Rewrite <- app_assoc app_comm_cons : canonlist.
Hint Rewrite -> app_nil_l app_nil_r : canonlist.


(* Lists indexed numerically. *)

Inductive truncate {T:Set} : nat -> list T -> list T -> Prop :=
| truncate_0 {l}
    : truncate 0 l l

| truncate_S {i x l l'}
    : truncate i l l'
      -> truncate (S i) (x :: l) l'.


Inductive index {T:Set} : nat -> list T -> T -> Prop :=
| index_0 {x l}
    : index 0 (x :: l) x
| index_S {n x l y}
    : index n l y
      -> index (S n) (x :: l) y.


Hint Constructors truncate index : sequence.


Lemma index_truncate :
  forall (T:Set) i l (x:T),
    index i l x
    -> exists l', truncate i l (x :: l').
Proof.
intros T i.
induction i.
(* 0 *)
intros l x H.
inversion H; subst.
rename l0 into l.
have (index 0 (x :: l) x) as H.
toshow (exists l', truncate 0 (x :: l) (x :: l')).
esplit.
apply truncate_0.

(* S *)
intros l x H.
inversion H; subst.
rename l0 into l.
have (index i l x) as H1.
have (forall (l : list T) (x : T),
        index i l x -> exists l' : list T, truncate i l (x :: l')) as IHi.
toshow (exists l' : list T, truncate (S i) (x0 :: l) (x :: l')).
thus (exists l' : list T, truncate i l (x :: l')) as H2 by IHi.
destruct H2 as [l' H3].
exists l'.
apply truncate_S.
apply H3.
Qed.


Lemma truncate_index :
  forall (T:Set) i l (x:T) l',
    truncate i l (x :: l')
    -> index i l x.
Proof.
intros T i.
induction i.
(* 0 *)
intros l x l' H.
inversion H; subst.
have (truncate 0 (x :: l') (x :: l')) as H.
toshow (index 0 (x :: l') x).
apply index_0.

(* S *)
intros l x l' H.
inversion H; subst.
have (truncate i l0 (x :: l')) as H1.
have (forall (l : list T) (x : T) (l' : list T),
        truncate i l (x :: l') -> index i l x) as IHi.
toshow (index (S i) (x0 :: l0) x).
apply index_S.
toshow (index i l0 x).
eapply IHi.
apply H1.
Qed.


Lemma truncate_sum :
  forall (T:Set) m n (l:list T) l' l'',
    truncate m l l'
    -> truncate n l' l''
    -> truncate (m+n) l l''.
Proof.
intros T m n l l' l'' H1 H2.
revert H2; induct H1.
(* 0 *)
intros l H2.
have (truncate n l l'') as H2.
toshow (truncate (0+n) l l'').
calculate.
apply H2; done.

(* S *)
intros i x l l' _ IH H.
have (truncate n l' l'' -> truncate (i + n) l l'') as IH.
have (truncate n l' l'') as H.
toshow (truncate (S i + n) (x :: l) l'').
thus (truncate (i + n) l l'') as H' by IH.
replace (S i + n) with (S (i+n)) by omega.
apply truncate_S; auto; done.
Qed.


Corollary truncate_succ :
  forall (T:Set) n (x:T) l l',
    truncate n l (x :: l')
    -> truncate (S n) l l'.
Proof.
intros T n x l l' H.
replace (S n) with (n+1) by omega.
eapply truncate_sum.
apply H.
auto with sequence.
Qed.


Corollary truncate_index_sum :
  forall (T:Set) m n (l:list T) l' x,
    truncate m l l'
    -> index n l' x
    -> index (m+n) l x.
Proof.
intros T m n l l' x Htrunc Hindex.
thus (exists l'', truncate n l' (x :: l'')) as Htruncex by index_truncate.
destruct Htruncex as  [l'' Htrunc'].
thus (truncate (m+n) l (x :: l'')) as H by truncate_sum.
eapply truncate_index.
apply H.
Qed.


Lemma truncate_length :
  forall (T:Set) n (l:list T) l',
    truncate n l l'
    -> length l = n + length l'.
Proof.
intros T n l l' H.
induction H.
auto.  
simpl.
omega.
Qed.


Lemma truncate_all :
  forall (A : Set) (l : list A),
    truncate (length l) l nil.
Proof.
intros A l.
induction l; simpl; auto with sequence.
Qed.


Lemma index_length :
  forall (T:Set) (l : list T) i x,
    index i l x
    -> i < length l.
Proof.
intros T l i x H.
pose proof (index_truncate _#4 H) as (l' & H').
pose proof (truncate_length _#4 H') as Heq.
simpl in Heq.
omega.
Qed.


Lemma index_app_lt :
  forall (T:Set) (l1 l2:list T) i x,
    i < length l1
    -> index i (l1 ++ l2) x
    -> index i l1 x.
Proof.
intros T l1 l2 i x Hlt Hindex.
revert l1 Hlt Hindex.
induction i.
(* 0 *)
intros.
destruct l1.
  simpl in Hlt; exfalso; omega.

  simpl in Hindex.
  invert Hindex; intros.
  subst t.
  apply index_0; done.

(* S *)
intros.
destruct l1.
  simpl in Hlt; exfalso; omega.

  simpl in Hindex.
  invert Hindex; intros.
  apply index_S.
  apply IHi.
    simpl in Hlt; omega.

    assumption.
Qed.


Lemma index_app_ge :
  forall (T:Set) (l1 l2:list T) i x,
    i >= length l1
    -> index i (l1 ++ l2) x
    -> index (i - length l1) l2 x.
Proof.
intros T l1 l2 i x Hge Hindex.
revert i Hge Hindex.
induction l1.
(* nil *)
intros.
simpl in Hindex.
simpl.
replace (i-0) with i by omega.
assumption.

(* cons *)
intros.
simpl.
replace (i - S (length l1)) with (i - 1 - length l1) by omega.
simpl in Hge.
apply IHl1.
  omega.

  have (index i ((a :: l1) ++ l2) x) as Hindex.
  toshow (index (i - 1) (l1 ++ l2) x).
  simpl in Hindex.
  invert Hindex; intros.
    exfalso; omega.
    
    rewrite <- Heq.
    replace (S n - 1) with n by omega.
    assumption.
Qed.


Lemma index_app_left :
  forall (T:Set) (l1 l2:list T) i x,
    index i l1 x
    -> index i (l1 ++ l2) x.
Proof.
intros T l1 l2 i x Hindex.
induction Hindex.
(* 0 *)
apply index_0.

(* S *)
simpl.
apply index_S.
assumption.
Qed.


Lemma index_app_right :
  forall (T:Set) (l1 l2:list T) i x,
    index i l2 x
    -> index (i + length l1) (l1 ++ l2) x.
Proof.
intros T l1 l2 i x Hindex.
induction l1.
(* nil *)
simpl.
replace (i+0) with i by omega.
assumption.

(* cons *)
simpl.
replace (i + S (length l1)) with (S (i + length l1)) by omega.
apply index_S.
assumption.
Qed.


Lemma app_truncate :
  forall (T:Set) (l1 l2:list T),
    truncate (length l1) (l1 ++ l2) l2.
Proof.
intros T l1 l2.
induction l1.
(* nil *)
simpl.
apply truncate_0.

(* cons *)
simpl.
apply truncate_S.
assumption.
Qed.


Corollary index_fun :
  forall (T:Set) i (l:list T) x x',
    index i l x
    -> index i l x'
    -> x = x'.
Proof.
intros T i l x x' H H'.
induction H.
(* 0 *)
inversion H'.
auto.

(* S *)
apply IHindex.
inversion H'.
auto.
Qed.


Lemma truncate_app :
  forall (T : Set) n (l l' : list T),
    truncate n l l'
    -> exists l'', l = l'' ++ l' /\ length l'' = n.
Proof.
intros T n l l' Htrunc.
induction Htrunc.
(* 0 *)
exists nil.
simpl; auto.

(* S *)
destruct IHHtrunc as (l'' & Heq & Hlen).
exists (x :: l'').
split.
  simpl.
  f_equal; auto.

  simpl.
  f_equal; auto.
Qed.


Lemma index_in :
  forall (T : Set) n (l : list T) x,
    index n l x
    -> In x l.
Proof.
intros T n l x Hindex.
induction Hindex.
(* 0 *)
left; auto.

(* S *)
right; auto.
Qed.


(* Association lists *)

Inductive indom {K T:Set} : K -> list (K * T) -> Prop :=
| indom_hit {k t l}
    : indom k ((k, t) :: l)

| indom_miss {k k' t' l}
    : indom k l
      -> indom k ((k', t') :: l).


Inductive lookup {K T:Set} : K -> list (K * T) -> T -> Prop :=
| lookup_hit {k t l}
    : lookup k ((k, t) :: l) t

| lookup_miss {k t k' t' l}
    : lookup k l t
      -> lookup k ((k', t') :: l) t.


Inductive update {K T:Set} : K -> list (K * T) -> T -> list (K*T) -> Prop :=
| update_hit {k t l t'}
    : update k ((k, t) :: l) t' ((k, t') :: l)

| update_miss {k t k' t' l l'}
    : update k l t l'
      -> update k ((k', t') :: l) t ((k', t') :: l').


Inductive delete {K T:Set} : K -> list (K * T) -> list (K*T) -> Prop :=
| delete_hit {k t l}
    : delete k ((k, t) :: l) l

| delete_miss {k k' t l l'}
    : delete k l l'
      -> delete k ((k', t) :: l) ((k', t) :: l').


Inductive ddistinct {K T : Set} : list (K * T) -> Prop :=
| ddistinct_nil
    : ddistinct nil

| ddistinct_cons {k t l}
    : ddistinct l
      -> ~ indom k l
      -> ddistinct ((k, t) :: l).


Hint Constructors indom lookup ddistinct : sequence.


Lemma lookup_iff_in :
  forall (K T : Set) k t (l : list (K * T)),
    In (k, t) l <-> lookup k l t.
Proof.
intros K T k t l.
split.
  intro Hin.
  induction l.
    destruct Hin; done.

    destruct Hin as [Heq | Hin].
      subst a.
      apply lookup_hit; done.

      destruct a as (k' & t').
      apply lookup_miss.
      apply IHl; assumption.

  intro Hlookup.
  induction Hlookup.
    left; reflexivity; done.

    right; assumption.
Qed.    


Lemma indom_decidable :
  forall (K T : Set) (k : K) (L : list (K * T)),
    eq_dec K
    -> decidable (indom k L).
Proof.
intros K T k L Hdec.
induction L as [| (k', t') L IH].
  right.
  intro Hindom.
  invert Hindom; done.

  so (Hdec k k') as [Heq | Hneq].
    subst k'.
    left; apply indom_hit; auto; done.

    destruct IH as [Hindom | Hnindom].
      left; apply indom_miss; auto; done.

      right.
      intro Hindom.
      invert Hindom; auto; done.
Qed.


Lemma lookup_app_left :
  forall (K T : Set) k (l : list (K * T)) l' t,
    lookup k l' t -> lookup k (l' ++ l) t.
Proof.
intros K T k l l' t Hlookup.
apply lookup_iff_in.
apply in_or_app; left.
apply lookup_iff_in; assumption.
Qed.


Lemma lookup_app_right :
  forall (K T : Set) k (l : list (K * T)) l' t,
    lookup k l t -> lookup k (l' ++ l) t.
Proof.
intros K T k l l' t Hlookup.
apply lookup_iff_in.
apply in_or_app; right.
apply lookup_iff_in; assumption.
Qed.


Lemma indom_lookup :
  forall (K T : Set) k (l : list (K * T)),
    indom k l -> exists t, lookup k l t.
Proof.
intros K T k l H.
induction H.
eauto with sequence.
destruct IHindom.
eauto with sequence.
Qed.


Lemma lookup_indom :
  forall (K T : Set) k (l : list (K * T)) t,
    lookup k l t -> indom k l.
Proof.
intros K T k l t H.
induction H; auto with sequence.
Qed.


Lemma update_lookup :
  forall (K T : Set) k (l : list (K * T)) t l',
    update k l t l'
    -> lookup k l' t.
Proof.
intros K T k l t l' Hupdate.
induction Hupdate.

(* hit *)
apply lookup_hit; done.

(* miss *)
apply lookup_miss; auto; done.
Qed.


Lemma lookup_update_neq :
  forall (K T : Set) k k' (l : list (K * T)) t t' l',
    lookup k l t
    -> update k' l t' l'
    -> k <> k'
    -> lookup k l' t.
Proof.
intros K T k k' l t t' l' Hlookup Hupdate Hneq.
induction Hupdate.

(* hit *)
invert Hlookup; clear Hlookup; [|].
  intros; contradiction.

  intro Hlookup'.
  apply lookup_miss; auto; done.

(* miss *)
invert Hlookup; clear Hlookup; [|].
  intros <- <-.
  apply lookup_hit; done.

  intro Hlookup'.
  apply lookup_miss; auto; done.
Qed.


Lemma update_indom :
  forall (K T : Set) k (l : list (K * T)) t l',
    update k l t l' -> indom k l.
Proof.
intros K T k l t l' H.
induction H; auto with sequence.
Qed.


Lemma update_preserves_indom_left :
  forall (K T : Set) k (l : list (K * T)) t l' k',
    update k l t l'
    -> indom k' l'
    -> indom k' l.
Proof.
intros K T k l t l' k' Hupdate Hindom.
induction Hupdate.
inversion Hindom; subst.
apply indom_hit.

apply indom_miss; assumption.

inversion Hindom; subst.
apply indom_hit.

apply indom_miss.
apply IHHupdate.
assumption.
Qed.


Lemma ddistinct_lookup_unique :
  forall (K T : Set) k (l : list (K * T)) t t',
    ddistinct l
    -> lookup k l t
    -> lookup k l t'
    -> t = t'.
Proof.
intros K T k l t t' Hddistinct H1 H2.
induction Hddistinct.
(* nil *)
inversion H1.

(* cons *)
inversion H1; inversion H2; subst; auto.
destruct H.
eapply lookup_indom; eauto.
destruct H.
eapply lookup_indom; eauto.
Qed.


Lemma ddistinct_update_unique :
  forall (K T : Set) k (l : list (K * T)) t l' l'',
    ddistinct l
    -> update k l t l'
    -> update k l t l''
    -> l' = l''.
Proof.
intros K T k l t l' l'' Hdistinct.
generalize dependent l''.
generalize dependent l'.
induction Hdistinct.
(* nil *)
intros l' l'' H1 H2.
inversion H1.

(* cons *)
intros l' l'' H1 H2.
inversion H1; inversion H2; subst; auto.
destruct H.
eapply update_indom; eauto.
destruct H.
eapply update_indom; eauto.
f_equal.
apply IHHdistinct; auto.
Qed.


Lemma update_ddistinct :
  forall (K T : Set) k (l : list (K * T)) t l',
    ddistinct l
    -> update k l t l'
    -> ddistinct l'.
Proof.
intros K T k l t l' Hdistinct Hupdate.
revert Hdistinct.
induct Hupdate.

(* hit *)
intros.
invert Hdistinct.
intros.
apply ddistinct_cons; auto; done.

(* miss *)
intros k t k' t' l l' H H0 Hdistinct.
invert Hdistinct.
intros ? Hnindom.
apply ddistinct_cons; auto; [].
contradict Hnindom.
eapply update_preserves_indom_left; eauto; done.
Qed.


Lemma indom_iff_in :
  forall (K T : Set) k (l : list (K * T)),
    indom k l <-> exists t, In (k, t) l.
Proof.
intros K T k l.
induct l.
(* nil *)
intros.
split.
  intro H; invert H; done.

  intros (? & H); destruct H; done.

(* cons *)
intros (k', t') l IH.
split.
  intro H.
  invert H.
    intro; subst k'.
    exists t'.
    left; reflexivity.

    intro H'.
    so (IH andel H') as (t & Hin).
    exists t; right; assumption.

  intros (t & Hin).
  invert Hin.
    intros; subst t' k'.
    apply indom_hit; done.

    intro Hin'.
    apply indom_miss; [].
    apply IH; eauto; done.
Qed.


Lemma indom_iff_in_car :
  forall (K T : Set) k (l : list (K * T)),
    indom k l <-> In k (map car l).
Proof.
intros K T k l.
split.
  intro Hindom.
  so (indom_iff_in _#4 andel Hindom) as (t, Hin).
  apply in_map_iff; [].
  exists (k, t).
  auto; done.

  intro Hin.
  so (in_map_iff _#5 andel Hin) as ((k', t) & Heq & Hin').
  simpl in Heq; subst k'.
  apply indom_iff_in; [].
  exists t.
  assumption.
Qed.


Lemma indom_map :
  forall (K T U : Set) (k : K) (l : list (K * T)) (f : T -> U),
    indom k l
    <-> indom k (map (fun x => (car x, f (cdr x))) l).
Proof.
intros K T U k l f.
refine (iff_trans (indom_iff_in_car _ _ _ _) _); [].
refine (iff_trans _ (iff_sym (indom_iff_in_car _ _ _ _))); [].
rewrite -> map_map.
apply iff_refl; done.
Qed.


Lemma indom_app :
  forall (K T : Set) k (l1 l2 : list (K * T)),
    (indom k l1 \/ indom k l2)
    <-> indom k (l1 ++ l2).
Proof.
intros K T k l1 l2.
split.
  intros Hindom.
  destruct Hindom as [Hindom | Hindom];
  so (indom_iff_in _#4 andel Hindom) as (t & Hin);
  apply indom_iff_in;
  exists t;
  apply in_or_app;
  [left | right];
  assumption.

  intros Hindom.
  so (indom_iff_in _#4 andel Hindom) as (t & Hin).
  so (in_app_or _#4 Hin) as [Hin' | Hin'];
  [left | right];
  apply indom_iff_in;
  eexists; eassumption.
Qed.


Lemma exists_fresh :
  forall (K T : Set),
    infinite K
    -> forall l : list (K * T), exists k, ~ indom k l.
Proof.
intros K T Hinf l.
destruct (Hinf (map (fun p : K * T => let (k', _) := p in k') l)) as [k Hnin].
exists k.
contradict Hnin.
rename Hnin into Hindom.
apply in_map_iff.
so (indom_iff_in _#4 andel Hindom) as (t & Hin).
exists (k, t).
auto.
Qed.


Lemma ddistinct_app :
  forall (K T : Set) (l1 l2 : list (K * T)),
    ddistinct (l1 ++ l2)
    -> ddistinct l1 /\ ddistinct l2.
Proof.
intros K T l1 l2 Hdist.
revert Hdist; induct l1; auto with sequence; [].
intros (k, t) l IH Hdist.
invert Hdist; intros Hdist' Hnindom.
so (IH Hdist') as (H1 & H2).
split; auto; [].
apply ddistinct_cons; auto; [].
contradict Hnindom.
apply indom_app; left; assumption.
Qed.


Lemma ddistinct_map :
  forall (K T U : Set) (l : list (K * T)) (f : T -> U),
    ddistinct l
    <-> ddistinct (map (fun x => (car x, f (cdr x))) l).
Proof.
intros K T U l f.
induction l as [| (k, t) l' IH].

(* nil *)
split; intro; apply ddistinct_nil; done.

(* cons *)
simpl.
split.
  intro Hdist.
  invert Hdist; [].
  intros ? Hnindom.
  apply ddistinct_cons; [|].
    apply IH; auto; done.

    contradict Hnindom.
    eapply (indom_map _#6 ander); eauto; done.

  intro Hdist.
  invert Hdist; [].
  intros ? Hnindom.
  apply ddistinct_cons; [|].
    apply IH; auto; done.

    contradict Hnindom.
    eapply (indom_map _#6 andel); eauto; done.
Qed.


Lemma ddistinct_app_disjoint :
  forall (K T : Set) (l1 l2 : list (K * T)) k,
    ddistinct (l1 ++ l2)
    -> indom k l1
    -> indom k l2
    -> False.
Proof.
intros K T l1 l2 k Hdist Hin1 Hin2.
revert Hdist Hin2.
induct Hin1.
  intros k t l1 Hdist Hin2.
  invert Hdist.
  intros _ Hnindom.
  destruct Hnindom.
  apply indom_app; right; auto; done.

  intros k k' t' l1 Hin IH Hdist Hin2.
  apply IH; auto; [].
  invert Hdist; auto; done.
Qed.


Lemma app_ddistinct :
  forall (K T : Set) (l1 l2 : list (K * T)),
    ddistinct l1
    -> ddistinct l2
    -> (forall k, indom k l1 -> indom k l2 -> False)
    -> ddistinct (l1 ++ l2).
Proof.
intros K T l1 l2 Hdist1 Hdist2 Hdisjoint.
revert Hdisjoint.
induct Hdist1.

(* nil *)
intros; assumption.

(* cons *)
intros k t l1 Hdist1 IH Hnindom Hdisjoint.
simpl.
apply ddistinct_cons; [|].
  apply IH.
  intros k' Hindom1 Hindom2.
  eapply Hdisjoint; eauto; [].
  apply indom_miss; auto; done.

  intro Hindom.
  so (indom_app _#5 ander Hindom) as [Hindom' | Hindom'].
    destruct Hnindom; auto; done.

    eapply Hdisjoint; eauto; [].
    apply indom_hit; done.
Qed.


Lemma ddistinct_middle :
  forall (K T : Set) (l1 l2 : list (K * T)) k t,
    ddistinct (l1 ++ (k, t) :: l2)
    -> ~ indom k (l1 ++ l2).
Proof.
intros K T l1 l2 k t Hdist.
intro Hindom.
so (indom_app _#5 ander Hindom) as [Hindom' | Hindom'].
  refine (ddistinct_app_disjoint _#5 Hdist _ _); eauto; [].
  apply indom_hit; done.

  so (ddistinct_app _#4 Hdist) as (_ & Hdist').
  invert Hdist'; intros; findcontra.
Qed.


Lemma delete_indom :
  forall (K T : Set) k (l l' : list (K * T)),
    delete k l l'
    -> indom k l.
Proof.
intros K T k l l' Hdelete.
induct Hdelete; auto with sequence.
Qed.


Lemma ddistinct_delete_unique :
  forall (K T : Set) k (l l1 l2 : list (K * T)),
    ddistinct l
    -> delete k l l1
    -> delete k l l2
    -> l1 = l2.
Proof.
intros K T k l l1 l2 Hdist Hdel1 Hdel2.
revert l1 l2 Hdel1 Hdel2.
induct Hdist.
(* nil *)
intros ? ? H ?.
invert H; done.

(* cons *)
intros k' t l Hdist IH Hnindom l1 l2 Hdel1 Hdel2.
invert Hdel1.
  intros <- <-.
  invert Hdel2.
    auto; done.
    intros l' Hdel ?.
    destruct Hnindom.
    eapply delete_indom; eauto; done.

  intros l1' Hdel1' <-.
  invert Hdel2.
    intros <- ?.
    destruct Hnindom.
    eapply delete_indom; eauto; done.

    intros l2' Hdel2' <-.
    f_equal.
    eapply IH; eauto; done.
Qed.


Lemma delete_app_right :
  forall (K T : Set) k (l1 l2 l2' : list (K * T)),
    delete k l2 l2'
    -> delete k (l1 ++ l2) (l1 ++ l2').
Proof.
intros K T k l1 l2 l2' Hdelete.
induction l1.
  assumption.
  
    destruct a as (k', t).
    simpl; apply delete_miss; auto.
Qed.


Lemma ddistinct_partition :
  forall (K T : Set) k t t' (l1 l2 l1' l2' : list (K * T)),
    ddistinct (l1 ++ (k, t) :: l2)
    -> l1 ++ (k, t) :: l2 = l1' ++ (k, t') :: l2'
    -> l1 = l1' /\ t = t' /\ l2 = l2'.
Proof.
intros K T k t t' l1a l2a l1b l2b Hdist Heq.
revert l1b Heq.
induction l1a as [| (ka, ta)].
(* nil *)
intros.
destruct l1b as [| (kb, tb)].
  injection Heq; auto; done.
  
  simpl in Hdist.
  simpl in Heq.
  injection Heq; intros Heq' _ <-.
  invert Hdist; intros _ Hnindom.
  destruct Hnindom.
  subst l2a.
  apply indom_app; right.
  apply indom_hit; done.

(* cons *)
intros.
destruct l1b as [| (kb, tb)].
  simpl in Hdist.
  simpl in Heq.
  injection Heq; intros Heq' <- <-.
  invert Hdist; intros _ Hnindom.
  destruct Hnindom.
  apply indom_app; right.
  apply indom_hit; done.

  simpl in Hdist.
  simpl in Heq.
  invert Hdist; intros.
  injection Heq; intros.
  eexploit IHl1a as (Heq1 & Heqt & Heq2); eauto; [].
  split; f_equal; f_equal; auto.
Qed.


(* Filter *)

Lemma filter_app :
  forall (A : Type) (f : A -> bool) l1 l2,
    filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
intros A f l1 l2.
induction l1 as [| x l1 IH].
  reflexivity.

  simpl.
  generalize (f x).
  intro b.
  destruct b; simpl; f_equal; auto.
Qed.


Lemma filter_cons_in :
  forall (A : Type) (f : A -> bool) l x,
    f x = true
    -> filter f (x :: l) = x :: filter f l.
Proof.
intros A f l x Heq.
simpl.
rewrite -> Heq.
reflexivity.
Qed.


Lemma filter_cons_out :
  forall (A : Type) (f : A -> bool) l x,
    f x = false
    -> filter f (x :: l) = filter f l.
Proof.
intros A f l x Heq.
simpl.
rewrite -> Heq.
reflexivity.
Qed.


Lemma lookup_filter :
  forall (A B : Set) (f : (A * B) -> bool) l k t,
    lookup k (filter f l) t
    -> f (k, t) = true.
Proof.
intros A B f l k t Hlookup.
so (lookup_iff_in _#5 ander Hlookup) as Hin.
so (filter_In _#4 andel Hin) as (_, ?).
assumption.
Qed.


Lemma filter_all :
  forall (A : Type) (l : list A),
    filter (fun _ => true) l = l.
Proof.
intros A l.
induction l as [| x l IH].
  reflexivity.

  simpl; f_equal.
  exact IH.
Qed.


Lemma filter_impl :
  forall (A : Type) (f g : A -> bool) l x,
    (forall y, f y = true -> g y = true)
    -> In x (filter f l) -> In x (filter g l).
Proof.
intros A f g l x Himpl Hin.
induction l as [| y l IH].
  destruct Hin; done.

  simpl.
  simpl in Hin.
  remember (f y) as b in Hin.
  destruct b.
    rewrite -> Himpl; auto; [].
    destruct Hin.
      left; assumption.

      right.
      apply IH; auto; done.

    generalize (g y).
    intro b.
    destruct b; [right |]; apply IH; auto; done.
Qed.


Lemma filter_iff :
  forall (A : Type) (f g : A -> bool) l,
    (forall y, f y = g y)
    -> filter f l = filter g l.
Proof.
intros A f g l Heq.
induction l as [| x l IH].
  reflexivity.

  simpl.
  rewrite <- Heq.
  rewrite <- IH.
  reflexivity.
Qed.


Lemma filter_and :
  forall (A : Type) (f g : A -> bool) l,
    filter f (filter g l) = filter (fun x => andb (f x) (g x)) l.
Proof.
intros A f g l.
induction l as [| x l IH].
  reflexivity.

  simpl.
  remember (g x) as b.
  destruct b.
    simpl.
    remember (f x) as b.
    destruct b.
      simpl.
      f_equal.
      exact IH.

      simpl.
      exact IH.

    rewrite -> Bool.andb_false_intro2; auto; done.
Qed.


Lemma filter_contain :
  forall (A B : Set) (f : (A * B) -> bool) l k t,
    lookup k (filter f l) t
    -> lookup k l t.
Proof.
intros A B f l k t Hlookup.
apply lookup_iff_in.
rewrite <- (filter_all _ l).
apply (filter_impl _ f); auto; [].
apply lookup_iff_in; auto; done.
Qed.


Lemma indom_filter :
  forall (K T : Set) (f : (K * T) -> bool) k l,
    indom k (filter f l)
    -> indom k l.
Proof.
intros K T f k l Hindom.
induction l as [| (k', t) l IH].
  invert Hindom; done.

  simpl in Hindom.
  remember (f (k', t)) as b in Hindom.
  destruct b.
    invert Hindom.
      intros; subst k'.
      apply indom_hit; done.

      intros.
      apply indom_miss; [].
      apply IH; [].
      assumption.

    apply indom_miss; [].
    apply IH; [].
    assumption.
Qed.


Lemma filter_ddistinct :
  forall (K T : Set) (f : (K * T) -> bool) l,
    ddistinct l
    -> ddistinct (filter f l).
Proof.
intros K T f l Hdist.
induct Hdist.
  apply ddistinct_nil; done.

  intros k t l Hdist IH Hnindom.
  simpl.
  remember (f (k, t)) as b.
  destruct b.
    apply ddistinct_cons; auto; [].
    contradict Hnindom.
    eapply indom_filter; eauto; done.
      
    assumption.
Qed.


(* Notation *)

Notation "l ; x" := (cons x l) (at level 65, left associativity) : sequence_scope.
Notation "l1 ;; l2" := (app l2 l1) (at level 65, left associativity) : sequence_scope.

Notation "H {{  hh  }}" := (In hh H)
  (at level 10, no associativity) : sequence_scope.

(* Note that any x .. y in H are captured. We don't want this, but there seems to be
   no good way to prevent it.
*)
Notation "H {{  hh | x .. y  }}" := (ex (fun x => .. (ex (fun y => (In hh H))) ..))
  (at level 10, x binder, y binder, no associativity) : sequence_scope.

Open Scope sequence_scope.
