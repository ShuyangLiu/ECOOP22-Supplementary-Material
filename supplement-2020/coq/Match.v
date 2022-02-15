Require Import Tactics.
Require Import Peano_dec.
Require Export Decidable.
Require Export Itemizable.
Require Import Sequence.
Require Import Subst.
Require Import Dynamic.


(* Decidable equalities *)

Definition eq_prod_dec {S T : Set} : eq_dec S -> eq_dec T -> eq_dec (S * T).
Proof.
intros HS HT p p'.
destruct p as (x, y).
destruct p' as (x', y').
destruct (HS x x') as [Hyes | Hno].
  destruct (HT y y') as [Hyes' | Hno].
    left.
    f_equal; auto.

    right.
    intro.
    inversion H.
    auto.

  right; intro.
  inversion H; auto.
Qed.


Ltac decide_yes := complete (left; f_equal; auto).

Ltac decide_no :=
  let H := fresh
  in
  complete
    (right; intro H; inversion H;
     (match goal with
        H : ?t <> ?t' |- _ => contradict H
      end);
     auto).


Definition eq_attr_dec : eq_dec attr.
Proof.
intros b b'.
destruct b; destruct b'; try (right; intro; discriminate); auto.
Qed.

Require Import TermDec.

Lemma eq_dec_decidable :
  forall (T : Set), eq_dec T -> forall (x y : T), decidable (x = y).
Proof.
intros T H x y.
destruct (H x y); [left | right]; auto.
Qed.


Lemma closed_decidable :
  forall t, decidable (closed t).
Proof.
intros t.
apply (eq_dec_decidable _ eq_term_dec).
Qed.


(* Matching problems *)

Lemma match_ac_read_decidable :
  forall a, decidable (exists l m, a = ac_read l m).
Proof.
intros a.
destruct a; try (right; intros (? & ? & ?); discriminate).
left; eexists; eexists; reflexivity.
Qed.


Lemma match_ac_write_decidable :
  forall a, decidable (exists l v m, a = ac_write l v m).
Proof.
intros a.
destruct a; try (right; intros (? & ? & ? & H); discriminate). 
left; do 3 eexists; reflexivity.
Qed.


Lemma match_ac_rw_decidable :
  forall a, decidable (exists l v, a = ac_rw l v).
Proof.
intros a.
destruct a; try (right; intros (? & ? & H); discriminate).
left; do 2 eexists; reflexivity.
Qed.


Lemma match_ac_write_l_decidable :
  forall l a, decidable (exists v m, a = ac_write l v m).
Proof.
intros l a.
destruct a;
try (right; intro H; destruct H as (? & ? & H); discriminate).
rename l0 into l'.
destruct (eq_loc_dec l l').
left; do 2 eexists; f_equal; auto.

right; intro H; destruct H as (? & ? & H); injection H; auto.
Qed.


Lemma match_tr_init_decidable :
  forall d, decidable (exists i a, d = tr_init i a).
Proof.
intros d.
destruct d; try (right; intro H; destruct H as (? & ? & H); discriminate).
left; do 3 eexists; reflexivity.
Qed.

Lemma match_tr_exec_decidable :
  forall d, decidable (exists i v, d = tr_exec i v).
Proof.
intros d.
destruct d; try (right; intro H; destruct H as (? & ? & H); discriminate).
left; do 2 eexists; reflexivity.
Qed.

Lemma match_tr_init_write_decidable :
  forall d, decidable (exists i l v m, d = tr_init i (ac_write l v m)).
Proof.
intros d.
destruct d; try (right; intros (? & ? & ? & ? & H); discriminate).
rename d into a.
destruct a; try (right; intros (? & ? & ? & ? & H); discriminate).
left; repeat eexists; reflexivity.
Qed.

Lemma match_init_decidable :
  forall h, decidable (exists i p, h = ev_init i p).
Proof.
intros h.
destruct h;
try (right; intro H; destruct H as (? & ? & H); discriminate H).
revert_all; intros i p.
left.
exists i, p; reflexivity.
Qed.


Lemma match_init_i_decidable :
  forall i h, decidable (exists p, h = ev_init i p).
Proof.
intros i h.
destruct h;
try (right; intro H; destruct H as (? & H); discriminate).
rename i0 into i'.
destruct (eq_ident_dec i i').
left; eexists; f_equal; auto.

right; intro H; destruct H as (? & H); injection H; auto.
Qed.


Lemma match_init_p_decidable :
  forall p h, decidable (exists i, h = ev_init i p).
Proof.
intros p h.
destruct h;
try (right; intro H; destruct H as (? & H); discriminate).
rename t into p'.
destruct (eq_thread_dec p p').
  left; eexists; f_equal; auto; done.

  right; intro H; destruct H as (? & H); injection H; auto; done.
Qed.


Lemma match_is_decidable :
  forall h, decidable (exists i a, h = ev_is i a).
Proof.
intros h.
destruct h;
try (right; intro H; destruct H as (? & ? & H); discriminate H).
revert_all; intros i a.
left.
exists i, a; reflexivity.
Qed.


Lemma match_is_i_decidable :
  forall i h, decidable (exists a, h = ev_is i a).
Proof.
intros i h.
destruct h;
try (right; intro H; destruct H; discriminate).
rename i0 into i'.
destruct (eq_ident_dec i i').
  left; eexists; f_equal; auto; done.

  right; intro H; destruct H as (? & H); injection H; auto; done.
Qed.


Lemma match_is_read_decidable :
  forall h, decidable (exists i l m, h = ev_is i (ac_read l m)).
Proof.
intros h.
destruct h;
try (right; intros H; destruct H as (? & ? & ? & ?); discriminate).
rename t into a.
destruct a;
try (right; intros H; destruct H as (? & ? & ? & ?); discriminate).
left.
repeat eexists; reflexivity.
Qed.


Lemma match_is_read_i_decidable :
  forall i h, decidable (exists l m, h = ev_is i (ac_read l m)).
Proof.
intros i h.
destruct h;
try (right; intros H; destruct H as (? & ? & ?); discriminate).
rename i0 into i', t into a.
destruct a;
try (right; intros H; destruct H as (? & ? & ?); discriminate).
destruct (eq_ident_dec i i').
  left; repeat eexists; f_equal; f_equal; auto; done.

  right; intro H; destruct H as (? & ? & H); injection H; auto; done.
Qed.


Lemma match_is_write_i_decidable :
  forall i h, decidable (exists l v m, h = ev_is i (ac_write l v m)).
Proof.
intros i h.
destruct h;
try (right; intros H; destruct H as (? & ? & ? & ?); discriminate).
rename i0 into i', t into a.
destruct a;
try (right; intros H; destruct H as (? & ? & ? & ?); discriminate).
rename a into v.
destruct (eq_ident_dec i i').
  left; repeat eexists; f_equal; f_equal; auto; done.

  right; intro H; destruct H as (? & ? & ? & H); injection H; auto; done.
Qed.


Lemma match_is_write_l_decidable :
  forall l h, decidable (exists i v m, h = ev_is i (ac_write l v m)).
Proof.
intros l h.
destruct h;
try (right; intros H; destruct H as (? & ? & ? & ?); discriminate).
rename t into a.
destruct a;
try (right; intros H; destruct H as (? & ? & ? & ?); discriminate).
rename l0 into l'.
destruct (eq_loc_dec l l').
  left; repeat eexists; f_equal; f_equal; auto; done.

  right; intro H; destruct H as (? & ? & ? & H); injection H; auto; done.
Qed.


Lemma match_is_write_il_decidable :
  forall i l h, decidable (exists v m, h = ev_is i (ac_write l v m)).
Proof.
intros i l h.
destruct h;
try (right; intros H; destruct H as (? & ? & ?); discriminate).
rename i0 into i', t into a.
destruct a;
try (right; intros H; destruct H as (? & ? & ?); discriminate).
rename l0 into l'.
destruct (eq_loc_dec l l').
  destruct (eq_ident_dec i i').
    left; repeat eexists; f_equal; f_equal; auto; done.

    right; intro H; destruct_all H; injection H; intros; findcontra.

  right; intro H; destruct_all H; injection H; intros; findcontra.
Qed.


Lemma match_is_rw_i_decidable :
  forall i h, decidable (exists l v, h = ev_is i (ac_rw l v)).
Proof.
intros i h.
destruct h;
try (right; intros H; destruct H as (? & ? & ?); discriminate).
rename i0 into i', t into a.
destruct a;
try (right; intros H; destruct H as (? & ? & ?); discriminate).
rename a into v.
destruct (eq_ident_dec i i').
  left; repeat eexists; f_equal; f_equal; auto; done.

  right; intro H; destruct H as (? & ? & H); injection H; auto; done.
Qed.


Lemma match_is_rw_l_decidable :
  forall l h, decidable (exists i v, h = ev_is i (ac_rw l v)).
Proof.
intros l h.
destruct h;
try (right; intros H; destruct H as (? & ? & ?); discriminate).
rename t into a.
destruct a;
try (right; intros H; destruct H as (? & ? & ?); discriminate).
rename l0 into l'.
destruct (eq_loc_dec l l').
  left; repeat eexists; f_equal; f_equal; auto; done.

  right; intro H; destruct H as (? & ? & H); injection H; auto; done.
Qed.


Lemma match_is_rw_il_decidable :
  forall i l h, decidable (exists v, h = ev_is i (ac_rw l v)).
Proof.
intros i l h.
destruct h;
try (right; intros H; destruct H as (? & ?); discriminate).
rename i0 into i', t into a.
destruct a;
try (right; intros H; destruct H as (? & ?); discriminate).
rename l0 into l'.
destruct (eq_loc_dec l l').
  destruct (eq_ident_dec i i').
    left; repeat eexists; f_equal; f_equal; auto; done.

    right; intro H; destruct_all H; injection H; intros; findcontra.

  right; intro H; destruct_all H; injection H; intros; findcontra.
Qed.


Lemma match_rf_w_decidable :
  forall i h, decidable (exists i', h = ev_rf i i').
Proof.
intros i h.
destruct h;
try (right; intros H; destruct H as (? & ?); discriminate).
destruct (eq_ident_dec i i0).
  left; eexists; f_equal; eauto; done.

  right; intro H; destruct_all H; injection H; intros; findcontra.
Qed.


Lemma match_rf_r_decidable :
  forall i h, decidable (exists i', h = ev_rf i' i).
Proof.
intros i h.
destruct h;
try (right; intros H; destruct H as (? & ?); discriminate).
destruct (eq_ident_dec i i1).
  left; eexists; f_equal; eauto; done.

  right; intro H; destruct_all H; injection H; intros; findcontra.
Qed.


(* Matching in histories *)

Lemma In_decidable :
  forall (T : Set) (x : T) (L : list T),
    eq_dec T
    -> decidable (In x L).
Proof.
intros T x L Heqdec.
apply (iff_decidable (Exists (fun x' => x = x') L)).
  apply Exists_eq_in.

  apply Exists_decidable.
  apply (eq_dec_decidable _ Heqdec).
Qed.


Lemma present_decidable :
  forall (h : event) H,
    decidable (H {{ h }}).
Proof.
intros h H.
apply In_decidable; auto; [].
exact eq_event_dec.
Qed.


(* Could get these from the above, but easier just to prove them directly. *)

Lemma present_1_decidable :
  forall (T : Set) (h : T -> event),
    (forall h', decidable (exists x, h' = h x))
    -> forall H, decidable (H {{ h x | x }}).
Proof.
intros T h H M.
induction M.
right; simpl; intro H'; destruct H' as (_ & H'); trivial.

rename a into h'.
destruct IHM as [(x & H') | H'].
  left; simpl; exists x.
  right; assumption.
  destruct (H h') as [(x & H'') | H''].
    left; simpl; exists x; left; assumption.
  
    right; simpl.
    intro HC.
    destruct HC as (x & [ HC | HC ]).
      contradict H''.
      exists x; auto.
  
      contradict H'.
      exists x; auto.
Qed.


Lemma present_2_decidable :
  forall (T T' : Set) (h : T -> T' -> event),
    (forall h', decidable (exists x y, h' = h x y))
    -> forall H, decidable (H {{ h x y | x y }}).
Proof.
intros T T' h H M.
induction M.
right; simpl; intro H'; destruct H' as (_ & _ & H'); trivial.

rename a into h'.
destruct IHM as [(x & y & H') | H'].
  left; simpl; exists x, y.
  right; assumption.
  destruct (H h') as [(x & y & H'') | H''].
    left; simpl; exists x, y; left; assumption.
  
    right; simpl.
    intro HC.
    destruct HC as (x & y & [ HC | HC ]).
      contradict H''.
      exists x, y; auto.
  
      contradict H'.
      exists x, y; auto.
Qed.


Lemma present_3_decidable :
  forall (T T' T'' : Set) (h : T -> T' -> T'' -> event),
    (forall h', decidable (exists x y z, h' = h x y z))
    -> forall H, decidable (H {{ h x y z | x y z }}).
Proof.
intros T T' T'' h H M.
induction M.
right; simpl; intro H'; destruct H' as (_ & _ & _ & H'); trivial.

rename a into h'.
destruct IHM as [(x & y & z & H') | H'].
  left; simpl; exists x, y, z.
  right; assumption.
  destruct (H h') as [(x & y & z & H'') | H''].
    left; simpl; exists x, y, z; left; assumption.
  
    right; simpl.
    intro HC.
    destruct HC as (x & y & z & [ HC | HC ]).
      contradict H''.
      exists x, y, z; auto.
  
      contradict H'.
      exists x, y, z; auto.
Qed.

Lemma writesto_decidable_i :
  forall H i,
    decidable (exists l, writesto H i l).
Proof.
  intros H i.
  #2 so (present_3_decidable _ _ _ _ (match_is_write_i_decidable i) H) as [(l & v & m & Hwrite) | Hnw].
  left.
  exists l, v.
  eapply writes_write. eauto.

  #2 so (present_2_decidable _ _ _ (match_is_rw_i_decidable i) H) as [(l & v & Hrw) | Hnrw].
    left.
    exists l, v.
    apply writes_rw; assumption.

    right.
    intros (l & v & Hwrite).
    #2 invert Hwrite.
      intros m His.
      apply Hnw; eauto; done.

      intro His.
      apply Hnrw; eauto; done.
Qed.

Lemma reads_decidable_i :
  forall H i,
    decidable (exists l, reads H i l).
Proof.
intros H i.
#2 so (present_2_decidable _ _ _ (match_is_read_i_decidable i) H) as [(l & m & Hread) | Hnr].
  left.
  eexists.
  eapply reads_read; eauto.

  #2 so (present_2_decidable _ _ _ (match_is_rw_i_decidable i) H) as [(l & v & Hrw) | Hnrw].
    left.
    eexists.
    eapply reads_rw; eassumption.

    right.
    intros (l & Hread).
    #2 invert Hread.
      intros His m.
      apply Hnr; eauto; done.

      intros v His.
      apply Hnrw; eauto; done.
Qed.