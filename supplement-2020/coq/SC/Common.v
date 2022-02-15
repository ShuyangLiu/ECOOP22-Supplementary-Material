Require Import Dynamic.
Require Import Sequence.
Require Import Relation.
Require Import Tactics.
Require Import Hwf.
Require Import History.

(* BEGIN duplicated in seq con *)
(* from-read *)
Definition fr H i i' :=
  exists i'',
    rf H i'' i
    /\ cop H i'' i'
    /\ i <> i'.

(* sequentially consistent order *)
Definition sc R H i i' :=
  R i i' \/ co H i i' \/ rf H i i' \/ fr H i i'.

(* same as rsc in SeqCon.v *)
Definition com H i i' :=
  co H i i' \/ rf H i i' \/ fr H i i'.
(* END duplicated in seq con *)

Lemma com_writesto {H i1 i2} :
  trco H
  -> com H i1 i2
  -> (exists l, writesto H i1 l) \/ (exists l, writesto H i2 l).
Proof.
  intros Htrco Hcom.
  destruct Hcom as [Hco | [ Hrf | (i & _ & Hcop & _) ]];
    [ destruct (co_wf_prop H i1 i2 Htrco Hco) as (l & Hwrites & _); left
    | destruct (rf_wf_prop H i1 i2 Htrco Hrf) as (l & Hwrites & _); left
    | destruct (cop_wf_prop H i i2 Htrco Hcop) as (l & _ & Hwrites); right ];
    eauto.
Qed.

(* must communicate *)
Definition mcomp H i1 i2 :=
  exists i3 i4, poq H i1 i3 /\ com H i3 i4 /\ star (sc (po H) H) i4 i2.

Hint Unfold com.
Lemma sc_must_com { H i1 i2 } :
  trco H
  -> plus (sc (po H) H) i1 i2
  -> ~ po H i1 i2
  -> mcomp H i1 i2.
Proof.
  intros Htrco Hplussc Hnpo.
  apply plus_plusi in Hplussc.
  induction Hplussc as [i1 i2 Hsc | i1 i2 i3 Hsc Hplussc];
    destruct Hsc as [Hpo | Hcom].
  - contradiction.
  - exists i1, i2.
    split; [ left | split ]; auto using star_refl.
  - destruct Hpo as (H1 & H2 & H3 & p & Hpoeq).
    assert (po H i1 i2) as Hpo. exists H1, H2, H3, p. auto.
    destruct (@pop_dec H p i2 i3) as [Hpop | Hpop]; auto.
    + exfalso.
      apply po_p_po in Hpop.
      apply Hnpo.
      eapply po_trans; eauto.
    + apply po_npop_npo in Hpop; auto;
        [| rewrite Hpoeq; find_app_cons ].
      destruct (IHHplussc Hpop) as (i4 & i5 & (Hpoq & Hcom & Hsc)).
      destruct Hpoq as [Heq | Hpoi2i4];
      exists i4, i5;
      split; auto;
        [ rewrite <- Heq | ];
        right;
        eauto using po_trans.
  - exists i1, i2.
    split; [ left | split ]; auto using plus_star, plusi_plus.
Qed.

(***
NOTE

The following lemmas a are taken verbatim from RMC/SeqCon.v, all credit to Crary and Sullivan

 **)

Lemma fr_isr_isw :
  forall H i i',
    trco H
    -> fr H i i'
    -> isr H i /\ isw H i'.
Proof.
intros H i i' Htrco Hfr.
destruct Hfr as (i'' & Hrf & Hcop & _).
split.
  pose proof (rf_wf_prop _#3 Htrco Hrf) as (l & _ & Hinr).
  eexists; eauto.

  pose proof (plus_plusr _#4 Hcop) as (i''' & _ & Hco).
  pose proof (co_isw _#3 Htrco Hco) as (_ & Hisw).
  assumption.
Qed.

Lemma fr_isw_cop :
  forall H i i',
    trco H
    -> fr H i i'
    -> isw H i
    -> cop H i i'.
Proof.
intros H i i' Htrco Hfr Hisw.
destruct Hfr as (i'' & Hrf & Hcop & Hneq).
apply star_neq_plus; auto; [].
eapply rwf_cop_cos; eauto; [].
apply rf_isw_rwf; auto; done.
Qed.


Lemma fr_cop_trans :
  forall H i1 i2 i3,
    trco H
    -> acyclic (co H)
    -> fr H i1 i2
    -> cop H i2 i3
    -> fr H i1 i3.
Proof.
intros H i1 i2 i3 Htrco Hcoacy Hfr Hcop23.
destruct Hfr as (iw & Hrf & Hcop & _).
exists iw.
#2 do2 2 split; auto.
  eapply plus_trans; eauto; done.

  intro; subst i3.
  destruct Hcoacy; [].
  exists i1.
  eapply star_plus_trans; eauto; [].
  eapply rwf_cop_cos; eauto; [].
  apply rf_isw_rwf; auto; [].
  eapply cop_isw; eauto; done.
Qed.

Lemma comp_to_write :
  forall H i i',
    trco H
    -> acyclic (co H)
    -> plus (com H) i i'
    -> isw H i'
    -> cop H i i' \/ fr H i i'.
Proof.
intros H i i' Htrco Hcoacy Hcomp Hisw.
pose proof (plus_plusi _#4 Hcomp) as Hcomp'; clear Hcomp.
revert Hisw.
elim Hcomp'; clear i i' Hcomp'.
(* refl *)
intros i i' Hcom Hisw.
have (com H i i') as Hcom.
have (isw H i') as Hisw.
toshow (cop H i i' \/ fr H i i').
destruct Hcom as [Hco | [Hrf | Hfr]].
  left.
  apply plus_one.
  assumption.

  left.
  apply plus_one; [].
  apply rwf_co; auto; [].
  apply rf_isw_rwf; auto; done.

  right.
  assumption.

(* step *)
intros i1 i2 i3 Hcom Hcomp IH Hisw.
thus (cop H i2 i3 \/ fr H i2 i3) as Hacc by IH; clear IH Hisw.
toshow (cop H i1 i3 \/ fr H i1 i3).
destruct Hcom as [Hco | [Hrf | Hfr]].
  have (co H i1 i2) as Hco.
  destruct Hacc as [Hcop | Hfr].
    left.
    have (cop H i2 i3) as Hcop.
    eapply plus_step; eauto; done.

    have (fr H i2 i3) as Hfr.
    left.
    exists i2; split; auto; [].
    apply plus_star; [].
    apply fr_isw_cop; auto; [].
    eapply co_isw; eauto; done.

  have (rf H i1 i2) as Hrf.
  left.
  destruct Hacc as [Hcop | Hfr].
    have (cop H i2 i3) as Hcop.
    pose proof (cop_isw _#3 Htrco Hcop) as (Hisw & _).
    eapply plus_step; eauto; [].
    apply rwf_co; auto; [].
    apply rf_isw_rwf; auto; done.

    have (fr H i2 i3) as Hfr.
    destruct Hfr as (i & Hrf' & Hcop & _).
    have (rf H i i2) as Hrf'.
    have (cop H i i3) as Hcop.
    thus (i = i1) as Heq by rf_fun.
    subst i.
    assumption.

  have (fr H i1 i2) as Hfr.
  right.
  eapply fr_cop_trans; eauto; [].
  destruct Hacc as [Hcop | Hfr']; auto; [].
  apply fr_isw_cop; auto; [].
  eapply fr_isr_isw; eauto; done.
Qed.

Lemma com_acyclic :
  forall H,
    trco H
    -> acyclic (co H)
    -> acyclic (com H).
Proof.
intros H Htrco Hcoacy.
intro Hcycle.
assert (exists i, isw H i /\ plus (com H) i i) as Hcycle'.
  destruct Hcycle as (i & (i' & Hcom & Hcoms)).
  destruct Hcom as [Hco | [Hrf | Hfr]].
    exists i.
    split.
      exact (co_isw _#3 Htrco Hco andel).

      exists i'; split; auto.

    exists i.
    split.
      exact (rf_isw_isr _#3 Htrco Hrf andel).

      exists i'; split; auto.

    exists i'.
    split.
      exact (fr_isr_isw _#3 Htrco Hfr ander).

      apply plusr_plus.
      exists i; split; auto.

have (exists i : identifier, isw H i /\ plus (com H) i i) as Hcycle'.
clear Hcycle.
destruct Hcycle' as (i & Hisw & Hcomp).
destruct (comp_to_write _#3 Htrco Hcoacy Hcomp Hisw) as [Hcop | Hfr].
  have (cop H i i) as Hcop.
  destruct Hcoacy; [].
  exists i; auto.

  have (fr H i i) as Hfr.
  destruct Hfr as (_ & _ & _ & Hneq).
  destruct Hneq; auto; done.
Qed.

Lemma sc_cycle_r :
  forall R H i,
    trco H
    -> acyclic (co H)
    -> plus (sc R H) i i
    -> exists i1 i2,
         R i1 i2
         /\ star (sc R H) i2 i1.
Proof.
intros R H i Htrco Hcoacy Hcycle.
destruct Hcycle as (i' & Hsc & Hscs).
destruct Hsc as [HR | Hcom].
  exists i, i'; splitall; auto; done.

  change (com H i i') in Hcom.
  thus (plus (com H) i i') as Hacc by plus_one; clear Hcom.
  remember i as i0 in Hacc.
  revert i0 Heqi0 Hacc.
  elim Hscs; clear i i' Hscs.
  (* refl *)
  intros i i0 Heqi0 Hacc.
  subst i0.
  destruct (com_acyclic _ Htrco Hcoacy).
  exists i; auto.

  (* step *)
  intros i1 i2 i3 H12 H23 IH i0 Heqi0 Hacc.
  subst i0.
  destruct H12 as [HR | Hcom].
    exists i1, i2.
    split; auto; [].
    eapply star_trans; eauto; [].
    apply (star_mono _ (com H)); [|].
      intros; right; auto; done.

      apply plus_star; auto; done.

    have (co H i1 i2 \/ rf H i1 i2 \/ fr H i1 i2) as Hcom.
    change (com H i1 i2) in Hcom.
    apply (IH _ (eq_refl _)); [].
    eapply plus_trans; eauto using plus_one.
Qed.