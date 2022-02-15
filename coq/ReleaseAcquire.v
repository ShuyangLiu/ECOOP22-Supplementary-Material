Require Import Dynamic.
Require Import Relation.
Require Import TermDec.
Require Import Hwf.
Require Import History.
Require Import Sequence.
Require Import Truncate.


Definition acquire_reads H := forall i, isr H i  -> isacqr H i.
Definition release_writes H := forall i, isw H i  -> isrelw H i.
Definition opaque_accesses H := forall i, isop H i.

Definition rfpo H i1 i2 := (exists i3, rf H i1 i3 /\ poq H i3 i2).

Lemma po_rf_must_read { H i1 i2 } :
  trco H
  -> plus (union (po H) (rf H)) i1 i2
  -> ~ po H i1 i2
  -> exists i3, poq H i1 i3 /\ plus (rfpo H) i3 i2.
Proof.
  intros Htco Hcycle Hnotpo.
  apply plus_plusi in Hcycle.
  induction Hcycle as [ i1 i2 Hporf | i1 i2 i3 Hone Hstep].
  - case Hporf as [Hpo | Hrf].
    * contradiction.
    * exists i1.
      split. left; auto.
      eapply plus_one.
      exists i2.
      split; [| left]; auto.
  - case Hone as [Hpo | Hrf].
    rename Hpo into Hpoeq.
    assert (po H i1 i2) as Hpo. auto.
    * destruct Hpoeq as (H1 & H2 & H3 & p & Hpoeq).
      case (@pop_dec H p i2 i3) as [Hl | Hr]; auto.
      + exfalso.
        apply Hnotpo.
        eapply po_trans; eauto.
        eapply po_p_po. eauto.
      + eapply po_npop_npo in Hr; eauto.
        eapply IHHstep in Hr.
        destruct Hr as (i4 & Hpoq & Hplus).
        exists i4.
        split; auto.
        destruct Hpoq as [Heq | Hpol].

        rewrite <- Heq; right; auto.
        right; eapply po_trans; eauto.

        rewrite Hpoeq.
        find_app_cons.
    * destruct (@rf_inited H i1 i2 Htco Hrf) as (_ & p & Hin).
      case (@pop_dec H p i2 i3) as [Hl | Hr]; auto.
      + apply po_p_po in Hl.
        exists i1.
        split; [ left; auto |].
        eapply plus_one.
        exists i2.
        split; eauto.
        right. eauto.
      + eapply po_npop_npo in Hr; eauto.
        apply IHHstep in Hr.
        destruct Hr as (i4 & Hpoq & Hplus).
        exists i1.
        split; [ left; auto |].
        eapply plus_step; [ exists i2; split |]; eauto.
Qed.


Lemma rf_head_isw { H i1 i2 } :
  trco H
  -> rf H i1 i2
  -> isw H i1.
Proof.
  intros Htrco Hrf.
  apply rf_wf_prop in Hrf as (l & (v & Hwrites) & Hreads); auto.
  exists l, v.
  auto.
Qed.

Lemma rf_tail_isr { H i1 i2 } :
  trco H
  -> rf H i1 i2
  -> isr H i2.
Proof.
  intros Htrco Hrf.
  apply rf_wf_prop in Hrf as (l & (v & Hwrites) & Hreads); auto.
  exists l.
  auto.
Qed.

Lemma rfpo_vop { H i1 i2 } :
  trco H
  -> acquire_reads H
  -> rfpo H i1 i2
  -> vop H i1 i2.
Proof.
  intros Htrco Hacq Hrfpo.
  destruct Hrfpo as (i3 & Hrf & Hpoq).
  assert (isr H i3) as Hisr. eapply rf_tail_isr; eauto.
  apply Hacq in Hisr.

  destruct Hpoq as [Heq | Hpo].

  - rewrite <- Heq.
    eapply plus_one.
    right. left.
    eauto.
  - eapply plus_step; [| eapply plus_one].
    * right. left.
      eauto.
    * do 4 right. left.
      split; eauto.
Qed.

Lemma rfpop_vop { H i1 i2 } :
  trco H
  -> acquire_reads H
  -> plus (rfpo H) i1 i2
  -> vop H i1 i2.
Proof.
  intros Htrco Hacq Hrfpop.
  apply plus_plusi in Hrfpop.
  induction Hrfpop.
  - apply rfpo_vop; auto.
  - eapply plus_trans; eauto.
    eapply rfpo_vop; eauto.
Qed.

Theorem acq_causality { H } :
  trco H
  -> acquire_reads H
  -> acyclic (union (po H) (rf H)).
Proof.
  intros Htrco Hacq Hcycle.
  destruct Hcycle as (i1 & Hcycle).
  eapply po_rf_must_read in Hcycle as (i2 & Hpoq & Hrf); eauto; [| eapply po_irreflex ]; eauto.
  eapply vop_irreflex; eauto.
  apply rfpop_vop; eauto.
  apply plus_plusr in Hrf.
  destruct Hrf as (i3 & Hrfpos & (i4 & Hrf & Hpoq2)).
  apply plusr_plus.
  exists i3. split; eauto.
  exists i4. split; auto.
  eapply poq_trans; eauto.
Qed.

(* TODO same for release_writes H *)
