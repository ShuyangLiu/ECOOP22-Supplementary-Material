Require Import Dynamic.
Require Import Sequence.
Require Import Relation.
Require Import Tactics.
Require Import Hwf.
Require Import History.
Require Import SC.Common.
Require Import Truncate.

Definition vof H i3 := 
  forall i4, po H i3 i4 -> vo H i3 i4.

Definition sb H i1 i2 :=
  exists i3, vop H i1 i3 /\ poq H i3 i2 /\ vof H i3.

Definition sbs H i1 i2 := star (sb H) i1 i2.
Definition sbp H i1 i2 := plus (sb H) i1 i2.

Definition posb H i1 i2 := po H i1 i2 \/ sb H i1 i2 .
Definition posbs H i1 i2 := star (posb H) i1 i2.
Definition posbp H i1 i2 := plus (posb H) i1 i2.

Definition race_free H :=
  forall i1 i2 l,
    access H i1 l
    -> access H i2 l
    -> sb H i1 i2 \/ sb H i2 i1.

Lemma sb_vop { H i1 i2 } :
  trco H
  -> sb H i1 i2
  -> vop H i1 i2.
Proof.
  intros Htrco (i4 & Hvop & Hpoq & Hvof).
  destruct Hpoq as [ Heq1 | Hpo1 ].
  - rewrite <- Heq1. auto.
  - eapply plus_trans; eauto.
    apply plus_one.
    eapply Hvof; auto.
Qed.

Lemma sb_poq_vop { H i1 i2 i3 } :
  trco H
  -> sb H i1 i3
  -> poq H i3 i2
  -> vop H i1 i2.
Proof.
  intros Htrco (i4 & Hvopi1i4 & Hpoqi4i2 & Hvof) Hpoq.
  destruct Hpoq as [ Heq1 | Hpo1 ];
    destruct Hpoqi4i2 as [ Heq2 | Hpo2 ].
  - rewrite <- Heq1.
    rewrite <- Heq2.
    auto.
  - rewrite <- Heq1.
    eapply plus_trans; eauto.
    apply plus_one.
    eapply Hvof. auto.
  - rewrite <- Heq2 in Hpo1.
    eapply plus_trans; eauto.
    apply plus_one.
    eapply Hvof. auto.
  - eapply plus_trans; eauto.
    apply plus_one.
    eapply Hvof.
    eapply po_trans; eauto.
Qed.

Lemma sb_trans { H i1 i2 i3 } :
  sb H i1 i3
  -> sb H i3 i2
  -> sb H i1 i2.
Proof.
  intros Hsb1 Hsb2.
  destruct Hsb1 as (i4 & Hvop1 & Hpoq1 & Hvof1).
  destruct Hsb2 as (i5 & Hvop2 & Hpoq2 & Hvof2).
  exists i5.
  split; [|split]; auto.
  - destruct Hpoq1 as [ Heq | Hpo ];
      eapply plus_trans; eauto.
    + rewrite <- Heq in Hvop2; auto.
    + eapply plus_trans; eauto.
      eapply plus_one.
      eauto using Hvof1.
Qed.

Lemma sb_posb_vop { H i1 i2 i3 } :
  trco H
  -> sb H i1 i3
  -> posb H i3 i2
  -> vop H i1 i2.
Proof.
  intros Htrco Hsb1 Hposb.
  destruct Hposb as [Hpo | Hsb2].
  - eapply sb_poq_vop; eauto.
    right; auto.
  - eauto using sb_vop, sb_trans.
Qed.

Lemma com_access { H i1 i2 } :
  trco H
  -> com H i1 i2
  -> exists l, access H i1 l /\ access H i2 l.
Proof.
  intros Htrco [Hco | [Hrf | (i3 & Hrf & Hcop & Hneq)]].
  - destruct (co_wf_prop H i1 i2 Htrco Hco) as (l & ? & ?).
    exists l.
    split; right; auto.
  - destruct (rf_wf_prop H i1 i2 Htrco Hrf) as (l & ? & ?).
    exists l.
    split; [ right | left ]; auto.
  - destruct (rf_wf_prop H i3 i1 Htrco Hrf) as (l & Hwritesi3 & Hreadsi1).
    destruct (cop_wf_prop H i3 i2 Htrco Hcop) as (l' & Hwritesi3' & Hwritesi2).
    erewrite <- (writesto_fun H i3 l l' Htrco Hwritesi3 Hwritesi3') in Hwritesi2; eauto.
    exists l.
    split; [ left | right ]; auto.
Qed.

Lemma drf_com_sb { H i1 i2 } :
  trco H
  -> race_free H
  -> acyclic (co H)
  -> com H i1 i2
  -> sb H i1 i2.
Proof.
  intros Htrco Hdrf Hacycco Hcom.
  destruct (com_access Htrco Hcom) as (l & Haccess1 & Haccess2).
  destruct (Hdrf i1 i2 l Haccess1 Haccess2) as [ Hsb | Hsb ]; auto;
    exfalso; apply Hacycco.
  apply sb_vop in Hsb; auto.
  destruct Hcom as [Hco | [Hrf | (i3 & Hrf & Hcop & Hneq)]]; auto.
  - exists i1.
    eapply plus_trans; eapply plus_one; eauto.
    destruct (co_wf_prop H i1 i2 Htrco Hco) as (? & ? & ?).
    eapply co_ww; eauto.
    left; auto.
  - exists i1.
    eapply plus_one; eauto.
    destruct (rf_wf_prop H i1 i2 Htrco Hrf) as (? & ? & ?).
    eapply co_ww; eauto.
    left.
    eapply plus_trans; eauto.
    apply plus_one. right; left; eauto.
  - exists i3.
    destruct (rf_wf_prop H i3 i1 Htrco Hrf) as (l' & Hwritesi3 & Hreadsi1).
    destruct (cop_wf_prop H i3 i2 Htrco Hcop) as (l'' & Hwritesi3' & Hwritesi2).
    erewrite <- (writesto_fun H i3 l' l'' Htrco Hwritesi3 Hwritesi3') in Hwritesi2; eauto.
    eapply plus_trans; eauto.
    apply plus_one.
    eapply co_wr; eauto.
    left; auto.
    intros Heq.
    apply Hacycco.
    exists i3.
    rewrite -> Heq in Hcop.
    auto.
Qed.

Lemma drf_sc_posb { H i1 i2 } :
  trco H
  -> race_free H
  -> acyclic (co H)
  -> sc (po H) H i1 i2
  -> posb H i1 i2.
Proof.
  intros Htrco Hdrf Hacycco Hsc.
  destruct Hsc as [Hpo | Hcom].
  - left; auto.
  - right.
    apply drf_com_sb; eauto.
Qed.

Lemma drf_scp_posbp { H i1 i2 } :
  trco H
  -> race_free H
  -> acyclic (co H)
  -> plus (sc (po H) H) i1 i2
  -> posbp H i1 i2.
Proof.
  intros Htrco Hdrf Hacycco Hsc.
  apply plus_plusi in Hsc.
  induction Hsc;
    [ eapply plus_one | eapply plus_step ];
    eauto using drf_sc_posb.
Qed.

Lemma drf_scs_posbs { H i1 i2 } :
  trco H
  -> race_free H
  -> acyclic (co H)
  -> star (sc (po H) H) i1 i2
  -> posbs H i1 i2.
Proof.
  intros Htrco Hdrf Hacycco Hsc.
  induction Hsc;
    [ apply star_refl | eapply star_step ];
    eauto using drf_sc_posb.
Qed.

Lemma sb_posb_sb { H i1 i3 i2 } :
  trco H
  -> sb H i1 i3
  -> posb H i3 i2
  -> sb H i1 i2.
Proof.
  intros Htrco Hsb Hposb.
  destruct Hposb.
  - destruct Hsb.
    exists x.
    split; [| split]; intuition.
    eapply poq_trans; eauto.
    right. auto.
  - eapply sb_trans; eauto.
Qed.

Lemma sb_posbs_sbp { H i1 i3 i2 } :
  trco H
  -> sb H i1 i3
  -> posbs H i3 i2
  -> sbp H i1 i2.
Proof.
  intros Hdrf Hsb Hposbs.
  induction Hposbs.
  - apply plus_one. auto.
  - apply IHHposbs.
    eapply sb_posb_sb; eauto.
Qed.

Lemma sbp_vop { H i1 i2 } :
  trco H
  -> sbp H i1 i2
  -> vop H i1 i2.
Proof.
  intros Htrco Hsbp.
  apply plus_plusi in Hsbp.
  induction Hsbp;
    [| eapply plus_trans; eauto] ;
    eapply sb_vop; eauto.
Qed.

Lemma scs_poq_scs { H i1 i3 i2 } :
  star (sc (po H) H) i1 i3
  -> poq H i3 i2
  -> star (sc (po H) H) i1 i2.
Proof.
  intros Hscs Hpoq.
  destruct Hpoq as [Heq | Hpoq].
  - rewrite <- Heq. auto.
  - apply plus_star.
    eapply plus_stepr; eauto.
    left. auto.
Qed.

Theorem drf_sc { H } :
  trco H
  -> race_free H
  -> acyclic (co H)
  -> acyclic (sc (po H) H).
Proof.
  intros Htrco Hdrf Hacycco (i1 & Hsc).
  destruct (sc_must_com Htrco Hsc) as (i2 & i3 & Hpoq & Hcom & Hscr).
  apply po_irreflex; auto.
  eapply vop_irreflex; eauto.
  eapply sbp_vop; eauto. (* sb implies vop *)
  eapply sb_posbs_sbp; eauto. (* po U sb with a leading sb => sbp, construct it *)
  - eapply drf_com_sb; eauto. (* first: com => sb *)
  - eapply drf_scs_posbs; eauto. (* second: scs => posbs *)
    eapply scs_poq_scs; eauto. (* seconsc*;poq => sc* *)
Qed.