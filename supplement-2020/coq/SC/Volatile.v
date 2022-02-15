Require Import Dynamic.
Require Import Sequence.
Require Import Relation.
Require Import Tactics.
Require Import Hwf.
Require Import History.
Require Import SC.Common.
Require Import Truncate.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Peano_dec.
Require Import Match.

Definition allexec H := forall i p, H {{ ev_init i p }} -> exec H i.

Lemma com_nvo { H i1 i2 } :
  trco H
  -> acyclic (co H)
  -> com H i1 i2
  -> ~ vo H i2 i1.
Proof.
  intros Htrco Hacyc [Hco | [Hrf | (i3 & Hrf & Hcop & Hneq)]] Hvo.
  - apply Hacyc.
    exists i1.
    eapply plus_step; eauto.
    eapply plus_one.
    assert (cop H i1 i2) as Hcop. {
      eapply plus_one.
      eauto.
    }
    destruct (cop_wf_prop H i1 i2 Htrco Hcop) as (l & Hwrl & Hwrr).
    eapply co_ww; eauto.
    left. apply plus_one. auto.
  - eapply vop_irreflex; eauto.
    eapply plus_step; eauto.
    apply plus_one.
    disj 1; auto.
  - apply Hacyc.
    exists i3.
    destruct (rf_wf_prop H i3 i1 Htrco Hrf) as (l & Hwritesi3 & Hreadsi1).
    destruct (cop_wf_prop H i3 i2 Htrco Hcop) as (l' & Hwritesi3' & Hwritesi2).
    erewrite <- (writesto_fun H i3 l l' Htrco Hwritesi3 Hwritesi3') in Hwritesi2; eauto.
    eapply plus_trans; eauto.
    eapply plus_one.
    eapply co_wr; eauto.
    + left; apply plus_one; auto.
    + intro Heq.
      apply Hacyc.
      exists i3.
      rewrite -> Heq in Hcop.
      auto.
Qed.

Lemma comp_writes_cop { H i1 i2 l }:
  trco H
  -> acyclic (co H)
  -> plus (com H) i1 i2
  -> writesto H i1 l
  -> writesto H i2 l
  -> plus (co H) i1 i2.
Proof.
  intros Htrco Hacycl Hcomp Hwr1 Hwr2.
  destruct (comp_to_write H i1 i2); auto.
  exists l. auto.
  apply fr_isw_cop; auto.
  exists l. auto.
Qed.


(* use to rearrange i1 -comp> i2 to i1 -coms> i3 -rf> i2 when i2 is not a write
 *)
Lemma comp_nisw_rf_coms { H i1 i2 i3 } :
  trco H
  -> plus (com H) i1 i2
  -> ~ isw H i2
  -> rf H i3 i2
  -> star (com H) i1 i3.
Proof.
  intros Htrco Hcomp Hnisw Hrf.
  apply plus_plusr in Hcomp.
  destruct Hcomp as (i4 & Hcoms & Hcom).
  edestruct (eq_nat_dec i3 i4) as [Heq | Hneq]; auto.
  - rewrite -> Heq. auto.
  - destruct Hcom as [Hco | [Hrf'  | Hfr]].
    + destruct (co_wf_prop H i4 i2 Htrco Hco) as (l & Hwritesi4 & Hwritesi2).
      exfalso.
      apply Hnisw.
      exists l.
      auto.
    + destruct (rf_fun H i4 i3 i2); auto.
    + exfalso.
      edestruct fr_isr_isw; eauto.
Qed.

Lemma is_access { H i } :
  trco H
  -> H {{ ev_is i ae | ae }}
  -> exists l, access H i l.
Proof.
  intros Htrco (a & His).
  destruct ((is_isac H i a) Htrco His);
    eauto;
    exists l.
  - left. apply reads_read in His. auto.
  - right. apply writes_write in His. exists v. auto.
  - left. apply reads_rw in His. auto.
Qed.

Lemma writesto_fun_loc { H i1 l1 l2 }:
  trco H
  -> writesto H i1 l1
  -> writesto H i1 l2
  -> l1 = l2.
Proof.
  intros Htrco (v1 & Hwrites1) (v2 & Hwrites2).
  destruct (writes_fun H i1 l1 l2 v1 v2 Htrco Hwrites1 Hwrites2); auto.
Qed.

Lemma co_access_locs { H i1 i2 l1 l2 } :
  trco H
  -> access H i1 l1
  -> access H i2 l2
  -> co H i1 i2
  -> l1 = l2.
Proof.
  intros Htrco Hac1 Hac2 Hco.
  edestruct co_wf_prop as (l & Hwrites1 & Hwrites2); eauto.
  destruct Hac1; destruct Hac2.
  - eapply reads_writesto_fun; eauto.
    assert (l2 = l) as Heq. eapply (reads_writesto_fun H); eauto.
    rewrite <- Heq in Hwrites1. auto.
  - eapply reads_writesto_fun; eauto.
    assert (l2 = l) as Heq. eapply (@writesto_fun_loc H); eauto.
    rewrite <- Heq in Hwrites1. auto.
  - apply eq_sym.
    eapply reads_writesto_fun; eauto.
    assert (l1 = l) as Heq. eapply (@writesto_fun_loc H); eauto.
    rewrite <- Heq in Hwrites2. auto.
  - eapply writesto_fun_loc; eauto.
    assert (l2 = l) as Heq. eapply (@writesto_fun_loc H); eauto.
    rewrite <- Heq in Hwrites1. auto.
Qed.

Lemma cop_access_locs { H i1 i2 l1 l2 } :
  trco H
  -> access H i1 l1
  -> access H i2 l2
  -> cop H i1 i2
  -> l1 = l2.
Proof.
  intros Htrco Hac1 Hac2 Hcop.
  apply plus_plusi in Hcop.
  induction Hcop.
  - eapply co_access_locs; eauto.
  - apply IHHcop; auto.
    destruct (@co_wf_prop H x y) as (l3 & Hwrite2 & Hwrite3); auto.
    right.
    assert (l1 = l3) as Heq. eapply co_access_locs; eauto.
    right. eauto.
    rewrite -> Heq; auto.
Qed.

Lemma rf_access_locs { H i1 i2 l1 l2 } :
  trco H
  -> access H i1 l1
  -> access H i2 l2
  -> rf H i1 i2
  -> l1 = l2.
Proof.
  intros Htrco Hac1 Hac2 Hrf.
  edestruct rf_wf_prop as (l & Hwrites & Hreads); eauto.
  destruct Hac1; destruct Hac2.
  - eapply reads_writesto_fun; eauto.
    assert (l2 = l) as Heq. eapply (reads_fun H); eauto.
    rewrite <- Heq in Hwrites. auto.
  - eapply reads_writesto_fun; eauto.
    assert (l = l2) as Heq. eapply (@reads_writesto_fun H); eauto.
    rewrite -> Heq in Hwrites. auto.
  - eapply reads_fun; eauto.
    assert (l1 = l) as Heq. eapply (@writesto_fun_loc H); eauto.
    rewrite <- Heq in Hreads. auto.
  - eapply writesto_fun_loc; eauto.
    assert (l = l2) as Heq. eapply (@reads_writesto_fun H); eauto.
    rewrite -> Heq in Hwrites. auto.
Qed.

Lemma fr_access_locs { H i1 i2 l1 l2 } :
  trco H
  -> access H i1 l1
  -> access H i2 l2
  -> fr H i1 i2
  -> l1 = l2.
Proof.
  intros Htrco Hac1 Hac2 Hfr.
  destruct Hfr as (i3 & Hrf & Hcop & Hneq).
  destruct (rf_wf_prop H i3 i1) as (l3 & Hwritesto & _); auto.
  eapply eq_trans;
    [ instantiate (1:=l3);apply eq_sym;eapply rf_access_locs; eauto
    | eapply cop_access_locs; eauto ];
    right; auto.
Qed.

Lemma com_fun { H i1 i2 l1 l2 } :
  trco H
  -> access H i1 l1
  -> access H i2 l2
  -> com H i1 i2
  -> l1 = l2.
Proof.
  intros Htrco Hac1 Hac2 Hcom.
  destruct Hcom as [Hco | [ Hrf | Hfr ]].
  - eapply co_access_locs; eauto.
  - eapply rf_access_locs; eauto.
  - eapply fr_access_locs; eauto.
Qed.

Lemma com_access_r {H i1 i2} :
  trco H
  -> com H i1 i2
  -> exists l, access H i2 l.
Proof.
  intros Htrco Hcom.
  destruct Hcom as [Hco | [Hrf | Hfr]].
  - destruct (co_wf_prop H i1 i2) as (l & _ & Hw); auto.
    exists l. right; auto.
  - destruct (rf_wf_prop H i1 i2) as (l & _ & Hr); auto.
    exists l. left; auto.
  - destruct (fr_isr_isw H i1 i2) as ( _ & (l & Hw)); auto.
    exists l. right; auto.
Qed.


Lemma comp_fun { H i1 i2 l1 l2 } :
  trco H
  -> access H i1 l1
  -> access H i2 l2
  -> plus (com H) i1 i2
  -> l1 = l2.
Proof.
  intros Htrco Hac1 Hac2 Hcomp.
  apply plus_plusi in Hcomp.
  induction Hcomp.
  - eapply com_fun; eauto.
  - apply IHHcomp; auto.
    edestruct (@com_access_r H) as (l3 & Hac3); eauto.
    assert (l1 = l3) as Heq. eapply com_fun; eauto.
    rewrite -> Heq.
    auto.
Qed.

Lemma isw_is { H i } : isw H i -> H {{ ev_is i ae | ae }}.
Proof.
  intros (l & v & [Hw | Hrw]); eauto.
Qed.

Lemma isr_is { H i } : isr H i -> H {{ ev_is i ae | ae }}.
Proof.
  intros (l & [Hr | Hrw]); eauto.
Qed.

Lemma com_is_l { H i1 i2 } :
  trco H
  -> com H i1 i2
  -> H {{ ev_is i1 ae | ae }}.
Proof.
  intros Htco [Hco | [Hrf | Hfr]];
    [ edestruct co_isw
    | edestruct rf_isw_isr
    | edestruct fr_isr_isw ];
    eauto using isw_is, isr_is.
Qed.

Lemma com_is_r { H i1 i2 } :
  trco H
  -> com H i1 i2
  -> H {{ ev_is i2 ae | ae }}.
Proof.
  intros Htco [Hco | [Hrf | Hfr]];
    [ edestruct co_isw
    | edestruct rf_isw_isr
    | edestruct fr_isr_isw ];
    eauto using isw_is, isr_is.
Qed.

Lemma comp_is_l { H i1 i2 } :
  trco H
  -> plus (com H) i1 i2
  -> H {{ ev_is i1 ae | ae }}.
Proof.
  intros Htrco Hcomp.
  apply plus_plusi in Hcomp.
  induction Hcomp; eauto using com_is_l.
Qed.

Lemma comp_is_r { H i1 i2 } :
  trco H
  -> plus (com H) i1 i2
  -> H {{ ev_is i2 ae | ae }}.
Proof.
  intros Htrco Hcomp.
  apply plus_plusi in Hcomp.
  induction Hcomp; eauto using com_is_r.
Qed.

Lemma allexec_spush_exec_l { H i1 i2 } :
  allexec H
  -> spush H i1 i2
  -> exec H i1.
Proof.
  intros Hallexec Hsp.
  destruct Hsp.
  edestruct po_init as (? & (? & Hpo)); eauto.
Qed.

Lemma allexec_spush_exec_r { H i1 i2 } :
  allexec H
  -> spush H i1 i2
  -> exec H i2.
Proof.
  intros Hallexec Hsp.
  destruct Hsp.
  edestruct po_init as (? & (? & Hpo)); eauto.
Qed.

Lemma allexec_volpo_exec_l { H i1 i2 } :
  allexec H
  -> volpo H i1 i2
  -> exec H i1.
Proof.
  intros Hallexec Hvol.
  destruct Hvol as (Hvol1 & Hvol2 & Hpo).
  edestruct po_init as (? & (? & Hpo')); eauto.
Qed.

Lemma allexec_volpo_exec_r { H i1 i2 } :
  allexec H
  -> volpo H i1 i2
  -> exec H i2.
Proof.
  intros Hallexec Hvol.
  destruct Hvol as (Hvol1 & Hvol2 & Hpo).
  edestruct po_init as (? & (? & Hpo')); eauto.
Qed.

Lemma allexec_push_exec_l { H i1 i2 } :
  allexec H
  -> push H i1 i2
  -> exec H i1.
Proof.
  intros Hallexec Hpush.
  destruct Hpush as [Hspush | Hvolpo];
    eauto using allexec_spush_exec_l, allexec_volpo_exec_l.
Qed.

Lemma allexec_po_l { H i1 i2 } :
  allexec H
  -> po H i1 i2
  -> exec H i1.
Proof.
  intros Hallexec Hpush.
  edestruct po_init as (? & ? & ?); eauto.
Qed.

Lemma allexec_po_r { H i1 i2 } :
  allexec H
  -> po H i1 i2
  -> exec H i2.
Proof.
  intros Hallexec Hpush.
  edestruct po_init as (? & ? & ?); eauto.
Qed.

Lemma allexec_push_exec_r { H i1 i2 } :
  allexec H
  -> push H i1 i2
  -> exec H i2.
Proof.
  intros Hallexec Hpush.
  destruct Hpush as [Hspush | Hvolpo];
    eauto using allexec_spush_exec_r, allexec_volpo_exec_r.
Qed.

(* if i1 -com->* i2
   i1 is executed
   i2 is a write
   then ~ i2 -vo> i1
   TODO switch to vop to match paper
 *)
Lemma coms_vo_contra { H i1 i2 l } :
  trco H
  -> acyclic (co H)
  -> star (com H) i1 i2
  -> exec H i1
  -> writesto H i2 l
  -> ~vopo H i2 i1.
Proof.
  intros Htrco Hacyc Hcom Hexec1 ? Hvo.
  destruct Hcom as [ | i1 ? i2 Hcom Hstar ].
  destruct Hvo.
  eapply vop_irreflex; eauto.
  eapply po_irreflex; eauto.

  assert (plus (com H) i1 i2) as Hcomp.
  exists y. auto.

  exfalso.
  eapply Hacyc.
  exists i2.
  edestruct (@is_access H i1) as (l' & Hworr); eauto.
  eapply exec_is; auto.
  erewrite -> (@comp_fun H i1 i2 l' l) in Hworr; auto.

  destruct Hworr as [Hreads | Hwritesto].
  + edestruct exec_read_rf as (iw & Hrf).
    eauto.
    eapply Hexec1. exists l. eauto.
    eapply plus_step.
    eapply co_wr; eauto.
    * edestruct (eq_nat_dec i2 iw) as [Heq' | Hneq]; auto.
      erewrite <- Heq' in Hrf.
      exfalso.
      apply Hacyc.
      exists i2.
      eapply comp_writes_cop; eauto.
      eapply plus_step; eauto.
    * eapply comp_writes_cop; eauto.
      eapply plus_step; eauto.
      eapply rf_loc_2; eauto.
  + eapply plus_trans.
    * eapply plus_one.
      instantiate (1:=i1).
      eapply co_ww; eauto.
    * eapply comp_writes_cop; eauto.
  + right; auto.
Qed.

(* i1 -push> i2 -com>* i3 -push> i4
   i3 is a write
   then
   i1 -to> i3
 *)
Lemma write_svo_comp_svo_to { H i1 i2 i3 i4 l } :
  trco H
  -> allexec H
  -> acyclic (co H)
  -> writesto H i3 l
  -> push H i1 i2
  -> star (com H) i2 i3
  -> push H i3 i4
  -> to H i1 i3.
Proof.
  intros Htrco Hallexec Hacyc Hisw Hsp1 Hcomp Hsp2.

  assert (exec H i1) as Hexec1. eauto using allexec_push_exec_l.
  assert (exec H i2) as Hexec2. eauto using allexec_push_exec_r.
  assert (exec H i3) as Hexec3. eauto using allexec_push_exec_l.

  destruct (trace_trichot H i1 i3) as [Hdone | [Heq | Hcontr]];
    auto;
    exfalso;
    eapply coms_vo_contra;
    eauto;
    left; apply plus_one.
  Hint Unfold push.
  - unfold vo.
    rewrite -> Heq in Hsp1.
    intuition.
  - disj 5.
    exists i4, i1.
    intuition.
Qed.

(* given the above lemma, then i1 -vo> i4
   that is, the head of the first push order is
   before the tail of the second push order
   because the heads are trace ordered
 *)
Corollary write_svo_comp_svo_vo { H i1 i2 i3 i4 l } :
  trco H
  -> allexec H
  -> acyclic (co H)
  -> writesto H i3 l
  -> push H i1 i2
  -> star (com H) i2 i3
  -> push H i3 i4
  -> vo H i1 i4.
Proof.
  intros; disj 5; do 2 econstructor; split; [|split]; eauto.
  eapply write_svo_comp_svo_to; eauto.
Qed.

(* when the second push has a read at the head (i4) then use the vis from the write

   i1 -push> i2 -com>* i3 -vo> i4 -push> i5

   then

   i1 -to> i4

   the idea being that if i4 is a read then i3 -rf> i4
   we use the more general i3 -vo> i4 to save time in proofs
   later.
 *)
Lemma write_svo_comp_vo_svo_to { H i1 i2 i3 i4 i5 l } :
  trco H
  -> allexec H
  -> acyclic (co H)
  -> writesto H i3 l
  -> push H i1 i2
  -> star (com H) i2 i3
  -> vo H i3 i4
  -> push H i4 i5
  -> to H i1 i4.
Proof.
  intros Htrco Hallexec Hacyc Hisw Hsp1 Hcomp Hvo Hsp2.

  assert (exec H i1) as Hexec1. eauto using allexec_push_exec_l.
  assert (exec H i2) as Hexec2. eauto using allexec_push_exec_r.
  assert (exec H i4) as Hexec3. eauto using allexec_push_exec_l.

  destruct (trace_trichot H i1 i4) as [Hdone | [Heq | Hcontr]];
    auto;
    exfalso;
    eapply coms_vo_contra;
    eauto;
    left;
    eapply plus_step; eauto;
    apply plus_one.
  Hint Unfold push vo.
  - rewrite -> Heq in Hsp1.
    disj 2.
    intuition.
  - disj 5.
    exists i5, i1.
    intuition.
Qed.

(*
  Now we can do both cases for i3 (write or read).

  i1 -push> i2 -com>+ i3 -push> i4

  When it's a write:
    - write_svo_comp_svo_to

  When it's a read:
    - then it must have read from some write i5
    - i2 -com>* i5 by comp_nisw_rf_coms
    - then write_sco_comp_vo_svo_to
 *)
Lemma svo_comp_svo_to { H i1 i2 i3 i4 } :
  trco H
  -> allexec H
  -> acyclic (co H)
  -> push H i1 i2
  -> plus (com H) i2 i3
  -> push H i3 i4
  -> to H i1 i3.
Proof.
  intros Htrco Hallexec Hacyc Hsp1 Hcomp Hsp2.
  destruct (writesto_decidable_i H i3) as [ (l & Hwrites) | ].
  - eapply write_svo_comp_svo_to; eauto using plus_star.
  - assert (exec H i3) as Hexec3. eauto using allexec_push_exec_l.
    edestruct (@exec_is H i3); eauto.
    edestruct (reads_writes H i3) as [ (l & Hreads) | Hcontra ]; eauto; try contradiction.
    edestruct (exec_read_rf H i3) as (i5 & Hrf); eauto.
    edestruct is_inited; eauto.
    exists l. auto.
    edestruct rf_wf_prop as (l' & Hwritesto & _ ); eauto.
    eapply write_svo_comp_vo_svo_to; eauto.
    eapply comp_nisw_rf_coms; eauto.
Qed.

Corollary svo_comp_svo_vo { H i1 i2 i3 i4 } :
  trco H
  -> allexec H
  -> acyclic (co H)
  -> push H i1 i2
  -> plus (com H) i2 i3
  -> push H i3 i4
  -> vo H i1 i4.
Proof.
  intros; disj 5; do 2 econstructor; split; [|split]; eauto.
  eapply svo_comp_svo_to; eauto.
Qed.


Definition poloc H i1 i2 := po H i1 i2 /\ exists l, access H i1 l /\ access H i2 l.

    
Lemma write_read_po_comp_contra { H i1 i2 l }:
  trco H
  -> allexec H
  -> acyclic (co H)
  -> writesto H i1 l
  -> reads H i2 l
  -> po H i1 i2
  -> plus (com H) i2 i1
  -> False.
Proof.
  intros Htco Hallexec Hacycl Hw Hr Hpoloc Hcomp.
  eapply com_acyclic; eauto.
  edestruct exec_read_rf as (i3 & Hrf); eauto using allexec_po_r.
  exists l; eauto.
  exists i1.
  edestruct rf_wf_prop as (l' & Hw' & Hr'); eauto.
  destruct (dec_eq_nat i1 i3) as [Heq | Hneq].
  + eapply plus_step; eauto.
    rewrite Heq.
    right; left; auto.
  + eapply plus_step.
    left. eapply co_wr; eauto. right; eauto.
    eapply plus_step; eauto.
Qed.

Lemma poloc_comp_contra { H i1 i2 } :
  trco H
  -> allexec H
  -> acyclic (co H)
  -> poloc H i1 i2
  -> plus (com H) i2 i1
  -> False.
Proof.
  intros Htrco Hexec Hacyc Hpoloc.
  intros.
  destruct Hpoloc as (Hpo & (l & [Hacc1 | Hacc1] & [Hacc2 | Hacc2])).
  - (*
      i1 = read
      i2 = read
      i3 -rf> i1
      i4 -rf> i2
      either i3 -co> i4 \/ i3 = i4
      cases
      - i3 -co> i4
        then i1 -fr> i4 -rf> i2 -coms> i1
        then i1 -coms> i1, contradiction by com_acyclic
      - i3 = i4
        by i2 -com+> i1, i3 -rf> i1 and comp_nisw_rf_coms we have i2 -com*> i3
        then i3 -rf> i2 -com*> i3
        then i3 -coms> i3, contradiction by com_acyclic
     *) 
    eapply com_acyclic; eauto.
    edestruct exec_read_rf as (i3 & Hrf'); eauto using allexec_po_l.
    exists l; eapply Hacc1.
    edestruct rf_wf_prop as (l' & Hw' & Hr'); eauto.
    edestruct exec_read_rf as (i4 & Hrf''); eauto using allexec_po_r.
    exists l; eauto.
    edestruct rf_wf_prop as (l'' & Hw'' & Hr''); eauto.
    destruct (dec_eq_nat i3 i4) as [Heq | Hneq].
    * exists i3.
      eapply plus_star_trans.
      eapply plus_one.
      right; left.
      rewrite <- Heq in Hrf''.
      eauto.
      eapply comp_nisw_rf_coms; eauto.
      intros (l''' & ? & Hwrite).
      assert (l = l''') as Heql. eapply reads_writes_fun. eauto. eapply Hacc1. eauto.
      rewrite <- Heql in Hwrite.
      eapply write_read_po_comp_contra.
      eauto.
      eauto.
      eauto.
      exists x. eapply Hwrite.
      eapply Hacc2.
      auto.
      auto.
    * exists i1.
      eapply plus_step.
      right; right.
      eexists.
      split; [|split].
      eapply Hrf'.
      eapply plus_one.
      eapply co_rr.
      eapply Hrf'.
      eapply Hrf''.
      auto.
      eauto.
      assert (l' = l) as Hloceq1. eapply reads_fun; eauto.
      assert (l = l'') as Hloceq2. eapply reads_fun; eauto.
      rewrite Hloceq1. rewrite Hloceq2.
      auto.
      auto.
      unfold not; intros Heq.
      eapply com_acyclic; eauto.
      exists i1.
      eapply plus_step.
      right; left.
      rewrite <- Heq in Hrf''.
      eauto.
      auto.
      eapply plus_step.
      right; left.
      eauto.
      auto.
  - 
    (*
      i1 = read
      i2 = write
      i1 -po> i2
      exists i3, i3 -rf> i1
      then by co_rw, i3 -co> i2
      then i1 -fr> i2
      then i1 -fr> i2 -com+> i1
      then i1 -com+> i1, contradiction by com_acyclic.
     *)

    eapply com_acyclic; eauto.
    edestruct exec_read_rf as (i3 & Hrf); eauto using allexec_po_l.
    exists l; eauto.
    edestruct rf_wf_prop as (l' & Hw & Hr); eauto.
    exists i2.
    eapply plus_stepr.
    apply plus_star; eauto.
    right; right.
    eexists.
    split; [|split].
    eauto.
    eapply plus_one.
    eapply co_rw; eauto.
    left.
    eapply plus_one.
    disj 1.
    eauto.
    erewrite (reads_fun); eauto.
    unfold not; intros Heq.
    rewrite Heq in Hpo.
    eapply po_irreflex; eauto.
  - (*
      i1 = write
      i2 = read
      exists i3 , i3 -rf> i2
      either i3 = i1 \/ i3 <> i1
      - i3 = i1
        then i1 -rf> i2 -com+> i1
        then i1 -com+> i1, contradiction by com_acyclic
      - i3 <> i1
        then by i3 -rf> i2 and i1 -po> i2 we have i1 -co> i3
        then i1 -co> i3 -rf> i2 -com+> i1
        then i1 -com+> i1, contradiction by com_acyclic
     *)

    eapply write_read_po_comp_contra; eauto.
  - eapply com_acyclic; eauto.
    exists i1.
    eapply plus_step; eauto.
    constructor.
    eapply co_ww; eauto.
    right; eauto.
Qed.
  

(* The rest of these lemmas are rearranging our assumptions to fit the
   above lemmas. Namely:

   i1 -sc> i1 => exists i2 i3, i1 -sc> i2 -po> i3 -sc>* i1           (must be by -com+> => -vo>+
              => i2 -po> i3 -sc> i2                                  (rearrange) 
              => exists i4 i5, i2 -po> i3 -sc>* i4 -com> i5 -sc>* i2 (must be by i -po> i contra)
              => i2 (-po>-com>+)+ i2                                 (then we rearrange to a sequence, this is the hard part)

   by induction and svo_comp_svo_vo i2 -vo>+ i2 which is a contradiction.
 *)

Definition pocomp H i1 i2 :=
  exists i3, po H i1 i3 /\ plus (com H) i3 i2.

Definition allpush H := forall i1 i2, po H i1 i2 -> push H i1 i2.
Definition allspush H := forall i1 i2, po H i1 i2 -> spush H i1 i2.
Definition allvolatile H := forall i, isvol H i.

Lemma svo_scp_svo_to { H i1 i3 i4 } :
  trco H
  -> allexec H
  -> acyclic (co H)
  -> allpush H
  -> plus (pocomp H) i1 i3
  -> push H i3 i4
  -> to H i1 i3.
Proof.
  intros Htrco Hallexec Hacyc Hallpush Hscp Hsp2.
  apply plus_plusi in Hscp.
  induction Hscp as [ i1 i2 Hpocomp | i1 i2 i3 Hpocomp Hplus ];
    destruct Hpocomp as (i5 & Hpo & Hcom).
  - eapply svo_comp_svo_to; eauto.
  - apply plusi_plus in Hplus.
    destruct Hplus as (i6 & (i7 & Hpo' & Hcomp) & Hstar).
    eapply to_trans; eauto.
    eapply svo_comp_svo_to; eauto.
Qed.

(* must communicate *)
Definition pocoms H i1 i2 :=
  exists i3, po H i1 i3 /\ star (com H) i3 i2.

Definition pocomppoq H i1 i2 :=
  exists i3 i4, po H i1 i3 /\ plus (com H) i3 i4 /\ poq H i4 i2.

Lemma sc_po_pocomp { H i1 i2 i3 } :
  trco H
  -> plus (pocomppoq H) i1 i2
  -> star (sc (po H) H) i2 i3
  -> plus (pocomppoq H) i1 i3.
Proof.
  intros Htrco Hpocomppoq Hscs.
  induction Hscs as [ i2 i3 Hsc | i2 i3 i4 Hsc Hscp ].
  - auto.
  - apply plus_plusr in Hpocomppoq.
    destruct Hpocomppoq as (i5 & Hpocomppoqp & Hpocomppoq ).
    destruct Hpocomppoq as (i6 & i7 & Hpo1 & Hcomp & Hpoq).
    destruct Hpoq as [ Hpo2 | Heq ];
      destruct Hsc as [ Hpo3 | Hcom ];
      apply IHHscp;
      [ apply plusr_plus; exists i5; split; auto
      | apply plusr_plus; exists i5; split; auto
      | apply plusr_plus; exists i5; split; auto
      | ].
    + exists i6, i7.
      split; [ | split ]; auto.
      rewrite <- Hpo2 in Hpo3.
      right. auto.
    + exists i6, i3.
      split; [ | split ]; auto.
      apply plusr_plus.
      exists i2; split; auto.
      apply plus_star.
      rewrite -> Hpo2 in Hcomp.
      auto.
      left; auto.
    + exists i6, i7.
      split; [ | split ]; auto.
      right. eapply po_trans; eauto.
    + eapply plus_trans.
      * eapply plusr_plus.
        exists i5.
        split; auto.
        exists i6, i7.
        split; [ | split ]; auto.
        left. instantiate (1:=i7). eauto.
      * simpl.
        exists i3.
        split; [| apply star_refl] .
        exists i2, i3.
        split; [| split ]; auto.
        apply plus_one.
        unfold com. auto.
        left; auto.
Qed.

Lemma pocomppoq_pocomp_poq { H i1 i2 } :
  trco H
  -> plus (pocomppoq H) i1 i2
  -> exists i3, plus (pocomp H) i1 i3 /\ poq H i3 i2.
Proof.
  intros Htrco Hpocomppoq.
  apply plus_plusi in Hpocomppoq.
  induction Hpocomppoq as [ i1 i2 Hbase | i1 i2 i3 (i4 & i5 & Hind) Hrest (i6 & Hplus & Hpoq ) ].
  - destruct Hbase  as (i3 & i4 & Hpo & Hcomp & Hpoq).
    exists i4.
    split; auto.
    apply plus_one.
    exists i3. split; auto.
  - exists i6.
    split; auto.
    clear Hpoq Hrest.
    destruct Hplus as (i7 & Hpocomp & Hpocomps).
    destruct Hpocomp as (i8 & Hpo2 & Hcomp2).
    destruct Hind as (Hpo1 & Hcomp1 & Hpoq).
    destruct Hpoq as [Heq | Hpo];
      [ rewrite -> Heq in Hcomp1 | ].
    + eapply plus_trans.
      apply plus_one.
      exists i4. split; eauto.
      exists i7. split; [ exists i8; split |]; auto.
    + eapply plus_trans.
      apply plus_one.
      exists i4. split; eauto.
      exists i7. split; [ exists i8; split |]; auto.
      eapply po_trans; eauto.
Qed.

Theorem push_sc { H } :
  trco H
  -> allexec H
  -> allpush H
  -> acyclic (co H)
  -> acyclic (sc (po H) H).
Proof.
  intros Htrco Hallexec Hallpush Hacyc (i1 & Hsc).
  edestruct sc_cycle_r as (i2 & i3 & Hpo & Hcoms); eauto.
  edestruct star_plus as [Heq | Hplus]; eauto.
  - rewrite -> Heq in Hpo.
    exfalso.
    eapply po_irreflex; eauto.
  - clear Hcoms.
    edestruct (@sc_must_com H) as (i4 & i5 & Hpoq & (Hcom & Hscs)); eauto.
    intro.
    eapply po_irreflex; eauto.
    eapply po_trans; eauto.

    edestruct (@pocomppoq_pocomp_poq H i2 i2) as (i6 & Hpocomp & Hpoq'); auto.
    eapply sc_po_pocomp; eauto.
    destruct Hpoq as [Heq | Hpo']; apply plus_one; exists i4, i5; (split; [| split]; auto).
    rewrite -> Heq in Hpo; auto.
    apply plus_one; auto.
    left; auto.
    eapply po_trans; eauto.
    apply plus_one; auto.
    left; auto.

    destruct Hpoq' as [Heq | Hpo'];
      eapply to_irreflex;
      eapply svo_scp_svo_to; eauto.
    + rewrite -> Heq in Hpocomp.
      eauto.
    + destruct Hpocomp as (i7 & Hpocomp & Hposcomps).
      destruct Hpocomp as (i8 & Hpo'' & Hcomp).
      exists i7.
      split; eauto.
      exists i8.
      split; eauto.
      eapply po_trans; eauto.
Qed.

Corollary spush_sc { H } :
  trco H
  -> allexec H
  -> allspush H
  -> acyclic (co H)
  -> acyclic (sc (po H) H).
Proof.
  intros ? ? Hallspush ?.
  apply push_sc; auto.
  left.
  auto using Hallspush.
Qed.

Corollary volatile_sc { H } :
  trco H
  -> allexec H
  -> allvolatile H
  -> acyclic (co H)
  -> acyclic (sc (po H) H).
Proof.
  intros ? ? Hallvolatile ?.
  apply push_sc; auto.
  right; split; [| split];
  auto using Hallvolatile.
Qed.
