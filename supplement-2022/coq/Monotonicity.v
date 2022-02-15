Require Import Dynamic.
Require Import Sequence.
Require Import Relation.
Require Import Tactics.
Require Import Hwf.
Require Import History.
Require Import Bool.

Definition iss H i a := H {{ ev_is i a }}.

Definition subset {T1 T2 : Type} (R1 R2 : T1 -> T2 -> Prop) :=
  forall i1 i2, R1 i1 i2 -> R2 i1 i2.

Fixpoint mode_lte_ord (m1 m2 : mode) : bool :=
  match (m1, m2) with
  | (plain, _) => true
  | (opaque, opaque) => true
  | (opaque, relacq) => true
  | (opaque, vol) => true
  | (relacq, relacq) => true
  | (relacq, vol) => true
  | (vol, vol) => true
  | _ => false
  end.

Inductive access_lte_ordered : history -> history -> identifier -> Prop :=
| access_lte_ordered_read {H1 H2 i l m1 m2} :
    H1 {{ ev_is i (ac_read l m1) }}
    -> H2 {{ ev_is i (ac_read l m2) }}
    -> mode_lte_ord m1 m2 = true
    -> access_lte_ordered H1 H2 i

| access_lte_ordered_write {H1 H2 i l v m1 m2} :
    H1 {{ ev_is i (ac_write l v m1) }}
    -> H2 {{ ev_is i (ac_write l v m2) }}
    -> mode_lte_ord m1 m2 = true
    -> access_lte_ordered H1 H2 i

| access_lte_ordered_rw {H1 H2 i l v} :
    H1 {{ ev_is i (ac_rw l v) }}
    -> H2 {{ ev_is i (ac_rw l v) }}
    -> access_lte_ordered H1 H2 i.

Definition fiat_vo (H : history) (i1 i2 : identifier) := H {{ ev_vo i1 i2 }} \/ H {{ ev_push i1 i2}}.

Ltac write_discr i :=
  match goal with
  | [ Hw : ?H2 {{ ev_is i (ac_write ?l1 ?v1 ?m1) }} |- _ ] =>
    match goal with
    | [ Hr : H2 {{ ev_is i (ac_read ?l2 ?m2) }} |- _ ] =>
      discriminate (is_fun H2 i (ac_write l1 v1 m1) (ac_read l2 m2)); eauto
    | [ Hr : H2 {{ ev_is i (ac_rw ?l2 ?v2) }} |- _ ] =>
      discriminate (is_fun H2 i (ac_write l1 v1 m1) (ac_rw l2 v2)); eauto
    end
  end.

Ltac rw_discr i :=
  match goal with
  | [ Hw : ?H2 {{ ev_is i (ac_rw ?l1 ?v1) }} |- _ ] =>
    match goal with
    | [ Hr : H2 {{ ev_is i (ac_read ?l2 ?m2) }} |- _ ] =>
      discriminate (is_fun H2 i (ac_rw l1 v1) (ac_read l2 m2)); eauto
    | [ Hr : H2 {{ ev_is i (ac_write ?l2 ?v2 ?m2 ) }} |- _ ] =>
      discriminate (is_fun H2 i (ac_rw l1 v1) (ac_write l2 v2 m2)); eauto
    end
  end.

Ltac read_discr i :=
  match goal with
  | [ Hw : ?H2 {{ ev_is i (ac_read ?l1 ?v1) }} |- _ ] =>
    match goal with
    | [ Hr : H2 {{ ev_is i (ac_write ?l2 ?v2 ?m2 ) }} |- _ ] =>
      discriminate (is_fun H2 i (ac_read l1 v1) (ac_write l2 v2 m2)); eauto
    | [ Hr : H2 {{ ev_is i (ac_rw ?l2 ?v2) }} |- _ ] =>
      discriminate (is_fun H2 i (ac_read l1 v1) (ac_rw l2 v2)); eauto
    end
  end.


Ltac access_lte_ordered_disc i :=
  match goal with
  | [ Hord : forall i', access_lte_ordered ?H2 ?H1 i' |- _ ] =>
    destruct (Hord i) as 
      [ H2 H1 i l2 m1 m2 His1 His2 Hmodeord
      | H2 H1 i l2 v2 m1 m2  His1 His2 Hmodeord
      | H2 H1 i l2 v2 His1 His2 ];
    try write_discr i;
    try read_discr i;
    try rw_discr i
  end.

Lemma writesto_ord {H1 H2 i l1} :
  trco H2
  -> writesto H2 i l1
  -> (forall i, access_lte_ordered H2 H1 i)
  -> writesto H1 i l1.
Proof.
  intros Htrco Hw Hord.
  destruct Hw as (v1 & Hw).
  exists v1.
  destruct Hw as [ H2 i l1 v1 m | H2 i l1 v1 ];
    access_lte_ordered_disc i;
    edestruct (writes_fun H2 i l1) as (Hleq & Hveq);
    eauto using writes_write, writes_rw;
    rewrite Hleq, Hveq; eauto using writes_write, writes_rw.
Qed.

Lemma reads_ord {H1 H2 i l1} :
  trco H2
  -> reads H2 i l1
  -> (forall i, access_lte_ordered H2 H1 i)
  -> reads H1 i l1.
Proof.
  intros Htrco Hr Hord.
  destruct Hr as [ H2 i l1 m | H2 i l1 ];
  access_lte_ordered_disc i;
  erewrite reads_fun;
  eauto using reads_read, reads_rw.
Qed.

Hint Unfold isvolw isvolr.

Lemma hist_match_pop {H1 H2 i1 i2} :
  trco H2 
  -> subset (po H2) (po H1)
  -> subset (to H2) (to H1)
  -> subset (rf H2) (rf H1)
  -> (forall i, access_lte_ordered H2 H1 i)
  -> pop H2 i1 i2
  -> pop H1 i1 i2.
Proof.
  intros Htrco Hposub Htosub Hrfsub Hord Hpop.
  destruct Hpop as (Hpo & Hisop1 & Hisop2).

  Hint Unfold opm.
  split; [| split]; auto;
    [ destruct Hisop1 as [(m & (l1 & Hrd1) & Hopm) | (m & (l1 & v & Hwr1) & Hopm) ] 
    | destruct Hisop2 as [(m & (l1 & Hrd1) & Hopm) | (m & (l1 & v & Hwr1) & Hopm) ] ];
      [ left | right | left | right ];
      [ access_lte_ordered_disc i1
      | access_lte_ordered_disc i1
      | access_lte_ordered_disc i2
      | access_lte_ordered_disc i2 ].

  rewrite <- (reads_fun H2 i1 l2 l1) in Hrd1; eauto using reads_read.
  rewrite <- (read_fun_mode H2 i1 l2 l2 m m1) in Hmodeord, His1; eauto.
  destruct m2; simpl in Hmodeord; try discriminate; eauto;
    destruct m; destruct Hopm as [ ? | [ ? | ? ]]; try discriminate; auto;
      try ( exists opaque; intuition; exists l2; auto; done);
      try ( exists relacq; intuition; exists l2; auto; done);
      try ( exists vol; intuition; exists l2; auto; done).

  rewrite <- (writesto_fun H2 i1 l2 l1) in Hwr1; eauto using writes_write.
  rewrite <- (writes_fun_val H2 i1 l2 v2 v) in Hwr1; eauto using writes_write.
  rewrite <- (write_fun_mode H2 i1 l2 l2 v2 v2 m m1) in Hmodeord, His1; eauto.
  destruct m2; simpl in Hmodeord; try discriminate; eauto;
    destruct m; destruct Hopm as [ ? | [ ? | ? ]]; try discriminate; auto;
      try ( exists opaque; intuition; exists l2, v2; auto; done);
      try ( exists relacq; intuition; exists l2, v2 ; auto; done);
      try ( exists vol; intuition; exists l2, v2; auto; done).
  exists v2; eauto using writes_write.
  exists v; eauto using writes_write.

  rewrite <- (reads_fun H2 i2 l2 l1) in Hrd1; eauto using reads_read.
  rewrite <- (read_fun_mode H2 i2 l2 l2 m m1) in Hmodeord, His1; eauto.
  destruct m2; simpl in Hmodeord; try discriminate; eauto;
    destruct m; destruct Hopm as [ ? | [ ? | ? ]]; try discriminate; auto;
      try ( exists opaque; intuition; exists l2; auto; done);
      try ( exists relacq; intuition; exists l2; auto; done);
      try ( exists vol; intuition; exists l2; auto; done).

  rewrite <- (writesto_fun H2 i2 l2 l1) in Hwr1; eauto using writes_write.
  rewrite <- (writes_fun_val H2 i2 l2 v2 v) in Hwr1; eauto using writes_write.
  rewrite <- (write_fun_mode H2 i2 l2 l2 v2 v2 m m1) in Hmodeord, His1; eauto.
  destruct m2; simpl in Hmodeord; try discriminate; eauto;
    destruct m; destruct Hopm as [ ? | [ ? | ? ]]; try discriminate; auto;
      try ( exists opaque; intuition; exists l2, v2; auto; done);
      try ( exists relacq; intuition; exists l2, v2 ; auto; done);
      try ( exists vol; intuition; exists l2, v2; auto; done).
  exists v2; eauto using writes_write.
  exists v; eauto using writes_write.
Qed.

Hint Resolve hist_match_pop.

Lemma isvol_match { H1 H2 i } :
  trco H2
  -> isvol H2 i
  -> subset (po H2) (po H1)
  -> (forall i, access_lte_ordered H2 H1 i)
  -> isvol H1 i.
    Proof.
      intros Htrco Hisvol1 Hposub Hord.
    destruct Hisvol1 as [Hvol1d | Hvol1d];
      try (destruct Hvol1d as (l & v & Hvol1d));
      try (destruct Hvol1d as (l & Hvol1d));
      access_lte_ordered_disc i.

    rewrite <- (read_fun_mode H2 i l l2 vol m1) in Hmodeord, His1; eauto.
    Hint Unfold isvol.
    destruct m2; simpl in Hmodeord; try discriminate; unfold isvol.
    left. exists l2. auto.

    rewrite <- (write_fun_mode H2 i l l2 v v2 vol m1) in Hmodeord, His1; eauto.
    destruct m2; simpl in Hmodeord; try discriminate; unfold isvol.
    right. exists l2, v2. auto.
    Qed.


Lemma hist_match_vo {H1 H2 i1 i2} :
  trco H2 
  -> subset (po H2) (po H1)
  -> subset (to H2) (to H1)
  -> subset (rf H2) (rf H1)
  -> (forall i1 i2, ~ fiat_vo H2 i1 i2)
  -> (forall i, access_lte_ordered H2 H1 i)
  -> vo H2 i1 i2
  -> vo H1 i1 i2.
Proof.
  intros Hissub Hposub Htosub Hrfsub Hnofiat Hord Hvo.
  destruct Hvo as [(Hvo & Hpo) | [Hrf | [ [(Hpush & Hpo) | (Hisvol1 & Hisvol2 & Hpo) ]| [ Hrelvo | [ Hacqvo | Hpushvo]]]]].
  - exfalso.
    eapply Hnofiat.
    left; eauto.
  - disj 1.
    eauto using Hrfsub.
  - disj 2.
    exfalso.
    eapply Hnofiat.
    right; eauto.
  - disj 2.
    disj 1.
    split; [| split ]; eauto;
    eapply isvol_match; eauto.

  - disj 3.
    destruct Hrelvo as ([(l & v & Hrelw) | Hvolw ] & Hpo);
      split; eauto;
        [ | destruct Hvolw as (l & v & His)];
        access_lte_ordered_disc i2.

    + rewrite <- (write_fun_mode H2 i2 l l2 v v2 relacq m1) in Hmodeord, His1; eauto.
      destruct m2; simpl in Hmodeord; try discriminate; eauto; [ left | right ]; eauto.
    + rewrite <- (write_fun_mode H2 i2 l l2 v v2 vol m1) in Hmodeord, His1; eauto.
      destruct m2; simpl in Hmodeord; try discriminate; eauto; right; eauto.

  - disj 4.

    destruct Hacqvo as ([(l & Hacqr) | Hvolr ] & Hpo);
      split; eauto;
        [ | destruct Hvolr as (l & His)];
        access_lte_ordered_disc i1.

    + rewrite <- (read_fun_mode H2 i1 l l2 relacq m1) in Hmodeord, His1; eauto.
      destruct m2; simpl in Hmodeord; try discriminate; [ left | right ];  eauto.
    + rewrite <- (read_fun_mode H2 i1 l l2 vol m1) in Hmodeord, His1; eauto.
      destruct m2; simpl in Hmodeord; try discriminate; right; eauto.

  - disj 5.
    destruct Hpushvo as (i3 & i4 & [(Hpush & _) | (Hisvol1 & Hisvol2 & Hpo)] & [(Hpush' & _) | (Hisvol1' & Hisvol2' & Hpo')] & Hto);
      try (exfalso; eapply Hnofiat; right; eauto; done).
    exists i3, i4;
      split; [| split]; auto; right;
        (split; [| split]; auto);
        eauto using isvol_match.
Qed.


Lemma hist_match_vop {H1 H2 i1 i2} :
  trco H2 
  -> subset (po H2) (po H1)
  -> subset (to H2) (to H1)
  -> subset (rf H2) (rf H1)
  -> (forall i1 i2, ~ fiat_vo H2 i1 i2)
  -> (forall i, access_lte_ordered H2 H1 i)
  -> vop H2 i1 i2
  -> vop H1 i1 i2.
Proof.
  intros Hissub Hposub Htosub Hrfsub Hnofiat Hord Hvop.
  apply plus_plusi in Hvop.
  induction Hvop.
  - apply plus_one.
    eauto using hist_match_vo.
  - eapply plus_step;
    eauto using hist_match_vo.
Qed.

Lemma hist_match_hb {H1 H2 i1 i2} :
  trco H2 
  -> subset (po H2) (po H1)
  -> subset (to H2) (to H1)
  -> subset (rf H2) (rf H1)
  -> (forall i1 i2, ~ fiat_vo H2 i1 i2)
  -> (forall i, access_lte_ordered H2 H1 i)
  -> vopo H2 i1 i2
  -> vopo H1 i1 i2.
Proof.
  intros Hissub Hposub Htosub Hrfsub Hnofiat Hord Hhb.
  inversion Hhb;
    [ left; eauto using hist_match_vop
    | right; auto ].
Qed.

Theorem monotonicity {H1 H2} :
  acyclic(co H1)
  -> trco H2
  -> subset (po H2) (po H1)
  -> subset (to H2) (to H1)
  -> subset (rf H2) (rf H1)
  -> (forall i1 i2, ~ fiat_vo H2 i1 i2)
  -> (forall i, access_lte_ordered H2 H1 i)
  -> acyclic(co H2).
Proof.
  intros Hacyc Htrco Hposub Htosub Hrfsub Hnofiat Hmode.
  eapply acyclic_anti; [| apply Hacyc ].
  intros i3 i4 Hcosub.
  induction Hcosub;
    [ eapply co_ww
    | eapply co_wr
    | eapply co_rw
    | eapply co_rr
    | eapply co_atm_total
    | eapply co_atm_after ]; 
    eauto using writesto_ord, reads_ord, hist_match_hb.
  - destruct H0 as [ (l' & v' & His) | (l' & v' & His) ].
    access_lte_ordered_disc iw1.
    left. exists l2, v2. auto.

    access_lte_ordered_disc iw2.
    right. exists l2, v2. auto.
  - destruct H0 as (Hrf & Hrw).
    split.
    + apply Hrfsub. auto.
    + destruct Hrw as (l' & v' & His).
    access_lte_ordered_disc irw.
    exists l2, v2. auto.
Qed.
