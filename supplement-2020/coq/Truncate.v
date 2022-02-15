Require Import Tactics.
Require Import Dynamic.
Require Import Sequence.
Require Import Relation.
Require Import Hwf.
Require Import History.
Require Import Match.

Lemma so_tail :
  forall H h i1 i2,
    trco (H; h)
    -> ~ h = ev_vo i1 i2
    -> ~ h = ev_push i1 i2
    -> ~ (exists a, h = ev_is i1 a)
    -> ~ (exists a, h = ev_is i2 a)
    -> ~ (exists p, h = ev_init i2 p)
    -> so (H; h) i1 i2
    -> so H i1 i2.
Proof.
  intros H h i1 i2 Htrco Hneqvo Hneqpush Hneqis1 Hneqis2 Hneqinit Hso.
  invert Hso; intros Hpo Hin; destruct Hin;
    try contradiction.

  Ltac fix_po Hneqinit := 
    eapply po_tail; eauto;
    intros i p Hheq Heq;
    apply Hneqinit;
    exists p;
    rewrite <- Heq;
    eauto.

  - apply so_vo; auto. fix_po Hneqinit.
  - apply so_push; auto. fix_po Hneqinit.
  - apply so_acqr. fix_po Hneqinit.
    destruct H0 as (l & [Heq | Hin]).
    exfalso.
    apply Hneqis1.
    exists (ac_read l relacq). auto.
    left. eauto.
  - apply so_acqr. fix_po Hneqinit.
    destruct H0 as (l & [Heq | Hin]).
    exfalso.
    apply Hneqis1.
    exists (ac_read l vol). auto.
    right.
    exists l.
    auto.
  - apply so_relw. fix_po Hneqinit.
    destruct H0 as (l & v & [Heq | Hin]).
    exfalso.
    apply Hneqis2.
    exists (ac_write l v relacq).
    auto.
    left.
    exists l, v. auto.
  - apply so_relw. fix_po Hneqinit.
    destruct H0 as (l & v & [Heq | Hin]).
    exfalso.
    apply Hneqis2.
    exists (ac_write l v vol).
    auto.
    right.
    exists l, v. auto.
  - intro. apply so_vol. fix_po Hneqinit.
    + destruct H0 as (l & [ Heq | Hin ]).
      * exfalso.
        apply Hneqis1.
        exists (ac_read l vol).
        auto.
      * left. exists l. auto.
    + destruct H3 as [ Hvolr | Hvolw ].
      * destruct Hvolr as (l & [ Heq | Hin ]).
        -- exfalso.
           apply Hneqis2.
           exists (ac_read l vol).
           auto.
        -- left. exists l. auto.
      * destruct Hvolw as (l & v & [ Heq | Hin ]).
        exfalso.
        apply Hneqis2.
        exists (ac_write l v vol).
        auto.
        right. exists l, v. auto.
  - intro. apply so_vol. fix_po Hneqinit.
    + destruct H0 as (l & v & [ Heq | Hin ]).
      * exfalso.
        apply Hneqis1.
        exists (ac_write l v vol).
        auto.
      * right. exists l, v. auto.
    + destruct H3 as [ Hvolr | Hvolw ].
      * destruct Hvolr as (l & [ Heq | Hin ]).
        -- exfalso.
           apply Hneqis2.
           exists (ac_read l vol).
           auto.
        -- left. exists l. auto.
      * destruct Hvolw as (l & v & [ Heq | Hin ]).
        exfalso.
        apply Hneqis2.
        exists (ac_write l v vol).
        auto.
        right. exists l, v. auto.
Qed.

Lemma so_execed_tail :
  forall H h i1 i2,
    trco (H; h)
    -> exec H i2
    -> so (H; h) i1 i2
    -> so H i1 i2.
Proof.
  intros H h i1 i2 Htrco Hexeced2 Hso.
  assert (po (H; h) i1 i2) as Hpo by (inversion Hso; auto).
  thus (po H i1 i2) as Hpo' by po_execed_tail.
  clear Hpo.
  intros.
  eapply so_tail; eauto.
  - intro Heq.
    apply (spo_before H h i1 i2).
    intuition.
    apply exec_cons_incl; auto.
  - intro Heq.
    apply (spo_before H h i1 i2).
    intuition.
    apply exec_cons_incl; auto.
  - intros Heq.
    destruct Heq as (a & Heq).
    eapply trco_is_invert_npo.
    rewrite -> Heq in Htrco.
    eauto.
    apply po_cons_incl.
    eauto.
  - intros Heq.
    destruct (trco_exec_invert (H;h) i2 Htrco (exec_cons_incl H h i2 Hexeced2)) as (H1 & H2 & h' & a' & Hiseq & _ & Hi2is & _).
    destruct Heq as (a & Heq).
    eapply trco_is_invert_nis.
    rewrite Heq in Htrco.
    eauto.
    exists a'.
    destruct H2.
    + simpl in Hiseq.
      inversion Hiseq.
      auto.
    + rewrite <- app_comm_cons in Hiseq.
      inversion Hiseq.
      eapply in_or_app.
      right.
      right.
      auto.
  - intros (p & Hinit).
    rewrite Hinit in Htrco.
    eapply trco_init_invert_nexec; eauto.
Qed.

Lemma so_execed_truncate :
  forall H1 H2 i1 i2,
    trco (H1;; H2)
    -> exec H1 i2
    -> so (H1;; H2) i1 i2
    -> so H1 i1 i2.
Proof.
intros H1 H2 i1 i2 Htrco Hexec Hso.
induction H2 as [| h].
(* nil *)
simpl in Hso; auto.

(* cons *)
apply IHlist.
  simpl in Htrco.
  eapply trco_tail; eauto.

  simpl in Hso.
  eapply so_execed_tail; eauto.
  apply exec_app_incl; assumption.
Qed.  


Lemma so_to :
  forall H i i',
    trco H
    -> so H i i'
    -> exec H i'
    -> to H i i'.
Proof.
intros H i1 i2 Htrco Hso Hexec2.
so (exec_invert _ _ Hexec2) as (h & Hin & Hexecutes).
so (in_split _#3 Hin) as (H2 & H1 & Heq).
so (trco_executes_invert _#3 (trco_truncate _ _ (eqconv Heq Htrco)) Hexecutes) as (_ & _ & Hnexec & Hpriors).
unfold to.
exists H1, (nil; h;; H2).
autorewrite with canonlist.
repeat2 split; auto; [].
apply Hpriors; [].
apply (so_tail _ h); try discform; [prove_trco |].
apply (so_execed_truncate _ H2); subst H; auto; [].
eapply executes_exec; eauto; [].
left; reflexivity.
Qed.
                                                                                       
Lemma exec_decidable :
  forall H i,
    decidable (exec H i).
Proof.
intros H i.
so (present_decidable (ev_exec i) H) as [Hexec | Hnexec].
  left; apply exec_exec; auto; done.

  so (present_1_decidable _ _ (match_rf_r_decidable i) H) as [(iw & Hrf) | Hnrf].
    left; eapply exec_rf; eauto; done.

    right.
    intro Hexec.
    invert Hexec; [|].
      exact Hnexec.

      intros iw Hrf.
      destruct Hnrf; eauto; done.
Qed.

Lemma vo_to_or_so :
  forall H i i',
    trco H
    -> vo H i i'
    -> to H i i' \/ so H i i'.
Proof.
  intros H i i' Htrco Hvo.
  Hint Constructors so : truncate.

  destruct Hvo as [(Hvo & Hpo) | [Hrf | [ [(Hpush & Hpo) | (Hisvol1 & Hisvol2 & Hpo) ]| [ Hrelvo | [ Hacqvo | Hpushvo]]]]];
    try (right; intuition; done).
  - left. apply rf_to; auto; done.
  - right. unfold relvo in Hrelvo. intuition.
  - right. unfold acqvo in Hacqvo. intuition.
  - destruct Hpushvo as (? & ? & ? & (Hpush & Hto)).
    left.
    destruct (exec_decidable H i') as [ Hexec | Hnexec ].
    + eapply to_trans; eauto.
      destruct Hpush as [(Hso & Hpo) | (Hso1 & Hso & Hpo) ];
        [ apply (so_push Hpo) in Hso 
        | apply (so_vol Hpo Hso1) in Hso ];
        apply so_to in Hso; auto.
    + unfold to. unfold to in Hto.
      destruct Hto as (H1 & H2 & Heq & Hexeci & _ ).
      exists H1, H2.
      intuition.
      apply Hnexec.
      rewrite Heq.
      eauto using exec_app_incl.
Qed.

Lemma vo_to :
  forall H i i',
    trco H
    -> vo H i i' 
    -> exec H i'
    -> to H i i'.
Proof.
intros H i i' Htrco Hvo Hexec.
so (vo_to_or_so _#3 Htrco Hvo) as [| Hsvo]; auto; [].
eapply so_to; eauto; done.
Qed.

Lemma sop_to :
  forall H i i',
    trco H
    -> sop H i i'
    -> exec H i'
    -> to H i i'.
Proof.
intros H i i' Htrco Hsop Hexec.
pose proof (plus_plusi _#4 Hsop) as Hsop'; clear Hsop.
revert Hexec.
elim Hsop'; clear i i' Hsop'.
(* one *)
intros i i' Hso Hexec.
eapply so_to; eauto; done.

(* step *)
intros i1 i2 i3 Hso _ IH Hexec.
pose proof (IH Hexec) as Hto23.
apply (to_trans _ _ i2); auto.
eapply so_to; eauto.
apply (to_execed_fst H i2 i3); auto.
Qed.

Lemma vop_to_or_sop :
  forall H i i',
    trco H
    -> vop H i i'
    -> to H i i' \/ sop H i i'.
Proof.
intros H i i' Htrco Hvop.
so (plus_plusi _#4 Hvop) as Hvop'; clear Hvop.
induct Hvop'.

(* one *)
intros i1 i2 Hvo.
so (vo_to_or_so _#3 Htrco Hvo) as [Hto | Hpo].
  left.
  assumption.
  right. apply plus_one. auto.

(* step *)
intros i1 i2 i3 Hvo12 _ IH.
destruct IH as [Hto23 | Hpo23].
  left.
  eapply to_trans; eauto; [].
  apply vo_to; auto; [].
  eapply to_execed_fst; eauto; done.

  so (vo_to_or_so _#3 Htrco Hvo12) as [Hto12 | Hsvo12].
    left.
    so (exec_decidable H i3) as [Hexec3 | Hnexec3].
      eapply to_trans; eauto; [].
      eapply sop_to; eauto; done.

      apply to_from_nexec; auto; [].
      eapply to_execed_fst; eauto; done.
  
    right.
    exists i2; split; auto; [].
    apply plus_star; auto; done.
Qed.

Lemma vop_execed_fst_or_sop :
  forall H i i',
    trco H
    -> vop H i i'
    -> exec H i \/ sop H i i'.
Proof.
intros H i i' Htrco Hvop.
so (vop_to_or_sop _#3 Htrco Hvop) as [Hto | Hsop].
  left.
  eapply to_execed_fst; eauto; done.

  right; assumption.
Qed.

Lemma vo_to_or_sop :
  forall H i i',
    trco H
    -> vo H i i'
    -> to H i i' \/ sop H i i'.
Proof.
  intros H i i' Htrco Hvo.
  destruct (vo_to_or_so H i i'); auto.
  right.
  apply plus_one.
  auto.
Qed.

Lemma vop_to :
  forall H i i',
    trco H
    -> vop H i i'
    -> exec H i'
    -> to H i i'.
Proof.
intros H i1 i2 Htrco Hvop Hexec2.
so (plus_plusi _#4 Hvop) as Hvop'; clear Hvop.
revert Hexec2.
induct Hvop'.

(* one *)
intros i1 i2 Hvo Hexec2.
so (vo_to_or_so _#3 Htrco Hvo) as [Hto | Hsop].
  assumption.

  eapply so_to; eauto; done.

(* step *)
intros i1 i2 i3 Hvo12 _ IH Hexec3.
so (IH Hexec3) as Hto23.
eapply to_trans; eauto; [].
so (vo_to_or_so _#3 Htrco Hvo12) as [Hto12 | Hsvo12].
  assumption.

  eapply so_to; eauto; [].
  eapply to_execed_fst; eauto; done.
Qed.

Lemma vop_irreflex :
  forall H i,
    trco H
    -> ~ vop H i i.
Proof.
intros H i Htrco Hvop.
so (vop_execed_fst_or_sop _#3 Htrco Hvop) as [Hexec | Hsvop].
  destruct (to_irreflex H i).
  apply vop_to; auto; done.

  destruct (po_irreflex _ i Htrco).
  eapply sop_po; eauto; done.
Qed.