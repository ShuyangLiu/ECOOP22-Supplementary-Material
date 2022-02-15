  
Require Import Tactics.
Require Import Sequence.
Require Import Static.
Require Import Dynamic.
Require Import Hwf.
Require Import History.
Require Import Relation.


(* Tag Types *)

Lemma tgtp_sat_cons :
  forall H h U,
    tgtp_sat H U
    -> (forall b T T', h <> ev_edge b T T')
    -> tgtp_sat (H; h) U.
Proof.
intros H h U Hsat Hneq.
destruct Hsat as (Htgtpof & Hindecl & Hdeclin).
do2 2 split.
  assumption.

  intros T Hin.
  apply tag_declared_cons; auto; done.

  intros T Hdecl.
  apply Hdeclin.
  invert Hdecl; intros b T' Hin';
  (destruct Hin';
   [edestruct Hneq; eauto | eauto using tag_declared_1, tag_declared_2]).
Qed.


Lemma tgtp_sat_app :
  forall H H' U,
    tgtp_sat H U
    -> ~ H' {{ ev_edge be Te Te' | be Te Te' }}
    -> tgtp_sat (H;; H') U.
Proof.
intros H H' U Hsat Hneq.
induction H' as [| h].
  auto; done.

  simpl.
  apply tgtp_sat_cons; auto.
    apply IHH'.
    intros (b & T & T' & Hin).
    destruct Hneq.
    do 3 eexists; right; eassumption.

    intros b t T' Heq.
    destruct Hneq.
    do 3 eexists; left; eassumption.
Qed.


Lemma tgtp_sat_bind :
  forall H U b T T',
    tgtp_sat H U
    -> ~ In T U
    -> ~ In T' U
    -> T <> T'
    -> tgtp_sat (H; ev_edge b T T') (U; T; T').
Proof.
intros H U b T1 T2 Hsat Hnin Hnin' Hneq.
destruct Hsat as (HofU & Hindecl & Hdeclin).
do2 2 split.
  toshow (tgtpof (U; T1; T2)).
  apply NoDup_cons.
    toshow (~ (U; T1) {{ T2 }}).
    intro Hin.
    destruct Hin as [Heq | Hin].
      destruct Hneq; assumption.

      destruct Hnin'; assumption.

    toshow (NoDup (U; T1)).
    apply NoDup_cons; assumption.

  intros T Hin.
  have ((U; T1; T2) {{ T }}) as Hin.
  toshow (tag_declared (H; ev_edge b T1 T2) T).
  destruct Hin as [Heq | [Heq | Hin]].
    subst T.
    eapply tag_declared_2; left; reflexivity.

    subst T.
    eapply tag_declared_1; left; reflexivity.

    apply tag_declared_cons.
    apply Hindecl; assumption.

  intros T Hdecl.
  invert Hdecl; intros b' T' Hin.
    destruct Hin as [Heq | Hin].
      injection Heq; intros; subst T T'.
      right; left; reflexivity.

      right; right.
      apply Hdeclin.
      eapply tag_declared_1; exact Hin.

    destruct Hin as [Heq | Hin].
      injection Heq; intros; subst T T'.
      left; reflexivity.

      right; right.
      apply Hdeclin.
      eapply tag_declared_2; exact Hin.
Qed.


Lemma tgtp_sat_declared :
  forall H U T,
    tgtp_sat H U
    -> In T U
    -> tag_declared H T.
Proof.
intros H U T Hsat Hin.
destruct Hsat as (_ & Hindecl & _).
apply Hindecl; auto.
Qed.


Lemma tgof_declared :
  forall U H t,
    tgtp_sat H U
    -> tgof U nil t
    -> exists T, t = tg_lit T /\ tag_declared H T.
Proof.
intros U H t Hsat Hof.
invert Hof.
  intros i Hindex _.
  inversion Hindex.

  intros T Hin Heq.
  exists T.
  split; auto.
  eapply tgtp_sat_declared; eauto.
Qed.


Lemma fcof_declared :
  forall U H f,
    tgtp_sat H U
    -> fcof U nil f
    -> fence_declared H f.
Proof.
intros U H f Hsat Hof.
invert Hof; clear Hof.
  intros t Hof ?; subst f.
  pose proof (tgof_declared _#3 Hsat Hof) as (T' & Heq & Hdecl).
  subst t.
  apply fence_declared_tag; auto; done.

  intros b ?; subst f; apply fence_declared_pre; done.

  intros b ?; subst f; apply fence_declared_post.
Qed.


(* Location types *)

Lemma lctpof_ddistinct :
  forall P,
    lctpof P
    -> ddistinct P.
Proof.
intros P HofP.
induction HofP.
  apply ddistinct_nil.

  apply ddistinct_cons; auto.
Qed.


Lemma initialized_cons_incl :
  forall H h l,
    trco (H; h)
    -> initialized H l
    -> initialized (H; h) l.
Proof.
intros H h l Htrco Hinit.
destruct Hinit as (iw & ip & (v & Hisw) & Hisp & Hvvop & Hexec & Hallto).
exists iw, ip.
splitall; [| | | |].
  eexists; apply writes_cons_incl; eassumption.

  right; assumption.

  apply vvop_cons_incl; auto; done.

  apply exec_cons_incl; assumption.

  intros ir Hread.
  so (reads_cons_invert_is _#4 Hread) as [Hread' | (a & His)].
    apply to_cons_incl.
    apply Hallto; auto; done.

    subst h.
    apply to_cons_incl; [].
    apply to_from_nexec; auto; [].
    intro Hexec'.
    eapply trco_is_invert_nexec; eauto; done.
Qed.


Lemma lctp_sat_cons :
  forall H h U P P',
    trco (H; h)
    -> lctp_sat U P H P'
    -> (forall i l v, h <> ev_is i (ac_write l v))
    -> (forall i l v, h <> ev_is i (ac_rw l v))
    -> lctp_sat U P (H; h) P'.
Proof.
intros H h U P P' Htrco Hsat Hneqw Hneqrw.
destruct Hsat as (HofP & Hallinit & Hallof & Hisin).
do2 3 split; [| | |].
  assumption.

  intros l t Hin.
  apply initialized_cons_incl; auto; [].
  eapply Hallinit; eauto; done.

  intros l t i v Hin Hwrite.
  so (writes_cons_invert _#5 Hwrite) as [Hwrite' | [His | His]].
    eapply Hallof; eauto; done.

    subst; edestruct Hneqw; eauto; done.

    subst; edestruct Hneqrw; eauto; done.
  
  intros i l v Hwrite.
  so (writes_cons_invert _#5 Hwrite) as [Hwrite' | [His | His]].
    eapply Hisin; eauto; done.

    subst; edestruct Hneqw; eauto; done.

    subst; edestruct Hneqrw; eauto; done.
Qed.


Lemma lctp_sat_app :
  forall H H' U P P',
    trco (H;; H')
    -> lctp_sat U P H P'
    -> ~ H' {{ ev_is ie (ac_write le ve) | ie le ve }}
    -> ~ H' {{ ev_is ie (ac_rw le ve) | ie le ve }}
    -> lctp_sat U P (H;; H') P'.
Proof.
intros H H' U P P' Htrco Hsat Hneqw Hneqrw.
induction H' as [| h].
  auto; done.

  simpl.
  simpl in Htrco.
  #3 apply lctp_sat_cons; auto.
    apply IHH'; [prove_trco | |].
      intros (i & l & v & Hin).
      destruct Hneqw.
      do 3 eexists; right; eassumption.

      intros (i & l & v & Hin).
      destruct Hneqrw.
      do 3 eexists; right; eassumption.

    intros i l v Heq.
    destruct Hneqw.
    do 3 eexists; left; eassumption.

    intros i l v Heq.
    destruct Hneqrw.
    do 3 eexists; left; eassumption.
Qed.


Lemma lctp_sat_write :
  forall U P H P' a i l v t,
    (a = ac_write l v \/ a = ac_rw l v)
    -> trco (H; ev_is i a)
    -> lctp_sat U P H P'
    -> lookup l P' t
    -> value nil v
    -> tmof U P nil v t
    -> lctp_sat U P (H; ev_is i a) P'.
Proof.
intros U Pl H P a i l v t Heqa Htrco Hsat Hlookup Hvalue Hofv.
destruct Hsat as (HofP & Hallinit & Hallof & Hisin).
#4 splitall.
  assumption.

  intros l' t' HinP.
  apply initialized_cons_incl; eauto using Hallinit; done.

  intros l' t' i' v' Hin Hwrite.
  #2 so (writes_cons_invert _#5 Hwrite) as [Hwrite' | Heqs].
    eapply Hallof; eauto; done.

    assert (i = i' /\ l = l' /\ v = v') as (<- & <- & <-).
      destruct Heqa; subst a; destruct Heqs as [Heqs | Heqs]; try (discriminate Heqs); injection Heqs; auto; done.
    thus (lookup l P t') as Hlookup' by lookup_iff_in.
    thus (ddistinct P) as HdistP by lctpof_ddistinct.
    thus (t = t') by ddistinct_lookup_unique.
    subst t'.
    split; assumption.

  intros i' l' v' Hwrite.
  #2 so (writes_cons_invert _#5 Hwrite) as [Hwrite' | Heqs].
    eapply Hisin; eauto; done.

    assert (i = i' /\ l = l' /\ v = v') as (<- & <- & <-).
      destruct Heqa; subst a; destruct Heqs as [Heqs | Heqs]; try (discriminate Heqs); injection Heqs; auto; done.
    eapply lookup_indom; eauto; done.
Qed.


Lemma nois_map :
  forall (A : Type) (f : A -> event) (l : list A),
    (forall x, ~ exists i a, f x = ev_is i a)
    -> ~ (map f l) {{ ev_is i a | i a }}.
Proof.
intros A f l Hall.
intros (i & a & Hin).
pose proof (in_map_iff _#5 andel Hin) as (x & Heq & _).
have (f x = ev_is i a) as Heq.
destruct (Hall x); eauto.
Qed.


Lemma lctp_sat_ddistinct :
  forall U P H P',
    lctp_sat U P H P'
    -> ddistinct P'.
Proof.
intros U P H P' Hsat.
destruct Hsat as (HofP' & _).
apply lctpof_ddistinct; auto.
Qed.


(* Id types *)

Lemma idtpof_delete :
  forall I1 I2 i t p,
    idtpof (I1; (i, (t, p));; I2)
    -> idtpof (I1;; I2).
Proof.
intros I1 I2 i t p Hdist.
so (ddistinct_app _#4 Hdist) as (Hdist2 & Hdist1).
apply app_ddistinct; auto; [|].
  invert Hdist1; auto; done.

  intros; eapply ddistinct_app_disjoint; eauto; [].
  apply indom_miss; assumption.
Qed.  


Lemma idtp_sat_cons :
  forall U P H I h,
    idtp_sat U P H I
    -> ~ (exists i p, h = ev_init i p)
    -> ~ (exists i, h = ev_exec i)
    -> ~ (exists iw ir, h = ev_rf iw ir)
    -> idtp_sat U P (H; h) I.
Proof.
intros U P H I h Hsat Hneqinit Hneqexec Hneqrf.
destruct Hsat as (HofI & Hinis & Hinitin & Horder).
do2 3 split.
  assumption.

  intros i t p Hin.
  destruct (Hinis i t p Hin) as (a & Hinit & His & Hofa & Hnexec).
  exists a.
  do2 3 split.
    right; assumption.

    right; assumption.

    assumption.

    contradict Hnexec.
    eapply exec_tail; eauto; done.

  intros i p Hinit Hnexec.
  destruct Hinit as [Heq | Hinit].
    edestruct Hneqinit; eauto; done.

    eapply Hinitin; eauto; [].
    contradict Hnexec.
    apply exec_cons_incl; assumption.

  intros I1 I2 I3 i t i' t' p Heq.
  apply po_cons_incl; [].
  eapply Horder; eauto; done.
Qed.


Lemma idtp_sat_app :
  forall U P H I H',
    idtp_sat U P H I
    -> ~ H' {{ ev_init ie pe | ie pe }}
    -> ~ H' {{ ev_exec ie | ie }}
    -> ~ H' {{ ev_rf iw ir | iw ir }}
    -> idtp_sat U P (H;; H') I.
Proof.
intros U P H I H' Hsat Hninit Hnexec Hnrf.
induction H' as [| h].
  auto; done.

  simpl.
  apply idtp_sat_cons; auto; [| | |].
    apply IHH'; [| |].
      intros (i & p & Hin).
      destruct Hninit.
      do 2 eexists; right; eassumption.

      intros (i & Hin).
      destruct Hnexec.
      eexists; right; eassumption.

      intros (iw & ir & Hin).
      destruct Hnrf.
      repeat eexists; right; eassumption.
      
    intros (i & p & ->).
    destruct Hninit.
    do 2 eexists; left; reflexivity.

    intros (i & ->).
    destruct Hnexec.
    eexists; left; reflexivity.

    intros (iw & ir & ->).
    destruct Hnrf.
    repeat eexists; left; reflexivity.
Qed.


Lemma idtp_sat_bind :
  forall U P H I i a t p,
    trco H
    -> ~ H {{ ev_init i pe | pe }}
    -> idtp_sat U P H I
    -> acof U P nil a t
    -> idtp_sat U P (H; ev_init i p; ev_is i a) (I; (i, (t, p))).
Proof.
intros U P H I i a t p Htrco Hfresh Hsat Hofa.
destruct Hsat as (HofI & Hinis & Hinitin & Horder).
assert (~ indom i I) as Hnindom.
  intro Hindom.
  so (indom_lookup _#4 Hindom) as ((t', p') & Hlookup).
  thus (In (i, (t', p')) I) as Hin by lookup_iff_in.
  so (Hinis i t' p' Hin) as (_ & Hinit & _).
  destruct Hfresh.
  eexists; eauto; done.
do2 3 split.
  toshow (idtpof (I; (i, (t, p)))).
  apply ddistinct_cons; assumption.

  intros i' t' p' Hin.
  destruct Hin as [Heq | Hin].
    have ((i, (t, p)) = (i', (t', p'))) as Heq.
    injection Heq; intros; subst i' t' p'.
    exists a.
    do2 3 split.
      right; left; reflexivity.

      left; reflexivity.

      assumption.

      intro Hin.
      destruct Hfresh.
      apply exec_inited; auto; [].
      eapply exec_tail; [.. | eapply exec_tail]; eauto; discform.

    so (Hinis _#3 Hin) as (a' & Hinit & His & Hofa' & Hnexec).
    exists a'.
    do2 3 split.
      right; right; assumption.

      right; right; assumption.

      assumption.

      contradict Hnexec.
      eapply exec_tail; [.. | eapply exec_tail]; eauto; discform.

  intros i' p' Hinit Hnexec.
  destruct Hinit as [Heq | [Heq | Hinit]].
    discriminate.

    injection Heq; intros; subst i' p'.
    apply indom_hit; done.

    apply indom_miss; [].
    eapply Hinitin; eauto; [].
    contradict Hnexec.
    apply exec_cons_incl; apply exec_cons_incl; assumption.

  intros I1 I2 I3 i1 t1 i2 t2 p' HeqI.
  so (app_eq_cons _#5 HeqI) as [(I3' & HeqI3 & HeqI') | (HeqI3 & HeqI')].
    apply po_cons_incl; [].
    apply po_cons_incl; [].
    eapply (Horder I1 I2 I3'); eauto; done.

    subst I3.
    injection HeqI'; intros HeqI'' ? ? ?.
    subst p' t2 i2.
    exploit (Hinis i1 t1 p) as (_ & Hinit & _); [|].
      subst I.
      apply in_or_app; right; left; reflexivity.

      so (in_split _#3 Hinit) as (H2 & H1 & HeqH).
      subst H.
      exists H1, H2, (nil; ev_is i a), p.
      reflexivity.
Qed.


Lemma idtp_sat_exec :
  forall U P H h I1 I2 i t p,
    executes h i
    -> idtp_sat U P H (I1; (i, (t, p));; I2)
    -> idtp_sat U P (H; h) (I1;; I2).
Proof.
intros U P H h I1 I2 i t p Hexecutes Hsat.
destruct Hsat as (HofI & Hinis & Hinitin & Horder).
do2 3 split.
  eapply idtpof_delete; eauto; done.

  intros i' t' p' Hin.
  exploit (Hinis i' t' p') as (a & Hinit & His & Hofa & Hnexec); [|].
    so (in_app_or _#4 Hin) as [Hin' | Hin'];
    apply in_or_app; [left | right; right]; assumption.
  exists a.
  do2 3 split; try right; auto; [].
  assert (i <> i') as Hneq.
    intro.
    subst i'.
    thus (indom i (I1;; I2)) as Hindom by indom_iff_in.
    exfalso.
    exact (ddistinct_middle _#6 HofI Hindom).
  contradict Hnexec.
  so (exec_cons_invert _#3 Hnexec) as [Hexecutes' | ?]; auto; [].
  so (executes_fun_1 _#3 Hexecutes Hexecutes') as Heq.
  destruct Hneq; auto; done.

  intros i' p' Hinit Hnexec.
  discriminate_in Hinit; intro Hinit; [|].
    discriminate_executes Hexecutes; done.
  exploit (Hinitin i' p') as Hindom; auto; [|].
    contradict Hnexec.
    apply exec_cons_incl; assumption.
  so (indom_app _#5 ander Hindom) as [Hindom' | Hindom'].
    apply indom_app; left; assumption.

    invert Hindom'; [|].
      intro.
      subst i'.
      destruct Hnexec.
      eapply executes_exec; eauto; [].
      left; reflexivity.

      intro; apply indom_app; right; assumption.

  intros I3 I4 I5 i1 t1 i2 t2 p' Heq.
  apply po_cons_incl.
  so (app_eq_app2 _#5 Heq) as [(x & I6 & HeqI2 & Heq') | (I7 & HeqI5 & HeqI1)].
    injection Heq'; intros HeqI16 ->.
    so (app_eq_app2 _#5 HeqI16) as [(x & I8 & HeqI6 & HeqI16') | (I9 & HeqI96 & HeqI1)].
      injection HeqI16'; intros HeqI17 ->.
      apply (Horder (I1; (i, (t, p));; I8) I4 I5 i1 t1 i2 t2 p'); [].
      rewrite -> HeqI2.
      rewrite -> HeqI6.
      repeat (progress (rewrite <- ?app_assoc, ?app_comm_cons)).
      reflexivity.

      apply (Horder I3 (I9; (i, (t, p));; I6) I5 i1 t1 i2 t2 p'); [].
      rewrite -> HeqI1.
      rewrite -> HeqI2.
      repeat (progress (rewrite <- ?app_assoc, ?app_comm_cons)).
      reflexivity.

    apply (Horder I3 I4 (I7; (i, (t, p));; I2) i1 t1 i2 t2 p'); [].
    rewrite -> HeqI1.
    repeat (progress (rewrite <- ?app_assoc, ?app_comm_cons)).
    reflexivity.
Qed.


Lemma idtpof_ddistinct :
  forall I,
    idtpof I
    -> ddistinct I.
Proof.
auto.
Qed.


Lemma idtp_sat_ddistinct :
  forall U P H I,
    idtp_sat U P H I
    -> ddistinct I.
Proof.
intros U P H I Hsat.
destruct Hsat as (HofI & _).
apply idtpof_ddistinct; auto.
Qed.


Lemma init_idtp_sat_in :
  forall U P H I i p,
    trco H
    -> idtp_sat U P H I
    -> H {{ ev_init i p }}
    -> ~ exec H i
    -> exists t, In (i, (t, p)) I.
Proof.
intros U P H I i p Htrco Hsat Hinit Hnexec.
destruct Hsat as (_ & Hininit & Hinitin & _).
thus (indom i I) as Hindom by Hinitin.
so (indom_iff_in _#4 andel Hindom) as ((t, p') & Hin).
so (Hininit _#3 Hin) as (_ & Hinit' & _).
thus (p = p') by init_unique.
subst p'.
exists t.
assumption.
Qed.
