Require Import Tactics.
Require Import Relation.
Require Import Sequence.
Require Import Dynamic.
Require Import Hwf.
Require Import Match.
Require Import TermDec.
Require Subst.


Lemma trco_tail :
  forall H h,
    trco (H; h) -> trco H.
Proof.
intros H h Htrco.
inversion Htrco; auto.
Qed.


Lemma trco_truncate :
  forall H H',
    trco (H;; H') -> trco H.
Proof.
intros; induction H'; eauto using trco_tail.
Qed.


Ltac prove_trco' :=
  first [
        assumption
        |
         (lazymatch goal with
          | H : trco (_; _) |- trco _ => so (trco_tail _ _ H); clear H; prove_trco'
          | H : trco (_;; _) |- trco _ => so (trco_truncate _ _ H); clear H; prove_trco'
          end)
        ].

Ltac prove_trco := subst; prove_trco'.


Definition executes h i := (h = ev_exec i) \/ (exists iw, h = ev_rf iw i).

Hint Unfold executes.

Ltac discriminate_executes Hexecutes :=
  let i := fresh "i" in
  let Heq := fresh "Heq"
  in
    destruct Hexecutes as [Heq | (i, Heq)];
    [ try (subst; discriminate); revert Heq
    | try (subst; discriminate); revert i Heq].


Ltac discform :=
  repeat (lazymatch goal with
          | Hex : executes ?H ?i |- _ => destruct Hex as [-> | (? & ->)]
          end);
  let Hyp := fresh
  in
    intro Hyp; destruct_all Hyp; try (discriminate Hyp); discform.


Definition inited (H : history) (i : identifier) : Prop :=
  H {{ ev_init i p | p }}.

Lemma pop_po :
  forall H i i',
    pop H i i'
    -> po H i i'.
Proof.
  intros ? ? ? (Hpo & ? & ?).
  auto.
Qed.

Hint Resolve pop_po.

(* Monotonicity *)

Lemma cons_incl_imp_app_incl1 :
  forall (S T : Set) (R : list S -> T -> Prop),
    (forall L x i, R L i -> R (L; x) i)
    -> (forall L L' i, R L i -> R (L;; L') i).
Proof.
intros S T R Hcons L L' i HRL.
induction L'.
(* nil *)
exact HRL.

(* cons *)
simpl.
apply Hcons.
exact IHL'.
Qed.


Lemma cons_incl_imp_app_incl2 :
  forall (S T : Set) (R : list S -> T -> T -> Prop),
    (forall L x i i', R L i i' -> R (L; x) i i')
    -> (forall L L' i i', R L i i' -> R (L;; L') i i').
Proof.
intros S T R Hcons L L' i i' HRL.
induction L'.
(* nil *)
exact HRL.

(* cons *)
simpl.
apply Hcons.
exact IHL'.
Qed.


Lemma reads_cons_incl :
  forall H h i l,
    reads H i l
    -> reads (H; h) i l.
Proof.
intros H h i l Hreads.
invert Hreads.

(* read *)
intros m His.
eapply reads_read; [].
right; eassumption.

(* rw *)
intros v His.
eapply reads_rw; eauto; [].
right; eassumption.
Qed.


Lemma reads_app_incl :
  forall H H' i l,
    reads H i l
    -> reads (H;; H') i l.
Proof.
intros H H' i l Hreads.
induction H'.
(* nil *)
exact Hreads.

(* cons *)
simpl.
apply reads_cons_incl; auto; done.
Qed.


Lemma writes_cons_incl :
  forall H h i l v,
    writes H i l v
    -> writes (H; h) i l v.
Proof.
intros H h i l v Hwrites.
invert Hwrites.

(* write *)
intros m His.
eapply writes_write; [].
right; eassumption.

(* rw *)
intros His.
eapply writes_rw; eauto; [].
right; eassumption.
Qed.


Lemma writes_app_incl :
  forall H H' i l v,
    writes H i l v
    -> writes (H;; H') i l v.
Proof.
intros H H' i l v Hwrites.
induction H'.

(* nil *)
assumption.

(* cons *)
simpl.
apply writes_cons_incl; auto; done.
Qed.

Lemma writesto_cons_incl :
  forall H h i l,
    writesto H i l
    -> writesto (H; h) i l.
Proof.
intros H h i l Hwritesto.
destruct Hwritesto as (v & Hwrites).
exists v.
eapply writes_cons_incl.
eauto.
Qed.

Lemma writesto_app_incl :
  forall H H' i l,
    writesto H i l
    -> writesto (H;; H') i l.
Proof.
intros H H' i l Hwritesto.
destruct Hwritesto; eexists; apply writes_app_incl; eauto.
Qed.


Lemma po_cons_incl :
  forall H h i i',
    po H i i'
    -> po (H; h) i i'.
Proof.
intros H h i i' Hpo.
destruct Hpo as (H1 & H2 & H3 & p & Heq).
exists H1, H2, (H3; h), p.
simpl; f_equal; auto.
Qed.

Lemma po_app_incl :
  forall H H' i i',
    po H i i'
    -> po (H;; H') i i'.
Proof.
exact (cons_incl_imp_app_incl2 _#3 po_cons_incl).
Qed.

Lemma isopr_cons_incl : 
  forall H h i,
    isopr H i
    -> isopr (H; h) i.
Proof.
  intros H h i (m & (l & Hread) & Hopm).
  exists m.
  split; auto.
  exists l.
  right; auto.
Qed.

Lemma isopw_cons_incl :
  forall H h i,
    isopw H i
    -> isopw (H; h) i.
Proof.
  intros H h i (m & (l & v & Hwrite) & Hopm).
  exists m.
  split; auto.
  exists l, v.
  right; auto.
Qed.

Lemma isop_cons_incl : 
  forall H h i,
    isop H i
    -> isop (H; h) i.
Proof.
  intros H h i Hisop.
  destruct Hisop;
    [ left | right ];
    auto using isopr_cons_incl, isopw_cons_incl.
Qed.

Lemma pop_cons_incl :
  forall H h i i',
    pop H i i'
    -> pop (H; h) i i'.
Proof.
  intros H h i i' (Hpo & Hisopl & Hisopr).
  split; [ |split];
    auto using po_cons_incl, isop_cons_incl.
Qed.

Lemma pop_app_incl :
  forall H H' i i',
    pop H i i'
    -> pop (H;; H') i i'.
Proof.
exact (cons_incl_imp_app_incl2 _#3 pop_cons_incl).
Qed.

Lemma poq_cons_incl :
  forall H h i i',
    poq H i i'
    -> poq (H; h) i i'.
Proof.
intros H h i i' Hpoq.
destruct Hpoq as [Heq | Hpo].
  subst; left; reflexivity.

  right; apply po_cons_incl; assumption.
Qed.


Lemma poq_app_incl :
  forall H H' i i',
    poq H i i'
    -> poq (H;; H') i i'.
Proof.
exact (cons_incl_imp_app_incl2 _#3 poq_cons_incl).
Qed.


Lemma exec_cons_incl :
  forall H h i,
    exec H i
    -> exec (H; h) i.
Proof.
intros H h i Hexec.
invert Hexec; [|].
  intro Hexec'.
  apply exec_exec.
  right; assumption.

  intros iw Hrf.
  eapply exec_rf.
  right; eassumption.
Qed.


Lemma exec_app_incl :
  forall H H' i,
    exec H i
    -> exec (H;; H') i.
Proof.
exact (cons_incl_imp_app_incl1 _#3 exec_cons_incl).
Qed.


Lemma to_cons_incl :
  forall H h i i',
    to H i i'
    -> to (H; h) i i'.
Proof.
intros H h i i' Hto.
destruct Hto as (H1 & H2 & Heq & Hexec & Hnexec).
exists H1, (H2; h).
simpl.
repeat2 split; f_equal; auto; done.
Qed.


Lemma to_app_incl :
  forall H H' i i',
    to H i i'
    -> to (H;; H') i i'.
Proof.
exact (cons_incl_imp_app_incl2 _#3 to_cons_incl).
Qed.

Lemma rf_cons_incl :
  forall H h i i',
    rf H i i'
    -> rf (H; h) i i'.
Proof.
intros ? ? ? ? Hrf.
right; auto; done.
Qed.

Lemma isvolr_cons_incl :
  forall H h i,
    isvolr H i
    -> isvolr (H;h) i.
Proof.
  intros ? ? ? (l & Hisvolr).
  exists l.
  right. auto.
Qed.

Lemma isvolw_cons_incl :
  forall H h i,
    isvolw H i
    -> isvolw (H;h) i.
Proof.
  intros ? ? ? (l & v & Hisvolw).
  exists l, v.
  right. auto.
Qed.

Lemma isvol_cons_incl :
  forall H h i,
    isvol H i
    -> isvol (H;h) i.
Proof.
  intros ? ? ? Hisvol.
  destruct Hisvol as [Hisvolr | Hisvolw].
  - left. auto using isvolr_cons_incl.
  - right. auto using isvolw_cons_incl.
Qed.

Lemma isrelw_cons_incl :
  forall H h i,
    isrelw H i
    -> isrelw (H;h) i.
Proof.
  intros ? ? ? [(l & v & Hw) | Hvol].
  - left. exists l, v. right. auto.
  - right. auto using isvolw_cons_incl.
Qed.

Lemma isacqr_cons_incl :
  forall H h i,
    isacqr H i
    -> isacqr (H;h) i.
Proof.
  intros ? ? ? [(l & Hr) | Hvol].
  - left. exists l. right. auto.
  - right. auto using isvolr_cons_incl.
Qed.

Lemma relvo_cons_incl :
  forall H h i i',
    relvo H i i'
    -> relvo (H;h) i i'.
Proof.
  intros ? ? ? ? (Hisrelw & Hpo).
  split; auto using isrelw_cons_incl, po_cons_incl.
Qed.

Lemma acqvo_cons_incl :
  forall H h i i',
    acqvo H i i'
    -> acqvo (H;h) i i'.
Proof.
  intros ? ? ? ? (Hisacqr & Hpo).
  split; auto using isacqr_cons_incl, po_cons_incl.
Qed.

Lemma volwpo_cons_incl :
  forall H h i i',
    volwpo H i i'
    -> volwpo (H;h) i i'.
Proof.
  intros ? ? ? ? (Hisvolw & Hpo).
  split; auto using isvolw_cons_incl, po_cons_incl.
Qed.

Lemma volrpo_cons_incl :
  forall H h i i',
    volrpo H i i'
    -> volrpo (H;h) i i'.
Proof.
  intros ? ? ? ? (Hisvolr & Hpo).
  split; auto using isvolr_cons_incl, po_cons_incl.
Qed.


Lemma volpo_cons_incl :
  forall H h i i',
    volpo H i i'
    -> volpo (H;h) i i'.
Proof.
  intros ? ? ? ? (Hisvol1 & Hisvol2 & Hpo).
  split; auto using isvol_cons_incl, po_cons_incl.
Qed.

Lemma svo_cons_incl :
  forall H h i i',
    svo H i i'
    -> svo (H;h) i i'.
Proof.
  intros ? ? ? ? (Hvo & Hpo).
  split; [right|]; auto using po_cons_incl.
Qed.

Lemma push_cons_incl :
  forall H h i i',
    push H i i'
    -> push (H;h) i i'.
Proof.
  intros ? ? ? ? [(Hpush & Hpo) | Hvolpo ];
    [ disj 0 | disj 1 ];
    auto using volpo_cons_incl.

  split; [right|]; auto using po_cons_incl.
Qed.

Lemma vo_cons_incl :
  forall H h i i',
    vo H i i'
    -> vo (H; h) i i'.
Proof.
intros H h i i' Hvo.
destruct Hvo as [Hsvo | [Hrf | [ Hpush | [ Hrelvo | [ Hacqvo | Hcross]]]]].
- disj 0. auto using svo_cons_incl.
- disj 1; auto using rf_cons_incl.
- disj 2. auto using push_cons_incl.
- disj 3. auto using relvo_cons_incl.
- disj 4. auto using acqvo_cons_incl.
- disj 5. 
  destruct Hcross as (i'' & i''' & Hl & Hr & Hto).
  exists i'', i'''.
  split; [|split]; auto using push_cons_incl.
  apply to_cons_incl; auto.
Qed.

Lemma vo_app_incl :
  forall H H' i i',
    vo H i i'
    -> vo (H;; H') i i'.
Proof.
exact (cons_incl_imp_app_incl2 _#3 vo_cons_incl).
Qed.


Lemma vop_cons_incl :
  forall H h i i',
    vop H i i'
    -> vop (H; h) i i'.
Proof.
intros H h i i' Hvvop.
apply (plus_mono _  (vo H)); auto; [].
auto using vo_cons_incl.
Qed.


Lemma vos_cons_incl :
  forall H h i i',
    vos H i i'
    -> vos (H; h) i i'.
Proof.
intros H h i i' Hvvos.
apply (star_mono _  (vo H)); auto; [].
auto using vo_cons_incl.
Qed.


Lemma vop_app_incl :
  forall H H' i i',
    vop H i i'
    -> vop (H;; H') i i'.
Proof.
intros H H' i i' Hvvop.
apply (plus_mono _  (vo H)); auto; [].
auto using vo_app_incl.
Qed.


Lemma vos_app_incl :
  forall H H' i i',
    vos H i i'
    -> vos (H;; H') i i'.
Proof.
intros H H' i i' Hvvos.
apply (star_mono _  (vo H)); auto; [].
auto using vo_app_incl.
Qed.

Lemma rwf_cons_incl :
  forall H h i i',
    rwf H i i'
    -> rwf (H; h) i i'.
Proof.
intros H h i i' Hrwf.
destruct Hrwf as (Hrf & (l & v & His)).
split.
  right; assumption.

  repeat eexists; right; eassumption.
Qed.


Lemma rwfs_cons_incl :
  forall H h i i',
    rwfs H i i'
    -> rwfs (H; h) i i'.
Proof.
intros H h i i' Hrwfs.
apply (star_mono _ (rwf H)); auto; [].
auto using rwf_cons_incl.
Qed.  


Lemma rwfs_app_incl :
  forall H H' i i',
    rwfs H i i'
    -> rwfs (H;; H') i i'.
Proof.
exact (cons_incl_imp_app_incl2 _#3 rwfs_cons_incl).
Qed.


Lemma isr_cons_incl :
  forall H h i,
    isr H i
    -> isr (H; h) i.
Proof.
intros H h i Hisr.
destruct Hisr as (l & His).
exists l.
apply reads_cons_incl; assumption.
Qed.

Lemma isr_app_incl :
  forall H H' i,
    isr H i
    -> isr (H;; H') i.
Proof.
intros H H' i Hisr.
destruct Hisr as (l & His).
exists l.
apply reads_app_incl; assumption.
Qed.

Lemma isrw_cons_incl :
  forall H h i,
    isrw H i
    -> isrw (H; h) i.
Proof.
intros H h i Hisrw.
destruct Hisrw as (l & v & His).
exists l, v.
right. auto.
Qed.

Lemma isw_cons_incl :
  forall H h i,
    isw H i
    -> isw (H; h) i.
Proof.
intros H h i Hisw.
destruct Hisw as (l & v & His).
exists l, v.
auto using writes_cons_incl.
Qed.

Lemma vt_cons_incl :
  forall H h i i',
    vt H i i'
    -> vt (H; h) i i'.
Proof.
intros H h i i' Hvt. 
destruct Hvt as (i'' & Hvvop & Hxos).
exists i''.
split.
auto using vo_cons_incl.
apply vos_cons_incl. auto.
Qed.

Lemma hb_cons_incl:
  forall H h i i',
    vopo H i i'
    -> vopo (H;h) i i'.
Proof.
intros H h i i' Hhb.
destruct Hhb as [Hvvop | Hpo].
left. apply vop_cons_incl. auto.
right. apply po_cons_incl. auto.
Qed.

Lemma co_cons_incl :
  forall H h i i',
    co H i i'
    -> co (H; h) i i'.
Proof.
intros H h i i' Hco.
remember (H; h) as H' eqn:HeqH'.
revert HeqH'.
induction Hco;
intros;
[ eapply co_ww
| eapply co_wr
| eapply co_rw
| eapply co_rr
| eapply co_atm_total; destruct H0
| eapply co_atm_after];
subst H';
try (eauto using hb_cons_incl,
       rf_cons_incl,
       writesto_cons_incl,
       reads_cons_incl,
       po_cons_incl,
       isrw_cons_incl,
       to_cons_incl,
       rwf_cons_incl,
       isw_cons_incl).
Qed.

Lemma co_app_incl :
  forall H H' i i',
    co H i i'
    -> co (H;; H') i i'.
Proof.
exact (cons_incl_imp_app_incl2 _#3 co_cons_incl).
Qed.


Lemma cos_cons_incl :
  forall H h i i',
    cos H i i'
    -> cos (H; h) i i'.
Proof.
intros H h i i' Hcos.
apply (star_mono _ (co H)); auto; [].
auto using co_cons_incl.
Qed.


Lemma cos_app_incl :
  forall H H' i i',
    cos H i i'
    -> cos (H;; H') i i'.
Proof.
intros H1 H2 i i' Hcos.
induction H2 as [| h H2 IH].

(* nil *)
assumption.

(* cons *)
autorewrite with canonlist in *.
apply cos_cons_incl; auto; done.
Qed.


Lemma cop_cons_incl :
  forall H h i i',
    cop H i i'
    -> cop (H; h) i i'.
Proof.
intros H h i i' Hcos.
apply (plus_mono _ (co H)); auto; [].
auto using co_cons_incl.
Qed.


Lemma cop_app_incl :
  forall H H' i i',
    cop H i i'
    -> cop (H;; H') i i'.
Proof.
intros H1 H2 i i' Hcop.
induction H2 as [| h H2 IH].

(* nil *)
assumption.

(* cons *)
autorewrite with canonlist in *.
apply cop_cons_incl; auto; done.
Qed.


(* Init *)

Lemma init_twice :
  forall H1 H2 H3 i p p',
    ~ trco (H1; ev_init i p;; H2; ev_init i p';; H3).
Proof.
intros H1 H2 H3 i p p' Htrco.
so (trco_truncate _ _ Htrco) as Htrco'.
invert Htrco'; intros _ Hninit.
destruct Hninit.
eexists.
apply in_or_app; right; left; eauto.
Qed.


Lemma init_twice' :
  forall H1 H2 i p p',
    trco (H1;; H2)
    -> H1 {{ ev_init i p }}
    -> H2 {{ ev_init i p' }}
    -> False.
Proof.
intros H1 H2 i p p' Htrco Hinit1 Hinit2.
so (in_split _#3 Hinit1) as (H1b & H1a & HeqH1).
so (in_split _#3 Hinit2) as (H2b & H2a & HeqH2).
subst H1 H2.
autorewrite with canonlist in Htrco.
edestruct (init_twice H1a (H1b;; H2a) H2b); eauto.
autorewrite with canonlist.
eassumption.
Qed.


Lemma init_unique :
  forall H i p p',
    trco H
    -> H {{ ev_init i p}}
    -> H {{ ev_init i p' }}
    -> p = p'.
Proof.
intros H i p p' Htrco Hin Hin'.
so (in_split_2 _#4 Hin Hin') as [(H3 & H2 & H1 & Heq) | [(Heq & ?) | (H3 & H2 & H1 & Heq)]].
  exfalso.
  subst H.
  eapply init_twice; eauto; done.

  injection Heq; auto; done.

  exfalso.
  subst H.
  eapply init_twice; eauto; done.
Qed.


Lemma init_split_fun :
  forall H i H1 H2 H1' H2' p p',
    trco H
    -> H = H1; ev_init i p;; H2
    -> H = H1'; ev_init i p';; H2'
    -> H1 = H1' /\ H2 = H2' /\ p = p'.
Proof.
intros H i H1 H2 H1' H2' p p' Htrco Heq Heq'.
assert (H1; ev_init i p;; H2 = H1'; ev_init i p';; H2') as Heqapp by (subst H; auto).
so (app_eq_app _#5 Heqapp) as [(h & H' & Heq2 & Heq1) | [(Heq2 & Heq1) | (h & H' & Heq2 & Heq1)]].
  injection Heq1; intros; subst h.
  rewrite -> Heq2 in Heq.
  rewrite <- app_assoc in Heq.
  rewrite <- app_comm_cons in Heq.
  rewrite -> Heq in Htrco.
  edestruct init_twice; eauto; done.

  injection Heq1; auto; done.

  injection Heq1; intros; subst h.
  rewrite <- Heq2 in Heq'.
  rewrite <- app_assoc in Heq'.
  rewrite <- app_comm_cons in Heq'.
  rewrite -> Heq' in Htrco.
  edestruct init_twice; eauto; done.
Qed.


Lemma init_tail :
  forall H h i p,
    ~ (exists i' p', h = ev_init i' p')
    -> (H; h) {{ ev_init i p }}
    -> H {{ ev_init i p }}.
Proof.
intros H h i p Hninit Hinit.
destruct Hinit as [Heq | Hinit].
  destruct Hninit.
  eauto; done.

  assumption.
Qed.


(* Is *)

Lemma is_isac :
  forall H i a,
    trco H
    -> H {{ ev_is i a }}
    -> isac a.
Proof.
intros H i a Htrco His.
so (in_split _#3 His) as (H2 & H1 & ->).
invert (trco_truncate _ _ Htrco).
intros; assumption.
Qed.


Lemma is_closed :
  forall H i a,
    trco H
    -> H {{ ev_is i a }}
    -> Subst.closed a.
Proof.
intros H i a Htrco His.
so (in_split _#3 His) as (H2 & H1 & ->).
invert (trco_truncate _ _ Htrco).
auto.
Qed.


Lemma is_twice :
  forall H1 H2 H3 i a a',
    ~ trco (H1; ev_is i a;; H2; ev_is i a';; H3).
Proof.
intros H1 H2 H3 i a a' Htrco.
so (trco_truncate _ _ Htrco) as Htrco12e.
invert Htrco12e; intros Htrco12 _ _ (p & H12 & Heq12e).
symmetry in Heq12e.
exploit (first_neq_middle_invert _#6 Heq12e) as (H2' & HeqH2 & ?); [|].
  discriminate.
rewrite -> HeqH2 in Htrco12.
rewrite <- app_comm_cons in Htrco12.
invert Htrco12; intros _ Hninit.
destruct Hninit.
so (trco_truncate _ _ (trco_tail _ _ Htrco12)) as Htrco1e.
invert Htrco1e; intros _ _ _ (p' & H1' & HeqH1).
exists p'.
rewrite -> HeqH1.
apply in_or_app; right; right; left; reflexivity.
Qed.


Lemma is_fun :
  forall H i a a',
    trco H
    -> H {{ ev_is i a }}
    -> H {{ ev_is i a' }}
    -> a = a'.
Proof.
intros H i a a' Htrco Hin1 Hin2.
so (in_split_2 _#4 Hin2 Hin1) as [(H3 & H2 & H1 & Heq) | [ (Heq & _) | (H3 & H2 & H1 & Heq)]].
  exfalso.
  subst H.
  eapply is_twice; eauto; done.

  injection Heq; auto; done.

  exfalso.
  subst H.
  eapply is_twice; eauto; done.
Qed.


Lemma reads_fun :
  forall H i l l',
    trco H
    -> reads H i l
    -> reads H i l'
    -> l = l'.
Proof.
  intros H i l l' Htrco Hreads Hreads'.
  invert Hreads; invert Hreads';
    [ intros m His m' His'
    | intros v His m His'
    | intros m His v His'
    | intros v His v' His' ];
    so (is_fun _#4 Htrco His His') as Heq;
    try (injection Heq; auto; done);
    try (discriminate).
Qed.


Lemma read_fun_mode :
  forall H i l l' m m',
    trco H
    -> H {{ ev_is i (ac_read l m) }}
    -> H {{ ev_is i (ac_read l' m') }}
    -> m = m'.
Proof.
intros H i l l' m m' Htrco His His'.
invert (is_fun H i (ac_read l m) (ac_read l' m') Htrco His His'); eauto.
Qed.

Lemma writes_fun :
  forall H i l l' v v',
    trco H
    -> writes H i l v
    -> writes H i l' v'
    -> l = l' /\ v = v'.
Proof.
intros H i l l' v v' Htrco Hwrites Hwrites'.
invert Hwrites; invert Hwrites';
  [ intros m His m' His'
  | intros His m His'
  | intros m His His'
  | intros His His' ];
  so (is_fun _#4 Htrco His His') as Heq; simplify_eq Heq; auto.
Qed.

Lemma write_fun_mode :
  forall H i l l' v v' m m',
    trco H
    -> H {{ ev_is i (ac_write l v m) }}
    -> H {{ ev_is i (ac_write l' v' m') }}
    -> m = m'.
Proof.
intros H i l l' v v' m m' Htrco His His'.
invert (is_fun H i (ac_write l v m) (ac_write l' v' m') Htrco His His'); eauto.
Qed.

Lemma writes_fun_val :
  forall H i l v v',
    trco H
    -> writes H i l v
    -> writes H i l v'
    -> v = v'.
Proof.
intros H i l v v' Htrco Hwrites Hwrites'.
so (writes_fun _#6 Htrco Hwrites Hwrites') as (_ & ?).
assumption.
Qed.


Lemma writesto_fun :
  forall H i l l',
    trco H
    -> writesto H i l
    -> writesto H i l'
    -> l = l'.
Proof.
intros H i l l' Htrco (v & Hwrites) (v' & Hwrites').
so (writes_fun _#6 Htrco Hwrites Hwrites') as (? & _).
assumption.
Qed.


Lemma reads_writes_fun :
  forall H i l l' v,
    trco H
    -> reads H i l
    -> writes H i l' v
    -> l = l'.
Proof.
intros H i l l' v Htrco Hread Hwrite.
invert Hwrite; invert Hread;
  [ intros ? His ? His'
  | intros ? His ? His'
  | intros ? His His'
  | intros ? His His' ];
  so (is_fun _#4 Htrco His His') as Heq;
  try (discriminate Heq).
injection Heq; auto; done.
Qed.

Lemma reads_writesto_fun :
  forall H i l l',
    trco H
    -> reads H i l
    -> writesto H i l'
    -> l = l'.
Proof.
intros H i l l' Htrco Hread (? & Hwrite).
eapply reads_writes_fun; eauto.
Qed.


Lemma is_inited :
  forall H i a,
    trco H
    -> H {{ ev_is i a }}
    -> H {{ ev_init i pe | pe }}.
Proof.
intros H i a Htrco Hin.
so (in_split _#3 Hin) as (H2 & H1 & Heq).
subst H.
so (trco_truncate _ _ Htrco) as Htrco1e.
invert Htrco1e.
intros _ _ _ (p & H1' & HeqH1).
rewrite -> HeqH1.
exists p.
apply in_or_app; right; right; left; reflexivity.
Qed.


Lemma reads_inited :
  forall H i l,
    trco H
    -> reads H i l
    -> H {{ ev_init i pe | pe }}.
Proof.
intros H i l Htrco Hreads.
invert Hreads; intro;
eapply is_inited; eauto.
Qed.


Lemma writes_inited :
  forall H i l v,
    trco H
    -> writes H i l v
    -> inited H i.
Proof.
intros H i l v Htrco Hwrites.
invert Hwrites; intro; eapply is_inited; eauto; done.
Qed.


Lemma writesto_inited :
  forall H i l,
    trco H
    -> writesto H i l
    -> inited H i.
Proof.
intros H i l Htrco (v & Hwrites).
eapply writes_inited; eauto; done.
Qed.


Lemma trco_init_invert_nis :
  forall H i p,
    trco (H; ev_init i p)
    -> ~ H {{ ev_is i a | a }}.
Proof.
intros H i p Htrco (a & His).
invert Htrco.
intros Htrco' Hinit.
so (is_inited _#3 Htrco' His) as (p' & Hinit').
destruct Hinit; eauto.
Qed.


Lemma trco_is_invert_nis :
  forall H i a,
    trco (H; ev_is i a)
    -> ~ H {{ ev_is i a' | a' }}.
Proof.
intros H i p Htrco (a & His).
invert Htrco.
intros Htrco' _ _ Hinit.
destruct Hinit as (p' & H' & ->).
discriminate_in His; [].
intro His.
edestruct trco_init_invert_nis; eauto; done.
Qed.


Lemma is_split_fun :
  forall H i H1 H2 H1' H2' a a',
    trco H
    -> H = H1; ev_is i a;; H2
    -> H = H1'; ev_is i a';; H2'
    -> H1 = H1' /\ H2 = H2' /\ a = a'.
Proof.
intros H i H1 H2 H1' H2' a a' Htrco Heq Heq'.
assert (H1; ev_is i a;; H2 = H1'; ev_is i a';; H2') as Heqapp by (subst H; auto).
so (app_eq_app _#5 Heqapp) as [(h & H' & Heq2 & Heq1) | [(Heq2 & Heq1) | (h & H' & Heq2 & Heq1)]].
  injection Heq1; intros; subst h.
  rewrite -> Heq2 in Heq.
  rewrite <- app_assoc in Heq.
  rewrite <- app_comm_cons in Heq.
  rewrite -> Heq in Htrco.
  edestruct is_twice; eauto; done.

  injection Heq1; auto; done.

  injection Heq1; intros; subst h.
  rewrite <- Heq2 in Heq'.
  rewrite <- app_assoc in Heq'.
  rewrite <- app_comm_cons in Heq'.
  rewrite -> Heq' in Htrco.
  edestruct is_twice; eauto; done.
Qed.


Lemma is_split :
  forall H H1 H2 i p a,
    H = H1; ev_init i p;; H2
    -> trco H
    -> H {{ ev_is i a }}
    -> exists H3, H2 = nil; ev_is i a;; H3.
Proof.
intros H H1 H2 i p a Heq_init Htrco His.
so (in_split _#3 His) as (H4 & H3 & Heq_is).
invert (trco_truncate _ _ (eqconv Heq_is Htrco)).
intros _ _ _ (p' & (H3' & HeqH3)).
assert (H = H3'; ev_init i p';; (nil; ev_is i a;; H4)) as Heq_is'.
  subst H3.
  autorewrite with canonlist.
  assumption.
so (init_split_fun _#8 Htrco Heq_init Heq_is') as (_ & HeqH2 & _).
eauto; done.
Qed.


Lemma split_is_left :
  forall H H1 h H2 i p a,
    trco H
    -> H = H1; h;; H2
    -> H1 {{ ev_init i p }}
    -> H {{ ev_is i a }}
    -> (H1; h) {{ ev_is i a }}.
Proof.
intros H H1 h H2 i p a Htrco HeqH Hinit His.
subst H.
so (in_app_or _#4 His) as [His' | His'].
  exfalso.
  assert (exists p', (nil; h;; H2) {{ ev_init i p'}}) as (p' & Hinit').
    so (in_split _#3 His') as (H4 & H3 & HeqH2).
    rewrite -> HeqH2 in Htrco.
    autorewrite with canonlist in Htrco.
    invert (trco_truncate _ _ Htrco).
    intros _ _ _ (p' & H5 & Heq).
    exists p'.
    symmetry in Heq.
    so (app_eq_cons _#5 Heq) as [(H3' & HeqH3 & _) | (_ & HeqH1h)].
      apply in_or_app; left.
      rewrite -> HeqH2.
      apply in_or_app; right; right.
      rewrite -> HeqH3.
      left; reflexivity.

      injection HeqH1h; intros; subst h.
      apply in_or_app; right; left; reflexivity.
      
  apply (init_twice' H1 (nil; h;; H2) i p p'); auto; [].
  autorewrite with canonlist; auto; done.

  assumption.
Qed.


Lemma is_tail :
  forall H h i a,
    ~ (exists i' a', h = ev_is i' a')
    -> (H; h) {{ ev_is i a }}
    -> H {{ ev_is i a }}.
Proof.
intros H h i a Hneqis His.
destruct His.
  destruct Hneqis; do 2 eexists; eauto.

  assumption.
Qed.


Lemma is_truncate :
  forall H H' i a,
    ~ H' {{ ev_is i a | i a }}
    -> (H;; H') {{ ev_is i a }}
    -> H {{ ev_is i a }}.
Proof.
intros H H' i a Hnis His.
induction H' as [| h H' IH].
(* nil *)
assumption.

(* cons *)
apply IH; [|].
  intros (i' & a' & Hin).
  destruct Hnis.
  exists i', a'.
  right.
  assumption.

  eapply is_tail; eauto; [].
  intros (i' & a' & Heq).
  destruct Hnis.
  exists i', a'.
  left; assumption.
Qed.


Lemma reads_cons_invert :
  forall H h i l,
    reads (H; h) i l
    -> reads H i l \/ (exists m, h = ev_is i (ac_read l m)) \/ (exists v, h = ev_is i (ac_rw l v)).
Proof.
intros H h i l Hreads.
#4 invert Hreads;
  [ intros m His
  | intros v His ];
  destruct His as [Heq | His'].
- right; left; exists m; assumption.
- eauto using reads_read.
- right; right; eauto; done.
- left.
  eauto using reads_rw.
Qed.


Lemma writes_cons_invert :
  forall H h i l v,
    writes (H; h) i l v
    -> writes H i l v \/ (exists m, h = ev_is i (ac_write l v m)) \/ h = ev_is i (ac_rw l v).
Proof.
intros H h i l v Hwrites.
invert Hwrites; 
  [ intros m His
  | intros His];
  destruct His as [Heq | His'];
  [ right; left; exists m; assumption | | | ];
  eauto using writes_write, writes_rw.
Qed.


Lemma reads_cons_invert_is :
  forall H h i l,
    reads (H; h) i l
    -> reads H i l \/ exists a, h = ev_is i a.
Proof.
intros H h i l Hread.
so (reads_cons_invert _#4 Hread) as [Hread' | [(m & Heq) | (v & Heq)]]; eauto.
Qed.


Lemma writes_cons_invert_is :
  forall H h i l v,
    writes (H; h) i l v
    -> writes H i l v \/ exists a, h = ev_is i a.
Proof.
intros H h i l v Hwrite.
so (writes_cons_invert _#5 Hwrite) as [Hread' | [(m & Heq) | Heq]]; eauto.
Qed.
    

Lemma reads_tail :
  forall H h i l,
    ~ (exists i' a', h = ev_is i' a')
    -> reads (H; h) i l
    -> reads H i l.
Proof.
intros H h i l Hnis Hreads.
so (reads_cons_invert _#4 Hreads) as [Hreads' | [(m & His) | (v & His)]].
- assumption.
- subst h; destruct Hnis; eauto; done.
- subst h; destruct Hnis; eauto; done.
Qed.

Lemma writes_tail :
  forall H h i l v,
    ~ (exists i' a', h = ev_is i' a')
    -> writes (H; h) i l v
    -> writes H i l v.
Proof.
intros H h i l v Hnis Hwrites.
#3 so (writes_cons_invert _#5 Hwrites) as [Hwrites' | [(m & His) | His]].
  assumption.
  subst h; destruct Hnis; eauto; done.
  subst h; destruct Hnis; eauto; done.
Qed.

Lemma writesto_tail :
  forall H h i l,
    ~ (exists i' a', h = ev_is i' a')
    -> writesto (H; h) i l
    -> writesto H i l.
Proof.
intros H h i l Hnis (v & Hwrites).
exists v.
eapply writes_tail; eauto.
Qed.


Lemma reads_truncate :
  forall H H' i l,
    ~ H' {{ ev_is i' a' | i' a' }}
    -> reads (H;; H') i l
    -> reads H i l.
Proof.
intros H H' i l Hnis Hreads.
invert Hreads; [ intros m | intros v ];
intro His; (so (in_app_or _#4 His) as [|]; [destruct Hnis; eauto | eauto with dynamic]).
Qed.

Lemma writes_truncate :
  forall H H' i l v,
    ~ H' {{ ev_is i' a' | i' a' }}
    -> writes (H;; H') i l v
    -> writes H i l v.
Proof.
intros H H' i l v Hnis Hwrites.
invert Hwrites; [ intros m | ];
intros His; (so (in_app_or _#4 His) as [|]; [destruct Hnis; eauto | eauto with dynamic]).
Qed.


Lemma writesto_truncate :
  forall H H' i l,
    ~ H' {{ ev_is i' a' | i' a' }}
    -> writesto (H;; H') i l
    -> writesto H i l.
Proof.
intros H H' i l Hnis (v & Hwrites).
exists v.
eapply writes_truncate; eauto; done.
Qed.


Lemma writes_writesto :
  forall H i l v,
    writes H i l v
    -> writesto H i l.
Proof.
intros; eexists; eauto.
Qed.


Lemma writesto_isr :
  forall H i l,
    trco H
    -> writesto H i l
    -> isr H i
    -> reads H i l.
Proof.
intros H i l Htrco Hwrite Hisr.
destruct Hisr as (l' & Hread).
so (reads_writesto_fun _#4 Htrco Hread Hwrite) as Heq.
subst l'.
assumption.
Qed.


Lemma reads_isw :
  forall H i l,
    trco H
    -> reads H i l
    -> isw H i
    -> writesto H i l.
Proof.
intros H i l Htrco Hread Hisw.
destruct Hisw as (l' & v & Hwrite).
so (reads_writes_fun _#5 Htrco Hread Hwrite) as Heq.
subst l'.
eexists; eauto.
Qed.


Lemma exec_read_rf :
  forall H i,
    trco H
    -> exec H i
    -> isr H i
    -> exists iw, rf H iw i.
Proof.
intros H i Htrco Hexec Hisr.
invert Hexec; [|].
  intro Hin.
  exfalso.
  so (in_split _#3 Hin) as (H2 & H1 & HeqH).
  destruct Hisr as (l & His).
  invert (trco_truncate _ _ (eqconv HeqH Htrco)).
  intros a _ His' _ _ Hnread Hnrw.
  invert His; [|].
    intros m His''.
    exploit (is_fun H i (ac_read l m) a) as Heqa; auto; [|].
      rewrite -> HeqH.
      apply in_or_app; right; right.
      assumption.
    destruct Hnread.
    eauto; done.

    intros v His''.
    exploit (is_fun H i (ac_rw l v) a) as Heqa; auto; [|].
      rewrite -> HeqH.
      apply in_or_app; right; right.
      assumption.
    destruct Hnrw.
    eauto; done.

  eauto; done.
Qed.

(* Exec *)

Lemma exec_invert :
  forall H i,
    exec H i
    -> exists h, H {{ h }} /\ executes h i.
Proof.
intros H i Hexec.
invert Hexec; intros; repeat eexists; eauto.
Qed.


Lemma executes_exec :
  forall H h i,
    H {{ h }}
    -> executes h i
    -> exec H i.
Proof.
intros H h i Hin Hexecutes.
splithyp Hexecutes; destruct_all Hexecutes; subst; eauto using exec_exec, exec_rf.
Qed.


Lemma exec_cons_invert :
  forall H h i,
    exec (H; h) i
    -> executes h i \/ exec H i.
Proof.
intros H h i Hexec.
so (exec_invert _ _ Hexec) as (h' & Hin & Hexecutes).
destruct Hin as [Heq | Hin].
  subst h'.
  left; assumption.

  right.
  eapply executes_exec; eauto; done.
Qed.


Ltac discriminate_exec Hexec :=
  let H := fresh
  in
    so (exec_cons_invert _#3 Hexec) as [H | H];
    clear Hexec;
    [discriminate_executes H | revert H].


Lemma exec_or :
  forall H i, exec H i <-> (H {{ ev_exec i }} \/ H {{ ev_rf iw i | iw }}).
Proof.
intros H i.
split.
  intro Hexec.
  invert Hexec; eauto; done.

  intros [| (? & ?)]; eauto using exec_exec, exec_rf; done.
Qed.


Lemma exec_tail :
  forall H h i,
    ~ (exists i', h = ev_exec i')
    -> ~ (exists iw ir, h = ev_rf iw ir) 
    -> exec (H; h) i
    -> exec H i.
Proof.
intros H h i Hnexec Hnrf Hexec.
invert Hexec; clear Hexec.
  intro Hexec.
  destruct Hexec as [-> | Hexec].
    destruct Hnexec; eauto; done.

    apply exec_exec; assumption.

  intros iw Hrf.
  destruct Hrf as [-> | Hrf].
    destruct Hnrf; eauto; done.

    eapply exec_rf; eassumption.
Qed.


Lemma exec_decidable :
  forall H i, decidable (exec H i).
Proof.
intros H i.
apply (iff_decidable (H {{ ev_exec i }} \/ exists iw, H {{ ev_rf iw i }})); [symmetry; apply exec_or |].
apply dec_or; [|].
  apply present_decidable; done.

  apply present_1_decidable; [].
  intro.
  apply match_rf_r_decidable; done.
Qed.


Lemma trco_executes_invert :
  forall H h i,
    trco (H; h)
    -> executes h i
    -> exists a,
         H {{ ev_is i a }}
         /\ ~ exec H i 
         /\ (forall i', so H i' i -> exec H i').
Proof.
intros H h i Htrco Hexecutes.
destruct Hexecutes as [-> | (iw & ->)].
invert Htrco.
eauto; done.

invert Htrco.
intros l H1 H2 Hread H4 H5.
invert Hread.
- intro m.
  exists (ac_read l m).
  repeat2 split; eauto; done.
- intro v.
  exists (ac_rw l v).
  repeat2 split; eauto; done.
Qed.

Lemma trco_exec_invert :
  forall H i,
    trco H
    -> exec H i
    -> exists H1 H2 h a,
         H = H1; h;; H2
         /\ executes h i
         /\ H1 {{ ev_is i a }}
         /\ ~ exec H1 i
         /\ (forall i', so H1 i' i -> exec H1 i').
Proof.
intros H i Htrco Hexec.
so (exec_invert _ _ Hexec) as (h & Hin & Hexecutes).
so (in_split _#3 Hin) as (H2 & H1 & ->).
so (trco_executes_invert _#3 (trco_truncate _ _ Htrco) Hexecutes) as (a & Hcond).
exists H1, H2, h, a.
auto.
Qed.

Lemma exec_is :
  forall H i,
    trco H
    -> exec H i
    -> H {{ ev_is i ae | ae }}.
Proof.
intros H i Htrco Hexec.
so (trco_exec_invert _ _ Htrco Hexec) as (H1 & H2 & h & a & Heq & _ & His & _).
exists a.
subst H.
apply in_or_app; right; right; assumption.
Qed.


Lemma exec_inited :
  forall H i,
    trco H
    -> exec H i
    -> H {{ ev_init i pe | pe }}.
Proof.
intros H i Htrco Hexec.
so (exec_is _ _ Htrco Hexec) as (a & His).
eapply is_inited; eauto.
Qed.


Lemma trco_init_invert_nexec :
  forall H i p,
    trco (H; ev_init i p)
    -> ~ exec H i.
Proof.
intros H i p Htrco Hexec.
invert Htrco.
intros _ Hninit.
destruct Hninit.
so (exec_inited _ _ (trco_tail _ _ Htrco) Hexec) as (p' & Hinit).
eauto.
Qed.


Lemma trco_is_invert_nexec :
  forall H i a,
    trco (H; ev_is i a)
    -> ~ exec H i.
Proof.
intros H i a Htrco Hexec.
invert Htrco.
intros Htrco' _ _ (p & H' & ->).
apply (trco_init_invert_nexec H' i p); auto; [].
eapply exec_tail; eauto; discform.
Qed.


Lemma trco_exec_invert_init :
  forall H i,
    trco (H; ev_exec i)
    -> H {{ ev_init i pe | pe }}.
Proof.
intros H i Htrco.
invert Htrco.
intros a Htrco' His _ _.
so (in_split _#3 His) as (H2 & H1 & ->).
invert (trco_truncate _ _ Htrco').
intros _ _ _ (p & H' & ->).
exists p.
apply in_or_app; right; right; left; reflexivity.
Qed.


Lemma executes_fun_1 :
  forall h i i',
    executes h i
    -> executes h i'
    -> i = i'.
Proof.
intros h i i' Hexecutes Hexecutes'.
invert Hexecutes; invert Hexecutes'.
  intros -> Heq; injection Heq; auto; done.
  
  intros (iw & ->) Heq; discriminate Heq.

  intros Heq (iw & ->); discriminate Heq.

  intros (iw & ->) (iw' & Heq); injection Heq; auto; done.
Qed.


(* Elementary truncation *)

Lemma init_execed_truncate :
  forall H H' i p,
    trco (H;; H')
    -> exec H i
    -> (H;; H') {{ ev_init i p }}
    -> H {{ ev_init i p }}.
Proof.
intros H H' i a Htrco Hexec Hinit.
so (in_split _#3 Hinit) as (H2 & H1 & Heq).
so (app_eq_app2 _#5 Heq) as [(h & H3 & HeqH' & HeqHe) | (H4 & _ & HeqH)].
  injection HeqHe; intros _ ->.
  subst H'.
  autorewrite with canonlist in Htrco.
  destruct (trco_init_invert_nexec _#3 (trco_truncate _ _ Htrco)); [].
  apply exec_app_incl; assumption.

  subst H.
  apply in_or_app; right; left; reflexivity.
Qed.


Lemma is_execed_tail :
  forall H h i a,
    trco (H; h)
    -> exec H i
    -> (H; h) {{ ev_is i a }}
    -> H {{ ev_is i a }}.
Proof.
intros H h i a Htrco Hexec His.
destruct His; try assumption.
subst h.
destruct (trco_is_invert_nexec _ _ _ Htrco); assumption.
Qed.


Lemma is_execed_truncate :
  forall H H' i a,
    trco (H;; H')
    -> exec H i
    -> (H;; H') {{ ev_is i a }}
    -> H {{ ev_is i a }}.
Proof.
intros H H' i a Htrco Hexec His.
so (in_split _#3 His) as (H2 & H1 & Heq).
so (app_eq_app2 _#5 Heq) as [(h & H3 & HeqH' & HeqHe) | (H4 & _ & HeqH)].
  injection HeqHe; intros _ ->.
  subst H'.
  autorewrite with canonlist in Htrco.
  destruct (trco_is_invert_nexec _#3 (trco_truncate _ _ Htrco)); [].
  apply exec_app_incl; assumption.

  subst H.
  apply in_or_app; right; left; reflexivity.
Qed.


Lemma reads_execed_tail :
  forall H h i l,
    trco (H; h)
    -> exec H i
    -> reads (H; h) i l
    -> reads H i l.
Proof.
intros H h i a Htrco Hexec Hreads.
invert Hreads.
  intros m His.
  eapply reads_read; [].
  eapply is_execed_tail; eauto; done.

  intros v His.
  eapply reads_rw; [].
  eapply is_execed_tail; eauto; done.
Qed.


Lemma writes_execed_tail :
  forall H h i l v,
    trco (H; h)
    -> exec H i
    -> writes (H; h) i l v
    -> writes H i l v.
Proof.
intros H h i l v Htrco Hexec Hwrites.
invert Hwrites.
  intros m His.
  eapply writes_write; [].
  eapply is_execed_tail; eauto; done.

  intros His.
  eapply writes_rw; [].
  eapply is_execed_tail; eauto; done.
Qed.

Lemma writesto_execed_tail :
  forall H h i l,
    trco (H; h)
    -> exec H i
    -> writesto (H; h) i l
    -> writesto H i l.
Proof.
intros H h i l Htrco Hexec (v & Hwrites).
exists v.
eapply writes_execed_tail; eauto.
Qed.


Lemma is_inited_truncate :
  forall H1 h H2 i a,
    trco (H1; h;; H2)
    -> (H1; h;; H2) {{ ev_is i a }}
    -> H1 {{ ev_init i pe | pe }}
    -> (H1; h) {{ ev_is i a }}.
Proof.
intros H1 h H2 i a Htrco His (p & Hinit).
so (in_app_or _#4 His) as [Hin | Hin].
  exfalso.
  so (in_split _#3 Hin) as (H4 & H3 & ->).
  autorewrite with canonlist in Htrco.
  invert (trco_truncate _ _ Htrco).
  intros _ _ _ (p' & (H & Heq)).
  destruct H3 as [| h' H3'].
    simpl in Heq.
    injection Heq; intros; subst h H1.
    simpl in Htrco.
    invert (trco_tail _ _ (trco_truncate _ _ Htrco)).
    intros _ Hninit.
    destruct Hninit.
    exists p; exact Hinit.

    autorewrite with canonlist in Heq.
    injection Heq.
    intros; subst H h'.
    autorewrite with canonlist in Htrco.
    invert (trco_tail _ _ (trco_truncate _ _ Htrco)).
    intros _ Hninit.
    destruct Hninit.
    exists p.
    apply in_or_app; right; right.
    exact Hinit.

  assumption.
Qed.


(* Program order *)

Lemma po_init :
  forall H i i',
    po H i i'
    -> exists p, H {{ ev_init i p }} /\ H {{ ev_init i' p }}.
Proof.
intros H i i' Hpo.
destruct Hpo as (H1 & H2 & H3 & p & Heq).
exists p.
subst H.
split.
  apply in_or_app.
  right.
  simpl.
  right.
  apply in_or_app.
  right.
  simpl; left; auto.

  apply in_or_app.
  right.
  simpl; left; auto.
Qed.

Lemma pop_init : 
  forall H i i',
    pop H i i'
    -> exists p, H {{ ev_init i p }} /\ H {{ ev_init i' p }}.
Proof.
  auto using pop_po, po_init.
Qed.

Lemma po_init_1 :
  forall H i i' p,
    trco H
    -> po H i i'
    -> H {{ ev_init i p }}
    -> H {{ ev_init i' p }}.
Proof.
intros H i i' p Htrco Hpo Hiniti.
so (po_init _#3 Hpo) as (p' & Hinit' & Hiniti').
so (init_unique _#4 Htrco Hiniti Hinit'); subst p'.
assumption.
Qed.


Lemma po_init_2 :
  forall H i i' p,
    trco H
    -> po H i i'
    -> H {{ ev_init i' p }}
    -> H {{ ev_init i p }}.
Proof.
intros H i i' p Htrco Hpo Hiniti'.
so (po_init _#3 Hpo) as (p' & Hinit & Hinit'i').
so (init_unique _#4 Htrco Hiniti' Hinit'i'); subst p'.
assumption.
Qed.


Lemma poq_init_2 :
  forall H i i' p,
    trco H
    -> poq H i i'
    -> H {{ ev_init i' p }}
    -> H {{ ev_init i p }}.
Proof.
intros H i i' p Htrco Hpoq Hinit.
destruct Hpoq as [Heq | Hpo].
  subst; assumption.

  eapply po_init_2; eauto; done.
Qed.


Lemma po_inited :
  forall H i i',
    po H i i' -> inited H i /\ inited H i'.
Proof.
intros H i i' Hpo.
pose proof (po_init H i i' Hpo) as (p & Hi & Hi').
split; eexists; eauto.
Qed.

Lemma pop_inited :
  forall H i i',
    pop H i i' -> inited H i /\ inited H i'.
Proof.
  intros H i i' (Hpo & _ & _).
  apply po_inited; auto.
Qed.

Lemma po_tail :
  forall H h i1 i2,
    (forall i p, h = ev_init i p -> i <> i2)
    -> po (H; h) i1 i2
    -> po H i1 i2.
Proof.
intros H h i1 i2 Hneq Hpo.
destruct Hpo as (H1 & H2 & H3 & p & Heq).
destruct (app_eq_cons _#5 Heq) as [(H3' & Heq' & _) | (HeqH3 & Heq')].
  subst H3.
  simpl in Heq.
  injection Heq; intro HeqH.
  subst H.
  repeat eexists; eauto.

  subst H3.
  simpl in Heq.
  injection Heq; intros HeqH Heqh.
  destruct (Hneq i2 p); auto.
Qed.

Lemma isop_tail :
  forall H h i,
    ~ (exists a, h = ev_is i a)
    -> isop (H; h) i
    -> isop H i.
Proof.
  intros H h i Hneq Hisop.
  destruct Hisop as [Hisop | Hisop]; [ left | right ].
  - destruct Hisop as (m & (l & [Hin | Hheq]) & Hopm).
    + exfalso.
      apply Hneq.
      exists (ac_read l m).
      auto.
    + exists m.
      split; [exists l | ]; auto.
  - destruct Hisop as (m & (l & v & [Hin | Hheq]) & Hopm).
    + exfalso.
      apply Hneq.
      exists (ac_write l v m).
      auto.
    + exists m.
      split; [exists l, v | ]; auto.
Qed.  

Lemma pop_tail :
  forall H h i1 i2,
    (forall i p, h = ev_init i p -> i <> i2)
    -> ~ (exists a, h = ev_is i1 a)
    -> ~ (exists a, h = ev_is i2 a)
    -> pop (H; h) i1 i2
    -> pop H i1 i2.
Proof.
  intros H h i1 i2 Hneq Hnis1 Hnis2 Hpop.
  split; [| split]; eauto using po_tail;
    destruct Hpop as (Hpo & Hisop1 & Hisop2);
    eapply isop_tail; eauto.
Qed.

Lemma po_truncate :
  forall H H' i1 i2,
    (forall i p, H' {{ ev_init i p }} -> i <> i2)
    -> po (H;; H') i1 i2
    -> po H i1 i2.
Proof.
intros H H' i1 i2 Hninit Hpo.
induction H' as [| h H' IH].
(* nil *)
assumption.

(* cons *)
apply IH; [|].
  intros i p Hin.
  eapply Hninit; eauto; [].
  right; eassumption.

  eapply po_tail; eauto; [].
  intros i p Heq.
  eapply Hninit; eauto; [].
  left; eassumption.
Qed.


Lemma po_init_tail :
  forall H i p i1 i2,
    trco (H; ev_init i p)
    -> po (H; ev_init i p) i1 i2
    -> po H i1 i2 \/ i = i2.
Proof.
intros H i p i1 i2 Htrco Hpo.
destruct Hpo as (H1 & H2 & H3 & p' & Heq).
so (app_eq_cons _#5 Heq) as [(H3' & _ & Heq') | (_ & Heq')].
    left.
    repeat eexists; eauto; done.

    right.
    injection Heq'; auto; done.
Qed.


Lemma po_trans :
  forall H i1 i2 i3,
    trco H
    -> po H i1 i2
    -> po H i2 i3
    -> po H i1 i3.
Proof.
intros H i1 i2 i3 Htrco Hpo12 Hpo23.
destruct Hpo12 as (H1 & H2 & H3 & p & Heq1).
destruct Hpo23 as (H4 & H5 & H6 & p' & Heq2).
assert (p = p') as Heqp.
  apply (init_unique H i2); auto.
    rewrite -> Heq1; apply in_or_app; right; left; auto.

    rewrite -> Heq2; apply in_or_app; right; right; apply in_or_app; right; left; auto.
subst p'.
pose proof Heq2 as Heq.
rewrite -> app_comm_cons in Heq; rewrite -> app_assoc in Heq; rewrite -> Heq1 in Heq.
pose proof (app_eq_app _#5 Heq) as [(h & H' & Heq3 & Heq4) | [(Heq3 & Heq4) | (h & H' & Heq3 & Heq4)]].
  exists H1, (H2; ev_init i2 p;; H'; h;; H5), H6, p.
  rewrite -> Heq3 in Heq1.
  rewrite <- !app_assoc in Heq1; rewrite <- !app_comm_cons in Heq1.
  rewrite <- !app_assoc; rewrite <- !app_comm_cons; rewrite <- !app_assoc; rewrite <- !app_comm_cons.
  exact Heq1.

  exists H1, (H2; ev_init i2 p;; H5), H6, p.
  rewrite -> Heq3 in Heq1.
  rewrite <- !app_assoc in Heq1; rewrite <- !app_comm_cons in Heq1.
  rewrite <- !app_assoc; rewrite <- !app_comm_cons.
  exact Heq1.

  injection Heq4; intros; subst h.
  rewrite <- Heq3 in Heq.
  rewrite <- Heq1 in Heq.
  rewrite <- app_assoc in Heq; rewrite <- app_comm_cons in Heq.
  rewrite -> Heq in Htrco.
  thus (trco (H4; ev_init i2 p;; H'; ev_init i2 p)) as Htrco' by trco_truncate.
  invert Htrco'; intros _ Hndecl.
  destruct Hndecl.
  exists p.
  apply in_or_app; right; left; auto.
Qed.


Lemma po_poq_trans :
  forall H i1 i2 i3,
    trco H
    -> po H i1 i2
    -> poq H i2 i3
    -> po H i1 i3.
Proof.
intros H i1 i2 i3 Htrco H12 H23.
destruct H23 as [Heq | H23].
  subst i3; auto.

  eapply po_trans; eauto.
Qed.


Lemma poq_po_trans :
  forall H i1 i2 i3,
    trco H
    -> poq H i1 i2
    -> po H i2 i3
    -> po H i1 i3.
Proof.
intros H i1 i2 i3 Htrco H12 H23.
destruct H12 as [Heq | H12].
  subst i2; auto; done.

  eapply po_trans; eauto; done.
Qed.


Lemma poq_trans :
  forall H i1 i2 i3,
    trco H
    -> poq H i1 i2
    -> poq H i2 i3
    -> poq H i1 i3.
Proof.
intros H i1 i2 i3 Htrco H12 H23.
destruct H12 as [Heq | H12].
  subst; assumption.

  right.
  eapply po_poq_trans; eauto; done.
Qed.
  

Lemma po_from_before :
  forall H H1 H2 i i' p,
    H = H1; ev_init i' p ;; H2
    -> H1 {{ ev_init i p }}
    -> po H i i'.
Proof.
intros H H1 H2 i i' p Heq Hinit.
so (in_split _#3 Hinit) as (H4 & H3 & ->).
repeat eexists; eauto.
Qed.


Lemma po_from_before' :
  forall H H1 H2 i i' p p',
    trco H 
    -> H = H1; ev_init i' p ;; H2
    -> H {{ ev_init i p }}
    -> H1 {{ ev_init i p' }}
    -> po H i i'.
Proof.
intros H H1 H2 i i' p p' Htrco Heq Hinit Hinit'.
eapply po_from_before; eauto; [].
replace p' with p in Hinit'; auto; [].
apply (init_unique H i); auto; [].
subst H; apply in_or_app; right; right; assumption.
Qed.


Lemma program_trichot :
  forall H i i' p,
    H {{ ev_init i p }}
    -> H {{ ev_init i' p }}
    -> po H i i' \/ i = i' \/ po H i' i.
Proof.
intros H i i' p Hinit Hinit'.
so (in_split _#3 Hinit) as (H2 & H1 & Heq).
subst H; clear Hinit.
so (in_app_or _#4 Hinit') as [Hin | Hin].
  left.
  so (in_split _#3 Hin) as (H4 & H3 & Heq).
  subst H2.
  autorewrite with canonlist.
  do 4 eexists; reflexivity.

  destruct Hin as [Heq | Hin].
    injection Heq; intros; right; left; assumption.

    right; right.
  so (in_split _#3 Hin) as (H4 & H3 & Heq).
  subst H1.
  do 4 eexists; reflexivity.
Qed.


Lemma po_execed_tail :
  forall H h i1 i2,
    trco (H; h)
    -> exec H i2
    -> po (H; h) i1 i2
    -> po H i1 i2.
Proof.
intros H h i1 i2 Htrco Hexec Hpo.
destruct h;
(eapply po_tail; [| eassumption]);
intros ii pp Heq;
try (discriminate Heq).
injection Heq; intros; subst ii pp.
intro; subst i.
invert Htrco; intros _ Hndecl.
destruct Hndecl.
eapply exec_inited; eauto.
eapply trco_tail; eauto.
Qed.

Lemma isop_execed_tail :
  forall H h i,
    trco (H; h)
    -> exec H i
    -> isop (H; h) i
    -> isop H i.
Proof.
  intros H h i Htrco Hexec Hisop.
  eapply isop_tail; eauto; intros (a & Hheq).
  - destruct Hisop as [ (m & ( l & His) & Hopm) | (m & ( l & v & His) & Hopm) ].
    + rewrite <- (is_fun (H;h) i a (ac_read l m)) in His; auto.
      assert (H {{ ev_is i a }}) as His2. {
      eapply is_execed_tail; eauto.
      }
      edestruct in_split as (H2 & H1 & Heq); eauto.
      apply (is_twice H1 H2 nil i a a).
      simpl.
      rewrite <- Heq.
      rewrite <- Hheq.
      auto.
      left; auto.
    + rewrite <- (is_fun (H;h) i a (ac_write l v m)) in His; auto.
      assert (H {{ ev_is i a }}) as His2. {
      eapply is_execed_tail; eauto.
      }
      edestruct in_split as (H2 & H1 & Heq); eauto.
      apply (is_twice H1 H2 nil i a a).
      simpl.
      rewrite <- Heq.
      rewrite <- Hheq.
      auto.
      left; auto.
Qed.



Lemma po_execed_truncate :
  forall H H' i1 i2,
    trco (H;; H')
    -> exec H i2
    -> po (H;; H') i1 i2
    -> po H i1 i2.
Proof.
intros H H' i1 i2 Htrco Hexec Hpo.
induction H' as [| h H'].
  assumption.

  apply IHH'.
    simpl in Htrco.
    eapply trco_tail; eauto.

    simpl in Hpo.
    eapply po_execed_tail; eauto.
    apply exec_app_incl; assumption.
Qed.


Lemma poq_execed_truncate :
  forall H H' i1 i2,
    trco (H;; H')
    -> exec H i2
    -> poq (H;; H') i1 i2
    -> poq H i1 i2.
Proof.
intros H H' i1 i2 Htrco Hexec Hpoq.
destruct Hpoq as [Heq | Hpo].
  subst i2.
  left; reflexivity.

  right.
  eapply po_execed_truncate; eauto; done.
Qed.


Lemma po_irreflex :
  forall H i,
    trco H
    -> ~ po H i i.
Proof.
intros H i Htrco Hpo.
destruct Hpo as (H1 & H2 & H3 & p & Heq).
subst H.
destruct (init_twice _#6 Htrco).
Qed.


Lemma po_init_2_strengthen :
  forall H1 H2 i i' p,
    trco (H1;; H2)
    -> po (H1;; H2) i i'
    -> H1 {{ ev_init i' p }}
    -> H1 {{ ev_init i p }}.
Proof.
intros H1 H2 i1 i2 p Htrco Hpo Hinit2.
assert ((H1;; H2) {{ ev_init i1 p }}) as Hinit1.
  eapply po_init_2; eauto; [].
  apply in_or_app; right; assumption.
so (in_app_or _#4 Hinit1) as [Hinit1' | Hinit1'].
  exfalso.
  edestruct po_irreflex; eauto; [].
  eapply po_trans; eauto; [].
  so (in_split _#3 Hinit2) as (H4 & H3 & Hin2).
  so (in_split _#3 Hinit1') as (H6 & H5 & Hin1).
  exists H3, (H4;; H5), H6, p.
  subst.
  autorewrite with canonlist.
  reflexivity.

  assumption.
Qed.


Lemma is_po_tail :
  forall H h i i' a,
    trco (H; h)
    -> po (H; h) i i'
    -> (H; h) {{ ev_is i a }}
    -> H {{ ev_is i a }}.
Proof.
intros H h i i' a Htrco Hpo His.
destruct His; auto; [].
exfalso.
assert (i <> i') as Hneqi.
  intros <-.
  exact (po_irreflex _ _ Htrco Hpo).
subst h.
invert Htrco.
intros _ _ _ (p & H0 & Heq).
subst H.
destruct Hpo as (H1 & H2 & H3 & p' & Heq0ee).
exploit (first_neq_middle_invert _#6 Heq0ee) as (H4 & _ & Heq0e); [|].
  intro; discriminate.
exploit (first_neq_middle_invert _#6 Heq0e) as (H5 & _ & Heq0); [|].
  intro Heqinit.
  injection Heqinit.
  intros; subst.
  destruct Hneqi; auto; done.
subst H0.
destruct (init_twice H1 (H2; ev_init i' p';; H5) (nil; ev_is i a) i p' p).
autorewrite with canonlist.
assumption.
Qed.


Lemma pop_execed_tail :
  forall H h i1 i2,
    trco (H; h)
    -> exec H i2
    -> pop (H; h) i1 i2
    -> pop H i1 i2.
Proof.
  intros H h i1 i2 Htrco Hexec Hpop.
  destruct Hpop as (Hpo & Hisop1 & Hisop2).
  split; [| split];
    eauto using po_execed_tail, isop_execed_tail.

  destruct Hisop1 as [ (m & ( l & His) & Hopm) | (m & ( l & v & His) & Hopm) ].
  - left.
    exists m. split; auto.
    exists l.
    eapply is_po_tail; eauto.
  - right.
    exists m. split; auto.
    exists l, v.
    eapply is_po_tail; eauto.
Qed.


Lemma is_po_truncate :
  forall H H' i i' a,
    trco (H;; H')
    -> po H i i'
    -> (H;; H') {{ ev_is i a }}
    -> H {{ ev_is i a }}.
Proof.
intros H H' i i' a Htrco Hpo His.
induction H' as [| h H' IH].
(* nil *)
assumption.

(* cons *)
simpl in Htrco.
autorewrite with canonlist in His.
apply IH; [|].
  prove_trco.
eapply is_po_tail; eauto; [].
apply po_cons_incl; [].
apply po_app_incl; [].
eassumption.
Qed.


Lemma reads_po_tail :
  forall H h i i' l,
    trco (H; h)
    -> po (H; h) i i'
    -> reads (H; h) i l
    -> reads H i l.
Proof.
intros H h i i' l Htrco Hpo Hreads.
invert Hreads; [|].
  intros m His.
  eapply reads_read; [].
  eapply is_po_tail; eauto; done.

  intros v His.
  eapply reads_rw; [].
  eapply is_po_tail; eauto; done.
Qed.

Lemma reads_po_truncate :
  forall H H' i i' l,
    trco (H;; H')
    -> po H i i'
    -> reads (H;; H') i l
    -> reads H i l.
Proof.
intros H H' i i' l Htrco Hpo Hreads.
induction H' as [| h H' IH].
(* nil *)
assumption.

(* cons *)
simpl in Htrco.
autorewrite with canonlist in Hreads.
apply IH; [|].
  prove_trco.
eapply reads_po_tail; eauto; [].
apply po_cons_incl; [].
apply po_app_incl; [].
eassumption.
Qed.


Lemma writes_po_tail :
  forall H h i i' l v,
    trco (H; h)
    -> po (H; h) i i'
    -> writes (H; h) i l v
    -> writes H i l v.
Proof.
intros H h i i' l v Htrco Hpo Hwrites.
invert Hwrites; [|].
  intros m His.
  eapply writes_write; [].
  eapply is_po_tail; eauto; done.

  intro His.
  eapply writes_rw; [].
  eapply is_po_tail; eauto; done.
Qed.


Lemma writes_po_truncate :
  forall H H' i i' l v,
    trco (H;; H')
    -> po H i i'
    -> writes (H;; H') i l v
    -> writes H i l v.
Proof.
intros H H' i i' l v Htrco Hpo Hwrites.
induction H' as [| h H' IH].
(* nil *)
assumption.

(* cons *)
simpl in Htrco.
autorewrite with canonlist in Hwrites.
apply IH; [|].
  prove_trco.
eapply writes_po_tail; eauto; [].
apply po_cons_incl; [].
apply po_app_incl; [].
eassumption.
Qed.


Lemma po_inited_tail :
  forall H h i i',
    trco (H; h)
    -> inited H i'
    -> po (H; h) i i'
    -> po H i i'.
Proof.
intros H h i1 i2 Htrco (p & Hinit2) Hpo.
eapply po_tail; eauto; [].
intros i p' Heqh Heqi.
subst h i.
invert Htrco.
intros _ Hninit.
destruct Hninit.
eexists; eassumption.
Qed.


Lemma po_po_tail :
  forall H h i1 i2 i3,
    trco (H; h)
    -> po (H; h) i2 i3
    -> po (H; h) i1 i2
    -> po H i1 i2.
Proof.
intros H h i1 i2 i3 Htrco Hpo23 Hpo12.
eapply po_tail; eauto; [].
intros i p Heqh Heqi.
subst h i.
destruct Hpo23 as (H1 & H2 & H3 & p' & Heq).
so (app_eq_cons _#5 Heq) as [(H4 & HeqH3 & _) | (_ & Heq')].
  subst H3.
  rewrite -> Heq in Htrco.
  destruct (init_twice H1 (H2; ev_init i3 p';; H4) nil i2 p' p).
  autorewrite with canonlist in Htrco.
  autorewrite with canonlist.
  assumption.

  injection Heq'.
  intros _ _ ->.
  rewrite <- Heq' in Htrco.
  destruct (init_twice H1 H2 nil i2 p' p').
  assumption.
Qed.


Lemma po_po_truncate :
  forall H H' i1 i2 i3,
    trco (H;; H')
    -> po H i2 i3
    -> po (H;; H') i1 i2
    -> po H i1 i2.
Proof.
intros H H' i1 i2 i3 Htrco Hpo23 Hpo.
induction H' as [| h H' IH].
(* nil *)
exact Hpo.

(* cons *)
simpl in Htrco, Hpo.
apply IH; [|].
  prove_trco.

  eapply po_po_tail; eauto; [].
  apply po_cons_incl; [].
  apply po_app_incl; [].
  eassumption.
Qed.

Lemma so_po :
  forall H i i',
    so H i i'
    -> po H i i'.
Proof.
  intros H i i' Hso.
  induction Hso; auto; destruct H0; auto.
Qed.

Lemma sop_po :
  forall H i i',
    trco H
    -> sop H i i'
    -> po H i i'.
Proof.
intros H i i' Htrco Hsop.
thus (plusi (so H) i i') as Hsop' by plus_plusi; clear Hsop.
elim Hsop'; clear Hsop'.
(* refl *)
intros.
eapply so_po; eauto; done.

(* trans *)
intros i1 i2 i3 Hso _ Hpo.
apply (po_trans _ _ i2); auto; [].
eapply so_po; eauto; done.
Qed.

Lemma so_inited :
  forall H i i',
    so H i i' -> inited H i /\ inited H i'.
Proof.
intros H i i' Hso.
apply po_inited; [].
eapply so_po; eauto; done.
Qed.

Lemma sop_inited :
  forall H i i',
    sop H i i' -> inited H i /\ inited H i'.
Proof.
intros H i i' Hsop.
destruct Hsop as (i'' & Hso & Hsos).
split.
  exact (so_inited H i i'' Hso andel).

  so (star_plus _#4 Hsos) as [Heq | Hsop'].
    subst i''.
    exact (so_inited H i i' Hso ander).

    destruct (plus_plusr _#4 Hsop') as (i''' & _ & Hso').
    exact (so_inited H i''' i' Hso' ander).
Qed.


Lemma trco_init_invert_npo :
  forall H p i i',
    trco (H; ev_init i p)
    -> ~ po (H; ev_init i p) i i'.
Proof.
intros H p i i' Htrco.
intros (H1 & H2 & H3 & p' & Heq).
invert Htrco.
intros _ Hninit.
destruct Hninit.
exists p'.
so (app_eq_cons _#5 Heq) as [(H3' & _ & Heq') | (_ & Heq')].
  subst H.
  apply in_or_app; right; right; apply in_or_app; right; left; reflexivity.

  injection Heq'.
  intros Heq'' _ _.
  subst H.
  apply in_or_app; right; left; reflexivity.
Qed.

Lemma trco_is_invert_npo :
  forall H a i i',
    trco (H; ev_is i a)
    -> ~ po (H; ev_is i a) i i'.
Proof.
intros H a i i' Htrco Hpo.
invert Htrco.
intros _ _ _ (p & H' & Heq).
subst H.
#2 apply (trco_init_invert_npo H' p i i').
  eapply trco_tail; eauto; done.
  eapply po_tail; eauto; discform; done.
Qed.


Lemma trco_is_invert_nco :
  forall H i a,
    trco (H; ev_is i a)
    -> ~ H {{ ev_co i i' | i' }}.
Proof.
intros H i a Htrco.
intros (i' & Hin).
edestruct trco_is_invert_nis; eauto; [].
so (in_split _#3 Hin) as (H2 & H1 & ->).
invert (trco_truncate _ _ (trco_tail _ _ Htrco)).
Qed.

(* Trace order *)

Lemma to_trans :
  forall H i1 i2 i3,
    to H i1 i2
    -> to H i2 i3
    -> to H i1 i3.
Proof.
intros H i1 i2 i3 Hto12 Hto23.
destruct Hto12 as (H1 & H2 & Heq12 & Hexec1 & Hnexec2).
destruct Hto23 as (H3 & H4 & Heq34 & Hexec2 & Hnexec3).
exists H1, H2.
do2 2 split; auto; [].
rewrite -> Heq12 in Heq34.
so (app_eq_app2 _#5 Heq34) as [(h & H' & _ & Heq) | (H' & _ & Heq)].
  intro Hexec3.
  destruct Hnexec3.
  rewrite <- Heq.
  apply exec_cons_incl; apply exec_app_incl; assumption.

  destruct Hnexec2.
  rewrite -> Heq.
  apply exec_app_incl; assumption.
Qed.


Lemma to_toq_trans :
  forall H i1 i2 i3,
    to H i1 i2
    -> toq H i2 i3
    -> to H i1 i3.
Proof.
intros H i1 i2 i3 H12 H23.
destruct H23 as [Heq | H23].
  subst i3; auto.

  eapply to_trans; eauto.
Qed.


Lemma toq_to_trans :
  forall H i1 i2 i3,
    toq H i1 i2
    -> to H i2 i3
    -> to H i1 i3.
Proof.
intros H i1 i2 i3 H12 H23.
destruct H12 as [Heq | H12].
  subst i2; auto; done.

  eapply to_trans; eauto; done.
Qed.


Lemma toq_trans :
  forall H i1 i2 i3,
    toq H i1 i2
    -> toq H i2 i3
    -> toq H i1 i3.
Proof.
intros H i1 i2 i3 H12 H23.
destruct H12 as [Heq | H12].
  subst; assumption.

  right.
  eapply to_toq_trans; eauto; done.
Qed.


Lemma to_irreflex :
  forall H i, ~ to H i i.
Proof.
intros H i Hto.
destruct Hto as (H1 & H2 & Heq & Hexec & Hnexec).
contradiction.
Qed.


Lemma to_execed_fst :
  forall H i i',
    to H i i'
    -> exec H i.
Proof.
intros H i i' Hto.
destruct Hto as (H1 & H2 & Heq & Hexec & _).
subst H.
apply exec_app_incl; assumption.
Qed.


Lemma to_inited :
  forall H i i',
    trco H
    -> to H i i'
    -> inited H i.
Proof.
  intros H i i' Htrco Hto.
  apply exec_inited; auto.
  eapply to_execed_fst; eauto.
Qed.


Lemma toq_execed_2 :
  forall H i i',
    toq H i i'
    -> exec H i'
    -> exec H i.
Proof.
intros H i i' Htoq Hexeced'.
destruct Htoq as [Heq | Hto].
  subst i'; assumption.

  apply (to_execed_fst _ _ i'); auto.
Qed.


Lemma to_from_halves :
  forall H H1 H2 i i',
    H = H1;; H2
    -> trco H
    -> exec H1 i
    -> exec H2 i'
    -> to H i i'.
Proof.
intros H H1 H2 i1 i2 Heq Htrco Hexec1 Hexec2.
exists H1, H2.
repeat2 split; auto; [].
so (exec_invert _ _ Hexec2) as (h & Hin & Hexecutes).
so (in_split _#3 Hin) as (H2a & H2b & ->); clear Hin.
autorewrite with canonlist in Heq.
intro Hexec2'.
so (trco_executes_invert _#3 (trco_truncate _ _ (eqconv Heq Htrco)) Hexecutes) as (_ & _ & Hnexec2 & _).
destruct Hnexec2.
apply exec_app_incl; assumption.
Qed.


Lemma to_from_before :
  forall H H1 H2 h i i',
    H = H1; h;; H2
    -> executes h i'
    -> trco H
    -> exec H1 i
    -> to H i i'.
Proof.
intros H H1 H2 h i i' Heq Hexecutes Htrco Hexec.
apply (to_from_halves _ H1 (nil; h;; H2)); autorewrite with canonlist; auto; [].
eapply executes_exec; eauto; [].
apply in_or_app; right; left; reflexivity.
Qed.


Lemma to_from_after :
  forall H H1 H2 h i i',
    H = H1; h;; H2
    -> executes h i
    -> trco H
    -> exec H2 i'
    -> to H i i'.
Proof.
intros H H1 H2 h i i' Heq Hexecutes Htrco Hexec.
eapply to_from_halves; eauto; [].
eapply executes_exec; eauto; [].
left; reflexivity.
Qed.


Lemma to_from_nexec :
  forall H i i',
    exec H i
    -> ~ exec H i'
    -> to H i i'.
Proof.
intros H i1 i2 Hexec1 Hnexec2.
exists H, nil.
auto.
Qed.


Lemma trace_trichot :
  forall H i i',
    trco H
    -> exec H i
    -> exec H i'
    -> to H i i' \/ i = i' \/ to H i' i.
Proof.
intros H i i' Htrco Hexec Hexec'.
so (exec_invert _ _ Hexec) as (h & Hin & Hexecutes).
so (exec_invert _ _ Hexec') as (h' & Hin' & Hexecutes').
so (in_split _#3 Hin) as (H2 & H1 & Heq).
so (in_app_or _#4 (eqconv Heq Hin')) as [Hin'' | Hin''].
  left.
  eapply to_from_after; eauto using executes_exec; done.

  destruct Hin'' as [Heqi | Hin''].
    right; left.
    subst h'.
    eapply executes_fun_1; eauto; done.

    right; right.
    eapply to_from_before; eauto using executes_exec; done.
Qed.


Lemma to_front_half :
  forall H H1 H2 i i',
    H = H1;; H2
    -> trco H
    -> to H i i'
    -> exec H1 i'
    -> exec H1 i.
Proof.
intros H H1 H2 i1 i2 Heq Htrco Hto Hexec2.
apply (dec_not_not _ (exec_decidable _ _)); [].
intro Hnexec1.
destruct (to_irreflex H i1); auto; [].
eapply to_trans; eauto; [].
eexists; eauto; done.
Qed.


Lemma to_cons_nexec :
  forall H h i i',
    trco (H; h)
    -> executes h i
    -> to (H; h) i i'
    -> ~ exec H i'.
Proof.
intros H h i i' Htrco Hexecutes Hto Hexec.
destruct (to_irreflex (H; h) i); [].
eapply to_trans; eauto; [].
apply (to_from_halves _ H (nil; h)); auto; [].
eapply executes_exec; eauto; [].
left; reflexivity.
Qed.


Lemma to_tail_gen :
  forall H h i1 i2,
    ~ executes h i1
    -> to (H; h) i1 i2
    -> to H i1 i2.
Proof.
intros H h i1 i2 Hnexecutes Hto.
destruct Hto as (H1 & H2 & Heq & Hexec & Hnexec).
so (app_eq_cons _#5 Heq) as [(H2' & _ & Heq') | (_ & Heq')].
  exists H1, H2'; auto; done.

  rewrite -> Heq' in Hexec.
  so (exec_invert _ _ Hexec) as (h' & Hin & Hexecutes).
  destruct Hin as [Heq'' | Hin].
    subst; contradiction.

    exists H, nil.
    repeat2 split; auto; [|].
      eapply executes_exec; eauto; done.

      contradict Hnexec.
      rewrite -> Heq'.
      apply exec_cons_incl; assumption.
Qed.


Lemma to_tail :
  forall H h i1 i2,
    ~ (exists i, h = ev_exec i)
    -> ~ (exists iw ir, h = ev_rf iw ir)
    -> to (H; h) i1 i2
    -> to H i1 i2.
Proof.
intros H h i1 i2 Hneqexec Hneqrf Hto.
eapply to_tail_gen; eauto.
intro Hexecutes.
invert Hexecutes; [|].
  intros ->.
  destruct Hneqexec; eauto; done.

  intros (? & ->).
  destruct Hneqrf; eauto; done.
Qed.


(* XX this really should be i2 execed now, not i1. *)
Lemma to_execed_tail :
  forall H h i1 i2,
    trco (H; h)
    -> exec H i2
    -> to (H; h) i1 i2
    -> to H i1 i2.
Proof.
intros H h i1 i2 Htrco Hexec Hto.
eapply to_tail_gen; eauto.
intro.
eapply (to_irreflex _ i1); eauto; [].
eapply to_trans; eauto; [].
apply (to_from_halves _ H (nil; h)); auto; [].
eapply executes_exec; eauto; [].
left; reflexivity.
Qed.


Lemma to_execed_truncate :
  forall H H' i1 i2,
    trco (H;; H')
    -> exec H i2
    -> to (H;; H') i1 i2
    -> to H i1 i2.
Proof.
intros H H' i1 i2 Htrco Hexec2 Hto.
induction H'.

(* nil *)
assumption.

(* cons *)
autorewrite with canonlist in *.
apply IHH'; [|].
  prove_trco.

  eapply to_execed_tail; eauto; [].
  apply exec_app_incl; assumption.
Qed.


Lemma toq_execed_truncate :
  forall H H' i1 i2,
    trco (H;; H')
    -> exec H i2
    -> toq (H;; H') i1 i2
    -> toq H i1 i2.
Proof.
intros H H' i1 i2 Htrco Hexec2 Htoq.
destruct Htoq as [Heq | Hto].
  subst; left; reflexivity.

  right; eapply to_execed_truncate; eauto; done.
Qed.


(* Reads-from *)

Lemma rf_twice :
  forall H1 H2 H3 i1 i2 i,
    ~ trco (H1; ev_rf i1 i;; H2; ev_rf i2 i;; H3).
Proof.
intros H1 H2 H3 i1 i2 i Htrco.
invert (trco_truncate _ _ Htrco).
intros ? Htrco12 _ _ _ Hnexec.
destruct Hnexec.
eapply exec_rf; [].
apply in_or_app; right; left; reflexivity.
Qed.


Lemma rf_fun :
  forall H i1 i2 i,
    trco H
    -> rf H i1 i
    -> rf H i2 i
    -> i1 = i2.
Proof.
intros H i1 i2 i Htrco Hrf1 Hrf2.
destruct (in_split_2 _#4 Hrf2 Hrf1) as [(H3 & H2 & H1 & Heq) | [ (Heq & _) | (H3 & H2 & H1 & Heq)]].
  exfalso.
  subst H.
  eapply rf_twice; eauto; done.

  injection Heq; auto; done.

  exfalso.
  subst H.
  eapply rf_twice; eauto; done.
Qed.


Lemma rf_wf_prop :
  forall H i i',
    trco H
    -> rf H i i'
    -> exists l,
        writesto H i l
        /\ reads H i' l.
Proof.
intros H i i' Htrco Hrf.
so (in_split _#3 Hrf) as (H2 & H1 & ->).
invert (trco_truncate _ _ Htrco).
intros l _ (v & Hwrite) Hread _ _.
exists l.
split.
  exists v.
  apply writes_app_incl; apply writes_cons_incl; assumption.

  apply reads_app_incl; apply reads_cons_incl; assumption.
Qed.


Lemma rf_isw_isr :
  forall H i i',
    trco H
    -> rf H i i'
    -> isw H i /\ isr H i'.
Proof.
intros H i i' Htrco Hrf.
pose proof (rf_wf_prop _#3 Htrco Hrf) as (l & (v & Hinw) & Hinr).
split.
  do 2 eexists; eauto.

  eexists; eauto.
Qed.


Lemma rf_inited :
  forall H i i',
    trco H
    -> rf H i i'
    -> inited H i /\ inited H i'.
Proof.
intros H i i' Htrco Hrf.
so (rf_wf_prop _#3 Htrco Hrf) as (l & (v & His) & His').
split.
  eapply writes_inited; eauto; done.

  eapply reads_inited; eauto; done.
Qed.


Lemma rf_irreflex :
  forall H i,
    trco H
    -> ~ rf H i i.
Proof.
intros H i Htrco Hrf.
so (in_split _#3 Hrf) as (H2 & H1 & ->).
invert (trco_truncate _ _ Htrco).
intros _ _ _ _ Hexec Hnexec.
contradiction.
Qed.


Lemma rf_loc_1 :
  forall H i i' l,
    trco H
    -> rf H i i'
    -> writesto H i l
    -> reads H i' l.
Proof.
intros H i i' l Htrco Hrf Hwrite.
so (rf_wf_prop _#3 Htrco Hrf) as (l' & Hwrite' & Hread).
so (writesto_fun _#4 Htrco Hwrite Hwrite') as Heq.
subst l'.
assumption.
Qed.


Lemma rf_loc_2 :
  forall H i i' l,
    trco H
    -> rf H i i'
    -> reads H i' l
    -> writesto H i l.
Proof.
intros H i i' l Htrco Hrf Hread.
so (rf_wf_prop _#3 Htrco Hrf) as (l' & Hwrite & Hread').
so (reads_fun _#4 Htrco Hread Hread') as Heq.
subst l'.
assumption.
Qed.


Lemma rf_to :
  forall H i i',
    trco H
    -> rf H i i'
    -> to H i i'.
Proof.
intros H i1 i2 Htrco Hrf.
so (in_split _#3 Hrf) as (H2 & H1 & ->).
invert (trco_truncate _ _ Htrco); [].
intros _ _ _ _ Hexec _ _.
eapply to_from_before; eauto; done.
Qed.


Lemma rf_execed :
  forall H i i',
    trco H
    -> rf H i i'
    -> exec H i /\ exec H i'.
Proof.
intros H i1 i2 Htrco Hrf.
so (in_split _#3 Hrf) as (H2 & H1 & Heq).
invert (trco_truncate _ _ (eqconv Heq Htrco)).
intros _ _ _ _ Hexec _.
subst H.
split.
  apply exec_app_incl; apply exec_cons_incl; assumption.

  eapply exec_rf; eauto; done.
Qed.


Lemma rf_execed_fst :
  forall H i i',
    trco H
    -> rf H i i'
    -> exec H i.
Proof.
intros.
refine (rf_execed _#5 andel); eauto; done.
Qed.


Lemma rf_execed_snd :
  forall H i i',
    trco H
    -> rf H i i'
    -> exec H i'.
Proof.
eapply rf_execed; eauto; done.
Qed.


Lemma rf_loc_fun :
  forall H i i' l l',
    trco H
    -> rf H i i'
    -> writesto H i l
    -> reads H i' l'
    -> l = l'.
Proof.
intros H i1 i2 l1 l2 Htrco Hrf Hwrite Hread.
so (rf_wf_prop _#3 Htrco Hrf) as (l & Hwrite' & Hread').
so (writesto_fun _#4 Htrco Hwrite Hwrite') as Heq1.
so (reads_fun _#4 Htrco Hread Hread') as Heq2.
subst; reflexivity.
Qed.


Lemma rf_execed_tail :
  forall H h i1 i2,
    trco (H; h)
    -> exec H i2
    -> rf (H; h) i1 i2
    -> rf H i1 i2.
Proof.
intros H h i1 i2 Htrco Hexec Hrf.
destruct Hrf as [Heq | Hrf]; auto; [].
subst h.
invert Htrco.
intros _ _ _ _ _ Hnexec.
contradiction.
Qed.


Lemma trco_rf_invert :
  forall H iw ir,
    trco (H; ev_rf iw ir)
    -> exists l,
         writesto H iw l
         /\ reads H ir l
         /\ exec H iw.
Proof.
intros H iw ir Htrco.
invert Htrco; eauto.
Qed.


(* Read-writes-from *)

Lemma rwf_rf :
  forall H i i', rwf H i i' -> rf H i i'.
Proof.
intros H i i' (Hrf & _).
assumption.
Qed.


Lemma rwf_isw_isr :
  forall H i i',
    trco H
    -> rwf H i i'
    -> isw H i /\ isw H i' /\ isr H i'.
Proof.
intros H i i' Htrco Hrwf.
destruct Hrwf as (Hrf & (l & v & His)).
repeat2 split.
  exact (rf_isw_isr _#3 Htrco Hrf andel).

  exists l, v; auto using writes_rw; done.

  exists l; eauto using reads_rw; done.
Qed.


Lemma rwfp_isw_isr :
  forall H i i',
    trco H
    -> rwfp H i i'
    -> isw H i /\ isw H i' /\ isr H i'.
Proof.
intros H i i' Htrco Hrwfp.
split.
  destruct Hrwfp as (? & (Hrf & _) & _).
  exact (rf_isw_isr _#3 Htrco Hrf andel).

  so (plus_plusr _#4 Hrwfp) as (? & _ & Hrwf).
  exact (rwf_isw_isr _#3 Htrco Hrwf ander).
Qed.


Lemma rwf_loc_1 :
  forall H i i' l,
    trco H
    -> rwf H i i'
    -> writesto H i l
    -> writesto H i' l.
Proof.
intros H i i' l Htrco (Hrf & (l' & v & His)) Hwrite.
exists v.
apply writes_rw; [].
replace l with l'; [assumption |].
#2 apply (reads_fun H i' l' l); auto.
  eapply @reads_rw; eauto; done.

  eapply rf_loc_1; eauto; done.
Qed.


Lemma rwf_loc_2 :
  forall H i i' l,
    trco H
    -> rwf H i i'
    -> writesto H i' l
    -> writesto H i l.
Proof.
intros H i i' l Htrco Hrwf Hwrite.
apply (rf_loc_2 _ _ i'); auto using rwf_rf; [].
apply writesto_isr; auto.  
exact (rwf_isw_isr _#3 Htrco Hrwf ander ander).
Qed.


Lemma rwfs_loc_2 :
  forall H i i' l,
    trco H
    -> rwfs H i i'
    -> writesto H i' l
    -> writesto H i l.
Proof.
intros H i i' l Htrco Hrwfs Hwrite.
revert Hwrite.
induct Hrwfs.
  auto; done.

  eauto using rwf_loc_2; done.
Qed.


Lemma rwf_hb :
  forall H i i',
    trco H
    -> rwf H i i'
    -> vopo H i i'.
Proof.
intros H i i' Htrco Hrwf.
destruct Hrwf as (Hrf & His).
so (rf_wf_prop _#3 Htrco Hrf) as (l & Hwrite & Hread).
left.
apply plus_one.
right.
left.
eauto.
Qed.

Lemma rwf_writesto :
  forall H i i',
    rwf H i i'
    -> exists l, writesto H i' l.
  intros H i i' Hrwf.
  unfold rwf in Hrwf.
  unfold writesto.
  destruct Hrwf as (Hrf & l' & v' & His).
  exists l', v'.
  apply writes_rw; auto.
Qed.

Lemma rwf_co :
  forall H i i',
    trco H
    -> rwf H i i'
    -> co H i i'.
Proof.
  intros H i i' Htrco Hrwf.

  assert (exists l, writesto H i' l) as Hwritesto. {
    eapply rwf_writesto; eauto.
  }

  destruct Hwritesto as (l & Hwritesto).
  eapply co_ww.
  apply rwf_hb; auto.
  eapply rwf_loc_2; eauto.
  auto.
Qed.

Lemma rwfs_cos :
  forall H i i',
    trco H
    -> rwfs H i i'
    -> cos H i i'.
Proof.
intros H i i' Htrco H0.
apply (star_mono _ (rwf H)); auto using rwf_co.
Qed.


Lemma rwfp_cop :
  forall H i i',
    trco H
    -> rwfp H i i'
    -> cop H i i'.
Proof.
intros H i i' Htrco H0.
apply (plus_mono _ (rwf H)); auto using rwf_co.
Qed.


Lemma rwf_fun_2 :
  forall H i i1 i2,
    trco H
    -> acyclic (co H)
    -> rwf H i i1
    -> rwf H i i2
    -> i1 = i2.
Proof.
intros H i i1 i2 Htrco Hcoacy Hrwf1 Hrwf2.
so (eq_ident_dec i1 i2) as [| Hneq]; auto; [].
exfalso.
destruct Hcoacy.
exists i1, i2; split.
- eapply co_atm_after; eauto using rwf_co.
- apply star_one; [].
  eapply co_atm_after; eauto using rwf_co; done.
Qed.

Lemma rwfs_co_group :
  forall H i1 i2 i,
    trco H
    -> rwfs H i1 i2
    -> co H i1 i
    -> (rwfp H i1 i /\ rwfs H i i2) \/ co H i2 i.
Proof.
intros H i1 i2 i Htrco Hrwfs Hco.
revert Hco.
induct Hrwfs.

(* refl *)
intros i' Hco.
right; assumption.

(* step *)
intros i1 i2 i3 Hrwf Hrwfs IH Hco.
so (eq_ident_dec i i2) as [Heq | Hneq].
  subst i2.
  left; split; auto; [].
  apply plus_one; assumption.

  #2 lapply IH.
    intros [(Hrwfp2 & Hrwfs3) | Hco'].
      left.
      split; auto; [].
      eapply plus_trans; eauto; [].
      apply plus_one; assumption.
      
      right; assumption.

    eapply co_atm_after; eauto; done.
Qed.


Lemma rwfs_cop_group :
  forall H i1 i2 i,
    trco H
    -> rwfs H i1 i2
    -> cop H i1 i
    -> (rwfp H i1 i /\ rwfs H i i2) \/ cop H i2 i.
Proof.
intros H i1 iz i Htrco Hrwfs Hcop.
revert Hrwfs.
so (plus_plusi _#4 Hcop) as Hcop'; clear Hcop.
induct Hcop'.

(* one *)
intros i1 i2 H12 H2z.
so (rwfs_co_group _#4 Htrco H2z H12) as [(H12' & H2z') | Hcop].
  left; auto; done.

  right; apply plus_one; auto; done.

(* step *)
intros i1 i2 i3 H12 H23 IH Hrwfs.
so (rwfs_co_group _#4 Htrco Hrwfs H12) as [(H12' & H2z) | Hcop].
  so (IH H2z) as [(H23' & H3z) | Hcop].
    left; split; auto; [].
    eapply plus_trans; eauto; done.

    right; assumption.

  right.
  exists i2; split; auto; [].
  apply plus_star; [].
  apply plusi_plus; auto; done.
Qed.


Lemma isr_isw_rw:
  forall H i,
    trco H
    -> isr H i
    -> isw H i
    -> H {{ ev_is i (ac_rw le ve) | le ve }}.
Proof.
intros H i Htrco Hisr Hisw.
destruct Hisr as (l & Hread).
destruct Hisw as (l' & v & Hwrite).
#2 invert Hread.
  intros m His.
  #2 invert Hwrite.
    intros m' His'.
    so (is_fun _#4 Htrco His His') as Heq.
    discriminate Heq.

    eauto; done.

  eauto; done.
Qed.


Lemma rf_isw_rwf :
  forall H i i',
    trco H
    -> rf H i i'
    -> isw H i'
    -> rwf H i i'.
Proof.
intros H i i' Htrco Hrf Hisw.
so (rf_isw_isr _#3 Htrco Hrf) as (_ & Hisr).
so (isr_isw_rw _ _ Htrco Hisr Hisw) as His.
split; auto; done.
Qed.


Lemma rwf_cop_cos :
  forall H i1 i2 i3,
    trco H
    -> rwf H i1 i2
    -> cop H i1 i3
    -> cos H i2 i3.
Proof.
intros H i1 i2 i3 Htrco Hrwf Hcop.
destruct Hcop as (i4 & Hco & Hcos).
eapply star_trans; eauto; [].
#2 so (eq_ident_dec i2 i4) as [Heq | Hneq].
  subst; apply star_refl; done.

  apply star_one; [].
  eapply co_atm_after; eauto; done.
Qed.


Lemma rwf_chain_trichot :
  forall H i i' id,
    trco H
    -> rwfs H i id
    -> rwfs H i' id
    -> rwfp H i i' \/ i = i' \/ rwfp H i' i.
Proof.
intros H i i' id Htrco Hrwfs Hrwfs'.
revert i' Hrwfs'.
induct Hrwfs.

(* refl *)
intros i iz Hz.
so (star_plus _#4 Hz) as [Heq | Hz'].
  subst; right; left; reflexivity.

  right; right; assumption.

(* step *)
intros i1 i2 i3 H12 _ IH iz Hz3.
destruct (IH _ Hz3) as [H2z | [Heq | Hz2]].
  left.
  eapply plus_trans; eauto using plus_one; done.

  subst i2.
  left.
  apply plus_one; auto; done.

  so (plus_plusr _#4 Hz2) as (i4 & Hz4 & H42).
  assert (i1 = i4) by (apply (rf_fun H _ _ i2); auto using rwf_rf).
  subst i4.
  so (star_plus _#4 Hz4) as [Heq | H42'].
    subst; right; left; reflexivity.

    right; right; assumption.
Qed.


Lemma rwfs_last :
  forall H i1 i2 i3,
    trco H
    -> acyclic (co H)
    -> rwfs H i1 i3
    -> rwfs H i1 i2
    -> ~ (exists i, rwf H i3 i)
    -> rwfs H i2 i3.
Proof.
intros H i1 iz i3 Htrco Hcoacy H13 H23 Hlast.
revert H23 Hlast.
induct H13.

(* refl *)
intros i1 H1z Hlast.
so (star_plus _#4 H1z) as [Heq | H1z'].
  subst; apply star_refl; done.

  destruct Hlast.
  destruct H1z' as (i3 & Hrwf & _).
  eauto; done.

(* step *)
intros i1 i2 i3 H12 H23 IH H1z Hlast.
so (star_plus _#4 H1z) as [Heq | H1z'].
  subst iz.
  eapply star_step; eauto; done.

  apply IH; auto; [].
  destruct H1z' as (i4 & H14 & H4z).
  thus (i2 = i4) by rwf_fun_2.
  subst i4.
  assumption.
Qed.

(* Visibility order *)

Lemma vo_inited_fst :
  forall H i i',
    trco H
    -> vo H i i'
    -> inited H i.
Proof.
  intros H i i' Htrco Hvo.
  destruct Hvo as [(Hvo & Hpo) | [Hrf | [ [(Hpush & Hpo) | (Hisvol1 & Hisvol2 & Hpo) ] | [ Hrelvo | [ Hacqvo | Hpushvo]]]]].
  - apply (so_inited H i i' (so_vo Hpo Hvo) andel).
  - exact (rf_inited _#3 Htrco Hrf andel).
  - apply (so_inited H i i' (so_push Hpo Hpush) andel).
  - apply (so_inited H i i' (so_vol Hpo Hisvol1 Hisvol2) andel).
  - destruct Hrelvo as (Hisrelw & Hpo).
    destruct (po_init H i i' Hpo) as (p & Hi & Hi').
    exists p. auto.
  - destruct Hacqvo as (Hisacqr & Hpo).
    destruct (po_init H i i' Hpo) as (p & Hi & Hi').
    exists p. auto.
  - destruct Hpushvo as (i'' & i''' & Hpush1 & Hpush2 & Hto).
    + eapply to_inited; eauto.
Qed.

Lemma vop_inited_fst :
  forall H i i',
    trco H
    -> vop H i i'
    -> inited H i.
Proof.
intros H i i' Htrco Hvvop.
destruct Hvvop as (? & ? & _).
eapply vo_inited_fst; eauto.
Qed.


(* Visible-to *)

Lemma vo_vt :
  forall H i i', vo H i i' -> vt H i i'.
Proof.
intros H i i' Hvo.
apply plus_one; assumption.
Qed.

Lemma vop_vt :
  forall H i i', vop H i i' -> vt H i i'.
Proof.
  eauto.
Qed.


Lemma rf_vt :
  forall H i i', rf H i i' -> vt H i i'.
Proof.
intros H i i' Hrf.
apply vo_vt; [].
right; left; assumption.
Qed.


Lemma wrp_rf_cos :
  forall H iw iw' ir l,
    trco H
    -> writesto H iw l 
    -> writesto H iw' l 
    -> vopo H iw ir
    -> rf H iw' ir
    -> cos H iw iw'.
Proof.
intros H iw iw' ir l Htrco Hwritestoiw Hwritestoiw' Hwrp Hrf.
so (eq_ident_dec iw iw') as [Heq | Hneq].
subst; apply star_refl; done.
apply star_one; [].
eapply co_wr; eauto.
destruct (rf_wf_prop H iw' ir Htrco Hrf) as (l' & Hwrites & Hreads).
rewrite <- (writesto_fun H iw' l'); eauto.
Qed.


Lemma vos_vt_trans :
  forall H i1 i2 i3,
    vos H i1 i2
    -> vt H i2 i3
    -> vt H i1 i3.
Proof.
intros H i1 i2 i3 Hvvos Hvt.
eapply star_plus_trans; eauto.
Qed.


Lemma rf_po_contra :
  forall H i i',
    trco H
    -> acyclic (co H)
    -> rf H i i'
    -> po H i' i
    -> False.
Proof.
intros H i i' Htrco Hcoacy Hrf Hpo.
so (rf_wf_prop _#3 Htrco Hrf) as (l & Hwritesto & Hread).
apply Hcoacy.
exists i.
eapply plus_one.
eapply co_rw; eauto. left. eapply plus_one. disj 1. auto.
Qed.

(* Coherence order *)

Lemma isw_writesto :
  forall H i,
    isw H i
    -> exists l, writesto H i l.
Proof.
  unfold isw.
  intros ? ? (l & v & Hwrites).
  exists l, v.
  auto.
Qed.

Lemma isrw_writesto :
  forall H i,
    isrw H i
    -> exists l, writesto H i l.
Proof.
  unfold isrw.
  intros ? ? (l & v & His).
  apply isw_writesto.
  exists l, v.
  auto using writes_rw.
Qed.

Lemma co_wf_prop :
  forall H i i',
    trco H
    -> co H i i'
    -> exists l,
         writesto H i l
         /\ writesto H i' l.
Proof.
intros H i i' Htrco Hco.
revert Htrco.
induct Hco; try (intros; exists l; auto; done).
- (* co_wr *)
  intros H i1 i2 l ir Hhb Hrf Hwritesto1 Hreads Hneq Htrco.
  exists l.
  intuition.
  destruct (rf_wf_prop H i2 ir Htrco Hrf) as (l' & Hwritesto2 & Hreads2).
  erewrite reads_fun; eauto.
- (* co_atm_after *)
  intros ? ? ? ? Hrwf Hco IH Hneq Htrco.
  destruct (IH Htrco) as (l & Hwritestoiw1 & Hwritestoiw2).
  exists l.
  split; auto.
  destruct (rwf_writesto H iw1 irw Hrwf) as (l' & Hwritestoirw).
  eapply rwf_loc_1; eauto.
Qed.

Lemma co_wf_prop_1 :
  forall H i i' l v,
    trco H
    -> co H i i'
    -> writes H i l v
    -> writesto H i' l.
Proof.
intros H i1 i2 l v Htrco Hco Hexec.
so (co_wf_prop _#3 Htrco Hco) as (l' & (v1 & Hexec1) & (v2 & Hexec2)).
exists v2.
so (writes_fun _#6 Htrco Hexec Hexec1) as (Heq, _).
subst; auto.
Qed.


Lemma co_wf_prop_2 :
  forall H i i' l v,
    trco H
    -> co H i i'
    -> writes H i' l v
    -> writesto H i l.
Proof.
intros H i1 i2 l v Htrco Hco Hexec.
so (co_wf_prop _#3 Htrco Hco) as (l' & (v1 & Hexec1) & (v2 & Hexec2)).
exists v1.
so (writes_fun _#6 Htrco Hexec Hexec2) as (Heq, _).
subst; auto.
Qed.


Lemma co_loc_1 :
  forall H i i' l,
    trco H
    -> co H i i'
    -> writesto H i l
    -> writesto H i' l.
Proof.
intros H i1 i2 l Htrco Hcos Hwrite1.
destruct Hwrite1 as (v & His1).
eapply co_wf_prop_1; eauto; done.
Qed.


Lemma co_loc_2 :
  forall H i i' l,
    trco H
    -> co H i i'
    -> writesto H i' l
    -> writesto H i l.
Proof.
intros H i1 i2 l Htrco Hcos Hwrite2.
destruct Hwrite2 as (v & His2).
eapply co_wf_prop_2; eauto; done.
Qed.


Lemma cos_wf_prop_1 :
  forall H i i' l v,
    trco H
    -> cos H i i'
    -> writes H i l v
    -> writesto H i' l.
Proof.
intros H i i' l v Htrco Hcos Hexec.
assert (writesto H i l) as Hexec' by (eexists; eauto).
clear Hexec.
induction Hcos.
(* refl *)
assumption.

(* step *)
destruct Hexec'; eauto.
eapply IHHcos.
eapply co_wf_prop_1; eauto.
Qed.


Lemma cos_wf_prop_2 :
  forall H i i' l v,
    trco H
    -> cos H i i'
    -> writes H i' l v
    -> writesto H i l.
Proof.
intros H i i' l v Htrco Hcos Hwrite.
assert (writesto H i' l) as Hwrite' by (eexists; eauto).
clear Hwrite.
so (star_starr _#4 Hcos) as Hcos'; clear Hcos.
induction Hcos'.
(* refl *)
assumption.

(* step *)
destruct Hwrite'; eauto.
eapply IHHcos'.
eapply co_wf_prop_2; eauto.
Qed.


Lemma cos_loc_2 :
  forall H i i' l,
    trco H
    -> cos H i i'
    -> writesto H i' l
    -> writesto H i l.
Proof.
intros H i1 i2 l Htrco Hcos Hwrite2.
destruct Hwrite2 as (v & His2).
eapply cos_wf_prop_2; eauto; done.
Qed.


Lemma cop_wf_prop :
  forall H i i',
    trco H
    -> cop H i i'
    -> exists l,
        writesto H i l
        /\ writesto H i' l.
Proof.
intros H i i' Htrco Hcop.
thus (plusi (co H) i i') as HH by plus_plusi; clear Hcop; rename HH into Hcop.
elim Hcop; clear i i' Hcop.
(* nil *)
intros.
apply co_wf_prop; auto; done.

(* cons *)
intros i1 i2 i3 Hco _ IH.
so (co_wf_prop _#3 Htrco Hco) as (l & (v1 & His1) & (v2 & His2)).
destruct IH as (l' & (v2' & His2') & (v3 & His3)).
so (writes_fun _#6 Htrco His2 His2') as (Heq2, _).
subst l'.
exists l.
splitall; repeat eexists; eauto.
Qed.


Lemma cop_wf_prop_1 :
  forall H i i' l v,
    trco H
    -> cop H i i'
    -> writes H i l v
    -> writesto H i' l.
Proof.
intros.
eapply cos_wf_prop_1; eauto.
apply plus_star.
assumption.
Qed.


Lemma co_isw :
  forall H i i',
    trco H
    -> co H i i'
    -> isw H i /\ isw H i'.
Proof.
intros H i i' Htrco Hco.
pose proof (co_wf_prop _#3 Htrco Hco) as (l & (v & Hin) & (v' & Hin')).
split; do 2 eexists; eauto.
Qed.

 
Lemma cop_isw :
  forall H i i',
    trco H
    -> cop H i i'
    -> isw H i /\ isw H i'.
Proof.
intros H i i' Htrco Hcop.
split.
  destruct Hcop as (i'' & Hco & _).
    exact (co_isw _#3 Htrco Hco andel).

    pose proof (plus_plusr _#4 Hcop) as (i'' & _ & Hco).
    exact (co_isw _#3 Htrco Hco ander).
Qed.


Lemma cos_isw_1 :
  forall H i i',
    trco H
    -> cos H i i'
    -> isw H i
    -> isw H i'.
Proof.
intros H i i' Htrco Hcos Hisw.
pose proof (star_starr _#4 Hcos) as Hcos'.
destruct Hcos'.
  assumption.

  eapply co_isw; eauto.
Qed.


Lemma cos_isw_2 :
  forall H i i',
    trco H
    -> cos H i i'
    -> isw H i'
    -> isw H i.
Proof.
intros H i i' Htrco Hcos Hisw.
destruct Hcos.
  assumption.

  refine (co_isw _#5 andel); eauto.
Qed.



Lemma co_inited :
  forall H i i',
    trco H
    -> co H i i'
    -> inited H i /\ inited H i'.
Proof.
intros H i i' Htrco Hco.
so (co_wf_prop _#3 Htrco Hco) as (l & (v & His) & (v' & His')).
split.
  eapply writes_inited; eauto; done.

  eapply writes_inited; eauto; done.
Qed.


Lemma cop_inited :
  forall H i i',
    trco H
    -> cop H i i'
    -> inited H i /\ inited H i'.
Proof.
intros H i i' Htrco Hcop.
split.
  destruct Hcop as (? & Hco & _).
  exact (co_inited _#3 Htrco Hco andel).

  so (plus_plusr _#4 Hcop) as (? & _ & Hco).
  eapply co_inited; eauto; done.
Qed.

(* Universal supersets *)

Fixpoint ids (H : history) {struct H} :=
  (match H with
   | nil => nil
   | h :: t =>
       (match h with
        | ev_init i _ => i :: ids t
        | _ => ids t
        end)
   end).


Fixpoint locs (H : history) {struct H} :=
  (match H with
   | nil => nil
   | h :: t =>
       (match h with
        | ev_is _ (ac_read l _) => l :: locs t
        | ev_is _ (ac_write l _ _) => l :: locs t
        | _ => locs t
        end)
   end).


Lemma init_ids :
  forall H i,
    H {{ ev_init i p | p }}
    -> In i (ids H).
Proof.
intros M i (p & Hin).
induction M as [| h M].
(* nil *)
destruct Hin.

(* cons *)
simpl in Hin.
destruct Hin as [Heq | Hin'].
  subst h.
  simpl; left; auto.

  pose proof (IHM Hin') as Hin''.
  simpl; destruct h; auto.
  simpl; right; auto.
Qed.


Lemma is_ids :
  forall H i a,
    trco H
    -> H {{ ev_is i a }}
    -> In i (ids H).
Proof.
intros H i a Htrco Hin.
thus (H {{ ev_init i p | p }}) as Hin' by is_inited.
apply init_ids; auto.
Qed.


Lemma reads_ids :
  forall H i l,
    trco H
    -> reads H i l
    -> In i (ids H).
Proof.
intros H i l Htrco Hreads.
invert Hreads; intros; eapply is_ids; eauto.
Qed.


Lemma writes_ids :
  forall H i l v,
    trco H
    -> writes H i l v
    -> In i (ids H).
Proof.
intros H i l v Htrco Hwrites.
invert Hwrites; intros; eapply is_ids; eauto.
Qed.


Lemma exec_ids :
  forall H i,
    trco H
    -> exec H i
    -> In i (ids H).
Proof.
intros H i Htrco Hexec.
so (exec_is _ _ Htrco Hexec) as (a & His).
eapply is_ids; eauto.
Qed.


Lemma po_ids :
  forall H i i',
    po H i i' -> In i (ids H) /\ In i' (ids H).
Proof.
intros H i i' Hpo.
pose proof (po_init _#3 Hpo) as (p & Hi & Hi').
split; apply init_ids; eexists; eassumption.
Qed.

Lemma pop_ids :
  forall H i i',
    pop H i i' -> In i (ids H) /\ In i' (ids H).
Proof.
intros H i i' Hpop.
pose proof (pop_init _#3 Hpop) as (p & Hi & Hi').
split; apply init_ids; eexists; eassumption.
Qed.


Lemma to_ids :
  forall H i i',
    trco H -> to H i i' -> In i (ids H).
Proof.
intros H i i' Htrco Hto.
apply exec_ids; auto; [].
eapply to_execed_fst; eauto; done.
Qed.


Lemma rf_ids :
  forall H i i',
    trco H -> rf H i i' -> In i (ids H) /\ In i' (ids H).
Proof.
intros H i i' Htrco Hrf.
so (rf_wf_prop _#3 Htrco Hrf) as (l & (v & Hwrite) & Hread).
split.
  eapply writes_ids; eauto; done.

  eapply reads_ids; eauto; done.
Qed.


Lemma co_ids :
  forall H i i',
    trco H -> co H i i' -> In i (ids H) /\ In i' (ids H).
Proof.
intros H i i' Htrco Hco.
pose proof (co_wf_prop _#3 Htrco Hco) as (l & (v & Hwrite) & (v' & Hwrite')).
split; eapply writes_ids; eauto.
Qed.


Lemma so_ids :
  forall H i i',
    so H i i' -> In i (ids H) /\ In i' (ids H).
Proof.
intros H i i' Hso.
apply po_ids.
eapply so_po; eassumption.
Qed.


Lemma push_ids :
  forall H i i',
    trco H
    -> push H i i'
    -> In i (ids H) /\ In i' (ids H).
Proof.
intros H i i' Htrco Hpush.
destruct Hpush as [(_, Hpo) | (_ & _ & Hpo) ];
  eapply po_ids; eauto; done.
Qed.

Lemma vo_ids :
  forall H i i',
    trco H
    -> vo H i i' 
    -> In i (ids H).
Proof.
intros H i i' Htrco Hvo.
destruct Hvo as [(_ & Hpo) | [Hrf | [ [(_ & Hpo) | (_ & _ & Hpo) ] | [ (_ & Hpo) | [ (_ & Hpo) |  Hpushvo]]]]];
  try (destruct (po_ids H i i' Hpo); eauto).
- refine (rf_ids _#3 _ _ andel); eauto; done.
- destruct Hpushvo as (i'' & i''' & _ & _ & Hto).
  eapply to_ids; eauto.
Qed.

Lemma in_locs_cons :
  forall H h l,
    In l (locs H) -> In l (locs (H; h)).
Proof.
intros M h l Hin.
simpl; destruct h; try (destruct t); auto; simpl; right; auto.
Qed.


Lemma write_locs :
  forall H l m,
    H {{ ev_is i (ac_write l v m) | i v }}
    -> In l (locs H).
Proof.
intros M l m H.
destruct H as (i & v & Hin).
induction M as [| h M].
(* nil *)
auto.

(* cons *)
simpl in Hin.
destruct Hin as [Heq | Hin].
  have (h = ev_is i (ac_write l v m)) as Heq.
  subst h.
  simpl; left; auto.

  have (M {{ ev_is i (ac_write l v m) }}) as Hin.
  pose proof (IHM Hin) as H.
  apply in_locs_cons; auto.
Qed.


Definition list_product {S T : Set} (l : list S) (l' : list T) : list (S * T) :=
  flat_map (fun x => map (fun y => (x, y)) l') l.


Lemma In_product :
  forall (S T : Set) (l : list S) (l' : list T) x y,
    In x l -> In y l' -> In (x, y) (list_product l l').
Proof.
intros S T l l' x y Hx Hy.
apply in_flat_map.
exists x.
split; [auto |].
apply in_map.
auto.
Qed.

Definition po_p H p i1 i2 := exists H1 H2 H3, H = H1;ev_init i1 p;;H2;ev_init i2 p;;H3.

Lemma pop_irreflex { H p i } :
  trco H
  -> ~ po_p H p i i.
Proof.
  intros Htrco Hpo_p.
  destruct Hpo_p as (H1 & H2 & H3 & Heq).
  eapply po_irreflex; eauto.
  exists H1, H2, H3, p.
  eauto.
Qed.

Lemma po_p_po {H p i1 i2 } : po_p H p i1 i2 -> po H i1 i2.
Proof.
  intros Hpo_p.
  destruct Hpo_p as (H1 & H2 & H3 & Heq).
  exists H1, H2, H3, p.
  auto.
Qed.

Ltac find_app_cons :=
  first [apply in_or_app; right; apply in_eq | 
         apply in_or_app; right; apply in_cons; find_app_cons].

(* TODO obviated by Decide.v once we get it and Truncate.v to go through *) 
Lemma pop_dec { H p i1 i2 } :
  trco H 
  -> po_p H p i1 i2 \/ ~ po_p H p i1 i2.
Proof.
  destruct (@in_dec event eq_event_dec (ev_init i1 p) H) as [ Hin1 | Hout1 ];
    destruct (@in_dec event eq_event_dec (ev_init i2 p) H) as [ Hin2 | Hout2 ].
  - destruct (in_split (ev_init i1 p) H) as (H2 & H1 & Heq); eauto.
    destruct (in_app_or H2 (H1; ev_init i1 p) (ev_init i2 p)) as [ HinH2 | Hinrest ]; [ rewrite <- Heq; auto | |].
    + left.
      apply in_split in HinH2.
      destruct HinH2 as (H4 & H3 & H2eq).
      rewrite H2eq in Heq.
      rewrite <- app_assoc in Heq.
      exists H1, H3, H4.
      auto.
    + destruct (eq_event_dec (ev_init i1 p) (ev_init i2 p)) as [ Heveq | Hevneq].
      * inversion Heveq.
        right.
        apply pop_irreflex; eauto.
      * destruct (in_inv Hinrest) as [Heveq | HinH1]; [ contradiction |].
        apply in_split in HinH1.
        destruct HinH1 as (H4 & H3 & H1eq).
        rewrite H1eq in Heq.
        right.
        intros Hpop.
        eapply po_irreflex; eauto.
        apply po_p_po in Hpop.
        eapply po_trans; eauto.
        exists H3, H4, H2, p.
        auto.
  - right.
    intros Hpo_p.
    destruct Hpo_p as (H1 & H2 & H3 & Heq).
    eapply Hout2.
    rewrite Heq.
    find_app_cons.
  - right.
    intros Hpo_p.
    destruct Hpo_p as (H1 & H2 & H3 & Heq).
    eapply Hout1.
    rewrite Heq.
    find_app_cons.
  - right.
    intros Hpo_p.
    destruct Hpo_p as (H1 & H2 & H3 & Heq).
    eapply Hout2.
    rewrite Heq.
    find_app_cons.
Qed.

Lemma po_npop_npo { H p1 i2 i3 }:
  trco H
  -> H {{ ev_init i2 p1 }} 
  -> ~ po_p H p1 i2 i3
  -> ~ po H i2 i3.
Proof.
  intros Htco Hpo Hpo_p Hnpo.
  apply Hpo_p.
  destruct Hnpo as (H1 & H2 & H3 & p2 & Heq).
  exists H1, H2, H3.
  rewrite (@init_unique H i2 p1 p2); auto.
  rewrite Heq.
  find_app_cons.
Qed.


Lemma reads_writes :
  forall H i ac,
    trco H
    -> H {{ ev_is i ac }} 
    -> (exists l, reads H i l) \/ (exists l, writesto H i l).
Proof.
  intros H i ac Htrco His.
  assert (isac ac) as Hisac. eauto using is_isac.
  destruct Hisac;
    [ left; exists l | | ];
    eauto using reads_read;
    right; exists l, v;
    eauto using writes_write, writes_rw.
Qed.
