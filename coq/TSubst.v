
Require Import Tactics.
Require Import Static.
Require Import Sequence.
Require Export TSubstGeneral.
Require Import Omega.



(* depends on static hints *)
Lemma ofs_behaved : 
  forall U, behaved (ofs U).
Proof.
intros U G i c Hc Hindex.
destruct Hc; simp_sub; replace (i+1) with (S i) by omega; auto with static.
Qed.


(* depends on static hints *)
Lemma ofd_behaved :
  forall U P, behaved (ofd U P).
Proof.
intros U P G i c Hc Hindex.
destruct Hc; simp_sub; replace (i+1) with (S i) by omega; eauto with static substlem.
Qed.


Lemma ofd_ofs :
  forall U P G t c,
    ofd U P G t c -> ofs U G t c.
Proof.
intros U P G t c H.
destruct H; auto with static substlem.
Qed.


Hint Resolve ofd_ofs : substlem.


Lemma subst_value :
  forall U P G1 s G2 v,
    subof (ofd U P) G1 s G2
    -> value G2 v
    -> value G1 (subst s v).
Proof.
intros U P G1 s G2 v Hsubof Hvalue.
revert Hsubof.
induct Hvalue; try (complete (intros; simp_sub; auto with static)).
(* var *)
intros G i t Hindex Hsubof.
simp_sub.
have (index i G (cl_vl t)) as Hindex.
have (subof (ofd U P) G1 s G) as Hsubof.
toshow (value G1 (project s i)).
pose proof (subof_index _ (ofd_behaved U P) _#5 iscl_vl Hsubof Hindex) as Hof.
have (ofd U P G1 (project s i) (subst (compose (sh (S i)) s) (cl_vl t))) as Hof.
invert Hof; auto.
Qed.


Lemma subst_value_wc :
  forall U P G1 s G2 v,
    subof (wc (ofd U P)) G1 s G2
    -> value G2 v
    -> value G1 (subst s v).
Proof.
intros U P G1 s G2 v Hsubof Hvalue.
eapply subst_value; eauto.
eapply subof_mono.
eapply (wc_elim (ofd U P)).
auto.
Qed.


Lemma subst_tg_wc :
  forall U G1 G2 s T,
    subof (wc (ofs U)) G1 s G2
    -> tgof U G2 T
    -> tgof U G1 (subst s T).
Proof.
intros U G1 G2 s t Hs Ht.
generalize dependent s.
generalize dependent G1.
induction Ht; intros G1 s Hs; simp_sub; auto with static substlem.
(* var *)
rename G into G2, H into Hindex.
have (index i G2 cl_tg) as Hindex.
have (subof (wc (ofs U)) G1 s G2) as Hs.
toshow (tgof U G1 (project s i)).
assert (subof (ofs U) G1 s G2) as Hs'
  by (apply (subof_mono (wc (ofs U)) (ofs U)); [apply wc_elim |]; auto).
pose proof (subof_index _ (ofs_behaved U) _#5 iscl_tg Hs' Hindex) as Hof.
have (ofs U G1 (project s i) (subst (compose (sh (S i)) s) cl_tg)) as Hof.
simp_sub in Hof.
inversion Hof; auto.
Qed.


Lemma subst_tp_wc :
  forall U G1 G2 s t,
    subof (wc (ofs U)) G1 s G2
    -> tpof G2 t
    -> tpof G1 (subst s t).
Proof.
intros U G1 G2 s t Hs Ht.
generalize dependent s.
generalize dependent G1.
induction Ht; intros G1 s Hs; simp_sub; auto with static substlem.
Qed.


Lemma subst_fc_wc :
  forall U G1 G2 s f,
    subof (wc (ofs U)) G1 s G2
    -> fcof U G2 f
    -> fcof U G1 (subst s f).
Proof.
intros U G1 G2 s f Hs Hf.
generalize dependent s.
generalize dependent G1.
induction Hf; intros G1 s Hf; simp_sub; eauto using subst_tg_wc with static substlem.
Qed.


Lemma subst_init :
  forall s e,
    init e
    -> init (subst s e).
Proof.
intros s e Hinit.
revert s.
induct Hinit;
intros; simp_sub; auto with static.
Qed.


Lemma subst_tm_xp_wc :
  (forall U P G1 G2 s m t,
     subof (wc (ofd U P)) G1 s G2
     -> tmof U P G2 m t
     -> tmof U P G1 (subst s m) (subst s t))
  /\
  (forall U P I G1 G2 s e t,
     subof (wc (ofd U P)) G1 s G2
     -> xpof U P I G2 e t
     -> xpof U P I G1 (subst s e) (subst s t)).
Proof.
#11 exploit
  (tmof_xpof_ind
     (fun U P G2 m t =>
        forall G1 s,
          subof (wc (ofd U P)) G1 s G2
          -> tmof U P G1 (subst s m) (subst s t))
     (fun U P I G2 e t =>
        forall G1 s,
          subof (wc (ofd U P)) G1 s G2
          -> xpof U P I G1 (subst s e) (subst s t))) as Hind;
  [.. | destruct Hind as (Htm & Hxp); repeat split; eauto; done];
try (intros; simp_sub; eauto with static; done).

(* var *)
intros U P G2 i t Hindex G1 s Hs.
simp_sub.
have (index i G2 (cl_vl t)) as Hindex.
have (subof (wc (ofd U P)) G1 s G2) as Hs.
assert (subof (ofd U P) G1 s G2) as Hs' by (apply (subof_mono (wc (ofd U P)) (ofd U P)); [apply wc_elim |]; auto).
toshow (tmof U P G1 (project s i) (subst (compose (sh (i + 1)) s) t)).
assert (ofd U P G1 (project s i) (subst (compose (sh (S i)) s) (cl_vl t))) as Hof
  by (eapply (subof_index (ofd U P) (ofd_behaved U P) _#5 iscl_vl Hs' Hindex); eauto).
simp_sub in Hof.
inversion Hof; auto; done.

(* loc *)
intros U P G2 l t Hlookup G1 s Hs.
simp_sub.
have (lookup l P t) as Hlookup.
toshow (tmof U P G1 (tm_loc l) (tp_ref (subst (compose (sh (length G2)) s) t))).
assert (tmof U P G1 (tm_loc l) (tp_ref (subst (sh (length G1)) t))) as Hof
  by apply (tmof_loc Hlookup).
thus (compose (sh (length G2)) s = sh (length G1)) as Hcomp by subof_sh_all.
rewrite -> Hcomp.
apply Hof; done.

(* lam *)
intros U P G2 m t1 t2 Ht1 Hm IHm G1 s Hs.
simp_sub.
exploit (subof_wc_bind (ofd U P) (ofd_behaved U P) G1 G2 s (cl_vl t1)) as Hs'; auto with static substlem.
pose proof (IHm _ _ Hs') as H; simp_sub in H.
apply tmof_lam.
  eapply subst_tp_wc; eauto with static substlem; done.
 
  simp_sub; auto; done.

(* fun *)
intros U P G2 m t1 t2 Ht1 Ht2 Hm IHm G1 s Hs.
simp_sub.
so (subof_wc_bind _ (ofd_behaved U P) _ _ _ (cl_vl (tp_arrow t1 t2)) iscl_vl Hs) as Hs'.
so (subof_wc_bind _ (ofd_behaved U P) _ _ _ (cl_vl (shift1 t1)) iscl_vl Hs') as Hs''.
simp_sub in Hs''.
so (IHm _ _ Hs'') as IHm'.
simp_sub in IHm'.
apply tmof_fun; [| |].
  eapply subst_tp_wc; eauto with static substlem; done.

  eapply subst_tp_wc; eauto with static substlem; done.

  simp_sub; assumption.

(* bind *)
intros U P I G2 t1 e1 e2 t2 Ht1 He1 IHe1 He2 IHe2 G1 s Hs.
simp_sub.
apply xpof_bind; [| |].
  eapply subst_tp_wc; eauto with static substlem; done.
 
  apply IHe1; assumption.

  simp_sub.
  exploit (subof_wc_bind (ofd U P) (ofd_behaved U P) G1 G2 s (cl_vl t1)) as Hs'; auto with static substlem.
  pose proof (IHe2 _ _ Hs') as He2'.
  simp_sub in He2'.
  exact He2'.

(* bind-init *)
intros U P I1 I2 G2 t1 e1 e2 t2 Hinit Ht1 He1 IHe1 He2 IHe2 G1 s Hs.
simp_sub.
apply xpof_bind_init; [| | |].
  apply subst_init; assumption.

  eapply subst_tp_wc; eauto with static substlem; done.
 
  apply IHe1; assumption.

  simp_sub.
  exploit (subof_wc_bind (ofd U P) (ofd_behaved U P) G1 G2 s (cl_vl t1)) as Hs'; auto with static substlem.
  pose proof (IHe2 _ _ Hs') as He2'.
  simp_sub in He2'.
  exact He2'.

(* spec *)
intros; simp_sub; eapply xpof_spec; try eapplyall; eauto using subst_value_wc; done.

(* rmw *)
intros U P G2 t m1 m2 Ht Hm1 IH1 Hm2 IH2 G1 s Hs.
simp_sub.
#3 apply xpof_rmw.
  eapply subst_tp_wc; eauto with static substlem; done.

  apply IH1; auto; done.

  simp_sub.
  exploit (subof_wc_bind (ofd U P) (ofd_behaved U P) G1 G2 s (cl_vl t)) as Hs'; auto with static substlem.
  so (IH2 _ _ Hs') as Hm2'.
  simp_sub in Hm2'.
  exact Hm2'.

(* action *)
intros U P G2 i t p G1 s Hs.
simp_sub.
toshow (xpof U P (nil; (i, (t, p))) G1 (xp_action i) (subst (compose (sh (length G2)) s) t)).
thus (xpof U P (nil; (i, (t, p))) G1 (xp_action i) (subst (sh (length G1)) t)) as Hof by @xpof_action.
thus (compose (sh (length G2)) s = sh (length G1)) as Hcomp by subof_sh_all.
rewrite -> Hcomp.
exact Hof.

(* newx *)
intros U P G2 e t b He IHe G1 s Hs.
simp_sub.
apply xpof_new.
simp_sub.
eexploit subof_wc_bind as Hs'; [apply ofd_behaved | apply iscl_tg | eexact Hs |].
eexploit subof_wc_bind as Hs''; [apply ofd_behaved | apply iscl_tg | eexact Hs' |].
have (subof (wc (ofd U P))
        (G1; subst s cl_tg; subst (dot (var 0) (compose s sh1)) cl_tg)
        (dot (var 0) (compose (dot (var 0) (compose s sh1)) sh1))
        (G2; cl_tg; cl_tg)) as Hs''.
pose proof (IHe _ _ Hs'') as H'.
simp_sub in H'.
exact H'.

(* fence *)
intros; simp_sub; eapply xpof_fence; try eapplyall; eauto using subst_fc_wc with static substlem; done.
Qed.


Lemma subst_tm_wc :
  forall U P G1 G2 s m t,
    subof (wc (ofd U P)) G1 s G2
    -> tmof U P G2 m t
    -> tmof U P G1 (subst s m) (subst s t).
Proof.
apply subst_tm_xp_wc.
Qed.


Lemma subst_xp_wc :
  (forall U P I G1 G2 s e t,
     subof (wc (ofd U P)) G1 s G2
     -> xpof U P I G2 e t
     -> xpof U P I G1 (subst s e) (subst s t)).
Proof.
apply subst_tm_xp_wc.
Qed.


Lemma subst_ofs_wc :
  forall U G1 G2 s t c,
    subof (wc (ofs U)) G1 s G2
    -> (ofs U) G2 t c
    -> (ofs U) G1 (subst s t) (subst s c).
Proof.
intros U G1 G2 s t c Hs Ht.
destruct Ht; simp_sub; eauto using subst_tm_wc, subst_tg_wc with static substlem.
Qed.


Lemma subst_ofd_wc :
  forall U P G1 G2 s t c,
    subof (wc (ofd U P)) G1 s G2
    -> ofd U P G2 t c
    -> ofd U P G1 (subst s t) (subst s c).
Proof.
intros U P G1 G2 s t c Hs Ht.
destruct Ht; simp_sub.
  eauto using subst_tm_wc, subst_tg_wc, subst_value_wc with static substlem.

  apply ofd_tg.
  eauto using subst_tm_wc, subst_tg_wc with static substlem.
Qed.


Lemma ofs_wc :
  forall U G t c,
    (ofs U) G t c -> wc (ofs U) G t c.
Proof.
intro U.
exact (wc_intro _ (subst_ofs_wc U)).
Qed.


Lemma ofd_wc :
  forall U P G t c,
    ofd U P G t c -> wc (ofd U P) G t c.
Proof.
intros U P.
exact (wc_intro _ (subst_ofd_wc U P)).
Qed.


Lemma subst_fc :
  forall U G1 G2 s f,
    subof (ofs U) G1 s G2
    -> fcof U G2 f
    -> fcof U G1 (subst s f).
Proof.
intros U G1 G2 s f Hs Hf.
eapply subst_fc_wc; eauto.
apply (subof_mono (ofs U) (wc (ofs U))); auto using ofs_wc.
Qed.


Lemma subst_tp :
  forall U G1 G2 s t,
    subof (ofs U) G1 s G2
    -> tpof G2 t
    -> tpof G1 (subst s t).
Proof.
intros U G1 G2 s t Hs Gt.
eapply subst_tp_wc; eauto.
apply (subof_mono (ofs U) (wc (ofs U))); auto using ofs_wc.
Qed.


Lemma subst_tm :
  forall U P G1 G2 s m t,
    subof (ofd U P) G1 s G2
    -> tmof U P G2 m t
    -> tmof U P G1 (subst s m) (subst s t).
Proof.
intros U P G1 G2 s m t Hs Hm.
eapply subst_tm_wc; eauto.
apply (subof_mono (ofd U P) (wc (ofd U P))); auto using ofd_wc.
Qed.


Lemma subst_xp :
  forall U P I G1 G2 s e t,
    subof (ofd U P) G1 s G2
    -> xpof U P I G2 e t
    -> xpof U P I G1 (subst s e) (subst s t).
Proof.
intros U P I G1 G2 s e t Hs He.
eapply subst_xp_wc; eauto.
apply (subof_mono (ofd U P) (wc (ofd U P))); auto using ofd_wc.
Qed.


Lemma subst_ac :
  forall U P G1 G2 s a t,
    subof (ofd U P) G1 s G2
    -> acof U P G2 a t
    -> acof U P G1 (subst s a) (subst s t).
Proof.
intros U P G1 G2 s a t Hs Ha.
revert Hs.
#3 elim Ha; clear U P G2 a t Ha; eauto with static substlem.
(* read *)
intros l U P G2 t H Hs.
simp_sub.
toshow (acof U P G1 (ac_read l) (subst (compose (sh (length G2)) s) t)).
thus (compose (sh (length G2)) s = sh (length G1)) as Hcomp by subof_sh_all.
rewrite -> Hcomp.
apply acof_read; auto.

(* write *)
intros U P G2 l v t Hlookup Hvalue Hof Hs.
simp_sub.
toshow (acof U P G1 (ac_write l (subst s v)) tp_unit).
thus (value G1 (subst s v)) as Hvalue' by subst_value.
thus (tmof U P G1 (subst s v) (subst s (subst (sh (length G2)) t))) as Hof' by subst_tm.
simp_sub in Hof'.
thus (compose (sh (length G2)) s = sh (length G1)) as Hcomp by subof_sh_all.
rewrite -> Hcomp in Hof'.
eapply acof_write; eauto.

(* rw *)
intros U P G2 l v t Hlookup Hvalue Hof Hs.
simp_sub.
thus (value G1 (subst s v)) as Hvalue' by subst_value.
thus (tmof U P G1 (subst s v) (subst s (subst (sh (length G2)) t))) as Hof' by subst_tm.
simp_sub in Hof'.
thus (compose (sh (length G2)) s = sh (length G1)) as Hcomp by subof_sh_all.
rewrite -> Hcomp.
rewrite -> Hcomp in Hof'.
eapply acof_rw; eauto.
Qed.


Lemma subst_fl :
  forall U G1 G2 s fl,
    subof (ofs U) G1 s G2
    -> flof U G2 fl
    -> flof U G1 (subst s fl).
Proof.
intros U G1 G2 s fl Hs Hfl.
induction Hfl; simp_sub; eauto using subst_fc with static.
Qed.


Hint Resolve subst_value subst_fc subst_fl subst_tp subst_tm subst_xp subst_ac : substlem.


Lemma subst_tro :
  forall U P I G1 G2 s d,
    subof (ofd U P) G1 s G2
    -> trofo U P I G2 d
    -> trofo U P I G1 (subst s d).
Proof.
intros U P I G1 G2 s d Hs Hd.
induction Hd; simp_sub; eauto with static substlem.

(* init *)
eapply trofo_init; eauto using (subof_mono (ofd U P)) with static substlem; done.
Qed.


Lemma subst1_tg_tm :
  forall U P G T m t,
    tgof U G T
    -> tmof U P (G; cl_tg) m t
    -> tmof U P G (subst1 T m) (subst1 T t).
Proof.
intros U P G T m t H1 H2.
eapply subst_tm.
2: apply H2.
apply subof_dot.
apply subof_id.
simp_sub; eauto with static substlem.
Qed.


Lemma subst1_tm_tm :
  forall U P G m1 t1 m2 t2,
    tmof U P G m1 t1
    -> value G m1
    -> tmof U P (G; cl_vl t1) m2 t2
    -> tmof U P G (subst1 m1 m2) (subst1 m1 t2).
Proof.
intros U P G m1 t1 m2 t2 H1 Hval H2.
eapply subst_tm.
2: apply H2.
apply subof_dot.
apply subof_id.
simp_sub; eauto with static substlem.
Qed.


Lemma subst1_tm_xp :
  forall U P I G m1 t1 e2 t2,
    tmof U P G m1 t1
    -> value G m1
    -> xpof U P I (G; cl_vl t1) e2 t2
    -> xpof U P I G (subst1 m1 e2) (subst1 m1 t2).
Proof.
intros U P I G m1 t1 e2 t2 H1 Hval H2.
eapply subst_xp.
2: apply H2.
apply subof_dot.
apply subof_id.
simp_sub; eauto with static substlem.
Qed.


Lemma shift1_tro :
  forall U P I G c d,
    trofo U P I G d
    -> trofo U P I (G; c) (shift1 d).
Proof.
intros U P I G c d Hof.
unfold shift1, sh1.
eauto using subst_tro, subof_sh with sequence.
Qed.


Lemma weaken_tmof :
  forall U P G1 G2 m t,
    tmof U P G1 m t
    -> tmof U P (G1;; G2) (subst (sh (length G2)) m) (subst (sh (length G2)) t).
Proof.
intros U P G1 G2 m t Hof.
eapply subst_tm.
  apply subof_sh.
  apply app_truncate.

  assumption.
Qed.


Lemma weaken_value :
  forall G1 G2 v,
    value G1 v
    -> value (G1;; G2) (subst (sh (length G2)) v).
Proof.
intros G1 G2 v Hvalue.
eapply (subst_value nil nil).
  apply subof_sh.
  apply app_truncate.

  assumption.
Qed.


Lemma weaken_value_all :
  forall G v,
    value nil v
    -> value G v.
Proof.
intros G v Hvalue.
invert Hvalue; try (intros; subst; auto with static; done); [].
intros i t Hindex _.
invert Hindex; done.
Qed.


Lemma subof_ofd_under :
  forall U P G1 G1' G2 s,
    Forall iscl G2
    -> subof (ofd U P) G1 s G1'
    -> subof (ofd U P) (G1;; subst_ctx s G2) (under (length G2) s) (G1';; G2).
Proof.
intros U P.
exact (subof_under (ofd U P) (ofd_behaved U P) (ofd_wc U P)).
Qed.


Lemma subof_ofd_bind :
  forall U P G G' s c,
    iscl c
    -> subof (ofd U P) G s G'
    -> subof (ofd U P) (G; subst s c) (dot (var 0) (compose s sh1)) (G'; c).
Proof.
intros U P G G' s c Hiscl Hsubof.
exploit (subof_ofd_under U P G G' (nil; c) s) as Hsubof'; auto; [].
simpl in Hsubof'.
simp_sub in Hsubof'.
assumption.
Qed.


(* Closure (here for lack of a better place) *)

(* We have a stronger theorem in Strengthen (tpof_closed), but this one is more robust. *)
Lemma tpof_context_closedn :
  forall G t,
    tpof G t
    -> closedn (length G) t.
Proof.
intros G t Hof.
induct Hof;
try (complete (intros; reduce_closed; trivial; eapplyall; eauto)).
Qed.


Lemma tgof_context_closedn :
  forall U G T,
    tgof U G T
    -> closedn (length G) T.
Proof.
intros U G T Hof.
induct Hof.

(* var *)
intros U G i Hindex.
thus (i < length G) as Hlt by index_length.
unfold closedn.
simp_sub.
rewrite -> project_under_lt; auto; done.

(* tag *)
intros.
reduce_closed; done.
Qed.


Lemma fcof_context_closedn :
  forall U G f,
    fcof U G f
    -> closedn (length G) f.
Proof.
intros U G f Hof.
induct Hof;
try (complete (intros; reduce_closed; trivial; try eapplyall; eauto using tgof_context_closedn)).
Qed.


Lemma tmof_xpof_context_closedn :
  (forall U P G m t,
      tmof U P G m t
      -> closedn (length G) m)
  /\
  (forall U P I G e t,
     xpof U P I G e t
     -> closedn (length G) e).
Proof.
exploit
  (tmof_xpof_ind
     (fun U P G m t => closedn (length G) m)
     (fun U P I G e t => closedn (length G) e)); [.. | assumption];
try (complete (intros; reduce_closed; trivial; rewrite <- ?under_succ, <- ?under_succ2; try eapplyall; eauto using tpof_context_closedn, fcof_context_closedn)).

(* var *)
intros U P G i t Hindex.
thus (i < length G) as Hlt by index_length.
unfold closedn.
simp_sub.
rewrite -> project_under_lt; auto; done.
Qed.


Lemma tmof_context_closedn :
  forall U P G m t,
    tmof U P G m t
    -> closedn (length G) m.
Proof.
exact (carp tmof_xpof_context_closedn).
Qed.


Lemma xpof_context_closedn :
  forall U P I G e t,
    xpof U P I G e t
    -> closedn (length G) e.
Proof.
exact (cdrp tmof_xpof_context_closedn).
Qed.


Lemma flof_context_closedn :
  forall U G fl,
    flof U G fl
    -> closedn (length G) fl.
Proof.
intros U G fl Hof.
induct Hof;
try (complete (intros; reduce_closed; trivial; try eapplyall; eauto using fcof_context_closedn)).
Qed.


Lemma acof_context_closedn :
  forall U P G a t,
    acof U P G a t
    -> closedn (length G) a.
Proof.
intros U P G a t Hofa.
destruct Hofa; reduce_closed; eauto using tmof_context_closedn.
Qed.


Lemma tmof_context_closed :
  forall U P e t,
    tmof U P nil e t
    -> closed e.
Proof.
intros U P e t H.
apply closed_closedn.
replace 0 with (length (@nil term)) by trivial.
eapply tmof_context_closedn; eauto.
Qed.


Lemma xpof_context_closed :
  forall U P I e t,
    xpof U P I nil e t
    -> closed e.
Proof.
intros U P I e t H.
apply closed_closedn.
replace 0 with (length (@nil term)) by trivial.
eapply xpof_context_closedn; eauto.
Qed.


Lemma flof_context_closed :
  forall U fl,
    flof U nil fl
    -> closed fl.
Proof.
intros U fl H.
apply closed_closedn.
replace 0 with (length (@nil term)) by trivial.
eapply flof_context_closedn; eauto.
Qed.


Lemma acof_context_closed :
  forall U P a t,
    acof U P nil a t
    -> closed a.
Proof.
intros U P e t H.
apply closed_closedn.
replace 0 with (length (@nil term)) by trivial.
eapply acof_context_closedn; eauto.
Qed.
