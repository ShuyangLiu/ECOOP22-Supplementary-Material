
Require Import Tactics.
Require Import Compare_dec.
Require Import Omega.
Require Import Static.
Require Import Sequence.
Require Import TSubst.



(* Unique types *)

Fixpoint xp_actions (e : (* xp *) term) {struct e} : list identifier :=
  (match e with
   | xp_bind t e1 e2 =>
       xp_actions e1;; xp_actions e2
   | xp_spec v1 v2 e' =>
       xp_actions e'
   | xp_fence f e' =>
       xp_actions e'
   | xp_action i =>
       nil; i
   | _ =>
       nil
   end).
       

Lemma xpof_idtp :
  forall U P I G e t,
    xpof U P I G e t
    -> map car I = xp_actions e.
Proof.
intros U P I G e t Hof.
induct Hof;
try (intros; subst; trivial; simpl; rewrite -> map_app; f_equal; auto; done); [].

(* bind_init *)
intros U P I G t1 e1 e2 t2 H H0 IH1 H2 IH2.
simpl.
simpl in IH2.
rewrite <- IH2.
assumption.
Qed.


Lemma tmof_xpof_unique :
  (forall U P G m t t',
     ddistinct P
     -> tmof U P G m t
     -> tmof U P G m t'
     -> t = t')
  /\
  (forall U P I G a t t',
     ddistinct P
     -> ddistinct I
     -> xpof U P I G a t
     -> xpof U P I G a t'
     -> t = t').
Proof.
#13 exploit
  (tmof_xpof_ind
     (fun U P G m t =>
        forall t',
          ddistinct P
          -> tmof U P G m t'
          -> t = t')
     (fun U P I G e t =>
        forall t',
          ddistinct P
          -> ddistinct I
          -> xpof U P I G e t'
          -> t = t')) as (? & ?); [.. | repeat split; eauto; done];
try (intros;
     (match goal with
      | H : tmof _ _ _ ?m _ |- _ => isapp m; invert H
      | H : xpof _ _ _ _ ?e _ |- _ => isapp e; invert H
      end);
     eauto;
     done).

(* var *)
intros U P G i t Hindex tt Hdistinct Hof.
invert Hof; intros t' Hindex' ?; subst tt.
have (index i G (cl_vl t)) as Hindex.
have (index i G (cl_vl t')) as Hindex'.
toshow (subst (sh (S i)) t = subst (sh (S i)) t').
thus (cl_vl t = cl_vl t') as Heq by index_fun.
injection Heq; intro Heq'.
f_equal; auto; done.

(* unit *)
intros U P G t' H Hof; invert Hof; eauto; done.

(* loc *)
intros U P G l t Hlookup tt Hdistinct Hof.
invert Hof; intros t' Hlookup' ?; subst tt.
have (ddistinct P) as Hdistinct.
have (lookup l P t) as Hlookup.
have (lookup l P t') as Hlookup'.
toshow (tp_ref (subst (sh (length G)) t) = tp_ref (subst (sh (length G)) t')).
thus (t = t') as Heq by ddistinct_lookup_unique.
f_equal; f_equal; auto; done.

(* susp *)
intros U P G e t Hofe IH tt Hdistinct Hof.
invert Hof; intros t' Hofe' ?; subst tt.
assert (t = t') as Heq by (eapply IH; eauto with sequence).
f_equal; assumption.

(* lam *)
intros U P G m t1 t2 Hoft1 Hofm IH tt Hdistinct Hof.
invert Hof; intros t2' _ Hofm' ?; subst tt.
thus (shift1 t2 = shift1 t2') as Heq by IH.
assert (subst1 nonsense (shift1 t2) = subst1 nonsense (shift1 t2')) as Heq' by (f_equal; assumption).
simp_sub in Heq'.
f_equal; auto; done.

(* app *)
intros U P G m1 m2 t1 t2 Hofm1 IH1 Hofm2 IH t2' Hdistinct Hof.
invert Hof; intros t1' Hofm1' Hofm2'.
thus (tp_arrow t1 t2 = tp_arrow t1' t2') as Heq by IH1.
injection Heq; auto; done.

(* force *)
intros U P G m t Hofm IH t' HdistinctP HdistinctI Hof.
invert Hof; intros Hofm'.
thus (tp_susp t = tp_susp t') as Heq by IH.
injection Heq; auto; done.

(* bind *)
intros U P I G t1 e1 e2 t2 Hoft1 Hofe1 IH1 Hofe2 IH2 t2' HdistinctP HdistinctI Hof.
assert (exists I1' I2', I = I1';; I2' /\ xpof U P I1' G e1 t1 /\ xpof U P I2' (G; cl_vl t1) e2 (shift1 t2')) as (I1' & I2' & HeqI & Hofe1' & Hofe2').
  invert Hof; intros; do 3 eexists; simpl; eauto; auto; done.
assert (I2' = nil /\ I1' = I) as HeqI'.
  apply split_app_length; auto; [].
  rewrite <- !(@map_length _ _ car).
  erewrite -> !xpof_idtp; eauto; done.
destruct HeqI'; subst I1' I2'; clear HeqI.
assert (shift1 t2 = shift1 t2') as Heq by (eapply IH2; eauto using ddistinct_nil).
assert (subst1 nonsense (shift1 t2) = subst1 nonsense (shift1 t2')) as Heq' by (f_equal; assumption).
simp_sub in Heq'.
assumption.

(* bind *)
intros U P I1 I2 G t1 e1 e2 t2 Hinit Hoft1 Hofe1 IH1 Hofe2 IH2 t2' HdistinctP HdistinctI Hof.
assert (exists I1' I2', I1 ;; I2 = I1';; I2' /\ xpof U P I1' G e1 t1 /\ xpof U P I2' (G; cl_vl t1) e2 (shift1 t2')) as (I1' & I2' & HeqI & Hofe1' & Hofe2').
  invert Hof.
    intros; exists (I1;; I2); do 2 eexists; simpl; eauto; auto; done.

    intros I1' I2' _ _ Hofe1' Hofe2' HeqI.
    exists I1', I2'.
    auto; done.
assert (I2' = I2 /\ I1' = I1) as HeqI'.
  apply split_app_length; auto; [].
  rewrite <- !(@map_length _ _ car).
  erewrite -> !xpof_idtp; eauto; done.
destruct HeqI'; subst I1' I2'; clear HeqI.
so (ddistinct_app _#4 HdistinctI) as (HdistinctI1 & HdistinctI2).
thus (shift1 t2 = shift1 t2') as Heq by IH2.
assert (subst1 nonsense (shift1 t2) = subst1 nonsense (shift1 t2')) as Heq' by (f_equal; assumption).
simp_sub in Heq'.
assumption.

(* read *)
intros U P G m t Hofm IH t' HdistinctP HdistinctI Hof.
invert Hof; intros Hofm'.
thus (tp_ref t = tp_ref t') as Heq by IH.
injection Heq; auto.

(* push *)
intros U P G tt HdistinctP HdistinctI Hof.
invert Hof; intros; subst tt.
reflexivity.

(* nop *)
intros U P G tt HdistinctP HdistinctI Hof.
invert Hof; intros; subst tt.
reflexivity.

(* new *)
intros U P G e t b Hofe IH t' HdistinctP HdistinctI Hof.
invert Hof; intros Hofe'.
thus (subst (sh 2) t = subst (sh 2) t') as Heq by IH.
assert (subst (dot nonsense (dot nonsense id)) (subst (sh 2) t) = subst (dot nonsense (dot nonsense id)) (subst (sh 2) t')) as Heq' by (f_equal; assumption).
simp_sub in Heq'.
assumption.
Qed.


Lemma tmof_unique :
  forall U P G m t t',
    ddistinct P
    -> tmof U P G m t
    -> tmof U P G m t'
    -> t = t'.
Proof.
exact (carp tmof_xpof_unique).
Qed.


Lemma acof_unique :
  forall U P G a t t',
    ddistinct P
    -> acof U P G a t
    -> acof U P G a t'
    -> t = t'.
Proof.
intros U P G a t1 t2 Hdist Hof1 Hof2.
revert Hdist Hof2.
induct Hof1.
(* read *)
intros l U P G t Hlookup Hdist Hof2.
invert Hof2; intros t' Hlookup' ?.
so (ddistinct_lookup_unique _#6 Hdist Hlookup Hlookup') as Heq.
subst t'.
assumption.

(* write *)
intros U P G l v t H H0 H1 Hdist Hof2.
invert Hof2; intros.
assumption.

(* rw *)
intros U P G l v t Hlookup H0 H1 Hdist Hof2.
invert Hof2; intros t' Hlookup' ? ? ?.
so (ddistinct_lookup_unique _#6 Hdist Hlookup Hlookup') as Heq.
subst t'.
assumption.

(* push *)
intros U P G Hdist Hof2.
invert Hof2; intros.
assumption.

(* nop *)
intros U P G Hdist Hof2.
invert Hof2; intros.
assumption.
Qed.


(* Subordination *)

Lemma tmof_tgof_disjoint :
  forall U P G M t,
    tmof U P G M t
    -> tgof U G M
    -> False.
Proof.
intros U P G M t H1 H2.
induction H1; inversion H2.
thus (cl_vl t = cl_tg) as Heq by index_fun.
discriminate Heq.
Qed.


Lemma tmof_tpof_disjoint :
  forall U P G M t,
    tmof U P G M t
    -> tpof G M
    -> False.
Proof.
intros U P G M t H1 H2.
induction H1; inversion H2.
Qed.


Lemma tmof_xpof_disjoint :
  forall U P I G M t t',
    tmof U P G M t
    -> xpof U P I G M t'
    -> False.
Proof.
intros U P I G M t t' H1 H2.
induction H1; inversion H2.
Qed.


Lemma tmof_fcof_disjoint :
  forall U P G M t,
    tmof U P G M t
    -> fcof U G M
    -> False.
Proof.
intros U P G M t H1 H2.
induction H1; inversion H2.
Qed.


Lemma subst_under_var :
  forall n t i,
    (i < n /\ subst (under n (dot t id)) (var i) = var i)
    \/
    (i = n /\ subst (under n (dot t id)) (var i) = subst (sh n) t)
    \/
    (i > n /\ subst (under n (dot t id)) (var i) = var (i-1)).
Proof.
intros.
destruct (lt_dec i n) as [Hlt | Hge].
  left.
  split; [assumption |].
  simp_sub.
  rewrite -> project_under_lt; auto.

  right.
  destruct (gt_dec i n) as [Hgt | Hle].
    right.
    split; [assumption |].
    simp_sub.
    rewrite -> project_under_ge; [| omega].
    repl (i-n) with (S (i-n-1)) by omega.
    simp_sub.
    f_equal; omega.

    assert (i = n) as Heq by omega.
    left.
    split; [assumption |].
    subst i.
    simp_sub.
    rewrite -> project_under_ge; [| omega].
    repl (n-n) with 0 by omega.
    simp_sub.
    reflexivity.
Qed.


Lemma tmof_tgof_subord :
  forall U P G1 G2 m mt T,
    tmof U P G1 m mt
    -> tgof U (G1;; G2) (subst (under (length G2) (dot m id)) T)
    -> T = subst (under (length G2) (dot nonsense sh1)) T.
Proof.
intros U P G1 G2 m mt T Hofm Hof.
induction T;
try (complete (inversion Hof)).

(* var *)
pose proof (subst_under_var (length G2) m n) as [(Hlt & H) | [(Heq & H) | (Hgt & H)]];
rewrite -> H in Hof; clear H.
  simp_sub.
  rewrite -> project_under_lt; auto.
  
  pose proof (weaken_tmof _#3 G2 _ _ Hofm) as Hofm'.
  destruct (tmof_tgof_disjoint _#5 Hofm' Hof).

  simp_sub.
  rewrite -> project_under_ge; [| omega].
  repl (n - length G2) with (S (n - length G2 - 1)) by omega.
  simp_sub.
  f_equal; omega.

(* lit *)
simp_sub.
reflexivity.
Qed.


Lemma tmof_tpof_subord :
  forall U P G1 G2 m mt t,
    tmof U P G1 m mt
    -> tpof (G1;; G2) (subst (under (length G2) (dot m id)) t)
    -> t = subst (under (length G2) (dot nonsense sh1)) t.
Proof.
intros U P G1 G2 m mt t Hofm Hof.
induction t;
try (complete (inversion Hof)).

(* var *)
pose proof (subst_under_var (length G2) m n) as [(_ & H) | [(_ & H) | (_ & H)]];
rewrite -> H in Hof; clear H; [| |].
  inversion Hof; done.

  pose proof (weaken_tmof _#3 G2 _ _ Hofm) as Hofm'.
  destruct (tmof_tpof_disjoint _#5 Hofm' Hof); done.

  inversion Hof; done.

(* unit *)
simp_sub.
reflexivity.

(* base *)
simp_sub.
reflexivity.

(* susp *)
simp_sub.
f_equal.
apply IHt.
simp_sub in Hof.
invert Hof; intros.
assumption.

(* ref *)
simp_sub.
f_equal.
apply IHt.
simp_sub in Hof.
invert Hof; intros.
assumption.

(* arrow *)
simp_sub.
simp_sub in Hof.
invert Hof; intros.
f_equal; eapplyall; auto; done.
Qed.


Lemma tmof_tpof_subord2 :
  forall U P G1 G2 m mt t,
    tmof U P G1 m mt
    -> tpof (G1;; G2) (subst (under (length G2) (dot m id)) t)
    -> t = subst (compose (under (length G2) (dot m id)) (under (length G2) sh1)) t.
Proof.
intros U P G1 G2 m mt t Hofm Hof.
rewrite -> (tmof_tpof_subord _#7 Hofm Hof).
rewrite <- subst_compose.
simp_sub.
reflexivity.
Qed.


Lemma tmof_tpof_subord2a :
  forall U P G1 G2 m mt t,
    tmof U P G1 m mt
    -> tpof (G1;; G2) (subst (under (length G2) (dot m id)) t)
    -> t = subst (under (length G2) (dot (shift1 m) sh1)) t.
Proof.
intros U P G1 G2 m mt t Hofm Hof.
so (tmof_tpof_subord2 _#7 Hofm Hof) as HH.
simp_sub in HH.
assumption.
Qed.


Lemma tmof_fcof_subord :
  forall U P G1 G2 m mt f,
    tmof U P G1 m mt
    -> fcof U (G1;; G2) (subst (under (length G2) (dot m id)) f)
    -> f = subst (under (length G2) (dot nonsense sh1)) f.
Proof.
intros U P G1 G2 m mt f Hofm Hof.
induction f;
try (complete (inversion Hof)).

(* var *)
pose proof (subst_under_var (length G2) m n) as [(_ & H) | [(_ & H) | (_ & H)]];
rewrite -> H in Hof; clear H.
  inversion Hof.
  
  pose proof (weaken_tmof _#3 G2 _ _ Hofm) as Hofm'.
  destruct (tmof_fcof_disjoint _#5 Hofm' Hof).

  inversion Hof.

(* tag *)
rename f into T.
simp_sub in Hof.
invert Hof; intros HofT.
simp_sub.
f_equal.
eapply tmof_tgof_subord; eauto; done.

(* pre *)
simp_sub.
reflexivity.

(* post *)
simp_sub.
reflexivity.
Qed.


Lemma tmof_fcof_subord2 :
  forall U P G1 G2 m mt f,
    tmof U P G1 m mt
    -> fcof U (G1;; G2) (subst (under (length G2) (dot m id)) f)
    -> f = subst (compose (under (length G2) (dot m id)) (under (length G2) sh1)) f.
Proof.
intros U P G1 G2 m mt f Hofm Hof.
rewrite -> (tmof_fcof_subord _#7 Hofm Hof).
rewrite <- subst_compose.
rewrite -> !dist_compose_under.
simp_sub.
reflexivity.
Qed.


(* Factoring *)

Lemma tpof_factor :
  forall U P G1 G2 m mt t,
    Forall iscl G2
    -> tmof U P G1 m mt
    -> tpof (G1;; G2) (subst (under (length G2) (dot m id)) t)
    -> tpof (G1; cl_vl mt;; subst_ctx sh1 G2) t.
Proof.
intros U P G1 G2 m mt t Hallcl Hofm Hof.
assert (subof (ofs U) (G1; cl_vl mt;; subst_ctx sh1 G2) (under (length G2) sh1) (G1;; G2)) as Hsubof.
  apply (subof_mono (ofd U P)); [apply ofd_ofs |].
  apply subof_ofd_under; auto.
  unfold sh1.
  apply subof_sh.
  apply truncate_S; apply truncate_0.
rewrite -> (tmof_tpof_subord2 _#7 Hofm Hof).
rewrite -> subst_compose.
apply (subst_tp _#5 Hsubof).
assumption.
Qed.


Lemma fcof_factor :
  forall U P G1 G2 m mt f,
    Forall iscl G2
    -> tmof U P G1 m mt
    -> fcof U (G1;; G2) (subst (under (length G2) (dot m id)) f)
    -> fcof U (G1; cl_vl mt;; subst_ctx sh1 G2) f.
Proof.
intros U P G1 G2 m mt f Hallcl Hofm Hof.
assert (subof (ofs U) (G1; cl_vl mt;; subst_ctx sh1 G2) (under (length G2) sh1) (G1;; G2)) as Hsubof.
  apply (subof_mono (ofd U P)); [apply ofd_ofs |].
  apply subof_ofd_under; auto.
  unfold sh1.
  apply subof_sh.
  apply truncate_S; apply truncate_0.
rewrite -> (tmof_fcof_subord2 _#7 Hofm Hof).
rewrite -> subst_compose.
apply (subst_fc _#5 Hsubof).
assumption.
Qed.


Lemma value_factor :
  forall G1 G2 m t v,
    Forall iscl G2
    -> value (G1;; G2) (subst (under (length G2) (dot m id)) v)
    -> value (G1; cl_vl t;; subst_ctx sh1 G2) v.
Proof.
intros G1 G2 m t v Hallcl Hvalue.
destruct v; try (complete (inversion Hvalue)); auto with static.

(* var *)
pose proof (subst_under_var (length G2) m n) as [(Hlt & H) | [(Heq & H) | (Hgt & H)]];
rewrite -> H in Hvalue; clear H.
  repl (var n) with (subst (under (length G2) sh1) (var n)).
    simp_sub.
    apply project_under_lt; auto; done.
  eapply subst_value; [| eexact Hvalue].
  apply subof_ofd_under; [assumption |].
  apply subof_sh; [].
  apply truncate_S; apply truncate_0; done.

  eapply value_var; [].
  repl n with (0+n) by omega.
  subst n.
  erewrite <- subst_ctx_length.
  apply index_app_right; [].
  apply index_0; done.

  repl (var n) with (subst (under (length G2) sh1) (var (n - 1))).
    simp_sub.
    rewrite -> project_under_ge; [| omega].
    simp_sub.
    f_equal; omega.
  eapply subst_value; [| eexact Hvalue].
  apply subof_ofd_under; [assumption |].
  apply subof_sh; [].
  apply truncate_S; apply truncate_0; done.

Existential 1 := nil.
Existential 1 := nil.
Existential 1 := nil.
Existential 1 := nil.
Qed.


Lemma tmof_init_disjoint :
  forall U P G M t,
    tmof U P G M t
    -> init M
    -> False.
Proof.
intros U P G M t H1 H2.
induction H1; inversion H2.
Qed.


Lemma unsubst_init :
  forall n m e,
    ~ init m
    -> init (subst (under n (dot m id)) e)
    -> init e.
Proof.
intros n m e Hninit Hinit.
revert n Hinit.
induct e;
try (intros; simp_sub in Hinit; invert Hinit; intros; eauto with static; done).
(* var *)
intros i n Hinit.
simp_sub in Hinit.
destruct (lt_dec i n) as [Hlt | Hge].
  rewrite -> project_under_lt in Hinit; auto; done.

  rewrite -> project_under_ge in Hinit; [| omega].
  remember (i - n) as n' in Hinit.
  destruct n'.
    simp_sub in Hinit.
    so (subst_init (unsh n) _ Hinit) as Hinit'.
    simp_sub in Hinit'.
    rewrite -> compose_sh_unsh in Hinit'.
    simp_sub in Hinit'.
    destruct Hninit; assumption.

    simp_sub in Hinit.
    invert Hinit; done.

(* bind *)
intros t _ e1 IH1 e2 IH2 n Hinit.
simp_sub in Hinit.
invert Hinit; intros Hinit1 Hinit2.
apply init_bind.
  eapply IH1; eauto; done.

  apply (IH2 (S n)).
  simp_sub.
  assumption.
Qed.


Lemma tmof_xpof_factor :
  (forall U P G1 G2 m t m' t',
     ddistinct P
     -> Forall iscl G2
     -> tmof U P G1 m t
     -> tmof U P (G1;; G2) (subst (under (length G2) (dot m id)) m') t'
     -> tmof U P (G1; cl_vl t;; subst_ctx sh1 G2) m' (subst (under (length G2) sh1) t'))
  /\
  (forall U P I G1 G2 m t e t',
     ddistinct P
     -> ddistinct I
     -> Forall iscl G2
     -> tmof U P G1 m t
     -> xpof U P I (G1;; G2) (subst (under (length G2) (dot m id)) e) t'
     -> xpof U P I (G1; cl_vl t;; subst_ctx sh1 G2) e (subst (under (length G2) sh1) t')).
Proof.
cut (forall U P G1 G2 m t M t',
       ddistinct P
       -> Forall iscl G2
       -> tmof U P G1 m t
       -> (tmof U P (G1;; G2) (subst (under (length G2) (dot m id)) M) t'
           -> tmof U P (G1; cl_vl t;; subst_ctx sh1 G2) M (subst (under (length G2) sh1) t'))
          /\
          (forall I,
             ddistinct I
             -> xpof U P I (G1;; G2) (subst (under (length G2) (dot m id)) M) t'
             -> xpof U P I (G1; cl_vl t;; subst_ctx sh1 G2) M (subst (under (length G2) sh1) t'))).
  intro Hind.
  split; intros; eapply Hind; eauto; exact nil.
intros U P G1 G2 m t M t' HdistinctP Hallcl Hofm.
revert G2 t' Hallcl.
#24 induction M;
intros G2 t' Hallcl;
(split; [| intros I HdistinctI]);
intro HofM;
try (complete (simpl in HofM; inversion HofM)).

(* var (tmof) *)
have (tmof U P G1 m t) as Hofm.
toshow (tmof U P (G1; cl_vl t;; subst_ctx sh1 G2) (var n)
          (subst (under (length G2) sh1) t')).
pose proof (subst_under_var (length G2) m n) as [(Hlt & H) | [(Heq & H) | (Hgt & H)]];
rewrite -> H in HofM; clear H; [| |].
  have (tmof U P (G1;; G2) (var n) t') as HofM.
  have (n < length G2) as Hlt.
  repl (var n) with (subst (under (length G2) sh1) (var n)).
    simp_sub.
    apply project_under_lt; auto; done.
  eapply subst_tm; [| eexact HofM].
  apply subof_ofd_under; [assumption |].
  apply subof_sh; [].
  apply truncate_S; apply truncate_0; done.

  have (tmof U P (G1;; G2) (subst (sh (length G2)) m) t') as HofM.
  have (n = length G2) as Heq.
  thus (tmof U P (G1;; G2) (subst (sh (length G2)) m) (subst (sh (length G2)) t)) as Hofm' by weaken_tmof.
  thus (subst (sh (length G2)) t = t') as Heqt' by tmof_unique.
  subst t'.
  toshow (tmof U P (G1; cl_vl t;; subst_ctx sh1 G2) (var n)
            (subst (under (length G2) sh1) (subst (sh (length G2)) t))).
  rewrite <- subst_compose.
  rewrite -> compose_sh_under_all.
  simp_sub.
  repl (length G2 + 1) with (S n) by omega.
  apply tmof_var.
  toshow (index n (G1; cl_vl t;; subst_ctx sh1 G2) (cl_vl t)).
  repl n with (0 + length (subst_ctx sh1 G2)).
    rewrite -> subst_ctx_length.
    omega.
  apply index_app_right.
  apply index_0; done.

  have (tmof U P (G1;; G2) (var (n - 1)) t') as HofM.
  have (n > length G2) as Hgt.
  repl (var n) with (subst (under (length G2) sh1) (var (n-1))).
    simp_sub.
    rewrite -> project_under_ge; [| omega].
    simp_sub.
    f_equal; omega.
  eapply subst_tm; [| eexact HofM].
  apply subof_ofd_under; [assumption |].
  apply subof_sh; [].
  apply truncate_S; apply truncate_0; done.

(* var (xpof) *)
pose proof (subst_under_var (length G2) m n) as [(_ & H) | [(_ & H) | (_ & H)]];
rewrite -> H in HofM; clear H; [| |].
  invert HofM; done.
  
  pose proof (weaken_tmof _#3 G2 _ _ Hofm) as Hofm'.
  destruct (tmof_xpof_disjoint _#7 Hofm' HofM); done.

  invert HofM; done.

(* unit *)
simp_sub in HofM.
invert HofM; intros; subst t'.
simp_sub.
auto with static; done.

(* lit *)
simp_sub in HofM.
invert HofM; intros; subst t'.
simp_sub.
auto with static; done.

(* prim *)
simp_sub in HofM.
invert HofM; intros HofM1 HofM2 <-.
simp_sub.
pose proof (IHM1 _ _ Hallcl andel HofM1) as HofM1'.
pose proof (IHM2 _ _ Hallcl andel HofM2) as HofM2'.
auto with static; done.

(* if *)
simp_sub in HofM.
invert HofM; intros HofM1 HofM2 HofM3.
simp_sub.
pose proof (IHM1 _ _ Hallcl andel HofM1) as HofM1'.
pose proof (IHM2 _ _ Hallcl andel HofM2) as HofM2'.
pose proof (IHM3 _ _ Hallcl andel HofM3) as HofM3'.
auto with static; done.

(* loc *)
simp_sub in HofM.
invert HofM; intros t'' Hlookup Heqt'; subst t'.
simp_sub.
rewrite -> compose_sh_under_more; [| rewrite -> app_length; omega].
simp_sub.
repl (length (G1;; G2) - length G2 + length G2 + 1) with (length (G1; cl_vl t;; subst_ctx sh1 G2)); [| auto with static].
rewrite -> !app_length.
simpl.
rewrite -> subst_ctx_length.
omega.

(* susp *)
simp_sub in HofM.
invert HofM; intros t'' HofM' Heqt'; subst t'.
simp_sub.
apply tmof_susp.
eapply (IHM _ _ Hallcl ander); [|].
  apply ddistinct_nil; done.

  exact HofM'.

(* lam *)
(* UGH! This is a mess! *)
rename M1 into t1.
rename M2 into M'.
simp_sub in HofM.
invert HofM; intros t2 Hoft1 HofM' Heqt'; subst t'.
simp_sub.
rewrite <- (tmof_tpof_subord2a _#7 Hofm Hoft1).
apply tmof_lam; [|].
  assert (subof (ofs U) (G1; cl_vl t;; subst_ctx sh1 G2) (under (length G2) sh1) (G1;; G2)) as Hsubof.
    apply (subof_mono (ofd U P)); [apply ofd_ofs |].
    apply subof_ofd_under; auto.
    unfold sh1.
    apply subof_sh; [].
    apply truncate_S; apply truncate_0; done.
  rewrite -> (tmof_tpof_subord2 _#7 Hofm Hoft1).
  rewrite -> subst_compose.
  apply (subst_tp _#5 Hsubof); [].
  assumption.

  exploit (IHM2 (G2; cl_vl (subst (under (length G2) (dot m id)) t1)) (shift1 t2) (Forall_cons _ iscl_vl Hallcl) andel) as H; [|].
    simpl length.
    simp_sub.
    exact HofM'.
  
    simpl subst_ctx in H.
    simpl length in H.
    simp_sub in H.
    rewrite <- (tmof_tpof_subord2a _#7 Hofm Hoft1) in H.
    simpl app in H.
    unfold shift1.
    rewrite <- subst_compose.
    exact H.

(* fun *)
(* UGH! Even more of a mess! *)
rename M1 into t1.
rename M2 into t2.
rename M3 into M'.
simp_sub in HofM.
invert HofM.
intros Hoft1 Hoft2 HofM' <-.
simp_sub.
rewrite <- (tmof_tpof_subord2a _#7 Hofm Hoft1).
rewrite <- (tmof_tpof_subord2a _#7 Hofm Hoft2).
assert (subof (ofs U) (G1; cl_vl t;; subst_ctx sh1 G2) (under (length G2) sh1) (G1;; G2)) as Hsubof.
  apply (subof_mono (ofd U P)); [apply ofd_ofs |].
  apply subof_ofd_under; auto.
  unfold sh1.
  apply subof_sh; [].
  apply truncate_S; apply truncate_0; done.
apply tmof_fun; [| |].
  rewrite -> (tmof_tpof_subord2 _#7 Hofm Hoft1).
  rewrite -> subst_compose.
  apply (subst_tp _#5 Hsubof); [].
  assumption.

  rewrite -> (tmof_tpof_subord2 _#7 Hofm Hoft2).
  rewrite -> subst_compose.
  apply (subst_tp _#5 Hsubof); [].
  assumption.

  exploit (IHM3 (G2; cl_vl (tp_arrow (subst (under (length G2) (dot m id)) t1) (subst (under (length G2) (dot m id)) t2)); cl_vl (shift1 (subst (under (length G2) (dot m id)) t1))) (subst (sh 2) (subst (under (length G2) (dot m id)) t2)) (Forall_cons _ iscl_vl (Forall_cons _ iscl_vl Hallcl)) andel) as H; [|].
    simpl length.
    simp_sub.
    simp_sub in HofM'.
    exact HofM'.

    simpl subst_ctx in H.
    simpl length in H.
    simpl app in H.
    simp_sub in H.
    rewrite <- !(tmof_tpof_subord2a _#7 Hofm Hoft1) in H.
    rewrite <- !(tmof_tpof_subord2a _#7 Hofm Hoft2) in H.
    rewrite <- !compose_assoc in H.
    rewrite -> !dist_compose_under in H.
    simp_sub in H.
    rewrite -> !subst_compose in H.
    rewrite <- (tmof_tpof_subord2a _#7 Hofm Hoft1) in H.
    rewrite <- (tmof_tpof_subord2a _#7 Hofm Hoft2) in H.
    exact H.

(* app *)
simp_sub in HofM.
invert HofM; intros t1 HofM1 HofM2.
rename t' into t2.
pose proof (IHM1 _ _ Hallcl andel HofM1) as HofM1'.
pose proof (IHM2 _ _ Hallcl andel HofM2) as HofM2'.
eauto with static; done.

(* ret *)
simp_sub in HofM.
invert HofM; intros HofM' <-.
pose proof (IHM _ _ Hallcl andel HofM') as HofM''.
auto with static; done.

(* force *)
simp_sub in HofM.
invert HofM; intros HofM' <-.
pose proof (IHM _ _ Hallcl andel HofM') as HofM''.
auto with static; done.

(* bind *)
rename M1 into t1.
rename M2 into e1.
rename M3 into e2.
rename t' into t2.
simp_sub in HofM.
invert HofM.
  intros Hoft1 Hofe1 Hofe2.
  apply xpof_bind; [| |].
    eapply tpof_factor; eauto; done.

    pose proof (IHM2 _ _ Hallcl ander I HdistinctI Hofe1) as HofM1'.
    rewrite <- subst_compose in HofM1'.
    rewrite <- (tmof_tpof_subord2 _#7 Hofm Hoft1) in HofM1'.
    assumption.

    exploit (IHM3 (G2; cl_vl (subst (under (length G2) (dot m id)) t1)) (shift1 t2) (Forall_cons _ iscl_vl Hallcl) ander nil ddistinct_nil) as H.
      simpl length.
      simp_sub.
      exact Hofe2.
  
      simpl subst_ctx in H.
      simpl length in H.
      simp_sub in H.
      rewrite <- (tmof_tpof_subord2a _#7 Hofm Hoft1) in H.
      simpl app in H.
      unfold shift1.
      rewrite <- subst_compose.
      exact H.

  intros I1 I2 Hinit Hoft1 Hofe1 Hofe2 <-.
  so (ddistinct_app _#4 HdistinctI) as (HdistinctI2 & HdistinctI1).
  apply xpof_bind_init; [| | |].
    eapply unsubst_init; eauto; [].
    intros Hinitm.
    eapply tmof_init_disjoint; eauto; done.

    eapply tpof_factor; eauto; done.
  
    pose proof (IHM2 _ _ Hallcl ander I1 HdistinctI1 Hofe1) as HofM1'.
    rewrite <- subst_compose in HofM1'.
    rewrite <- (tmof_tpof_subord2 _#7 Hofm Hoft1) in HofM1'.
    assumption.
  
    exploit (IHM3 (G2; cl_vl (subst (under (length G2) (dot m id)) t1)) (shift1 t2) (Forall_cons _ iscl_vl Hallcl) ander I2 HdistinctI2) as H.
      simpl length.
      simp_sub.
      exact Hofe2.
  
      simpl subst_ctx in H.
      simpl length in H.
      simp_sub in H.
      rewrite <- (tmof_tpof_subord2a _#7 Hofm Hoft1) in H.
      simpl app in H.
      unfold shift1.
      rewrite <- subst_compose.
      exact H.

(* spec *)
rename M1 into v1.
rename M2 into v2.
rename M3 into e.
simp_sub in HofM.
invert HofM; intros t'' Hofv1 Hofv2 Hvalue1 Hvalue2 Hofe.
so (IHM1 _ _ Hallcl andel Hofv1) as Hofv1'.
so (IHM2 _ _ Hallcl andel Hofv2) as Hofv2'.
so (IHM3 _ _ Hallcl ander I HdistinctI Hofe) as Hofe'.
eauto using value_factor with static; done.

(* read *)
simp_sub in HofM.
invert HofM; intros HofM' <-.
so (IHM _ _ Hallcl andel HofM') as HofM''.
auto with static; done.

(* write *)
simp_sub in HofM.
invert HofM; intros t'' HofM1 HofM2 <- <-.
so (IHM1 _ _ Hallcl andel HofM1) as HofM1'.
so (IHM2 _ _ Hallcl andel HofM2) as HofM2'.
eauto with static; done.

(* rw *)
simp_sub in HofM.
invert HofM; intros HofM1 HofM2 <-.
so (IHM1 _ _ Hallcl andel HofM1) as HofM1'.
so (IHM2 _ _ Hallcl andel HofM2) as HofM2'.
eauto with static; done.

(* rmw *)
rename M1 into t1.
rename M2 into m1.
rename M3 into m2.
simp_sub in HofM.
invert HofM; [].
intros Hoft1 Hofm1 Hofm2 <- Heqt'.
rewrite <- Heqt'.
simp_sub.
rewrite <- (tmof_tpof_subord2a _#7 Hofm Hoft1); [].
#3 apply xpof_rmw.
  eapply tpof_factor; eauto; done.

  so (IHM2 _ _ Hallcl andel Hofm1) as Hofm1'.
  simp_sub in Hofm1'.
  rewrite <- (tmof_tpof_subord2a _#7 Hofm Hoft1) in Hofm1'.
  exact Hofm1'.

  clear IHM1 IHM2.
  #2 exploit (IHM3 (G2; cl_vl (subst (under (length G2) (dot m id)) t1)) (subst (compose (under (length G2) (dot m id)) sh1) t1) (Forall_cons _ iscl_vl Hallcl) andel) as H.
    simpl length.
    simp_sub.
    simp_sub in Hofm2.
    exact Hofm2.

    simpl subst_ctx in H.
    simpl length in H.
    simp_sub in H.
    rewrite <- (tmof_tpof_subord2a _#7 Hofm Hoft1) in H.
    simpl app in H.
    rewrite <- compose_assoc in H.
    rewrite -> dist_compose_under in H.
    simp_sub in H.
    rewrite -> subst_compose in H.
    rewrite <- (tmof_tpof_subord2a _#7 Hofm Hoft1) in H.
    simp_sub in H.
    exact H.

(* push *)
simp_sub in HofM.
invert HofM; intros <- <-.
simp_sub.
auto with static; done.

(* nop *)
simp_sub in HofM.
invert HofM; intros <- <-.
simp_sub.
auto with static; done.

(* action *)
simp_sub in HofM.
invert HofM; intros t'' p' <- Heqt'; subst t'.
simp_sub.
rewrite -> compose_sh_under_more; [| rewrite -> app_length; omega].
simp_sub.
repl (length (G1;; G2) - length G2 + length G2 + 1) with (length (G1; cl_vl t;; subst_ctx sh1 G2)); [| eauto with static; done].
toshow (length (G1; cl_vl t;; subst_ctx sh1 G2) =
        length (G1;; G2) - length G2 + length G2 + 1).
rewrite -> !app_length.
simpl.
rewrite -> subst_ctx_length.
omega.

(* new *)
simp_sub in HofM.
invert HofM; intros HofM' <-.
apply xpof_new.
rewrite <- under_plus2 in HofM'.
rewrite <- subst_compose.
rewrite <- compose_sh_under2.
pose proof (IHM (G2; cl_tg; cl_tg) _ (Forall_cons _ iscl_tg (Forall_cons _ iscl_tg Hallcl)) ander nil HdistinctI HofM') as HofM''.
simpl subst_ctx in HofM''.
simpl app in HofM''.
simp_sub in HofM''.
exact HofM''.

(* fence *)
simp_sub in HofM.
invert HofM; intros HofM1 HofM2.
pose proof (fcof_factor _#7 Hallcl Hofm HofM1) as HofM1'.
pose proof (IHM2 _ _ Hallcl ander I HdistinctI HofM2) as HofM2'.
auto with static; done.
Qed.


Lemma xpof_factor :
  forall U P I G m t e t',
    ddistinct P
    -> ddistinct I
    -> tmof U P G m t
    -> xpof U P I G (subst1 m e) t'
    -> xpof U P I (G; cl_vl t) e (shift1 t').
Proof.
intros U P I G m t e t' HdistinctP HdistinctI Hofm Hofe.
assert (xpof U P I (G;; nil) (subst (under 0 (dot m id)) e) t') as Hofe' by (simp_sub; auto).
exact (tmof_xpof_factor ander _#9 HdistinctP HdistinctI (Forall_nil _) Hofm Hofe').
Qed.
