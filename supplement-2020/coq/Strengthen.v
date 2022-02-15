
Require Import Tactics.
Require Import Static.
Require Import TSubst.
Require Import Sequence.
Require Import Compare_dec.
Require Import Plus.
Require Import Omega.


(* It's probably a bad idea to rely on this. *)
Lemma tpof_closed :
  forall G t s,
    tpof G t
    -> t = subst s t.
Proof.
intros G t s Hof.
induction Hof;
simp_sub; f_equal; auto with static.
Qed.


Lemma strengthen_tpof_gen :
  forall G1 G2 c t,
    tpof (G1; c;; G2) t
     -> G2 = subst_ctx (dot nonsense sh1) G2
     -> t = subst (under (length G2) (dot nonsense sh1)) t
     -> tpof (G1;; subst_ctx (dot nonsense id) G2)
          (subst (under (length G2) (dot nonsense id)) t).
Proof.
intros G1 G2 c t Hof HeqG2 Heqt.
induction Hof;
simp_sub; simp_sub in Heqt; try (injection Heqt); auto with static.
Qed.


(* necessary? *)
Lemma absent_shift :
  forall s m t,
    t = subst (under m s) t
    -> shift1 t = subst (under (S m) s) (shift1 t).
Proof.
intros s m t Heq.
unfold shift1, sh1.
rewrite <- subst_compose.
rewrite -> compose_sh_under; [| omega].
rewrite -> subst_compose.
f_equal.
replace (S m - 1) with m by omega.
assumption.
Qed.


Lemma absent_unshift :
  forall s m t,
    shift1 t = subst (under (S m) s) (shift1 t)
    -> t = subst (under m s) t.
Proof.
intros s m t Heq.
assert (subst (dot nonsense id) (shift1 t)
        = subst (dot nonsense id) (subst (under (S m) s) (shift1 t))) as Heq' by (f_equal; auto).
simp_sub in Heq'.
assumption.
Qed.


Lemma strengthen_var :
  forall G1 G2 c i c',
    index i (G1; c;; G2) c'
    -> G2 = subst_ctx (dot nonsense sh1) G2
    -> var i = subst (under (length G2) (dot nonsense sh1)) (var i)
    -> subst (sh (S i)) c' = subst (under (length G2) (dot nonsense sh1)) (subst (sh (S i)) c')
       /\ exists i', exists c'',
            project (under (length G2) (dot nonsense id)) i = var i'
            /\ index i' (G1;; subst_ctx (dot nonsense id) G2) c''
            /\ subst (sh (S i')) c'' = subst (compose (sh (S i)) (under (length G2) (dot nonsense id))) c'.
Proof.
intros G1 G2 c i c' Hindex HeqG2 Heqvar.
destruct (lt_dec i (length G2)) as [Hlt | Hge].
  have (i < length G2) as Hlt.
  split.
    thus (index i G2 c') as Hindex' by index_app_lt.
    thus (index i (subst_ctx (dot nonsense sh1) G2) (subst (under (length G2 - i - 1) (dot nonsense sh1)) c')) as Hindex'' by index_subst_ctx.
    rewrite <- HeqG2 in Hindex''.
    thus (c' = subst (under (length G2 - i - 1) (dot nonsense sh1)) c') as Heq by index_fun.
    rewrite <- subst_compose.
    rewrite -> compose_sh_under; [| omega].
    rewrite -> subst_compose.
    f_equal.
    replace (length G2 - S i) with (length G2 - i - 1) by omega.
    assumption.

    exists i.
    exists (subst (under (length G2 - i - 1) (dot nonsense id)) c').
    do2 2 split.
      rewrite -> project_under_lt; [| omega].
      reflexivity.

      apply index_app_left.
      apply index_subst_ctx.
      eapply index_app_lt; eauto.
      
      rewrite <- !subst_compose.
      rewrite -> !compose_sh_under; [| omega ..].
      rewrite -> !subst_compose.
      replace (length G2 - S i) with (length G2 - i - 1) by omega.
      reflexivity.

    
  have (~ i < length G2) as Hge.
  destruct (gt_dec i (length G2)) as [Hgt | Hle].
    have (i > length G2) as Hgt.
    split.
      assert (index (i - length G2) (G1; c) c') as Hindex' by (eapply index_app_ge; eauto; omega).
      replace (i - length G2) with (S (i - length G2 - 1)) in Hindex' by omega.
      invert Hindex'; intros Hindex''.
      rewrite <- subst_compose.
      rewrite -> compose_sh_under_more; [| omega].
      replace (S i - length G2) with (S (i - length G2)) by omega.
      simp_sub.
      f_equal; f_equal; omega.

      exists (i-1).
      exists c'.
      do2 2 split.
        rewrite -> project_under_ge; [| omega].
        replace (i - length G2) with (S (i - length G2 - 1)) by omega.
        rewrite -> project_dot.
        unfold id; rewrite -> project_sh.
        reduce_subst.
        rewrite -> project_sh.
        replace (length G2 + (0 + (i - length G2 - 1))) with (i - 1) by omega.
        reflexivity.

        replace (i-1) with (i-1 - length G2 + length G2) by omega.
        replace (length G2) with (length (subst_ctx (dot nonsense id) G2)) by (apply subst_ctx_length).
        apply index_app_right.
        rewrite -> subst_ctx_length.
        assert (i >= length (nil; c;; G2)) as Hge' by (rewrite -> app_length; simpl; omega).
        replace (G1; c) with (G1;; (nil; c)) in Hindex by (simpl; auto).
        rewrite -> app_assoc in Hindex.
        pose proof (index_app_ge _#5 Hge' Hindex) as Hindex'.
        rewrite -> app_length in Hindex'; simpl in Hindex'.
        replace (i - 1 - length G2) with (i - (length G2 + 1)) by omega.
        exact Hindex'.

        rewrite -> compose_sh_under_more; [| omega].
        replace (S i - length G2) with (S (i - length G2)) by omega.
        simp_sub.
        replace (i - 1 + 1) with i by omega.
        replace (i - length G2 + length G2) with i by omega.
        reflexivity.

    have (~ i > length G2) as Hle.
    replace i with (length G2) in Heqvar by omega.
    reduce_subst in Heqvar.
    rewrite -> project_under_ge in Heqvar; [| omega].
    replace (length G2 - length G2) with 0 in Heqvar by omega.
    rewrite -> project_zero in Heqvar.
    reduce_subst in Heqvar.
    discriminate Heqvar.
Qed.


Lemma tmof_var_eq :
  forall U P G i t c,
    index i G c
    -> cl_vl t = subst (sh (S i)) c
    -> tmof U P G (var i) t.
Proof.
intros U P G i t c Hindex Heq.
destruct c;
reduce_subst in Heq; try (discriminate Heq).
(* var *)
rewrite -> project_sh in Heq.
discriminate Heq.

(* vl *)
injection Heq; intro Heq'.
subst t.
apply tmof_var.
assumption.
Qed.


Lemma strengthen_value_gen :
  forall G1 G2 c v,
    value (G1; c;; G2) v
    -> G2 = subst_ctx (dot nonsense sh1) G2
    -> v = subst (under (length G2) (dot nonsense sh1)) v
    -> value (G1;; subst_ctx (dot nonsense id) G2)
         (subst (under (length G2) (dot nonsense id)) v).
Proof.
intros G1 G2 c v Hvalue HeqG2 Heqv.
remember (G1; c;; G2) as G.
destruct Hvalue; subst G; simp_sub; auto with static.
(* var *)
pose proof (strengthen_var _#5 H HeqG2 Heqv) as (_ & i' & c'' & Heqproj & Hindex' & Heq).
rewrite -> Heqproj.
reduce_subst in Heq.
assert (subst (unsh (S i')) (subst (sh (S i')) c'')
        = subst (unsh (S i')) (cl_vl (subst (compose (sh (S i)) (under (length G2) (dot nonsense id))) t)))
    as Heq' by (f_equal; assumption).
rewrite <- subst_compose in Heq'.
rewrite -> compose_sh_unsh in Heq'.
simp_sub in Heq'.
rewrite -> Heq' in Hindex'.
eapply value_var; eauto.
Qed.


Lemma strengthen_tgof_gen :
  forall U G1 G2 c T,
    tgof U (G1; c;; G2) T
    -> G2 = subst_ctx (dot nonsense sh1) G2
    -> T = subst (under (length G2) (dot nonsense sh1)) T
    -> tgof U (G1;; subst_ctx (dot nonsense id) G2) (subst (under (length G2) (dot nonsense id)) T).
Proof.
intros U G1 G2 c T Hof HeqG2 HeqT.
remember (G1; c;; G2) as G.
destruct Hof; subst G; simp_sub; auto with static.
(* var *)
pose proof (strengthen_var _#5 H HeqG2 HeqT) as (_ & i' & c'' & Heqproj & Hindex' & Heq).
rewrite -> Heqproj.
reduce_subst in Heq.
assert (subst (unsh (S i')) (subst (sh (S i')) c'') = subst (unsh (S i')) cl_tg)
    as Heq' by (f_equal; assumption).
rewrite <- subst_compose in Heq'.
rewrite -> compose_sh_unsh in Heq'.
simp_sub in Heq'.
rewrite -> Heq' in Hindex'.
apply tgof_var; auto.
Qed.


Lemma strengthen_fcof_gen :
  forall U G1 G2 c f,
    fcof U (G1; c;; G2) f
    -> G2 = subst_ctx (dot nonsense sh1) G2
    -> f = subst (under (length G2) (dot nonsense sh1)) f
    -> fcof U (G1;; subst_ctx (dot nonsense id) G2) (subst (under (length G2) (dot nonsense id)) f).
Proof.
intros U G1 G2 c f Hof HeqG2 Heqf.
remember (G1; c;; G2) as G.
destruct Hof; subst G; simp_sub; auto with static.
(* tag *)
simp_sub in Heqf.
injection Heqf; intros HeqT.
eauto using strengthen_tgof_gen with static.
Qed.


Lemma strengthen_tmof_xpof_gen :
  (forall U P G1 G2 c m t,
     tmof U P (G1; c;; G2) m t
     -> G2 = subst_ctx (dot nonsense sh1) G2
     -> m = subst (under (length G2) (dot nonsense sh1)) m
     -> t = subst (under (length G2) (dot nonsense sh1)) t
        /\ tmof U P 
             (G1;; subst_ctx (dot nonsense id) G2)
             (subst (under (length G2) (dot nonsense id)) m)
             (subst (under (length G2) (dot nonsense id)) t))
  /\
  (forall U P I G1 G2 c e t,
     xpof U P I (G1; c;; G2) e t
     -> G2 = subst_ctx (dot nonsense sh1) G2
     -> e = subst (under (length G2) (dot nonsense sh1)) e
     -> t = subst (under (length G2) (dot nonsense sh1)) t
        /\ xpof U P I
             (G1;; subst_ctx (dot nonsense id) G2)
             (subst (under (length G2) (dot nonsense id)) e)
             (subst (under (length G2) (dot nonsense id)) t)).
Proof.
#21 exploit
  (tmof_xpof_ind
     (fun U P G m t =>
        forall G1 G2 c,
          G = G1; c;; G2
          -> G2 = subst_ctx (dot nonsense sh1) G2
          -> m = subst (under (length G2) (dot nonsense sh1)) m
          -> t = subst (under (length G2) (dot nonsense sh1)) t
             /\ tmof U P
                  (G1;; subst_ctx (dot nonsense id) G2)
                  (subst (under (length G2) (dot nonsense id)) m)
                  (subst (under (length G2) (dot nonsense id)) t))
     (fun U P I G e t =>
        forall G1 G2 c,
          G = G1; c;; G2
          -> G2 = subst_ctx (dot nonsense sh1) G2
          -> e = subst (under (length G2) (dot nonsense sh1)) e
          -> t = subst (under (length G2) (dot nonsense sh1)) t
             /\ xpof U P I
                  (G1;; subst_ctx (dot nonsense id) G2)
                  (subst (under (length G2) (dot nonsense id)) e)
                  (subst (under (length G2) (dot nonsense id)) t))) as Hind;
try (intros; split; simp_sub; eauto with static; done).

(* var *)
intros U P G i t Hindex G1 G2 c HeqG HeqG2 Heqm.
subst G.
pose proof (strengthen_var _#5 Hindex HeqG2 Heqm) as (Heqc & i' & c'' & Heqproj & Hindex' & Heq).
reduce_subst in Heqc.
injection Heqc; intros Heqt.
split.
  assumption.

  simp_sub.
  rewrite -> Heqproj.
  eapply tmof_var_eq; [|].
    eexact Hindex'.
    
    simp_sub.
    simp_sub in Heq.
    auto; done.

(* prim *)
intros U P G m1 m2 Hofm1 IH1 Hofm2 IH2 G1 G2 c HeqG HeqG2 Heqm.
subst G.
simp_sub.
split; auto; [].
simp_sub in Heqm.
injection Heqm; clear Heqm; intros Heqm2 Heqm1.
pose proof (IH1 _#3 (eq_refl _) HeqG2 Heqm1) as (_ & Hofm1').
pose proof (IH2 _#3 (eq_refl _) HeqG2 Heqm2) as (_ & Hofm2').
eauto with static; done.

(* if *)
intros U P G m0 m1 m2 t Hofm0 IH0 Hofm1 IH1 Hofm2 IH2 G1 G2 c HeqG HeqG2 Heqm.
subst G.
simp_sub.
simp_sub in Heqm.
injection Heqm; clear Heqm; intros Heqm2 Heqm1 Heqm0.
so (IH0 _#3 (eq_refl _) HeqG2 Heqm0) as (_ & Hofm0').
so (IH1 _#3 (eq_refl _) HeqG2 Heqm1) as (Heqt & Hofm1').
so (IH2 _#3 (eq_refl _) HeqG2 Heqm2) as (_ & Hofm2').
eauto with static; done.

(* loc *)
intros U P G l t H G1 G2 c HeqG HeqG2 Heqm.
subst G.
simp_sub.
split.
  f_equal.
  rewrite -> app_length.
  simpl length.
  rewrite -> compose_sh_under_more; [| omega].
  replace (length G2 + S (length G1) - length G2) with (S (length G1)) by omega.
  rewrite -> compose_sh_succ_dot.
  simp_sub.
  f_equal; f_equal; omega.

  rewrite -> app_length.
  simpl length.
  replace (length G2 + S (length G1)) with ((length G1 + 1) + length G2) by omega.
  rewrite <- compose_sh_sh.
  rewrite -> compose_assoc.
  rewrite -> compose_sh_under_all.
  rewrite <- compose_sh_sh.
  simp_sub.
  rewrite -> plus_comm.
  replace (length G2) with (length (subst_ctx (dot nonsense id) G2)) by (rewrite -> subst_ctx_length; auto).
  rewrite <- app_length.
  apply tmof_loc; [].
  assumption.

(* susp *)
intros U P G e t Hof IH G1 G2 c HeqG HeqG2 Heqm.
subst G.
simp_sub.
simp_sub in Heqm.
injection Heqm; intro Heqe.
pose proof (IH _#3 (eq_refl _) HeqG2 Heqe) as (Heqt & Hof').
split; try f_equal; eauto with static; done.

(* lam *)
intros U P G m t1 t2 Hoft1 Hofm IH G1 G2 c HeqG HeqG2 Heqm.
subst G.
simp_sub.
simp_sub in Heqm.
injection Heqm; intros Heqm' Heqt1.
assert (G2; cl_vl t1 = subst_ctx (dot nonsense sh1) (G2; cl_vl t1)) as HeqG2'.
  simpl; simp_sub; repeat (f_equal; auto); done.
rewrite <- under_succ in Heqm'.
assert (G1; c;; G2; cl_vl t1 = G1; c;; (G2; cl_vl t1)) as HeqG' by (simpl; auto).
pose proof (IH _#3 HeqG' HeqG2' Heqm') as (Heqt2 & Hof').
split.
  f_equal; auto.
  apply absent_unshift; [].
  exact Heqt2.

  apply tmof_lam; [|].
    eapply strengthen_tpof_gen; eauto; done.

    rewrite <- under_succ.
    rewrite -> shift1_subst_under.
    exact Hof'.

(* fun *)
intros U P G m t1 t2 Hoft1 Hoft2 Hofm IH G1 G2 c HeqG HeqG2 Heqm.
subst G.
simp_sub.
simp_sub in Heqm.
injection Heqm; clear Heqm.
intros Heqm' Heqt2 Heqt1.
assert (G2; cl_vl (tp_arrow t1 t2); cl_vl (shift1 t1) = subst_ctx (dot nonsense sh1) (G2; cl_vl (tp_arrow t1 t2); cl_vl (shift1 t1))) as HeqG2'.
  simpl; simp_sub; repeat (f_equal; auto); [].
  f_apply shift1 in Heqt1 as Heqt1'.
  simp_sub in Heqt1'.
  assumption.
rewrite <- under_plus2 in Heqm'.
assert (G1; c;; G2; cl_vl (tp_arrow t1 t2); cl_vl (shift1 t1) = G1; c;; (G2; cl_vl (tp_arrow t1 t2); cl_vl (shift1 t1))) as HeqG' by (simpl; auto).
so (IH _#3 HeqG' HeqG2' Heqm') as (HHH & Hof').
split.
  f_equal; auto; done.

  apply tmof_fun; [| |].
    eapply strengthen_tpof_gen; eauto; done.

    eapply strengthen_tpof_gen; eauto; done.

    rewrite -> !subst_ctx_cons in Hof'.
    simpl length in Hof'.
    simp_sub in Hof'.
    simp_sub.
    exact Hof'.

(* app *)
intros U P G m1 m2 t1 t2 Hofm1 IH1 Hofm2 IH2 G1 G2 c HeqG HeqG2 Heqm.
subst G.
simp_sub.
simp_sub in Heqm.
injection Heqm; intros Heqm2 Heqm1.
pose proof (IH1 _#3 (eq_refl _) HeqG2 Heqm1) as (Heqarrow & Hofm1').
pose proof (IH2 _#3 (eq_refl _) HeqG2 Heqm2) as (_ & Hofm2').
simp_sub in Heqarrow.
injection Heqarrow; intros Heqt2 _.
eauto with static; done.

(* ret *)
intros U P G m t Hofm IH G1 G2 c HeqG HeqG2 Heqe.
subst G.
simp_sub.
simp_sub in Heqe.
injection Heqe; intros Heqm.
pose proof (IH _#3 (eq_refl _) HeqG2 Heqm) as (Heqt & Hofm').
eauto with static; done.

(* force *)
intros U P G m t Hofm IH G1 G2 c HeqG HeqG2 Heqe.
subst G.
simp_sub.
simp_sub in Heqe.
injection Heqe; intros Heqm.
pose proof (IH _#3 (eq_refl _) HeqG2 Heqm) as (Heqsusp & Hofm').
simp_sub in Heqsusp.
injection Heqsusp; intros Heqt.
eauto with static; done.

(* bind *)
intros U P I G t1 e1 e2 t2 Hoft Hofe1 IH1 Hofe2 IH2 G1 G2 c HeqG HeqG2 Heqe.
subst G.
simp_sub.
simp_sub in Heqe.
injection Heqe; intros Heqe2 Heqe1 Heqt1.
pose proof (IH1 _#3 (eq_refl _) HeqG2 Heqe1) as (_ & Hofe1').
assert (G2; cl_vl t1 = subst_ctx (dot nonsense sh1) (G2; cl_vl t1)) as HeqG2'.
  simpl; simp_sub; repeat (f_equal; auto); done.
rewrite <- under_succ in Heqe2.
assert (G1; c;; G2; cl_vl t1 = G1; c;; (G2; cl_vl t1)) as HeqG' by (simpl; auto).
pose proof (IH2 _#3 HeqG' HeqG2' Heqe2) as (Heqt2 & Hofe2').
split.
  apply absent_unshift.
  exact Heqt2.

  apply xpof_bind; [| |].
    eapply strengthen_tpof_gen; eauto; done.

    assumption.

    rewrite <- under_succ.
    rewrite -> shift1_subst_under.
    assumption.

(* bind *)
intros U P I1 I2 G t1 e1 e2 t2 Hinit Hoft Hofe1 IH1 Hofe2 IH2 G1 G2 c HeqG HeqG2 Heqe.
subst G.
simp_sub.
simp_sub in Heqe.
injection Heqe; intros Heqe2 Heqe1 Heqt1.
pose proof (IH1 _#3 (eq_refl _) HeqG2 Heqe1) as (_ & Hofe1').
assert (G2; cl_vl t1 = subst_ctx (dot nonsense sh1) (G2; cl_vl t1)) as HeqG2'.
  simpl; simp_sub; repeat (f_equal; auto); done.
rewrite <- under_succ in Heqe2.
assert (G1; c;; G2; cl_vl t1 = G1; c;; (G2; cl_vl t1)) as HeqG' by (simpl; auto).
pose proof (IH2 _#3 HeqG' HeqG2' Heqe2) as (Heqt2 & Hofe2').
split.
  apply absent_unshift.
  exact Heqt2.

  apply xpof_bind_init; [| | |].
    apply subst_init; assumption.

    eapply strengthen_tpof_gen; eauto; done.

    assumption.

    rewrite <- under_succ.
    rewrite -> shift1_subst_under.
    assumption.

(* spec *)
intros U P I G v1 v2 t1 e t2 Hofv1 IHv1 Hofv2 IHv2 Hvalue1 Hvalue2 Hofe3 IHe3 G1 G2 c HeqG HeqG2 Heqe.
subst G.
simp_sub.
simp_sub in Heqe.
injection Heqe; intros Heqe3 Heqv2 Heqv1.
pose proof (IHv1 _#3 (eq_refl _) HeqG2 Heqv1) as (Heqt1 & Hofv1').
pose proof (IHv2 _#3 (eq_refl _) HeqG2 Heqv2) as (_ & Hofv2').
pose proof (IHe3 _#3 (eq_refl _) HeqG2 Heqe3) as (Heqt2 & Hofe3').
split.
  assumption.

  eauto using strengthen_value_gen with static; done.

(* read *)
intros U P G m t Hofm IH G1 G2 c HeqG HeqG2 Heqa.
subst G.
simp_sub.
simp_sub in Heqa.
injection Heqa; intros Heqm.
pose proof (IH _#3 (eq_refl _) HeqG2 Heqm) as (Heqref & Hofm').
simp_sub in Heqref.
injection Heqref; intros Heqt.
eauto with static; done.

(* write *)
intros U P G m1 m2 t Hofm1 IH1 Hofm2 IH2 G1 G2 c HeqG HeqG2 Heqa.
subst G.
simp_sub.
simp_sub in Heqa.
injection Heqa; intros Heqm2 Heqm1.
pose proof (IH1 _#3 (eq_refl _) HeqG2 Heqm1) as (_ & Hofm1').
pose proof (IH2 _#3 (eq_refl _) HeqG2 Heqm2) as (Heqt & Hofm2').
eauto with static; done.

(* rw *)
intros U P G m1 m2 t Hofm1 IH1 Hofm2 IH2 G1 G2 c HeqG HeqG2 Heqa.
subst G.
simp_sub.
simp_sub in Heqa.
injection Heqa; intros Heqm2 Heqm1.
so (IH1 _#3 (eq_refl _) HeqG2 Heqm1) as (_ & Hofm1').
so (IH2 _#3 (eq_refl _) HeqG2 Heqm2) as (Heqt & Hofm2').
eauto with static; done.

(* rmw *)
intros U P G t m1 m2 Hoft Hofm1 IH1 Hofm2 IH2 G1 G2 c HeqG HeqG2 Heqa.
subst G.
simp_sub.
simp_sub in Heqa.
injection Heqa; intros Heqm2 Heqm1 Heqt.
split; [assumption |].
#3 apply xpof_rmw.
  eapply strengthen_tpof_gen; eauto; done.

  so (IH1 _#3 (eq_refl _) HeqG2 Heqm1) as (_ & Hofm1').
  simp_sub in Hofm1'.
  exact Hofm1'.

  rewrite <- under_succ.
  rewrite -> shift1_subst_under.
  assert (G2; cl_vl t = subst_ctx (dot nonsense sh1) (G2; cl_vl t)) as HeqG2'.
    simpl; simp_sub; repeat (f_equal; auto); done.
  assert (G1; c;; G2; cl_vl t = G1; c;; (G2; cl_vl t)) as HeqG' by (simpl; auto).
  rewrite <- under_succ in Heqm2.
  so (IH2 _#3 HeqG' HeqG2' Heqm2) as (_ & Hofm2').
  exact Hofm2'.

(* action *)
intros U P G i t p G1 G2 c HeqG HeqG2 Heqe.
subst G.
simp_sub.
split.
  f_equal; [].
  rewrite -> app_length.
  simpl length.
  rewrite -> compose_sh_under_more; [| omega].
  replace (length G2 + S (length G1) - length G2) with (S (length G1)) by omega.
  rewrite -> compose_sh_succ_dot.
  simp_sub.
  f_equal; f_equal; omega.

  rewrite -> app_length.
  simpl length.
  replace (length G2 + S (length G1)) with ((length G1 + 1) + length G2) by omega.
  rewrite <- compose_sh_sh.
  rewrite -> compose_assoc.
  rewrite -> compose_sh_under_all.
  rewrite <- compose_sh_sh.
  simp_sub.
  rewrite -> plus_comm.
  replace (length G2) with (length (subst_ctx (dot nonsense id) G2)) by (rewrite -> subst_ctx_length; auto).
  rewrite <- app_length.
  eapply xpof_action; done.

(* new *)
intros U P G e t b Hofe IH G1 G2 c HeqG HeqG2 Heqe.
subst G.
simp_sub.
simp_sub in Heqe.
injection Heqe; intros Heqee.
assert (G2; cl_tg; cl_tg = subst_ctx (dot nonsense sh1) (G2; cl_tg; cl_tg)) as HeqG2'.
  simpl; simp_sub; repeat (f_equal; auto); done.
rewrite <- under_plus2 in Heqee.
assert (G1; c;; G2; cl_tg; cl_tg = G1; c;; (G2; cl_tg; cl_tg)) as HeqG' by (simpl; auto).
pose proof (IH _#3 HeqG' HeqG2' Heqee) as (Heqt & Hofe').
split.
  apply absent_unshift.
  apply absent_unshift.
  simp_sub; simpl length in Heqt; simp_sub in Heqt.
  assumption.

  apply xpof_new.
  rewrite <- under_plus2.
  rewrite <- subst_compose.
  rewrite <- compose_sh_under2.
  rewrite -> subst_compose.
  exact Hofe'.

(* fence *)
intros U P I G f e t Hoff Hofe IH G1 G2 c HeqG HeqG2 Heqe.
subst G.
simp_sub.
simp_sub in Heqe.
injection Heqe; intros Heqee Heqf.
pose proof (IH _#3 (eq_refl _) HeqG2 Heqee) as (Heqt & Hofee).
split.
  assumption.

  eauto using strengthen_fcof_gen with static; done.

(* peroration *)
destruct Hind as (Hindm & Hinde).
split.
  intros; eapply Hindm; eauto; done.

  intros; eapply Hinde; eauto; done.
Qed.


Corollary strengthen_tmof_gen :
  forall U P G1 G2 c m t,
     tmof U P (G1; c;; G2) m t
     -> G2 = subst_ctx (dot nonsense sh1) G2
     -> m = subst (under (length G2) (dot nonsense sh1)) m
     -> t = subst (under (length G2) (dot nonsense sh1)) t
        /\ tmof U P 
             (G1;; subst_ctx (dot nonsense id) G2)
             (subst (under (length G2) (dot nonsense id)) m)
             (subst (under (length G2) (dot nonsense id)) t).
Proof.
exact (strengthen_tmof_xpof_gen andel).
Qed.


Lemma strengthen_acof_gen :
  forall U P G1 G2 c a t,
     acof U P (G1; c;; G2) a t
     -> G2 = subst_ctx (dot nonsense sh1) G2
     -> a = subst (under (length G2) (dot nonsense sh1)) a
     -> t = subst (under (length G2) (dot nonsense sh1)) t
        /\ acof U P 
             (G1;; subst_ctx (dot nonsense id) G2)
             (subst (under (length G2) (dot nonsense id)) a)
             (subst (under (length G2) (dot nonsense id)) t).
Proof.
intros U P G1 G2 c a t Hofa.
remember (G1; c;; G2) as G eqn:HeqG.
revert HeqG.
induct Hofa.
(* read *)
intros l U P G t Hlookup HeqG HeqG2 Heqa.
subst G.
simp_sub.
split.
  f_equal.
  rewrite -> app_length.
  simpl length.
  rewrite -> compose_sh_under_more; [| omega].
  replace (length G2 + S (length G1) - length G2) with (S (length G1)) by omega.
  rewrite -> compose_sh_succ_dot.
  simp_sub.
  f_equal; f_equal; omega.

  rewrite -> app_length.
  simpl length.
  replace (length G2 + S (length G1)) with ((length G1 + 1) + length G2) by omega.
  rewrite <- compose_sh_sh.
  rewrite -> compose_assoc.
  rewrite -> compose_sh_under_all.
  rewrite <- compose_sh_sh.
  simp_sub.
  rewrite -> plus_comm.
  replace (length G2) with (length (subst_ctx (dot nonsense id) G2)) by (rewrite -> subst_ctx_length; auto).
  rewrite <- app_length.
  apply acof_read.
  assumption.

(* write *)
intros U P G l v t Hlookup Hvalue Hofv HeqG HeqG2 Heqa.
subst G.
simp_sub.
simp_sub in Heqa.
injection Heqa; intros Heqv.
split.
  reflexivity.

  eapply acof_write; eauto using strengthen_value_gen.
  pose proof (strengthen_tmof_gen _#7 Hofv HeqG2 Heqv) as (_ & Hofv').
  rewrite <- subst_compose in Hofv'.
  rewrite -> app_length in Hofv'.
  simpl length in Hofv'.
  replace (length G2 + S (length G1)) with ((length G1 + 1) + length G2) in Hofv' by omega.
  rewrite <- compose_sh_sh in Hofv'.
  rewrite -> compose_assoc in Hofv'.
  rewrite -> compose_sh_under_all in Hofv'.
  rewrite <- compose_assoc in Hofv'.
  replace (length G1 + 1) with (S (length G1)) in Hofv' by omega.
  simp_sub in Hofv'.
  rewrite -> app_length.
  rewrite -> subst_ctx_length.
  rewrite -> plus_comm.
  assumption.

(* rw *)
intros U P G l v t Hlookup Hvalue Hofv HeqG HeqG2 Heqa.
subst G.
simp_sub.
simp_sub in Heqa.
injection Heqa; intros Heqv.
split.
  f_equal.
  rewrite -> app_length.
  simpl length.
  rewrite -> compose_sh_under_more; [| omega].
  replace (length G2 + S (length G1) - length G2) with (S (length G1)) by omega.
  rewrite -> compose_sh_succ_dot.
  simp_sub.
  f_equal; omega.
  
  rewrite -> app_length.
  simpl length.
  replace (length G2 + S (length G1)) with ((length G1 + 1) + length G2) by omega.
  rewrite <- compose_sh_sh.
  rewrite -> compose_assoc.
  rewrite -> compose_sh_under_all.
  rewrite <- compose_sh_sh.
  simp_sub.
  rewrite -> plus_comm.
  replace (length G2) with (length (subst_ctx (dot nonsense id) G2)) by (rewrite -> subst_ctx_length; auto).
  rewrite <- app_length.
  #2 eapply acof_rw; eauto.
    rewrite -> subst_ctx_length; [].
    eapply strengthen_value_gen; eauto; done.
  pose proof (strengthen_tmof_gen _#7 Hofv HeqG2 Heqv) as (_ & Hofv').
  rewrite <- subst_compose in Hofv'.
  rewrite -> app_length in Hofv'.
  simpl length in Hofv'.
  replace (length G2 + S (length G1)) with ((length G1 + 1) + length G2) in Hofv' by omega.
  rewrite <- compose_sh_sh in Hofv'.
  rewrite -> compose_assoc in Hofv'.
  rewrite -> compose_sh_under_all in Hofv'.
  rewrite <- compose_assoc in Hofv'.
  replace (length G1 + 1) with (S (length G1)) in Hofv' by omega.
  simp_sub in Hofv'.
  rewrite -> app_length.
  rewrite -> subst_ctx_length.
  rewrite -> plus_comm.
  assumption.

(* push *)
intros U P G HeqG HeqG2 Heqa.
simp_sub.
auto with static.

(* nop *)
intros U P G HeqG HeqG2 Heqa.
simp_sub.
auto with static.
Qed.


Lemma strengthen_flof_gen :
  forall U G1 G2 c fl,
    flof U (G1; c;; G2) fl
    -> G2 = subst_ctx (dot nonsense sh1) G2
    -> fl = subst (under (length G2) (dot nonsense sh1)) fl
    -> flof U
         (G1;; subst_ctx (dot nonsense id) G2)
         (subst (under (length G2) (dot nonsense id)) fl).
Proof.
intros U G1 G2 c fl Hof.
remember (G1; c;; G2) as G eqn:HeqG.
revert HeqG.
induct Hof.
(* nil *)
intros U G HeqG HeqG2 _.
simp_sub.
apply flof_nil.

(* cons *)
intros U G f fl Hoffl IHfl Hoff HeqG HeqG2 Heqcons.
subst G.
simp_sub.
simp_sub in Heqcons.
injection Heqcons; intros Heqfl Heqf.
eauto using IHfl, strengthen_fcof_gen with static.
Qed.


Lemma strengthen_trofo_gen :
  forall U P I G1 G2 c d,
    trofo U P I (G1; c;; G2) d
    -> G2 = subst_ctx (dot nonsense sh1) G2
    -> d = subst (under (length G2) (dot nonsense sh1)) d
    -> trofo U P I
         (G1;; subst_ctx (dot nonsense id) G2)
         (subst (under (length G2) (dot nonsense id)) d).
Proof.
intros U P I G1 G2 c d Hof HeqG2 Heqd.
remember (G1; c;; G2) as G eqn:HeqG.
revert Heqd HeqG.
induct Hof.
(* nothing *)
intros U P I G Heqd HeqG.
simp_sub.
auto with static.

(* init *)
intros U P I G fl i a t Hoffl Hofa Heqd HeqG.
subst G.
simp_sub.
simp_sub in Heqd.
injection Heqd; intros Heqa Heqfl.
eapply trofo_init; eauto using strengthen_flof_gen.
eapply strengthen_acof_gen; eauto.

(* exec *)
intros U P I G i v Heqd HeqG.
simp_sub.
auto with static.

(* new *)
intros U P I G b T T' Heqd HeqG.
simp_sub.
auto with static.
Qed.


Corollary strengthen_trofo :
  forall U P I G c d,
    trofo U P I (G; c) (shift1 d)
    -> trofo U P I G d.
Proof.
intros U P I G c d Hof.
replace (G; c) with (G; c;; nil) in Hof by auto.
assert (shift1 d = subst (under 0 (dot nonsense sh1)) (shift1 d)) as Heq by (simp_sub; auto).
pose proof (strengthen_trofo_gen _#7 Hof (eq_refl _) Heq) as Hof'.
simp_sub in Hof'.
exact Hof'.
Qed.
