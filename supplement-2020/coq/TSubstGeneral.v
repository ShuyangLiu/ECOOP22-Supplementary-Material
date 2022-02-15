
Require Import Tactics.
Require Import Arith.
Require Export Subst.
Require Import Sequence.
Require Import Static.
Require Import Omega.


(* Generic development: parameterized over Syntax and Static:STATIC where: *)

Module Type STATIC.

Definition context := list term.

Parameter isclx : term -> Prop.

Axiom subst_cl :
  forall s c, isclx c -> isclx (subst s c).

Notation "G , t" := (cons t G) (at level 65, left associativity).

End STATIC.


(*
To check parametrically, remove Static import and:

Declare Module Static : STATIC.
Import Static.
Definition iscl := isclx.
*)


(* Verify that Static satisfies STATIC. *)
Module StaticCheck <: STATIC := Static.

Goal Static.isclx = iscl.
Proof. auto. Qed.



Definition behaved (R : context -> term -> term -> Prop) : Prop :=
  forall G i c,
    iscl c
    -> index i G c
    -> R G (var i) (subst (sh (S i)) c).


Inductive subof (R : context -> term -> term -> Prop) : context -> sub -> context -> Prop :=
| subof_dot {G t s c G'}
    : subof R G s G'
      -> R G t (subst s c)
      -> subof R G (dot t s) (G'; c)

| subof_sh {G n G'}
    : truncate n G G'
      -> subof R G (sh n) G'.


Hint Constructors subof : static.


Lemma subof_mono :
  forall (R : _ -> _ -> _ -> Prop) (R' : _ -> _ -> _ -> Prop),
    (forall G1 t c, R G1 t c -> R' G1 t c)
    -> forall G1 G2 s, subof R G1 s G2 -> subof R' G1 s G2.
Proof.
intros R R' HR G1 G2 s Hs.
induction Hs.
(* dot *)
apply subof_dot.
apply IHHs.
apply HR, H.

(* sh *)
apply subof_sh.
auto.
Qed.


Hint Resolve subof_mono : substlem.


(* weakening closure: need to strengthen the induction hypothesis for substitution *)
Definition wc (R : context -> term -> term -> Prop) (G : context) (t : term) (c : term) : Prop :=
  forall G' n, truncate n G' G -> R G' (subst (sh n) t) (subst (sh n) c).


Lemma wc_mono :
  forall (R1 : _ -> _ -> _ -> Prop) (R2 : _ -> _ -> _ -> Prop),
    (forall G t c, R1 G t c -> R2 G t c)
    -> forall G t c,
         wc R1 G t c -> wc R2 G t c.
Proof.
intros R1 R2 HR.
intros G t c H.
unfold wc.
auto.
Qed.


Hint Resolve wc_mono : substlem.


Lemma wc_elim :
  forall R G t c,
    wc R G t c -> R G t c.
Proof.
intros R G t c H.
unfold wc in H.
assert (truncate 0 G G) as Htrunc by auto with sequence.
pose proof (H _ _ Htrunc) as H'.
simp_sub in H'.
assumption.
Qed.


Lemma wc_weaken :
  forall R G1 G2 n t c,
    truncate n G1 G2
    -> wc R G2 t c
    -> wc R G1 (subst (sh n) t) (subst (sh n) c).
Proof.
intros R G1 G2 n t c Htr Ht.
have (truncate n G1 G2) as Htr.
have (wc R G2 t c) as Ht.
toshow (wc R G1 (subst (sh n) t) (subst (sh n) c)).
intros G3 m Htr'.
have (truncate m G3 G1) as Htr'.
toshow (R G3 (subst (sh m) (subst (sh n) t)) (subst (sh m) (subst (sh n) c))).
simp_sub.
apply Ht.
replace (n+m) with (m+n) by omega.
eapply truncate_sum; eauto.
Qed.


Lemma wc_behaved :
  forall R,
    behaved R -> behaved (wc R).
Proof.
intros R HR.
unfold behaved.
intros G i c Hc Hindex.
toshow (wc R G (var i) (subst (sh (S i)) c)).
intros G' n Htrunc.
toshow (R G' (subst (sh n) (var i)) (subst (sh n) (subst (sh (S i)) c))).
repeat simp_sub.
replace (i + n + 1) with (S (n+i)) by omega.
apply HR.
apply Hc.
eapply truncate_index_sum; eauto.
Qed.


Lemma subof_wc_truncate_left_1 :
  forall R G1 G2 s c,
    subof (wc R) G1 s G2
    -> subof (wc R) (G1; c) (compose s (sh 1)) G2.
Proof.
intros R G1 G2 s c Hs.
induction Hs.
(* dot *)
have (subof (wc R) G s G') as Hs.
have (wc R G t (subst s c0)) as H.
have (subof (wc R) (G; c) (compose s (sh 1)) G') as IHHs.
toshow (subof (wc R) (G; c) (compose (dot t s) (sh 1)) (G'; c0)).
simp_sub.
apply subof_dot.
toshow (subof (wc R) (G; c) (compose s sh1) G').
apply IHHs.

toshow (wc R (G; c) (shift1 t) (subst (compose s sh1) c0)).
unfold shift1.
rewrite -> subst_compose.
eapply wc_weaken.
eauto with sequence.
assumption.

(* sh *)
have (truncate n G G') as H.
toshow (subof (wc R) (G; c) (compose (sh n) (sh 1)) G').
simp_sub.
apply subof_sh.
replace (n+1) with (S n) by omega.
auto with sequence.
Qed.


Lemma subof_wc_bind :
  forall R,
    behaved R
    -> forall G G' s c,
         iscl c
         -> subof (wc R) G s G'
         -> subof (wc R) (G; subst s c) (dot (var 0) (compose s sh1)) (G'; c).
Proof.
intros R HR G G' s c Hc Hs.
apply subof_dot.
toshow (subof (wc R) (G; subst s c) (compose s sh1) G').
replace sh1 with (sh 1) by (simp_sub; auto).
apply subof_wc_truncate_left_1.
apply Hs.

toshow (wc R (G; subst s c) (var 0) (subst (compose s sh1) c)).
replace (subst (compose s sh1) c) with (subst (sh 1) (subst s c)) by (simp_sub; auto).
apply (wc_behaved R HR).
apply subst_cl.
assumption.
apply index_0.
Qed.


Lemma subof_index :
  forall R,
    behaved R
    -> forall G1 G2 s i c,
         iscl c
         -> subof R G1 s G2
         -> index i G2 c
         -> R G1 (project s i) (subst (compose (sh (S i)) s) c).
Proof.
intros R HR G1 G2 s i c Hc Hs Hindex.
generalize dependent i.
induction Hs; intros i Hindex.
(* dot *)
destruct i.
simp_sub.
inversion Hindex as [x l |]; subst x l c0.
apply H.

rewrite -> project_dot.
rewrite -> compose_sh_succ_dot.
apply IHHs.
inversion Hindex; subst.
assumption.

(* sh *)
simp_sub.
replace (i+n+1) with (S (n+i)) by omega.
apply HR.
apply Hc.
eapply truncate_index_sum; eauto.
Qed.


Lemma wc_intro :
  forall R,
    (forall G1 G2 s t c,
       subof (wc R) G1 s G2
       -> R G2 t c
       -> R G1 (subst s t) (subst s c))
    -> forall G t c,
         R G t c -> wc R G t c.
Proof.
intros R HR G t c H.
have (R G t c) as H.
toshow (wc R G t c).
intros G' n Htrunc.
have (truncate n G' G) as Htrunc.
toshow (R G' (subst (sh n) t) (subst (sh n) c)).
thus (subof (wc R) G' (sh n) G) as Hn by subof_sh.
apply (HR _#5 Hn).
assumption.
Qed.


Lemma subof_id :
  forall R G, subof R G id G.
Proof.
intros R G.
apply subof_sh.
apply truncate_0.
Qed.


Hint Resolve subof_id : static.


Lemma subof_sh_all :
  forall R G1 G2 s,
    subof R G1 s G2
    -> compose (sh (length G2)) s = sh (length G1).
Proof.
intros R G1 G2 s Hs.
induction Hs.
(* dot *)
simpl length.
simp_sub.
apply IHHs.

(* sh *)
thus (length G = n + length G') as H' by truncate_length.
simp_sub.
f_equal.
omega.
Qed.


Lemma subof_close :
  forall R G,
    subof R G (sh (length G)) nil.
Proof.
intros R G.
apply subof_sh.
apply truncate_all.
Qed.



Fixpoint subst_ctx (s : sub) (G : context) {struct G} : context :=
  (match G with
   | nil => nil
   | G'; c => subst_ctx s G'; subst (under (length G') s) c
   end).
    

Lemma subst_ctx_cons :
  forall s G c,
    subst_ctx s (G; c) = subst_ctx s G; subst (under (length G) s) c.
Proof.
intros.
reflexivity.
Qed.


Lemma subst_ctx_length :
  forall s G,
    length (subst_ctx s G) = length G.
Proof.
intros s G.
induction G.
(* 0 *)
reflexivity.

(* S *)
simpl.
f_equal; apply IHG.
Qed.


Lemma index_subst_ctx :
  forall G i c s,
    index i G c
    -> index i (subst_ctx s G) (subst (under (length G - i - 1) s) c).
Proof.
intros G i c s Hindex.
induct Hindex.
(* 0 *)
intros c G.
simpl.
replace (length G - 0) with (length G) by omega.
apply index_0.

(* S *)
intros i c G c' _ IH.
thus (i < length (subst_ctx s G)) as Hlt by index_length.
rewrite -> subst_ctx_length in Hlt.
replace (length (G; c) - S i) with (length G - i) by (simpl length; omega).
apply index_S.
exact IH.
Qed.


Lemma subof_under :
  forall R,
    behaved R
    -> (forall G t c, R G t c -> wc R G t c)
    -> forall G1 G1' G2 s,
         Forall iscl G2
         -> subof R G1 s G1'
         -> subof R (G1;; subst_ctx s G2) (under (length G2) s) (G1';; G2).
Proof.
intros R Hbehaved Hwc G1 G1' G2 s Hallcl Hofs.
induction G2 as [| c G2].
(* nil *)
simpl.
assumption.

(* cons *)
simpl subst_ctx.
simpl length.
simpl app.
simp_sub.
apply (subof_mono (wc R)); [apply wc_elim |].
invert Hallcl; intros Hiscl Hallcl'.
apply subof_wc_bind; auto.
apply (subof_mono R); [apply Hwc |].
apply IHG2; auto.
Qed.
