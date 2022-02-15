
Require Import Tactics.
Require Import Omega.
Require Import Wf_nat.
Require Export Relation_Definitions.
Require Import List.
Require Import Decidable.


Definition irreflexive (T : Set) (R : T -> T -> Prop) :=
  ~ exists x, R x x.


(* reflexive, transitive closure *)
Inductive star {T : Set} (R : T -> T -> Prop) : T -> T -> Prop :=
| star_refl {x}
    : star R x x

| star_step {x y z}
    : R x y
      -> star R y z
      -> star R x z.


Inductive starr {T : Set} (R : T -> T -> Prop) : T -> T -> Prop :=
| starr_refl {x}
    : starr R x x

| starr_step {x y z}
    : starr R x y
      -> R y z
      -> starr R x z.


Lemma star_trans :
  forall (T : Set) (R : T -> T -> Prop) x y z,
    star R x y -> star R y z -> star R x z.
Proof.
intros T R x y z Hxy Hyz.
induction Hxy.
assumption.
eapply star_step.
eexact H.
apply IHHxy; auto.
Qed.


Lemma star_transitive :
  forall (T : Set) (R : T -> T -> Prop),
    transitive T (star R).
Proof.
exact star_trans.
Qed.


Lemma star_one :
  forall (T : Set) (R : T -> T -> Prop) x y,
    R x y -> star R x y.
Proof.
intros T R x y H.
eapply star_step.
eassumption.
apply star_refl.
Qed.


Lemma star_stepr :
  forall (T : Set) (R : T -> T -> Prop) x y z,
    star R x y
    -> R y z
    -> star R x z.
Proof.
intros.
eapply star_trans.
  eassumption.

  apply star_one; auto.
Qed.


Lemma star_mono :
  forall (T : Set) (R R' : T -> T -> Prop),
    (forall x y, R x y -> R' x y)
    -> forall x y, star R x y -> star R' x y.
Proof.
intros T R R' HR x y H.
induction H.
apply star_refl.
eapply star_step.
apply HR; eassumption.
assumption.
Qed.


Lemma star_map :
  forall (S T : Set) (R : S -> S -> Prop) (R' : T -> T -> Prop) (f : S -> T),
    (forall x y, R x y -> R' (f x) (f y))
    -> forall x y, star R x y -> star R' (f x) (f y).
Proof.
intros S T R R' f HR x y H.
induct H.

(* refl *)
intros x.
apply star_refl; done.

(* step *)
intros x y z Hxy _ IH.
eapply star_step; eauto; done.
Qed.


Lemma star_starr :
  forall (T : Set) (R : T -> T -> Prop) x y,
    star R x y
    -> starr R x y.
Proof.
intros T R x y Hstar.
thus (starr R x x) as Hacc by @starr_refl.
remember x as z in Hacc at 1 |- * at 1.
clear Heqz; revert Hacc.
elim Hstar; clear x y Hstar.
(* refl *)
intros x Hacc.
assumption.

(* step *)
intros x y w HR _ IH Hacc.
apply IH.
eapply starr_step; eauto.
Qed.


Definition compose {T : Set} (R R' : T -> T -> Prop) (x x' : T) : Prop :=
  exists x'', R x x'' /\ R' x'' x'.


(* transitive closure *)
Definition plus {T : Set} (R : T -> T -> Prop) : T -> T -> Prop :=
  compose R (star R).


Definition plusr {T : Set} (R : T -> T -> Prop) : T -> T -> Prop :=
  compose (star R) R.


Inductive plusi {T : Set} (R : T -> T -> Prop) : T -> T -> Prop :=
| plusi_one {x y}
    : R x y
      -> plusi R x y

| plusi_step {x y z}
    : R x y
      -> plusi R y z
      -> plusi R x z.


Inductive plusri {T : Set} (R : T -> T -> Prop) : T -> T -> Prop :=
| plusri_one {x y}
    : R x y
      -> plusri R x y

| plusri_step {x y z}
    : plusri R x y
      -> R y z
      -> plusri R x z.


Lemma plus_star :
  forall (T : Set) (R : T -> T -> Prop) x y,
    plus R x y -> star R x y.
Proof.
intros T R x y H.
destruct H as (z & H1 & H2).
eapply star_step; eauto.
Qed.


Lemma star_plus :
  forall (T : Set) (R : T -> T -> Prop) x y,
    star R x y -> x = y \/ plus R x y.
Proof.
intros T R x y H.
destruct H as [ | x y z Hxy Hyz].
  left; auto.

  right.
  exists y.
  auto.
Qed.
  

Lemma star_neq_plus :
  forall (T : Set) (R : T -> T -> Prop) x y,
    star R x y -> x <> y -> plus R x y.
Proof.
intros T R x y Hstar Hneq.
so (star_plus _#4 Hstar) as [Heq | Hplus].
  destruct Hneq; assumption.

  assumption.
Qed.


Lemma plus_one :
  forall (T : Set) (R : T -> T -> Prop) x y,
    R x y -> plus R x y.
Proof.
intros T R x y H.
exists y.
split.
assumption.
apply star_refl.
Qed.


Lemma plusr_plus :
  forall (T : Set) (R : T -> T -> Prop) x y,
    plusr R x y -> plus R x y.
Proof.
intros T R x y H.
destruct H as (z & Hxz & Hzy).
destruct Hxz.
  apply plus_one; auto.

  exists y0.
  split.
    assumption.

    eapply star_trans.
    apply Hxz.
    apply star_one.
    apply Hzy.
Qed.


Lemma plus_plusr :
  forall (T : Set) (R : T -> T -> Prop) x y,
    plus R x y -> plusr R x y.
Proof.
unfold plus, plusr.
intros T R x y H.
destruct H as (z & H1 & H2).
generalize dependent H1.
generalize dependent x.
induction H2 as [ | a b c Ha Hb IHstar].

(* nil *)
intros y H.
exists y.
split.
apply star_refl.
assumption.

(* cons *)
intros x Hx.
have (R a b) as Ha.
have (star R b c) as Hb.
have (R x a) as Hx.
have (forall x : T, R x b -> compose (star R) R x c) as IHstar.
toshow (compose (star R) R x c).
pose proof (IHstar a Ha) as (y & Ha' & Hy).
have (star R a y) as Ha'.
have (R y c) as Hy.
exists y.
toshow (star R x y /\ R y c).
split; [| apply Hy].
eapply star_step; eauto.
Qed.


Lemma plus_trans :
  forall (T : Set) (R : T -> T -> Prop) x y z,
    plus R x y -> plus R y z -> plus R x z.
Proof.
intros T R x y z Hxy Hyz.
destruct Hxy as (w & Hxw & Hwy).
thus (star R y z) as Hyz' by plus_star.
thus (star R w z) as Hwz by star_trans.
exists w; auto.
Qed.


Lemma plus_transitive :
  forall (T : Set) (R : T -> T -> Prop),
    transitive T (plus R).
Proof.
exact plus_trans.
Qed.


Lemma plus_star_trans :
  forall (T : Set) (R : T -> T -> Prop) x y z,
    plus R x y -> star R y z -> plus R x z.
Proof.
intros T R x y z Hplus Hstar.
destruct Hplus as (w & HR & Hstar').
exists w.
split; eauto using star_trans; done.
Qed.


Lemma star_plus_trans :
  forall (T : Set) (R : T -> T -> Prop) x y z,
    star R x y -> plus R y z -> plus R x z.
Proof.
intros T R x y z Hxy Hyz.
apply plusr_plus.
thus (plusr R y z) as Hyz' by plus_plusr.
destruct Hyz' as (w & Hyw & Hwz).
thus (star R x w) as Hxw by star_trans.
exists w; auto.
Qed.


Lemma plus_plusi :
  forall (T : Set) (R : T -> T -> Prop) x y,
    plus R x y -> plusi R x y.
Proof.
intros T R x y Hplus.
pose proof (plus_plusr _#4 Hplus) as (z & Hstar & HR).
thus (plusi R z y) as Hacc by @plusi_one.
clear Hplus HR.
revert Hacc.
induction Hstar.
(* refl *)
auto.

(* step *)
intro Hacc.
eapply plusi_step.
  eassumption.

  apply IHHstar; auto.
Qed.


Lemma plusi_plus :
  forall (T : Set) (R : T -> T -> Prop) x y,
    plusi R x y -> plus R x y.
Proof.
intros T R x y Hplusi.
induction Hplusi.
(* one *)
apply plus_one; auto.

(* step *)
eapply plus_trans; eauto using plus_one.
Qed.


Lemma plus_plusri :
  forall (T : Set) (R : T -> T -> Prop) x y,
    plus R x y -> plusri R x y.
Proof.
intros T R x y Hplus.
destruct Hplus as (z & HR & Hstar).
thus (plusri R x z) as Hacc by @plusri_one.
clear HR.
revert Hacc.
induct Hstar.
(* refl *)
auto; done.

(* step *)
intros w y z HR _ IH Hacc.
apply IH.
eapply plusri_step; eauto; done.
Qed.


Lemma plusri_plus :
  forall (T : Set) (R : T -> T -> Prop) x y,
    plusri R x y -> plus R x y.
Proof.
intros T R x y Hplusri.
induction Hplusri.
(* one *)
apply plus_one; auto; done.

(* step *)
eapply plus_trans; eauto using plus_one; done.
Qed.


Lemma plus_step :
  forall (T : Set) (R : T -> T -> Prop) x y z,
    R x y -> plus R y z -> plus R x z.
Proof.
intros.
exists y.
auto using plus_star.
Qed.

Lemma plus_stepr  :
  forall (T : Set) (R : T -> T -> Prop) x y z,
    star R x y
    -> R y z
    -> plus R x z.
Proof.
  intros.
  eapply star_plus_trans.
  eauto.
  eapply plus_one.
  auto.
Qed.

Lemma plus_mono :
  forall (T : Set) (R R' : T -> T -> Prop),
    (forall x y, R x y -> R' x y)
    -> forall x y, plus R x y -> plus R' x y.
Proof.
intros T R R' HR x y H.
destruct H as (z & H1 & H2).
exists z; split.
  apply HR; auto.

  apply (star_mono _ R); auto.
Qed.


Lemma plus_idem :
  forall (T : Set) (R : T -> T -> Prop) x y,
    plus R x y <-> plus (plus R) x y.
Proof.
intros T R x y.
split.
  intro Hp.
  apply plus_one; auto; done.

  intro Hpp.
  elim (plus_plusi _#4 Hpp); clear x y Hpp; auto; [].
  intros x y z Hxy _ Hyz.
  eapply plus_trans; eauto; done.
Qed.


Lemma plus_of_transitive :
  forall (T : Set) (R : T -> T -> Prop),
    transitive T R
    -> forall x y, plus R x y -> R x y.
Proof.
intros T R Htrans x y Hplus.
so (plus_plusi _#4 Hplus) as Hplus'; clear Hplus.
induct Hplus'; eauto using Htrans.
Qed.


Lemma plus_well_founded :
  forall (T : Set) (R : T -> T -> Prop),
    well_founded R
    -> well_founded (plus R).
Proof.
intros T R Hwf.
unfold well_founded.
apply (well_founded_ind Hwf (Acc (plus R))).
intros x IH.
apply Acc_intro; [].
intros y Hyx.
remember x as x' eqn:Heq in Hyx.
so (plus_plusi _#4 Hyx) as Hyx'; clear Hyx.
revert Heq.
induct Hyx'.
  intros y x' Hyz ->.
  apply IH; auto; done.

  intros y z x' Hyz Hxz IH' ->.
  apply (@Acc_inv _ _ z); auto; [].
  apply plus_one; auto; done.
Qed.


Lemma plus_ind :
  forall (T : Set) (R P : T -> T -> Prop),
    (forall x y z, R x y -> (y = z \/ (plus R y z /\ P y z)) -> P x z)
    -> forall x y, plus R x y -> P x y.
Proof.
intros T R P Hind x y Hxy.
so (plus_plusi _#4 Hxy) as Hxy'; clear Hxy.
induct Hxy'.

(* one *)
intros x y Hxy.
apply (Hind x y y); auto; done.

(* step *)
intros x y z Hxy Hyz IH.
apply (Hind x y z); auto; [].
right.
auto using plusi_plus.
Qed.


Lemma plus_ind_r :
  forall (T : Set) (R P : T -> T -> Prop),
    (forall x y z, (x = y \/ (plus R x y /\ P x y)) -> R y z -> P x z)
    -> forall x y, plus R x y -> P x y.
Proof.
intros T R P Hind x y Hxy.
so (plus_plusri _#4 Hxy) as Hxy'; clear Hxy.
induct Hxy'.

(* one *)
intros x y Hxy.
apply (Hind x x y); auto; done.

(* step *)
intros x y z Hxy IH Hyz.
apply (Hind x y z); auto; [].
right.
auto using plusri_plus.
Qed.


Definition transpose {T : Set} (R : T -> T -> Prop) x x' : Prop :=
  R x' x.


Lemma transpose_inv :
  forall (T : Set) (R : T -> T -> Prop) x y,
    transpose (transpose R) x y <-> R x y.
Proof.
intros T R x y.
unfold transpose.
split; auto.
Qed.


Lemma star_transpose :
  forall (T : Set) (R : T -> T -> Prop) x y,
    star (transpose R) y x -> star R x y.
Proof.
intros T R x y H.
induction H.
apply star_refl.
eapply star_trans.
eexact IHstar.
unfold transpose in H.
apply star_one.
exact H.
Qed.


Lemma star_transpose_intro :
  forall (T : Set) (R : T -> T -> Prop) x y,
    star R x y -> star (transpose R) y x.
Proof.
intros T R x y H.
apply star_transpose.
eapply star_mono; [| eassumption].
clear x y H.
intros x y H.
apply transpose_inv; assumption.
Qed.


Lemma plus_transpose :
  forall (T : Set) (R : T -> T -> Prop) x y,
    plus (transpose R) y x -> plus R x y.
Proof.
intros T R x y H.
destruct H as (z & H & H').
apply plusr_plus.
exists z; split.
  apply star_transpose; auto; done.

  assumption.
Qed.


Lemma plus_transpose_intro :
  forall (T : Set) (R : T -> T -> Prop) x y,
    plus R x y -> plus (transpose R) y x.
Proof.
intros T R x y H.
destruct H as (z & H & H').
apply plusr_plus.
exists z; split.
  apply star_transpose_intro; auto; done.
  
  assumption.
Qed.


Lemma transitive_transpose :
  forall (T : Set) (R : T -> T -> Prop),
    transitive T R
    -> transitive T (transpose R).
Proof.
intros T R Htrans.
intros x y z Hxy Hzy.
eapply Htrans.
  eexact Hzy.

  eexact Hxy.
Qed.


Lemma antisymmetric_transpose :
  forall (T : Set) (R : T -> T -> Prop),
    antisymmetric T R
    -> antisymmetric T (transpose R).
Proof.
intros T R Hantisymm.
intros x y Hxy Hyx.
apply Hantisymm; auto.
Qed.


Lemma decidable_transpose :
  forall (T : Set) (R : T -> T -> Prop),
    (forall x y, decidable (R x y))
    -> (forall x y, decidable (transpose R x y)).
Proof.
intros T R Hdec x y.
apply Hdec.
Qed.


Definition union {T : Set} (R1 R2 : T -> T -> Prop) x y := R1 x y \/ R2 x y.



Definition acyclic {T : Set} (R : T -> T -> Prop) :=
  ~ (exists x, plus R x x).


Lemma acyclic_plus :
  forall (T : Set) (R : T -> T -> Prop),
    acyclic R
    -> acyclic (plus R).
Proof.
intros T R Hacy.
intros (x & Hpp).
destruct Hacy.
exists x.
apply plus_idem; assumption.
Qed.


Lemma acyclic_transpose :
  forall (T : Set) (R : T -> T -> Prop),
    acyclic R -> acyclic (transpose R).
Proof.
intros T R H (x & H').
apply H.
exists x.
destruct H' as (y & Hxy & Hyx).
apply plusr_plus.
exists y.
split.
apply star_transpose; assumption.
unfold transpose in Hxy; assumption.
Qed.


Lemma acyclic_anti :
  forall (T : Set) (R R' : T -> T -> Prop),
    (forall x y, R x y -> R' x y)
    -> acyclic R'
    -> acyclic R.
Proof.
intros T R R' Hincl Hacyclic.
intros (x & Hpath).
destruct Hacyclic.
exists x.
apply (plus_mono _ R); auto.
Qed.


Lemma acyclic_extend :
  forall (T : Set) (R R' : T -> T -> Prop),
    acyclic R
    -> (forall x y, R x y -> R' x y)
    -> (forall x y, R' x y -> R x y \/ ~ star R' y x)
    -> acyclic R'.
Proof.
intros T R R' Hacyclic Hincl Hcond.
(* strengthen IH *)
assert (forall x y z, star R x y -> R' y z -> star R' z x -> False) as Hind.
  intros x y z Hleft Hmid Hright.
  have (acyclic R) as Hacyclic.
  have (forall x y : T, R x y -> R' x y) as Hincl.
  have (forall x y : T, R' x y -> R x y \/ ~ star R' y x) as Hcond.
  revert dependent y.
  elim Hright; clear x z Hright.
  (* refl *)
  intros x y Hleft Hmid.
  have (star R x y) as Hleft.
  have (R' y x) as Hmid.
  destruct (Hcond y x Hmid) as [Hmid' | Hnocycle].
    have (R y x) as Hmid'.
    destruct Hacyclic.
    toshow (exists x0 : T, plus R x0 x0).
    exists y, x; auto.

    have (~ star R' x y) as Hnocycle.
    destruct Hnocycle.
    toshow (star R' x y).
    eapply star_mono.
      eexact Hincl.
    assumption.

  (* step *)
  intros y z w Hnewmid Hright IH x Hleft Hmid.
  have (star R w x) as Hleft.
  have (R' x y) as Hmid.
  have (R' y z) as Hnewmid.
  have (forall y : T, star R w y -> R' y z -> False) as IH.
  destruct (Hcond x y Hmid) as [Hmid' | Hnocycle].
    have (R x y) as Hmid'.
    thus (star R w y) as Hleft' by star_stepr.
    exact (IH y Hleft' Hnewmid).

    have (~ star R' y x) as Hnocycle.
    destruct Hnocycle.
    toshow (star R' y x).
    apply (star_step _ Hnewmid).
    apply (star_trans _#5 Hright).
    apply (star_mono _#3 Hincl).
    exact Hleft.
have (forall x y z : T, star R x y -> R' y z -> star R' z x -> False) as Hind.
toshow (acyclic R').
intro H.
destruct H as (x & y & Hxy & Hyz).
apply (Hind x x y); auto.
apply star_refl.
Qed.


Lemma acyclic_extend_fresh :
  forall (T : Set) (R R' : T -> T -> Prop),
    acyclic R
    -> (forall x y, R x y -> R' x y)
    -> (forall x y, R' x y -> R x y \/ forall z, ~ R' y z)
    -> acyclic R'.
Proof.
intros T R R' Hacyclic Hincl Hcond.
apply (acyclic_extend _ R R'); auto.
intros x y Hxy.
destruct (Hcond x y Hxy) as [Hxy' | Hfresh].
  left; auto.

  right.
  toshow (~ star R' y x).
  have (forall z : T, ~ R' y z) as Hfresh.
  intro Hyx.
  assert (plusr R' y y) as Hyy by (eexists; eauto).
  destruct (plusr_plus _#4 Hyy) as (z & Hyz & _).
  exact (Hfresh z Hyz).
Qed.


Lemma simpler_path_strong :
  forall (T : Set) (R R' : T -> T -> Prop) x y,
    (forall x' y',
       R x' y' 
       -> star R' y x'
       -> star R y' x
       -> R' x' y' \/ x' = x \/ y' = y)
    -> star R y x
    -> star R' y x.
Proof.
intros T R R' x y Hincl Hpath.
set (z1 := y) in Hpath.
thus (star R' y z1) as Hleft by @star_refl.
clearbody z1.
remember x as z3 eqn:Heqz3 in Hpath |- *.
revert Hleft Heqz3.
induct Hpath.

(* refl *)
auto; done.

(* trans *)
intros z1 z2 z3 H12 Hright IH Hleft ->.
so (Hincl _ _ H12 Hleft Hright) as [H12' |[? | ?]].
  apply IH; auto; [].
  apply (star_trans _#3 z1); auto; [].
  apply star_one; auto; done.

  subst.
  assumption.

  subst z2.
  apply IH; auto using star_refl; done.
Qed.


Lemma simpler_path_strong' :
  forall (T : Set) (R R' : T -> T -> Prop) x y,
    (forall x' y',
       R x' y' 
       -> star R y x'
       -> star R' y' x
       -> R' x' y' \/ x' = x \/ y' = y)
    -> star R y x
    -> star R' y x.
Proof.
intros T R R' x y Hincl HR.
apply star_transpose; [].
apply (simpler_path_strong _ (transpose R)); [|].
  intros y' x' HRt HR'ts HRts.
  exploit (Hincl x' y') as Hprop; [| | |].
    assumption.

    apply star_transpose; auto; done.

    apply star_transpose; auto; done.

    destruct Hprop as [HR' | [Heq | Heq]]; auto; done.

  apply star_transpose_intro; auto; done.
Qed.


Lemma simpler_path :
  forall (T : Set) (R R' : T -> T -> Prop) x y,
    (forall x' y', R x' y' -> R' x' y' \/ x' = x \/ y' = y)
    -> star R y x
    -> star R' y x.
Proof.
intros T R R' x y Hincl Hpath.
eapply simpler_path_strong; eauto.
Qed.


Lemma excise_path :
  forall (T : Set) (R R' : T -> T -> Prop) (P : T -> Prop) w x y,
    (forall x y, R x y -> R' x y \/ (P x /\ y = w))
    -> plus R x y
    -> plus R' x y \/ (exists z, star R' x z /\ P z /\ star R' w y).
Proof.
intros T R R' P w x y Hincl Hpath.
so (plus_plusi _#4 Hpath) as Hpath'.
clear Hpath.
induct Hpath'.

(* one *)
intros x y Hxy.
so (Hincl x y Hxy) as [Hxy' | (Hp & Heq)].
  left; apply plus_one; assumption.

  right; exists x.
  subst y.
  repeat2 split; auto using star_refl; done.

(* step *)
intros x y z Hxy Hyz IH.
#4 so (Hincl x y Hxy) as [Hxy' | (Hpx & Heqy)]; destruct IH as [Hyz' | (v & Hyv & Hpv & Hwz)].
  left.
  eapply plus_trans; eauto using plus_one; done.

  right.
  exists v.
  repeat2 split; auto; [].
  eapply star_step; eauto; done.

  right.
  subst y.
  eauto using star_refl, plus_star; done.

  right.
  exists x.
  auto using star_refl; done.
Qed.


(* Acyclic induction *)

Lemma delete_elem :
  forall (T : Set) (l : list T) x,
    In x l
    -> exists l',
         (forall y, y <> x -> In y l -> In y l')
         /\ length l = S (length l').
Proof.
intros T l x Hx.
induction l as [ | h t IHl].
(* nil *)
destruct Hx.

(* cons *)
have (In x (h :: t)) as Hx.
have (In x t ->
      exists l' : list T,
        (forall y : T, y <> x -> In y t -> In y l') /\
        length t = S (length l')) as IHl.
toshow (exists l' : list T,
          (forall y : T, y <> x -> In y (h :: t) -> In y l') /\
          length (h :: t) = S (length l')).
simpl in Hx.
destruct Hx as [Hx | Hx].
  have (h = x) as Hx.
  exists t.
  split.
    toshow (forall y : T, y <> x -> In y (h :: t) -> In y t).
    intros y Hneq Hcons.
    simpl in Hcons.
    have (h = y \/ In y t) as Hcons.
    toshow (In y t).
    destruct Hcons as [Hh | Ht].
      have (h = y) as Hh.
      subst y.
      contradict Hneq; assumption.

      apply Ht.

    toshow (length (h :: t) = S (length t)).
    simpl.
    auto.

  have (In x t) as Hx.
  pose proof (IHl Hx) as Hind.
  toshow (exists l' : list T,
            (forall y : T, y <> x -> In y (h :: t) -> In y l') /\
            length (h :: t) = S (length l')).
  destruct Hind as (l' & Hmem & Hlength).
  exists (h :: l').
  split.
    toshow (forall y : T, y <> x -> In y (h :: t) -> In y (h :: l')).
    intros y Hneq Hcons.
    simpl.
    simpl in Hcons.
    destruct Hcons; auto.

    toshow (length (h :: t) = S (length (h :: l'))).
    simpl.
    omega.
Qed.


Definition downfin {T : Set} (R : T -> T -> Prop) :=
  forall x, exists l, forall y, plus R y x -> In y l.


Lemma contained_downfin :
  forall (T : Set) (R : T -> T -> Prop),
    (exists l, forall x y, R x y -> In x l)
    -> downfin R.
Proof.
intros T R (l & Hin) y.
exists l.
intros x Hplus.
destruct Hplus as (z & HR & _).
eapply Hin; eauto; done.
Qed.


Theorem acyclic_well_founded :
  forall (T : Set) (R : T -> T -> Prop),
    downfin R
    -> acyclic R
    -> well_founded R.
Proof.
intros T R Hfin Hacyclic.
unfold well_founded.
intro x.
destruct (Hfin x) as (S & Hmem).
pose proof 
  (well_founded_ind (well_founded_ltof (list T) (@length _))
     (fun S => forall x, (forall y, plus R y x -> In y S) -> Acc R x))
  as Hind.
simpl in Hind.
apply (fun H => Hind H S); clear Hind; [| exact Hmem].
clear x S Hmem.
intros S IH x Hmem.
have (forall y : list T,
      ltof (list T) (@length _) y S ->
      forall x : T, (forall y0 : T, plus R y0 x -> In y0 y) -> Acc R x) as IH.
have (forall y : T, plus R y x -> In y S) as Hmem.
toshow (Acc R x).
apply Acc_intro.
intros y Hyx.
have (R y x) as Hyx.
toshow (Acc R y).
thus (plus R y x) as Hyx' by plus_one.
thus (In y S) as Hiny by Hmem.
pose proof (delete_elem _ S y Hiny) as (S' & Hmem' & Hlength).
have (forall y0 : T, y0 <> y -> In y0 S -> In y0 S') as Hmem'.
have (length S = Datatypes.S (length S')) as Hlength.
apply (IH S').
  unfold ltof.
  toshow (length S' < length S).
  omega.

  toshow (forall y0 : T, plus R y0 y -> In y0 S').
  intros z Hzy.
  apply Hmem'.
    have (plus R z y) as Hzy.
    toshow (z <> y).
    intro Heq.
    subst z.
    have (plus R y y) as Hzy.
    apply Hacyclic.
    exists y; auto.
    
    toshow (In z S).
    apply Hmem.
    eapply plus_trans; eauto.
Qed.


(* List minimal element *)

Lemma list_minimal_element :
  forall (T : Set) (R : T -> T -> Prop) l,
    antisymmetric T R
    -> transitive T R
    -> (forall x y, decidable (R x y))
    -> l = nil
       \/ (exists x, In x l /\ Forall (fun y => R y x -> x = y) l).
Proof.
intros T R l Hantisymm Htrans HdecR.
induction l as [| x l IH].
  (* nil *)
  left; reflexivity.

  (* cons *)
  right.
  destruct IH as [Heql | (y & Hy & Hminy)].
    have (l = nil) as Heql.
    subst l.
    exists x.
    split.
      left; reflexivity.

      apply Forall_cons; [|].
        intros _; reflexivity; done.

        apply Forall_nil; done.

    have (In y l) as Hy.
    have (Forall (fun y0 : T => R y0 y -> y = y0) l) as Hminy.
    so (HdecR x y) as [Hxy | Hnxy].
      have (R x y) as Hxy.
      exists x.
      split.
        left; reflexivity.

        apply Forall_cons; [|].
          intros _; reflexivity.

          toshow (Forall (fun y0 : T => R y0 x -> x = y0) l).
          refine (Forall_impl _#4 l Hminy).
          intros z Hyz Hzx.
          have (R z y -> y = z) as Hyz.
          have (R z x) as Hzx.
          exploit Hyz as Heqz.
            toshow (R z y).
            eapply Htrans; [apply Hzx | apply Hxy]; done.
          have (y = z) as Heqz.
          subst z.
          eapply Hantisymm; eauto; done.

      have (~ R x y) as Hnxy.
      exists y.
      split.
        right; assumption.

        apply Forall_cons; auto; [].
        intro Hxy.
        destruct Hnxy; assumption.
Qed.


Lemma list_maximal_element :
  forall (T : Set) (R : T -> T -> Prop) l,
    antisymmetric T R
    -> transitive T R
    -> (forall x y, decidable (R x y))
    -> l = nil
       \/ (exists x, In x l /\ Forall (fun y => R x y -> x = y) l).
Proof.
intros T R l Hantisymm Htrans Hdec.
exploit (list_minimal_element T (transpose R) l) as [Hnone | Hsome]; [| | | |].
  apply antisymmetric_transpose; auto; done.

  apply transitive_transpose; auto; done.

  apply decidable_transpose; auto; done.

  left; assumption.

  destruct Hsome as (x & Hin & Hall).
  right.
  eauto; done.
Qed.



(* Relation exponentiation *)

Inductive expon {T : Set} (R : T -> T -> Prop) : nat -> T -> T -> Prop :=
| expon_refl {x}
    : expon R 0 x x

| expon_step {n x y z}
    : R x y
      -> expon R n y z
      -> expon R (S n) x z.


Lemma star_expon :
  forall (T : Set) (R : T -> T -> Prop) x y,
    star R x y
    -> exists n, expon R n x y.
Proof.
intros T R x y HRs.
induct HRs.

(* refl *)
intro x.
exists 0.
apply expon_refl; done.

(* step *)
intros x y z HR _ IH.
destruct IH as (n & HRn).
exists (S n).
eapply expon_step; eauto; done.
Qed. 


Lemma expon_star :
  forall (T : Set) (R : T -> T -> Prop) x y n,
    expon R n x y
    -> star R x y.
Proof.
intros T R x y n HRn.
induct HRn.

(* refl *)
intro x.
apply star_refl; done.

(* step *)
intros n x y z HR _ IH.
eapply star_step; eauto; done.
Qed. 


Lemma expon_one :
  forall (T : Set) (R : T -> T -> Prop) x y,
    R x y
    -> expon R 1 x y.
Proof.
intros T R x y HR.
eauto using expon_step, expon_refl.
Qed.


Lemma expon_trans :
  forall (T : Set) (R : T -> T -> Prop) m n x y z,
    expon R m x y
    -> expon R n y z
    -> expon R (m + n) x z.
Proof.
intros T R m n x y z Hxy Hzy.
revert Hzy.
induct Hxy.

(* refl *)
auto; done.

(* step *)
intros m x y w Hyz _ IH Hzy.
eapply expon_step; eauto; done.
Qed.
