
Require Import Tactics.
Require Import List.
Require Import Decidable.
Require Import Relation_Definitions.
Require Import Relation.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Wf_nat.
Require Import Omega.


(* Generalities *)

Lemma Exists_eq_in :
  forall (T : Set) (x : T) l,
    (Exists (fun y => x = y) l) <-> In x l.
Proof.
intros T x l.
assert ((exists y, In y l /\ x = y) <-> In x l).
split.
intro H.
destruct H as (y & H1 & H2).
subst y; auto.

intro H.
exists x.
auto.

eapply iff_trans.
apply Exists_exists.
apply H.
Qed.


Lemma iff_decidable :
  forall P Q, (P <-> Q) -> decidable P -> decidable Q.
Proof.
intros P Q Hiff HP.
destruct HP.
  left; apply Hiff; auto.

  right; contradict H; apply Hiff; auto.
Qed.


Lemma Exists_decidable :
  forall (T : Set) (P : T -> Prop),
    (forall x, decidable (P x))
    -> forall l, decidable (Exists P l).
Proof.
intros T P Hdec l.
induction l.
(* nil *)
right.
intro H.
inversion H.

(* cons *)
destruct (Hdec a) as [Ha | Ha].
  left.
  apply Exists_cons_hd; auto.

  destruct IHl as [Hl | Hl].
    left.
    apply Exists_cons_tl; auto.

    right.
    intro H.
    inversion H; subst; auto.
Qed.


Lemma In_decidable :
  forall (T : Set),
    (forall (x y : T), decidable (x = y))
    -> forall (x : T) l, decidable (In x l).
Proof.
intros T Hdec x l.
apply (iff_decidable (Exists (fun x' => x = x') l)).
  apply Exists_eq_in.

  apply Exists_decidable.
  apply Hdec.
Qed.


Lemma In_iff_impl_Forall :
  forall (T : Set) (P : T -> Prop) (l : list T),
    (forall x, P x <-> In x l)
    -> Forall P l.
Proof.
intros T P l H.
apply Forall_forall.
intros x Hin.
apply H; auto.
Qed.


Lemma sumbool_decidable :
  forall P, {P} + {~P} -> decidable P.
Proof.
intros P H.
destruct H.
  left; assumption.

  right; assumption.
Qed.



(* A form of constructive finiteness *)

Definition itemizable {T : Set} (P : T -> Prop) : Prop :=
  exists l, forall x, P x <-> In x l.


Lemma iff_itemizable :
  forall (T : Set) (P Q : T -> Prop), (forall x, P x <-> Q x) -> itemizable P -> itemizable Q.
Proof.
intros T P Q Hiff HP.
destruct HP as (L & HL).
exists L.
intro x.
split; intro.
  apply HL; apply Hiff; auto.

  apply Hiff; apply HL; auto.
Qed.


Lemma itemizable_empty :
  forall (T : Set),
    itemizable (fun x : T => False).
Proof.
intro T.
exists nil.
intro x.
split; intro H; destruct H.
Qed.


Lemma itemizable_none :
  forall (T : Set) (P : T -> Prop),
    ~ (exists x, P x)
    -> itemizable P.
Proof.
intros T P Hnone.
apply (iff_itemizable _ (fun _ => False)); [|].
  split.
    intro Hfalse; destruct Hfalse; done.

    intro HP.
    destruct Hnone.
    eauto; done.

  apply itemizable_empty; done.
Qed.


Lemma itemizable_singleton :
  forall (T : Set) (x : T),
    itemizable (fun y => x = y).
Proof.
intros T x.
exists (x :: nil).
intro y.
split.
  intro; subst.
  simpl.
  left; reflexivity.

  intro H.
  simpl in H.
  destruct H; auto.
  destruct H.
Qed.


Lemma itemizable_sole :
  forall (T : Set) (P : T -> Prop) (x : T),
    P x
    -> (forall y, P y -> x = y)
    -> itemizable P.
Proof.
intros T P x HP Honly.
apply (iff_itemizable _ (fun y => x = y)); [|].
  intro y.
  split.
    intro; subst; assumption.

    apply Honly; done.

  apply itemizable_singleton; done.
Qed.


Lemma itemizable_in :
  forall (S : Set) (l : list S),
    itemizable (fun x => In x l).
Proof.
intros A l.
unfold itemizable.
exists l.
intro; split; auto.
Qed.


Lemma itemizable_match :
  forall (S T : Set) (f : T -> S) x,
    decidable (exists y, x = f y)
    -> (forall y y', f y = f y' -> y = y')
    -> itemizable (fun y => x = f y).
Proof.
intros S T f x Hdec Hinj.
destruct Hdec as [(y & Heq) | Hnmatch].
  apply (iff_itemizable _ (fun y' => y = y')); [| apply itemizable_singleton; done].
  intro y'.
  split.
    intros; subst; auto; done.

    intros; subst.
    apply Hinj; auto; done.

  apply (iff_itemizable _ (fun _ => False)); [| apply itemizable_empty; done].
  intro y.
  split.
    intro H; destruct H; done.

    intro H.
    destruct Hnmatch.
    exists y; assumption.
Qed.

    
Lemma itemizable_decidable :
  forall (T : Set) (P : T -> Prop),
    itemizable P
    -> (forall (x y : T), decidable (x = y))
    -> forall x, decidable (P x).
Proof.
intros T P HitemP Hdec x.
destruct HitemP as (L & HL).
apply (iff_decidable (In x L)); [split; apply HL; auto |].
apply In_decidable; auto.
Qed.


Lemma itemizable_decidable_exists :
  forall (T : Set) (P : T -> Prop),
    itemizable P
    -> decidable (exists x, P x).
Proof.
intros T P Hitem.
destruct Hitem as (l & Hforall).
destruct l as [| x].
  right.
  intros (x & H).
  destruct (Hforall x andel H); done.

  left.
  exists x.
  apply Hforall.
  left; reflexivity.
Qed.


Lemma itemizable_from_univ :
  forall (T : Set) (P : T -> Prop) U,
    (forall x, In x U -> decidable (P x))
    -> (forall x, P x -> In x U)
    -> itemizable P.
Proof.
intros T P U HdecP HU.
assert (exists L, Forall P L /\ (forall x, In x U -> P x -> In x L)) as Hcomp.
  (* prove assertion *)
  clear HU.
  have (forall x : T, In x U -> decidable (P x)) as HdecP.
  induction U.
  (* nil *)
  exists nil.
  split.
    apply Forall_nil.
  
    simpl; auto.
  
  (* cons *)
  rename a into x.
  assert (forall x, In x U -> decidable (P x)) as HdecP'.
    (* prove assertion *)
    intros y Hy.
    apply HdecP.
    simpl; right; auto.
  
  destruct (IHU HdecP') as (L & Hsound & Hcomplete).
  have (Forall P L) as Hsound.
  have (forall x : T, In x U -> P x -> In x L) as Hcomplete.
  toshow (exists L0 : list T,
            Forall P L0 /\ (forall x0 : T, In x0 (x :: U) -> P x0 -> In x0 L0)).
  assert (In x (x :: U)) as Hinx by (simpl; auto).
  destruct (HdecP x Hinx) as [HPx | HnPx].
    have (P x) as HPx.
    exists (x :: L).
    split.
      toshow (Forall P (x :: L)).
      apply Forall_cons; auto.
  
      toshow (forall x0 : T, In x0 (x :: U) -> P x0 -> In x0 (x :: L)).
      intros y Hiny HPy.
      have (In y (x :: U)) as Hiny.
      have (P y) as HPy.
      toshow (In y (x :: L)).
      inversion Hiny; subst.
        simpl; auto.
        
        simpl; right.
        apply Hcomplete; auto.
  
    have (~ P x) as HnPx.
    exists L.
    split.
      assumption.
  
      toshow (forall x0 : T, In x0 (x :: U) -> P x0 -> In x0 L).
      intros y Hiny HPy.
      apply Hcomplete; auto.
      inversion Hiny; auto.
      subst y.
      contradict HnPx; auto.

destruct Hcomp as (L & Hcomp').
exists L.
intro x.
toshow (P x <-> In x L).
split.
  toshow (P x -> In x L).
  intro H.
  apply Hcomp'; auto.

  toshow (In x L -> P x).
  intro H.
  destruct Hcomp'; apply (Forall_forall P L); auto.
Qed.


Lemma itemizable_subset :
  forall (T : Set) (P : T -> Prop) (Q : T -> Prop),
    (forall x, Q x -> P x)
    -> (forall x, P x -> decidable (Q x))
    -> itemizable P
    -> itemizable Q.
Proof.
intros T P Q Himp HdecQ HitemP.
destruct HitemP as (L & HL).
apply (itemizable_from_univ _ _ L).
  toshow (forall x : T, In x L -> decidable (Q x)).
  intros x H.
  apply HdecQ.
  apply HL.
  auto.

  intros x H.
  apply HL.
  apply Himp.
  auto.
Qed.


Lemma itemizable_and_dep :
  forall (T : Set) (P Q : T -> Prop),
    itemizable P
    -> (forall x, P x -> decidable (Q x))
    -> itemizable (fun x => P x /\ Q x).
Proof.
intros T P Q HfinP HdecQ.
apply (itemizable_subset _ P).
  toshow (forall x : T, P x /\ Q x -> P x).
  intros x (HPx & HQx).
  assumption.

  toshow (forall x : T, P x -> decidable (P x /\ Q x)).
  intros x HPx.
  destruct (HdecQ _ HPx) as [HQx | HnQx].
    left; split; assumption.

    right; intro H; destruct H; contradict HnQx; auto.

  assumption.
Qed.


Lemma itemizable_and :
  forall (T : Set) (P Q : T -> Prop),
    itemizable P
    -> (forall x, decidable (Q x))
    -> itemizable (fun x => P x /\ Q x).
Proof.
intros T P Q HP HQ.
apply itemizable_and_dep; auto.
Qed.


Lemma itemizable_and_dep_right :
  forall (T : Set) (P Q : T -> Prop),
    (forall x, Q x -> decidable (P x))
    -> itemizable Q
    -> itemizable (fun x => P x /\ Q x).
Proof.
intros T P Q HdecQ HitemP.
apply (iff_itemizable _ (fun x => Q x /\ P x)); [|].
  tauto.

  apply itemizable_and_dep; auto; done.
Qed.


Lemma itemizable_and_right :
  forall (T : Set) (P Q : T -> Prop),
    (forall x, decidable (P x))
    -> itemizable Q
    -> itemizable (fun x => P x /\ Q x).
Proof.
intros T P Q HitemP HdecQ.
eapply itemizable_and_dep_right; eauto; done.
Qed.


Lemma itemizable_decidable_forall :
  forall (T : Set) (P Q : T -> Prop),
    itemizable P
    -> (forall x, P x -> decidable (Q x))
    -> decidable (forall x, P x -> Q x).
Proof.
intros T P Q HitemP HdecQ.
assert (decidable (exists x, P x /\ ~ Q x)) as HdecPnotQ.
  apply itemizable_decidable_exists; [].
  apply itemizable_and_dep; auto; [].
  intros x HPx.
  apply dec_not.
  apply HdecQ; auto; done.
destruct HdecPnotQ as [(x & HPx & HnQx) | Hno].
  have (P x) as HPx.
  have (~ Q x) as HnQx.
  right.
  intros HPimpQ.
  destruct HnQx.
  apply HPimpQ; auto; done.
  
  have (~ (exists x : T, P x /\ ~ Q x)) as Hno.
  left.
  intros x HPx.
  so (HdecQ x HPx) as [? | HnQx]; auto; [].
  destruct Hno.
  exists x; auto; done.
Qed.


Lemma itemizable_compose :
  forall (S T : Set) (P : S -> Prop) (Q : S -> T -> Prop),
    itemizable P
    -> (forall x, P x -> itemizable (Q x))
    -> itemizable (fun xy => P (car xy) /\ Q (car xy) (cdr xy)).
Proof.
intros S T P Q HP HQ.
destruct HP as (L & HL).
assert (exists L',
          Forall (fun xy => P (car xy) /\ Q (car xy) (cdr xy)) L'
          /\ (forall x y, In x L -> Q x y -> In (x, y) L')) as Hcomp.
  (* prove assertion *)
  assert (forall x, In x L -> P x) as HL' by (intros; apply HL; auto).
  clear HL; rename HL' into HL.
  induction L as [ | x].
  (* nil *)
  exists nil.
  split.
    toshow (Forall (fun xy : S * T => P (car xy) /\ Q (car xy) (cdr xy)) nil).
    apply Forall_nil.

    toshow (forall (x : S) (y : T), In x nil -> Q x y -> In (x, y) nil).
    simpl; auto.
    
  (* cons *)
  have ((forall x : S, In x L -> P x) ->
        exists L' : list (S * T),
          Forall (fun xy : S * T => P (car xy) /\ Q (car xy) (cdr xy)) L' /\
          (forall (x : S) (y : T), In x L -> Q x y -> In (x, y) L')) as IHL.
  toshow (exists L' : list (S * T),
            Forall (fun xy : S * T => P (car xy) /\ Q (car xy) (cdr xy)) L' /\
            (forall (x0 : S) (y : T), In x0 (x :: L) -> Q x0 y -> In (x0, y) L')).
  destruct IHL as (Lback & Hsound & Hcomplete).
    toshow (forall x0 : S, In x0 L -> P x0).
    intros x' Hinx'.
    apply HL.
    simpl; right; auto.
    
  have (Forall (fun xy : S * T => P (car xy) /\ Q (car xy) (cdr xy)) Lback) as Hsound.
  have (forall (x : S) (y : T), In x L -> Q x y -> In (x, y) Lback) as Hcomplete.
  assert (P x) as HPx.
    apply HL.
    simpl; auto.

  destruct (HQ x HPx) as (Lfront & HLfront).
  exists (map (fun y => (x, y)) Lfront ++ Lback).
  split.
    toshow (Forall (fun xy : S * T => P (car xy) /\ Q (car xy) (cdr xy))
              (map (fun y : T => (x, y)) Lfront ++ Lback)).
    apply Forall_forall.
    intros (x' & y').
    simpl.
    intro Hin.
    destruct (in_app_or _ _ (x', y') Hin) as [Hinfront | Hinback].
      have (In (x', y') (map (fun y : T => (x, y)) Lfront)) as Hinfront.
      pose proof (in_map_iff _ _ _ andel Hinfront) as (x'' & Heq & Hinx'').
      inversion Heq; subst x'' x'.
        split.
        apply HL.
        simpl; auto.

        apply HLfront; auto.

      have (In (x', y') Lback) as Hinback.
      change (P (car (x', y')) /\ Q (car (x', y')) (cdr (x', y'))).
      apply (Forall_forall (fun xy => P (car xy) /\ Q (car xy) (cdr xy)) Lback); auto.

    toshow (forall (x0 : S) (y : T),
            In x0 (x :: L) ->
            Q x0 y -> In (x0, y) (map (fun y0 : T => (x, y0)) Lfront ++ Lback)).
    intros x' y Hinx' HQx'y.
    apply in_or_app.
    toshow (In (x', y) (map (fun y : T => (x, y)) Lfront) \/ In (x', y) Lback).
    simpl in Hinx'.
    have (x = x' \/ In x' L) as Hinx'.
    destruct Hinx' as [Heq | Hinx'].
      have (x = x') as Heq.
      subst x'.
      left.
      toshow (In (x, y) (map (fun y0 : T => (x, y0)) Lfront)).
      apply in_map.
      apply HLfront; auto.

      have (In x' L) as Hinx'.
      right.
      apply Hcomplete; auto.

have (exists L' : list (S * T),
        Forall (fun xy : S * T => P (car xy) /\ Q (car xy) (cdr xy)) L' /\
        (forall (x : S) (y : T), In x L -> Q x y -> In (x, y) L')) as Hcomp.
destruct Hcomp as (L' & Hsound & Hcomplete).
have (Forall (fun xy : S * T => P (car xy) /\ Q (car xy) (cdr xy)) L') as Hsound.
have (forall (x : S) (y : T), In x L -> Q x y -> In (x, y) L') as Hcomplete.
exists L'.
intros (x & y).
simpl.
toshow (P x /\ Q x y <-> In (x, y) L').
split.
  intros (HPx & HQxy).
  apply Hcomplete; auto.
  apply HL; auto.

  intro HL'.
  change (P (car (x, y)) /\ Q (car (x, y)) (cdr (x, y))).
  apply (Forall_forall (fun xy : S * T => P (car xy) /\ Q (car xy) (cdr xy)) L'); auto.
Qed.


Lemma itemizable_or :
  forall (T : Set) (P Q : T -> Prop),
    itemizable P
    -> itemizable Q
    -> itemizable (fun x => P x \/ Q x).
Proof.
intros T P Q (L & HL) (L' & HL').
exists (L ++ L').
intro x.
split.
  intro Hor.
  apply in_or_app.
  destruct Hor; [left | right]; eapplyall; auto.

  intro H.
  destruct (in_app_or _ _ _ H); [left | right]; eapplyall; auto.
Qed.


Lemma itemizable_car :
  forall (S T : Set) (P : S * T -> Prop),
    itemizable P
    -> itemizable (fun x => exists y, P (x, y)).
Proof.
intros S T P (L & HL).
exists (map car L).
intros x.
split.
  toshow ((exists y : T, P (x, y)) -> In x (map car L)).
  intros (y & HP).
  replace x with (car (x, y)) by auto.
  apply in_map.
  apply HL; auto.

  toshow (In x (map car L) -> exists y : T, P (x, y)).
  intros Hinx.
  thus (exists p, car p = x /\ In p L) as HH by in_map_iff.
  destruct HH as ((x', y) & Heq & Hinp).
  simpl in Heq; subst x'.
  exists y.
  apply HL; auto.
Qed.


Lemma itemizable_cdr :
  forall (S T : Set) (P : S * T -> Prop),
    itemizable P
    -> itemizable (fun y => exists x, P (x, y)).
Proof.
intros S T P (L & HL).
exists (map cdr L).
intros y.
split.
  toshow ((exists x : S, P (x, y)) -> In y (map cdr L)).
  intros (x & HP).
  replace y with (cdr (x, y)) by auto.
  apply in_map.
  apply HL; auto.

  toshow (In y (map cdr L) -> exists x : S, P (x, y)).
  intros Hiny.
  thus (exists p, cdr p = y /\ In p L) as HH by in_map_iff.
  destruct HH as ((x, y') & Heq & Hinp).
  simpl in Heq; subst y'.
  exists x.
  apply HL; auto.
Qed.


Lemma itemizable_compose_cdr :
  forall (S T : Set) (P : S -> Prop) (Q : S -> T -> Prop),
    itemizable P
    -> (forall x, P x -> itemizable (Q x))
    -> itemizable (fun y => exists x, P x /\ Q x y).
Proof.
intros S T P Q HP HQ.
apply (itemizable_cdr _ _ (fun xy => P (car xy) /\ Q (car xy) (cdr xy))); [].
apply itemizable_compose; auto; done.
Qed.


Lemma itemizable_preimage :
  forall (S T : Set) (f : T -> S) (P : S -> Prop),
    (forall x, P x -> decidable (exists y, x = f y))
    -> (forall y y', f y = f y' -> y = y')
    -> itemizable P
    -> itemizable (fun y => P (f y)).
Proof.
intros S T f P Hdec Hinj HitemP.
assert (forall x, P x -> itemizable (fun y => x = f y)) as HitemQ.
  intros x Hx.
  apply itemizable_match; auto; done.
so (itemizable_compose _#4 HitemP HitemQ) as Hitem.
simpl in Hitem.
so (itemizable_cdr _#3 Hitem) as Hitem'.
simpl in Hitem'.
refine (iff_itemizable _#4 Hitem').
intro y.
split.
  intros (x & Hx & Heq).
  subst x; assumption.

  intro Hy.
  exists (f y).
  auto; done.
Qed.


Lemma itemizable_preimage_1 :
  forall (S T U : Set) (f : T -> U -> S) (P : S -> Prop),
    (forall x, P x -> decidable (exists y z, x = f y z))
    -> (forall y y' z z', f y z = f y' z' -> y = y' /\ z = z')
    -> itemizable P
    -> itemizable (fun y => exists z, P (f y z)).
Proof.
intros S T U f P Hdec Hinj HitemP.
apply (itemizable_car _ _ (fun p => P (f (car p) (cdr p)))); [].
apply itemizable_preimage; [| |].
  intros x Hx.
  so (Hdec x Hx) as [(y & z & Hyes) | Hno].
    left; exists (y, z); assumption.

    right.
    intros ((y, z) & Heq).
    destruct Hno.
    exists y, z; assumption.

  intros (y, z) (y', z') Heq.
  simpl in Heq.
  so (Hinj _#4 Heq) as (Heqy & Heqz).
  f_equal; auto; done.

  assumption.
Qed.


Lemma itemizable_car_fixed :
  forall (S T : Set) (P : S * T -> Prop) y,
    (forall y', decidable (y' = y))
    -> itemizable P
    -> itemizable (fun x => P (x, y)).
Proof.
intros S T P y Heqdec HitemP.
apply (itemizable_preimage _ _ (fun x => (x, y)) P).
  intros (x, y') _.
  so (Heqdec y') as [Heq | Hneq].
    subst; left; eexists; reflexivity.

    right.
    intros (y'' & Heq).
    injection Heq.
    intros; subst.
    destruct Hneq; trivial; done.

  intros x x' Heq.
  injection Heq; intros; subst; reflexivity.

  assumption.
Qed.


Lemma itemizable_cdr_fixed :
  forall (S T : Set) (P : S * T -> Prop) x,
    (forall x', decidable (x' = x))
    -> itemizable P
    -> itemizable (fun y => P (x, y)).
Proof.
intros S T P x Heqdec HitemP.
apply (itemizable_preimage _ _ (fun y => (x, y)) P).
  intros (x', y) _.
  so (Heqdec x') as [Heq | Hneq].
    subst; left; eexists; reflexivity.

    right.
    intros (x'' & Heq).
    injection Heq.
    intros; subst.
    destruct Hneq; trivial; done.

  intros y y' Heq.
  injection Heq; intros; subst; reflexivity.

  assumption.
Qed.


Lemma itemizable_in_match :
  forall (S T : Set) (f : T -> S) (l : list S),
    (forall x, decidable (exists y, x = f y))
    -> (forall y y', f y = f y' -> y = y')
    -> itemizable (fun y => In (f y) l).
Proof.
intros S T f l Hdec Hinj.
apply (itemizable_preimage _#3 (fun x => In x l)); auto; [].
apply itemizable_in; done.    
Qed.


Lemma itemizable_in_match_1 :
  forall (S T U : Set) (f : T -> U -> S) (l : list S),
    (forall x, decidable (exists y z, x = f y z))
    -> (forall y y' z z', f y z = f y' z' -> y = y' /\ z = z')
    -> itemizable (fun y => exists z, In (f y z) l).
Proof.
intros S T U f l Hdec Hinj.
apply (itemizable_preimage_1 _#4 (fun x => In x l)); auto; [].
apply itemizable_in; done.    
Qed.


Lemma itemizable_map :
  forall (S T : Set) (P : T -> Prop) (f : S -> T) (g : T -> S),
    (forall y, f (g y) = y)
    -> (forall x, g (f x) = x)
    -> itemizable (fun x => P (f x))
    -> itemizable P.
Proof.
intros S T P f g Hinvert Hinvert' HP.
destruct HP as (L & HP).
exists (map f L).
intro y.
have (forall y : T, f (g y) = y) as Hinvert.
have (forall x : S, g (f x) = x) as Hinvert'.
have (forall x : S, P (f x) <-> In x L) as HP.
toshow (P y <-> In y (map f L)).
split.
  toshow (P y -> In y (map f L)).
  intro HPy.
  rewrite <- (Hinvert y).
  apply in_map.
  apply HP.
  rewrite -> (Hinvert y).
  assumption.

  toshow (In y (map f L) -> P y).
  intro Hy.
  rewrite <- (Hinvert y).
  apply HP.
  pose proof (in_map_iff _ _ _ andel Hy) as (x & Heq & Hx).
  subst y.
  rewrite -> (Hinvert' x).
  assumption.
Qed.


Lemma itemizable_forall :
  forall (S T : Set) (P : S -> T -> Prop),
    itemizable (fun xy => P (car xy) (cdr xy))
    -> (forall (x x' : S), decidable (x = x'))
    -> forall x, itemizable (P x).
Proof.
intros S T P HitemP HdecS x.
destruct HitemP as (L & HL).
assert (exists L', forall y, In y L' <-> In (x, y) L) as HL'.
  clear HL.
  induction L as [ | xy L].
  (* nil *)
  exists nil.
  intro y.
  simpl; split; auto.

  (* cons *)
  destruct xy as (x', y).
  destruct IHL as (L' & HL').
  destruct (HdecS x x') as [Heq | Hneq].
    have (x = x') as Heq.
    subst x'.
    exists (y :: L').
    intro y'.
    split.
      toshow (In y' (y :: L') -> In (x, y') ((x, y) :: L)).
      intros Hiny'.
        invert Hiny'.
          intro.
          subst y'.
          simpl; auto.

          intro Hiny''.
          simpl.
          right.
          apply HL'.
          exact Hiny''.

      toshow (In (x, y') ((x, y) :: L) -> In y' (y :: L')).
      intros Hinxy'.
      simpl in Hinxy'.
      destruct Hinxy' as [Heq | Hinxy''].
        inversion Heq.
        subst y'; simpl; left; auto.

        simpl; right.
        apply HL'.
        auto.

    have (x <> x') as Hneq.
    exists L'.
    intro y'.
    split.
      toshow (In y' L' -> In (x, y') ((x', y) :: L)).
      intros Hiny'.
      simpl; right.
      apply HL'; auto.

      toshow (In (x, y') ((x', y) :: L) -> In y' L').
      intros Hinxy'.
      apply HL'.
      simpl in Hinxy'.
      destruct Hinxy' as [Heq |]; auto.
      inversion Heq; subst.
      contradict Hneq; auto.

have (exists L' : list T, forall y : T, In y L' <-> In (x, y) L) as HL'.
destruct HL' as (L' & HL').
exists L'.
intro y.
split.
  toshow (P x y -> In y L').
  intro HPxy.
  apply HL'.
  apply HL.
  simpl; auto.

  toshow (In y L' -> P x y).
  intro Hiny.
  apply (HL (car (x, y), cdr (x, y))).
  apply HL'.
  simpl; auto.
Qed.


Lemma itemizable_pair :
  forall (S T : Set) (P : S -> Prop) (Q : T -> Prop),
    itemizable P
    -> itemizable Q 
    -> itemizable (fun xy => P (car xy) /\ Q (cdr xy)).
Proof.
intros S T P Q HfinP HfinQ.
apply (itemizable_compose _ _ P (fun _ => Q)); auto.
Qed.


Lemma itemizable_swap :
  forall (S T : Set) (P : S -> T -> Prop),
    itemizable (fun xy => P (cdr xy) (car xy))
    -> itemizable (fun xy => P (car xy) (cdr xy)).
Proof.
intros S T P Hitem.
refine (itemizable_map _#3 (fun xy => (cdr xy, car xy)) (fun xy => (cdr xy, car xy)) _ _ _).
  intros (x, y); simpl; auto; done.

  intros (x, y); simpl; auto; done.

  simpl; assumption.
Qed.


Lemma itemizable_exists_minimal :
  forall (T : Set) (P : T -> Prop) (R : T -> T -> Prop),
    itemizable P
    -> antisymmetric T R
    -> transitive T R
    -> (forall x y, decidable (R x y))
    -> ~ (exists x, P x)
       \/ (exists x, P x /\ forall y, P y -> R y x -> x = y).
Proof.
intros T P R HitemP Hantisymm Htrans HdecR.
destruct HitemP as (l & Hprop).
so (list_minimal_element _ R l Hantisymm Htrans HdecR) as [Hempty | (x & Hin & Hmin)].
  have (l = nil) as Hempty.
  subst l.
  left.
  intros (x & Hx).
  destruct (Hprop x andel Hx); done.

  have (In x l) as Hin.
  have (Forall (fun y : T => R y x -> x = y) l) as Hmin.
  right.
  exists x.
  split.
    apply Hprop; auto; done.

    intros y Hy.
    refine (Forall_forall _ l andel Hmin y _); [].
    apply Hprop; auto; done.
Qed.


Lemma itemizable_exists_minimal_strict :
  forall (T : Set) (P : T -> Prop) (R : T -> T -> Prop),
    itemizable P
    -> irreflexive T R
    -> transitive T R
    -> (forall x y, decidable (R x y))
    -> ~ (exists x, P x)
       \/ (exists x, P x /\ ~ exists y, P y /\ R y x).
Proof.
intros T P R Hitem Hirrefl Htrans Hdec.
assert (antisymmetric T R) as Hantisymm.
  intros x y Hxy Hyx.
  destruct Hirrefl.
  exists x.
  eapply Htrans; eauto; done.
so (itemizable_exists_minimal _#3 Hitem Hantisymm Htrans Hdec) as [Hempty | (x & Hx & Hmin)].
  left; assumption.

  right.
  exists x.
  split; auto; [].
  intros (y & Hy & Hyx).
  thus (x = y) by Hmin.
  subst y.
  destruct Hirrefl.
  eexists; eassumption.
Qed.


Lemma itemizable_minimal :
  forall (T : Set) (P : T -> Prop) (R : T -> T -> Prop),
    itemizable P
    -> antisymmetric T R
    -> transitive T R
    -> (forall x y, decidable (R x y))
    -> (forall x y, P x -> P y -> decidable (x = y))
    -> itemizable (fun x => P x /\ forall y, P y -> R y x -> x = y).
Proof.
intros T P R HitemP Hantisymm Htrans HdecR Hdeceq.
apply itemizable_and_dep; auto; [].
intros x HPx.
cut (decidable (exists y, P y /\ R y x /\ x <> y)).
  intros [(y & HPy & HRyx & Hneq) | Hncond].
    right.
    contradict Hneq.
    apply Hneq; auto; done.

    left.
    intros y HPy HRyx.
    apply dec_not_not; auto; [].
    intro Hneq.
    destruct Hncond.
    eexists; repeat2 split; eauto; done.
apply itemizable_decidable_exists.
apply itemizable_and_dep; auto using dec_and, dec_not; done.
Qed.


Lemma itemizable_exists_minimal_prefer :
  forall (T : Set) (P : T -> Prop) (Q : T -> Prop) (R : T -> T -> Prop),
    itemizable P
    -> antisymmetric T R
    -> transitive T R
    -> (forall x, P x -> decidable (Q x))
    -> (forall x y, decidable (R x y))
    -> (forall x y, P x -> P y -> decidable (x = y))
    -> ~ (exists x, P x)
       \/ (exists x, P x /\ (forall y, P y -> R y x -> x = y)
             /\ (Q x \/ forall y, P y -> (forall z, P z -> R z y -> y = z) -> ~ Q y)).
Proof.
intros T P Q R HitemP Hantisymm Htrans HdecQ HdecR Hdeceq.
so (itemizable_exists_minimal _#3 HitemP Hantisymm Htrans HdecR) as [Hnone | (w & HPw & Hminw)].
  left; assumption.

  right.
  so (HdecQ w HPw) as [HQw | HnQw].
    eexists; repeat2 split; eauto; done.
  assert (decidable (exists x, Q x /\ P x /\ (forall y, P y -> R y x -> x = y))) as Hdec.
    apply itemizable_decidable_exists; [].
    apply itemizable_and_dep_right; [|].
      intros x (HPx & _).
      apply HdecQ; auto; done.

      apply itemizable_minimal; auto; done.
  destruct Hdec as [(x & HQx & HPx & Hmin) | Hncond].
    eexists; repeat2 split; eauto; done.

    eexists; repeat2 split; eauto; [].
    right.
    intros y HPy Hminy HQy.
    destruct Hncond.
    eexists; eauto; done.
Qed.


Lemma itemizable_exists_minimal_strict_prefer :
  forall (T : Set) (P : T -> Prop) (Q : T -> Prop) (R : T -> T -> Prop),
    itemizable P
    -> irreflexive T R
    -> transitive T R
    -> (forall x, P x -> decidable (Q x))
    -> (forall x y, decidable (R x y))
    -> (forall x y, P x -> P y -> decidable (x = y))
    -> ~ (exists x, P x)
       \/ (exists x, P x /\ ~ (exists y, P y /\ R y x)
             /\ (Q x \/ forall y, P y -> ~ (exists z, P z /\ R z y) -> ~ Q y)).
Proof.
intros T P Q R HitemP Hirrefl Htrans HdecQ HdecR Hdeceq.
assert (antisymmetric T R) as Hantisymm.
  intros x y Hxy Hyx.
  destruct Hirrefl.
  exists x.
  eapply Htrans; eauto; done.
so (itemizable_exists_minimal_prefer _#4 HitemP Hantisymm Htrans HdecQ HdecR Hdeceq) as Hcond.
repeat2 splithyp Hcond; [|].
  left; assumption.

  destruct Hcond as (x & HPx & Hmin & HQcond).
  right.
  exists x.
  repeat2 split; auto; [|].
    intros (y & HPy & HR).
    destruct Hirrefl.
    exists x.
    so (Hmin y HPy HR) as <-.
    assumption.

    destruct HQcond as [HQx | HnoQ]; auto; [].
    right.
    intros y HPy Hminy.
    apply HnoQ; auto; [].
    intros z HPz HR.
    exfalso.
    destruct Hminy; eauto; done.
Qed.


Lemma itemizable_exists_maximal :
  forall (T : Set) (P : T -> Prop) (R : T -> T -> Prop),
    itemizable P
    -> antisymmetric T R
    -> transitive T R
    -> (forall x y, decidable (R x y))
    -> ~ (exists x, P x)
       \/ (exists x, P x /\ forall y, P y -> R x y -> x = y).
Proof.
intros T P R Hitem Hantisymm Htrans Hdec.
exploit (itemizable_exists_minimal _ P (transpose R));
auto using antisymmetric_transpose, transitive_transpose, decidable_transpose.
Qed.


Lemma itemizable_exists_maximal_strict :
  forall (T : Set) (P : T -> Prop) (R : T -> T -> Prop),
    itemizable P
    -> irreflexive T R
    -> transitive T R
    -> (forall x y, decidable (R x y))
    -> ~ (exists x, P x)
       \/ (exists x, P x /\ ~ exists y, P y /\ R x y).
Proof.
intros T P R Hitem Hantisymm Htrans Hdec.
exploit (itemizable_exists_minimal_strict _ P (transpose R));
auto using antisymmetric_transpose, transitive_transpose, decidable_transpose.
Qed.


Lemma itemizable_exists_maximal_strict_prefer :
  forall (T : Set) (P : T -> Prop) (Q : T -> Prop) (R : T -> T -> Prop),
    itemizable P
    -> irreflexive T R
    -> transitive T R
    -> (forall x, P x -> decidable (Q x))
    -> (forall x y, decidable (R x y))
    -> (forall x y, P x -> P y -> decidable (x = y))
    -> ~ (exists x, P x)
       \/ (exists x, P x /\ ~ (exists y, P y /\ R x y)
             /\ (Q x \/ forall y, P y -> ~ (exists z, P z /\ R y z) -> ~ Q y)).
Proof.
intros T P Q R Hitem Hantisymm Htrans HdecQ HdecR Hdeceq.
exploit (itemizable_exists_minimal_strict_prefer _ P Q (transpose R));
auto using antisymmetric_transpose, transitive_transpose, decidable_transpose.
Qed.


Lemma itemizable_star_right :
  forall (T : Set) (R : T -> T -> Prop),
    well_founded (transpose R)
    -> (forall x, itemizable (fun y => R x y))
    -> forall x, itemizable (fun y => star R x y).
Proof.
intros T R Hwf Hitem.
apply (well_founded_ind Hwf).
unfold transpose.
intros x IH.
apply (iff_itemizable _ (fun y => x = y \/ plus R x y)); [|].
  intro z.
  split.
    intros [Heq | Hplus].
      subst z; apply star_refl; done.

      apply plus_star; assumption.

    exact (star_plus _ _ _ _).
apply itemizable_or.
  apply itemizable_singleton; done.

  unfold plus, compose.
  apply (itemizable_cdr _ _ (fun zy => R x (car zy) /\ star R (car zy) (cdr zy))); [].
  apply itemizable_compose; [|].
    apply Hitem; done.

    exact IH.
Qed.


Lemma itemizable_star_left :
  forall (T : Set) (R : T -> T -> Prop),
    well_founded R
    -> (forall y, itemizable (fun x => R x y))
    -> forall y, itemizable (fun x => star R x y).
Proof.
intros T R Hwf Hitem y.
apply (iff_itemizable _ (fun x => star (transpose R) y x)).
  intro x.
  split.
    apply star_transpose; done.

    apply star_transpose_intro; done.
apply itemizable_star_right; [|].
  exact Hwf.

  exact Hitem.
Qed.


Lemma itemizable_plus_right :
  forall (T : Set) (R : T -> T -> Prop),
    well_founded (transpose R)
    -> (forall x, itemizable (fun y => R x y))
    -> forall x, itemizable (fun y => plus R x y).
Proof.
intros T R Hwf Hitem x.
unfold plus, compose.
apply (itemizable_cdr _ _ (fun zy => R x (car zy) /\ star R (car zy) (cdr zy))); [].
apply itemizable_compose; [|].
  apply Hitem; done.

  intros y _.
  apply itemizable_star_right; auto; done.
Qed.


Lemma itemizable_plus_left :
  forall (T : Set) (R : T -> T -> Prop),
    well_founded R
    -> (forall y, itemizable (fun x => R x y))
    -> forall y, itemizable (fun x => plus R x y).
Proof.
intros T R Hwf Hitem y.
apply (iff_itemizable _ (fun x => plus (transpose R) y x)).
  intro x.
  split.
    apply plus_transpose; done.

    apply plus_transpose_intro; done.
apply itemizable_plus_right; [|].
  exact Hwf.

  exact Hitem.
Qed.


Lemma itemizable_composition :
  forall (T : Set) (R R' : T -> T -> Prop),
    (forall x, itemizable (R x))
    -> (forall x, itemizable (R' x))
    -> forall x, itemizable (compose R R' x).
Proof.
intros T R R' HitemR HitemR' x.
exploit (itemizable_compose _ _ (R x) R') as Hitem; [| |].
  apply HitemR; auto; done.

  intros; apply HitemR'; auto; done.

  refine (iff_itemizable _#4 (itemizable_cdr _#3 Hitem)); [].
  intro z.
  split; auto; done.
Qed.


Lemma itemizable_expon_right :
  forall (T : Set) (R : T -> T -> Prop),
    (forall x, itemizable (fun y => R x y))
    -> forall n x, itemizable (fun y => expon R n x y).
Proof.
intros T R Hitem n x.
revert x.
induction n as [| n IH].

(* refl *)
intro x.
#2 apply (itemizable_sole _ _ x).
  apply expon_refl; done.

  intros y Hxy.
  invert Hxy; intros; subst; reflexivity.

(* step *)
intro x.
#2 apply (iff_itemizable _ (fun y => exists z, R x z /\ expon R n z y)).
  intro y.
  split.
    intros (z & Hxz & Hzy).
    eapply expon_step; eauto; done.

    intro Hxy.
    invert Hxy; eauto; done.

  #2 apply itemizable_compose_cdr.
    apply Hitem; done.

    intros y Hxy.
    apply IH; done.
Qed.    


Lemma itemizable_bound_right :
  forall (T : Set) (R : T -> T -> Prop),
    (forall x, itemizable (fun y => R x y))
    -> forall n x, itemizable (fun y => exists m, m < n /\ expon R m x y).
Proof.
intros T R Hitem n x.
induction n as [| n IH].

(* 0 *)
apply itemizable_none; [].
intros (_ & m & Hlt & _).
omega.

(* S *)
#2 apply (iff_itemizable _ (fun y => expon R n x y \/ exists m, m < n /\ expon R m x y)).
  intro y.
  split.
    intros [Hxy | (m & Hlt & Hxy)].
      exists n; auto; done.

      exists m; auto; done.

    intros (m & Hlt & Hxy).
    so (eq_nat_dec m n) as [Heq | Hneq].
      subst m.
      left; assumption.

      right.
      exists m.
      split.
        omega.

        assumption.

  #2 apply itemizable_or.
    apply itemizable_expon_right; auto; done.

    assumption.
Qed.


Lemma finite_sequence :
  forall (T : Set) (R : T -> T -> Prop) U,
    (forall (x y : T), decidable (x = y))
    -> (forall x y, R x y -> In x U)
    -> forall x y,
         star R x y
         -> exists n,
              n <= length U
              /\ expon R n x y.
Proof.
intros T R U Heqdec Hfinite x y HRs.
so (star_expon _#4 HRs) as (n & HRn).
clear HRs.
revert x y HRn.
wfinduct n using lt_wf.
intros n IH w z HRn.
so (le_lt_dec n (length U)) as [Hleq | HltUn].
  eauto; done.
cut (exists m, m < n /\ expon R m w z).
  intros (m & Hltmn & HRm).
  eapply IH; eauto; done.
clear IH.
assert (length (@nil T) = 0) as Hlength by auto.
assert (0 + n = n) as Heqlk by auto.
assert (NoDup (@nil T)) as Hnodup by (apply NoDup_nil; auto).
assert (Forall (fun x => exists m, m < 0 /\ expon R m w x /\ In x U) nil) as Hall by (apply Forall_nil; auto).
assert (expon R 0 w w) as HRl by (apply expon_refl; auto).
revert Hlength Heqlk Hnodup Hall HRl HRn.
generalize w at 3 4 as x.
generalize (@nil T) as L.
generalize 0 as l.
generalize n at 1 3 as k.
intro k.
induction k as [| k IH].
(* zero *)
intros l L x Hlength Heqlk Hnodup Hall HRl HRn.
exfalso.
clear x z HRl HRn Hfinite.
replace (l + 0) with l in Heqlk by omega.
subst l n.
assert (Forall (fun x => In x U) L) as Hall'.
  refine (Forall_impl _#5 Hall); [].
  intros x (_ & _ & _ & ?); assumption.
clear w Hall.
rename Hall' into Hall.
revert U HltUn Hall.
induct Hnodup.
  (* nil *)
  intros U Hlt _.
  simpl in Hlt.
  omega.
  
  (* cons *)
  intros x L Hnin H0 IH U Hlt Hall.
  invert Hall.
  intros Hin Hall'.
  so (in_split _#3 Hin) as (U1 & U2 & Heq).
  #2 apply (IH (U1 ++ U2)).
    subst U.
    rewrite -> app_length.
    rewrite -> app_length in Hlt.
    simpl in Hlt.
    omega.

    apply Forall_forall; [].
    intros y Hiny.
    so (Forall_forall _#3 andel Hall' _ Hiny) as Hiny'.
    rewrite -> Heq in Hiny'.
    so (in_app_or _#4 Hiny') as [Hiny'' | Hiny''].
      apply in_or_app; left; assumption.

      destruct Hiny'' as [Heqy | Hiny''].
        subst y.
        contradiction.

        apply in_or_app; right; assumption.

(* succ *)
intros l L x Hlength Heqlk Hnodup Hall HRl HRk.
so (In_decidable _ Heqdec x L) as [Hin | Hnin].
  so (Forall_forall _#3 andel Hall _ Hin) as (m & Hltml & Hwy & _).
  exists (m + S k).
  split.
    omega.

    eapply expon_trans; eauto; done.

  invert HRk.
  intros y Hxy Hyz.
  #6 apply (IH (S l) (x :: L) y).
    simpl; auto; done.

    omega.

    apply NoDup_cons; auto; done.

    #2 apply Forall_cons.
      exists l.
      do2 2 split; auto; [].
      eapply Hfinite; eauto; done.

      refine (Forall_impl _#5 Hall); [].
      intros v (m & Hlt & Hwv).
      eauto; done.

    replace (S l) with (l + 1) by omega.
    eapply expon_trans; eauto; [].
    apply expon_one; auto; done.

    assumption.
Qed.


Lemma itemizable_star_right_finite :
  forall (T : Set) (R : T -> T -> Prop) U,
    (forall (x y : T), decidable (x = y))
    -> (forall x y, R x y -> In x U)
    -> (forall x, itemizable (fun y => R x y))
    -> forall x, itemizable (fun y => star R x y).
Proof.
intros T R U Heqdec Hfinite Hitem x.
#2 apply (iff_itemizable _ (fun y => exists n, n < S (length U) /\ expon R n x y)).
  intro y.
  split.
    intros (n & _ & Hxy).
    eapply expon_star; eauto; done.

    intro Hxy.
    so (finite_sequence _#3 Heqdec Hfinite x y Hxy) as (n & Hleq & Hxy').
    exists n.
    split; auto; [].
    omega.

  apply itemizable_bound_right; auto; done.
Qed.


Lemma itemizable_plus_right_finite :
  forall (T : Set) (R : T -> T -> Prop) U,
    (forall (x y : T), decidable (x = y))
    -> (forall x y, R x y -> In x U)
    -> (forall x, itemizable (fun y => R x y))
    -> forall x, itemizable (fun y => plus R x y).
Proof.
intros T R U Heqdec Hfinite Hitem x.
#2 apply itemizable_compose_cdr.
  apply Hitem; done.

  intros.
  eapply itemizable_star_right_finite; eauto; done.
Qed.


Lemma itemizable_star_left_finite :
  forall (T : Set) (R : T -> T -> Prop) U,
    (forall (x y : T), decidable (x = y))
    -> (forall x y, R x y -> In y U)
    -> (forall y, itemizable (fun x => R x y))
    -> forall y, itemizable (fun x => star R x y).
Proof.
intros T R U Heqdec Hfinite Hitem y.
#2 apply (iff_itemizable _ (fun x => star (transpose R) y x)).
  intro x.
  split.
    intro Hyx.
    apply star_transpose; auto; done.

    intro Hxy.
    apply star_transpose_intro; auto; done.

  apply (itemizable_star_right_finite _ _ U); auto; [].
  intros x z Hxz.
  eapply Hfinite; eauto; done.
Qed.


Lemma itemizable_plus_left_finite :
  forall (T : Set) (R : T -> T -> Prop) U,
    (forall (x y : T), decidable (x = y))
    -> (forall x y, R x y -> In y U)
    -> (forall y, itemizable (fun x => R x y))
    -> forall y, itemizable (fun x => plus R x y).
Proof.
intros T R U Heqdec Hfinite Hitem y.
#2 apply (iff_itemizable _ (fun x => plus (transpose R) y x)).
  intro x.
  split.
    intro Hyx.
    apply plus_transpose; auto; done.

    intro Hxy.
    apply plus_transpose_intro; auto; done.

  apply (itemizable_plus_right_finite _ _ U); auto; [].
  intros x z Hxz.
  eapply Hfinite; eauto; done.
Qed.
