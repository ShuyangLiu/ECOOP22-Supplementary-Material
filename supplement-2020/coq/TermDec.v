Require Import Dynamic.
Require Import Syntax.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Peano_dec.

Theorem eq_nat_is_eq n m : eq_nat n m <-> n = m.
Proof.
  split.
  - revert m; induction n; destruct m; simpl; contradiction || auto.
  - intros <-; apply eq_nat_refl.
Defined.

Lemma eq_eq_nat n m : n = m -> eq_nat n m.
Proof.
 apply eq_nat_is_eq.
Defined.

Lemma eq_nat_eq n m : eq_nat n m -> n = m.
Proof.
 apply eq_nat_is_eq.
Defined.

Theorem eq_mode_dec : forall (m1 m2 : mode), {m1 = m2} + {m1 <> m2}.
  intros.
  induction m1; induction m2; try (right; discriminate); left; auto.
Qed.

Theorem eq_term_dec : forall (t1 t2 : term), {t1 = t2} + {t1 <> t2}.
Proof.
  intros t1;
    induction t1;
    intros t2;
    destruct t2;
    try (right; discriminate);
    try (destruct (IHt1 t2) as [ Ht1t2eq | Ht1t2neq ]);
    try (destruct (eq_nat_dec l l0) as [ Hleq | Hlneq ]);
    try (destruct (eq_nat_dec n n0) as [ Hnateq | Hnatneq ]);
    try (destruct (eq_mode_dec m m0) as [ Hmeq | Hlmeq ]);
    try (destruct (IHt1_1 t2_1) as [ Ht1_1t2_1eq | Ht1_1t2_1neq ]);
    try (destruct (IHt1_2 t2_2) as [ Ht1_2t2_2eq | Ht1_2t2_2neq ]);
    try (destruct (IHt1_3 t2_3) as [ Ht1_3t2_3eq | Ht1_3t2_3neq ]);
    try (right; unfold not; intros Hneq; inversion Hneq; contradiction);
    try (left; congruence).
Defined.

Lemma eq_event_dec :
  forall ev1 ev2 : event,
  { ev1 = ev2 } + { ev1 <> ev2 }.
Proof.
  destruct ev1; destruct ev2;
    try (right; discriminate);

    try (destruct (PeanoNat.Nat.eq_dec i i1) as [Heq1 | Hneq1];
         destruct (PeanoNat.Nat.eq_dec i0 i2) as [Heq2 | Hneq2]);

    try (destruct (PeanoNat.Nat.eq_dec i i0) as [Heq1 | Hneq1]); 
    try (destruct (PeanoNat.Nat.eq_dec t t0) as [Heq2 | Hneq2]);
    try (destruct (eq_term_dec t t0) as [Heq2 | Hneq2]);
    try (left; congruence);
    try (right; unfold not; intros Heq; inversion Heq; contradiction).
Qed.

Require Import Coq.Logic.EqdepFacts.

Theorem eq_nat_dec_refl :
  forall x , eq_nat_dec x x = left eq_refl.
Proof.
  intros.
  destruct eq_nat_dec.
  assert (e = eq_refl).
  apply (Eqdep_dec.UIP_refl_nat).
  rewrite -> H.
  auto.
  contradiction.
Defined.