
Require Import Tactics.
Require Import Relation.
Require Import Sequence.
Require Import Dynamic.
Require Import Subst.


(* trace coherence *)

Definition head (H : list event) (h : event) :=
  exists H', H = H'; h.


Inductive isac : term -> Prop :=
| isac_read {l m}
    : isac (ac_read l m)
| isac_write {l v m}
    : isac (ac_write l v m)
| isac_rw {l v}
    : isac (ac_rw l v)
.

Definition allexec H :=
  forall i p, H {{ ev_init i p }} -> exec H i.

Hint Constructors isac : isac.


Inductive trco : history -> Prop :=
| trco_nil
    : trco nil

| trco_init {H i p}
    : trco H
      -> ~ H {{ ev_init i pe | pe }}
      -> trco (H; ev_init i p)

| trco_is {H i a}
    : trco H
      -> isac a
      -> closed a
      -> (exists p, head H (ev_init i p))
      -> trco (H; ev_is i a)

| trco_exec {H i a}
    : trco H
      -> H {{ ev_is i a }}
      -> ~ exec H i
      -> (forall i', so H i' i -> exec H i')
      -> (~ exists l m, a = ac_read l m)
      -> (~ exists l v, a = ac_rw l v)
      -> trco (H; ev_exec i)

| trco_rf {H iw ir l}
    : trco H
      -> writesto H iw l
      -> reads H ir l
      -> exec H iw
      -> ~ exec H ir
      -> (forall i, so H i ir -> exec H i)
      -> trco (H; ev_rf iw ir)
.

Definition hok (H : history) (U : tgtp) (P : lctp) (I : idtp) : Prop :=
  trco H /\ acyclic (co H).
