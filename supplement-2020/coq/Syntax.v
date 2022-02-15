Require Import TraverseTactics.
Require Export PreSyntax.
Require Import Tactics.
Require Import List.


Inductive attr : Set :=
| at_x : attr
| at_v : attr
| at_push : attr.

Inductive mode : Set := plain | opaque | relacq | vol .

Inductive term : Set :=
| var : nat -> term

(* terms *)
| tm_label : nat -> term
| tm_loc : nat -> term
| tm_nat : nat -> term

(* expressions *)
| xp_bind : (* tp *) term -> term -> (* tm => *) term -> term
| xp_spec : (* tm *) term -> (* tm *) term -> term -> term
| xp_read : (* tm *) term -> mode -> term
| xp_write : (* tm *) term -> (* tm *) term -> mode -> term
| xp_rw : (* tm *) term -> (* tm *) term -> term
| xp_action : nat -> term
| xp_label : term -> term -> term 
| xp_if : (* tm *) term -> (* tm *) term -> (* tm *) term -> term
| xp_repeat : (* body *) term -> (* tm *) term

(* actions *)
| ac_read : location -> mode -> term
| ac_write : location -> term -> mode -> term
| ac_rw : location -> term -> term 

(* transactions *)
| tr_nothing : term
| tr_init : nat -> (* ac *) term -> term
| tr_exec : nat -> (* tm *) term -> term

(* nonsense *)
| nonsense : term
.


Inductive event : Set :=
| ev_init : identifier -> thread -> event
| ev_is : identifier -> (* ac *) term -> event
| ev_exec : identifier -> event
| ev_rf : identifier -> identifier -> event

(* by fiat for the purposes of assumption *)
| ev_co : identifier -> identifier -> event
| ev_push : identifier -> identifier -> event
| ev_vo : identifier -> identifier -> event
.

Definition xstate := list (thread * (* xp *) term).
Definition history := list event.

Definition tgtp := list tag.
Definition lctp := list (location * (* tp *) term).
Definition idtp := list (identifier * ((* tp *) term * thread)).

Definition state := (tgtp * lctp * idtp * history * xstate)%type.

Fixpoint traverse (S:Set) (enter : S -> S) (resolve : S -> nat -> term) (s : S) (t : term) {struct t} : term :=
  (match t with
   | var i => resolve s i
   | tm_loc l => tm_loc l
   | tm_nat n => tm_nat n
   | tm_label n => tm_label n
   | xp_bind t1 t2 t3 =>
       xp_bind (traverse S enter resolve s t1) (traverse S enter resolve s t2) (traverse S enter resolve (enter s) t3)
   | xp_spec t1 t2 t3 =>
       xp_spec (traverse S enter resolve s t1) (traverse S enter resolve s t2) (traverse S enter resolve s t3)
   | xp_read t1 m => xp_read (traverse S enter resolve s t1) m
   | xp_write t1 t2 m =>
       xp_write (traverse S enter resolve s t1) (traverse S enter resolve s t2) m
   | xp_rw t1 t2 =>
       xp_rw (traverse S enter resolve s t1) (traverse S enter resolve s t2)
   | xp_action i => xp_action i
   | xp_label l e =>
     xp_label (traverse S enter resolve s l) (traverse S enter resolve s e)

   | xp_if t1 t2 t3 =>
     xp_if (traverse S enter resolve s t1) (traverse S enter resolve s t2) (traverse S enter resolve s t3)
           
   | xp_repeat t =>
     xp_repeat (traverse S enter resolve s t)

   | ac_read l m => ac_read l m
   | ac_write l t m => ac_write l (traverse S enter resolve s t) m
   | ac_rw l t => ac_rw l (traverse S enter resolve s t)

   | tr_nothing => tr_nothing
   | tr_init i t2 =>
       tr_init i (traverse S enter resolve s t2)
   | tr_exec i t1 =>
       tr_exec i (traverse S enter resolve s t1)

   | nonsense => nonsense
   end).


Lemma traverse_var :
  forall S enter resolve s i,
    traverse S enter resolve s (var i) = resolve s i.
Proof.
auto.
Qed.


Lemma traverse_parametric :
  forall (S:Set) (S':Set) (R : S -> S' -> Prop) enter enter' resolve resolve' s s' t,
    (forall s s', R s s' -> R (enter s) (enter' s'))
    -> (forall s s' i, R s s' -> resolve s i = resolve' s' i)
    -> R s s'
    -> traverse S enter resolve s t = traverse S' enter' resolve' s' t.
Proof.
prove_traverse_parametric term_ind.
Qed.


Lemma traverse_id :
  forall (S:Set) (R : S -> Prop) enter resolve s t,
    (forall s, R s -> R (enter s))
    -> (forall s i, R s -> resolve s i = var i)
    -> R s
    -> traverse S enter resolve s t = t.
Proof.
prove_traverse_id term_ind.
Qed.


Lemma traverse_compose :
  forall (S:Set) (S':Set) enter enter' resolve resolve' s s' t,
    traverse S enter resolve s (traverse S' enter' resolve' s' t)
    = traverse (S * S')
      (fun p => let (s, s') := p in (enter s, enter' s'))
      (fun p i => let (s, s') := p in traverse S enter resolve s (resolve' s' i))
      (s, s') t.
Proof.
prove_traverse_compose term_ind.
Qed.


Definition termx := term.
Definition varx := var.
