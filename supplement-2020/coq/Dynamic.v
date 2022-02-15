Require Import Tactics.
Require Import Relation.
Require Import Subst.
Export Syntax.
Require Import Sequence.
Require Import Coq.ZArith.Zdiv.

Definition varany := (tm_nat 0).

Inductive init : (* xp *) term -> Prop :=
| init_nat {n}
    : init (tm_nat n)

| init_bind {t e1 e2}
    : init e1
      -> init e2
      -> init (xp_bind t e1 e2)

| init_spec {v v' e}
    : init e
      -> init (xp_spec v v' e)

| init_action {i}
    : init (xp_action i)
.

(* TODO remove entirely *)
Inductive value : term -> Prop :=
| value_nat {n}
  : value (tm_nat n).

Inductive xstep : tgtp -> lctp -> (* xp *) term -> (* xp *) term -> (* tr *) term -> Prop :=

(* [l] -empty#i=[l]-> i *)
(* NOTE that the location and the value can be constants or variables only *)
| xstep_read {U P l i m}
    : xstep U P (xp_read (tm_loc l) m) (xp_action i) (tr_init i (ac_read l m))

(* [l] := n -empty#i=[l]:=n-> i *)
(* NOTE that the location and the value can be constants or variables only *)
| xstep_write {U P l n i m}
  (* : value G v ->  *)
     : xstep U P (xp_write (tm_loc l) (tm_nat n) m) (xp_action i) (tr_init i (ac_write l (tm_nat n) m))

(* [l] := n -empty#i=[l]:=n-> i *)
(* NOTE that the location and the value can be constants or variables only *)
| xstep_rw {U P l n i}
  (* : value G v ->  *)
     : xstep U P (xp_rw (tm_loc l) (tm_nat n)) (xp_action i) (tr_init i (ac_rw l (tm_nat n)))

(* TODO sort this out *)
(* i -i-> 0 *)
(* i -i ret n-> n *)
| xstep_exec {U P i n}
    : xstep U P (xp_action i) (tm_nat n) (tr_exec i (tm_nat n))

| xstep_label_under {U P l e e' d}
    : xstep U P e e' d
      -> xstep U P (xp_label l e) (xp_label l e') d

| xstep_label_rm {U P l n d}
    : xstep U P (xp_label l (tm_nat n)) (tm_nat n) d

(* e1 -d-> e1', let x = e1 in e2 -d-> let x = e1' in e2 -> *)
| xstep_bindl {U P t e1 e1' e2 d}
    : xstep U P e1 e1' d
      -> xstep U P (xp_bind t e1 e2) (xp_bind t e1' e2) d

(* init e1, e2 -d-> e2', let x = e1 in e2 -d-> let x = e1 in e2' -> *)
| xstep_bindr {U P t e1 e2 e2' d}
    : init e1
      -> xstep U P e2 e2' (shift1 d)
      -> xstep U P (xp_bind t e1 e2) (xp_bind t e1 e2') d

(* let x = n in e *)
| xstep_bind_subst {U P t n e}
  : xstep U P (xp_bind t (tm_nat n) e) (subst1 (tm_nat n) e) tr_nothing

(* [v1/x] e -empty-> v1 = v2 in [v2/x]e *)
| xstep_spec_subst {U P v1 v2 e}
    (* tmof requirements should be simple (if we keep them at all) because
    everything is a nat *)
    : value v1
      -> value v2
      -> xstep U P (subst1 v1 e) (xp_spec v1 v2 (subst1 v2 e)) tr_nothing

(* e -> e', v1 = v2 in e -empty-> v1 = v2 in e' *)
| xstep_spec_under {U P e e' d v1 v2}
    : xstep U P e e' d
      -> xstep U P (xp_spec v1 v2 e) (xp_spec v1 v2 e') d

(* v = v in e -empty-> e *)
| xstep_spec_rm {U P v e}
    : xstep U P (xp_spec v v e) e tr_nothing

(* n == 0, if n then e1 else e2 -empty-> e2 *)
| xstep_ifr {U P e1 e2}
    : xstep U P (xp_if (tm_nat 0) e1 e2) e2 tr_nothing

(* n =/= 0, if n then e1 else e2 -empty-> e1 *)
| xstep_ifl {U P x e1 e2}
    : x <> 0
      -> xstep U P (xp_if (tm_nat x) e1 e2) e1 tr_nothing

(* x not in FV(e), repeat n e -empty-> let x = n:e in if x then x else repeat (S n) e *)
| xstep_repeat {U P e t}
  : xstep U P
          (xp_repeat e)
          (xp_bind
             t (* = *) e (* in *)
             (xp_if (var 0) 
         (* then *) (var 0) 
         (* else *) (shift1 (xp_repeat e))))
          tr_nothing
.

Inductive xtrstep : tgtp -> lctp -> list term * term -> list term * term -> Prop :=
| xtrstep_base {U P trl trl' e e' tr} :
    xstep U P e e' tr ->
    trl' = tr :: trl ->
    xtrstep U P (trl,e) (trl',e').

Lemma list_neq :
  (forall v, forall a : list v, forall b : v, a <> b::a ).
Proof.
  intros.
  induction a.
  - discriminate.
  - unfold not.
    intros contra.
    inversion contra.
    contradiction.
Qed.

Lemma irreflexive_xtrstep :
  forall U P, irreflexive (list term * term) (xtrstep U P).
Proof.
  intros.
  intro H.
  inversion H.
  inversion H0.
  apply list_neq in H7.
  assumption.
Qed.

Inductive exstep : tgtp -> lctp -> xstate -> xstate -> (* tr *) term -> thread -> Prop :=
| exstep_hit {U P ex p e e' d}
    : xstep U P e e' d
      -> exstep U P (ex; (p, e)) (ex; (p, e')) d p

| exstep_miss {U P ex ex' p e d p'}
    : exstep U P ex ex' d p'
      -> exstep U P (ex; (p, e)) (ex'; (p, e)) d p'
.

Definition program := ((list term) * thread * xstate)%type.

Inductive extrstep : tgtp -> lctp -> program -> program -> Prop :=
| xstrep_base {U P ds ds' d p p' ex ex'}
  : exstep U P ex ex' d p' 
    -> ds' = d :: ds
    -> extrstep U P (ds, p, ex) (ds', p', ex').


Hint Constructors init xstep xtrstep exstep extrstep : dynamic.

(* Reads and write *)
Inductive reads : history -> identifier -> location -> Prop :=
| reads_read {H i l m}
  : H {{ ev_is i (ac_read l m) }}
    -> reads H i l
| reads_rw {H i l v}
  : H {{ ev_is i (ac_rw l v)}}
    -> reads H i l.

Inductive writes : history -> identifier -> location -> (* tm *) term -> Prop :=
| writes_write {H i l v m}
  : H {{ ev_is i (ac_write l v m) }}
    -> writes H i l v
| writes_rw {H i l v}
  : H {{ ev_is i (ac_rw l v)}}
    -> writes H i l v.

Definition writesto H i l := exists v, writes H i l v.
Definition access H i l := reads H i l \/ writesto H i l.

Hint Constructors reads writes : dynamic.

(* program order *)
(* Should we define this as for trace order? *)
Definition po (H : history) (i i' : identifier) : Prop :=
  exists H1 H2 H3 p,
    H = H1; ev_init i p;; H2; ev_init i' p;; H3.

Definition poq H i i' := i = i' \/ po H i i'.


(* exec *)
Inductive exec : history -> identifier -> Prop :=
| exec_exec {H i}
    : H {{ ev_exec i }}
      -> exec H i

| exec_rf {H i' i}
    : H {{ ev_rf i' i }}
      -> exec H i.

Definition executes h i := (h = ev_exec i) \/ (exists iw, h = ev_rf iw i).

(* trace order *)
Definition to (H : history) (i i' : identifier) : Prop :=
  exists H1 H2,
    H = H1;; H2
    /\ exec H1 i
    /\ ~ exec H1 i'.
    
Definition toq H i i' := i = i' \/ to H i i'.

(* reads-from *)
Definition rf H i i' := H {{ ev_rf i i' }}.
Definition rwf H i i' := H {{ ev_rf i i' }} /\ H {{ ev_is i' (ac_rw le ve) | le ve }}.

Definition rwfs H := star (rwf H).
Definition rwfp H := plus (rwf H).

Definition opm m := m = opaque \/ m = relacq \/ m = vol.
Definition isopr H i := exists m, H {{ ev_is i (ac_read le m) | le }} /\ opm m.
Definition isopw H i := exists m, H {{ ev_is i (ac_write le ve m) | le ve }} /\ opm m.
Definition isop H i := isopr H i \/ isopw H i.
Definition pop H i i' := po H i i' /\ isop H i /\ isop H i'.

Definition isr H i := exists l, reads H i l.
Definition isw H i := exists l v, writes H i l v.
Definition isrw H i := H {{ ev_is i (ac_rw le ve) | le ve }}.
Definition isvolw H i := H {{ ev_is i (ac_write le ve vol) | le ve }} .
Definition isvolr H i := H {{ ev_is i (ac_read le vol) | le }} .
Definition isvol H i := isvolr H i \/ isvolw H i.
Definition isrelw H i := H {{ ev_is i (ac_write le ve relacq) | le ve }} \/  isvolw H i.
Definition isacqr H i := H {{ ev_is i (ac_read le relacq) | le }} \/ isvolr H i.

(* OLD *)
Definition volrpo H i i' := isvolr H i' /\ po H i i'. (* works with acqr def *)
Definition volwpo H i i' := isvolw H i /\ po H i i'. (* works with relw def *)

(* NEW *)
Definition volpo H i i' := isvol H i /\ isvol H i' /\ po H i i'.

Definition spush H i i' :=  H {{ ev_push i i' }} /\ po H i i'.
Definition svo H i i' := H {{ ev_vo i i' }} /\ po H i i'.

(* includes volatile w and r per the axiomatic semantics  *)
Definition push H i i' := spush H i i' \/ volpo H i i'.

(* specified order definitions should appear before the second id's execution,
   otherwise their effects cannot apply in the derivation of coherence order cycles *)
Axiom spo_before :
  forall H h i1 i2,
    h = (ev_vo i1 i2) \/ h = (ev_push i1 i2) 
    -> ~ exec (H; h) i2.

Definition relvo H i i' := isrelw H i' /\ po H i i'.
Definition acqvo H i i' := isacqr H i /\ po H i i'. 
Definition pushvo H i i' := exists i'' i''', push H i i'' /\ push H i''' i' /\ to H i i'''.

Inductive so : history -> identifier -> identifier -> Prop :=
| so_vo {H i i'}
  : po H i i'
    -> H {{ ev_vo i i' }}
    -> so H i i'

| so_push {H i i'}
  : po H i i'
    -> H {{ ev_push i i' }}
    -> so H i i'

| so_acqr {H i i'}
  : po H i i'
    -> isacqr H i
    -> so H i i'

| so_relw {H i i'}
  : po H i i'
    -> isrelw H i'
    -> so H i i'

| so_vol {H i i'}
  : po H i i'
    -> isvol H i
    -> isvol H i'
    -> so H i i'
.

Definition sop H := plus (so H).

(* visibility order *)
(* TODO swich svo, push, relvo, acqvo and vol(wr) to so *)
Definition vo H i i' :=
  svo H i i' \/
  rf H i i' \/
  push H i i' \/
  relvo H i i' \/
  acqvo H i i' \/
  pushvo H i i'.

Definition vos H := star  (vo H).
Definition vop H := plus  (vo H).

Definition visibile := vos.

(* Trying to keep the lemmas in History.v *)
Definition vt := vop.

Definition vopo H i1 i2 :=
  vop H i1 i2 \/ po H i1 i2.

Inductive co : history -> identifier -> identifier -> Prop :=
| co_ww {H i1 i2 l}
  : vopo H i1 i2
    -> writesto H i1 l
    -> writesto H i2 l
    -> co H i1 i2

| co_wr {H i1 i2 l ir}
  : vopo H i1 ir
    -> rf H i2 ir
    -> writesto H i1 l
    -> reads H ir l
    -> i1 <> i2
    -> co H i1 i2

| co_rw {H i1 ir i2 l}
  : vopo H i1 ir
    -> po H ir i2
    -> writesto H i1 l
    -> reads H ir l
    -> writesto H i2 l
    -> co H i1 i2

| co_rr {H i1 i2 ir1 ir2 l}
  : rf H i1 ir1
    -> rf H i2 ir2
    -> po H ir1 ir2
    -> writesto H i1 l
    -> writesto H i2 l
    -> i1 <> i2
    -> co H i1 i2

(* concurrent writes to the same location are trace ordered when at least one
   is an atomic readwrite *)
| co_atm_total {H iw1 iw2 l}
  : isrw H iw1 \/ isrw H iw2
    -> writesto H iw1 l
    -> writesto H iw2 l
    -> to H iw1 iw2
    -> co H iw1 iw2

(* non-concurrent writes are ordered after the atomic read-write  *)
| co_atm_after {H irw iw1 iw2}
    : rwf H iw1 irw
      -> co H iw1 iw2
      -> irw <> iw2
      -> co H irw iw2
.

(* TODO bring in proof of relationship with old RMC co from RMC/Gps.v *) 

Definition cos H := star (co H).
Definition cop H := plus (co H).

Definition executable H i := ~ exec H i /\ forall i', so H i' i -> exec H i'.

Inductive trans : history -> (* tr *) term -> thread -> history -> Prop :=
| trans_nothing {H p}
    : trans H tr_nothing p H

| trans_init {H i a p}
    : ~ H {{ ev_init i p | p }}
      -> trans H (tr_init i a) p (H; ev_init i p; ev_is i a)

| trans_read {H ir l p iw v}
    : H {{ ev_init ir p }}
      -> reads H ir l 
      -> executable H ir
      -> writes H iw l v
      -> exec H iw
      -> acyclic (co (H; ev_rf iw ir))
      -> acyclic (union (pop (H; ev_rf iw ir)) (rf (H; ev_rf iw ir)))
      -> trans H (tr_exec ir v) p (H; ev_rf iw ir)

| trans_write {H i l p}
    : H {{ ev_init i p }}
      -> (exists m v, H {{ ev_is i (ac_write l v m) }})
      -> executable H i
      -> acyclic (co (H; ev_exec i))
      -> trans H (tr_exec i (tm_nat 0)) p (H; ev_exec i)
.


Inductive step : state -> state -> Prop :=
| step_sync {U P I U' P' I' H H' ex ex' d p}
    : exstep U P ex ex' d p
      -> trans H d p H'
      -> step (U, P, I, H, ex) (U', P', I', H', ex')
.