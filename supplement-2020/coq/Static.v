
Require Import Tactics.
Require Import Subst.
Export Syntax.
Require Import Sequence.


Inductive iscl : term -> Prop :=
| iscl_vl {t}
    : iscl (cl_vl t)
| iscl_tg
    : iscl cl_tg.

Hint Constructors iscl : static.


(* depends on static hints *)
Lemma subst_cl :
  forall s c, iscl c -> iscl (subst s c).
Proof.
intros s c Hc.
destruct Hc; simp_sub; auto with static.
Qed.


Definition context := list term.


Inductive value : context -> term -> Prop :=
| value_var {G i t}
    : index i G (cl_vl t)
      -> value G (var i)

| value_unit {G}
    : value G tm_unit

| value_lit {G c}
    : value G (tm_lit c)

| value_loc {G l}
    : value G (tm_loc l)

| value_susp {G e}
    : value G (tm_susp e)

| value_lam {G t m}
    : value G (tm_lam t m)

| value_fun {G t1 t2 m}
    : value G (tm_fun t1 t2 m)
.


Inductive tgof : tgtp -> context -> (* tg *) term -> Prop :=
| tgof_var {U G i}
    : index i G cl_tg
      -> tgof U G (var i)

| tgof_lit {U G T}
    : In T U
      -> tgof U G (tg_lit T)
.


Inductive tpof : context -> (* tp *) term -> Prop :=
| tpof_unit {G}
    : tpof G tp_unit

| tpof_base {G}
    : tpof G tp_base

| tpof_susp {G t}
    : tpof G t
      -> tpof G (tp_susp t)

| tpof_ref {G t}
    : tpof G t
      -> tpof G (tp_ref t)

| tpof_arrow {G t1 t2}
    : tpof G t1
      -> tpof G t2
      -> tpof G (tp_arrow t1 t2)
.


Inductive fcof : tgtp -> context -> (* fc *) term -> Prop :=
| fcof_tag {U G T}
    : tgof U G T
      -> fcof U G (fc_tag T)

| fcof_pre {U G b}
    : fcof U G (fc_pre b)

| fcof_post {U G b}
    : fcof U G (fc_post b)
.


Inductive init : (* xp *) term -> Prop :=
| init_ret {m}
    : init (xp_ret m)

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


Inductive tmof : tgtp -> lctp -> context -> (* tm *) term -> (* tp *) term -> Prop :=
| tmof_var {U P G i t}
    : index i G (cl_vl t)
      -> tmof U P G (var i) (subst (sh (S i)) t)

| tmof_unit {U P G}
    : tmof U P G tm_unit tp_unit

| tmof_lit {U P G c}
    : tmof U P G (tm_lit c) tp_base

| tmof_prim {U P G m1 m2}
    : tmof U P G m1 tp_base
      -> tmof U P G m2 tp_base
      -> tmof U P G (tm_prim m1 m2) tp_base

| tmof_if {U P G m m1 m2 t}
    : tmof U P G m tp_base
      -> tmof U P G m1 t
      -> tmof U P G m2 t
      -> tmof U P G (tm_if m m1 m2) t

| tmof_loc {U P G l t}
    : lookup l P t
      -> tmof U P G (tm_loc l) (tp_ref (subst (sh (length G)) t))

| tmof_susp {U P G e t}
    : xpof U P nil G e t
      -> tmof U P G (tm_susp e) (tp_susp t)

| tmof_lam {U P G m t1 t2}
    : tpof G t1
      -> tmof U P (G; cl_vl t1) m (shift1 t2)
      -> tmof U P G (tm_lam t1 m) (tp_arrow t1 t2)

| tmof_fun {U P G m t1 t2}
    : tpof G t1
      -> tpof G t2
      -> tmof U P (G; cl_vl (tp_arrow t1 t2); cl_vl (shift1 t1)) m (subst (sh 2) t2)
      -> tmof U P G (tm_fun t1 t2 m) (tp_arrow t1 t2)

| tmof_app {U P G m1 m2 t1 t2}
    : tmof U P G m1 (tp_arrow t1 t2)
      -> tmof U P G m2 t1
      -> tmof U P G (tm_app m1 m2) t2


with xpof : tgtp -> lctp -> idtp -> context -> (* xp *) term -> (* tp *) term -> Prop :=
| xpof_ret {U P G m t}
    : tmof U P G m t
      -> xpof U P nil G (xp_ret m) t

| xpof_force {U P G m t}
    : tmof U P G m (tp_susp t)
      -> xpof U P nil G (xp_force m) t

| xpof_bind {U P I G t1 e1 e2 t2}
    : tpof G t1
      -> xpof U P I G e1 t1
      -> xpof U P nil (G; cl_vl t1) e2 (shift1 t2)
      -> xpof U P I G (xp_bind t1 e1 e2) t2

| xpof_bind_init {U P I1 I2 G t1 e1 e2 t2}
    : init e1
      -> tpof G t1
      -> xpof U P I1 G e1 t1
      -> xpof U P I2 (G; cl_vl t1) e2 (shift1 t2)
      -> xpof U P (I1;; I2) G (xp_bind t1 e1 e2) t2

| xpof_spec {U P I G v1 v2 t e t'}
    : tmof U P G v1 t
      -> tmof U P G v2 t
      -> value G v1
      -> value G v2
      -> xpof U P I G e t'
      -> xpof U P I G (xp_spec v1 v2 e) t'

| xpof_read {U P G m t}
    : tmof U P G m (tp_ref t)
      -> xpof U P nil G (xp_read m) t

| xpof_write {U P G m1 m2 t}
    : tmof U P G m1 (tp_ref t)
      -> tmof U P G m2 t
      -> xpof U P nil G (xp_write m1 m2) tp_unit

| xpof_rw {U P G m1 m2 t}
    : tmof U P G m1 (tp_ref t)
      -> tmof U P G m2 t
      -> xpof U P nil G (xp_rw m1 m2) t

| xpof_rmw {U P G t m1 m2}
    : tpof G t
      -> tmof U P G m1 (tp_ref t)
      -> tmof U P (G; cl_vl t) m2 (shift1 t)
      -> xpof U P nil G (xp_rmw t m1 m2) t

| xpof_push {U P G}
    : xpof U P nil G xp_push tp_unit

| xpof_nop {U P G}
    : xpof U P nil G xp_nop tp_unit

| xpof_action {U P G i t p}
    : xpof U P (nil; (i, (t, p))) G (xp_action i) (subst (sh (length G)) t)

| xpof_new {U P G e t b}
    : xpof U P nil (G; cl_tg; cl_tg) e (subst (sh 2) t)
      -> xpof U P nil G (xp_new b e) t

| xpof_fence {U P I G f e t}
    : fcof U G f
      -> xpof U P I G e t
      -> xpof U P I G (xp_fence f e) t
.


Scheme tmof_mut_ind := Minimality for tmof Sort Prop
with   xpof_mut_ind := Minimality for xpof Sort Prop.
Combined Scheme tmof_xpof_ind from tmof_mut_ind, xpof_mut_ind.


Inductive ofs : tgtp -> context -> term -> term -> Prop :=
| ofs_vl {U G e t}
    : ofs U G e (cl_vl t)

| ofs_tg {U G T}
    : tgof U G T
      -> ofs U G T cl_tg
.


Inductive ofd : tgtp -> lctp -> context -> term -> term -> Prop :=
| ofd_vl {U P G v t}
    : tmof U P G v t
      -> value G v
      -> ofd U P G v (cl_vl t)

| ofd_tg {U P G T}
    : tgof U G T
      -> ofd U P G T cl_tg
.


Inductive clof : tgtp -> context -> term -> Prop :=
| clof_vl {U G t}
    : tpof G t
      -> clof U G (cl_vl t)

| clof_tg {U G}
    : clof U G cl_tg.


Inductive ctxof : tgtp -> context -> Prop :=
| ctxof_nil {U}
    : ctxof U nil

| ctxof_cons {U G c}
    : ctxof U G
      -> clof U G c
      -> ctxof U (G; c)
.


Fixpoint restricteq (I : idtp) (p : thread) {struct I} : idtp :=
  (match I with
   | nil => nil
   | I'; (i, (t, p')) =>
       if eq_thread_dec p p' then
         restricteq I' p; (i, (t, p'))
       else
         restricteq I' p
   end).


Fixpoint restrictneq (I : idtp) (p : thread) {struct I} : idtp :=
  (match I with
   | nil => nil
   | I'; (i, (t, p')) =>
       if eq_thread_dec p p' then
         restrictneq I' p
       else
         restrictneq I' p; (i, (t, p'))
   end).


Inductive exof : tgtp -> lctp -> idtp -> xstate -> Prop :=
| exof_nil {U P}
    : exof U P nil nil

| exof_cons {U P I ex p e t}
    : ~ indom p ex 
      -> exof U P (restrictneq I p) ex
      -> xpof U P (restricteq I p) nil e t
      -> exof U P I (ex; (p, e))
.


Inductive acof : tgtp -> lctp -> context -> (* ac *) term -> (* tp *) term -> Prop :=
| acof_read {l U P G t}
    : lookup l P t
      -> acof U P G (ac_read l) (subst (sh (length G)) t)

| acof_write {U P G l v t}
    : lookup l P t
      -> value G v
      -> tmof U P G v (subst (sh (length G)) t)
      -> acof U P G (ac_write l v) tp_unit

| acof_rw {U P G l v t}
    : lookup l P t
      -> value G v
      -> tmof U P G v (subst (sh (length G)) t)
      -> acof U P G (ac_rw l v) (subst (sh (length G)) t)

| acof_push {U P G}
    : acof U P G ac_push tp_unit

| acof_nop {U P G}
    : acof U P G ac_nop tp_unit
.


Inductive flof : tgtp -> context -> (* fl *) term -> Prop :=
| flof_nil {U G}
    : flof U G fl_nil

| flof_cons {U G f fl}
    : flof U G fl
      -> fcof U G f
      -> flof U G (fl_cons f fl)
.


(* Carries typing information out of expressions. *)
Inductive trofo : tgtp -> lctp -> idtp -> context -> (* tr *) term -> Prop :=
| trofo_nothing {U P I G}
    : trofo U P I G tr_nothing

| trofo_init {U P I G fl i a t}
    : flof U G fl
      -> acof U P G a t
      -> trofo U P I G (tr_init fl i a)

| trofo_exec {U P I G i v}
    : trofo U P I G (tr_exec i v)

| trofo_new {U P I G b T T'}
    : trofo U P I G (tr_new b T T')
.


Definition tgtpof (U : tgtp) : Prop := NoDup U.


Inductive lctpof : lctp -> Prop :=
| lctpof_nil
    : lctpof nil

| lctpof_cons {P l t}
    : lctpof P
      -> ~ indom l P
      -> tpof nil t
      -> lctpof (P; (l, t))
.


Definition idtpof (I : idtp) : Prop := ddistinct I.

(* We really ought to use the following instead, but then we would need to prove regularity. *)
(*
Inductive idtpof : idtp -> Prop :=
| idtpof_nil
    : idtpof nil

| idtpof_cons {I i t p}
    : idtpof I
      -> ~ indom i I
      -> tpof nil t
      -> idtpof (I; (i, (t, p)))
.
*)


Inductive evolve : tgtp -> lctp -> idtp -> (* tr *) term -> thread -> tgtp -> lctp -> idtp -> Prop :=
| evolve_nothing {U P I p}
    : evolve U P I tr_nothing p U P I

| evolve_init {U P I fl i a t p}
    : ~ indom i I
      -> flof U nil fl
      -> acof U P nil a t
      -> evolve U P I (tr_init fl i a) p U P (I; (i, (t, p)))

| evolve_exec {U P I1 I2 i t p v}
    : tmof U P nil v t
      -> evolve U P (I1; (i, (t, p));; I2) (tr_exec i v) p U P (I1;; I2)

| evolve_new {U P I b T T' p}
    : ~ In T U
      -> ~ In T' U
      -> T <> T'
      -> evolve U P I (tr_new b T T') p (U; T; T') P I
.


Hint Constructors value tgof tpof fcof init tmof xpof ofs ofd clof ctxof exof acof flof trofo evolve : static.


Definition isclx := iscl.
