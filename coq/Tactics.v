
(* Misc *)

Tactic Notation "isapp" constr(t) := (match t with appcontext [_ _] => idtac end).


Ltac last_hyp k
  :=
  (lazymatch goal with
   | H:_ |- _ => k H
   end).


Declare Reduction unf := lazy delta.


Ltac evargen T k
  :=
  let X := fresh "XYZZY"
  in
    evar (X : T);
    let E := eval unf in X in
      clear X;
      k E.


Tactic Notation "complete" tactic(tac)
  :=
  solve [tac].


(* Failure without the negative connotation, for marking completions. *)
Ltac done := fail 0 "goal incomplete".


Tactic Notation "#" "1" tactic(tac) := tac; [].
Tactic Notation "#" "2" tactic(tac) := tac; [|].
Tactic Notation "#" "3" tactic(tac) := tac; [| |].
Tactic Notation "#" "4" tactic(tac) := tac; [| | |].
Tactic Notation "#" "5" tactic(tac) := tac; [| | | |].
Tactic Notation "#" "6" tactic(tac) := tac; [| | | | |].
Tactic Notation "#" "7" tactic(tac) := tac; [| | | | | |].
Tactic Notation "#" "8" tactic(tac) := tac; [| | | | | | |].
Tactic Notation "#" "9" tactic(tac) := tac; [| | | | | | | |].
Tactic Notation "#" "10" tactic(tac) := tac; [| | | | | | | | |].
Tactic Notation "#" "11" tactic(tac) := tac; [| | | | | | | | | |].
Tactic Notation "#" "12" tactic(tac) := tac; [| | | | | | | | | | |].
Tactic Notation "#" "13" tactic(tac) := tac; [| | | | | | | | | | | |].
Tactic Notation "#" "14" tactic(tac) := tac; [| | | | | | | | | | | | |].
Tactic Notation "#" "15" tactic(tac) := tac; [| | | | | | | | | | | | | |].
Tactic Notation "#" "16" tactic(tac) := tac; [| | | | | | | | | | | | | | |].
Tactic Notation "#" "17" tactic(tac) := tac; [| | | | | | | | | | | | | | | |].
Tactic Notation "#" "18" tactic(tac) := tac; [| | | | | | | | | | | | | | | | |].
Tactic Notation "#" "19" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "20" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "21" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "22" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "23" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "24" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "25" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | | | |].




Ltac do2_main n tac :=
  (lazymatch n with
   | 0 => idtac
   | S ?n' => tac; [| do2_main n' tac]
   end).


Tactic Notation "do2" constr(n) tactic3(tac)
  :=
  do2_main n tac.


Ltac repeat2_main tac :=
  try (tac; [| repeat2_main tac]).


Tactic Notation "repeat2" tactic3(tac)
  :=
  repeat2_main tac.


Ltac splitall := repeat2 split.


Tactic Notation "splithyp" ident(H) := destruct H as [H | H].


Ltac findcontra :=
  (match goal with
   | H1:?T, H2:(not ?T) |- _ => destruct H2; exact H1
   | H1:(@eq _ ?x ?y), H2:(not (@eq _ ?y ?x)) |- _ => destruct H2; symmetry; exact H1
   | H:(not (@eq _ ?x ?x)) |- _ => destruct H; reflexivity
   | H:False |- _ => destruct H
   end).


Ltac revert_last
  :=
  (lazymatch goal with
     H:_ |- _ => revert H
   end).


Ltac revert_all := repeat revert_last.


Ltac clear_all := repeat (match goal with H:_ |- _ => clear H end).


Ltac destruct_all_main H :=
  (lazymatch type of H with
   | exists _:_, _ => 
               let H' := fresh "x"
               in
                 destruct H as [H' H]; destruct_all_main H'; destruct_all_main H
   | _ /\ _ => let H' := fresh "H"
               in
                 destruct H as [H' H]; destruct_all_main H'; destruct_all_main H
   | prod _ _ =>
               let H' := fresh "x"
               in
                 destruct H as [H' H]; destruct_all_main H'; destruct_all_main H
   | _ => idtac
   end).


Ltac destruct_all t :=
  first [
        destruct_all_main t
        |
        let H := fresh
        in
          pose proof t as H;
          destruct_all_main H
        ].


Tactic Notation "substeq" "->" hyp(H) :=
  (match type of H with
   | ?t = _ => subst t
   end).


Tactic Notation "substeq" "<-" hyp(H) :=
  (match type of H with
   | ?t = _ => subst t
   end).


Tactic Notation "f_apply" constr(f) "in" hyp(H) "as" ident(H') :=
  (match type of H with
   | @eq _ ?t1 ?t2 =>
       assert (f t1 = f t2) as H' by (f_equal; exact H);
       cbv beta in H'
   end).


Tactic Notation "f_apply" constr(f) "in" hyp(H) :=
  let H' := fresh "H" in f_apply f in H as H'.


Tactic Notation "eassert" constr(T)
  :=
  evargen T ltac:(fun X => assert X).


Tactic Notation "eassert" constr(T) "as" ident(H)
  :=
  evargen T ltac:(fun X => assert X as H).


Ltac cut_discriminate t1 t2
  :=
  let H := fresh
  in
    cut (t1 = t2); [intro H; discriminate H |].


Tactic Notation "renameover" hyp(H1) "into" hyp(H2) :=
  clear H2; rename H1 into H2.


(* Better inversion *)

(* Below, can't use "rewrite" because it numbers occurrences from the left, so there's no way to
   rewrite the last occurrence unless you know the total number of occurrences.  We can't use
   "remember" for the same reason, and also because its "eqn:" option requires a literal variable
   (ie, can't use an ltac identifier bound to a variable).
*)
Ltac invscan H F G ctac :=
  (lazymatch F with
   | ?F' ?x =>
       let y := fresh "x"
       in let Heq := fresh "Heq"
       in
         first
         [
         generalize (eq_refl x);
         generalize x at 1;
         intros y Heq;
         let Told := type of H
         in let Tnew := G (F' y)  (* must do this after y is introduced, or G (F' y) is ill-formed *)
         in
           replace Told with Tnew in H by (subst y; reflexivity);
           revert Heq;
           invscan H F' ltac:(fun F'' => G (F'' y)) ltac:(clear y; ctac)
         |
         (* generalizing x might fail with a dependent type, in which case do this *)
         invscan H F' ltac:(fun F'' => G (F'' x)) ctac
         ]
   | _ =>
       case H; clear H; ctac
   end).


Ltac simpimp stac rtac :=
  (lazymatch goal with
   | |- (@eq _ ?t ?t) -> _ =>
       intros _;
       simpimp stac rtac
   | |- forall (_:_),_ =>
       intro;
       (lazymatch goal with
        | y:_ |- _ =>
            first [ injection y; clear y; simpimp stac rtac
                  | simpimp ltac:(try (subst y); stac) ltac:(try (revert y); rtac) ]
        end)
   | |- _ => stac; rtac
   end).


Tactic Notation "invert" constr(t) :=
  let H := fresh
  in
    pose proof t as H;
    invscan H ltac:(type of H) ltac:(fun x => x) idtac; try (intros; discriminate);
    simpimp idtac idtac.


(* Simpler induction. *)

Tactic Notation "clear" "codependent" hyp(H)
  :=
  let T := type of H
  in
    clear H;
    repeat
      (match goal with
         x:_ |- _ =>
           (match T with
              appcontext [x] => 
                (* This might fail because:
                   * x is mentioned in a hyp that should have been reverted but wasn't,
                     so leaving it is necessary; or
                   * x is fixed (ie, non-inductive) argument to H,
                     so leaving it is actually desired.
                *)
                clear x
            end)
       end).


Tactic Notation "induct" hyp(H)
  :=
  elim H;
  clear codependent H.


Tactic Notation "induct" hyp(H) "using" constr(ind)
  :=
  elim H using ind;
  clear codependent H.


Tactic Notation "wfinduct" hyp(H) "using" constr(T) :=
  revert H;
  match goal with
  | |- forall x, @?P x => apply (well_founded_ind T P)
  end.


(* Proof labels *)

Tactic Notation "toshow" constr(P)
  :=
  (lazymatch goal with
   | |- P => idtac
   | |- ?Q => (lazymatch eval compute in P with
               | ?P' => (lazymatch eval compute in Q with
                         | P' => idtac
                         | _ => fail "conclusion does not match specification"
                         end)
               end)
   end).

Tactic Notation "have" constr(P) "as" hyp(H)
  :=
  (match type of H with
   | P => idtac
   | ?Q => (lazymatch eval compute in P with
            | ?P' => (lazymatch eval compute in Q with
                      | P' => idtac
                      | _ => fail 1 "hypothesis does not match specification"
                      end)
            end)
   end).


(* Use a hypothesis/lemma. *)

Ltac exploit_main t T pat cleanup
  :=
  (lazymatch T with
   | ?U1 -> ?U2 =>
       let H := fresh "QWERTY"
       in
         assert U1 as H;
         [cleanup () | exploit_main (t H) U2 pat ltac:(fun _ => clear H; cleanup ())]
   | _ =>
       pose proof t as pat;
       cleanup ()
   end).


Tactic Notation "exploit" constr(t) "as" simple_intropattern(pat)
  :=
  exploit_main t ltac:(type of t) pat ltac:(fun _ => idtac).


Tactic Notation "exploit" constr(t)
  :=
  let H := fresh "H"
  in
    exploit_main t ltac:(type of t) H ltac:(fun _ => idtac).


Ltac eexploit_main t T pat cleanup
  :=
  (lazymatch T with
   | ?U1 -> ?U2 =>
       let H := fresh "QWERTY"
       in
         assert U1 as H;
         [cleanup () | eexploit_main (t H) U2 pat ltac:(fun t' => clear H; cleanup ())]
   | forall x : ?S, @?P x =>
       evargen S ltac:(fun x' => eexploit_main (t x') ltac:(eval hnf in (P x')) pat cleanup)
   | _ =>
       pose proof t as pat;
       cleanup ()
   end).


Tactic Notation "eexploit" constr(t) "as" simple_intropattern(pat)
  :=
  eexploit_main t ltac:(type of t) pat ltac:(fun _ => idtac).


Tactic Notation "eexploit" constr(t)
  :=
  let H := fresh "H"
  in
    eexploit_main t ltac:(type of t) H ltac:(fun _ => idtac).


Ltac eapplyall
  :=
  (match goal with
     H:_ |- _ => eapply H
   end).


Ltac tryall tac
  :=
  try (match goal with H:_ |- _ => tac H end).


Ltac repeatall tac
  :=
  repeat (match goal with H:_ |- _ => tac H end).


Tactic Notation "thus" constr(P) "as" ident(H) "by" constr(T)
  :=
  assert P as H by (eapply T; eauto).


Tactic Notation "thus" constr(P) "by" constr(T)
  :=
  assert P by (eapply T; eauto).


Tactic Notation "so" constr(T) "as" simple_intropattern(pat)
  :=
  pose proof T as pat.


Tactic Notation "so" constr(T)
  :=
  pose proof T.


(* Better replace *)

Tactic Notation "repl" constr(t) "with" constr(t') :=
  let Heq := fresh
  in
    assert (t' = t) as Heq; [| rewrite <- Heq; clear Heq].

Tactic Notation "repl" constr(t) "with" constr(t') "in" hyp(H) :=
  let Heq := fresh
  in
    assert (t' = t) as Heq; [| rewrite <- Heq in H; clear Heq].

Tactic Notation "repl" constr(t) "with" constr(t') "at" ne_integer_list(l) :=
  let Heq := fresh
  in
    assert (t' = t) as Heq; [| rewrite <- Heq at l; clear Heq].

Tactic Notation "repl" constr(t) "with" constr(t') "in" hyp(H) "at" ne_integer_list(l) :=
  let Heq := fresh
  in
    assert (t' = t) as Heq; [| rewrite <- Heq in H at l; clear Heq].

Tactic Notation "repl" constr(t) "with" constr(t') "by" tactic(tac) :=
  let Heq := fresh
  in
    assert (t' = t) as Heq; [complete tac | rewrite <- Heq; clear Heq].

Tactic Notation "repl" constr(t) "with" constr(t') "in" hyp(H) "by" tactic(tac) :=
  let Heq := fresh
  in
    assert (t' = t) as Heq; [complete tac | rewrite <- Heq in H; clear Heq].

Tactic Notation "repl" constr(t) "with" constr(t') "at" ne_integer_list(l) "by" tactic(tac) :=
  let Heq := fresh
  in
    assert (t' = t) as Heq; [complete tac | rewrite <- Heq at l; clear Heq].

Tactic Notation "repl" constr(t) "with" constr(t') "in" hyp(H) "at" ne_integer_list(l) "by" tactic(tac) :=
  let Heq := fresh
  in
    assert (t' = t) as Heq; [complete tac | rewrite <- Heq in H at l; clear Heq].


(* Nat calculation *)

Require Import Omega.


Ltac simplify_nat t :=
  let rec scan acc t :=
    (lazymatch t with
     | 0 =>
         acc
     | S ?t1 =>
         let acc' :=
           (lazymatch acc with
            | ?tacc + ?n => constr:(tacc + S n)
            | ?n => constr:(S n)
            end)
         in
           scan acc' t1
     | ?t1 + ?t2 =>
         let acc' := scan acc t1
         in
           scan acc' t2
     | _ =>
         (lazymatch acc with
          | ?tacc + ?n => constr:((tacc + t) + n)
          | ?n => constr:(t + n)
          end)
     end)
  in
  let t' :=
    (lazymatch scan 0 t with
     | ?tacc + 0 => tacc
     | ?acc => acc
     end)
  in
    t'.


Ltac find_nat f t :=
  (match t with
   | 0 => fail
   | S _ => progress (f t)
   | _ + _ => progress (f t)
   | ?t1 ?t2 =>
       first [ find_nat f t1 | find_nat f t2 ]
   end).


Ltac calculate :=
  let simpit t' := let t'' := simplify_nat t'
                   in
                     replace t' with t'' by omega
  in
  (match goal with 
   | |- ?t => find_nat simpit t
   end).


Tactic Notation "calculate" "in" hyp(H)
  := 
  let simpit t' := let t'' := simplify_nat t'
                   in
                     replace t' with t'' in H by omega
  in
  (match goal with
   | H : ?t |- _ => find_nat simpit t
   end).


(* List membership discrimination *)

Require Import List.

Ltac discriminate_in Hin :=
  (match type of Hin with
   | In _ (_ :: _) =>
       let Heq := fresh "Heq"
       in
         destruct Hin as [Heq | Hin];
         [ simplify_eq Heq; clear Heq | discriminate_in Hin ]
   | In _ (app _ _) =>
       let Hin' := fresh "Hin"
       in
         destruct (@in_app_or _ _ _ _ Hin) as [Hin' | Hin'];
         [discriminate_in Hin' | discriminate_in Hin']
   | In _ (map _ _) =>
       let Heq := fresh
       in
         try (destruct (let (H, _) := @in_map_iff _ _ _ _ _ in H Hin) as (? & Heq & _);
              discriminate Heq)
   | In _ (flat_map _ _) =>
       let Hin' := fresh "Hin"
       in
         try (destruct (let (H, _) := @in_flat_map _ _ _ _ _ in H Hin) as (? & _ & Hin');
              complete (discriminate_in Hin'))
   | In _ nil =>
       destruct Hin
   | exists _:_, _ =>
       destruct Hin as (? & Hin);
       discriminate_in Hin
   | _ => revert Hin
   end).


Ltac auto_in :=
  (lazymatch goal with
   | |- In _ (_ :: _) =>
      first [ left; reflexivity | right; auto_in ]
   | |- In _ (_ ++ _) =>
      apply in_or_app;
      first [ left; auto_in | right; auto_in ]
   | _ =>
      assumption
   end).


(* Notation *)

Definition eqconv {A : Type} {P : A -> Prop} {x y : A} (Heq : x = y) (H : P x) : P y.
Proof.
subst y.
exact H.
Qed.


Definition eintro {A : Type} {P : A -> Prop} (x : A) (H : P x) : (exists x, P x).
Proof.
eauto.
Qed.


Definition car {A B : Set} (p : A * B) := let (x, _) := p in x.
Definition cdr {A B : Set} (p : A * B) := let (_, y) := p in y.

Definition caar {A B C : Set} (p : A * B * C) := (car (car p)).
Definition caaar {A B C D : Set} (p : A * B * C * D) := (car (car (car p))).
Definition cdaar {A B C D : Set} (p : A * B * C * D) := (cdr (car (car p))).
Definition cdar {A B C : Set} (p : A * B * C) := (cdr (car p)).
Definition cadr {A B C : Set} (p : A * (B * C)) := (car (cdr p)).
Definition cddr {A B C : Set} (p : A * (B * C)) := (cdr (cdr p)).


Definition tuple2 {T : Type} {A B : Set} :=
  fun (f : A -> B -> T) x => f (car x) (cdr x).

Definition tuple3 {T : Type} {A B C : Set} :=
  fun (f : A -> B -> C -> T) x => f (caar x) (cdar x) (cdr x).

Definition tuple4 {T : Type} {A B C D : Set} :=
  fun (f : A -> B -> C -> D -> T) x => f (caaar x) (cdaar x) (cdar x) (cdr x).

Definition tuple22 {T : Type} {A B C D : Set} :=
  fun (f : A -> B -> C -> D -> T) x => f (caar x) (cdar x) (cadr x) (cddr x).


Definition carp {P Q : Prop} (x : P /\ Q) : P.
elim x.
exact (fun p q => p).
Defined.

Definition cdrp {P Q : Prop} (x : P /\ Q) : Q.
elim x.
exact (fun p q => q).
Defined.

Definition cadrp {P Q R : Prop} (x : P /\ Q /\ R) := carp (cdrp x).
Definition cddrp {P Q R : Prop} (x : P /\ Q /\ R) := cdrp (cdrp x).


Definition swapp {P Q : Prop} (x : P \/ Q) : (Q \/ P).
Proof.
destruct x as [y | z].
  right; assumption.

  left; assumption.
Qed.


Notation "a 'andel'" := (carp a)
  (at level 11, left associativity, only parsing) : tactics_scope.

Notation "a 'ander'" := (cdrp a)
  (at level 11, left associativity, only parsing) : tactics_scope.

Notation " x _#2 " := (x _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#3 " := (x _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#4 " := (x _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#5 " := (x _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#6 " := (x _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#7 " := (x _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#8 " := (x _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#9 " := (x _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#10 " := (x _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#11 " := (x _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#12 " := (x _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#13 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#14 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#15 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#16 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#17 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#18 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#19 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#20 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.

Ltac disj n :=
  match n with
  | 0 => try left; idtac
  | S ?n' => 
    right; disj n'
  end.

Open Scope tactics_scope.
