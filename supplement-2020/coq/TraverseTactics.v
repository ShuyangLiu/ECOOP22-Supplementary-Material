
Ltac prove_traverse_parametric ind :=
intros S S' R enter enter' resolve resolve' s s' t Henter Hresolve Hs;
generalize dependent s';
generalize dependent s;
induction t using ind; intros s s' Hs;
[apply Hresolve; apply Hs | ..];  (* deal with first goal (var) *)
simpl;
try reflexivity;  (* dispense with trivial goals *)
f_equal;
(* find and apply IH *)
try
  ((match goal with
    | IH : (forall (s : S) (s' : S'), _ -> _ = ?f _ ?t)
      |- _ = ?g _ ?t
      => apply IH
    end);
   repeat (apply Henter);
   apply Hs).


Ltac prove_traverse_id ind :=
intros S R enter resolve s t Henter Hresolve Hs;
generalize dependent s;
induction t using ind; intros s Hs;
[apply Hresolve; apply Hs | ..];  (* deal with first goal (var) *)
simpl;
try reflexivity;  (* dispense with trivial goals *)
f_equal;
(* find and apply IH *)
try ((match goal with
      | IH : (forall (s : S), _ -> _ = ?t)
        |- _ = ?t
        => apply IH
      end);
     repeat (apply Henter);
     apply Hs).


Ltac prove_traverse_compose ind :=
intros S S' enter enter' resolve resolve' s s' t;
generalize dependent s';
generalize dependent s;
induction t using ind; intros s s';
[simpl; reflexivity | ..];  (* deal with first goal (var) *)
simpl;
try reflexivity;  (* dispense with trivial goals *)
f_equal;
(* find and apply IH *)
try (match goal with
      | IH : (forall (s : S) (s' : S'), _ = ?f ?t)
        |- _ = ?g ?t
        => apply IH
      end).


