Require Import List.

Definition eq_dec (T : Set) := forall x x' : T, {x = x'} + {x <> x'}.

Definition finite (T : Set) := exists l : list T, forall x, In x l.
Definition infinite (T : Set) := forall l : list T, exists x, ~ In x l.


Definition thread := nat.

Axiom eq_thread_dec : eq_dec thread.

Axiom thread_finite : finite thread.  (* generalize this *)


Definition location := nat.

Axiom eq_loc_dec : eq_dec location.

Axiom loc_infinite : infinite location.


Definition identifier := nat.

Axiom eq_ident_dec : eq_dec identifier.

Axiom ident_infinite : infinite identifier.


Definition tag := nat.

Axiom eq_tag_dec : eq_dec tag.

Axiom tag_infinite : infinite tag.


Parameter base : Set.
Parameter base0 : base.  (* a distinguished element *)
Parameter prim : base -> base -> base.

Axiom eq_base_dec : eq_dec base.
