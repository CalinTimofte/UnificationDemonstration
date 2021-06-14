From Licenta Require Import Semantics.
From Licenta Require Import Syntax.

Require Import String.
Open Scope string_scope.

Require Import List.
Import ListNotations.

Definition unification_problem_is_bottom (u : unification_problem) : bool :=
  true.

(*Inductive solver : Prop :=
  | Sbottom (u_p : unification_problem) (H : (unification_problem_is_bottom u_p) = true)
  | Ssolved (u_p : unification_problem) (H : (unification_problem_in_solved_form u_p) = true)
  | Sdelete (u_p u_p' : unification_problem)(H : ((term_in_unification_problem u_p term_eq) = true)) (H' : (remove_first_appearance_term_unification_problem u_p term_eq) = u_p')
  | Sdecompose (u_p u_p' : unification_problem)(tp : term_pair)(H : ((term_in_unification_problem u_p is_decomposition_term_pair) = true)) (H' : (remove_and_replace_decomposition_unif_problem tp u_p) = u_p')
  | Sorientation (u_p u_p' : unification_problem) (tp : term_pair) (H : ((term_in_unification_problem u_p is_orientation_term_pair) = true)) (H' : (apply_orientation tp u_p) = u_p') 
  | Selimination (u_p u_p' : unification_problem) (tp : term_pair) (H : ((term_in_unification_problem u_p is_elimination_term_pair) = true)) (H' : (elimination tp u_p) = u_p') 
  | Sconflict (u_p u_p' : unification_problem) (tp : term_pair) (H : ((term_in_unification_problem u_p is_conflict_term_pair) = true)) (H' : (remove_conflict_term_pair tp u_p) = u_p') 
  | Soccurs_check (u_p u_p' : unification_problem) (tp : term_pair) (H : ((term_in_unification_problem u_p is_occurs_check_term_pair) = true)) (H' : (occurs_check tp u_p) = u_p').


Inductive solver : Type :=
  | Sbottom (u : unification_problem)
  | Ssolved (u : unification_problem)
  | Sdelete (u : unification_problem)
  | Sdecompose (u : unification_problem)
  | Sorientation (u : unification_problem)
  | Selimination (u : unification_problem)
  | Sconflict (u : unification_problem)
  | Soccurs_check (u : unification_problem).
*)

Inductive solver : unification_problem -> Prop :=
  | Sbottom : solver Ubottom
  | Ssolved (u_p : unification_problem) (H : (unification_problem_in_solved_form u_p) = true) : solver u_p
  | Sdelete (u_p u_p' : unification_problem)(H : ((term_in_unification_problem u_p term_eq) = true)) (H' : (remove_first_appearance_term_unification_problem u_p term_eq) = u_p')(H'' : solver u_p'): solver u_p
  | Sdecompose (u_p u_p' : unification_problem)(H : ((term_in_unification_problem u_p is_decomposition_term_pair) = true)) (H': exists (tp : term_pair), (remove_and_replace_decomposition_unif_problem tp u_p) = u_p')(H'' : solver u_p'): solver u_p
  | Sorientation (u_p u_p' : unification_problem) (H : ((term_in_unification_problem u_p is_orientation_term_pair) = true)) (H' : exists (tp : term_pair), (apply_orientation tp u_p) = u_p') (H'' : solver u_p'): solver u_p
  | Selimination (u_p u_p' : unification_problem) (H : ((term_in_unification_problem u_p is_elimination_term_pair) = true)) (H' : exists (tp : term_pair), (elimination tp u_p) = u_p') (H'' : solver u_p'): solver u_p
  | Sconflict (u_p u_p' : unification_problem) (H : ((term_in_unification_problem u_p is_conflict_term_pair) = true)) (H' : exists (tp : term_pair), (remove_conflict_term_pair tp u_p) = u_p') (H'' : solver u_p'): solver u_p
  | Soccurs_check (u_p u_p' : unification_problem) (H : ((term_in_unification_problem u_p is_occurs_check_term_pair) = true)) (H' : exists (tp : term_pair), (occurs_check tp u_p) = u_p') (H'' : solver u_p'): solver u_p.

Definition is_bottom (u : unification_problem) : bool :=
  match u with
  | Ubottom => true
  | _ => false
  end.


Theorem is_solved_in_one_step : forall (u_p : unification_problem),
  ((is_bottom u_p) = true) \/ ((unification_problem_in_solved_form u_p) = true) ->
  solver u_p.
Proof.
  intros. destruct H.
  - destruct u_p.
    -- simpl in H. discriminate.
    -- apply Sbottom.
  - apply Ssolved. apply H.
Qed. 

