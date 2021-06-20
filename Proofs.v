From Licenta Require Import Semantics.
From Licenta Require Import Syntax.
From Licenta Require Import Unification_solver2.

Theorem apply_conflict_up_different: forall (u_p : unification_problem),
  ~(check_conflict_and_deliver u_p = TError) /\ ~(u_p = Ubottom) ->
  ~(u_p = occurs_check (mtp_to_tp (check_conflict_and_deliver u_p)) u_p).
Proof.
  intros. destruct H. induction u_p.
  - simpl. apply H0.
  - destruct ((check_conflict_and_deliver (Uset l))).
    -- contradiction.
    -- simpl. unfold occurs_check. unfold remove_conflict_term_pair. apply H0.
Qed.

Theorem progress'' : forall (m_u_p: maybe_unification_problem),
  ~(m_u_p = UError) /\
  ~(m_u_p = UP Ubottom) /\ ~(unification_problem_in_solved_form (mup_to_up m_u_p) = true) ->
  (exists (m_u_p' : maybe_unification_problem), (apply_one_step' m_u_p = m_u_p') /\ ~(m_u_p = m_u_p')).
Proof.
  intros. destruct H. destruct H0. exists (apply_one_step' m_u_p). split.
  - reflexivity.
  - destruct m_u_p.
    -- contradiction.
    -- simpl.  destruct u_p.
      --- contradiction.
      --- simpl in H1. destruct (unification_problem_in_solved_form (Uset l)).
        ---- contradiction.
        ---- destruct (check_conflict_and_deliver (Uset l)).
          2 : { apply apply_conflict_up_different.