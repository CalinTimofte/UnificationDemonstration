From Licenta Require Import Semantics.
From Licenta Require Import Syntax.

Theorem apply_conflict_up_different: forall (u_p : unification_problem) (tp: term_pair),
  ~(check_conflict_and_deliver u_p = TError) /\ ~(u_p = Ubottom) ->
  ~(UP u_p = UP (remove_conflict_term_pair tp u_p)).
Proof.
  intros. destruct H. induction u_p.
  - contradiction.
  - destruct ((check_conflict_and_deliver (Uset l))).
    -- contradiction.
    -- unfold occurs_check. unfold remove_conflict_term_pair. injection. apply H0.
Qed.

Theorem apply_occurs_check_up_different: forall (u_p : unification_problem) (tp: term_pair),
  ~(check_occurs_check_and_deliver u_p = TError) /\ ~(u_p = Ubottom) ->
  ~(UP u_p = UP (occurs_check tp u_p)).
Proof.
  intros. destruct H. induction u_p.
  - contradiction.
  - destruct ((check_occurs_check_and_deliver (Uset l))).
    -- contradiction.
    -- unfold occurs_check. unfold remove_conflict_term_pair. injection. apply H0.
Qed.

Theorem apply_delete_up_different: forall (u_p : unification_problem) (tp: term_pair),
  ~(check_delete_and_deliver u_p = TError) /\ ~(u_p = Ubottom) 
  /\ (check_delete_and_deliver u_p = TP tp) ->
  ~(UP u_p = UP (solver_delete tp u_p)).
Proof.
  intros. destruct H. destruct H0. induction u_p.
  - contradiction.
  - destruct ((check_delete_and_deliver (Uset l))).
    -- contradiction.
    -- unfold solver_delete. unfold remove_first_appearance_term_unification_problem.
       destruct (remove_first_appearance_term_pair_list) as [|l0] eqn: H_first_app.
      --- injection. destruct l.
        ----

Qed.

Theorem neq_mup_implies_neq_up: forall (u_p u_p' : unification_problem),
  (UP u_p <> UP u_p')->
  (u_p <> u_p').
Proof.
  intros. unfold not. intros. unfold not in H. apply H. rewrite H0. reflexivity.
Qed.

Theorem progress'' : forall (m_u_p: maybe_unification_problem),
  ~(m_u_p = UError) /\
  ~(m_u_p = UP Ubottom) /\ ~(unification_problem_in_solved_form (mup_to_up m_u_p) = true) ->
  (exists (m_u_p' : maybe_unification_problem), (maybe_apply_one_step m_u_p = m_u_p') /\ ~(m_u_p = m_u_p')).
Proof.
  intros. destruct H. destruct H0. exists (maybe_apply_one_step m_u_p). split.
  - reflexivity.
  - destruct m_u_p.
    -- contradiction.
    -- simpl.  destruct u_p.
      --- contradiction.
      --- simpl in H1. destruct (unification_problem_in_solved_form (Uset l)).
        ---- contradiction.
        ---- destruct (check_conflict_and_deliver (Uset l)) as [ | mtp] eqn: tp_eq_conflict.
          2 : { apply (apply_conflict_up_different (Uset l)). split.
            - rewrite tp_eq_conflict. unfold not. intros. discriminate.
            - apply neq_mup_implies_neq_up. apply H0. }
          ----- destruct (check_occurs_check_and_deliver (Uset l)) as [ | mtp] eqn: tp_eq_occurs_check.
            2 : { apply (apply_occurs_check_up_different (Uset l)). split.
              - rewrite tp_eq_occurs_check. unfold not. intros. discriminate.
              - apply neq_mup_implies_neq_up. apply H0. }
            ------ destruct (check_delete_and_deliver (Uset l)) as [ | mtp] eqn: tp_eq_delete.
              2 : { 