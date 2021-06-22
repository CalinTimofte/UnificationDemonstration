From Licenta Require Import Semantics.
From Licenta Require Import Syntax.

Require Import String.
Open Scope string_scope.

Require Import List.
Import ListNotations.

Theorem apply_conflict_up_different: forall (u_p : unification_problem) (tp: term_pair),
  ~(check_conflict_and_deliver u_p = TError) /\ ~(u_p = Ubottom) ->
  maybe_unification_problem_eq (UP u_p) (UP (remove_conflict_term_pair tp u_p)) = false.
Proof.
  intros. destruct H. induction u_p.
  - contradiction.
  - destruct ((check_conflict_and_deliver (Uset l))).
    -- contradiction.
    -- unfold occurs_check. unfold remove_conflict_term_pair. simpl. reflexivity.
Qed.

Theorem apply_occurs_check_up_different: forall (u_p : unification_problem) (tp: term_pair),
  ~(check_occurs_check_and_deliver u_p = TError) /\ ~(u_p = Ubottom) ->
  maybe_unification_problem_eq (UP u_p) (UP (occurs_check tp u_p)) = false.
Proof.
  intros. destruct H. induction u_p.
  - contradiction.
  - destruct ((check_occurs_check_and_deliver (Uset l))).
    -- contradiction.
    -- unfold occurs_check. unfold remove_conflict_term_pair. simpl. reflexivity.
Qed.

Theorem deliver_tpair_means_in_list: forall (l : list term_pair) (tp: term_pair) (criterion: term -> term -> bool),
  ~(deliver_tpair_from_list l criterion = TError) ->
  In tp l.
Proof.
  intros. induction l.
  - simpl in H. contradiction.
  - simpl. right. apply IHl. unfold deliver_tpair_from_list. destruct term_pair_correct_for_rule.
Admitted.

Theorem delete_shortens_list: forall (l : list term_pair) (tp: term_pair),
  deliver_tpair_from_list l term_eq = TP tp ->
  length l = S (length (remove_decomposition_term_pair tp l)).
Proof.
  intros. unfold remove_decomposition_term_pair. Admitted.

Theorem delete_term_list_inequality: forall (l : list term_pair) (tp: term_pair),
  deliver_tpair_from_list l term_eq = TP tp ->
  term_pair_list_eq l (remove_decomposition_term_pair tp l) = false.
Proof.
  intros. induction l.
  - simpl in H. discriminate.
  - simpl. induction (term_pair_eq tp a).
    -- induction l.
      --- reflexivity.
      --- simpl. Search andb. apply Bool.andb_false_intro2. simpl. Admitted.

Theorem apply_delete_up_different: forall (u_p : unification_problem) (tp: term_pair),
  ~(check_delete_and_deliver u_p = TError) /\ ~(u_p = Ubottom) 
  /\ (check_delete_and_deliver u_p = TP tp) ->
  maybe_unification_problem_eq (UP u_p) (UP (solver_delete tp u_p)) = false.
Proof.
  intros. destruct H. destruct H0. induction u_p.
  - contradiction.
  - simpl in H1. simpl in H1. simpl. Admitted.

Theorem neq_mup_implies_neq_up: forall (u_p u_p' : unification_problem),
  (UP u_p <> UP u_p')->
  (u_p <> u_p').
Proof.
  intros. unfold not. intros. unfold not in H. apply H. rewrite H0. reflexivity.
Qed.

Theorem progress : forall (m_u_p: maybe_unification_problem),
  ~(m_u_p = UError) /\
  ~(m_u_p = UP Ubottom) /\ ~(unification_problem_in_solved_form (mup_to_up m_u_p) = true) ->
  (exists (m_u_p' : maybe_unification_problem), (maybe_apply_one_step m_u_p = m_u_p') /\ (maybe_unification_problem_eq m_u_p m_u_p' = false)).
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
          2 : { apply (apply_conflict_up_different (Uset l) mtp). split.
            - rewrite tp_eq_conflict. unfold not. intros. discriminate.
            - apply neq_mup_implies_neq_up. apply H0. }
          ----- destruct (check_occurs_check_and_deliver (Uset l)) as [ | mtp] eqn: tp_eq_occurs_check.
            2 : { apply (apply_occurs_check_up_different (Uset l) mtp). split.
              - rewrite tp_eq_occurs_check. unfold not. intros. discriminate.
              - apply neq_mup_implies_neq_up. apply H0. }
            ------ destruct (check_delete_and_deliver (Uset l)) as [ | mtp] eqn: tp_eq_delete.
              2 : { apply (apply_delete_up_different (Uset l) mtp). split.
                - rewrite tp_eq_delete. unfold not. intros. discriminate.
                - split.
                  -- apply neq_mup_implies_neq_up. apply H0.
                  -- apply tp_eq_delete. Admitted.