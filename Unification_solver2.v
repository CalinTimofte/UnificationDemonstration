From Licenta Require Import Semantics.
From Licenta Require Import Syntax.

Require Import String.
Open Scope string_scope.

Require Import List.
Import ListNotations.

Definition unification_problem_is_bottom (u : unification_problem) : bool :=
  true.

Inductive maybe_unification_problem : Type :=
  | UError
  | UP (u_p :unification_problem).

(*Definition maybe_unification_problem_to_unification_problem (m_u_p : maybe_unification_problem) : unification_problem :=
  match m_u_p with
  | UError => Ubottom
  | UP u_p => u_p
  end.

Coercion maybe_unification_problem_to_unification_problem : maybe_unification_problem >-> unification_problem.*)

Inductive unif_solver_rule (tp : term_pair) (u_p : unification_problem) : Type:=
  | Rdelete
  | Rdecompose
  | Rorientation
  | Relimination
  | Rconflict
  | Roccurs_check .

Definition solver_delete (tp : term_pair) (up : unification_problem) : unification_problem :=
  remove_first_appearance_term_unification_problem up term_eq.

Definition term_pair_correct_for_rule (tp : term_pair) (rule : term -> term -> bool) : bool :=
  match tp with
  | Tpair t1 t2 => rule t1 t2
  end.

Definition rule_test (tp : term_pair) (u_p : unification_problem) (criterion : term -> term -> bool) : bool :=
  andb (term_pair_correct_for_rule tp criterion) (term_in_unification_problem u_p criterion).

Definition delete_test (tp : term_pair) (u_p : unification_problem) : bool :=
  andb (term_pair_correct_for_rule tp term_eq) (term_in_unification_problem u_p term_eq).

Definition decompose_test (tp : term_pair) (u_p : unification_problem) :=
  rule_test tp u_p is_decomposition_term_pair.

Definition orientation_test (tp : term_pair) (u_p : unification_problem) :=
  rule_test tp u_p is_orientation_term_pair.

Definition elimination_test (tp : term_pair) (u_p : unification_problem) :=
  rule_test tp u_p is_elimination_term_pair.

Definition conflict_test (tp : term_pair) (u_p : unification_problem) :=
  rule_test tp u_p is_conflict_term_pair.

Definition occurs_check_test (tp : term_pair) (u_p : unification_problem) :=
  rule_test tp u_p is_occurs_check_term_pair.

Inductive maybe_term_pair : Type :=
  | TError
  | TP (tp : term_pair).

Fixpoint deliver_tpair_from_list (tpl : list term_pair) (criterion : term -> term -> bool) : maybe_term_pair :=
  match tpl with
  | [] => TError
  | h::tl => match (term_pair_correct_for_rule h criterion) with
             | true => TP h
             | false => deliver_tpair_from_list tl criterion
             end
  end.

Definition deliver_tpair_from_unification_problem (u_p : unification_problem) (criterion : term -> term -> bool) : maybe_term_pair :=
  match u_p with
  | Ubottom => TError
  | Uset l => deliver_tpair_from_list l criterion
  end.

Definition delete_term_pair := Tpair t1 t1.

Definition check_delete_and_deliver (u_p : unification_problem) :=
  deliver_tpair_from_unification_problem u_p term_eq.

Definition check_decomposition_and_deliver (u_p : unification_problem) :=
  deliver_tpair_from_unification_problem u_p is_decomposition_term_pair.

Definition check_orientation_and_deliver (u_p : unification_problem) :=
  deliver_tpair_from_unification_problem u_p is_orientation_term_pair.

Definition check_elimination_and_deliver (u_p : unification_problem) :=
  deliver_tpair_from_unification_problem u_p is_elimination_term_pair.

Definition check_conflict_and_deliver (u_p : unification_problem) :=
  deliver_tpair_from_unification_problem u_p is_conflict_term_pair.

Definition check_occurs_check_and_deliver (u_p : unification_problem) :=
  deliver_tpair_from_unification_problem u_p is_occurs_check_term_pair.

Compute (check_delete_and_deliver unif_probl1).

Definition unif_probl1' := Uset [decomposition_term_pair; orientation_term_pair].
Compute (check_decomposition_and_deliver unif_probl1').

Definition unif_probl1'' := Uset [orientation_term_pair].
Compute (check_decomposition_and_deliver unif_probl1'').

Compute (check_orientation_and_deliver unif_probl1).

Compute (check_elimination_and_deliver elimination_example).

Compute (check_conflict_and_deliver unif_probl2).

Compute (check_occurs_check_and_deliver (Uset [occurs_check_term_pair])).

Definition apply_one_step (u_p : unification_problem) : maybe_unification_problem :=
  match u_p with
  | Ubottom => UP Ubottom
  | _ => match (check_delete_and_deliver u_p) with
         | TP tp => UP (solver_delete tp u_p)
         | TError => match (check_decomposition_and_deliver u_p) with
                     | TP tp => UP (remove_and_replace_decomposition_unif_problem tp u_p)
                     | TError => match (check_elimination_and_deliver u_p) with
                                 | TP tp => UP (elimination tp u_p) 
                                 | TError => match (check_orientation_and_deliver u_p) with
                                             | TP tp => UP (apply_orientation tp u_p)
                                             | TError => match (check_conflict_and_deliver u_p) with
                                                         | TP tp => UP (remove_conflict_term_pair tp u_p)
                                                         | TError => match (check_occurs_check_and_deliver u_p) with
                                                                     | TP tp => UP (occurs_check tp u_p)
                                                                     | TError => UP u_p
                                                                     end
                                                          end
                                             end
                                  end
                     end
         end
  end.

Definition maybe_apply_one_step (m_u_p : maybe_unification_problem) : maybe_unification_problem :=
  match m_u_p with
  | UError => UError
  | UP up => apply_one_step up
  end.

Definition maybe_unification_problem_in_solved_form (m_u_p : maybe_unification_problem) : bool :=
  match m_u_p with
  | UError => false
  | UP up => unification_problem_in_solved_form up
  end.

Compute apply_one_step unif_probl1.
Print unif_probl1.
Compute maybe_apply_one_step (apply_one_step unif_probl1).
Compute maybe_apply_one_step (maybe_apply_one_step (apply_one_step unif_probl1)).
Compute maybe_apply_one_step (maybe_apply_one_step (maybe_apply_one_step (apply_one_step unif_probl1))).
Compute maybe_unification_problem_in_solved_form (maybe_apply_one_step (maybe_apply_one_step (apply_one_step unif_probl1))).

Print elimination_example.
Compute apply_one_step elimination_example.
Compute maybe_apply_one_step (apply_one_step elimination_example).
Compute maybe_apply_one_step (maybe_apply_one_step (apply_one_step elimination_example)).
Compute maybe_apply_one_step (maybe_apply_one_step (maybe_apply_one_step (apply_one_step elimination_example))).
Compute maybe_apply_one_step (maybe_apply_one_step (maybe_apply_one_step (maybe_apply_one_step (apply_one_step elimination_example)))).

Definition apply_rule (tp : term_pair) (u_p : unification_problem) (rule : unif_solver_rule tp u_p) : maybe_unification_problem :=
  match rule with
  | Rdelete _ _ => match (delete_test tp u_p) with
                   | true => UP (solver_delete tp u_p)
                   | false => UError
                   end
  | Rdecompose  _ _ => match (decompose_test tp u_p) with
                       | true => UP (remove_and_replace_decomposition_unif_problem tp u_p)
                       | false => UError
                       end
  | Rorientation  _ _ => match (orientation_test tp u_p) with
                         | true => UP (apply_orientation tp u_p)
                         | false => UError
                         end
  | Relimination  _ _ => match (elimination_test tp u_p) with
                         | true => UP (elimination tp u_p)
                         | false => UError
                         end
  | Rconflict   _ _ => match (conflict_test tp u_p) with
                       | true => UP (remove_conflict_term_pair tp u_p)
                       | false => UError
                       end
  | Roccurs_check   _ _ => match (occurs_check_test tp u_p) with
                           | true => UP (occurs_check tp u_p)
                           | false => UError
                           end
  end.

Inductive solver : maybe_unification_problem -> Prop :=
  | Serror : solver UError
  | Sbottom : solver (UP Ubottom)
  | Ssolved (u_p : unification_problem) (H : (unification_problem_in_solved_form u_p) = true) : solver (UP u_p)
  | Sapply (u_p u_p': unification_problem) (tp : term_pair) (rule : unif_solver_rule tp u_p) (H: (solver (UP u_p')) /\ (apply_rule tp u_p rule = (UP u_p'))) : solver (UP u_p).

Definition is_bottom (u : unification_problem) : bool :=
  match u with
  | Ubottom => true
  | _ => false
  end.

Theorem is_solved_in_one_step : forall (u_p : unification_problem),
  ((is_bottom u_p) = true) \/ ((unification_problem_in_solved_form u_p) = true) ->
  solver (UP u_p).
Proof.
  intros. destruct H.
  - destruct u_p.
    -- simpl in H. discriminate.
    -- apply Sbottom.
  - apply Ssolved. apply H.
Qed. 

Theorem test5: solver ( UP Ubottom ).
Proof.
  apply is_solved_in_one_step. left. simpl. reflexivity.
Qed.

Fixpoint term_pair_list_eq (tpl1 tpl2 : list term_pair) : bool :=
  match tpl1 with
  | [] => match tpl2 with 
          | [] => true
          | _ => false
          end
  | h1::tl1 => match tpl2 with
               | [] => false
               | h2::tl2 => andb (term_pair_eq h1 h2) (term_pair_list_eq tl1 tl2)
               end
  end.

Definition unification_problem_eq (up1 up2: unification_problem) : bool :=
  match up1 with
  | Ubottom => match up2 with
              | Ubottom => true
              | _ => false
              end
  | Uset l1 => match up2 with
               | Ubottom => false
               | Uset l2 => term_pair_list_eq l1 l2
               end
  end.

Compute (unification_problem_eq
        (Uset [orientation_term_pair; Tpair (Tvar x) (Tvar a); Tpair (Tvar y) (Tvar b)])
        (Uset [orientation_term_pair; Tpair (Tvar x) (Tvar a); Tpair (Tvar y) (Tvar b)])
      ).

Theorem progress : forall (u_p : unification_problem),
  (((is_bottom u_p) = true) \/ ((unification_problem_in_solved_form u_p) = true) \/ 
  (exists (u_p': unification_problem), (solver (UP u_p')) /\ (exists (tp : term_pair) (rule : unif_solver_rule tp u_p), apply_rule tp u_p rule = (UP u_p')))) ->
  solver (UP u_p).
Proof.
  intros. destruct H.
  - apply is_solved_in_one_step. left. apply H.
  - destruct H.
    -- apply is_solved_in_one_step. right. apply H.
    -- destruct H. destruct H. destruct H0. destruct H0. apply (Sapply u_p x x0 x1). split.
      --- apply H.
      --- apply H0.
Qed.

Theorem progress' : forall (u_p : unification_problem),
  solver (UP u_p) ->
  ~((is_bottom u_p) = true) -> ~((unification_problem_in_solved_form u_p) = true) ->
  (exists (u_p': unification_problem), (solver (UP u_p'))
   /\ (exists (tp : term_pair) (rule : unif_solver_rule tp u_p), apply_rule tp u_p rule = (UP u_p'))).
Proof.
  intros. inversion H.
  - unfold not in H0. rewrite <- H3 in H0. simpl in H0. exfalso. apply H0. reflexivity.
  - unfold not in H1. exfalso. apply H1. apply H3.
  - exists u_p'. destruct H3. split.
    -- apply H3.
    -- exists tp. exists rule. apply H4.
Qed.

Theorem test3 : solver (UP (Uset [occurs_check_term_pair])).
Proof.
  apply (Sapply (Uset [occurs_check_term_pair]) Ubottom occurs_check_term_pair (Roccurs_check occurs_check_term_pair (Uset [occurs_check_term_pair]))). split.
  - apply Sbottom.
  - simpl. reflexivity.
Qed.

Theorem test1 : solver (UP unif_probl1).
  Proof. unfold unif_probl1. apply (Sapply unif_probl1 
                                           (Uset [decomposition_term_pair; orientation_term_pair]) 
                                           (Tpair t1 t1) 
                                           (Rdelete (Tpair t1 t1) unif_probl1)). split.
  - apply (Sapply (Uset [decomposition_term_pair; orientation_term_pair])
                  (Uset [orientation_term_pair; Tpair (Tvar x) (Tvar a); Tpair (Tvar y) (Tvar b)])
                  decomposition_term_pair
                  (Rdecompose decomposition_term_pair (Uset [decomposition_term_pair; orientation_term_pair]))). split.
    -- apply (Sapply (Uset [orientation_term_pair; Tpair (Tvar x) (Tvar a); Tpair (Tvar y) (Tvar b)])
                     (Uset [Tpair (Tvar a) t2; Tpair (Tvar x) (Tvar a); Tpair (Tvar y) (Tvar b)])
                     orientation_term_pair
                     (Rorientation orientation_term_pair (Uset [orientation_term_pair; Tpair (Tvar x) (Tvar a); Tpair (Tvar y) (Tvar b)]))). split.
       --- apply Ssolved. simpl. reflexivity.
       --- simpl. reflexivity.
    -- simpl. reflexivity.
  - simpl. reflexivity.
Qed.