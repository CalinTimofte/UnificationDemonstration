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

Definition apply_rule (tp : term_pair) (u_p : unification_problem) (rule : unif_solver_rule tp u_p) : maybe_unification_problem :=
  match rule with
  | Rdelete _ _ => match (term_in_unification_problem u_p term_eq) with
                   | true => UP (solver_delete tp u_p)
                   | false => UError
                   end
  | Rdecompose  _ _ => match (term_in_unification_problem u_p is_decomposition_term_pair) with
                       | true => UP (remove_and_replace_decomposition_unif_problem tp u_p)
                       | false => UError
                       end
  | Rorientation  _ _ => match (term_in_unification_problem u_p is_orientation_term_pair) with
                         | true => UP (apply_orientation tp u_p)
                         | false => UError
                         end
  | Relimination  _ _ => match (term_in_unification_problem u_p is_elimination_term_pair) with
                         | true => UP (elimination tp u_p)
                         | false => UError
                         end
  | Rconflict   _ _ => match (term_in_unification_problem u_p is_conflict_term_pair) with
                       | true => UP (remove_conflict_term_pair tp u_p)
                       | false => UError
                       end
  | Roccurs_check   _ _ => match (term_in_unification_problem u_p is_occurs_check_term_pair) with
                           | true => UP (occurs_check tp u_p)
                           | false => UError
                           end
  end.

Inductive solver : maybe_unification_problem -> Prop :=
  | SError : solver UError
  | Sbottom : solver (UP Ubottom)
  | Ssolved (u_p : unification_problem) (H : (unification_problem_in_solved_form u_p) = true) : solver (UP u_p)
  | Sapply (u_p u_p': unification_problem) (tp : term_pair) (rule : unif_solver_rule tp u_p) (H: (solver (UP u_p')) /\ (apply_rule tp u_p rule = (UP u_p'))) : solver (UP u_p).


Theorem test3 : solver (UP (Uset [occurs_check_term_pair])).
Proof.
  apply (Sapply (Uset [occurs_check_term_pair]) Ubottom occurs_check_term_pair (Roccurs_check occurs_check_term_pair (Uset [occurs_check_term_pair]))). split.
  - apply Sbottom.
  - simpl. reflexivity.
Qed.


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




Theorem test1 : solver unif_probl1.
  Proof. unfold unif_probl1. apply (Sapply unif_probl1 solver_delete). exists (Uset [decomposition_term_pair; orientation_term_pair]). split.
  - apply (Sapply (Uset [decomposition_term_pair; orientation_term_pair]) remove_and_replace_decomposition_unif_problem).
    exists (Uset [orientation_term_pair; Tpair (Tvar x) (Tvar a); Tpair (Tvar y) (Tvar b)]). split.
    -- apply (Sapply (Uset [orientation_term_pair; Tpair (Tvar x) (Tvar a); Tpair (Tvar y) (Tvar b)]) apply_orientation). 
       exists (Uset [Tpair (Tvar a) t2; Tpair (Tvar x) (Tvar a); Tpair (Tvar y) (Tvar b)]). split.
       --- apply Ssolved. simpl. reflexivity.
       --- exists orientation_term_pair. simpl. reflexivity.
    -- exists decomposition_term_pair. simpl. reflexivity.
    (* Delete does not need a term pair *)
  - exists decomposition_term_pair. simpl. reflexivity.
Qed.