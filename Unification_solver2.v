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


Inductive solver : unification_problem -> Prop :=
  | Sbottom : solver Ubottom
  | Ssolved (u_p : unification_problem) (H : (unification_problem_in_solved_form u_p) = true) : solver u_p
  | Sdelete (u_p u_p' : unification_problem)(H : ((term_in_unification_problem u_p term_eq) = true)) (H' : (remove_first_appearance_term_unification_problem u_p term_eq) = u_p')(H'' : solver u_p'): solver u_p
  | Sdecompose (u_p u_p' : unification_problem)(H : ((term_in_unification_problem u_p is_decomposition_term_pair) = true)) (H': exists (tp : term_pair), (remove_and_replace_decomposition_unif_problem tp u_p) = u_p')(H'' : solver u_p'): solver u_p
  | Sorientation (u_p u_p' : unification_problem) (H : ((term_in_unification_problem u_p is_orientation_term_pair) = true)) (H' : exists (tp : term_pair), (apply_orientation tp u_p) = u_p') (H'' : solver u_p'): solver u_p
  | Selimination (u_p u_p' : unification_problem) (H : ((term_in_unification_problem u_p is_elimination_term_pair) = true)) (H' : exists (tp : term_pair), (elimination tp u_p) = u_p') (H'' : solver u_p'): solver u_p
  | Sconflict (u_p u_p' : unification_problem) (H : ((term_in_unification_problem u_p is_conflict_term_pair) = true)) (H' : exists (tp : term_pair), (remove_conflict_term_pair tp u_p) = u_p') (H'' : solver u_p'): solver u_p
  | Soccurs_check (u_p u_p' : unification_problem) (H : ((term_in_unification_problem u_p is_occurs_check_term_pair) = true)) (H' : exists (tp : term_pair), (occurs_check tp u_p) = u_p') (H'' : solver u_p'): solver u_p.
*)

Inductive unif_solver_rule (tp : term_pair) (u_p : unification_problem) : Type:=
  | Rdelete
  | Rdecompose
  | Rorientation
  | Relimination
  | Rconflict
  | Roccurs_check.

Definition solver_delete (tp : term_pair) (up : unification_problem) : unification_problem :=
  remove_first_appearance_term_unification_problem up term_eq.

Definition apply_rule (tp : term_pair) (u_p : unification_problem) (rule : unif_solver_rule tp u_p) : unification_problem :=
  match rule with
  | Rdelete _ _ => solver_delete tp u_p
  | Rdecompose  _ _ => remove_and_replace_decomposition_unif_problem tp u_p
  | Rorientation  _ _ => apply_orientation tp u_p
  | Relimination  _ _ => elimination tp u_p
  | Rconflict   _ _ => remove_conflict_term_pair tp u_p
  | Roccurs_check   _ _ => occurs_check tp u_p
  end.

Inductive solver : unification_problem -> Prop :=
  | Sbottom : solver Ubottom
  | Ssolved (u_p : unification_problem) (H : (unification_problem_in_solved_form u_p) = true) : solver u_p
  | Sapply (u_p u_p': unification_problem) (tp : term_pair) (rule : unif_solver_rule tp u_p) (H: (solver u_p') /\ (apply_rule tp u_p rule = u_p')) : solver u_p.


Theorem test3 : solver (Uset [occurs_check_term_pair]).
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
  solver u_p.
Proof.
  intros. destruct H.
  - destruct u_p.
    -- simpl in H. discriminate.
    -- apply Sbottom.
  - apply Ssolved. apply H.
Qed. 

Theorem test5: solver Ubottom.
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
  (exists (u_p': unification_problem), (solver u_p') /\ (exists (tp : term_pair) (rule : unif_solver_rule tp u_p), apply_rule tp u_p rule = u_p'))) ->
  solver u_p.
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