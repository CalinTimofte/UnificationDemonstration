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
  ((is_bottom u_p) = true) \/ ((unification_problem_in_solved_form u_p) = true) \/ (exists (u_p': unification_problem), solver u_p -> solver u_p')->
  solver u_p.
Proof.
  intros. destruct H.
  - apply is_solved_in_one_step. left. apply H.
  - destruct H.
    -- apply is_solved_in_one_step. right. apply H.
    -- inversion H. apply H.
Qed.
  
Theorem test1 : solver unif_probl1.
  Proof. unfold unif_probl1. apply (Sdelete unif_probl1 (Uset [decomposition_term_pair; orientation_term_pair])).
  - simpl. reflexivity.
  - simpl. reflexivity.
  - apply (Sdecompose (Uset [decomposition_term_pair; orientation_term_pair]) (Uset [orientation_term_pair; Tpair (Tvar x) (Tvar a); Tpair (Tvar y) (Tvar b)])).
    -- simpl. reflexivity.
    -- exists decomposition_term_pair. simpl. reflexivity.
    -- apply (Sorientation (Uset [orientation_term_pair; Tpair (Tvar x) (Tvar a); Tpair (Tvar y) (Tvar b)]) (Uset [Tpair (Tvar a) t2; Tpair (Tvar x) (Tvar a); Tpair (Tvar y) (Tvar b)]) orientation_term_pair).
     --- simpl. reflexivity.
     --- simpl. reflexivity. 
     --- apply Ssolved. 
      ---- simpl. reflexivity.
Qed.