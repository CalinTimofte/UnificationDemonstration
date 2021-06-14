From Licenta Require Import Semantics.
From Licenta Require Import Syntax.

Require Import String.
Open Scope string_scope.

Require Import List.
Import ListNotations.

Inductive solver : unification_problem -> Prop :=
  | Sbottom : solver Ubottom
  | Ssolved (u_p : unification_problem) (H : (unification_problem_in_solved_form u_p) = true) : solver u_p
  | Sdelete (u_p u_p' : unification_problem)(H : ((term_in_unification_problem u_p term_eq) = true)) (H' : (remove_first_appearance_term_unification_problem u_p term_eq) = u_p')(H'' : solver u_p'): solver u_p
  | Sdecompose (u_p u_p' : unification_problem)(tp : term_pair)(H : ((term_in_unification_problem u_p is_decomposition_term_pair) = true)) (H' : (remove_and_replace_decomposition_unif_problem tp u_p) = u_p')(H'' : solver u_p'): solver u_p
  | Sorientation (u_p u_p' : unification_problem) (tp : term_pair) (H : ((term_in_unification_problem u_p is_orientation_term_pair) = true)) (H' : (apply_orientation tp u_p) = u_p') (H'' : solver u_p'): solver u_p
  | Selimination (u_p u_p' : unification_problem) (tp : term_pair) (H : ((term_in_unification_problem u_p is_elimination_term_pair) = true)) (H' : (elimination tp u_p) = u_p') (H'' : solver u_p'): solver u_p
  | Sconflict (u_p u_p' : unification_problem) (tp : term_pair) (H : ((term_in_unification_problem u_p is_conflict_term_pair) = true)) (H' : (remove_conflict_term_pair tp u_p) = u_p') (H'' : solver u_p'): solver u_p
  | Soccurs_check (u_p u_p' : unification_problem) (tp : term_pair) (H : ((term_in_unification_problem u_p is_occurs_check_term_pair) = true)) (H' : (occurs_check tp u_p) = u_p') (H'' : solver u_p'): solver u_p.

Definition is_bottom (u : unification_problem) : bool :=
  match u with
  | Ubottom => true
  | _ => false
  end.

Compute (Sdecompose 
          (Uset [Tpair (Tfunc (Func "f") [Tvar x; Tvar y]) (Tfunc (Func "f") [Tvar a; Tvar b])])
          (Uset [Tpair (Tvar x) (Tvar a); Tpair (Tvar y) (Tvar b)])
          decomposition_term_pair).

Compute (Ssolved (Uset [Tpair (Tvar x) (Tvar a); Tpair (Tvar y) (Tvar b)])).

Theorem is_solved : forall (u_p : unification_problem),
  ((is_bottom u_p) = true) \/ ((unification_problem_in_solved_form u_p) = true) ->
  solver u_p.
Proof.
  intros. destruct H.
  - destruct u_p.
    -- simpl in H. discriminate.
    -- apply Sbottom.
  - apply Ssolved. apply H.
Qed. 


Theorem test1 : solver unif_probl1.
  Proof. unfold unif_probl1. apply (Sdelete unif_probl1 (Uset [decomposition_term_pair; orientation_term_pair])).
  - simpl. reflexivity.
  - simpl. reflexivity.
  - apply (Sdecompose (Uset [decomposition_term_pair; orientation_term_pair]) (Uset [orientation_term_pair; Tpair (Tvar x) (Tvar a); Tpair (Tvar y) (Tvar b)]) decomposition_term_pair).
    -- simpl. reflexivity.
    -- simpl. reflexivity.
    -- apply (Sorientation (Uset [orientation_term_pair; Tpair (Tvar x) (Tvar a); Tpair (Tvar y) (Tvar b)]) (Uset [Tpair (Tvar a) t2; Tpair (Tvar x) (Tvar a); Tpair (Tvar y) (Tvar b)]) orientation_term_pair).
     --- simpl. reflexivity.
     --- simpl. reflexivity. 
     --- apply Ssolved. 
      ---- simpl. reflexivity.
Qed.

Theorem test2 : solver unif_probl2.
  Proof. unfold unif_probl2. unfold conflict_term.
  apply (Sconflict unif_probl2 Ubottom conflict_term).
  - simpl. reflexivity.
  - simpl. reflexivity.
  - apply Sbottom.
Qed.

Theorem test3 : solver (Uset [occurs_check_term_pair]).
Proof.
  apply (Soccurs_check (Uset [occurs_check_term_pair]) Ubottom occurs_check_term_pair).
  - simpl. reflexivity.
  - simpl. reflexivity.
  - apply Sbottom.
Qed.

Theorem test4 : solver unif_probl4.
Proof.
  apply (Sdecompose unif_probl4 unif_probl4' (Tpair (Tfunc f [Tvar x2; Tvar x2]) (Tfunc f [Tvar a; Tvar x1]))).
  - simpl. reflexivity.
  - simpl. reflexivity.
  - apply (Selimination unif_probl4' unif_probl4'' (Tpair (Tvar x2) (Tvar a))).
    -- simpl. reflexivity.
    -- simpl. reflexivity.
    -- apply (Sorientation unif_probl4'' unif_probl4''' (Tpair (Tvar a) (Tvar x1))).
      --- simpl. reflexivity.
      --- simpl. reflexivity.
      --- apply (Selimination unif_probl4''' unif_probl4'''' (Tpair (Tvar x1) (Tvar a))).
        ---- simpl. reflexivity.
        ---- simpl. reflexivity.
        ---- apply (Sorientation unif_probl4'''' unif_probl4''''' (Tpair (Tfunc f [Tfunc g [Tvar a; Tvar a]; Tvar a])(Tvar x3))).
          ----- simpl. reflexivity.
          ----- simpl. reflexivity.
          ----- apply Ssolved. simpl. reflexivity.
Qed.

Compute (Sdelete unif_probl1 (Uset [decomposition_term_pair; orientation_term_pair])).
