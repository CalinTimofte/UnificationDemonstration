From Licenta Require Import Syntax.

Require Import String.
Open Scope string_scope.

Require Import List.
Import ListNotations.

Definition arity_term (t : term) : nat :=
  match t with
  | Tconst _ => 0
  | Tvar _=> 0
  | Tfunc f l => length l
  end.

Compute (arity_term(Tfunc (Func "f") [Tvar a;Tvar b])).

(* Support functions for removing duplicates in a var list *)

Definition var_get_name (v : var) : string := 
  match v with
  | Named_var s => s
  end.

Fixpoint disassemble_var_list (l : list var) : list string :=
  match l with
  | [] => []
  | h::t => [var_get_name h] ++ disassemble_var_list t
  end.

Fixpoint assemble_var_list (l : list string) : list var :=
  match l with
  | [] => []
  | h::t => [Named_var h] ++ assemble_var_list t
  end.

Compute (disassemble_var_list [Named_var "a"; Named_var "b"; Named_var "b"]).
Compute (assemble_var_list ["a"; "b"; "b"]).

(* --------------------------------------------- *)

Definition remove_duplicates_var_list (l : list var) : list var :=
  assemble_var_list (nodup string_dec (disassemble_var_list l)).

Compute (remove_duplicates_var_list [Named_var "a"; Named_var "b"; Named_var "b"]).

Fixpoint vars_term' (t : term) : list var :=
  match t with
  | Tconst c => []
  | Tvar v => [v]
  | Tfunc f l => flat_map vars_term' l
  end.

Definition vars_term (t : term) : list var :=
  remove_duplicates_var_list (vars_term' t).

Compute (vars_term (Tfunc (Func "f") [(Tvar a); (Tfunc (Func "g") [Tvar b; Tvar b])])).

Compute (vars_term (Tfunc (Func "f") [(Tvar a); (Tvar a)])).

Definition remove_element_var_list (v : var) (l : list var) : list var :=
  assemble_var_list (remove string_dec (var_get_name v)(disassemble_var_list l)).

Compute (remove_element_var_list x [x; y; z]).

Definition var_eq (v1 v2 : var) : bool :=
  var_get_name v1 =? var_get_name v2.

Compute (var_eq x x).
Compute (var_eq x y).

(* var_assignment needs fuel to determine if recursion is correct *)

Fixpoint var_assignment' (v : var) (a : assignment) (fuel: nat): term :=
  match fuel with
  | O => Tvar v
  | S fuel' => match a with
              | Apairs l => match l with
                            | [] => Tvar v
                            | h::tl => match h with
                                      | Apair v0 t => match (var_eq v0 v) with
                                                      | true => t
                                                      | false => var_assignment' v (Apairs tl) fuel'
                                                      end
                                      end
                             end
               end
  end.

Definition var_assignment (a : assignment) (v: var): term :=
  match a with
  | Apairs l => var_assignment' v a (length l)
  end.

Compute (var_assignment (Apairs [Apair y (Tvar x); Apair x (Tvar y)]) x).


Fixpoint term_assignment (a : assignment) (t : term) : term :=
  match t with
  | Tconst c => Tconst c
  | Tvar v => var_assignment a v
  | Tfunc f l=> Tfunc f (map (term_assignment a) l)
  end.

Compute (term_assignment sigma1 t2).
Compute (term_assignment sigma1 t1).

Definition append_assignment_to_list (l : list assignment_pair) (ap : assignment_pair) : list assignment_pair :=
  l ++ [ap].

Definition append_assignment (a : assignment) (ap : assignment_pair) : assignment :=
  match a with
  | Apairs l => Apairs (append_assignment_to_list l ap)
  end.

Compute (append_assignment sigma1 (Apair z (Tvar y))).

Fixpoint change_assignment_list (l : list assignment_pair) (ap : assignment_pair) : list assignment_pair :=
  match l with
  | [] => append_assignment_to_list l ap
  | hd::tl => match hd with
              | Apair v1 t1 => match ap with
                               | Apair v2 t2 => match (var_eq v1 v2) with
                                                | true => [(Apair v1 t2)] ++ tl
                                                | false => [hd] ++  (change_assignment_list tl ap)
                                                end
                              end
              end
  end.

Definition change_assignment (a : assignment) (ap : assignment_pair) : assignment :=
  match a with
  | Apairs l => Apairs (change_assignment_list l ap)
  end.

Compute (change_assignment sigma1 (Apair x (Tvar z))).



Fixpoint term_in_unification_problem' (u : unification_problem) (criterion : term -> term -> bool) (gas : nat): bool :=
  match gas with
  | O => false
  | S n' =>
    match u with
    | Ubottom => false
    | Uset l => match l with
                | [] => false
                | h::tl => match h with
                           | Tpair t1 t2 => match (criterion t1 t2) with
                                            | true => true
                                            | false => term_in_unification_problem' (Uset tl) criterion n'
                                            end
                            end
                end
    end
  end.

Definition term_in_unification_problem (u : unification_problem) (criterion : term -> term -> bool) : bool :=
  match u with
  | Ubottom => false
  | Uset l => term_in_unification_problem' u criterion (length l)
  end.

Fixpoint remove_first_appearance_term_pair_list (l : list term_pair) (criterion : term -> term -> bool) : list term_pair :=
  match l with
  | [] => []
  | h::tl => match h with
             | Tpair t1 t2 => match (criterion t1 t2) with
                              | true => tl
                              | false => h :: (remove_first_appearance_term_pair_list tl criterion)
                              end
             end
  end.

Definition remove_first_appearance_term_unification_problem (u : unification_problem) (criterion : term -> term -> bool) : unification_problem :=
  match u with
  | Ubottom => Ubottom
  | Uset l => Uset (remove_first_appearance_term_pair_list l criterion)
  end.

Fixpoint all_terms_have_property_unification_problem' (u : unification_problem) (criterion : term -> term -> bool) (gas : nat): bool :=
  match gas with
  | O => false
  | S n' =>  
          match u with
          | Ubottom => false
          | Uset l => match l with
                      | [] => true
                      | h::tl => match h with
                                 | Tpair t1 t2 => match (criterion t1 t2) with
                                                  | false => false
                                                  | true => all_terms_have_property_unification_problem' (Uset tl) criterion n'
                                                  end
                                  end
                      end
          end
  end.

Definition all_terms_have_property_unification_problem (u : unification_problem) (criterion : term -> term -> bool) : bool :=
  match u with
  | Ubottom => false
  | Uset l => all_terms_have_property_unification_problem' u criterion ((length l) + 1)
  end.

Fixpoint andb_list (l : list bool) : bool :=
  match l with
  | [] => true
  | h::tl => andb h (andb_list tl)
  end.

Fixpoint term_eq' (t1 t2 : term) (gas : nat): bool :=
  match gas with
  | O => false
  | S n' => 
            match t1 with
            | Tconst c1 => match c1 with
                          | Func f1 => match t2 with
                                      | Tconst c2 => match c2 with
                                                     | Func f2 => f1 =? f2
                                                     end
                                      | _ => false
                                      end
                          end
            | Tvar v1 => match t2 with
                         | Tvar v2 => var_eq v1 v2
                         | _ => false
                         end
            | Tfunc f1 l1 => match t2 with
                            | Tfunc f2 l2 => match f1 with
                                             | Func fs1 => match f2 with
                                                           | Func fs2 => match l1 with
                                                                         | [] => match l2 with
                                                                                 | [] => true
                                                                                 | _ => false
                                                                                 end
                                                                         | hd1::tl1 => match l2 with
                                                                                    | [] => false
                                                                                    | hd2::tl2 => andb (andb (fs1 =? fs2) (term_eq' hd1 hd2 n')) (term_eq' (Tfunc (Func fs1) tl1) (Tfunc (Func fs2) tl2) n')
                                                                                    end
                                                                          end
                                                            end
                                              end
                            | _ => false
                            end
            end
    end.

Definition term_eq (t1 t2 : term) : bool :=
  match t1 with
  | Tconst c => term_eq' t1 t2 100
  | Tvar v => term_eq' t1 t2 100
  | Tfunc f l => term_eq' t1 t2 ((length l) + 100)
  end.

Compute (term_eq t1 t1).

Compute (term_in_unification_problem (Uset [Tpair t1 t2; Tpair t1 t1; Tpair t2 t2]) term_eq).
Compute (remove_first_appearance_term_unification_problem (remove_first_appearance_term_unification_problem (Uset [Tpair t1 t2; Tpair t1 t1; Tpair t2 t2]) term_eq) term_eq).

Check ((term_in_unification_problem (Uset [Tpair t1 t2; Tpair t1 t1; Tpair t2 t2]) term_eq) = true).

Fixpoint var_in_list_var (v : var) (l : list var) : bool :=
  match l with
  | [] => false
  | h::tl => match (var_eq h v) with
             | true => true
             | false => var_in_list_var v tl
             end
  end.

Compute (var_in_list_var x [y; y; x; y; x]).

Definition var_in_term (v : var) (t : term) : bool :=
  var_in_list_var v (vars_term t).

Compute (var_in_term x (Tfunc (Func "f") [Tvar y; Tvar x; Tvar y])).

Definition term_pair_first_var (t1 t2 : term) : bool :=
  match t1 with
           | Tconst _ => false
           | Tvar _ => true
           | Tfunc _ _ => false
           end.


Compute (term_pair_first_var  (Tvar x) (Tvar x)).
Compute (term_pair_first_var (Tconst (Func "f")) (Tvar x)).
Compute (term_pair_first_var (Tfunc (Func "f") []) (Tvar x)).

Definition term_pair_solved_form (t1 t2 : term) : bool :=
  match (term_pair_first_var t1 t2) with
  | false => false
  | true => match (vars_term t1) with
            | [] => false
            | h::tl => match (var_in_term h t2) with
                       | true => false
                       | false => true
                       end
            end
  end.

Compute (term_pair_solved_form (Tvar x) (Tfunc (Func "f") [Tvar y; Tvar z])).

Compute (all_terms_have_property_unification_problem (Uset [Tpair t1 t2; Tpair t1 t1; Tpair t2 t2]) term_pair_solved_form).
Compute (all_terms_have_property_unification_problem (Uset [Tpair (Tvar a) t2; Tpair (Tvar a) t1]) term_pair_solved_form).

Fixpoint times_term_appears_on_left_side_unification_problem' (t : term) (up : unification_problem) (gas : nat): nat :=
  match gas with
  | O => 0
  | S n' =>
        match up with
        | Ubottom => 0
        | Uset l => match l with
                    | [] => 0
                    | h::tl => match h with
                               | Tpair t1 t2 => match (term_eq t t1) with
                                                | true => 1 + (times_term_appears_on_left_side_unification_problem' t (Uset tl) n')
                                                | false => times_term_appears_on_left_side_unification_problem' t (Uset tl) n'
                                                end
                                end
                    end
        end
  end.

Definition times_term_appears_on_left_side_unification_problem (t : term) (up : unification_problem) : nat :=
  match up with
  | Ubottom => 0
  | Uset l => times_term_appears_on_left_side_unification_problem' t up ((length l) + 1)
  end.

Compute (times_term_appears_on_left_side_unification_problem t1 (Uset [Tpair t2 t2; Tpair t2 t1; Tpair t2 t2])).

Fixpoint all_terms_appear_only_once' (up : unification_problem) (gas : nat): bool :=
  match gas with
  | O => false
  | S n' =>
          match up with
          | Ubottom => true
          | Uset l => match l with
                      | [] => true
                      | h::tl => match h with
                                 | Tpair t1 t2 => match (Nat.eqb (times_term_appears_on_left_side_unification_problem t1 up) 1) with
                                                  | false => false
                                                  | true => all_terms_appear_only_once' (Uset tl) n'
                                                  end
                                 end
                      end
          end
  end.

Definition all_terms_appear_only_once (up : unification_problem) : bool :=
  match up with
  | Ubottom => true
  | Uset l => all_terms_appear_only_once' up ((length l) + 1)
  end.

Compute (all_terms_appear_only_once (Uset [Tpair t1 t2; Tpair t2 t2])).

Definition unification_problem_in_solved_form (up : unification_problem) : bool :=
  andb (all_terms_have_property_unification_problem up term_pair_solved_form) (all_terms_appear_only_once up).

Definition is_decomposition_term_pair (t1 t2: term) : bool :=
  match t1 with
  | Tconst _ => false
  | Tvar _ => false
  | Tfunc f1 l1 => match f1 with
                 | Func fn1 => match t2 with 
                               | Tconst _ => false
                               | Tvar _ => false
                               | Tfunc f2 l2 => match f2 with
                                                | Func fn2 => andb (fn1 =? fn2) (Nat.eqb  (length l1)(length l2))
                                                end
                               end
                 end
  end.

Fixpoint  get_list_of_tpairs_from_decomposition_tpair' (tp : term_pair) (gas : nat): list term_pair:=
  match gas with
  | O => []
  | S n' =>
          match tp with
          | Tpair t1 t2 => match t1 with
                           | Tconst _ => []
                           | Tvar _ => []
                           | Tfunc f1 l1 => match t2 with
                                            | Tconst _ => []
                                            | Tvar _ => []
                                            | Tfunc f2 l2 => match l1 with
                                                             | [] => []
                                                             | h1::tl1 => match l2 with
                                                                          | [] => []
                                                                          | h2::tl2 => [(Tpair h1 h2)] ++ (get_list_of_tpairs_from_decomposition_tpair' (Tpair (Tfunc f1 tl1)(Tfunc f2 tl2)) n')
                                                                          end
                                                              end
                                             end
                           end
          end
  end.

Definition get_list_of_tpairs_from_decomposition_tpair (tp : term_pair) : list term_pair :=
  get_list_of_tpairs_from_decomposition_tpair' tp 100.

Compute (get_list_of_tpairs_from_decomposition_tpair (Tpair (Tfunc (Func "f") [Tvar a; Tvar b]) (Tfunc (Func "g") [Tvar y; Tvar x]))).

Definition term_pair_eq (tp1 tp2 : term_pair) : bool :=
  match tp1 with
  | Tpair t11 t12 => match tp2 with
                     | Tpair t21 t22 => andb (term_eq t11 t21) (term_eq t12 t22)
                     end
  end.

Compute (term_pair_eq (Tpair (Tfunc (Func "f") [Tvar a; Tvar b]) (Tfunc (Func "g") [Tvar y; Tvar x])) (Tpair (Tfunc (Func "f") [Tvar a; Tvar b]) (Tfunc (Func "g") [Tvar y; Tvar x]))).

Definition append_decomposition_unification_problem (tp : term_pair) (up : unification_problem) : unification_problem:=
  match up with
  | Ubottom => Ubottom
  | Uset l => Uset (l ++ get_list_of_tpairs_from_decomposition_tpair tp)
  end.

Fixpoint remove_decomposition_term_pair (tp : term_pair) (tpl : list term_pair) : list term_pair :=
  match tpl with
  | [] => []
  | h::tl => match (term_pair_eq tp h) with
            | true => tl
            | false => [h] ++ (remove_decomposition_term_pair tp tl)
            end
  end.



Compute (remove_decomposition_term_pair (Tpair (Tfunc (Func "f") [Tvar a; Tvar b]) (Tfunc (Func "g") [Tvar y; Tvar x])) [Tpair (Tvar a) t2; Tpair t1 t1; Tpair (Tfunc (Func "f") [Tvar a; Tvar b]) (Tfunc (Func "g") [Tvar y; Tvar x])]).

Definition remove_and_replace_decomposition_unif_problem (tp : term_pair) (up : unification_problem) : unification_problem :=
  match up with 
  | Ubottom => Ubottom
  | Uset l => append_decomposition_unification_problem tp (Uset (remove_decomposition_term_pair tp l))
  end.

Compute (remove_and_replace_decomposition_unif_problem (Tpair (Tfunc (Func "f") [Tvar x; Tvar y]) (Tfunc (Func "g") [Tvar a; Tvar b])) unif_probl1).

Compute (is_decomposition_term_pair (Tfunc (Func "f") [Tvar a; Tvar b]) (Tfunc (Func "f") [Tvar y; Tvar x])).
Compute (term_in_unification_problem (Uset [Tpair (Tfunc (Func "f") [Tvar a; Tvar b]) (Tfunc (Func "g") [Tvar y; Tvar x])]) is_decomposition_term_pair).

Definition is_orientation_term_pair (t1 t2 : term) : bool :=
  term_pair_first_var t2 t1.

Compute (is_orientation_term_pair t2 (Tvar a)).
Compute (term_in_unification_problem unif_probl1 is_orientation_term_pair).

Fixpoint orientation_term_pair_list (t1 t2: term) (tl : list term_pair) : list term_pair :=
  match tl with
  | [] => []
  | h::tl => match h with
             | Tpair tl1 tl2 => match (andb (term_eq t1 tl1) (term_eq t2 tl2)) with
                                | true => [(Tpair tl2 tl1)] ++ tl
                                | false => [h] ++ (orientation_term_pair_list t1 t2 tl)
                                end
              end
  end.

Compute orientation_term_pair_list t2 (Tvar a) [Tpair t2 (Tvar a)].

Definition apply_orientation (tp : term_pair) (up : unification_problem) : unification_problem :=
  match up with
  | Ubottom => Ubottom
  | Uset l => match tp with
              |Tpair t1 t2 => Uset (orientation_term_pair_list t1 t2 l)
              end
  end.

Compute (apply_orientation orientation_term_pair unif_probl1).

Definition is_conflict_term_pair (t1 t2 : term) : bool :=
  match t1, t2 with
  | Tfunc f1 l1, Tfunc f2 l2 => match f1, f2 with
                          | Func fn1, Func fn2 => negb (eqb fn1 fn2)
                          end
  | _, _ => false
  end.

Compute (is_conflict_term_pair (Tfunc (Func "f") [Tvar x; Tvar y]) (Tfunc (Func "g") [Tvar a; Tvar b])).
Compute (is_conflict_term_pair (Tfunc (Func "f") [Tvar x; Tvar y]) (Tfunc (Func "f") [Tvar a; Tvar b])).

Definition remove_conflict_term_pair (tp : term_pair) (up : unification_problem) : unification_problem :=
  Ubottom.

Compute (remove_conflict_term_pair conflict_term unif_probl2).

Definition is_occurs_check_term_pair (t1 t2 : term) : bool :=
  match (term_pair_first_var t1 t2) with
  | false => false
  | true => match (vars_term t1) with
            | [] => false
            | h::tl => var_in_term h t2 
            end
  end.

Compute (is_occurs_check_term_pair (Tvar a) (Tfunc (Func "g") [Tvar a; Tvar b])).

Definition occurs_check (tp : term_pair) (up : unification_problem) : unification_problem :=
  remove_conflict_term_pair tp up.

Definition is_elimination_term_pair (t1 t2 : term) : bool :=
  term_pair_solved_form t1 t2.

Definition from_elimination_term_pair_to_assignment (tp : term_pair) : assignment :=
  match tp with
  | Tpair t1 t2 => match t1 with
                   | Tvar v => Apairs [Apair v t2]
                   | _ => Apairs []
                   end
  end.

Compute (from_elimination_term_pair_to_assignment (Tpair (Tvar x) (Tvar a))).

Fixpoint elimination_term_pair_list (tp : term_pair) (tpl : list term_pair) : list term_pair :=
  match tpl with
  | [] => []
  | h::tl => match (term_pair_eq tp h) with
             | true => (elimination_term_pair_list tp tl) ++ [h]
             | _ => match h with
                    | Tpair t1 t2 => [Tpair (term_assignment (from_elimination_term_pair_to_assignment tp) t1) (term_assignment (from_elimination_term_pair_to_assignment tp) t2)] ++ (elimination_term_pair_list tp tl)
                    end
             end
  end.

Definition elimination (tp : term_pair) (up : unification_problem) : unification_problem :=
  match up with
  | Ubottom => Ubottom
  | Uset l => Uset (elimination_term_pair_list tp l)
  end.

Compute (elimination elimination_tpair elimination_example').

Definition unif_problem_minus_term_pair (u_p : unification_problem) (tp : term_pair) : unification_problem :=
  match u_p with
  | Ubottom => u_p
  | Uset l => Uset (remove_decomposition_term_pair tp l)
  end.

Fixpoint no_common_vars_in_lists (lvar1 lvar2 : list var) : bool :=
  match lvar1 with 
  | [] => true
  | h::tl => match (var_in_list_var h lvar2) with
            | true => false
            | false => no_common_vars_in_lists tl lvar2
            end
  end.

Compute (no_common_vars_in_lists [a; b] [x1; x2]).
Compute (no_common_vars_in_lists [a; b] [x1; b; x3]).

Fixpoint vars_in_unification_problem' (u_p : unification_problem) (gas : nat): list var :=
  match gas with
  | O => []
  | S n' =>
            match u_p with
            | Ubottom => []
            | Uset l => match l with
                        | [] => []
                        | h::tl => match h with
                                   | Tpair t1 t2 => (vars_term t1) ++ (vars_term t2) ++ (vars_in_unification_problem' (Uset tl) n')
                                   end
                        end
            end
  end.

Definition vars_in_unification_problem (u_p : unification_problem) :=  remove_duplicates_var_list (vars_in_unification_problem' u_p 100).

Compute vars_in_unification_problem (Uset [Tpair (Tvar a) (Tvar b); Tpair (Tvar a) (Tvar x1)]).

Definition check_if_elimination_applies (u_p : unification_problem) (tp : term_pair) : bool :=
  match tp with
  | Tpair t1 t2 => negb (no_common_vars_in_lists (vars_term t1) (vars_in_unification_problem (unif_problem_minus_term_pair u_p tp)))
  end.

Compute (check_if_elimination_applies (Uset [Tpair (Tvar x2) (Tvar x2); elimination_tpair]) elimination_tpair).
Compute (check_if_elimination_applies (Uset [Tpair (Tvar a) (Tvar a); elimination_tpair]) elimination_tpair).

Definition term_pair_correct_for_rule (tp : term_pair) (rule : term -> term -> bool) : bool :=
  match tp with
  | Tpair t1 t2 => rule t1 t2
  end.

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

Definition check_delete_and_deliver (u_p : unification_problem) :=
  deliver_tpair_from_unification_problem u_p term_eq.

Definition check_decomposition_and_deliver (u_p : unification_problem) :=
  deliver_tpair_from_unification_problem u_p is_decomposition_term_pair.

Definition check_orientation_and_deliver (u_p : unification_problem) :=
  deliver_tpair_from_unification_problem u_p is_orientation_term_pair.

Definition check_conflict_and_deliver (u_p : unification_problem) :=
  deliver_tpair_from_unification_problem u_p is_conflict_term_pair.

Definition check_occurs_check_and_deliver (u_p : unification_problem) :=
  deliver_tpair_from_unification_problem u_p is_occurs_check_term_pair.

Fixpoint deliver_elimination_tpair_from_list (tpl copy: list term_pair) : maybe_term_pair :=
  match tpl with
  | [] => TError
  | h::tl => match (term_pair_correct_for_rule h is_elimination_term_pair) with
             | true => match (check_if_elimination_applies (Uset copy) h) with
                       | true => TP h
                       | false => deliver_elimination_tpair_from_list tl copy
                       end
             | false => deliver_elimination_tpair_from_list tl copy
             end
  end.

Definition deliver_elimination_tpair_from_unification_problem (u_p : unification_problem) : maybe_term_pair :=
  match u_p with
  | Ubottom => TError
  | Uset l => deliver_elimination_tpair_from_list l l
  end.


Definition check_elimination_and_deliver (u_p : unification_problem) :=
  deliver_elimination_tpair_from_unification_problem u_p.

Compute (check_elimination_and_deliver elimination_example).

Compute (check_delete_and_deliver unif_probl1).

Definition solver_delete (tp : term_pair) (up : unification_problem) : unification_problem :=
  remove_first_appearance_term_unification_problem up term_eq.

Compute (check_decomposition_and_deliver unif_probl1').

Compute (check_decomposition_and_deliver unif_probl1'').

Compute (check_orientation_and_deliver unif_probl1).
Compute (term_pair_correct_for_rule elimination_tpair is_elimination_term_pair).
Compute (check_elimination_and_deliver elimination_example).

Compute (check_conflict_and_deliver unif_probl2).

Compute (check_occurs_check_and_deliver (Uset [occurs_check_term_pair])).

Compute (elimination elimination_tpair elimination_example').


Definition apply_one_step (u_p : unification_problem) : maybe_unification_problem :=
  match u_p with
  | Ubottom => UP Ubottom
  | _ => match (unification_problem_in_solved_form u_p) with
         | true => UP (u_p)
         | false => match (check_conflict_and_deliver u_p) with
                     | TP tp => UP (remove_conflict_term_pair tp u_p)
                     | TError => match (check_occurs_check_and_deliver u_p) with
                                 | TP tp => UP (occurs_check tp u_p)
                                 | TError =>match (check_delete_and_deliver u_p) with
                                           | TP tp => UP (solver_delete tp u_p)
                                           | TError => match (check_decomposition_and_deliver u_p) with
                                                       | TP tp => UP (remove_and_replace_decomposition_unif_problem tp u_p)
                                                       | TError => match (check_elimination_and_deliver u_p) with
                                                                   | TP tp => UP (elimination tp u_p) 
                                                                   | TError => match (check_orientation_and_deliver u_p) with
                                                                               | TP tp => UP (apply_orientation tp u_p)
                                                                               | TError => UError
                                                                               end
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
  | UP u_p =>
            match u_p with
            | Ubottom => UP Ubottom
            | _ => match (unification_problem_in_solved_form u_p) with
                   | true => UP (u_p)
                   | false => match (check_conflict_and_deliver u_p) with
                               | TP tp => UP (remove_conflict_term_pair tp u_p)
                               | TError => match (check_occurs_check_and_deliver u_p) with
                                           | TP tp => UP (occurs_check tp u_p)
                                           | TError =>match (check_delete_and_deliver u_p) with
                                                     | TP tp => UP (solver_delete tp u_p)
                                                     | TError => match (check_decomposition_and_deliver u_p) with
                                                                 | TP tp => UP (remove_and_replace_decomposition_unif_problem tp u_p)
                                                                 | TError => match (check_elimination_and_deliver u_p) with
                                                                             | TP tp => UP (elimination tp u_p) 
                                                                             | TError => match (check_orientation_and_deliver u_p) with
                                                                                         | TP tp => UP (apply_orientation tp u_p)
                                                                                         | TError => UError
                                                                                         end
                                                                              end
                                                                 end
                                                     end
                                           end
                             end
                  end
            end
  end.

Definition maybe_unification_problem_in_solved_form (m_u_p : maybe_unification_problem) : bool :=
  match m_u_p with
  | UError => false
  | UP up => unification_problem_in_solved_form up
  end.

Print unification_problem1'.
Compute apply_one_step unification_problem1'.
Compute maybe_apply_one_step (apply_one_step unification_problem1').
Compute maybe_apply_one_step (maybe_apply_one_step (apply_one_step unification_problem1')).
Compute maybe_apply_one_step (maybe_apply_one_step (maybe_apply_one_step (apply_one_step unification_problem1'))).
Compute maybe_apply_one_step (maybe_apply_one_step (maybe_apply_one_step (maybe_apply_one_step (apply_one_step unification_problem1')))).
Compute maybe_unification_problem_in_solved_form (maybe_apply_one_step (maybe_apply_one_step (maybe_apply_one_step (maybe_apply_one_step (apply_one_step unification_problem1'))))).

Print unif_probl1.
Compute apply_one_step unif_probl1.
Compute maybe_apply_one_step (apply_one_step unif_probl1).
Compute maybe_apply_one_step (maybe_apply_one_step (apply_one_step unif_probl1)).
Compute maybe_apply_one_step (maybe_apply_one_step (maybe_apply_one_step (apply_one_step unif_probl1))).
Compute maybe_apply_one_step (maybe_apply_one_step (maybe_apply_one_step (maybe_apply_one_step (apply_one_step unif_probl1)))).
Compute maybe_apply_one_step (maybe_apply_one_step (maybe_apply_one_step (maybe_apply_one_step (maybe_apply_one_step (apply_one_step unif_probl1))))).

Print elimination_example.
Compute apply_one_step elimination_example.
Compute maybe_apply_one_step (apply_one_step elimination_example).
Compute maybe_apply_one_step (maybe_apply_one_step (apply_one_step elimination_example)).
Compute maybe_apply_one_step (maybe_apply_one_step (maybe_apply_one_step (apply_one_step elimination_example))).
Compute maybe_apply_one_step (maybe_apply_one_step (maybe_apply_one_step (maybe_apply_one_step (apply_one_step elimination_example)))).


Fixpoint solve_unification_problem' (m_u_p : maybe_unification_problem) (gas : nat): maybe_unification_problem :=
  match gas with
  | O => UError
  | S n' =>
          match m_u_p with
          | UError => UError
          | UP Ubottom => m_u_p
          | _ => match (maybe_unification_problem_in_solved_form m_u_p) with
                 | true => m_u_p
                 | false => solve_unification_problem' (maybe_apply_one_step m_u_p) n'
                 end
          end
  end.

Definition solve_unification_problem (m_u_p : maybe_unification_problem) :=
  solve_unification_problem' m_u_p 100.

Compute solve_unification_problem (UP unif_probl1).
Compute solve_unification_problem (UP unification_problem1').

Definition is_bottom (u : unification_problem) : bool :=
  match u with
  | Ubottom => true
  | _ => false
  end.

Definition maybe_is_bottom (m_u_p : maybe_unification_problem) : bool :=
  match m_u_p with
  | UError => false
  | UP u_p => is_bottom u_p
  end.

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

Definition mup_to_up (mup : maybe_unification_problem): unification_problem :=
  match mup with
  | UError => Uset [Tpair (Tvar (Named_var "Error")) (Tvar (Named_var "Error"))]
  | UP u_p => u_p
  end.

Definition mtp_to_tp (mtp : maybe_term_pair): term_pair :=
  match mtp with
  | TError => Tpair (Tvar (Named_var "Error")) (Tvar (Named_var "Error"))
  | TP tp => tp 
  end.





(*DEPRECATED*)

Definition vars_atomic_formulae (a : atomic_formulae) : list var :=
  match a with
  | Afpred p l => remove_duplicates_var_list (flat_map vars_term l)
  end.

Fixpoint vars_first_order_formulae' (phi : first_order_formulae) : list var :=
  match phi with
  | Aformulae phi0 => vars_atomic_formulae phi0
  | Anot phi0 => vars_first_order_formulae' phi0
  | Aand phi1 phi2 => (vars_first_order_formulae' phi1) ++ (vars_first_order_formulae' phi2)
  | Aor phi1 phi2 => (vars_first_order_formulae' phi1) ++ (vars_first_order_formulae' phi2)
  | Aimplies phi1 phi2 => (vars_first_order_formulae' phi1) ++ (vars_first_order_formulae' phi2)
  | Adoubleimplies phi1 phi2 => (vars_first_order_formulae' phi1) ++ (vars_first_order_formulae' phi2)
  | Aforall x phi0 => (vars_first_order_formulae' phi0) ++ [x]
  | Aexists x phi0 => (vars_first_order_formulae' phi0) ++ [x]
  end.

Definition vars_first_order_formulae (phi : first_order_formulae) : list var := remove_duplicates_var_list (vars_first_order_formulae' phi).

Compute(vars_first_order_formulae' phi1).

Fixpoint free_vars_first_order_formulae' (phi : first_order_formulae) : list var :=
  match phi with
  | Aformulae phi0 => vars_atomic_formulae phi0
  | Anot phi0 => free_vars_first_order_formulae' phi0
  | Aand phi1 phi2 => (free_vars_first_order_formulae' phi1) ++ (free_vars_first_order_formulae' phi2)
  | Aor phi1 phi2 => (free_vars_first_order_formulae' phi1) ++ (free_vars_first_order_formulae' phi2)
  | Aimplies phi1 phi2 => (free_vars_first_order_formulae' phi1) ++ (free_vars_first_order_formulae' phi2)
  | Adoubleimplies phi1 phi2 => (free_vars_first_order_formulae' phi1) ++ (free_vars_first_order_formulae' phi2)
  | Aforall x phi0 => remove_element_var_list x (free_vars_first_order_formulae' phi0)
  | Aexists x phi0 => remove_element_var_list x (free_vars_first_order_formulae' phi0)
  end.

Definition free_vars_first_order_formulae (phi : first_order_formulae) : list var := 
              remove_duplicates_var_list (free_vars_first_order_formulae' phi).

Compute (free_vars_first_order_formulae (Aforall x (Aformulae (phi [Tvar x; Tvar y])))).
Compute (free_vars_first_order_formulae phi1).

Fixpoint bound_vars_first_order_formulae' (phi : first_order_formulae) : list var :=
  match phi with
  | Aformulae phi0 => []
  | Anot phi0 => bound_vars_first_order_formulae' phi0
  | Aand phi1 phi2 => (bound_vars_first_order_formulae' phi1) ++ (bound_vars_first_order_formulae' phi2)
  | Aor phi1 phi2 => (bound_vars_first_order_formulae' phi1) ++ (bound_vars_first_order_formulae' phi2)
  | Aimplies phi1 phi2 => (bound_vars_first_order_formulae' phi1) ++ (bound_vars_first_order_formulae' phi2)
  | Adoubleimplies phi1 phi2 => (bound_vars_first_order_formulae' phi1) ++ (bound_vars_first_order_formulae' phi2)
  | Aforall x phi0 => (bound_vars_first_order_formulae' phi0) ++ [x]
  | Aexists x phi0 => (bound_vars_first_order_formulae' phi0) ++ [x]
  end.

Definition bound_vars_first_order_formulae (phi : first_order_formulae) : list var := 
              remove_duplicates_var_list (bound_vars_first_order_formulae' phi).

Compute (bound_vars_first_order_formulae (Aforall x (Aformulae (phi [Tvar x; Tvar y])))).
Compute (bound_vars_first_order_formulae phi1).

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

(* Definition maybe_apply_one_step (m_u_p : maybe_unification_problem) : maybe_unification_problem :=
  match m_u_p with
  | UError => UError
  | UP up => apply_one_step up
  end. *)
