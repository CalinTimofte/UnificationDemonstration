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

Compute (vars_term (Tfunc (Func "f") [(Tvar a); (Tfunc (Func "g") [Tvar b; Tvar b])])).



Compute (vars_term (Tfunc (Func "f") [(Tvar a); (Tvar a)])).
Compute(vars_first_order_formulae' phi1).

Definition remove_element_var_list (v : var) (l : list var) : list var :=
  assemble_var_list (remove string_dec (var_get_name v)(disassemble_var_list l)).

Compute (remove_element_var_list x [x; y; z]).

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
  term_pair_solved_form t2 t1.

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
             | true => [h] ++ (elimination_term_pair_list tp tl)
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

Compute (elimination elimination_tpair elimination_example).
