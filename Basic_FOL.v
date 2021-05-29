Require Import String.
Open Scope string_scope.

Require Import List.
Import ListNotations.

Inductive var: Type :=
  | Named_var: string -> var.

Check ([Named_var "a"; Named_var "b"]).
Check(Named_var "a").
Definition a := Named_var "a".
Definition b := Named_var "b".

Inductive functional_symbol : Type :=
  | Func: string -> functional_symbol.

Inductive predicative_symbol : Type :=
  | Predicate: string -> predicative_symbol.

Inductive term : Type :=
  | Tconst : functional_symbol -> term
  | Tvar : var -> term
  | Tfunc : functional_symbol -> list term -> term.

Inductive atomic_formulae : Type :=
  | Afpred: predicative_symbol -> list term -> atomic_formulae.

Definition P := Predicate "P".
Check (Afpred (Predicate "P") [Tvar a]).
Definition phi := Afpred P.


Inductive first_order_formulae : Type :=
  | Aformulae (phi : atomic_formulae)
  | Anot (phi : first_order_formulae)
  | Aand (phi1 phi2 : first_order_formulae)
  | Aor (phi1 phi2 : first_order_formulae)
  | Aimplies (phi1 phi2 : first_order_formulae)
  | Adoubleimplies (phi1 phi2 : first_order_formulae)
  | Aforall (x : var) (phi : first_order_formulae)
  | Aexists (x : var) (phi : first_order_formulae).

Compute(hd a [b;a]).
Compute (hd (Tvar a) [Tvar b; Tvar a]).

(* Support functions for removing duplicates in a var list *)

Definition var_get_name (v : var) : string := 
  match v with
  | Named_var s => s
  end.

Check (Named_var "a" = Named_var "b").

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

Definition x := Named_var "x".
Definition y := Named_var "y".
Definition z := Named_var "z".

Compute (vars_term (Tfunc (Func "f") [(Tvar a); (Tvar a)])).
Definition phi1 := ( Aand ( Aforall x ( Aand ( Aformulae ( phi [Tvar x; Tvar y] ) ) ( Aexists y ( Aand ( Aformulae (phi [Tvar z; Tfunc ( Func "f" ) [Tvar x; Tvar y]]) ) ( Aformulae ( phi [Tvar x; Tvar y] ) )  ) ) ) ) ( Aformulae ( phi [Tvar x; Tvar x] ) )).
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

Inductive assignment_pair : Type :=
  | Apair: var -> term -> assignment_pair.

Inductive assignment : Type :=
  | Apairs: list assignment_pair -> assignment.

Check (Apair x (Tvar y)).
Check (Apairs [Apair x (Tvar y); Apair z (Tfunc (Func "f") [Tvar x; Tvar y])]).

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
Definition sigma1 := Apairs [Apair y (Tvar x); Apair x (Tvar y)].

Definition t1 := Tfunc (Func "f") [Tvar x; Tvar y; Tvar x; Tfunc (Func "g") [Tvar x; Tvar y]].
Definition t2 := Tfunc (Func "f") [Tvar x; Tvar y; Tvar x].

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

Inductive term_pair : Type :=
  | Tpair (t1 t2 : term) : term_pair.

Inductive unification_problem : Type :=
  | Uset (l : list term_pair) : unification_problem
  | Ubottom.

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

Definition some_func (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

Inductive solver : unification_problem -> Prop :=
  | Solved : solver Ubottom
  | Delete (
