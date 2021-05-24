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

Check (Afpred (Predicate "P") [Tvar a]).
Definition phi := Afpred (Predicate "p") [Tvar a].


Inductive first_order_formulae : Type :=
  | Aformula (phi : atomic_formulae)
  | Anot (phi : first_order_formulae)
  | Aand (phi1 phi2 : first_order_formulae)
  | Aor (phi1 phi2 : first_order_formulae)
  | Aimplies (phi1 phi2 : first_order_formulae)
  | Adoubleimplies (phi1 phi2 : first_order_formulae)
  | Aforall (x : var) (phi : first_order_formulae)
  | Aexists (x : var) (phi : first_order_formulae).

Compute(hd a [b;a]).
Compute (hd (Tvar a) [Tvar b; Tvar a]).

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

Definition remove_duplicates_var_list (l : list var) : list var :=
  assemble_var_list (nodup string_dec (disassemble_var_list l)).

Compute (remove_duplicates_var_list [Named_var "a"; Named_var "b"; Named_var "b"]).

Fixpoint vars_term (t : term) : list var :=
  match t with
  | Tconst c => []
  | Tvar v => [v]
  | Tfunc f l => remove_duplicates_var_list (flat_map vars_term l)
  end.

Definition vars_atomic_formulae (a : atomic_formulae) : list var :=
  match a with
  | Afpred p l => flat_map vars_term l
  end.

Fixpoint vars_first_order_formulae (phi : first_order_formulae) : list var :=
  match phi with
  | Aformula phi0 => vars_atomic_formulae phi0
  | Anot phi0 => vars_first_order_formulae phi0
  | Aand phi1 phi2 => (vars_first_order_formulae phi1) ++ (vars_first_order_formulae phi2)
  | Aor phi1 phi2 => (vars_first_order_formulae phi1) ++ (vars_first_order_formulae phi2)
  | Aimplies phi1 phi2 => (vars_first_order_formulae phi1) ++ (vars_first_order_formulae phi2)
  | Adoubleimplies phi1 phi2 => (vars_first_order_formulae phi1) ++ (vars_first_order_formulae phi2)
  | Aforall x phi0 => (vars_first_order_formulae phi0) ++ [x]
  | Aexists x phi0 => (vars_first_order_formulae phi0) ++ [x]
  end.


Compute (vars_term (Tfunc (Func "f") [(Tvar a); (Tfunc (Func "g") [Tvar b; Tvar b])])).
