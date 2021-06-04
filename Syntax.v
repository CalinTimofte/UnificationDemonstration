Require Import String.
Open Scope string_scope.

Require Import List.
Import ListNotations.

Inductive var: Type :=
  | Named_var: string -> var.

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


Inductive first_order_formulae : Type :=
  | Aformulae (phi : atomic_formulae)
  | Anot (phi : first_order_formulae)
  | Aand (phi1 phi2 : first_order_formulae)
  | Aor (phi1 phi2 : first_order_formulae)
  | Aimplies (phi1 phi2 : first_order_formulae)
  | Adoubleimplies (phi1 phi2 : first_order_formulae)
  | Aforall (x : var) (phi : first_order_formulae)
  | Aexists (x : var) (phi : first_order_formulae).

Inductive assignment_pair : Type :=
  | Apair: var -> term -> assignment_pair.

Inductive assignment : Type :=
  | Apairs: list assignment_pair -> assignment.

Inductive term_pair : Type :=
  | Tpair (t1 t2 : term) : term_pair.

Inductive unification_problem : Type :=
  | Uset (l : list term_pair) : unification_problem
  | Ubottom.

Definition a := Named_var "a".
Definition b := Named_var "b".
Definition x := Named_var "x".
Definition y := Named_var "y".
Definition z := Named_var "z".
Definition x1 := Named_var "x1".
Definition x2 := Named_var "x2".
Definition x3 := Named_var "x3".
Definition f := Func "f".
Definition g := Func "g".


Definition P := Predicate "P".
Definition phi := Afpred P.

Definition phi1 := ( Aand ( Aforall x ( Aand ( Aformulae ( phi [Tvar x; Tvar y] ) ) ( Aexists y ( Aand ( Aformulae (phi [Tvar z; Tfunc ( Func "f" ) [Tvar x; Tvar y]]) ) ( Aformulae ( phi [Tvar x; Tvar y] ) )  ) ) ) ) ( Aformulae ( phi [Tvar x; Tvar x] ) )).

Definition sigma1 := Apairs [Apair y (Tvar x); Apair x (Tvar y)].

Definition t1 := Tfunc (Func "f") [Tvar x; Tvar y; Tvar x; Tfunc (Func "g") [Tvar x; Tvar y]].
Definition t2 := Tfunc (Func "f") [Tvar x; Tvar y; Tvar x].

Definition decomposition_term_pair := Tpair (Tfunc (Func "f") [Tvar x; Tvar y]) (Tfunc (Func "f") [Tvar a; Tvar b]).
Definition orientation_term_pair := Tpair t2 (Tvar a).
Definition conflict_term := Tpair (Tfunc (Func "f") [Tvar x; Tvar y]) (Tfunc (Func "g") [Tvar a; Tvar b]).
Definition occurs_check_term_pair := (Tpair (Tvar a) (Tfunc (Func "g") [Tvar a; Tvar b])).
Definition unif_probl1 := Uset [ Tpair t1 t1; decomposition_term_pair; orientation_term_pair].
Definition unif_probl2 := Uset [ conflict_term ].
Definition elimination_tpair := Tpair (Tvar x2) (Tvar a).
Definition unif_probl4 := Uset [Tpair (Tfunc f [Tfunc g [Tvar x1; Tvar a]; Tvar x2]) (Tvar x3); Tpair (Tfunc f [Tvar x2; Tvar x2]) (Tfunc f [Tvar a; Tvar x1])].
Definition unif_probl4' := Uset [Tpair (Tfunc f [Tfunc g [Tvar x1; Tvar a]; Tvar x2]) (Tvar x3); Tpair (Tvar x2) (Tvar a); Tpair (Tvar x2) (Tvar x1)].
Definition unif_probl4'' := Uset [Tpair (Tfunc f [Tfunc g [Tvar x1; Tvar a]; Tvar a]) (Tvar x3); Tpair (Tvar x2) (Tvar a); Tpair (Tvar a) (Tvar x1)].
Definition unif_probl4''' := Uset [Tpair (Tfunc f [Tfunc g [Tvar x1; Tvar a]; Tvar a]) (Tvar x3); Tpair (Tvar x2) (Tvar a); Tpair (Tvar x1) (Tvar a)].
Definition unif_probl4'''' := Uset [Tpair (Tfunc f [Tfunc g [Tvar a; Tvar a]; Tvar a]) (Tvar x3); Tpair (Tvar x2) (Tvar a); Tpair (Tvar x1) (Tvar a)].
Definition unif_probl4''''' := Uset [Tpair (Tvar x3) (Tfunc f [Tfunc g [Tvar a; Tvar a]; Tvar a]); Tpair (Tvar x2) (Tvar a); Tpair (Tvar x1) (Tvar a)].
Definition elimination_example := Uset [Tpair (Tfunc f [Tfunc g [Tvar x1; Tvar a]; Tvar x2]) (Tvar x3); Tpair (Tfunc f [Tvar x2; Tvar x2]) (Tfunc f [Tvar a; Tvar x1]); elimination_tpair].

Check (Afpred (Predicate "P") [Tvar a]).
Check (Apair x (Tvar y)).
Check (Apairs [Apair x (Tvar y); Apair z (Tfunc (Func "f") [Tvar x; Tvar y])]).
