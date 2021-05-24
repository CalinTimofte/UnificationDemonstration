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

Inductive atomic_formulae : Prop :=
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

