Require Import String.
Open Scope string_scope.

Require Import List.
Import ListNotations.

Inductive var: Type :=
  | named_var: string -> var.

Check ([named_var "a"; named_var "b"]).
Definition a := named_var "a".
Definition b := named_var "b".

Inductive functional_symbol : Type :=
  | func: string -> functional_symbol.

Inductive predicative_symbol : Type :=
  | predicate: string -> predicative_symbol.

Inductive term : Type :=
  | tconst : functional_symbol -> term
  | tvar : var -> term
  | tfunc : functional_symbol -> list term -> term.

Inductive atomic_formulae : Type :=
  | afpred : predicative_symbol -> list term -> atomic_formulae.