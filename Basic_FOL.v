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

Inductive atomic_formulae : Prop :=
  | afpred: predicative_symbol -> list term -> atomic_formulae.

Check (afpred (predicate "P") [tvar a]).

Inductive first_order_formulae : Type :=
  | Aformula (p : atomic_formulae)
  | Anot (phi : first_order_formulae)
  | Aand (phi1 phi2 : first_order_formulae)
  | Aor (phi1 phi2 : first_order_formulae)
  | Aimplies (phi1 phi2 : first_order_formulae)
  | Adoubleimplies (phi1 phi2 : first_order_formulae)
  | Aforall (x : var) (phi : first_order_formulae)
  | Aexists (x : var) (phi : first_order_formulae).

Fixpoint first_order_formulae_eval (phi: first_order_formulae) : Prop :=
  match phi with
  | Aformula phi0 => phi0
  end.