Require Import String.
Open Scope string_scope.

Require Import List.
Import ListNotations.

(*Inductive var: Type.
Variable P: list var -> functional_symbol.
Definition vars (f : functional_symbol) : list var :=
  match f with
  | constant => []
  | func l => l
  end.
Definition arity (f : functional_symbol) : nat :=
  length (vars f).
Compute (vars (func [a;b])).
Compute (arity (func [a;b;c])). *)

Inductive var: Type :=
  | named_var: string -> var.

Check ([named_var "a"; named_var "b"]).
Definition a := named_var "a".
Definition b := named_var "b".

Inductive const : Type :=
  | cconst: string -> const.

Inductive func : Type :=
  | fconst: const -> func
  | ffunc: string -> list var_or_term -> func

with var_or_term : Type :=
  | v : var -> var_or_term
  | t : term -> var_or_term

with term : Type :=
  | tconst: const -> term
  | tvar: var -> term
  | tfunc: func -> term.

Definition fake_parse_func (f : func) : var := named_var "default".

Inductive predicate : string -> list var -> Prop:=
  | predicative_symbol (name : string)  (vars : list var) : predicate name vars.

Check (ffunc "f" [v a; v b]).
Definition f := ffunc "f".
Check (f [v a;v b]).
Check (f).
Compute (fake_parse_func (f[v a])).

Check (predicate).
Check (predicate "P" [a]).
Definition P := predicate "P".
Check (P [a]).

Check ( forall x : var, P [x]).

Check (forall x:var, (forall y:var, ((P [x; y]) -> exists z:var, ((P [x; z]) /\ (P [z;y]))))).