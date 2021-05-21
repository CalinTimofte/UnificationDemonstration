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

Inductive functional_symbol : Type :=
  | constant : string -> functional_symbol
  | func : string -> list var -> functional_symbol.

Inductive predicate : string -> list var -> Prop:=
  | predicative_symbol (name : string)  (vars : list var) : predicate name vars.

Check (func "f" [a; b]).
Definition f := func "f".
Check (f [a;b]).
Check (f).

Check (predicate "P" [a]).
Definition P := predicate "P".
Check (P [a]).

Check ( forall x : var, P [x]).



