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

Inductive func : string -> list var -> Type :=
  | constant_symbol (name : string): func name []
  | functional_symbol (name : string) (vars : list var): func name vars.

Definition fake_parse_func (f : Type) : var := named_var "default".

Inductive predicate : string -> list var -> Prop:=
  | predicative_symbol (name : string)  (vars : list var) : predicate name vars.

Check (functional_symbol "f" [a; b]).
Definition f := func "f".
Check (f [a;b]).
Check (f).
Compute (fake_parse_func (f[a])).

Check (predicate).
Check (predicate "P" [a]).
Definition P := predicate "P".
Check (P [a]).

Check ( forall x : var, P [x]).

Check (forall x:var, (forall y:var, ((P [x; y]) -> exists z:var, ((P [x; z]) /\ (P [z;y]))))).



