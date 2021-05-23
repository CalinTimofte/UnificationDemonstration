Require Import String.
Open Scope string_scope.

Require Import List.
Import ListNotations.

Inductive var: Type :=
  | named_var: string -> var.

Check ([named_var "a"; named_var "b"]).
Check(named_var "a").
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

Inductive atomic_formulae : predicative_symbol -> list term -> Prop :=
  | afpred (p : predicative_symbol) (l : list term): atomic_formulae p l.

Check (afpred (predicate "P") [tvar a]).
Definition phi := atomic_formulae (predicate "p") [tvar a].
Check (phi /\ phi).


Inductive first_order_formulae : Type :=
  | Aformula (p: predicative_symbol)(l: list term)
  | Anot (phi : first_order_formulae)
  | Aand (phi1 phi2 : first_order_formulae)
  | Aor (phi1 phi2 : first_order_formulae)
  | Aimplies (phi1 phi2 : first_order_formulae)
  | Adoubleimplies (phi1 phi2 : first_order_formulae)
  | Aforall (x : var) (phi : first_order_formulae)
  | Aexists (x : var) (phi : first_order_formulae).

Fixpoint first_order_formulae_eval (phi: first_order_formulae) : Prop :=
  match phi with
  | Aformula p l => atomic_formulae p l
  | Anot phi0 => ~(first_order_formulae_eval phi0)
  | Aand phi1 phi2 => (first_order_formulae_eval phi1) /\ (first_order_formulae_eval phi2)
  | Aor phi1 phi2 => (first_order_formulae_eval phi1) \/ (first_order_formulae_eval phi2)
  | Aimplies phi1 phi2 => (first_order_formulae_eval phi1) -> (first_order_formulae_eval phi2)
  | Adoubleimplies phi1 phi2 => (first_order_formulae_eval phi1) <-> (first_order_formulae_eval phi2)
  | Aforall x phi0 => forall x: var, (first_order_formulae_eval phi0)
  | Aexists x phi0 => exists x: var, (first_order_formulae_eval phi0)
  end.

(* Run some tests *)

Definition P := predicate "P".
Check(Aformula P [tvar a]).
Definition phi1 := Aformula P [tvar a].
Definition phi2 := Aformula P [tvar b; tvar b].
Check(Aand phi1 phi2).
Check(Aexists a phi1).

Compute first_order_formulae_eval phi1.
Compute first_order_formulae_eval (Anot phi1).
Compute first_order_formulae_eval (Aand phi1 phi2).
Compute first_order_formulae_eval (Aor phi1 phi2).
Compute first_order_formulae_eval (Aimplies phi1 phi2).
Compute first_order_formulae_eval (Adoubleimplies phi1 phi2).
Compute first_order_formulae_eval (Aforall a phi1).
Compute first_order_formulae_eval (Aexists b phi2).