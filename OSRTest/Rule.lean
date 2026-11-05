import OSR

/-!
# Rule well-formedness tests

A rule must bind every variable it uses, its replacement may only use
variables bound by its pattern, and its pattern must not be a bare variable.
-/

namespace OSRTest.Rule

open OSR

private def mk (vars : List String) (lhs rhs : Expr) (conds : List Cond := []) : Rule :=
  { id := "test.rule", vars, lhs, rhs, conditions := conds,
    profiles := ["default"], priority := 0, description := "",
    provenance := { method := .authored, sources := [] } }

private def x : Expr := .var "x"
private def y : Expr := .var "y"

-- Accepted: rhs variables are bound by the lhs.
#guard (mk ["x"] (.app1 .sin x) x).wellFormed.isEmpty

-- Rejected: the replacement introduces an unbound variable.
#guard !(mk ["x", "y"] (.app1 .sin x) y).wellFormed.isEmpty

-- Rejected: a variable is used but not declared.
#guard !(mk ["x"] (.app2 .add x y) x).wellFormed.isEmpty

-- Rejected: duplicate variable declarations.
#guard !(mk ["x", "x"] (.app1 .sin x) x).wellFormed.isEmpty

-- Rejected: a bare-variable pattern matches every expression.
#guard !(mk ["x"] x x).wellFormed.isEmpty

-- Rejected: a condition mentions a variable the pattern does not bind.
#guard !(mk ["x", "y"] (.app1 .sin x) x [.ne y (.int 0)]).wellFormed.isEmpty

-- Every Trigonometry rule is well formed.
#guard OSR.Trigonometry.catalog.all fun e => e.rule.wellFormed.isEmpty

-- Canonical identifiers are unique within the catalogue.
#guard (OSR.Trigonometry.catalog.map (·.rule.id)).eraseDups.length ==
  OSR.Trigonometry.catalog.length

-- Definedness: a division requires a nonzero denominator.
example (a b : ℝ) (h : b ≠ 0) :
    Defined Interp.real (fun s => if s = "a" then a else b)
      (.app2 .div (.var "a") (.var "b")) := by
  simp [Defined, eval, h]

end OSRTest.Rule
