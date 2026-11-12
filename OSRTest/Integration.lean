import OSR

/-!
# Integration tests
-/

namespace OSRTest.Integration

open OSR OSR.Calculus OSR.Integration

private def t : Expr := .var "t"

-- Every rule of the syntactic inventory is migrated or reported.
#guard Integration.catalog.length + Integration.notMigrated.length == 9
#guard Integration.notMigrated.length == 3

-- Identifiers are unique, every rule is well formed and has the antiderivative shape.
#guard (Integration.catalog.map (·.rule.id)).eraseDups.length == Integration.catalog.length
#guard Integration.catalog.all (·.rule.wellFormed)
#guard Integration.catalog.all (·.rule.shape == .antideriv)

-- Every migrated rule is proved or refuted over ℝ.
#guard Integration.catalog.all fun e =>
  (e.proofs.lookup .real).isSome || (e.counterexamples.lookup .real).isSome

-- No Calculus rule has the antiderivative shape: the Calculus set is unchanged.
#guard Calculus.catalog.all (·.rule.shape != .antideriv)

-- The exported pattern is calculus1#int applied to a lambda.
#guard match constant.patternOM with
  | .oma h [.ombind b ["x"] _] => h == intSymbol && b == lambdaSymbol
  | _ => false
#guard constant.symbols.contains intSymbol

private def rules : List CRule :=
  (Integration.catalog.filter fun e => (e.proofs.lookup .real).isSome).map (·.rule)

-- Only the two proved rules are applied.
#guard rules.map (·.id) == ["integration.log_monomial", "integration.constant"]

-- int(λt. u) ⟶ λt. u t: the input's bound variable is kept.
#guard (rewrite rules (.integral "t" (.var "u"))).map (·.2) ==
  some (.lam "t" (.app2 .mul (.var "u") t))

-- FreeQ as an independence constraint: int(λt. t) is not a constant.
#guard (rewrite rules (.integral "t" t)).isNone

-- int(λt. ln(c t^n)) ⟶ λt. t ln(c t^n) - n t.
#guard (rewrite rules (.integral "t" (.app1 .ln (.app2 .mul (.var "c") (.pow t (.var "n")))))).map
    (·.2) ==
  some (.lam "t" (.app2 .add
    (.app2 .mul t (.app1 .ln (.app2 .mul (.var "c") (.pow t (.var "n")))))
    (.app2 .mul (.app2 .mul (.int (-1)) (.var "n")) t)))

-- Refuted rules are not applied: int(λt. 1 · t^(-1)) stays.
#guard (rewrite rules (.integral "t" (.app2 .mul (.int 1) (.pow t (.int (-1)))))).isNone

-- Antiderivative rules do not apply to derivatives, and vice versa.
#guard (rewrite rules (.diff "t" (.var "u"))).isNone
#guard (rewrite (Calculus.catalog.map (·.rule)) (.integral "t" (.var "u"))).isNone

-- Rules apply once: their results are lambdas.
#guard rules.all fun r =>
  match rewrite rules (.integral r.x r.body) with
  | some (_, out) => (rewrite rules out).isNone
  | none => false

-- Proofs and counterexamples use the standard axioms only.
run_meta do
  for e in Integration.catalog do
    for (_, thm) in e.proofs ++ e.counterexamples do
      let forbidden := (← Lean.collectAxioms thm).toList.filter fun ax =>
        ax ∉ [``propext, ``Classical.choice, ``Quot.sound]
      unless forbidden.isEmpty do
        throwError "{thm} depends on {forbidden}"

end OSRTest.Integration
