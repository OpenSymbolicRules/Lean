import OSR

/-!
# Integration tests
-/

namespace OSRTest.Integration

open OSR OSR.Calculus OSR.Integration

private def t : Expr := .var "t"

-- The twenty rules of the syntactic inventory (FreeQ or NeQ conditions,
-- registered heads, no Int in the result) are migrated or reported, plus
-- twenty-two rules with residual integrals.
#guard Integration.catalog.length + Integration.notMigrated.length == 42
#guard Integration.notMigrated.length == 7
#guard (Integration.catalog.filter (·.rule.shape == .antiderivRec)).length == 22
#guard (Integration.catalog.filter (!·.rule.conditions.isEmpty)).length == 15

-- Identifiers are unique, every rule is well formed and has the antiderivative shape.
#guard (Integration.catalog.map (·.rule.id)).eraseDups.length == Integration.catalog.length
#guard Integration.catalog.all fun e =>
  if e.rule.shape == .antiderivRec then e.rule.recOk else e.rule.wellFormed
#guard Integration.catalog.all (·.rule.recOk)
#guard Integration.catalog.all fun e => e.rule.shape == .antideriv || e.rule.shape == .antiderivRec
#guard Integration.catalog.all (·.rule.conditionsOk)
#guard Calculus.catalog.all (·.rule.conditionsOk)

-- Conditions are exported as relation1#neq.
#guard power.symbols.contains ⟨"relation1", "neq"⟩

-- A residual integral is exported as int(λx. H)(x).
#guard match IntegrationRec.sinAddSq.replacementOM with
  | .ombind b ["x"] (.oma _ [.oma _ [_, .omapp (.oma h [.ombind b' ["x"] _]) [.omv "x"]], _]) =>
    b == lambdaSymbol && h == intSymbol && b' == lambdaSymbol
  | _ => false

-- Recursive rules are not applied by the reference rewriter.
#guard (rewrite (Integration.catalog.map (·.rule))
  (.integral "t" (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d")
    (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") t)) (.int 2))))))).isNone

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

-- The rules proved over ℝ; the reference rewriter applies the unconditional ones.
#guard rules.map (·.id) == ["integration.log_monomial", "integration.constant",
  "integration.power", "integration.sin_log", "integration.cos_log",
  "integration.sin_add_square", "integration.cos_add_square",
  "integration.sin_add_power_over_x", "integration.cos_add_power_over_x",
  "integration.power_sin_square", "integration.power_cos_square",
  "integration.log_linear_power", "integration.partial_fractions_linear",
  "integration.partial_fractions_power", "integration.split_linear_factor_binomial",
  "integration.split_linear_factor_quadratic"]

-- A conditional rule is not applied: int(λt. t^m) stays.
#guard (rewrite rules (.integral "t" (.pow t (.var "m")))).isNone

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

-- Unconditional, non-recursive rules apply once: their results are lambdas.
#guard (rules.filter fun r => r.conditions.isEmpty && r.shape == .antideriv).all fun r =>
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
