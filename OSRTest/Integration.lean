import OSR

/-!
# Integration tests
-/

namespace OSRTest.Integration

open OSR OSR.Calculus OSR.Integration

private def t : Expr := .var "t"

-- The twenty rules of the syntactic inventory (FreeQ or NeQ conditions,
-- registered heads, no Int in the result) are migrated or reported, plus
-- 110 rules with residual integrals and seven unmigrated ones.
#guard Integration.catalog.length + Integration.notMigrated.length == 170
#guard Integration.notMigrated.length == 14
#guard (Integration.catalog.filter (·.rule.shape == .antiderivRec)).length == 143
#guard (Integration.catalog.filter (!·.rule.conditions.isEmpty)).length == 128

-- RUBI 4.16.1: the new degenerate-coefficient cases are refuted in both
-- domains, with no proof or unresolved domain accidentally attached.
private def degenerateCoefficientIds : List String := [
  "integration.rubi_1_2_2_4_r57", "integration.rubi_1_2_2_4_r58",
  "integration.rubi_2_1_r10", "integration.rubi_4_1_12_r45",
  "integration.rubi_4_1_12_r46"]

#guard degenerateCoefficientIds.all fun id =>
  match Integration.catalog.find? (·.rule.id == id) with
  | none => false
  | some e => e.proofs.isEmpty && e.unproved.isEmpty &&
      [Domain.real, Domain.complex].all fun d =>
        (e.counterexamples.lookup d).isSome

-- Identifiers are unique, every rule is well formed and has the antiderivative shape.
#guard (Integration.catalog.map (·.rule.id)).eraseDups.length == Integration.catalog.length
#guard Integration.catalog.all fun e =>
  match e.rule.legacyId with
  | none => false
  | some id => Integration.notMigrated.all fun entry => entry.1 != id
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

-- Every migrated rule is proved or refuted in at least one domain (a few
-- numerically found counterexamples are established over ℂ only).
#guard Integration.catalog.all fun e =>
  [Domain.real, Domain.complex].any fun d =>
    (e.proofs.lookup d).isSome || (e.counterexamples.lookup d).isSome

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
  "integration.split_linear_factor_quadratic",
  "integration.partial_fractions_linear_quadratic",
  "integration.partial_fractions_linear_trinomial",
  "integration.partial_fractions_power_weighted", "integration.sin_cos_double_angle",
  "integration.split_log_linear_factor", "integration.linear_power_over_quadratic",
  "integration.binomial_negative_power", "integration.binomial_power_sin",
  "integration.binomial_power_cos", "integration.monomial_binomial_power_sin",
  "integration.monomial_binomial_power_cos"]

-- A conditional rule applies only when its conditions are decided: int(λt. t^m)
-- stays (m ≠ -1 is undecided), int(λt. t^(-1)) stays (decided false),
-- int(λt. t^3) rewrites with the power rule (3 ≠ -1 decided true).
#guard (rewrite rules (.integral "t" (.pow t (.var "m")))).isNone
#guard (rewrite rules (.integral "t" (.pow t (.int (-1))))).isNone
#guard (rewrite rules (.integral "t" (.pow t (.int 3)))).map (·.2) ==
  some (.lam "t" (.app2 .mul (.pow t (.app2 .add (.int 3) (.int 1)))
    (.pow (.app2 .add (.int 3) (.int 1)) (.int (-1)))))
#guard (rewrite rules (.integral "t" (.pow t (.int 3)))).map (·.1) == some "integration.power"

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
