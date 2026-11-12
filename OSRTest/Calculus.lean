import OSR

/-!
# Calculus tests
-/

namespace OSRTest.Calculus

open OSR OSR.Calculus

private def t : Expr := .var "t"

-- Every v0.1 rule is migrated or reported.
#guard Calculus.catalog.length + Calculus.notMigrated.length == 32
#guard Calculus.notMigrated.length == 3
#guard Calculus.notMigrated.all fun (_, reason) =>
  reason == "requires differentiability assumptions for the operands; the v0.1 rule has no such conditions, and its osr#Apply application is outside OSR v1"

-- A composite can have a derivative even though its operands have none.
-- sqrt(x^2) is expressible in the existing real OpenMath fragment.
example :
    HasDerivAt (fun x : ℝ => Real.sqrt (x ^ 2) + -Real.sqrt (x ^ 2)) 0 0 ∧
      ¬ DifferentiableAt ℝ (fun x : ℝ => Real.sqrt (x ^ 2)) 0 ∧
      ¬ DifferentiableAt ℝ (fun x : ℝ => -Real.sqrt (x ^ 2)) 0 :=
  structuralSum_missingPremise

example :
    HasDerivAt (fun x : ℝ => Real.sqrt (x ^ 2) - Real.sqrt (x ^ 2)) 0 0 ∧
      ¬ DifferentiableAt ℝ (fun x : ℝ => Real.sqrt (x ^ 2)) 0 :=
  structuralDifference_missingPremise

example :
    HasDerivAt (fun x : ℝ => Real.sqrt (x ^ 2) * Real.sqrt (x ^ 2)) 0 0 ∧
      ¬ DifferentiableAt ℝ (fun x : ℝ => Real.sqrt (x ^ 2)) 0 :=
  structuralProduct_missingPremise

-- The diagnostic proofs use the same axiom policy as certified rules.
run_meta do
  for thm in [``structuralSum_missingPremise,
      ``structuralDifference_missingPremise, ``structuralProduct_missingPremise] do
    let forbidden := (← Lean.collectAxioms thm).toList.filter fun ax =>
      ax ∉ [``propext, ``Classical.choice, ``Quot.sound]
    unless forbidden.isEmpty do
      throwError "structural diagnostic {thm} depends on {forbidden}"

-- Identifiers are unique and every rule is well formed.
#guard (Calculus.catalog.map (·.rule.id)).eraseDups.length == Calculus.catalog.length
#guard Calculus.catalog.all (·.rule.wellFormed)

private def rules : List CRule :=
  (Calculus.catalog.filter fun e => (e.proofs.lookup .real).isSome).map (·.rule)

-- The input's bound variable is kept.
#guard (rewrite rules (.diff "t" (.app1 .sin t))).map (·.2) == some (.lam "t" (.app1 .cos t))
#guard (rewrite rules (.limit (.int 0) "t" (.app2 .div (.app1 .sin t) t))).map (·.2) ==
  some (.val (.int 1))

-- No rule for sin(2t), a limit at another point, or a lambda.
#guard (rewrite rules (.diff "t" (.app1 .sin (.app2 .mul (.int 2) t)))).isNone
#guard (rewrite rules (.limit (.int 1) "t" (.app2 .div (.app1 .sin t) t))).isNone
#guard (rewrite rules (.lam "t" (.app1 .cos t))).isNone

-- Rules apply once: their results are lambdas or values.
#guard (Calculus.catalog.filter fun e => (e.proofs.lookup .real).isSome).all fun e =>
  let r := e.rule
  let input := match r.shape with
    | .deriv => CTerm.diff r.x r.body
    | .limit => CTerm.limit r.point r.x r.body
    | .antideriv => CTerm.integral r.x r.body
  match rewrite rules input with
  | some (_, out) => (rewrite rules out).isNone
  | none => false

-- The exported pattern decodes as OpenMath with a lambda binder.
#guard match derivSin.patternOM with
  | .oma h [.ombind b ["x"] _] => h == diffSymbol && b == lambdaSymbol
  | _ => false

-- Every rule but the refuted power rule is proved over ℝ.
#guard rules.length + 1 == Calculus.catalog.length
#guard !(rules.contains derivPow)

-- FreeQ as an independence constraint: diff(λt. sin u) is a constant, diff(λt. t u) is not.
#guard (rewrite rules (.diff "t" (.app1 .sin (.var "u")))).map (·.2) == some (.lam "t" (.int 0))
#guard (rewrite rules (.diff "t" (.app2 .mul t (.var "u")))).isNone
#guard (rewrite rules (.limit (.int 1) "t" (.var "u"))).map (·.2) == some (.val (.var "u"))
#guard (rewrite rules (.diff "t" (.app1 .arctanh t))).isSome
#guard (rewrite rules (.diff "t" (.app1 .arcsin t))).map (·.2) ==
  some (.lam "t" (.app2 .div (.int 1) (.app2 .root (.app2 .sub (.int 1) (.pow t (.int 2))) (.int 2))))

end OSRTest.Calculus
