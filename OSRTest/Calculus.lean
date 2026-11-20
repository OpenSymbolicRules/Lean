import OSR

/-!
# Calculus tests
-/

namespace OSRTest.Calculus

open OSR OSR.Calculus

private def t : Expr := .var "t"

-- Every v0.1 rule is migrated or reported.
#guard Calculus.catalog.length + Calculus.notMigrated.length == 33
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

-- Rules apply once: their results are lambdas or values (unconditional rules;
-- a conditional rule applies only when its conditions are decided).
#guard (Calculus.catalog.filter fun e => (e.proofs.lookup .real).isSome &&
    e.rule.conditions.isEmpty).all fun e =>
  let r := e.rule
  let input := match r.shape with
    | .deriv => CTerm.diff r.x r.body
    | .limit => CTerm.limit r.point r.x r.body
    | .antideriv | .antiderivRec | .antiderivSubst => CTerm.integral r.x r.body
  match rewrite rules input with
  | some (_, out) => (rewrite rules out).isNone
  | none => false

-- The exported pattern decodes as OpenMath with a lambda binder.
#guard match derivSin.patternOM with
  | .oma h [.ombind b ["x"] _] => h == diffSymbol && b == lambdaSymbol
  | _ => false

-- The strengthened power rule applies when n is decided nonzero: d/dt t³ = 3 t^(3 - 1);
-- not to t⁰ (n = 0 decided false) nor to tⁿ (undecided).
#guard (rewrite rules (.diff "t" (.pow t (.int 3)))).map (·.2) ==
  some (.lam "t" (.app2 .mul (.int 3) (.pow t (.app2 .add (.int 3) (.int (-1))))))
#guard (rewrite rules (.diff "t" (.pow t (.int 0)))).isNone
#guard (rewrite rules (.diff "t" (.pow t (.var "n")))).isNone

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

-- A rule with a substitution (`antiderivSubst`, v0.1 `Subst`):
-- ∫ 2x cos(x²) dx = int(λx. cos x)(x²), an antiderivative of cos read at x².
private def substTest : CRule where
  id := "test.subst"; shape := .antiderivSubst; x := "x"
  body := .app2 .mul (.app2 .mul (.int 2) (.var "x")) (.app1 .cos (.pow (.var "x") (.int 2)))
  result := .var "I1"
  integrals := [("I1", .app1 .cos (.var "x"))]
  substs := [("I1", .pow (.var "x") (.int 2))]
  priority := 0; description := "test"; provenance := { method := .derived, sources := [] }

#guard substTest.recOk && substTest.conditionsOk
-- The hole is exported as int(λx. cos x)(x²): its argument is the power, not x.
#guard (substTest.replacementOM.toJson.compress.splitOn "\"power\"").length == 2
-- Substitutions belong to antiderivSubst only, and only on holes.
#guard !{ substTest with shape := .antiderivRec }.recOk
#guard !{ substTest with substs := [("J", .var "x")] }.recOk

open Filter in
theorem substTest_real : substTest.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" [] substTest.body substTest.result
    substTest.integrals substTest.substs
  intro env _ t _
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have i2' : intValue? ((2 : ℤ) : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [substTest, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    exact ⟨Eventually.of_forall fun v g hg => by
        simp [substTest] at hg; subst hg; simp [Defined, eval, Interp.real, i2, i2'],
      Eventually.of_forall fun u => by simp [Defined, eval, Interp.real]⟩
  · exact Eventually.of_forall fun v => by simp [substTest, Defined]
  · simp only [substTest, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have key : ∀ v : ℝ, substAt Interp.real env [("I1", .pow (.var "x") (.int 2))] "x" "I1" v =
        v ^ 2 := fun v => by
      simp [substAt, List.lookup, eval, Interp.real, i2, i2', zpow_ofNat]
    rw [key t] at hΦ
    have hv : eval Interp.real (Function.update env "x" (t ^ 2)) (.app1 .cos (.var "x")) =
        Real.cos (t ^ 2) := by simp [eval, Interp.real]
    rw [hv] at hΦ
    have h2 : HasDerivAt (fun v : ℝ => v ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have hc := HasDerivAt.comp (h := fun v : ℝ => v ^ 2) t hΦ h2
    convert hc using 1
    · funext v
      simp only [substEnv, eval, substTest, List.map, List.mem_cons, List.not_mem_nil, or_false,
        Function.update_apply]
      simp [key v]
    · simp [substTest, eval, Interp.real, i2, i2']
      ring

end OSRTest.Calculus
