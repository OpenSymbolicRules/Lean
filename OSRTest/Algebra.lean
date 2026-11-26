import OSR

/-!
# Algebra tests
-/

namespace OSRTest.Algebra

open OSR

private def t : Expr := .var "t"
private def u : Expr := .var "u"

-- Every rule belongs to a profile, every profile is non-empty, and every
-- replacement only uses pattern variables.
#guard Algebra.catalog.all fun e => e.rule.profiles.all (· ∈ Algebra.profiles)
#guard Algebra.profiles.all fun p => !(Algebra.profileRules p).isEmpty
#guard Algebra.catalog.all fun e => e.rule.rhsClosed
#guard Algebra.catalog.all fun e => e.rule.wellFormed.isEmpty

-- Distribution and factoring never share a profile (they are inverse).
#guard Algebra.profiles.all fun p =>
  !((Algebra.profileRules p).contains Algebra.distribute &&
    (Algebra.profileRules p).contains Algebra.factorLeftAdd)

-- Every profile terminates on every catalogue pattern within the proved bound.
#guard Algebra.profiles.all fun p =>
  Algebra.catalog.all fun e =>
    (normalize (Algebra.profileRules p)
      ((Algebra.defaultWeight).eval (fun _ => 0) e.rule.lhs + 64) e.rule.lhs).normal

-- Conditional rules are never applied by the reference engine.
#guard (normalize (Algebra.profileRules "default") 8 (.app1 .ln (.app2 .mul t u))).trace == []
#guard (normalize (Algebra.profileRules "default") 8 (.pow t (.int 0))).trace == []

-- Unconditional rules are.
#guard (normalize (Algebra.profileRules "default") 8 (.app2 .mul t (.int 0))).result == .int 0
#guard (normalize (Algebra.profileRules "factor_polynomials") 8
  (.app2 .add (.app2 .mul t u) (.app2 .mul t t))).result ==
    .app2 .mul t (.app2 .add u t)

-- Every v0.1 rule is migrated; one more rule is authored in OSR.
#guard Algebra.notMigrated.isEmpty && Algebra.catalog.length == 24
#guard (Algebra.catalog.filter (·.rule.provenance.method == .authored)).map (·.rule.id) ==
  ["algebra.root.sqrt_sq_nonneg", "algebra.root.sqrt_sq_abs", "algebra.root.sq_sqrt",
    "algebra.root.sqrt_mul"]
-- The square-root rules are proved over ℝ only (arith1#root has no complex interpretation).
#guard (Algebra.catalog.filter (·.rule.provenance.method == .authored)).all fun e =>
  e.proofs.map (·.1) == [.real] && e.findings.any (·.startsWith "complex:")

-- `sqrt(a^2) ⟶ a` for `a ≥ 0`: proved over ℝ, not stated over ℂ (no complex
-- interpretation of arith1#root), and conditional, so the engine leaves it alone.
#guard
  match Algebra.catalog.find? (·.rule.id == "algebra.root.sqrt_sq_nonneg") with
  | none => false
  | some e =>
    e.rule.conditions == [.ge (.var "a") (.int 0)] &&
    e.proofs == [(.real, ``OSR.Algebra.sqrtSq_real)] &&
    e.findings.any (·.startsWith "complex:")
-- `sqrt(t^2) ⟶ |t|` is unconditional, so the engine applies it; the conditional
-- `(sqrt t)^2 ⟶ t` and `sqrt(t u) ⟶ sqrt t sqrt u` are left alone.
#guard (normalize (Algebra.profileRules "default") 8
  (.app2 .root (.pow t (.int 2)) (.int 2))).result == .app1 .abs t
#guard (normalize (Algebra.profileRules "default") 8
  (.pow (.app2 .root t (.int 2)) (.int 2))).trace == []
#guard (normalize (Algebra.profileRules "default") 8
  (.app2 .root (.app2 .mul t u) (.int 2))).trace == []
-- `arith1#abs` is a fragment symbol with a real interpretation.
#guard Expr.allSymbols.contains ⟨"arith1", "abs"⟩

-- `1^x ⟶ 1` is unconditional: the engine applies it, whatever the exponent.
#guard (normalize (Algebra.profileRules "default") 8 (.pow (.int 1) (.var "n"))).result == .int 1

-- An integer variable in a pattern matches any exponent; the conditions
-- `p ∈ ℤ` keep the engine from applying the rule.
#guard (matchExpr Algebra.powPow.lhs (.pow (.pow t (.int 2)) (.int 3))).isSome
#guard (normalize (Algebra.profileRules "default") 8 (.pow (.pow t (.int 2)) (.int 3))).trace == []

end OSRTest.Algebra
