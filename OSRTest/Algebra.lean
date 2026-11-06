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

-- Every v0.1 rule is migrated.
#guard Algebra.notMigrated.isEmpty && Algebra.catalog.length == 20

-- `1^x ⟶ 1` is unconditional: the engine applies it, whatever the exponent.
#guard (normalize (Algebra.profileRules "default") 8 (.pow (.int 1) (.var "n"))).result == .int 1

-- An integer variable in a pattern matches any exponent; the conditions
-- `p ∈ ℤ` keep the engine from applying the rule.
#guard (matchExpr Algebra.powPow.lhs (.pow (.pow t (.int 2)) (.int 3))).isSome
#guard (normalize (Algebra.profileRules "default") 8 (.pow (.pow t (.int 2)) (.int 3))).trace == []

end OSRTest.Algebra
