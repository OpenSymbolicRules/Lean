import OSR

/-!
# Calculus tests
-/

namespace OSRTest.Calculus

open OSR OSR.Calculus

private def t : Expr := .var "t"

-- Every v0.1 rule is migrated or reported.
#guard Calculus.catalog.length + Calculus.notMigrated.length == 32

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
  match rewrite rules input with
  | some (_, out) => (rewrite rules out).isNone
  | none => false

-- The exported pattern decodes as OpenMath with a lambda binder.
#guard match derivSin.patternOM with
  | .oma h [.ombind b ["x"] _] => h == diffSymbol && b == lambdaSymbol
  | _ => false

-- An unproved rule is not applied by the reference engine.
#guard (rewrite rules (.diff "t" (.app1 .arctanh t))).isNone
#guard (rewrite rules (.diff "t" (.app1 .arcsin t))).map (·.2) ==
  some (.lam "t" (.app2 .div (.int 1) (.app2 .root (.app2 .sub (.int 1) (.pow t (.int 2))) (.int 2))))

end OSRTest.Calculus
