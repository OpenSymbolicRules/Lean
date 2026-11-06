import OSR

/-!
# Reference rewriter tests

Matching, substitution, the outermost-first strategy, and termination of
every Trigonometry profile on the patterns of the catalogue.
-/

namespace OSRTest.Rewrite

open OSR

private def x : Expr := .var "x"
private def t : Expr := .var "t"
private def sin (e : Expr) : Expr := .app1 .sin e
private def cos (e : Expr) : Expr := .app1 .cos e
private def add (e f : Expr) : Expr := .app2 .add e f
private def sq (e : Expr) : Expr := .pow e (.int 2)

-- Matching binds pattern variables.
#guard matchExpr (sin x) (sin (add t t)) == some [("x", add t t)]

-- A repeated variable must match equal subterms.
#guard matchExpr (add x x) (add t t) == some [("x", t)]
#guard matchExpr (add x x) (add t (.int 1)) == none

-- Integer literals match by value (regression: OSRv1 BigInt identity).
#guard matchExpr (.pow x (.int 2)) (.pow t (.int 2)) == some [("x", t)]
#guard matchExpr (.int 2) (.int 2) == some []
#guard matchExpr (.int 2) (.int 3) == none

-- Operators must agree.
#guard matchExpr (sin x) (cos t) == none

-- Substitution replaces bound variables and keeps unbound ones.
#guard (add x (.var "y")).subst [("x", t)] == add t (.var "y")

-- The Pythagorean identity rewrites at the root.
#guard (normalize (Trigonometry.profileRules "default") 10
    (add (sq (sin t)) (sq (cos t)))).result == .int 1

-- Outermost-first: the root is tried before its arguments.
#guard (rewriteStep (Trigonometry.profileRules "default")
    (add (sq (sin t)) (sq (cos t)))).map (·.1) == some "trigonometry.pythagorean"

-- Every profile terminates on every catalogue pattern.
#guard Trigonometry.profiles.all fun p =>
  Trigonometry.catalog.all fun e =>
    (normalize (Trigonometry.profileRules p) 64 e.rule.lhs).normal

-- Regression: the v0.1 profiles cycle under the reference strategy.
#guard !(normalize [Trigonometry.sinAdd, Trigonometry.sinMulCos] 64 Trigonometry.sinAdd.lhs).normal
#guard !(normalize [Trigonometry.cosSub, Trigonometry.sinMulSin] 64 Trigonometry.cosSub.lhs).normal
#guard !(normalize [Trigonometry.cosTwoMul, Trigonometry.sinSq, Trigonometry.cosSq] 64
  Trigonometry.sinSq.lhs).normal

-- Every rule belongs to at least one profile, and every profile is non-empty.
#guard Trigonometry.catalog.all fun e => e.rule.profiles.all (· ∈ Trigonometry.profiles)
#guard Trigonometry.profiles.all fun p => !(Trigonometry.profileRules p).isEmpty

-- Every catalogue rule satisfies the closure condition of the soundness
-- theorem.
#guard Trigonometry.catalog.all fun e => e.rule.rhsClosed

-- The proved step bound covers the observed runs: on every catalogue pattern,
-- normalizing within the weight of the input reaches a normal form.
#guard Trigonometry.profiles.all fun p =>
  Trigonometry.catalog.all fun e =>
    (normalize (Trigonometry.profileRules p)
      ((Trigonometry.weight p).eval (fun _ => 0) e.rule.lhs) e.rule.lhs).normal

-- A rule of a profile decreases the weight of that profile.
#guard ((Trigonometry.weight "default").eval (fun _ => 0) Trigonometry.sinAdd.rhs) <
  (Trigonometry.weight "default").eval (fun _ => 0) Trigonometry.sinAdd.lhs

-- The opposite orientation does not: `sinMulCos` increases the weight of the
-- `default` profile, which is why the v0.1 profiles could cycle.
#guard ((Trigonometry.weight "default").eval (fun _ => 0) Trigonometry.sinMulCos.lhs) <
  (Trigonometry.weight "default").eval (fun _ => 0) Trigonometry.sinMulCos.rhs

end OSRTest.Rewrite
