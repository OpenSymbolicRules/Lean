# Integration

`OSR/Integration.lean` holds the first rules migrated from the RUBI 4.16.1
corpus of `OpenSymbolicRules/Integration` (commit
`f84ed2a81702836c019e647e0a586b8d576ae7c6`, 6,257 rules in 188 nonempty
files).  They are exported as `integration.osr.json` with its report and
conformance cases.

## Statement

A RUBI rule `Int[F, x] := G` becomes the calculus rule
`int(λx. F) ⟶ λx. G`, with the OpenMath symbol `calculus1#int` applied to a
`fns1#lambda` binder (shape `antideriv` of `OSR.Calculus.CRule`).  Its
statement, `OSR.Calculus.AntiderivHolds`, reads:

> for every assignment of the metavariables and every point `t` near which
> `F` is defined, `G` is defined near `t` and `v ↦ G[x := v]` has derivative
> `F[x := t]` at `t` (`HasDerivAt`).

This is the CMP of `calculus1#int`, `diff(λy. int(λz. f(z))(y)) = f`, on the
interior of the domain of the integrand.  Two consequences:

- `G` must be defined on a whole neighbourhood of `t`, not only at `t`.
  Mathlib's functions are total (`Real.log (-1) = 0`, `Real.sqrt (-1) = 0`),
  so definedness at a single point would let a totalized value certify a
  derivative;
- an antiderivative is unique only up to a locally constant function, which
  the CD leaves open; the statement does not fix the constant.

The reference rewriter applies the rule at the root of an `int` term, renaming
the bound variable to the input's.  `antideriv_instance` proves the renamed
instance from the rule's statement, and `apply?_sound` covers the three
calculus shapes.  `not_antiderivHolds` refutes a rule from one assignment and
one point at which the integrand is defined nearby and the result is not.

## Encoding

The converted v0.1 terms are kept without simplification:

- an n-ary `Multiply` or `Add` becomes a left-nested chain of binary
  `arith1#times` or `arith1#plus`;
- `Power[u, -1]` stays a power with exponent `-1`;
- an optional wildcard (`c.`, `n.`, …) becomes an ordinary metavariable, so
  the v1 rule matches only the explicit form and not the instances with
  RUBI's default value (a loss of coverage, not of soundness);
- `FreeQ[{…}, x]` becomes the `independent` constraint of each listed
  metavariable, as in the Calculus set.

## Scope and results

A syntactic inventory of the corpus (`scripts/inventory_v1.py` in the
Integration repository) selected the rules whose only conditions
are `FreeQ` and whose heads, after removal of the outer `Int`, are in the
registry: nine rules.  These counts are inventory counts, not migration
claims.

| Rule | v0.1 rule | ℝ | ℂ |
|---|---|---|---|
| `integration.constant` | 9.1 Integrand simplification #8, `∫ a = a x` | proved | proved |
| `integration.log_monomial` | 3.1.1 #1, `∫ log(c xⁿ) = x log(c xⁿ) − n x` | proved | unproved (branch cut) |
| `integration.reciprocal` | 1.1.1.1 #1, `∫ 1/x = log x` | counterexample at `x = −1` | unproved (branch cut) |
| `integration.constant_times_linear` | 9.1 #9, `∫ a (b + c x) = a (b + c x)²/(2c)` | counterexample at `c = 0` | counterexample |
| `integration.log_linear_over_x` | 3.1.2 #1, `∫ (a + b log(c xⁿ))/x = (a + b log(c xⁿ))²/(2bn)` | counterexample at `b = n = 0` | counterexample |
| `integration.log_log_over_x` | 3.5 #2 | counterexample at `n = 0` | counterexample |

The three other rules are not migrated: their integrands are powers with the
exponent `3/2` or with an exponent that depends on `x`, and the fragment
interprets `arith1#power` for integer exponents only.

The counterexamples follow the rule policy: the v0.1 conditions are kept, and
a missing condition is recorded as a finding instead of being added.  RUBI
relies on Mathematica's evaluation, which simplifies an integrand with a
literal `b = 0` before matching; OSR v1 matching is syntactic.  In the same
way, RUBI reads `Log` as the complex logarithm, so `∫ 1/x = log x` has no real
reading on the negative axis.

## Next steps

- Further RUBI predicates (`EqQ`, `NeQ`, `IGtQ`, `IntegerQ`, `GtQ`, …), most
  of which map to the existing conditions, would widen the inventory.
- The rules whose result contains another `Int` (5,459) need a rewriter that
  rewrites inside results and a linearity statement.
- Conditioned variants of the refuted rules (`c ≠ 0`, `b ≠ 0 ∧ n ≠ 0`) would
  be new rules, not migrations; they need a decision on provenance.
