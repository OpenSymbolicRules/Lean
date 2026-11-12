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

> for every assignment of the metavariables satisfying the rule's conditions
> and every point `t` near which `F` is defined, `G` is defined near `t` and
> `v ↦ G[x := v]` has derivative `F[x := t]` at `t` (`HasDerivAt`).

(`OSR.Calculus.AntiderivHoldsUnder`; without conditions it is
`AntiderivHolds`.)

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
calculus shapes.  Like the Algebra and Julia engines, the rewriter does not
apply a conditional rule: deciding a condition such as `m ≠ -1` on a symbolic
match needs a decision procedure.  `not_antiderivHoldsUnder` refutes a rule
from one assignment satisfying its conditions and one point at which the
integrand is defined nearby and the result is not.

## Residual integrals

Most RUBI rules have another `Int` in their result.  Such a rule becomes a
recursive antiderivative rule (`Shape.antiderivRec`, `OSR/IntegrationRec.lean`):
each residual integral `Int[H, x]` of the result is a hole variable `I1`, `I2`,
…, exported as `int(λx. H)(x)`, the form of the `calculus1#int` FMP
(Specification V1-E-002b).  Its statement, `AntiderivRecHolds`, reads:

> wherever `F` is defined near `t` (and the conditions hold), every residual
> integrand `H` is defined near `t`, and for **every** choice of functions
> with derivative `H(t)` at `t` in place of the residual integrals, the
> result is defined near `t` and has derivative `F(t)` at `t`.

So whatever antiderivatives a consumer later finds for the residual
integrals, the result is an antiderivative of `F`.  Requiring the residual
integrands to be defined keeps a rule from producing a meaningless integral,
even with a zero coefficient.  `not_antiderivRecHolds_integrand` and
`not_antiderivRecHolds_result` refute a recursive rule; the second uses
linear functions `w ↦ w · H(t)` as the chosen antiderivatives.  Neither the
reference rewriter nor OpenSymbolicRules.jl applies a recursive rule
(V1-R-005c): rewriting does not continue inside residual integrals yet.

## Encoding

The converted v0.1 terms are kept without simplification:

- an n-ary `Multiply` or `Add` becomes a left-nested chain of binary
  `arith1#times` or `arith1#plus`;
- `Power[u, -1]` stays a power with exponent `-1`;
- an optional wildcard (`c.`, `n.`, …) becomes an ordinary metavariable, so
  the v1 rule matches only the explicit form and not the instances with
  RUBI's default value (a loss of coverage, not of soundness);
- `FreeQ[{…}, x]` becomes the `independent` constraint of each listed
  metavariable, as in the Calculus set;
- `NeQ[a, b]` becomes the condition `a ≠ b` (`relation1#neq`), read
  semantically: both sides are defined and their values differ.  Mathematica
  tests instead that `a - b` is not possibly zero; conditions only mention
  independent metavariables (`CRule.conditionsOk`).

## Scope and results

A syntactic inventory of the corpus (`scripts/inventory_v1.py` in the
Integration repository) selected the rules with no `Int` in their result,
whose heads, after removal of the outer `Int`, are in the registry, and whose
conditions map to the fragment's conditions (`ne`, `gt`, `int`): twenty
rules, nine with `FreeQ` only and eleven with `NeQ`.  The predicates
`GtQ`, `LtQ`, `IntegerQ`, `IGtQ` and `ILtQ` are mapped too, but no rule
using them passes the other two filters.  These counts are inventory counts,
not migration claims.

| Rule | v0.1 rule | ℝ | ℂ |
|---|---|---|---|
| `integration.constant` | 9.1 Integrand simplification #8, `∫ a = a x` | proved | proved |
| `integration.log_monomial` | 3.1.1 #1, `∫ log(c xⁿ) = x log(c xⁿ) − n x` | proved | unproved (branch cut) |
| `integration.reciprocal` | 1.1.1.1 #1, `∫ 1/x = log x` | counterexample at `x = −1` | unproved (branch cut) |
| `integration.constant_times_linear` | 9.1 #9, `∫ a (b + c x) = a (b + c x)²/(2c)` | counterexample at `c = 0` | counterexample |
| `integration.log_linear_over_x` | 3.1.2 #1, `∫ (a + b log(c xⁿ))/x = (a + b log(c xⁿ))²/(2bn)` | counterexample at `b = n = 0` | counterexample |
| `integration.log_log_over_x` | 3.5 #2 | counterexample at `n = 0` | counterexample |
| `integration.power` | 1.1.1.1 #2, `∫ xᵐ = xᵐ⁺¹/(m+1)`, `m ≠ −1` | proved | proved |
| `integration.linear_power` | 1.1.1.1 #4, `∫ (a + b x)ᵐ`, `m ≠ −1` | counterexample at `b = 0` | counterexample |
| `integration.power_log_linear` | 3.1.2 #4, `∫ (d x)ᵐ (a + b log(c xⁿ))`, `m ≠ −1` | counterexample at `d = 0` | counterexample |
| `integration.sin_log` | 4.7.8 #1, `∫ sin(d (a + b log(c xⁿ)))` | proved | unproved (branch cut) |
| `integration.cos_log` | 4.7.8 #2, `∫ cos(d (a + b log(c xⁿ)))` | proved | unproved (branch cut) |
| `integration.power_sin_log` | 4.7.8 #11, `∫ (e x)ᵐ sin(…)` | counterexample at `e = 0` | counterexample |
| `integration.power_cos_log` | 4.7.8 #12, `∫ (e x)ᵐ cos(…)` | counterexample at `e = 0` | counterexample |

The seven other rules are not migrated: their integrands are powers with the
exponent `3/2` or with an exponent that depends on `x`, and the fragment
interprets `arith1#power` for integer exponents only.  The power rule
`∫ xᵐ` is certified for the integer values of `m`; for the others its
integrand is undefined in the fragment.

The counterexamples follow the rule policy: the v0.1 conditions are kept, and
a missing condition is recorded as a finding instead of being added.  RUBI
relies on Mathematica's evaluation, which simplifies an integrand with a
literal `b = 0` before matching; OSR v1 matching is syntactic.  In the same
way, RUBI reads `Log` as the complex logarithm, so `∫ 1/x = log x` has no real
reading on the negative axis.

### First recursive rules

Among the 272 recursive rules with registered heads, expressible conditions
and a result linear in its residual integrals, eleven without square roots or
fractional exponents were migrated first:

| Rule | v0.1 rule | ℝ | ℂ |
|---|---|---|---|
| `integration.sin_add_square`, `integration.cos_add_square` | 4.1.12 #3, #4, `sin/cos(c + d (e + f x)²)` | proved | proved |
| `integration.sin_add_power_over_x`, `integration.cos_add_power_over_x` | 4.1.12 #25, #26, `sin/cos(c + d xⁿ)/x` | proved | proved |
| `integration.power_sin_square`, `integration.power_cos_square` | 4.1.12 #39, #40, `xᵐ sin²/cos²(a + b xⁿ/2)` | proved | proved |
| `integration.log_linear_power` | 3.1.1 #2, `(a + b log(c xⁿ))ᵖ`, `p > 0`, `2p ∈ ℤ` | proved | unproved (branch cut) |
| `integration.log_power_log` | 3.5 #1, `log(c log(d xⁿ)ᵖ)` | counterexample at `p = 0` (residual `1/log 1`) | counterexample |
| `integration.sin_x_log_times_log`, `integration.cos_x_log_times_log` | 4.7.8 #45, #46 | counterexample at `a = 0` | counterexample |
| `integration.linear_times_quadratic_power` | 1.2.1.2 #14, `NeQ[p, -1]` | counterexample at `c = 0` | counterexample |

### Second recursive batch

Eleven more, chosen among the rules whose wildcards are all `FreeQ` (so that
no metavariable may depend on `x`) and whose result names nothing the pattern
does not bind:

| Rule | v0.1 rule | ℝ | ℂ |
|---|---|---|---|
| `integration.partial_fractions_linear` | 1.1.1.2 #3, `1/((a + b x)(c + d x))`, `b c - a d ≠ 0` | proved | proved |
| `integration.partial_fractions_power` | 1.1.3.3 #19, `1/((a + b xⁿ)(c + d xⁿ))` | proved | proved |
| `integration.split_linear_factor_binomial` | 1.1.3.5 #11 | proved | proved |
| `integration.split_linear_factor_quadratic` | 1.2.1.6 #13 | proved | proved |
| `integration.linear_sin_trinomial`, `integration.linear_cos_trinomial` | 4.1.13 #17, #18 | counterexample at `c = 0` | counterexample |
| `integration.linear_times_trinomial_power` | 1.2.1.2 #13 | counterexample at `c = 0` | counterexample |
| `integration.product_over_trinomial`, `integration.product_over_quadratic` | 1.2.1.3 #11, #12 | counterexample at `c = 0` | counterexample |
| `integration.power_ratio_split` | 1.1.3.5 #10 | counterexample at `d = 0` | counterexample |
| `integration.log_power_binomial` | 3.4 #1 | counterexample at `p = 0` (residual `xⁿ/0`) | counterexample |

Every refutation follows the same pattern: RUBI's conditions leave a
coefficient free to vanish, and the result divides by it.  In Mathematica,
an earlier rule of the load order catches the degenerate case first; an OSR
v1 rule is stated on its own.

The inventory excludes 739 rules whose result or conditions use a name the
pattern does not bind: 630 of them use the constants `E`, `ImaginaryI` or
`Pi`, which the converter left without semantics (Integration,
`docs/known-issues.md` §4).

## Next steps

- Conditions do not limit the inventory: 2,155 rules have only expressible
  conditions, but almost all of them have another `Int` in their result or
  unregistered heads (`Subst`, `Simp`, `Rt`, …).
- The other recursive rules: 250 more are linear in their residual
  integrals, many with square roots (outside the complex fragment) or
  rational exponents (outside the fragment).
- A rewriter that continues inside residual integrals would let engines apply
  recursive rules: `AntiderivRecHolds` composes, since any antiderivative
  found for a residual integral may be substituted.
- An engine applying conditional rules needs a decision procedure for the
  conditions on the matched terms.
- Conditioned variants of the refuted rules (`c ≠ 0`, `b ≠ 0 ∧ n ≠ 0`) would
  be new rules, not migrations; they need a decision on provenance.
