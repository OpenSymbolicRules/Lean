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
calculus shapes.  A conditional rule is applied only when every condition,
with the match substituted, is closed rational arithmetic decided `true`
(`OSR/Decide.lean`: `Expr.ratEval?`, `Cond.decide?`, proved sound by
`Cond.decide?_sound`; `antideriv_instance_under`).  So `int(λt. t^3)` is
rewritten by the power rule (`3 ≠ -1`), while `int(λt. t^(-1))` (decided
false) and `int(λt. t^m)` (undecided) are left alone.  OpenSymbolicRules.jl
does the same (`decide_condition`), and the Conformance suite checks both.  `not_antiderivHoldsUnder` refutes a rule
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

### Third recursive batch

| Rule | v0.1 rule | ℝ | ℂ |
|---|---|---|---|
| `integration.partial_fractions_linear_quadratic` | 1.2.1.2 #79, `1/((d + e x)(a + c x²))` | proved | proved |
| `integration.partial_fractions_linear_trinomial` | 1.2.1.2 #78, `1/((d + e x)(a + b x + c x²))` | proved | proved |
| `integration.partial_fractions_power_weighted` | 1.1.3.4 #63, `(e x)ᵐ/((a + b xⁿ)(c + d xⁿ))` | proved | proved |
| `integration.sin_cos_double_angle` | 4.7.9 #68, `sin u cos u = sin(2u)/2` | proved | proved |
| `integration.partial_fractions_general` | 1.1.3.5 #2 | counterexample at `b c = a d` | counterexample |
| `integration.linear_factor_over_linear` | 1.1.1.4 #17 | counterexample at `b = 0` | counterexample |
| `integration.sin_trinomial_square`, `integration.cos_trinomial_square` | 4.1.13 #3, #4 | counterexample at `c = 0` (residual `sin/cos(…/(4c))`) | counterexample |
| `integration.binomial_ratio_negative_power` | 1.1.3.3 #14, `n < 0` | counterexample at `a = 0` | counterexample |
| `integration.power_log_log` | 3.5 #3 | counterexample (residual `1/log 1`) | counterexample |
| `integration.linear_times_two_powers` | 1.1.1.3 #8 | counterexample at `d = 0` | counterexample |
| `integration.power_log_binomial` | 3.4 #7 | counterexample (residual `…/0`) | counterexample |

### Fourth recursive batch

`OSR/IntegrationRec2.lean` holds 25 more rules, transcribed by a tool from
the converted v0.1 rules and checked by the Integration repository's
`scripts/v1_faithfulness.py` (which also checks every earlier rule).  One is
proved over ℝ and ℂ (`integration.split_log_linear_factor`, 3.3 #44, a
linearity split); 24 are refuted.  22 refutations share one template: the
conditions leave a coefficient free to vanish that the result divides by
(`b`, `d`, `g`, `h`, `m`, `q`, `c`, `d n`, `b² d² (m+n+2)(m+n+3)`), or, at
`n = 0`, a residual integrand divides by `d + e x`.  Two hold over ℂ only
in RUBI's reading of `Log` and are refuted over ℝ, where `log x` or
`log(d + e x)` is undefined at a point near which the integrand is defined
(3.3 #4, 3.1.3 #3).  The reduction of `(d + e x)^m/(a + c x²)` for `m < -1`
(1.2.1.2 #83, `integration.linear_power_over_quadratic`) is proved over ℝ
and ℂ.  Seven rules with integrands `F^(…)`, whose exponent
depends on `x`, are not migrated.

### Refutations found by a numerical search

Many RUBI exponents (`m`, `n`, `p`, …) are not listed in `FreeQ` but are
constrained by numeric predicates (`IntegerQ`, `IGtQ`, `GtQ`, …) that only
hold for numbers.  Declaring them independent of `x`, with an
`independence:` finding, brings 127 more rules into scope.  A numerical
search (development tool `handoff/refute_search.py`, not part of the
certified chain) evaluates the integrand, the result and the residual
integrands under the real definedness semantics of the fragment, for small
integer assignments satisfying the conditions, and proposes a counterexample
for 47 of them.  Each proposal is then generated as a Lean theorem per
domain; `OSR/IntegrationRec3.lean` keeps the 45 rules for which at least one
of them is proved (42 over both ℝ and ℂ, 3 over one domain only, the other
recorded as unproved). The initial pass left 82 rules to investigate:
some may be true, and need proofs.

`integration.linear_power_over_quadratic` is proved over ℂ but not
certified there: its condition `m < -1` uses `relation1#gt`, whose complex
reading is not an OpenMath mapping (registry).

### Further degenerate-coefficient cases

Five further rules are refuted over both ℝ and ℂ in
`OSR/IntegrationRec3.lean`. Each witness satisfies the original conditions
and has an integrand defined near `x = 1`, while the result is undefined
there. All omitted metavariables are zero:

| RUBI 4.16.1 rule | Nonzero metavariables |
|---|---|
| 1.2.2.4 #57 | `a = c = f = p = 1`, `b = e = m = -1` |
| 1.2.2.4 #58 | `c = f = p = 1`, `a = e = m = -1` |
| 2.1 #10 | `F = c = e = m = 1`, `b = d = g = p = -1` |
| 4.1.12 #45, #46 | `a = n = 1`, `m = p = 2` |

No condition is strengthened. The type and axiom audit checks the ten
refutation theorems, and `OSRTest/Integration.lean` checks that all five
catalogue entries remain refuted in both domains. The toolchain is Lean
4.35.0 with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

That batch brought Integration to 123 rules: 22 proved and 100 refuted over ℝ
(one unproved), 18 proved and 96 refuted over ℂ (nine unproved). Of the
complex proofs, 17 are certified. Fourteen other rules remain explicitly
reported as not migrated.

### Proof backlog: first proofs and refutations

The numerical classification (development tool, as above) left 50 candidates
behaving as true identities where defined, and 22 it could not sample. A
second, stricter pass (guards analysed exactly instead of sampled) settles
33 of them.

`OSR/IntegrationRec4.lean` proves five rules over ℝ and ℂ. They rewrite a
binomial with a negative integer exponent `n` as
`(a + b xⁿ)ᵖ = x^(n p) (b + a x^(-n))ᵖ` (`binom_core`, valid for `x ≠ 0`):

| RUBI 4.16.1 rule | Rule |
|---|---|
| 1.1.3.1 #5 | `integration.binomial_negative_power` |
| 4.1.11 #7, #8 | `integration.binomial_power_sin`, `integration.binomial_power_cos` |
| 4.1.11 #19, #20 | `integration.monomial_binomial_power_sin`, `integration.monomial_binomial_power_cos` |

`OSR/IntegrationRec5.lean` refutes 28 rules over both ℝ and ℂ: 1.1.1.3 #14,
1.1.1.4 #3, 1.1.3.5 #24 and #26, 1.2.1.2 #12, 1.2.1.3 #15 and #16,
1.2.2.2 #17, 1.2.2.4 #55, #56 and #59–#62, 2.3 #24, 3.1.2 #6, 3.1.3 #7
and #10, 3.1.4 #12, #13 and #18, 3.1.5 #8, #9 and #17, 4.1.11 #3 and #4,
4.1.13 #21 and #22. Each witness, recorded in the rule's finding, satisfies
the conditions, has an integrand defined near `x = 1`, and makes the result
undefined at `x = 1`. Ten further proposals could not be proved in either
domain and are left out.

That round brought Integration to 156 rules: 27 proved and 128 refuted over ℝ (one
unproved), 23 proved and 124 refuted over ℂ (nine unproved). Of the
complex proofs, 17 are certified: like
`integration.linear_power_over_quadratic`, the five new rules state `n < 0`
with `relation1#gt`, whose complex reading is not an OpenMath mapping. Fourteen other rules remain explicitly
reported as not migrated.

### Wider search grid

The first search filled the metavariables uniformly with `1`, `-1` or `2`,
and so missed witnesses needing an exponent `≤ -2` next to a vanishing
coefficient. The second pass also varies one metavariable over `-3…3` and
requires the integrand to be defined at several points near `t`, not only
at `t`. It found the following in the backlog, each refuted over ℝ and ℂ in
`OSR/IntegrationRec6.lean` (the omitted metavariables are zero, and the
result is undefined at `x = 1`):

| RUBI 4.16.1 rule | Nonzero metavariables |
|---|---|
| 1.2.2.1 #5 | `b = 1`, `p = -3` |
| 2.3 #23 | `a = c = d = e = 1`, `m = -3` (`F = 0`, so `log F` is undefined) |
| 2.3 #26 | `a = b = c = f = 1`, `m = -3` (`F = 0`) |
| 2.3 #35 | `F = a = b = d = e = g = 1`, `m = -3` |
| 3.1.1 #3 | `b = c = 2`, `p = -3` (`n = 0`) |
| 3.1.4 #9 | `b = c = e = p = r = 1`, `m = -3` |
| 3.1.4 #17, 3.1.5 #16 | `b = c = e = p = 1`, `q = -3` |
| 3.3 #12 | `b = c = e = f = g = q = 2`, `p = -3` |

That pass brought Integration to 165 rules: 27 proved and 137 refuted over ℝ
(one unproved), 23 proved and 133 refuted over ℂ (nine unproved).

### Backlog proofs

`OSR/IntegrationRec7.lean` proves four backlog rules over ℝ and ℂ, in
every interpretation with the needed trigonometric derivatives or
identities:

| RUBI 4.16.1 rule | Rule | Argument |
|---|---|---|
| 3.1.5 #15 | `integration.split_power_linear_log_over_x` | `(d + e x)^q = (d + e x)^(q-1) (d + e x)` for an integer `q ≥ 1` |
| 4.1.12 #35, #36 | `integration.power_sin_power_by_parts`, `integration.power_cos_power_by_parts` | integration by parts, for `m < -1` and `n > 0` |
| 4.7.9 #71 | `integration.power_over_trig_squares` | `2 (a + b cos² u + c sin² u) = 2a + b + c + (b - c) cos 2u` |

Their conditions use `relation1#gt`, so the complex proofs are not
certified.

Four logarithmic rules are proved over ℝ only, by integration by parts
(`hasDerivAt_log_monomial`: `d/dx log(c xⁿ) = n/x` wherever `c xⁿ > 0`,
including `x = 0`, where this forces `n = 0`):

| RUBI 4.16.1 rule | Rule |
|---|---|
| 3.1.3 #8 | `integration.quadratic_power_log_by_parts` |
| 3.1.5 #24 | `integration.power_log_times_power_log` |
| 4.7.8 #3, #4 | `integration.sin_power_log_reduction`, `integration.cos_power_log_reduction` |

RUBI 3.1.4 #16 states the same rule as 3.1.5 #15
(`integration.split_power_linear_log_over_x_monomial`), proved over ℝ and ℂ
by the same theorem.

Over ℂ they stay unproved: `ln` is defined for `z ≠ 0`, but the principal
logarithm is not differentiable across the negative real axis.

Integration now exports 174 rules: 36 proved and 137 refuted over ℝ (one
unproved), 28 proved and 133 refuted over ℂ (thirteen unproved). Of the
complex proofs, 17 are certified. Fourteen other rules remain explicitly
reported as not migrated. Of the 39 backlog rules, 21 are neither proved
nor refuted.

These further refutations expose coefficients that the converted rule's
conditions allow to vanish, although the result divides by them. RUBI may
handle degenerate cases through evaluation or rule ordering; an OSR v1 rule
is stated on its own.

The inventory excludes 739 rules whose result or conditions use a name the
pattern does not bind: 630 of them use the constants `E`, `ImaginaryI` or
`Pi`, which the converter left without semantics (Integration,
`docs/known-issues.md` §4).

## Next steps

- Conditions do not limit the inventory: 2,155 rules have only expressible
  conditions, but almost all of them have another `Int` in their result or
  unregistered heads (`Subst`, `Simp`, `Rt`, …).
- Further recursive rules are linear in their residual integrals, many
  with square roots (outside the complex fragment) or
  rational exponents (outside the fragment).
- A rewriter that continues inside residual integrals would let engines apply
  recursive rules: `AntiderivRecHolds` composes, since any antiderivative
  found for a residual integral may be substituted.
- An engine applying conditional rules needs a decision procedure for the
  conditions on the matched terms.
- Conditioned variants of the refuted rules (`c ≠ 0`, `b ≠ 0 ∧ n ≠ 0`) would
  be new rules, not migrations; they need a decision on provenance.
