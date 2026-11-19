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
- `EqQ[a, b]` becomes the condition `a = b` (`relation1#eq`), read the same
  way: both sides are defined and their values are equal.

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

`OSR/IntegrationRec8.lean` proves 4.1.12 #47 and #48
(`integration.power_sin_power_reduction`, `integration.power_cos_power_reduction`)
over ℝ and ℂ: `∫ x^m sinᵖ(a + b xⁿ)` and its cosine analogue, integrated by
parts twice, for integers `p ≥ 2`, `n > 0`, `m < -2n + 1` and
`m + n + 1 ≠ 0` (a non-integer `p` leaves the integrand undefined, so the
statement is vacuous there). The derivative identity holds modulo
`sin² + cos² = 1`; the `linear_combination` coefficients were computed with
SymPy 1.14.0 (development aid) and are checked by Lean. Their complex
proofs are not certified: `p > 1` uses `relation1#gt`.

`OSR/IntegrationRec9.lean` refutes 4.1.12 #53 and #54, the reverse
reductions for `p < -1`, over ℝ and ℂ. Their results divide by
`b n (p + 1)`, and the conditions allow `b = 0`: at `a = 1` (`a = 0` for
#54), `b = 0`, `m = 2`, `n = 1` and `p = -3` the integrand `x² sin(1)⁻³`
(`x² cos(0)⁻³`) is defined everywhere, while the result is undefined at
`x = 1`. The search grid of `handoff/refute_search.py` did not reach this
assignment; it was found by reading the result and checked with the same
evaluator before the Lean proofs.

`OSR/IntegrationRec10.lean` proves the quadratic reductions 1.2.1.1 #7
(`integration.quadratic_power_reduction`) and 1.2.1.2 #11
(`integration.linear_quadratic_power_reduction`) over ℝ and ℂ, for integers
`p < -1`: with `Q = a + b x + c x²` and `D = b² - 4 a c ≠ 0`, they rest on
`(b + 2 c x)² - 4 c Q = D` and, with `L = b d - 2 a e + (2 c d - b e) x`,
`L Q' - 2 (2 c d - b e) Q = D (d + e x)`. Their complex proofs are not
certified (`p < -1` uses `relation1#gt`).

Six other backlog rules (1.2.2.3 #32, #33, #37 and #38; 1.2.2.8 #5 and
#6) require `p + 1/2` to be an integer. Only integer powers are defined in
the fragment, so their integrands are never defined and their statements
hold vacuously; they are left unproved rather than counted as proofs that no
engine could ever use.

`OSR/IntegrationRec11.lean` refutes two more rules whose results divide by
a coefficient the conditions allow to vanish. 1.2.2.2 #19 divides by `c`;
at `a = b = d = 1`, `c = 0` and `m = 4` the integrand `x⁴/(1 + x²)` is
defined on ℝ but the result is not. Over ℂ the same integrand is undefined
at `x = ±i`, so this refutation is real only. 3.1.4 #11 divides by
`d f (q + 1)`; at `f = 0`, `a = c = d = m = p = 1` and `q = -4` the integrand
`(0 x)¹ (1)⁻⁴ (1 + 0)¹` is defined everywhere and the result is not, in both
domains.

RUBI 2.3 #44 and #45 and 4.7.7 #3, #4, #7 and #8 contain `F^(polynomial)`.
In the fragment, a power is defined only for an integer exponent, so the
integrand is defined near a point only if the exponent is constant there.
For 2.3 #44 and #45 the conditions exclude that case, so the statements are
vacuous. For 4.7.7, `F < 0` makes `log F` undefined over ℝ in both the
condition and the result, so the conditions fail and the case is no
counterexample. These rules remain unproved.

`OSR/IntegrationRec12.lean` proves the quartic reduction 1.2.2.1 #4
(`integration.quartic_power_reduction`) over ℝ and ℂ for integers `p ≥ 1`,
from `(x Qᵖ)' + 2 p (2 a + b x²) Qᵖ⁻¹ = (4 p + 1) Qᵖ` with
`Q = a + b x² + c x⁴`; all powers are natural, so `Q` may vanish. The complex
proof is not certified (`p > 0` uses `relation1#gt`).

### Rules with `EqQ` conditions

`EqQ` was the only condition without a fragment counterpart in 296 rules
whose heads are registered. With `relation1#eq` (`Cond.eq`: both operands
defined and equal) they can be stated. 187 of them only have metavariables
that are `FreeQ` or numerically constrained, and 156 of those transcribe (31
use `Sqrt` or `Simplify`). The numerical search proposes a counterexample for
113; `OSR/IntegrationRec13.lean` and `OSR/IntegrationRec14.lean` prove 108 of
them over ℝ (38 without residual integrals, 70 with) and 102 also over ℂ. Six
real witnesses do not carry over to ℂ (mostly logarithms of negative
arguments, which the complex logarithm defines), and five proposals were not
proved in either domain; those are left out, as are the 43 rules without a
proposal.

Of the 43 rules without a proposal, six have a literal fractional exponent
in their pattern (vacuous in the fragment). A random-sampling search
(development aid) refutes 3.2.1 #7; 4.7.8 #47 and #48 divide by `a n`, and the
optional `a` may vanish, while their real integrands need `x > 0`, a guard the
search does not classify, so the witnesses (`a = 0`, `b = n = 1`, `x = 1`) were
written by hand (`OSR/IntegrationRec15.lean`, both domains).
`OSR/IntegrationRec16.lean` proves 1.1.1.2 #4 (`integration.linear_linear_power`)
over ℝ and ℂ: when `m + n + 2 = 0`,
`((a + b x)^(m+1) (c + d x)^(n+1))' = (m + 1) (b c - a d) (a + b x)^m (c + d x)^n`.
Its conditions use only `relation1#neq` and `relation1#eq`, so the complex
proof is certified, bringing the certified complex proofs to 18.

`OSR/IntegrationRec17.lean` proves 1.1.3.2 #68
(`integration.monomial_binomial_power_by_parts`) over ℝ and ℂ: integration by
parts of `x^m (a + b xⁿ)ᵖ` for an integer `p ≥ 1`, where the condition
`(m + 1)/n + p = 0` gives `m + 1 ≠ 0`; at `x = 0` the exponents are natural
(`zpow_add_of`). The complex proof is not certified (`p > 0`).

`OSR/IntegrationRec18.lean` proves seven rules that rewrite the integrand
into a residual integral, over ℝ and ℂ:

| RUBI 4.16.1 rule | Identity |
|---|---|
| 1.1.1.2 #2 | `(a + b x)(c + d x) = a c + b d x²` when `b c + a d = 0` |
| 1.1.1.3 #50 | the same, under a common integer power (`mul_zpow`) |
| 3.1.4 #1, 3.1.5 #2, 3.3 #21 | `x^q (d + e/x)^q = (e + d x)^q` for `x ≠ 0` |
| 1.1.3.7 #11, #18 | linearity: `(A + B x^m) F = A F + B x^m F` |

Six of the seven complex proofs are certified (24 in all); 1.1.1.3 #50 states
`a > 0` and `c > 0` with `relation1#gt`.

`OSR/IntegrationRec19.lean` refutes 4.7.9 #78 and #82 over ℝ and ℂ at a
non-integer point: with `a = c = 1` and `d = -1` (so `a c + d = 0`) the
integrand's denominator `sin x - x cos x` equals `π` at `x = π`, hence stays
nonzero nearby (continuity), while the residual integrands `1/sin²(x)` and
`1/(x sin x)` (#82 at `b = m = n = 1`) are undefined at `x = π`.

`OSR/IntegrationRec20.lean` settles five more `EqQ` rules. Four are proved
over ℝ and ℂ by a trigonometric identity under the integral:

| RUBI 4.16.1 rule | Identity |
|---|---|
| 4.7.9 #9, #10 | `cosⁿ u/(a + b sin u) = cosⁿ⁻² u (1/a - sin u/b)` when `a² = b²` (and with `sin`, `cos` exchanged), from `(b - a s)(a + b s) = a b (1 - s²)` |
| 4.7.7 #26, #27 | `f + f cos u = 2 f cos²(u/2)`, `f - f cos u = 2 f sin²(u/2)` |

Their conditions `n > 1` and `n < 0` use `relation1#gt`, so the complex
proofs are not certified. 4.7.7 #32 is refuted in both domains at `e = 1`
and the other metavariables `0`: the integrand `0⁰ sin(x)⁰ (0 + 0 cos x)⁰`
is defined everywhere, while the residual integrand `0⁰ tan(x/2)⁰` is
undefined at `x = π`.

`OSR/IntegrationRec21.lean` settles four more. 4.7.7 #34 and #35 split the
numerator, `h + i cos u = 2 i cos u + (h - i cos u)` (and with `sin`), and
hold over ℝ and ℂ without their conditions. 1.2.1.2 #54 and #59 are refuted
in both domains at `a = c = e = 1` (and `m = 2`, `p = -2` for #59), the
other metavariables `0`: `2 c d = b e` then allows `d = b = 0`, the
integrand stays defined near `x = 1`, and the result divides by `d` (#54)
or by `b (p + 1)` (#59). The numerical search cannot meet `EqQ` conditions
exactly, so these witnesses were chosen by hand.

`OSR/IntegrationRec22.lean` proves two more over ℝ and ℂ. 3.1.2 #8 writes
`∫ (d x)^m / log(c xⁿ)` as `(d x)^m / x^m · ∫ x^m / log(c xⁿ)` when
`m = n - 1`: the factor is `d^m` wherever `x ≠ 0`, and the integrand is never
defined at `x = 0` (`n ≥ 1` makes `log(c · 0ⁿ) = log 0`). 4.7.9 #80 is a
closed form, `∫ sin²(a x)/(c sin(a x) + d x cos(a x))² = 1/(d² x) +
sin(a x)/(a d x (d x cos(a x) + c sin(a x)))` when `a c + d = 0`; its
derivative is checked in Lean with `linear_combination`, using coefficients
computed by SymPy 1.14.0 modulo `sin² + cos² = 1` and `a c + d = 0`.

`OSR/IntegrationRec23.lean` settles three more `EqQ` rules:

| RUBI 4.16.1 rule | Result |
|---|---|
| 3.3 #15 | proved over ℝ and ℂ: `log(c/(d + e x)) = log(c/(2 d)) + log(2 d/(d + e x))` given `c/(2 d) > 0` (`Real.log_mul`; over ℂ the first factor is a positive real, `Complex.log_ofReal_mul`) |
| 1.2.1.2 #101 | proved over ℝ and ℂ: with `m = -2 p - 3`, the derivative identity reduces to `(b + 2 c x)² - 4 c (a + b x + c x²) = b² - 4 a c` |
| 1.2.1.2 #103 | refuted over ℝ and ℂ at `m = p = -1`, `a = b = e = 1`: the integrand `1/(x (1 + x))` is defined near `x = 1`, the result divides by `m + 1 = 0` |

`OSR/IntegrationRec24.lean` proves 1.1.3.2 #69 over ℝ and ℂ, a by-parts rule
for `x^m (a₁ + b₁ xⁿ)^p (a₂ + b₂ xⁿ)^p` when `a₂ b₁ + a₁ b₂ = 0` and
`(m + 1)/(2 n) + p = 0`, `p > 0`: then `b₁ (a₂ + b₂ xⁿ) + b₂ (a₁ + b₁ xⁿ) =
2 b₁ b₂ xⁿ`. The point `x = 0` is outside the domain: the condition needs
`n ≠ 0`, and either `n < 0` or `m = -2 n p - 1 < 0`.

`OSR/IntegrationRec25.lean` carries eight refutations to the domain where
they were "not established": 3.1.5 #33 to ℝ, and 3.4 #9, 4.7.6 #2,
1.2.2.2 #19 and 3.5 #14, #17, #22, #23 to ℂ. The witnesses are unchanged;
over ℂ the integrand is shown defined near `x = 1` by continuity where it
vanishes elsewhere (`1 + x²` at `±i`), and `log 2 ≠ 0` is
`Real.log 2 > 0` cast to ℂ. Two others, 3.2.3 #5 and 3.3 #40, stay unproved
over ℂ: their real witnesses use the logarithm of a negative number, which
is defined over ℂ.

### The branch cut of the complex logarithm

Most rules left unproved over ℂ involve `log`, which is defined for `z ≠ 0`
but jumps across the negative real axis: `log(-1) = π i`, while
`log z → -π i` as `z → -1` from below
(`Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero`, Mathlib).
An antiderivative is differentiable, hence continuous, so a rule is refuted
over ℂ wherever its integrand is defined near a point of the cut while its
result is `Ψ(x, log x)` with `Ψ(-1, π i) ≠ Ψ(-1, -π i)`
(`OSR.IntegrationRec26.not_continuous_clog`). Six rules are refuted this way:

| Rule | Witness | Result near the cut |
|---|---|---|
| `integration.reciprocal` | `x = -1` | `log x` |
| `integration.log_monomial` | `c = n = 1`, `x = -1` | `x log x - x` |
| `integration.sin_log`, `integration.cos_log` | `a = 0`, `b = c = d = n = 1`, `x = -1` | `(x sin(log x) ∓ x cos(log x))/2`; the jump is `sin(π i) = i sinh π ≠ 0` |
| `integration.log_linear_over_x_split` | `a = c = d = 1`, `x = -1` | `log x` |
| `integration.log_over_linear` | `a = c = d = 1`, `e = -1`, `x = 2` | `-log(1 - x)` |

`OSR/IntegrationRec27.lean` extends the argument to by-parts rules, whose
result is `Ψ(x, log x)` plus residual antiderivatives (chosen linear, hence
continuous; `not_continuous_clog_add`): `integration.log_linear_power`,
`power_log_times_power_log` (result `x log x - Φ(x)`),
`quadratic_power_log_by_parts` (`x log x/3 + …`), `sin_power_log_reduction`
and `cos_power_log_reduction` at `p = 2` (jump `4 cos(π i) sin(π i)/5`, with
`cos(π i) = cosh π` and `sin(π i) = i sinh π`), and 3.3 #40 (result `log x`).
3.2.3 #5, whose discontinuous factor multiplies residual integrals, needs
another choice of antiderivatives (below).

`OSR/IntegrationRec28.lean` refutes the last one, 3.2.3 #5, whose result is
`I₁ + B(x) (2 I₂ + I₃)` with `B = log(e (…)^r) - log((a+b x)^(p r)) -
log((c+d x)^(q r))`. At `e = -1`, `b = c = f = h = p = r = 1` (others `0`) the
integrand `log(-x)²/x` is defined near `x = -1` and `B = log(-x) - log x`
jumps there. Antiderivatives are free up to a constant; with linear ones and
`2 Φ₂ + Φ₃ = 2` at `-1`, a continuous result would make `B` continuous.

That left no statement unproved among the 320 rules.

### A wider pass over the registered-head rules

A new inventory of RUBI 4.16.1 (the committed v0.1 corpus) selected the rules
whose heads are all registered, whose conditions are expressible (`FreeQ`,
`NeQ`, `EqQ`, `GtQ`, `LtQ`, `IntegerQ`, `IntegersQ`, `IGtQ`, `ILtQ`), whose
metavariables are independent of `x` (`FreeQ` or numeric predicates), and
that were not yet considered: 213 rules. The numerical search proposed a
counterexample for 69; `OSR/IntegrationRec29.lean` keeps 39 rules refuted in
Lean, 38 in both domains and one over ℝ only (its real witness does not carry
over to ℂ). Twenty-two further refutations use `Sqrt`, which the converter in
progress maps to `arith1#root`; the committed faithfulness check does not
yet accept that convention, so they are held back.
The other 145 candidates (one, 3.3 #43, has a condition on `x` itself and is
left out), and 35 rules excluded for metavariables that may
depend on `x` (`u_`) and 18 whose conditions use `Simplify`, are the next
backlog.

`OSR/IntegrationRec30.lean` refutes 12 more in both domains: random sampling
of the 144 candidates without a grid proposal returned 17 proposals (four use
`Sqrt` and are held back, one did not survive Lean).

`OSR/IntegrationRec31.lean` proves the first two of the backlog over ℝ and ℂ,
1.2.4.1 #1 and 1.2.4.2 #1: `a x^q + b x^n + c x^r = (a + b + c) x^n` when
`q = n = r`.

`OSR/IntegrationRec32.lean` proves 1.2.3.1 #1 over ℝ and ℂ: for `n < 0`,
`(a + b xⁿ + c x²ⁿ)^p = x^(2 n p) (c + b x^(-n) + a x^(-2n))^p` (`trinom_core`).

`OSR/IntegrationRec33.lean` proves 1.1.3.4 #45 over ℝ and ℂ, a partial-fraction
split of `(e x)^m/((a + b xⁿ)(c + d xⁿ))` when `b c - a d ≠ 0`.

`OSR/IntegrationRec34.lean` proves 1.1.3.5 #41 and 1.1.3.6 #29 (with a factor
`x^m`) over ℝ and ℂ:
`(c + d x^(-n))^q = (d + c xⁿ)^q / x^(n q)` (`neg_flip`, for `x ≠ 0` or `n = 0`).

`OSR/IntegrationRec35.lean` proves 1.1.3.5 #42 and 1.1.3.6 #30 over ℝ and ℂ:
`(a + b xⁿ)^p = x^(n p) (b + a x^(-n))^p` (`pos_flip`) for the two binomials in
`xⁿ` when the third is in `x^(-n)`.

`OSR/IntegrationRec36.lean` proves 1.2.3.3 #56 and #57 over ℝ and ℂ by
linearity, `(A + B x^m) F = A F + B x^m F` under the integral.

### Strengthened variants and later batches

The strengthened variants of refuted rules and the proof batches that follow
are described in [Integration: strengthened variants and later proof
batches](integration-proofs.md).

Integration now exports 1506 rules: 443 proved and 1063 refuted over ℝ, 272
proved (135 certified), 376 refuted and 858 unproved over ℂ; 520 more RUBI
rules are reported as not migrated (see
[Integration: strengthened variants and later proof batches](integration-proofs.md)).

A numerical truth check of the remaining candidates (development tool,
finite differences with linear residual antiderivatives) finds 69 that
behave as true identities, the proof backlog, and 58 whose integrand was
never defined in the samples. Of these, 27 are genuinely outside the
fragment: a condition forces a half-integer exponent, or the integrand has
an exponent with denominator 2. They join the rules reported as not
migrated (41 in all). The other 31 carry `EqQ` conditions that random
sampling cannot meet. Of the
complex proofs, 28 are certified (the recent ones state `relation1#gt`
conditions). Fourteen other rules remain explicitly
reported as not migrated. Of the 39 backlog rules, 12 are neither proved
nor refuted: the six `p + 1/2 ∈ ℤ` rules, 2.3 #44 and #45, and the four
4.7.7 rules discussed above. The `EqQ` rules refuted here expose the same
pattern as the earlier batches: results dividing by coefficients that the
conditions allow to vanish.

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
- Prove the remaining strengthened variants found true numerically (about
  200), family by family.
