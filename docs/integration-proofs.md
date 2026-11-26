# Integration: strengthened variants and later proof batches

RUBI 7.3.7 #19 has a real counterexample: with `a = 3`, `b = c = 1` and
`x = -1`, the original condition holds and the integrand is defined locally,
but the result asks for the real logarithm of the negative value `artanh(-1/2)`.
The Lean theorem checks local definedness and the failure of the result's
domain condition. The complex case is unproved because the fragment does not
interpret complex square roots or `arctanh`.

RUBI 1.1.1.2 #21, the inverse square-root product integrated to an `arcosh`,
is proved over ℝ under its original conditions `a+c=0`, `b-d=0` and `a>0`.
Local definedness of the integrand entails `b*x > a`, which establishes the
required `arcosh` domain and `b ≠ 0`; these are derived, not added premises.
The complex case is unproved because the fragment does not interpret complex
square roots or `arccosh`.

RUBI 5.3.7 #19 has a real counterexample in the current interpretation: for
`a = 2`, `b = -1`, `c = 1`, the original condition `b + c² = 0` holds. The
integrand is defined near `x = -1`, but the result asks for the real
logarithm of `arctan(-1)`, which is negative. The compiled theorem
`OSR.IntegrationCandidate.rubi537r19_counterexample_real` formalizes the
complete local-definedness statement. Its complex case is unproved: the
current fragment does not interpret complex square roots, so a proof there
would not establish the intended identity. The source rule remains unchanged.

This page continues [Integration](integration.md): the strengthened variants
of refuted rules, and the proofs and refutations added batch by batch after
the first backlog. The counts of the current catalogue are on the
[Integration](integration.md) page.

## Strengthened variants

Most refutations (about 220 of 318) come from a degenerate coefficient: at
`b = 0`, `c = 0` or `m = -1` the integrand is defined everywhere while the
result divides by zero. RUBI never reaches these cases, because an earlier
rule or evaluation handles them; an OSR v1 rule is stated on its own. A
*strengthened variant* (Specification V1-R-005e) is a new rule with the id of
the rule as stated plus `_nondegenerate`, the same `legacy_id`, the same
pattern and replacement, and the converted RUBI conditions followed by the
missing non-degeneracy condition, declared in a `strengthened:` finding. The
refuted rule as stated stays in the catalogue with its counterexample, and
the Integration faithfulness check counts strengthened rules separately.

`OSR/IntegrationRec37.lean` proves the first four over ℝ and ℂ:

| Rule as stated | Added condition | Variant |
|---|---|---|
| 1.1.1.1 #4 `∫ (a + b x)^m` | `b (m + 1) ≠ 0` | `integration.linear_power_nondegenerate` |
| 9.1 #9 `∫ a (b + c x)` | `2 c ≠ 0` | `integration.constant_times_linear_nondegenerate` |
| 4.1.13 #11 `∫ (d + e x) sin(a + b x + c x²)` | `2 c ≠ 0` | `integration.rubi_4_1_13_r11_nondegenerate` |
| 4.1.13 #12 `∫ (d + e x) cos(a + b x + c x²)` | `2 c ≠ 0` | `integration.rubi_4_1_13_r12_nondegenerate` |

`OSR/IntegrationRec38.lean` proves four binomial variants over ℝ and ℂ, with
integer exponents (`zpow`) and the points where a negative power is undefined
excluded by the definedness of the integrand:

| Rule as stated | Added condition | Variant |
|---|---|---|
| 1.1.1.2 #1 `∫ (a + b x)^m (c + d x)`, `a d = b c (m + 2)` | `b (m + 2) ≠ 0` | `integration.rubi_1_1_1_2_r1_nondegenerate` |
| 1.1.3.2 #3 `∫ x^m (a + b xⁿ)^p`, `m = n - 1` | `b n (p + 1) ≠ 0` | `integration.rubi_1_1_3_2_r3_nondegenerate` |
| 1.1.3.1 #3 `∫ (a + b xⁿ)^p`, `1/n + p + 1 = 0` | `a ≠ 0` | `integration.rubi_1_1_3_1_r3_nondegenerate` |
| 1.1.3.2 #6 `∫ (c x)^m (a + b xⁿ)^p`, `(m + 1)/n + p + 1 = 0` | `a c (m + 1) ≠ 0` | `integration.rubi_1_1_3_2_r6_nondegenerate` |

`OSR/IntegrationRec39.lean` proves two variants with a second binomial factor,
where `b c - a d ≠ 0` and the `EqQ` condition exclude `n = 0`:

| Rule as stated | Added condition | Variant |
|---|---|---|
| 1.1.3.3 #10 `∫ (a + b xⁿ)^p (c + d xⁿ)` | `a ≠ 0` | `integration.rubi_1_1_3_3_r10_nondegenerate` |
| 1.1.3.4 #14 `∫ (e x)^m (a + b xⁿ)^p (c + d xⁿ)` | `a e (m + 1) ≠ 0` | `integration.rubi_1_1_3_4_r14_nondegenerate` |

`OSR/IntegrationRec40.lean` proves three variants on quadratic trinomials:

| Rule as stated | Added condition | Variant |
|---|---|---|
| 1.2.1.2 #4 `∫ (d + e x) (a + b x + c x²)^p`, `2 c d = b e` | `b (p + 1) ≠ 0` | `integration.rubi_1_2_1_2_r4_nondegenerate` |
| 1.2.1.3 #1 `∫ (e x)^m (f + g x) (b x + c x²)^p` | `c (m + 2 p + 2) ≠ 0` | `integration.rubi_1_2_1_3_r1_nondegenerate` |
| 1.2.1.4 #1 `∫ x^m (f + g x)^n (b x + c x²)` | `g (m + n + 3) ≠ 0` | `integration.rubi_1_2_1_4_r1_nondegenerate` |

`OSR/IntegrationRec41.lean` proves two more:

| Rule as stated | Added condition | Variant |
|---|---|---|
| 1.1.1.3 #2 `∫ (a + b x) (c + d x)^n (e + f x)^p` | `d f (n + p + 2) ≠ 0` | `integration.rubi_1_1_1_3_r2_nondegenerate` |
| 1.2.1.1 #3 `∫ (a + b x + c x²)^p`, `b² = 4 a c` | `2 c (2 p + 1) ≠ 0` | `integration.rubi_1_2_1_1_r3_nondegenerate` |

`OSR/IntegrationRec42.lean` proves five more:

| Rule as stated | Added condition | Variant |
|---|---|---|
| 1.2.1.2 #55 `∫ (d + e x)^m (a + b x + c x²)^p` | `e (p + 1) (b² - 4 a c) ≠ 0` | `integration.rubi_1_2_1_2_r55_nondegenerate` |
| 4.1.12 #81 `∫ x^m sin(a + b xⁿ)^p cos(a + b xⁿ)`, `m = n - 1` | `b n (p + 1) ≠ 0` | `integration.rubi_4_1_12_r81_nondegenerate` |
| 4.1.12 #82 `∫ x^m cos(a + b xⁿ)^p sin(a + b xⁿ)`, `m = n - 1` | `b n (p + 1) ≠ 0` | `integration.rubi_4_1_12_r82_nondegenerate` |
| 1.2.1.4 #65 `∫ x² (d + e x)^m (a + b x + c x²)^p` | `c e (m + 2 p + 3) ≠ 0` | `integration.rubi_1_2_1_4_r65_nondegenerate` |
| 1.2.1.4 #66 `∫ x² (d + e x)^m (a + c x²)^p` | `c e (m + 2 p + 3) ≠ 0` | `integration.rubi_1_2_1_4_r66_nondegenerate` |

`OSR/IntegrationRec43.lean` proves two more:

| Rule as stated | Added condition | Variant |
|---|---|---|
| 1.2.3.5 #2 `∫ (d + e xⁿ + f x²ⁿ) (a + b xⁿ + c x²ⁿ)^p` | `a ≠ 0` | `integration.rubi_1_2_3_5_r2_nondegenerate` |
| 1.2.1.3 #14 `∫ (d + e x) (f + g x) (a + c x²)^p` | `2 c (p + 1) (2 p + 3) ≠ 0` | `integration.rubi_1_2_1_3_r14_nondegenerate` |

`OSR/IntegrationRec44.lean` proves two more:

| Rule as stated | Added condition | Variant |
|---|---|---|
| 1.2.1.3 #13 `∫ (d + e x) (f + g x) (a + b x + c x²)^p` | `2 c² (p + 1) (2 p + 3) ≠ 0` | `integration.rubi_1_2_1_3_r13_nondegenerate` |
| 1.1.1.7 #6 `∫ x^m (a₁ + b₁ xⁿ)^p (a₂ + b₂ xⁿ)^p`, `m = 2 n - 1` | `2 b₁ b₂ n (p + 1) ≠ 0` | `integration.rubi_1_1_1_7_r6_nondegenerate` |

`OSR/IntegrationRec45.lean` proves 1.1.1.3 #9 with
`d² f² (n + p + 2) (n + p + 3) ≠ 0`, and 1.2.1.3 #25 with two appended
conditions, `c (m + 2 p + 2) ≠ 0` and `e ≠ 0`
(`integration.rubi_1_1_1_3_r9_nondegenerate`,
`integration.rubi_1_2_1_3_r25_nondegenerate`). `OSR/IntegrationRec46.lean`
proves 1.2.1.3 #24 the same way, with `c (m + 2 p + 2) ≠ 0` and `e ≠ 0`
(`integration.rubi_1_2_1_3_r24_nondegenerate`): with the first condition
alone it is false at `e = d = m = 0`, like #25.

`OSR/IntegrationRec47.lean` begins the strengthened variants of rules with
residual integrals, stated for every choice of antiderivatives of the
residual integrands: 1.2.1.2 #20 with `e^p ≠ 0`, #103 with
`(m + 1) (c d² - b d e + a e²) ≠ 0` and #104 with `(m + 1) (c d² + a e²) ≠ 0`.
`OSR/IntegrationRec48.lean` proves 1.2.1.2 #1 and 1.2.1.3 #20 with `d ≠ 0` and
`e ≠ 0` (the converted condition `c d² - b d e + a e² = 0` factors the
trinomial as `(d + e x) (a/d + c x/e)`), and 1.2.1.3 #19 with `e^p ≠ 0`.

## Strengthened variants checked numerically

`OSR/IntegrationNum1.lean` distributed strengthened variants before their
proofs (Specification V1-R-005e): both domains unproved, and a `numerical:`
finding recording the evidence. The catalogue currently retains 740 unproved entries.
Each candidate was checked over ℝ
by central differences, each residual integral replaced by a function whose
derivative is the residual integrand at the point, on assignments where each
metavariable is 0 with probability 0.4 (otherwise an integer between -3 and
3), and kept only with no failure on at least 50 points; a point where the
integrand is defined but a residual integrand or the result is not counts as
a failure. This adversarial sampling rejects the false candidates 1.2.1.3 #24
and #25 that a uniform sampling had accepted, and 44 others, mostly
logarithmic rules whose results need sign conditions over ℝ; it errs on the
safe side (4.1.12 #81, proved above, fails at 2 of 721 points through
rounding). A second pass searches,
for sampled assignments, the real zeros of every base raised to a negative
or non-integer power in the residual integrands and the result: if the
integrand is defined around such a zero, a residual integrand or the result
is not, and the variant fails. This pole probe, which fixed sample points
cannot replace, removed 11 variants after their first distribution (for
example 1.1.3.3 #18 at `n = 1`, `p = 0`, where `(a + b x)⁻¹` appears in a residual
integrand while the integrand `1/(c + d x)` is defined). The complex domain
is not checked. The entries live in their own module with their own
well-formedness theorem; `Integration.catalog` is `catalogVerified` followed
by them. When a variant is proved, its definition stays in
`OSR/IntegrationNum1.lean` and its entry moves to the verified catalogue:
`OSR/IntegrationRec49.lean` proves 1.2.2.3 #7 and #8 (the quartic factors as
`(d + e x²) (a/d + c x²/e)`) and 1.1.3.3 #15, `OSR/IntegrationRec50.lean`
proves 1.1.3.4 #24, `OSR/IntegrationRec51.lean` 1.1.3.4 #17, 1.2.1.3 #35 and
1.2.2.4 #11 and #12, and `OSR/IntegrationRec52.lean` 1.2.3.3 #12 with `d ≠ 0`
and `e ≠ 0` (`a + c x²ⁿ` factors as `(d + e xⁿ) (a/d + c xⁿ/e)`) and 1.2.3.3
#19 and #20 with `e (n (q + 2) + 1) ≠ 0`. `OSR/IntegrationRec197.lean`
proves 1.1.3.3 #11 over ℝ and ℂ: the opposite linear coefficients make the
product of the two binomials a binomial in `x^n`, and `a1 * a2 ≠ 0` justifies
the constant inverse in the result. `OSR/IntegrationRec198.lean` proves
1.1.3.3 #8 over ℝ and ℂ: its two equality conditions cancel the `x^n` and
`x^(2n)` coefficients in the derivative. `OSR/IntegrationRec199.lean` proves
1.1.3.2 #4 over ℝ and ℂ using the cancellation of the cross term in the
product of the two binomials. `OSR/IntegrationRec200.lean` proves 1.1.3.2 #7
over ℝ and ℂ using the same cross-term cancellation and the exponent condition.
`OSR/IntegrationRec201.lean` proves the recursive rule 1.1.1.3 #19, for every
choice of antiderivative of the residual integrand.
`OSR/IntegrationRec202.lean` proves 1.1.3.4 #15 over ℝ and ℂ by applying
the binomial product identity with a monomial factor.
`OSR/IntegrationRec203.lean` proves the recursive rule 1.1.3.4 #16 over ℝ and
ℂ, including the scaled residual integral and its definedness. The complex
proof is not exported as certified because the rule's mapping assurance for
that domain is unsupported.
The derived rule `integration.rubi_1_1_3_4_r16_order_free` retains the same
expressions and matching constraints with `a*e*(m + 1) ≠ 0` and
`m + n*(p + 1) + 1 = 0`. It is proved over ℝ and ℂ with reviewed mappings;
the original strengthened conditions imply these conditions.
`OSR/IntegrationRec204.lean` proves the recursive rule 1.1.3.4 #27, including
the polynomial residual integrand and the scaling of integer powers. Its
complex mapping is likewise unsupported, so the complex proof is not certified.
The separate derived rule `integration.rubi_1_1_3_4_r27_order_free` retains
the same expressions and matching constraints and needs only
`a*e*(m + 1) ≠ 0`. Its mapping is reviewed over ℝ and ℂ; the original
strengthened conditions imply its condition, and that rule remains catalogued.
`OSR/IntegrationRec207.lean` proves the strengthened substitution rule 3.1.2
#2 over ℝ, including the local definedness of the substitution and residual
integrand. The original rule remains refuted over ℝ. `OSR/IntegrationRec208.lean`
refutes the strengthened rule over ℂ at the principal logarithm's branch cut:
with `a = p = 0`, `b = c = n = 1` and `x = -1`, the result is discontinuous.
`OSR/IntegrationRec209.lean` proves the strengthened substitution rule 3.1.2
#7 over ℝ and ℂ, including the local definedness of the residual integrand.
The proof differentiates the integer-power substitution and does not require
differentiability of the complex logarithm at its branch cut.
`OSR/IntegrationRec210.lean`, `OSR/IntegrationRec211.lean` and
`OSR/IntegrationRec212.lean` prove 18 strengthened variants whose result has no
residual integral (shape `antideriv`), so their proofs differentiate the closed
result directly. Over ℝ and ℂ: 4.1.1.1 #2, #6 and #11, 4.1.2.1 #1, 4.1.4.1 #2,
4.1.7 #1, 4.3.2.1 #3 and 6.1.13 #7 and #8. Over ℝ only: the inverse tangent
rules 5.3.4 #15 and #16 and 5.3.6 #13 and #55 (Mathlib has no derivative of
`Complex.arctan` at this revision), and 4.5.1.1 #4 and the inverse hyperbolic
tangent rules 7.3.1 #35 and #36 and 7.3.4 #15 and #16, whose cosecant or
inverse hyperbolic tangent has no complex interpretation in the fragment (the
complex statement is vacuous and is not recorded as proved). The 7.3.4 rules
have the same statement as their 7.3.1 twins and reuse their proofs. These
variants leave `OSR.IntegrationNum1`'s unproved set through
`Integration.promotedVariants` and are catalogued with the verified rules,
without their `numerical:` finding.
`OSR/IntegrationRec213.lean`, `OSR/IntegrationRec214.lean` and
`OSR/IntegrationRec215.lean` prove 18 recursive inverse hyperbolic tangent
variants over ℝ, integrating `a + b artanh(c x)` (or `artanh(1/(c x))`) by
parts against powers of `d + e x` or `d + e x²`: 7.3.1 #17, #18, #29, #47,
#69, #73, #79, #123 and #124, each with its 7.3.3 or 7.3.4 twin of the same
statement (7.3.3 #9 and #10, 7.3.4 #9, #27, #49, #53, #59, #103 and #104).
`OSR.IntegrationRec215.hasDerivAt_artanh_mul` and `hasDerivAt_artanh_inv` give
both arguments the derivative `c / (1 - c² x²)`. The complex statements are
vacuous (no complex interpretation of `transc1#arctanh`) and stay unproved.
`OSR/IntegrationRec216.lean` proves the `artanh(1/(c x))` companions 7.3.1
#70, #74 and #80 (with 7.3.4 #50, #54 and #60) on `|c x| > 1`.
`OSR/IntegrationRec217.lean` proves 7.3.1 #65–#68 (with 7.3.4 #45–#48), whose
results are constant-coefficient combinations of two residual integrals that
move `x²` between the integrands; the inverse hyperbolic tangent factor is
carried unchanged.
`OSR/IntegrationRec218.lean` to `OSR/IntegrationRec221.lean` prove 7.3.1 #85 and
#86 (`x² (a + b artanh)^p / (d + e x²)²`), #43 and #44 (`(a + b artanh)^p /
(d + e x²)²`), #83 (`x² (d + e x²)^q (a + b artanh)`, `q < -1`) and #87
(`(f x)^m (d + e x²)^q (a + b artanh)` with `m + 2q + 2 = 0`), each with its
7.3.4 twin, over ℝ.
`OSR/IntegrationRec222.lean` proves 7.3.1 #94 (with 7.3.4 #74), the
`artanh(1/(c x))` rule with `m + 2q + 3 = 0`, where `m` and `q` may be negative.
`OSR/IntegrationRec205.lean` and `OSR/IntegrationRec206.lean` prove the
recursive rules 1.1.3.4 #28 and #29, respectively, including their residual
integrands and definedness conditions. Both complex proofs are exported as
uncertified because their complex mapping assurance is unsupported.
For #28 the same module proves `integration.rubi_1_1_3_4_r28_order_free`, a
separate derived rule with the same expressions and matching constraints and
only the nonzero-denominator condition. Its complex mapping is certifiable;
the original strengthened rule and its unsupported complex order mapping are
unchanged. Integer-power definedness remains part of the semantics even though
the generalized rule does not add explicit integer conditions.
For #29 the separate derived rule `integration.rubi_1_1_3_4_r29_order_free`
retains its expressions and matching constraints while requiring `e ≠ 0` and
`b*e^(n + 1)*(m + n*(p + 2) + 1) ≠ 0`. Its proof covers negative integer
exponents and both domains have reviewed symbol mappings. The original
strengthened rule implies these conditions and remains separately catalogued.
`OSR/IntegrationRec53.lean` proves
1.2.1.6 #5 to #8 with `a ≠ 0` and `c ≠ 0` (the converted conditions make
`(g + h x) (d + e x + f x²)` equal to `(d g/a + f h x/c) (a + b x + c x²)`; when
`h = 0` they force `g = 0`) and 1.2.1.6 #10 with `e ≠ 0` and `f ≠ 0` (`x (a + c x²)`
equals `(a/e + c x/f) (e x + f x²)`). `OSR/IntegrationRec54.lean` proves 1.2.1.6
#9 (`x (a + b x + c x²) = (a/e + c x/f) (e x + f x²)`), 1.2.1.3 #36
(`a + b x + c x² = (f + g x) (a/f + c x/g)`) and 1.2.2.4 #55 to #58, whose
partial fractions in `x²` rest on identities such as
`(a e + c d x²) (d + e x²) - (c d² + a e²) x² = d e (a + c x⁴)`; the
converted conditions `p > 0` and `m < 0` make the residual integrands
defined wherever the integrand is (over ℂ these four are proved but not
certified: the order conditions have no certified mapping there).
`OSR/IntegrationRec55.lean` proves 1.1.1.3 #12 and 1.1.1.4 #38 (partial
fractions in `(a + b x) (c + d x)` with `p > 0`, from
`(b e - a f) (c + d x) - (d e - c f) (a + b x) = (b c - a d) (e + f x)`) and
1.2.1.2 #12 and 1.2.1.3 #16 (the reduction of `(a + c x²)^p` for `p < -1`);
over ℂ these four are not certified either, for the same reason.
`OSR/IntegrationRec56.lean` proves the reductions 1.2.1.3 #15 (`p < -1`),
1.2.1.1 #5 (`p > 0`, from `(b + 2 c x)² - (b² - 4 a c) = 4 c (a + b x + c x²)`)
and 1.2.2.2 #17 (`m < -1`, from `(a + b x² + c x⁴) - x² (b + c x²) = a`);
they are not certified over ℂ either. `OSR/IntegrationRec57.lean` proves the
reduction 1.2.2.1 #5 of `(a + b x² + c x⁴)^p` for `p < -1` and 1.2.1.2 #102,
where `m + 2 p + 3 = 0` and `p < -1` make `m ≥ 1` (not certified over ℂ).
`OSR/IntegrationRec58.lean` proves the reductions 1.1.1.3 #13 (`p > 1`) and
#14 (`p < -1`) of `(e + f x)^p / ((a + b x) (c + d x))`, from
`f² (a + b x) (c + d x) + R(x) = b d (e + f x)²` and its analogue (not
certified over ℂ). `OSR/IntegrationRec59.lean` proves 1.1.3.5 #24, #25 and
#26, which split `(c + d x²)^q (e + f x²)^r / (a + b x²)` by polynomial
identities in `x²` such as `d (a + b x²) + (b c - a d) = b (c + d x²)` (not
certified over ℂ). `OSR/IntegrationRec60.lean` proves 1.1.3.5 #30 (the same
identity in `xⁿ`, with `p < 0` and `q > 0`) and 1.2.1.2 #43 and #44
(`m > 1`), whose derivative identity is `(m - 1)` times the converted
condition `c d² - b d e + a e² = 0` (not certified over ℂ).
`OSR/IntegrationRec61.lean` proves 1.2.1.2 #45 (`m < 0`, identity `-m` times
the condition) and #39 (`m > 0`, `p < -1`, identity `2 (b + 2 c x) (p + 1)`
times the condition); not certified over ℂ. `OSR/IntegrationRec62.lean`
proves 1.2.1.2 #54, the partial fractions of `1 / ((d + e x) (a + b x + c x²))`
when `2 c d = b e` (then `b (d + e x) = d (b + 2 c x)`), over fields of
characteristic zero. `OSR/IntegrationRec63.lean` proves the first
trigonometric variants checked numerically: 4.7.9 #1, #2, #25 and #26, from
`S / (a + b S) = 1/b - (a/b) / (a + b S)` with `S` a sine or cosine of
`c + d x`, and 4.7.6 #1, #2, #16 and #17, integrations by parts of
`(c + d x)^m sinⁿ cos` and its companions with `m > 0`; the derivatives of
sine and cosine are hypotheses instantiated by Mathlib over ℝ and ℂ (not
certified over ℂ). `OSR/IntegrationRec64.lean` proves 4.1.13 #1 and #2, where
`b² = 4 a c` makes `(b + 2 c x)² / (4 c)` equal to `a + b x + c x²` (certified
over ℝ and ℂ), and the integrations by parts 4.1.13 #13 to #16 and #19 to #22
of `(d + e x)^m` times the sine or cosine of `a + b x + c x²`, from
`e (b + 2 c x) = (b e - 2 c d) + 2 c (d + e x)` (not certified over ℂ).
`OSR/IntegrationRec65.lean` proves 4.7.9 #11 and #12, which split
`cos² / (a + b sin)` and its mirror with `sin² + cos² = 1` (a hypothesis
instantiated by Mathlib; not certified over ℂ), and 2.3 #32 and #33, whose
exponents agree: `e + f (a + b x)/(c + d x)` is `e + f b/d` when `b c = a d`
and `(d e + b f)/d - f (b c - a d)/(d (c + d x))` in general (certified over
ℝ and ℂ). `OSR/IntegrationRec66.lean` proves the logarithmic splittings 3.1.4
#9, #17 and #18 and 3.1.5 #13, #16 and #17, where `a + b log (c xⁿ)` is an
atom and the identities are rational, such as `(d + e x)/x - e = d/x` (not
certified over ℂ). `OSR/IntegrationRec67.lean` proves 4.7.9 #16, #27 and #30,
which split quotients involving `tan` with `tan cos = sin` where `tan` is
defined (a hypothesis instantiated over ℝ and ℂ; not certified over ℂ).
`OSR/IntegrationRec68.lean` proves 4.1.12 #33 and #34, integrations by parts
of `(e x)^m` times the sine or cosine of `c + d xⁿ` with `n > 0` and
`m + 1 > n` (not certified over ℂ). `OSR/IntegrationRec69.lean` proves over
ℝ only 3.1.1 #3 and 3.1.2 #5 and #6, reductions of `(a + b log (c xⁿ))^p`
from `x (n/x) = n`: the proofs use the real logarithm, which is not
differentiable on the complex branch cut, so the complex domain stays
unproved and a `domain:` finding replaces the `numerical:` one.
`OSR/IntegrationRec70.lean` proves over ℝ 3.1.4 #12 and 3.1.5 #8,
integrations by parts of `(f x)^m (d + e x)^q (a + b log (c xⁿ))`, and
`OSR/IntegrationRec71.lean` 3.1.4 #2 and 3.1.5 #3, those of
`(f x)^m (d + e xʳ)^q (a + b log (c xⁿ))` when `m + r (q + 1) + 1 = 0`;
`OSR/IntegrationRec72.lean` proves over ℝ the variant of
`log_power_over_linear_square`, from `d/dx [x / (d (d + e x))] = 1/(d + e x)²`,
and `OSR/IntegrationRec73.lean` 3.1.3 #1, the integration by parts of
`(d + e xʳ)^q (a + b log (c xⁿ))` when `r (q + 1) + 1 = 0`;
`OSR/IntegrationRec74.lean` proves over ℝ 3.1.3 #10, 3.1.4 #13 and 3.1.5 #9,
integrations by parts with `(d + e x²)^q` and `q < -1`, from
`2 (q + 1) ((d + e x²) - e x²) = 2 (q + 1) d`. The verified catalogue now
has six parts of at most 100 entries. `OSR/IntegrationRec75.lean` proves over
ℝ 3.1.3 #7, the integration by parts of `(d + e x)^q (a + b log (c xⁿ))^p`
with `p < -1` and `q > 0`, and `OSR/IntegrationRec76.lean` 4.7.8 #47 and #48,
from `d/dx (a xⁿ log (b x)) = xⁿ⁻¹ (a n log (b x) + a)`, and
`OSR/IntegrationRec77.lean` 3.1.2 #3, where `a (m + 1) = b n`, and
`OSR/IntegrationRec78.lean` 3.1.5 #28, the integration by parts of
`(g x)^m (a + b log (c xⁿ))^p (d + e log (f xʳ))^q`, and
`OSR/IntegrationRec79.lean` 3.5 #16 and #21, where `r = q - 1` and
`d/dx (a xᵐ + b log (c xⁿ)^q) = a m xᵐ⁻¹ + b q n log (c xⁿ)^(q-1)/x`.
`OSR/IntegrationRec80.lean` proves, over ℝ and ℂ, 1.2.3.1 #5, the reduction
of `(a + b xⁿ + c x²ⁿ)^p` for `p < -1` (not certified over ℂ).
`OSR/IntegrationRec81.lean` proves, over ℝ and ℂ, 2.1 #9 and #10, the
reductions of `(c + d x)^m (a + b (F^(g (e + f x)))ⁿ)^p` that split off the
constant `a` (not certified over ℂ).
The last twelve follow. Over ℝ and ℂ: `OSR/IntegrationRec82.lean` proves
4.1.12 #43 and #44, the reductions of `x^m sin(a + b xⁿ)^p` and of the cosine
analogue for `m = 2 n - 1` and `p > 1` (with `sin² + cos² = 1`);
`OSR/IntegrationRec87.lean` 1.1.1.4 #6 and `OSR/IntegrationRec88.lean`
1.1.1.4 #3, the reductions of `(a + b x)^m (c + d x)^n (e + f x)(g + h x)`;
`OSR/IntegrationRec89.lean` 1.2.1.3 #33, where `c d² + a e² = 0` makes
`e² (a + c x²)` equal to `c (e x - d)(d + e x)`; and `OSR/IntegrationRec90.lean`
and `OSR/IntegrationRec91.lean` 1.1.3.3 #16 and 1.1.3.4 #25, where
`a2 b1 + a1 b2 = 0` makes `(a1 + b1 x^(n/2))(a2 + b2 x^(n/2))` equal to
`a1 a2 + b1 b2 xⁿ`. Over ℝ only, with the real logarithm:
`OSR/IntegrationRec83.lean` proves 4.7.8 #13 and #14, the reductions of
`(e x)^m sin(d (a + b log (c xⁿ)))^p` and of the cosine analogue for `p > 1`;
`OSR/IntegrationRec84.lean` 3.4 #2, with `d/dx log (c (d + e/x)^p) =
-e p/(x (d x + e))`; `OSR/IntegrationRec85.lean` 3.2.1 #1, with
`d/dx log (e ((a + b x)/(c + d x))ⁿ) = n (b c - a d)/((a + b x)(c + d x))`; and
`OSR/IntegrationRec86.lean` 3.3 #22. The variant of 3.3 #22 distributed
before its proof was false: at `n = 0` the integrand `x^(r-1) (f + g xʳ)^q
(a + b log c)^p` is defined around `x = -d/e`, where the residual integrand,
with the factor `(d + e x)⁻¹`, is not. It now appends `n ≠ 0` as well, which
the pole probe missed because the base `d + e x` has no negative power in the
integrand.

## Strengthened variants of the first named rules

The first migrated rules carry names (`integration.power_log_linear`, …)
rather than RUBI numbers, and the triage of variants had skipped them. Nineteen
of them, refuted as stated, pass both numerical passes with their
non-degeneracy conditions and are now proved directly. Over ℝ and ℂ:
`OSR/IntegrationRec92.lean` proves 1.1.1.4 #17, 1.1.3.5 #10 and #2, and
1.2.1.3 #11 and #12 (with `b ≠ 0`, `d ≠ 0`, `b c - a d ≠ 0` and `c ≠ 0`: the
result is a linear combination of residual integrals, or a polynomial plus
one); `OSR/IntegrationRec93.lean` 1.1.1.3 #8, 1.1.3.3 #14 (with `a ≠ 0`, for
`n < 0`, where `b + a x⁻ⁿ = x⁻ⁿ (a + b xⁿ)`) and 1.2.1.2 #13 and #14; and
`OSR/IntegrationRec94.lean` 4.1.13 #17 and #18 (with `2 c ≠ 0`) and #3 and #4
(with `4 c ≠ 0`: `a + b x + c x² = (b + 2 c x)²/(4 c) - (b² - 4 a c)/(4 c)`,
then the subtraction formulas). Over ℝ only, with the real logarithm,
`OSR/IntegrationRec95.lean` proves 3.1.2 #1 and #4, 4.7.8 #11 and #12, and
4.7.8 #45 and #46.

Eleven other candidates left by the adversarial sampling fail the pole probe.
Eight of them fail only at a vanishing exponent, where the integrand no
longer vanishes or blows up at the pole of a residual integrand: with the
exponent nonzero as well they pass both numerical passes and are proved.
`OSR/IntegrationRec96.lean` proves 1.1.3.3 #18 with `p ≠ 0` over ℝ and ℂ (the
conditions then force `n = -1`, `p = 2`); over ℝ only, with the real logarithm,
`OSR/IntegrationRec97.lean` proves 3.3 #7, 3.2.1 #13 and 3.5 #23 with `n ≠ 0`,
and `OSR/IntegrationRec98.lean` 3.2.1 #2 with `n ≠ 0` and 3.2.3 #2, #4 and #7
with `p, q, r ≠ 0` (from `d/dx log (e (f (a + b x)^p (c + d x)^q)^r) =
r (p b/(a + b x) + q d/(c + d x))`). The last three, 4.1.11 #3 and #4 and
4.7.9 #79, fail at a point rather than for a parameter value (`x = 0`, a zero
of `cos (a x)`) and are not included.

Twenty-five candidates had been sampled at fewer than 50 points, most because
an `EqQ` condition is rarely met by random values. Sampling again with each
equality solved for one of its coefficients (exponents kept integral), 23 pass
both numerical passes, two of them only with one more nonzero exponent
(3.1.4 #22 with `n ≠ 0`, 3.2.3 #8 with `p, q, r ≠ 0`). Over ℝ and ℂ:
`OSR/IntegrationRec99.lean` proves 1.2.1.2 #5 and 1.2.3.3 #50 (with `d ≠ 0` and
`e ≠ 0`, the trinomial factors as `(d + e y)(a/d + c y/e)`);
`OSR/IntegrationRec100.lean` 4.1.12 #45, #46, #53 and #54, whose powers of `x`
all have nonnegative exponents; `OSR/IntegrationRec101.lean` 1.2.1.2 #40, #46
and #96 (for #40 and #46, `c d² + a e² = 0` eliminates `a`);
`OSR/IntegrationRec102.lean` 1.2.3.3 #27; `OSR/IntegrationRec103.lean` 1.2.3.4
#34, #38 and #40; `OSR/IntegrationRec104.lean` 1.2.3.2 #10 and #18;
`OSR/IntegrationRec105.lean` 1.2.3.4 #61 and #64, splits into two residual
integrals; `OSR/IntegrationRec108.lean` 1.2.1.3 #26 (the conditions force
`e ≠ 0`, and `e² (a + b x + c x²) = (d + e x)(c e x - c d + b e)`); and
`OSR/IntegrationRec109.lean` 1.1.3.3 #5, where `n (p + q + 1) + 1 = 0` closes
the identity. Over ℝ only, with the real logarithm,
`OSR/IntegrationRec106.lean` proves 3.1.4 #10 and #22 and 3.3 #12, and
`OSR/IntegrationRec107.lean` 3.2.3 #8 (`h j = g k` makes
`1/(j + k x) = h/(k (g + h x))`).

Eight candidates that failed the numerical truth check at a single zero of a
parameter hold once that zero is excluded. `OSR/IntegrationRec110.lean`
proves 1.1.3.7 #5 over ℝ and ℂ with `B ≠ 0` (at `A = B = 0` the residual
integrand is nowhere defined; otherwise `B³ (a + b x³) = b (A + B x)(A² - A B x
+ B² x²)`). Over ℝ only, `OSR/IntegrationRec111.lean` proves 3.3 #29 and #31
(with `n ≠ 0`) and 3.1.5 #33 (with `r ≠ 0`), and `OSR/IntegrationRec112.lean`
3.3 #30 and #39 (with `n ≠ 0`), 3.4 #27 and 3.5 #3 (with `p ≠ 0`): at the
excluded zero a residual integrand or the result is undefined somewhere the
integrand is defined.

Six more candidates need a tighter exponent bound. RUBI 1.2.2.4 #59–62 split
off residual integrands with `(f x)^(m-4)` (#59, #60) or `(f x)^(m-2)` (#61,
#62): RUBI's `m > 2` (resp. `m > 0`) admits the integer `m = 3` (resp. `m = 1`),
where they have a pole at `x = 0` that the integrand does not.
`OSR/IntegrationRec113.lean` proves them over ℝ and ℂ with `m > 3` (resp.
`m > 1`) and RUBI's own `c d² - b d e + a e² ≠ 0`, from `d² P - (a d + (b d -
a e) x²)(d + e x²) = (c d² - b d e + a e²) x⁴` and its analogues.
`OSR/IntegrationRec115.lean` proves 1.1.1.3 #53 over ℝ and ℂ with `m, n > 0`
and `f² ≠ 0`: `2 b d e = f (b c + a d)` gives `f² (a + b x)(c + d x) = b d (e +
f x)² + (b e - a f)(d e - c f)`. Over ℝ only, `OSR/IntegrationRec114.lean`
proves 3.4 #7 (`integration.power_log_binomial`) with `f (m + 1) ≠ 0` and
`p, n ≠ 0`; at `n = 0` the residual integrand `x^(n-1) (f x)^(m+1)/(d + e xⁿ)`
is undefined at `x = 0`.

`OSR/IntegrationRec116.lean` proves 1.3.1 #4 and 1.3.2 #1 over ℝ and ℂ: when
`4 b³ + 27 a² d = 0`, `(3 a - b x)(3 a + 2 b x)² = 27 a² (a + b x + d x³)`, and
RUBI's own `3^(3p) a^(2p) ≠ 0` suffices since integer powers need no other
condition. Their numerical failures were an artefact of the check's overflow
guard. `OSR/IntegrationRec117.lean` proves 2.3 #11, #23, #24, #26 and #35 over
ℝ and ℂ with `F > 0`, which `log F` needs. OSR powers have integer exponents,
so an integrand `F^g(x)` is defined near a point only where `g` is a locally
constant integer; over ℝ and ℂ an integer-valued function continuous at a
point is constant near it, so `g' = 0` there, which makes the logarithmic
term of the result vanish (`b = 0`, or `d = 0`, or `f = 0` for #35).

Nine RUBI rules that had not been considered are migrated and proved as
RUBI states them, over ℝ and ℂ. `OSR/IntegrationRec118.lean` proves 1.2.3.3
#41, #42 and #47 and 1.2.3.4 #92, #93 and #100: for an integer `p`,
`(a + b x^(-n) + c x^(-2n))^p = x^(-2np) (c + b xⁿ + a x^(2n))^p` (and the
analogue with `x^(-np)`) wherever the integrand is defined, since `x ≠ 0`
there unless `n = 0`. `OSR/IntegrationRec119.lean` proves the reductions
1.2.1.2 #93, #94 and #95 (`m + 2p + 2 = 0`); the derivative identity is
polynomial once `m = -2p - 2` is substituted, and was checked exactly with
Giac. For #95 (`p < -1`, so `m ≥ 2`) every power of `d + e x` that occurs has
a nonnegative exponent.

247 further RUBI rules are migrated and refuted as stated
(`OSR/IntegrationRec120.lean` … `IntegrationRec127`), among the rules not
considered before whose heads all have an OpenMath symbol and an OSR
operator (Integration now maps the reciprocal, hyperbolic and inverse
functions to `transc1` and reads `Sqrt` as `root(a, 2)`). A numerical search
gives each an assignment of the metavariables and a point where the
conditions hold and the integrand is defined nearby, but the result or a
residual integrand is not; the counterexample theorems are generated from
these witnesses. All 247 are refuted over ℝ and 53 over ℂ; the other 194 are
unproved over ℂ, mostly because their integrand uses sec, csc, coth, sech,
csch, an inverse function other than arctan, or a square root, none of which
has a complex interpretation in the fragment. 39 further candidates whose
real counterexample did not check, one whose condition depends on x (3.3 #43), and 141 that hold numerically, are left
for later.

Fourteen of these are now proved as RUBI states them.
`OSR/IntegrationRec128.lean` proves twelve rules whose result is a
combination of residual integrals with constant coefficients and whose
integrand is the same combination of their integrands, an identity of the
polynomial ring once each function application is an atom (5.3.4 #41, #132,
#138, #140 over ℝ and ℂ; 7.3.4 #41, #132, #138, #140 and 7.3.1 #61, #152,
#158, #160 over ℝ only, arctanh having no complex interpretation).
`OSR/IntegrationRec129.lean` proves 5.3.4 #107 and 6.7.7 #33 over ℝ, using
the real definitions of the reciprocal functions.

`OSR/IntegrationRec130.lean` refutes 19 more of the candidates over ℝ: their
counterexample theorems need `sin c`, `cos c` or `sinh c` nonzero at a small
integer `c`, which the first batch did not discharge. They stay unproved
over ℂ.

Ten more are proved over ℝ by integration by parts.
`OSR/IntegrationRec131.lean` proves `∫ A(u) = x A(u) - ∫ x u' A'(u)` for
`A = artanh` with `u = a + b xⁿ` or `c xⁿ` (7.3.4 #1, 7.3.7 #1, 7.3.1 #168)
and `A = arctan` with `u = a + b xⁿ` (5.3.7 #1); it also derives the
derivative of `Real.artanh`, `1/(1 - x²)` on `(-1, 1)`, which Mathlib lacks,
from `Real.artanh_eq_half_log`. `OSR/IntegrationRec132.lean` and
`IntegrationRec133` prove the rules for `(d + e log(f + g x²)) (a + b A(c x))`
without and with a factor `xᵐ`, `m/2` a negative integer (7.3.4 #134, #142,
7.3.1 #154, #162, 5.3.4 #134, #142): the product rule leaves exactly the two
residual integrands.

`OSR/IntegrationRec134.lean` proves 5.3.7 #43 and #45 over ℝ:
`(arctan ∘ tanh)(a + b x)' = b/(cosh² + sinh²) = b sech(2a + 2b x)` and the
analogue for coth, with the derivatives of tanh and coth of a linear
argument derived from the quotient rule. `OSR/IntegrationRec135.lean` proves
7.3.4 #13, 7.3.7 #13 (arctanh, `b = c²`) and 5.3.7 #13 (arctan, `b = -c²`) for
`A(c x/√(a + b x²))`: `x A'(u) u' = c x/√(a + b x²)` is a field identity in
`r = 1/√(a + b x²)`.

`OSR/IntegrationRec136.lean` and `IntegrationRec137` prove the rules for
`(a + b A(c x))^p/(x² √(d + e x²))` and `(f x)^m (a + b A(c x))^p/√(d + e x²)`
(7.3.4 #89, #91, 7.3.1 #109, #111, 5.3.4 #89, #91): with `q = √(d + e x²)`,
the condition gives `q² = d (1 ∓ c² x²)`, so after eliminating
`d = q²/(1 ∓ c² x²)` the derivative identity is rational in `q`.

`OSR/IntegrationRec138.lean` proves 7.3.4 #39 and 7.3.1 #59 over ℝ:
`artanh u = (log(1 + u) - log(1 - u))/2` for `-1 < u < 1` (from
`Real.artanh_eq_half_log`) splits the integrand into the residual integrands.
`OSR/IntegrationRec139.lean` proves eight more such splits over ℝ, with
integer exponents taken from the integrand's definedness: 7.3.4 #107 and
7.3.1 #127 by linearity, 7.3.4 #130, 7.3.1 #150, 7.3.7 #3 and 7.3.4 #3 with the
arctanh identity, and 6.1.12 #19 and #20 with the addition formulas of sinh
and cosh.
`OSR/IntegrationRec140.lean` and `IntegrationRec141` prove six splits with a
shifted exponent over ℝ: `1/(d + e x) = 1/d - e x/(d (d + e x))` with
`(f x)^(m+1) = (f x)^m f x` (7.3.4 #5, 7.3.1 #25, 5.3.4 #5), and
`d (d + e x²)^q = (d + e x²)^(q+1) - e x² (d + e x²)^q` (7.3.4 #95, 7.3.1 #115,
5.3.4 #95). In each the condition forces `d ≠ 0`: with `d = 0` it gives
`e = 0`, and the integrand is nowhere defined.

`OSR/IntegrationRec142.lean` to `IntegrationRec152` prove 48 more rules over
ℝ, eight of them over ℂ as well:

- 7.2.3 #1 and 7.2.4 #1: with `d₂ e₁ + d₁ e₂ = 0`,
  `(d₁ + e₁ x)(d₂ + e₂ x) = d₁ d₂ + e₁ e₂ x²`, and `mul_zpow` for an integer `p`.
- 6.7.9 #70 (ℝ and ℂ): `sinh u cosh u = sinh(2u)/2`.
- 6.1.11 #7, #8, #19 and #20 (ℝ and ℂ): for negative integers `n` and `p` the
  integrand is only defined at `x ≠ 0`, where `a + b x^n = x^n (b + a x^(-n))`.
- 7.3.4 #136 and 7.3.1 #156: with `g = -c² f`, `log(f + g x²) = log f +
  log(1 - c x) + log(1 + c x)` where the integrand is defined (there `f > 0`),
  so the coefficient of the first residual integral is locally constant.
- 4.7.9 #72 to #75: multiplying by `cos² u` (or `sin² u`) turns
  `b + a sec² u + c tan² u` into half of `2a + b + c + (b - c) cos 2u`.
- 4.7.9 #17 to #20, 6.7.9 #8 (ℝ and ℂ) and #16 to #18: reductions of
  `(e + f x)^m F^n/(a + b G)` with `sin² + cos² = 1` or `cosh² - sinh² = 1`;
  `a² = b²` forces `a ≠ 0` and `b ≠ 0` where the integrand is defined.
- 4.7.6 #10 to #13 and 6.7.6 #5, #10 to #13: `tan² = sec² - 1`,
  `cot² = csc² - 1`, `tanh² = 1 - sech²` and `coth² = 1 + csch²`, the power
  `p ≥ 2` coming from `p/2 ∈ ℤ`, `p/2 > 0`.
- 7.3.4 #7, #9 and 7.3.7 #7, #9: `artanh u = (log(1 + u) - log(1 - u))/2`, the
  power `f^(c + d x)` being the same atom on both sides.
- 5.3.7 #23, 7.3.4 #23 and 7.3.7 #23: with `b d = a e`,
  `(a + b x²)/(d + e x²)` is constant where both are positive, so
  `√(a + b x²)/√(d + e x²)` is locally constant.
- 6.7.7 #24, #25 (ℝ and ℂ) and #30: `1 + cosh u = 2 cosh²(u/2)`,
  `cosh u - 1 = 2 sinh²(u/2)` and `sinh u = 2 sinh(u/2) cosh(u/2)`.
- 5.1.1 #1, #2, 5.1.2 #5, #6, 7.1.1 #1, 7.1.2 #3, 7.2.1 #1 and 7.2.2 #3:
  integration by parts with the derivatives of arcsin, arccos, arsinh and
  arcosh. An integrand defined on a neighbourhood of `x` keeps `c x` in the
  open domain (`strict_Icc`, `strict_Ici`), where these derivatives hold.

`OSR/IntegrationRec153.lean` to `IntegrationRec156` add 21 rules over ℝ:

- 6.7.9 #86 to #89 and 4.7.9 #96, #97: with `b² = d²`, `d = ± b`, so the two
  arguments differ (or add up) by the constant `c - a` (or `a + c`), and the
  addition formulas split `sech · sech`, `csch · csch`, `tanh · tanh`,
  `coth · coth`, `tan · tan` and `cot · cot`; `b c - a d ≠ 0` keeps the
  hyperbolic constants `csch(c - a)` defined.
- 4.7.9 #94 and #95 are refuted: at `a = 0`, `b = d = 1`, `c = π` the
  conditions hold and `sec x sec(x + π)` (resp. `csc x csc(x + π)`) is defined
  near `x = 0` (resp. `x = 1`), but the result contains `csc π`.
- 6.7.7 #1 to #4, #7 and 4.7.7 #13, #14, #17, #18: the fragment interprets
  `F^(c (a + b x))` for integer exponents only, so an integrand defined on a
  neighbourhood makes `c (a + b x)` an integer on an interval, hence `b c = 0`
  (`int_valued_const`) and the power is constant; the rules reduce to the
  reduction formulas of `sinh^n`, `cosh^n`, `sec^n` and `csc^n`.
- 6.7.8 #3 to #6: with `θ = d (a + b log(c xⁿ))`, `x θ' = b d n` wherever the
  logarithm is defined (also for `n = 0`), and `cosh² θ - sinh² θ = 1`.

The rules of `OSR/IntegrationRec155.lean` carry a `domain:` finding: the
fragment interprets `F^(c (a + b x))` for integer exponents only, so their
proofs cover only the constant power (`b c = 0`). 4.7.7 #1 and #2 and 2.3 #1
and #8 stay among the rules not migrated.

`OSR/IntegrationRec157.lean` and `IntegrationRec158` add eight rules:

- 4.7.6 #4, #5 and 6.7.6 #4 are refuted over ℝ and ℂ: at `n = 1`, `p = 2` the
  integrand `sin x tan² x` (resp. `cos x cot² x`, `sinh x tanh² x`) is defined
  near `x = 0` (resp. `π/2`, `0`), but a residual integrand keeps
  `sin^(-1) x` (resp. `cos^(-1) x`, `sinh^(-1) x`), not defined there. The
  hyperbolic 6.7.6 #5 (`cosh^n coth^p`) is proved: `cosh` has no real zero.
- 7.3.1 #1 by parts with `artanh' u = 1/(1 - u²)`; 7.3.4 #41 and 7.3.7 #41 by
  parts with `d/dx artanh(tan u) = b sec(2u)`, where `|tan u| < 1` gives
  `cos 2u > 0`.
- 6.7.9 #73 (ℝ and ℂ) and #75: `2 (a + b cosh² u + c sinh² u) = 2a + b - c +
  (b + c) cosh 2u`, multiplying by `cosh² u` for the sech/tanh form.

A numerical pass over the 399 RUBI rules not yet considered whose heads and
conditions the fragment translates (rules with a generic factor `u`, `v` or
`w` excluded) finds 47 candidates true and 164 false. The definedness search
finds witnesses for 26 of the false ones; `OSR/IntegrationRec159.lean` keeps
the three that compile, have conditions free of x and are not exponential
rules of 2.2 and 2.3 (which, like 4.7.7 #1 and #2, stay out of the fragment):
5.3.4 #144 and 6.3.12 #3, #4, refuted over ℝ (6.3.12 #3 over ℂ too). `IntegrationRec160` proves 1.2.2.3
#25 over ℝ by linearity.

`OSR/IntegrationRec161.lean` integrates by parts 6.1.12 #27, #28 and 4.1.12
#41, #42 over ℝ and ℂ (for `m + n = 0`, `n x^(m+1) x^(n-1) = n` also at
`x = 0`, where `n = 0`) and 3.3 #9 over ℝ (`(d + e x) θ' = n e` for
`θ = log(c (d + e x)ⁿ)`, as for 6.7.8), and refutes 5.3.5 #7 over ℝ and ℂ at
`f = 0`.

`OSR/IntegrationRec162.lean` refutes ten rules the numerical pass judged true,
at points it does not sample: 1.2.2.8 #1, #2 and 1.3.3 #6 at `d = e x`, where
the residual integrands have `(d² - e² x²)⁻¹` (resp. `(a² - b² x²)⁻¹`) and the
integrand is defined; 1.2.2.3 #47, #48, #51, #52 and 1.2.2.4 #71, #72 at
`x = 0`, where `√(e + d/x²)` is not defined (elsewhere their prefactor is the
sign of `x`); and 3.1.2 #12 at `x = 0` with `n = 0` (also over ℂ).

`OSR/IntegrationRec163.lean` proves 1.3.3 #24 (the radicand `e x (a x + b
√(c + d x²))` distributed) and 6.7.9 #76 (`2 (c sinh² u + b cosh² u) = b - c +
(b + c) cosh 2u`) over ℝ, and refutes 1.3.3 #36 at `d = 0`, 1.2.1.5 #17 at
`f = 0` and 1.2.1.6 #26 at `f = 0` (where `c e = b f` forces `c = 0`): the
result divides by `d`, `f` or `2 f` while the integrand is defined.

A definedness search over the 243 rules not yet considered whose result
divides by a coefficient expression (rules with `E`, `ImaginaryI` or `Pi`, a
generic factor, or exponential bases left out; non-integer exponents not
counted as failures) finds integer assignments at which the conditions hold,
the integrand is defined everywhere and the result or a residual integrand is
not. `OSR/IntegrationRec164.lean` keeps the nine whose Lean refutation checks:
1.1.1.4 #33, #35, 1.1.1.7 #9, #12, 1.1.3.3 #27, 1.1.3.4 #49, 1.2.2.3 #41,
4.7.9 #83 and 7.3.4 #69.

The same search over the remaining 41 translatable rules gives
`OSR/IntegrationRec165.lean`: 3.2.3 #9, whose split of
`log(e (f (a + b x)^p (c + d x)^q)^r)` into logarithms of the factors fails
where a factor is negative, and 3.4 #1, 3.5 #1 at degenerate coefficients.

A wider search (assignments with halves, integrands required to be defined
only on a neighbourhood of the point, which the Lean proofs establish on an
interval of radius 1/16) gives `OSR/IntegrationRec166.lean`: 40 more
refutations whose Lean proof checks, the rules with a condition on `x` left
out.

`OSR/IntegrationRec167.lean` refutes 7.2.5 #17. The rules not considered so
far whose integrand the fragment cannot interpret are now reported in
`Integration.notMigrated` (320 entries): 147 with an exponent of denominator
2, 3, 4 or 6 (nowhere defined), and 132 with a power `F^(…)` whose exponent
depends on `x`. Exponentials written `E^u` are left for a translation of `E^u`
into `transc1#exp`.

That translation is now made: `E^u` reads as `exp(u)`, both in the Lean rules
and in the faithfulness check (`Integration/scripts/v1_faithfulness.py`),
since the v0.1 corpus writes every exponential so; a bare `E` is still left
out. `OSR/IntegrationRec169.lean` proves over ℝ and ℂ the 14 rules that
rewrite `sinh u` and `cosh u` as `(exp u ∓ exp(-u))/2` (6.1.12 #1, #2, #7, #8,
#29, #30, #55, #56, 6.1.13 #1, #2 and 6.7.9 #91 to #94).
`OSR/IntegrationRec168.lean` refutes 10 more over ℝ, all at degenerate
coefficients where the result divides by zero (7.3.4 #33, #37, #39, 7.3.7
#33, #37, #39, 6.7.8 #25, #26, 6.7.9 #4, 5.3.6 #13).

The transcription now also reads `Simp[e]` and `Simp[e, x]` as `e` (RUBI's
algebraic normaliser does not change the value), flattens `And[…]`
conditions, and reads `Not[EqQ[a, b]]` as `NeQ[a, b]` and `Not[NeQ[a, b]]`
as `EqQ[a, b]`; the faithfulness check does the same. Of the 266 rules not
considered so far that this makes translatable, the definedness search finds
a counterexample for 140; 91 of them have a Lean proof that checks
(`OSR/IntegrationRec170.lean`, `OSR/IntegrationRec171.lean`), the others
are left out.

Among the rules left, 50 have a result that is a combination of residual
integrals with coefficients free of `x`. `OSR/IntegrationRec172.lean` proves
five of them over ℝ and ℂ with one template: each residual integrand is
defined wherever the integrand is (its denominators are factors of the
integrand's), the derivative of the combination is the same combination of
the residual integrands, and the identity closes by `field_simp` (the
partial fractions 1.1.1.2 #3, 1.2.1.2 #78 and #79, with the condition
`c d² - b d e + a e² ≠ 0` used through `mul_inv_cancel₀`) or by the addition
theorem (4.1.12 #3 and #4, `sin(c + u)` and `cos(c + u)`). The others need
symbolic exponents, square roots or exponential identities.

RUBI writes many trig rules with inert copies `sin`, `cos`, `tan`, `cot`,
`sec` and `csc` of the trig functions; they have the same value and are now
read as `Sin`, …, `Csc` by the transcription and the faithfulness check.
That makes 583 more rules translatable; the definedness search finds a
counterexample for 452, and 185 of them have a Lean proof that checks
(`OSR/IntegrationRec173.lean` to `OSR/IntegrationRec175.lean`). In 171 the
result is undefined at the point (mostly a logarithm or a power of a
negative number), in 14 a residual integrand is.

Of the 316 counterexamples whose Lean proof did not check (267 here, 49
from the `Simp` batch), most failed on the sign of a trig function at the
point (`sin 3 ≠ 0`, `0 < cos (1/2)`, `sin (2 w) ≠ 0` near `w = 2`) or on
the integrality of a literal exponent. The generated tactics now try
`Real.sin_pos_of_pos_of_lt_pi`, `Real.sin_neg_of_neg_of_neg_pi_lt` (also
after a shift by `2π`), `Real.cos_pos_of_mem_Ioo` and
`Real.cos_neg_of_pi_div_two_lt_of_lt` with `3 < π < 3.15`, unfold `csc` and
`sec`, and give the integer of a literal exponent explicitly. 114 more
refutations check (`OSR/IntegrationRec176.lean` to
`OSR/IntegrationRec178.lean`); for most of the others the Lean evaluation
shows that the sampled conditions do not hold, so they are left out.

`Acoth[u]` is now transcribed as `arctanh(u^-1)`, which has the same value
over ℝ (`|u| > 1`) and on the principal complex branch; the fragment has no
`transc1#arccoth`, and the faithfulness check reads `Acoth` the same way.
Of the 150 rules this makes translatable, the definedness search finds a
counterexample for 70 and 12 of them check in Lean
(`OSR/IntegrationRec179.lean`, `OSR/IntegrationRec180.lean`). The 7.3.1 file
`(a+b arctanh(c x^n))^p` shares its section number with
`u (a+b arctanh(c x^n))^p`; its rules get the id prefix
`integration.rubi_7_3_1_pow_`.

A condition `Not[IntegerQ[e]]` has no v1 counterpart. When `e` is an
exponent of the integrand, the fragment's `arith1#power` (integer exponents
only) leaves the integrand nowhere defined under that condition, so such a
rule says nothing in the fragment: 200 of them are reported in
`Integration.notMigrated` (520 entries).

The linear-split template of `OSR/IntegrationRec172.lean` proves 11 more
rules (`OSR/IntegrationRec181.lean`): over ℝ all of them, over ℂ the three
without `sec`, `csc` or `arctanh` (4.1.2.1 #14, 4.3.2.1 #29, 4.3.4.1 #9).
The closing step now also rewrites `tan` and `cot` as quotients of `sin` and
`cos` before `field_simp`.

The five rules of `OSR/IntegrationRec172.lean`, and 3.4 #1, 3.5 #1 and
3.5 #2 refuted earlier, turned out to be catalogued already under named ids
whose legacy id is built by interpolation; their second entries are removed
and an `OSRTest` guard now rejects such duplicates.

Most of the `Acoth` counterexamples that did not check failed on the domain
of `arctanh(u^-1)`, goals such as `w⁻¹ < 1` near `w = 2`; the generated
tactics now close them by `nlinarith` with `w w⁻¹ = 1` and the sign of
`w⁻¹`, and 42 more check (`OSR/IntegrationRec182.lean`,
`OSR/IntegrationRec183.lean`). `Acot[u]` is transcribed as `arctan(u^-1)`,
Mathematica's definition of `ArcCot`; of the 66 rules this makes
translatable, 28 have a counterexample and 23 check
(`OSR/IntegrationRec184.lean`).

`OSR/IntegrationRec185.lean` generalises the linear-split template to
results that are sums of terms `c ∫ H`, `c x` and `c` with `c` free of `x`:
the derivative is assembled from the result tree (`HasDerivAt.const_mul`,
`hasDerivAt_id`, `hasDerivAt_const`, `HasDerivAt.add`) and matched to the
evaluated result by `convert … using 1`, which leaves an equality of
functions (closed by `ring`) and the algebraic identity. Of 56 candidates,
11 check over ℝ and five of them over ℂ; the others need identities on
square roots (`√a √b = √(a b)`), exponentials, or an `EqQ` condition in the
algebra.

With two more closing steps, `grind` (which uses the conditions, including
`EqQ`, as ring equations) and an expansion of `sinh`, `cosh` and `tanh` into
exponentials before `field_simp`, 14 of the remaining 45 check over ℝ and 11
of them over ℂ (`OSR/IntegrationRec186.lean`), among them 6.7.9 #45 and #48.

The refutation tactics also try `grind` now: of the 222 counterexamples
whose Lean proof did not check, seven more do (`OSR/IntegrationRec187.lean`,
`OSR/IntegrationRec188.lean`). A second definedness search with another
random seed over the 581 translatable rules without a counterexample finds
three more (`OSR/IntegrationRec189.lean`); the search space is close to
exhausted for these rules.

OSR v1 conditions now include `relation1#geq` and binary `logic1#or`, so
RUBI's `GeQ`, `LeQ`, `Not[LtQ]`, `Not[GtQ]` and `Or` can be stated. Of the 145
rules this makes translatable, the definedness search finds a
counterexample for 99 and 77 of them check in Lean
(`OSR/IntegrationRec190.lean`, `OSR/IntegrationRec191.lean`), all with a
`relation1#geq` condition. The rules with `Or` were not among them: the
inventory read the disjuncts of `Or` as expressions. With that fixed, 82
rules with `Or` (each disjunct one v1 condition) are translatable, the
search finds a counterexample for 61, and 33 check
(`OSR/IntegrationRec192.lean`).

Compound conditions are now put in conjunctive normal form before they are
stated: `And` flattens, `Or` distributes over `And`, `Not` moves inward (De
Morgan; the negation of a comparison is the opposite comparison, `Not[IntegerQ]`
has no counterpart), with at most 16 clauses. The transcription
(`handoff/gen_lean_rule.py`) and the faithfulness check share the same
function, so they read the conditions identically. This makes 113 more rules
translatable; the search finds a counterexample for 75 and 54 check
(`OSR/IntegrationRec193.lean`).

RUBI writes many results with `Subst[Int[H, x], x, g]`, an antiderivative of
`H` evaluated at `g`. OSR v1 now states such residual integrals as
`int(λx. H)(g)` (shape `antiderivSubst`, `AntiderivSubstHolds`), and the
transcription and the faithfulness check read `Subst` so. Of the 427 rules
this makes translatable, the definedness search (with `H` evaluated at
`g(t)`) finds a counterexample for 326 and 275 check in Lean
(`OSR/IntegrationRec194.lean` to `OSR/IntegrationRec196.lean`): 183 where a
residual integrand is undefined at its substitution, 92 where the result is.

Most refutations are degenerate cases: the counterexample sets a coefficient
to zero where the result divides by it. For each refuted rule without a
variant, the bases `c` free of `x` raised to a negative power that vanish at
the counterexample give conditions `c ≠ 0`; the definedness search is run
again on the strengthened rule, and a condition is added for a new
degenerate counterexample (at most three rounds). Of 1361 refutations, 923
have such a variant with no counterexample left (one condition for 886, two
for 37). Each is then checked numerically over ℝ, adversarially (each
metavariable 0 with probability 0.4) and at the real zeros of the bases
raised to a negative power, comparing the derivative of the result, with the
residual integrals linearised, with the integrand: 604 pass with no failure
on at least 30 points and are distributed unproved in
`OSR/IntegrationNum1.lean`, with the evidence in a `numerical:` finding; 217
had too few points and 102 fail (64 on the value, 38 on definedness), so the
rule needs more than a non-degeneracy condition.

The float check turned out to report rounding errors as failures: near a
pole, for large values, and when an equality condition is solved only
approximately. The check now also computes the derivative of the result
symbolically (each residual integral `Φ(g)` contributing `H(g) g'`) and
compares it with the integrand to 50 digits, at rational assignments with the
equality conditions solved exactly. It confirms the 604 variants already
distributed and accepts 184 more (788 in all); 6 candidates are false, and the
others are left out until their definedness failures (78) or sample sizes
(51) are settled.

Of the 78 definedness failures, 38 are genuine in the fragment: the result
has a power with a non-integer exponent such as `(d + e x²)^(p + 1/2)` where
the integrand is defined, so the variant is false in OSR v1. Of the 40 found
with equality conditions solved numerically, 24 come from the approximate
solution (a value near `0` or an exponent near an integer) and pass the exact
check; with more samples, 15 of the 51 under-sampled variants reach ten exact
points. These 39 are distributed too (827 in all).

The numerical triage is not a proof: the candidate variant of 1.2.1.3 #25
(`c (m + 2 p + 2) ≠ 0`) is false at `e = d = m = 0`, `f ≠ 0`, a case the
samples missed; it needs `e ≠ 0` as well and is not included.

A development triage adds `D ≠ 0` for every coefficient-only denominator
`D^k` (`k < 0`) of the result of the 318 refuted rules: 291 receive a
condition, and a numerical truth check finds 206 of these variants true (35
without residual integrals), 39 still refuted, 41 never defined in the samples
and 5 mixed. They are the backlog of strengthened variants.
