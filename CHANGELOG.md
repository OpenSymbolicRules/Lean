# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- Prove 36 strengthened RUBI variants and move them from the numerically
  checked candidates to the verified catalogue: 18 with closed results
  (trigonometric, hyperbolic, inverse tangent and inverse hyperbolic tangent
  families; nine over ℝ and ℂ, nine over ℝ only) and 18 inverse hyperbolic
  tangent rules with one residual integral, over ℝ only.
- State 39 more original RUBI rules with integer-matching parameters. Check the
  cosecant witness for RUBI 4.5.2.1 #47 and reassess counterexamples under the
  full chained bounds of their source rules.
- Migrate 118 default-profile RUBI source identities, retaining their guards,
  source locators and per-domain evidence.
- Migrate RUBI 2.3 #1 with its original condition and a Lean-checked real
  counterexample in the integer-power interpretation; the complex case is
  unproved and runtime dispatch in RUBI has not been tested.
- Formally check a candidate-domain counterexample to the OSR transcription
  of RUBI rule 2.3 #1, and document the separate question of whether
  RUBI's runtime matching actually applies that rule to the witness.
- Prove the complete real `integration.power` statement in the test-only
  power interpreter, reusing the existing certificate for integer exponents
  and handling nonpositive points via neighborhood definedness. The
  production interpretation and published rule are unchanged.
- Check the existing `integration.power` expressions against the test-only
  real-power interpreter on the positive half-line, including neighborhood
  definedness; the published rule and its status remain unchanged.
- Add a test-only recursive real-power interpreter and prove that all currently
  defined real expressions retain their values and definedness. A constructed
  counterexample shows why this does not preserve all guarded theorems.
- Prove that a test-only candidate real-power domain includes every currently
  defined integer power, and check fractional powers and poles explicitly.
  No production interpretation or exported rule is changed.
- Check the current integer-only interpretation rejects `2^(1/2)` despite
  its positive real value, documenting the non-integer domain gap.
- Add exploratory Lean checks for positive-base real powers, including
  integer-fragment agreement, a local primitive and definedness pitfalls.
  The existing v1 interpretation and exported rules are unchanged.
- Migrate RUBI 7.3.7 #19 with its original condition and a Lean-checked
  real counterexample; its complex case is unproved.
- Prove RUBI 1.1.1.2 #21 over ℝ using its original conditions and local
  definedness of its square-root product; its complex case remains unproved.
- Migrate RUBI 5.3.7 #19 with its original conditions and a Lean-checked
  real counterexample at a negative arctangent; its complex case is unproved.
- Application tests for the real log-product rule covering positive factors,
  a missing guard, and a loss of definedness despite equal totalized values.
- Preliminary Mathlib checks for 28 linear-algebra identities and five
  concrete counterexamples. These are
  hand-written mathematical statements and do not certify OSR exports or
  OpenMath mappings.

### Fixed
- Eight RUBI rules were catalogued twice: 1.1.1.2 #3, 1.2.1.2 #78 and #79,
  4.1.12 #3 and #4 (`OSR/IntegrationRec172.lean`), 3.4 #1 and 3.5 #1
  (`OSR/IntegrationRec165.lean`) and 3.5 #2 (`OSR/IntegrationRec166.lean`)
  were already in the catalogue under named ids (`integration.partial_fractions_linear`,
  `integration.sin_add_square`, `integration.log_power_log`, …) whose legacy
  id is written by interpolation, which the migration tooling did not read.
  The second entries are removed (both copies had the same verdict); the
  Lean theorems stay. A new `OSRTest` guard rejects two catalogue entries
  with the same legacy id unless one is a strengthened variant.
- The nine RUBI rules migrated in report `37faa87a…` declare exponent
  metavariables (`m`, `p`, `mn`, `mn2`) independent of x without the
  `independence:` finding that the Integration faithfulness check requires;
  the finding is added.
- The strengthened variant of 3.3 #22 distributed unproved was false: at
  `n = 0` the integrand is defined around `x = -d/e`, where the residual
  integrand is not. It now also appends `n ≠ 0`, and is proved over ℝ.

### Removed
- 11 strengthened variants distributed unproved, refuted by a pole probe of the
  numerical check (a residual integrand or the result undefined where the
  integrand is defined), among them 1.1.3.3 #18 at `n = 1`, `p = 0`. The
  `numerical:` findings now describe both passes.

### Changed
- The nine rules of `OSR/IntegrationRec155.lean` (6.7.7 #1 to #4, #7 and
  4.7.7 #13, #14, #17, #18) carry a `domain:` finding: their proofs cover only
  the case where `F^(c (a + b x))` is constant, the only one the fragment can
  state (`b c = 0`).
- The Integration documentation page is split: the strengthened variants and
  the later proof batches move to `docs/integration-proofs.md`, which keeps the
  generated HTML pages under the Documenter size threshold.
- `just check` can replay modules with `leanchecker` in parallel:
  `OSR_CHECK_JOBS=N` runs `N` replays at once (default 1). With 8 jobs the
  replay of the 175 modules takes about two minutes.
- The Integration catalogue is split into parts of at most 100 entries
  (`catalogPart1` …), each with its own well-formedness theorem: the single
  list literal reached the code generator's recursion limit at 411 entries.
  `Integration.catalog` is their concatenation, in the same order.
- Report the three unmigrated structural derivative rules as lacking the
  differentiability assumptions needed by their operands, in addition to
  using the non-OpenMath `osr#Apply` construct. The v1 format cannot express
  these premises, so no assumptions were added silently.

### Added
- Prove the previously unproved strengthened RUBI substitution rule 3.1.2 #7
  over ℝ and ℂ, including the local definedness of the residual integrand.
- Refute the strengthened RUBI substitution rule 3.1.2 #2 over ℂ at the
  principal logarithm's branch cut, while retaining its real proof.
- Prove the previously unproved strengthened RUBI substitution rule 3.1.2 #2
  over ℝ, including local definedness of its residual integral. Its complex
  case remains unproved, and the original refuted rule remains in the catalogue.
- A separate order-free generalization of RUBI 1.1.3.4 #16 is proved over ℝ
  and ℂ using its exponent relation and nonzero denominator conditions.
- A separate order-free generalization of RUBI 1.1.3.4 #27 is proved over ℝ
  and ℂ using only its nonzero denominator condition.
- A separately identified order-free generalization of RUBI 1.1.3.4 #29 is
  proved over ℝ and ℂ, with nonzero `e` and denominator conditions. It
  preserves the strengthened variant and admits negative integer exponents.
- A separately identified order-free generalization of RUBI 1.1.3.4 #28 is
  proved over ℝ and ℂ and certified on both domains. Its single denominator
  condition replaces the original conditions; the original rule is retained.
- `integration.rubi_1_1_3_4_r28_nondegenerate` and `...r29_nondegenerate`
  are proved over ℝ and ℂ in `OSR/IntegrationRec205.lean` and
  `OSR/IntegrationRec206.lean`, including their residual integrals.
- `integration.rubi_1_1_3_4_r27_nondegenerate` is proved over ℝ and ℂ in
  `OSR/IntegrationRec204.lean`, including its polynomial residual integral.
- `integration.rubi_1_1_3_4_r16_nondegenerate` is proved over ℝ and ℂ in
  `OSR/IntegrationRec203.lean`, including its scaled residual integral.
- `integration.rubi_1_1_3_4_r15_nondegenerate` is proved over ℝ and ℂ in
  `OSR/IntegrationRec202.lean`, including the monomial factor.
- `integration.rubi_1_1_1_3_r19_nondegenerate` is proved over ℝ and ℂ in
  `OSR/IntegrationRec201.lean`, including its residual integral.
- `integration.rubi_1_1_3_2_r7_nondegenerate` is proved over ℝ and ℂ in
  `OSR/IntegrationRec200.lean`, using the binomial product identity.
- `integration.rubi_1_1_3_2_r4_nondegenerate` is proved over ℝ and ℂ in
  `OSR/IntegrationRec199.lean`, including the zero case for integer powers.
- `integration.rubi_1_1_3_3_r8_nondegenerate` is proved over ℝ and ℂ in
  `OSR/IntegrationRec198.lean`.  Its two algebraic equality conditions cancel
  the nonconstant coefficients in the differentiated result.
- `integration.rubi_1_1_3_3_r11_nondegenerate` is proved over ℝ and ℂ in
  `OSR/IntegrationRec197.lean`.  The conditions make the product of its two
  binomials a binomial in `x^n`; differentiating the stated result establishes
  the rule when `a1 * a2 ≠ 0`.
- 39 more strengthened variants are distributed unproved (827 in all):
  24 whose definedness failures came from the approximate solution of an
  equality condition (a value of about 2·10⁻⁷ instead of 0, an exponent
  2.999999999999999 instead of 3), and 15 whose exact check reached ten
  points with more samples. The catalogue has 2875 rules: 474 proved, 1574
  refuted and 827 unproved over ℝ; 286 proved (146 certified), 376 refuted
  and 2213 unproved over ℂ.
- 184 more strengthened variants are distributed unproved
  (`OSR/IntegrationNum1.lean`, 788 in all). Their numerical check now also
  computes the derivative of the result symbolically and compares it with the
  integrand to 50 digits at rational assignments, with equality conditions
  solved exactly: the float check had reported rounding errors near poles
  and for large values as failures. The 604 variants of the previous report
  are confirmed. The catalogue has 2836 rules: 474 proved, 1574 refuted and
  788 unproved over ℝ; 286 proved (146 certified), 376 refuted and 2174
  unproved over ℂ.
- 604 strengthened variants of refuted RUBI rules are distributed unproved
  (`OSR/IntegrationNum1.lean`, Specification V1-R-005e), each with a
  `numerical:` finding. A variant appends `c ≠ 0` for each `x`-free base `c`
  raised to a negative power that vanishes at the counterexample (one
  condition for most, two for a few); the definedness search finds no
  counterexample to it, and an adversarial numerical check over ℝ (each
  metavariable 0 with probability 0.4, plus the real zeros of the bases
  raised to a negative power) finds no failure on at least 30 points. The
  refuted rules stay refuted as stated. The catalogue has 2652 rules:
  474 proved, 1574 refuted and 604 unproved over ℝ; 286 proved (146
  certified), 376 refuted and 1990 unproved over ℂ.
- Derivative rules may have conditions (`DerivHoldsUnder`; `conditionsOk`
  accepts them, `apply?` applies a conditional derivative rule only when its
  conditions are decided true, and `apply?_sound` covers it through
  `deriv_instance_under`). The strengthened power rule
  `calculus.derivative.power_nonzero` (`n ≠ 0`) is proved over ℝ and ℂ;
  `calculus.derivative.power` stays refuted. The reference rewriter now
  rewrites `diff(λt. t³)` to `λt. 3 t^(3 - 1)`.
- Shape `antiderivSubst` and field `CRule.substs` for residual integrals
  evaluated at an expression of the bound variable, `int(λx. H)(g)` (v0.1
  `Subst[Int[H, x], x, g]`, V1-E-002b): statement `AntiderivSubstHolds`
  (helpers `substAt`, `substEnv`), refutation lemmas
  `not_antiderivSubstHolds_integrand` and `not_antiderivSubstHolds_result`,
  `recOk` checks of the substitutions, and export of the hole at `g`. A test
  rule (∫ 2x cos(x²) dx = int(λx. cos x)(x²)) is proved over ℝ by the chain
  rule (`OSRTest/Calculus.lean`).
- 275 RUBI rules written with `Subst` are migrated (shape `antiderivSubst`)
  and refuted over ℝ (`OSR/IntegrationRec194.lean` to
  `OSR/IntegrationRec196.lean`), at degenerate coefficients where the result
  or a residual integrand at its substitution is undefined. The catalogue
  has 2048 rules (2355 RUBI rules considered): 474 proved and 1574 refuted
  over ℝ; 286 proved (146 certified), 376 refuted and 1386 unproved over ℂ.
- Conditions `Cond.ge` (`relation1#geq`, both operands defined and the first
  greater than or equal to the second; real only, like `relation1#gt`) and
  `Cond.or` (binary `logic1#or`, which holds when one side holds), with
  their decision (`Cond.decide?`, proved sound), substitution, export and
  registry entries (`relation1#geq` with its CMP over ℝ; `logic1#or` now also
  interpreted over ℝ and ℂ as the disjunction of conditions, with its two
  CMPs). RUBI's `GeQ`, `LeQ`, `Not[LtQ]`, `Not[GtQ]` and `Or` conditions can
  now be stated.
- 54 more RUBI rules are migrated and refuted over ℝ
  (`OSR/IntegrationRec193.lean`): their compound conditions are put in
  conjunctive normal form (`Or` distributes over `And`, `Not` moves inward,
  the negation of a comparison is the opposite comparison), as the
  faithfulness check now reads them. The catalogue has 1773 rules (2080
  RUBI rules considered): 474 proved and 1299 refuted over ℝ; 286 proved
  (146 certified), 376 refuted and 1111 unproved over ℂ.
- 33 RUBI rules with `Or` conditions (`logic1#or`) are migrated and refuted
  over ℝ (`OSR/IntegrationRec192.lean`); the migration tooling had read the
  disjuncts of `Or` as expressions, so these rules were not translated
  before. The catalogue has 1719 rules (2026 RUBI rules considered): 474
  proved and 1245 refuted over ℝ; 286 proved (146 certified), 376 refuted
  and 1057 unproved over ℂ.
- 77 RUBI rules with such conditions (all with `relation1#geq`) are migrated
  and refuted over ℝ (`OSR/IntegrationRec190.lean`,
  `OSR/IntegrationRec191.lean`), found by the definedness search over the
  145 rules the new conditions make translatable. The catalogue has 1686
  rules (1993 RUBI rules considered): 474 proved and 1212 refuted over ℝ;
  286 proved (146 certified), 376 refuted and 1024 unproved over ℂ.
- 10 more RUBI rules are refuted over ℝ (`OSR/IntegrationRec187.lean` to
  `OSR/IntegrationRec189.lean`): seven earlier counterexamples whose Lean
  proof now checks, as the generated tactics also try `grind`, and three
  found by a second definedness search with another seed. The catalogue
  has 1609 rules (1916 RUBI rules considered): 474 proved and 1135 refuted
  over ℝ; 286 proved (146 certified), 376 refuted and 947 unproved over ℂ.
- 14 more RUBI rules whose result is a sum of residual integrals are proved
  over ℝ, 11 also over ℂ (`OSR/IntegrationRec186.lean`): 4.1.3.1 #36,
  4.1.5 #27 and #28, 4.3.2.1 #10 and #49, 4.3.3.1 #24, 4.3.4.1 #7, #10 and
  #11, 4.3.4.2 #20 and #21, 4.5.2.1 #11, and 6.7.9 #45 and #48 (`sinh` and
  `cosh` times `tanh`, split into exponentials). The algebraic step now
  also tries `grind`, which uses the `EqQ` conditions, and an expansion of
  the hyperbolic functions into exponentials. The catalogue has 1599 rules
  (1906 RUBI rules considered): 474 proved and 1125 refuted over ℝ; 286
  proved (146 certified), 376 refuted and 937 unproved over ℂ.
- 11 more RUBI rules whose result is a sum of terms `c ∫ H`, `c x` and `c`
  (`c` free of `x`) are proved over ℝ, five also over ℂ
  (`OSR/IntegrationRec185.lean`): 4.3.1.1 #12, 4.3.4.1 #8, 4.5.1.1 #7,
  4.5.1.2 #51, 4.5.2.1 #12, 4.5.3.1 #10, 4.5.4.1 #18 and #19, and 5.3.4
  #42, #139 and #141. The proof builds the derivative from the shape of the
  result and matches it by `convert`. The catalogue has 1585 rules (1892
  RUBI rules considered): 460 proved and 1125 refuted over ℝ; 275 proved
  (135 certified), 376 refuted and 934 unproved over ℂ.
- 65 more RUBI rules are refuted over ℝ: 42 with `Acoth` whose
  counterexample now checks, as the generated tactics bound `w⁻¹` near the
  point (`OSR/IntegrationRec182.lean`, `OSR/IntegrationRec183.lean`), and 23
  with `Acot[u]`, transcribed as `arctan(u^-1)` (`OSR/IntegrationRec184.lean`).
  With the eight duplicates removed, the catalogue has 1574 rules (1881 RUBI
  rules considered): 449 proved and 1125 refuted over ℝ; 270 proved (133
  certified), 376 refuted and 928 unproved over ℂ.
- 11 more RUBI rules whose result is a combination of residual integrals
  are proved over ℝ (`OSR/IntegrationRec181.lean`), three of them also over
  ℂ: the partial fractions in `sin` and `tan` 4.1.2.1 #14 and 4.3.2.1 #29,
  `(A + C tan²)/tan` (4.3.4.1 #9), the splits of `(a + b arccoth(c x)) u`
  (7.3.1 #62, #159, #161, 7.3.4 #42, #139, #141) and of
  `(c + d csc) √(a + b csc)` (4.5.2.1 #13, #19). The catalogue has 1517
  rules (1824 RUBI rules considered): 454 proved and 1063 refuted over ℝ;
  275 proved (138 certified), 376 refuted and 866 unproved over ℂ.
- RUBI rules written with `Acoth[u]` are transcribed with `arctanh(u^-1)`
  (the same value; the fragment has no `transc1#arccoth`); 12 are refuted
  over ℝ (`OSR/IntegrationRec179.lean`, `OSR/IntegrationRec180.lean`). 200
  more RUBI rules are reported in `Integration.notMigrated` (520 in all):
  their conditions require an exponent of the integrand not to be an
  integer, so the integrand is nowhere defined in the fragment. The
  catalogue has 1506 rules (1813 RUBI rules considered): 443 proved and 1063
  refuted over ℝ; 272 proved (135 certified), 376 refuted and 858 unproved
  over ℂ.
- 114 more RUBI rules are refuted over ℝ (`OSR/IntegrationRec176.lean` to
  `OSR/IntegrationRec178.lean`): counterexamples found earlier whose Lean
  proof did not check now do, as the generated definedness tactics decide
  the sign of `sin`, `cos`, `csc` and `sec` at a point or near it (bounds
  `3 < π < 3.15`) and the integrality of literal exponents. The catalogue
  has 1494 rules (1601 RUBI rules considered): 443 proved and 1051 refuted
  over ℝ; 272 proved (135 certified), 376 refuted and 846 unproved over ℂ.
- 185 more RUBI rules written with RUBI's inert trig functions `sin`, `cos`,
  `tan`, `cot`, `sec` and `csc` (read as `Sin`, …, `Csc`) are migrated and
  refuted over ℝ (`OSR/IntegrationRec173.lean` to
  `OSR/IntegrationRec175.lean`; 148 from 4.1, 32 from 4.3), found by the
  definedness search. The catalogue has 1380 rules (1487 RUBI rules
  considered): 443 proved and 937 refuted over ℝ; 272 proved (135
  certified), 376 refuted and 732 unproved over ℂ.
- Five RUBI rules whose result is a combination of residual integrals with
  coefficients free of `x` are proved over ℝ and ℂ
  (`OSR/IntegrationRec172.lean`): the partial fractions 1.1.1.2 #3,
  1.2.1.2 #78 and #79, and 4.1.12 #3 and #4 (`sin` and `cos` of `c + u`).
  The catalogue has 1195 rules (1302 RUBI rules considered): 443 proved and
  752 refuted over ℝ; 272 proved (135 certified), 376 refuted and 547
  unproved over ℂ.
- 91 more RUBI rules are migrated and refuted over ℝ
  (`OSR/IntegrationRec170.lean`, `OSR/IntegrationRec171.lean`), found by the
  definedness search; 89 of them are written with `Simp[e]` or `Simp[e, x]`,
  now read as `e` (`And`, `Not[EqQ]` and `Not[NeQ]` conditions are now
  flattened too). The catalogue has 1190 rules
  (1297 RUBI rules considered): 438 proved and 752 refuted over ℝ; 267
  proved (130 certified), 376 refuted and 547 unproved over ℂ.
- RUBI rules with exponentials written `E^u` are migrated: `E^u` reads as
  `exp(u)` (`transc1#exp`). 14 are proved over ℝ and ℂ
  (`OSR/IntegrationRec169.lean`: 6.1.12 #1, #2, #7, #8, #29, #30, #55, #56,
  6.1.13 #1, #2 and 6.7.9 #91 to #94, which split `sinh` and `cosh` into
  exponentials) and 10 are refuted over ℝ at degenerate coefficients
  (`OSR/IntegrationRec168.lean`). The catalogue has 1099 rules (1206 RUBI
  rules considered): 438 proved and 661 refuted over ℝ; 267 proved (130
  certified), 376 refuted and 456 unproved over ℂ.
- 279 more RUBI rules are reported in `Integration.notMigrated` (320 in all):
  in 147 the integrand raises an expression to an exponent with denominator 2,
  3, 4 or 6, and in 132 it contains a power `F^(…)` with a non-constant
  exponent; the fragment interprets `arith1#power` for integer exponents only,
  so these integrands are nowhere (or, for `F^(…)`, only degenerately)
  defined. Rules whose pattern contains `E` (exponentials written `E^u`) are
  not reported yet. 7.2.5 #17 is migrated and refuted over ℝ
  (`OSR/IntegrationRec167.lean`). The catalogue has 1075 rules (1182 RUBI
  rules considered): 424 proved and 651 refuted over ℝ; 253 proved (120
  certified), 376 refuted and 446 unproved over ℂ.
- 40 more RUBI rules are migrated and refuted over ℝ
  (`OSR/IntegrationRec166.lean`), from a definedness search over the rules
  not yet considered, now with assignments in halves and integrands defined
  only near the point: the result or a residual integrand divides by a
  coefficient (or takes a logarithm or an inverse function outside its
  domain) that the conditions let vanish while the integrand is defined there.
  They include 7.2.2 #2, #5, 7.2.1 #2, 7.2.4 #42, #43, 7.2.5 #2, 5.1.4 #45,
  #46, 6.7.8 #47 to #50 and families of 1.1.1, 1.1.3, 1.2.1, 1.2.2, 1.2.3,
  3.1.3, 3.2.2, 3.3, 3.5, 7.3.1 and 7.3.4. The catalogue has 1074 rules (902
  RUBI rules considered): 424 proved and 650 refuted over ℝ; 253 proved (120
  certified), 376 refuted and 445 unproved over ℂ.
- Three more RUBI rules are migrated and refuted over ℝ
  (`OSR/IntegrationRec165.lean`): 3.2.3 #9 splits
  `log(e (f (a + b x)^p (c + d x)^q)^r)` into logarithms of factors that can be
  negative where the integrand is defined; 3.4 #1 (at `d = e = 0`) and 3.5 #1
  (at `n = 0`) leave a residual integrand with a zero divisor. The catalogue
  has 1034 rules (862 RUBI rules considered): 424 proved and 610 refuted over
  ℝ; 253 proved (120 certified), 376 refuted and 405 unproved over ℂ.
- Nine more RUBI rules are migrated and refuted over ℝ
  (`OSR/IntegrationRec164.lean`): 1.1.1.4 #33, #35, 1.1.1.7 #9, #12, 1.1.3.3
  #27, 1.1.3.4 #49, 1.2.2.3 #41, 4.7.9 #83 and 7.3.4 #69 divide by a
  coefficient their conditions let vanish while the integrand stays defined
  everywhere. The witnesses come from a definedness search over the rules not
  yet considered whose result divides by a coefficient expression. The
  catalogue has 1031 rules (859 RUBI rules considered): 424 proved and 607
  refuted over ℝ; 253 proved (120 certified), 376 refuted and 402 unproved
  over ℂ.
- Five more RUBI rules are migrated (`OSR/IntegrationRec163.lean`): 1.3.3 #24
  (`√(e x (a x + b √(c + d x²)))` distributed) and 6.7.9 #76
  (`csch² u/(c + b coth² u)` with `cosh 2u`) are proved over ℝ; 1.3.3 #36,
  1.2.1.5 #17 and 1.2.1.6 #26 are refuted over ℝ where the conditions let the
  divisor `d`, `f` or `2 f` of the result vanish while the integrand is
  defined. The catalogue has 1022 rules (850 RUBI rules considered): 424 proved
  and 598 refuted over ℝ; 253 proved (120 certified), 376 refuted and 393
  unproved over ℂ.
- Ten more RUBI rules are migrated and refuted (`OSR/IntegrationRec162.lean`),
  each at a single point the numerical sampling misses: 1.2.2.8 #1, #2 and
  1.3.3 #6 split `1/((d + e x) √Q)` with `(d² - e² x²)⁻¹`, undefined at
  `d = e x`; 1.2.2.3 #47, #48, #51, #52 and 1.2.2.4 #71, #72 rewrite with
  `√(e + d/x²)`, undefined at `x = 0`; 3.1.2 #12 (also over ℂ) divides by
  `x^(m₁ q₁ + m₂ q₂)`. The catalogue has 1017 rules (845 RUBI rules
  considered): 422 proved and 595 refuted over ℝ; 253 proved (120
  certified), 376 refuted and 388 unproved over ℂ.
- Six more RUBI rules are migrated (`OSR/IntegrationRec161.lean`): integrations
  by parts of `(e x)^m sinh(c + d xⁿ)`, `(e x)^m cosh(c + d xⁿ)` (6.1.12 #27,
  #28) and of `x^m sin^p(a + b xⁿ)`, `x^m cos^p(a + b xⁿ)` with `m + n = 0`
  (4.1.12 #41, #42), proved over ℝ and ℂ, and of
  `(a + b log(c (d + e x)ⁿ))^p/(f + g x)²` (3.3 #9) over ℝ; 5.3.5 #7 is refuted
  over ℝ and ℂ at `f = 0`, where the result's `(f (m + 1))^(-1)` is undefined.
  The catalogue has 1007 rules (835 RUBI rules considered): 422 proved and 585
  refuted over ℝ; 253 proved (120 certified), 375 refuted and 379 unproved
  over ℂ.
- Four more RUBI rules are migrated (`OSR/IntegrationRec159.lean`,
  `IntegrationRec160`): 5.3.4 #144, 6.3.12 #3 and #4 are refuted over ℝ
  (6.3.12 #3 over ℂ too) by explicit assignments at which the integrand is
  defined but the result is not, and 1.2.2.3 #25 is proved over ℝ by
  linearity. The catalogue has 1001 rules (829 RUBI rules considered): 417
  proved and 584 refuted over ℝ; 249 proved (120 certified), 374 refuted and
  378 unproved over ℂ.
- Eight more RUBI rules are migrated (`OSR/IntegrationRec157.lean`,
  `IntegrationRec158`): 4.7.6 #4, #5 and 6.7.6 #4 are refuted over ℝ and ℂ (at
  `n = 1` a residual integrand keeps `sin^(-1)`, `cos^(-1)` or `sinh^(-1)` where
  the integrand is defined); 7.3.1 #1 and 7.3.4 #41, 7.3.7 #41
  (`artanh(tan(a + b x))`) are proved by parts, and 6.7.9 #73 (also over ℂ) and
  #75 with `2 (a + b cosh² u + c sinh² u) = 2a + b - c + (b + c) cosh 2u`. The
  catalogue has 997 rules (825 RUBI rules considered): 416 proved and 581
  refuted over ℝ; 249 proved (120 certified), 373 refuted and 375 unproved
  over ℂ.
- 21 more RUBI rules are migrated, 19 of them proved and two refuted over ℝ
  (`OSR/IntegrationRec153.lean` to `IntegrationRec156`): products
  `F(a + b x) G(c + d x)` with `b² = d²` by the addition formulas (6.7.9 #86 to
  #89, 4.7.9 #96, #97); 4.7.9 #94 and #95 refuted at `c - a = π`, where the
  result's `csc π` is undefined; `F^(c (a + b x))` times sinh, cosh, sec or csc
  powers, where definedness on a neighbourhood forces `b c = 0`
  (`int_valued_const`) (6.7.7 #1 to #4, #7, 4.7.7 #13, #14, #17, #18); and
  `sinh` and `cosh` of `d (a + b log(c xⁿ))` (6.7.8 #3 to #6). The catalogue has
  989 rules (817 RUBI rules considered): 411 proved and 578 refuted over ℝ; 248
  proved (120 certified), 370 refuted and 371 unproved over ℂ.
- 48 more RUBI rules are migrated and proved over ℝ, eight of them over ℂ
  too (`OSR/IntegrationRec142.lean` to `IntegrationRec152`):
  `(d₁ + e₁ x)^p (d₂ + e₂ x)^p = (d₁ d₂ + e₁ e₂ x²)^p` (7.2.3 #1, 7.2.4 #1);
  the double-argument formula of sinh (6.7.9 #70); `(a + b x^n)^p =
  x^(n p) (b + a x^(-n))^p` for negative `n` and `p` (6.1.11 #7, #8, #19, #20);
  `log(f + g x²)` split into logarithms when `g = -c² f` (7.3.4 #136,
  7.3.1 #156); `sec² u/(b + a sec² u + c tan² u)` with `cos 2u` (4.7.9 #72 to
  #75); reductions of `trig^n/(a + b trig)` (4.7.9 #17 to #20, 6.7.9 #8, #16 to
  #18); `tan² = sec² - 1` and its hyperbolic forms (4.7.6 #10 to #13, 6.7.6 #5,
  #10 to #13); arctanh of `a + b f^(c + d x)` split into logarithms (7.3.4 #7,
  #9, 7.3.7 #7, #9); a locally constant factor `√(a + b x²)/√(d + e x²)`
  (5.3.7 #23, 7.3.4 #23, 7.3.7 #23); half-argument forms of `g (1 ± cosh u)`
  (6.7.7 #24, #25, #30); and integration by parts of `x^m (a + b F(c x))^n` for
  arcsin, arccos, arsinh and arcosh (5.1.1 #1, #2, 5.1.2 #5, #6, 7.1.1 #1,
  7.1.2 #3, 7.2.1 #1, 7.2.2 #3). The catalogue has 968 rules (796 RUBI rules
  considered): 392 proved and 576 refuted over ℝ; 248 proved (120 certified),
  370 refuted and 350 unproved over ℂ.
- Six more RUBI rules are migrated and proved over ℝ by splits with a shifted
  exponent: `1/(d + e x) = 1/d - e x/(d (d + e x))` for 7.3.4 #5, 7.3.1 #25 and
  5.3.4 #5 (`OSR/IntegrationRec140.lean`), and `d (d + e x²)^q = (d + e x²)^(q+1)
  - e x² (d + e x²)^q` for 7.3.4 #95, 7.3.1 #115 and 5.3.4 #95
  (`IntegrationRec141`); the conditions force `d ≠ 0`. The catalogue has 920
  rules (748 RUBI rules considered): 344 proved and 576 refuted over ℝ; 240
  proved (119 certified), 370 refuted and 310 unproved over ℂ.
- Eight more RUBI rules are migrated and proved over ℝ by linear splits
  with integer exponents (`OSR/IntegrationRec139.lean`): 7.3.4 #107 and
  7.3.1 #127 (linearity), 7.3.4 #130, 7.3.1 #150, 7.3.7 #3 and 7.3.4 #3
  (arctanh into logarithms), and 6.1.12 #19 and #20 (addition formulas of
  sinh and cosh). The catalogue has 914 rules (742 RUBI rules considered):
  338 proved and 576 refuted over ℝ; 240 proved (119 certified), 370 refuted
  and 304 unproved over ℂ.
- 7.3.4 #39 and 7.3.1 #59 are migrated and proved over ℝ
  (`OSR/IntegrationRec138.lean`): `artanh u = (log(1 + u) - log(1 - u))/2` on
  `(-1, 1)` splits the integrand into the two residual integrands. The
  catalogue has 906 rules (734 RUBI rules considered): 330 proved and 576
  refuted over ℝ; 240 proved (119 certified), 370 refuted and 296 unproved
  over ℂ.
- Six more RUBI rules are migrated and proved over ℝ by integration by parts:
  `(a + b A(c x))^p/(x² √(d + e x²))` and `(f x)^m (a + b A(c x))^p/√(d + e x²)`
  for `A = artanh` with `c² d + e = 0` and `A = arctan` with `e = c² d`
  (7.3.4 #89, #91, 7.3.1 #109, #111, 5.3.4 #89, #91;
  `OSR/IntegrationRec136.lean`, `IntegrationRec137`). The catalogue has 904
  rules (732 RUBI rules considered): 328 proved and 576 refuted over ℝ; 240
  proved (119 certified), 370 refuted and 294 unproved over ℂ.
- Five more RUBI rules are migrated and proved over ℝ by integration by
  parts: arctan(tanh(a + b x)) and arctan(coth(a + b x)) (5.3.7 #43, #45;
  `OSR/IntegrationRec134.lean`, with the derivatives of tanh and coth of a
  linear argument), and arctanh(c x/√(a + b x²)) with `b = c²` and
  arctan(c x/√(a + b x²)) with `b = -c²` (7.3.4 #13, 7.3.7 #13, 5.3.7 #13;
  `IntegrationRec135`). The catalogue has 898 rules (726 RUBI rules
  considered): 322 proved and 576 refuted over ℝ; 240 proved (119 certified),
  370 refuted and 288 unproved over ℂ.
- Ten more RUBI rules not considered before are migrated and proved over ℝ
  by integration by parts: `∫ A(u) = x A(u) - ∫ x u' A'(u)` for arctanh and
  arctan of `a + b xⁿ` or `c xⁿ` (7.3.4 #1, 7.3.7 #1, 7.3.1 #168, 5.3.7 #1;
  `OSR/IntegrationRec131.lean`), and `(d + e log(f + g x²)) (a + b A(c x))`
  with or without a factor `xᵐ` (7.3.4 #134, #142, 7.3.1 #154, #162, 5.3.4
  #134, #142; `IntegrationRec132`, `IntegrationRec133`). Mathlib has no
  derivative of `Real.artanh`; `OSR.IntegrationRec131.hasDerivAt_artanh`
  derives it from `Real.artanh_eq_half_log`. The catalogue has 893 rules
  (721 RUBI rules considered): 317 proved and 576 refuted over ℝ; 240 proved
  (119 certified), 370 refuted and 283 unproved over ℂ.
- 19 more RUBI rules not considered before are migrated and refuted over ℝ
  (`OSR/IntegrationRec130.lean`); their counterexample theorems needed the
  values of sin, cos and sinh at small integers to be nonzero. They stay
  unproved over ℂ. The catalogue has 883 rules (711 RUBI rules considered):
  307 proved and 576 refuted over ℝ; 240 proved (119 certified), 370 refuted
  and 273 unproved over ℂ.
- 14 more RUBI rules not considered before are migrated and proved as
  stated: twelve split by linearity into residual integrals with constant
  coefficients (5.3.4 #41, #132, #138, #140 over ℝ and ℂ; 7.3.4 #41, #132,
  #138, #140 and 7.3.1 #61, #152, #158, #160 over ℝ, their arctanh having no
  complex interpretation; `OSR/IntegrationRec128.lean`), and 5.3.4 #107 and
  6.7.7 #33 over ℝ (`IntegrationRec129`). The catalogue has 864 rules (692
  RUBI rules considered): 307 proved and 557 refuted over ℝ; 240 proved
  (119 certified), 370 refuted and 254 unproved over ℂ.
- 247 RUBI rules not considered before are migrated and refuted as stated
  (`OSR/IntegrationRec120.lean` … `IntegrationRec127`): for each, an explicit
  assignment satisfies the conditions and makes the integrand defined near a
  point where the result or a residual integrand is not. All are refuted
  over ℝ; 53 also over ℂ. The other 194 are unproved over ℂ, most because
  their integrand uses a function without a complex interpretation in the
  fragment (sec, csc, coth, sech, csch, the inverse functions other than
  arctan, or the square root), so it is nowhere defined there. They use the
  `transc1` mappings of reciprocal, hyperbolic and inverse functions and the
  `Sqrt` → `root(a, 2)` reading now committed in Integration. The catalogue
  has 850 rules (678 RUBI rules considered): 293 proved and 557 refuted over
  ℝ; 236 proved (119 certified), 370 refuted and 244 unproved over ℂ.
- Nine RUBI rules not considered before, now migrated and proved over ℝ and
  ℂ as RUBI states them: 1.2.3.3 #41, #42 and #47 and 1.2.3.4 #92, #93 and
  #100 (`OSR/IntegrationRec118.lean`), which rewrite `(a + b x^(-n) + c
  x^(-2n))^p` as `x^(-2np) (c + b xⁿ + a x^(2n))^p`, and the reductions
  1.2.1.2 #93, #94 and #95 with `m + 2p + 2 = 0` (`IntegrationRec119`). They
  are the first entries of `catalogPart7`. The catalogue has 603 rules (431
  RUBI rules considered): 293 proved and 310 refuted over ℝ; 236 proved (130
  certified), 317 refuted and 50 unproved over ℂ.
- Seven more variants, proved over ℝ and ℂ: 1.3.1 #4 and 1.3.2 #1
  (`OSR/IntegrationRec116.lean`), whose reported numerical failures were an
  artefact of the check's overflow guard, and 2.3 #11, #23, #24, #26 and #35
  with `F > 0` (`IntegrationRec117`). The catalogue has 594 rules: 284 proved
  and 310 refuted over ℝ; 227 proved (113 certified), 317 refuted and 50
  unproved over ℂ.
- Six more variants whose candidates had failed the numerical truth check,
  proved with a tighter exponent bound or more `≠ 0` conditions: 1.2.2.4 #59
  and #60 (with `m > 3`) and #61 and #62 (with `m > 1`), whose residual
  integrands have a pole at `x = 0` for `m = 3` (resp. `m = 1`), and 1.1.1.3
  #53 (with `m, n > 0`), over ℝ and ℂ (`OSR/IntegrationRec113.lean`,
  `IntegrationRec115`); and 3.4 #7 (`integration.power_log_binomial`, with
  `p, n ≠ 0`) over ℝ only (`IntegrationRec114`). The catalogue has 587 rules:
  277 proved and 310 refuted over ℝ; 220 proved (111 certified), 317 refuted
  and 50 unproved over ℂ.
- Eight variants whose candidates had failed the numerical truth check at a
  single zero, proved with one more `≠ 0` condition: 1.1.3.7 #5 (with
  `B ≠ 0`) over ℝ and ℂ (`OSR/IntegrationRec110.lean`), and 3.3 #29, #30, #31
  and #39, 3.4 #27, 3.5 #3 and 3.1.5 #33 (with the exponent, `n`, `p` or `r`,
  nonzero) over ℝ only (`IntegrationRec111`, `IntegrationRec112`). The
  catalogue has 581 rules: 271 proved and 310 refuted over ℝ; 215 proved
  (111 certified), 317 refuted and 49 unproved over ℂ.
- Eight more such variants proved: 1.1.3.3 #5, 1.2.1.3 #26 and 1.2.3.4 #61 and
  #64 over ℝ and ℂ (`OSR/IntegrationRec105.lean`, `IntegrationRec108`,
  `IntegrationRec109`), and 3.1.4 #10, 3.1.4 #22 (with `n ≠ 0`), 3.3 #12 and
  3.2.3 #8 (with `p, q, r ≠ 0`) over ℝ only (`IntegrationRec106`,
  `IntegrationRec107`). The catalogue has 573 rules: 263 proved and 310 refuted
  over ℝ; 214 proved (110 certified), 317 refuted and 42 unproved over ℂ.
- Fifteen strengthened variants whose candidates had been sampled too rarely
  (an `EqQ` condition), sampled again with the equalities solved and proved
  over ℝ and ℂ: 1.2.1.2 #5, #40, #46 and #96, 1.2.3.2 #10 and #18, 1.2.3.3 #27
  and #50, 1.2.3.4 #34, #38 and #40, and 4.1.12 #45, #46, #53 and #54
  (`OSR/IntegrationRec99.lean` to `IntegrationRec104`). The catalogue has 565
  rules: 255 proved and 310 refuted over ℝ; 210 proved (110 certified), 317
  refuted and 38 unproved over ℂ.
- Eight strengthened variants that the pole probe had refuted, corrected with
  one more nonzero exponent and proved: 1.1.3.3 #18 (`p ≠ 0`) over ℝ and ℂ
  (`OSR/IntegrationRec96.lean`); 3.3 #7, 3.2.1 #13 and 3.5 #23 (`n ≠ 0`,
  `IntegrationRec97`), 3.2.1 #2 (`n ≠ 0`) and 3.2.3 #2, #4 and #7
  (`p, q, r ≠ 0`, `IntegrationRec98`) over ℝ only. The catalogue has 550
  rules: 240 proved and 310 refuted over ℝ; 195 proved (109 certified), 317
  refuted and 38 unproved over ℂ.
- Strengthened variants of nineteen refuted named rules, which the triage of
  variants had skipped, proved directly: 1.1.1.3 #8, 1.1.1.4 #17, 1.1.3.3 #14,
  1.1.3.5 #2 and #10, 1.2.1.2 #13 and #14, 1.2.1.3 #11 and #12, and 4.1.13 #3,
  #4, #17 and #18 over ℝ and ℂ (`OSR/IntegrationRec92.lean` to
  `IntegrationRec94`); 3.1.2 #1 and #4 and 4.7.8 #11, #12, #45 and #46 over ℝ
  only (`IntegrationRec95`). The catalogue has 542 rules: 232 proved and 310
  refuted over ℝ; 194 proved (108 certified), 317 refuted and 31 unproved
  over ℂ.
- Proofs of the last twelve strengthened variants distributed unproved:
  4.1.12 #43 and #44, 1.1.1.4 #3 and #6, 1.2.1.3 #33, 1.1.3.3 #16 and
  1.1.3.4 #25 over ℝ and ℂ (`OSR/IntegrationRec82.lean`, `IntegrationRec87` to
  `IntegrationRec91`), and 4.7.8 #13 and #14, 3.4 #2, 3.2.1 #1 and 3.3 #22 over
  ℝ only, with the real logarithm (`IntegrationRec83` to `IntegrationRec86`).
  `OSR.IntegrationNum1.entries` is now empty. The catalogue has 523 rules: 213
  proved and 310 refuted over ℝ; 181 proved (96 certified), 317 refuted and
  25 unproved over ℂ.
- Proofs of 2.1 #9 and #10 over ℝ and ℂ, first distributed unproved
  (`OSR/IntegrationRec81.lean`). The catalogue has 523 rules: 201 proved, 310
  refuted and 12 unproved over ℝ; 174 proved (92 certified), 317 refuted and 32
  unproved over ℂ.
- Proof of 1.2.3.1 #5 over ℝ and ℂ, first distributed unproved
  (`OSR/IntegrationRec80.lean`). The catalogue has 523 rules: 199 proved, 310
  refuted and 14 unproved over ℝ; 172 proved (92 certified), 317 refuted and 34
  unproved over ℂ.
- Proofs over ℝ only of 3.5 #16 and #21, first distributed unproved
  (`OSR/IntegrationRec79.lean`). The catalogue has 523 rules: 198 proved, 310
  refuted and 15 unproved over ℝ; 171 proved (92 certified), 317 refuted and 35
  unproved over ℂ.
- Proof over ℝ only of 3.1.5 #28, first distributed unproved
  (`OSR/IntegrationRec78.lean`). The catalogue has 523 rules: 196 proved, 310
  refuted and 17 unproved over ℝ; 171 proved (92 certified), 317 refuted and 35
  unproved over ℂ.
- Proof over ℝ only of 3.1.2 #3, first distributed unproved
  (`OSR/IntegrationRec77.lean`). The catalogue has 523 rules: 195 proved, 310
  refuted and 18 unproved over ℝ; 171 proved (92 certified), 317 refuted and 35
  unproved over ℂ.
- Proofs over ℝ only of 4.7.8 #47 and #48, first distributed unproved
  (`OSR/IntegrationRec76.lean`). The catalogue has 523 rules: 194 proved, 310
  refuted and 19 unproved over ℝ; 171 proved (92 certified), 317 refuted and 35
  unproved over ℂ.
- Proof over ℝ only of 3.1.3 #7, first distributed unproved
  (`OSR/IntegrationRec75.lean`). The catalogue has 523 rules: 192 proved, 310
  refuted and 21 unproved over ℝ; 171 proved (92 certified), 317 refuted and 35
  unproved over ℂ.
- Proofs over ℝ only of 3.1.3 #10, 3.1.4 #13 and 3.1.5 #9, first distributed
  unproved (`OSR/IntegrationRec74.lean`); the verified catalogue gains a sixth
  part (`catalogPart6`). The catalogue has 523 rules: 191 proved, 310 refuted
  and 22 unproved over ℝ; 171 proved (92 certified), 317 refuted and 35
  unproved over ℂ.
- Proof over ℝ only of 3.1.3 #1, first distributed unproved
  (`OSR/IntegrationRec73.lean`). The catalogue has 523 rules: 188 proved, 310
  refuted and 25 unproved over ℝ; 171 proved (92 certified), 317 refuted and 35
  unproved over ℂ.
- Proof over ℝ only of the variant of `log_power_over_linear_square`, first
  distributed unproved (`OSR/IntegrationRec72.lean`). The catalogue has 523
  rules: 187 proved, 310 refuted and 26 unproved over ℝ; 171 proved (92
  certified), 317 refuted and 35 unproved over ℂ.
- Proofs over ℝ only of 3.1.4 #2 and 3.1.5 #3, first distributed unproved
  (`OSR/IntegrationRec71.lean`). The catalogue has 523 rules: 186 proved, 310
  refuted and 27 unproved over ℝ; 171 proved (92 certified), 317 refuted and 35
  unproved over ℂ.
- Proofs over ℝ only of 3.1.4 #12 and 3.1.5 #8, first distributed unproved
  (`OSR/IntegrationRec70.lean`). The catalogue has 523 rules: 184 proved, 310
  refuted and 29 unproved over ℝ; 171 proved (92 certified), 317 refuted and 35
  unproved over ℂ.
- Proofs over ℝ only of 3.1.1 #3 and 3.1.2 #5 and #6, first distributed
  unproved (`OSR/IntegrationRec69.lean`); their complex domain stays unproved,
  recorded in a `domain:` finding. The catalogue has 523 rules: 182 proved, 310
  refuted and 31 unproved over ℝ; 171 proved (92 certified), 317 refuted and 35
  unproved over ℂ.
- Proofs of 4.1.12 #33 and #34, first distributed unproved
  (`OSR/IntegrationRec68.lean`). The catalogue has 523 rules: 179 proved, 310
  refuted and 34 unproved over ℝ; 171 proved (92 certified), 317 refuted and 35
  unproved over ℂ.
- Proofs of three variants with `tan` first distributed unproved, 4.7.9 #16,
  #27 and #30 (`OSR/IntegrationRec67.lean`). The catalogue has 523 rules: 177
  proved, 310 refuted and 36 unproved over ℝ; 169 proved (92 certified), 317
  refuted and 37 unproved over ℂ.
- Proofs of six logarithmic variants first distributed unproved, 3.1.4 #9,
  #17 and #18 and 3.1.5 #13, #16 and #17 (`OSR/IntegrationRec66.lean`). The
  catalogue has 523 rules: 174 proved, 310 refuted and 39 unproved over ℝ; 166
  proved (92 certified), 317 refuted and 40 unproved over ℂ.
- Proofs of four variants first distributed unproved, 4.7.9 #11 and #12 and
  2.3 #32 and #33 (`OSR/IntegrationRec65.lean`). The catalogue has 523 rules:
  168 proved, 310 refuted and 45 unproved over ℝ; 160 proved (92 certified), 317
  refuted and 46 unproved over ℂ.
- Proofs of ten variants first distributed unproved, 4.1.13 #1, #2, #13 to
  #16 and #19 to #22 (`OSR/IntegrationRec64.lean`). The catalogue has 523
  rules: 164 proved, 310 refuted and 49 unproved over ℝ; 156 proved (90
  certified), 317 refuted and 50 unproved over ℂ.
- Proofs of eight trigonometric variants first distributed unproved, 4.7.9
  #1, #2, #25 and #26 and 4.7.6 #1, #2, #16 and #17
  (`OSR/IntegrationRec63.lean`). The catalogue has 523 rules: 154 proved, 310
  refuted and 59 unproved over ℝ; 146 proved (88 certified), 317 refuted and 60
  unproved over ℂ.
- Proof of 1.2.1.2 #54, first distributed unproved
  (`OSR/IntegrationRec62.lean`). The catalogue has 523 rules: 146 proved, 310
  refuted and 67 unproved over ℝ; 138 proved (88 certified), 317 refuted and 68
  unproved over ℂ.
- Proofs of two variants first distributed unproved, 1.2.1.2 #45 and #39
  (`OSR/IntegrationRec61.lean`). The catalogue has 523 rules: 145 proved, 310
  refuted and 68 unproved over ℝ; 137 proved (87 certified), 317 refuted and 69
  unproved over ℂ.
- Proofs of three variants first distributed unproved, 1.1.3.5 #30 and
  1.2.1.2 #43 and #44 (`OSR/IntegrationRec60.lean`). The catalogue has 523
  rules: 143 proved, 310 refuted and 70 unproved over ℝ; 135 proved (87
  certified), 317 refuted and 71 unproved over ℂ.
- Proofs of three variants first distributed unproved, 1.1.3.5 #24, #25 and
  #26 (`OSR/IntegrationRec59.lean`). The catalogue has 523 rules: 140 proved,
  310 refuted and 73 unproved over ℝ; 132 proved (87 certified), 317 refuted
  and 74 unproved over ℂ.
- Proofs of two variants first distributed unproved, 1.1.1.3 #13 and #14
  (`OSR/IntegrationRec58.lean`). The catalogue has 523 rules: 137 proved, 310
  refuted and 76 unproved over ℝ; 129 proved (87 certified), 317 refuted and 77
  unproved over ℂ.
- Proofs of two variants first distributed unproved, 1.2.2.1 #5 and 1.2.1.2
  #102 (`OSR/IntegrationRec57.lean`). The catalogue has 523 rules: 135 proved,
  310 refuted and 78 unproved over ℝ; 127 proved (87 certified), 317 refuted
  and 79 unproved over ℂ.
- Proofs of three variants first distributed unproved, 1.2.1.3 #15, 1.2.1.1
  #5 and 1.2.2.2 #17 (`OSR/IntegrationRec56.lean`). The catalogue has 523
  rules: 133 proved, 310 refuted and 80 unproved over ℝ; 125 proved (87
  certified), 317 refuted and 81 unproved over ℂ.
- Proofs of four variants first distributed unproved, 1.1.1.3 #12, 1.1.1.4
  #38, 1.2.1.2 #12 and 1.2.1.3 #16 (`OSR/IntegrationRec55.lean`). The
  catalogue has 523 rules: 130 proved, 310 refuted and 83 unproved over ℝ; 122
  proved (87 certified: order conditions have no certified mapping over ℂ),
  317 refuted and 84 unproved over ℂ.
- Proofs of six variants first distributed unproved, 1.2.1.6 #9, 1.2.1.3 #36
  and 1.2.2.4 #55 to #58 (`OSR/IntegrationRec54.lean`). The catalogue has 523
  rules: 126 proved, 310 refuted and 87 unproved over ℝ; 118 proved (87
  certified: the 1.2.2.4 order conditions have no certified mapping over ℂ),
  317 refuted and 88 unproved over ℂ.
- Proofs of five variants first distributed unproved, 1.2.1.6 #5, #6, #7, #8
  and #10 (`OSR/IntegrationRec53.lean`). The catalogue has 523 rules: 120
  proved, 310 refuted and 93 unproved over ℝ; 112 proved (85 certified), 317
  refuted and 94 unproved over ℂ.
- Proofs of three variants first distributed unproved, 1.2.3.3 #12, #19 and
  #20 (`OSR/IntegrationRec52.lean`). The catalogue has 523 rules: 115 proved,
  310 refuted and 98 unproved over ℝ; 107 proved (80 certified), 317 refuted
  and 99 unproved over ℂ.
- Proofs of four variants first distributed unproved, 1.1.3.4 #17, 1.2.1.3 #35
  and 1.2.2.4 #11 and #12 (`OSR/IntegrationRec51.lean`). The catalogue has 523
  rules: 112 proved, 310 refuted and 101 unproved over ℝ; 104 proved (77
  certified), 317 refuted and 102 unproved over ℂ.
- Proof of the strengthened variant of 1.1.3.4 #24, first distributed unproved
  (`OSR/IntegrationRec50.lean`). The catalogue has 523 rules: 108 proved, 310
  refuted and 105 unproved over ℝ; 100 proved (73 certified), 317 refuted and
  106 unproved over ℂ.
- Proofs of three variants first distributed unproved, 1.2.2.3 #7 and #8 and
  1.1.3.3 #15 (`OSR/IntegrationRec49.lean`); their entries move to the verified
  catalogue. The catalogue has 534 rules: 107 proved, 310 refuted and 117
  unproved over ℝ; 99 proved (72 certified), 317 refuted and 118 unproved over
  ℂ.
- 120 strengthened variants distributed unproved with a numerical check over
  ℝ (`OSR/IntegrationNum1.lean`, Specification V1-R-005e), in their own module
  with their own well-formedness theorem; the finding texts move to
  `OSR/IntegrationFindings.lean`. Strengthened variants of 1.2.1.2 #1 and
  1.2.1.3 #20 with `d ≠ 0` and `e ≠ 0`, and of 1.2.1.3 #19 with `e^p ≠ 0`, proved
  over ℝ and ℂ (`OSR/IntegrationRec48.lean`). The catalogue has 534 rules: 104
  proved, 310 refuted and 120 unproved over ℝ; 96 proved (69 certified), 317
  refuted and 121 unproved over ℂ.
- First strengthened variants of rules with residual integrals: 1.2.1.2 #20
  with `e^p ≠ 0`, #103 with `(m + 1) (c d² - b d e + a e²) ≠ 0` and #104 with
  `(m + 1) (c d² + a e²) ≠ 0`, proved over ℝ and ℂ
  (`OSR/IntegrationRec47.lean`). The catalogue has 411 rules: 101 proved and
  310 refuted over ℝ, 93 proved (66 certified), 317 refuted and one unproved
  over ℂ.
- Strengthened variant of 1.2.1.3 #24 with `c (m + 2 p + 2) ≠ 0` and `e ≠ 0`,
  proved over ℝ and ℂ (`OSR/IntegrationRec46.lean`). The catalogue has 408
  rules: 98 proved and 310 refuted over ℝ, 90 proved (63 certified), 317
  refuted and one unproved over ℂ.
- Strengthened variants of 1.1.1.3 #9 with `d² f² (n + p + 2) (n + p + 3) ≠ 0`
  and 1.2.1.3 #25 with `c (m + 2 p + 2) ≠ 0` and `e ≠ 0`, proved over ℝ and ℂ
  (`OSR/IntegrationRec45.lean`). The catalogue has 407 rules: 97 proved and
  310 refuted over ℝ, 89 proved (62 certified), 317 refuted and one unproved
  over ℂ.
- Strengthened variants of 1.2.1.3 #13 with `2 c² (p + 1) (2 p + 3) ≠ 0` and
  1.1.1.7 #6 with `2 b1 b2 n (p + 1) ≠ 0`, proved over ℝ and ℂ
  (`OSR/IntegrationRec44.lean`). The catalogue has 405 rules: 95 proved and
  310 refuted over ℝ, 87 proved (60 certified), 317 refuted and one unproved
  over ℂ.
- Strengthened variants of 1.2.3.5 #2 with `a ≠ 0` and 1.2.1.3 #14 with
  `2 c (p + 1) (2 p + 3) ≠ 0`, proved over ℝ and ℂ
  (`OSR/IntegrationRec43.lean`). The catalogue has 403 rules: 93 proved and
  310 refuted over ℝ, 85 proved (58 certified), 317 refuted and one unproved
  over ℂ.
- Strengthened variants of 1.2.1.2 #55, 4.1.12 #81 and #82, 1.2.1.4 #65 and
  #66, proved over ℝ and ℂ (`OSR/IntegrationRec42.lean`). The catalogue has
  401 rules: 91 proved and 310 refuted over ℝ, 83 proved (56 certified), 317
  refuted and one unproved over ℂ.
- Strengthened variants of 1.1.1.3 #2 with `d f (n + p + 2) ≠ 0` and 1.2.1.1 #3
  with `2 c (2 p + 1) ≠ 0`, proved over ℝ and ℂ (`OSR/IntegrationRec41.lean`).
  The catalogue has 396 rules: 86 proved and 310 refuted over ℝ, 78 proved
  (51 certified), 317 refuted and one unproved over ℂ.
- Strengthened variants of 1.2.1.2 #4 with `b (p + 1) ≠ 0`, 1.2.1.3 #1 with
  `c (m + 2 p + 2) ≠ 0` and 1.2.1.4 #1 with `g (m + n + 3) ≠ 0`, proved over ℝ
  and ℂ (`OSR/IntegrationRec40.lean`). The catalogue has 394 rules: 84 proved
  and 310 refuted over ℝ, 76 proved (49 certified), 317 refuted and one
  unproved over ℂ.
- Strengthened variants of 1.1.3.3 #10 with `a ≠ 0` and 1.1.3.4 #14 with
  `a e (m + 1) ≠ 0`, proved over ℝ and ℂ (`OSR/IntegrationRec39.lean`). The
  catalogue has 391 rules: 81 proved and 310 refuted over ℝ, 73 proved (46
  certified), 317 refuted and one unproved over ℂ.
- Four more strengthened variants, proved over ℝ and ℂ
  (`OSR/IntegrationRec38.lean`): 1.1.1.2 #1 with `b (m + 2) ≠ 0`, 1.1.3.2 #3
  with `b n (p + 1) ≠ 0`, 1.1.3.1 #3 with `a ≠ 0` and 1.1.3.2 #6 with
  `a c (m + 1) ≠ 0`. The catalogue has 389 rules: 79 proved and 310 refuted
  over ℝ, 71 proved (44 certified), 317 refuted and one unproved over ℂ.
- Strengthened variants (Specification V1-R-005e): four corrected rules with a
  non-degeneracy condition appended to the converted RUBI conditions, proved
  over ℝ and ℂ (`OSR/IntegrationRec37.lean`): 1.1.1.1 #4 with
  `b (m + 1) ≠ 0`, 9.1 #9, 4.1.13 #11 and #12 with `2 c ≠ 0`. Their ids end in
  `_nondegenerate`; the refutations of the rules as stated are kept. The
  catalogue has 385 rules: 75 proved and 310 refuted over ℝ, 67 proved (40
  certified), 317 refuted and one unproved over ℂ.
- RUBI 4.16.1 1.2.3.3 #56 and #57 proved over ℝ and ℂ by linearity
  (`OSR/IntegrationRec36.lean`). The catalogue has 381 rules: 71 proved and
  310 refuted over ℝ, 63 proved (36 certified), 317 refuted and one unproved
  over ℂ.
- RUBI 4.16.1 1.1.3.5 #42 and 1.1.3.6 #30 proved over ℝ and ℂ
  (`OSR/IntegrationRec35.lean`, `pos_flip`). The catalogue has 379 rules: 69
  proved and 310 refuted over ℝ, 61 proved (34 certified), 317 refuted and
  one unproved over ℂ.
- RUBI 4.16.1 1.1.3.6 #29 proved over ℝ and ℂ (`OSR/IntegrationRec34.lean`),
  the `x^m` variant of 1.1.3.5 #41. The catalogue has 377 rules: 67 proved
  and 310 refuted over ℝ, 59 proved (32 certified), 317 refuted and one
  unproved over ℂ.
- RUBI 4.16.1 1.1.3.5 #41 proved over ℝ and ℂ (`OSR/IntegrationRec34.lean`):
  `(c + d x^(-n))^q = (d + c xⁿ)^q / x^(n q)`. The catalogue has 376 rules:
  66 proved and 310 refuted over ℝ, 58 proved (31 certified), 317 refuted
  and one unproved over ℂ.
- RUBI 4.16.1 1.1.3.4 #45 proved over ℝ and ℂ (`OSR/IntegrationRec33.lean`),
  a partial-fraction split of `(e x)^m/((a + b xⁿ)(c + d xⁿ))`. The catalogue
  has 375 rules: 65 proved and 310 refuted over ℝ, 57 proved (30 certified),
  317 refuted and one unproved over ℂ.
- RUBI 4.16.1 1.2.3.1 #1 proved over ℝ and ℂ (`OSR/IntegrationRec32.lean`):
  for `n < 0`, `(a + b xⁿ + c x²ⁿ)^p = x^(2 n p) (c + b x^(-n) + a x^(-2n))^p`.
  The catalogue has 374 rules: 64 proved and 310 refuted over ℝ, 56 proved
  (30 certified), 317 refuted and one unproved over ℂ.
- RUBI 4.16.1 1.2.4.1 #1 and 1.2.4.2 #1 proved over ℝ and ℂ
  (`OSR/IntegrationRec31.lean`): `a x^q + b x^n + c x^r = (a + b + c) x^n`
  when `q = n = r`. The catalogue has 373 rules: 63 proved and 310 refuted
  over ℝ, 55 proved (30 certified), 317 refuted and one unproved over ℂ.
- 27 RUBI rules reported as not migrated: a condition forces a half-integer
  exponent, or the integrand has an exponent with denominator 2, so the
  integrand is nowhere defined in the fragment (41 not migrated in all).
- Twelve more RUBI rules refuted in both domains from random-sampling
  proposals (`OSR/IntegrationRec30.lean`). The catalogue has 371 rules: 61
  proved and 310 refuted over ℝ, 53 proved, 317 refuted and one unproved over ℂ.
- A wider inventory pass over the registered-head RUBI rules with
  expressible conditions and `x`-independent metavariables found 213 new
  candidates; 39 are refuted in Lean (`OSR/IntegrationRec29.lean`), 38 in
  both domains and one over ℝ only (22 more, using `Sqrt`, wait for the
  converter's `arith1#root` convention). The catalogue has 359 rules: 61
  proved and 298 refuted over ℝ, 53 proved, 305 refuted and one unproved
  over ℂ.
- RUBI 4.16.1 3.2.3 #5 refuted over ℂ at the branch cut of `log`, with
  residual antiderivatives chosen up to a constant (`OSR/IntegrationRec28.lean`).
  No Integration statement is left unproved in either domain: 61 proved and
  259 refuted over ℝ, 53 proved and 267 refuted over ℂ.
- Six by-parts Integration rules refuted over ℂ at the branch cut of `log`
  (`OSR/IntegrationRec27.lean`, `not_continuous_clog_add`):
  `log_linear_power`, `power_log_times_power_log`,
  `quadratic_power_log_by_parts`, `sin_power_log_reduction`,
  `cos_power_log_reduction` and 3.3 #40. One complex statement (3.2.3 #5)
  remains unproved: 53 proved and 266 refuted over ℂ.
- Six Integration rules refuted over ℂ at the branch cut of the principal
  logarithm (`OSR.IntegrationRec26.not_continuous_clog`: an antiderivative
  is continuous, but `Ψ(x, log x)` jumps at `x = -1` when
  `Ψ(-1, π i) ≠ Ψ(-1, -π i)`): `integration.reciprocal`, `log_monomial`,
  `sin_log`, `cos_log`, `log_linear_over_x_split` and `log_over_linear`.
  Over ℂ: 53 proved, 260 refuted, 7 unproved.
- Eight one-domain refutations carried to the other domain
  (`OSR/IntegrationRec25.lean`): RUBI 4.16.1 3.1.5 #33 over ℝ; 3.4 #9,
  4.7.6 #2, 1.2.2.2 #19 and 3.5 #14, #17, #22, #23 over ℂ. Integration has
  no unproved real statement left: 61 proved and 259 refuted over ℝ, 53
  proved (28 certified), 254 refuted and 13 unproved over ℂ.
- RUBI 4.16.1 1.1.3.2 #69 (by parts for a product of two binomials) proved
  over ℝ and ℂ (`OSR/IntegrationRec24.lean`). The catalogue has 320 rules:
  61 proved and 258 refuted over ℝ, 53 proved (28 certified) and 247
  refuted over ℂ.
- RUBI 4.16.1 3.3 #15 (splitting a logarithm of a quotient) and 1.2.1.2 #101
  (a quadratic reduction when `m + 2 p + 3 = 0`) proved over ℝ and ℂ, and
  1.2.1.2 #103 refuted in both domains at `m = p = -1`
  (`OSR/IntegrationRec23.lean`). The catalogue has 319 rules: 60 proved and
  258 refuted over ℝ, 52 proved (28 certified) and 247 refuted over ℂ.
- RUBI 4.16.1 3.1.2 #8 (scaling under a logarithm) and 4.7.9 #80 (a closed
  form, its derivative checked with SymPy-computed `linear_combination`
  coefficients) proved over ℝ and ℂ (`OSR/IntegrationRec22.lean`). The
  catalogue has 316 rules: 58 proved and 257 refuted over ℝ, 50 proved
  (28 certified) and 246 refuted over ℂ.
- RUBI 4.16.1 4.7.7 #34 and #35 proved over ℝ and ℂ (linearity of the
  numerator), and 1.2.1.2 #54 and #59 refuted in both domains at `d = b = 0`
  (`OSR/IntegrationRec21.lean`). The catalogue has 314 rules: 56 proved and
  257 refuted over ℝ, 48 proved (26 certified) and 246 refuted over ℂ.
- RUBI 4.16.1 4.7.9 #9, #10 and 4.7.7 #26, #27 proved over ℝ and ℂ by
  trigonometric identities under the integral, and 4.7.7 #32 refuted in
  both domains at `x = π` (`OSR/IntegrationRec20.lean`). The catalogue has
  310 rules: 54 proved and 255 refuted over ℝ, 46 proved (24 certified)
  and 244 refuted over ℂ.
- RUBI 4.16.1 4.7.9 #78 and #82 refuted over ℝ and ℂ at `x = π`
  (`OSR/IntegrationRec19.lean`). The catalogue has 305 rules: 50 proved and
  254 refuted over ℝ, 42 proved (24 certified) and 243 refuted over ℂ.
- Seven RUBI 4.16.1 rules that rewrite the integrand into a residual
  integral proved over ℝ and ℂ (`OSR/IntegrationRec18.lean`): 1.1.1.2 #2,
  1.1.1.3 #50, 3.1.4 #1, 3.1.5 #2, 3.3 #21, 1.1.3.7 #11 and #18. The
  catalogue has 303 rules: 50 proved and 252 refuted over ℝ, 42 proved (24
  certified) and 241 refuted over ℂ.
- RUBI 4.16.1 1.1.3.2 #68 (integration by parts of `x^m (a + b xⁿ)ᵖ`)
  proved over ℝ and ℂ (`OSR/IntegrationRec17.lean`). The catalogue has 296
  rules: 43 proved and 252 refuted over ℝ, 35 proved (18 certified) and 241
  refuted over ℂ.
- RUBI 4.16.1 1.1.1.2 #4 proved over ℝ and ℂ (`OSR/IntegrationRec16.lean`);
  3.2.1 #7, 4.7.8 #47 and #48 refuted over ℝ and ℂ
  (`OSR/IntegrationRec15.lean`). The catalogue has 295 rules: 42 proved and
  252 refuted over ℝ, 34 proved (18 certified) and 241 refuted over ℂ.
- 108 RUBI 4.16.1 rules with `EqQ` conditions migrated and refuted
  (`OSR/IntegrationRec13.lean`, `OSR/IntegrationRec14.lean`): all over ℝ,
  102 also over ℂ, by Lean counterexamples proposed by the numerical search.
  The catalogue has 291 rules: 41 proved and 249 refuted over ℝ, 33 proved
  (17 certified) and 238 refuted over ℂ.
- `relation1#eq` conditions (`OSR.Cond.eq`: both operands defined and equal),
  with the registry entry, OpenMath export, exact decision (`Cond.decide?`,
  soundness `Cond.decide?_sound`) and substitution, so RUBI `EqQ` conditions
  can be stated (Specification V1-R-005).
- RUBI 4.16.1 1.2.2.1 #4 (quartic power reduction, `p ≥ 1`) proved over ℝ
  and ℂ (`OSR/IntegrationRec12.lean`). The catalogue has 183 rules: 41
  proved and 141 refuted over ℝ, 33 proved (17 certified) and 136 refuted
  over ℂ.
- RUBI 4.16.1 1.2.2.2 #19 refuted over ℝ (division by `c` at `c = 0`) and
  3.1.4 #11 over ℝ and ℂ (division by `f` at `f = 0`), in
  `OSR/IntegrationRec11.lean`. The catalogue has 182 rules: 40 proved and
  141 refuted over ℝ, 32 proved (17 certified) and 136 refuted over ℂ.
- RUBI 4.16.1 1.2.1.1 #7 and 1.2.1.2 #11 (quadratic power reductions for
  `p < -1`) proved over ℝ and ℂ (`OSR/IntegrationRec10.lean`). The catalogue
  has 180 rules: 40 proved and 139 refuted over ℝ, 32 proved (17 certified)
  and 135 refuted over ℂ.
- RUBI 4.16.1 4.1.12 #53 and #54 refuted over ℝ and ℂ
  (`OSR/IntegrationRec9.lean`): their results divide by `b n (p + 1)` while
  the conditions allow `b = 0`. The catalogue has 178 rules: 38 proved and
  139 refuted over ℝ, 30 proved (17 certified) and 135 refuted over ℂ.
- RUBI 4.16.1 4.1.12 #47 and #48 proved over ℝ and ℂ
  (`OSR/IntegrationRec8.lean`): `∫ x^m sinᵖ(a + b xⁿ)` and its cosine
  analogue, by parts twice. The catalogue has 176 rules: 38 proved and 137
  refuted over ℝ, 30 proved (17 certified) and 133 refuted over ℂ.
- RUBI 4.16.1 4.7.8 #3 and #4 (`sin`/`cos` powers of `d (a + b log(c xⁿ))`)
  proved over ℝ, and 3.1.4 #16 (the same rule as 3.1.5 #15) over ℝ and ℂ.
  The catalogue has 174 rules: 36 proved and 137 refuted over ℝ, 28 proved
  (17 certified) and 133 refuted over ℂ.
- Two logarithmic RUBI 4.16.1 rules proved over ℝ by integration by parts
  (`OSR/IntegrationRec7.lean`, `hasDerivAt_log_monomial`): 3.1.3 #8 and
  3.1.5 #24; unproved over ℂ (branch cut). The catalogue has 171 rules: 33
  proved and 137 refuted over ℝ, 27 proved (17 certified) and 133 refuted
  over ℂ.
- Four backlog RUBI 4.16.1 rules proved over ℝ and ℂ
  (`OSR/IntegrationRec7.lean`): 3.1.5 #15 (linear split), 4.1.12 #35 and
  #36 (integration by parts) and 4.7.9 #71 (double angle). The catalogue
  has 169 rules: 31 proved and 137 refuted over ℝ, 27 proved (17
  certified) and 133 refuted over ℂ. `catalog_wellFormed` raises
  `maxRecDepth` for the longer catalogue.
- Nine further RUBI 4.16.1 rules refuted over ℝ and ℂ
  (`OSR/IntegrationRec6.lean`): 1.2.2.1 #5, 2.3 #23, #26 and #35, 3.1.1 #3,
  3.1.4 #9 and #17, 3.1.5 #16 and 3.3 #12, by witnesses from a wider
  search grid. The catalogue has 165 rules: 27 proved and 137 refuted over
  ℝ, 23 proved (17 certified) and 133 refuted over ℂ.
- Five recursive RUBI 4.16.1 rules proved over ℝ and ℂ
  (`OSR/IntegrationRec4.lean`): 1.1.3.1 #5 and 4.1.11 #7, #8, #19 and #20
  rewrite a binomial with a negative integer exponent (`binom_core`).
  28 further rules refuted over both domains (`OSR/IntegrationRec5.lean`)
  by witnesses from a stricter numerical search. The catalogue has 156
  rules: 27 proved and 128 refuted over ℝ, 23 proved (17 certified)
  and 124 refuted over ℂ.
- Exact decision of closed conditions (`OSR/Decide.lean`: `Expr.ratEval?`,
  `Cond.decide?`, soundness `Cond.decide?_sound`).  The calculus rewriter
  applies a conditional rule when its substituted conditions are decided
  true (`CRule.conditionsDecided`, `antideriv_instance_under`); engine
  soundness covers it.  New Integration conformance seeds exercise the
  power rule at literal exponents.
- Five further RUBI 4.16.1 rules refuted over both ℝ and ℂ: 1.2.2.4 #57
  and #58, 2.1 #10, and 4.1.12 #45 and #46. Their conditions permit zero
  coefficients in result denominators. The catalogue has 123 rules, with
  22 proved and 100 refuted over ℝ, 18 proved (17 certified) and 96 refuted
  over ℂ. Regression checks keep all five refuted in both domains.
- Antiderivative rules `int(λx. F) ⟶ λx. G` (`calculus1#int`, now in the
  registry): `AntiderivHolds` requires the result to be defined on a
  neighbourhood wherever the integrand is, with `HasDerivAt`; instantiation
  (`antideriv_instance`) and engine soundness cover the new shape.
- First RUBI migration (`OSR/Integration.lean`, exported as
  `integration.osr.json` with its reports and conformance cases): of the nine
  `FreeQ`-only rules with registered heads, `∫ a = a x` is proved over ℝ and ℂ,
  `∫ log(c xⁿ)` over ℝ, four rules are refuted by Lean counterexamples, and
  three are reported as not migrated.  The other rule sets export unchanged.
- 45 more recursive RUBI rules refuted (`OSR/IntegrationRec3.lean`): their
  counterexamples were proposed by a numerical search under the fragment's
  real definedness semantics and are Lean theorems per domain.  Exponents
  constrained only by numeric RUBI predicates are declared independent of
  `x` with an `independence:` finding.  Integration: 118 rules, 22 proved
  over ℝ, 18 over ℂ (17 certified), 95 refuted over ℝ, 91 over ℂ.
- The reduction of `(d + e x)^m/(a + c x²)` for `m < -1` (RUBI 1.2.1.2 #83)
  is proved over ℝ and ℂ.
- A fourth batch of 25 recursive RUBI rules (`OSR/IntegrationRec2.lean`),
  transcribed by a tool and checked against the v0.1 rules by the
  Integration repository's `v1_faithfulness.py`: one proved over ℝ and ℂ,
  22 refuted by a zero coefficient or a residual division by zero, two
  refuted over ℝ (`log` at a negative point); seven `F^(…)` rules reported as
  not migrated.  `integration.log_linear_power` records why `p` is declared
  independent of `x`.
- Twelve more recursive RUBI rules: three partial fraction decompositions and
  `sin u cos u = sin(2u)/2` proved over ℝ and ℂ, eight rules refuted.
- Eleven more recursive RUBI rules: partial fractions of
  `1/((a + b xⁿ)(c + d xⁿ))` (n = 1 and general) and two linearity splits are
  proved over ℝ and ℂ; seven rules are refuted where a coefficient they divide
  by may vanish.
- Recursive antiderivative rules (`Shape.antiderivRec`, `AntiderivRecHolds`):
  residual integrals `int(λx. H)(x)` in the result, exported with the new
  `OMObj.omapp` (Specification V1-E-002b); the statement holds for every
  choice of antiderivatives of the residual integrands.  Eleven RUBI rules
  (`OSR/IntegrationRec.lean`): seven proved (six over ℝ and ℂ), four refuted.
  The schema copy accepts residual integrals.  The reference rewriter does not
  apply recursive rules.
- Conditional antiderivative rules (`CRule.conditions`,
  `AntiderivHoldsUnder`): RUBI `NeQ` becomes `relation1#neq`.  Seven more RUBI
  rules: the power rule `∫ xᵐ` (`m ≠ −1`) is proved over ℝ and ℂ, the
  `sin`/`cos` of `d (a + b log(c xⁿ))` over ℝ, and four rules are refuted
  (a zero coefficient in a denominator); four are not migrated.  The
  reference rewriter does not apply conditional rules.
- A `just doc` entry point using Documenter and DocumenterLandingPage,
  including `llms.txt` and `llms-full.txt` under `docs/build/`.
- Kernel-checked witnesses for the missing differentiability premises of
  the three structural Calculus rules, with type and axiom regression checks.
  All witnesses use `sqrt(x^2)` from the existing real expression fragment.
- OpenMath semantic registry relating `arith1`, `transc1`, `nums1`,
  `relation1` and `setname1` symbols to real and complex Mathlib
  interpretations, with assurance levels, definedness restrictions and CMP
  obligations proved in Lean.
- Structured expression fragment (`OSR.Expr`) with real and complex
  interpretations and an explicit definedness relation for partial operations.
- Rules with a per-domain soundness statement `Rule.Holds`, well-formedness
  checks and catalogue entries linking rules to their proofs.
- Migration of the 13 Trigonometry v0.1 rules, proved over ℝ and ℂ by reusing
  Mathlib theorems.
- Audited export to the OSR v1 interchange format (OpenMath 2.0 JSON
  expressions, per-domain verification records), registry export and
  verification reports; JSON Schema for the rule set.
- Architecture, trust model, M0 audit and migration proposal documents.
- `justfile` entry points and a CI workflow.
- Reference rewriter (`OSR/Rewrite.lean`): syntactic matching, substitution,
  outermost-leftmost strategy, with soundness proved (`normalize_sound`) and
  instantiated for every Trigonometry profile over ℝ and ℂ.
- Termination check of every profile at export, and generated conformance
  cases (`generated/conformance/trigonometry.cases.json`).
- Termination proofs (`OSR/Termination.lean`): monotone weights into ℕ, a
  `Terminates` predicate and `Weight.terminates`, instantiated by one weight
  per Trigonometry profile (`Trigonometry.normalize_terminates`).  The export
  audits each termination theorem (exact statement, standard axioms) and
  records it in `report.json` and `report.md`.
- OpenMath object model (`OSR/OMObject.lean`): the export is the JSON
  serialization of `Expr.toOM`, decoding by symbol identity recovers the
  expression (`decode_toOM`, `evalOM_toOM`), and the registry covers every
  emitted symbol at its arity (`registry_covers_toOM`).
- `transc1#exp`, `transc1#ln` and `relation1#gt` conditions in the fragment
  and the registry (ℝ and ℂ for exp/ln; ℝ only for gt), with CMP obligations.
- Algebra pilot (`OSR/Algebra.lean`): all 20 v0.1 rules proved (ℝ: 20,
  ℂ: 18; the two logarithm rules with a positivity condition are stated over
  ℝ only), two terminating profiles with termination proofs, engine
  soundness.  Exported as `algebra.osr.json` with its report and conformance
  cases.
- Integer exponents: `Expr.pow a e` takes an expression exponent and is
  interpreted only where the exponent is an integer (`Interp.toInt?`), with a
  nonzero base for a negative exponent; integer conditions `p ∈ ℤ`
  (`Cond.int`, `set1#in` with `setname1#Z`, CD `set1` pinned) carry v0.1
  `IntegerQ`.  They migrate `(x^p)^q`, `x^p x^q`, `x^(-1)`, `1^x` and
  `ln(a^b)`.

- Logic (`OSR/LogicOps.lean`, `OSR/LogicCore.lean`, `OSR/Logic.lean`): a
  `boolean` domain (carrier `setname2#Boolean`, CDs `logic1`, `quant1` and
  `setname2` pinned), quantified Boolean formulas with a sound reference
  rewriter, a faithful OpenMath encoding (quantifiers as `OMBIND`) and
  generic termination weights; rule statements are higher order, so
  substitution under binders needs no freshness condition (`evalM_subst`).
  all 39 Logic rules proved, three terminating profiles (`default`,
  `to_cnf`, `to_dnf`).  v0.1 `FreeQ` conditions become `independent`
  matching constraints, checked syntactically by the rewriter
  (`independentOk`) and assumed semantically by the rule statement
  (`eval_upd_notFree` links the two).  Exported as `logic.osr.json` with its
  report and conformance cases.
- `OMObj.ombind` and `OMBIND` in the rule-set JSON Schema.
- Further functions in the fragment: `transc1#sinh`, `cosh`, `tanh`, `coth`,
  `sech`, `csch`, `cot`, `sec`, `csc`, `arcsin`, `arccos`, `arcsinh`,
  `arccosh`, `arctanh` and `arith1#root` (square root), with their domains of
  definition (`Interp.fn`, `Interp.fnDefined`) and registry entries; the
  complex domain interprets `sinh`, `cosh`, `tanh` and `cot` only.
- Calculus (`OSR/Calculus.lean`): derivative rules stated with `HasDerivAt`
  and two-sided limits with `Tendsto` along `𝓝[≠] a`, over lambda terms
  (`fns1#lambda`, CDs `calculus1`, `fns1` and `limit1` pinned); 29 of the 32
  v0.1 rules migrated, 28 proved over ℝ, and the v0.1 power rule refuted
  (`derivPow_counterexample`: false at `n = 0`, `x = 0`; reported with the
  status `counterexample`); `FreeQ` becomes `CRule.independent`; all proved (the derivative of `artanh` is
  derived from its logarithmic form, Mathlib having no lemma for it) and 16
  over ℂ, with a sound root rewriter whose
  instances rename the bound variable (`apply?_sound`) and one-step
  termination (`rewrite_result`).  Exported as `calculus.osr.json` with its
  report and conformance cases.

### Changed
- `Expr.powNat` (natural literal exponent) is replaced by `Expr.pow` with an
  expression exponent; `arith1#power` is registered for integer exponents.
- Termination (`Weight.RulesDecrease`) only requires the unconditional rules
  of a profile to decrease, as the engine never applies the others.
- The exporter handles several rule sets (`RuleSet`, `ruleSets`); reports are
  now written per rule set as `<set>.report.json` and `<set>.report.md`
  (previously `report.json` and `report.md`), and include the rules not
  migrated.
- `RulesSound` only requires the unconditional rules of a profile to be
  sound, since the reference engine never applies conditional rules.
- Trigonometry profiles: the v0.1 `default` and `sum_to_product` profiles
  cycle; they are replaced by `default` (expansion), `product_to_sum`,
  `power_reduction` and `sum_to_product`.
