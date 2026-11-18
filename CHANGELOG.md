# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Fixed
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
  RUBI rules considered): 293 proved and 310 refuted over ℝ; 236 proved (CERT
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
