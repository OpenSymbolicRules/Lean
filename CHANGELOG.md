# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Changed
- Report the three unmigrated structural derivative rules as lacking the
  differentiability assumptions needed by their operands, in addition to
  using the non-OpenMath `osr#Apply` construct. The v1 format cannot express
  these premises, so no assumptions were added silently.

### Added
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
