# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
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
  35 of the 39 Logic rules proved, three terminating profiles (`default`,
  `to_cnf`, `to_dnf`); the 4 rules with a `FreeQ` condition are reported as
  not migrated (no OpenMath symbol).  Exported as `logic.osr.json` with its
  report and conformance cases.
- `OMObj.ombind` and `OMBIND` in the rule-set JSON Schema.
- Further functions in the fragment: `transc1#sinh`, `cosh`, `tanh`, `coth`,
  `sech`, `csch`, `cot`, `sec`, `csc`, `arcsin`, `arccos`, `arcsinh`,
  `arccosh`, `arctanh` and `arith1#root` (square root), with their domains of
  definition (`Interp.fn`, `Interp.fnDefined`) and registry entries; the
  complex domain interprets `sinh`, `cosh`, `tanh` and `cot` only.
- Calculus (`OSR/Calculus.lean`): derivative rules stated with `HasDerivAt`
  and two-sided limits with `Tendsto` along `𝓝[≠] a`, over lambda terms
  (`fns1#lambda`, CDs `calculus1`, `fns1` and `limit1` pinned); 26 of the 32
  v0.1 rules migrated, 25 proved over ℝ (Mathlib has no derivative of
  `artanh`) and 14 over ℂ, with a sound root rewriter whose
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
