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
- Algebra pilot (`OSR/Algebra.lean`): 15 of the 20 v0.1 rules proved
  (ℝ: 15, ℂ: 14), two terminating profiles with termination proofs, engine
  soundness; the 5 v0.1 rules outside the fragment are listed in
  `notMigrated` and in the report.  Exported as `algebra.osr.json` with its
  report and 46 conformance cases.

### Changed
- The exporter handles several rule sets (`RuleSet`, `ruleSets`); reports are
  now written per rule set as `<set>.report.json` and `<set>.report.md`
  (previously `report.json` and `report.md`), and include the rules not
  migrated.
- `RulesSound` only requires the unconditional rules of a profile to be
  sound, since the reference engine never applies conditional rules.
- Trigonometry profiles: the v0.1 `default` and `sum_to_product` profiles
  cycle; they are replaced by `default` (expansion), `product_to_sum`,
  `power_reduction` and `sum_to_product`.
