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
