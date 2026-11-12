# OpenSymbolicRules — Lean

Canonical source of the Open Symbolic Rules (OSR): symbolic rewriting rules
authored in Lean 4, proved against Mathlib, grounded in OpenMath content
dictionaries, and exported to a portable JSON interchange format that any
computer algebra system can consume without Lean.

```
OpenMath CDs ──► semantic registry ──► Lean rules + proofs ──► kernel
                                                                 │
                     OpenSymbolicRules.jl, other CAS ◄── OSR v1 JSON (audited export)
```

Status: **pilot** (`1.0.0-alpha.1` format).  Five rule sets are migrated:

| Rule set | Rules | ℝ proved / certified | ℂ proved / certified | Not migrated |
|---|---|---|---|---|
| Trigonometry | 13 | 13 / 13 | 13 / 12 | 0 |
| Algebra | 20 | 20 / 20 | 18 / 18 | 0 |
| Logic (domain 𝔹) | 39 | 39 / 39 in 𝔹 | — | 0 |
| Calculus | 29 | 28 / 28 (+1 counterexample) | 16 / 16 | 3 |
| Integration (RUBI, first 20) | 13 | 5 / 5 (+8 counterexamples) | 2 / 2 (+7 counterexamples) | 7 |

`tan(arctan z) = z` over ℂ is proved but not certified, because the mapping of
`transc1#arctan` to `Complex.arctan` is provisional.  `ln(ab) = ln a + ln b`
and `ln(a^b) = b ln a` are stated over ℝ only (their positivity conditions
have no complex meaning).  Powers are interpreted for integer exponents only,
so `1^x = 1` and `ln(a^b)` are certified where the exponent is an integer.
Logic rules are stated in the Boolean domain (`logic1` on Lean's `Bool`,
`quant1` quantifiers over the truth values, encoded as `OMBIND`); v0.1
`FreeQ` becomes a matching constraint (`independent`), checked syntactically.  Calculus
rules state derivatives (`HasDerivAt`) and two-sided limits (`Tendsto`) of
lambda terms (`OMBIND fns1#lambda`).  The v0.1 power rule is refuted in Lean
(false at `n = 0`, `x = 0`); 3 structural v0.1 rules lack differentiability
premises and use the invented symbol `osr#Apply`. The missing premises have
[Lean witnesses](docs/structural-derivatives.md).
Integration rules state antiderivatives (`calculus1#int`, `HasDerivAt` on a
neighbourhood where the integrand is defined, under `NeQ` conditions); the
first twenty RUBI rules of a syntactic inventory give five proofs and eight
counterexamples, see
[Integration](docs/integration.md).
Every profile is proved to terminate.  See
[`docs/audit-m0.md`](docs/audit-m0.md) and the generated reports.

## Example

The Pythagorean identity is data:

```lean
def pythagorean : Rule where
  id := "trigonometry.pythagorean"
  vars := ["x"]
  lhs := add (sq (sin x)) (sq (cos x))
  rhs := .int 1
  ...
```

Its proof reuses Mathlib, stated over the rule's own interpretation:

```lean
theorem pythagorean_real : pythagorean.Holds .real := by
  osr_intro pythagorean Interp.real
  exact Real.sin_sq_add_cos_sq _
```

The export carries the OpenMath expression (`arith1#plus`, `arith1#power`,
`transc1#sin`, `transc1#cos`) and the verification record: theorem, statement,
axioms, toolchain, Mathlib revision and source digest.

Rewriting is verified as well: the reference engine `OSR.normalize`
(outermost-first, syntactic matching) is proved to preserve definedness and
value (`OSR.normalize_sound`), for every Trigonometry profile over ℝ and ℂ.
Its runs are exported as conformance cases that other engines must reproduce.

## Usage

Requires [elan](https://github.com/leanprover/elan) and
[just](https://github.com/casey/just); `check-jsonschema` for `just validate`.

```bash
just setup        # fetch Mathlib (pinned) and its build cache
just build        # compile registry, rules and proofs
just test         # #guard tests and examples
just doc          # HTML documentation and LLM text exports in docs/build/
just check        # replay modules with leanchecker
just export       # audit rule and termination proofs, write generated/
                  #   <set>.osr.json, <set>.report.{json,md}, registry.json,
                  #   conformance/<set>.cases.json for set in trigonometry,
                  #   algebra, logic, calculus, integration
just determinism  # export twice, require identical bytes
just validate     # validate against schemas/ruleset.schema.json
```

## Documentation

- [Architecture](docs/architecture.md): decisions, registry, breaking changes
  from v0.1
- [Trust model](docs/trust-model.md): what certification means and how to
  re-check it
- [M0 audit](docs/audit-m0.md): inspected revisions, Specification v0.1
  findings, Trigonometry inventory
- [Migration proposal](docs/migration-proposal.md): ecosystem plan, future
  domains, research questions

## License

[MIT](LICENSE.md).  OpenMath content dictionaries are referenced by
identifier; snapshots live in `OpenSymbolicRules/OpenMath`.
