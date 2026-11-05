# Architecture

> OpenMath provides the semantic identity, Lean provides the formal language,
> Mathlib provides the mathematical foundations, and OSR makes verified
> rewriting knowledge portable.

## Decisions

1. **Rules are authored in Lean.**  The portable JSON is a build artifact,
   generated and audited by `scripts/Export.lean`.  It is never edited by hand.
2. **OpenMath is the canonical symbol namespace.**  A rule refers to
   `arith1#plus` or `transc1#sin`, never to `Real.sin`.  The relationship between
   the two is an explicit, reviewable registry entry (`OSR/Semantics.lean`).
3. **One structured expression, two interpretations.**  An `OSR.Expr` value is
   interpreted in Lean by `OSR.eval` (to state the theorem) and serialized by
   `Expr.toOMJson` (to export the rule).  No theorem text is parsed, and no JSON
   is maintained beside a theorem.
4. **Partiality is explicit.**  Lean totalizes (`x / 0 = 0`, `tan` at a pole is
   `0`, `Complex.arctan I` has a value).  `OSR.Defined` encodes where each
   OpenMath operation is defined.  The certified statement is:

   ```
   Rule.Holds r d :=
     ∀ env, conditions hold → Defined lhs → Defined rhs ∧ eval lhs = eval rhs
   ```

   A rewrite may therefore enlarge the domain of definition (as `x/x ⟶ 1` would)
   but can never change a defined value or produce an undefined result.
5. **Mathematical truth, rewrite rule and strategy are separate.**  The theorem
   is about values.  Orientation, profiles and priority are rule metadata.
   Termination and confluence of a strategy are a separate obligation that is
   not proved here (see the cycle found in the v0.1 `default` profile, in
   `docs/audit-m0.md`).
6. **Certification is per domain and has two independent inputs:**
   - the proof status of `Rule.Holds r d`;
   - the weakest assurance of the symbol mappings the rule uses in `d`.

   A rule is certified only when it is proved with the standard axioms **and**
   every mapping is `reviewed` or `formally_related`.
7. **Expressions use the OpenMath 2.0 JSON encoding** (2019 revision, §3.3),
   restricted to `OMS`, `OMV`, `OMI` and `OMA` with a symbol head.  It is a
   published standard rather than an OSR-specific S-expression syntax.

## Repository roles

| Repository | Role |
|---|---|
| `Lean` | Registry, expression language, rules, proofs, exporter, audit (this repository) |
| `OpenMath` | Pinned snapshots of the content dictionaries used (`cd/*.ocd`) and, later, the exported registry for non-Lean consumers |
| `Specification` | The v1 interchange contract (schema, semantics of `applicability`, verification records) |
| `Conformance` | Engine conformance suite: matching, substitution and strategy tests, independent of any CAS |
| `Verification` | Published verification reports and an independent recheck workflow (rebuild at a source digest, `leanchecker`) |
| `Trigonometry`, `Algebra`, `Calculus`, `Logic` | Distribution of generated rule sets |
| `Integration` | RUBI-derived corpus and its progressive formalization |
| `OpenSymbolicRules.jl` | Julia execution engine (`OpenSymbolicRules.OSRv1`) |

## Layout of this repository

```
OSR/Registry.lean      symbol identity, domains, assurance levels, CD references
OSR/Expr.lean          expression fragment and its OpenMath JSON encoding
OSR/Interp.lean        real and complex interpretations, `eval`, `Defined`
OSR/Rule.lean          rules, conditions, well-formedness, `Rule.Holds`
OSR/Semantics.lean     registry contents and semantic obligations
OSR/Catalog.lean       catalogue entries and the `osr_intro` proof helper
OSR/Trigonometry.lean  the pilot rules and their proofs
OSR/Export.lean        pure JSON rendering
scripts/Export.lean    audit (types, axioms, registry) and generation
schemas/               JSON Schema of the generated rule set
OSRTest/               `#guard` tests and examples
```

## Semantic registry

Each `SymbolEntry` holds:

- the OpenMath symbol;
- its arity in the OSR fragment, and any restriction of the fragment (for
  example: `power` takes natural literal exponents only; `plus` is binary);
- one `Interpretation` per domain.

An `Interpretation` records:

- the Lean constant, referenced with a double-backtick name, so a nonexistent
  declaration does not compile;
- an assurance level;
- the definedness restriction;
- a justification;
- obligations: CD properties (CMP text) paired with the Lean theorem that
  establishes them;
- unresolved differences.

`scripts/Export.lean` checks the registry before any export:

- every symbol has a single entry;
- every CD is pinned by SHA-256;
- every Lean constant exists;
- every obligation is a theorem that uses the standard axioms only;
- a `formally_related` interpretation has at least one obligation.

OpenMath symbols are never derived from Lean names.  A symbol missing from the
registry makes the export fail.

CMPs are evidence of compatibility, not definitions: a few properties never
characterize a function.  Semantic obligations are therefore an assurance level,
not a proof that the Lean function *is* the OpenMath function.

## Breaking changes from OSR v0.1

| v0.1 | v1 |
|---|---|
| JSON is the authoring format | Lean is the authoring format; JSON is generated |
| S-expressions `["Sin", "x_"]` with an `openmath:` prefix map | OpenMath 2.0 JSON (`OMA`/`OMS`/`OMV`/`OMI`) with real CD symbols |
| Wildcard syntax encoded in symbol names (`x_`, `a.`, `n_integer`) | Variables declared in `variables`, encoded as `OMV`; no name-based typing |
| `semantics` map per file, `openmath:osr#…` placeholders tolerated | Every symbol must exist in the registry and in a pinned CD; no invented CDs |
| n-ary `Multiply`/`Add` | Binary `times`/`plus` (n-ary is left-nested) |
| `identity:id` with an integer `id` | Dotted canonical id; the v0.1 identity is kept as `legacy_id` |
| `meta.json` with `load_order` per file | `profiles` listing rule ids in priority order |
| No proof information | Per-domain `verification` records (status, theorem, axioms, mapping assurance, toolchain, Mathlib revision, source digest) |
| Unconditional rules over partial functions | `applicability: defined_pattern` with a machine-checked definedness semantics |
