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
   Rewrite soundness is proved once for the engine (`OSR.normalize_sound`).
   Termination of each profile is proved with a weight (see "Termination"
   below).  The v0.1 profiles cycle (`docs/audit-m0.md`), so v1 profiles group
   rules by orientation.
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
OSR/Rewrite.lean       reference rewriter (matching, substitution, outermost
                       strategy) and its soundness proof
OSR/Termination.lean   monotone weights and the termination theorem
OSR/Semantics.lean     registry contents and semantic obligations
OSR/OMObject.lean      OpenMath object model; faithfulness of the export
OSR/Catalog.lean       catalogue entries and the `osr_intro` proof helper
OSR/Trigonometry.lean  the pilot rules, their proofs, profiles and engine
                       soundness and termination per profile
OSR/Algebra.lean       Algebra rules (all 20), same structure
OSR/LogicOps.lean      Boolean interpretations of the logic1 connectives, CMPs
OSR/LogicCore.lean     quantified Boolean formulas, rewriter, soundness, termination
OSR/Logic.lean         Logic rules (all 39), profiles and their weights
OSR/Decide.lean        exact decision of closed conditions (rational arithmetic), soundness
OSR/Calculus.lean      derivative, limit and antiderivative statements, the
                       Calculus rules (29), their proofs and rewriter
OSR/IntegrationRec.lean RUBI rules with residual integrals (34), proofs, counterexamples
OSR/IntegrationRec2.lean fourth batch (26), transcribed by a tool, checked against v0.1
OSR/IntegrationRec3.lean refutations proposed by a numerical search (50), per domain
OSR/IntegrationRec4.lean binomials with negative integer exponents (5), proofs
OSR/IntegrationRec5.lean further searched refutations (28), per domain
OSR/IntegrationRec6.lean refutations from a wider search grid (9), per domain
OSR/IntegrationRec7.lean backlog proofs (6): linear split, by parts, double angle;
                       two logarithmic rules over ℝ only
OSR/Integration.lean   RUBI antiderivative rules (13) and the Integration catalogue (171)
OSR/Export.lean        pure JSON rendering
scripts/Export.lean    audit (types, axioms, registry, termination proofs),
                       generation of rule set, reports and conformance cases
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

## Reference rewriter

`OSR/Rewrite.lean` defines a syntactic engine and proves it sound:

| Definition | Theorem |
|---|---|
| `matchExpr p e` (non-linear, syntactic) | `matchExpr_subst`: the substitution instantiates `p` to `e` |
| `Expr.subst σ` | `eval_subst`, `defined_subst`: substitution commutes with `eval` and `Defined` |
| one root rewrite | `Rule.rewrite_sound`: definedness and value are preserved |
| `rewriteStep` (outermost-leftmost, rules in order) | `rewriteStep_sound`: lifted through every context |
| `normalize rules fuel e` | `normalize_sound`: for any budget |

`Trigonometry.normalize_sound_real` and `normalize_sound_complex` instantiate
the result for every profile: running the engine with Trigonometry rules on a
defined expression yields a defined expression with the same value.  The
engine only applies unconditional rules, and it requires each rule to be
*closed* (`Rule.rhsClosed`: the replacement only uses pattern variables),
which `#guard` tests check for the catalogue.

## Exporter

`OSR/OMObject.lean` models the exported OpenMath objects (`OMObj`: `OMV`,
`OMI`, `OMS`, `OMA` with a symbol head) and proves that `Expr.toOMJson` is
their JSON serialization, that decoding by symbol identity and arity recovers
the expression (`decode_toOM`, hence `evalOM_toOM`), and that the registry
covers every emitted symbol at its arity (`registry_covers_toOM`).  See
`docs/trust-model.md` for what remains trusted.

## Rule sets

The exporter knows rule sets through `RuleSet` records (`scripts/Export.lean`,
`ruleSets`): name, catalogue, profiles, termination theorems, extra seeds and
the v0.1 rules not migrated.  Per rule set it writes `<set>.osr.json`,
`<set>.report.json`, `<set>.report.md` and `conformance/<set>.cases.json`;
`registry.json` is shared.

`OSR/Algebra.lean` adds `ln`, `exp`, positivity conditions (`relation1#gt`)
and integer conditions (`set1#in` with `setname1#Z`).  `Expr.pow a e` takes an
expression exponent; `Interp.toInt?` (with `toInt?_eq`) recovers the integer
an exponent equals, and the power is defined only when there is one (and the
base is nonzero for a negative exponent).  An integer-valued rule variable is
an ordinary variable with the condition `p ∈ ℤ`.  The conditions only have a real meaning: `Interp` carries an
order, and the registry gives `relation1#gt` no complex mapping, so a rule
with such a condition is stated over ℝ only.  Conditional rules are never
applied by the reference engine, so engine soundness (`RulesSound`) only
needs the unconditional ones.

## Logic

Propositional rules live in their own sort: `OSR.Logic.BExpr` (variables,
`true`, `false`, `not` and the binary `logic1` connectives), evaluated in
`Bool` in the `boolean` domain (carrier `setname2#Boolean`).  Every connective
is total, so `BRule.Holds` is plain equality of truth values and each proof
evaluates both sides on every assignment of the variables (`decide`).
`OSR/LogicCore.lean` repeats the rewriter of `OSR/Rewrite.lean` for this sort
(matching, outermost-leftmost strategy, `normalize_sound`), with a generic
termination argument (`BasicWeight`): derived connectives weigh one more than
their elimination, so only negation, conjunction and disjunction need weights,
plus the De Morgan inequalities.  The exporter writes `logic.osr.json`, its
report and conformance cases like the other rule sets.

Quantifiers (`quant1#forall`, `quant1#exists`, exported as `OMBIND`) range over
the truth values.  Binders make first-order substitution unsound (capture),
so a Boolean rule statement is higher order: `BRule.Holds` interprets each
pattern metavariable as an arbitrary function of the whole assignment
(`evalM`) and holds for every renaming of the rule's bound variables.
Matching binds a pattern's bound variable to the input's bound variable, and
`evalM_subst` shows that instantiating a rule means interpreting its
metavariables by their images under the current assignment, so no freshness
condition is needed.  v0.1 `FreeQ` ("p does not mention x") is a matching
constraint, not a mathematical condition: a rule lists it in `independent`,
the rewriter checks that the bound name is not free in the matched subterm
(`independentOk`), and the rule statement assumes the metavariable's meaning
does not depend on the bound variable; `eval_upd_notFree` connects the two.
Quantifiers weigh `2b + 6`, so that both pulling a conjunction into a
universal and pulling one out of an existential decrease the weight.

## Calculus

A calculus rule is `diff(λx. F) ⟶ λx. G` or `limit(a, both_sides, λx. F) ⟶ L`,
where `F`, `G` and `L` are field expressions whose only variable is `x`.  The
statements use Mathlib's analysis: `DerivHolds` says that wherever `F` is
defined on a neighbourhood of `t`, `v ↦ F[x := v]` has derivative `G[x := t]`
at `t` (`HasDerivAt`), and `LimitHolds` says that `F[x := v]` tends to `L`
along `𝓝[≠] a`.  The rewriter applies a rule at the root of a `diff` or
`limit` term, renaming its bound variable to the input's; `deriv_instance`
and `limit_instance` prove the renamed instance from the rule's statement
(`eval_rename`), and `apply?_sound` packages them.  A result is a lambda or a
value, so normalization takes at most one step (`rewrite_result`).
Metavariables other than the bound variable must be `independent` of it
(v0.1 `FreeQ`): the rewriter checks that their matches do not mention the
input's bound variable (`indepOk`), which `eval_rename` turns into the
semantic independence the statements need.  A rule can also be refuted: the
v0.1 power rule `diff(λx. x^n) = λx. n x^(n-1)` is false at `n = 0`, `x = 0`
(`derivPow_counterexample`), and the exporter audits the type `¬ CRule.Holds`.

The three structural v0.1 rules remain outside `CRule`: besides their
non-OpenMath `osr#Apply`, they omit differentiability premises for their
operands. A composite can have a derivative while its operands do not.
The `structuralSum_missingPremise`, `structuralDifference_missingPremise`
and `structuralProduct_missingPremise` theorems exhibit this in the existing
real expression fragment; see [Structural derivatives](structural-derivatives.md).
They justify the migration diagnostics, rather than certify a structural
rewrite that the format cannot express.

A third shape, `int(λx. F) ⟶ λx. G` (`calculus1#int`), states antiderivatives:
`AntiderivHolds` says that wherever `F` is defined on a neighbourhood of `t`,
`G` is defined on a neighbourhood of `t` and `v ↦ G[x := v]` has derivative
`F[x := t]` at `t`; `AntiderivHoldsUnder` adds conditions on the
metavariables; the rewriter applies a conditional rule only when its
substituted conditions are closed and decided true by exact rational
arithmetic (`OSR/Decide.lean`, `CRule.conditionsDecided`; `apply?_sound`
then requires characteristic zero and the rational order).  A fourth
shape, `antiderivRec`, has residual integrals in its result
(`AntiderivRecHolds`, exported with `OMObj.omapp` as `int(λx. H)(x)`); the
rewriter does not apply it either.
`antideriv_instance` is its instantiation theorem.  The
Calculus set has no rule of this shape; the RUBI rules are in
`OSR/Integration.lean`, see [Integration](integration.md).

## Termination

`OSR/Termination.lean` proves termination with monotone interpretations.  A
`Weight` maps every operator to a strictly monotone function on ℕ.  A rule
*decreases* when its right-hand side weighs less than its left-hand side for
every weight of its variables.  Since weighing commutes with substitution and
contexts are monotone, every `rewriteStep` with decreasing rules strictly
lowers the weight (`rewriteStep_lt`), and `normalize` reaches a normal form
when its budget is at least the weight of the input
(`Weight.normalize_normal`, `Terminates`).

Each Trigonometry profile has its own weight, because the profiles orient
rules in opposite directions:

| Profile | Sine, cosine | Products | Sums, differences | Powers |
|---|---|---|---|---|
| `default` | `8^(a+1)` | `a+b+1` | `a+b+1` | `a+k+1` |
| `product_to_sum` | `a+3` | `(a+1)(b+1)` | `a+b+1` | `a+k+1` |
| `power_reduction` | `a+1` | `a+b+1` | `a+b+1` | `(a+1)^(k+1)` |
| `sum_to_product` | `3a+5` | `a+b+1` | `(a+1)(b+1)` | `a+k+1` |

Literals and `π` weigh 1; other operators add 1 to their argument.  The
theorems `Trigonometry.default_terminates`, … are audited by the exporter.

The exporter runs every profile on every seed (rule patterns and nested
inputs) and fails if a run does not reach a normal form within 64 steps.  The
same runs are written as language-neutral conformance cases
(`generated/conformance/<set>.cases.json`): input, expected result and
rule trace.  OpenSymbolicRules.jl must reproduce each of them exactly.
