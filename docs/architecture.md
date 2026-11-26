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
OSR/Algebra.lean       Algebra rules (all 20 v0.1, four authored), same structure
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
OSR/IntegrationRec7.lean backlog proofs (9): linear split, by parts, double angle;
                       four logarithmic rules over ℝ only
OSR/IntegrationRec8.lean x^m sin^p / cos^p (a + b x^n) by parts twice (2)
OSR/IntegrationRec9.lean refutations at b = 0 of the reverse reductions (2), per domain
OSR/IntegrationRec10.lean quadratic power reductions (2)
OSR/IntegrationRec11.lean refutations at c = 0 and f = 0 (2), per domain
OSR/IntegrationRec12.lean quartic power reduction (1)
OSR/IntegrationRec13.lean, OSR/IntegrationRec14.lean rules with EqQ conditions, refuted (108)
OSR/IntegrationRec15.lean more EqQ refutations (3); OSR/IntegrationRec16.lean an EqQ proof (1)
OSR/IntegrationRec17.lean by parts for x^m (a + b x^n)^p (1)
OSR/IntegrationRec18.lean rewritings into a residual integral (7)
OSR/IntegrationRec19.lean refutations at x = π (2), per domain
OSR/IntegrationRec20.lean EqQ trigonometric identities (4 proofs, 1 refutation)
OSR/IntegrationRec21.lean EqQ linearity proofs (2) and refutations at d = 0 (2)
OSR/IntegrationRec22.lean EqQ proofs: a log scaling rule and a closed form (2)
OSR/IntegrationRec23.lean EqQ: a log split, a quadratic reduction (2 proofs), 1 refutation
OSR/IntegrationRec24.lean EqQ: a by-parts rule for two binomials (1 proof)
OSR/IntegrationRec25.lean refutations carried to the other domain (8)
OSR/IntegrationRec26.lean discontinuity of log at the cut (`not_continuous_clog`), 2 refutations
OSR/IntegrationRec27.lean branch-cut refutations of by-parts rules (6)
OSR/IntegrationRec28.lean branch-cut refutation of 3.2.3 #5 (residual antiderivatives with a constant)
OSR/IntegrationRec29.lean refutations from a wider inventory pass (39), per domain
OSR/IntegrationRec30.lean refutations proposed by random sampling (12), per domain
OSR/IntegrationRec31.lean improper trinomials with equal powers (2 proofs)
OSR/IntegrationRec32.lean a trinomial with a negative exponent (1 proof)
OSR/IntegrationRec33.lean partial fractions of a pair of binomials (1 proof)
OSR/IntegrationRec34.lean flipping a binomial in x^(-n) (2 proofs)
OSR/IntegrationRec35.lean flipping binomials in x^n (2 proofs)
OSR/IntegrationRec36.lean linearity in a polynomial factor (2 proofs)
OSR/IntegrationRec37.lean strengthened variants with a non-degeneracy condition (4 proofs)
OSR/IntegrationRec38.lean strengthened binomial variants, second batch (4 proofs)
OSR/IntegrationRec39.lean strengthened binomial-pair variants, third batch (2 proofs)
OSR/IntegrationRec40.lean strengthened quadratic-trinomial variants, fourth batch (3 proofs)
OSR/IntegrationRec41.lean strengthened variants, fifth batch (2 proofs)
OSR/IntegrationRec42.lean strengthened variants, sixth batch (5 proofs)
OSR/IntegrationRec43.lean strengthened variants, seventh batch (2 proofs)
OSR/IntegrationRec44.lean strengthened variants, eighth batch (2 proofs)
OSR/IntegrationRec45.lean strengthened variants, ninth batch (2 proofs)
OSR/IntegrationRec46.lean strengthened variant of 1.2.1.3 #24 (1 proof)
OSR/IntegrationRec47.lean strengthened variants with residual integrals (3 proofs)
OSR/IntegrationRec48.lean strengthened variants with residual integrals, second batch (3 proofs)
OSR/IntegrationFindings.lean texts of the standard migration findings
OSR/IntegrationNum1.lean strengthened variants checked numerically, unproved (0, all proved)
OSR/IntegrationRec49.lean proofs of variants first checked numerically (3 proofs)
OSR/IntegrationRec50.lean proof of a variant first checked numerically (1 proof)
OSR/IntegrationRec51.lean proofs of variants first checked numerically (4 proofs)
OSR/IntegrationRec52.lean proofs of variants first checked numerically (3 proofs)
OSR/IntegrationRec53.lean proofs of variants first checked numerically (5 proofs)
OSR/IntegrationRec54.lean proofs of variants first checked numerically (6 proofs)
OSR/IntegrationRec55.lean proofs of variants first checked numerically (4 proofs)
OSR/IntegrationRec56.lean proofs of variants first checked numerically (3 proofs)
OSR/IntegrationRec57.lean proofs of variants first checked numerically (2 proofs)
OSR/IntegrationRec58.lean proofs of variants first checked numerically (2 proofs)
OSR/IntegrationRec59.lean proofs of variants first checked numerically (3 proofs)
OSR/IntegrationRec60.lean proofs of variants first checked numerically (3 proofs)
OSR/IntegrationRec61.lean proofs of variants first checked numerically (2 proofs)
OSR/IntegrationRec62.lean proofs of variants first checked numerically (1 proof)
OSR/IntegrationRec63.lean proofs of variants first checked numerically (8 proofs)
OSR/IntegrationRec64.lean proofs of variants first checked numerically (10 proofs)
OSR/IntegrationRec65.lean proofs of variants first checked numerically (4 proofs)
OSR/IntegrationRec66.lean proofs of variants first checked numerically (6 proofs)
OSR/IntegrationRec67.lean proofs of variants first checked numerically (3 proofs)
OSR/IntegrationRec68.lean proofs of variants first checked numerically (2 proofs)
OSR/IntegrationRec69.lean proofs over ℝ of variants first checked numerically (3 proofs)
OSR/IntegrationRec70.lean proofs over ℝ of variants first checked numerically (2 proofs)
OSR/IntegrationRec71.lean proofs over ℝ of variants first checked numerically (2 proofs)
OSR/IntegrationRec72.lean proofs over ℝ of variants first checked numerically (1 proof)
OSR/IntegrationRec73.lean proofs over ℝ of variants first checked numerically (1 proof)
OSR/IntegrationRec74.lean proofs over ℝ of variants first checked numerically (3 proofs)
OSR/IntegrationRec75.lean proofs over ℝ of variants first checked numerically (1 proof)
OSR/IntegrationRec76.lean proofs over ℝ of variants first checked numerically (2 proofs)
OSR/IntegrationRec77.lean proofs over ℝ of variants first checked numerically (1 proof)
OSR/IntegrationRec78.lean proofs over ℝ of variants first checked numerically (1 proof)
OSR/IntegrationRec79.lean proofs over ℝ of variants first checked numerically (2 proofs)
OSR/IntegrationRec80.lean proofs of variants first checked numerically (1 proof)
OSR/IntegrationRec81.lean proofs of variants first checked numerically (2 proofs)
OSR/IntegrationRec82.lean proofs of variants first checked numerically (2 proofs)
OSR/IntegrationRec83.lean proofs of variants first checked numerically (2 proofs over ℝ)
OSR/IntegrationRec84.lean proofs of variants first checked numerically (1 proof over ℝ)
OSR/IntegrationRec85.lean proofs of variants first checked numerically (1 proof over ℝ)
OSR/IntegrationRec86.lean proofs of variants first checked numerically (1 proof over ℝ)
OSR/IntegrationRec87.lean proofs of variants first checked numerically (1 proof)
OSR/IntegrationRec88.lean proofs of variants first checked numerically (1 proof)
OSR/IntegrationRec89.lean proofs of variants first checked numerically (1 proof)
OSR/IntegrationRec90.lean proofs of variants first checked numerically (1 proof)
OSR/IntegrationRec91.lean proofs of variants first checked numerically (1 proof)
OSR/IntegrationRec92.lean variants of refuted named rules, with their proofs (5)
OSR/IntegrationRec93.lean variants of refuted named rules, with their proofs (4)
OSR/IntegrationRec94.lean variants of refuted named rules, with their proofs (4)
OSR/IntegrationRec95.lean variants of refuted named rules, with their proofs over ℝ (6)
OSR/IntegrationRec96.lean variant corrected after the pole probe, with its proof (1)
OSR/IntegrationRec97.lean variants corrected after the pole probe, with their proofs over ℝ (3)
OSR/IntegrationRec98.lean variants corrected after the pole probe, with their proofs over ℝ (4)
OSR/IntegrationRec99.lean variants sampled with their equality conditions solved, with their proofs (2)
OSR/IntegrationRec100.lean variants sampled with their equality conditions solved, with their proofs (4)
OSR/IntegrationRec101.lean variants sampled with their equality conditions solved, with their proofs (3)
OSR/IntegrationRec102.lean variants sampled with their equality conditions solved, with their proofs (1)
OSR/IntegrationRec103.lean variants sampled with their equality conditions solved, with their proofs (3)
OSR/IntegrationRec104.lean variants sampled with their equality conditions solved, with their proofs (2)
OSR/IntegrationRec105.lean variants sampled with their equality conditions solved, with their proofs (2)
OSR/IntegrationRec106.lean variants sampled with their equality conditions solved, with their proofs over ℝ (3)
OSR/IntegrationRec107.lean variant sampled with its equality condition solved, with its proof over ℝ (1)
OSR/IntegrationRec108.lean variant sampled with its equality condition solved, with its proof (1)
OSR/IntegrationRec109.lean variant sampled with its equality condition solved, with its proof (1)
OSR/IntegrationRec110.lean variant excluding a zero of its numerical check, with its proof (1)
OSR/IntegrationRec111.lean variants excluding a zero of their numerical check, with their proofs over ℝ (3)
OSR/IntegrationRec112.lean variants excluding a zero of their numerical check, with their proofs over ℝ (4)
OSR/IntegrationRec113.lean variants with a tighter exponent bound, with their proofs (4)
OSR/IntegrationRec114.lean variant excluding zeros of its numerical check, with its proof over ℝ (1)
OSR/IntegrationRec115.lean variant with positive exponents, with its proof (1)
OSR/IntegrationRec116.lean variants of the cubic factorisation rules, with their proofs (2)
OSR/IntegrationRec117.lean exponential variants with a locally constant exponent, with their proofs (5)
OSR/IntegrationRec118.lean RUBI 1.2.3.3/1.2.3.4 normalisations of negative powers, with their proofs (6)
OSR/IntegrationRec119.lean RUBI 1.2.1.2 reductions with m + 2p + 2 = 0, with their proofs (3)
OSR/IntegrationRec120.lean … IntegrationRec127.lean: RUBI rules refuted by numerical witnesses (247)
OSR/IntegrationRec128.lean RUBI rules split by linearity into residual integrals, with their proofs (12)
OSR/IntegrationRec129.lean RUBI rules split with the real reciprocal functions, with their proofs over ℝ (2)
OSR/IntegrationRec130.lean further RUBI rules refuted by numerical witnesses over ℝ (19)
OSR/IntegrationRec131.lean integration by parts of arctanh/arctan of a monomial, the derivative of Real.artanh (4)
OSR/IntegrationRec132.lean, IntegrationRec133.lean: integration by parts of log·arctanh/arctan products (6)
OSR/IntegrationRec134.lean, IntegrationRec135.lean: integration by parts of arctan(tanh), arctan(coth) and A(c x/√(a + b x²)) (5)
OSR/IntegrationRec136.lean, IntegrationRec137.lean: integration by parts of (a + b A(c x))^p over square roots (6)
OSR/IntegrationRec138.lean arctanh split into logarithms (2)
OSR/IntegrationRec139.lean linear splits with integer exponents (8)
OSR/IntegrationRec140.lean, IntegrationRec141.lean: splits with a shifted exponent (6)
OSR/IntegrationRec142.lean … IntegrationRec152.lean: algebraic, trigonometric and by-parts identities (48)
OSR/IntegrationRec153.lean … IntegrationRec156.lean: addition formulas, constant powers F^(c (a + b x)) and log arguments (19, 2 refuted)
OSR/IntegrationRec157.lean, IntegrationRec158.lean: refutations of 4.7.6 #4, #5, 6.7.6 #4; arctanh by parts, cosh² forms (5)
OSR/IntegrationRec159.lean, IntegrationRec160.lean: three refutations from a numerical pass; a linear split (1)
OSR/IntegrationRec161.lean: integrations by parts (5), one refutation
OSR/IntegrationRec162.lean: refutations at a single point (10)
OSR/IntegrationRec163.lean: two identities, three degenerate refutations
OSR/IntegrationRec164.lean: degenerate-coefficient refutations (9)
OSR/IntegrationRec165.lean: logarithm and degenerate refutations (3)
OSR/IntegrationRec166.lean: refutations from a wider definedness search (40)
OSR/IntegrationRec167.lean: one refutation (7.2.5 #17)
OSR/IntegrationRec168.lean: refutations of rules with E^u = exp u (10)
OSR/IntegrationRec169.lean: sinh and cosh split into exponentials (14)
OSR/IntegrationRec170.lean: refutations, mostly of rules written with Simp (46)
OSR/IntegrationRec171.lean: refutations, mostly of rules written with Simp (45)
OSR/IntegrationRec172.lean: linear splits into residual integrals (5; duplicates of named rules, not catalogued)
OSR/IntegrationRec173.lean: refutations of rules with inert trig functions (51)
OSR/IntegrationRec174.lean: refutations of rules with inert trig functions (66)
OSR/IntegrationRec175.lean: refutations of rules with inert trig functions (68)
OSR/IntegrationRec176.lean: refutations, trig signs decided at a point (20)
OSR/IntegrationRec177.lean: refutations, trig signs decided at a point (49)
OSR/IntegrationRec178.lean: refutations, trig signs decided at a point (45)
OSR/IntegrationRec179.lean: refutations of rules with Acoth (4)
OSR/IntegrationRec180.lean: refutations of rules with Acoth (8)
OSR/IntegrationRec181.lean: more linear splits into residual integrals (11)
OSR/IntegrationRec182.lean: refutations of rules with Acoth (26)
OSR/IntegrationRec183.lean: refutations of rules with Acoth (16)
OSR/IntegrationRec184.lean: refutations of rules with Acot (23)
OSR/IntegrationRec185.lean: sums of residual integrals, x and constants (11)
OSR/IntegrationRec186.lean: sums of residual integrals, closed by grind (14)
OSR/IntegrationRec187.lean: refutations checked with grind (3)
OSR/IntegrationRec188.lean: refutations checked with grind (4)
OSR/IntegrationRec189.lean: refutations from a second search (3)
OSR/IntegrationRec190.lean: refutations of rules with ≥ / ≤ conditions (42)
OSR/IntegrationRec191.lean: refutations of rules with ≥ / ≤ conditions (35)
OSR/IntegrationRec192.lean: refutations of rules with Or conditions (33)
OSR/IntegrationRec193.lean: refutations of rules with compound conditions (54)
OSR/IntegrationRec194.lean: refutations of rules with Subst (88)
OSR/IntegrationRec195.lean: refutations of rules with Subst (93)
OSR/IntegrationRec196.lean: refutations of rules with Subst (94)
OSR/Integration.lean   RUBI antiderivative rules (13) and the Integration catalogue (523)
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
with such a condition is stated over ℝ only.  `Cond.ge` (`relation1#geq`,
real only like `gt`) and `Cond.or` (binary `logic1#or`, which holds when one
side holds and is mapped over ℝ, ℂ and the Booleans) state RUBI's `GeQ`,
`LeQ`, `Not[LtQ]`, `Not[GtQ]` and `Or`; `Cond.decide?` decides an `or` when
one side is decided true or both false, and its soundness proof covers both.
Conditional rules are never
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
metavariables, and `DerivHoldsUnder` does the same for derivative rules (the
strengthened power rule `calculus.derivative.power_nonzero`, `n ≠ 0`); the
rewriter applies a conditional rule only when its
substituted conditions are closed and decided true by exact rational
arithmetic (`OSR/Decide.lean`, `CRule.conditionsDecided`; `apply?_sound`
then requires characteristic zero and the rational order).  A fourth
shape, `antiderivRec`, has residual integrals in its result
(`AntiderivRecHolds`, exported with `OMObj.omapp` as `int(λx. H)(x)`); the
rewriter does not apply it either.  A fifth, `antiderivSubst`, also lists
substitutions (`CRule.substs`): a hole `h` with `g` stands for
`int(λx. H)(g)`, v0.1 `Subst[Int[H, x], x, g]`.  `AntiderivSubstHolds`
reads it at `substAt` (`g` at the point), requires `g` defined near the point
and `H` near `g(t)`, and quantifies over functions with derivative `H(g(t))`
at `g(t)`; the result reads them composed with `g` (`substEnv`), so a proof
uses the chain rule.  `not_antiderivSubstHolds_integrand` and
`not_antiderivSubstHolds_result` refute it.
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
