# M0 — Ecosystem and semantic audit

Audit date: 2026-11-05.

## Inspected revisions

| Repository | Commit | Local branch at inspection |
|---|---|---|
| Specification | `b8bea34aad328ab09e1b5850c5830c17aa8d00fc` | `feat/semantic-closure-over-constraints` |
| Trigonometry | `e9b6ef0e46495c9896b5dc168dabd5f7c1fa39b5` | `main` |
| Algebra | `e8152ba57aa7a10a270a1e9ed16f75bede335ad1` | `main` |
| Calculus | `20b7d168454571192047fd6b2440d1fe2a9b321b` | `feat/composable-structural-derivatives` |
| Logic | `57277b06dfcac4a92ed0c536e6bd94fa76935245` | `main` |
| Integration | `66f04cb1433cc06256a1b2e73a711c00492f4286` | `fix/converter-constraint-semantics` |
| OpenSymbolicRules.jl | `bd24d5a55c2645c8830a0b096d3b01b7a026d6df` | `main` |
| .github (profile) | `018bf796836631996cfbfe5a2802d29026b22da2` | `main` |
| Lean, OpenMath, Conformance, Verification | empty at creation | — |

Pinned dependencies of the pilot:

| Dependency | Version |
|---|---|
| Lean | `leanprover/lean4:v4.35.0` |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` (tag `v4.35.0`) |
| OpenMath CDs | see the table below; files in `OpenSymbolicRules/OpenMath/cd/` |
| Julia | 1.13.0, with OpenSymbolicRules.jl's own `Manifest.toml` |

| CD | Version | Revision | Date | SHA-256 |
|---|---|---|---|---|
| arith1 | 3 | 1 | 2004-03-30 | `8dab1c65…6f8a` |
| transc1 | 3 | 1 | 2004-03-30 | `75ed9e26…177d` |
| nums1 | 4 | 0 | 2009-04-01 | `691c8ebf…bbe5` |
| relation1 | 3 | 1 | 2004-03-30 | `1c50e725…42e6` |
| setname1 | 3 | 1 | 2004-03-30 | `746cc460…abd` |

Full hashes are recorded in `OSR/Semantics.lean`.

## Specification v0.1 findings

These motivate a new major version rather than incremental fixes.

1. **Corpus and format are conflated.**  A global replacement of "RUBI" by
   "OSR" left `docs/spec.md` describing the RUBI corpus as OSR.  For example:
   - "Inspired by: OSR 4.16+ / OSR 5 (Albert Rich)";
   - "OSR-style symbolic symbolic rules";
   - the glossary entry "OSR = Portable Integration Rules Format";
   - "OSR Software License (MIT)".
2. **The specification is integration-only.**  The following requirements
   cannot be met by Logic, Trigonometry or Algebra:
   - the mandatory RUBI 9-section taxonomy (OSR-T-001);
   - a test suite of at least 72,000 problems (OSR-V-005);
   - an "integration engine" (§10).
3. **Specification and schemas disagree:**
   - `$schema` is `rubi-integration-rules/vX.Y` (OSR-F-004) in the spec, but
     `open-symbolic-rules/v0.1` in the schemas;
   - OSR-V-002 names the field `optimal_antiderivative`, the schema names it
     `expected_result`;
   - the `load_order` objects `{path, requires}` of OSR-F-012a are rejected by
     `meta.schema.json`;
   - the ABNF lacks the `symbol` type tag and sequence wildcards;
   - OSR-W-002 gives `b.` the default 1, OSR-W-002a gives it 0;
   - OSR-L-012 forbids a duplicate `id` globally, while OSR-F-008 makes `id`
     file-local.
4. **OSR-F-003a is unsatisfiable.**  It requires an OpenMath mapping for every
   operator, yet many operators have none (`Dist`, `Subst`, `Simp`, utility
   functions).  Integration works around this with invented CDs
   (`openmath:osr#Dist`, `openmath:osr#f`, …).
5. **Editorial defects:**
   - two sections numbered 5.5;
   - an unnumbered "Ecosystem discovery" section;
   - a stale traceability matrix ("159" requirements);
   - placeholder `$id` (`https://domain.org/…`);
   - mojibake in `ROADMAP.md` ("GrÃ¶bner");
   - duplicated `### Added` in `CHANGELOG.md`.
6. **Submodule drift.**  Integration pins Specification `e4f2d5c`; Algebra,
   Calculus, Trigonometry and Logic pin `5424ff2`, which predates the `symbol`
   wildcard and the closure check over constraints.

## Trigonometry inventory

13 distinct rules in 7 files:
- the `default` manifest (10 rules) excludes `1.6-sum-to-product`;
- the `sum_to_product` profile (11 rules) excludes `1.4-product-to-sum`.

OpenMath symbols used:
- `arith1`: `plus`, `minus`, `times`, `divide`, `power`;
- `transc1`: `sin`, `cos`, `tan`, `arctan`.

No rule has a constraint.  There are 13 test problems, one per rule, each a
single-step rewrite.

| v0.1 identity | v1 id | ℝ | ℂ |
|---|---|---|---|
| `…/1.1-pythagorean:1` | `trigonometry.pythagorean` | certified | certified |
| `…/1.2-angle-sum:1` | `trigonometry.angle_sum.sin_add` | certified | certified |
| `…/1.2-angle-sum:2` | `trigonometry.angle_sum.cos_sub` | certified | certified |
| `…/1.3-double-angle:1` | `trigonometry.double_angle.sin` | certified | certified |
| `…/1.3-double-angle:2` | `trigonometry.double_angle.cos` | certified | certified |
| `…/1.4-product-to-sum:1` | `trigonometry.product_to_sum.sin_cos` | certified | certified |
| `…/1.4-product-to-sum:2` | `trigonometry.product_to_sum.sin_sin` | certified | certified |
| `…/1.5-power-reduction:1` | `trigonometry.power_reduction.sin_sq` | certified | certified |
| `…/1.5-power-reduction:2` | `trigonometry.power_reduction.cos_sq` | certified | certified |
| `…/1.6-sum-to-product:1` | `trigonometry.sum_to_product.sin_add_sin` | certified | certified |
| `…/1.6-sum-to-product:2` | `trigonometry.sum_to_product.cos_add_cos` | certified | certified |
| `…/1.6-sum-to-product:3` | `trigonometry.sum_to_product.cos_sub_cos` | certified | certified |
| `…/2.1-tangent-inverse:1` | `trigonometry.inverse.tan_arctan` | certified | proved, **not certified** |

The generated `report.md` is the authoritative per-rule record.

### Findings

- **`tan(arctan z) ⟶ z` over ℂ.**  v0.1 states it without a condition and cites
  Fungrim `1f026d` for complex `z`.  `arctan` is undefined at `z = ±i`, and
  `Complex.tan_arctan` (Mathlib) requires `z ≠ I` and `z ≠ -I`.  No hypothesis
  was added.  The pattern's definedness carries the restriction, and the proof
  uses exactly that.  The record stays uncertified because the mapping of
  `transc1#arctan` to `Complex.arctan` is `provisional`: the CMP gives
  arctan z = (i/2) ln((1 − iz)/(1 + iz)), Mathlib defines
  arctan z = −i/2 · log((1 + zi)/(1 − zi)), and their agreement on the branch
  cuts is not established.
- **The v0.1 `default` profile does not terminate.**  Angle sum gives
  `sin(x + y) ⟶ sin x cos y + cos x sin y`, and product-to-sum then gives
  `sin x cos y ⟶ (sin(x + y) + sin(x − y))/2`.  The result contains `sin(x + y)`
  again, so the two rules cycle under any strategy that applies both.  Both
  rules are proved: this is a strategy property, observed in the Julia engine,
  where the step budget is exhausted.  The `sum_to_product` profile already
  excludes product-to-sum for the analogous reason; `default` needs the same
  treatment.
- **Mixed-arity products in v0.1.**  `["Multiply", 2, sin, cos]` is n-ary while
  other rules are binary.  v1 uses binary `times`, left-nested.
