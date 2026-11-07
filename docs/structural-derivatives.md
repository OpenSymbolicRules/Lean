# Structural derivatives and missing premises

The three structural rules in Calculus v0.1
(`eb9eb87aa7ffcd6dd7da055fa6b6d87f35f840da`,
`2-derivatives/2.3-structural-derivatives`) have empty conditions.
They differentiate a sum, product or difference and introduce derivatives
of the operands on the right-hand side. Those derivatives need not exist,
even when the composite has a derivative.

## Formal witnesses

Let `h(x) = sqrt(x^2) = |x|`. This uses `arith1#root` and `arith1#power`
from the existing real fragment, with no new OpenMath symbol. It is defined
everywhere but is not differentiable at zero. The following theorems in
`OSR/Calculus.lean` prove `HasDerivAt` with derivative zero for each composite,
and prove that its operands are not differentiable at zero:

| v0.1 rule | Operands | Composite | Lean theorem |
|---|---|---|---|
| Sum (`:1`) | `h`, `-h` | `0` | `OSR.Calculus.structuralSum_missingPremise` |
| Product (`:2`) | `h`, `h` | `x^2` | `OSR.Calculus.structuralProduct_missingPremise` |
| Difference (`:3`) | `h`, `h` | `0` | `OSR.Calculus.structuralDifference_missingPremise` |

These are diagnostics of missing premises, not refutations of a
`CRule.Holds` statement: `CRule` does not represent structural derivatives.
In particular, Mathlib's totalized `deriv` returns zero when a function is
not differentiable; a numerical equality between such values would not
establish that the OpenMath derivatives exist.

The proofs use Lean **4.35.0** and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. `OSRTest/Calculus.lean` checks
their types and rejects axioms other than `propext`, `Classical.choice`
and `Quot.sound`. `just check` replays their module with `leanchecker`.

## Migration decision

Keep all three rules in the report's `not_migrated` list, with both reasons:
missing differentiability premises and the non-OpenMath `osr#Apply` node.
The v1 conditions cannot currently express differentiability of matched
operands. Adding that premise silently would strengthen the source rule.
Supporting lambda application alone would therefore not resolve migration.

With explicit differentiability premises, the sum, difference and product
rules are valid. A future extension must express and check those premises
before these rules can enter the certified catalogue.
