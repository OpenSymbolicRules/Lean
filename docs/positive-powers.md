# Positive real powers: exploratory proof

The current OSR interpretation of `arith1#power` accepts only integer
exponents. The Integration migration report lists 520 examined rules as not
migrated because of this limit. This number is a report subset, not a count of
all unmigrated RUBI rules. The official [OpenMath definition of power](https://openmath.org/cd/arith1#power)
also describes non-integer powers via exponentials and logarithms.

`OSRTest/PositivePower.lean` uses the existing pinned Mathlib API to check a
possible first step, restricted to strictly positive real bases:

- The value of Mathlib's `Real.rpow` at an integer exponent agrees with the
  current integer-power evaluation. This equality of total values does not
  by itself establish agreement of definedness.
- On positive bases, its value is `exp(p * log(x))`, matching the applicable
  OpenMath characterization.
- With a positive base, defined operands, and an integer exponent, the
  existing OSR power expression is defined.
- For `t > 0` and `p ≠ -1`, Lean proves that the derivative of
  `x ↦ x^(p+1)/(p+1)` at `t` is `t^p`, using `Real.hasDerivAt_rpow_const`.
- A negative check shows that omitting `p ≠ -1` yields a false derivative
  claim. Another check records that Mathlib's totalized `0^(-1)` has value
  zero while the current OSR expression is undefined.
- A test-only candidate power domain accepts a strictly positive base at any
  real exponent, or an integer exponent under the current nonzero condition
  for negative exponents. Lean proves that every currently defined power is
  admitted by this candidate, including negative bases and `0^0`; it also
  checks that `2^(1/2)` is admitted and `0^(-1)` is rejected. This is a
  one-operation domain inclusion using the existing evaluations of the
  operands, not a recursive interpreter or a proof that existing rules
  remain valid after extending their domain.
- A separate check proves that `2^(1/2)` is not defined by the current OSR
  integer-only interpretation even though Mathlib's real value is positive.
  This illustrates the precise gap; it does not turn the expression into a
  supported OSR rule.

`OSRTest/RecursiveRealPower.lean` also defines a **test-only recursive
interpreter** that uses the candidate power domain and `Real.rpow`. Lean
proves by structural induction that every expression defined by the current
real interpretation remains defined with the same value in this interpreter.
A nested fractional-power example exercises recursive evaluation. This result
concerns expressions, not the preservation of theorems over the enlarged
domain, and it does not address complex powers.

`OSRTest/RealPowerPrimitive.lean` checks the exact pattern and replacement
expressions of the existing `integration.power` rule against the candidate
interpreter. It proves the full real statement with the published rule's
original condition `m ≠ -1`, including neighborhood definedness of the
replacement and its derivative. On the positive half-line this covers real,
possibly non-integer exponents. At nonpositive points, the hypothesis that
the integrand is defined on a neighborhood implies that `m` is an integer;
the proof then reuses the existing certificate, including its treatment of
zero. This is a theorem for the test interpreter, not the production
`CRule.Holds`; the rule's published status and exponent finding do not change.

A separate Lean counterexample demonstrates why theorem replay is essential:
a claim about `2^(1/2)` is vacuously true under the old definedness guard but
false when the candidate domain admits that power. This is a constructed
example, not a finding that any existing exported rule is invalid.

These are exploratory Mathlib/Lean results, not exported OSR v1 rules or
a production interpretation. They use Lean `v4.35.0` and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

Before an extension can certify or export rules, it needs an explicit domain
contract and a faithful mapping from OpenMath expressions and conditions. A
production implementation must separately establish that its recursive
interpreter satisfies the same compatibility theorem. Enlarging `Defined` changes the
quantification of existing theorem statements, so previous certificates must
be rechecked under any changed interpretation. Negative real bases, zero,
non-integer exponents, and complex branch cuts need separate decisions. No
rule has been marked proved for them here.
