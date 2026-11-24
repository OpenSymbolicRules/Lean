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

These are exploratory Mathlib/Lean results, not exported OSR v1 rules and
not a new interpretation. They use Lean `v4.35.0` and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

Before an extension can certify or export rules, it needs an explicit domain
contract and a faithful mapping from OpenMath expressions and conditions. A
compatibility proof must account for **all** currently defined integer-power
cases, including negative bases and zero with nonnegative exponents; the
positive-base overlap alone is insufficient. Enlarging `Defined` changes the
quantification of existing theorem statements, so previous certificates must
be rechecked under any changed interpretation. Negative real bases, zero,
non-integer exponents, and complex branch cuts need separate decisions. No
rule has been marked proved for them here.
