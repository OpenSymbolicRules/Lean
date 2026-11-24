# Candidate upstream issues

## RUBI 4.16.1, rule 2.3 #1: missing denominator condition in transcription

The `OpenSymbolicRules/Integration` v0.1 transcription at revision
`f84ed2a81702836c019e647e0a586b8d576ae7c6` and the vendored RUBI 4.16.1
source both show only a `FreeQ[{F,a,b,c,n},x]` condition for rule 2.3 #1.
As a mathematical rewrite over the test-only candidate real interpretation,
the instance `F=b=c=n=1`, `a=0` has an everywhere-defined integrand but an
undefined result, because `b*c*n*log(F)=0`. The checked statement is
`OSRTest.RealPowerRefutation.rubi23_counterexample` in
`OSRTest/RealPowerRefutation.lean`, using Lean 4.35.0 and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

This does not prove that RUBI actually applies the rule to this instance:
Mathematica evaluation or rule dispatch may simplify it first. Runtime
reproduction is still required before reporting a confirmed upstream bug.
The case establishes that a nonzero denominator is necessary for an OSR
rewrite valid for every mathematical substitution; it does not establish that
this condition alone handles all real or complex branch and domain cases.
