# Candidate upstream issues

## RUBI 4.17.3.0 (pinned source), rule 2.3 #1: missing denominator condition in transcription

The `OpenSymbolicRules/Integration` v0.1 transcription at revision
`f84ed2a81702836c019e647e0a586b8d576ae7c6` and the vendored RUBI 4.17.3.0
source (revision `61e9c18`, declaring version `4.17.3.0` in `PacletInfo.m`)
both show only a `FreeQ[{F,a,b,c,n},x]` condition for rule 2.3 #1. The
v0.1 per-rule `4.16.1` label is historical and not independently verified.
As a mathematical rewrite over the test-only candidate real interpretation,
the instance `F=b=c=n=1`, `a=0` has an everywhere-defined integrand but an
undefined result, because `b*c*n*log(F)=0`. The checked statement is
`OSRTest.RealPowerRefutation.rubi23_counterexample` in
`OSRTest/RealPowerRefutation.lean`, using Lean 4.35.0 and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

A second witness, `F=2`, `a=b=0`, `c=n=1`, is also checked against the
production integer-exponent interpretation by
`OSR.IntegrationExpPower.rubi23r1_counterexample_real`.

Neither witness proves that RUBI actually applies the rule to this instance:
Mathematica evaluation or rule dispatch may simplify it first. Runtime
reproduction is still required before reporting a confirmed upstream bug.
The case establishes that a nonzero denominator is necessary for an OSR
rewrite valid for every mathematical substitution; it does not establish that
this condition alone handles all real or complex branch and domain cases.
