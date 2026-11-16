import OSR.Calculus

/-!
# Integration: standard migration findings

The texts of the findings shared by the Integration catalogue
(`OSR.Integration`) and the strengthened variants checked numerically
(`OSR.IntegrationNum1`).
-/

namespace OSR.IntegrationFindings

def optionalFinding (vars : String) (plural : Bool := true) : String :=
  if plural then
    s!"matching: the optional wildcards {vars} of the v0.1 pattern are ordinary metavariables; the v1 rule does not match the instances with RUBI's default values."
  else
    s!"matching: the optional wildcard {vars} of the v0.1 pattern is an ordinary metavariable; the v1 rule does not match the instances with RUBI's default value."

def neqFinding (cond : String) : String :=
  s!"conditions: RUBI's {cond} becomes a relation1#neq condition, read semantically (both sides defined, values different); Mathematica's NeQ tests that the difference is not possibly zero. The reference rewriter does not apply conditional rules."

def integerFinding (m : String) : String :=
  s!"exponent: the fragment interprets arith1#power for integer exponents only, so the statement covers the integer values of {m}; for other values the integrand is undefined."

def condFinding (cs : String) : String :=
  s!"conditions: RUBI's {cs} become OSR v1 conditions (relation1#neq, relation1#eq, relation1#gt, set1#in with setname1#Z), read semantically on defined values."

def recFinding : String :=
  "residual integrals: the result contains Int[…], exported as int(λx. H)(x) (the calculus1#int FMP form); the statement holds for every choice of antiderivatives of the residual integrands. The reference rewriter does not apply this rule."

end OSR.IntegrationFindings
