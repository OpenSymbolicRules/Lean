import OSR.IntegrationExpPower

open OSR OSR.Calculus OSR.IntegrationExpPower

-- The migration retains the original FreeQ parameters and adds no condition.
#guard rubi23r1.conditions.isEmpty
#guard rubi23r1.independent == ["F", "a", "b", "c", "n"]
#guard rubi23r1.wellFormed
#guard rubi23r1.shape == .antideriv

-- The counterexample is a kernel-checked negation of the original real rule.
example : ¬ rubi23r1.Holds .real := rubi23r1_counterexample_real
