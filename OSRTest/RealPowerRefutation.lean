import OSRTest.RecursiveRealPower

/-! Test-only counterexample to RUBI 2.3 #1 under candidate real powers. -/

namespace OSRTest.RealPowerRefutation

open OSR OSRTest.PositivePower OSRTest.RecursiveRealPower

-- RUBI 4.17.3.0 (pinned source), 2 Exponentials/2.3 Miscellaneous exponentials.m#1.
def rubi23_body : Expr :=
  .pow (.pow (.var "F") (.app2 .mul (.var "c")
    (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.var "n")

def rubi23_result : Expr :=
  .app2 .mul rubi23_body (.pow
    (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "n"))
      (.app1 .ln (.var "F"))) (.int (-1)))

-- All parameters are independent of x. F = b = c = n = 1 and a = 0.
def witness : String → ℝ := fun name => if name = "a" then 0 else 1

private theorem zero_pole : ¬ candidatePowerDefined 0 (-1) := by
  intro h
  rcases h with hpos | ⟨n, hn, hne⟩
  · norm_num at hpos
  · have hn' : n = -1 := by exact_mod_cast hn.symm
    subst n
    exact hne (by norm_num) rfl

/-- The integrand is defined everywhere, but the proposed result is undefined. -/
theorem rubi23_counterexample (t : ℝ) :
    (∀ v : ℝ, definedCandidate (Function.update witness "x" v) rubi23_body) ∧
      ¬ definedCandidate (Function.update witness "x" t) rubi23_result := by
  constructor
  · intro v
    simp [rubi23_body, definedCandidate, evalCandidate, Function.update, witness,
      candidatePowerDefined]
  · simp [rubi23_result, rubi23_body, definedCandidate, evalCandidate, Function.update,
      witness, Interp.real, zero_pole]

end OSRTest.RealPowerRefutation
