import OSRTest.RecursiveRealPower
import OSR.Integration

/-! Local test of an OSR expression under the candidate interpretation. -/

namespace OSRTest.RealPowerPrimitive

open OSR OSRTest.PositivePower OSRTest.RecursiveRealPower Filter Topology

def power_body : Expr := .pow (.var "x") (.var "m")
def power_result : Expr :=
  .app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1)))
    (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))

-- Match the existing published rule's actual expressions, not merely an equivalent formula.
example : power_body = Integration.power.body := rfl
example : power_result = Integration.power.result := rfl

/-- On the positive half-line, the candidate OSR expressions have the expected derivative. -/
theorem candidate_power_primitive (env : String → ℝ) (t : ℝ)
    (ht : 0 < t) (hp : env "m" ≠ -1) :
    definedCandidate (Function.update env "x" t) power_body ∧
    definedCandidate (Function.update env "x" t) power_result ∧
    HasDerivAt (fun v => evalCandidate (Function.update env "x" v) power_result)
      (evalCandidate (Function.update env "x" t) power_body) t := by
  have hp' : env "m" + 1 ≠ 0 := by
    intro h
    apply hp
    linarith
  constructor
  · simp [power_body, definedCandidate, evalCandidate, Function.update,
      candidatePowerDefined, ht]
  constructor
  · simp only [power_result, definedCandidate, evalCandidate, Function.update]
    refine ⟨⟨trivial, ⟨trivial, trivial⟩, Or.inl ht⟩, ?_⟩
    exact ⟨⟨trivial, trivial⟩, trivial,
      Or.inr ⟨-1, by norm_num, fun _ => by simpa using hp'⟩⟩
  · simpa [power_result, power_body, evalCandidate, Function.update,
      Real.rpow_neg_one, div_eq_mul_inv] using
      positive_power_primitive (env "m") t ht hp

/-- The replacement is defined throughout a neighborhood, as calculus rules require. -/
theorem candidate_power_primitive_neighborhood (env : String → ℝ) (t : ℝ)
    (ht : 0 < t) (hp : env "m" ≠ -1) :
    (∀ᶠ v in 𝓝 t, definedCandidate (Function.update env "x" v) power_result) ∧
    HasDerivAt (fun v => evalCandidate (Function.update env "x" v) power_result)
      (evalCandidate (Function.update env "x" t) power_body) t := by
  constructor
  · filter_upwards [isOpen_Ioi.mem_nhds ht] with v hv
    exact (candidate_power_primitive env v hv hp).2.1
  · exact (candidate_power_primitive env t ht hp).2.2

end OSRTest.RealPowerPrimitive
