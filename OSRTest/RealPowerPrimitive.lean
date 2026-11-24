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

/-- For an integer exponent the candidate adds no points to this integrand's domain. -/
theorem integer_body_candidate_implies_old (env : String → ℝ) (n : ℤ)
    (hn : env "m" = n) (v : ℝ)
    (h : definedCandidate (Function.update env "x" v) power_body) :
    Defined Interp.real (Function.update env "x" v) power_body := by
  have hdomain : candidatePowerDefined v (env "m") := by
    simpa [power_body, definedCandidate, evalCandidate, Function.update] using h
  have hnonzero : n < 0 → v ≠ 0 := by
    rcases hdomain with hpos | ⟨k, hk, hkne⟩
    · exact fun _ => ne_of_gt hpos
    · have heq : k = n := by exact_mod_cast (hk.symm.trans hn)
      subst k
      exact hkne
  have hi : intValue? (env "m") = some n := (intValue?_eq _ _).2 hn
  have hpow : ∃ k, Interp.real.toInt? (env "m") = some k ∧ (k < 0 → v ≠ 0) :=
    ⟨n, hi, hnonzero⟩
  simpa [power_body, Defined, eval, Function.update] using hpow

/-- For integer exponents the existing certificate transfers, including negative bases and zero. -/
theorem candidate_power_primitive_integer (env : String → ℝ) (t : ℝ) (n : ℤ)
    (hn : env "m" = n) (hp : env "m" ≠ -1)
    (hF : ∀ᶠ v in 𝓝 t, definedCandidate (Function.update env "x" v) power_body) :
    (∀ᶠ v in 𝓝 t, definedCandidate (Function.update env "x" v) power_result) ∧
    HasDerivAt (fun v => evalCandidate (Function.update env "x" v) power_result)
      (evalCandidate (Function.update env "x" t) power_body) t := by
  have hFold : ∀ᶠ v in 𝓝 t, Defined Interp.real (Function.update env "x" v) power_body := by
    filter_upwards [hF] with v hv
    exact integer_body_candidate_implies_old env n hn v hv
  have hc : ∀ c ∈ Integration.power.conditions, c.Holds Interp.real env := by
    simp [Integration.power, Cond.Holds, Defined, eval, hp]
  have hold := Integration.power_holds Interp.real env hc t hFold
  have heqF := (old_recursive_compatibility (Function.update env "x" t)
    power_body hFold.self_of_nhds).2
  have heqG : (fun v => evalCandidate (Function.update env "x" v) power_result) =ᶠ[𝓝 t]
      (fun v => eval Interp.real (Function.update env "x" v) power_result) := by
    filter_upwards [hold.1] with v hv
    exact (old_recursive_compatibility (Function.update env "x" v) power_result hv).2
  constructor
  · filter_upwards [hold.1] with v hv
    exact (old_recursive_compatibility (Function.update env "x" v) power_result hv).1
  · have hd := hold.2.congr_of_eventuallyEq heqG
    change HasDerivAt (fun v => evalCandidate (Function.update env "x" v) power_result)
      (eval Interp.real (Function.update env "x" t) power_body) t at hd
    rw [← heqF] at hd
    exact hd

/-- The existing power rule holds in the test interpreter over its whole real domain. -/
theorem candidate_power_full (env : String → ℝ) (t : ℝ)
    (hp : env "m" ≠ -1)
    (hF : ∀ᶠ v in 𝓝 t, definedCandidate (Function.update env "x" v) power_body) :
    (∀ᶠ v in 𝓝 t, definedCandidate (Function.update env "x" v) power_result) ∧
    HasDerivAt (fun v => evalCandidate (Function.update env "x" v) power_result)
      (evalCandidate (Function.update env "x" t) power_body) t := by
  by_cases ht : 0 < t
  · exact candidate_power_primitive_neighborhood env t ht hp
  · obtain ⟨v, hvt, hv⟩ := hF.exists_lt
    have hvnot : ¬ 0 < v := by linarith
    have hdomain : candidatePowerDefined v (env "m") := by
      simpa [power_body, definedCandidate, evalCandidate, Function.update] using hv
    rcases hdomain with hpos | ⟨n, hn, _⟩
    · exact (hvnot hpos).elim
    · exact candidate_power_primitive_integer env t n hn hp hF

/-- The full candidate statement with the published rule's original conditions. -/
theorem candidate_published_power (env : String → ℝ) (t : ℝ)
    (hc : ∀ c ∈ Integration.power.conditions, c.Holds Interp.real env)
    (hF : ∀ᶠ v in 𝓝 t, definedCandidate (Function.update env Integration.power.x v)
      Integration.power.body) :
    (∀ᶠ v in 𝓝 t, definedCandidate (Function.update env Integration.power.x v)
      Integration.power.result) ∧
    HasDerivAt (fun v => evalCandidate (Function.update env Integration.power.x v)
      Integration.power.result)
      (evalCandidate (Function.update env Integration.power.x t) Integration.power.body) t := by
  have hp : env "m" ≠ -1 := by
    simpa [Integration.power, Cond.Holds, Defined, eval] using hc
  exact candidate_power_full env t hp hF

end OSRTest.RealPowerPrimitive
