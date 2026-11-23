import OSR.IntegrationRec207
import OSR.IntegrationRec26

/-! # A complex branch-cut counterexample for RUBI 3.1.2 #2 -/

namespace OSR.IntegrationRec208

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem iv0 : intValue? (0 : ℂ) = some 0 := by
  simpa using intValue?_intCast (α := ℂ) 0

private theorem iv1 : intValue? (1 : ℂ) = some 1 := by
  simpa using intValue?_intCast (α := ℂ) 1

private theorem ivm1 : intValue? (-1 : ℂ) = some (-1) := by
  simpa using intValue?_intCast (α := ℂ) (-1)

/-- The nonzero denominator does not remove the logarithm's branch cut. -/
theorem rubi312r2Nondeg_counterexample_complex : ¬ rubi312r2Nondeg.Holds .complex := by
  show ¬ AntiderivSubstHolds Interp.complex "x" rubi312r2Nondeg.conditions
    rubi312r2Nondeg.body rubi312r2Nondeg.result rubi312r2Nondeg.integrals
    rubi312r2Nondeg.substs
  let env : String → ℂ := fun s => if s = "b" ∨ s = "c" ∨ s = "n" then 1 else 0
  have hc : ∀ c ∈ rubi312r2Nondeg.conditions, c.Holds Interp.complex env := by
    simp [rubi312r2Nondeg, Cond.Holds, Defined, eval, Interp.complex, env]
  have hF : ∀ᶠ v : ℂ in 𝓝 (-1 : ℂ),
      Defined Interp.complex (Function.update env "x" v) rubi312r2Nondeg.body := by
    filter_upwards [eventually_ne_nhds (by norm_num : (-1 : ℂ) ≠ 0)] with v hv
    simp [rubi312r2Nondeg, Defined, eval, Interp.complex, env, iv0, iv1, ivm1, hv]
  intro h
  let Φ : String → ℂ → ℂ := fun _ w => w
  have hΦ : ∀ i ∈ rubi312r2Nondeg.integrals, HasDerivAt (Φ i.1)
      (eval Interp.complex (Function.update env "x"
        (substAt Interp.complex env rubi312r2Nondeg.substs "x" i.1 (-1))) i.2)
      (substAt Interp.complex env rubi312r2Nondeg.substs "x" i.1 (-1)) := by
    simp [rubi312r2Nondeg, Φ, substAt, List.lookup, eval, Interp.complex, env, iv0, iv1]
    exact hasDerivAt_id' _
  have hderiv := ((h env hc (-1) hF).2 Φ hΦ).2
  have hfun : (fun v => eval Interp.complex
      (substEnv Interp.complex env (rubi312r2Nondeg.integrals.map (·.1))
        rubi312r2Nondeg.substs Φ "x" v) rubi312r2Nondeg.result) = Complex.log := by
    funext v
    simp [rubi312r2Nondeg, substEnv, substAt, List.lookup, eval, Interp.complex, env, Φ, iv1, ivm1]
  rw [hfun] at hderiv
  have hne : (fun (_ l : ℂ) => l) (-1) (Real.pi * Complex.I) ≠
      (fun (_ l : ℂ) => l) (-1) (-(Real.pi * Complex.I)) := by
    intro heq
    have him := congrArg Complex.im heq
    simp at him
    linarith [Real.pi_pos]
  exact OSR.IntegrationRec26.not_continuous_clog (fun _ l => l) (by fun_prop) hne hderiv.continuousAt

end OSR.IntegrationRec208
