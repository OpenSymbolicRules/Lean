import OSR.IntegrationNum1
import OSR.IntegrationRec131

open OSR OSR.Calculus Filter Topology
namespace OSR.IntegrationCosecant

/-- Away from a sine zero the cosine lies in the real domain of artanh. -/
theorem cos_between (x : ℝ) (hs : Real.sin x ≠ 0) :
    -1 < Real.cos x ∧ Real.cos x < 1 := by
  have hs2 : 0 < Real.sin x ^ 2 := sq_pos_of_ne_zero hs
  have hp := Real.sin_sq_add_cos_sq x
  constructor <;> nlinarith [sq_nonneg (Real.cos x + 1), sq_nonneg (Real.cos x - 1)]

/-- The strengthened cosecant primitive is valid over the reals. -/
theorem cosecant_real : IntegrationNum1.rubi4511r4Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" IntegrationNum1.rubi4511r4Nondeg.conditions
    IntegrationNum1.rubi4511r4Nondeg.body IntegrationNum1.rubi4511r4Nondeg.result
  intro env hcond t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hd : env "d" ≠ 0 := by
    have h := hcond (.ne (.var "d") (.int 0)) (by simp [IntegrationNum1.rubi4511r4Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hsin : ∀ᶠ w in 𝓝 t, Real.sin (env "c" + env "d" * w) ≠ 0 := by
    filter_upwards [hF] with w hw
    simpa [IntegrationNum1.rubi4511r4Nondeg, Defined, eval, Interp.real, Function.update] using hw
  constructor
  · filter_upwards [hsin] with w hw
    obtain ⟨hl, hr⟩ := cos_between _ hw
    simp [IntegrationNum1.rubi4511r4Nondeg, Defined, eval, Interp.real, Function.update, hm1, hd, hl, hr]
  · have hs0 := hsin.self_of_nhds
    obtain ⟨hl, hr⟩ := cos_between _ hs0
    have hU : HasDerivAt (fun w : ℝ => env "c" + env "d" * w) (env "d") t := by
      simpa using (((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c"))
    have hC := (Real.hasDerivAt_cos _).comp t hU
    have hA := (OSR.IntegrationRec131.hasDerivAt_artanh hl hr).comp t hC
    have hfun : (fun w => eval Interp.real (Function.update env "x" w) IntegrationNum1.rubi4511r4Nondeg.result) =
      (fun w : ℝ => -Real.artanh (Real.cos (env "c" + env "d" * w)) * (env "d")⁻¹) := by
      funext w
      simp [IntegrationNum1.rubi4511r4Nondeg, eval, Interp.real, Function.update, hm1]
    rw [hfun]
    refine (hA.neg.mul_const _).congr_deriv ?_
    simp [IntegrationNum1.rubi4511r4Nondeg, eval, Interp.real, Fn.csc, Function.update]
    have hp := Real.sin_sq_add_cos_sq (env "c" + env "d" * t)
    have hs2 : Real.sin (env "c" + env "d" * t) ^ 2 ≠ 0 := pow_ne_zero 2 hs0
    have heq : 1 - Real.cos (env "c" + env "d" * t) ^ 2 = Real.sin (env "c" + env "d" * t) ^ 2 := by linarith
    rw [heq]
    field_simp

end OSR.IntegrationCosecant
