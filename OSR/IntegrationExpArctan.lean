import OSR.IntegrationNum1

open OSR OSR.Calculus Filter Topology
namespace OSR.IntegrationExpArctan

/-- The strengthened exponential-arctangent primitive over the reals. -/
theorem expArctan_real : IntegrationNum1.rubi536r13Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" IntegrationNum1.rubi536r13Nondeg.conditions
    IntegrationNum1.rubi536r13Nondeg.body IntegrationNum1.rubi536r13Nondeg.result
  intro env hcond t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hd : env "d" = (env "a") ^ 2 * env "c" := by
    have h := hcond (.eq (.var "d") (.app2 .mul (.pow (.var "a") (.int 2)) (.var "c")))
      (by simp [IntegrationNum1.rubi536r13Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, h2] using h
  have hn : env "a" * env "c" * env "n" ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "n")) (.int 0))
      (by simp [IntegrationNum1.rubi536r13Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have ha : env "a" ≠ 0 := by intro h; apply hn; simp [h]
  have hc : env "c" ≠ 0 := by intro h; apply hn; simp [h]
  have hn' : env "n" ≠ 0 := by intro h; apply hn; simp [h]
  have hbody : env "c" + env "d" * t ^ 2 ≠ 0 := by
    have h := hF.self_of_nhds
    simpa [IntegrationNum1.rubi536r13Nondeg, Defined, eval, Interp.real, Function.update, h2, hm1] using h
  have hpos : 1 + (env "a" * t) ^ 2 ≠ 0 := by positivity
  constructor
  · filter_upwards with w
    simp [IntegrationNum1.rubi536r13Nondeg, Defined, eval, Interp.real, Function.update, hm1, hn]
  · have hU : HasDerivAt (fun w : ℝ => env "a" * w) (env "a") t := by
      simpa using (hasDerivAt_id' t).const_mul (env "a")
    have hA := (Real.hasDerivAt_arctan' _).comp t hU
    have hE := (hA.const_mul (env "n")).exp
    have hfun : (fun w => eval Interp.real (Function.update env "x" w) IntegrationNum1.rubi536r13Nondeg.result) =
      (fun w : ℝ => Real.exp (env "n" * Real.arctan (env "a" * w)) * (env "a" * env "c" * env "n")⁻¹) := by
      funext w
      simp [IntegrationNum1.rubi536r13Nondeg, eval, Interp.real, Function.update, hm1]
    rw [hfun]
    refine (hE.mul_const _).congr_deriv ?_
    simp [IntegrationNum1.rubi536r13Nondeg, eval, Interp.real, Function.update, h2, hm1]
    rw [hd]
    field_simp [ha, hc, hn']

/-- The strengthened reciprocal-arctangent variant over the reals. -/
theorem expArctanReciprocal_real : IntegrationNum1.rubi536r55Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" IntegrationNum1.rubi536r55Nondeg.conditions
    IntegrationNum1.rubi536r55Nondeg.body IntegrationNum1.rubi536r55Nondeg.result
  intro env hcond t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hd : env "d" = (env "a") ^ 2 * env "c" := by
    have h := hcond (.eq (.var "d") (.app2 .mul (.pow (.var "a") (.int 2)) (.var "c")))
      (by simp [IntegrationNum1.rubi536r55Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, h2] using h
  have hn : env "a" * env "c" * env "n" ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "n")) (.int 0))
      (by simp [IntegrationNum1.rubi536r55Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have ha : env "a" ≠ 0 := by intro h; apply hn; simp [h]
  have hc : env "c" ≠ 0 := by intro h; apply hn; simp [h]
  have hn' : env "n" ≠ 0 := by intro h; apply hn; simp [h]
  have hdefined : ∀ᶠ w in 𝓝 t, env "a" * w ≠ 0 ∧ env "c" + env "d" * w ^ 2 ≠ 0 := by
    filter_upwards [hF] with w hw
    simpa [IntegrationNum1.rubi536r55Nondeg, Defined, eval, Interp.real, Function.update, h2, hm1] using hw
  have hat := hdefined.self_of_nhds
  have ht : t ≠ 0 := by intro h; apply hat.1; simp [h]
  have hinvpos : 1 + ((env "a" * t)⁻¹) ^ 2 ≠ 0 := by positivity
  constructor
  · filter_upwards [hdefined] with w hw
    simp [IntegrationNum1.rubi536r55Nondeg, Defined, eval, Interp.real, Function.update, hm1, hn, hw.1]
  · have hU : HasDerivAt (fun w : ℝ => env "a" * w) (env "a") t := by
      simpa using (hasDerivAt_id' t).const_mul (env "a")
    have hV := hU.inv hat.1
    have hA := (Real.hasDerivAt_arctan' _).comp t hV
    have hE := (hA.const_mul (env "n")).exp
    have hfun : (fun w => eval Interp.real (Function.update env "x" w) IntegrationNum1.rubi536r55Nondeg.result) =
      (fun w : ℝ => -Real.exp (env "n" * Real.arctan ((env "a" * w)⁻¹)) * (env "a" * env "c" * env "n")⁻¹) := by
      funext w
      simp [IntegrationNum1.rubi536r55Nondeg, eval, Interp.real, Function.update, hm1]
    rw [hfun]
    refine (hE.neg.mul_const _).congr_deriv ?_
    simp [IntegrationNum1.rubi536r55Nondeg, eval, Interp.real, Function.update, h2, hm1]
    rw [hd]
    field_simp [ha, hc, hn', ht]
    ring

end OSR.IntegrationExpArctan
