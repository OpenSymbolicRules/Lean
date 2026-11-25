import OSR.IntegrationNum1
import OSR.IntegrationRec131

/-! # Strengthened trigonometric and hyperbolic variants without residual integrals

Proofs of strengthened variants of `OSR.IntegrationNum1` whose result is closed (shape
`antideriv`): the integrand is the derivative of the result wherever the integrand is defined
near the point. -/

namespace OSR.IntegrationRec210

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem hasDerivAt_lin {𝕜 : Type} [NontriviallyNormedField 𝕜] (a b t : 𝕜) :
    HasDerivAt (fun w => a + b * w) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

private theorem hasDerivAt_quad {𝕜 : Type} [NontriviallyNormedField 𝕜] (a b c t : 𝕜) :
    HasDerivAt (fun w => a + b * w + c * w ^ 2) (b + 2 * c * t) t := by
  have h := (((hasDerivAt_id t).const_mul b).const_add a).add ((hasDerivAt_pow 2 t).const_mul c)
  refine h.congr_deriv ?_
  simp; ring

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

/-! ## RUBI 4.1.1.1 #6: `∫ sin(c + d x) dx` -/

theorem rubi4111r6Nondeg_real : rubi4111r6Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi4111r6Nondeg.conditions rubi4111r6Nondeg.body
    rubi4111r6Nondeg.result
  intro env hc t _
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4111r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  refine ⟨?_, ?_⟩
  · filter_upwards with w
    simp [rubi4111r6Nondeg, Defined, eval, Interp.real, ivm1R, hd]
  · have hfun : (fun w => eval Interp.real (Function.update env "x" w) rubi4111r6Nondeg.result) =
        fun w => -Real.cos (env "c" + env "d" * w) * (env "d")⁻¹ := by
      funext w; simp [rubi4111r6Nondeg, eval, Interp.real, ivm1R]
    rw [hfun]
    refine (((Real.hasDerivAt_cos _).comp t (hasDerivAt_lin _ _ t)).neg.mul_const _).congr_deriv ?_
    simp [rubi4111r6Nondeg, eval, Interp.real]
    field_simp

theorem rubi4111r6Nondeg_complex : rubi4111r6Nondeg.Holds .complex := by
  show AntiderivHoldsUnder Interp.complex "x" rubi4111r6Nondeg.conditions rubi4111r6Nondeg.body
    rubi4111r6Nondeg.result
  intro env hc t _
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4111r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  refine ⟨?_, ?_⟩
  · filter_upwards with w
    simp [rubi4111r6Nondeg, Defined, eval, Interp.complex, ivm1C, hd]
  · have hfun : (fun w => eval Interp.complex (Function.update env "x" w)
        rubi4111r6Nondeg.result) =
        fun w => -Complex.cos (env "c" + env "d" * w) * (env "d")⁻¹ := by
      funext w; simp [rubi4111r6Nondeg, eval, Interp.complex, ivm1C]
    rw [hfun]
    refine (((Complex.hasDerivAt_cos _).comp t (hasDerivAt_lin _ _ t)).neg.mul_const _).congr_deriv ?_
    simp [rubi4111r6Nondeg, eval, Interp.complex]
    field_simp

/-! ## RUBI 4.5.1.1 #4: `∫ csc(c + d x) dx` -/

private theorem cos_mem_of_sin_ne {u : ℝ} (h : Real.sin u ≠ 0) :
    -1 < Real.cos u ∧ Real.cos u < 1 := by
  have hs : 0 < Real.sin u ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h))
  have hc : Real.cos u ^ 2 < 1 := by nlinarith [Real.sin_sq_add_cos_sq u]
  exact abs_lt.mp (sq_lt_one_iff_abs_lt_one _ |>.mp hc)

theorem rubi4511r4Nondeg_real : rubi4511r4Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi4511r4Nondeg.conditions rubi4511r4Nondeg.body
    rubi4511r4Nondeg.result
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4511r4Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4511r4Nondeg.body →
      Real.sin (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simpa [rubi4511r4Nondeg, Defined, eval, Interp.real] using h
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := cos_mem_of_sin_ne (hD w hw)
    simp [rubi4511r4Nondeg, Defined, eval, Interp.real, ivm1R, hd, h.1, h.2]
  · have hs := hD t hF.self_of_nhds
    have hcm := cos_mem_of_sin_ne hs
    have hfun : (fun w => eval Interp.real (Function.update env "x" w) rubi4511r4Nondeg.result) =
        fun w => -Real.artanh (Real.cos (env "c" + env "d" * w)) * (env "d")⁻¹ := by
      funext w; simp [rubi4511r4Nondeg, eval, Interp.real, ivm1R]
    rw [hfun]
    have h := (((OSR.IntegrationRec131.hasDerivAt_artanh hcm.1 hcm.2).comp t
      ((Real.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "c") (env "d") t))).neg.mul_const
      (env "d")⁻¹)
    refine h.congr_deriv ?_
    have h1 : 1 - Real.cos (env "c" + env "d" * t) ^ 2 = Real.sin (env "c" + env "d" * t) ^ 2 := by
      rw [Real.cos_sq']; ring
    rw [h1]
    simp [rubi4511r4Nondeg, eval, Interp.real, Fn.csc]
    field_simp

/-! ## RUBI 4.1.1.1 #2: `∫ sin(c + d x / 2)^2 dx` -/

theorem rubi4111r2Nondeg_real : rubi4111r2Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi4111r2Nondeg.conditions rubi4111r2Nondeg.body
    rubi4111r2Nondeg.result
  intro env hc t _
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "d")) (.int 0)) (by simp [rubi4111r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  refine ⟨?_, ?_⟩
  · filter_upwards with w
    simp [rubi4111r2Nondeg, Defined, eval, Interp.real, ivm1R, hd]
  · have hfun : (fun w => eval Interp.real (Function.update env "x" w) rubi4111r2Nondeg.result) =
        fun w => w * 2⁻¹ + -Real.sin (2 * env "c" + env "d" * w) * (2 * env "d")⁻¹ := by
      funext w; simp [rubi4111r2Nondeg, eval, Interp.real, ivm1R]
    have hE : eval Interp.real (Function.update env "x" t) rubi4111r2Nondeg.body =
        Real.sin (env "c" + env "d" * t * 2⁻¹) ^ 2 := by
      simp [rubi4111r2Nondeg, eval, Interp.real, ivm1R, iv2R]
    rw [hfun, hE]
    refine (((hasDerivAt_id t).mul_const 2⁻¹).add
      (((Real.hasDerivAt_sin _).comp t (hasDerivAt_lin _ _ t)).neg.mul_const _)).congr_deriv ?_
    have h2 : 2 * env "c" + env "d" * t = 2 * (env "c" + env "d" * t * 2⁻¹) := by ring
    rw [h2, Real.cos_two_mul, Real.cos_sq']
    field_simp
    ring

theorem rubi4111r2Nondeg_complex : rubi4111r2Nondeg.Holds .complex := by
  show AntiderivHoldsUnder Interp.complex "x" rubi4111r2Nondeg.conditions rubi4111r2Nondeg.body
    rubi4111r2Nondeg.result
  intro env hc t _
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "d")) (.int 0)) (by simp [rubi4111r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  refine ⟨?_, ?_⟩
  · filter_upwards with w
    simp [rubi4111r2Nondeg, Defined, eval, Interp.complex, ivm1C, hd]
  · have hfun : (fun w => eval Interp.complex (Function.update env "x" w)
        rubi4111r2Nondeg.result) =
        fun w => w * 2⁻¹ + -Complex.sin (2 * env "c" + env "d" * w) * (2 * env "d")⁻¹ := by
      funext w; simp [rubi4111r2Nondeg, eval, Interp.complex, ivm1C]
    have hE : eval Interp.complex (Function.update env "x" t) rubi4111r2Nondeg.body =
        Complex.sin (env "c" + env "d" * t * 2⁻¹) ^ 2 := by
      simp [rubi4111r2Nondeg, eval, Interp.complex, ivm1C, iv2C]
    rw [hfun, hE]
    refine (((hasDerivAt_id t).mul_const 2⁻¹).add
      (((Complex.hasDerivAt_sin _).comp t (hasDerivAt_lin _ _ t)).neg.mul_const _)).congr_deriv ?_
    have h2 : 2 * env "c" + env "d" * t = 2 * (env "c" + env "d" * t * 2⁻¹) := by ring
    rw [h2, Complex.cos_two_mul, Complex.cos_sq']
    field_simp
    ring

/-! ## RUBI 6.1.1.3 #7 and #8: `∫ (d + e x) sinh(a + b x + c x^2) dx` and its cosh twin -/

theorem rubi6113r7Nondeg_real : rubi6113r7Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi6113r7Nondeg.conditions rubi6113r7Nondeg.body
    rubi6113r7Nondeg.result
  intro env hc t _
  have hcz : env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi6113r7Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" * env "e" + -1 * 2 * env "c" * env "d" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r7Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  refine ⟨?_, ?_⟩
  · filter_upwards with w
    simp [rubi6113r7Nondeg, Defined, eval, Interp.real, ivm1R, iv2R, hcz]
  · have hfun : (fun w => eval Interp.real (Function.update env "x" w) rubi6113r7Nondeg.result) =
        fun w => env "e" * Real.cosh (env "a" + env "b" * w + env "c" * w ^ 2) *
          (2 * env "c")⁻¹ := by
      funext w; simp [rubi6113r7Nondeg, eval, Interp.real, ivm1R, iv2R]
    have hE : eval Interp.real (Function.update env "x" t) rubi6113r7Nondeg.body =
        (env "d" + env "e" * t) * Real.sinh (env "a" + env "b" * t + env "c" * t ^ 2) := by
      simp [rubi6113r7Nondeg, eval, Interp.real, iv2R]
    rw [hfun, hE]
    refine ((((Real.hasDerivAt_cosh _).comp t (hasDerivAt_quad _ _ _ t)).const_mul
      (env "e")).mul_const _).congr_deriv ?_
    generalize Real.sinh (env "a" + env "b" * t + env "c" * t ^ 2) = S
    field_simp
    linear_combination S * hrel

theorem rubi6113r7Nondeg_complex : rubi6113r7Nondeg.Holds .complex := by
  show AntiderivHoldsUnder Interp.complex "x" rubi6113r7Nondeg.conditions rubi6113r7Nondeg.body
    rubi6113r7Nondeg.result
  intro env hc t _
  have hcz : env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi6113r7Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" * env "e" + -1 * 2 * env "c" * env "d" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r7Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  refine ⟨?_, ?_⟩
  · filter_upwards with w
    simp [rubi6113r7Nondeg, Defined, eval, Interp.complex, ivm1C, iv2C, hcz]
  · have hfun : (fun w => eval Interp.complex (Function.update env "x" w)
        rubi6113r7Nondeg.result) =
        fun w => env "e" * Complex.cosh (env "a" + env "b" * w + env "c" * w ^ 2) *
          (2 * env "c")⁻¹ := by
      funext w; simp [rubi6113r7Nondeg, eval, Interp.complex, ivm1C, iv2C]
    have hE : eval Interp.complex (Function.update env "x" t) rubi6113r7Nondeg.body =
        (env "d" + env "e" * t) * Complex.sinh (env "a" + env "b" * t + env "c" * t ^ 2) := by
      simp [rubi6113r7Nondeg, eval, Interp.complex, iv2C]
    rw [hfun, hE]
    refine ((((Complex.hasDerivAt_cosh _).comp t (hasDerivAt_quad _ _ _ t)).const_mul
      (env "e")).mul_const _).congr_deriv ?_
    generalize Complex.sinh (env "a" + env "b" * t + env "c" * t ^ 2) = S
    field_simp
    linear_combination S * hrel

theorem rubi6113r8Nondeg_real : rubi6113r8Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi6113r8Nondeg.conditions rubi6113r8Nondeg.body
    rubi6113r8Nondeg.result
  intro env hc t _
  have hcz : env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi6113r8Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" * env "e" + -1 * 2 * env "c" * env "d" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r8Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  refine ⟨?_, ?_⟩
  · filter_upwards with w
    simp [rubi6113r8Nondeg, Defined, eval, Interp.real, ivm1R, iv2R, hcz]
  · have hfun : (fun w => eval Interp.real (Function.update env "x" w) rubi6113r8Nondeg.result) =
        fun w => env "e" * Real.sinh (env "a" + env "b" * w + env "c" * w ^ 2) *
          (2 * env "c")⁻¹ := by
      funext w; simp [rubi6113r8Nondeg, eval, Interp.real, ivm1R, iv2R]
    have hE : eval Interp.real (Function.update env "x" t) rubi6113r8Nondeg.body =
        (env "d" + env "e" * t) * Real.cosh (env "a" + env "b" * t + env "c" * t ^ 2) := by
      simp [rubi6113r8Nondeg, eval, Interp.real, iv2R]
    rw [hfun, hE]
    refine ((((Real.hasDerivAt_sinh _).comp t (hasDerivAt_quad _ _ _ t)).const_mul
      (env "e")).mul_const _).congr_deriv ?_
    generalize Real.cosh (env "a" + env "b" * t + env "c" * t ^ 2) = S
    field_simp
    linear_combination S * hrel

theorem rubi6113r8Nondeg_complex : rubi6113r8Nondeg.Holds .complex := by
  show AntiderivHoldsUnder Interp.complex "x" rubi6113r8Nondeg.conditions rubi6113r8Nondeg.body
    rubi6113r8Nondeg.result
  intro env hc t _
  have hcz : env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi6113r8Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" * env "e" + -1 * 2 * env "c" * env "d" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r8Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  refine ⟨?_, ?_⟩
  · filter_upwards with w
    simp [rubi6113r8Nondeg, Defined, eval, Interp.complex, ivm1C, iv2C, hcz]
  · have hfun : (fun w => eval Interp.complex (Function.update env "x" w)
        rubi6113r8Nondeg.result) =
        fun w => env "e" * Complex.sinh (env "a" + env "b" * w + env "c" * w ^ 2) *
          (2 * env "c")⁻¹ := by
      funext w; simp [rubi6113r8Nondeg, eval, Interp.complex, ivm1C, iv2C]
    have hE : eval Interp.complex (Function.update env "x" t) rubi6113r8Nondeg.body =
        (env "d" + env "e" * t) * Complex.cosh (env "a" + env "b" * t + env "c" * t ^ 2) := by
      simp [rubi6113r8Nondeg, eval, Interp.complex, iv2C]
    rw [hfun, hE]
    refine ((((Complex.hasDerivAt_sinh _).comp t (hasDerivAt_quad _ _ _ t)).const_mul
      (env "e")).mul_const _).congr_deriv ?_
    generalize Complex.cosh (env "a" + env "b" * t + env "c" * t ^ 2) = S
    field_simp
    linear_combination S * hrel

end OSR.IntegrationRec210
