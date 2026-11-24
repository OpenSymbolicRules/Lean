import OSR.IntegrationNum1

open OSR OSR.Calculus Filter Topology
namespace OSR.IntegrationSinSquare

section
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem htwo (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)
private theorem hneg (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

variable [CharZero 𝕜]

theorem sinSquare_holds (I : Interp 𝕜)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u)
    (hc : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u)
    (hsc : ∀ u : 𝕜, I.sin u ^ 2 + I.cos u ^ 2 = 1) :
    AntiderivHoldsUnder I "x" IntegrationNum1.rubi4111r11Nondeg.conditions
      IntegrationNum1.rubi4111r11Nondeg.body IntegrationNum1.rubi4111r11Nondeg.result := by
  intro env hcond t _hF
  have hd : env "d" ≠ 0 := by
    have h := hcond (.ne (.var "d") (.int 0)) (by simp [IntegrationNum1.rubi4111r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  constructor
  · filter_upwards with w
    simp [IntegrationNum1.rubi4111r11Nondeg, Defined, eval, htwo, hneg, hd, (show (2 : 𝕜) ≠ 0 by norm_num)]
  · have hU : HasDerivAt (fun w : 𝕜 => env "c" + env "d" * w) (env "d") t := by
      simpa using (((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c"))
    have hS := (hs _).comp t hU
    have hC := (hc _).comp t hU
    have hfun : (fun w => eval I (Function.update env "x" w) IntegrationNum1.rubi4111r11Nondeg.result) =
        (fun w : 𝕜 => ((2 * env "a" ^ 2 + env "b" ^ 2) * (2 : 𝕜)⁻¹) * w +
          (-2 * env "a" * env "b" * (env "d")⁻¹) * I.cos (env "c" + env "d" * w) +
          (-env "b" ^ 2 * (2 * env "d")⁻¹) * (I.cos (env "c" + env "d" * w) * I.sin (env "c" + env "d" * w))) := by
      funext w
      simp [IntegrationNum1.rubi4111r11Nondeg, eval, htwo, hneg, Function.update, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      ring
    rw [hfun]
    have hresult := (((hasDerivAt_id' t).const_mul ((2 * env "a" ^ 2 + env "b" ^ 2) * (2 : 𝕜)⁻¹)).add
      (hC.const_mul (-2 * env "a" * env "b" * (env "d")⁻¹))).add
      ((hC.mul hS).const_mul (-env "b" ^ 2 * (2 * env "d")⁻¹))
    refine hresult.congr_deriv ?_
    simp [IntegrationNum1.rubi4111r11Nondeg, eval, htwo, Function.update]
    have ht := hsc (env "c" + env "d" * t)
    field_simp [hd]
    linear_combination -(env "b") ^ 2 * ht

omit [CharZero 𝕜] in
/-- The strengthened sine primitive holds under its original nonzero guard. -/
theorem sinLinear_holds (I : Interp 𝕜)
    (hc : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivHoldsUnder I "x" IntegrationNum1.rubi4111r6Nondeg.conditions
      IntegrationNum1.rubi4111r6Nondeg.body IntegrationNum1.rubi4111r6Nondeg.result := by
  intro env hcond t _hF
  have hd : env "d" ≠ 0 := by
    have h := hcond (.ne (.var "d") (.int 0)) (by simp [IntegrationNum1.rubi4111r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  constructor
  · filter_upwards with w
    simp [IntegrationNum1.rubi4111r6Nondeg, Defined, eval, hneg, hd]
  · have hU : HasDerivAt (fun w : 𝕜 => env "c" + env "d" * w) (env "d") t := by
      simpa using (((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c"))
    have hC := (hc _).comp t hU
    have hfun : (fun w => eval I (Function.update env "x" w) IntegrationNum1.rubi4111r6Nondeg.result) =
        (fun w : 𝕜 => (-I.cos (env "c" + env "d" * w)) * (env "d")⁻¹) := by
      funext w
      simp [IntegrationNum1.rubi4111r6Nondeg, eval, hneg, Function.update]
    rw [hfun]
    refine (hC.neg.mul_const _).congr_deriv ?_
    simp [IntegrationNum1.rubi4111r6Nondeg, eval, Function.update]
    field_simp

end

theorem sinSquare_real : IntegrationNum1.rubi4111r11Nondeg.Holds .real :=
  sinSquare_holds Interp.real Real.hasDerivAt_sin Real.hasDerivAt_cos Real.sin_sq_add_cos_sq

theorem sinSquare_complex : IntegrationNum1.rubi4111r11Nondeg.Holds .complex :=
  sinSquare_holds Interp.complex Complex.hasDerivAt_sin Complex.hasDerivAt_cos Complex.sin_sq_add_cos_sq

theorem sinLinear_real : IntegrationNum1.rubi4111r6Nondeg.Holds .real :=
  sinLinear_holds Interp.real Real.hasDerivAt_cos

theorem sinLinear_complex : IntegrationNum1.rubi4111r6Nondeg.Holds .complex :=
  sinLinear_holds Interp.complex Complex.hasDerivAt_cos

end OSR.IntegrationSinSquare
