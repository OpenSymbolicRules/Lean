import OSR.IntegrationNum1

/-! # Strengthened variants with explicit terms and residual integrals

Proofs of RUBI 4.7.9 #76, #77, 6.7.9 #78, #79, 4.5.4.1 #8, #9, 6.7.8 #47, #48 and 6.3.12 #3:
the result combines an explicit term with one residual integral; the integrand is recovered
with `sin² + cos² = 1` (or `cosh² - sinh² = 1`) and the stated parameter relation. Rules with
`csc` or `ln` are proved over ℝ only (the principal complex logarithm is not differentiable across
the negative real axis). -/

namespace OSR.IntegrationRec261

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem hasDerivAt_lin {𝕜 : Type} [NontriviallyNormedField 𝕜] (a b t : 𝕜) :
    HasDerivAt (fun w => a + b * w) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

private theorem hasDerivAt_quad {𝕜 : Type} [NontriviallyNormedField 𝕜] (a b c t : 𝕜) :
    HasDerivAt (fun w => a + b * w + c * w ^ 2) (b + 2 * c * t) t := by
  have := (hasDerivAt_lin a b t).add ((hasDerivAt_pow 2 t).const_mul c)
  convert this using 1
  push_cast
  ring

private theorem tan_deriv_R (e f t : ℝ) (h : Real.cos (e + f * t) ≠ 0) :
    HasDerivAt (fun w => Real.tan (e + f * w)) ((1 + Real.tan (e + f * t) ^ 2) * f) t := by
  refine ((Real.hasDerivAt_tan h).comp t (hasDerivAt_lin e f t)).congr_deriv ?_
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  first
  | linear_combination f * Real.sin_sq_add_cos_sq (e + f * t)
  | linear_combination (-f) * Real.sin_sq_add_cos_sq (e + f * t)

private theorem tan_deriv_C (e f t : ℂ) (h : Complex.cos (e + f * t) ≠ 0) :
    HasDerivAt (fun w => Complex.tan (e + f * w)) ((1 + Complex.tan (e + f * t) ^ 2) * f) t := by
  refine ((Complex.hasDerivAt_tan h).comp t (hasDerivAt_lin e f t)).congr_deriv ?_
  rw [Complex.tan_eq_sin_div_cos]
  field_simp
  first
  | linear_combination f * Complex.sin_sq_add_cos_sq (e + f * t)
  | linear_combination (-f) * Complex.sin_sq_add_cos_sq (e + f * t)

/-! ## rubi479r76Nondeg -/

theorem rubi479r76Nondeg_real : rubi479r76Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r76Nondeg.conditions rubi479r76Nondeg.body
    rubi479r76Nondeg.result rubi479r76Nondeg.integrals
  intro env hc t hF
  have had := hc (.ne (.app2 .mul (.var "a") (.var "d")) (.int 0)) (by simp [rubi479r76Nondeg])
  have ha : env "a" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at had
  have hd : env "d" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at had
  have hrel : env "a" * env "A" - env "b" * env "B" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B"))) (.int 0)) (by simp [rubi479r76Nondeg])
    simpa [Cond.Holds, Defined, eval, sub_eq_add_neg] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi479r76Nondeg.body →
      env "a" + env "b" * Real.sin (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi479r76Nondeg, Defined, eval, Interp.real, ivm1R, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r76Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, ivm1R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi479r76Nondeg, Defined, eval, recEnv, Interp.real, ivm1R] at h ⊢
    try tauto
  · simp only [rubi479r76Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi479r76Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi479r76Nondeg.result) = fun w => -(env "B") * (env "e" + env "f" * w) *
            Real.cos (env "c" + env "d" * w) *
            ((env "a")⁻¹ * (env "d")⁻¹ *
            (env "a" + env "b" * Real.sin (env "c" + env "d" * w))⁻¹) + env "B" * env "f" *
            ((env "a")⁻¹ * (env "d")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi479r76Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hU := hasDerivAt_lin (env "e") (env "f") t
    have hZ := (Real.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "c") (env "d") t)
    have hY :=
        (((Real.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "c") (env "d") t)).const_mul (env "b")).const_add (env "a")
    have hYi := hY.inv h0
    refine ((((hU.const_mul _).mul hZ).mul (hYi.const_mul _)).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi479r76Nondeg, eval, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hP := Real.sin_sq_add_cos_sq (env "c" + env "d" * t)
    generalize hE : env "a" + env "b" * Real.sin (env "c" + env "d" * t) = Dz at h0 ⊢
    field_simp
    rw [← hE]
    generalize Real.sin (env "c" + env "d" * t) = S at hP ⊢
    generalize Real.cos (env "c" + env "d" * t) = C at hP ⊢
    linear_combination (env "B"*env "b"*env "d"*env "e" + env "B"*env "b"*env "d"*env "f"*t) * hP +
        (-env "d"*env "e" - env "d"*env "f"*t) * hrel


theorem rubi479r76Nondeg_complex : rubi479r76Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi479r76Nondeg.conditions rubi479r76Nondeg.body
    rubi479r76Nondeg.result rubi479r76Nondeg.integrals
  intro env hc t hF
  have had := hc (.ne (.app2 .mul (.var "a") (.var "d")) (.int 0)) (by simp [rubi479r76Nondeg])
  have ha : env "a" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at had
  have hd : env "d" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at had
  have hrel : env "a" * env "A" - env "b" * env "B" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B"))) (.int 0)) (by simp [rubi479r76Nondeg])
    simpa [Cond.Holds, Defined, eval, sub_eq_add_neg] using h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi479r76Nondeg.body →
      env "a" + env "b" * Complex.sin (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi479r76Nondeg, Defined, eval, Interp.complex, ivm1C, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r76Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, ivm1C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi479r76Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C] at h ⊢
    try tauto
  · simp only [rubi479r76Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi479r76Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi479r76Nondeg.result) = fun w => -(env "B") * (env "e" + env "f" * w) *
            Complex.cos (env "c" + env "d" * w) *
            ((env "a")⁻¹ * (env "d")⁻¹ *
            (env "a" + env "b" * Complex.sin (env "c" + env "d" * w))⁻¹) + env "B" * env "f" *
            ((env "a")⁻¹ * (env "d")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi479r76Nondeg, eval, recEnv, Interp.complex, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hU := hasDerivAt_lin (env "e") (env "f") t
    have hZ := (Complex.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "c") (env "d") t)
    have hY :=
        (((Complex.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "c") (env "d") t)).const_mul (env "b")).const_add (env "a")
    have hYi := hY.inv h0
    refine ((((hU.const_mul _).mul hZ).mul (hYi.const_mul _)).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi479r76Nondeg, eval, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hP := Complex.sin_sq_add_cos_sq (env "c" + env "d" * t)
    generalize hE : env "a" + env "b" * Complex.sin (env "c" + env "d" * t) = Dz at h0 ⊢
    field_simp
    rw [← hE]
    generalize Complex.sin (env "c" + env "d" * t) = S at hP ⊢
    generalize Complex.cos (env "c" + env "d" * t) = C at hP ⊢
    linear_combination (env "B"*env "b"*env "d"*env "e" + env "B"*env "b"*env "d"*env "f"*t) * hP +
        (-env "d"*env "e" - env "d"*env "f"*t) * hrel


/-! ## rubi479r77Nondeg -/

theorem rubi479r77Nondeg_real : rubi479r77Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r77Nondeg.conditions rubi479r77Nondeg.body
    rubi479r77Nondeg.result rubi479r77Nondeg.integrals
  intro env hc t hF
  have had := hc (.ne (.app2 .mul (.var "a") (.var "d")) (.int 0)) (by simp [rubi479r77Nondeg])
  have ha : env "a" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at had
  have hd : env "d" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at had
  have hrel : env "a" * env "A" - env "b" * env "B" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B"))) (.int 0)) (by simp [rubi479r77Nondeg])
    simpa [Cond.Holds, Defined, eval, sub_eq_add_neg] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi479r77Nondeg.body →
      env "a" + env "b" * Real.cos (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi479r77Nondeg, Defined, eval, Interp.real, ivm1R, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r77Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, ivm1R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi479r77Nondeg, Defined, eval, recEnv, Interp.real, ivm1R] at h ⊢
    try tauto
  · simp only [rubi479r77Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi479r77Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi479r77Nondeg.result) = fun w => env "B" * (env "e" + env "f" * w) *
            Real.sin (env "c" + env "d" * w) *
            ((env "a")⁻¹ * (env "d")⁻¹ *
            (env "a" + env "b" * Real.cos (env "c" + env "d" * w))⁻¹) + -(env "B") * env "f" *
            ((env "a")⁻¹ * (env "d")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi479r77Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hU := hasDerivAt_lin (env "e") (env "f") t
    have hZ := (Real.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "c") (env "d") t)
    have hY :=
        (((Real.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "c") (env "d") t)).const_mul (env "b")).const_add (env "a")
    have hYi := hY.inv h0
    refine ((((hU.const_mul _).mul hZ).mul (hYi.const_mul _)).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi479r77Nondeg, eval, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hP := Real.sin_sq_add_cos_sq (env "c" + env "d" * t)
    generalize hE : env "a" + env "b" * Real.cos (env "c" + env "d" * t) = Dz at h0 ⊢
    field_simp
    rw [← hE]
    generalize Real.sin (env "c" + env "d" * t) = S at hP ⊢
    generalize Real.cos (env "c" + env "d" * t) = C at hP ⊢
    linear_combination (env "B"*env "b"*env "d"*env "e" + env "B"*env "b"*env "d"*env "f"*t) * hP +
        (-env "d"*env "e" - env "d"*env "f"*t) * hrel


theorem rubi479r77Nondeg_complex : rubi479r77Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi479r77Nondeg.conditions rubi479r77Nondeg.body
    rubi479r77Nondeg.result rubi479r77Nondeg.integrals
  intro env hc t hF
  have had := hc (.ne (.app2 .mul (.var "a") (.var "d")) (.int 0)) (by simp [rubi479r77Nondeg])
  have ha : env "a" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at had
  have hd : env "d" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at had
  have hrel : env "a" * env "A" - env "b" * env "B" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B"))) (.int 0)) (by simp [rubi479r77Nondeg])
    simpa [Cond.Holds, Defined, eval, sub_eq_add_neg] using h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi479r77Nondeg.body →
      env "a" + env "b" * Complex.cos (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi479r77Nondeg, Defined, eval, Interp.complex, ivm1C, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r77Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, ivm1C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi479r77Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C] at h ⊢
    try tauto
  · simp only [rubi479r77Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi479r77Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi479r77Nondeg.result) = fun w => env "B" * (env "e" + env "f" * w) *
            Complex.sin (env "c" + env "d" * w) *
            ((env "a")⁻¹ * (env "d")⁻¹ *
            (env "a" + env "b" * Complex.cos (env "c" + env "d" * w))⁻¹) + -(env "B") * env "f" *
            ((env "a")⁻¹ * (env "d")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi479r77Nondeg, eval, recEnv, Interp.complex, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hU := hasDerivAt_lin (env "e") (env "f") t
    have hZ := (Complex.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "c") (env "d") t)
    have hY :=
        (((Complex.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "c") (env "d") t)).const_mul (env "b")).const_add (env "a")
    have hYi := hY.inv h0
    refine ((((hU.const_mul _).mul hZ).mul (hYi.const_mul _)).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi479r77Nondeg, eval, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hP := Complex.sin_sq_add_cos_sq (env "c" + env "d" * t)
    generalize hE : env "a" + env "b" * Complex.cos (env "c" + env "d" * t) = Dz at h0 ⊢
    field_simp
    rw [← hE]
    generalize Complex.sin (env "c" + env "d" * t) = S at hP ⊢
    generalize Complex.cos (env "c" + env "d" * t) = C at hP ⊢
    linear_combination (env "B"*env "b"*env "d"*env "e" + env "B"*env "b"*env "d"*env "f"*t) * hP +
        (-env "d"*env "e" - env "d"*env "f"*t) * hrel


/-! ## rubi679r78Nondeg -/

theorem rubi679r78Nondeg_real : rubi679r78Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r78Nondeg.conditions rubi679r78Nondeg.body
    rubi679r78Nondeg.result rubi679r78Nondeg.integrals
  intro env hc t hF
  have had := hc (.ne (.app2 .mul (.var "a") (.var "d")) (.int 0)) (by simp [rubi679r78Nondeg])
  have ha : env "a" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at had
  have hd : env "d" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at had
  have hrel : env "a" * env "A" + env "b" * env "B" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.var "b") (.var "B"))) (.int 0)) (by simp [rubi679r78Nondeg])
    simpa [Cond.Holds, Defined, eval, sub_eq_add_neg] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r78Nondeg.body →
      env "a" + env "b" * Real.sinh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r78Nondeg, Defined, eval, Interp.real, ivm1R, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r78Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, ivm1R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi679r78Nondeg, Defined, eval, recEnv, Interp.real, ivm1R] at h ⊢
    try tauto
  · simp only [rubi679r78Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r78Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r78Nondeg.result) = fun w => env "B" * (env "e" + env "f" * w) *
            Real.cosh (env "c" + env "d" * w) *
            ((env "a")⁻¹ * (env "d")⁻¹ *
            (env "a" + env "b" * Real.sinh (env "c" + env "d" * w))⁻¹) + -(env "B") * env "f" *
            ((env "a")⁻¹ * (env "d")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi679r78Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hU := hasDerivAt_lin (env "e") (env "f") t
    have hZ := (Real.hasDerivAt_cosh _).comp t (hasDerivAt_lin (env "c") (env "d") t)
    have hY :=
        (((Real.hasDerivAt_sinh _).comp t (hasDerivAt_lin (env "c") (env "d") t)).const_mul (env "b")).const_add (env "a")
    have hYi := hY.inv h0
    refine ((((hU.const_mul _).mul hZ).mul (hYi.const_mul _)).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi679r78Nondeg, eval, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hP := Real.cosh_sq_sub_sinh_sq (env "c" + env "d" * t)
    generalize hE : env "a" + env "b" * Real.sinh (env "c" + env "d" * t) = Dz at h0 ⊢
    field_simp
    rw [← hE]
    generalize Real.sinh (env "c" + env "d" * t) = S at hP ⊢
    generalize Real.cosh (env "c" + env "d" * t) = C at hP ⊢
    linear_combination (-env "B"*env "b"*env "d"*env "e" - env "B"*env "b"*env "d"*env "f"*t) *
        hP + (-env "d"*env "e" - env "d"*env "f"*t) * hrel


theorem rubi679r78Nondeg_complex : rubi679r78Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi679r78Nondeg.conditions rubi679r78Nondeg.body
    rubi679r78Nondeg.result rubi679r78Nondeg.integrals
  intro env hc t hF
  have had := hc (.ne (.app2 .mul (.var "a") (.var "d")) (.int 0)) (by simp [rubi679r78Nondeg])
  have ha : env "a" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at had
  have hd : env "d" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at had
  have hrel : env "a" * env "A" + env "b" * env "B" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.var "b") (.var "B"))) (.int 0)) (by simp [rubi679r78Nondeg])
    simpa [Cond.Holds, Defined, eval, sub_eq_add_neg] using h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi679r78Nondeg.body →
      env "a" + env "b" * Complex.sinh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r78Nondeg, Defined, eval, Interp.complex, ivm1C, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r78Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, ivm1C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi679r78Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C] at h ⊢
    try tauto
  · simp only [rubi679r78Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi679r78Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r78Nondeg.result) = fun w => env "B" * (env "e" + env "f" * w) *
            Complex.cosh (env "c" + env "d" * w) *
            ((env "a")⁻¹ * (env "d")⁻¹ *
            (env "a" + env "b" * Complex.sinh (env "c" + env "d" * w))⁻¹) + -(env "B") * env "f" *
            ((env "a")⁻¹ * (env "d")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi679r78Nondeg, eval, recEnv, Interp.complex, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hU := hasDerivAt_lin (env "e") (env "f") t
    have hZ := (Complex.hasDerivAt_cosh _).comp t (hasDerivAt_lin (env "c") (env "d") t)
    have hY :=
        (((Complex.hasDerivAt_sinh _).comp t (hasDerivAt_lin (env "c") (env "d") t)).const_mul (env "b")).const_add (env "a")
    have hYi := hY.inv h0
    refine ((((hU.const_mul _).mul hZ).mul (hYi.const_mul _)).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi679r78Nondeg, eval, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hP := Complex.cosh_sq_sub_sinh_sq (env "c" + env "d" * t)
    generalize hE : env "a" + env "b" * Complex.sinh (env "c" + env "d" * t) = Dz at h0 ⊢
    field_simp
    rw [← hE]
    generalize Complex.sinh (env "c" + env "d" * t) = S at hP ⊢
    generalize Complex.cosh (env "c" + env "d" * t) = C at hP ⊢
    linear_combination (-env "B"*env "b"*env "d"*env "e" - env "B"*env "b"*env "d"*env "f"*t) *
        hP + (-env "d"*env "e" - env "d"*env "f"*t) * hrel


/-! ## rubi679r79Nondeg -/

theorem rubi679r79Nondeg_real : rubi679r79Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r79Nondeg.conditions rubi679r79Nondeg.body
    rubi679r79Nondeg.result rubi679r79Nondeg.integrals
  intro env hc t hF
  have had := hc (.ne (.app2 .mul (.var "a") (.var "d")) (.int 0)) (by simp [rubi679r79Nondeg])
  have ha : env "a" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at had
  have hd : env "d" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at had
  have hrel : env "a" * env "A" - env "b" * env "B" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B"))) (.int 0)) (by simp [rubi679r79Nondeg])
    simpa [Cond.Holds, Defined, eval, sub_eq_add_neg] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r79Nondeg.body →
      env "a" + env "b" * Real.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r79Nondeg, Defined, eval, Interp.real, ivm1R, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r79Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, ivm1R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi679r79Nondeg, Defined, eval, recEnv, Interp.real, ivm1R] at h ⊢
    try tauto
  · simp only [rubi679r79Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r79Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r79Nondeg.result) = fun w => env "B" * (env "e" + env "f" * w) *
            Real.sinh (env "c" + env "d" * w) *
            ((env "a")⁻¹ * (env "d")⁻¹ *
            (env "a" + env "b" * Real.cosh (env "c" + env "d" * w))⁻¹) + -(env "B") * env "f" *
            ((env "a")⁻¹ * (env "d")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi679r79Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hU := hasDerivAt_lin (env "e") (env "f") t
    have hZ := (Real.hasDerivAt_sinh _).comp t (hasDerivAt_lin (env "c") (env "d") t)
    have hY :=
        (((Real.hasDerivAt_cosh _).comp t (hasDerivAt_lin (env "c") (env "d") t)).const_mul (env "b")).const_add (env "a")
    have hYi := hY.inv h0
    refine ((((hU.const_mul _).mul hZ).mul (hYi.const_mul _)).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi679r79Nondeg, eval, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hP := Real.cosh_sq_sub_sinh_sq (env "c" + env "d" * t)
    generalize hE : env "a" + env "b" * Real.cosh (env "c" + env "d" * t) = Dz at h0 ⊢
    field_simp
    rw [← hE]
    generalize Real.sinh (env "c" + env "d" * t) = S at hP ⊢
    generalize Real.cosh (env "c" + env "d" * t) = C at hP ⊢
    linear_combination (env "B"*env "b"*env "d"*env "e" + env "B"*env "b"*env "d"*env "f"*t) * hP +
        (-env "d"*env "e" - env "d"*env "f"*t) * hrel


theorem rubi679r79Nondeg_complex : rubi679r79Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi679r79Nondeg.conditions rubi679r79Nondeg.body
    rubi679r79Nondeg.result rubi679r79Nondeg.integrals
  intro env hc t hF
  have had := hc (.ne (.app2 .mul (.var "a") (.var "d")) (.int 0)) (by simp [rubi679r79Nondeg])
  have ha : env "a" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at had
  have hd : env "d" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at had
  have hrel : env "a" * env "A" - env "b" * env "B" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B"))) (.int 0)) (by simp [rubi679r79Nondeg])
    simpa [Cond.Holds, Defined, eval, sub_eq_add_neg] using h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi679r79Nondeg.body →
      env "a" + env "b" * Complex.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r79Nondeg, Defined, eval, Interp.complex, ivm1C, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r79Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, ivm1C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi679r79Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C] at h ⊢
    try tauto
  · simp only [rubi679r79Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi679r79Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r79Nondeg.result) = fun w => env "B" * (env "e" + env "f" * w) *
            Complex.sinh (env "c" + env "d" * w) *
            ((env "a")⁻¹ * (env "d")⁻¹ *
            (env "a" + env "b" * Complex.cosh (env "c" + env "d" * w))⁻¹) + -(env "B") * env "f" *
            ((env "a")⁻¹ * (env "d")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi679r79Nondeg, eval, recEnv, Interp.complex, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hU := hasDerivAt_lin (env "e") (env "f") t
    have hZ := (Complex.hasDerivAt_sinh _).comp t (hasDerivAt_lin (env "c") (env "d") t)
    have hY :=
        (((Complex.hasDerivAt_cosh _).comp t (hasDerivAt_lin (env "c") (env "d") t)).const_mul (env "b")).const_add (env "a")
    have hYi := hY.inv h0
    refine ((((hU.const_mul _).mul hZ).mul (hYi.const_mul _)).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi679r79Nondeg, eval, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hP := Complex.cosh_sq_sub_sinh_sq (env "c" + env "d" * t)
    generalize hE : env "a" + env "b" * Complex.cosh (env "c" + env "d" * t) = Dz at h0 ⊢
    field_simp
    rw [← hE]
    generalize Complex.sinh (env "c" + env "d" * t) = S at hP ⊢
    generalize Complex.cosh (env "c" + env "d" * t) = C at hP ⊢
    linear_combination (env "B"*env "b"*env "d"*env "e" + env "B"*env "b"*env "d"*env "f"*t) * hP +
        (-env "d"*env "e" - env "d"*env "f"*t) * hrel


/-! ## rubi4541r9Nondeg -/

theorem rubi4541r9Nondeg_real : rubi4541r9Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4541r9Nondeg.conditions rubi4541r9Nondeg.body
    rubi4541r9Nondeg.result rubi4541r9Nondeg.integrals
  intro env hc t hF
  have hf : env "f" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "f")) (.int 0)) (by simp [rubi4541r9Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4541r9Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4541r9Nondeg, Defined, eval, Interp.real, iv2R, Fn.csc] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4541r9Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, iv2R, Fn.csc] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4541r9Nondeg, Defined, eval, recEnv, Interp.real, ivm1R] at h ⊢
    try tauto
  · simp only [rubi4541r9Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4541r9Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4541r9Nondeg.result) = fun w => -(env "b") * env "C" *
            (Real.sin (env "e" + env "f" * w))⁻¹ *
            (Real.cos (env "e" + env "f" * w) / Real.sin (env "e" + env "f" * w)) *
            (2 * env "f")⁻¹ + 2⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4541r9Nondeg, eval, recEnv, Interp.real, ivm1R, Fn.csc, Real.cot_eq_cos_div_sin,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hS := (Real.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hC := (Real.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hSi := hS.inv h0
    have hCot := hC.div hS h0
    refine ((((hSi.const_mul _).mul hCot).mul_const _).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi4541r9Nondeg, eval, Interp.real, iv2R, Fn.csc, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize Real.sin (env "e" + env "f" * t) = S at hP h0 ⊢
    generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (2*env "C"*env "b") * hP


/-! ## rubi4541r8Nondeg -/

theorem rubi4541r8Nondeg_real : rubi4541r8Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4541r8Nondeg.conditions rubi4541r8Nondeg.body
    rubi4541r8Nondeg.result rubi4541r8Nondeg.integrals
  intro env hc t hF
  have hf : env "f" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "f")) (.int 0)) (by simp [rubi4541r8Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4541r8Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4541r8Nondeg, Defined, eval, Interp.real, iv2R, Fn.csc] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4541r8Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, iv2R, Fn.csc] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4541r8Nondeg, Defined, eval, recEnv, Interp.real, ivm1R] at h ⊢
    try tauto
  · simp only [rubi4541r8Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4541r8Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4541r8Nondeg.result) = fun w => -(env "b") * env "C" *
            (Real.sin (env "e" + env "f" * w))⁻¹ *
            (Real.cos (env "e" + env "f" * w) / Real.sin (env "e" + env "f" * w)) *
            (2 * env "f")⁻¹ + 2⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4541r8Nondeg, eval, recEnv, Interp.real, ivm1R, Fn.csc, Real.cot_eq_cos_div_sin,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hS := (Real.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hC := (Real.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hSi := hS.inv h0
    have hCot := hC.div hS h0
    refine ((((hSi.const_mul _).mul hCot).mul_const _).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi4541r8Nondeg, eval, Interp.real, iv2R, Fn.csc, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize Real.sin (env "e" + env "f" * t) = S at hP h0 ⊢
    generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (2*env "C"*env "b") * hP


/-! ## rubi678r47Nondeg -/

theorem rubi678r47Nondeg_real : rubi678r47Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi678r47Nondeg.conditions rubi678r47Nondeg.body
    rubi678r47Nondeg.result rubi678r47Nondeg.integrals
  intro env hc t hF
  have ha : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi678r47Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi678r47Nondeg.body →
      0 < env "b" * w := by
    intro w h
    simp [rubi678r47Nondeg, Defined, eval, Interp.real] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi678r47Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi678r47Nondeg, Defined, eval, recEnv, Interp.real, ivm1R] at h ⊢
    try tauto
  · simp only [rubi678r47Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi678r47Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi678r47Nondeg.result) =
            fun w => Real.cosh (env "a" * w * Real.log (env "b" * w)) * (env "a")⁻¹ + -Φ "I1" w :=
            by
      funext w
      simp [rubi678r47Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hL := ((hasDerivAt_id' t).const_mul (env "b")).log h0.ne'
    have hG := ((hasDerivAt_id' t).const_mul (env "a")).mul hL
    have hX := (Real.hasDerivAt_cosh _).comp t hG
    refine ((hX.mul_const _).add hΦ1.neg).congr_deriv ?_
    simp [rubi678r47Nondeg, eval, Interp.real, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hb : env "b" ≠ 0 := (mul_ne_zero_iff.mp h0.ne').1
    have ht : t ≠ 0 := (mul_ne_zero_iff.mp h0.ne').2
    field_simp
    ring


/-! ## rubi678r48Nondeg -/

theorem rubi678r48Nondeg_real : rubi678r48Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi678r48Nondeg.conditions rubi678r48Nondeg.body
    rubi678r48Nondeg.result rubi678r48Nondeg.integrals
  intro env hc t hF
  have ha : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi678r48Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi678r48Nondeg.body →
      0 < env "b" * w := by
    intro w h
    simp [rubi678r48Nondeg, Defined, eval, Interp.real] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi678r48Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi678r48Nondeg, Defined, eval, recEnv, Interp.real, ivm1R] at h ⊢
    try tauto
  · simp only [rubi678r48Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi678r48Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi678r48Nondeg.result) =
            fun w => Real.sinh (env "a" * w * Real.log (env "b" * w)) * (env "a")⁻¹ + -Φ "I1" w :=
            by
      funext w
      simp [rubi678r48Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hL := ((hasDerivAt_id' t).const_mul (env "b")).log h0.ne'
    have hG := ((hasDerivAt_id' t).const_mul (env "a")).mul hL
    have hX := (Real.hasDerivAt_sinh _).comp t hG
    refine ((hX.mul_const _).add hΦ1.neg).congr_deriv ?_
    simp [rubi678r48Nondeg, eval, Interp.real, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hb : env "b" ≠ 0 := (mul_ne_zero_iff.mp h0.ne').1
    have ht : t ≠ 0 := (mul_ne_zero_iff.mp h0.ne').2
    field_simp
    ring


/-! ## rubi6312r3Nondeg -/

theorem rubi6312r3Nondeg_real : rubi6312r3Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6312r3Nondeg.conditions rubi6312r3Nondeg.body
    rubi6312r3Nondeg.result rubi6312r3Nondeg.integrals
  intro env hc t hF
  have hc0 : env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi6312r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi6312r3Nondeg.body →
      True := by
    intro w h
    trivial
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6312r3Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, iv2R] at h ⊢
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6312r3Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, Real.cosh_pos,
        hc0] at h ⊢
  · simp only [rubi6312r3Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi6312r3Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6312r3Nondeg.result) = fun w => env "e" *
            Real.log (Real.cosh (env "a" + env "b" * w + env "c" * w ^ 2)) * (2 * env "c")⁻¹ +
            (2 * env "c" * env "d" - env "b" * env "e") * (2 * env "c")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi6312r3Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hX := ((Real.hasDerivAt_cosh _).comp t (hasDerivAt_quad (env "a") (env "b") (env "c")
      t)).log (Real.cosh_pos _).ne'
    have hch := (Real.cosh_pos (env "a" + env "b" * t + env "c" * t ^ 2)).ne'
    refine (((hX.const_mul _).mul_const _).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi6312r3Nondeg, eval, Interp.real, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    simp only [Real.tanh_eq_sinh_div_cosh]
    field_simp
    ring


end OSR.IntegrationRec261
