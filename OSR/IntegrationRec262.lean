import OSR.IntegrationNum1

/-! # Strengthened variants with explicit terms and residual integrals

Proofs of RUBI 4.3.3.1 #19 and 4.3.10 #17 over ℝ and ℂ: the result combines explicit terms in
`tan` and `(c + d x)` with one residual integral, and the integrand is recovered by `field_simp`
and `ring` once `tan' = (1 + tan²) f`. -/

namespace OSR.IntegrationRec262

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

/-! ## rubi4331r19Nondeg -/

theorem rubi4331r19Nondeg_real : rubi4331r19Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4331r19Nondeg.conditions rubi4331r19Nondeg.body
    rubi4331r19Nondeg.result rubi4331r19Nondeg.integrals
  intro env hc t hF
  have hdf := hc (.ne (.app2 .mul (.var "d") (.var "f")) (.int 0)) (by simp [rubi4331r19Nondeg])
  have hd : env "d" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hdf
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hdf
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4331r19Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧ env "c" + env "d" *
          Real.tan (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4331r19Nondeg, Defined, eval, Interp.real, ivm1R, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4331r19Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, ivm1R, iv2R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4331r19Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R] at h ⊢
    try tauto
  · simp only [rubi4331r19Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4331r19Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4331r19Nondeg.result) = fun w => env "b" ^ 2 * env "B" *
            Real.tan (env "e" + env "f" * w) * (env "d" * env "f")⁻¹ + (env "d")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4331r19Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hT := tan_deriv_R (env "e") (env "f") t h0.1
    refine (((hT.const_mul _).mul_const _).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi4331r19Nondeg, eval, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    obtain ⟨-, hD0⟩ := h0
    generalize Real.tan (env "e" + env "f" * t) = T at hD0 ⊢
    generalize hE : env "c" + env "d" * T = Dz at hD0 ⊢
    field_simp
    rw [← hE]
    ring


theorem rubi4331r19Nondeg_complex : rubi4331r19Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4331r19Nondeg.conditions rubi4331r19Nondeg.body
    rubi4331r19Nondeg.result rubi4331r19Nondeg.integrals
  intro env hc t hF
  have hdf := hc (.ne (.app2 .mul (.var "d") (.var "f")) (.int 0)) (by simp [rubi4331r19Nondeg])
  have hd : env "d" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hdf
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hdf
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4331r19Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧ env "c" + env "d" *
          Complex.tan (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4331r19Nondeg, Defined, eval, Interp.complex, ivm1C, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4331r19Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, ivm1C, iv2C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4331r19Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C] at h ⊢
    try tauto
  · simp only [rubi4331r19Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4331r19Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4331r19Nondeg.result) = fun w => env "b" ^ 2 * env "B" *
            Complex.tan (env "e" + env "f" * w) * (env "d" * env "f")⁻¹ + (env "d")⁻¹ * Φ "I1" w :=
            by
      funext w
      simp [rubi4331r19Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hT := tan_deriv_C (env "e") (env "f") t h0.1
    refine (((hT.const_mul _).mul_const _).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi4331r19Nondeg, eval, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    obtain ⟨-, hD0⟩ := h0
    generalize Complex.tan (env "e" + env "f" * t) = T at hD0 ⊢
    generalize hE : env "c" + env "d" * T = Dz at hD0 ⊢
    field_simp
    rw [← hE]
    ring


/-! ## rubi4310r17Nondeg -/

theorem rubi4310r17Nondeg_real : rubi4310r17Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4310r17Nondeg.conditions rubi4310r17Nondeg.body
    rubi4310r17Nondeg.result rubi4310r17Nondeg.integrals
  intro env hc t hF
  have hab : env "a" ^ 2 + env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0))
      (by simp [rubi4310r17Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hdab := hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.pow (.var "a")
    (.int 2)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4310r17Nondeg])
  have hd : env "d" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hdab
  have hfab := hc (.ne (.app2 .mul (.var "f") (.app2 .add (.pow (.var "a") (.int 2))
    (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4310r17Nondeg])
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hfab
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4310r17Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧ env "a" + env "b" *
          Real.tan (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4310r17Nondeg, Defined, eval, Interp.real, ivm1R, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4310r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, ivm1R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4310r17Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R] at h ⊢
    try tauto
  · simp only [rubi4310r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4310r17Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4310r17Nondeg.result) = fun w => -(env "c" + env "d" * w) ^ 2 *
            (2 * env "d" * (env "a" ^ 2 + env "b" ^ 2))⁻¹ + -(env "b") * (env "c" + env "d" * w) *
            (env "f" * (env "a" ^ 2 + env "b" ^ 2) *
            (env "a" + env "b" * Real.tan (env "e" + env "f" * w)))⁻¹ +
            (env "f" * (env "a" ^ 2 + env "b" ^ 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4310r17Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hT := tan_deriv_R (env "e") (env "f") t h0.1
    have hV := hasDerivAt_lin (env "c") (env "d") t
    have hA2 := (((hT.const_mul (env "b")).const_add (env "a")).const_mul
      (env "f" * (env "a" ^ 2 + env "b" ^ 2))).inv (mul_ne_zero (mul_ne_zero hf hab) h0.2)
    refine ((((hV.pow 2).neg.mul_const _).add ((hV.const_mul _).mul hA2)).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi4310r17Nondeg, eval, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    obtain ⟨-, hD0⟩ := h0
    generalize Real.tan (env "e" + env "f" * t) = T at hD0 ⊢
    generalize hE : env "a" + env "b" * T = Dz at hD0 ⊢
    field_simp
    rw [← hE]
    ring


theorem rubi4310r17Nondeg_complex : rubi4310r17Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4310r17Nondeg.conditions rubi4310r17Nondeg.body
    rubi4310r17Nondeg.result rubi4310r17Nondeg.integrals
  intro env hc t hF
  have hab : env "a" ^ 2 + env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0))
      (by simp [rubi4310r17Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  have hdab := hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.pow (.var "a")
    (.int 2)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4310r17Nondeg])
  have hd : env "d" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hdab
  have hfab := hc (.ne (.app2 .mul (.var "f") (.app2 .add (.pow (.var "a") (.int 2))
    (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4310r17Nondeg])
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hfab
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4310r17Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧ env "a" + env "b" *
          Complex.tan (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4310r17Nondeg, Defined, eval, Interp.complex, ivm1C, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4310r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, ivm1C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4310r17Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C] at h ⊢
    try tauto
  · simp only [rubi4310r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4310r17Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4310r17Nondeg.result) = fun w => -(env "c" + env "d" * w) ^ 2 *
            (2 * env "d" * (env "a" ^ 2 + env "b" ^ 2))⁻¹ + -(env "b") * (env "c" + env "d" * w) *
            (env "f" * (env "a" ^ 2 + env "b" ^ 2) *
            (env "a" + env "b" * Complex.tan (env "e" + env "f" * w)))⁻¹ +
            (env "f" * (env "a" ^ 2 + env "b" ^ 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4310r17Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hT := tan_deriv_C (env "e") (env "f") t h0.1
    have hV := hasDerivAt_lin (env "c") (env "d") t
    have hA2 := (((hT.const_mul (env "b")).const_add (env "a")).const_mul
      (env "f" * (env "a" ^ 2 + env "b" ^ 2))).inv (mul_ne_zero (mul_ne_zero hf hab) h0.2)
    refine ((((hV.pow 2).neg.mul_const _).add ((hV.const_mul _).mul hA2)).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi4310r17Nondeg, eval, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    obtain ⟨-, hD0⟩ := h0
    generalize Complex.tan (env "e" + env "f" * t) = T at hD0 ⊢
    generalize hE : env "a" + env "b" * T = Dz at hD0 ⊢
    field_simp
    rw [← hE]
    ring


end OSR.IntegrationRec262
