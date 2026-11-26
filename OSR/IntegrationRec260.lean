import OSR.IntegrationNum1

/-! # Strengthened variants with explicit terms and residual integrals

Proofs of RUBI 4.1.2.1 #2, #13, 4.3.2.1 #4, #19, 4.3.3.1 #2, 4.5.2.1 #17 and 6.1.13 #9, #10:
the result combines an explicit term (`x`, `cos`, `tan`, `cosh`, `sinh`) with residual integrals,
and the integrand is recovered by `field_simp` and `ring` once `tan' = (1 + tan²) f`. Rules with
`csc` are proved over ℝ only. -/

namespace OSR.IntegrationRec260

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

/-! ## rubi4321r4Nondeg -/

theorem rubi4321r4Nondeg_real : rubi4321r4Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4321r4Nondeg.conditions rubi4321r4Nondeg.body
    rubi4321r4Nondeg.result rubi4321r4Nondeg.integrals
  intro env hc t hF
  have hf : env "f" ≠ 0 := by
    have h := hc (.ne (.var "f") (.int 0)) (by simp [rubi4321r4Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4321r4Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4321r4Nondeg, Defined, eval, Interp.real] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4321r4Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4321r4Nondeg, Defined, eval, recEnv, Interp.real, ivm1R] at h ⊢
    try tauto
  · simp only [rubi4321r4Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4321r4Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4321r4Nondeg.result) = fun w => (env "a" * env "c" - env "b" * env "d") * w +
            env "b" * env "d" * Real.tan (env "e" + env "f" * w) * (env "f")⁻¹ +
            (env "b" * env "c" + env "a" * env "d") * Φ "I1" w := by
      funext w
      simp [rubi4321r4Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hT := tan_deriv_R (env "e") (env "f") t h0
    refine ((((hasDerivAt_id t).const_mul _).add ((hT.const_mul _).mul_const _)).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi4321r4Nondeg, eval, Interp.real, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    field_simp
    ring


theorem rubi4321r4Nondeg_complex : rubi4321r4Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4321r4Nondeg.conditions rubi4321r4Nondeg.body
    rubi4321r4Nondeg.result rubi4321r4Nondeg.integrals
  intro env hc t hF
  have hf : env "f" ≠ 0 := by
    have h := hc (.ne (.var "f") (.int 0)) (by simp [rubi4321r4Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4321r4Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4321r4Nondeg, Defined, eval, Interp.complex] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4321r4Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4321r4Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C] at h ⊢
    try tauto
  · simp only [rubi4321r4Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4321r4Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4321r4Nondeg.result) = fun w => (env "a" * env "c" - env "b" * env "d") * w +
            env "b" * env "d" * Complex.tan (env "e" + env "f" * w) * (env "f")⁻¹ +
            (env "b" * env "c" + env "a" * env "d") * Φ "I1" w := by
      funext w
      simp [rubi4321r4Nondeg, eval, recEnv, Interp.complex, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hT := tan_deriv_C (env "e") (env "f") t h0
    refine ((((hasDerivAt_id t).const_mul _).add ((hT.const_mul _).mul_const _)).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi4321r4Nondeg, eval, Interp.complex, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    field_simp
    ring


/-! ## rubi4121r2Nondeg -/

theorem rubi4121r2Nondeg_real : rubi4121r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4121r2Nondeg.conditions rubi4121r2Nondeg.body
    rubi4121r2Nondeg.result rubi4121r2Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4121r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4121r2Nondeg.body →
      env "c" + env "d" * Real.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4121r2Nondeg, Defined, eval, Interp.real, ivm1R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, ivm1R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r2Nondeg, Defined, eval, recEnv, Interp.real, ivm1R] at h ⊢
    try tauto
  · simp only [rubi4121r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4121r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r2Nondeg.result) = fun w => env "b" * w * (env "d")⁻¹ +
            -((env "b" * env "c" - env "a" * env "d") * (env "d")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4121r2Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    refine ((((hasDerivAt_id t).const_mul _).mul_const _).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi4121r2Nondeg, eval, Interp.real, ivm1R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    generalize hE : env "c" + env "d" * Real.sin (env "e" + env "f" * t) = Dz at h0 ⊢
    field_simp
    rw [← hE]
    ring


theorem rubi4121r2Nondeg_complex : rubi4121r2Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4121r2Nondeg.conditions rubi4121r2Nondeg.body
    rubi4121r2Nondeg.result rubi4121r2Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4121r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4121r2Nondeg.body →
      env "c" + env "d" * Complex.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4121r2Nondeg, Defined, eval, Interp.complex, ivm1C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, ivm1C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r2Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C] at h ⊢
    try tauto
  · simp only [rubi4121r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4121r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r2Nondeg.result) = fun w => env "b" * w * (env "d")⁻¹ +
            -((env "b" * env "c" - env "a" * env "d") * (env "d")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4121r2Nondeg, eval, recEnv, Interp.complex, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    refine ((((hasDerivAt_id t).const_mul _).mul_const _).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi4121r2Nondeg, eval, Interp.complex, ivm1C, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    generalize hE : env "c" + env "d" * Complex.sin (env "e" + env "f" * t) = Dz at h0 ⊢
    field_simp
    rw [← hE]
    ring


/-! ## rubi4331r2Nondeg -/

theorem rubi4331r2Nondeg_real : rubi4331r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4331r2Nondeg.conditions rubi4331r2Nondeg.body
    rubi4331r2Nondeg.result rubi4331r2Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4331r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4331r2Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧ env "a" + env "b" *
          Real.tan (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4331r2Nondeg, Defined, eval, Interp.real, ivm1R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4331r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, ivm1R] at h ⊢
      try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4331r2Nondeg, Defined, eval, recEnv, Interp.real, ivm1R] at h ⊢
    try tauto
  · simp only [rubi4331r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4331r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4331r2Nondeg.result) = fun w => env "B" * env "d" * (env "b")⁻¹ * Φ "I1" w +
            (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi4331r2Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    refine ((hΦ1.const_mul _).add (hΦ2.const_mul _)).congr_deriv ?_
    simp [rubi4331r2Nondeg, eval, Interp.real, ivm1R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    obtain ⟨-, hD0⟩ := h0
    generalize Real.tan (env "e" + env "f" * t) = T at hD0 ⊢
    generalize hE : env "a" + env "b" * T = Dz at hD0 ⊢
    field_simp
    rw [← hE]
    ring


theorem rubi4331r2Nondeg_complex : rubi4331r2Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4331r2Nondeg.conditions rubi4331r2Nondeg.body
    rubi4331r2Nondeg.result rubi4331r2Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4331r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4331r2Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧ env "a" + env "b" *
          Complex.tan (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4331r2Nondeg, Defined, eval, Interp.complex, ivm1C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4331r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, ivm1C] at h ⊢
      try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4331r2Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C] at h ⊢
    try tauto
  · simp only [rubi4331r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4331r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4331r2Nondeg.result) = fun w => env "B" * env "d" * (env "b")⁻¹ * Φ "I1" w +
            (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi4331r2Nondeg, eval, recEnv, Interp.complex, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    refine ((hΦ1.const_mul _).add (hΦ2.const_mul _)).congr_deriv ?_
    simp [rubi4331r2Nondeg, eval, Interp.complex, ivm1C, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    obtain ⟨-, hD0⟩ := h0
    generalize Complex.tan (env "e" + env "f" * t) = T at hD0 ⊢
    generalize hE : env "a" + env "b" * T = Dz at hD0 ⊢
    field_simp
    rw [← hE]
    ring


/-! ## rubi4321r19Nondeg -/

theorem rubi4321r19Nondeg_real : rubi4321r19Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4321r19Nondeg.conditions rubi4321r19Nondeg.body
    rubi4321r19Nondeg.result rubi4321r19Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4321r19Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4321r19Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧ env "a" + env "b" *
          Real.tan (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4321r19Nondeg, Defined, eval, Interp.real, ivm1R, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4321r19Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, ivm1R] at h ⊢
      try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4321r19Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R] at h ⊢
    try tauto
  · simp only [rubi4321r19Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4321r19Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4321r19Nondeg.result) = fun w => env "d" *
            (2 * env "b" * env "c" - env "a" * env "d") * w * (env "b" ^ 2)⁻¹ + env "d" ^ 2 *
            (env "b")⁻¹ * Φ "I1" w + (env "b" * env "c" - env "a" * env "d") ^ 2 *
            (env "b" ^ 2)⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi4321r19Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    refine (((((hasDerivAt_id t).const_mul _).mul_const _).add (hΦ1.const_mul _)).add (hΦ2.const_mul _)).congr_deriv ?_
    simp [rubi4321r19Nondeg, eval, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    obtain ⟨-, hD0⟩ := h0
    generalize Real.tan (env "e" + env "f" * t) = T at hD0 ⊢
    generalize hE : env "a" + env "b" * T = Dz at hD0 ⊢
    field_simp
    rw [← hE]
    ring


theorem rubi4321r19Nondeg_complex : rubi4321r19Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4321r19Nondeg.conditions rubi4321r19Nondeg.body
    rubi4321r19Nondeg.result rubi4321r19Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4321r19Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4321r19Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧ env "a" + env "b" *
          Complex.tan (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4321r19Nondeg, Defined, eval, Interp.complex, ivm1C, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4321r19Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, ivm1C] at h ⊢
      try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4321r19Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C] at h ⊢
    try tauto
  · simp only [rubi4321r19Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4321r19Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4321r19Nondeg.result) = fun w => env "d" *
            (2 * env "b" * env "c" - env "a" * env "d") * w * (env "b" ^ 2)⁻¹ + env "d" ^ 2 *
            (env "b")⁻¹ * Φ "I1" w + (env "b" * env "c" - env "a" * env "d") ^ 2 *
            (env "b" ^ 2)⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi4321r19Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    refine (((((hasDerivAt_id t).const_mul _).mul_const _).add (hΦ1.const_mul _)).add (hΦ2.const_mul _)).congr_deriv ?_
    simp [rubi4321r19Nondeg, eval, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    obtain ⟨-, hD0⟩ := h0
    generalize Complex.tan (env "e" + env "f" * t) = T at hD0 ⊢
    generalize hE : env "a" + env "b" * T = Dz at hD0 ⊢
    field_simp
    rw [← hE]
    ring


/-! ## rubi4521r17Nondeg -/

theorem rubi4521r17Nondeg_real : rubi4521r17Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4521r17Nondeg.conditions rubi4521r17Nondeg.body
    rubi4521r17Nondeg.result rubi4521r17Nondeg.integrals
  intro env hc t hF
  have ha : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi4521r17Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4521r17Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧ env "a" + env "b" *
          (Real.sin (env "e" + env "f" * w))⁻¹ ≠ 0 := by
    intro w h
    simp [rubi4521r17Nondeg, Defined, eval, Interp.real, ivm1R, Fn.csc] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4521r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, ivm1R, Fn.csc] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4521r17Nondeg, Defined, eval, recEnv, Interp.real, ivm1R] at h ⊢
    try tauto
  · simp only [rubi4521r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4521r17Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4521r17Nondeg.result) = fun w => env "c" * w * (env "a")⁻¹ +
            -((env "b" * env "c" - env "a" * env "d") * (env "a")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4521r17Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    refine ((((hasDerivAt_id t).const_mul _).mul_const _).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi4521r17Nondeg, eval, Interp.real, ivm1R, Fn.csc, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    obtain ⟨-, hD0⟩ := h0
    generalize (Real.sin (env "e" + env "f" * t))⁻¹ = K at hD0 ⊢
    generalize hE : env "a" + env "b" * K = Dz at hD0 ⊢
    field_simp
    rw [← hE]
    ring


/-! ## rubi4121r13Nondeg -/

theorem rubi4121r13Nondeg_real : rubi4121r13Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4121r13Nondeg.conditions rubi4121r13Nondeg.body
    rubi4121r13Nondeg.result rubi4121r13Nondeg.integrals
  intro env hc t hF
  have hdf := hc (.ne (.app2 .mul (.var "d") (.var "f")) (.int 0)) (by simp [rubi4121r13Nondeg])
  have hd : env "d" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hdf
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hdf
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4121r13Nondeg.body →
      env "c" + env "d" * Real.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4121r13Nondeg, Defined, eval, Interp.real, ivm1R, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, ivm1R, iv2R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r13Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R] at h ⊢
    try tauto
  · simp only [rubi4121r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4121r13Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r13Nondeg.result) = fun w => -(env "b" ^ 2) *
            Real.cos (env "e" + env "f" * w) * (env "d" * env "f")⁻¹ + (env "d")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4121r13Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hCd := (Real.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    refine (((hCd.const_mul _).mul_const _).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi4121r13Nondeg, eval, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    generalize hE : env "c" + env "d" * Real.sin (env "e" + env "f" * t) = Dz at h0 ⊢
    field_simp
    rw [← hE]
    ring


theorem rubi4121r13Nondeg_complex : rubi4121r13Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4121r13Nondeg.conditions rubi4121r13Nondeg.body
    rubi4121r13Nondeg.result rubi4121r13Nondeg.integrals
  intro env hc t hF
  have hdf := hc (.ne (.app2 .mul (.var "d") (.var "f")) (.int 0)) (by simp [rubi4121r13Nondeg])
  have hd : env "d" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hdf
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hdf
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4121r13Nondeg.body →
      env "c" + env "d" * Complex.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4121r13Nondeg, Defined, eval, Interp.complex, ivm1C, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, ivm1C, iv2C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r13Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C] at h ⊢
    try tauto
  · simp only [rubi4121r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4121r13Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r13Nondeg.result) = fun w => -(env "b" ^ 2) *
            Complex.cos (env "e" + env "f" * w) * (env "d" * env "f")⁻¹ + (env "d")⁻¹ * Φ "I1" w :=
            by
      funext w
      simp [rubi4121r13Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hCd := (Complex.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    refine (((hCd.const_mul _).mul_const _).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi4121r13Nondeg, eval, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    generalize hE : env "c" + env "d" * Complex.sin (env "e" + env "f" * t) = Dz at h0 ⊢
    field_simp
    rw [← hE]
    ring


/-! ## rubi6113r9Nondeg -/

theorem rubi6113r9Nondeg_real : rubi6113r9Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6113r9Nondeg.conditions rubi6113r9Nondeg.body
    rubi6113r9Nondeg.result rubi6113r9Nondeg.integrals
  intro env hc t hF
  have hc0 : env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi6113r9Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi6113r9Nondeg.body →
      True := by
    intro w h
    trivial
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r9Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, iv2R] at h ⊢
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r9Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R] at h ⊢
    try tauto
  · simp only [rubi6113r9Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi6113r9Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r9Nondeg.result) = fun w => env "e" *
            Real.cosh (env "a" + env "b" * w + env "c" * w ^ 2) * (2 * env "c")⁻¹ +
            -((env "b" * env "e" - 2 * env "c" * env "d") * (2 * env "c")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi6113r9Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hX := (Real.hasDerivAt_cosh _).comp t (hasDerivAt_quad (env "a") (env "b") (env "c") t)
    refine (((hX.const_mul _).mul_const _).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi6113r9Nondeg, eval, Interp.real, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    field_simp
    ring


theorem rubi6113r9Nondeg_complex : rubi6113r9Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6113r9Nondeg.conditions rubi6113r9Nondeg.body
    rubi6113r9Nondeg.result rubi6113r9Nondeg.integrals
  intro env hc t hF
  have hc0 : env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi6113r9Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi6113r9Nondeg.body →
      True := by
    intro w h
    trivial
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r9Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, iv2C] at h ⊢
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r9Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C] at h ⊢
    try tauto
  · simp only [rubi6113r9Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi6113r9Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r9Nondeg.result) = fun w => env "e" *
            Complex.cosh (env "a" + env "b" * w + env "c" * w ^ 2) * (2 * env "c")⁻¹ +
            -((env "b" * env "e" - 2 * env "c" * env "d") * (2 * env "c")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi6113r9Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hX := (Complex.hasDerivAt_cosh _).comp t (hasDerivAt_quad (env "a") (env "b") (env "c") t)
    refine (((hX.const_mul _).mul_const _).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi6113r9Nondeg, eval, Interp.complex, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    field_simp
    ring


/-! ## rubi6113r10Nondeg -/

theorem rubi6113r10Nondeg_real : rubi6113r10Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6113r10Nondeg.conditions rubi6113r10Nondeg.body
    rubi6113r10Nondeg.result rubi6113r10Nondeg.integrals
  intro env hc t hF
  have hc0 : env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi6113r10Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi6113r10Nondeg.body →
      True := by
    intro w h
    trivial
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, iv2R] at h ⊢
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r10Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R] at h ⊢
    try tauto
  · simp only [rubi6113r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi6113r10Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r10Nondeg.result) = fun w => env "e" *
            Real.sinh (env "a" + env "b" * w + env "c" * w ^ 2) * (2 * env "c")⁻¹ +
            -((env "b" * env "e" - 2 * env "c" * env "d") * (2 * env "c")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi6113r10Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hX := (Real.hasDerivAt_sinh _).comp t (hasDerivAt_quad (env "a") (env "b") (env "c") t)
    refine (((hX.const_mul _).mul_const _).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi6113r10Nondeg, eval, Interp.real, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    field_simp
    ring


theorem rubi6113r10Nondeg_complex : rubi6113r10Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6113r10Nondeg.conditions rubi6113r10Nondeg.body
    rubi6113r10Nondeg.result rubi6113r10Nondeg.integrals
  intro env hc t hF
  have hc0 : env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi6113r10Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi6113r10Nondeg.body →
      True := by
    intro w h
    trivial
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, iv2C] at h ⊢
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r10Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C] at h ⊢
    try tauto
  · simp only [rubi6113r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1 := hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi6113r10Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r10Nondeg.result) = fun w => env "e" *
            Complex.sinh (env "a" + env "b" * w + env "c" * w ^ 2) * (2 * env "c")⁻¹ +
            -((env "b" * env "e" - 2 * env "c" * env "d") * (2 * env "c")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi6113r10Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    have h0 := hD t hF.self_of_nhds
    have hX := (Complex.hasDerivAt_sinh _).comp t (hasDerivAt_quad (env "a") (env "b") (env "c") t)
    refine (((hX.const_mul _).mul_const _).add (hΦ1.const_mul _)).congr_deriv ?_
    simp [rubi6113r10Nondeg, eval, Interp.complex, iv2C, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    field_simp
    ring


end OSR.IntegrationRec260
