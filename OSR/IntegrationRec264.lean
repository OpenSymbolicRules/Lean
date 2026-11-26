import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: residual integrals with shifted powers

Proofs of RUBI 4.1.3.1 #21, #37, 4.1.4.2 #35, #36 and 4.1.2.1 #89 over ℝ and ℂ and 4.5.3.1 #12, #43
over ℝ (`csc` has no complex interpretation): the result is a combination of residual integrals with
constant coefficients whose integrands differ from the integrand by powers shifted by one; the
powers are split with `X^(j + n) = X^j X^n` (when `X ≠ 0` or `0 ≤ j`). -/

namespace OSR.IntegrationRec264

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem zsplit {K : Type} [Field K] (X : K) (j : ℤ) (n : ℕ) (h : X ≠ 0 ∨ 0 ≤ j) :
    X ^ (j + n) = X ^ j * X ^ n := by
  rcases h with h | h
  · rw [zpow_add₀ h, zpow_natCast]
  · lift j to ℕ using h
    rw [show ((j : ℤ) + n) = ((j + n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_add]

/-! ## rubi4131r21Nondeg -/

theorem rubi4131r21Nondeg_real : rubi4131r21Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4131r21Nondeg.conditions rubi4131r21Nondeg.body
    rubi4131r21Nondeg.result rubi4131r21Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4131r21Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4131r21Nondeg, Defined, eval, Interp.real, hkm] at h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4131r21Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) ∧ env "c" + env "d" *
          Real.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4131r21Nondeg, Defined, eval, Interp.real, hkm, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4131r21Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, hkm, ivm1R] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi4131r21Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hd]
  · simp only [rubi4131r21Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Real.sin (env "e" + env "f" * t)) ^ m) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Real.sin (env "e" + env "f" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, ivm1R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4131r21Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4131r21Nondeg.result) = fun w => env "B" * (env "d")⁻¹ * Φ "I1" w +
            -((env "B" * env "c" - env "A" * env "d") * (env "d")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi4131r21Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi4131r21Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "B" * Real.sin (env "e" + env "f" * t)) *
        (env "c" + env "d" * Real.sin (env "e" + env "f" * t))⁻¹ := by
      simp [rubi4131r21Nondeg, eval, Interp.real, hkm, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨-, hC0⟩ := hD t hF.self_of_nhds
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m = G0
    generalize hE : env "c" + env "d" * Real.sin (env "e" + env "f" * t) = Dz at hC0 ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi4131r21Nondeg_complex : rubi4131r21Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4131r21Nondeg.conditions rubi4131r21Nondeg.body
    rubi4131r21Nondeg.result rubi4131r21Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4131r21Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4131r21Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4131r21Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) ∧ env "c" + env "d" *
          Complex.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4131r21Nondeg, Defined, eval, Interp.complex, hkm, ivm1C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4131r21Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, hkm, ivm1C] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi4131r21Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hd]
  · simp only [rubi4131r21Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ m) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Complex.sin (env "e" + env "f" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkm, ivm1C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4131r21Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4131r21Nondeg.result) = fun w => env "B" * (env "d")⁻¹ * Φ "I1" w +
            -((env "B" * env "c" - env "A" * env "d") * (env "d")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi4131r21Nondeg, eval, recEnv, Interp.complex, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4131r21Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "B" * Complex.sin (env "e" + env "f" * t)) *
        (env "c" + env "d" * Complex.sin (env "e" + env "f" * t))⁻¹ := by
      simp [rubi4131r21Nondeg, eval, Interp.complex, hkm, ivm1C]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨-, hC0⟩ := hD t hF.self_of_nhds
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = G0
    generalize hE : env "c" + env "d" * Complex.sin (env "e" + env "f" * t) = Dz at hC0 ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi4131r37Nondeg -/

theorem rubi4131r37Nondeg_real : rubi4131r37Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4131r37Nondeg.conditions rubi4131r37Nondeg.body
    rubi4131r37Nondeg.result rubi4131r37Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4131r37Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4131r37Nondeg, Defined, eval, Interp.real, hkm] at h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4131r37Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) ∧ env "c" + env "d" *
          Real.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4131r37Nondeg, Defined, eval, Interp.real, hkm, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4131r37Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, hkm, ivm1R] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi4131r37Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hd]
  · simp only [rubi4131r37Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Real.sin (env "e" + env "f" * t)) ^ m) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Real.sin (env "e" + env "f" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, ivm1R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4131r37Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4131r37Nondeg.result) = fun w => env "B" * (env "d")⁻¹ * Φ "I1" w +
            -((env "B" * env "c" - env "A" * env "d") * (env "d")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi4131r37Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi4131r37Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "B" * Real.sin (env "e" + env "f" * t)) *
        (env "c" + env "d" * Real.sin (env "e" + env "f" * t))⁻¹ := by
      simp [rubi4131r37Nondeg, eval, Interp.real, hkm, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨-, hC0⟩ := hD t hF.self_of_nhds
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m = G0
    generalize hE : env "c" + env "d" * Real.sin (env "e" + env "f" * t) = Dz at hC0 ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi4131r37Nondeg_complex : rubi4131r37Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4131r37Nondeg.conditions rubi4131r37Nondeg.body
    rubi4131r37Nondeg.result rubi4131r37Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4131r37Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4131r37Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4131r37Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) ∧ env "c" + env "d" *
          Complex.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4131r37Nondeg, Defined, eval, Interp.complex, hkm, ivm1C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4131r37Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, hkm, ivm1C] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi4131r37Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hd]
  · simp only [rubi4131r37Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ m) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Complex.sin (env "e" + env "f" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkm, ivm1C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4131r37Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4131r37Nondeg.result) = fun w => env "B" * (env "d")⁻¹ * Φ "I1" w +
            -((env "B" * env "c" - env "A" * env "d") * (env "d")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi4131r37Nondeg, eval, recEnv, Interp.complex, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4131r37Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "B" * Complex.sin (env "e" + env "f" * t)) *
        (env "c" + env "d" * Complex.sin (env "e" + env "f" * t))⁻¹ := by
      simp [rubi4131r37Nondeg, eval, Interp.complex, hkm, ivm1C]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨-, hC0⟩ := hD t hF.self_of_nhds
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = G0
    generalize hE : env "c" + env "d" * Complex.sin (env "e" + env "f" * t) = Dz at hC0 ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi4142r36Nondeg -/

theorem rubi4142r36Nondeg_real : rubi4142r36Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4142r36Nondeg.conditions rubi4142r36Nondeg.body
    rubi4142r36Nondeg.result rubi4142r36Nondeg.integrals
  intro env hc t hF
  have hbd : env "b" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.var "d")) (.int 0)) (by simp [rubi4142r36Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r36Nondeg, Defined, eval, Interp.real, hkk] at h
  have hb : env "b" ≠ 0 := left_ne_zero_of_mul hbd
  have hd : env "d" ≠ 0 := right_ne_zero_of_mul hbd
  have enp1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ho0 : k + 1 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4142r36Nondeg.body →
      (k < 0 → env "d" * Real.sin (env "e" + env "f" * w) ≠ 0) ∧ env "a" + env "b" *
          Real.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4142r36Nondeg, Defined, eval, Interp.real, hkk, ivm1R, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4142r36Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, hkk, enp1, ivm1R] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi4142r36Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hb, hd]
  · simp only [rubi4142r36Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2, hΦ3⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "d" * Real.sin (env "e" + env "f" * t)) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkk, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "d" * Real.sin (env "e" + env "f" * t)) ^ (k + 1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, enp1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ3' : HasDerivAt (Φ "I3") ((env "d" * Real.sin (env "e" + env "f" * t)) ^ k *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t))⁻¹) t := by
      convert hΦ3 using 1
      simp [eval, Interp.real, hkk, ivm1R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4142r36Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4142r36Nondeg.result) = fun w => -(env "a" * env "C") * (env "b" ^ 2)⁻¹ *
            Φ "I1" w + env "C" * (env "b" * env "d")⁻¹ * Φ "I2" w +
            (env "A" * env "b" ^ 2 + env "a" ^ 2 * env "C") * (env "b" ^ 2)⁻¹ * Φ "I3" w := by
      funext w
      simp [rubi4142r36Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4142r36Nondeg.body =
        (env "d" * Real.sin (env "e" + env "f" * t)) ^ k *
        (env "A" + env "C" * (Real.sin (env "e" + env "f" * t)) ^ 2) *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t))⁻¹ := by
      simp [rubi4142r36Nondeg, eval, Interp.real, hkk, ivm1R, iv2R]
    rw [hfun, hEF]
    refine (((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).add (hΦ3'.const_mul _)).congr_deriv ?_
    obtain ⟨hS0, hA0⟩ := hD t hF.self_of_nhds
    have eX0 : (env "d" * Real.sin (env "e" + env "f" * t)) ^ (k + 1) =
        (env "d" * Real.sin (env "e" + env "f" * t)) ^ (k) *
        (env "d" * Real.sin (env "e" + env "f" * t)) ^ 1 := by
      have := zsplit (env "d" *
          Real.sin (env "e" + env "f" *
          t)) (k) 1 ((by by_cases hk : k < 0; exacts [Or.inl (hS0 hk), Or.inr (by omega)]))
      rwa [show k + ((1 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
    rw [eX0]
    rw [pow_one]
    generalize (env "d" * Real.sin (env "e" + env "f" * t)) ^ k = G0
    generalize hE : env "a" + env "b" * Real.sin (env "e" + env "f" * t) = Dz at hA0 ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi4142r36Nondeg_complex : rubi4142r36Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4142r36Nondeg.conditions rubi4142r36Nondeg.body
    rubi4142r36Nondeg.result rubi4142r36Nondeg.integrals
  intro env hc t hF
  have hbd : env "b" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.var "d")) (.int 0)) (by simp [rubi4142r36Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r36Nondeg, Defined, eval, Interp.complex, hkk] at h
  have hb : env "b" ≠ 0 := left_ne_zero_of_mul hbd
  have hd : env "d" ≠ 0 := right_ne_zero_of_mul hbd
  have enp1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ho0 : k + 1 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4142r36Nondeg.body →
      (k < 0 → env "d" * Complex.sin (env "e" + env "f" * w) ≠ 0) ∧ env "a" + env "b" *
          Complex.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4142r36Nondeg, Defined, eval, Interp.complex, hkk, ivm1C, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4142r36Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, hkk, enp1, ivm1C] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi4142r36Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, hb, hd]
  · simp only [rubi4142r36Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2, hΦ3⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "d" * Complex.sin (env "e" + env "f" * t)) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkk, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "d" * Complex.sin (env "e" + env "f" * t)) ^ (k +
        1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, enp1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ3' : HasDerivAt (Φ "I3") ((env "d" * Complex.sin (env "e" + env "f" * t)) ^ k *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t))⁻¹) t := by
      convert hΦ3 using 1
      simp [eval, Interp.complex, hkk, ivm1C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4142r36Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4142r36Nondeg.result) = fun w => -(env "a" * env "C") * (env "b" ^ 2)⁻¹ *
            Φ "I1" w + env "C" * (env "b" * env "d")⁻¹ * Φ "I2" w +
            (env "A" * env "b" ^ 2 + env "a" ^ 2 * env "C") * (env "b" ^ 2)⁻¹ * Φ "I3" w := by
      funext w
      simp [rubi4142r36Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4142r36Nondeg.body =
        (env "d" * Complex.sin (env "e" + env "f" * t)) ^ k *
        (env "A" + env "C" * (Complex.sin (env "e" + env "f" * t)) ^ 2) *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t))⁻¹ := by
      simp [rubi4142r36Nondeg, eval, Interp.complex, hkk, ivm1C, iv2C]
    rw [hfun, hEF]
    refine (((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).add (hΦ3'.const_mul _)).congr_deriv ?_
    obtain ⟨hS0, hA0⟩ := hD t hF.self_of_nhds
    have eX0 : (env "d" * Complex.sin (env "e" + env "f" * t)) ^ (k + 1) =
        (env "d" * Complex.sin (env "e" + env "f" * t)) ^ (k) *
        (env "d" * Complex.sin (env "e" + env "f" * t)) ^ 1 := by
      have := zsplit (env "d" *
          Complex.sin (env "e" + env "f" *
          t)) (k) 1 ((by by_cases hk : k < 0; exacts [Or.inl (hS0 hk), Or.inr (by omega)]))
      rwa [show k + ((1 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
    rw [eX0]
    rw [pow_one]
    generalize (env "d" * Complex.sin (env "e" + env "f" * t)) ^ k = G0
    generalize hE : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) = Dz at hA0 ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi4142r35Nondeg -/

theorem rubi4142r35Nondeg_real : rubi4142r35Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4142r35Nondeg.conditions rubi4142r35Nondeg.body
    rubi4142r35Nondeg.result rubi4142r35Nondeg.integrals
  intro env hc t hF
  have hbd : env "b" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.var "d")) (.int 0)) (by simp [rubi4142r35Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r35Nondeg, Defined, eval, Interp.real, hkk] at h
  have hb : env "b" ≠ 0 := left_ne_zero_of_mul hbd
  have hd : env "d" ≠ 0 := right_ne_zero_of_mul hbd
  have enp1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ho0 : k + 1 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4142r35Nondeg.body →
      (k < 0 → env "d" * Real.sin (env "e" + env "f" * w) ≠ 0) ∧ env "a" + env "b" *
          Real.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4142r35Nondeg, Defined, eval, Interp.real, hkk, ivm1R, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4142r35Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, hkk, enp1, ivm1R] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi4142r35Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hb, hd]
  · simp only [rubi4142r35Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2, hΦ3⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "d" * Real.sin (env "e" + env "f" * t)) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkk, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "d" * Real.sin (env "e" + env "f" * t)) ^ (k + 1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, enp1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ3' : HasDerivAt (Φ "I3") ((env "d" * Real.sin (env "e" + env "f" * t)) ^ k *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t))⁻¹) t := by
      convert hΦ3 using 1
      simp [eval, Interp.real, hkk, ivm1R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4142r35Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4142r35Nondeg.result) = fun w => (env "b" * env "B" - env "a" * env "C") *
            (env "b" ^ 2)⁻¹ * Φ "I1" w + env "C" * (env "b" * env "d")⁻¹ * Φ "I2" w +
            (env "A" * env "b" ^ 2 - env "a" * env "b" * env "B" + env "a" ^ 2 * env "C") *
            (env "b" ^ 2)⁻¹ * Φ "I3" w := by
      funext w
      simp [rubi4142r35Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi4142r35Nondeg.body =
        (env "d" * Real.sin (env "e" + env "f" * t)) ^ k *
        (env "A" + env "B" * Real.sin (env "e" + env "f" * t) + env "C" *
        (Real.sin (env "e" + env "f" * t)) ^ 2) *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t))⁻¹ := by
      simp [rubi4142r35Nondeg, eval, Interp.real, hkk, ivm1R, iv2R]
    rw [hfun, hEF]
    refine (((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).add (hΦ3'.const_mul _)).congr_deriv ?_
    obtain ⟨hS0, hA0⟩ := hD t hF.self_of_nhds
    have eX0 : (env "d" * Real.sin (env "e" + env "f" * t)) ^ (k + 1) =
        (env "d" * Real.sin (env "e" + env "f" * t)) ^ (k) *
        (env "d" * Real.sin (env "e" + env "f" * t)) ^ 1 := by
      have := zsplit (env "d" *
          Real.sin (env "e" + env "f" *
          t)) (k) 1 ((by by_cases hk : k < 0; exacts [Or.inl (hS0 hk), Or.inr (by omega)]))
      rwa [show k + ((1 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
    rw [eX0]
    rw [pow_one]
    generalize (env "d" * Real.sin (env "e" + env "f" * t)) ^ k = G0
    generalize hE : env "a" + env "b" * Real.sin (env "e" + env "f" * t) = Dz at hA0 ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi4142r35Nondeg_complex : rubi4142r35Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4142r35Nondeg.conditions rubi4142r35Nondeg.body
    rubi4142r35Nondeg.result rubi4142r35Nondeg.integrals
  intro env hc t hF
  have hbd : env "b" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.var "d")) (.int 0)) (by simp [rubi4142r35Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r35Nondeg, Defined, eval, Interp.complex, hkk] at h
  have hb : env "b" ≠ 0 := left_ne_zero_of_mul hbd
  have hd : env "d" ≠ 0 := right_ne_zero_of_mul hbd
  have enp1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ho0 : k + 1 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4142r35Nondeg.body →
      (k < 0 → env "d" * Complex.sin (env "e" + env "f" * w) ≠ 0) ∧ env "a" + env "b" *
          Complex.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4142r35Nondeg, Defined, eval, Interp.complex, hkk, ivm1C, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4142r35Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, hkk, enp1, ivm1C] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi4142r35Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, hb, hd]
  · simp only [rubi4142r35Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2, hΦ3⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "d" * Complex.sin (env "e" + env "f" * t)) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkk, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "d" * Complex.sin (env "e" + env "f" * t)) ^ (k +
        1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, enp1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ3' : HasDerivAt (Φ "I3") ((env "d" * Complex.sin (env "e" + env "f" * t)) ^ k *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t))⁻¹) t := by
      convert hΦ3 using 1
      simp [eval, Interp.complex, hkk, ivm1C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4142r35Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4142r35Nondeg.result) = fun w => (env "b" * env "B" - env "a" * env "C") *
            (env "b" ^ 2)⁻¹ * Φ "I1" w + env "C" * (env "b" * env "d")⁻¹ * Φ "I2" w +
            (env "A" * env "b" ^ 2 - env "a" * env "b" * env "B" + env "a" ^ 2 * env "C") *
            (env "b" ^ 2)⁻¹ * Φ "I3" w := by
      funext w
      simp [rubi4142r35Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4142r35Nondeg.body =
        (env "d" * Complex.sin (env "e" + env "f" * t)) ^ k *
        (env "A" + env "B" * Complex.sin (env "e" + env "f" * t) + env "C" *
        (Complex.sin (env "e" + env "f" * t)) ^ 2) *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t))⁻¹ := by
      simp [rubi4142r35Nondeg, eval, Interp.complex, hkk, ivm1C, iv2C]
    rw [hfun, hEF]
    refine (((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).add (hΦ3'.const_mul _)).congr_deriv ?_
    obtain ⟨hS0, hA0⟩ := hD t hF.self_of_nhds
    have eX0 : (env "d" * Complex.sin (env "e" + env "f" * t)) ^ (k + 1) =
        (env "d" * Complex.sin (env "e" + env "f" * t)) ^ (k) *
        (env "d" * Complex.sin (env "e" + env "f" * t)) ^ 1 := by
      have := zsplit (env "d" *
          Complex.sin (env "e" + env "f" *
          t)) (k) 1 ((by by_cases hk : k < 0; exacts [Or.inl (hS0 hk), Or.inr (by omega)]))
      rwa [show k + ((1 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
    rw [eX0]
    rw [pow_one]
    generalize (env "d" * Complex.sin (env "e" + env "f" * t)) ^ k = G0
    generalize hE : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) = Dz at hA0 ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi4121r89Nondeg -/

theorem rubi4121r89Nondeg_real : rubi4121r89Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4121r89Nondeg.conditions rubi4121r89Nondeg.body
    rubi4121r89Nondeg.result rubi4121r89Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4121r89Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r89Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r89Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi4121r89Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have enp1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ho0 : ¬ m - 1 < 0 := by omega
  have ho1 : ¬ m < 1 := by omega
  have ho2 : ¬ m < 0 := by omega
  have ho3 : k + 1 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4121r89Nondeg.body →
      (k < 0 → env "c" + env "d" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r89Nondeg, Defined, eval, Interp.real, hkm, hkk] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r89Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, hkk, emm1, enp1] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi4121r89Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hd]
  · simp only [rubi4121r89Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m -
        1) * (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ (k + 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, emm1, enp1, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m -
        1) * (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ k) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkk, emm1, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4121r89Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r89Nondeg.result) = fun w => env "b" * (env "d")⁻¹ * Φ "I1" w +
            -((env "b" * env "c" - env "a" * env "d") * (env "d")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi4121r89Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi4121r89Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ k := by
      simp [rubi4121r89Nondeg, eval, Interp.real, hkm, hkk]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain hC0 := hD t hF.self_of_nhds
    have eX0 : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m - 1) *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ 1 := by
      have := zsplit (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) (m -
          1) 1 ((Or.inr (by omega)))
      rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
    have eX1 : (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ (k + 1) =
        (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ (k) *
        (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ 1 := by
      have := zsplit (env "c" + env "d" *
          Real.sin (env "e" + env "f" *
          t)) (k) 1 ((by by_cases hk : k < 0; exacts [Or.inl (hC0 hk), Or.inr (by omega)]))
      rwa [show k + ((1 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
    rw [eX0, eX1]
    rw [pow_one, pow_one]
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m - 1) = G0
    generalize (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ k = G1
    field_simp
    ring

theorem rubi4121r89Nondeg_complex : rubi4121r89Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4121r89Nondeg.conditions rubi4121r89Nondeg.body
    rubi4121r89Nondeg.result rubi4121r89Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4121r89Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r89Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r89Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi4121r89Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (0 : ℝ) < m := by simpa using h'
    exact_mod_cast h''
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have enp1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ho0 : ¬ m - 1 < 0 := by omega
  have ho1 : ¬ m < 1 := by omega
  have ho2 : ¬ m < 0 := by omega
  have ho3 : k + 1 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4121r89Nondeg.body →
      (k < 0 → env "c" + env "d" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r89Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r89Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, hkk, emm1, enp1] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi4121r89Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hd]
  · simp only [rubi4121r89Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ (m - 1) *
        (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ (k + 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, emm1, enp1, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ (m - 1) *
        (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ k) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkk, emm1, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4121r89Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r89Nondeg.result) = fun w => env "b" * (env "d")⁻¹ * Φ "I1" w +
            -((env "b" * env "c" - env "a" * env "d") * (env "d")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi4121r89Nondeg, eval, recEnv, Interp.complex, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4121r89Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ k := by
      simp [rubi4121r89Nondeg, eval, Interp.complex, hkm, hkk]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain hC0 := hD t hF.self_of_nhds
    have eX0 : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m - 1) *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ 1 := by
      have := zsplit (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) (m -
          1) 1 ((Or.inr (by omega)))
      rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
    have eX1 : (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ (k + 1) =
        (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ (k) *
        (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ 1 := by
      have := zsplit (env "c" + env "d" *
          Complex.sin (env "e" + env "f" *
          t)) (k) 1 ((by by_cases hk : k < 0; exacts [Or.inl (hC0 hk), Or.inr (by omega)]))
      rwa [show k + ((1 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
    rw [eX0, eX1]
    rw [pow_one, pow_one]
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m - 1) = G0
    generalize (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ k = G1
    field_simp
    ring

/-! ## rubi4531r12Nondeg -/

theorem rubi4531r12Nondeg_real : rubi4531r12Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4531r12Nondeg.conditions rubi4531r12Nondeg.body
    rubi4531r12Nondeg.result rubi4531r12Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4531r12Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4531r12Nondeg, Defined, eval, Interp.real, hkm, Fn.csc] at h
  have emp1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho0 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4531r12Nondeg.body →
      (m < 0 → env "a" + env "b" * (Real.sin (env "e" + env "f" * w))⁻¹ ≠ 0) ∧
          Real.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4531r12Nondeg, Defined, eval, Interp.real, hkm, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4531r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, hkm, emp1, Fn.csc] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi4531r12Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hb]
  · simp only [rubi4531r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((Real.sin (env "e" + env "f" * t))⁻¹ *
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((Real.sin (env "e" + env "f" * t))⁻¹ *
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ (m + 1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, emp1, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4531r12Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4531r12Nondeg.result) = fun w => (env "A" * env "b" - env "a" * env "B") *
            (env "b")⁻¹ * Φ "I1" w + env "B" * (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi4531r12Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi4531r12Nondeg.body =
        (Real.sin (env "e" + env "f" * t))⁻¹ *
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m *
        (env "A" + env "B" * (Real.sin (env "e" + env "f" * t))⁻¹) := by
      simp [rubi4531r12Nondeg, eval, Interp.real, hkm, Fn.csc]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hA0, hs0⟩ := hD t hF.self_of_nhds
    have eX0 : (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ (m + 1) =
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ (m) *
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ 1 := by
      have := zsplit (env "a" + env "b" *
          (Real.sin (env "e" + env "f" *
          t))⁻¹) (m) 1 ((by by_cases hm : m < 0; exacts [Or.inl (hA0 hm), Or.inr (by omega)]))
      rwa [show m + ((1 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
    rw [eX0]
    rw [pow_one]
    generalize (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m = G0
    generalize (Real.sin (env "e" + env "f" * t))⁻¹ = G1
    field_simp
    ring

/-! ## rubi4531r43Nondeg -/

theorem rubi4531r43Nondeg_real : rubi4531r43Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4531r43Nondeg.conditions rubi4531r43Nondeg.body
    rubi4531r43Nondeg.result rubi4531r43Nondeg.integrals
  intro env hc t hF
  have ha : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi4531r43Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have had : env "a" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "a") (.var "d")) (.int 0)) (by simp [rubi4531r43Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4531r43Nondeg, Defined, eval, Interp.real, hkk, Fn.csc] at h
  have hd : env "d" ≠ 0 := right_ne_zero_of_mul had
  have enp1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ho0 : k + 1 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4531r43Nondeg.body →
      (k < 0 → env "d" * (Real.sin (env "e" + env "f" * w))⁻¹ ≠ 0) ∧
          Real.sin (env "e" + env "f" * w) ≠ 0 ∧ env "a" + env "b" *
          (Real.sin (env "e" + env "f" * w))⁻¹ ≠ 0 := by
    intro w h
    simp [rubi4531r43Nondeg, Defined, eval, Interp.real, hkk, ivm1R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4531r43Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, hkk, enp1, ivm1R, Fn.csc] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi4531r43Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, ha, hd]
  · simp only [rubi4531r43Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkk, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ (k + 1) *
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, enp1, ivm1R, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4531r43Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4531r43Nondeg.result) = fun w => env "A" * (env "a")⁻¹ * Φ "I1" w +
            -((env "A" * env "b" - env "a" * env "B") * (env "a" * env "d")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi4531r43Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi4531r43Nondeg.body =
        (env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ k *
        (env "A" + env "B" * (Real.sin (env "e" + env "f" * t))⁻¹) *
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹)⁻¹ := by
      simp [rubi4531r43Nondeg, eval, Interp.real, hkk, ivm1R, Fn.csc]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hS0, hs0, hA0⟩ := hD t hF.self_of_nhds
    have eX0 : (env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ (k + 1) =
        (env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ (k) *
        (env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ 1 := by
      have := zsplit (env "d" *
          (Real.sin (env "e" + env "f" *
          t))⁻¹) (k) 1 ((by by_cases hk : k < 0; exacts [Or.inl (hS0 hk), Or.inr (by omega)]))
      rwa [show k + ((1 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
    rw [eX0]
    rw [pow_one]
    generalize (env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ k = G0
    generalize (Real.sin (env "e" + env "f" * t))⁻¹ = Y at hA0 ⊢
    generalize hE : env "a" + env "b" * Y = Dz at hA0 ⊢
    field_simp
    rw [← hE]
    ring

end OSR.IntegrationRec264
