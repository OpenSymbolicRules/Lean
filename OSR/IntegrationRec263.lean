import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: quadratic factors absorbed by `a + b y`

Proofs of RUBI 4.1.4.2 #1, #2, 4.3.4.2 #1, #2 (over ℝ and ℂ) and 4.5.4.1 #2, 4.5.4.2 #1, #2 (over ℝ,
`csc` has no complex interpretation): when `A b² - a b B + a² C = 0`, the factor `A + B y + C y²`
equals `(a + b y) (b B - a C + b C y) / b²`, so the integrand is a constant multiple of the
residual integrand with `(a + b y)^(m + 1)`. -/

namespace OSR.IntegrationRec263

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

/-! ## rubi4142r2Nondeg -/

theorem rubi4142r2Nondeg_real : rubi4142r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4142r2Nondeg.conditions rubi4142r2Nondeg.body
    rubi4142r2Nondeg.result rubi4142r2Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4142r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hrel : env "A" * env "b" ^ 2 + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4142r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r2Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r2Nondeg, Defined, eval, Interp.real, hkm, hkn] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4142r2Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) ∧
          (k < 0 → env "c" + env "d" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4142r2Nondeg, Defined, eval, Interp.real, hkm, hkn, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4142r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, hkn] at h ⊢
    tauto
  · filter_upwards with w
    simp [rubi4142r2Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hb]
  · simp only [rubi4142r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m +
        1) * (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ k *
        (env "a" - env "b" * Real.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, hkn, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4142r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4142r2Nondeg.result) = fun w => -(env "C") * (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4142r2Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4142r2Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
            (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ k *
            (env "A" + env "C" * (Real.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4142r2Nondeg, eval, Interp.real, hkm, hkn, iv2R]
    rw [hfun, hEF]
    refine (hΦ1'.const_mul _).congr_deriv ?_
    obtain ⟨hA0, -⟩ := hD t hF.self_of_nhds
    have eA : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ (hA0 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    have hA : env "A" = -(env "a" ^ 2 * env "C") / env "b" ^ 2 := by
      field_simp
      linear_combination hrel
    rw [eA, hA]
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m = P
    generalize (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ k = Q
    generalize Real.sin (env "e" + env "f" * t) = Y
    field_simp
    ring

theorem rubi4142r2Nondeg_complex : rubi4142r2Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4142r2Nondeg.conditions rubi4142r2Nondeg.body
    rubi4142r2Nondeg.result rubi4142r2Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4142r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  have hrel : env "A" * env "b" ^ 2 + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4142r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r2Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r2Nondeg, Defined, eval, Interp.complex, hkm, hkn] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4142r2Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) ∧
          (k < 0 → env "c" + env "d" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4142r2Nondeg, Defined, eval, Interp.complex, hkm, hkn, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4142r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1, hkn] at h ⊢
    tauto
  · filter_upwards with w
    simp [rubi4142r2Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, hb]
  · simp only [rubi4142r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ (m + 1) *
        (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ k *
        (env "a" - env "b" * Complex.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, hkn, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4142r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4142r2Nondeg.result) = fun w => -(env "C") * (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4142r2Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4142r2Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
            (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ k *
            (env "A" + env "C" * (Complex.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4142r2Nondeg, eval, Interp.complex, hkm, hkn, iv2C]
    rw [hfun, hEF]
    refine (hΦ1'.const_mul _).congr_deriv ?_
    obtain ⟨hA0, -⟩ := hD t hF.self_of_nhds
    have eA : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ (hA0 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    have hA : env "A" = -(env "a" ^ 2 * env "C") / env "b" ^ 2 := by
      field_simp
      linear_combination hrel
    rw [eA, hA]
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = P
    generalize (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ k = Q
    generalize Complex.sin (env "e" + env "f" * t) = Y
    field_simp
    ring

/-! ## rubi4142r1Nondeg -/

theorem rubi4142r1Nondeg_real : rubi4142r1Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4142r1Nondeg.conditions rubi4142r1Nondeg.body
    rubi4142r1Nondeg.result rubi4142r1Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4142r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hrel : env "A" * env "b" ^ 2 - env "a" * env "b" * env "B" + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4142r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r1Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r1Nondeg, Defined, eval, Interp.real, hkm, hkn] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4142r1Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) ∧
          (k < 0 → env "c" + env "d" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4142r1Nondeg, Defined, eval, Interp.real, hkm, hkn, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4142r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, hkn] at h ⊢
    tauto
  · filter_upwards with w
    simp [rubi4142r1Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hb]
  · simp only [rubi4142r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m +
        1) * (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ k *
        (env "b" * env "B" - env "a" * env "C" + env "b" * env "C" *
        Real.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, hkn, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4142r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4142r1Nondeg.result) = fun w => (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4142r1Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4142r1Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
            (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ k *
            (env "A" + env "B" * Real.sin (env "e" + env "f" * t) + env "C" *
            (Real.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4142r1Nondeg, eval, Interp.real, hkm, hkn, iv2R]
    rw [hfun, hEF]
    refine (hΦ1'.const_mul _).congr_deriv ?_
    obtain ⟨hA0, -⟩ := hD t hF.self_of_nhds
    have eA : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ (hA0 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    have hA : env "A" = (env "a" * env "b" * env "B" - env "a" ^ 2 * env "C") / env "b" ^ 2 := by
      field_simp
      linear_combination hrel
    rw [eA, hA]
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m = P
    generalize (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ k = Q
    generalize Real.sin (env "e" + env "f" * t) = Y
    field_simp
    ring

theorem rubi4142r1Nondeg_complex : rubi4142r1Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4142r1Nondeg.conditions rubi4142r1Nondeg.body
    rubi4142r1Nondeg.result rubi4142r1Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4142r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  have hrel : env "A" * env "b" ^ 2 - env "a" * env "b" * env "B" + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4142r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r1Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r1Nondeg, Defined, eval, Interp.complex, hkm, hkn] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4142r1Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) ∧
          (k < 0 → env "c" + env "d" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4142r1Nondeg, Defined, eval, Interp.complex, hkm, hkn, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4142r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1, hkn] at h ⊢
    tauto
  · filter_upwards with w
    simp [rubi4142r1Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, hb]
  · simp only [rubi4142r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ (m + 1) *
        (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ k *
        (env "b" * env "B" - env "a" * env "C" + env "b" * env "C" *
        Complex.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, hkn, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4142r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4142r1Nondeg.result) = fun w => (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4142r1Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4142r1Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
            (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ k *
            (env "A" + env "B" * Complex.sin (env "e" + env "f" * t) + env "C" *
            (Complex.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4142r1Nondeg, eval, Interp.complex, hkm, hkn, iv2C]
    rw [hfun, hEF]
    refine (hΦ1'.const_mul _).congr_deriv ?_
    obtain ⟨hA0, -⟩ := hD t hF.self_of_nhds
    have eA : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ (hA0 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    have hA : env "A" = (env "a" * env "b" * env "B" - env "a" ^ 2 * env "C") / env "b" ^ 2 := by
      field_simp
      linear_combination hrel
    rw [eA, hA]
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = P
    generalize (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ k = Q
    generalize Complex.sin (env "e" + env "f" * t) = Y
    field_simp
    ring

/-! ## rubi4342r2Nondeg -/

theorem rubi4342r2Nondeg_real : rubi4342r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4342r2Nondeg.conditions rubi4342r2Nondeg.body
    rubi4342r2Nondeg.result rubi4342r2Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4342r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hrel : env "A" * env "b" ^ 2 + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4342r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4342r2Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4342r2Nondeg, Defined, eval, Interp.real, hkm, hkn] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4342r2Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.tan (env "e" + env "f" * w) ≠ 0) ∧
          (k < 0 → env "c" + env "d" * Real.tan (env "e" + env "f" * w) ≠ 0) ∧
          Real.cos (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4342r2Nondeg, Defined, eval, Interp.real, hkm, hkn, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4342r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, hkn] at h ⊢
    tauto
  · filter_upwards with w
    simp [rubi4342r2Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hb]
  · simp only [rubi4342r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ (m +
        1) * (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) ^ k *
        (env "a" - env "b" * Real.tan (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, hkn, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4342r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4342r2Nondeg.result) = fun w => -(env "C") * (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4342r2Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4342r2Nondeg.body =
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m *
            (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) ^ k *
            (env "A" + env "C" * (Real.tan (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4342r2Nondeg, eval, Interp.real, hkm, hkn, iv2R]
    rw [hfun, hEF]
    refine (hΦ1'.const_mul _).congr_deriv ?_
    obtain ⟨hA0, -, -⟩ := hD t hF.self_of_nhds
    have eA : (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ (hA0 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    have hA : env "A" = -(env "a" ^ 2 * env "C") / env "b" ^ 2 := by
      field_simp
      linear_combination hrel
    rw [eA, hA]
    generalize (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m = P
    generalize (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) ^ k = Q
    generalize Real.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

theorem rubi4342r2Nondeg_complex : rubi4342r2Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4342r2Nondeg.conditions rubi4342r2Nondeg.body
    rubi4342r2Nondeg.result rubi4342r2Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4342r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  have hrel : env "A" * env "b" ^ 2 + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4342r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4342r2Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4342r2Nondeg, Defined, eval, Interp.complex, hkm, hkn] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4342r2Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.tan (env "e" + env "f" * w) ≠ 0) ∧
          (k < 0 → env "c" + env "d" * Complex.tan (env "e" + env "f" * w) ≠ 0) ∧
          Complex.cos (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4342r2Nondeg, Defined, eval, Interp.complex, hkm, hkn, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4342r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1, hkn] at h ⊢
    tauto
  · filter_upwards with w
    simp [rubi4342r2Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, hb]
  · simp only [rubi4342r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.tan (env "e" + env "f" * t)) ^ (m + 1) *
        (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) ^ k *
        (env "a" - env "b" * Complex.tan (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, hkn, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4342r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4342r2Nondeg.result) = fun w => -(env "C") * (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4342r2Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4342r2Nondeg.body =
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m *
            (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) ^ k *
            (env "A" + env "C" * (Complex.tan (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4342r2Nondeg, eval, Interp.complex, hkm, hkn, iv2C]
    rw [hfun, hEF]
    refine (hΦ1'.const_mul _).congr_deriv ?_
    obtain ⟨hA0, -, -⟩ := hD t hF.self_of_nhds
    have eA : (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ (hA0 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    have hA : env "A" = -(env "a" ^ 2 * env "C") / env "b" ^ 2 := by
      field_simp
      linear_combination hrel
    rw [eA, hA]
    generalize (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m = P
    generalize (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) ^ k = Q
    generalize Complex.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

/-! ## rubi4342r1Nondeg -/

theorem rubi4342r1Nondeg_real : rubi4342r1Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4342r1Nondeg.conditions rubi4342r1Nondeg.body
    rubi4342r1Nondeg.result rubi4342r1Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4342r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hrel : env "A" * env "b" ^ 2 - env "a" * env "b" * env "B" + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4342r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4342r1Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4342r1Nondeg, Defined, eval, Interp.real, hkm, hkn] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4342r1Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.tan (env "e" + env "f" * w) ≠ 0) ∧
          (k < 0 → env "c" + env "d" * Real.tan (env "e" + env "f" * w) ≠ 0) ∧
          Real.cos (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4342r1Nondeg, Defined, eval, Interp.real, hkm, hkn, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4342r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, hkn] at h ⊢
    tauto
  · filter_upwards with w
    simp [rubi4342r1Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hb]
  · simp only [rubi4342r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ (m +
        1) * (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) ^ k *
        (env "b" * env "B" - env "a" * env "C" + env "b" * env "C" *
        Real.tan (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, hkn, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4342r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4342r1Nondeg.result) = fun w => (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4342r1Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4342r1Nondeg.body =
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m *
            (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) ^ k *
            (env "A" + env "B" * Real.tan (env "e" + env "f" * t) + env "C" *
            (Real.tan (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4342r1Nondeg, eval, Interp.real, hkm, hkn, iv2R]
    rw [hfun, hEF]
    refine (hΦ1'.const_mul _).congr_deriv ?_
    obtain ⟨hA0, -, -⟩ := hD t hF.self_of_nhds
    have eA : (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ (hA0 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    have hA : env "A" = (env "a" * env "b" * env "B" - env "a" ^ 2 * env "C") / env "b" ^ 2 := by
      field_simp
      linear_combination hrel
    rw [eA, hA]
    generalize (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m = P
    generalize (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) ^ k = Q
    generalize Real.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

theorem rubi4342r1Nondeg_complex : rubi4342r1Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4342r1Nondeg.conditions rubi4342r1Nondeg.body
    rubi4342r1Nondeg.result rubi4342r1Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4342r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  have hrel : env "A" * env "b" ^ 2 - env "a" * env "b" * env "B" + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4342r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4342r1Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4342r1Nondeg, Defined, eval, Interp.complex, hkm, hkn] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4342r1Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.tan (env "e" + env "f" * w) ≠ 0) ∧
          (k < 0 → env "c" + env "d" * Complex.tan (env "e" + env "f" * w) ≠ 0) ∧
          Complex.cos (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4342r1Nondeg, Defined, eval, Interp.complex, hkm, hkn, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4342r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1, hkn] at h ⊢
    tauto
  · filter_upwards with w
    simp [rubi4342r1Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, hb]
  · simp only [rubi4342r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.tan (env "e" + env "f" * t)) ^ (m + 1) *
        (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) ^ k *
        (env "b" * env "B" - env "a" * env "C" + env "b" * env "C" *
        Complex.tan (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, hkn, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4342r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4342r1Nondeg.result) = fun w => (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4342r1Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4342r1Nondeg.body =
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m *
            (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) ^ k *
            (env "A" + env "B" * Complex.tan (env "e" + env "f" * t) + env "C" *
            (Complex.tan (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4342r1Nondeg, eval, Interp.complex, hkm, hkn, iv2C]
    rw [hfun, hEF]
    refine (hΦ1'.const_mul _).congr_deriv ?_
    obtain ⟨hA0, -, -⟩ := hD t hF.self_of_nhds
    have eA : (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ (hA0 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    have hA : env "A" = (env "a" * env "b" * env "B" - env "a" ^ 2 * env "C") / env "b" ^ 2 := by
      field_simp
      linear_combination hrel
    rw [eA, hA]
    generalize (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m = P
    generalize (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) ^ k = Q
    generalize Complex.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

/-! ## rubi4541r2Nondeg -/

theorem rubi4541r2Nondeg_real : rubi4541r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4541r2Nondeg.conditions rubi4541r2Nondeg.body
    rubi4541r2Nondeg.result rubi4541r2Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4541r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hrel : env "A" * env "b" ^ 2 + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4541r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4541r2Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4541r2Nondeg.body →
      (m < 0 → env "a" + env "b" * (Real.sin (env "e" + env "f" * w))⁻¹ ≠ 0) ∧
          Real.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4541r2Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4541r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, Fn.csc] at h ⊢
    tauto
  · filter_upwards with w
    simp [rubi4541r2Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hb]
  · simp only [rubi4541r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        (Real.sin (env "e" + env "f" * t))⁻¹) ^ (m + 1) *
        (-env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4541r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4541r2Nondeg.result) = fun w => env "C" * (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4541r2Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4541r2Nondeg.body =
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m *
            (env "A" + env "C" * ((Real.sin (env "e" + env "f" * t))⁻¹) ^ 2) := by
      simp [rubi4541r2Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    refine (hΦ1'.const_mul _).congr_deriv ?_
    obtain ⟨hA0, -⟩ := hD t hF.self_of_nhds
    have eA : (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ (m + 1) =
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m *
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ (hA0 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    have hA : env "A" = -(env "a" ^ 2 * env "C") / env "b" ^ 2 := by
      field_simp
      linear_combination hrel
    rw [eA, hA]
    generalize (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m = P
    generalize (Real.sin (env "e" + env "f" * t))⁻¹ = Y
    field_simp
    ring

/-! ## rubi4542r2Nondeg -/

theorem rubi4542r2Nondeg_real : rubi4542r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4542r2Nondeg.conditions rubi4542r2Nondeg.body
    rubi4542r2Nondeg.result rubi4542r2Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4542r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hrel : env "A" * env "b" ^ 2 + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4542r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r2Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r2Nondeg, Defined, eval, Interp.real, hkm, hkn, Fn.csc] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4542r2Nondeg.body →
      (m < 0 → env "a" + env "b" * (Real.sin (env "e" + env "f" * w))⁻¹ ≠ 0) ∧
          (k < 0 → env "c" + env "d" * (Real.sin (env "e" + env "f" * w))⁻¹ ≠ 0) ∧
          Real.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4542r2Nondeg, Defined, eval, Interp.real, hkm, hkn, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4542r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, hkn, Fn.csc] at h ⊢
    tauto
  · filter_upwards with w
    simp [rubi4542r2Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hb]
  · simp only [rubi4542r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        (Real.sin (env "e" + env "f" * t))⁻¹) ^ (m + 1) *
        (env "c" + env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ k *
        (env "a" - env "b" * (Real.sin (env "e" + env "f" * t))⁻¹)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, hkn, Fn.csc, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4542r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4542r2Nondeg.result) = fun w => -(env "C") * (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4542r2Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4542r2Nondeg.body =
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m *
            (env "c" + env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ k *
            (env "A" + env "C" * ((Real.sin (env "e" + env "f" * t))⁻¹) ^ 2) := by
      simp [rubi4542r2Nondeg, eval, Interp.real, hkm, hkn, iv2R, Fn.csc]
    rw [hfun, hEF]
    refine (hΦ1'.const_mul _).congr_deriv ?_
    obtain ⟨hA0, -, -⟩ := hD t hF.self_of_nhds
    have eA : (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ (m + 1) =
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m *
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ (hA0 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    have hA : env "A" = -(env "a" ^ 2 * env "C") / env "b" ^ 2 := by
      field_simp
      linear_combination hrel
    rw [eA, hA]
    generalize (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m = P
    generalize (env "c" + env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ k = Q
    generalize (Real.sin (env "e" + env "f" * t))⁻¹ = Y
    field_simp
    ring

/-! ## rubi4542r1Nondeg -/

theorem rubi4542r1Nondeg_real : rubi4542r1Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4542r1Nondeg.conditions rubi4542r1Nondeg.body
    rubi4542r1Nondeg.result rubi4542r1Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4542r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hrel : env "A" * env "b" ^ 2 - env "a" * env "b" * env "B" + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4542r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r1Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r1Nondeg, Defined, eval, Interp.real, hkm, hkn, Fn.csc] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4542r1Nondeg.body →
      (m < 0 → env "a" + env "b" * (Real.sin (env "e" + env "f" * w))⁻¹ ≠ 0) ∧
          (k < 0 → env "c" + env "d" * (Real.sin (env "e" + env "f" * w))⁻¹ ≠ 0) ∧
          Real.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4542r1Nondeg, Defined, eval, Interp.real, hkm, hkn, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4542r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, hkn, Fn.csc] at h ⊢
    tauto
  · filter_upwards with w
    simp [rubi4542r1Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hb]
  · simp only [rubi4542r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        (Real.sin (env "e" + env "f" * t))⁻¹) ^ (m + 1) *
        (env "c" + env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ k *
        (env "b" * env "B" - env "a" * env "C" + env "b" * env "C" *
        (Real.sin (env "e" + env "f" * t))⁻¹)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, hkn, Fn.csc, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4542r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4542r1Nondeg.result) = fun w => (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4542r1Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4542r1Nondeg.body =
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m *
            (env "c" + env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ k *
            (env "A" + env "B" * (Real.sin (env "e" + env "f" * t))⁻¹ + env "C" *
            ((Real.sin (env "e" + env "f" * t))⁻¹) ^ 2) := by
      simp [rubi4542r1Nondeg, eval, Interp.real, hkm, hkn, iv2R, Fn.csc]
    rw [hfun, hEF]
    refine (hΦ1'.const_mul _).congr_deriv ?_
    obtain ⟨hA0, -, -⟩ := hD t hF.self_of_nhds
    have eA : (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ (m + 1) =
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m *
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ (hA0 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    have hA : env "A" = (env "a" * env "b" * env "B" - env "a" ^ 2 * env "C") / env "b" ^ 2 := by
      field_simp
      linear_combination hrel
    rw [eA, hA]
    generalize (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m = P
    generalize (env "c" + env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ k = Q
    generalize (Real.sin (env "e" + env "f" * t))⁻¹ = Y
    field_simp
    ring

end OSR.IntegrationRec263
