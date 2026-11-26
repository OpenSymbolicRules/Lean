import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: a further split

Proof over ℝ and ℂ of RUBI 4.1.2.1 #23, the split
`(a + b sin u)^m (c + d sin u) = ((b c - a d) / b) (a + b sin u)^m + (d / b) (a + b sin u)^(m + 1)`.
-/

namespace OSR.IntegrationRec252

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)

/-! ## RUBI 4.1.2.1 #23 -/

theorem rubi4121r23Nondeg_real : rubi4121r23Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4121r23Nondeg.conditions rubi4121r23Nondeg.body
    rubi4121r23Nondeg.result rubi4121r23Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4121r23Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r23Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4121r23Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r23Nondeg, Defined, eval, Interp.real, hkm] at h
    simp only [ne_eq]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r23Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp only [ne_eq] at h
      simp [Defined, eval, Interp.real, hkm]
      exact h
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp only [ne_eq] at h
      simp [Defined, eval, Interp.real, em1]
      exact fun h' => h (by omega)
  · filter_upwards with w
    simp [rubi4121r23Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hb]
  · simp only [rubi4121r23Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Real.sin (env "e" + env "f" * t)) ^ m) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm]
    have hΦ2' : HasDerivAt (Φ "I2")
        ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, em1]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4121r23Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r23Nondeg.result) =
        fun w => (env "b" * env "c" - env "a" * env "d") * (env "b")⁻¹ * Φ "I1" w +
          env "d" * (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi4121r23Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
      ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi4121r23Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
          (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) := by
      simp [rubi4121r23Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have e1 : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
          (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ (hD t hF.self_of_nhds hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1]
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m = P
    field_simp
    ring

theorem rubi4121r23Nondeg_complex : rubi4121r23Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4121r23Nondeg.conditions rubi4121r23Nondeg.body
    rubi4121r23Nondeg.result rubi4121r23Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4121r23Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r23Nondeg, Defined, eval, Interp.complex, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4121r23Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r23Nondeg, Defined, eval, Interp.complex, hkm] at h
    simp only [ne_eq]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r23Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp only [ne_eq] at h
      simp [Defined, eval, Interp.complex, hkm]
      exact h
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp only [ne_eq] at h
      simp [Defined, eval, Interp.complex, em1]
      exact fun h' => h (by omega)
  · filter_upwards with w
    simp [rubi4121r23Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hb]
  · simp only [rubi4121r23Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ m) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkm]
    have hΦ2' : HasDerivAt (Φ "I2")
        ((env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, em1]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4121r23Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r23Nondeg.result) =
        fun w => (env "b" * env "c" - env "a" * env "d") * (env "b")⁻¹ * Φ "I1" w +
          env "d" * (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi4121r23Nondeg, eval, recEnv, Interp.complex, ivm1C, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
      ring
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4121r23Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
          (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) := by
      simp [rubi4121r23Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have e1 : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
          (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ (hD t hF.self_of_nhds hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1]
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = P
    field_simp
    ring

end OSR.IntegrationRec252
