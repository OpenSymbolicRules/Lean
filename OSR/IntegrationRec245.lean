import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: algebraic splits and quotients

Proofs over ℝ and ℂ of RUBI 4.1.2.1 #15 (`(b sin u)^m (c + d sin u)` split into
`c (b sin u)^m + (d / b) (b sin u)^(m + 1)`), 4.1.4.1 #1 (`(b sin u)^m (B sin u + C sin^2 u)`
as `(b sin u)^(m + 1) (B + C sin u) / b`) and 4.3.1.1 #5 (`(a + b tan u)^2`, using
`tan' = 1 / cos^2` and `sin^2 + cos^2 = 1`), and over ℝ only (no complex interpretation of
`transc1#sec` and `transc1#csc`) of 4.5.7 #6, 4.5.1.1 #17, 4.5.1.2 #45 and 4.5.1.2 #1, which
rewrite quotients by `a + b sec^2 u` and `a + b csc u` in terms of `cos` and `sin`; and over ℝ and
ℂ of the substitutions 4.3.4.1 #1 and #2, `u = b tan(e + f x)` and `u = b cot(e + f x)` in
`(a + b tan)^m (A + A tan^2)` and its `cot` analogue. -/

namespace OSR.IntegrationRec245

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

/-! ## RUBI 4.1.2.1 #15 -/

theorem rubi4121r15Nondeg_real : rubi4121r15Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4121r15Nondeg.conditions rubi4121r15Nondeg.body
    rubi4121r15Nondeg.result rubi4121r15Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4121r15Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r15Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4121r15Nondeg.body →
      (m < 0 → env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r15Nondeg, Defined, eval, Interp.real, hkm] at h
    simp only [ne_eq, mul_eq_zero, not_or]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp only [ne_eq, mul_eq_zero, not_or] at h
      simp [Defined, eval, Interp.real, hkm]
      exact h
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp only [ne_eq, mul_eq_zero, not_or] at h
      simp [Defined, eval, Interp.real, em1]
      exact fun h' => h (by omega)
  · filter_upwards with w
    simp [rubi4121r15Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hb]
  · simp only [rubi4121r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "b" * Real.sin (env "e" + env "f" * t)) ^ m) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm]
    have hΦ2' : HasDerivAt (Φ "I2")
        ((env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, em1]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4121r15Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r15Nondeg.result) =
        fun w => env "c" * Φ "I1" w + env "d" * (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi4121r15Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4121r15Nondeg.body =
        (env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
          (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) := by
      simp [rubi4121r15Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have e1 : (env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
          (env "b" * Real.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ (hD t hF.self_of_nhds hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1]
    generalize (env "b" * Real.sin (env "e" + env "f" * t)) ^ m = P
    field_simp

theorem rubi4121r15Nondeg_complex : rubi4121r15Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4121r15Nondeg.conditions rubi4121r15Nondeg.body
    rubi4121r15Nondeg.result rubi4121r15Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4121r15Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r15Nondeg, Defined, eval, Interp.complex, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4121r15Nondeg.body →
      (m < 0 → env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r15Nondeg, Defined, eval, Interp.complex, hkm] at h
    simp only [ne_eq, mul_eq_zero, not_or]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp only [ne_eq, mul_eq_zero, not_or] at h
      simp [Defined, eval, Interp.complex, hkm]
      exact h
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp only [ne_eq, mul_eq_zero, not_or] at h
      simp [Defined, eval, Interp.complex, em1]
      exact fun h' => h (by omega)
  · filter_upwards with w
    simp [rubi4121r15Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hb]
  · simp only [rubi4121r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "b" * Complex.sin (env "e" + env "f" * t)) ^ m) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkm]
    have hΦ2' : HasDerivAt (Φ "I2")
        ((env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, em1]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4121r15Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r15Nondeg.result) =
        fun w => env "c" * Φ "I1" w + env "d" * (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi4121r15Nondeg, eval, recEnv, Interp.complex, ivm1C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4121r15Nondeg.body =
        (env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
          (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) := by
      simp [rubi4121r15Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have e1 : (env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
          (env "b" * Complex.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ (hD t hF.self_of_nhds hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1]
    generalize (env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = P
    field_simp

/-! ## RUBI 4.1.4.1 #1 -/

theorem rubi4141r1Nondeg_real : rubi4141r1Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4141r1Nondeg.conditions rubi4141r1Nondeg.body
    rubi4141r1Nondeg.result rubi4141r1Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4141r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r1Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4141r1Nondeg.body →
      (m < 0 → env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r1Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
    simp only [ne_eq, mul_eq_zero, not_or]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp only [ne_eq, mul_eq_zero, not_or] at h
    simp [Defined, eval, Interp.real, em1]
    exact fun h' => h (by omega)
  · filter_upwards with w
    simp [rubi4141r1Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hb]
  · simp only [rubi4141r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) *
        (env "B" + env "C" * Real.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4141r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r1Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4141r1Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4141r1Nondeg.body =
        (env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
          (env "B" * Real.sin (env "e" + env "f" * t) +
            env "C" * Real.sin (env "e" + env "f" * t) ^ 2) := by
      simp [rubi4141r1Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have e1 : (env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
          (env "b" * Real.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ (hD t hF.self_of_nhds hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1]
    generalize (env "b" * Real.sin (env "e" + env "f" * t)) ^ m = P
    field_simp

theorem rubi4141r1Nondeg_complex : rubi4141r1Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4141r1Nondeg.conditions rubi4141r1Nondeg.body
    rubi4141r1Nondeg.result rubi4141r1Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4141r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r1Nondeg, Defined, eval, Interp.complex, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4141r1Nondeg.body →
      (m < 0 → env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r1Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
    simp only [ne_eq, mul_eq_zero, not_or]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp only [ne_eq, mul_eq_zero, not_or] at h
    simp [Defined, eval, Interp.complex, em1]
    exact fun h' => h (by omega)
  · filter_upwards with w
    simp [rubi4141r1Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hb]
  · simp only [rubi4141r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) *
        (env "B" + env "C" * Complex.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4141r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r1Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4141r1Nondeg, eval, recEnv, Interp.complex, ivm1C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4141r1Nondeg.body =
        (env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
          (env "B" * Complex.sin (env "e" + env "f" * t) +
            env "C" * Complex.sin (env "e" + env "f" * t) ^ 2) := by
      simp [rubi4141r1Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have e1 : (env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
          (env "b" * Complex.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ (hD t hF.self_of_nhds hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1]
    generalize (env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = P
    field_simp

/-! ## RUBI 4.3.1.1 #5 -/

theorem rubi4311r5Nondeg_real : rubi4311r5Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4311r5Nondeg.conditions rubi4311r5Nondeg.body
    rubi4311r5Nondeg.result rubi4311r5Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4311r5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4311r5Nondeg.body →
      Real.cos (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simpa [rubi4311r5Nondeg, Defined, eval, Interp.real, iv2R] using h
  have hc0 := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4311r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simpa [Defined, eval, Interp.real] using hD w hw
  · filter_upwards [hF] with w hw
    simp [rubi4311r5Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hd, hD w hw]
  · simp only [rubi4311r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (Real.tan (env "c" + env "d" * t)) t := by
      convert hΦ using 1
      simp [eval, Interp.real]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4311r5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4311r5Nondeg.result) =
        fun w => (env "a" ^ 2 - env "b" ^ 2) * w +
          env "b" ^ 2 * Real.tan (env "c" + env "d" * w) * (env "d")⁻¹ +
          2 * env "a" * env "b" * Φ "I1" w := by
      funext w
      simp [rubi4311r5Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
      ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi4311r5Nondeg.body =
        (env "a" + env "b" * Real.tan (env "c" + env "d" * t)) ^ 2 := by
      simp [rubi4311r5Nondeg, eval, Interp.real, iv2R]
    rw [hfun, hEF]
    have hL : HasDerivAt (fun w => env "c" + env "d" * w) (env "d") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "d")).const_add (env "c")
    have hT := (Real.hasDerivAt_tan hc0).comp t hL
    refine ((((hasDerivAt_id t).const_mul _).add ((hT.const_mul _).mul_const _)).add
      (hΦ'.const_mul _)).congr_deriv ?_
    have hsc := Real.sin_sq_add_cos_sq (env "c" + env "d" * t)
    rw [Real.tan_eq_sin_div_cos]
    generalize Real.sin (env "c" + env "d" * t) = S at hsc ⊢
    generalize Real.cos (env "c" + env "d" * t) = C at hc0 hsc ⊢
    field_simp
    linear_combination (-(env "b") ^ 2) * hsc

theorem rubi4311r5Nondeg_complex : rubi4311r5Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4311r5Nondeg.conditions rubi4311r5Nondeg.body
    rubi4311r5Nondeg.result rubi4311r5Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4311r5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4311r5Nondeg.body →
      Complex.cos (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simpa [rubi4311r5Nondeg, Defined, eval, Interp.complex, iv2C] using h
  have hc0 := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4311r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simpa [Defined, eval, Interp.complex] using hD w hw
  · filter_upwards [hF] with w hw
    simp [rubi4311r5Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, hd, hD w hw]
  · simp only [rubi4311r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (Complex.tan (env "c" + env "d" * t)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4311r5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4311r5Nondeg.result) =
        fun w => (env "a" ^ 2 - env "b" ^ 2) * w +
          env "b" ^ 2 * Complex.tan (env "c" + env "d" * w) * (env "d")⁻¹ +
          2 * env "a" * env "b" * Φ "I1" w := by
      funext w
      simp [rubi4311r5Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
      ring
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4311r5Nondeg.body =
        (env "a" + env "b" * Complex.tan (env "c" + env "d" * t)) ^ 2 := by
      simp [rubi4311r5Nondeg, eval, Interp.complex, iv2C]
    rw [hfun, hEF]
    have hL : HasDerivAt (fun w => env "c" + env "d" * w) (env "d") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "d")).const_add (env "c")
    have hT := (Complex.hasDerivAt_tan hc0).comp t hL
    refine ((((hasDerivAt_id t).const_mul _).add ((hT.const_mul _).mul_const _)).add
      (hΦ'.const_mul _)).congr_deriv ?_
    have hsc := Complex.sin_sq_add_cos_sq (env "c" + env "d" * t)
    rw [Complex.tan_eq_sin_div_cos]
    generalize Complex.sin (env "c" + env "d" * t) = S at hsc ⊢
    generalize Complex.cos (env "c" + env "d" * t) = C at hc0 hsc ⊢
    field_simp
    linear_combination (-(env "b") ^ 2) * hsc

/-! ## RUBI 4.5.7 #6 -/

theorem rubi457r6Nondeg_real : rubi457r6Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi457r6Nondeg.conditions rubi457r6Nondeg.body
    rubi457r6Nondeg.result rubi457r6Nondeg.integrals
  intro env hc t hF
  have ha : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi457r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi457r6Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧
        env "b" + env "a" * Real.cos (env "e" + env "f" * w) ^ 2 ≠ 0 := by
    intro w h
    simp [rubi457r6Nondeg, Defined, eval, Interp.real, ivm1R, iv2R, Fn.sec] at h
    obtain ⟨hcw, hne⟩ := h
    refine ⟨hcw, ?_⟩
    intro h0
    apply hne
    have hC2 : Real.cos (env "e" + env "f" * w) ^ 2 ≠ 0 := pow_ne_zero 2 hcw
    field_simp
    linear_combination h0
  obtain ⟨hc0, hq0⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi457r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simpa [Defined, eval, Interp.real, ivm1R, iv2R] using (hD w hw).2
  · filter_upwards with w
    simp [rubi457r6Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, ha]
  · simp only [rubi457r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "b" + env "a" * Real.cos (env "e" + env "f" * t) ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, ivm1R, iv2R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi457r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi457r6Nondeg.result) =
        fun w => w * (env "a")⁻¹ + -(env "b" * (env "a")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi457r6Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi457r6Nondeg.body =
        (env "a" + env "b" * ((Real.cos (env "e" + env "f" * t))⁻¹) ^ 2)⁻¹ := by
      simp [rubi457r6Nondeg, eval, Interp.real, ivm1R, iv2R, Fn.sec]
    rw [hfun, hEF]
    refine (((hasDerivAt_id t).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    generalize Real.cos (env "e" + env "f" * t) = C at hc0 hq0 ⊢
    have hC2 : C ^ 2 ≠ 0 := pow_ne_zero 2 hc0
    rw [show env "a" + env "b" * (C⁻¹) ^ 2 = (env "b" + env "a" * C ^ 2) / C ^ 2 by
      field_simp; ring]
    generalize hE : env "b" + env "a" * C ^ 2 = D at hq0 ⊢
    field_simp
    rw [← hE]
    ring

/-! ## RUBI 4.5.1.1 #17 -/

theorem rubi4511r17Nondeg_real : rubi4511r17Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4511r17Nondeg.conditions rubi4511r17Nondeg.body
    rubi4511r17Nondeg.result rubi4511r17Nondeg.integrals
  intro env hc t hF
  have ha : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi4511r17Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4511r17Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4511r17Nondeg.body →
      Real.sin (env "c" + env "d" * w) ≠ 0 ∧
        1 + env "a" * (env "b")⁻¹ * Real.sin (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi4511r17Nondeg, Defined, eval, Interp.real, ivm1R, Fn.csc] at h
    obtain ⟨hsw, hne⟩ := h
    refine ⟨hsw, ?_⟩
    intro h0
    apply hne
    field_simp
    field_simp at h0
    linear_combination h0
  obtain ⟨hs0, hq0⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4511r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simpa [Defined, eval, Interp.real, ivm1R, hb] using (hD w hw).2
  · filter_upwards with w
    simp [rubi4511r17Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, ha]
  · simp only [rubi4511r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((1 + env "a" * (env "b")⁻¹ * Real.sin (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4511r17Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4511r17Nondeg.result) =
        fun w => w * (env "a")⁻¹ + -(env "a")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4511r17Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4511r17Nondeg.body =
        (env "a" + env "b" * (Real.sin (env "c" + env "d" * t))⁻¹)⁻¹ := by
      simp [rubi4511r17Nondeg, eval, Interp.real, ivm1R, Fn.csc]
    rw [hfun, hEF]
    refine (((hasDerivAt_id t).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    generalize Real.sin (env "c" + env "d" * t) = S at hs0 hq0 ⊢
    have hq1 : env "b" + env "a" * S ≠ 0 := by
      intro h0; apply hq0; field_simp; linear_combination h0
    rw [show 1 + env "a" * (env "b")⁻¹ * S = (env "b" + env "a" * S) / env "b" by
      field_simp]
    rw [show env "a" + env "b" * S⁻¹ = (env "b" + env "a" * S) / S by field_simp; ring]
    generalize hE : env "b" + env "a" * S = D at hq1 ⊢
    field_simp
    rw [← hE]
    ring

/-! ## RUBI 4.5.1.2 #45 -/

theorem rubi4512r45Nondeg_real : rubi4512r45Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4512r45Nondeg.conditions rubi4512r45Nondeg.body
    rubi4512r45Nondeg.result rubi4512r45Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4512r45Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4512r45Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
        1 + env "a" * (env "b")⁻¹ * Real.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4512r45Nondeg, Defined, eval, Interp.real, ivm1R, Fn.csc] at h
    obtain ⟨hsw, hne⟩ := h
    refine ⟨hsw, ?_⟩
    intro h0
    apply hne
    field_simp
    field_simp at h0
    linear_combination h0
  obtain ⟨hs0, hq0⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4512r45Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simpa [Defined, eval, Interp.real, ivm1R, hb] using (hD w hw).2
  · filter_upwards with w
    simp [rubi4512r45Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hb]
  · simp only [rubi4512r45Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((1 + env "a" * (env "b")⁻¹ * Real.sin (env "e" + env "f" * t))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4512r45Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4512r45Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4512r45Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4512r45Nondeg.body =
        (Real.sin (env "e" + env "f" * t))⁻¹ *
          (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹)⁻¹ := by
      simp [rubi4512r45Nondeg, eval, Interp.real, ivm1R, Fn.csc]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    generalize Real.sin (env "e" + env "f" * t) = S at hs0 hq0 ⊢
    have hq1 : env "b" + env "a" * S ≠ 0 := by
      intro h0; apply hq0; field_simp; linear_combination h0
    rw [show 1 + env "a" * (env "b")⁻¹ * S = (env "b" + env "a" * S) / env "b" by
      field_simp]
    rw [show env "a" + env "b" * S⁻¹ = (env "b" + env "a" * S) / S by field_simp; ring]
    generalize hE : env "b" + env "a" * S = D at hq1 ⊢
    field_simp

/-! ## RUBI 4.5.1.2 #1 -/

theorem rubi4512r1Nondeg_real : rubi4512r1Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4512r1Nondeg.conditions rubi4512r1Nondeg.body
    rubi4512r1Nondeg.result rubi4512r1Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4512r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4512r1Nondeg, Defined, eval, Interp.real, hkn] at h
  have en1 : intValue? (env "n" + 1) = some (n + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkn]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4512r1Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4512r1Nondeg, Defined, eval, Interp.real, hkn, Fn.csc] at h
    tauto
  have hs0 := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4512r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.real, hkn, Fn.csc, hd, hD w hw]
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.real, en1, Fn.csc, hd, hD w hw]
  · filter_upwards with w
    simp [rubi4512r1Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hd]
  · simp only [rubi4512r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1")
        ((env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ n) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkn, Fn.csc]
    have hΦ2' : HasDerivAt (Φ "I2")
        ((env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ (n + 1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, en1, Fn.csc]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4512r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4512r1Nondeg.result) =
        fun w => env "a" * Φ "I1" w + env "b" * (env "d")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi4512r1Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4512r1Nondeg.body =
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) *
          (env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ n := by
      simp [rubi4512r1Nondeg, eval, Interp.real, hkn, Fn.csc]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hK : env "d" * (Real.sin (env "e" + env "f" * t))⁻¹ ≠ 0 :=
      mul_ne_zero hd (inv_ne_zero hs0)
    rw [zpow_add_one₀ hK]
    generalize (env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ n = P
    generalize Real.sin (env "e" + env "f" * t) = S at hs0 hK ⊢
    field_simp

/-! ## RUBI 4.3.4.1 #1 -/

theorem rubi4341r1Nondeg_real : rubi4341r1Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi4341r1Nondeg.conditions
    rubi4341r1Nondeg.body rubi4341r1Nondeg.result rubi4341r1Nondeg.integrals
    rubi4341r1Nondeg.substs
  intro env hc t hF
  have hAC : env "A" = env "C" := by
    have h := hc (.eq (.var "A") (.var "C")) (by simp [rubi4341r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW : env "b" * env "f" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.var "f")) (.int 0)) (by simp [rubi4341r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4341r1Nondeg, Defined, eval, Interp.real, hkm] at h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4341r1Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧
        (m < 0 → env "a" + env "b" * Real.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4341r1Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
    tauto
  obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
  have hnear : ∀ᶠ u : ℝ in 𝓝 (env "b" * Real.tan (env "e" + env "f" * t)),
      m < 0 → env "a" + u ≠ 0 := by
    by_cases hm : m < 0
    · have hcont : ContinuousAt (fun u : ℝ => env "a" + u)
          (env "b" * Real.tan (env "e" + env "f" * t)) := by fun_prop
      filter_upwards [hcont.tendsto.eventually (eventually_ne_nhds (hA0 hm))] with u hu
      exact fun _ => hu
    · exact Filter.Eventually.of_forall fun _ h => absurd h hm
  have hsub : substAt Interp.real env rubi4341r1Nondeg.substs "x" "I1" t =
      env "b" * Real.tan (env "e" + env "f" * t) := by
    simp [rubi4341r1Nondeg, substAt, eval, Interp.real]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi4341r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards [hF] with w hw
      intro g hg
      simp only [rubi4341r1Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined, eval, Interp.real, (hD w hw).1]
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simpa [Defined, eval, Interp.real, hkm] using hu
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi4341r1Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hW]
    · simp only [rubi4341r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m)
          (env "b" * Real.tan (env "e" + env "f" * t)) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkm]
      have hL : HasDerivAt (fun w => env "e" + env "f" * w) (env "f") t := by
        simpa using ((hasDerivAt_id t).const_mul (env "f")).const_add (env "e")
      have hT := ((Real.hasDerivAt_tan hc0).comp t hL).const_mul (env "b")
      have h := (hΦ'.comp t hT).const_mul (env "A" * (env "b" * env "f")⁻¹)
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi4341r1Nondeg.integrals.map (·.1))
            rubi4341r1Nondeg.substs Φ "x" w) rubi4341r1Nondeg.result) =
          fun w => env "A" * (env "b" * env "f")⁻¹ *
            Φ "I1" (env "b" * Real.tan (env "e" + env "f" * w)) := by
        funext w
        simp [rubi4341r1Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      refine h.congr_deriv ?_
      have hEF : eval Interp.real (Function.update env "x" t) rubi4341r1Nondeg.body =
          (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m *
            (env "A" + env "C" * Real.tan (env "e" + env "f" * t) ^ 2) := by
        simp [rubi4341r1Nondeg, eval, Interp.real, hkm, iv2R]
      rw [hEF, ← hAC]
      have hsc := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
      have hb : env "b" ≠ 0 := left_ne_zero_of_mul hW
      have hf : env "f" ≠ 0 := right_ne_zero_of_mul hW
      rw [Real.tan_eq_sin_div_cos]
      generalize (env "a" + env "b" * (Real.sin (env "e" + env "f" * t) /
        Real.cos (env "e" + env "f" * t))) ^ m = P
      generalize Real.sin (env "e" + env "f" * t) = S at hsc ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hc0 hsc ⊢
      field_simp
      linear_combination (-(env "A" * P)) * hsc

theorem rubi4341r1Nondeg_complex : rubi4341r1Nondeg.Holds .complex := by
  show AntiderivSubstHolds Interp.complex "x" rubi4341r1Nondeg.conditions
    rubi4341r1Nondeg.body rubi4341r1Nondeg.result rubi4341r1Nondeg.integrals
    rubi4341r1Nondeg.substs
  intro env hc t hF
  have hAC : env "A" = env "C" := by
    have h := hc (.eq (.var "A") (.var "C")) (by simp [rubi4341r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW : env "b" * env "f" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.var "f")) (.int 0)) (by simp [rubi4341r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4341r1Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4341r1Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧
        (m < 0 → env "a" + env "b" * Complex.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4341r1Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
    tauto
  obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
  have hnear : ∀ᶠ u : ℂ in 𝓝 (env "b" * Complex.tan (env "e" + env "f" * t)),
      m < 0 → env "a" + u ≠ 0 := by
    by_cases hm : m < 0
    · have hcont : ContinuousAt (fun u : ℂ => env "a" + u)
          (env "b" * Complex.tan (env "e" + env "f" * t)) := by fun_prop
      filter_upwards [hcont.tendsto.eventually (eventually_ne_nhds (hA0 hm))] with u hu
      exact fun _ => hu
    · exact Filter.Eventually.of_forall fun _ h => absurd h hm
  have hsub : substAt Interp.complex env rubi4341r1Nondeg.substs "x" "I1" t =
      env "b" * Complex.tan (env "e" + env "f" * t) := by
    simp [rubi4341r1Nondeg, substAt, eval, Interp.complex]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi4341r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards [hF] with w hw
      intro g hg
      simp only [rubi4341r1Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined, eval, Interp.complex, (hD w hw).1]
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simpa [Defined, eval, Interp.complex, hkm] using hu
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi4341r1Nondeg, Defined, eval, Interp.complex, substEnv, ivm1C, hW]
    · simp only [rubi4341r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m)
          (env "b" * Complex.tan (env "e" + env "f" * t)) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.complex, hkm]
      have hL : HasDerivAt (fun w => env "e" + env "f" * w) (env "f") t := by
        simpa using ((hasDerivAt_id t).const_mul (env "f")).const_add (env "e")
      have hT := ((Complex.hasDerivAt_tan hc0).comp t hL).const_mul (env "b")
      have h := (hΦ'.comp t hT).const_mul (env "A" * (env "b" * env "f")⁻¹)
      have hfun : (fun w => eval Interp.complex
          (substEnv Interp.complex env (rubi4341r1Nondeg.integrals.map (·.1))
            rubi4341r1Nondeg.substs Φ "x" w) rubi4341r1Nondeg.result) =
          fun w => env "A" * (env "b" * env "f")⁻¹ *
            Φ "I1" (env "b" * Complex.tan (env "e" + env "f" * w)) := by
        funext w
        simp [rubi4341r1Nondeg, substEnv, substAt, eval, Interp.complex, ivm1C]
      rw [hfun]
      refine h.congr_deriv ?_
      have hEF : eval Interp.complex (Function.update env "x" t) rubi4341r1Nondeg.body =
          (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m *
            (env "A" + env "C" * Complex.tan (env "e" + env "f" * t) ^ 2) := by
        simp [rubi4341r1Nondeg, eval, Interp.complex, hkm, iv2C]
      rw [hEF, ← hAC]
      have hsc := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
      have hb : env "b" ≠ 0 := left_ne_zero_of_mul hW
      have hf : env "f" ≠ 0 := right_ne_zero_of_mul hW
      rw [Complex.tan_eq_sin_div_cos]
      generalize (env "a" + env "b" * (Complex.sin (env "e" + env "f" * t) /
        Complex.cos (env "e" + env "f" * t))) ^ m = P
      generalize Complex.sin (env "e" + env "f" * t) = S at hsc ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hc0 hsc ⊢
      field_simp
      linear_combination (-(env "A" * P)) * hsc

/-! ## RUBI 4.3.4.1 #2 -/

private theorem hasDerivAt_cot_lin_Real {e f t : ℝ} (hs : Real.sin (e + f * t) ≠ 0) :
    HasDerivAt (fun w => Real.cot (e + f * w)) (-f / Real.sin (e + f * t) ^ 2) t := by
  have hL : HasDerivAt (fun w => e + f * w) f t := by
    simpa using ((hasDerivAt_id t).const_mul f).const_add e
  have h := ((Real.hasDerivAt_cos (e + f * t)).div (Real.hasDerivAt_sin (e + f * t)) hs).comp
    t hL
  have hf : (fun w => Real.cot (e + f * w)) =
      (Real.cos / Real.sin) ∘ fun w => e + f * w := by
    funext v; simp [Real.cot_eq_cos_div_sin]
  rw [hf]
  refine h.congr_deriv ?_
  have := Real.sin_sq_add_cos_sq (e + f * t)
  field_simp
  linear_combination -f * this

private theorem hasDerivAt_cot_lin_Complex {e f t : ℂ} (hs : Complex.sin (e + f * t) ≠ 0) :
    HasDerivAt (fun w => Complex.cot (e + f * w)) (-f / Complex.sin (e + f * t) ^ 2) t := by
  have hL : HasDerivAt (fun w => e + f * w) f t := by
    simpa using ((hasDerivAt_id t).const_mul f).const_add e
  have h := ((Complex.hasDerivAt_cos (e + f * t)).div (Complex.hasDerivAt_sin (e + f * t)) hs).comp
    t hL
  have hf : (fun w => Complex.cot (e + f * w)) =
      (Complex.cos / Complex.sin) ∘ fun w => e + f * w := by
    funext v; simp [Complex.cot_eq_cos_div_sin]
  rw [hf]
  refine h.congr_deriv ?_
  have := Complex.sin_sq_add_cos_sq (e + f * t)
  field_simp
  linear_combination -f * this

theorem rubi4341r2Nondeg_real : rubi4341r2Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi4341r2Nondeg.conditions
    rubi4341r2Nondeg.body rubi4341r2Nondeg.result rubi4341r2Nondeg.integrals
    rubi4341r2Nondeg.substs
  intro env hc t hF
  have hAC : env "A" = env "C" := by
    have h := hc (.eq (.var "A") (.var "C")) (by simp [rubi4341r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW : env "b" * env "f" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.var "f")) (.int 0)) (by simp [rubi4341r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4341r2Nondeg, Defined, eval, Interp.real, hkm] at h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4341r2Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
        (m < 0 → env "a" + env "b" * Real.cot (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4341r2Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
    tauto
  obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
  have hnear : ∀ᶠ u : ℝ in 𝓝 (env "b" * Real.cot (env "e" + env "f" * t)),
      m < 0 → env "a" + u ≠ 0 := by
    by_cases hm : m < 0
    · have hcont : ContinuousAt (fun u : ℝ => env "a" + u)
          (env "b" * Real.cot (env "e" + env "f" * t)) := by fun_prop
      filter_upwards [hcont.tendsto.eventually (eventually_ne_nhds (hA0 hm))] with u hu
      exact fun _ => hu
    · exact Filter.Eventually.of_forall fun _ h => absurd h hm
  have hsub : substAt Interp.real env rubi4341r2Nondeg.substs "x" "I1" t =
      env "b" * Real.cot (env "e" + env "f" * t) := by
    simp [rubi4341r2Nondeg, substAt, eval, Interp.real]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi4341r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards [hF] with w hw
      intro g hg
      simp only [rubi4341r2Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined, eval, Interp.real, (hD w hw).1]
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simpa [Defined, eval, Interp.real, hkm] using hu
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi4341r2Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hW]
    · simp only [rubi4341r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "a" + env "b" * Real.cot (env "e" + env "f" * t)) ^ m)
          (env "b" * Real.cot (env "e" + env "f" * t)) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkm]
      have hL : HasDerivAt (fun w => env "e" + env "f" * w) (env "f") t := by
        simpa using ((hasDerivAt_id t).const_mul (env "f")).const_add (env "e")
      have hT := (hasDerivAt_cot_lin_Real hc0).const_mul (env "b")
      have h := (hΦ'.comp t hT).const_mul (-env "A" * (env "b" * env "f")⁻¹)
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi4341r2Nondeg.integrals.map (·.1))
            rubi4341r2Nondeg.substs Φ "x" w) rubi4341r2Nondeg.result) =
          fun w => -env "A" * (env "b" * env "f")⁻¹ *
            Φ "I1" (env "b" * Real.cot (env "e" + env "f" * w)) := by
        funext w
        simp [rubi4341r2Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      refine h.congr_deriv ?_
      have hEF : eval Interp.real (Function.update env "x" t) rubi4341r2Nondeg.body =
          (env "a" + env "b" * Real.cot (env "e" + env "f" * t)) ^ m *
            (env "A" + env "C" * Real.cot (env "e" + env "f" * t) ^ 2) := by
        simp [rubi4341r2Nondeg, eval, Interp.real, hkm, iv2R]
      rw [hEF, ← hAC]
      have hsc := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
      have hb : env "b" ≠ 0 := left_ne_zero_of_mul hW
      have hf : env "f" ≠ 0 := right_ne_zero_of_mul hW
      rw [Real.cot_eq_cos_div_sin]
      generalize (env "a" + env "b" * (Real.cos (env "e" + env "f" * t) /
        Real.sin (env "e" + env "f" * t))) ^ m = P
      generalize Real.sin (env "e" + env "f" * t) = S at hc0 hsc ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hsc ⊢
      field_simp
      linear_combination (-(env "A" * P)) * hsc

theorem rubi4341r2Nondeg_complex : rubi4341r2Nondeg.Holds .complex := by
  show AntiderivSubstHolds Interp.complex "x" rubi4341r2Nondeg.conditions
    rubi4341r2Nondeg.body rubi4341r2Nondeg.result rubi4341r2Nondeg.integrals
    rubi4341r2Nondeg.substs
  intro env hc t hF
  have hAC : env "A" = env "C" := by
    have h := hc (.eq (.var "A") (.var "C")) (by simp [rubi4341r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW : env "b" * env "f" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.var "f")) (.int 0)) (by simp [rubi4341r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4341r2Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4341r2Nondeg.body →
      Complex.sin (env "e" + env "f" * w) ≠ 0 ∧
        (m < 0 → env "a" + env "b" * Complex.cot (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4341r2Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
    tauto
  obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
  have hnear : ∀ᶠ u : ℂ in 𝓝 (env "b" * Complex.cot (env "e" + env "f" * t)),
      m < 0 → env "a" + u ≠ 0 := by
    by_cases hm : m < 0
    · have hcont : ContinuousAt (fun u : ℂ => env "a" + u)
          (env "b" * Complex.cot (env "e" + env "f" * t)) := by fun_prop
      filter_upwards [hcont.tendsto.eventually (eventually_ne_nhds (hA0 hm))] with u hu
      exact fun _ => hu
    · exact Filter.Eventually.of_forall fun _ h => absurd h hm
  have hsub : substAt Interp.complex env rubi4341r2Nondeg.substs "x" "I1" t =
      env "b" * Complex.cot (env "e" + env "f" * t) := by
    simp [rubi4341r2Nondeg, substAt, eval, Interp.complex]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi4341r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards [hF] with w hw
      intro g hg
      simp only [rubi4341r2Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined, eval, Interp.complex, (hD w hw).1]
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simpa [Defined, eval, Interp.complex, hkm] using hu
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi4341r2Nondeg, Defined, eval, Interp.complex, substEnv, ivm1C, hW]
    · simp only [rubi4341r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "a" + env "b" * Complex.cot (env "e" + env "f" * t)) ^ m)
          (env "b" * Complex.cot (env "e" + env "f" * t)) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.complex, hkm]
      have hL : HasDerivAt (fun w => env "e" + env "f" * w) (env "f") t := by
        simpa using ((hasDerivAt_id t).const_mul (env "f")).const_add (env "e")
      have hT := (hasDerivAt_cot_lin_Complex hc0).const_mul (env "b")
      have h := (hΦ'.comp t hT).const_mul (-env "A" * (env "b" * env "f")⁻¹)
      have hfun : (fun w => eval Interp.complex
          (substEnv Interp.complex env (rubi4341r2Nondeg.integrals.map (·.1))
            rubi4341r2Nondeg.substs Φ "x" w) rubi4341r2Nondeg.result) =
          fun w => -env "A" * (env "b" * env "f")⁻¹ *
            Φ "I1" (env "b" * Complex.cot (env "e" + env "f" * w)) := by
        funext w
        simp [rubi4341r2Nondeg, substEnv, substAt, eval, Interp.complex, ivm1C]
      rw [hfun]
      refine h.congr_deriv ?_
      have hEF : eval Interp.complex (Function.update env "x" t) rubi4341r2Nondeg.body =
          (env "a" + env "b" * Complex.cot (env "e" + env "f" * t)) ^ m *
            (env "A" + env "C" * Complex.cot (env "e" + env "f" * t) ^ 2) := by
        simp [rubi4341r2Nondeg, eval, Interp.complex, hkm, iv2C]
      rw [hEF, ← hAC]
      have hsc := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
      have hb : env "b" ≠ 0 := left_ne_zero_of_mul hW
      have hf : env "f" ≠ 0 := right_ne_zero_of_mul hW
      rw [Complex.cot_eq_cos_div_sin]
      generalize (env "a" + env "b" * (Complex.cos (env "e" + env "f" * t) /
        Complex.sin (env "e" + env "f" * t))) ^ m = P
      generalize Complex.sin (env "e" + env "f" * t) = S at hc0 hsc ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hsc ⊢
      field_simp
      linear_combination (-(env "A" * P)) * hsc

end OSR.IntegrationRec245
