import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: quadratic numerators and partial fractions

Proofs over ℝ and ℂ of RUBI 4.1.4.1 #6 and 4.3.4.1 #3 (`(a + b y)^m (A + B y + C y^2)` as
`(a + b y)^(m + 1) (b B - a C + b C y) / b^2` when `A b^2 - a b B + a^2 C = 0`, with `y = sin` or
`tan`), 4.1.2.2 #35, 4.1.5 #31 and #32 (partial fractions of `1 / (cos u (a cos u + b sin u))`
and of its `sin` analogue, using `sin^2 + cos^2 = 1`) 4.1.10 #8 (the addition formula for
`sin(e + f x) / (c + d x)`) and 4.1.2.2 #47 and #83 (`(a + b sin u)(a - b sin u) = b^2 cos^2 u`
when `a^2 = b^2`), and over ℝ only of the `csc` analogue 4.5.4.1 #1. -/

namespace OSR.IntegrationRec254

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

/-! ## RUBI 4.1.4.1 #6, 4.3.4.1 #3 and 4.5.4.1 #1 -/

theorem rubi4141r6Nondeg_real : rubi4141r6Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4141r6Nondeg.conditions rubi4141r6Nondeg.body
    rubi4141r6Nondeg.result rubi4141r6Nondeg.integrals
  intro env hc t hF
  have hb2 : env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4141r6Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hb : env "b" ≠ 0 := fun h => hb2 (by rw [h]; ring)
  have hrel : env "A" * env "b" ^ 2 - env "a" * env "b" * env "B" + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2)))
      (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B")))
      (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4141r6Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hA : env "A" = (env "a" * env "b" * env "B" - env "a" ^ 2 * env "C") / env "b" ^ 2 := by
    field_simp; linear_combination hrel
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r6Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4141r6Nondeg.body →
      True ∧ (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r6Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := (hD w hw).2
    simp [Defined, eval, Interp.real, em1] at h ⊢
    exact fun h' => h (by omega)
  · filter_upwards with w
    simp [rubi4141r6Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hb]
  · simp only [rubi4141r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m +
        1) *
        (env "b" * env "B" - env "a" * env "C" + env "b" * env "C" *
            Real.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4141r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r6Nondeg.result) = fun w => (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4141r6Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4141r6Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
            (env "A" + env "B" * Real.sin (env "e" + env "f" * t) + env "C" *
            (Real.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4141r6Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have e1 : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1, hA]
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m = Q
    field_simp
    ring

theorem rubi4141r6Nondeg_complex : rubi4141r6Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4141r6Nondeg.conditions rubi4141r6Nondeg.body
    rubi4141r6Nondeg.result rubi4141r6Nondeg.integrals
  intro env hc t hF
  have hb2 : env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4141r6Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  have hb : env "b" ≠ 0 := fun h => hb2 (by rw [h]; ring)
  have hrel : env "A" * env "b" ^ 2 - env "a" * env "b" * env "B" + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2)))
      (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B")))
      (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4141r6Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hA : env "A" = (env "a" * env "b" * env "B" - env "a" ^ 2 * env "C") / env "b" ^ 2 := by
    field_simp; linear_combination hrel
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r6Nondeg, Defined, eval, Interp.complex, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4141r6Nondeg.body →
      True ∧ (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r6Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := (hD w hw).2
    simp [Defined, eval, Interp.complex, em1] at h ⊢
    exact fun h' => h (by omega)
  · filter_upwards with w
    simp [rubi4141r6Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, hb]
  · simp only [rubi4141r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ (m + 1) *
        (env "b" * env "B" - env "a" * env "C" + env "b" * env "C" *
            Complex.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4141r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r6Nondeg.result) = fun w => (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4141r6Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4141r6Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
            (env "A" + env "B" * Complex.sin (env "e" + env "f" * t) + env "C" *
            (Complex.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4141r6Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have e1 : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1, hA]
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = Q
    field_simp
    ring

theorem rubi4341r3Nondeg_real : rubi4341r3Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4341r3Nondeg.conditions rubi4341r3Nondeg.body
    rubi4341r3Nondeg.result rubi4341r3Nondeg.integrals
  intro env hc t hF
  have hb2 : env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4341r3Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hb : env "b" ≠ 0 := fun h => hb2 (by rw [h]; ring)
  have hrel : env "A" * env "b" ^ 2 - env "a" * env "b" * env "B" + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2)))
      (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B")))
      (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4341r3Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hA : env "A" = (env "a" * env "b" * env "B" - env "a" ^ 2 * env "C") / env "b" ^ 2 := by
    field_simp; linear_combination hrel
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4341r3Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4341r3Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Real.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4341r3Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r3Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := (hD w hw).2
    simp [Defined, eval, Interp.real, em1, (hD w hw).1] at h ⊢
    exact fun h' => h (by omega)
  · filter_upwards with w
    simp [rubi4341r3Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hb]
  · simp only [rubi4341r3Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ (m +
        1) *
        (env "b" * env "B" - env "a" * env "C" + env "b" * env "C" *
            Real.tan (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4341r3Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4341r3Nondeg.result) = fun w => (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4341r3Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4341r3Nondeg.body =
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m *
            (env "A" + env "B" * Real.tan (env "e" + env "f" * t) + env "C" *
            (Real.tan (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4341r3Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have e1 : (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1, hA]
    generalize (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m = Q
    field_simp
    ring

theorem rubi4341r3Nondeg_complex : rubi4341r3Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4341r3Nondeg.conditions rubi4341r3Nondeg.body
    rubi4341r3Nondeg.result rubi4341r3Nondeg.integrals
  intro env hc t hF
  have hb2 : env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4341r3Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  have hb : env "b" ≠ 0 := fun h => hb2 (by rw [h]; ring)
  have hrel : env "A" * env "b" ^ 2 - env "a" * env "b" * env "B" + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2)))
      (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B")))
      (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4341r3Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hA : env "A" = (env "a" * env "b" * env "B" - env "a" ^ 2 * env "C") / env "b" ^ 2 := by
    field_simp; linear_combination hrel
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4341r3Nondeg, Defined, eval, Interp.complex, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4341r3Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Complex.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4341r3Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r3Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := (hD w hw).2
    simp [Defined, eval, Interp.complex, em1, (hD w hw).1] at h ⊢
    exact fun h' => h (by omega)
  · filter_upwards with w
    simp [rubi4341r3Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, hb]
  · simp only [rubi4341r3Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.tan (env "e" + env "f" * t)) ^ (m + 1) *
        (env "b" * env "B" - env "a" * env "C" + env "b" * env "C" *
            Complex.tan (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4341r3Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4341r3Nondeg.result) = fun w => (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4341r3Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4341r3Nondeg.body =
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m *
            (env "A" + env "B" * Complex.tan (env "e" + env "f" * t) + env "C" *
            (Complex.tan (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4341r3Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have e1 : (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1, hA]
    generalize (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m = Q
    field_simp
    ring

theorem rubi4541r1Nondeg_real : rubi4541r1Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4541r1Nondeg.conditions rubi4541r1Nondeg.body
    rubi4541r1Nondeg.result rubi4541r1Nondeg.integrals
  intro env hc t hF
  have hb2 : env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4541r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hb : env "b" ≠ 0 := fun h => hb2 (by rw [h]; ring)
  have hrel : env "A" * env "b" ^ 2 - env "a" * env "b" * env "B" + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2)))
      (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B")))
      (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4541r1Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hA : env "A" = (env "a" * env "b" * env "B" - env "a" ^ 2 * env "C") / env "b" ^ 2 := by
    field_simp; linear_combination hrel
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4541r1Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4541r1Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * (Real.sin (env "e" + env "f" * w))⁻¹ ≠ 0) := by
    intro w h
    simp [rubi4541r1Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4541r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := (hD w hw).2
    simp [Defined, eval, Interp.real, em1, Fn.csc, (hD w hw).1] at h ⊢
    exact fun h' => h (by omega)
  · filter_upwards with w
    simp [rubi4541r1Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hb]
  · simp only [rubi4541r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        (Real.sin (env "e" + env "f" * t))⁻¹) ^ (m + 1) *
        (env "b" * env "B" - env "a" * env "C" + env "b" * env "C" *
            (Real.sin (env "e" + env "f" * t))⁻¹)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4541r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4541r1Nondeg.result) = fun w => (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4541r1Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4541r1Nondeg.body =
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m *
            (env "A" + env "B" * (Real.sin (env "e" + env "f" * t))⁻¹ + env "C" *
            ((Real.sin (env "e" + env "f" * t))⁻¹) ^ 2) := by
      simp [rubi4541r1Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have e1 : (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ (m + 1) =
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m *
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1, hA]
    generalize (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m = Q
    field_simp
    ring

/-! ## RUBI 4.1.2.2 #35 -/

theorem rubi4122r35Nondeg_real : rubi4122r35Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4122r35Nondeg.conditions rubi4122r35Nondeg.body
    rubi4122r35Nondeg.result rubi4122r35Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4122r35Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkp : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r35Nondeg, Defined, eval, Interp.real, hkp] at h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4122r35Nondeg.body →
      (q < 0 → env "g" * Real.cos (env "e" + env "f" * w) ≠ 0) ∧ env "a" + env "b" *
          Real.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4122r35Nondeg, Defined, eval, Interp.real, hkp, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r35Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, hkp] at h ⊢
      tauto
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, hkp, ivm1R] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi4122r35Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hb]
  · simp only [rubi4122r35Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "g" * Real.cos (env "e" + env "f" * t)) ^ q) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkp]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "g" * Real.cos (env "e" + env "f" * t)) ^ q *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkp, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4122r35Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r35Nondeg.result) =
        fun w => env "d" * (env "b")⁻¹ * Φ "I1" w +
          (env "b" * env "c" - env "a" * env "d") * (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi4122r35Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi4122r35Nondeg.body =
        (env "g" * Real.cos (env "e" + env "f" * t)) ^ q *
            (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) *
          (env "a" + env "b" * Real.sin (env "e" + env "f" * t))⁻¹ := by
      simp [rubi4122r35Nondeg, eval, Interp.real, hkp, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hY := (hD t hF.self_of_nhds).2
    generalize (env "g" * Real.cos (env "e" + env "f" * t)) ^ q = Q
    generalize hE : env "a" + env "b" * Real.sin (env "e" + env "f" * t) = D at hY ⊢
    have hs : Real.sin (env "e" + env "f" * t) = (D - env "a") / env "b" := by
      rw [← hE]; field_simp; ring
    rw [hs]
    field_simp
    ring

theorem rubi4122r35Nondeg_complex : rubi4122r35Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4122r35Nondeg.conditions rubi4122r35Nondeg.body
    rubi4122r35Nondeg.result rubi4122r35Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4122r35Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkp : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r35Nondeg, Defined, eval, Interp.complex, hkp] at h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4122r35Nondeg.body →
      (q < 0 → env "g" * Complex.cos (env "e" + env "f" * w) ≠ 0) ∧ env "a" + env "b" *
          Complex.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4122r35Nondeg, Defined, eval, Interp.complex, hkp, ivm1C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r35Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, hkp] at h ⊢
      tauto
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, hkp, ivm1C] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi4122r35Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hb]
  · simp only [rubi4122r35Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "g" * Complex.cos (env "e" + env "f" * t)) ^ q) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkp]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "g" * Complex.cos (env "e" + env "f" * t)) ^ q *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkp, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4122r35Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r35Nondeg.result) =
        fun w => env "d" * (env "b")⁻¹ * Φ "I1" w +
          (env "b" * env "c" - env "a" * env "d") * (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi4122r35Nondeg, eval, recEnv, Interp.complex, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      ring
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4122r35Nondeg.body =
        (env "g" * Complex.cos (env "e" + env "f" * t)) ^ q *
            (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) *
          (env "a" + env "b" * Complex.sin (env "e" + env "f" * t))⁻¹ := by
      simp [rubi4122r35Nondeg, eval, Interp.complex, hkp, ivm1C]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hY := (hD t hF.self_of_nhds).2
    generalize (env "g" * Complex.cos (env "e" + env "f" * t)) ^ q = Q
    generalize hE : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) = D at hY ⊢
    have hs : Complex.sin (env "e" + env "f" * t) = (D - env "a") / env "b" := by
      rw [← hE]; field_simp; ring
    rw [hs]
    field_simp
    ring

/-! ## RUBI 4.1.5 #32 and #31 -/

theorem rubi415r32Nondeg_real : rubi415r32Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi415r32Nondeg.conditions rubi415r32Nondeg.body
    rubi415r32Nondeg.result rubi415r32Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi415r32Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi415r32Nondeg.body →
      Real.cos (env "c" + env "d" * w) ≠ 0 ∧ env "a" * Real.cos (env "c" + env "d" * w) + env "b" *
          Real.sin (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi415r32Nondeg, Defined, eval, Interp.real, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi415r32Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real] at h ⊢
      tauto
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, ivm1R] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi415r32Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi415r32Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") (Real.tan (env "c" + env "d" * t)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real]
    have hΦ2' : HasDerivAt (Φ "I2")
        ((env "b" * Real.cos (env "c" + env "d" * t) - env "a" *
            Real.sin (env "c" + env "d" * t)) *
            (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
            Real.sin (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, ivm1R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      try ring
    have hfun : (fun w => eval Interp.real (recEnv env (rubi415r32Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi415r32Nondeg.result) =
        fun w => (env "b")⁻¹ * Φ "I1" w + (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi415r32Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi415r32Nondeg.body =
        (Real.cos (env "c" + env "d" * t) *
            (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
            Real.sin (env "c" + env "d" * t)))⁻¹ := by
      simp [rubi415r32Nondeg, eval, Interp.real, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hB0, hD0⟩ := hD t hF.self_of_nhds
    have hsc := Real.sin_sq_add_cos_sq (env "c" + env "d" * t)
    rw [Real.tan_eq_sin_div_cos]
    generalize Real.sin (env "c" + env "d" * t) = S at hsc hB0 hD0 ⊢
    generalize Real.cos (env "c" + env "d" * t) = C at hsc hB0 hD0 ⊢
    generalize hE : env "a" * C + env "b" * S = D at hD0 ⊢
    have key : S * D + C * (env "b" * C - env "a" * S) = env "b" :=
        by rw [← hE]; linear_combination env "b" * hsc
    rw [show (env "b")⁻¹ * (S / C) + (env "b")⁻¹ * ((env "b" * C - env "a" * S) * D⁻¹) =
        (S * D + C * (env "b" * C - env "a" * S)) / (env "b" * C * D) by field_simp, key]
    field_simp

theorem rubi415r32Nondeg_complex : rubi415r32Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi415r32Nondeg.conditions rubi415r32Nondeg.body
    rubi415r32Nondeg.result rubi415r32Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi415r32Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi415r32Nondeg.body →
      Complex.cos (env "c" + env "d" * w) ≠ 0 ∧ env "a" * Complex.cos (env "c" + env "d" * w) +
          env "b" * Complex.sin (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi415r32Nondeg, Defined, eval, Interp.complex, ivm1C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi415r32Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex] at h ⊢
      tauto
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, ivm1C] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi415r32Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hl]
  · simp only [rubi415r32Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") (Complex.tan (env "c" + env "d" * t)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex]
    have hΦ2' : HasDerivAt (Φ "I2")
        ((env "b" * Complex.cos (env "c" + env "d" * t) - env "a" *
            Complex.sin (env "c" + env "d" * t)) *
            (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
            Complex.sin (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, ivm1C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      try ring
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi415r32Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi415r32Nondeg.result) =
        fun w => (env "b")⁻¹ * Φ "I1" w + (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi415r32Nondeg, eval, recEnv, Interp.complex, ivm1C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi415r32Nondeg.body =
        (Complex.cos (env "c" + env "d" * t) *
            (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
            Complex.sin (env "c" + env "d" * t)))⁻¹ := by
      simp [rubi415r32Nondeg, eval, Interp.complex, ivm1C]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hB0, hD0⟩ := hD t hF.self_of_nhds
    have hsc := Complex.sin_sq_add_cos_sq (env "c" + env "d" * t)
    rw [Complex.tan_eq_sin_div_cos]
    generalize Complex.sin (env "c" + env "d" * t) = S at hsc hB0 hD0 ⊢
    generalize Complex.cos (env "c" + env "d" * t) = C at hsc hB0 hD0 ⊢
    generalize hE : env "a" * C + env "b" * S = D at hD0 ⊢
    have key : S * D + C * (env "b" * C - env "a" * S) = env "b" :=
        by rw [← hE]; linear_combination env "b" * hsc
    rw [show (env "b")⁻¹ * (S / C) + (env "b")⁻¹ * ((env "b" * C - env "a" * S) * D⁻¹) =
        (S * D + C * (env "b" * C - env "a" * S)) / (env "b" * C * D) by field_simp, key]
    field_simp

theorem rubi415r31Nondeg_real : rubi415r31Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi415r31Nondeg.conditions rubi415r31Nondeg.body
    rubi415r31Nondeg.result rubi415r31Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi415r31Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi415r31Nondeg.body →
      Real.sin (env "c" + env "d" * w) ≠ 0 ∧ env "a" * Real.cos (env "c" + env "d" * w) + env "b" *
          Real.sin (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi415r31Nondeg, Defined, eval, Interp.real, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi415r31Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real] at h ⊢
      tauto
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, ivm1R] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi415r31Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi415r31Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") (Real.cot (env "c" + env "d" * t)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real]
    have hΦ2' : HasDerivAt (Φ "I2")
        ((env "b" * Real.cos (env "c" + env "d" * t) - env "a" *
            Real.sin (env "c" + env "d" * t)) *
            (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
            Real.sin (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, ivm1R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      try ring
    have hfun : (fun w => eval Interp.real (recEnv env (rubi415r31Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi415r31Nondeg.result) =
        fun w => (env "a")⁻¹ * Φ "I1" w + -(env "a")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi415r31Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi415r31Nondeg.body =
        (Real.sin (env "c" + env "d" * t) *
            (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
            Real.sin (env "c" + env "d" * t)))⁻¹ := by
      simp [rubi415r31Nondeg, eval, Interp.real, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hB0, hD0⟩ := hD t hF.self_of_nhds
    have hsc := Real.sin_sq_add_cos_sq (env "c" + env "d" * t)
    rw [Real.cot_eq_cos_div_sin]
    generalize Real.sin (env "c" + env "d" * t) = S at hsc hB0 hD0 ⊢
    generalize Real.cos (env "c" + env "d" * t) = C at hsc hB0 hD0 ⊢
    generalize hE : env "a" * C + env "b" * S = D at hD0 ⊢
    have key : C * D - S * (env "b" * C - env "a" * S) = env "a" :=
        by rw [← hE]; linear_combination env "a" * hsc
    rw [show (env "a")⁻¹ * (C / S) + -(env "a")⁻¹ * ((env "b" * C - env "a" * S) * D⁻¹) =
        (C * D - S * (env "b" * C - env "a" * S)) / (env "a" * S * D) by field_simp; try ring, key]
    field_simp

theorem rubi415r31Nondeg_complex : rubi415r31Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi415r31Nondeg.conditions rubi415r31Nondeg.body
    rubi415r31Nondeg.result rubi415r31Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi415r31Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi415r31Nondeg.body →
      Complex.sin (env "c" + env "d" * w) ≠ 0 ∧ env "a" * Complex.cos (env "c" + env "d" * w) +
          env "b" * Complex.sin (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi415r31Nondeg, Defined, eval, Interp.complex, ivm1C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi415r31Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex] at h ⊢
      tauto
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, ivm1C] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi415r31Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hl]
  · simp only [rubi415r31Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") (Complex.cot (env "c" + env "d" * t)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex]
    have hΦ2' : HasDerivAt (Φ "I2")
        ((env "b" * Complex.cos (env "c" + env "d" * t) - env "a" *
            Complex.sin (env "c" + env "d" * t)) *
            (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
            Complex.sin (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, ivm1C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      try ring
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi415r31Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi415r31Nondeg.result) =
        fun w => (env "a")⁻¹ * Φ "I1" w + -(env "a")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi415r31Nondeg, eval, recEnv, Interp.complex, ivm1C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi415r31Nondeg.body =
        (Complex.sin (env "c" + env "d" * t) *
            (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
            Complex.sin (env "c" + env "d" * t)))⁻¹ := by
      simp [rubi415r31Nondeg, eval, Interp.complex, ivm1C]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hB0, hD0⟩ := hD t hF.self_of_nhds
    have hsc := Complex.sin_sq_add_cos_sq (env "c" + env "d" * t)
    rw [Complex.cot_eq_cos_div_sin]
    generalize Complex.sin (env "c" + env "d" * t) = S at hsc hB0 hD0 ⊢
    generalize Complex.cos (env "c" + env "d" * t) = C at hsc hB0 hD0 ⊢
    generalize hE : env "a" * C + env "b" * S = D at hD0 ⊢
    have key : C * D - S * (env "b" * C - env "a" * S) = env "a" :=
        by rw [← hE]; linear_combination env "a" * hsc
    rw [show (env "a")⁻¹ * (C / S) + -(env "a")⁻¹ * ((env "b" * C - env "a" * S) * D⁻¹) =
        (C * D - S * (env "b" * C - env "a" * S)) / (env "a" * S * D) by field_simp; try ring, key]
    field_simp

/-! ## RUBI 4.1.10 #8 -/

theorem rubi4110r8Nondeg_real : rubi4110r8Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4110r8Nondeg.conditions rubi4110r8Nondeg.body
    rubi4110r8Nondeg.result rubi4110r8Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4110r8Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4110r8Nondeg.body → env "c" +
      env "d" * w ≠ 0 := by
    intro w h
    simpa [rubi4110r8Nondeg, Defined, eval, Interp.real, ivm1R] using h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4110r8Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simpa [Defined, eval, Interp.real, ivm1R, hd] using hD w hw
    · filter_upwards [hF] with w hw
      simpa [Defined, eval, Interp.real, ivm1R, hd] using hD w hw
  · filter_upwards with w
    simp [rubi4110r8Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hd]
  · simp only [rubi4110r8Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") (Real.sin (env "c" * env "f" * (env "d")⁻¹ + env "f" * t) *
        (env "c" + env "d" * t)⁻¹) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, ivm1R]
    have hΦ2' : HasDerivAt (Φ "I2") (Real.cos (env "c" * env "f" * (env "d")⁻¹ + env "f" * t) *
        (env "c" + env "d" * t)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4110r8Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4110r8Nondeg.result) =
        fun w => Real.cos ((env "d" * env "e" - env "c" * env "f") * (env "d")⁻¹) * Φ "I1" w +
            Real.sin ((env "d" * env "e" - env "c" * env "f") * (env "d")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi4110r8Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      ring_nf
    have hEF : eval Interp.real (Function.update env "x" t) rubi4110r8Nondeg.body =
        Real.sin (env "e" + env "f" * t) * (env "c" + env "d" * t)⁻¹ := by
      simp [rubi4110r8Nondeg, eval, Interp.real, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    rw [show Real.sin (env "e" + env "f" * t) =
        Real.sin ((env "d" * env "e" - env "c" * env "f") * (env "d")⁻¹) *
        Real.cos (env "c" * env "f" * (env "d")⁻¹ + env "f" * t) +
        Real.cos ((env "d" * env "e" - env "c" * env "f") * (env "d")⁻¹) *
            Real.sin (env "c" * env "f" * (env "d")⁻¹ + env "f" * t) by
      rw [← Real.sin_add]; congr 1; field_simp; ring]
    ring

theorem rubi4110r8Nondeg_complex : rubi4110r8Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4110r8Nondeg.conditions rubi4110r8Nondeg.body
    rubi4110r8Nondeg.result rubi4110r8Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4110r8Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4110r8Nondeg.body →
      env "c" + env "d" * w ≠ 0 := by
    intro w h
    simpa [rubi4110r8Nondeg, Defined, eval, Interp.complex, ivm1C] using h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4110r8Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simpa [Defined, eval, Interp.complex, ivm1C, hd] using hD w hw
    · filter_upwards [hF] with w hw
      simpa [Defined, eval, Interp.complex, ivm1C, hd] using hD w hw
  · filter_upwards with w
    simp [rubi4110r8Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hd]
  · simp only [rubi4110r8Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") (Complex.sin (env "c" * env "f" * (env "d")⁻¹ + env "f" * t) *
        (env "c" + env "d" * t)⁻¹) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, ivm1C]
    have hΦ2' : HasDerivAt (Φ "I2") (Complex.cos (env "c" * env "f" * (env "d")⁻¹ + env "f" * t) *
        (env "c" + env "d" * t)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4110r8Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4110r8Nondeg.result) =
        fun w => Complex.cos ((env "d" * env "e" - env "c" * env "f") * (env "d")⁻¹) * Φ "I1" w +
            Complex.sin ((env "d" * env "e" - env "c" * env "f") * (env "d")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi4110r8Nondeg, eval, recEnv, Interp.complex, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      ring_nf
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4110r8Nondeg.body =
        Complex.sin (env "e" + env "f" * t) * (env "c" + env "d" * t)⁻¹ := by
      simp [rubi4110r8Nondeg, eval, Interp.complex, ivm1C]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    rw [show Complex.sin (env "e" + env "f" * t) =
        Complex.sin ((env "d" * env "e" - env "c" * env "f") * (env "d")⁻¹) *
        Complex.cos (env "c" * env "f" * (env "d")⁻¹ + env "f" * t) +
        Complex.cos ((env "d" * env "e" - env "c" * env "f") * (env "d")⁻¹) *
            Complex.sin (env "c" * env "f" * (env "d")⁻¹ + env "f" * t) by
      rw [← Complex.sin_add]; congr 1; field_simp; ring]
    ring

/-! ## RUBI 4.1.2.2 #47 and #83 -/

theorem rubi4122r47Nondeg_real : rubi4122r47Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4122r47Nondeg.conditions rubi4122r47Nondeg.body
    rubi4122r47Nondeg.result rubi4122r47Nondeg.integrals
  intro env hc t hF
  have hb2 : env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4122r47Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hab : env "a" ^ 2 - env "b" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1))
      (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4122r47Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r47Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r47Nondeg, Defined, eval, Interp.real, hkm, hkn] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4122r47Nondeg.body →
      (n < 0 → env "d" * Real.sin (env "e" + env "f" * w) ≠ 0) ∧
          (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4122r47Nondeg, Defined, eval, Interp.real, hkm, hkn, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r47Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hD w hw
    have h2' : m + 1 < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0 :=
        fun h => h2 (by omega)
    simp [Defined, eval, Interp.real, hkn, em1] at h1 h2' ⊢
    tauto
  · filter_upwards with w
    simp [rubi4122r47Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hb2]
  · simp only [rubi4122r47Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" * Real.sin (env "e" + env "f" * t)) ^ n *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) *
        (env "a" - env "b" * Real.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkn, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      try ring
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4122r47Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r47Nondeg.result) = fun w => (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4122r47Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4122r47Nondeg.body =
        Real.cos (env "e" + env "f" * t) ^ 2 * (env "d" * Real.sin (env "e" + env "f" * t)) ^ n *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m := by
      simp [rubi4122r47Nondeg, eval, Interp.real, hkm, hkn, iv2R]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have e1 : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    have hsc := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    have key : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) *
        (env "a" - env "b" * Real.sin (env "e" + env "f" * t)) = env "b" ^ 2 *
        Real.cos (env "e" + env "f" * t) ^ 2 := by
      linear_combination hab - env "b" ^ 2 * hsc
    rw [e1]
    generalize (env "d" * Real.sin (env "e" + env "f" * t)) ^ n = P
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m = Q
    rw [show P * (Q * (env "a" + env "b" * Real.sin (env "e" + env "f" * t))) *
        (env "a" - env "b" * Real.sin (env "e" + env "f" * t)) = P * Q *
        ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) *
        (env "a" - env "b" * Real.sin (env "e" + env "f" * t))) by ring, key]
    have hb : env "b" ≠ 0 := fun h => hb2 (by rw [h]; ring)
    field_simp

theorem rubi4122r47Nondeg_complex : rubi4122r47Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4122r47Nondeg.conditions rubi4122r47Nondeg.body
    rubi4122r47Nondeg.result rubi4122r47Nondeg.integrals
  intro env hc t hF
  have hb2 : env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4122r47Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  have hab : env "a" ^ 2 - env "b" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1))
      (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4122r47Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r47Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r47Nondeg, Defined, eval, Interp.complex, hkm, hkn] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4122r47Nondeg.body →
      (n < 0 → env "d" * Complex.sin (env "e" + env "f" * w) ≠ 0) ∧
          (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4122r47Nondeg, Defined, eval, Interp.complex, hkm, hkn, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r47Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hD w hw
    have h2' : m + 1 < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0 :=
        fun h => h2 (by omega)
    simp [Defined, eval, Interp.complex, hkn, em1] at h1 h2' ⊢
    tauto
  · filter_upwards with w
    simp [rubi4122r47Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, hb2]
  · simp only [rubi4122r47Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" * Complex.sin (env "e" + env "f" * t)) ^ n *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) *
        (env "a" - env "b" * Complex.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkn, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      try ring
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4122r47Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r47Nondeg.result) = fun w => (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4122r47Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4122r47Nondeg.body =
        Complex.cos (env "e" + env "f" * t) ^ 2 *
        (env "d" * Complex.sin (env "e" + env "f" * t)) ^ n *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m := by
      simp [rubi4122r47Nondeg, eval, Interp.complex, hkm, hkn, iv2C]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have e1 : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    have hsc := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    have key : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) *
        (env "a" - env "b" * Complex.sin (env "e" + env "f" * t)) = env "b" ^ 2 *
        Complex.cos (env "e" + env "f" * t) ^ 2 := by
      linear_combination hab - env "b" ^ 2 * hsc
    rw [e1]
    generalize (env "d" * Complex.sin (env "e" + env "f" * t)) ^ n = P
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = Q
    rw [show P * (Q * (env "a" + env "b" * Complex.sin (env "e" + env "f" * t))) *
        (env "a" - env "b" * Complex.sin (env "e" + env "f" * t)) = P * Q *
        ((env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) *
        (env "a" - env "b" * Complex.sin (env "e" + env "f" * t))) by ring, key]
    have hb : env "b" ≠ 0 := fun h => hb2 (by rw [h]; ring)
    field_simp

theorem rubi4122r83Nondeg_real : rubi4122r83Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4122r83Nondeg.conditions rubi4122r83Nondeg.body
    rubi4122r83Nondeg.result rubi4122r83Nondeg.integrals
  intro env hc t hF
  have hb2 : env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4122r83Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hab : env "a" ^ 2 - env "b" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1))
      (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4122r83Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r83Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r83Nondeg, Defined, eval, Interp.real, hkm, hkn] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4122r83Nondeg.body →
      (n < 0 → env "c" + env "d" * Real.sin (env "e" + env "f" * w) ≠ 0) ∧
          (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4122r83Nondeg, Defined, eval, Interp.real, hkm, hkn, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r83Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hD w hw
    have h2' : m + 1 < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0 :=
        fun h => h2 (by omega)
    simp [Defined, eval, Interp.real, hkn, em1] at h1 h2' ⊢
    tauto
  · filter_upwards with w
    simp [rubi4122r83Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hb2]
  · simp only [rubi4122r83Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m +
        1) * (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ n *
        (env "a" - env "b" * Real.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkn, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      try ring
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4122r83Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r83Nondeg.result) = fun w => (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4122r83Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4122r83Nondeg.body =
        Real.cos (env "e" + env "f" * t) ^ 2 *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ n := by
      simp [rubi4122r83Nondeg, eval, Interp.real, hkm, hkn, iv2R]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have e1 : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    have hsc := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    have key : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) *
        (env "a" - env "b" * Real.sin (env "e" + env "f" * t)) = env "b" ^ 2 *
        Real.cos (env "e" + env "f" * t) ^ 2 := by
      linear_combination hab - env "b" ^ 2 * hsc
    rw [e1]
    generalize (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ n = P
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m = Q
    rw [show Q * (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) * P *
        (env "a" - env "b" * Real.sin (env "e" + env "f" * t)) = P * Q *
        ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) *
        (env "a" - env "b" * Real.sin (env "e" + env "f" * t))) by ring, key]
    have hb : env "b" ≠ 0 := fun h => hb2 (by rw [h]; ring)
    field_simp

theorem rubi4122r83Nondeg_complex : rubi4122r83Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4122r83Nondeg.conditions rubi4122r83Nondeg.body
    rubi4122r83Nondeg.result rubi4122r83Nondeg.integrals
  intro env hc t hF
  have hb2 : env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4122r83Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  have hab : env "a" ^ 2 - env "b" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1))
      (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4122r83Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r83Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r83Nondeg, Defined, eval, Interp.complex, hkm, hkn] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4122r83Nondeg.body →
      (n < 0 → env "c" + env "d" * Complex.sin (env "e" + env "f" * w) ≠ 0) ∧
          (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4122r83Nondeg, Defined, eval, Interp.complex, hkm, hkn, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r83Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hD w hw
    have h2' : m + 1 < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0 :=
        fun h => h2 (by omega)
    simp [Defined, eval, Interp.complex, hkn, em1] at h1 h2' ⊢
    tauto
  · filter_upwards with w
    simp [rubi4122r83Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, hb2]
  · simp only [rubi4122r83Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ (m + 1) *
        (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ n *
        (env "a" - env "b" * Complex.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkn, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      try ring
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4122r83Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r83Nondeg.result) = fun w => (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4122r83Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4122r83Nondeg.body =
        Complex.cos (env "e" + env "f" * t) ^ 2 *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ n := by
      simp [rubi4122r83Nondeg, eval, Interp.complex, hkm, hkn, iv2C]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have e1 : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    have hsc := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    have key : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) *
        (env "a" - env "b" * Complex.sin (env "e" + env "f" * t)) = env "b" ^ 2 *
        Complex.cos (env "e" + env "f" * t) ^ 2 := by
      linear_combination hab - env "b" ^ 2 * hsc
    rw [e1]
    generalize (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ n = P
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = Q
    rw [show Q * (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) * P *
        (env "a" - env "b" * Complex.sin (env "e" + env "f" * t)) = P * Q *
        ((env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) *
        (env "a" - env "b" * Complex.sin (env "e" + env "f" * t))) by ring, key]
    have hb : env "b" ≠ 0 := fun h => hb2 (by rw [h]; ring)
    field_simp

end OSR.IntegrationRec254
