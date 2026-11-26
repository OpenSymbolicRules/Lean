import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: `cos y^(m + 1)` plus a residual integral

Proofs of RUBI 4.1.4.1 #3, #5, #12, #13, #14 and #15 over ℝ and ℂ: the result is an explicit term
`K cos y^(m + 1)` (with `y = a + b sin` or `y = b sin`) plus a residual integral with `y^m`,
    `y^(m + 1)`
or `y^(m + 2)`; the integrand is recovered with `sin² + cos² = 1` (`linear_combination`
coefficients computed by Gröbner reduction). -/

namespace OSR.IntegrationRec272

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem hasDerivAt_lin {𝕜 : Type} [NontriviallyNormedField 𝕜] (a b t : 𝕜) :
    HasDerivAt (fun w => a + b * w) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

private theorem zsplit {K : Type} [Field K] (X : K) (j : ℤ) (n : ℕ) (h : X ≠ 0 ∨ 0 ≤ j) :
    X ^ (j + n) = X ^ j * X ^ n := by
  rcases h with h | h
  · rw [zpow_add₀ h, zpow_natCast]
  · lift j to ℕ using h
    rw [show ((j : ℤ) + n) = ((j + n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_add]

/-! ## rubi4141r14Nondeg -/

theorem rubi4141r14Nondeg_real : rubi4141r14Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4141r14Nondeg.conditions rubi4141r14Nondeg.body
    rubi4141r14Nondeg.result rubi4141r14Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 2)))
    (.int 0)) (by simp [rubi4141r14Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hmk2 : env "m" + 2 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r14Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4141r14Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r14Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r14Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4141r14Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, hb, hf, hmk2] at h ⊢
    tauto
  · simp only [rubi4141r14Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "A" * env "b" * (env "m" + 2) + env "b" * env "C" * (env "m" + 1) +
        (env "b" * env "B" * (env "m" + 2) - env "a" * env "C") *
        Real.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, sub_eq_add_neg, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4141r14Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r14Nondeg.result) = fun w => -(env "C") * Real.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Real.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 2))⁻¹ + (env "b" * (env "m" + 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4141r14Nondeg, eval, recEnv, Interp.real, em1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4141r14Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "B" * Real.sin (env "e" + env "f" * t) + env "C" *
        (Real.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4141r14Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Real.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Real.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hdisj : env "a" + env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "a" + env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hm2c : ((m : ℤ) : ℝ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hmk2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m = P
    generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "C"*env "b"*P*((m : ℤ) : ℝ) - env "C"*env "b"*P) * hP

theorem rubi4141r14Nondeg_complex : rubi4141r14Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4141r14Nondeg.conditions rubi4141r14Nondeg.body
    rubi4141r14Nondeg.result rubi4141r14Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 2)))
    (.int 0)) (by simp [rubi4141r14Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hmk2 : env "m" + 2 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r14Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4141r14Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r14Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r14Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4141r14Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, hb, hf, hmk2] at h ⊢
    tauto
  · simp only [rubi4141r14Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "A" * env "b" * (env "m" + 2) + env "b" * env "C" * (env "m" + 1) +
        (env "b" * env "B" * (env "m" + 2) - env "a" * env "C") *
        Complex.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, sub_eq_add_neg, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4141r14Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r14Nondeg.result) = fun w => -(env "C") *
            Complex.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Complex.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 2))⁻¹ + (env "b" * (env "m" + 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4141r14Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4141r14Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "B" * Complex.sin (env "e" + env "f" * t) + env "C" *
        (Complex.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4141r14Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Complex.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Complex.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hdisj : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hm2c : ((m : ℤ) : ℂ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hmk2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = P
    generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "C"*env "b"*P*((m : ℤ) : ℂ) - env "C"*env "b"*P) * hP

/-! ## rubi4141r15Nondeg -/

theorem rubi4141r15Nondeg_real : rubi4141r15Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4141r15Nondeg.conditions rubi4141r15Nondeg.body
    rubi4141r15Nondeg.result rubi4141r15Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 2)))
    (.int 0)) (by simp [rubi4141r15Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hmk2 : env "m" + 2 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r15Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4141r15Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r15Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4141r15Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, hb, hf, hmk2] at h ⊢
    tauto
  · simp only [rubi4141r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "A" * env "b" * (env "m" + 2) + env "b" * env "C" * (env "m" + 1) - env "a" *
        env "C" * Real.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, sub_eq_add_neg, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4141r15Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r15Nondeg.result) = fun w => -(env "C") * Real.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Real.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 2))⁻¹ + (env "b" * (env "m" + 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4141r15Nondeg, eval, recEnv, Interp.real, em1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4141r15Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "C" * (Real.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4141r15Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Real.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Real.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hdisj : env "a" + env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "a" + env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hm2c : ((m : ℤ) : ℝ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hmk2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m = P
    generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "C"*env "b"*P*((m : ℤ) : ℝ) - env "C"*env "b"*P) * hP

theorem rubi4141r15Nondeg_complex : rubi4141r15Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4141r15Nondeg.conditions rubi4141r15Nondeg.body
    rubi4141r15Nondeg.result rubi4141r15Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 2)))
    (.int 0)) (by simp [rubi4141r15Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hmk2 : env "m" + 2 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r15Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4141r15Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r15Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4141r15Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, hb, hf, hmk2] at h ⊢
    tauto
  · simp only [rubi4141r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "A" * env "b" * (env "m" + 2) + env "b" * env "C" * (env "m" + 1) - env "a" *
        env "C" * Complex.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, sub_eq_add_neg, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4141r15Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r15Nondeg.result) = fun w => -(env "C") *
            Complex.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Complex.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 2))⁻¹ + (env "b" * (env "m" + 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4141r15Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4141r15Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "C" * (Complex.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4141r15Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Complex.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Complex.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hdisj : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hm2c : ((m : ℤ) : ℂ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hmk2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = P
    generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "C"*env "b"*P*((m : ℤ) : ℂ) - env "C"*env "b"*P) * hP

/-! ## rubi4141r12Nondeg -/

theorem rubi4141r12Nondeg_real : rubi4141r12Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4141r12Nondeg.conditions rubi4141r12Nondeg.body
    rubi4141r12Nondeg.result rubi4141r12Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m")
    (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
    (.int 2))))) (.int 0)) (by simp [rubi4141r12Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hm1' : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hab : env "a" ^ 2 - env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
      (.int 2)))) (.int 0)) (by simp [rubi4141r12Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r12Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4141r12Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r12Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4141r12Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R, hb, hf,
        hm1'] at h ⊢
    tauto
  · simp only [rubi4141r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m +
        1) * (env "b" * (env "a" * env "A" - env "b" * env "B" + env "a" * env "C") *
        (env "m" + 1) -
        (env "A" * env "b" ^ 2 - env "a" * env "b" * env "B" + env "a" ^ 2 * env "C" + env "b" *
        (env "A" * env "b" - env "a" * env "B" + env "b" * env "C") * (env "m" + 1)) *
        Real.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4141r12Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r12Nondeg.result) =
            fun w => -(env "A" * env "b" ^ 2 - env "a" * env "b" * env "B" + env "a" ^ 2 *
            env "C") * Real.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Real.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 1) * (env "a" ^ 2 - env "b" ^ 2))⁻¹ +
            (env "b" * (env "m" + 1) * (env "a" ^ 2 - env "b" ^ 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4141r12Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi4141r12Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "B" * Real.sin (env "e" + env "f" * t) + env "C" *
        (Real.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4141r12Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Real.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Real.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hdisj : env "a" + env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "a" + env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hm1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hm1'
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m = P
    generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "A"*env "b"^3*P*((m : ℤ) : ℝ) - env "A"*env "b"^3*P +
        env "B"*env "a"*env "b"^2*P*((m : ℤ) : ℝ) + env "B"*env "a"*env "b"^2*P -
        env "C"*env "a"^2*env "b"*P*((m : ℤ) : ℝ) - env "C"*env "a"^2*env "b"*P) * hP

theorem rubi4141r12Nondeg_complex : rubi4141r12Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4141r12Nondeg.conditions rubi4141r12Nondeg.body
    rubi4141r12Nondeg.result rubi4141r12Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m")
    (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
    (.int 2))))) (.int 0)) (by simp [rubi4141r12Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hm1' : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hab : env "a" ^ 2 - env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
      (.int 2)))) (.int 0)) (by simp [rubi4141r12Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r12Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4141r12Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r12Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4141r12Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, hb, hf,
        hm1'] at h ⊢
    tauto
  · simp only [rubi4141r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ (m + 1) *
        (env "b" * (env "a" * env "A" - env "b" * env "B" + env "a" * env "C") * (env "m" + 1) -
        (env "A" * env "b" ^ 2 - env "a" * env "b" * env "B" + env "a" ^ 2 * env "C" + env "b" *
        (env "A" * env "b" - env "a" * env "B" + env "b" * env "C") * (env "m" + 1)) *
        Complex.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4141r12Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r12Nondeg.result) =
            fun w => -(env "A" * env "b" ^ 2 - env "a" * env "b" * env "B" + env "a" ^ 2 *
            env "C") * Complex.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Complex.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 1) * (env "a" ^ 2 - env "b" ^ 2))⁻¹ +
            (env "b" * (env "m" + 1) * (env "a" ^ 2 - env "b" ^ 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4141r12Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4141r12Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "B" * Complex.sin (env "e" + env "f" * t) + env "C" *
        (Complex.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4141r12Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Complex.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Complex.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hdisj : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hm1c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hm1'
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = P
    generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "A"*env "b"^3*P*((m : ℤ) : ℂ) - env "A"*env "b"^3*P +
        env "B"*env "a"*env "b"^2*P*((m : ℤ) : ℂ) + env "B"*env "a"*env "b"^2*P -
        env "C"*env "a"^2*env "b"*P*((m : ℤ) : ℂ) - env "C"*env "a"^2*env "b"*P) * hP

/-! ## rubi4141r13Nondeg -/

theorem rubi4141r13Nondeg_real : rubi4141r13Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4141r13Nondeg.conditions rubi4141r13Nondeg.body
    rubi4141r13Nondeg.result rubi4141r13Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m")
    (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
    (.int 2))))) (.int 0)) (by simp [rubi4141r13Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hm1' : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hab : env "a" ^ 2 - env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
      (.int 2)))) (.int 0)) (by simp [rubi4141r13Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r13Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4141r13Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r13Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4141r13Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R, hb, hf,
        hm1'] at h ⊢
    tauto
  · simp only [rubi4141r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m +
        1) * (env "a" * env "b" * (env "A" + env "C") * (env "m" + 1) -
        (env "A" * env "b" ^ 2 + env "a" ^ 2 * env "C" + env "b" ^ 2 * (env "A" + env "C") *
        (env "m" + 1)) * Real.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4141r13Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r13Nondeg.result) =
            fun w => -(env "A" * env "b" ^ 2 + env "a" ^ 2 * env "C") *
            Real.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Real.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 1) * (env "a" ^ 2 - env "b" ^ 2))⁻¹ +
            (env "b" * (env "m" + 1) * (env "a" ^ 2 - env "b" ^ 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4141r13Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi4141r13Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "C" * (Real.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4141r13Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Real.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Real.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hdisj : env "a" + env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "a" + env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hm1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hm1'
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m = P
    generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "A"*env "b"^3*P*((m : ℤ) : ℝ) - env "A"*env "b"^3*P -
        env "C"*env "a"^2*env "b"*P*((m : ℤ) : ℝ) - env "C"*env "a"^2*env "b"*P) * hP

theorem rubi4141r13Nondeg_complex : rubi4141r13Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4141r13Nondeg.conditions rubi4141r13Nondeg.body
    rubi4141r13Nondeg.result rubi4141r13Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m")
    (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
    (.int 2))))) (.int 0)) (by simp [rubi4141r13Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hm1' : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hab : env "a" ^ 2 - env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
      (.int 2)))) (.int 0)) (by simp [rubi4141r13Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r13Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4141r13Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r13Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4141r13Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, hb, hf,
        hm1'] at h ⊢
    tauto
  · simp only [rubi4141r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ (m + 1) *
        (env "a" * env "b" * (env "A" + env "C") * (env "m" + 1) -
        (env "A" * env "b" ^ 2 + env "a" ^ 2 * env "C" + env "b" ^ 2 * (env "A" + env "C") *
        (env "m" + 1)) * Complex.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4141r13Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r13Nondeg.result) =
            fun w => -(env "A" * env "b" ^ 2 + env "a" ^ 2 * env "C") *
            Complex.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Complex.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 1) * (env "a" ^ 2 - env "b" ^ 2))⁻¹ +
            (env "b" * (env "m" + 1) * (env "a" ^ 2 - env "b" ^ 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4141r13Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4141r13Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "C" * (Complex.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4141r13Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Complex.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Complex.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hdisj : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hm1c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hm1'
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = P
    generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "A"*env "b"^3*P*((m : ℤ) : ℂ) - env "A"*env "b"^3*P -
        env "C"*env "a"^2*env "b"*P*((m : ℤ) : ℂ) - env "C"*env "a"^2*env "b"*P) * hP

/-! ## rubi4141r5Nondeg -/

theorem rubi4141r5Nondeg_real : rubi4141r5Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4141r5Nondeg.conditions rubi4141r5Nondeg.body
    rubi4141r5Nondeg.result rubi4141r5Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 2)))
    (.int 0)) (by simp [rubi4141r5Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hmk2 : env "m" + 2 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r5Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4141r5Nondeg.body →
      (m < 0 → env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r5Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4141r5Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, hb, hf, hmk2] at h ⊢
    tauto
  · simp only [rubi4141r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "b" * Real.sin (env "e" + env "f" * t)) ^ m) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4141r5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r5Nondeg.result) = fun w => -(env "C") * Real.cos (env "e" + env "f" * w) *
            (env "b" * Real.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 2))⁻¹ +
            (env "A" * (env "m" + 2) + env "C" * (env "m" + 1)) * (env "m" + 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4141r5Nondeg, eval, recEnv, Interp.real, em1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4141r5Nondeg.body =
        (env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "C" * (Real.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4141r5Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Real.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Real.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := hS.const_mul (env "b")
    have hdisj : env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "b" * Real.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "b" * Real.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hm2c : ((m : ℤ) : ℝ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hmk2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "b" * Real.sin (env "e" + env "f" * t)) ^ m = P
    generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "C"*P*((m : ℤ) : ℝ) - env "C"*P) * hP

theorem rubi4141r5Nondeg_complex : rubi4141r5Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4141r5Nondeg.conditions rubi4141r5Nondeg.body
    rubi4141r5Nondeg.result rubi4141r5Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 2)))
    (.int 0)) (by simp [rubi4141r5Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hmk2 : env "m" + 2 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r5Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4141r5Nondeg.body →
      (m < 0 → env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r5Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4141r5Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, hb, hf, hmk2] at h ⊢
    tauto
  · simp only [rubi4141r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "b" * Complex.sin (env "e" + env "f" * t)) ^ m) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4141r5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r5Nondeg.result) = fun w => -(env "C") *
            Complex.cos (env "e" + env "f" * w) *
            (env "b" * Complex.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 2))⁻¹ +
            (env "A" * (env "m" + 2) + env "C" * (env "m" + 1)) * (env "m" + 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4141r5Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4141r5Nondeg.body =
        (env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "C" * (Complex.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4141r5Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Complex.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Complex.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := hS.const_mul (env "b")
    have hdisj : env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "b" * Complex.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "b" * Complex.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hm2c : ((m : ℤ) : ℂ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hmk2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = P
    generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "C"*P*((m : ℤ) : ℂ) - env "C"*P) * hP

/-! ## rubi4141r3Nondeg -/

theorem rubi4141r3Nondeg_real : rubi4141r3Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4141r3Nondeg.conditions rubi4141r3Nondeg.body
    rubi4141r3Nondeg.result rubi4141r3Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1)))
    (.int 0)) (by simp [rubi4141r3Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hmk1 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r3Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have em2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm2' : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4141r3Nondeg.body →
      (m < 0 → env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r3Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r3Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em2] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4141r3Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R, hb, hf,
        hmk1] at h ⊢
    tauto
  · simp only [rubi4141r3Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 2)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em2, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4141r3Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r3Nondeg.result) = fun w => env "A" * Real.cos (env "e" + env "f" * w) *
            (env "b" * Real.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 1))⁻¹ +
            (env "A" * (env "m" + 2) + env "C" * (env "m" + 1)) * (env "b" ^ 2 * (env "m" + 1))⁻¹ *
            Φ "I1" w := by
      funext w
      simp [rubi4141r3Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4141r3Nondeg.body =
        (env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "C" * (Real.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4141r3Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Real.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Real.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := hS.const_mul (env "b")
    have hdisj : env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "b" * Real.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "b" * Real.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    have eA2 : (env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 2) =
        (env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "b" * Real.sin (env "e" + env "f" * t)) ^ 2 := by
      have := zsplit (env "b" * Real.sin (env "e" + env "f" * t)) m 2 hdisj
      rwa [show m + ((2 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
    rw [eA2, eA]
    have hm1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hmk1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "b" * Real.sin (env "e" + env "f" * t)) ^ m = P
    generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (env "A"*P*((m : ℤ) : ℝ) + env "A"*P) * hP

theorem rubi4141r3Nondeg_complex : rubi4141r3Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4141r3Nondeg.conditions rubi4141r3Nondeg.body
    rubi4141r3Nondeg.result rubi4141r3Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1)))
    (.int 0)) (by simp [rubi4141r3Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hmk1 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r3Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have em2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm2' : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4141r3Nondeg.body →
      (m < 0 → env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r3Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r3Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em2] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4141r3Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, hb, hf,
        hmk1] at h ⊢
    tauto
  · simp only [rubi4141r3Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 2)) t :=
        by
      convert hΦ using 1
      simp [eval, Interp.complex, em2, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4141r3Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r3Nondeg.result) = fun w => env "A" * Complex.cos (env "e" + env "f" * w) *
            (env "b" * Complex.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 1))⁻¹ +
            (env "A" * (env "m" + 2) + env "C" * (env "m" + 1)) * (env "b" ^ 2 * (env "m" + 1))⁻¹ *
            Φ "I1" w := by
      funext w
      simp [rubi4141r3Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4141r3Nondeg.body =
        (env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "C" * (Complex.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4141r3Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Complex.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Complex.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := hS.const_mul (env "b")
    have hdisj : env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "b" * Complex.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "b" * Complex.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    have eA2 : (env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 2) =
        (env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "b" * Complex.sin (env "e" + env "f" * t)) ^ 2 := by
      have := zsplit (env "b" * Complex.sin (env "e" + env "f" * t)) m 2 hdisj
      rwa [show m + ((2 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
    rw [eA2, eA]
    have hm1c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hmk1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = P
    generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (env "A"*P*((m : ℤ) : ℂ) + env "A"*P) * hP

end OSR.IntegrationRec272
