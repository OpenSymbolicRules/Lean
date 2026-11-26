import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: explicit terms with powers plus a residual integral

Proofs over ℝ (`csc` has no complex interpretation) of RUBI rules whose result is an explicit term
`K cot (a + b csc)^E` (or a product of `cot`, `csc` and such powers) plus a residual integral. The
derivative of the explicit term is built from the rule expression; the integrand is recovered with
`sin² + cos² = 1` and the stated parameter relations, separately for `m = 0` and `m ≠ 0`
(`linear_combination` coefficients computed by Gröbner reduction). -/

namespace OSR.IntegrationRec280

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

/-! ## rubi4110r2Nondeg -/

theorem rubi4110r2Nondeg_real : rubi4110r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4110r2Nondeg.conditions rubi4110r2Nondeg.body
    rubi4110r2Nondeg.result rubi4110r2Nondeg.integrals
  intro env hc t hF
  have hc1 :=
      hc (.ne (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4110r2Nondeg])
  have hn1_0 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4110r2Nondeg, Defined, eval, Interp.real, hkm] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4110r2Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4110r2Nondeg.body →
      (m < 0 → (env "c" + (env "d" * w)) ≠ 0) := by
    intro w h
    simp [rubi4110r2Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4110r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4110r2Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R] at h hn1_0 hn1_1 ⊢
    tauto
  · simp only [rubi4110r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "c" + (env "d" * t))) ^ (m + 1) *
        Real.cos ((env "e" + (env "f" * t)))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4110r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4110r2Nondeg.result) =
            fun w => ((((env "c" + (env "d" * w))) ^ (m + 1) *
            Real.sin ((env "e" + (env "f" * w)))) * ((env "d" * (env "m" + 1)))⁻¹) +
            (((-1) * env "f") * ((env "d" * (env "m" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4110r2Nondeg, eval, recEnv, Interp.real, em1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4110r2Nondeg.body =
        ((env "c" + (env "d" * t))) ^ (m) * Real.sin ((env "e" + (env "f" * t))) := by
      simp [rubi4110r2Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) → (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdz (m +
        1) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t)))).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (hasDerivAt_const t (((env "d" * (env "m" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn1_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination
    · have hdm : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "c" + (env "d" * t))) ^ m = ((env "c" + (env "d" * t))) ^ (m - 1) *
          ((env "c" + (env "d" * t))) ^ 1 := by
        have := zsplit ((env "c" + (env "d" * t))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "c" + (env "d" * t))) ^ (m + 1) = ((env "c" + (env "d" * t))) ^ (m - 1) *
          ((env "c" + (env "d" * t))) ^ 2 := by
        have := zsplit ((env "c" + (env "d" * t))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "c" + (env "d" * t))) ^ (m + 2) = ((env "c" + (env "d" * t))) ^ (m - 1) *
          ((env "c" + (env "d" * t))) ^ 3 := by
        have := zsplit ((env "c" + (env "d" * t))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "c" + (env "d" * t))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination

theorem rubi4110r2Nondeg_complex : rubi4110r2Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4110r2Nondeg.conditions rubi4110r2Nondeg.body
    rubi4110r2Nondeg.result rubi4110r2Nondeg.integrals
  intro env hc t hF
  have hc1 :=
      hc (.ne (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4110r2Nondeg])
  have hn1_0 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4110r2Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4110r2Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4110r2Nondeg.body →
      (m < 0 → (env "c" + (env "d" * w)) ≠ 0) := by
    intro w h
    simp [rubi4110r2Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4110r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4110r2Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C] at h hn1_0 hn1_1 ⊢
    tauto
  · simp only [rubi4110r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "c" + (env "d" * t))) ^ (m + 1) *
        Complex.cos ((env "e" + (env "f" * t)))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4110r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4110r2Nondeg.result) =
            fun w => ((((env "c" + (env "d" * w))) ^ (m + 1) *
            Complex.sin ((env "e" + (env "f" * w)))) * ((env "d" * (env "m" + 1)))⁻¹) +
            (((-1) * env "f") * ((env "d" * (env "m" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4110r2Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4110r2Nondeg.body =
        ((env "c" + (env "d" * t))) ^ (m) * Complex.sin ((env "e" + (env "f" * t))) := by
      simp [rubi4110r2Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) → (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdz (m +
        1) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t)))).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (hasDerivAt_const t (((env "d" * (env "m" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn1_1c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination
    · have hdm : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "c" + (env "d" * t))) ^ m = ((env "c" + (env "d" * t))) ^ (m - 1) *
          ((env "c" + (env "d" * t))) ^ 1 := by
        have := zsplit ((env "c" + (env "d" * t))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "c" + (env "d" * t))) ^ (m + 1) = ((env "c" + (env "d" * t))) ^ (m - 1) *
          ((env "c" + (env "d" * t))) ^ 2 := by
        have := zsplit ((env "c" + (env "d" * t))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "c" + (env "d" * t))) ^ (m + 2) = ((env "c" + (env "d" * t))) ^ (m - 1) *
          ((env "c" + (env "d" * t))) ^ 3 := by
        have := zsplit ((env "c" + (env "d" * t))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "c" + (env "d" * t))) ^ (m - 1) = P
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination

/-! ## rubi4122r26Nondeg -/

theorem rubi4122r26Nondeg_real : rubi4122r26Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4122r26Nondeg.conditions rubi4122r26Nondeg.body
    rubi4122r26Nondeg.result rubi4122r26Nondeg.integrals
  intro env hc t hF
  have hr0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4122r26Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "f")) (.app2 .add (.var "m") (.int 3))) (.int 0)) (by simp [rubi4122r26Nondeg])
  have hn3_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  have hn3_2 : env "m" + 3 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r26Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have hb2 : m < 0 := by
    have h := hc (.gt (.int 0) (.var "m")) (by simp [rubi4122r26Nondeg])
    have h' : ((m : ℤ) : ℝ) < (0 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4122r26Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4122r26Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r26Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4122r26Nondeg, Defined, eval, recEnv, Interp.real, em2, ivm1R,
        iv2R] at h hn3_0 hn3_1 hn3_2 ⊢
    tauto
  · simp only [rubi4122r26Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) *
        ((((env "b" * env "d") * (env "m" + 2)) + ((((-1) * env "a") * env "c") * (env "m" + 3))) +
        ((((env "b" * env "c") * (env "m" + 3)) + ((((-1) * env "a") * env "d") * (env "m" + 4))) *
        Real.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4122r26Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r26Nondeg.result) =
            fun w => (((env "d" * Real.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w)))))) ^ (m + 2)) *
            ((((env "b") ^ 2 * env "f") * (env "m" + 3)))⁻¹) +
            ((-1) * (((env "b") ^ 2 * (env "m" + 3)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4122r26Nondeg, eval, recEnv, Interp.real, em2, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4122r26Nondeg.body =
        ((Real.cos ((env "e" + (env "f" * t)))) ^ 2 *
        ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m)) *
        (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) := by
      simp [rubi4122r26Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "d")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 2) _ (hdz (m + 2) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((((env "b") ^ 2 * env "f") * (env "m" + 3)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      show m + 2 - 1 = m + 1 by ring]
    have hn3_2c : ((m : ℤ) : ℝ) + 3 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (2*env "a"*env "b"*env "d" - 3*env "b"^2*env "c" - env "b"^2*env "d"*S) *
          hP + (3*env "c" + 3*env "d"*S) * hr0
    · have hdm : (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ m =
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1, e2]
      generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "a"^2*env "b"*env "d"*env "f"*P*((m : ℤ) : ℝ) +
          2*env "a"^2*env "b"*env "d"*env "f"*P -
          env "a"*env "b"^2*env "c"*env "f"*P*((m : ℤ) : ℝ) -
          3*env "a"*env "b"^2*env "c"*env "f"*P +
          env "a"*env "b"^2*env "d"*env "f"*P*S*((m : ℤ) : ℝ) +
          env "a"*env "b"^2*env "d"*env "f"*P*S - env "b"^3*env "c"*env "f"*P*S*((m : ℤ) : ℝ) -
          3*env "b"^3*env "c"*env "f"*P*S - env "b"^3*env "d"*env "f"*P*S^2) * hP +
          (env "a"*env "c"*env "f"*P*((m : ℤ) : ℝ) + 3*env "a"*env "c"*env "f"*P +
          env "a"*env "d"*env "f"*P*S*((m : ℤ) : ℝ) + 3*env "a"*env "d"*env "f"*P*S +
          env "b"*env "c"*env "f"*P*S*((m : ℤ) : ℝ) + 3*env "b"*env "c"*env "f"*P*S +
          env "b"*env "d"*env "f"*P*S^2*((m : ℤ) : ℝ) + 3*env "b"*env "d"*env "f"*P*S^2) * hr0

theorem rubi4122r26Nondeg_complex : rubi4122r26Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4122r26Nondeg.conditions rubi4122r26Nondeg.body
    rubi4122r26Nondeg.result rubi4122r26Nondeg.integrals
  intro env hc t hF
  have hr0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4122r26Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "f")) (.app2 .add (.var "m") (.int 3))) (.int 0)) (by simp [rubi4122r26Nondeg])
  have hn3_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  have hn3_2 : env "m" + 3 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r26Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have hb2 : m < 0 := by
    have h := hc (.gt (.int 0) (.var "m")) (by simp [rubi4122r26Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (0 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4122r26Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4122r26Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r26Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4122r26Nondeg, Defined, eval, recEnv, Interp.complex, em2, ivm1C,
        iv2C] at h hn3_0 hn3_1 hn3_2 ⊢
    tauto
  · simp only [rubi4122r26Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) *
        ((((env "b" * env "d") * (env "m" + 2)) + ((((-1) * env "a") * env "c") * (env "m" + 3))) +
        ((((env "b" * env "c") * (env "m" + 3)) + ((((-1) * env "a") * env "d") * (env "m" + 4))) *
        Complex.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4122r26Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r26Nondeg.result) =
            fun w => (((env "d" * Complex.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (m + 2)) *
            ((((env "b") ^ 2 * env "f") * (env "m" + 3)))⁻¹) +
            ((-1) * (((env "b") ^ 2 * (env "m" + 3)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4122r26Nondeg, eval, recEnv, Interp.complex, em2, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4122r26Nondeg.body =
        ((Complex.cos ((env "e" + (env "f" * t)))) ^ 2 *
        ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m)) *
        (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) := by
      simp [rubi4122r26Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "d")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 2) _ (hdz (m + 2) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((((env "b") ^ 2 * env "f") * (env "m" + 3)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      show m + 2 - 1 = m + 1 by ring]
    have hn3_2c : ((m : ℤ) : ℂ) + 3 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (2*env "a"*env "b"*env "d" - 3*env "b"^2*env "c" - env "b"^2*env "d"*S) *
          hP + (3*env "c" + 3*env "d"*S) * hr0
    · have hdm : (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 1 :=
        by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ m =
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1, e2]
      generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = P
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "a"^2*env "b"*env "d"*env "f"*P*((m : ℤ) : ℂ) +
          2*env "a"^2*env "b"*env "d"*env "f"*P -
          env "a"*env "b"^2*env "c"*env "f"*P*((m : ℤ) : ℂ) -
          3*env "a"*env "b"^2*env "c"*env "f"*P +
          env "a"*env "b"^2*env "d"*env "f"*P*S*((m : ℤ) : ℂ) +
          env "a"*env "b"^2*env "d"*env "f"*P*S - env "b"^3*env "c"*env "f"*P*S*((m : ℤ) : ℂ) -
          3*env "b"^3*env "c"*env "f"*P*S - env "b"^3*env "d"*env "f"*P*S^2) * hP +
          (env "a"*env "c"*env "f"*P*((m : ℤ) : ℂ) + 3*env "a"*env "c"*env "f"*P +
          env "a"*env "d"*env "f"*P*S*((m : ℤ) : ℂ) + 3*env "a"*env "d"*env "f"*P*S +
          env "b"*env "c"*env "f"*P*S*((m : ℤ) : ℂ) + 3*env "b"*env "c"*env "f"*P*S +
          env "b"*env "d"*env "f"*P*S^2*((m : ℤ) : ℂ) + 3*env "b"*env "d"*env "f"*P*S^2) * hr0

/-! ## rubi4142r5Nondeg -/

theorem rubi4142r5Nondeg_real : rubi4142r5Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4142r5Nondeg.conditions rubi4142r5Nondeg.body
    rubi4142r5Nondeg.result rubi4142r5Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4142r5Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4142r5Nondeg])
  have hn1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4142r5Nondeg])
  have hn1v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4142r5Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 3))) (.int 0)) (by simp [rubi4142r5Nondeg])
  have hn3_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "m" + 3 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r5Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have hb2 : -1 ≤ m := by
    have h := hc (.ge (.var "m") (.int (-1))) (by simp [rubi4142r5Nondeg])
    have h' : (-1 : ℝ) ≤ ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      rcases h with h | h <;> linarith
    exact_mod_cast h'
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4142r5Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4142r5Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4142r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4142r5Nondeg, Defined, eval, recEnv, Interp.real, em1,
        ivm1R] at h hn0 hn1 hn3_0 hn3_1 hn3_2 ⊢
    tauto
  · simp only [rubi4142r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        (((((env "a" * env "C") * env "d") + (((env "A" * env "b") * env "c") * (env "m" + 3))) +
        ((env "b" *
        (((env "B" * env "c") * (env "m" + 3)) +
        (env "d" * ((env "C" * (env "m" + 2)) + (env "A" * (env "m" + 3)))))) *
        Real.sin ((env "e" + (env "f" * t))))) +
        (((-1) *
        ((((2 * env "a") * env "C") * env "d") +
        ((((-1) * env "b") * ((env "c" * env "C") + (env "B" * env "d"))) * (env "m" + 3)))) *
        (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4142r5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4142r5Nondeg.result) =
            fun w => (((((((-1) * env "C") * env "d") * Real.cos ((env "e" + (env "f" * w)))) *
            Real.sin ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "b" * env "f") * (env "m" + 3)))⁻¹) + (1 * ((env "b" * (env "m" + 3)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4142r5Nondeg, eval, recEnv, Interp.real, em1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4142r5Nondeg.body =
        (((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) *
        ((env "A" + (env "B" * Real.sin ((env "e" + (env "f" * t))))) +
        (env "C" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4142r5Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t ((((-1) * env "C") *
        env "d"))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "b" * env "f") * (env "m" + 3)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn3_2c : ((m : ℤ) : ℝ) + 3 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "C"*env "a"*env "d" - 2*env "C"*env "b"*env "d"*S) * hP
    · have hdm : (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ m =
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "C"*env "a"^2*env "d"*env "f"*P -
          env "C"*env "a"*env "b"*env "d"*env "f"*P*S*((m : ℤ) : ℝ) -
          3*env "C"*env "a"*env "b"*env "d"*env "f"*P*S -
          env "C"*env "b"^2*env "d"*env "f"*P*S^2*((m : ℤ) : ℝ) -
          2*env "C"*env "b"^2*env "d"*env "f"*P*S^2) * hP

theorem rubi4142r5Nondeg_complex : rubi4142r5Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4142r5Nondeg.conditions rubi4142r5Nondeg.body
    rubi4142r5Nondeg.result rubi4142r5Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4142r5Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4142r5Nondeg])
  have hn1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4142r5Nondeg])
  have hn1v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4142r5Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 3))) (.int 0)) (by simp [rubi4142r5Nondeg])
  have hn3_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "m" + 3 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r5Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have hb2 : -1 ≤ m := by
    have h := hc (.ge (.var "m") (.int (-1))) (by simp [rubi4142r5Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (-1 : ℝ) ≤ ((m : ℤ) : ℝ) := by
      rcases h with h | h <;> linarith
    exact_mod_cast h'
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4142r5Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4142r5Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4142r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4142r5Nondeg, Defined, eval, recEnv, Interp.complex, em1,
        ivm1C] at h hn0 hn1 hn3_0 hn3_1 hn3_2 ⊢
    tauto
  · simp only [rubi4142r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        (((((env "a" * env "C") * env "d") + (((env "A" * env "b") * env "c") * (env "m" + 3))) +
        ((env "b" *
        (((env "B" * env "c") * (env "m" + 3)) +
        (env "d" * ((env "C" * (env "m" + 2)) + (env "A" * (env "m" + 3)))))) *
        Complex.sin ((env "e" + (env "f" * t))))) +
        (((-1) *
        ((((2 * env "a") * env "C") * env "d") +
        ((((-1) * env "b") * ((env "c" * env "C") + (env "B" * env "d"))) * (env "m" + 3)))) *
        (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4142r5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4142r5Nondeg.result) =
            fun w => (((((((-1) * env "C") * env "d") * Complex.cos ((env "e" + (env "f" * w)))) *
            Complex.sin ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "b" * env "f") * (env "m" + 3)))⁻¹) + (1 * ((env "b" * (env "m" + 3)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4142r5Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4142r5Nondeg.body =
        (((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) *
        ((env "A" + (env "B" * Complex.sin ((env "e" + (env "f" * t))))) +
        (env "C" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4142r5Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t ((((-1) * env "C") *
        env "d"))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "b" * env "f") * (env "m" + 3)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn3_2c : ((m : ℤ) : ℂ) + 3 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "C"*env "a"*env "d" - 2*env "C"*env "b"*env "d"*S) * hP
    · have hdm : (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 1 :=
        by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ m =
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = P
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "C"*env "a"^2*env "d"*env "f"*P -
          env "C"*env "a"*env "b"*env "d"*env "f"*P*S*((m : ℤ) : ℂ) -
          3*env "C"*env "a"*env "b"*env "d"*env "f"*P*S -
          env "C"*env "b"^2*env "d"*env "f"*P*S^2*((m : ℤ) : ℂ) -
          2*env "C"*env "b"^2*env "d"*env "f"*P*S^2) * hP

/-! ## rubi4142r6Nondeg -/

theorem rubi4142r6Nondeg_real : rubi4142r6Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4142r6Nondeg.conditions rubi4142r6Nondeg.body
    rubi4142r6Nondeg.result rubi4142r6Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4142r6Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4142r6Nondeg])
  have hn1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4142r6Nondeg])
  have hn1v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4142r6Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 3))) (.int 0)) (by simp [rubi4142r6Nondeg])
  have hn3_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "m" + 3 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r6Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have hb2 : -1 ≤ m := by
    have h := hc (.ge (.var "m") (.int (-1))) (by simp [rubi4142r6Nondeg])
    have h' : (-1 : ℝ) ≤ ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      rcases h with h | h <;> linarith
    exact_mod_cast h'
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4142r6Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4142r6Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4142r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4142r6Nondeg, Defined, eval, recEnv, Interp.real, em1,
        ivm1R] at h hn0 hn1 hn3_0 hn3_1 hn3_2 ⊢
    tauto
  · simp only [rubi4142r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        (((((env "a" * env "C") * env "d") + (((env "A" * env "b") * env "c") * (env "m" + 3))) +
        (((env "b" * env "d") * ((env "C" * (env "m" + 2)) + (env "A" * (env "m" + 3)))) *
        Real.sin ((env "e" + (env "f" * t))))) +
        (((-1) *
        ((((2 * env "a") * env "C") * env "d") +
        (((((-1) * env "b") * env "c") * env "C") * (env "m" + 3)))) *
        (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4142r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4142r6Nondeg.result) =
            fun w => (((((((-1) * env "C") * env "d") * Real.cos ((env "e" + (env "f" * w)))) *
            Real.sin ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "b" * env "f") * (env "m" + 3)))⁻¹) + (1 * ((env "b" * (env "m" + 3)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4142r6Nondeg, eval, recEnv, Interp.real, em1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4142r6Nondeg.body =
        (((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) *
        (env "A" + (env "C" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4142r6Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t ((((-1) * env "C") *
        env "d"))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "b" * env "f") * (env "m" + 3)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn3_2c : ((m : ℤ) : ℝ) + 3 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "C"*env "a"*env "d" - 2*env "C"*env "b"*env "d"*S) * hP
    · have hdm : (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ m =
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "C"*env "a"^2*env "d"*env "f"*P -
          env "C"*env "a"*env "b"*env "d"*env "f"*P*S*((m : ℤ) : ℝ) -
          3*env "C"*env "a"*env "b"*env "d"*env "f"*P*S -
          env "C"*env "b"^2*env "d"*env "f"*P*S^2*((m : ℤ) : ℝ) -
          2*env "C"*env "b"^2*env "d"*env "f"*P*S^2) * hP

theorem rubi4142r6Nondeg_complex : rubi4142r6Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4142r6Nondeg.conditions rubi4142r6Nondeg.body
    rubi4142r6Nondeg.result rubi4142r6Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4142r6Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4142r6Nondeg])
  have hn1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4142r6Nondeg])
  have hn1v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4142r6Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 3))) (.int 0)) (by simp [rubi4142r6Nondeg])
  have hn3_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "m" + 3 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r6Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have hb2 : -1 ≤ m := by
    have h := hc (.ge (.var "m") (.int (-1))) (by simp [rubi4142r6Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (-1 : ℝ) ≤ ((m : ℤ) : ℝ) := by
      rcases h with h | h <;> linarith
    exact_mod_cast h'
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4142r6Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4142r6Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4142r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4142r6Nondeg, Defined, eval, recEnv, Interp.complex, em1,
        ivm1C] at h hn0 hn1 hn3_0 hn3_1 hn3_2 ⊢
    tauto
  · simp only [rubi4142r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        (((((env "a" * env "C") * env "d") + (((env "A" * env "b") * env "c") * (env "m" + 3))) +
        (((env "b" * env "d") * ((env "C" * (env "m" + 2)) + (env "A" * (env "m" + 3)))) *
        Complex.sin ((env "e" + (env "f" * t))))) +
        (((-1) *
        ((((2 * env "a") * env "C") * env "d") +
        (((((-1) * env "b") * env "c") * env "C") * (env "m" + 3)))) *
        (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4142r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4142r6Nondeg.result) =
            fun w => (((((((-1) * env "C") * env "d") * Complex.cos ((env "e" + (env "f" * w)))) *
            Complex.sin ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "b" * env "f") * (env "m" + 3)))⁻¹) + (1 * ((env "b" * (env "m" + 3)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4142r6Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4142r6Nondeg.body =
        (((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) *
        (env "A" + (env "C" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4142r6Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t ((((-1) * env "C") *
        env "d"))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "b" * env "f") * (env "m" + 3)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn3_2c : ((m : ℤ) : ℂ) + 3 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "C"*env "a"*env "d" - 2*env "C"*env "b"*env "d"*S) * hP
    · have hdm : (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 1 :=
        by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ m =
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = P
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "C"*env "a"^2*env "d"*env "f"*P -
          env "C"*env "a"*env "b"*env "d"*env "f"*P*S*((m : ℤ) : ℂ) -
          3*env "C"*env "a"*env "b"*env "d"*env "f"*P*S -
          env "C"*env "b"^2*env "d"*env "f"*P*S^2*((m : ℤ) : ℂ) -
          2*env "C"*env "b"^2*env "d"*env "f"*P*S^2) * hP

end OSR.IntegrationRec280
