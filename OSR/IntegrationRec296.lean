import OSR.IntegrationNum1

/-! # Strengthened variants with two integer exponents: explicit terms plus a residual integral

Proofs of RUBI rules whose result is an explicit term with powers `y^m z^n` plus at most one residual
integral. The derivative of the explicit term is built from the rule expression; the integrand is
recovered with `sin² + cos² = 1` (when trigonometric) and the stated parameter relations, separately
for each exponent equal to `0` or not (`linear_combination` coefficients computed by Gröbner
reduction). Rules with `csc`, `cot` or `arctan` are proved over ℝ only. -/

namespace OSR.IntegrationRec296

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

/-! ## rubi4121r16Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4121r16Nondeg_real : rubi4121r16Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi4121r16Nondeg.conditions rubi4121r16Nondeg.body
    rubi4121r16Nondeg.result
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4121r16Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4121r16Nondeg])
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4121r16Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hr2 : ((env "a" * env "d") * env "m") + ((env "b" * env "c") * (env "m" + 1)) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "m")) (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "m") (.int 1)))) (.int 0)) (by simp [rubi4121r16Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc3 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4121r16Nondeg])
  have hn3_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr1 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (-env "d") * hza + (env "c") * hzb)
  have hdb : env "b" ≠ 0 := by
    intro hzb
    have hza : env "a" = 0 := by
      have h2 : env "a" ^ 2 = 0 := by linear_combination (1) * hr1 - (-env "b") * hzb
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (env "c") * hzb + (-env "d") * hza)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r16Nondeg, Defined, eval, Interp.real, hkm] at h
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4121r16Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4121r16Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r16Nondeg, Defined, eval, Interp.real, hkm, ivm1R] at h hn0 hn3_0 hn3_1 hda hdb ⊢
    tauto
  · have hfun : (fun w => eval Interp.real (Function.update env "x" w)
        rubi4121r16Nondeg.result) =
            fun w => (((((-1) * env "d") * Real.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "f" * (env "m" + 1)))⁻¹) := by
      funext w
      simp [rubi4121r16Nondeg, eval, Interp.real, hkm, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4121r16Nondeg.body =
        ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) := by
      simp [rubi4121r16Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((hasDerivAt_const t (((-1) *
        env "d"))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((env "f" * (env "m" + 1)))⁻¹))).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hr2c : ((env "a" * env "d") * ((m : ℤ) : ℝ)) +
        ((env "b" * env "c") * (((m : ℤ) : ℝ) + 1)) - (0) = 0 :=
        by rw [← (intValue?_eq _ _).1 hkm]; exact hr2
    have hn3_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
          add_zero]
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      refine mul_left_cancel₀ hdb ?_
      linear_combination (0) * hP + (0) * hr1 + (-1) * hr2c
    · have hdmm : (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ m =
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m]
      generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      refine mul_left_cancel₀ hda ?_
      linear_combination (-env "a"*env "b"*env "d"*env "f"*Pm*((m : ℤ) : ℝ)) * hP +
          (-env "c"*env "f"*Pm*((m : ℤ) : ℝ) - env "c"*env "f"*Pm) * hr1 +
          (-env "a"*env "f"*Pm*S - env "b"*env "f"*Pm) * hr2c

set_option maxHeartbeats 1000000 in
theorem rubi4121r16Nondeg_complex : rubi4121r16Nondeg.Holds .complex := by
  show AntiderivHoldsUnder Interp.complex "x" rubi4121r16Nondeg.conditions rubi4121r16Nondeg.body
    rubi4121r16Nondeg.result
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4121r16Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4121r16Nondeg])
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4121r16Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hr2 : ((env "a" * env "d") * env "m") + ((env "b" * env "c") * (env "m" + 1)) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "m")) (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "m") (.int 1)))) (.int 0)) (by simp [rubi4121r16Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc3 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4121r16Nondeg])
  have hn3_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr1 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (-env "d") * hza + (env "c") * hzb)
  have hdb : env "b" ≠ 0 := by
    intro hzb
    have hza : env "a" = 0 := by
      have h2 : env "a" ^ 2 = 0 := by linear_combination (1) * hr1 - (-env "b") * hzb
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (env "c") * hzb + (-env "d") * hza)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r16Nondeg, Defined, eval, Interp.complex, hkm] at h
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4121r16Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4121r16Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r16Nondeg, Defined, eval, Interp.complex, hkm,
        ivm1C] at h hn0 hn3_0 hn3_1 hda hdb ⊢
    tauto
  · have hfun : (fun w => eval Interp.complex (Function.update env "x" w)
        rubi4121r16Nondeg.result) =
            fun w => (((((-1) * env "d") * Complex.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "f" * (env "m" + 1)))⁻¹) := by
      funext w
      simp [rubi4121r16Nondeg, eval, Interp.complex, hkm, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4121r16Nondeg.body =
        ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) := by
      simp [rubi4121r16Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((hasDerivAt_const t (((-1) *
        env "d"))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((env "f" * (env "m" + 1)))⁻¹))).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hr2c : ((env "a" * env "d") * ((m : ℤ) : ℂ)) +
        ((env "b" * env "c") * (((m : ℤ) : ℂ) + 1)) - (0) = 0 :=
        by rw [← (intValue?_eq _ _).1 hkm]; exact hr2
    have hn3_1c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
          add_zero]
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      refine mul_left_cancel₀ hdb ?_
      linear_combination (0) * hP + (0) * hr1 + (-1) * hr2c
    · have hdmm : (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m -
        1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ m =
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
            1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
            1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
            1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m]
      generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      refine mul_left_cancel₀ hda ?_
      linear_combination (-env "a"*env "b"*env "d"*env "f"*Pm*((m : ℤ) : ℂ)) * hP +
          (-env "c"*env "f"*Pm*((m : ℤ) : ℂ) - env "c"*env "f"*Pm) * hr1 +
          (-env "a"*env "f"*Pm*S - env "b"*env "f"*Pm) * hr2c

/-! ## rubi4121r18Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4121r18Nondeg_real : rubi4121r18Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4121r18Nondeg.conditions rubi4121r18Nondeg.body
    rubi4121r18Nondeg.result rubi4121r18Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4121r18Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4121r18Nondeg])
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4121r18Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hc3 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4121r18Nondeg])
  have hn3_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr1 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (-env "d") * hza + (env "c") * hzb)
  have hdb : env "b" ≠ 0 := by
    intro hzb
    have hza : env "a" = 0 := by
      have h2 : env "a" ^ 2 = 0 := by linear_combination (1) * hr1 - (-env "b") * hzb
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (env "c") * hzb + (-env "d") * hza)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r18Nondeg, Defined, eval, Interp.real, hkm] at h
  have hb2 : -1 < m := by
    have h := hc (.ge (.var "m") (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1))))) (by simp [rubi4121r18Nondeg])
    have h' : (-1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real, ivm1R] at h
      rcases h with h | h <;> linarith
    exact_mod_cast h'
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4121r18Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4121r18Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r18Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r18Nondeg, Defined, eval, recEnv, Interp.real, hkm,
        ivm1R] at h hn0 hn3_0 hn3_1 hda hdb ⊢
    tauto
  · simp only [rubi4121r18Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4121r18Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r18Nondeg.result) =
            fun w => (((((-1) * env "d") * Real.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "f" * (env "m" + 1)))⁻¹) +
            ((((env "a" * env "d") * env "m") + ((env "b" * env "c") * (env "m" + 1))) *
            ((env "b" * (env "m" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4121r18Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4121r18Nondeg.body =
        ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) := by
      simp [rubi4121r18Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (((-1) *
        env "d"))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((env "f" * (env "m" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hn3_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
          add_zero]
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      ring
    · have hdmm : (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ m =
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m]
      generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "b"^2*env "d"*env "f"*Pm*((m : ℤ) : ℝ)) * hP +
          (env "d"*env "f"*Pm*((m : ℤ) : ℝ)) * hr1

set_option maxHeartbeats 1000000 in
theorem rubi4121r18Nondeg_complex : rubi4121r18Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4121r18Nondeg.conditions rubi4121r18Nondeg.body
    rubi4121r18Nondeg.result rubi4121r18Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4121r18Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4121r18Nondeg])
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4121r18Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hc3 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4121r18Nondeg])
  have hn3_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr1 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (-env "d") * hza + (env "c") * hzb)
  have hdb : env "b" ≠ 0 := by
    intro hzb
    have hza : env "a" = 0 := by
      have h2 : env "a" ^ 2 = 0 := by linear_combination (1) * hr1 - (-env "b") * hzb
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (env "c") * hzb + (-env "d") * hza)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r18Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hb2 : -1 < m := by
    have h := hc (.ge (.var "m") (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1))))) (by simp [rubi4121r18Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, ivm1C, (intValue?_eq _ _).1 hkm,
        Complex.ext_iff] at h
    have h' : (-1 : ℝ) < ((m : ℤ) : ℝ) := by
      rcases h with h | h <;> linarith
    exact_mod_cast h'
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4121r18Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4121r18Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r18Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r18Nondeg, Defined, eval, recEnv, Interp.complex, hkm,
        ivm1C] at h hn0 hn3_0 hn3_1 hda hdb ⊢
    tauto
  · simp only [rubi4121r18Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4121r18Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r18Nondeg.result) =
            fun w => (((((-1) * env "d") * Complex.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "f" * (env "m" + 1)))⁻¹) +
            ((((env "a" * env "d") * env "m") + ((env "b" * env "c") * (env "m" + 1))) *
            ((env "b" * (env "m" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4121r18Nondeg, eval, recEnv, Interp.complex, hkm, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4121r18Nondeg.body =
        ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) := by
      simp [rubi4121r18Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (((-1) *
        env "d"))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((env "f" * (env "m" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hn3_1c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
          add_zero]
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      ring
    · have hdmm : (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m -
        1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ m =
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
            1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
            1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
            1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m]
      generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "b"^2*env "d"*env "f"*Pm*((m : ℤ) : ℂ)) * hP +
          (env "d"*env "f"*Pm*((m : ℤ) : ℂ)) * hr1

/-! ## rubi4131r19Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4131r19Nondeg_real : rubi4131r19Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4131r19Nondeg.conditions rubi4131r19Nondeg.body
    rubi4131r19Nondeg.result rubi4131r19Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4131r19Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4131r19Nondeg])
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4131r19Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hn2 : (env "c") ^ 2 + ((-1) * (env "d") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4131r19Nondeg])
  have hn2v : (env "c") ^ 2 + -(env "d") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4131r19Nondeg])
  have hc5 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))))) (.int 0)) (by simp [rubi4131r19Nondeg])
  have hn5_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc5
  have hn5_1 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc5
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr1 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (-env "d") * hza + (env "c") * hzb)
  have hdb : env "b" ≠ 0 := by
    intro hzb
    have hza : env "a" = 0 := by
      have h2 : env "a" ^ 2 = 0 := by linear_combination (1) * hr1 - (-env "b") * hzb
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (env "c") * hzb + (-env "d") * hza)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4131r19Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4131r19Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hb3 : k < -1 := by
    have h := hc (.gt (.int (-1)) (.var "n")) (by simp [rubi4131r19Nondeg])
    have h' : ((k : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkk]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltk : k < 1 → k < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "n" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4131r19Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4131r19Nondeg, Defined, eval, Interp.real, hkm, hkk] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4131r19Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, emk1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4131r19Nondeg, Defined, eval, recEnv, Interp.real, hkm, emk1, ivm1R,
        iv2R] at h hn0 hn2 hn5_0 hn5_1 hda hdb ⊢
    tauto
  · simp only [rubi4131r19Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 1)) *
        (((env "A" * (((env "a" * env "d") * env "m") + ((env "b" * env "c") * (env "n" + 1)))) +
        (((-1) * env "B") *
        (((env "a" * env "c") * env "m") + ((env "b" * env "d") * (env "n" + 1))))) +
        (((env "b" * ((env "B" * env "c") + (((-1) * env "A") * env "d"))) *
        ((env "m" + env "n") + 2)) * Real.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, emk1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4131r19Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4131r19Nondeg.result) =
            fun w => ((((((env "B" * env "c") + (((-1) * env "A") * env "d")) *
            Real.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * w)))))) ^ (k + 1)) *
            (((env "f" * (env "n" + 1)) * ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹) +
            (1 * (((env "b" * (env "n" + 1)) * ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4131r19Nondeg, eval, recEnv, Interp.real, hkm, emk1, ivm1R, iv2R,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4131r19Nondeg.body =
        (((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k)) *
        (env "A" + (env "B" * Real.sin ((env "e" + (env "f" * t))))) := by
      simp [rubi4131r19Nondeg, eval, Interp.real, hkm, hkk]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((env "B" * env "c") +
        (((-1) * env "A") *
        env "d")))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "f" * (env "n" + 1)) * ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, add_sub_cancel_right]
    have hn5_1c : ((k : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn5_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb3 (by omega)
      · subst hm0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k - 1 :=
            by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "c"*env "d"^2*Pk*((k : ℤ) : ℝ) -
            env "A"*env "c"*env "d"^2*Pk - env "A"*env "d"^3*Pk*S*((k : ℤ) : ℝ) -
            env "A"*env "d"^3*Pk*S + env "B"*env "c"^2*env "d"*Pk*((k : ℤ) : ℝ) +
            env "B"*env "c"^2*env "d"*Pk + env "B"*env "c"*env "d"^2*Pk*S*((k : ℤ) : ℝ) +
            env "B"*env "c"*env "d"^2*Pk*S) * hP + (0) * hr1
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb3 (by omega)
      · have hdmm : (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 1 :=
          by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ m =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k - 1 :=
            by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*((k : ℤ) : ℝ) - env "A"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm - env "A"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) - env "A"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S - env "A"*env "b"^2*env "c"^2*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℝ) - env "A"*env "b"^2*env "c"*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) - 2*env "A"*env "b"^2*env "c"*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) - env "A"*env "b"^2*env "c"*env "d"^2*env "f"*Pk*Pm*S - env "A"*env "b"^2*env "d"^3*env "f"*Pk*Pm*S^2*((k : ℤ) : ℝ) - env "A"*env "b"^2*env "d"^3*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) - env "A"*env "b"^2*env "d"^3*env "f"*Pk*Pm*S^2 + env "B"*env "a"*env "b"*env "c"^2*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℝ) + env "B"*env "a"*env "b"*env "c"^2*env "d"*env "f"*Pk*Pm + env "B"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) + env "B"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*S + env "B"*env "b"^2*env "c"^3*env "f"*Pk*Pm*((m : ℤ) : ℝ) + env "B"*env "b"^2*env "c"^2*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) + 2*env "B"*env "b"^2*env "c"^2*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) + env "B"*env "b"^2*env "c"^2*env "d"*env "f"*Pk*Pm*S + env "B"*env "b"^2*env "c"*env "d"^2*env "f"*Pk*Pm*S^2*((k : ℤ) : ℝ) + env "B"*env "b"^2*env "c"*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) + env "B"*env "b"^2*env "c"*env "d"^2*env "f"*Pk*Pm*S^2) * hP + (env "A"*env "c"^2*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℝ) + 2*env "A"*env "c"*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) + env "A"*env "d"^3*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) - env "B"*env "c"^3*env "f"*Pk*Pm*((m : ℤ) : ℝ) - 2*env "B"*env "c"^2*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) - env "B"*env "c"*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ)) * hr1

set_option maxHeartbeats 1000000 in
theorem rubi4131r19Nondeg_complex : rubi4131r19Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4131r19Nondeg.conditions rubi4131r19Nondeg.body
    rubi4131r19Nondeg.result rubi4131r19Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4131r19Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4131r19Nondeg])
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4131r19Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hn2 : (env "c") ^ 2 + ((-1) * (env "d") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4131r19Nondeg])
  have hn2v : (env "c") ^ 2 + -(env "d") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4131r19Nondeg])
  have hc5 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))))) (.int 0)) (by simp [rubi4131r19Nondeg])
  have hn5_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc5
  have hn5_1 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc5
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr1 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (-env "d") * hza + (env "c") * hzb)
  have hdb : env "b" ≠ 0 := by
    intro hzb
    have hza : env "a" = 0 := by
      have h2 : env "a" ^ 2 = 0 := by linear_combination (1) * hr1 - (-env "b") * hzb
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (env "c") * hzb + (-env "d") * hza)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4131r19Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4131r19Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h
  have hb3 : k < -1 := by
    have h := hc (.gt (.int (-1)) (.var "n")) (by simp [rubi4131r19Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkk, Complex.ext_iff] at h
    have h' : ((k : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltk : k < 1 → k < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "n" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4131r19Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4131r19Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4131r19Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm, emk1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4131r19Nondeg, Defined, eval, recEnv, Interp.complex, hkm, emk1, ivm1C,
        iv2C] at h hn0 hn2 hn5_0 hn5_1 hda hdb ⊢
    tauto
  · simp only [rubi4131r19Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 1)) *
        (((env "A" * (((env "a" * env "d") * env "m") + ((env "b" * env "c") * (env "n" + 1)))) +
        (((-1) * env "B") *
        (((env "a" * env "c") * env "m") + ((env "b" * env "d") * (env "n" + 1))))) +
        (((env "b" * ((env "B" * env "c") + (((-1) * env "A") * env "d"))) *
        ((env "m" + env "n") + 2)) * Complex.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, emk1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4131r19Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4131r19Nondeg.result) =
            fun w => ((((((env "B" * env "c") + (((-1) * env "A") * env "d")) *
            Complex.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (k + 1)) *
            (((env "f" * (env "n" + 1)) * ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹) +
            (1 * (((env "b" * (env "n" + 1)) * ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4131r19Nondeg, eval, recEnv, Interp.complex, hkm, emk1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4131r19Nondeg.body =
        (((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k)) *
        (env "A" + (env "B" * Complex.sin ((env "e" + (env "f" * t))))) := by
      simp [rubi4131r19Nondeg, eval, Interp.complex, hkm, hkk]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((env "B" * env "c") +
        (((-1) * env "A") *
        env "d")))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "f" * (env "n" + 1)) * ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, add_sub_cancel_right]
    have hn5_1c : ((k : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn5_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb3 (by omega)
      · subst hm0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k -
            1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "c"*env "d"^2*Pk*((k : ℤ) : ℂ) -
            env "A"*env "c"*env "d"^2*Pk - env "A"*env "d"^3*Pk*S*((k : ℤ) : ℂ) -
            env "A"*env "d"^3*Pk*S + env "B"*env "c"^2*env "d"*Pk*((k : ℤ) : ℂ) +
            env "B"*env "c"^2*env "d"*Pk + env "B"*env "c"*env "d"^2*Pk*S*((k : ℤ) : ℂ) +
            env "B"*env "c"*env "d"^2*Pk*S) * hP + (0) * hr1
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb3 (by omega)
      · have hdmm : (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m -
          1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ m =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k -
            1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*((k : ℤ) : ℂ) - env "A"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm - env "A"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) - env "A"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S - env "A"*env "b"^2*env "c"^2*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℂ) - env "A"*env "b"^2*env "c"*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) - 2*env "A"*env "b"^2*env "c"*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) - env "A"*env "b"^2*env "c"*env "d"^2*env "f"*Pk*Pm*S - env "A"*env "b"^2*env "d"^3*env "f"*Pk*Pm*S^2*((k : ℤ) : ℂ) - env "A"*env "b"^2*env "d"^3*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) - env "A"*env "b"^2*env "d"^3*env "f"*Pk*Pm*S^2 + env "B"*env "a"*env "b"*env "c"^2*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℂ) + env "B"*env "a"*env "b"*env "c"^2*env "d"*env "f"*Pk*Pm + env "B"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) + env "B"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*S + env "B"*env "b"^2*env "c"^3*env "f"*Pk*Pm*((m : ℤ) : ℂ) + env "B"*env "b"^2*env "c"^2*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) + 2*env "B"*env "b"^2*env "c"^2*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) + env "B"*env "b"^2*env "c"^2*env "d"*env "f"*Pk*Pm*S + env "B"*env "b"^2*env "c"*env "d"^2*env "f"*Pk*Pm*S^2*((k : ℤ) : ℂ) + env "B"*env "b"^2*env "c"*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) + env "B"*env "b"^2*env "c"*env "d"^2*env "f"*Pk*Pm*S^2) * hP + (env "A"*env "c"^2*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℂ) + 2*env "A"*env "c"*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) + env "A"*env "d"^3*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) - env "B"*env "c"^3*env "f"*Pk*Pm*((m : ℤ) : ℂ) - 2*env "B"*env "c"^2*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) - env "B"*env "c"*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ)) * hr1

/-! ## rubi4142r15Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4142r15Nondeg_real : rubi4142r15Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4142r15Nondeg.conditions rubi4142r15Nondeg.body
    rubi4142r15Nondeg.result rubi4142r15Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4142r15Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4142r15Nondeg])
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4142r15Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hn2 : (env "c") ^ 2 + ((-1) * (env "d") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4142r15Nondeg])
  have hn2v : (env "c") ^ 2 + -(env "d") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4142r15Nondeg])
  have hc5 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))))) (.int 0)) (by simp [rubi4142r15Nondeg])
  have hn5_0 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc5
  have hn5_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc5
  have hn5_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc5
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr1 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (-env "d") * hza + (env "c") * hzb)
  have hdb : env "b" ≠ 0 := by
    intro hzb
    have hza : env "a" = 0 := by
      have h2 : env "a" ^ 2 = 0 := by linear_combination (1) * hr1 - (-env "b") * hzb
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (env "c") * hzb + (-env "d") * hza)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r15Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r15Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h
  have hb3 : -1 < m := by
    have h := hc (.ge (.var "m") (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1))))) (by simp [rubi4142r15Nondeg])
    have h' : (-1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real, ivm1R] at h
      rcases h with h | h <;> linarith
    exact_mod_cast h'
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "n" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4142r15Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4142r15Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4142r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, emk1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4142r15Nondeg, Defined, eval, recEnv, Interp.real, hkm, emk1, ivm1R,
        iv2R] at h hn0 hn2 hn5_0 hn5_1 hn5_2 hda hdb ⊢
    tauto
  · simp only [rubi4142r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 1)) *
        ((((env "A" * env "d") *
        (((env "a" * env "d") * env "m") + ((env "b" * env "c") * (env "n" + 1)))) +
        (((env "c" * env "C") + (((-1) * env "B") * env "d")) *
        (((env "a" * env "c") * env "m") + ((env "b" * env "d") * (env "n" + 1))))) +
        ((env "b" *
        (((env "d" * ((env "B" * env "c") + (((-1) * env "A") * env "d"))) *
        ((env "m" + env "n") + 2)) +
        (((-1) * env "C") *
        (((env "c") ^ 2 * (env "m" + 1)) + ((env "d") ^ 2 * (env "n" + 1)))))) *
        Real.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, emk1, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4142r15Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4142r15Nondeg.result) =
            fun w => ((((((-1) *
            ((((env "c") ^ 2 * env "C") + ((((-1) * env "B") * env "c") * env "d")) +
            (env "A" * (env "d") ^ 2))) * Real.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * w)))))) ^ (k + 1)) *
            ((((env "d" * env "f") * (env "n" + 1)) *
            ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹) +
            (1 * ((((env "b" * env "d") * (env "n" + 1)) *
            ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4142r15Nondeg, eval, recEnv, Interp.real, hkm, emk1, ivm1R, iv2R,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4142r15Nondeg.body =
        (((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k)) *
        ((env "A" + (env "B" * Real.sin ((env "e" + (env "f" * t))))) +
        (env "C" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4142r15Nondeg, eval, Interp.real, hkm, hkk, iv2R]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        ((((env "c") ^ 2 * env "C") + ((((-1) * env "B") * env "c") * env "d")) +
        (env "A" *
        (env "d") ^ 2))))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((((env "d" * env "f") * (env "n" + 1)) * ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, add_sub_cancel_right]
    have hn5_2c : ((k : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn5_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        subst hk0
        simp only [zero_add, zero_sub, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "d"^3 + env "B"*env "c"*env "d"^2 -
            env "C"*env "c"^2*env "d") * hP + (0) * hr1
      · subst hm0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k - 1 :=
            by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "c"*env "d"^3*Pk*((k : ℤ) : ℝ) -
            env "A"*env "c"*env "d"^3*Pk - env "A"*env "d"^4*Pk*S*((k : ℤ) : ℝ) -
            env "A"*env "d"^4*Pk*S + env "B"*env "c"^2*env "d"^2*Pk*((k : ℤ) : ℝ) +
            env "B"*env "c"^2*env "d"^2*Pk + env "B"*env "c"*env "d"^3*Pk*S*((k : ℤ) : ℝ) +
            env "B"*env "c"*env "d"^3*Pk*S - env "C"*env "c"^3*env "d"*Pk*((k : ℤ) : ℝ) -
            env "C"*env "c"^3*env "d"*Pk - env "C"*env "c"^2*env "d"^2*Pk*S*((k : ℤ) : ℝ) -
            env "C"*env "c"^2*env "d"^2*Pk*S) * hP + (0) * hr1
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 1 :=
            by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ m =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "a"*env "b"*env "d"^3*Pm -
            env "A"*env "b"^2*env "c"*env "d"^2*Pm*((m : ℤ) : ℝ) -
            env "A"*env "b"^2*env "d"^3*Pm*S*((m : ℤ) : ℝ) - env "A"*env "b"^2*env "d"^3*Pm*S +
            env "B"*env "a"*env "b"*env "c"*env "d"^2*Pm +
            env "B"*env "b"^2*env "c"^2*env "d"*Pm*((m : ℤ) : ℝ) +
            env "B"*env "b"^2*env "c"*env "d"^2*Pm*S*((m : ℤ) : ℝ) +
            env "B"*env "b"^2*env "c"*env "d"^2*Pm*S -
            env "C"*env "a"*env "b"*env "c"^2*env "d"*Pm -
            env "C"*env "b"^2*env "c"^3*Pm*((m : ℤ) : ℝ) -
            env "C"*env "b"^2*env "c"^2*env "d"*Pm*S*((m : ℤ) : ℝ) -
            env "C"*env "b"^2*env "c"^2*env "d"*Pm*S) * hP +
            (env "A"*env "c"*env "d"^2*Pm*((m : ℤ) : ℝ) + env "A"*env "d"^3*Pm*S*((m : ℤ) : ℝ) -
            env "B"*env "c"^2*env "d"*Pm*((m : ℤ) : ℝ) -
            env "B"*env "c"*env "d"^2*Pm*S*((m : ℤ) : ℝ) + env "C"*env "c"^3*Pm*((m : ℤ) : ℝ) +
            env "C"*env "c"^2*env "d"*Pm*S*((m : ℤ) : ℝ)) * hr1
      · have hdmm : (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 1 :=
          by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ m =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k - 1 :=
            by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "a"*env "b"*env "c"*env "d"^3*env "f"*Pk*Pm*((k : ℤ) : ℝ) - env "A"*env "a"*env "b"*env "c"*env "d"^3*env "f"*Pk*Pm - env "A"*env "a"*env "b"*env "d"^4*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) - env "A"*env "a"*env "b"*env "d"^4*env "f"*Pk*Pm*S - env "A"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*((m : ℤ) : ℝ) - env "A"*env "b"^2*env "c"*env "d"^3*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) - 2*env "A"*env "b"^2*env "c"*env "d"^3*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) - env "A"*env "b"^2*env "c"*env "d"^3*env "f"*Pk*Pm*S - env "A"*env "b"^2*env "d"^4*env "f"*Pk*Pm*S^2*((k : ℤ) : ℝ) - env "A"*env "b"^2*env "d"^4*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) - env "A"*env "b"^2*env "d"^4*env "f"*Pk*Pm*S^2 + env "B"*env "a"*env "b"*env "c"^2*env "d"^2*env "f"*Pk*Pm*((k : ℤ) : ℝ) + env "B"*env "a"*env "b"*env "c"^2*env "d"^2*env "f"*Pk*Pm + env "B"*env "a"*env "b"*env "c"*env "d"^3*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) + env "B"*env "a"*env "b"*env "c"*env "d"^3*env "f"*Pk*Pm*S + env "B"*env "b"^2*env "c"^3*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℝ) + env "B"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) + 2*env "B"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) + env "B"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*S + env "B"*env "b"^2*env "c"*env "d"^3*env "f"*Pk*Pm*S^2*((k : ℤ) : ℝ) + env "B"*env "b"^2*env "c"*env "d"^3*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) + env "B"*env "b"^2*env "c"*env "d"^3*env "f"*Pk*Pm*S^2 - env "C"*env "a"*env "b"*env "c"^3*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℝ) - env "C"*env "a"*env "b"*env "c"^3*env "d"*env "f"*Pk*Pm - env "C"*env "a"*env "b"*env "c"^2*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) - env "C"*env "a"*env "b"*env "c"^2*env "d"^2*env "f"*Pk*Pm*S - env "C"*env "b"^2*env "c"^4*env "f"*Pk*Pm*((m : ℤ) : ℝ) - env "C"*env "b"^2*env "c"^3*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) - 2*env "C"*env "b"^2*env "c"^3*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) - env "C"*env "b"^2*env "c"^3*env "d"*env "f"*Pk*Pm*S - env "C"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*S^2*((k : ℤ) : ℝ) - env "C"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) - env "C"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*S^2) * hP + (env "A"*env "c"^2*env "d"^2*env "f"*Pk*Pm*((m : ℤ) : ℝ) + 2*env "A"*env "c"*env "d"^3*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) + env "A"*env "d"^4*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) - env "B"*env "c"^3*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℝ) - 2*env "B"*env "c"^2*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) - env "B"*env "c"*env "d"^3*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) + env "C"*env "c"^4*env "f"*Pk*Pm*((m : ℤ) : ℝ) + 2*env "C"*env "c"^3*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) + env "C"*env "c"^2*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ)) * hr1

set_option maxHeartbeats 1000000 in
theorem rubi4142r15Nondeg_complex : rubi4142r15Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4142r15Nondeg.conditions rubi4142r15Nondeg.body
    rubi4142r15Nondeg.result rubi4142r15Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4142r15Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4142r15Nondeg])
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4142r15Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hn2 : (env "c") ^ 2 + ((-1) * (env "d") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4142r15Nondeg])
  have hn2v : (env "c") ^ 2 + -(env "d") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4142r15Nondeg])
  have hc5 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))))) (.int 0)) (by simp [rubi4142r15Nondeg])
  have hn5_0 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc5
  have hn5_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc5
  have hn5_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc5
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr1 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (-env "d") * hza + (env "c") * hzb)
  have hdb : env "b" ≠ 0 := by
    intro hzb
    have hza : env "a" = 0 := by
      have h2 : env "a" ^ 2 = 0 := by linear_combination (1) * hr1 - (-env "b") * hzb
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (env "c") * hzb + (-env "d") * hza)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r15Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r15Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h
  have hb3 : -1 < m := by
    have h := hc (.ge (.var "m") (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1))))) (by simp [rubi4142r15Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, ivm1C, (intValue?_eq _ _).1 hkm,
        Complex.ext_iff] at h
    have h' : (-1 : ℝ) < ((m : ℤ) : ℝ) := by
      rcases h with h | h <;> linarith
    exact_mod_cast h'
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "n" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4142r15Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4142r15Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4142r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm, emk1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4142r15Nondeg, Defined, eval, recEnv, Interp.complex, hkm, emk1, ivm1C,
        iv2C] at h hn0 hn2 hn5_0 hn5_1 hn5_2 hda hdb ⊢
    tauto
  · simp only [rubi4142r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 1)) *
        ((((env "A" * env "d") *
        (((env "a" * env "d") * env "m") + ((env "b" * env "c") * (env "n" + 1)))) +
        (((env "c" * env "C") + (((-1) * env "B") * env "d")) *
        (((env "a" * env "c") * env "m") + ((env "b" * env "d") * (env "n" + 1))))) +
        ((env "b" *
        (((env "d" * ((env "B" * env "c") + (((-1) * env "A") * env "d"))) *
        ((env "m" + env "n") + 2)) +
        (((-1) * env "C") *
        (((env "c") ^ 2 * (env "m" + 1)) + ((env "d") ^ 2 * (env "n" + 1)))))) *
        Complex.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, emk1, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4142r15Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4142r15Nondeg.result) =
            fun w => ((((((-1) *
            ((((env "c") ^ 2 * env "C") + ((((-1) * env "B") * env "c") * env "d")) +
            (env "A" * (env "d") ^ 2))) * Complex.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (k + 1)) *
            ((((env "d" * env "f") * (env "n" + 1)) *
            ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹) +
            (1 * ((((env "b" * env "d") * (env "n" + 1)) *
            ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4142r15Nondeg, eval, recEnv, Interp.complex, hkm, emk1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4142r15Nondeg.body =
        (((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k)) *
        ((env "A" + (env "B" * Complex.sin ((env "e" + (env "f" * t))))) +
        (env "C" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4142r15Nondeg, eval, Interp.complex, hkm, hkk, iv2C]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        ((((env "c") ^ 2 * env "C") + ((((-1) * env "B") * env "c") * env "d")) +
        (env "A" *
        (env "d") ^ 2))))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((((env "d" * env "f") * (env "n" + 1)) * ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, add_sub_cancel_right]
    have hn5_2c : ((k : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn5_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        subst hk0
        simp only [zero_add, zero_sub, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "d"^3 + env "B"*env "c"*env "d"^2 -
            env "C"*env "c"^2*env "d") * hP + (0) * hr1
      · subst hm0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k -
            1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "c"*env "d"^3*Pk*((k : ℤ) : ℂ) -
            env "A"*env "c"*env "d"^3*Pk - env "A"*env "d"^4*Pk*S*((k : ℤ) : ℂ) -
            env "A"*env "d"^4*Pk*S + env "B"*env "c"^2*env "d"^2*Pk*((k : ℤ) : ℂ) +
            env "B"*env "c"^2*env "d"^2*Pk + env "B"*env "c"*env "d"^3*Pk*S*((k : ℤ) : ℂ) +
            env "B"*env "c"*env "d"^3*Pk*S - env "C"*env "c"^3*env "d"*Pk*((k : ℤ) : ℂ) -
            env "C"*env "c"^3*env "d"*Pk - env "C"*env "c"^2*env "d"^2*Pk*S*((k : ℤ) : ℂ) -
            env "C"*env "c"^2*env "d"^2*Pk*S) * hP + (0) * hr1
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m -
            1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ m =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "a"*env "b"*env "d"^3*Pm -
            env "A"*env "b"^2*env "c"*env "d"^2*Pm*((m : ℤ) : ℂ) -
            env "A"*env "b"^2*env "d"^3*Pm*S*((m : ℤ) : ℂ) - env "A"*env "b"^2*env "d"^3*Pm*S +
            env "B"*env "a"*env "b"*env "c"*env "d"^2*Pm +
            env "B"*env "b"^2*env "c"^2*env "d"*Pm*((m : ℤ) : ℂ) +
            env "B"*env "b"^2*env "c"*env "d"^2*Pm*S*((m : ℤ) : ℂ) +
            env "B"*env "b"^2*env "c"*env "d"^2*Pm*S -
            env "C"*env "a"*env "b"*env "c"^2*env "d"*Pm -
            env "C"*env "b"^2*env "c"^3*Pm*((m : ℤ) : ℂ) -
            env "C"*env "b"^2*env "c"^2*env "d"*Pm*S*((m : ℤ) : ℂ) -
            env "C"*env "b"^2*env "c"^2*env "d"*Pm*S) * hP +
            (env "A"*env "c"*env "d"^2*Pm*((m : ℤ) : ℂ) + env "A"*env "d"^3*Pm*S*((m : ℤ) : ℂ) -
            env "B"*env "c"^2*env "d"*Pm*((m : ℤ) : ℂ) -
            env "B"*env "c"*env "d"^2*Pm*S*((m : ℤ) : ℂ) + env "C"*env "c"^3*Pm*((m : ℤ) : ℂ) +
            env "C"*env "c"^2*env "d"*Pm*S*((m : ℤ) : ℂ)) * hr1
      · have hdmm : (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m -
          1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ m =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k -
            1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "a"*env "b"*env "c"*env "d"^3*env "f"*Pk*Pm*((k : ℤ) : ℂ) - env "A"*env "a"*env "b"*env "c"*env "d"^3*env "f"*Pk*Pm - env "A"*env "a"*env "b"*env "d"^4*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) - env "A"*env "a"*env "b"*env "d"^4*env "f"*Pk*Pm*S - env "A"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*((m : ℤ) : ℂ) - env "A"*env "b"^2*env "c"*env "d"^3*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) - 2*env "A"*env "b"^2*env "c"*env "d"^3*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) - env "A"*env "b"^2*env "c"*env "d"^3*env "f"*Pk*Pm*S - env "A"*env "b"^2*env "d"^4*env "f"*Pk*Pm*S^2*((k : ℤ) : ℂ) - env "A"*env "b"^2*env "d"^4*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) - env "A"*env "b"^2*env "d"^4*env "f"*Pk*Pm*S^2 + env "B"*env "a"*env "b"*env "c"^2*env "d"^2*env "f"*Pk*Pm*((k : ℤ) : ℂ) + env "B"*env "a"*env "b"*env "c"^2*env "d"^2*env "f"*Pk*Pm + env "B"*env "a"*env "b"*env "c"*env "d"^3*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) + env "B"*env "a"*env "b"*env "c"*env "d"^3*env "f"*Pk*Pm*S + env "B"*env "b"^2*env "c"^3*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℂ) + env "B"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) + 2*env "B"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) + env "B"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*S + env "B"*env "b"^2*env "c"*env "d"^3*env "f"*Pk*Pm*S^2*((k : ℤ) : ℂ) + env "B"*env "b"^2*env "c"*env "d"^3*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) + env "B"*env "b"^2*env "c"*env "d"^3*env "f"*Pk*Pm*S^2 - env "C"*env "a"*env "b"*env "c"^3*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℂ) - env "C"*env "a"*env "b"*env "c"^3*env "d"*env "f"*Pk*Pm - env "C"*env "a"*env "b"*env "c"^2*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) - env "C"*env "a"*env "b"*env "c"^2*env "d"^2*env "f"*Pk*Pm*S - env "C"*env "b"^2*env "c"^4*env "f"*Pk*Pm*((m : ℤ) : ℂ) - env "C"*env "b"^2*env "c"^3*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) - 2*env "C"*env "b"^2*env "c"^3*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) - env "C"*env "b"^2*env "c"^3*env "d"*env "f"*Pk*Pm*S - env "C"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*S^2*((k : ℤ) : ℂ) - env "C"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) - env "C"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*S^2) * hP + (env "A"*env "c"^2*env "d"^2*env "f"*Pk*Pm*((m : ℤ) : ℂ) + 2*env "A"*env "c"*env "d"^3*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) + env "A"*env "d"^4*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) - env "B"*env "c"^3*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℂ) - 2*env "B"*env "c"^2*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) - env "B"*env "c"*env "d"^3*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) + env "C"*env "c"^4*env "f"*Pk*Pm*((m : ℤ) : ℂ) + 2*env "C"*env "c"^3*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) + env "C"*env "c"^2*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ)) * hr1

/-! ## rubi4142r16Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4142r16Nondeg_real : rubi4142r16Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4142r16Nondeg.conditions rubi4142r16Nondeg.body
    rubi4142r16Nondeg.result rubi4142r16Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4142r16Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4142r16Nondeg])
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4142r16Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hn2 : (env "c") ^ 2 + ((-1) * (env "d") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4142r16Nondeg])
  have hn2v : (env "c") ^ 2 + -(env "d") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4142r16Nondeg])
  have hc5 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))))) (.int 0)) (by simp [rubi4142r16Nondeg])
  have hn5_0 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc5
  have hn5_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc5
  have hn5_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc5
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr1 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (-env "d") * hza + (env "c") * hzb)
  have hdb : env "b" ≠ 0 := by
    intro hzb
    have hza : env "a" = 0 := by
      have h2 : env "a" ^ 2 = 0 := by linear_combination (1) * hr1 - (-env "b") * hzb
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (env "c") * hzb + (-env "d") * hza)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r16Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r16Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h
  have hb3 : -1 < m := by
    have h := hc (.ge (.var "m") (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1))))) (by simp [rubi4142r16Nondeg])
    have h' : (-1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real, ivm1R] at h
      rcases h with h | h <;> linarith
    exact_mod_cast h'
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "n" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4142r16Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4142r16Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4142r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, emk1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4142r16Nondeg, Defined, eval, recEnv, Interp.real, hkm, emk1, ivm1R,
        iv2R] at h hn0 hn2 hn5_0 hn5_1 hn5_2 hda hdb ⊢
    tauto
  · simp only [rubi4142r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 1)) *
        ((((env "A" * env "d") *
        (((env "a" * env "d") * env "m") + ((env "b" * env "c") * (env "n" + 1)))) +
        ((env "c" * env "C") *
        (((env "a" * env "c") * env "m") + ((env "b" * env "d") * (env "n" + 1))))) +
        ((((-1) * env "b") *
        (((env "A" * (env "d") ^ 2) * ((env "m" + env "n") + 2)) +
        (env "C" * (((env "c") ^ 2 * (env "m" + 1)) + ((env "d") ^ 2 * (env "n" + 1)))))) *
        Real.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, emk1, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4142r16Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4142r16Nondeg.result) =
            fun w => ((((((-1) * (((env "c") ^ 2 * env "C") + (env "A" * (env "d") ^ 2))) *
            Real.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * w)))))) ^ (k + 1)) *
            ((((env "d" * env "f") * (env "n" + 1)) *
            ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹) +
            (1 * ((((env "b" * env "d") * (env "n" + 1)) *
            ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4142r16Nondeg, eval, recEnv, Interp.real, hkm, emk1, ivm1R, iv2R,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4142r16Nondeg.body =
        (((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k)) *
        (env "A" + (env "C" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4142r16Nondeg, eval, Interp.real, hkm, hkk, iv2R]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        (((env "c") ^ 2 * env "C") +
        (env "A" *
        (env "d") ^ 2))))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((((env "d" * env "f") * (env "n" + 1)) * ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, add_sub_cancel_right]
    have hn5_2c : ((k : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn5_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        subst hk0
        simp only [zero_add, zero_sub, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "d"^3 - env "C"*env "c"^2*env "d") * hP + (0) * hr1
      · subst hm0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k - 1 :=
            by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "c"*env "d"^3*Pk*((k : ℤ) : ℝ) -
            env "A"*env "c"*env "d"^3*Pk - env "A"*env "d"^4*Pk*S*((k : ℤ) : ℝ) -
            env "A"*env "d"^4*Pk*S - env "C"*env "c"^3*env "d"*Pk*((k : ℤ) : ℝ) -
            env "C"*env "c"^3*env "d"*Pk - env "C"*env "c"^2*env "d"^2*Pk*S*((k : ℤ) : ℝ) -
            env "C"*env "c"^2*env "d"^2*Pk*S) * hP + (0) * hr1
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 1 :=
            by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ m =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "a"*env "b"*env "d"^3*Pm -
            env "A"*env "b"^2*env "c"*env "d"^2*Pm*((m : ℤ) : ℝ) -
            env "A"*env "b"^2*env "d"^3*Pm*S*((m : ℤ) : ℝ) - env "A"*env "b"^2*env "d"^3*Pm*S -
            env "C"*env "a"*env "b"*env "c"^2*env "d"*Pm -
            env "C"*env "b"^2*env "c"^3*Pm*((m : ℤ) : ℝ) -
            env "C"*env "b"^2*env "c"^2*env "d"*Pm*S*((m : ℤ) : ℝ) -
            env "C"*env "b"^2*env "c"^2*env "d"*Pm*S) * hP +
            (env "A"*env "c"*env "d"^2*Pm*((m : ℤ) : ℝ) + env "A"*env "d"^3*Pm*S*((m : ℤ) : ℝ) +
            env "C"*env "c"^3*Pm*((m : ℤ) : ℝ) + env "C"*env "c"^2*env "d"*Pm*S*((m : ℤ) : ℝ)) * hr1
      · have hdmm : (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 1 :=
          by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ m =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k - 1 :=
            by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "a"*env "b"*env "c"*env "d"^3*env "f"*Pk*Pm*((k : ℤ) : ℝ) - env "A"*env "a"*env "b"*env "c"*env "d"^3*env "f"*Pk*Pm - env "A"*env "a"*env "b"*env "d"^4*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) - env "A"*env "a"*env "b"*env "d"^4*env "f"*Pk*Pm*S - env "A"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*((m : ℤ) : ℝ) - env "A"*env "b"^2*env "c"*env "d"^3*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) - 2*env "A"*env "b"^2*env "c"*env "d"^3*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) - env "A"*env "b"^2*env "c"*env "d"^3*env "f"*Pk*Pm*S - env "A"*env "b"^2*env "d"^4*env "f"*Pk*Pm*S^2*((k : ℤ) : ℝ) - env "A"*env "b"^2*env "d"^4*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) - env "A"*env "b"^2*env "d"^4*env "f"*Pk*Pm*S^2 - env "C"*env "a"*env "b"*env "c"^3*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℝ) - env "C"*env "a"*env "b"*env "c"^3*env "d"*env "f"*Pk*Pm - env "C"*env "a"*env "b"*env "c"^2*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) - env "C"*env "a"*env "b"*env "c"^2*env "d"^2*env "f"*Pk*Pm*S - env "C"*env "b"^2*env "c"^4*env "f"*Pk*Pm*((m : ℤ) : ℝ) - env "C"*env "b"^2*env "c"^3*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) - 2*env "C"*env "b"^2*env "c"^3*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) - env "C"*env "b"^2*env "c"^3*env "d"*env "f"*Pk*Pm*S - env "C"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*S^2*((k : ℤ) : ℝ) - env "C"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) - env "C"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*S^2) * hP + (env "A"*env "c"^2*env "d"^2*env "f"*Pk*Pm*((m : ℤ) : ℝ) + 2*env "A"*env "c"*env "d"^3*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) + env "A"*env "d"^4*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) + env "C"*env "c"^4*env "f"*Pk*Pm*((m : ℤ) : ℝ) + 2*env "C"*env "c"^3*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) + env "C"*env "c"^2*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ)) * hr1

set_option maxHeartbeats 1000000 in
theorem rubi4142r16Nondeg_complex : rubi4142r16Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4142r16Nondeg.conditions rubi4142r16Nondeg.body
    rubi4142r16Nondeg.result rubi4142r16Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4142r16Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4142r16Nondeg])
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4142r16Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hn2 : (env "c") ^ 2 + ((-1) * (env "d") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4142r16Nondeg])
  have hn2v : (env "c") ^ 2 + -(env "d") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4142r16Nondeg])
  have hc5 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))))) (.int 0)) (by simp [rubi4142r16Nondeg])
  have hn5_0 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc5
  have hn5_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc5
  have hn5_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc5
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr1 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (-env "d") * hza + (env "c") * hzb)
  have hdb : env "b" ≠ 0 := by
    intro hzb
    have hza : env "a" = 0 := by
      have h2 : env "a" ^ 2 = 0 := by linear_combination (1) * hr1 - (-env "b") * hzb
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (env "c") * hzb + (-env "d") * hza)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r16Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r16Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h
  have hb3 : -1 < m := by
    have h := hc (.ge (.var "m") (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1))))) (by simp [rubi4142r16Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, ivm1C, (intValue?_eq _ _).1 hkm,
        Complex.ext_iff] at h
    have h' : (-1 : ℝ) < ((m : ℤ) : ℝ) := by
      rcases h with h | h <;> linarith
    exact_mod_cast h'
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "n" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4142r16Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4142r16Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4142r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm, emk1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4142r16Nondeg, Defined, eval, recEnv, Interp.complex, hkm, emk1, ivm1C,
        iv2C] at h hn0 hn2 hn5_0 hn5_1 hn5_2 hda hdb ⊢
    tauto
  · simp only [rubi4142r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 1)) *
        ((((env "A" * env "d") *
        (((env "a" * env "d") * env "m") + ((env "b" * env "c") * (env "n" + 1)))) +
        ((env "c" * env "C") *
        (((env "a" * env "c") * env "m") + ((env "b" * env "d") * (env "n" + 1))))) +
        ((((-1) * env "b") *
        (((env "A" * (env "d") ^ 2) * ((env "m" + env "n") + 2)) +
        (env "C" * (((env "c") ^ 2 * (env "m" + 1)) + ((env "d") ^ 2 * (env "n" + 1)))))) *
        Complex.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, emk1, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4142r16Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4142r16Nondeg.result) =
            fun w => ((((((-1) * (((env "c") ^ 2 * env "C") + (env "A" * (env "d") ^ 2))) *
            Complex.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (k + 1)) *
            ((((env "d" * env "f") * (env "n" + 1)) *
            ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹) +
            (1 * ((((env "b" * env "d") * (env "n" + 1)) *
            ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4142r16Nondeg, eval, recEnv, Interp.complex, hkm, emk1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4142r16Nondeg.body =
        (((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k)) *
        (env "A" + (env "C" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4142r16Nondeg, eval, Interp.complex, hkm, hkk, iv2C]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        (((env "c") ^ 2 * env "C") +
        (env "A" *
        (env "d") ^ 2))))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((((env "d" * env "f") * (env "n" + 1)) * ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, add_sub_cancel_right]
    have hn5_2c : ((k : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn5_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        subst hk0
        simp only [zero_add, zero_sub, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "d"^3 - env "C"*env "c"^2*env "d") * hP + (0) * hr1
      · subst hm0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k -
            1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "c"*env "d"^3*Pk*((k : ℤ) : ℂ) -
            env "A"*env "c"*env "d"^3*Pk - env "A"*env "d"^4*Pk*S*((k : ℤ) : ℂ) -
            env "A"*env "d"^4*Pk*S - env "C"*env "c"^3*env "d"*Pk*((k : ℤ) : ℂ) -
            env "C"*env "c"^3*env "d"*Pk - env "C"*env "c"^2*env "d"^2*Pk*S*((k : ℤ) : ℂ) -
            env "C"*env "c"^2*env "d"^2*Pk*S) * hP + (0) * hr1
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m -
            1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ m =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "a"*env "b"*env "d"^3*Pm -
            env "A"*env "b"^2*env "c"*env "d"^2*Pm*((m : ℤ) : ℂ) -
            env "A"*env "b"^2*env "d"^3*Pm*S*((m : ℤ) : ℂ) - env "A"*env "b"^2*env "d"^3*Pm*S -
            env "C"*env "a"*env "b"*env "c"^2*env "d"*Pm -
            env "C"*env "b"^2*env "c"^3*Pm*((m : ℤ) : ℂ) -
            env "C"*env "b"^2*env "c"^2*env "d"*Pm*S*((m : ℤ) : ℂ) -
            env "C"*env "b"^2*env "c"^2*env "d"*Pm*S) * hP +
            (env "A"*env "c"*env "d"^2*Pm*((m : ℤ) : ℂ) + env "A"*env "d"^3*Pm*S*((m : ℤ) : ℂ) +
            env "C"*env "c"^3*Pm*((m : ℤ) : ℂ) + env "C"*env "c"^2*env "d"*Pm*S*((m : ℤ) : ℂ)) * hr1
      · have hdmm : (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m -
          1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ m =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k -
            1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "a"*env "b"*env "c"*env "d"^3*env "f"*Pk*Pm*((k : ℤ) : ℂ) - env "A"*env "a"*env "b"*env "c"*env "d"^3*env "f"*Pk*Pm - env "A"*env "a"*env "b"*env "d"^4*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) - env "A"*env "a"*env "b"*env "d"^4*env "f"*Pk*Pm*S - env "A"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*((m : ℤ) : ℂ) - env "A"*env "b"^2*env "c"*env "d"^3*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) - 2*env "A"*env "b"^2*env "c"*env "d"^3*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) - env "A"*env "b"^2*env "c"*env "d"^3*env "f"*Pk*Pm*S - env "A"*env "b"^2*env "d"^4*env "f"*Pk*Pm*S^2*((k : ℤ) : ℂ) - env "A"*env "b"^2*env "d"^4*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) - env "A"*env "b"^2*env "d"^4*env "f"*Pk*Pm*S^2 - env "C"*env "a"*env "b"*env "c"^3*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℂ) - env "C"*env "a"*env "b"*env "c"^3*env "d"*env "f"*Pk*Pm - env "C"*env "a"*env "b"*env "c"^2*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) - env "C"*env "a"*env "b"*env "c"^2*env "d"^2*env "f"*Pk*Pm*S - env "C"*env "b"^2*env "c"^4*env "f"*Pk*Pm*((m : ℤ) : ℂ) - env "C"*env "b"^2*env "c"^3*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) - 2*env "C"*env "b"^2*env "c"^3*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) - env "C"*env "b"^2*env "c"^3*env "d"*env "f"*Pk*Pm*S - env "C"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*S^2*((k : ℤ) : ℂ) - env "C"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) - env "C"*env "b"^2*env "c"^2*env "d"^2*env "f"*Pk*Pm*S^2) * hP + (env "A"*env "c"^2*env "d"^2*env "f"*Pk*Pm*((m : ℤ) : ℂ) + 2*env "A"*env "c"*env "d"^3*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) + env "A"*env "d"^4*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) + env "C"*env "c"^4*env "f"*Pk*Pm*((m : ℤ) : ℂ) + 2*env "C"*env "c"^3*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) + env "C"*env "c"^2*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ)) * hr1

/-! ## rubi4531r27Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4531r27Nondeg_real : rubi4531r27Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4531r27Nondeg.conditions rubi4531r27Nondeg.body
    rubi4531r27Nondeg.result rubi4531r27Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "A" * env "b") + (((-1) * env "a") * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r27Nondeg])
  have hn0v : (env "A" * env "b") + (-env "a" * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r27Nondeg])
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4531r27Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hc3 := hc (.ne (.app2 .mul (.var "f") (.var "n")) (.int 0)) (by simp [rubi4531r27Nondeg])
  have hn3_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "n" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr1 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (-env "B") * hza + (env "A") * hzb)
  have hdb : env "b" ≠ 0 := by
    intro hzb
    have hza : env "a" = 0 := by
      have h2 : env "a" ^ 2 = 0 := by linear_combination (1) * hr1 - (-env "b") * hzb
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (env "A") * hzb + (-env "B") * hza)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4531r27Nondeg, Defined, eval, Interp.real, hkm, Fn.csc] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4531r27Nondeg, Defined, eval, Interp.real, hkm, hkk, Fn.csc] at h
  have hb2 : k < 0 := by
    have h := hc (.gt (.int 0) (.var "n")) (by simp [rubi4531r27Nondeg])
    have h' : ((k : ℤ) : ℝ) < (0 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkk]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltk : k < 1 → k < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "n" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4531r27Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) ∧
          (k < 0 → (env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹) ≠ 0) := by
    intro w h
    simp [rubi4531r27Nondeg, Defined, eval, Interp.real, hkm, hkk, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4531r27Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, emk1, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4531r27Nondeg, Defined, eval, recEnv, Interp.real, hkm, hkk, ivm1R,
        Fn.csc] at h hn0 hn3_0 hn3_1 hda hdb ⊢
    tauto
  · simp only [rubi4531r27Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m) *
        ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k + 1)) *
        ((((env "a" * env "A") * env "m") + ((((-1) * env "b") * env "B") * env "n")) +
        (((((-1) * env "A") * env "b") * ((env "m" + env "n") + 1)) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, emk1, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4531r27Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4531r27Nondeg.result) =
            fun w => ((((env "A" *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m)) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ^ (k)) *
            ((env "f" * env "n"))⁻¹) + ((-1) * (((env "b" * env "d") * env "n"))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4531r27Nondeg, eval, recEnv, Interp.real, hkm, hkk, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4531r27Nondeg.body =
        (((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m) *
        ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k)) *
        (env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) := by
      simp [rubi4531r27Nondeg, eval, Interp.real, hkm, hkk, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (env "A")).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k) _ (hdzk (k) (by omega))) ((hasDerivAt_const t (env "d")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0)))).mul (hasDerivAt_const t (((env "f" * env "n"))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply]
    have hn3_1c : ((k : ℤ) : ℝ) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd (by norm_num) hn3_1c
      · subst hm0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ k =
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 1 := by
          have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k + 1) =
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 2 := by
          have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k + 2) =
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 3 := by
          have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "d"*Pk*((k : ℤ) : ℝ) - env "A"*env "d"*Pk) * hP + (0) * hr1
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd (by norm_num) hn3_1c
      · have hdmm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
          1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ k =
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 1 := by
          have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k + 1) =
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 2 := by
          have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k + 2) =
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 3 := by
          have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = Pm
        generalize ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "A"*env "a"*env "b"*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) -
            env "A"*env "a"*env "b"*env "d"*env "f"*Pk*Pm*S -
            env "A"*env "b"^2*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℝ) -
            env "A"*env "b"^2*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℝ) -
            env "A"*env "b"^2*env "d"*env "f"*Pk*Pm) * hP +
            (-env "A"*env "d"*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ)) * hr1

/-! ## rubi4531r4Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4531r4Nondeg_real : rubi4531r4Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi4531r4Nondeg.conditions rubi4531r4Nondeg.body
    rubi4531r4Nondeg.result
  intro env hc t hF
  have hn0 : (env "A" * env "b") + (((-1) * env "a") * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r4Nondeg])
  have hn0v : (env "A" * env "b") + (-env "a" * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r4Nondeg])
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4531r4Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hr2 : ((env "a" * env "B") * env "m") + ((env "A" * env "b") * (env "m" + 1)) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "B")) (.var "m")) (.app2 .mul (.app2 .mul (.var "A") (.var "b")) (.app2 .add (.var "m") (.int 1)))) (.int 0)) (by simp [rubi4531r4Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc3 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4531r4Nondeg])
  have hn3_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr1 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (-env "B") * hza + (env "A") * hzb)
  have hdb : env "b" ≠ 0 := by
    intro hzb
    have hza : env "a" = 0 := by
      have h2 : env "a" ^ 2 = 0 := by linear_combination (1) * hr1 - (-env "b") * hzb
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (env "A") * hzb + (-env "B") * hza)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4531r4Nondeg, Defined, eval, Interp.real, hkm, Fn.csc] at h
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4531r4Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4531r4Nondeg, Defined, eval, Interp.real, hkm, Fn.csc] at h ⊢
    tauto
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4531r4Nondeg, Defined, eval, Interp.real, hkm, ivm1R,
        Fn.csc] at h hn0 hn3_0 hn3_1 hda hdb ⊢
    tauto
  · have hfun : (fun w => eval Interp.real (Function.update env "x" w)
        rubi4531r4Nondeg.result) =
            fun w => (((((-1) * env "B") *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m)) *
            ((env "f" * (env "m" + 1)))⁻¹) := by
      funext w
      simp [rubi4531r4Nondeg, eval, Interp.real, hkm, ivm1R, Fn.csc, Real.cot_eq_cos_div_sin,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4531r4Nondeg.body =
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        (env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) := by
      simp [rubi4531r4Nondeg, eval, Interp.real, hkm, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hBm0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((hasDerivAt_const t (((-1) *
        env "B"))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t (((env "f" * (env "m" + 1)))⁻¹))).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply]
    have hr2c : ((env "a" * env "B") * ((m : ℤ) : ℝ)) +
        ((env "A" * env "b") * (((m : ℤ) : ℝ) + 1)) - (0) = 0 :=
        by rw [← (intValue?_eq _ _).1 hkm]; exact hr2
    have hn3_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
          add_zero]
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      refine mul_left_cancel₀ hdb ?_
      linear_combination (env "B"*env "b") * hP + (0) * hr1 + (-S) * hr2c
    · have hdmm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
        1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = Pm
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      refine mul_left_cancel₀ hda ?_
      linear_combination (env "B"*env "a"^2*env "f"*Pm*S +
          env "B"*env "a"*env "b"*env "f"*Pm*((m : ℤ) : ℝ) + env "B"*env "a"*env "b"*env "f"*Pm) *
          hP + (-env "A"*env "f"*Pm*S^2*((m : ℤ) : ℝ) - env "A"*env "f"*Pm*S^2) * hr1 +
          (-env "a"*env "f"*Pm*S - env "b"*env "f"*Pm*S^2) * hr2c

/-! ## rubi4531r6Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4531r6Nondeg_real : rubi4531r6Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4531r6Nondeg.conditions rubi4531r6Nondeg.body
    rubi4531r6Nondeg.result rubi4531r6Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "A" * env "b") + (((-1) * env "a") * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r6Nondeg])
  have hn0v : (env "A" * env "b") + (-env "a" * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r6Nondeg])
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4531r6Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hn2 : ((env "a" * env "B") * env "m") + ((env "A" * env "b") * (env "m" + 1)) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "B")) (.var "m")) (.app2 .mul (.app2 .mul (.var "A") (.var "b")) (.app2 .add (.var "m") (.int 1)))) (.int 0)) (by simp [rubi4531r6Nondeg])
  have hc4 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4531r6Nondeg])
  have hn4_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr1 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (-env "B") * hza + (env "A") * hzb)
  have hdb : env "b" ≠ 0 := by
    intro hzb
    have hza : env "a" = 0 := by
      have h2 : env "a" ^ 2 = 0 := by linear_combination (1) * hr1 - (-env "b") * hzb
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (env "A") * hzb + (-env "B") * hza)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4531r6Nondeg, Defined, eval, Interp.real, hkm, Fn.csc] at h
  have hb3 : -1 < m := by
    have h := hc (.ge (.var "m") (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1))))) (by simp [rubi4531r6Nondeg])
    have h' : (-1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real, ivm1R] at h
      rcases h with h | h <;> linarith
    exact_mod_cast h'
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4531r6Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4531r6Nondeg, Defined, eval, Interp.real, hkm, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4531r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4531r6Nondeg, Defined, eval, recEnv, Interp.real, hkm, ivm1R,
        Fn.csc] at h hn0 hn2 hn4_0 hn4_1 hda hdb ⊢
    tauto
  · simp only [rubi4531r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4531r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4531r6Nondeg.result) =
            fun w => (((((-1) * env "B") *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m)) *
            ((env "f" * (env "m" + 1)))⁻¹) +
            ((((env "a" * env "B") * env "m") + ((env "A" * env "b") * (env "m" + 1))) *
            ((env "b" * (env "m" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4531r6Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4531r6Nondeg.body =
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        (env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) := by
      simp [rubi4531r6Nondeg, eval, Interp.real, hkm, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hBm0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (((-1) *
        env "B"))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t (((env "f" * (env "m" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply]
    have hn2c : ((env "a" * env "B") * ((m : ℤ) : ℝ)) +
        ((env "A" * env "b") * (((m : ℤ) : ℝ) + 1)) ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm]; exact hn2
    have hn4_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn4_1
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
          add_zero]
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "B") * hP + (0) * hr1
    · have hdmm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
        1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = Pm
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "B"*env "a"*env "b"*env "f"*Pm*S +
          env "B"*env "b"^2*env "f"*Pm*((m : ℤ) : ℝ) + env "B"*env "b"^2*env "f"*Pm) * hP +
          (env "B"*env "f"*Pm*S^2*((m : ℤ) : ℝ)) * hr1

end OSR.IntegrationRec296
