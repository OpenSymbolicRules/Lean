import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: explicit terms with powers plus a residual integral

Proofs over ℝ (`csc` has no complex interpretation) of RUBI rules whose result is an explicit term
`K cot (a + b csc)^E` (or a product of `cot`, `csc` and such powers) plus a residual integral. The
derivative of the explicit term is built from the rule expression; the integrand is recovered with
`sin² + cos² = 1` and the stated parameter relations, separately for `m = 0` and `m ≠ 0`
(`linear_combination` coefficients computed by Gröbner reduction). -/

namespace OSR.IntegrationRec283

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

/-! ## rubi416r30Nondeg -/

theorem rubi416r30Nondeg_real : rubi416r30Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi416r30Nondeg.conditions rubi416r30Nondeg.body
    rubi416r30Nondeg.result
  intro env hc t hF
  have hn1 : (env "b") ^ 2 + (env "c") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.int 0)) (by simp [rubi416r30Nondeg])
  have hr2 : (env "b" * env "B") + (env "c" * env "C") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.var "c") (.var "C"))) (.int 0)) (by simp [rubi416r30Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r30Nondeg])
  have hn3_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  have hn3_1 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r30Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi416r30Nondeg.body →
      (m < 0 → ((env "b" * Real.cos ((env "d" + (env "e" * w)))) +
          (env "c" * Real.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r30Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r30Nondeg, Defined, eval, Interp.real, em1, ivm1R, iv2R] at h hn1 hn3_0 hn3_1 ⊢
    tauto
  · have hfun : (fun w => eval Interp.real (Function.update env "x" w)
        rubi416r30Nondeg.result) =
            fun w => ((((env "c" * env "B") + (((-1) * env "b") * env "C")) *
            (((env "b" * Real.cos ((env "d" + (env "e" * w)))) +
            (env "c" * Real.sin ((env "d" + (env "e" * w)))))) ^ (m + 1)) *
            (((env "e" * (env "n" + 1)) * ((env "b") ^ 2 + (env "c") ^ 2)))⁻¹) := by
      funext w
      simp [rubi416r30Nondeg, eval, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi416r30Nondeg.body =
        ((env "B" * Real.cos ((env "d" + (env "e" * t)))) +
        (env "C" * Real.sin ((env "d" + (env "e" * t))))) *
        (((env "b" * Real.cos ((env "d" + (env "e" * t)))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r30Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "b" * Real.cos ((env "d" + (env "e" * t)))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((hasDerivAt_const t (((env "c" * env "B") +
        (((-1) * env "b") * env "C")))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdz (m +
        1) (by omega))) (((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).add ((hasDerivAt_const t (env "c")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "e" * (env "n" + 1)) * ((env "b") ^ 2 + (env "c") ^ 2)))⁻¹))).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn3_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (0) * hP + (-C*env "b" - env "c"*S) * hr2
    · have hdm : ((env "b" * Real.cos ((env "d" + (env "e" * t)))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : (((env "b" * Real.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "b" * Real.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "b" * Real.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "b" * Real.cos ((env "d" + (env "e" * t)))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : (((env "b" * Real.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "b" * Real.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "b" * Real.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "b" * Real.cos ((env "d" + (env "e" * t)))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : (((env "b" * Real.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "b" * Real.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "b" * Real.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "b" * Real.cos ((env "d" + (env "e" * t)))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize (((env "b" * Real.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = P
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "B"*env "b"^3*env "e"*P*((m : ℤ) : ℝ) -
          env "B"*env "b"^3*env "e"*P - env "C"*env "b"^2*env "c"*env "e"*P*((m : ℤ) : ℝ) -
          env "C"*env "b"^2*env "c"*env "e"*P) * hP +
          (-2*C*env "b"*env "c"*env "e"*P*S*((m : ℤ) : ℝ) - 2*C*env "b"*env "c"*env "e"*P*S +
          env "b"^2*env "e"*P*S^2*((m : ℤ) : ℝ) + env "b"^2*env "e"*P*S^2 -
          env "b"^2*env "e"*P*((m : ℤ) : ℝ) - env "b"^2*env "e"*P -
          env "c"^2*env "e"*P*S^2*((m : ℤ) : ℝ) - env "c"^2*env "e"*P*S^2) * hr2

theorem rubi416r30Nondeg_complex : rubi416r30Nondeg.Holds .complex := by
  show AntiderivHoldsUnder Interp.complex "x" rubi416r30Nondeg.conditions rubi416r30Nondeg.body
    rubi416r30Nondeg.result
  intro env hc t hF
  have hn1 : (env "b") ^ 2 + (env "c") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.int 0)) (by simp [rubi416r30Nondeg])
  have hr2 : (env "b" * env "B") + (env "c" * env "C") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.var "c") (.var "C"))) (.int 0)) (by simp [rubi416r30Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r30Nondeg])
  have hn3_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  have hn3_1 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r30Nondeg, Defined, eval, Interp.complex, hkm] at h
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi416r30Nondeg.body →
      (m < 0 → ((env "b" * Complex.cos ((env "d" + (env "e" * w)))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r30Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r30Nondeg, Defined, eval, Interp.complex, em1, ivm1C, iv2C] at h hn1 hn3_0 hn3_1 ⊢
    tauto
  · have hfun : (fun w => eval Interp.complex (Function.update env "x" w)
        rubi416r30Nondeg.result) =
            fun w => ((((env "c" * env "B") + (((-1) * env "b") * env "C")) *
            (((env "b" * Complex.cos ((env "d" + (env "e" * w)))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * w)))))) ^ (m + 1)) *
            (((env "e" * (env "n" + 1)) * ((env "b") ^ 2 + (env "c") ^ 2)))⁻¹) := by
      funext w
      simp [rubi416r30Nondeg, eval, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi416r30Nondeg.body =
        ((env "B" * Complex.cos ((env "d" + (env "e" * t)))) +
        (env "C" * Complex.sin ((env "d" + (env "e" * t))))) *
        (((env "b" * Complex.cos ((env "d" + (env "e" * t)))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r30Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "b" * Complex.cos ((env "d" + (env "e" * t)))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((hasDerivAt_const t (((env "c" * env "B") +
        (((-1) * env "b") * env "C")))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdz (m +
        1) (by omega))) (((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).add ((hasDerivAt_const t (env "c")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "e" * (env "n" + 1)) * ((env "b") ^ 2 + (env "c") ^ 2)))⁻¹))).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn3_1c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (0) * hP + (-C*env "b" - env "c"*S) * hr2
    · have hdm : ((env "b" * Complex.cos ((env "d" + (env "e" * t)))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : (((env "b" * Complex.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "b" * Complex.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "b" * Complex.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "b" * Complex.cos ((env "d" + (env "e" * t)))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : (((env "b" * Complex.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "b" * Complex.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "b" * Complex.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "b" * Complex.cos ((env "d" + (env "e" * t)))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : (((env "b" * Complex.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "b" * Complex.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "b" * Complex.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "b" * Complex.cos ((env "d" + (env "e" * t)))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize (((env "b" * Complex.cos ((env "d" + (env "e" * t)))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = P
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "B"*env "b"^3*env "e"*P*((m : ℤ) : ℂ) -
          env "B"*env "b"^3*env "e"*P - env "C"*env "b"^2*env "c"*env "e"*P*((m : ℤ) : ℂ) -
          env "C"*env "b"^2*env "c"*env "e"*P) * hP +
          (-2*C*env "b"*env "c"*env "e"*P*S*((m : ℤ) : ℂ) - 2*C*env "b"*env "c"*env "e"*P*S +
          env "b"^2*env "e"*P*S^2*((m : ℤ) : ℂ) + env "b"^2*env "e"*P*S^2 -
          env "b"^2*env "e"*P*((m : ℤ) : ℂ) - env "b"^2*env "e"*P -
          env "c"^2*env "e"*P*S^2*((m : ℤ) : ℂ) - env "c"^2*env "e"*P*S^2) * hr2

end OSR.IntegrationRec283
