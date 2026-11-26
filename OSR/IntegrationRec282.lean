import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: explicit terms with powers plus a residual integral

Proofs over ℝ (`csc` has no complex interpretation) of RUBI rules whose result is an explicit term
`K cot (a + b csc)^E` (or a product of `cot`, `csc` and such powers) plus a residual integral. The
derivative of the explicit term is built from the rule expression; the integrand is recovered with
`sin² + cos² = 1` and the stated parameter relations, separately for `m = 0` and `m ≠ 0`
(`linear_combination` coefficients computed by Gröbner reduction). -/

namespace OSR.IntegrationRec282

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

/-! ## rubi4112r3xNondeg -/

theorem rubi4112r3xNondeg_real : rubi4112r3xNondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4112r3xNondeg.conditions rubi4112r3xNondeg.body
    rubi4112r3xNondeg.result rubi4112r3xNondeg.integrals
  intro env hc t hF
  have hc1 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "f") (.var "g")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi4112r3xNondeg])
  have hn1_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_1 : env "g" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_2 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r3xNondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "p" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "p" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "p" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4112r3xNondeg.body →
      (m < 0 → (env "g" * Real.cos ((env "e" + (env "f" * w)))) ≠ 0) := by
    intro w h
    simp [rubi4112r3xNondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r3xNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4112r3xNondeg, Defined, eval, recEnv, Interp.real, em1,
        ivm1R] at h hn1_0 hn1_1 hn1_2 ⊢
    tauto
  · simp only [rubi4112r3xNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (m)) t :=
        by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4112r3xNondeg.integrals.map (·.1)) Φ
        "x" w) rubi4112r3xNondeg.result) =
            fun w => ((((-1) * env "b") *
            ((env "g" * Real.cos ((env "e" + (env "f" * w))))) ^ (m + 1)) *
            (((env "f" * env "g") * (env "p" + 1)))⁻¹) + env "a" * Φ "I1" w := by
      funext w
      simp [rubi4112r3xNondeg, eval, recEnv, Interp.real, em1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4112r3xNondeg.body =
        ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (m) *
        (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) := by
      simp [rubi4112r3xNondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "g" * Real.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((hasDerivAt_const t (((-1) * env "b"))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdz (m +
        1) (by omega))) ((hasDerivAt_const t (env "g")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))))).mul (hasDerivAt_const t ((((env "f" * env "g") * (env "p" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn1_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_2
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
    · have hdm : (env "g" * Real.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ m =
          ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (m - 1) *
          ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ 1 := by
        have := zsplit ((env "g" * Real.cos ((env "e" + (env "f" * t))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (m + 1) =
          ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (m - 1) *
          ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ 2 := by
        have := zsplit ((env "g" * Real.cos ((env "e" + (env "f" * t))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (m + 2) =
          ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (m - 1) *
          ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ 3 := by
        have := zsplit ((env "g" * Real.cos ((env "e" + (env "f" * t))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination

theorem rubi4112r3xNondeg_complex : rubi4112r3xNondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4112r3xNondeg.conditions rubi4112r3xNondeg.body
    rubi4112r3xNondeg.result rubi4112r3xNondeg.integrals
  intro env hc t hF
  have hc1 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "f") (.var "g")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi4112r3xNondeg])
  have hn1_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_1 : env "g" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_2 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r3xNondeg, Defined, eval, Interp.complex, hkm] at h
  have em1 : intValue? (env "p" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "p" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "p" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4112r3xNondeg.body →
      (m < 0 → (env "g" * Complex.cos ((env "e" + (env "f" * w)))) ≠ 0) := by
    intro w h
    simp [rubi4112r3xNondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r3xNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4112r3xNondeg, Defined, eval, recEnv, Interp.complex, em1,
        ivm1C] at h hn1_0 hn1_1 hn1_2 ⊢
    tauto
  · simp only [rubi4112r3xNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "g" *
        Complex.cos ((env "e" + (env "f" * t))))) ^ (m)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4112r3xNondeg.integrals.map (·.1)) Φ
        "x" w) rubi4112r3xNondeg.result) =
            fun w => ((((-1) * env "b") *
            ((env "g" * Complex.cos ((env "e" + (env "f" * w))))) ^ (m + 1)) *
            (((env "f" * env "g") * (env "p" + 1)))⁻¹) + env "a" * Φ "I1" w := by
      funext w
      simp [rubi4112r3xNondeg, eval, recEnv, Interp.complex, em1, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4112r3xNondeg.body =
        ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (m) *
        (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) := by
      simp [rubi4112r3xNondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "g" * Complex.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((hasDerivAt_const t (((-1) * env "b"))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdz (m +
        1) (by omega))) ((hasDerivAt_const t (env "g")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))))).mul (hasDerivAt_const t ((((env "f" * env "g") * (env "p" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn1_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_2
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
    · have hdm : (env "g" * Complex.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ m =
          ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (m - 1) *
          ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ 1 := by
        have := zsplit ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (m + 1) =
          ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (m - 1) *
          ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ 2 := by
        have := zsplit ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (m + 2) =
          ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (m - 1) *
          ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ 3 := by
        have := zsplit ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (m - 1) = P
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination

/-! ## rubi417r14Nondeg -/

theorem rubi417r14Nondeg_real : rubi417r14Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi417r14Nondeg.conditions rubi417r14Nondeg.body
    rubi417r14Nondeg.result rubi417r14Nondeg.integrals
  intro env hc t hF
  have hn0 : env "a" + env "b" ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.var "a") (.var "b")) (.int 0)) (by simp [rubi417r14Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "f")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "a") (.var "b"))) (.int 0)) (by simp [rubi417r14Nondeg])
  have hn2_1 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_3 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi417r14Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have hb1 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi417r14Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have em1 : intValue? (env "p" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "p" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "p" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi417r14Nondeg.body →
      (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w)))) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi417r14Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi417r14Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi417r14Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R,
        iv2R] at h hn0 hn2_1 hn2_2 hn2_3 ⊢
    tauto
  · simp only [rubi417r14Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m + 1) *
        ((((2 * env "a") * (env "p" + 1)) + (env "b" * ((2 * env "p") + 3))) +
        ((((-2) * env "b") * (env "p" + 2)) * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi417r14Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi417r14Nondeg.result) =
            fun w => ((((((-1) * env "b") * Real.cos ((env "e" + (env "f" * w)))) *
            Real.sin ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w)))) ^ 2))) ^ (m + 1)) *
            (((((2 * env "a") * env "f") * (env "p" + 1)) * (env "a" + env "b")))⁻¹) +
            (1 * ((((2 * env "a") * (env "p" + 1)) * (env "a" + env "b")))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi417r14Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi417r14Nondeg.body =
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m) := by
      simp [rubi417r14Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        env "b"))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).pow 2))))).mul (hasDerivAt_const t ((((((2 * env "a") * env "f") * (env "p" + 1)) * (env "a" + env "b")))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      add_sub_cancel_right]
    have hn2_3c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_3
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
      linear_combination (-env "a"*env "b" - 3*env "b"^2*S^2) * hP
    · have hdm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2)) ≠ 0 ∨ 0 ≤ m -
        1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ m =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m + 1) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m + 2) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "a"^2*env "b"*env "f"*P -
          2*env "a"*env "b"^2*env "f"*P*S^2*((m : ℤ) : ℝ) - 4*env "a"*env "b"^2*env "f"*P*S^2 -
          2*env "b"^3*env "f"*P*S^4*((m : ℤ) : ℝ) - 3*env "b"^3*env "f"*P*S^4) * hP

theorem rubi417r14Nondeg_complex : rubi417r14Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi417r14Nondeg.conditions rubi417r14Nondeg.body
    rubi417r14Nondeg.result rubi417r14Nondeg.integrals
  intro env hc t hF
  have hn0 : env "a" + env "b" ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.var "a") (.var "b")) (.int 0)) (by simp [rubi417r14Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "f")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "a") (.var "b"))) (.int 0)) (by simp [rubi417r14Nondeg])
  have hn2_1 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_3 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi417r14Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have hb1 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi417r14Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have em1 : intValue? (env "p" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "p" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "p" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi417r14Nondeg.body →
      (m < 0 → (env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * w)))) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi417r14Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi417r14Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi417r14Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C,
        iv2C] at h hn0 hn2_1 hn2_2 hn2_3 ⊢
    tauto
  · simp only [rubi417r14Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m + 1) *
        ((((2 * env "a") * (env "p" + 1)) + (env "b" * ((2 * env "p") + 3))) +
        ((((-2) * env "b") * (env "p" + 2)) * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) t :=
        by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi417r14Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi417r14Nondeg.result) =
            fun w => ((((((-1) * env "b") * Complex.cos ((env "e" + (env "f" * w)))) *
            Complex.sin ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * w)))) ^ 2))) ^ (m + 1)) *
            (((((2 * env "a") * env "f") * (env "p" + 1)) * (env "a" + env "b")))⁻¹) +
            (1 * ((((2 * env "a") * (env "p" + 1)) * (env "a" + env "b")))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi417r14Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi417r14Nondeg.body =
        ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m) := by
      simp [rubi417r14Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        env "b"))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).pow 2))))).mul (hasDerivAt_const t ((((((2 * env "a") * env "f") * (env "p" + 1)) * (env "a" + env "b")))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      add_sub_cancel_right]
    have hn2_3c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_3
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
      linear_combination (-env "a"*env "b" - 3*env "b"^2*S^2) * hP
    · have hdm : (env "a" +
        (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ m =
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m + 1) =
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m + 2) =
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m -
          1) = P
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "a"^2*env "b"*env "f"*P -
          2*env "a"*env "b"^2*env "f"*P*S^2*((m : ℤ) : ℂ) - 4*env "a"*env "b"^2*env "f"*P*S^2 -
          2*env "b"^3*env "f"*P*S^4*((m : ℤ) : ℂ) - 3*env "b"^3*env "f"*P*S^4) * hP

/-! ## rubi417r5Nondeg -/

theorem rubi417r5Nondeg_real : rubi417r5Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi417r5Nondeg.conditions rubi417r5Nondeg.body
    rubi417r5Nondeg.result rubi417r5Nondeg.integrals
  intro env hc t hF
  have hn1 : env "a" + env "b" ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.var "a") (.var "b")) (.int 0)) (by simp [rubi417r5Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "f")) (.app2 .add (.var "a") (.var "b"))) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi417r5Nondeg])
  have hn2_1 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_4 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi417r5Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi417r5Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have em1 : intValue? (env "p" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "p" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "p" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi417r5Nondeg.body →
      (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w)))) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi417r5Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi417r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi417r5Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R,
        iv2R] at h hn1 hn2_1 hn2_2 hn2_4 ⊢
    tauto
  · simp only [rubi417r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m + 1) *
        (((env "a" * env "B") +
        (((-1) * env "A") * (((2 * env "a") * (env "p" + 1)) + (env "b" * ((2 * env "p") + 3))))) +
        (((2 * ((env "A" * env "b") + (((-1) * env "a") * env "B"))) * (env "p" + 2)) *
        (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi417r5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi417r5Nondeg.result) =
            fun w => ((((((-1) * ((env "A" * env "b") + (((-1) * env "a") * env "B"))) *
            Real.cos ((env "e" + (env "f" * w)))) * Real.sin ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w)))) ^ 2))) ^ (m + 1)) *
            (((((2 * env "a") * env "f") * (env "a" + env "b")) * (env "p" + 1)))⁻¹) +
            ((-1) * ((((2 * env "a") * (env "a" + env "b")) * (env "p" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi417r5Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi417r5Nondeg.body =
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m) *
        (env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi417r5Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        ((env "A" * env "b") +
        (((-1) * env "a") *
        env "B"))))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).pow 2))))).mul (hasDerivAt_const t ((((((2 * env "a") * env "f") * (env "a" + env "b")) * (env "p" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      add_sub_cancel_right]
    have hn2_4c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_4
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
      linear_combination (-env "A"*env "a"*env "b" - 3*env "A"*env "b"^2*S^2 + env "B"*env "a"^2 +
          3*env "B"*env "a"*env "b"*S^2) * hP
    · have hdm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2)) ≠ 0 ∨ 0 ≤ m -
        1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ m =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m + 1) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m + 2) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "a"^2*env "b"*env "f"*P -
          2*env "A"*env "a"*env "b"^2*env "f"*P*S^2*((m : ℤ) : ℝ) -
          4*env "A"*env "a"*env "b"^2*env "f"*P*S^2 -
          2*env "A"*env "b"^3*env "f"*P*S^4*((m : ℤ) : ℝ) - 3*env "A"*env "b"^3*env "f"*P*S^4 +
          env "B"*env "a"^3*env "f"*P + 2*env "B"*env "a"^2*env "b"*env "f"*P*S^2*((m : ℤ) : ℝ) +
          4*env "B"*env "a"^2*env "b"*env "f"*P*S^2 +
          2*env "B"*env "a"*env "b"^2*env "f"*P*S^4*((m : ℤ) : ℝ) +
          3*env "B"*env "a"*env "b"^2*env "f"*P*S^4) * hP

theorem rubi417r5Nondeg_complex : rubi417r5Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi417r5Nondeg.conditions rubi417r5Nondeg.body
    rubi417r5Nondeg.result rubi417r5Nondeg.integrals
  intro env hc t hF
  have hn1 : env "a" + env "b" ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.var "a") (.var "b")) (.int 0)) (by simp [rubi417r5Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "f")) (.app2 .add (.var "a") (.var "b"))) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi417r5Nondeg])
  have hn2_1 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_4 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi417r5Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi417r5Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have em1 : intValue? (env "p" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "p" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "p" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi417r5Nondeg.body →
      (m < 0 → (env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * w)))) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi417r5Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi417r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi417r5Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C,
        iv2C] at h hn1 hn2_1 hn2_2 hn2_4 ⊢
    tauto
  · simp only [rubi417r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m + 1) *
        (((env "a" * env "B") +
        (((-1) * env "A") * (((2 * env "a") * (env "p" + 1)) + (env "b" * ((2 * env "p") + 3))))) +
        (((2 * ((env "A" * env "b") + (((-1) * env "a") * env "B"))) * (env "p" + 2)) *
        (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi417r5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi417r5Nondeg.result) =
            fun w => ((((((-1) * ((env "A" * env "b") + (((-1) * env "a") * env "B"))) *
            Complex.cos ((env "e" + (env "f" * w)))) * Complex.sin ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * w)))) ^ 2))) ^ (m + 1)) *
            (((((2 * env "a") * env "f") * (env "a" + env "b")) * (env "p" + 1)))⁻¹) +
            ((-1) * ((((2 * env "a") * (env "a" + env "b")) * (env "p" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi417r5Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi417r5Nondeg.body =
        ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m) *
        (env "A" + (env "B" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi417r5Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        ((env "A" * env "b") +
        (((-1) * env "a") *
        env "B"))))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).pow 2))))).mul (hasDerivAt_const t ((((((2 * env "a") * env "f") * (env "a" + env "b")) * (env "p" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      add_sub_cancel_right]
    have hn2_4c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_4
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
      linear_combination (-env "A"*env "a"*env "b" - 3*env "A"*env "b"^2*S^2 + env "B"*env "a"^2 +
          3*env "B"*env "a"*env "b"*S^2) * hP
    · have hdm : (env "a" +
        (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ m =
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m + 1) =
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m + 2) =
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m -
          1) = P
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "a"^2*env "b"*env "f"*P -
          2*env "A"*env "a"*env "b"^2*env "f"*P*S^2*((m : ℤ) : ℂ) -
          4*env "A"*env "a"*env "b"^2*env "f"*P*S^2 -
          2*env "A"*env "b"^3*env "f"*P*S^4*((m : ℤ) : ℂ) - 3*env "A"*env "b"^3*env "f"*P*S^4 +
          env "B"*env "a"^3*env "f"*P + 2*env "B"*env "a"^2*env "b"*env "f"*P*S^2*((m : ℤ) : ℂ) +
          4*env "B"*env "a"^2*env "b"*env "f"*P*S^2 +
          2*env "B"*env "a"*env "b"^2*env "f"*P*S^4*((m : ℤ) : ℂ) +
          3*env "B"*env "a"*env "b"^2*env "f"*P*S^4) * hP

end OSR.IntegrationRec282
