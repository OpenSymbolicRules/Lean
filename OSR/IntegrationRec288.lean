import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: explicit terms with powers plus a residual integral

Proofs over ℝ (`csc` has no complex interpretation) of RUBI rules whose result is an explicit term
`K cot (a + b csc)^E` (or a product of `cot`, `csc` and such powers) plus a residual integral. The
derivative of the explicit term is built from the rule expression; the integrand is recovered with
`sin² + cos² = 1` and the stated parameter relations, separately for `m = 0` and `m ≠ 0`
(`linear_combination` coefficients computed by Gröbner reduction). -/

namespace OSR.IntegrationRec288

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

/-! ## rubi1213r34Nondeg -/

theorem rubi1213r34Nondeg_real : rubi1213r34Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1213r34Nondeg.conditions rubi1213r34Nondeg.body
    rubi1213r34Nondeg.result rubi1213r34Nondeg.integrals
  intro env hc t hF
  have hr0 : (env "a" * (env "g") ^ 2) + ((env "f") ^ 2 * env "c") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a") (.pow (.var "g") (.int 2))) (.app2 .mul (.pow (.var "f") (.int 2)) (.var "c"))) (.int 0)) (by simp [rubi1213r34Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1213r34Nondeg])
  have hn2_1 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_3 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r34Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have hb1 : m < -2 := by
    have h := hc (.gt (.int (-2)) (.var "p")) (by simp [rubi1213r34Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-2 : ℝ) := by
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1213r34Nondeg.body →
      (m < 0 → (env "a" + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1213r34Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r34Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1213r34Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R,
        iv2R] at h hn2_1 hn2_2 hn2_3 ⊢
    tauto
  · simp only [rubi1213r34Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((t *
        (((2 * env "a") * env "g") + (((((-1) * env "c") * env "f") * ((2 * env "p") + 5)) * t))) *
        ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1213r34Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1213r34Nondeg.result) =
            fun w => ((((w) ^ 2 * ((env "a" * env "g") + ((((-1) * env "c") * env "f") * w))) *
            ((env "a" + (env "c" * (w) ^ 2))) ^ (m + 1)) *
            ((((2 * env "a") * env "c") * (env "p" + 1)))⁻¹) +
            ((-1) * ((((2 * env "a") * env "c") * (env "p" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1213r34Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1213r34Nondeg.body =
        ((t) ^ 2 * (env "f" + (env "g" * t))) * ((env "a" + (env "c" * (t) ^ 2))) ^ (m) := by
      simp [rubi1213r34Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) → (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_id' t).pow 2).mul ((hasDerivAt_const t ((env "a" *
        env "g"))).add ((hasDerivAt_const t ((((-1) * env "c") *
        env "f"))).mul (hasDerivAt_id' t)))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdz (m +
        1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((((2 * env "a") * env "c") * (env "p" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      add_sub_cancel_right]
    have hn2_3c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_3
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      field_simp
      ring
    · have hdm : (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "c" * (t) ^ 2))) ^ m =
          ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 1 := by
        have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 1) =
          ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 2 := by
        have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 2) =
          ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 3 := by
        have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) = P
      field_simp
      ring

theorem rubi1213r34Nondeg_complex : rubi1213r34Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1213r34Nondeg.conditions rubi1213r34Nondeg.body
    rubi1213r34Nondeg.result rubi1213r34Nondeg.integrals
  intro env hc t hF
  have hr0 : (env "a" * (env "g") ^ 2) + ((env "f") ^ 2 * env "c") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a") (.pow (.var "g") (.int 2))) (.app2 .mul (.pow (.var "f") (.int 2)) (.var "c"))) (.int 0)) (by simp [rubi1213r34Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1213r34Nondeg])
  have hn2_1 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_3 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r34Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have hb1 : m < -2 := by
    have h := hc (.gt (.int (-2)) (.var "p")) (by simp [rubi1213r34Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (-2 : ℝ) := by
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
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1213r34Nondeg.body →
      (m < 0 → (env "a" + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1213r34Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r34Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1213r34Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C,
        iv2C] at h hn2_1 hn2_2 hn2_3 ⊢
    tauto
  · simp only [rubi1213r34Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((t *
        (((2 * env "a") * env "g") + (((((-1) * env "c") * env "f") * ((2 * env "p") + 5)) * t))) *
        ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1213r34Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1213r34Nondeg.result) =
            fun w => ((((w) ^ 2 * ((env "a" * env "g") + ((((-1) * env "c") * env "f") * w))) *
            ((env "a" + (env "c" * (w) ^ 2))) ^ (m + 1)) *
            ((((2 * env "a") * env "c") * (env "p" + 1)))⁻¹) +
            ((-1) * ((((2 * env "a") * env "c") * (env "p" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1213r34Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1213r34Nondeg.body =
        ((t) ^ 2 * (env "f" + (env "g" * t))) * ((env "a" + (env "c" * (t) ^ 2))) ^ (m) := by
      simp [rubi1213r34Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) → (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_id' t).pow 2).mul ((hasDerivAt_const t ((env "a" *
        env "g"))).add ((hasDerivAt_const t ((((-1) * env "c") *
        env "f"))).mul (hasDerivAt_id' t)))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdz (m +
        1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((((2 * env "a") * env "c") * (env "p" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      add_sub_cancel_right]
    have hn2_3c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_3
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      field_simp
      ring
    · have hdm : (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "c" * (t) ^ 2))) ^ m =
          ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 1 := by
        have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 1) =
          ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 2 := by
        have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 2) =
          ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 3 := by
        have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) = P
      field_simp
      ring

end OSR.IntegrationRec288
