import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: explicit terms with powers plus a residual integral

Proofs over ℝ (`csc` has no complex interpretation) of RUBI rules whose result is an explicit term
`K cot (a + b csc)^E` (or a product of `cot`, `csc` and such powers) plus a residual integral. The
derivative of the explicit term is built from the rule expression; the integrand is recovered with
`sin² + cos² = 1` and the stated parameter relations, separately for `m = 0` and `m ≠ 0`
(`linear_combination` coefficients computed by Gröbner reduction). -/

namespace OSR.IntegrationRec285

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

/-! ## rubi533r9Nondeg -/

theorem rubi533r9Nondeg_real : rubi533r9Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi533r9Nondeg.conditions rubi533r9Nondeg.body
    rubi533r9Nondeg.result rubi533r9Nondeg.integrals
  intro env hc t hF
  have hc1 :=
      hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "q") (.int 1))) (.int 0)) (by simp [rubi533r9Nondeg])
  have hn1_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_1 : env "q" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  rcases hkm : intValue? (env "q") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi533r9Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "q" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "q" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "q" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi533r9Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) := by
    intro w h
    simp [rubi533r9Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi533r9Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    have hq : 1 + env "c" ^ 2 * w ^ 2 ≠ 0 := by positivity
    simp [Defined, eval, Interp.real, em1, ivm1R, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi533r9Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R] at h hn1_0 hn1_1 ⊢
    tauto
  · simp only [rubi533r9Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m + 1) *
        ((1 + ((env "c") ^ 2 * (t) ^ 2)))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi533r9Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi533r9Nondeg.result) =
            fun w => ((((env "d" + (env "e" * w))) ^ (m + 1) *
            (env "a" + (env "b" * Real.arctan ((env "c" * w))))) * ((env "e" * (env "q" + 1)))⁻¹) +
            ((((-1) * env "b") * env "c") * ((env "e" * (env "q" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi533r9Nondeg, eval, recEnv, Interp.real, em1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi533r9Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) * (env "a" + (env "b" * Real.arctan ((env "c" * t)))) :=
        by
      simp [rubi533r9Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdz (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))).mul ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_arctan _).comp t ((hasDerivAt_const t (env "c")).mul (hasDerivAt_id' t)))))).mul (hasDerivAt_const t (((env "e" * (env "q" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn1_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hq0 : 1 + env "c" ^ 2 * t ^ 2 ≠ 0 := by positivity
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.arctan (env "c" * t) = Z
      field_simp
      ring
    · have hdm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "d" + (env "e" * t))) ^ m = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 1 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 2 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 3 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "d" + (env "e" * t))) ^ (m - 1) = P
      generalize Real.arctan (env "c" * t) = Z
      field_simp
      ring

/-! ## rubi534r103Nondeg -/

theorem rubi534r103Nondeg_real : rubi534r103Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi534r103Nondeg.conditions rubi534r103Nondeg.body
    rubi534r103Nondeg.result rubi534r103Nondeg.integrals
  intro env hc t hF
  have hc1 :=
      hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "q") (.int 1))) (.int 0)) (by simp [rubi534r103Nondeg])
  have hn1_1 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_2 : env "q" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  rcases hkm : intValue? (env "q") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi534r103Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "q" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "q" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "q" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi534r103Nondeg.body →
      (m < 0 → (env "d" + (env "e" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi534r103Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi534r103Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    have hq : 1 + env "c" ^ 2 * w ^ 2 ≠ 0 := by positivity
    simp [Defined, eval, Interp.real, em1, ivm1R, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi534r103Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R,
        iv2R] at h hn1_1 hn1_2 ⊢
    tauto
  · simp only [rubi534r103Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * (t) ^ 2))) ^ (m + 1) *
        ((1 + ((env "c") ^ 2 * (t) ^ 2)))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi534r103Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi534r103Nondeg.result) =
            fun w => ((((env "d" + (env "e" * (w) ^ 2))) ^ (m + 1) *
            (env "a" + (env "b" * Real.arctan ((env "c" * w))))) *
            (((2 * env "e") * (env "q" + 1)))⁻¹) +
            ((((-1) * env "b") * env "c") * (((2 * env "e") * (env "q" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi534r103Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi534r103Nondeg.body =
        (t * ((env "d" + (env "e" * (t) ^ 2))) ^ (m)) *
        (env "a" + (env "b" * Real.arctan ((env "c" * t)))) := by
      simp [rubi534r103Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdz (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul ((hasDerivAt_id' t).pow 2)))).mul ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_arctan _).comp t ((hasDerivAt_const t (env "c")).mul (hasDerivAt_id' t)))))).mul (hasDerivAt_const t ((((2 * env "e") * (env "q" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      add_sub_cancel_right]
    have hn1_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hq0 : 1 + env "c" ^ 2 * t ^ 2 ≠ 0 := by positivity
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.arctan (env "c" * t) = Z
      field_simp
      ring
    · have hdm : (env "d" + (env "e" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "d" + (env "e" * (t) ^ 2))) ^ m =
          ((env "d" + (env "e" * (t) ^ 2))) ^ (m - 1) * ((env "d" + (env "e" * (t) ^ 2))) ^ 1 := by
        have := zsplit ((env "d" + (env "e" * (t) ^ 2))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "d" + (env "e" * (t) ^ 2))) ^ (m + 1) =
          ((env "d" + (env "e" * (t) ^ 2))) ^ (m - 1) * ((env "d" + (env "e" * (t) ^ 2))) ^ 2 := by
        have := zsplit ((env "d" + (env "e" * (t) ^ 2))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "d" + (env "e" * (t) ^ 2))) ^ (m + 2) =
          ((env "d" + (env "e" * (t) ^ 2))) ^ (m - 1) * ((env "d" + (env "e" * (t) ^ 2))) ^ 3 := by
        have := zsplit ((env "d" + (env "e" * (t) ^ 2))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "d" + (env "e" * (t) ^ 2))) ^ (m - 1) = P
      generalize Real.arctan (env "c" * t) = Z
      field_simp
      ring

end OSR.IntegrationRec285
