import OSR.IntegrationNum1

/-! # Strengthened cosecant variants: `K cot y^E` plus a residual integral

Proofs over ℝ (`csc` has no complex interpretation) of RUBI rules whose result is an explicit term
`K cot (a + b csc)^E` (or a product of `cot`, `csc` and such powers) plus a residual integral. The
derivative of the explicit term is built from the rule expression; the integrand is recovered with
`sin² + cos² = 1` and the stated parameter relations, separately for `m = 0` and `m ≠ 0`
(`linear_combination` coefficients computed by Gröbner reduction). -/

namespace OSR.IntegrationRec279

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

/-! ## rubi4531r2Nondeg -/

theorem rubi4531r2Nondeg_real : rubi4531r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4531r2Nondeg.conditions rubi4531r2Nondeg.body
    rubi4531r2Nondeg.result rubi4531r2Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "A" * env "b") + (((-1) * env "a") * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r2Nondeg])
  have hn0v : (env "A" * env "b") + (-env "a" * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r2Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi4531r2Nondeg])
  have hn2_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4531r2Nondeg, Defined, eval, Interp.real, hkm, Fn.csc] at h
  have hb1 : -1 < m := by
    have h := hc (.gt (.var "n") (.int (-1))) (by simp [rubi4531r2Nondeg])
    have h' : (-1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4531r2Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹) ≠ 0) := by
    intro w h
    simp [rubi4531r2Nondeg, Defined, eval, Interp.real, hkm, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4531r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4531r2Nondeg, Defined, eval, recEnv, Interp.real, hkm, ivm1R,
        Fn.csc] at h hn0 hn2_0 hn2_1 ⊢
    tauto
  · simp only [rubi4531r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m) *
        ((((env "A" * env "a") * (env "n" + 1)) + ((env "B" * env "b") * env "n")) +
        ((((env "A" * env "b") + (env "B" * env "a")) * (env "n" + 1)) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4531r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4531r2Nondeg.result) =
            fun w => ((((((-1) * env "b") * env "B") *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ^ (m)) *
            ((env "f" * (env "n" + 1)))⁻¹) + (1 * ((env "n" + 1))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4531r2Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4531r2Nondeg.body =
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) *
        ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m)) *
        (env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) := by
      simp [rubi4531r2Nondeg, eval, Interp.real, hkm, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hB0⟩ := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((((-1) * env "b") *
        env "B"))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdz (m) (by omega))) ((hasDerivAt_const t (env "d")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0)))).mul (hasDerivAt_const t (((env "f" * (env "n" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply]
    have hn2_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_1
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "B"*env "b") * hP
    · have hdm : (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ m =
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) *
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 1 := by
        have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m + 1) =
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) *
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 2 := by
        have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m + 2) =
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) *
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 3 := by
        have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0]
      generalize ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "B"*env "b"*env "d"*env "f"*P*((m : ℤ) : ℝ) +
          env "B"*env "b"*env "d"*env "f"*P) * hP

/-! ## rubi4542r5Nondeg -/

theorem rubi4542r5Nondeg_real : rubi4542r5Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4542r5Nondeg.conditions rubi4542r5Nondeg.body
    rubi4542r5Nondeg.result rubi4542r5Nondeg.integrals
  intro env hc t hF
  have hc1 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "n") (.int 2))) (.int 0)) (by simp [rubi4542r5Nondeg])
  have hn1_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_1 : env "n" + 2 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r5Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  have hb0 : -1 ≤ m := by
    have h := hc (.ge (.var "n") (.int (-1))) (by simp [rubi4542r5Nondeg])
    have h' : (-1 : ℝ) ≤ ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      rcases h with h | h <;> linarith
    exact_mod_cast h'
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4542r5Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹) ≠ 0) := by
    intro w h
    simp [rubi4542r5Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4542r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4542r5Nondeg, Defined, eval, recEnv, Interp.real, hkm, ivm1R,
        Fn.csc] at h hn1_0 hn1_1 ⊢
    tauto
  · simp only [rubi4542r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m) *
        ((((env "A" * env "a") * (env "n" + 2)) +
        ((((env "B" * env "a") * (env "n" + 2)) +
        (env "b" * ((env "C" * (env "n" + 1)) + (env "A" * (env "n" + 2))))) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹)) +
        ((((env "a" * env "C") + (env "B" * env "b")) * (env "n" + 2)) *
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, iv2R, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4542r5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4542r5Nondeg.result) =
            fun w => (((((((-1) * env "b") * env "C") * (Real.sin ((env "e" + (env "f" * w))))⁻¹) *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ^ (m)) *
            ((env "f" * (env "n" + 2)))⁻¹) + (1 * ((env "n" + 2))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4542r5Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4542r5Nondeg.body =
        (((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m) *
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) *
        ((env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) +
        (env "C" * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2)) := by
      simp [rubi4542r5Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hB0⟩ := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t ((((-1) * env "b") *
        env "C"))).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0)).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdz (m) (by omega))) ((hasDerivAt_const t (env "d")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0)))).mul (hasDerivAt_const t (((env "f" * (env "n" + 2)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply]
    have hn1_1c : ((m : ℤ) : ℝ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_1
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (2*env "C"*env "b") * hP
    · have hdm : (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ m =
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) *
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 1 := by
        have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m + 1) =
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) *
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 2 := by
        have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m + 2) =
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) *
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 3 := by
        have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0]
      generalize ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "C"*env "b"*env "d"*env "f"*P*((m : ℤ) : ℝ) +
          2*env "C"*env "b"*env "d"*env "f"*P) * hP

/-! ## rubi4542r6Nondeg -/

theorem rubi4542r6Nondeg_real : rubi4542r6Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4542r6Nondeg.conditions rubi4542r6Nondeg.body
    rubi4542r6Nondeg.result rubi4542r6Nondeg.integrals
  intro env hc t hF
  have hc1 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "n") (.int 2))) (.int 0)) (by simp [rubi4542r6Nondeg])
  have hn1_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_1 : env "n" + 2 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r6Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  have hb0 : -1 ≤ m := by
    have h := hc (.ge (.var "n") (.int (-1))) (by simp [rubi4542r6Nondeg])
    have h' : (-1 : ℝ) ≤ ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      rcases h with h | h <;> linarith
    exact_mod_cast h'
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4542r6Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹) ≠ 0) := by
    intro w h
    simp [rubi4542r6Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4542r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4542r6Nondeg, Defined, eval, recEnv, Interp.real, hkm, ivm1R,
        Fn.csc] at h hn1_0 hn1_1 ⊢
    tauto
  · simp only [rubi4542r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m) *
        ((((env "A" * env "a") * (env "n" + 2)) +
        ((env "b" * ((env "C" * (env "n" + 1)) + (env "A" * (env "n" + 2)))) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹)) +
        (((env "a" * env "C") * (env "n" + 2)) *
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, iv2R, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4542r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4542r6Nondeg.result) =
            fun w => (((((((-1) * env "b") * env "C") * (Real.sin ((env "e" + (env "f" * w))))⁻¹) *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ^ (m)) *
            ((env "f" * (env "n" + 2)))⁻¹) + (1 * ((env "n" + 2))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4542r6Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4542r6Nondeg.body =
        (((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m) *
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) *
        (env "A" + (env "C" * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2)) := by
      simp [rubi4542r6Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hB0⟩ := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t ((((-1) * env "b") *
        env "C"))).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0)).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdz (m) (by omega))) ((hasDerivAt_const t (env "d")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0)))).mul (hasDerivAt_const t (((env "f" * (env "n" + 2)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply]
    have hn1_1c : ((m : ℤ) : ℝ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_1
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (2*env "C"*env "b") * hP
    · have hdm : (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ m =
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) *
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 1 := by
        have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m + 1) =
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) *
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 2 := by
        have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m + 2) =
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) *
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 3 := by
        have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0]
      generalize ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "C"*env "b"*env "d"*env "f"*P*((m : ℤ) : ℝ) +
          2*env "C"*env "b"*env "d"*env "f"*P) * hP

end OSR.IntegrationRec279
