import OSR.IntegrationNum1

/-! # Strengthened variants with two integer exponents: explicit terms plus a residual integral

Proofs of RUBI rules whose result is an explicit term with powers `y^m z^n` plus at most one residual
integral. The derivative of the explicit term is built from the rule expression; the integrand is
recovered with `sin² + cos² = 1` (when trigonometric) and the stated parameter relations, separately
for each exponent equal to `0` or not (`linear_combination` coefficients computed by Gröbner
reduction). Rules with `csc`, `cot` or `arctan` are proved over ℝ only. -/

namespace OSR.IntegrationRec299

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

/-! ## rubi6113r13Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi6113r13Nondeg_real : rubi6113r13Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6113r13Nondeg.conditions rubi6113r13Nondeg.body
    rubi6113r13Nondeg.result rubi6113r13Nondeg.integrals
  intro env hc t hF
  have hn1 : (env "b" * env "e") + (((-2) * env "c") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r13Nondeg])
  have hc2 := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi6113r13Nondeg])
  have hn2_1 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi6113r13Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have hb0 : 1 < m := by
    have h := hc (.gt (.var "m") (.int 1)) (by simp [rubi6113r13Nondeg])
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi6113r13Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) := by
    intro w h
    simp [rubi6113r13Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, emmm1, emmm2, iv2R] at h ⊢
      try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r13Nondeg, Defined, eval, recEnv, Interp.real, emmm1, ivm1R,
        iv2R] at h hn1 hn2_1 ⊢
    try tauto
  · simp only [rubi6113r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    have hΦ'1 : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m - 1) *
        Real.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ.1 using 1
      simp [eval, Interp.real, emmm1, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hΦ'2 : HasDerivAt (Φ "I2") (((env "d" + (env "e" * t))) ^ (m - 2) *
        Real.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ.2 using 1
      simp [eval, Interp.real, emmm2, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi6113r13Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r13Nondeg.result) =
            fun w => (((env "e" * ((env "d" + (env "e" * w))) ^ (m - 1)) *
            Real.cosh (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)))) * ((2 * env "c"))⁻¹) +
            (((-1) * ((env "b" * env "e") + (((-2) * env "c") * env "d"))) * ((2 * env "c"))⁻¹) *
            Φ "I1" w + ((((-1) * (env "e") ^ 2) * (env "m" + (-1))) * ((2 * env "c"))⁻¹) *
            Φ "I2" w := by
      funext w
      simp [rubi6113r13Nondeg, eval, recEnv, Interp.real, emmm1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi6113r13Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) *
        Real.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) := by
      simp [rubi6113r13Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (env "e")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m -
        1) _ (hdzm (m -
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).mul ((Real.hasDerivAt_cosh _).comp t (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((2 * env "c"))⁻¹))).add (hΦ'1.const_mul _)).add (hΦ'2.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      show m - 1 - 1 = m -
          2 by ring]
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.cosh_sq_sub_sinh_sq ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 2 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have el1m : ((env "d" + (env "e" * t))) ^ (m - 1) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 1 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 1 hdmm
        rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
      have el2m : ((env "d" + (env "e" * t))) ^ (m) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 2 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 2 hdmm
        rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
      have el3m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 3 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 3 hdmm
        rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have el4m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 4 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 4 hdmm
        rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [el1m, el2m]
      generalize ((env "d" + (env "e" * t))) ^ (m - 2) = Pm
      generalize Real.sinh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = S at hP ⊢
      generalize Real.cosh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = C at hP ⊢
      have hqm1a : (1 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
      have hqm1b : (((m : ℤ) : ℝ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
      have hqm2a : (2 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
      have hqm2b : (((m : ℤ) : ℝ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
      have hqm3a : (3 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
      have hqm3b : (((m : ℤ) : ℝ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
      field_simp
      ring

set_option maxHeartbeats 1000000 in
theorem rubi6113r13Nondeg_complex : rubi6113r13Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6113r13Nondeg.conditions rubi6113r13Nondeg.body
    rubi6113r13Nondeg.result rubi6113r13Nondeg.integrals
  intro env hc t hF
  have hn1 : (env "b" * env "e") + (((-2) * env "c") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r13Nondeg])
  have hc2 := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi6113r13Nondeg])
  have hn2_1 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi6113r13Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have hb0 : 1 < m := by
    have h := hc (.gt (.var "m") (.int 1)) (by simp [rubi6113r13Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi6113r13Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) := by
    intro w h
    simp [rubi6113r13Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, emmm1, emmm2, iv2C] at h ⊢
      try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r13Nondeg, Defined, eval, recEnv, Interp.complex, emmm1, ivm1C,
        iv2C] at h hn1 hn2_1 ⊢
    try tauto
  · simp only [rubi6113r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    have hΦ'1 : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m - 1) *
        Complex.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ.1 using 1
      simp [eval, Interp.complex, emmm1, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hΦ'2 : HasDerivAt (Φ "I2") (((env "d" + (env "e" * t))) ^ (m - 2) *
        Complex.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ.2 using 1
      simp [eval, Interp.complex, emmm2, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi6113r13Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r13Nondeg.result) =
            fun w => (((env "e" * ((env "d" + (env "e" * w))) ^ (m - 1)) *
            Complex.cosh (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)))) *
            ((2 * env "c"))⁻¹) +
            (((-1) * ((env "b" * env "e") + (((-2) * env "c") * env "d"))) * ((2 * env "c"))⁻¹) *
            Φ "I1" w + ((((-1) * (env "e") ^ 2) * (env "m" + (-1))) * ((2 * env "c"))⁻¹) *
            Φ "I2" w := by
      funext w
      simp [rubi6113r13Nondeg, eval, recEnv, Interp.complex, emmm1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi6113r13Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) *
        Complex.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) := by
      simp [rubi6113r13Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (env "e")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m -
        1) _ (hdzm (m -
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).mul ((Complex.hasDerivAt_cosh _).comp t (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((2 * env "c"))⁻¹))).add (hΦ'1.const_mul _)).add (hΦ'2.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      show m - 1 - 1 = m -
          2 by ring]
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.cosh_sq_sub_sinh_sq ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 2 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have el1m : ((env "d" + (env "e" * t))) ^ (m - 1) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 1 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 1 hdmm
        rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
      have el2m : ((env "d" + (env "e" * t))) ^ (m) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 2 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 2 hdmm
        rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
      have el3m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 3 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 3 hdmm
        rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have el4m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 4 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 4 hdmm
        rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [el1m, el2m]
      generalize ((env "d" + (env "e" * t))) ^ (m - 2) = Pm
      generalize Complex.sinh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = S at hP ⊢
      generalize Complex.cosh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = C at hP ⊢
      have hqm1a : (1 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
      have hqm1b : (((m : ℤ) : ℂ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
      have hqm2a : (2 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
      have hqm2b : (((m : ℤ) : ℂ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
      have hqm3a : (3 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
      have hqm3b : (((m : ℤ) : ℂ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
      field_simp
      ring

/-! ## rubi6113r14Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi6113r14Nondeg_real : rubi6113r14Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6113r14Nondeg.conditions rubi6113r14Nondeg.body
    rubi6113r14Nondeg.result rubi6113r14Nondeg.integrals
  intro env hc t hF
  have hn1 : (env "b" * env "e") + (((-2) * env "c") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r14Nondeg])
  have hc2 := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi6113r14Nondeg])
  have hn2_1 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi6113r14Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have hb0 : 1 < m := by
    have h := hc (.gt (.var "m") (.int 1)) (by simp [rubi6113r14Nondeg])
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi6113r14Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) := by
    intro w h
    simp [rubi6113r14Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r14Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, emmm1, emmm2, iv2R] at h ⊢
      try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r14Nondeg, Defined, eval, recEnv, Interp.real, emmm1, ivm1R,
        iv2R] at h hn1 hn2_1 ⊢
    try tauto
  · simp only [rubi6113r14Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    have hΦ'1 : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m - 1) *
        Real.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ.1 using 1
      simp [eval, Interp.real, emmm1, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hΦ'2 : HasDerivAt (Φ "I2") (((env "d" + (env "e" * t))) ^ (m - 2) *
        Real.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ.2 using 1
      simp [eval, Interp.real, emmm2, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi6113r14Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r14Nondeg.result) =
            fun w => (((env "e" * ((env "d" + (env "e" * w))) ^ (m - 1)) *
            Real.sinh (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)))) * ((2 * env "c"))⁻¹) +
            (((-1) * ((env "b" * env "e") + (((-2) * env "c") * env "d"))) * ((2 * env "c"))⁻¹) *
            Φ "I1" w + ((((-1) * (env "e") ^ 2) * (env "m" + (-1))) * ((2 * env "c"))⁻¹) *
            Φ "I2" w := by
      funext w
      simp [rubi6113r14Nondeg, eval, recEnv, Interp.real, emmm1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi6113r14Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) *
        Real.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) := by
      simp [rubi6113r14Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (env "e")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m -
        1) _ (hdzm (m -
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).mul ((Real.hasDerivAt_sinh _).comp t (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((2 * env "c"))⁻¹))).add (hΦ'1.const_mul _)).add (hΦ'2.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      show m - 1 - 1 = m -
          2 by ring]
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.cosh_sq_sub_sinh_sq ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 2 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have el1m : ((env "d" + (env "e" * t))) ^ (m - 1) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 1 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 1 hdmm
        rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
      have el2m : ((env "d" + (env "e" * t))) ^ (m) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 2 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 2 hdmm
        rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
      have el3m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 3 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 3 hdmm
        rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have el4m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 4 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 4 hdmm
        rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [el1m, el2m]
      generalize ((env "d" + (env "e" * t))) ^ (m - 2) = Pm
      generalize Real.sinh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = S at hP ⊢
      generalize Real.cosh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = C at hP ⊢
      have hqm1a : (1 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
      have hqm1b : (((m : ℤ) : ℝ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
      have hqm2a : (2 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
      have hqm2b : (((m : ℤ) : ℝ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
      have hqm3a : (3 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
      have hqm3b : (((m : ℤ) : ℝ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
      field_simp
      ring

set_option maxHeartbeats 1000000 in
theorem rubi6113r14Nondeg_complex : rubi6113r14Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6113r14Nondeg.conditions rubi6113r14Nondeg.body
    rubi6113r14Nondeg.result rubi6113r14Nondeg.integrals
  intro env hc t hF
  have hn1 : (env "b" * env "e") + (((-2) * env "c") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r14Nondeg])
  have hc2 := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi6113r14Nondeg])
  have hn2_1 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi6113r14Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have hb0 : 1 < m := by
    have h := hc (.gt (.var "m") (.int 1)) (by simp [rubi6113r14Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi6113r14Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) := by
    intro w h
    simp [rubi6113r14Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r14Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, emmm1, emmm2, iv2C] at h ⊢
      try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r14Nondeg, Defined, eval, recEnv, Interp.complex, emmm1, ivm1C,
        iv2C] at h hn1 hn2_1 ⊢
    try tauto
  · simp only [rubi6113r14Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    have hΦ'1 : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m - 1) *
        Complex.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ.1 using 1
      simp [eval, Interp.complex, emmm1, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hΦ'2 : HasDerivAt (Φ "I2") (((env "d" + (env "e" * t))) ^ (m - 2) *
        Complex.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ.2 using 1
      simp [eval, Interp.complex, emmm2, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi6113r14Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r14Nondeg.result) =
            fun w => (((env "e" * ((env "d" + (env "e" * w))) ^ (m - 1)) *
            Complex.sinh (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)))) *
            ((2 * env "c"))⁻¹) +
            (((-1) * ((env "b" * env "e") + (((-2) * env "c") * env "d"))) * ((2 * env "c"))⁻¹) *
            Φ "I1" w + ((((-1) * (env "e") ^ 2) * (env "m" + (-1))) * ((2 * env "c"))⁻¹) *
            Φ "I2" w := by
      funext w
      simp [rubi6113r14Nondeg, eval, recEnv, Interp.complex, emmm1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi6113r14Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) *
        Complex.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) := by
      simp [rubi6113r14Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (env "e")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m -
        1) _ (hdzm (m -
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).mul ((Complex.hasDerivAt_sinh _).comp t (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((2 * env "c"))⁻¹))).add (hΦ'1.const_mul _)).add (hΦ'2.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      show m - 1 - 1 = m -
          2 by ring]
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.cosh_sq_sub_sinh_sq ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 2 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have el1m : ((env "d" + (env "e" * t))) ^ (m - 1) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 1 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 1 hdmm
        rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
      have el2m : ((env "d" + (env "e" * t))) ^ (m) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 2 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 2 hdmm
        rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
      have el3m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 3 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 3 hdmm
        rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have el4m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 4 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 4 hdmm
        rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [el1m, el2m]
      generalize ((env "d" + (env "e" * t))) ^ (m - 2) = Pm
      generalize Complex.sinh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = S at hP ⊢
      generalize Complex.cosh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = C at hP ⊢
      have hqm1a : (1 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
      have hqm1b : (((m : ℤ) : ℂ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
      have hqm2a : (2 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
      have hqm2b : (((m : ℤ) : ℂ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
      have hqm3a : (3 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
      have hqm3b : (((m : ℤ) : ℂ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
      field_simp
      ring

/-! ## rubi6113r17Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi6113r17Nondeg_real : rubi6113r17Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6113r17Nondeg.conditions rubi6113r17Nondeg.body
    rubi6113r17Nondeg.result rubi6113r17Nondeg.integrals
  intro env hc t hF
  have hn1 : (env "b" * env "e") + (((-2) * env "c") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r17Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi6113r17Nondeg])
  have hn2_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi6113r17Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi6113r17Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi6113r17Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) := by
    intro w h
    simp [rubi6113r17Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, emm1, emm2, iv2R] at h ⊢
      try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r17Nondeg, Defined, eval, recEnv, Interp.real, emm1, ivm1R,
        iv2R] at h hn1 hn2_0 hn2_1 ⊢
    try tauto
  · simp only [rubi6113r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    have hΦ'1 : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m + 1) *
        Real.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ.1 using 1
      simp [eval, Interp.real, emm1, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ'2 : HasDerivAt (Φ "I2") (((env "d" + (env "e" * t))) ^ (m + 2) *
        Real.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ.2 using 1
      simp [eval, Interp.real, emm2, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi6113r17Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r17Nondeg.result) =
            fun w => ((((env "d" + (env "e" * w))) ^ (m + 1) *
            Real.sinh (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)))) *
            ((env "e" * (env "m" + 1)))⁻¹) +
            (((-1) * ((env "b" * env "e") + (((-2) * env "c") * env "d"))) *
            (((env "e") ^ 2 * (env "m" + 1)))⁻¹) * Φ "I1" w +
            (((-2) * env "c") * (((env "e") ^ 2 * (env "m" + 1)))⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi6113r17Nondeg, eval, recEnv, Interp.real, emm1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi6113r17Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) *
        Real.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) := by
      simp [rubi6113r17Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))).mul ((Real.hasDerivAt_sinh _).comp t (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((env "e" * (env "m" + 1)))⁻¹))).add (hΦ'1.const_mul _)).add (hΦ'2.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      add_sub_cancel_right]
    have hn2_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.cosh_sq_sub_sinh_sq ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "d" + (env "e" * t))) ^ m = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 1 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 2 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 3 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m, e1m, e2m]
      generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
      generalize Real.sinh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = S at hP ⊢
      generalize Real.cosh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = C at hP ⊢
      field_simp
      ring

set_option maxHeartbeats 1000000 in
theorem rubi6113r17Nondeg_complex : rubi6113r17Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6113r17Nondeg.conditions rubi6113r17Nondeg.body
    rubi6113r17Nondeg.result rubi6113r17Nondeg.integrals
  intro env hc t hF
  have hn1 : (env "b" * env "e") + (((-2) * env "c") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r17Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi6113r17Nondeg])
  have hn2_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi6113r17Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi6113r17Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi6113r17Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) := by
    intro w h
    simp [rubi6113r17Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, emm1, emm2, iv2C] at h ⊢
      try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r17Nondeg, Defined, eval, recEnv, Interp.complex, emm1, ivm1C,
        iv2C] at h hn1 hn2_0 hn2_1 ⊢
    try tauto
  · simp only [rubi6113r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    have hΦ'1 : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m + 1) *
        Complex.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ.1 using 1
      simp [eval, Interp.complex, emm1, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ'2 : HasDerivAt (Φ "I2") (((env "d" + (env "e" * t))) ^ (m + 2) *
        Complex.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ.2 using 1
      simp [eval, Interp.complex, emm2, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi6113r17Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r17Nondeg.result) =
            fun w => ((((env "d" + (env "e" * w))) ^ (m + 1) *
            Complex.sinh (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)))) *
            ((env "e" * (env "m" + 1)))⁻¹) +
            (((-1) * ((env "b" * env "e") + (((-2) * env "c") * env "d"))) *
            (((env "e") ^ 2 * (env "m" + 1)))⁻¹) * Φ "I1" w +
            (((-2) * env "c") * (((env "e") ^ 2 * (env "m" + 1)))⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi6113r17Nondeg, eval, recEnv, Interp.complex, emm1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi6113r17Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) *
        Complex.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) := by
      simp [rubi6113r17Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))).mul ((Complex.hasDerivAt_sinh _).comp t (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((env "e" * (env "m" + 1)))⁻¹))).add (hΦ'1.const_mul _)).add (hΦ'2.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      add_sub_cancel_right]
    have hn2_1c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.cosh_sq_sub_sinh_sq ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "d" + (env "e" * t))) ^ m = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 1 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 2 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 3 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m, e1m, e2m]
      generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
      generalize Complex.sinh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = S at hP ⊢
      generalize Complex.cosh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = C at hP ⊢
      field_simp
      ring

/-! ## rubi6113r18Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi6113r18Nondeg_real : rubi6113r18Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6113r18Nondeg.conditions rubi6113r18Nondeg.body
    rubi6113r18Nondeg.result rubi6113r18Nondeg.integrals
  intro env hc t hF
  have hn1 : (env "b" * env "e") + (((-2) * env "c") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r18Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi6113r18Nondeg])
  have hn2_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi6113r18Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi6113r18Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi6113r18Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) := by
    intro w h
    simp [rubi6113r18Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r18Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, emm1, emm2, iv2R] at h ⊢
      try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r18Nondeg, Defined, eval, recEnv, Interp.real, emm1, ivm1R,
        iv2R] at h hn1 hn2_0 hn2_1 ⊢
    try tauto
  · simp only [rubi6113r18Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    have hΦ'1 : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m + 1) *
        Real.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ.1 using 1
      simp [eval, Interp.real, emm1, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ'2 : HasDerivAt (Φ "I2") (((env "d" + (env "e" * t))) ^ (m + 2) *
        Real.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ.2 using 1
      simp [eval, Interp.real, emm2, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi6113r18Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r18Nondeg.result) =
            fun w => ((((env "d" + (env "e" * w))) ^ (m + 1) *
            Real.cosh (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)))) *
            ((env "e" * (env "m" + 1)))⁻¹) +
            (((-1) * ((env "b" * env "e") + (((-2) * env "c") * env "d"))) *
            (((env "e") ^ 2 * (env "m" + 1)))⁻¹) * Φ "I1" w +
            (((-2) * env "c") * (((env "e") ^ 2 * (env "m" + 1)))⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi6113r18Nondeg, eval, recEnv, Interp.real, emm1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi6113r18Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) *
        Real.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) := by
      simp [rubi6113r18Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))).mul ((Real.hasDerivAt_cosh _).comp t (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((env "e" * (env "m" + 1)))⁻¹))).add (hΦ'1.const_mul _)).add (hΦ'2.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      add_sub_cancel_right]
    have hn2_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.cosh_sq_sub_sinh_sq ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "d" + (env "e" * t))) ^ m = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 1 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 2 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 3 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m, e1m, e2m]
      generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
      generalize Real.sinh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = S at hP ⊢
      generalize Real.cosh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = C at hP ⊢
      field_simp
      ring

set_option maxHeartbeats 1000000 in
theorem rubi6113r18Nondeg_complex : rubi6113r18Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6113r18Nondeg.conditions rubi6113r18Nondeg.body
    rubi6113r18Nondeg.result rubi6113r18Nondeg.integrals
  intro env hc t hF
  have hn1 : (env "b" * env "e") + (((-2) * env "c") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r18Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi6113r18Nondeg])
  have hn2_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi6113r18Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi6113r18Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi6113r18Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) := by
    intro w h
    simp [rubi6113r18Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r18Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, emm1, emm2, iv2C] at h ⊢
      try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r18Nondeg, Defined, eval, recEnv, Interp.complex, emm1, ivm1C,
        iv2C] at h hn1 hn2_0 hn2_1 ⊢
    try tauto
  · simp only [rubi6113r18Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    have hΦ'1 : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m + 1) *
        Complex.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ.1 using 1
      simp [eval, Interp.complex, emm1, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ'2 : HasDerivAt (Φ "I2") (((env "d" + (env "e" * t))) ^ (m + 2) *
        Complex.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ.2 using 1
      simp [eval, Interp.complex, emm2, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi6113r18Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r18Nondeg.result) =
            fun w => ((((env "d" + (env "e" * w))) ^ (m + 1) *
            Complex.cosh (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)))) *
            ((env "e" * (env "m" + 1)))⁻¹) +
            (((-1) * ((env "b" * env "e") + (((-2) * env "c") * env "d"))) *
            (((env "e") ^ 2 * (env "m" + 1)))⁻¹) * Φ "I1" w +
            (((-2) * env "c") * (((env "e") ^ 2 * (env "m" + 1)))⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi6113r18Nondeg, eval, recEnv, Interp.complex, emm1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi6113r18Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) *
        Complex.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) := by
      simp [rubi6113r18Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))).mul ((Complex.hasDerivAt_cosh _).comp t (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((env "e" * (env "m" + 1)))⁻¹))).add (hΦ'1.const_mul _)).add (hΦ'2.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      add_sub_cancel_right]
    have hn2_1c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.cosh_sq_sub_sinh_sq ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "d" + (env "e" * t))) ^ m = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 1 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 2 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 3 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m, e1m, e2m]
      generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
      generalize Complex.sinh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = S at hP ⊢
      generalize Complex.cosh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = C at hP ⊢
      field_simp
      ring

/-! ## rubi1222r16Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi1222r16Nondeg_real : rubi1222r16Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1222r16Nondeg.conditions rubi1222r16Nondeg.body
    rubi1222r16Nondeg.result rubi1222r16Nondeg.integrals
  intro env hc t hF
  have ivl3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have ivl4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have ivl5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have hn0 : (env "b") ^ 2 + (((-4) * env "a") * env "c") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, ivl3, ivl4,
        ivl5] using hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1222r16Nondeg])
  have hc4 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi1222r16Nondeg])
  have hn4_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_1 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_2 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1222r16Nondeg, Defined, eval, Interp.real, hkm, iv2R, ivl4] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1222r16Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, ivl4] at h
  have hb1 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi1222r16Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "p" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1222r16Nondeg.body →
      (m < 0 → (env "d" * w) ≠ 0) ∧
          (k < 0 → ((env "a" + (env "b" * (w) ^ 2)) + (env "c" * (w) ^ 4)) ≠ 0) := by
    intro w h
    simp [rubi1222r16Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, ivl4] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1222r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkk, emm2, iv2R, ivl4] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1222r16Nondeg, Defined, eval, recEnv, Interp.real, emm1, emk1, ivm1R, iv2R,
        ivl4] at h hn0 hn4_0 hn4_1 hn4_2 ⊢
    try tauto
  · simp only [rubi1222r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "d" * t)) ^ (m + 2) *
        ((env "b" * ((env "m" + (2 * env "p")) + 3)) +
        ((env "c" * ((env "m" + (4 * env "p")) + 5)) * (t) ^ 2))) *
        (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkk, emm2, iv2R, ivl4, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1222r16Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1222r16Nondeg.result) =
            fun w => ((((env "d" * w)) ^ (m + 1) *
            (((env "a" + (env "b" * (w) ^ 2)) + (env "c" * (w) ^ 4))) ^ (k + 1)) *
            (((env "a" * env "d") * (env "m" + 1)))⁻¹) +
            ((-1) * (((env "a" * (env "d") ^ 2) * (env "m" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1222r16Nondeg, eval, recEnv, Interp.real, emm1, emk1, ivm1R, iv2R, ivl4,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1222r16Nondeg.body =
        ((env "d" * t)) ^ (m) * (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k) :=
        by
      simp [rubi1222r16Nondeg, eval, Interp.real, hkm, hkk, iv2R, ivl4]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" * t) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        ((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((hasDerivAt_id' t).pow 2))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 4))))).mul (hasDerivAt_const t ((((env "a" * env "d") * (env "m" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn4_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn4_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb1 (by omega)
      · subst hm0
        exact absurd hb1 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "d" * t) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "d" * t)) ^ m = ((env "d" * t)) ^ (m - 1) * ((env "d" * t)) ^ 1 := by
          have := zsplit ((env "d" * t)) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "d" * t)) ^ (m + 1) = ((env "d" * t)) ^ (m - 1) * ((env "d" * t)) ^ 2 := by
          have := zsplit ((env "d" * t)) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "d" * t)) ^ (m + 2) = ((env "d" * t)) ^ (m - 1) * ((env "d" * t)) ^ 3 := by
          have := zsplit ((env "d" * t)) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m, e2m]
        generalize ((env "d" * t)) ^ (m - 1) = Pm
        field_simp
        ring
      · have hdmm : (env "d" * t) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "d" * t)) ^ m = ((env "d" * t)) ^ (m - 1) * ((env "d" * t)) ^ 1 := by
          have := zsplit ((env "d" * t)) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "d" * t)) ^ (m + 1) = ((env "d" * t)) ^ (m - 1) * ((env "d" * t)) ^ 2 := by
          have := zsplit ((env "d" * t)) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "d" * t)) ^ (m + 2) = ((env "d" * t)) ^ (m - 1) * ((env "d" * t)) ^ 3 := by
          have := zsplit ((env "d" * t)) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m, e2m]
        have hdmk : ((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ k =
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) *
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ 1 := by
          have := zsplit (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k + 1) =
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) *
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ 2 := by
          have := zsplit (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k + 2) =
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) *
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ 3 := by
          have := zsplit (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "d" * t)) ^ (m - 1) = Pm
        generalize (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) = Pk
        field_simp
        ring

set_option maxHeartbeats 1000000 in
theorem rubi1222r16Nondeg_complex : rubi1222r16Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1222r16Nondeg.conditions rubi1222r16Nondeg.body
    rubi1222r16Nondeg.result rubi1222r16Nondeg.integrals
  intro env hc t hF
  have ivl3 : intValue? (3 : ℂ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have ivl4 : intValue? (4 : ℂ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have ivl5 : intValue? (5 : ℂ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have hn0 : (env "b") ^ 2 + (((-4) * env "a") * env "c") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, ivl3, ivl4,
        ivl5] using hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1222r16Nondeg])
  have hc4 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi1222r16Nondeg])
  have hn4_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval,
      h0] at hc4
  have hn4_1 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval,
      h0] at hc4
  have hn4_2 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval,
      h0] at hc4
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1222r16Nondeg, Defined, eval, Interp.complex, hkm, iv2C, ivl4] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1222r16Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C, ivl4] at h
  have hb1 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi1222r16Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "p" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1222r16Nondeg.body →
      (m < 0 → (env "d" * w) ≠ 0) ∧
          (k < 0 → ((env "a" + (env "b" * (w) ^ 2)) + (env "c" * (w) ^ 4)) ≠ 0) := by
    intro w h
    simp [rubi1222r16Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C, ivl4] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1222r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkk, emm2, iv2C, ivl4] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1222r16Nondeg, Defined, eval, recEnv, Interp.complex, emm1, emk1, ivm1C, iv2C,
        ivl4] at h hn0 hn4_0 hn4_1 hn4_2 ⊢
    try tauto
  · simp only [rubi1222r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "d" * t)) ^ (m + 2) *
        ((env "b" * ((env "m" + (2 * env "p")) + 3)) +
        ((env "c" * ((env "m" + (4 * env "p")) + 5)) * (t) ^ 2))) *
        (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkk, emm2, iv2C, ivl4, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1222r16Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1222r16Nondeg.result) =
            fun w => ((((env "d" * w)) ^ (m + 1) *
            (((env "a" + (env "b" * (w) ^ 2)) + (env "c" * (w) ^ 4))) ^ (k + 1)) *
            (((env "a" * env "d") * (env "m" + 1)))⁻¹) +
            ((-1) * (((env "a" * (env "d") ^ 2) * (env "m" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1222r16Nondeg, eval, recEnv, Interp.complex, emm1, emk1, ivm1C, iv2C, ivl4,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1222r16Nondeg.body =
        ((env "d" * t)) ^ (m) * (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k) :=
        by
      simp [rubi1222r16Nondeg, eval, Interp.complex, hkm, hkk, iv2C, ivl4]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" * t) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        ((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((hasDerivAt_id' t).pow 2))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 4))))).mul (hasDerivAt_const t ((((env "a" * env "d") * (env "m" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn4_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn4_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb1 (by omega)
      · subst hm0
        exact absurd hb1 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "d" * t) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "d" * t)) ^ m = ((env "d" * t)) ^ (m - 1) * ((env "d" * t)) ^ 1 := by
          have := zsplit ((env "d" * t)) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "d" * t)) ^ (m + 1) = ((env "d" * t)) ^ (m - 1) * ((env "d" * t)) ^ 2 := by
          have := zsplit ((env "d" * t)) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "d" * t)) ^ (m + 2) = ((env "d" * t)) ^ (m - 1) * ((env "d" * t)) ^ 3 := by
          have := zsplit ((env "d" * t)) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m, e2m]
        generalize ((env "d" * t)) ^ (m - 1) = Pm
        field_simp
        ring
      · have hdmm : (env "d" * t) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "d" * t)) ^ m = ((env "d" * t)) ^ (m - 1) * ((env "d" * t)) ^ 1 := by
          have := zsplit ((env "d" * t)) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "d" * t)) ^ (m + 1) = ((env "d" * t)) ^ (m - 1) * ((env "d" * t)) ^ 2 := by
          have := zsplit ((env "d" * t)) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "d" * t)) ^ (m + 2) = ((env "d" * t)) ^ (m - 1) * ((env "d" * t)) ^ 3 := by
          have := zsplit ((env "d" * t)) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m, e2m]
        have hdmk : ((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ k =
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) *
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ 1 := by
          have := zsplit (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k + 1) =
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) *
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ 2 := by
          have := zsplit (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k + 2) =
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) *
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ 3 := by
          have := zsplit (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "d" * t)) ^ (m - 1) = Pm
        generalize (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) = Pk
        field_simp
        ring

/-! ## rubi1224r33Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi1224r33Nondeg_real : rubi1224r33Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1224r33Nondeg.conditions rubi1224r33Nondeg.body
    rubi1224r33Nondeg.result rubi1224r33Nondeg.integrals
  intro env hc t hF
  have ivl3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have ivl4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have ivl5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have hn0 : (env "b") ^ 2 + (((-4) * env "a") * env "c") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, ivl3, ivl4,
        ivl5] using hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1224r33Nondeg])
  have hc4 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi1224r33Nondeg])
  have hn4_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_2 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r33Nondeg, Defined, eval, Interp.real, hkm, iv2R, ivl4] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r33Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, ivl4] at h
  have hb1 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi1224r33Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "p" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1224r33Nondeg.body →
      (m < 0 → (env "f" * w) ≠ 0) ∧
          (k < 0 → ((env "a" + (env "b" * (w) ^ 2)) + (env "c" * (w) ^ 4)) ≠ 0) := by
    intro w h
    simp [rubi1224r33Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, ivl4] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1224r33Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkk, emm2, iv2R, ivl4] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1224r33Nondeg, Defined, eval, recEnv, Interp.real, emm1, emk1, ivm1R, iv2R,
        ivl4] at h hn0 hn4_0 hn4_1 hn4_2 ⊢
    try tauto
  · simp only [rubi1224r33Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "f" * t)) ^ (m + 2) *
        (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k)) *
        ((((env "a" * env "e") * (env "m" + 1)) +
        ((((-1) * env "b") * env "d") * ((env "m" + (2 * env "p")) + 3))) +
        (((((-1) * env "c") * env "d") * ((env "m" + (4 * env "p")) + 5)) * (t) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkk, emm2, iv2R, ivl4, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1224r33Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1224r33Nondeg.result) =
            fun w => (((env "d" * ((env "f" * w)) ^ (m + 1)) *
            (((env "a" + (env "b" * (w) ^ 2)) + (env "c" * (w) ^ 4))) ^ (k + 1)) *
            (((env "a" * env "f") * (env "m" + 1)))⁻¹) +
            (1 * (((env "a" * (env "f") ^ 2) * (env "m" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1224r33Nondeg, eval, recEnv, Interp.real, emm1, emk1, ivm1R, iv2R, ivl4,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1224r33Nondeg.body =
        (((env "f" * t)) ^ (m) * (env "d" + (env "e" * (t) ^ 2))) *
        (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k) := by
      simp [rubi1224r33Nondeg, eval, Interp.real, hkm, hkk, iv2R, ivl4]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "f" * t) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        ((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "d")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((hasDerivAt_id' t).pow 2))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 4))))).mul (hasDerivAt_const t ((((env "a" * env "f") * (env "m" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn4_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn4_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb1 (by omega)
      · subst hm0
        exact absurd hb1 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "f" * t) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "f" * t)) ^ m = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 1 := by
          have := zsplit ((env "f" * t)) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "f" * t)) ^ (m + 1) = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 2 := by
          have := zsplit ((env "f" * t)) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "f" * t)) ^ (m + 2) = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 3 := by
          have := zsplit ((env "f" * t)) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m, e2m]
        generalize ((env "f" * t)) ^ (m - 1) = Pm
        field_simp
        ring
      · have hdmm : (env "f" * t) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "f" * t)) ^ m = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 1 := by
          have := zsplit ((env "f" * t)) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "f" * t)) ^ (m + 1) = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 2 := by
          have := zsplit ((env "f" * t)) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "f" * t)) ^ (m + 2) = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 3 := by
          have := zsplit ((env "f" * t)) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m, e2m]
        have hdmk : ((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ k =
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) *
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ 1 := by
          have := zsplit (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k + 1) =
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) *
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ 2 := by
          have := zsplit (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k + 2) =
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) *
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ 3 := by
          have := zsplit (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "f" * t)) ^ (m - 1) = Pm
        generalize (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) = Pk
        field_simp
        ring

set_option maxHeartbeats 1000000 in
theorem rubi1224r33Nondeg_complex : rubi1224r33Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1224r33Nondeg.conditions rubi1224r33Nondeg.body
    rubi1224r33Nondeg.result rubi1224r33Nondeg.integrals
  intro env hc t hF
  have ivl3 : intValue? (3 : ℂ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have ivl4 : intValue? (4 : ℂ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have ivl5 : intValue? (5 : ℂ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have hn0 : (env "b") ^ 2 + (((-4) * env "a") * env "c") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, ivl3, ivl4,
        ivl5] using hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1224r33Nondeg])
  have hc4 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi1224r33Nondeg])
  have hn4_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval,
      h0] at hc4
  have hn4_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval,
      h0] at hc4
  have hn4_2 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval,
      h0] at hc4
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r33Nondeg, Defined, eval, Interp.complex, hkm, iv2C, ivl4] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r33Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C, ivl4] at h
  have hb1 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi1224r33Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "p" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1224r33Nondeg.body →
      (m < 0 → (env "f" * w) ≠ 0) ∧
          (k < 0 → ((env "a" + (env "b" * (w) ^ 2)) + (env "c" * (w) ^ 4)) ≠ 0) := by
    intro w h
    simp [rubi1224r33Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C, ivl4] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1224r33Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkk, emm2, iv2C, ivl4] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1224r33Nondeg, Defined, eval, recEnv, Interp.complex, emm1, emk1, ivm1C, iv2C,
        ivl4] at h hn0 hn4_0 hn4_1 hn4_2 ⊢
    try tauto
  · simp only [rubi1224r33Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "f" * t)) ^ (m + 2) *
        (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k)) *
        ((((env "a" * env "e") * (env "m" + 1)) +
        ((((-1) * env "b") * env "d") * ((env "m" + (2 * env "p")) + 3))) +
        (((((-1) * env "c") * env "d") * ((env "m" + (4 * env "p")) + 5)) * (t) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkk, emm2, iv2C, ivl4, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1224r33Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1224r33Nondeg.result) =
            fun w => (((env "d" * ((env "f" * w)) ^ (m + 1)) *
            (((env "a" + (env "b" * (w) ^ 2)) + (env "c" * (w) ^ 4))) ^ (k + 1)) *
            (((env "a" * env "f") * (env "m" + 1)))⁻¹) +
            (1 * (((env "a" * (env "f") ^ 2) * (env "m" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1224r33Nondeg, eval, recEnv, Interp.complex, emm1, emk1, ivm1C, iv2C, ivl4,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1224r33Nondeg.body =
        (((env "f" * t)) ^ (m) * (env "d" + (env "e" * (t) ^ 2))) *
        (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k) := by
      simp [rubi1224r33Nondeg, eval, Interp.complex, hkm, hkk, iv2C, ivl4]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "f" * t) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        ((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "d")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((hasDerivAt_id' t).pow 2))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 4))))).mul (hasDerivAt_const t ((((env "a" * env "f") * (env "m" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn4_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn4_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb1 (by omega)
      · subst hm0
        exact absurd hb1 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "f" * t) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "f" * t)) ^ m = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 1 := by
          have := zsplit ((env "f" * t)) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "f" * t)) ^ (m + 1) = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 2 := by
          have := zsplit ((env "f" * t)) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "f" * t)) ^ (m + 2) = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 3 := by
          have := zsplit ((env "f" * t)) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m, e2m]
        generalize ((env "f" * t)) ^ (m - 1) = Pm
        field_simp
        ring
      · have hdmm : (env "f" * t) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "f" * t)) ^ m = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 1 := by
          have := zsplit ((env "f" * t)) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "f" * t)) ^ (m + 1) = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 2 := by
          have := zsplit ((env "f" * t)) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "f" * t)) ^ (m + 2) = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 3 := by
          have := zsplit ((env "f" * t)) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m, e2m]
        have hdmk : ((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ k =
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) *
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ 1 := by
          have := zsplit (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k + 1) =
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) *
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ 2 := by
          have := zsplit (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k + 2) =
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) *
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ 3 := by
          have := zsplit (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "f" * t)) ^ (m - 1) = Pm
        generalize (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) = Pk
        field_simp
        ring

/-! ## rubi1224r34Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi1224r34Nondeg_real : rubi1224r34Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1224r34Nondeg.conditions rubi1224r34Nondeg.body
    rubi1224r34Nondeg.result rubi1224r34Nondeg.integrals
  intro env hc t hF
  have ivl4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have ivl5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi1224r34Nondeg])
  have hn3_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r34Nondeg, Defined, eval, Interp.real, hkm, iv2R, ivl4] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r34Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, ivl4] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi1224r34Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "p" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1224r34Nondeg.body →
      (m < 0 → (env "f" * w) ≠ 0) ∧ (k < 0 → (env "a" + (env "c" * (w) ^ 4)) ≠ 0) := by
    intro w h
    simp [rubi1224r34Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, ivl4] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1224r34Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkk, emm2, iv2R, ivl4] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1224r34Nondeg, Defined, eval, recEnv, Interp.real, emm1, emk1, ivm1R, iv2R,
        ivl4] at h hn3_0 hn3_1 hn3_2 ⊢
    try tauto
  · simp only [rubi1224r34Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "f" * t)) ^ (m + 2) *
        ((env "a" + (env "c" * (t) ^ 4))) ^ (k)) *
        (((env "a" * env "e") * (env "m" + 1)) +
        (((((-1) * env "c") * env "d") * ((env "m" + (4 * env "p")) + 5)) * (t) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkk, emm2, iv2R, ivl4, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1224r34Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1224r34Nondeg.result) =
            fun w => (((env "d" * ((env "f" * w)) ^ (m + 1)) *
            ((env "a" + (env "c" * (w) ^ 4))) ^ (k + 1)) *
            (((env "a" * env "f") * (env "m" + 1)))⁻¹) +
            (1 * (((env "a" * (env "f") ^ 2) * (env "m" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1224r34Nondeg, eval, recEnv, Interp.real, emm1, emk1, ivm1R, iv2R, ivl4,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1224r34Nondeg.body =
        (((env "f" * t)) ^ (m) * (env "d" + (env "e" * (t) ^ 2))) *
        ((env "a" + (env "c" * (t) ^ 4))) ^ (k) := by
      simp [rubi1224r34Nondeg, eval, Interp.real, hkm, hkk, iv2R, ivl4]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "f" * t) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) → (env "a" + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "d")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 4))))).mul (hasDerivAt_const t ((((env "a" * env "f") * (env "m" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn3_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb0 (by omega)
      · subst hm0
        exact absurd hb0 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "f" * t) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "f" * t)) ^ m = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 1 := by
          have := zsplit ((env "f" * t)) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "f" * t)) ^ (m + 1) = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 2 := by
          have := zsplit ((env "f" * t)) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "f" * t)) ^ (m + 2) = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 3 := by
          have := zsplit ((env "f" * t)) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m, e2m]
        generalize ((env "f" * t)) ^ (m - 1) = Pm
        field_simp
        ring
      · have hdmm : (env "f" * t) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "f" * t)) ^ m = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 1 := by
          have := zsplit ((env "f" * t)) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "f" * t)) ^ (m + 1) = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 2 := by
          have := zsplit ((env "f" * t)) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "f" * t)) ^ (m + 2) = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 3 := by
          have := zsplit ((env "f" * t)) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m, e2m]
        have hdmk : (env "a" + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "a" + (env "c" * (t) ^ 4))) ^ k =
            ((env "a" + (env "c" * (t) ^ 4))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 4))) ^ 1 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 4))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "a" + (env "c" * (t) ^ 4))) ^ (k + 1) =
            ((env "a" + (env "c" * (t) ^ 4))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 4))) ^ 2 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 4))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "a" + (env "c" * (t) ^ 4))) ^ (k + 2) =
            ((env "a" + (env "c" * (t) ^ 4))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 4))) ^ 3 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 4))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "f" * t)) ^ (m - 1) = Pm
        generalize ((env "a" + (env "c" * (t) ^ 4))) ^ (k - 1) = Pk
        field_simp
        ring

set_option maxHeartbeats 1000000 in
theorem rubi1224r34Nondeg_complex : rubi1224r34Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1224r34Nondeg.conditions rubi1224r34Nondeg.body
    rubi1224r34Nondeg.result rubi1224r34Nondeg.integrals
  intro env hc t hF
  have ivl4 : intValue? (4 : ℂ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have ivl5 : intValue? (5 : ℂ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi1224r34Nondeg])
  have hn3_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r34Nondeg, Defined, eval, Interp.complex, hkm, iv2C, ivl4] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r34Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C, ivl4] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi1224r34Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "p" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1224r34Nondeg.body →
      (m < 0 → (env "f" * w) ≠ 0) ∧ (k < 0 → (env "a" + (env "c" * (w) ^ 4)) ≠ 0) := by
    intro w h
    simp [rubi1224r34Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C, ivl4] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1224r34Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkk, emm2, iv2C, ivl4] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1224r34Nondeg, Defined, eval, recEnv, Interp.complex, emm1, emk1, ivm1C, iv2C,
        ivl4] at h hn3_0 hn3_1 hn3_2 ⊢
    try tauto
  · simp only [rubi1224r34Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "f" * t)) ^ (m + 2) *
        ((env "a" + (env "c" * (t) ^ 4))) ^ (k)) *
        (((env "a" * env "e") * (env "m" + 1)) +
        (((((-1) * env "c") * env "d") * ((env "m" + (4 * env "p")) + 5)) * (t) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkk, emm2, iv2C, ivl4, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1224r34Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1224r34Nondeg.result) =
            fun w => (((env "d" * ((env "f" * w)) ^ (m + 1)) *
            ((env "a" + (env "c" * (w) ^ 4))) ^ (k + 1)) *
            (((env "a" * env "f") * (env "m" + 1)))⁻¹) +
            (1 * (((env "a" * (env "f") ^ 2) * (env "m" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1224r34Nondeg, eval, recEnv, Interp.complex, emm1, emk1, ivm1C, iv2C, ivl4,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1224r34Nondeg.body =
        (((env "f" * t)) ^ (m) * (env "d" + (env "e" * (t) ^ 2))) *
        ((env "a" + (env "c" * (t) ^ 4))) ^ (k) := by
      simp [rubi1224r34Nondeg, eval, Interp.complex, hkm, hkk, iv2C, ivl4]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "f" * t) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) → (env "a" + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "d")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 4))))).mul (hasDerivAt_const t ((((env "a" * env "f") * (env "m" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn3_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb0 (by omega)
      · subst hm0
        exact absurd hb0 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "f" * t) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "f" * t)) ^ m = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 1 := by
          have := zsplit ((env "f" * t)) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "f" * t)) ^ (m + 1) = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 2 := by
          have := zsplit ((env "f" * t)) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "f" * t)) ^ (m + 2) = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 3 := by
          have := zsplit ((env "f" * t)) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m, e2m]
        generalize ((env "f" * t)) ^ (m - 1) = Pm
        field_simp
        ring
      · have hdmm : (env "f" * t) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "f" * t)) ^ m = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 1 := by
          have := zsplit ((env "f" * t)) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "f" * t)) ^ (m + 1) = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 2 := by
          have := zsplit ((env "f" * t)) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "f" * t)) ^ (m + 2) = ((env "f" * t)) ^ (m - 1) * ((env "f" * t)) ^ 3 := by
          have := zsplit ((env "f" * t)) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m, e2m]
        have hdmk : (env "a" + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "a" + (env "c" * (t) ^ 4))) ^ k =
            ((env "a" + (env "c" * (t) ^ 4))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 4))) ^ 1 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 4))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "a" + (env "c" * (t) ^ 4))) ^ (k + 1) =
            ((env "a" + (env "c" * (t) ^ 4))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 4))) ^ 2 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 4))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "a" + (env "c" * (t) ^ 4))) ^ (k + 2) =
            ((env "a" + (env "c" * (t) ^ 4))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 4))) ^ 3 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 4))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "f" * t)) ^ (m - 1) = Pm
        generalize ((env "a" + (env "c" * (t) ^ 4))) ^ (k - 1) = Pk
        field_simp
        ring

/-! ## rubi4122r25Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4122r25Nondeg_real : rubi4122r25Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4122r25Nondeg.conditions rubi4122r25Nondeg.body
    rubi4122r25Nondeg.result rubi4122r25Nondeg.integrals
  intro env hc t hF
  have ivln3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivl3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have hr0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4122r25Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 3))) (.int 0)) (by simp [rubi4122r25Nondeg])
  have hn2_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  have hn2_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  have hn2_2 : (2 * env "m") + 3 ≠ 0 := by
    have h := hc2
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    tauto
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr0 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn2_0 (by linear_combination (1) * hzb)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r25Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4122r25Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4122r25Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r25Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emm2] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4122r25Nondeg, Defined, eval, recEnv, Interp.real, emm1, ivm1R, iv2R,
        ivl3] at h hn2_0 hn2_1 hn2_2 hda ⊢
    try tauto
  · simp only [rubi4122r25Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) *
        (((env "b" * env "c") + (((2 * env "a") * env "d") * (env "m" + 1))) +
        (((((-1) * env "b") * env "d") * ((2 * env "m") + 3)) *
        Real.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emm2, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4122r25Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r25Nondeg.result) =
            fun w => ((((2 * ((env "b" * env "c") + (((-1) * env "a") * env "d"))) *
            Real.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            ((((env "b") ^ 2 * env "f") * ((2 * env "m") + 3)))⁻¹) +
            (1 * (((env "b") ^ 3 * ((2 * env "m") + 3)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4122r25Nondeg, eval, recEnv, Interp.real, emm1, ivm1R, iv2R, ivl3,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4122r25Nondeg.body =
        ((Real.cos ((env "e" + (env "f" * t)))) ^ 2 *
        ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m)) *
        (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) := by
      simp [rubi4122r25Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((2 *
        ((env "b" * env "c") +
        (((-1) * env "a") *
        env "d"))))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdzm (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((((env "b") ^ 2 * env "f") * ((2 * env "m") + 3)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn2_2c : (2 * ((m : ℤ) : ℝ)) + 3 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero]
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-2*env "a"*env "b"^2*env "d" - env "b"^3*env "c" -
          3*env "b"^3*env "d"*S) * hP +
          (2*env "a"*env "d" + env "b"*env "c" + 3*env "b"*env "d"*S) * hr0
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
      simp only [e0m, e1m, e2m]
      generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-2*env "a"^2*env "b"^2*env "d"*env "f"*Pm*((m : ℤ) : ℝ) -
          2*env "a"^2*env "b"^2*env "d"*env "f"*Pm - env "a"*env "b"^3*env "c"*env "f"*Pm -
          4*env "a"*env "b"^3*env "d"*env "f"*Pm*S*((m : ℤ) : ℝ) -
          5*env "a"*env "b"^3*env "d"*env "f"*Pm*S - env "b"^4*env "c"*env "f"*Pm*S -
          2*env "b"^4*env "d"*env "f"*Pm*S^2*((m : ℤ) : ℝ) - 3*env "b"^4*env "d"*env "f"*Pm*S^2) *
          hP + (2*env "a"^2*env "d"*env "f"*Pm*((m : ℤ) : ℝ) + 2*env "a"^2*env "d"*env "f"*Pm +
          env "a"*env "b"*env "c"*env "f"*Pm +
          4*env "a"*env "b"*env "d"*env "f"*Pm*S*((m : ℤ) : ℝ) +
          5*env "a"*env "b"*env "d"*env "f"*Pm*S + env "b"^2*env "c"*env "f"*Pm*S +
          2*env "b"^2*env "d"*env "f"*Pm*S^2*((m : ℤ) : ℝ) + 3*env "b"^2*env "d"*env "f"*Pm*S^2) *
          hr0

set_option maxHeartbeats 1000000 in
theorem rubi4122r25Nondeg_complex : rubi4122r25Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4122r25Nondeg.conditions rubi4122r25Nondeg.body
    rubi4122r25Nondeg.result rubi4122r25Nondeg.integrals
  intro env hc t hF
  have ivln3 : intValue? (-3 : ℂ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivl3 : intValue? (3 : ℂ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have hr0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4122r25Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 3))) (.int 0)) (by simp [rubi4122r25Nondeg])
  have hn2_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc2
  have hn2_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc2
  have hn2_2 : (2 * env "m") + 3 ≠ 0 := by
    have h := hc2
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    tauto
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr0 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn2_0 (by linear_combination (1) * hzb)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r25Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4122r25Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4122r25Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r25Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emm2] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4122r25Nondeg, Defined, eval, recEnv, Interp.complex, emm1, ivm1C, iv2C,
        ivl3] at h hn2_0 hn2_1 hn2_2 hda ⊢
    try tauto
  · simp only [rubi4122r25Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) *
        (((env "b" * env "c") + (((2 * env "a") * env "d") * (env "m" + 1))) +
        (((((-1) * env "b") * env "d") * ((2 * env "m") + 3)) *
        Complex.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emm2, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4122r25Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r25Nondeg.result) =
            fun w => ((((2 * ((env "b" * env "c") + (((-1) * env "a") * env "d"))) *
            Complex.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            ((((env "b") ^ 2 * env "f") * ((2 * env "m") + 3)))⁻¹) +
            (1 * (((env "b") ^ 3 * ((2 * env "m") + 3)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4122r25Nondeg, eval, recEnv, Interp.complex, emm1, ivm1C, iv2C, ivl3,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4122r25Nondeg.body =
        ((Complex.cos ((env "e" + (env "f" * t)))) ^ 2 *
        ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m)) *
        (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) := by
      simp [rubi4122r25Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((2 *
        ((env "b" * env "c") +
        (((-1) * env "a") *
        env "d"))))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdzm (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((((env "b") ^ 2 * env "f") * ((2 * env "m") + 3)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn2_2c : (2 * ((m : ℤ) : ℂ)) + 3 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero]
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-2*env "a"*env "b"^2*env "d" - env "b"^3*env "c" -
          3*env "b"^3*env "d"*S) * hP +
          (2*env "a"*env "d" + env "b"*env "c" + 3*env "b"*env "d"*S) * hr0
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
      simp only [e0m, e1m, e2m]
      generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-2*env "a"^2*env "b"^2*env "d"*env "f"*Pm*((m : ℤ) : ℂ) -
          2*env "a"^2*env "b"^2*env "d"*env "f"*Pm - env "a"*env "b"^3*env "c"*env "f"*Pm -
          4*env "a"*env "b"^3*env "d"*env "f"*Pm*S*((m : ℤ) : ℂ) -
          5*env "a"*env "b"^3*env "d"*env "f"*Pm*S - env "b"^4*env "c"*env "f"*Pm*S -
          2*env "b"^4*env "d"*env "f"*Pm*S^2*((m : ℤ) : ℂ) - 3*env "b"^4*env "d"*env "f"*Pm*S^2) *
          hP + (2*env "a"^2*env "d"*env "f"*Pm*((m : ℤ) : ℂ) + 2*env "a"^2*env "d"*env "f"*Pm +
          env "a"*env "b"*env "c"*env "f"*Pm +
          4*env "a"*env "b"*env "d"*env "f"*Pm*S*((m : ℤ) : ℂ) +
          5*env "a"*env "b"*env "d"*env "f"*Pm*S + env "b"^2*env "c"*env "f"*Pm*S +
          2*env "b"^2*env "d"*env "f"*Pm*S^2*((m : ℤ) : ℂ) + 3*env "b"^2*env "d"*env "f"*Pm*S^2) *
          hr0

/-! ## rubi4512r53Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4512r53Nondeg_real : rubi4512r53Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4512r53Nondeg.conditions rubi4512r53Nondeg.body
    rubi4512r53Nondeg.result rubi4512r53Nondeg.integrals
  intro env hc t hF
  have ivl3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have hn0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R,
        ivl3] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4512r53Nondeg])
  have hn0v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R,
        ivl3] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4512r53Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int 0)) (by simp [rubi4512r53Nondeg])
  have hn2_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  have hn2_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  have hn2_2 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4512r53Nondeg, Defined, eval, Interp.real, hkm, ivl3, Fn.csc] at h
  have hb1 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4512r53Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4512r53Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4512r53Nondeg, Defined, eval, Interp.real, hkm, ivl3, Fn.csc] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4512r53Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emm1, iv2R, Fn.csc] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4512r53Nondeg, Defined, eval, recEnv, Interp.real, emm1, ivm1R, iv2R,
        Fn.csc] at h hn0 hn2_0 hn2_1 hn2_2 ⊢
    try tauto
  · simp only [rubi4512r53Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1)) *
        (((env "a" * env "b") * (env "m" + 1)) +
        (((-1) * ((env "a") ^ 2 + ((env "b") ^ 2 * (env "m" + 1)))) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emm1, iv2R, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4512r53Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4512r53Nondeg.result) =
            fun w => (((((-1) * (env "a") ^ 2) *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m + 1)) *
            ((((env "b" * env "f") * (env "m" + 1)) *
            ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹) +
            (1 * (((env "b" * (env "m" + 1)) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4512r53Nondeg, eval, recEnv, Interp.real, emm1, ivm1R, iv2R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4512r53Nondeg.body =
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 3 *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m) := by
      simp [rubi4512r53Nondeg, eval, Interp.real, hkm, ivl3, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hBm0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (((-1) *
        (env "a") ^ 2))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdzm (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t (((((env "b" * env "f") * (env "m" + 1)) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply,

      add_sub_cancel_right]
    have hn2_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb1 (by omega)
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
      simp only [e0m, e1m]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = Pm
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "a"^4*env "f"*Pm*S^2 + env "a"^3*env "b"*env "f"*Pm*S*((m : ℤ) : ℝ) +
          3*env "a"^3*env "b"*env "f"*Pm*S + env "a"^2*env "b"^2*env "f"*Pm*((m : ℤ) : ℝ) +
          2*env "a"^2*env "b"^2*env "f"*Pm) * hP

/-! ## rubi4512r54Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4512r54Nondeg_real : rubi4512r54Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4512r54Nondeg.conditions rubi4512r54Nondeg.body
    rubi4512r54Nondeg.result rubi4512r54Nondeg.integrals
  intro env hc t hF
  have ivl3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have hn0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R,
        ivl3] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4512r54Nondeg])
  have hn0v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R,
        ivl3] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4512r54Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 2))) (.int 0)) (by simp [rubi4512r54Nondeg])
  have hn2_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "m" + 2 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4512r54Nondeg, Defined, eval, Interp.real, hkm, ivl3, Fn.csc] at h
  have hb1 : -1 ≤ m := by
    have h := hc (.ge (.var "m") (.int (-1))) (by simp [rubi4512r54Nondeg])
    have h' : (-1 : ℝ) ≤ ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      rcases h with h | h <;> linarith
    exact_mod_cast h'
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4512r54Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4512r54Nondeg, Defined, eval, Interp.real, hkm, ivl3, Fn.csc] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4512r54Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, Fn.csc] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4512r54Nondeg, Defined, eval, recEnv, Interp.real, emm1, ivm1R,
        Fn.csc] at h hn0 hn2_0 hn2_1 hn2_2 ⊢
    try tauto
  · simp only [rubi4512r54Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        ((env "b" * (env "m" + 1)) +
        (((-1) * env "a") * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4512r54Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4512r54Nondeg.result) =
            fun w => ((((-1) *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m + 1)) *
            (((env "b" * env "f") * (env "m" + 2)))⁻¹) + (1 * ((env "b" * (env "m" + 2)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4512r54Nondeg, eval, recEnv, Interp.real, emm1, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4512r54Nondeg.body =
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 3 *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m) := by
      simp [rubi4512r54Nondeg, eval, Interp.real, hkm, ivl3, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hBm0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((-1))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdzm (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t ((((env "b" * env "f") * (env "m" + 2)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply,

      add_sub_cancel_right]
    have hn2_2c : ((m : ℤ) : ℝ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero]
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "a"*S + 2*env "b") * hP
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
      simp only [e0m, e1m]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = Pm
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      have hqm2a : (2 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
      have hqm2b : (((m : ℤ) : ℝ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
      have hqm3a : (3 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
      have hqm3b : (((m : ℤ) : ℝ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
      field_simp
      linear_combination (env "a"^2*env "f"*Pm*S^2 + env "a"*env "b"*env "f"*Pm*S*((m : ℤ) : ℝ) +
          3*env "a"*env "b"*env "f"*Pm*S + env "b"^2*env "f"*Pm*((m : ℤ) : ℝ) +
          2*env "b"^2*env "f"*Pm) * hP

/-! ## rubi4531r33Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4531r33Nondeg_real : rubi4531r33Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4531r33Nondeg.conditions rubi4531r33Nondeg.body
    rubi4531r33Nondeg.result rubi4531r33Nondeg.integrals
  intro env hc t hF
  have ivl3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have hn0 : (env "A" * env "b") + (((-1) * env "a") * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R,
        ivl3] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r33Nondeg])
  have hn0v : (env "A" * env "b") + (-env "a" * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R,
        ivl3] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r33Nondeg])
  have hn1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R,
        ivl3] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4531r33Nondeg])
  have hn1v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R,
        ivl3] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4531r33Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int 0)) (by simp [rubi4531r33Nondeg])
  have hn3_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  have hn3_2 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4531r33Nondeg, Defined, eval, Interp.real, hkm, ivl3, Fn.csc] at h
  have hb2 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4531r33Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4531r33Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4531r33Nondeg, Defined, eval, Interp.real, hkm, ivl3, Fn.csc] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4531r33Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emm1, iv2R, Fn.csc] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4531r33Nondeg, Defined, eval, recEnv, Interp.real, emm1, ivm1R, iv2R,
        Fn.csc] at h hn0 hn1 hn3_0 hn3_1 hn3_2 ⊢
    try tauto
  · simp only [rubi4531r33Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1)) *
        (((((env "a" * env "b") * ((env "A" * env "b") + (((-1) * env "a") * env "B"))) *
        (env "m" + 1)) +
        ((((-1) * ((env "A" * env "b") + (((-1) * env "a") * env "B"))) *
        ((env "a") ^ 2 + ((env "b") ^ 2 * (env "m" + 1)))) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹)) +
        ((((env "b" * env "B") * (env "m" + 1)) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))) *
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emm1, iv2R, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4531r33Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4531r33Nondeg.result) =
            fun w => ((((((-1) * (env "a") ^ 2) *
            ((env "A" * env "b") + (((-1) * env "a") * env "B"))) *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m + 1)) *
            (((((env "b") ^ 2 * env "f") * (env "m" + 1)) *
            ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹) +
            (1 * ((((env "b") ^ 2 * (env "m" + 1)) *
            ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4531r33Nondeg, eval, recEnv, Interp.real, emm1, ivm1R, iv2R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4531r33Nondeg.body =
        (((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 3 *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        (env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) := by
      simp [rubi4531r33Nondeg, eval, Interp.real, hkm, ivl3, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hBm0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((((-1) * (env "a") ^ 2) *
        ((env "A" * env "b") +
        (((-1) * env "a") *
        env "B"))))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdzm (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t ((((((env "b") ^ 2 * env "f") * (env "m" + 1)) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply,

      add_sub_cancel_right]
    have hn3_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb2 (by omega)
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
      simp only [e0m, e1m]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = Pm
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "A"*env "a"^4*env "b"*env "f"*Pm*S^3 +
          env "A"*env "a"^3*env "b"^2*env "f"*Pm*S^2*((m : ℤ) : ℝ) +
          3*env "A"*env "a"^3*env "b"^2*env "f"*Pm*S^2 +
          env "A"*env "a"^2*env "b"^3*env "f"*Pm*S*((m : ℤ) : ℝ) +
          2*env "A"*env "a"^2*env "b"^3*env "f"*Pm*S - env "B"*env "a"^5*env "f"*Pm*S^3 -
          env "B"*env "a"^4*env "b"*env "f"*Pm*S^2*((m : ℤ) : ℝ) -
          3*env "B"*env "a"^4*env "b"*env "f"*Pm*S^2 -
          env "B"*env "a"^3*env "b"^2*env "f"*Pm*S*((m : ℤ) : ℝ) -
          2*env "B"*env "a"^3*env "b"^2*env "f"*Pm*S) * hP

/-! ## rubi1216r22Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi1216r22Nondeg_real : rubi1216r22Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1216r22Nondeg.conditions rubi1216r22Nondeg.body
    rubi1216r22Nondeg.result rubi1216r22Nondeg.integrals
  intro env hc t hF
  have ivl4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have hn0 : (env "b") ^ 2 + (((-4) * env "a") * env "c") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R,
        ivl4] using hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1216r22Nondeg])
  have hn1 : (env "e") ^ 2 + (((-4) * env "d") * env "f") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R,
        ivl4] using hc (.ne (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "d")) (.var "f"))) (.int 0)) (by simp [rubi1216r22Nondeg])
  have hn3 : (env "p" + env "q") + 1 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R,
        ivl4] using hc (.ne (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)) (.int 0)) (by simp [rubi1216r22Nondeg])
  have hc4 :=
      hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))) (.int 0)) (by simp [rubi1216r22Nondeg])
  have hn4_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_2 : (env "p" + env "q") + 1 ≠ 0 := by
    have h := hc4
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r22Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  rcases hkk : intValue? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r22Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h
  have hb2 : 0 < m := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi1216r22Nondeg])
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "p" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "p" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "p" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "p" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "q" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "q" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "q" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "q" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1216r22Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)) ≠ 0) ∧
          (k < 0 → ((env "d" + (env "e" * w)) + (env "f" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1216r22Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1216r22Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkk, emmm1, iv2R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1216r22Nondeg, Defined, eval, recEnv, Interp.real, hkm, emk1, ivm1R,
        iv2R] at h hn0 hn1 hn3 hn4_1 hn4_2 ⊢
    try tauto
  · simp only [rubi1216r22Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m -
        1) * (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k)) *
        (((((env "h" * env "p") * ((env "b" * env "d") + (((-1) * env "a") * env "e"))) +
        ((env "a" * ((env "h" * env "e") + (((-2) * env "g") * env "f"))) *
        ((env "p" + env "q") + 1))) +
        (((((2 * env "h") * env "p") * ((env "c" * env "d") + (((-1) * env "a") * env "f"))) +
        ((env "b" * ((env "h" * env "e") + (((-2) * env "g") * env "f"))) *
        ((env "p" + env "q") + 1))) * t)) +
        ((((env "h" * env "p") * ((env "c" * env "e") + (((-1) * env "b") * env "f"))) +
        ((env "c" * ((env "h" * env "e") + (((-2) * env "g") * env "f"))) *
        ((env "p" + env "q") + 1))) * (t) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkk, emmm1, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1216r22Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1216r22Nondeg.result) =
            fun w => (((env "h" * (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2))) ^ (m)) *
            (((env "d" + (env "e" * w)) + (env "f" * (w) ^ 2))) ^ (k + 1)) *
            (((2 * env "f") * ((env "p" + env "q") + 1)))⁻¹) +
            ((-1) * (((2 * env "f") * ((env "p" + env "q") + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1216r22Nondeg, eval, recEnv, Interp.real, hkm, emk1, ivm1R, iv2R,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1216r22Nondeg.body =
        ((((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m) *
        (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k)) * (env "g" + (env "h" * t)) := by
      simp [rubi1216r22Nondeg, eval, Interp.real, hkm, hkk, iv2R]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        ((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "h")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) (((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "f")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t ((((2 * env "f") * ((env "p" + env "q") + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn3c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn3
    have hn4_2c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn4_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb2 (by omega)
      · subst hm0
        exact absurd hb2 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ m =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 1 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 1) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 2 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 2) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 3 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        generalize (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) = Pm
        have hqm1a : (1 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℝ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℝ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℝ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring
      · have hdmm : ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ m =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 1 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 1) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 2 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 2) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 3 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : ((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ k =
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) *
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ 1 := by
          have := zsplit (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k + 1) =
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) *
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ 2 := by
          have := zsplit (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k + 2) =
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) *
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ 3 := by
          have := zsplit (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) = Pm
        generalize (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) = Pk
        have hqm1a : (1 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℝ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℝ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℝ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring

set_option maxHeartbeats 1000000 in
theorem rubi1216r22Nondeg_complex : rubi1216r22Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1216r22Nondeg.conditions rubi1216r22Nondeg.body
    rubi1216r22Nondeg.result rubi1216r22Nondeg.integrals
  intro env hc t hF
  have ivl4 : intValue? (4 : ℂ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have hn0 : (env "b") ^ 2 + (((-4) * env "a") * env "c") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C,
        ivl4] using hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1216r22Nondeg])
  have hn1 : (env "e") ^ 2 + (((-4) * env "d") * env "f") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C,
        ivl4] using hc (.ne (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "d")) (.var "f"))) (.int 0)) (by simp [rubi1216r22Nondeg])
  have hn3 : (env "p" + env "q") + 1 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C,
        ivl4] using hc (.ne (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)) (.int 0)) (by simp [rubi1216r22Nondeg])
  have hc4 :=
      hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))) (.int 0)) (by simp [rubi1216r22Nondeg])
  have hn4_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_2 : (env "p" + env "q") + 1 ≠ 0 := by
    have h := hc4
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r22Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  rcases hkk : intValue? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r22Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h
  have hb2 : 0 < m := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi1216r22Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "p" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "p" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "p" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "p" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "q" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "q" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "q" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "q" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1216r22Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)) ≠ 0) ∧
          (k < 0 → ((env "d" + (env "e" * w)) + (env "f" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1216r22Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1216r22Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkk, emmm1, iv2C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1216r22Nondeg, Defined, eval, recEnv, Interp.complex, hkm, emk1, ivm1C,
        iv2C] at h hn0 hn1 hn3 hn4_1 hn4_2 ⊢
    try tauto
  · simp only [rubi1216r22Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m -
        1) * (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k)) *
        (((((env "h" * env "p") * ((env "b" * env "d") + (((-1) * env "a") * env "e"))) +
        ((env "a" * ((env "h" * env "e") + (((-2) * env "g") * env "f"))) *
        ((env "p" + env "q") + 1))) +
        (((((2 * env "h") * env "p") * ((env "c" * env "d") + (((-1) * env "a") * env "f"))) +
        ((env "b" * ((env "h" * env "e") + (((-2) * env "g") * env "f"))) *
        ((env "p" + env "q") + 1))) * t)) +
        ((((env "h" * env "p") * ((env "c" * env "e") + (((-1) * env "b") * env "f"))) +
        ((env "c" * ((env "h" * env "e") + (((-2) * env "g") * env "f"))) *
        ((env "p" + env "q") + 1))) * (t) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkk, emmm1, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1216r22Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1216r22Nondeg.result) =
            fun w => (((env "h" * (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2))) ^ (m)) *
            (((env "d" + (env "e" * w)) + (env "f" * (w) ^ 2))) ^ (k + 1)) *
            (((2 * env "f") * ((env "p" + env "q") + 1)))⁻¹) +
            ((-1) * (((2 * env "f") * ((env "p" + env "q") + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1216r22Nondeg, eval, recEnv, Interp.complex, hkm, emk1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1216r22Nondeg.body =
        ((((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m) *
        (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k)) * (env "g" + (env "h" * t)) := by
      simp [rubi1216r22Nondeg, eval, Interp.complex, hkm, hkk, iv2C]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        ((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "h")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) (((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "f")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t ((((2 * env "f") * ((env "p" + env "q") + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn3c : (((m : ℤ) : ℂ) + ((k : ℤ) : ℂ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn3
    have hn4_2c : (((m : ℤ) : ℂ) + ((k : ℤ) : ℂ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn4_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb2 (by omega)
      · subst hm0
        exact absurd hb2 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ m =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 1 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 1) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 2 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 2) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 3 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        generalize (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) = Pm
        have hqm1a : (1 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℂ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℂ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℂ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring
      · have hdmm : ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ m =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 1 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 1) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 2 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 2) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 3 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : ((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ k =
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) *
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ 1 := by
          have := zsplit (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k + 1) =
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) *
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ 2 := by
          have := zsplit (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k + 2) =
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) *
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ 3 := by
          have := zsplit (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) = Pm
        generalize (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) = Pk
        have hqm1a : (1 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℂ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℂ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℂ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring

/-! ## rubi1216r23Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi1216r23Nondeg_real : rubi1216r23Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1216r23Nondeg.conditions rubi1216r23Nondeg.body
    rubi1216r23Nondeg.result rubi1216r23Nondeg.integrals
  intro env hc t hF
  have ivl4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have hn0 : (env "e") ^ 2 + (((-4) * env "d") * env "f") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R,
        ivl4] using hc (.ne (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "d")) (.var "f"))) (.int 0)) (by simp [rubi1216r23Nondeg])
  have hn2 : (env "p" + env "q") + 1 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R,
        ivl4] using hc (.ne (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)) (.int 0)) (by simp [rubi1216r23Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))) (.int 0)) (by simp [rubi1216r23Nondeg])
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : (env "p" + env "q") + 1 ≠ 0 := by
    have h := hc3
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r23Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  rcases hkk : intValue? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r23Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h
  have hb1 : 0 < m := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi1216r23Nondeg])
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "p" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "p" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "p" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "p" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "q" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "q" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "q" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "q" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1216r23Nondeg.body →
      (m < 0 → (env "a" + (env "c" * (w) ^ 2)) ≠ 0) ∧
          (k < 0 → ((env "d" + (env "e" * w)) + (env "f" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1216r23Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1216r23Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkk, emmm1, iv2R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1216r23Nondeg, Defined, eval, recEnv, Interp.real, hkm, emk1, ivm1R,
        iv2R] at h hn0 hn2 hn3_1 hn3_2 ⊢
    try tauto
  · simp only [rubi1216r23Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) *
        (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k)) *
        ((((((env "a" * env "h") * env "e") * env "p") +
        ((((-1) * env "a") * ((env "h" * env "e") + (((-2) * env "g") * env "f"))) *
        ((env "p" + env "q") + 1))) +
        (((((-2) * env "h") * env "p") * ((env "c" * env "d") + (((-1) * env "a") * env "f"))) *
        t)) + (((-1) *
        ((((env "h" * env "c") * env "e") * env "p") +
        ((env "c" * ((env "h" * env "e") + (((-2) * env "g") * env "f"))) *
        ((env "p" + env "q") + 1)))) * (t) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkk, emmm1, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1216r23Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1216r23Nondeg.result) =
            fun w => (((env "h" * ((env "a" + (env "c" * (w) ^ 2))) ^ (m)) *
            (((env "d" + (env "e" * w)) + (env "f" * (w) ^ 2))) ^ (k + 1)) *
            (((2 * env "f") * ((env "p" + env "q") + 1)))⁻¹) +
            (1 * (((2 * env "f") * ((env "p" + env "q") + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1216r23Nondeg, eval, recEnv, Interp.real, hkm, emk1, ivm1R, iv2R,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1216r23Nondeg.body =
        (((env "a" + (env "c" * (t) ^ 2))) ^ (m) *
        (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k)) * (env "g" + (env "h" * t)) := by
      simp [rubi1216r23Nondeg, eval, Interp.real, hkm, hkk, iv2R]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        ((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "h")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) (((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "f")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t ((((2 * env "f") * ((env "p" + env "q") + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn2c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn2
    have hn3_2c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb1 (by omega)
      · subst hm0
        exact absurd hb1 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "c" * (t) ^ 2))) ^ m =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 1 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 1) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 2 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 2) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 3 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        generalize ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) = Pm
        have hqm1a : (1 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℝ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℝ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℝ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring
      · have hdmm : (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "c" * (t) ^ 2))) ^ m =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 1 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 1) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 2 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 2) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 3 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : ((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ k =
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) *
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ 1 := by
          have := zsplit (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k + 1) =
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) *
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ 2 := by
          have := zsplit (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k + 2) =
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) *
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ 3 := by
          have := zsplit (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) = Pm
        generalize (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) = Pk
        have hqm1a : (1 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℝ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℝ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℝ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring

set_option maxHeartbeats 1000000 in
theorem rubi1216r23Nondeg_complex : rubi1216r23Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1216r23Nondeg.conditions rubi1216r23Nondeg.body
    rubi1216r23Nondeg.result rubi1216r23Nondeg.integrals
  intro env hc t hF
  have ivl4 : intValue? (4 : ℂ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have hn0 : (env "e") ^ 2 + (((-4) * env "d") * env "f") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C,
        ivl4] using hc (.ne (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "d")) (.var "f"))) (.int 0)) (by simp [rubi1216r23Nondeg])
  have hn2 : (env "p" + env "q") + 1 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C,
        ivl4] using hc (.ne (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)) (.int 0)) (by simp [rubi1216r23Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))) (.int 0)) (by simp [rubi1216r23Nondeg])
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : (env "p" + env "q") + 1 ≠ 0 := by
    have h := hc3
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r23Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  rcases hkk : intValue? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r23Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h
  have hb1 : 0 < m := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi1216r23Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "p" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "p" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "p" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "p" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "q" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "q" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "q" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "q" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1216r23Nondeg.body →
      (m < 0 → (env "a" + (env "c" * (w) ^ 2)) ≠ 0) ∧
          (k < 0 → ((env "d" + (env "e" * w)) + (env "f" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1216r23Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1216r23Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkk, emmm1, iv2C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1216r23Nondeg, Defined, eval, recEnv, Interp.complex, hkm, emk1, ivm1C,
        iv2C] at h hn0 hn2 hn3_1 hn3_2 ⊢
    try tauto
  · simp only [rubi1216r23Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) *
        (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k)) *
        ((((((env "a" * env "h") * env "e") * env "p") +
        ((((-1) * env "a") * ((env "h" * env "e") + (((-2) * env "g") * env "f"))) *
        ((env "p" + env "q") + 1))) +
        (((((-2) * env "h") * env "p") * ((env "c" * env "d") + (((-1) * env "a") * env "f"))) *
        t)) + (((-1) *
        ((((env "h" * env "c") * env "e") * env "p") +
        ((env "c" * ((env "h" * env "e") + (((-2) * env "g") * env "f"))) *
        ((env "p" + env "q") + 1)))) * (t) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkk, emmm1, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1216r23Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1216r23Nondeg.result) =
            fun w => (((env "h" * ((env "a" + (env "c" * (w) ^ 2))) ^ (m)) *
            (((env "d" + (env "e" * w)) + (env "f" * (w) ^ 2))) ^ (k + 1)) *
            (((2 * env "f") * ((env "p" + env "q") + 1)))⁻¹) +
            (1 * (((2 * env "f") * ((env "p" + env "q") + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1216r23Nondeg, eval, recEnv, Interp.complex, hkm, emk1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1216r23Nondeg.body =
        (((env "a" + (env "c" * (t) ^ 2))) ^ (m) *
        (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k)) * (env "g" + (env "h" * t)) := by
      simp [rubi1216r23Nondeg, eval, Interp.complex, hkm, hkk, iv2C]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        ((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "h")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) (((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "f")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t ((((2 * env "f") * ((env "p" + env "q") + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn2c : (((m : ℤ) : ℂ) + ((k : ℤ) : ℂ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn2
    have hn3_2c : (((m : ℤ) : ℂ) + ((k : ℤ) : ℂ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb1 (by omega)
      · subst hm0
        exact absurd hb1 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "c" * (t) ^ 2))) ^ m =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 1 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 1) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 2 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 2) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 3 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        generalize ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) = Pm
        have hqm1a : (1 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℂ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℂ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℂ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring
      · have hdmm : (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "c" * (t) ^ 2))) ^ m =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 1 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 1) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 2 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 2) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 3 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : ((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ k =
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) *
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ 1 := by
          have := zsplit (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k + 1) =
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) *
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ 2 := by
          have := zsplit (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k + 2) =
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) *
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ 3 := by
          have := zsplit (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) = Pm
        generalize (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) = Pk
        have hqm1a : (1 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℂ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℂ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℂ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring

/-! ## rubi1216r24Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi1216r24Nondeg_real : rubi1216r24Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1216r24Nondeg.conditions rubi1216r24Nondeg.body
    rubi1216r24Nondeg.result rubi1216r24Nondeg.integrals
  intro env hc t hF
  have ivln2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivl4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have hn0 : (env "b") ^ 2 + (((-4) * env "a") * env "c") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, ivln2,
        ivl4] using hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1216r24Nondeg])
  have hn2 : (env "p" + env "q") + 1 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, ivln2,
        ivl4] using hc (.ne (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)) (.int 0)) (by simp [rubi1216r24Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))) (.int 0)) (by simp [rubi1216r24Nondeg])
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : (env "p" + env "q") + 1 ≠ 0 := by
    have h := hc3
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r24Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  rcases hkk : intValue? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r24Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h
  have hb1 : 0 < m := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi1216r24Nondeg])
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "p" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "p" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "p" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "p" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "q" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "q" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "q" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "q" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1216r24Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)) ≠ 0) ∧
          (k < 0 → (env "d" + (env "f" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1216r24Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1216r24Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkk, emmm1, iv2R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1216r24Nondeg, Defined, eval, recEnv, Interp.real, hkm, emk1, ivm1R,
        iv2R] at h hn0 hn2 hn3_1 hn3_2 ⊢
    try tauto
  · simp only [rubi1216r24Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m -
        1) * ((env "d" + (env "f" * (t) ^ 2))) ^ (k)) *
        ((((((env "h" * env "p") * env "b") * env "d") +
        ((((env "a" * (-2)) * env "g") * env "f") * ((env "p" + env "q") + 1))) +
        (((((2 * env "h") * env "p") * ((env "c" * env "d") + (((-1) * env "a") * env "f"))) +
        ((((env "b" * (-2)) * env "g") * env "f") * ((env "p" + env "q") + 1))) * t)) +
        ((((((env "h" * env "p") * (-1)) * env "b") * env "f") +
        ((((env "c" * (-2)) * env "g") * env "f") * ((env "p" + env "q") + 1))) * (t) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkk, emmm1, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1216r24Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1216r24Nondeg.result) =
            fun w => (((env "h" * (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2))) ^ (m)) *
            ((env "d" + (env "f" * (w) ^ 2))) ^ (k + 1)) *
            (((2 * env "f") * ((env "p" + env "q") + 1)))⁻¹) +
            ((-1) * (((2 * env "f") * ((env "p" + env "q") + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1216r24Nondeg, eval, recEnv, Interp.real, hkm, emk1, ivm1R, iv2R,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1216r24Nondeg.body =
        ((((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m) *
        ((env "d" + (env "f" * (t) ^ 2))) ^ (k)) * (env "g" + (env "h" * t)) := by
      simp [rubi1216r24Nondeg, eval, Interp.real, hkm, hkk, iv2R]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) → (env "d" + (env "f" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "h")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "f")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t ((((2 * env "f") * ((env "p" + env "q") + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn2c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn2
    have hn3_2c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb1 (by omega)
      · subst hm0
        exact absurd hb1 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ m =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 1 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 1) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 2 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 2) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 3 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        generalize (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) = Pm
        have hqm1a : (1 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℝ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℝ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℝ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring
      · have hdmm : ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ m =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 1 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 1) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 2 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 2) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 3 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : (env "d" + (env "f" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "d" + (env "f" * (t) ^ 2))) ^ k =
            ((env "d" + (env "f" * (t) ^ 2))) ^ (k - 1) * ((env "d" + (env "f" * (t) ^ 2))) ^ 1 :=
            by
          have := zsplit ((env "d" + (env "f" * (t) ^ 2))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "d" + (env "f" * (t) ^ 2))) ^ (k + 1) =
            ((env "d" + (env "f" * (t) ^ 2))) ^ (k - 1) * ((env "d" + (env "f" * (t) ^ 2))) ^ 2 :=
            by
          have := zsplit ((env "d" + (env "f" * (t) ^ 2))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "d" + (env "f" * (t) ^ 2))) ^ (k + 2) =
            ((env "d" + (env "f" * (t) ^ 2))) ^ (k - 1) * ((env "d" + (env "f" * (t) ^ 2))) ^ 3 :=
            by
          have := zsplit ((env "d" + (env "f" * (t) ^ 2))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) = Pm
        generalize ((env "d" + (env "f" * (t) ^ 2))) ^ (k - 1) = Pk
        have hqm1a : (1 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℝ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℝ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℝ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring

set_option maxHeartbeats 1000000 in
theorem rubi1216r24Nondeg_complex : rubi1216r24Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1216r24Nondeg.conditions rubi1216r24Nondeg.body
    rubi1216r24Nondeg.result rubi1216r24Nondeg.integrals
  intro env hc t hF
  have ivln2 : intValue? (-2 : ℂ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivl4 : intValue? (4 : ℂ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have hn0 : (env "b") ^ 2 + (((-4) * env "a") * env "c") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, ivln2,
        ivl4] using hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1216r24Nondeg])
  have hn2 : (env "p" + env "q") + 1 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, ivln2,
        ivl4] using hc (.ne (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)) (.int 0)) (by simp [rubi1216r24Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))) (.int 0)) (by simp [rubi1216r24Nondeg])
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : (env "p" + env "q") + 1 ≠ 0 := by
    have h := hc3
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r24Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  rcases hkk : intValue? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r24Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h
  have hb1 : 0 < m := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi1216r24Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "p" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "p" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "p" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "p" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "q" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "q" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "q" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "q" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1216r24Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)) ≠ 0) ∧
          (k < 0 → (env "d" + (env "f" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1216r24Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1216r24Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkk, emmm1, iv2C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1216r24Nondeg, Defined, eval, recEnv, Interp.complex, hkm, emk1, ivm1C,
        iv2C] at h hn0 hn2 hn3_1 hn3_2 ⊢
    try tauto
  · simp only [rubi1216r24Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m -
        1) * ((env "d" + (env "f" * (t) ^ 2))) ^ (k)) *
        ((((((env "h" * env "p") * env "b") * env "d") +
        ((((env "a" * (-2)) * env "g") * env "f") * ((env "p" + env "q") + 1))) +
        (((((2 * env "h") * env "p") * ((env "c" * env "d") + (((-1) * env "a") * env "f"))) +
        ((((env "b" * (-2)) * env "g") * env "f") * ((env "p" + env "q") + 1))) * t)) +
        ((((((env "h" * env "p") * (-1)) * env "b") * env "f") +
        ((((env "c" * (-2)) * env "g") * env "f") * ((env "p" + env "q") + 1))) * (t) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkk, emmm1, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1216r24Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1216r24Nondeg.result) =
            fun w => (((env "h" * (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2))) ^ (m)) *
            ((env "d" + (env "f" * (w) ^ 2))) ^ (k + 1)) *
            (((2 * env "f") * ((env "p" + env "q") + 1)))⁻¹) +
            ((-1) * (((2 * env "f") * ((env "p" + env "q") + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1216r24Nondeg, eval, recEnv, Interp.complex, hkm, emk1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1216r24Nondeg.body =
        ((((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m) *
        ((env "d" + (env "f" * (t) ^ 2))) ^ (k)) * (env "g" + (env "h" * t)) := by
      simp [rubi1216r24Nondeg, eval, Interp.complex, hkm, hkk, iv2C]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) → (env "d" + (env "f" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "h")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "f")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t ((((2 * env "f") * ((env "p" + env "q") + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn2c : (((m : ℤ) : ℂ) + ((k : ℤ) : ℂ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn2
    have hn3_2c : (((m : ℤ) : ℂ) + ((k : ℤ) : ℂ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb1 (by omega)
      · subst hm0
        exact absurd hb1 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ m =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 1 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 1) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 2 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 2) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 3 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        generalize (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) = Pm
        have hqm1a : (1 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℂ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℂ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℂ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring
      · have hdmm : ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ m =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 1 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 1) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 2 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 2) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 3 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : (env "d" + (env "f" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "d" + (env "f" * (t) ^ 2))) ^ k =
            ((env "d" + (env "f" * (t) ^ 2))) ^ (k - 1) * ((env "d" + (env "f" * (t) ^ 2))) ^ 1 :=
            by
          have := zsplit ((env "d" + (env "f" * (t) ^ 2))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "d" + (env "f" * (t) ^ 2))) ^ (k + 1) =
            ((env "d" + (env "f" * (t) ^ 2))) ^ (k - 1) * ((env "d" + (env "f" * (t) ^ 2))) ^ 2 :=
            by
          have := zsplit ((env "d" + (env "f" * (t) ^ 2))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "d" + (env "f" * (t) ^ 2))) ^ (k + 2) =
            ((env "d" + (env "f" * (t) ^ 2))) ^ (k - 1) * ((env "d" + (env "f" * (t) ^ 2))) ^ 3 :=
            by
          have := zsplit ((env "d" + (env "f" * (t) ^ 2))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) = Pm
        generalize ((env "d" + (env "f" * (t) ^ 2))) ^ (k - 1) = Pk
        have hqm1a : (1 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℂ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℂ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℂ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring

/-! ## rubi1224r31Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi1224r31Nondeg_real : rubi1224r31Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1224r31Nondeg.conditions rubi1224r31Nondeg.body
    rubi1224r31Nondeg.result rubi1224r31Nondeg.integrals
  intro env hc t hF
  have ivl3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have ivl4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have hn0 : (env "b") ^ 2 + (((-4) * env "a") * env "c") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, ivl3,
        ivl4] using hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1224r31Nondeg])
  have hn2 : (env "m" + (4 * env "p")) + 3 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, ivl3,
        ivl4] using hc (.ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 4) (.var "p"))) (.int 3)) (.int 0)) (by simp [rubi1224r31Nondeg])
  have hc5 :=
      hc (.ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 4) (.var "p"))) (.int 3))) (.int 0)) (by simp [rubi1224r31Nondeg])
  have hn5_0 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  have hn5_1 : (env "m" + (4 * env "p")) + 3 ≠ 0 := by
    have h := hc5
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r31Nondeg, Defined, eval, Interp.real, hkm, iv2R, ivl4] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r31Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, ivl4] at h
  have hb1 : 1 < m := by
    have h := hc (.gt (.var "m") (.int 1)) (by simp [rubi1224r31Nondeg])
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "p" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1224r31Nondeg.body →
      (m < 0 → (env "f" * w) ≠ 0) ∧
          (k < 0 → ((env "a" + (env "b" * (w) ^ 2)) + (env "c" * (w) ^ 4)) ≠ 0) := by
    intro w h
    simp [rubi1224r31Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, ivl4] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1224r31Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkk, emmm2, iv2R, ivl4] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1224r31Nondeg, Defined, eval, recEnv, Interp.real, emmm1, emk1, ivm1R, iv2R,
        ivl4] at h hn0 hn2 hn5_0 hn5_1 ⊢
    try tauto
  · simp only [rubi1224r31Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "f" * t)) ^ (m - 2) *
        (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k)) *
        (((env "a" * env "e") * (env "m" + (-1))) +
        ((((env "b" * env "e") * ((env "m" + (2 * env "p")) + 1)) +
        ((((-1) * env "c") * env "d") * ((env "m" + (4 * env "p")) + 3))) * (t) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkk, emmm2, iv2R, ivl4, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1224r31Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1224r31Nondeg.result) =
            fun w => ((((env "e" * env "f") * ((env "f" * w)) ^ (m - 1)) *
            (((env "a" + (env "b" * (w) ^ 2)) + (env "c" * (w) ^ 4))) ^ (k + 1)) *
            ((env "c" * ((env "m" + (4 * env "p")) + 3)))⁻¹) +
            (((-1) * (env "f") ^ 2) * ((env "c" * ((env "m" + (4 * env "p")) + 3)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi1224r31Nondeg, eval, recEnv, Interp.real, emmm1, emk1, ivm1R, iv2R, ivl4,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1224r31Nondeg.body =
        (((env "f" * t)) ^ (m) * (env "d" + (env "e" * (t) ^ 2))) *
        (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k) := by
      simp [rubi1224r31Nondeg, eval, Interp.real, hkm, hkk, iv2R, ivl4]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "f" * t) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        ((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((env "e" *
        env "f"))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m -
        1) _ (hdzm (m -
        1) (by omega))) ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((hasDerivAt_id' t).pow 2))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 4))))).mul (hasDerivAt_const t (((env "c" * ((env "m" + (4 * env "p")) + 3)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right,
        show m - 1 - 1 = m - 2 by ring]
    have hn2c : (((m : ℤ) : ℝ) + (4 * ((k : ℤ) : ℝ))) + 3 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn2
    have hn5_1c : (((m : ℤ) : ℝ) + (4 * ((k : ℤ) : ℝ))) + 3 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn5_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb1 (by omega)
      · subst hm0
        exact absurd hb1 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "f" * t) ≠ 0 ∨ 0 ≤ m - 2 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have el1m : ((env "f" * t)) ^ (m - 1) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 1 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 1 hdmm
          rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
        have el2m : ((env "f" * t)) ^ (m) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 2 := by
          have := zsplit ((env "f" * t)) (m - 2) 2 hdmm
          rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
        have el3m : ((env "f" * t)) ^ (m + 1) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 3 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 3 hdmm
          rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have el4m : ((env "f" * t)) ^ (m + 2) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 4 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 4 hdmm
          rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [el1m, el2m]
        generalize ((env "f" * t)) ^ (m - 2) = Pm
        have hqm1a : (1 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℝ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℝ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℝ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring
      · have hdmm : (env "f" * t) ≠ 0 ∨ 0 ≤ m - 2 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have el1m : ((env "f" * t)) ^ (m - 1) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 1 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 1 hdmm
          rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
        have el2m : ((env "f" * t)) ^ (m) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 2 := by
          have := zsplit ((env "f" * t)) (m - 2) 2 hdmm
          rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
        have el3m : ((env "f" * t)) ^ (m + 1) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 3 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 3 hdmm
          rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have el4m : ((env "f" * t)) ^ (m + 2) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 4 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 4 hdmm
          rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [el1m, el2m]
        have hdmk : ((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ k =
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) *
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ 1 := by
          have := zsplit (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k + 1) =
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) *
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ 2 := by
          have := zsplit (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k + 2) =
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) *
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ 3 := by
          have := zsplit (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "f" * t)) ^ (m - 2) = Pm
        generalize (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) = Pk
        have hdn0 : ((m : ℤ) : ℝ) + ((k : ℤ) : ℝ) * 4 + 3 ≠ 0 :=
            fun h0 => hn2c (by linear_combination (1) * h0)
        have hqm1a : (1 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℝ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℝ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℝ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring

set_option maxHeartbeats 1000000 in
theorem rubi1224r31Nondeg_complex : rubi1224r31Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1224r31Nondeg.conditions rubi1224r31Nondeg.body
    rubi1224r31Nondeg.result rubi1224r31Nondeg.integrals
  intro env hc t hF
  have ivl3 : intValue? (3 : ℂ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have ivl4 : intValue? (4 : ℂ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have hn0 : (env "b") ^ 2 + (((-4) * env "a") * env "c") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, ivl3,
        ivl4] using hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1224r31Nondeg])
  have hn2 : (env "m" + (4 * env "p")) + 3 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, ivl3,
        ivl4] using hc (.ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 4) (.var "p"))) (.int 3)) (.int 0)) (by simp [rubi1224r31Nondeg])
  have hc5 :=
      hc (.ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 4) (.var "p"))) (.int 3))) (.int 0)) (by simp [rubi1224r31Nondeg])
  have hn5_0 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  have hn5_1 : (env "m" + (4 * env "p")) + 3 ≠ 0 := by
    have h := hc5
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r31Nondeg, Defined, eval, Interp.complex, hkm, iv2C, ivl4] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r31Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C, ivl4] at h
  have hb1 : 1 < m := by
    have h := hc (.gt (.var "m") (.int 1)) (by simp [rubi1224r31Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "p" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1224r31Nondeg.body →
      (m < 0 → (env "f" * w) ≠ 0) ∧
          (k < 0 → ((env "a" + (env "b" * (w) ^ 2)) + (env "c" * (w) ^ 4)) ≠ 0) := by
    intro w h
    simp [rubi1224r31Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C, ivl4] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1224r31Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkk, emmm2, iv2C, ivl4] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1224r31Nondeg, Defined, eval, recEnv, Interp.complex, emmm1, emk1, ivm1C, iv2C,
        ivl4] at h hn0 hn2 hn5_0 hn5_1 ⊢
    try tauto
  · simp only [rubi1224r31Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "f" * t)) ^ (m - 2) *
        (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k)) *
        (((env "a" * env "e") * (env "m" + (-1))) +
        ((((env "b" * env "e") * ((env "m" + (2 * env "p")) + 1)) +
        ((((-1) * env "c") * env "d") * ((env "m" + (4 * env "p")) + 3))) * (t) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkk, emmm2, iv2C, ivl4, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1224r31Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1224r31Nondeg.result) =
            fun w => ((((env "e" * env "f") * ((env "f" * w)) ^ (m - 1)) *
            (((env "a" + (env "b" * (w) ^ 2)) + (env "c" * (w) ^ 4))) ^ (k + 1)) *
            ((env "c" * ((env "m" + (4 * env "p")) + 3)))⁻¹) +
            (((-1) * (env "f") ^ 2) * ((env "c" * ((env "m" + (4 * env "p")) + 3)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi1224r31Nondeg, eval, recEnv, Interp.complex, emmm1, emk1, ivm1C, iv2C, ivl4,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1224r31Nondeg.body =
        (((env "f" * t)) ^ (m) * (env "d" + (env "e" * (t) ^ 2))) *
        (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k) := by
      simp [rubi1224r31Nondeg, eval, Interp.complex, hkm, hkk, iv2C, ivl4]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "f" * t) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        ((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((env "e" *
        env "f"))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m -
        1) _ (hdzm (m -
        1) (by omega))) ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((hasDerivAt_id' t).pow 2))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 4))))).mul (hasDerivAt_const t (((env "c" * ((env "m" + (4 * env "p")) + 3)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right,
        show m - 1 - 1 = m - 2 by ring]
    have hn2c : (((m : ℤ) : ℂ) + (4 * ((k : ℤ) : ℂ))) + 3 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn2
    have hn5_1c : (((m : ℤ) : ℂ) + (4 * ((k : ℤ) : ℂ))) + 3 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn5_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb1 (by omega)
      · subst hm0
        exact absurd hb1 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "f" * t) ≠ 0 ∨ 0 ≤ m - 2 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have el1m : ((env "f" * t)) ^ (m - 1) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 1 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 1 hdmm
          rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
        have el2m : ((env "f" * t)) ^ (m) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 2 := by
          have := zsplit ((env "f" * t)) (m - 2) 2 hdmm
          rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
        have el3m : ((env "f" * t)) ^ (m + 1) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 3 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 3 hdmm
          rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have el4m : ((env "f" * t)) ^ (m + 2) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 4 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 4 hdmm
          rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [el1m, el2m]
        generalize ((env "f" * t)) ^ (m - 2) = Pm
        have hqm1a : (1 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℂ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℂ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℂ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring
      · have hdmm : (env "f" * t) ≠ 0 ∨ 0 ≤ m - 2 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have el1m : ((env "f" * t)) ^ (m - 1) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 1 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 1 hdmm
          rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
        have el2m : ((env "f" * t)) ^ (m) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 2 := by
          have := zsplit ((env "f" * t)) (m - 2) 2 hdmm
          rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
        have el3m : ((env "f" * t)) ^ (m + 1) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 3 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 3 hdmm
          rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have el4m : ((env "f" * t)) ^ (m + 2) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 4 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 4 hdmm
          rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [el1m, el2m]
        have hdmk : ((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ k =
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) *
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ 1 := by
          have := zsplit (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k + 1) =
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) *
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ 2 := by
          have := zsplit (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k + 2) =
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) *
            (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ 3 := by
          have := zsplit (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "f" * t)) ^ (m - 2) = Pm
        generalize (((env "a" + (env "b" * (t) ^ 2)) + (env "c" * (t) ^ 4))) ^ (k - 1) = Pk
        have hdn0 : ((m : ℤ) : ℂ) + ((k : ℤ) : ℂ) * 4 + 3 ≠ 0 :=
            fun h0 => hn2c (by linear_combination (1) * h0)
        have hqm1a : (1 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℂ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℂ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℂ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring

/-! ## rubi1224r32Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi1224r32Nondeg_real : rubi1224r32Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1224r32Nondeg.conditions rubi1224r32Nondeg.body
    rubi1224r32Nondeg.result rubi1224r32Nondeg.integrals
  intro env hc t hF
  have ivl3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have ivl4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have hn1 : (env "m" + (4 * env "p")) + 3 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, ivl3,
        ivl4] using hc (.ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 4) (.var "p"))) (.int 3)) (.int 0)) (by simp [rubi1224r32Nondeg])
  have hc4 :=
      hc (.ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 4) (.var "p"))) (.int 3))) (.int 0)) (by simp [rubi1224r32Nondeg])
  have hn4_0 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_1 : (env "m" + (4 * env "p")) + 3 ≠ 0 := by
    have h := hc4
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r32Nondeg, Defined, eval, Interp.real, hkm, iv2R, ivl4] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r32Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, ivl4] at h
  have hb0 : 1 < m := by
    have h := hc (.gt (.var "m") (.int 1)) (by simp [rubi1224r32Nondeg])
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "p" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1224r32Nondeg.body →
      (m < 0 → (env "f" * w) ≠ 0) ∧ (k < 0 → (env "a" + (env "c" * (w) ^ 4)) ≠ 0) := by
    intro w h
    simp [rubi1224r32Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, ivl4] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1224r32Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkk, emmm2, iv2R, ivl4] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1224r32Nondeg, Defined, eval, recEnv, Interp.real, emmm1, emk1, ivm1R, iv2R,
        ivl4] at h hn1 hn4_0 hn4_1 ⊢
    try tauto
  · simp only [rubi1224r32Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "f" * t)) ^ (m - 2) *
        ((env "a" + (env "c" * (t) ^ 4))) ^ (k)) *
        (((env "a" * env "e") * (env "m" + (-1))) +
        (((((-1) * env "c") * env "d") * ((env "m" + (4 * env "p")) + 3)) * (t) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkk, emmm2, iv2R, ivl4, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1224r32Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1224r32Nondeg.result) =
            fun w => ((((env "e" * env "f") * ((env "f" * w)) ^ (m - 1)) *
            ((env "a" + (env "c" * (w) ^ 4))) ^ (k + 1)) *
            ((env "c" * ((env "m" + (4 * env "p")) + 3)))⁻¹) +
            (((-1) * (env "f") ^ 2) * ((env "c" * ((env "m" + (4 * env "p")) + 3)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi1224r32Nondeg, eval, recEnv, Interp.real, emmm1, emk1, ivm1R, iv2R, ivl4,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1224r32Nondeg.body =
        (((env "f" * t)) ^ (m) * (env "d" + (env "e" * (t) ^ 2))) *
        ((env "a" + (env "c" * (t) ^ 4))) ^ (k) := by
      simp [rubi1224r32Nondeg, eval, Interp.real, hkm, hkk, iv2R, ivl4]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "f" * t) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) → (env "a" + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((env "e" *
        env "f"))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m -
        1) _ (hdzm (m -
        1) (by omega))) ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 4))))).mul (hasDerivAt_const t (((env "c" * ((env "m" + (4 * env "p")) + 3)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right,
        show m - 1 - 1 = m - 2 by ring]
    have hn1c : (((m : ℤ) : ℝ) + (4 * ((k : ℤ) : ℝ))) + 3 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn1
    have hn4_1c : (((m : ℤ) : ℝ) + (4 * ((k : ℤ) : ℝ))) + 3 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn4_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb0 (by omega)
      · subst hm0
        exact absurd hb0 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "f" * t) ≠ 0 ∨ 0 ≤ m - 2 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have el1m : ((env "f" * t)) ^ (m - 1) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 1 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 1 hdmm
          rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
        have el2m : ((env "f" * t)) ^ (m) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 2 := by
          have := zsplit ((env "f" * t)) (m - 2) 2 hdmm
          rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
        have el3m : ((env "f" * t)) ^ (m + 1) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 3 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 3 hdmm
          rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have el4m : ((env "f" * t)) ^ (m + 2) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 4 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 4 hdmm
          rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [el1m, el2m]
        generalize ((env "f" * t)) ^ (m - 2) = Pm
        have hqm1a : (1 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℝ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℝ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℝ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring
      · have hdmm : (env "f" * t) ≠ 0 ∨ 0 ≤ m - 2 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have el1m : ((env "f" * t)) ^ (m - 1) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 1 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 1 hdmm
          rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
        have el2m : ((env "f" * t)) ^ (m) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 2 := by
          have := zsplit ((env "f" * t)) (m - 2) 2 hdmm
          rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
        have el3m : ((env "f" * t)) ^ (m + 1) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 3 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 3 hdmm
          rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have el4m : ((env "f" * t)) ^ (m + 2) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 4 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 4 hdmm
          rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [el1m, el2m]
        have hdmk : (env "a" + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "a" + (env "c" * (t) ^ 4))) ^ k =
            ((env "a" + (env "c" * (t) ^ 4))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 4))) ^ 1 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 4))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "a" + (env "c" * (t) ^ 4))) ^ (k + 1) =
            ((env "a" + (env "c" * (t) ^ 4))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 4))) ^ 2 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 4))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "a" + (env "c" * (t) ^ 4))) ^ (k + 2) =
            ((env "a" + (env "c" * (t) ^ 4))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 4))) ^ 3 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 4))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "f" * t)) ^ (m - 2) = Pm
        generalize ((env "a" + (env "c" * (t) ^ 4))) ^ (k - 1) = Pk
        have hdn0 : ((m : ℤ) : ℝ) + ((k : ℤ) : ℝ) * 4 + 3 ≠ 0 :=
            fun h0 => hn1c (by linear_combination (1) * h0)
        have hqm1a : (1 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℝ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℝ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℝ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring

set_option maxHeartbeats 1000000 in
theorem rubi1224r32Nondeg_complex : rubi1224r32Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1224r32Nondeg.conditions rubi1224r32Nondeg.body
    rubi1224r32Nondeg.result rubi1224r32Nondeg.integrals
  intro env hc t hF
  have ivl3 : intValue? (3 : ℂ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have ivl4 : intValue? (4 : ℂ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have hn1 : (env "m" + (4 * env "p")) + 3 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, ivl3,
        ivl4] using hc (.ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 4) (.var "p"))) (.int 3)) (.int 0)) (by simp [rubi1224r32Nondeg])
  have hc4 :=
      hc (.ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 4) (.var "p"))) (.int 3))) (.int 0)) (by simp [rubi1224r32Nondeg])
  have hn4_0 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_1 : (env "m" + (4 * env "p")) + 3 ≠ 0 := by
    have h := hc4
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r32Nondeg, Defined, eval, Interp.complex, hkm, iv2C, ivl4] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r32Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C, ivl4] at h
  have hb0 : 1 < m := by
    have h := hc (.gt (.var "m") (.int 1)) (by simp [rubi1224r32Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "p" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1224r32Nondeg.body →
      (m < 0 → (env "f" * w) ≠ 0) ∧ (k < 0 → (env "a" + (env "c" * (w) ^ 4)) ≠ 0) := by
    intro w h
    simp [rubi1224r32Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C, ivl4] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1224r32Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkk, emmm2, iv2C, ivl4] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1224r32Nondeg, Defined, eval, recEnv, Interp.complex, emmm1, emk1, ivm1C, iv2C,
        ivl4] at h hn1 hn4_0 hn4_1 ⊢
    try tauto
  · simp only [rubi1224r32Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "f" * t)) ^ (m - 2) *
        ((env "a" + (env "c" * (t) ^ 4))) ^ (k)) *
        (((env "a" * env "e") * (env "m" + (-1))) +
        (((((-1) * env "c") * env "d") * ((env "m" + (4 * env "p")) + 3)) * (t) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkk, emmm2, iv2C, ivl4, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1224r32Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1224r32Nondeg.result) =
            fun w => ((((env "e" * env "f") * ((env "f" * w)) ^ (m - 1)) *
            ((env "a" + (env "c" * (w) ^ 4))) ^ (k + 1)) *
            ((env "c" * ((env "m" + (4 * env "p")) + 3)))⁻¹) +
            (((-1) * (env "f") ^ 2) * ((env "c" * ((env "m" + (4 * env "p")) + 3)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi1224r32Nondeg, eval, recEnv, Interp.complex, emmm1, emk1, ivm1C, iv2C, ivl4,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1224r32Nondeg.body =
        (((env "f" * t)) ^ (m) * (env "d" + (env "e" * (t) ^ 2))) *
        ((env "a" + (env "c" * (t) ^ 4))) ^ (k) := by
      simp [rubi1224r32Nondeg, eval, Interp.complex, hkm, hkk, iv2C, ivl4]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "f" * t) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) → (env "a" + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((env "e" *
        env "f"))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m -
        1) _ (hdzm (m -
        1) (by omega))) ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 4))))).mul (hasDerivAt_const t (((env "c" * ((env "m" + (4 * env "p")) + 3)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right,
        show m - 1 - 1 = m - 2 by ring]
    have hn1c : (((m : ℤ) : ℂ) + (4 * ((k : ℤ) : ℂ))) + 3 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn1
    have hn4_1c : (((m : ℤ) : ℂ) + (4 * ((k : ℤ) : ℂ))) + 3 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn4_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb0 (by omega)
      · subst hm0
        exact absurd hb0 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "f" * t) ≠ 0 ∨ 0 ≤ m - 2 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have el1m : ((env "f" * t)) ^ (m - 1) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 1 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 1 hdmm
          rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
        have el2m : ((env "f" * t)) ^ (m) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 2 := by
          have := zsplit ((env "f" * t)) (m - 2) 2 hdmm
          rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
        have el3m : ((env "f" * t)) ^ (m + 1) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 3 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 3 hdmm
          rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have el4m : ((env "f" * t)) ^ (m + 2) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 4 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 4 hdmm
          rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [el1m, el2m]
        generalize ((env "f" * t)) ^ (m - 2) = Pm
        have hqm1a : (1 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℂ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℂ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℂ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring
      · have hdmm : (env "f" * t) ≠ 0 ∨ 0 ≤ m - 2 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have el1m : ((env "f" * t)) ^ (m - 1) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 1 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 1 hdmm
          rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
        have el2m : ((env "f" * t)) ^ (m) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 2 := by
          have := zsplit ((env "f" * t)) (m - 2) 2 hdmm
          rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
        have el3m : ((env "f" * t)) ^ (m + 1) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 3 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 3 hdmm
          rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have el4m : ((env "f" * t)) ^ (m + 2) = ((env "f" * t)) ^ (m - 2) * ((env "f" * t)) ^ 4 :=
            by
          have := zsplit ((env "f" * t)) (m - 2) 4 hdmm
          rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [el1m, el2m]
        have hdmk : (env "a" + (env "c" * (t) ^ 4)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "a" + (env "c" * (t) ^ 4))) ^ k =
            ((env "a" + (env "c" * (t) ^ 4))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 4))) ^ 1 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 4))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "a" + (env "c" * (t) ^ 4))) ^ (k + 1) =
            ((env "a" + (env "c" * (t) ^ 4))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 4))) ^ 2 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 4))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "a" + (env "c" * (t) ^ 4))) ^ (k + 2) =
            ((env "a" + (env "c" * (t) ^ 4))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 4))) ^ 3 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 4))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "f" * t)) ^ (m - 2) = Pm
        generalize ((env "a" + (env "c" * (t) ^ 4))) ^ (k - 1) = Pk
        have hdn0 : ((m : ℤ) : ℂ) + ((k : ℤ) : ℂ) * 4 + 3 ≠ 0 :=
            fun h0 => hn1c (by linear_combination (1) * h0)
        have hqm1a : (1 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 1 + m ≠ 0 by omega)
        have hqm1b : (((m : ℤ) : ℂ) + 1) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        have hqm2a : (2 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 2 + m ≠ 0 by omega)
        have hqm2b : (((m : ℤ) : ℂ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
        have hqm3a : (3 + ((m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast (show 3 + m ≠ 0 by omega)
        have hqm3b : (((m : ℤ) : ℂ) + 3) ≠ 0 := by exact_mod_cast (show m + 3 ≠ 0 by omega)
        field_simp
        ring

end OSR.IntegrationRec299
