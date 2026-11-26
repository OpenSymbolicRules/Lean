import OSR.IntegrationNum1

/-! # Strengthened variants with two integer exponents: explicit terms plus a residual integral

Proofs of RUBI rules whose result is an explicit term with powers `y^m z^n` plus at most one residual
integral. The derivative of the explicit term is built from the rule expression; the integrand is
recovered with `sin² + cos² = 1` (when trigonometric) and the stated parameter relations, separately
for each exponent equal to `0` or not (`linear_combination` coefficients computed by Gröbner
reduction). Rules with `csc`, `cot` or `arctan` are proved over ℝ only. -/

namespace OSR.IntegrationRec293

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

/-! ## rubi4101r1Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4101r1Nondeg_real : rubi4101r1Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi4101r1Nondeg.conditions rubi4101r1Nondeg.body
    rubi4101r1Nondeg.result
  intro env hc t hF
  have hr0 : (env "m" + env "n") + 2 - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2)) (.int 0)) (by simp [rubi4101r1Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4101r1Nondeg])
  have hn2_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_3 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4101r1Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4101r1Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4101r1Nondeg.body →
      (m < 0 → (env "a" * Real.sin ((env "e" + (env "f" * w)))) ≠ 0) ∧
          (k < 0 → (env "b" * Real.cos ((env "e" + (env "f" * w)))) ≠ 0) := by
    intro w h
    simp [rubi4101r1Nondeg, Defined, eval, Interp.real, hkm, hkk] at h ⊢
    tauto
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4101r1Nondeg, Defined, eval, Interp.real, emm1, emk1,
        ivm1R] at h hn2_0 hn2_1 hn2_2 hn2_3 ⊢
    tauto
  · have hfun : (fun w => eval Interp.real (Function.update env "x" w)
        rubi4101r1Nondeg.result) =
            fun w => ((((env "a" * Real.sin ((env "e" + (env "f" * w))))) ^ (m + 1) *
            ((env "b" * Real.cos ((env "e" + (env "f" * w))))) ^ (k + 1)) *
            ((((env "a" * env "b") * env "f") * (env "m" + 1)))⁻¹) := by
      funext w
      simp [rubi4101r1Nondeg, eval, Interp.real, emm1, emk1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4101r1Nondeg.body =
        ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ (m) *
        ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ (k) := by
      simp [rubi4101r1Nondeg, eval, Interp.real, hkm, hkk]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" * Real.sin ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "b" * Real.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "a")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))))).mul (hasDerivAt_const t (((((env "a" * env "b") * env "f") * (env "m" + 1)))⁻¹))).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, add_sub_cancel_right]
    have hr0c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 2 - (0) = 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hr0
    have hn2_3c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_3
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (1) * hP + (-S^2) * hr0c
      · subst hm0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "b" * Real.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ k =
            ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ 1 := by
          have := zsplit ((env "b" * Real.cos ((env "e" + (env "f" * t))))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ (k + 1) =
            ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ 2 := by
          have := zsplit ((env "b" * Real.cos ((env "e" + (env "f" * t))))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ (k + 2) =
            ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ 3 := by
          have := zsplit ((env "b" * Real.cos ((env "e" + (env "f" * t))))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (C*Pk) * hP + (-C*Pk*S^2) * hr0c
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "a" * Real.sin ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ m =
            ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ (m - 1) *
            ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ 1 := by
          have := zsplit ((env "a" * Real.sin ((env "e" + (env "f" * t))))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ (m + 1) =
            ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ (m - 1) *
            ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ 2 := by
          have := zsplit ((env "a" * Real.sin ((env "e" + (env "f" * t))))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ (m + 2) =
            ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ (m - 1) *
            ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ 3 := by
          have := zsplit ((env "a" * Real.sin ((env "e" + (env "f" * t))))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m]
        generalize ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ (m - 1) = Pm
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (Pm*S*((m : ℤ) : ℝ) + Pm*S) * hP + (-Pm*S^3) * hr0c
      · have hdmm : (env "a" * Real.sin ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ m =
            ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ (m - 1) *
            ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ 1 := by
          have := zsplit ((env "a" * Real.sin ((env "e" + (env "f" * t))))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ (m + 1) =
            ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ (m - 1) *
            ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ 2 := by
          have := zsplit ((env "a" * Real.sin ((env "e" + (env "f" * t))))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ (m + 2) =
            ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ (m - 1) *
            ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ 3 := by
          have := zsplit ((env "a" * Real.sin ((env "e" + (env "f" * t))))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m]
        have hdmk : (env "b" * Real.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ k =
            ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ 1 := by
          have := zsplit ((env "b" * Real.cos ((env "e" + (env "f" * t))))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ (k + 1) =
            ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ 2 := by
          have := zsplit ((env "b" * Real.cos ((env "e" + (env "f" * t))))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ (k + 2) =
            ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ 3 := by
          have := zsplit ((env "b" * Real.cos ((env "e" + (env "f" * t))))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "a" * Real.sin ((env "e" + (env "f" * t))))) ^ (m - 1) = Pm
        generalize ((env "b" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (C*env "a"*env "b"*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) +
            C*env "a"*env "b"*env "f"*Pk*Pm*S) * hP + (-C*env "a"*env "b"*env "f"*Pk*Pm*S^3) * hr0c

set_option maxHeartbeats 1000000 in
theorem rubi4101r1Nondeg_complex : rubi4101r1Nondeg.Holds .complex := by
  show AntiderivHoldsUnder Interp.complex "x" rubi4101r1Nondeg.conditions rubi4101r1Nondeg.body
    rubi4101r1Nondeg.result
  intro env hc t hF
  have hr0 : (env "m" + env "n") + 2 - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2)) (.int 0)) (by simp [rubi4101r1Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4101r1Nondeg])
  have hn2_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_3 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4101r1Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4101r1Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h
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
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4101r1Nondeg.body →
      (m < 0 → (env "a" * Complex.sin ((env "e" + (env "f" * w)))) ≠ 0) ∧
          (k < 0 → (env "b" * Complex.cos ((env "e" + (env "f" * w)))) ≠ 0) := by
    intro w h
    simp [rubi4101r1Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h ⊢
    tauto
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4101r1Nondeg, Defined, eval, Interp.complex, emm1, emk1,
        ivm1C] at h hn2_0 hn2_1 hn2_2 hn2_3 ⊢
    tauto
  · have hfun : (fun w => eval Interp.complex (Function.update env "x" w)
        rubi4101r1Nondeg.result) =
            fun w => ((((env "a" * Complex.sin ((env "e" + (env "f" * w))))) ^ (m + 1) *
            ((env "b" * Complex.cos ((env "e" + (env "f" * w))))) ^ (k + 1)) *
            ((((env "a" * env "b") * env "f") * (env "m" + 1)))⁻¹) := by
      funext w
      simp [rubi4101r1Nondeg, eval, Interp.complex, emm1, emk1, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4101r1Nondeg.body =
        ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m) *
        ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k) := by
      simp [rubi4101r1Nondeg, eval, Interp.complex, hkm, hkk]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" * Complex.sin ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "b" * Complex.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "a")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))))).mul (hasDerivAt_const t (((((env "a" * env "b") * env "f") * (env "m" + 1)))⁻¹))).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, add_sub_cancel_right]
    have hr0c : (((m : ℤ) : ℂ) + ((k : ℤ) : ℂ)) + 2 - (0) = 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hr0
    have hn2_3c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_3
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (1) * hP + (-S^2) * hr0c
      · subst hm0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "b" * Complex.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ k =
            ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ 1 := by
          have := zsplit ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k + 1) =
            ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ 2 := by
          have := zsplit ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k + 2) =
            ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ 3 := by
          have := zsplit ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (C*Pk) * hP + (-C*Pk*S^2) * hr0c
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "a" * Complex.sin ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ m =
            ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m - 1) *
            ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ 1 := by
          have := zsplit ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m + 1) =
            ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m - 1) *
            ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ 2 := by
          have := zsplit ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m + 2) =
            ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m - 1) *
            ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ 3 := by
          have := zsplit ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m]
        generalize ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m - 1) = Pm
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (Pm*S*((m : ℤ) : ℂ) + Pm*S) * hP + (-Pm*S^3) * hr0c
      · have hdmm : (env "a" * Complex.sin ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ m =
            ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m - 1) *
            ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ 1 := by
          have := zsplit ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m + 1) =
            ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m - 1) *
            ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ 2 := by
          have := zsplit ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m + 2) =
            ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m - 1) *
            ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ 3 := by
          have := zsplit ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m]
        have hdmk : (env "b" * Complex.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ k =
            ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ 1 := by
          have := zsplit ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k + 1) =
            ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ 2 := by
          have := zsplit ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k + 2) =
            ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ 3 := by
          have := zsplit ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "a" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m - 1) = Pm
        generalize ((env "b" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (C*env "a"*env "b"*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) +
            C*env "a"*env "b"*env "f"*Pk*Pm*S) * hP + (-C*env "a"*env "b"*env "f"*Pk*Pm*S^3) * hr0c

/-! ## rubi4122r34Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4122r34Nondeg_real : rubi4122r34Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4122r34Nondeg.conditions rubi4122r34Nondeg.body
    rubi4122r34Nondeg.result rubi4122r34Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4122r34Nondeg])
  have hn0v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4122r34Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "g")) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi4122r34Nondeg])
  have hn3_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  have hn3_1 : env "g" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  have hn3_3 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r34Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r34Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hb1 : k < -1 := by
    have h := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi4122r34Nondeg])
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
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4122r34Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "g" * Real.cos ((env "e" + (env "f" * w)))) ≠ 0) := by
    intro w h
    simp [rubi4122r34Nondeg, Defined, eval, Interp.real, hkm, hkk] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r34Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, emk2, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4122r34Nondeg, Defined, eval, recEnv, Interp.real, emm1, emk1, ivm1R,
        iv2R] at h hn0 hn3_0 hn3_1 hn3_3 ⊢
    tauto
  · simp only [rubi4122r34Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k + 2) *
        ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m)) *
        (((env "c" *
        (((env "a") ^ 2 * (env "p" + 2)) + (((-1) * (env "b") ^ 2) * ((env "m" + env "p") + 2)))) +
        (((env "a" * env "b") * env "d") * env "m")) +
        (((env "b" * ((env "a" * env "c") + (((-1) * env "b") * env "d"))) *
        ((env "m" + env "p") + 3)) * Real.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, emk2, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4122r34Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r34Nondeg.result) =
            fun w => (((((env "g" * Real.cos ((env "e" + (env "f" * w))))) ^ (k + 1) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "b" * env "c") + (((-1) * env "a") * env "d")) +
            (((-1) * ((env "a" * env "c") + (((-1) * env "b") * env "d"))) *
            Real.sin ((env "e" + (env "f" * w)))))) *
            ((((env "f" * env "g") * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))) *
            (env "p" + 1)))⁻¹) +
            (1 * ((((env "g") ^ 2 * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))) *
            (env "p" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4122r34Nondeg, eval, recEnv, Interp.real, emm1, emk1, ivm1R, iv2R,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4122r34Nondeg.body =
        (((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k) *
        ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m)) *
        (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) := by
      simp [rubi4122r34Nondeg, eval, Interp.real, hkm, hkk]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "g" * Real.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (k +
        1) _ (hdzk (k +
        1) (by omega))) ((hasDerivAt_const t (env "g")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdzm (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul ((hasDerivAt_const t (((env "b" * env "c") + (((-1) * env "a") * env "d")))).add ((hasDerivAt_const t (((-1) * ((env "a" * env "c") + (((-1) * env "b") * env "d"))))).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))))).mul (hasDerivAt_const t (((((env "f" * env "g") * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))) * (env "p" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, add_sub_cancel_right]
    have hn3_3c : ((k : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn3_3
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb1 (by omega)
      · subst hm0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "g" * Real.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ k =
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ 1 := by
          have := zsplit ((env "g" * Real.cos ((env "e" + (env "f" * t))))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k + 1) =
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ 2 := by
          have := zsplit ((env "g" * Real.cos ((env "e" + (env "f" * t))))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k + 2) =
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ 3 := by
          have := zsplit ((env "g" * Real.cos ((env "e" + (env "f" * t))))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k, e2k]
        generalize ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (C*env "a"^2*env "c"*Pk*((k : ℤ) : ℝ) + C*env "a"^2*env "c"*Pk +
            C*env "a"*env "b"*env "c"*Pk*S*((k : ℤ) : ℝ) + C*env "a"*env "b"*env "c"*Pk*S -
            C*env "b"^2*env "c"*Pk*((k : ℤ) : ℝ) - C*env "b"^2*env "c"*Pk -
            C*env "b"^2*env "d"*Pk*S*((k : ℤ) : ℝ) - C*env "b"^2*env "d"*Pk*S) * hP
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb1 (by omega)
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
        simp only [e0m, e1m]
        have hdmk : (env "g" * Real.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ k =
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ 1 := by
          have := zsplit ((env "g" * Real.cos ((env "e" + (env "f" * t))))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k + 1) =
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ 2 := by
          have := zsplit ((env "g" * Real.cos ((env "e" + (env "f" * t))))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k + 2) =
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ 3 := by
          have := zsplit ((env "g" * Real.cos ((env "e" + (env "f" * t))))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k, e2k]
        generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (C*env "a"^3*env "c"*env "f"*env "g"*Pk*Pm*((k : ℤ) : ℝ) +
            C*env "a"^3*env "c"*env "f"*env "g"*Pk*Pm +
            2*C*env "a"^2*env "b"*env "c"*env "f"*env "g"*Pk*Pm*S*((k : ℤ) : ℝ) +
            2*C*env "a"^2*env "b"*env "c"*env "f"*env "g"*Pk*Pm*S +
            C*env "a"*env "b"^2*env "c"*env "f"*env "g"*Pk*Pm*S^2*((k : ℤ) : ℝ) +
            C*env "a"*env "b"^2*env "c"*env "f"*env "g"*Pk*Pm*S^2 -
            C*env "a"*env "b"^2*env "c"*env "f"*env "g"*Pk*Pm*((k : ℤ) : ℝ) -
            C*env "a"*env "b"^2*env "c"*env "f"*env "g"*Pk*Pm -
            C*env "a"*env "b"^2*env "d"*env "f"*env "g"*Pk*Pm*S*((k : ℤ) : ℝ) -
            C*env "a"*env "b"^2*env "d"*env "f"*env "g"*Pk*Pm*S -
            C*env "b"^3*env "c"*env "f"*env "g"*Pk*Pm*S*((k : ℤ) : ℝ) -
            C*env "b"^3*env "c"*env "f"*env "g"*Pk*Pm*S -
            C*env "b"^3*env "d"*env "f"*env "g"*Pk*Pm*S^2*((k : ℤ) : ℝ) -
            C*env "b"^3*env "d"*env "f"*env "g"*Pk*Pm*S^2) * hP

set_option maxHeartbeats 1000000 in
theorem rubi4122r34Nondeg_complex : rubi4122r34Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4122r34Nondeg.conditions rubi4122r34Nondeg.body
    rubi4122r34Nondeg.result rubi4122r34Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4122r34Nondeg])
  have hn0v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4122r34Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "g")) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi4122r34Nondeg])
  have hn3_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  have hn3_1 : env "g" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  have hn3_3 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r34Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r34Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h
  have hb1 : k < -1 := by
    have h := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi4122r34Nondeg])
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
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4122r34Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "g" * Complex.cos ((env "e" + (env "f" * w)))) ≠ 0) := by
    intro w h
    simp [rubi4122r34Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r34Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm, emk2, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4122r34Nondeg, Defined, eval, recEnv, Interp.complex, emm1, emk1, ivm1C,
        iv2C] at h hn0 hn3_0 hn3_1 hn3_3 ⊢
    tauto
  · simp only [rubi4122r34Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k +
        2) * ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m)) *
        (((env "c" *
        (((env "a") ^ 2 * (env "p" + 2)) + (((-1) * (env "b") ^ 2) * ((env "m" + env "p") + 2)))) +
        (((env "a" * env "b") * env "d") * env "m")) +
        (((env "b" * ((env "a" * env "c") + (((-1) * env "b") * env "d"))) *
        ((env "m" + env "p") + 3)) * Complex.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, emk2, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4122r34Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r34Nondeg.result) =
            fun w => (((((env "g" * Complex.cos ((env "e" + (env "f" * w))))) ^ (k + 1) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "b" * env "c") + (((-1) * env "a") * env "d")) +
            (((-1) * ((env "a" * env "c") + (((-1) * env "b") * env "d"))) *
            Complex.sin ((env "e" + (env "f" * w)))))) *
            ((((env "f" * env "g") * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))) *
            (env "p" + 1)))⁻¹) +
            (1 * ((((env "g") ^ 2 * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))) *
            (env "p" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4122r34Nondeg, eval, recEnv, Interp.complex, emm1, emk1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4122r34Nondeg.body =
        (((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k) *
        ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m)) *
        (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) := by
      simp [rubi4122r34Nondeg, eval, Interp.complex, hkm, hkk]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "g" * Complex.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (k +
        1) _ (hdzk (k +
        1) (by omega))) ((hasDerivAt_const t (env "g")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdzm (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul ((hasDerivAt_const t (((env "b" * env "c") + (((-1) * env "a") * env "d")))).add ((hasDerivAt_const t (((-1) * ((env "a" * env "c") + (((-1) * env "b") * env "d"))))).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))))).mul (hasDerivAt_const t (((((env "f" * env "g") * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))) * (env "p" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, add_sub_cancel_right]
    have hn3_3c : ((k : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn3_3
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb1 (by omega)
      · subst hm0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "g" * Complex.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ k =
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ 1 := by
          have := zsplit ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k + 1) =
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ 2 := by
          have := zsplit ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k + 2) =
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ 3 := by
          have := zsplit ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k, e2k]
        generalize ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (C*env "a"^2*env "c"*Pk*((k : ℤ) : ℂ) + C*env "a"^2*env "c"*Pk +
            C*env "a"*env "b"*env "c"*Pk*S*((k : ℤ) : ℂ) + C*env "a"*env "b"*env "c"*Pk*S -
            C*env "b"^2*env "c"*Pk*((k : ℤ) : ℂ) - C*env "b"^2*env "c"*Pk -
            C*env "b"^2*env "d"*Pk*S*((k : ℤ) : ℂ) - C*env "b"^2*env "d"*Pk*S) * hP
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb1 (by omega)
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
        simp only [e0m, e1m]
        have hdmk : (env "g" * Complex.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ k =
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ 1 := by
          have := zsplit ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k + 1) =
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ 2 := by
          have := zsplit ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k + 2) =
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ 3 := by
          have := zsplit ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k, e2k]
        generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (C*env "a"^3*env "c"*env "f"*env "g"*Pk*Pm*((k : ℤ) : ℂ) +
            C*env "a"^3*env "c"*env "f"*env "g"*Pk*Pm +
            2*C*env "a"^2*env "b"*env "c"*env "f"*env "g"*Pk*Pm*S*((k : ℤ) : ℂ) +
            2*C*env "a"^2*env "b"*env "c"*env "f"*env "g"*Pk*Pm*S +
            C*env "a"*env "b"^2*env "c"*env "f"*env "g"*Pk*Pm*S^2*((k : ℤ) : ℂ) +
            C*env "a"*env "b"^2*env "c"*env "f"*env "g"*Pk*Pm*S^2 -
            C*env "a"*env "b"^2*env "c"*env "f"*env "g"*Pk*Pm*((k : ℤ) : ℂ) -
            C*env "a"*env "b"^2*env "c"*env "f"*env "g"*Pk*Pm -
            C*env "a"*env "b"^2*env "d"*env "f"*env "g"*Pk*Pm*S*((k : ℤ) : ℂ) -
            C*env "a"*env "b"^2*env "d"*env "f"*env "g"*Pk*Pm*S -
            C*env "b"^3*env "c"*env "f"*env "g"*Pk*Pm*S*((k : ℤ) : ℂ) -
            C*env "b"^3*env "c"*env "f"*env "g"*Pk*Pm*S -
            C*env "b"^3*env "d"*env "f"*env "g"*Pk*Pm*S^2*((k : ℤ) : ℂ) -
            C*env "b"^3*env "d"*env "f"*env "g"*Pk*Pm*S^2) * hP

/-! ## rubi4122r39Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4122r39Nondeg_real : rubi4122r39Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4122r39Nondeg.conditions rubi4122r39Nondeg.body
    rubi4122r39Nondeg.result rubi4122r39Nondeg.integrals
  intro env hc t hF
  have hr0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4122r39Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hr1 : (env "m" + env "p") + 1 - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)) (.int 0)) (by simp [rubi4122r39Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.var "g")) (.var "m")) (.int 0)) (by simp [rubi4122r39Nondeg])
  have hn2_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "g" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_3 : env "m" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r39Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r39Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4122r39Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "g" * Real.cos ((env "e" + (env "f" * w)))) ≠ 0) := by
    intro w h
    simp [rubi4122r39Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r39Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, emk2] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4122r39Nondeg, Defined, eval, recEnv, Interp.real, hkm, emk1, ivm1R,
        iv2R] at h hn2_0 hn2_1 hn2_2 hn2_3 ⊢
    tauto
  · simp only [rubi4122r39Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k + 2) *
        ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, emk2, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4122r39Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r39Nondeg.result) =
            fun w => (((env "b" * ((env "g" * Real.cos ((env "e" + (env "f" * w))))) ^ (k + 1)) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((((env "a" * env "f") * env "g") * env "m"))⁻¹) + ((-1) * ((env "g") ^ 2)⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4122r39Nondeg, eval, recEnv, Interp.real, hkm, emk1, ivm1R, iv2R,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4122r39Nondeg.body =
        (((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k) *
        (Real.sin ((env "e" + (env "f" * t)))) ^ 2) *
        ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) := by
      simp [rubi4122r39Nondeg, eval, Interp.real, hkm, hkk, iv2R]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "g" * Real.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "b")).mul (HasDerivAt.comp t (hasDerivAt_zpow (k +
        1) _ (hdzk (k +
        1) (by omega))) ((hasDerivAt_const t (env "g")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((((env "a" * env "f") * env "g") * env "m"))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, add_sub_cancel_right]
    have hr1c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 - (0) = 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hr1
    have hn2_3c : ((m : ℤ) : ℝ) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_3
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd (by norm_num) hn2_3c
      · subst hm0
        exact absurd (by norm_num) hn2_3c
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
        linear_combination (-env "a"^2*Pm*((m : ℤ) : ℝ) - env "a"*env "b"*Pm*S*((m : ℤ) : ℝ) +
            env "b"^2*Pm*((m : ℤ) : ℝ)) * hP + (-Pm*((m : ℤ) : ℝ)) * hr0 +
            (-env "a"*env "b"*Pm*S - env "b"^2*Pm*S^2) * hr1c
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
        have hdmk : (env "g" * Real.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ k =
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ 1 := by
          have := zsplit ((env "g" * Real.cos ((env "e" + (env "f" * t))))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k + 1) =
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ 2 := by
          have := zsplit ((env "g" * Real.cos ((env "e" + (env "f" * t))))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k + 2) =
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ 3 := by
          have := zsplit ((env "g" * Real.cos ((env "e" + (env "f" * t))))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k, e2k]
        generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-C*env "a"^2*env "f"*env "g"*Pk*Pm*((m : ℤ) : ℝ) -
            C*env "a"*env "b"*env "f"*env "g"*Pk*Pm*S*((m : ℤ) : ℝ) +
            C*env "b"^2*env "f"*env "g"*Pk*Pm*((m : ℤ) : ℝ)) * hP +
            (-C*env "f"*env "g"*Pk*Pm*((m : ℤ) : ℝ)) * hr0 +
            (-C*env "a"*env "b"*env "f"*env "g"*Pk*Pm*S - C*env "b"^2*env "f"*env "g"*Pk*Pm*S^2) *
            hr1c

set_option maxHeartbeats 1000000 in
theorem rubi4122r39Nondeg_complex : rubi4122r39Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4122r39Nondeg.conditions rubi4122r39Nondeg.body
    rubi4122r39Nondeg.result rubi4122r39Nondeg.integrals
  intro env hc t hF
  have hr0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4122r39Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hr1 : (env "m" + env "p") + 1 - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)) (.int 0)) (by simp [rubi4122r39Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.var "g")) (.var "m")) (.int 0)) (by simp [rubi4122r39Nondeg])
  have hn2_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "g" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_3 : env "m" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r39Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r39Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4122r39Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "g" * Complex.cos ((env "e" + (env "f" * w)))) ≠ 0) := by
    intro w h
    simp [rubi4122r39Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r39Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm, emk2] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4122r39Nondeg, Defined, eval, recEnv, Interp.complex, hkm, emk1, ivm1C,
        iv2C] at h hn2_0 hn2_1 hn2_2 hn2_3 ⊢
    tauto
  · simp only [rubi4122r39Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k +
        2) * ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, emk2, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4122r39Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r39Nondeg.result) =
            fun w => (((env "b" *
            ((env "g" * Complex.cos ((env "e" + (env "f" * w))))) ^ (k + 1)) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((((env "a" * env "f") * env "g") * env "m"))⁻¹) + ((-1) * ((env "g") ^ 2)⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4122r39Nondeg, eval, recEnv, Interp.complex, hkm, emk1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4122r39Nondeg.body =
        (((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k) *
        (Complex.sin ((env "e" + (env "f" * t)))) ^ 2) *
        ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) := by
      simp [rubi4122r39Nondeg, eval, Interp.complex, hkm, hkk, iv2C]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "g" * Complex.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "b")).mul (HasDerivAt.comp t (hasDerivAt_zpow (k +
        1) _ (hdzk (k +
        1) (by omega))) ((hasDerivAt_const t (env "g")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((((env "a" * env "f") * env "g") * env "m"))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, add_sub_cancel_right]
    have hr1c : (((m : ℤ) : ℂ) + ((k : ℤ) : ℂ)) + 1 - (0) = 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hr1
    have hn2_3c : ((m : ℤ) : ℂ) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_3
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd (by norm_num) hn2_3c
      · subst hm0
        exact absurd (by norm_num) hn2_3c
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
        linear_combination (-env "a"^2*Pm*((m : ℤ) : ℂ) - env "a"*env "b"*Pm*S*((m : ℤ) : ℂ) +
            env "b"^2*Pm*((m : ℤ) : ℂ)) * hP + (-Pm*((m : ℤ) : ℂ)) * hr0 +
            (-env "a"*env "b"*Pm*S - env "b"^2*Pm*S^2) * hr1c
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
        have hdmk : (env "g" * Complex.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ k =
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ 1 := by
          have := zsplit ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k + 1) =
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ 2 := by
          have := zsplit ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k + 2) =
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ 3 := by
          have := zsplit ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k, e2k]
        generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-C*env "a"^2*env "f"*env "g"*Pk*Pm*((m : ℤ) : ℂ) -
            C*env "a"*env "b"*env "f"*env "g"*Pk*Pm*S*((m : ℤ) : ℂ) +
            C*env "b"^2*env "f"*env "g"*Pk*Pm*((m : ℤ) : ℂ)) * hP +
            (-C*env "f"*env "g"*Pk*Pm*((m : ℤ) : ℂ)) * hr0 +
            (-C*env "a"*env "b"*env "f"*env "g"*Pk*Pm*S - C*env "b"^2*env "f"*env "g"*Pk*Pm*S^2) *
            hr1c

/-! ## rubi476r19Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi476r19Nondeg_real : rubi476r19Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi476r19Nondeg.conditions rubi476r19Nondeg.body
    rubi476r19Nondeg.result rubi476r19Nondeg.integrals
  intro env hc t hF
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi476r19Nondeg])
  have hn3_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi476r19Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc,
        Real.cot_eq_cos_div_sin] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi476r19Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, Fn.csc,
        Real.cot_eq_cos_div_sin] at h
  have hb1 : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi476r19Nondeg])
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi476r19Nondeg.body →
      Real.sin (env "c" + env "d" * w) ≠ 0 ∧ (m < 0 → (env "e" + (env "f" * w)) ≠ 0) ∧
          (k < 0 →
          (env "a" +
          (env "b" *
          (Real.cos ((env "c" + (env "d" * w))) / Real.sin ((env "c" + (env "d" * w)))))) ≠ 0) := by
    intro w h
    simp [rubi476r19Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, Fn.csc,
        Real.cot_eq_cos_div_sin] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi476r19Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emmm1, emk1, Real.cot_eq_cos_div_sin] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi476r19Nondeg, Defined, eval, recEnv, Interp.real, hkm, emk1, ivm1R,
        Real.cot_eq_cos_div_sin] at h hn3_0 hn3_1 hn3_2 ⊢
    tauto
  · simp only [rubi476r19Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "e" + (env "f" * t))) ^ (m - 1) *
        ((env "a" +
        (env "b" *
        (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t))))))) ^ (k +
        1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emmm1, emk1, Real.cot_eq_cos_div_sin, sub_eq_add_neg,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi476r19Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi476r19Nondeg.result) =
            fun w => ((((-1) * ((env "e" + (env "f" * w))) ^ (m)) *
            ((env "a" +
            (env "b" *
            (Real.cos ((env "c" + (env "d" * w))) / Real.sin ((env "c" + (env "d" * w))))))) ^ (k +
            1)) * (((env "b" * env "d") * (env "n" + 1)))⁻¹) +
            ((env "f" * env "m") * (((env "b" * env "d") * (env "n" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi476r19Nondeg, eval, recEnv, Interp.real, hkm, emk1, ivm1R, Real.cot_eq_cos_div_sin,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi476r19Nondeg.body =
        (((env "e" + (env "f" * t))) ^ (m) * ((Real.sin ((env "c" + (env "d" * t))))⁻¹) ^ 2) *
        ((env "a" +
        (env "b" *
        (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t))))))) ^ (k) := by
      simp [rubi476r19Nondeg, eval, Interp.real, hkm, hkk, iv2R, Fn.csc, Real.cot_eq_cos_div_sin]
    rw [hfun, hEF]
    obtain ⟨hs0, hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "a" +
        (env "b" *
        (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" +
        (env "d" * t)))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((-1))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t)))) hs0))))).mul (hasDerivAt_const t ((((env "b" * env "d") * (env "n" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, add_sub_cancel_right]
    have hn3_2c : ((k : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "c" + env "d" * t)
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
        have hdmm : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "e" + (env "f" * t))) ^ m = ((env "e" + (env "f" * t))) ^ (m - 1) *
            ((env "e" + (env "f" * t))) ^ 1 := by
          have := zsplit ((env "e" + (env "f" * t))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "e" + (env "f" * t))) ^ (m + 1) = ((env "e" + (env "f" * t))) ^ (m - 1) *
            ((env "e" + (env "f" * t))) ^ 2 := by
          have := zsplit ((env "e" + (env "f" * t))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "e" + (env "f" * t))) ^ (m + 2) = ((env "e" + (env "f" * t))) ^ (m - 1) *
            ((env "e" + (env "f" * t))) ^ 3 := by
          have := zsplit ((env "e" + (env "f" * t))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        generalize ((env "e" + (env "f" * t))) ^ (m - 1) = Pm
        generalize Real.sin (env "c" + env "d" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "c" + env "d" * t) = C at hP ⊢
        field_simp
        linear_combination (env "b"*env "d"*env "e"*Pm + env "b"*env "d"*env "f"*Pm*t) * hP
      · have hdmm : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "e" + (env "f" * t))) ^ m = ((env "e" + (env "f" * t))) ^ (m - 1) *
            ((env "e" + (env "f" * t))) ^ 1 := by
          have := zsplit ((env "e" + (env "f" * t))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "e" + (env "f" * t))) ^ (m + 1) = ((env "e" + (env "f" * t))) ^ (m - 1) *
            ((env "e" + (env "f" * t))) ^ 2 := by
          have := zsplit ((env "e" + (env "f" * t))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "e" + (env "f" * t))) ^ (m + 2) = ((env "e" + (env "f" * t))) ^ (m - 1) *
            ((env "e" + (env "f" * t))) ^ 3 := by
          have := zsplit ((env "e" + (env "f" * t))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : (env "a" +
            (env "b" *
            (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" +
            (env "d" * t)))))) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "a" +
            (env "b" *
            (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t))))))) ^ k =
            ((env "a" +
            (env "b" *
            (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t))))))) ^ (k -
            1) * ((env "a" +
            (env "b" *
            (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t))))))) ^ 1 :=
            by
          have := zsplit ((env "a" +
              (env "b" *
              (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t))))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "a" +
            (env "b" *
            (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t))))))) ^ (k +
            1) = ((env "a" +
            (env "b" *
            (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t))))))) ^ (k -
            1) * ((env "a" +
            (env "b" *
            (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t))))))) ^ 2 :=
            by
          have := zsplit ((env "a" +
              (env "b" *
              (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t))))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "a" +
            (env "b" *
            (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t))))))) ^ (k +
            2) = ((env "a" +
            (env "b" *
            (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t))))))) ^ (k -
            1) * ((env "a" +
            (env "b" *
            (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t))))))) ^ 3 :=
            by
          have := zsplit ((env "a" +
              (env "b" *
              (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t))))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "e" + (env "f" * t))) ^ (m - 1) = Pm
        generalize ((env "a" +
            (env "b" *
            (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t))))))) ^ (k -
            1) = Pk
        generalize Real.sin (env "c" + env "d" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "c" + env "d" * t) = C at hP ⊢
        field_simp
        linear_combination (C*env "b"^2*env "d"*env "e"*Pk*Pm*((k : ℤ) : ℝ) +
            C*env "b"^2*env "d"*env "e"*Pk*Pm + C*env "b"^2*env "d"*env "f"*Pk*Pm*t*((k : ℤ) : ℝ) +
            C*env "b"^2*env "d"*env "f"*Pk*Pm*t +
            env "a"*env "b"*env "d"*env "e"*Pk*Pm*S*((k : ℤ) : ℝ) +
            env "a"*env "b"*env "d"*env "e"*Pk*Pm*S +
            env "a"*env "b"*env "d"*env "f"*Pk*Pm*S*t*((k : ℤ) : ℝ) +
            env "a"*env "b"*env "d"*env "f"*Pk*Pm*S*t) * hP

/-! ## rubi476r21Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi476r21Nondeg_real : rubi476r21Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi476r21Nondeg.conditions rubi476r21Nondeg.body
    rubi476r21Nondeg.result rubi476r21Nondeg.integrals
  intro env hc t hF
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi476r21Nondeg])
  have hn3_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi476r21Nondeg, Defined, eval, Interp.real, hkm, Fn.csc] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi476r21Nondeg, Defined, eval, Interp.real, hkm, hkk, Fn.csc] at h
  have hb1 : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi476r21Nondeg])
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi476r21Nondeg.body →
      Real.sin (env "c" + env "d" * w) ≠ 0 ∧ (m < 0 → (env "e" + (env "f" * w)) ≠ 0) ∧
          (k < 0 → (env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi476r21Nondeg, Defined, eval, Interp.real, hkm, hkk, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi476r21Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emmm1, emk1, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi476r21Nondeg, Defined, eval, recEnv, Interp.real, hkm, emk1, ivm1R,
        Fn.csc] at h hn3_0 hn3_1 hn3_2 ⊢
    tauto
  · simp only [rubi476r21Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "e" + (env "f" * t))) ^ (m - 1) *
        ((env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * t))))⁻¹))) ^ (k + 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emmm1, emk1, Fn.csc, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi476r21Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi476r21Nondeg.result) =
            fun w => ((((-1) * ((env "e" + (env "f" * w))) ^ (m)) *
            ((env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * w))))⁻¹))) ^ (k + 1)) *
            (((env "b" * env "d") * (env "n" + 1)))⁻¹) +
            ((env "f" * env "m") * (((env "b" * env "d") * (env "n" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi476r21Nondeg, eval, recEnv, Interp.real, hkm, emk1, ivm1R, Fn.csc,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi476r21Nondeg.body =
        ((((env "e" + (env "f" * t))) ^ (m) * (Real.sin ((env "c" + (env "d" * t))))⁻¹) *
        (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t))))) *
        ((env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * t))))⁻¹))) ^ (k) := by
      simp [rubi476r21Nondeg, eval, Interp.real, hkm, hkk, Fn.csc, Real.cot_eq_cos_div_sin]
    rw [hfun, hEF]
    obtain ⟨hs0, hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((-1))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t ((((env "b" * env "d") * (env "n" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.inv_apply, add_sub_cancel_right]
    have hn3_2c : ((k : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "c" + env "d" * t)
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
        have hdmm : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "e" + (env "f" * t))) ^ m = ((env "e" + (env "f" * t))) ^ (m - 1) *
            ((env "e" + (env "f" * t))) ^ 1 := by
          have := zsplit ((env "e" + (env "f" * t))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "e" + (env "f" * t))) ^ (m + 1) = ((env "e" + (env "f" * t))) ^ (m - 1) *
            ((env "e" + (env "f" * t))) ^ 2 := by
          have := zsplit ((env "e" + (env "f" * t))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "e" + (env "f" * t))) ^ (m + 2) = ((env "e" + (env "f" * t))) ^ (m - 1) *
            ((env "e" + (env "f" * t))) ^ 3 := by
          have := zsplit ((env "e" + (env "f" * t))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        generalize ((env "e" + (env "f" * t))) ^ (m - 1) = Pm
        generalize Real.sin (env "c" + env "d" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "c" + env "d" * t) = C at hP ⊢
        field_simp
        ring
      · have hdmm : (env "e" + (env "f" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "e" + (env "f" * t))) ^ m = ((env "e" + (env "f" * t))) ^ (m - 1) *
            ((env "e" + (env "f" * t))) ^ 1 := by
          have := zsplit ((env "e" + (env "f" * t))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "e" + (env "f" * t))) ^ (m + 1) = ((env "e" + (env "f" * t))) ^ (m - 1) *
            ((env "e" + (env "f" * t))) ^ 2 := by
          have := zsplit ((env "e" + (env "f" * t))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "e" + (env "f" * t))) ^ (m + 2) = ((env "e" + (env "f" * t))) ^ (m - 1) *
            ((env "e" + (env "f" * t))) ^ 3 := by
          have := zsplit ((env "e" + (env "f" * t))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : (env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ k -
            1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * t))))⁻¹))) ^ k =
            ((env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * t))))⁻¹))) ^ (k - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * t))))⁻¹))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * t))))⁻¹))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * t))))⁻¹))) ^ (k + 1) =
            ((env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * t))))⁻¹))) ^ (k - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * t))))⁻¹))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * t))))⁻¹))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * t))))⁻¹))) ^ (k + 2) =
            ((env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * t))))⁻¹))) ^ (k - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * t))))⁻¹))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * t))))⁻¹))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "e" + (env "f" * t))) ^ (m - 1) = Pm
        generalize ((env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * t))))⁻¹))) ^ (k - 1) = Pk
        generalize Real.sin (env "c" + env "d" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "c" + env "d" * t) = C at hP ⊢
        field_simp
        ring

/-! ## rubi476r9Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi476r9Nondeg_real : rubi476r9Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi476r9Nondeg.conditions rubi476r9Nondeg.body
    rubi476r9Nondeg.result rubi476r9Nondeg.integrals
  intro env hc t hF
  have hc3 :=
      hc (.ne (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi476r9Nondeg])
  have hn3_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi476r9Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc,
        Real.cot_eq_cos_div_sin] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi476r9Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, Fn.csc,
        Real.cot_eq_cos_div_sin] at h
  have hb1 : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi476r9Nondeg])
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi476r9Nondeg.body →
      Real.sin (env "a" + env "b" * w) ≠ 0 ∧ (m < 0 → (env "c" + (env "d" * w)) ≠ 0) ∧
          (k < 0 →
          (Real.cos ((env "a" + (env "b" * w))) / Real.sin ((env "a" + (env "b" * w)))) ≠ 0) := by
    intro w h
    simp [rubi476r9Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, Fn.csc,
        Real.cot_eq_cos_div_sin] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi476r9Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emmm1, emk1, Real.cot_eq_cos_div_sin] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi476r9Nondeg, Defined, eval, recEnv, Interp.real, hkm, emk1, ivm1R,
        Real.cot_eq_cos_div_sin] at h hn3_0 hn3_1 ⊢
    tauto
  · simp only [rubi476r9Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "c" + (env "d" * t))) ^ (m - 1) *
        ((Real.cos ((env "a" + (env "b" * t))) / Real.sin ((env "a" + (env "b" * t))))) ^ (k +
        1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emmm1, emk1, Real.cot_eq_cos_div_sin, sub_eq_add_neg,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi476r9Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi476r9Nondeg.result) =
            fun w => ((((-1) * ((env "c" + (env "d" * w))) ^ (m)) *
            ((Real.cos ((env "a" + (env "b" * w))) / Real.sin ((env "a" + (env "b" * w))))) ^ (k +
            1)) * ((env "b" * (env "n" + 1)))⁻¹) +
            ((env "d" * env "m") * ((env "b" * (env "n" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi476r9Nondeg, eval, recEnv, Interp.real, hkm, emk1, ivm1R, Real.cot_eq_cos_div_sin,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi476r9Nondeg.body =
        (((env "c" + (env "d" * t))) ^ (m) * ((Real.sin ((env "a" + (env "b" * t))))⁻¹) ^ 2) *
        ((Real.cos ((env "a" + (env "b" * t))) / Real.sin ((env "a" + (env "b" * t))))) ^ (k) := by
      simp [rubi476r9Nondeg, eval, Interp.real, hkm, hkk, iv2R, Fn.csc, Real.cot_eq_cos_div_sin]
    rw [hfun, hEF]
    obtain ⟨hs0, hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (Real.cos ((env "a" + (env "b" * t))) / Real.sin ((env "a" +
        (env "b" * t)))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((-1))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t)))) hs0))).mul (hasDerivAt_const t (((env "b" * (env "n" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, add_sub_cancel_right]
    have hn3_1c : ((k : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "a" + env "b" * t)
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
        have hdmm : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "c" + (env "d" * t))) ^ m = ((env "c" + (env "d" * t))) ^ (m - 1) *
            ((env "c" + (env "d" * t))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * t))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "c" + (env "d" * t))) ^ (m + 1) = ((env "c" + (env "d" * t))) ^ (m - 1) *
            ((env "c" + (env "d" * t))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * t))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "c" + (env "d" * t))) ^ (m + 2) = ((env "c" + (env "d" * t))) ^ (m - 1) *
            ((env "c" + (env "d" * t))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * t))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        generalize ((env "c" + (env "d" * t))) ^ (m - 1) = Pm
        generalize Real.sin (env "a" + env "b" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "a" + env "b" * t) = C at hP ⊢
        field_simp
        linear_combination (env "b"*env "c"*Pm + env "b"*env "d"*Pm*t) * hP
      · have hdmm : (env "c" + (env "d" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "c" + (env "d" * t))) ^ m = ((env "c" + (env "d" * t))) ^ (m - 1) *
            ((env "c" + (env "d" * t))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * t))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "c" + (env "d" * t))) ^ (m + 1) = ((env "c" + (env "d" * t))) ^ (m - 1) *
            ((env "c" + (env "d" * t))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * t))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "c" + (env "d" * t))) ^ (m + 2) = ((env "c" + (env "d" * t))) ^ (m - 1) *
            ((env "c" + (env "d" * t))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * t))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : (Real.cos ((env "a" + (env "b" * t))) / Real.sin ((env "a" +
            (env "b" * t)))) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((Real.cos ((env "a" + (env "b" * t))) / Real.sin ((env "a" +
            (env "b" * t))))) ^ k =
            ((Real.cos ((env "a" + (env "b" * t))) / Real.sin ((env "a" + (env "b" * t))))) ^ (k -
            1) * ((Real.cos ((env "a" + (env "b" * t))) / Real.sin ((env "a" +
            (env "b" * t))))) ^ 1 := by
          have := zsplit ((Real.cos ((env "a" + (env "b" * t))) / Real.sin ((env "a" +
              (env "b" * t))))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((Real.cos ((env "a" + (env "b" * t))) / Real.sin ((env "a" +
            (env "b" * t))))) ^ (k + 1) =
            ((Real.cos ((env "a" + (env "b" * t))) / Real.sin ((env "a" + (env "b" * t))))) ^ (k -
            1) * ((Real.cos ((env "a" + (env "b" * t))) / Real.sin ((env "a" +
            (env "b" * t))))) ^ 2 := by
          have := zsplit ((Real.cos ((env "a" + (env "b" * t))) / Real.sin ((env "a" +
              (env "b" * t))))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((Real.cos ((env "a" + (env "b" * t))) / Real.sin ((env "a" +
            (env "b" * t))))) ^ (k + 2) =
            ((Real.cos ((env "a" + (env "b" * t))) / Real.sin ((env "a" + (env "b" * t))))) ^ (k -
            1) * ((Real.cos ((env "a" + (env "b" * t))) / Real.sin ((env "a" +
            (env "b" * t))))) ^ 3 := by
          have := zsplit ((Real.cos ((env "a" + (env "b" * t))) / Real.sin ((env "a" +
              (env "b" * t))))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "c" + (env "d" * t))) ^ (m - 1) = Pm
        generalize ((Real.cos ((env "a" + (env "b" * t))) / Real.sin ((env "a" +
            (env "b" * t))))) ^ (k - 1) = Pk
        generalize Real.sin (env "a" + env "b" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "a" + env "b" * t) = C at hP ⊢
        field_simp
        linear_combination (C*env "b"*env "c"*Pk*Pm*((k : ℤ) : ℝ) + C*env "b"*env "c"*Pk*Pm +
            C*env "b"*env "d"*Pk*Pm*t*((k : ℤ) : ℝ) + C*env "b"*env "d"*Pk*Pm*t) * hP

end OSR.IntegrationRec293
