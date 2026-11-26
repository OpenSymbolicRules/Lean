import OSR.IntegrationNum1

/-! # Strengthened variants with two integer exponents: explicit terms plus a residual integral

Proofs of RUBI rules whose result is an explicit term with powers `y^m z^n` plus at most one residual
integral. The derivative of the explicit term is built from the rule expression; the integrand is
recovered with `sin² + cos² = 1` (when trigonometric) and the stated parameter relations, separately
for each exponent equal to `0` or not (`linear_combination` coefficients computed by Gröbner
reduction). Rules with `csc`, `cot` or `arctan` are proved over ℝ only. -/

namespace OSR.IntegrationRec290

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

/-! ## rubi4542r15Nondeg -/

theorem rubi4542r15Nondeg_real : rubi4542r15Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4542r15Nondeg.conditions rubi4542r15Nondeg.body
    rubi4542r15Nondeg.result rubi4542r15Nondeg.integrals
  intro env hc t hF
  have hr0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r15Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hc3 := hc (.ne (.app2 .mul (.var "f") (.var "n")) (.int 0)) (by simp [rubi4542r15Nondeg])
  have hn3_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "n" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hc4 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "n")) (.int 0)) (by simp [rubi4542r15Nondeg])
  have hn4_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_1 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_2 : env "n" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r15Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r15Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, Fn.csc] at h
  have hb1 : -1 < m := by
    have h := hc (.ge (.var "m") (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1))))) (by simp [rubi4542r15Nondeg])
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4542r15Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) ∧
          (k < 0 → (env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹) ≠ 0) := by
    intro w h
    simp [rubi4542r15Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4542r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, emk1, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4542r15Nondeg, Defined, eval, recEnv, Interp.real, hkm, hkk, ivm1R,
        Fn.csc] at h hn3_0 hn3_1 hn4_0 hn4_1 hn4_2 ⊢
    tauto
  · simp only [rubi4542r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m) *
        ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k + 1)) *
        ((((env "a" * env "A") * env "m") + ((((-1) * env "b") * env "B") * env "n")) +
        ((((-1) * env "b") * ((env "A" * ((env "m" + env "n") + 1)) + (env "C" * env "n"))) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, emk1, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4542r15Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4542r15Nondeg.result) =
            fun w => ((((env "A" *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m)) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ^ (k)) *
            ((env "f" * env "n"))⁻¹) + ((-1) * (((env "b" * env "d") * env "n"))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4542r15Nondeg, eval, recEnv, Interp.real, hkm, hkk, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4542r15Nondeg.body =
        (((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m) *
        ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k)) *
        ((env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) +
        (env "C" * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2)) := by
      simp [rubi4542r15Nondeg, eval, Interp.real, hkm, hkk, iv2R, Fn.csc]
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
    have hn4_2c : ((k : ℤ) : ℝ) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn4_2
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
        linear_combination (-env "A"*Pk*((k : ℤ) : ℝ) - env "A"*Pk) * hP + (0) * hr0
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
            (-env "A"*env "d"*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ)) * hr0

/-! ## rubi4542r16Nondeg -/

theorem rubi4542r16Nondeg_real : rubi4542r16Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4542r16Nondeg.conditions rubi4542r16Nondeg.body
    rubi4542r16Nondeg.result rubi4542r16Nondeg.integrals
  intro env hc t hF
  have hr0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r16Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "n")) (.int 0)) (by simp [rubi4542r16Nondeg])
  have hn3_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "n" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hc4 := hc (.ne (.app2 .mul (.var "f") (.var "n")) (.int 0)) (by simp [rubi4542r16Nondeg])
  have hn4_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_1 : env "n" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r16Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r16Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, Fn.csc] at h
  have hb1 : -1 < m := by
    have h := hc (.ge (.var "m") (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1))))) (by simp [rubi4542r16Nondeg])
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4542r16Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) ∧
          (k < 0 → (env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹) ≠ 0) := by
    intro w h
    simp [rubi4542r16Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4542r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, emk1, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4542r16Nondeg, Defined, eval, recEnv, Interp.real, hkm, hkk, ivm1R,
        Fn.csc] at h hn3_0 hn3_1 hn3_2 hn4_0 hn4_1 ⊢
    tauto
  · simp only [rubi4542r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m) *
        ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k + 1)) *
        (((env "a" * env "A") * env "m") +
        ((((-1) * env "b") * ((env "A" * ((env "m" + env "n") + 1)) + (env "C" * env "n"))) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, emk1, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4542r16Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4542r16Nondeg.result) =
            fun w => ((((env "A" *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m)) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ^ (k)) *
            ((env "f" * env "n"))⁻¹) + ((-1) * (((env "b" * env "d") * env "n"))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4542r16Nondeg, eval, recEnv, Interp.real, hkm, hkk, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4542r16Nondeg.body =
        (((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m) *
        ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k)) *
        (env "A" + (env "C" * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2)) := by
      simp [rubi4542r16Nondeg, eval, Interp.real, hkm, hkk, iv2R, Fn.csc]
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
    have hn3_2c : ((k : ℤ) : ℝ) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn3_2
    have hn4_1c : ((k : ℤ) : ℝ) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn4_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd (by norm_num) hn3_2c
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
        linear_combination (-env "A"*Pk*((k : ℤ) : ℝ) - env "A"*Pk) * hP + (0) * hr0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd (by norm_num) hn3_2c
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
            (-env "A"*env "d"*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ)) * hr0

end OSR.IntegrationRec290
