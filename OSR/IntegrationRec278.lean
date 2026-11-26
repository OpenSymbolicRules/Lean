import OSR.IntegrationNum1

/-! # Strengthened cosecant variants: `K cot y^E` plus a residual integral

Proofs over ℝ (`csc` has no complex interpretation) of RUBI rules whose result is an explicit term
`K cot (a + b csc)^E` (or a product of `cot`, `csc` and such powers) plus a residual integral. The
derivative of the explicit term is built from the rule expression; the integrand is recovered with
`sin² + cos² = 1` and the stated parameter relations, separately for `m = 0` and `m ≠ 0`
(`linear_combination` coefficients computed by Gröbner reduction). -/

namespace OSR.IntegrationRec278

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

/-! ## rubi4512r50Nondeg -/

theorem rubi4512r50Nondeg_real : rubi4512r50Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4512r50Nondeg.conditions rubi4512r50Nondeg.body
    rubi4512r50Nondeg.result rubi4512r50Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4512r50Nondeg])
  have hn0v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4512r50Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int 0)) (by simp [rubi4512r50Nondeg])
  have hn2_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  have hn2_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4512r50Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  have hb1 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4512r50Nondeg])
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4512r50Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4512r50Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4512r50Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4512r50Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R,
        Fn.csc] at h hn0 hn2_0 hn2_1 ⊢
    tauto
  · simp only [rubi4512r50Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1)) *
        ((env "b" * (env "m" + 1)) +
        ((((-1) * env "a") * (env "m" + 2)) * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4512r50Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4512r50Nondeg.result) =
            fun w => (((env "a" *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m + 1)) *
            (((env "f" * (env "m" + 1)) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹) +
            ((-1) * (((env "m" + 1) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4512r50Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4512r50Nondeg.body =
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2 *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m) := by
      simp [rubi4512r50Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hB0⟩ := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "a")).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t ((((env "f" * (env "m" + 1)) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply,

      add_sub_cancel_right]
    have hn2_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "a"^2*S - 2*env "a"*env "b") * hP
    · have hdm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
        1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "a"^3*env "f"*P*S^2 - env "a"^2*env "b"*env "f"*P*S*((m : ℤ) : ℝ) -
          3*env "a"^2*env "b"*env "f"*P*S - env "a"*env "b"^2*env "f"*P*((m : ℤ) : ℝ) -
          2*env "a"*env "b"^2*env "f"*P) * hP

/-! ## rubi4531r14Nondeg -/

theorem rubi4531r14Nondeg_real : rubi4531r14Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4531r14Nondeg.conditions rubi4531r14Nondeg.body
    rubi4531r14Nondeg.result rubi4531r14Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "A" * env "b") + (((-1) * env "a") * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r14Nondeg])
  have hn0v : (env "A" * env "b") + (-env "a" * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r14Nondeg])
  have hn1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4531r14Nondeg])
  have hn1v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4531r14Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int 0)) (by simp [rubi4531r14Nondeg])
  have hn3_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  have hn3_2 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4531r14Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  have hb2 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4531r14Nondeg])
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4531r14Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4531r14Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4531r14Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, iv2R, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4531r14Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R,
        Fn.csc] at h hn0 hn1 hn3_0 hn3_1 hn3_2 ⊢
    tauto
  · simp only [rubi4531r14Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1)) *
        (((env "b" * ((env "A" * env "b") + (((-1) * env "a") * env "B"))) * (env "m" + 1)) +
        (((-1) *
        ((((env "a" * env "A") * env "b") * (env "m" + 2)) +
        (((-1) * env "B") * ((env "a") ^ 2 + ((env "b") ^ 2 * (env "m" + 1)))))) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, iv2R, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4531r14Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4531r14Nondeg.result) =
            fun w => ((((env "a" * ((env "A" * env "b") + (((-1) * env "a") * env "B"))) *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m + 1)) *
            ((((env "b" * env "f") * (env "m" + 1)) *
            ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹) +
            ((-1) * (((env "b" * (env "m" + 1)) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4531r14Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4531r14Nondeg.body =
        (((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2 *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        (env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) := by
      simp [rubi4531r14Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hB0⟩ := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((env "a" *
        ((env "A" * env "b") +
        (((-1) * env "a") *
        env "B"))))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t (((((env "b" * env "f") * (env "m" + 1)) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply,

      add_sub_cancel_right]
    have hn3_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "a"^2*env "b"*S - 2*env "A"*env "a"*env "b"^2 +
          env "B"*env "a"^3*S + 2*env "B"*env "a"^2*env "b") * hP
    · have hdm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
        1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "a"^3*env "b"*env "f"*P*S^2 -
          env "A"*env "a"^2*env "b"^2*env "f"*P*S*((m : ℤ) : ℝ) -
          3*env "A"*env "a"^2*env "b"^2*env "f"*P*S -
          env "A"*env "a"*env "b"^3*env "f"*P*((m : ℤ) : ℝ) -
          2*env "A"*env "a"*env "b"^3*env "f"*P + env "B"*env "a"^4*env "f"*P*S^2 +
          env "B"*env "a"^3*env "b"*env "f"*P*S*((m : ℤ) : ℝ) +
          3*env "B"*env "a"^3*env "b"*env "f"*P*S +
          env "B"*env "a"^2*env "b"^2*env "f"*P*((m : ℤ) : ℝ) +
          2*env "B"*env "a"^2*env "b"^2*env "f"*P) * hP

/-! ## rubi4531r15Nondeg -/

theorem rubi4531r15Nondeg_real : rubi4531r15Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4531r15Nondeg.conditions rubi4531r15Nondeg.body
    rubi4531r15Nondeg.result rubi4531r15Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "A" * env "b") + (((-1) * env "a") * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r15Nondeg])
  have hn0v : (env "A" * env "b") + (-env "a" * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r15Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 2))) (.int 0)) (by simp [rubi4531r15Nondeg])
  have hn2_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "m" + 2 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4531r15Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  have hb1 : -1 ≤ m := by
    have h := hc (.ge (.var "m") (.int (-1))) (by simp [rubi4531r15Nondeg])
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4531r15Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4531r15Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4531r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4531r15Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R,
        Fn.csc] at h hn0 hn2_0 hn2_1 hn2_2 ⊢
    tauto
  · simp only [rubi4531r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        (((env "b" * env "B") * (env "m" + 1)) +
        ((((env "A" * env "b") * (env "m" + 2)) + (((-1) * env "a") * env "B")) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4531r15Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4531r15Nondeg.result) =
            fun w => (((((-1) * env "B") *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m + 1)) *
            (((env "b" * env "f") * (env "m" + 2)))⁻¹) + (1 * ((env "b" * (env "m" + 2)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4531r15Nondeg, eval, recEnv, Interp.real, em1, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4531r15Nondeg.body =
        (((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2 *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        (env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) := by
      simp [rubi4531r15Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hB0⟩ := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (((-1) *
        env "B"))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t ((((env "b" * env "f") * (env "m" + 2)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply,

      add_sub_cancel_right]
    have hn2_2c : ((m : ℤ) : ℝ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "B"*env "a"*S + 2*env "B"*env "b") * hP
    · have hdm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
        1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "B"*env "a"^2*env "f"*P*S^2 +
          env "B"*env "a"*env "b"*env "f"*P*S*((m : ℤ) : ℝ) +
          3*env "B"*env "a"*env "b"*env "f"*P*S + env "B"*env "b"^2*env "f"*P*((m : ℤ) : ℝ) +
          2*env "B"*env "b"^2*env "f"*P) * hP

/-! ## rubi4531r8Nondeg -/

theorem rubi4531r8Nondeg_real : rubi4531r8Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4531r8Nondeg.conditions rubi4531r8Nondeg.body
    rubi4531r8Nondeg.result rubi4531r8Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "A" * env "b") + (((-1) * env "a") * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r8Nondeg])
  have hn0v : (env "A" * env "b") + (-env "a" * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r8Nondeg])
  have hn1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4531r8Nondeg])
  have hn1v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4531r8Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int 0)) (by simp [rubi4531r8Nondeg])
  have hn3_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  have hn3_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4531r8Nondeg, Defined, eval, Interp.real, hkm, Fn.csc] at h
  have hb2 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4531r8Nondeg])
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4531r8Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4531r8Nondeg, Defined, eval, Interp.real, hkm, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4531r8Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4531r8Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R,
        Fn.csc] at h hn0 hn1 hn3_0 hn3_1 ⊢
    tauto
  · simp only [rubi4531r8Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1)) *
        ((((env "a" * env "A") + (((-1) * env "b") * env "B")) * (env "m" + 1)) +
        ((((-1) * ((env "A" * env "b") + (((-1) * env "a") * env "B"))) * (env "m" + 2)) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4531r8Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4531r8Nondeg.result) =
            fun w => (((((-1) * ((env "A" * env "b") + (((-1) * env "a") * env "B"))) *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m + 1)) *
            (((env "f" * (env "m" + 1)) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹) +
            (1 * (((env "m" + 1) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4531r8Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4531r8Nondeg.body =
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        (env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) := by
      simp [rubi4531r8Nondeg, eval, Interp.real, hkm, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hB0⟩ := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (((-1) *
        ((env "A" * env "b") +
        (((-1) * env "a") *
        env "B"))))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t ((((env "f" * (env "m" + 1)) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply,

      add_sub_cancel_right]
    have hn3_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "A"*env "a"*env "b"*S + 2*env "A"*env "b"^2 - env "B"*env "a"^2*S -
          2*env "B"*env "a"*env "b") * hP
    · have hdm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
        1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "A"*env "a"^2*env "b"*env "f"*P*S^2 +
          env "A"*env "a"*env "b"^2*env "f"*P*S*((m : ℤ) : ℝ) +
          3*env "A"*env "a"*env "b"^2*env "f"*P*S + env "A"*env "b"^3*env "f"*P*((m : ℤ) : ℝ) +
          2*env "A"*env "b"^3*env "f"*P - env "B"*env "a"^3*env "f"*P*S^2 -
          env "B"*env "a"^2*env "b"*env "f"*P*S*((m : ℤ) : ℝ) -
          3*env "B"*env "a"^2*env "b"*env "f"*P*S -
          env "B"*env "a"*env "b"^2*env "f"*P*((m : ℤ) : ℝ) -
          2*env "B"*env "a"*env "b"^2*env "f"*P) * hP

/-! ## rubi4541r6Nondeg -/

theorem rubi4541r6Nondeg_real : rubi4541r6Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4541r6Nondeg.conditions rubi4541r6Nondeg.body
    rubi4541r6Nondeg.result rubi4541r6Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "C" * env "m") + (env "A" * (env "m" + 1)) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "C") (.var "m")) (.app2 .mul (.var "A") (.app2 .add (.var "m") (.int 1)))) (.int 0)) (by simp [rubi4541r6Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4541r6Nondeg])
  have hn2_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4541r6Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  have hb1 : -1 < m := by
    have h := hc (.gt (.var "m") (.int (-1))) (by simp [rubi4541r6Nondeg])
    have h' : (-1 : ℝ) < ((m : ℤ) : ℝ) := by
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4541r6Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹) ≠ 0) := by
    intro w h
    simp [rubi4541r6Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4541r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4541r6Nondeg, Defined, eval, recEnv, Interp.real, hkm, ivm1R,
        Fn.csc] at h hn0 hn2_0 hn2_1 ⊢
    tauto
  · simp only [rubi4541r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "b" *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4541r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4541r6Nondeg.result) =
            fun w => (((((-1) * env "C") *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ^ (m)) *
            ((env "f" * (env "m" + 1)))⁻¹) +
            (((env "C" * env "m") + (env "A" * (env "m" + 1))) * ((env "m" + 1))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4541r6Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4541r6Nondeg.body =
        ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m) *
        (env "A" + (env "C" * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2)) := by
      simp [rubi4541r6Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hB0⟩ := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (((-1) *
        env "C"))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdz (m) (by omega))) ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0)))).mul (hasDerivAt_const t (((env "f" * (env "m" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply]
    have hn0c : (env "C" * ((m : ℤ) : ℝ)) + (env "A" * (((m : ℤ) : ℝ) + 1)) ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm]; exact hn0
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
      linear_combination (env "C") * hP
    · have hdm : (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ m =
          ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) *
          ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 1 := by
        have := zsplit ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m + 1) =
          ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) *
          ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 2 := by
        have := zsplit ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m + 2) =
          ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) *
          ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 3 := by
        have := zsplit ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0]
      generalize ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "C"*env "b"*env "f"*P*((m : ℤ) : ℝ) + env "C"*env "b"*env "f"*P) * hP

/-! ## rubi4542r10Nondeg -/

theorem rubi4542r10Nondeg_real : rubi4542r10Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4542r10Nondeg.conditions rubi4542r10Nondeg.body
    rubi4542r10Nondeg.result rubi4542r10Nondeg.integrals
  intro env hc t hF
  have hn1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r10Nondeg])
  have hn1v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r10Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int 0)) (by simp [rubi4542r10Nondeg])
  have hn2_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  have hn2_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  have hn2_2 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r10Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4542r10Nondeg])
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4542r10Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4542r10Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4542r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, iv2R, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4542r10Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R,
        Fn.csc] at h hn1 hn2_0 hn2_1 hn2_2 ⊢
    tauto
  · simp only [rubi4542r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1)) *
        ((((env "a" * env "b") * (env "A" + env "C")) * (env "m" + 1)) +
        (((-1) *
        (((env "A" * (env "b") ^ 2) + ((env "a") ^ 2 * env "C")) +
        ((env "b" * ((env "A" * env "b") + (env "b" * env "C"))) * (env "m" + 1)))) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, iv2R, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4542r10Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4542r10Nondeg.result) =
            fun w => (((((-1) * ((env "A" * (env "b") ^ 2) + ((env "a") ^ 2 * env "C"))) *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m + 1)) *
            ((((env "b" * env "f") * (env "m" + 1)) *
            ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹) +
            (1 * (((env "b" * (env "m" + 1)) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4542r10Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4542r10Nondeg.body =
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        (env "A" + (env "C" * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2)) := by
      simp [rubi4542r10Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hB0⟩ := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (((-1) *
        ((env "A" * (env "b") ^ 2) +
        ((env "a") ^ 2 *
        env "C"))))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t (((((env "b" * env "f") * (env "m" + 1)) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply,

      add_sub_cancel_right]
    have hn2_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "A"*env "a"*env "b"^2*S + 2*env "A"*env "b"^3 + env "C"*env "a"^3*S +
          2*env "C"*env "a"^2*env "b") * hP
    · have hdm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
        1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "A"*env "a"^2*env "b"^2*env "f"*P*S^2 +
          env "A"*env "a"*env "b"^3*env "f"*P*S*((m : ℤ) : ℝ) +
          3*env "A"*env "a"*env "b"^3*env "f"*P*S + env "A"*env "b"^4*env "f"*P*((m : ℤ) : ℝ) +
          2*env "A"*env "b"^4*env "f"*P + env "C"*env "a"^4*env "f"*P*S^2 +
          env "C"*env "a"^3*env "b"*env "f"*P*S*((m : ℤ) : ℝ) +
          3*env "C"*env "a"^3*env "b"*env "f"*P*S +
          env "C"*env "a"^2*env "b"^2*env "f"*P*((m : ℤ) : ℝ) +
          2*env "C"*env "a"^2*env "b"^2*env "f"*P) * hP

/-! ## rubi4542r11Nondeg -/

theorem rubi4542r11Nondeg_real : rubi4542r11Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4542r11Nondeg.conditions rubi4542r11Nondeg.body
    rubi4542r11Nondeg.result rubi4542r11Nondeg.integrals
  intro env hc t hF
  have hc1 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 2))) (.int 0)) (by simp [rubi4542r11Nondeg])
  have hn1_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_2 : env "m" + 2 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r11Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  have hb0 : -1 ≤ m := by
    have h := hc (.ge (.var "m") (.int (-1))) (by simp [rubi4542r11Nondeg])
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4542r11Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4542r11Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4542r11Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4542r11Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R,
        Fn.csc] at h hn1_0 hn1_1 hn1_2 ⊢
    tauto
  · simp only [rubi4542r11Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        ((((env "b" * env "A") * (env "m" + 2)) + ((env "b" * env "C") * (env "m" + 1))) +
        ((((env "b" * env "B") * (env "m" + 2)) + (((-1) * env "a") * env "C")) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4542r11Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4542r11Nondeg.result) =
            fun w => (((((-1) * env "C") *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m + 1)) *
            (((env "b" * env "f") * (env "m" + 2)))⁻¹) + (1 * ((env "b" * (env "m" + 2)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4542r11Nondeg, eval, recEnv, Interp.real, em1, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4542r11Nondeg.body =
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        ((env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) +
        (env "C" * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2)) := by
      simp [rubi4542r11Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hB0⟩ := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (((-1) *
        env "C"))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t ((((env "b" * env "f") * (env "m" + 2)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply,

      add_sub_cancel_right]
    have hn1_2c : ((m : ℤ) : ℝ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "C"*env "a"*S + 2*env "C"*env "b") * hP
    · have hdm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
        1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "C"*env "a"^2*env "f"*P*S^2 +
          env "C"*env "a"*env "b"*env "f"*P*S*((m : ℤ) : ℝ) +
          3*env "C"*env "a"*env "b"*env "f"*P*S + env "C"*env "b"^2*env "f"*P*((m : ℤ) : ℝ) +
          2*env "C"*env "b"^2*env "f"*P) * hP

/-! ## rubi4542r12Nondeg -/

theorem rubi4542r12Nondeg_real : rubi4542r12Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4542r12Nondeg.conditions rubi4542r12Nondeg.body
    rubi4542r12Nondeg.result rubi4542r12Nondeg.integrals
  intro env hc t hF
  have hc1 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 2))) (.int 0)) (by simp [rubi4542r12Nondeg])
  have hn1_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_2 : env "m" + 2 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r12Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  have hb0 : -1 ≤ m := by
    have h := hc (.ge (.var "m") (.int (-1))) (by simp [rubi4542r12Nondeg])
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4542r12Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4542r12Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4542r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4542r12Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R,
        Fn.csc] at h hn1_0 hn1_1 hn1_2 ⊢
    tauto
  · simp only [rubi4542r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        ((((env "b" * env "A") * (env "m" + 2)) + ((env "b" * env "C") * (env "m" + 1))) +
        ((((-1) * env "a") * env "C") * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4542r12Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4542r12Nondeg.result) =
            fun w => (((((-1) * env "C") *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m + 1)) *
            (((env "b" * env "f") * (env "m" + 2)))⁻¹) + (1 * ((env "b" * (env "m" + 2)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4542r12Nondeg, eval, recEnv, Interp.real, em1, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4542r12Nondeg.body =
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        (env "A" + (env "C" * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2)) := by
      simp [rubi4542r12Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hB0⟩ := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (((-1) *
        env "C"))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t ((((env "b" * env "f") * (env "m" + 2)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply,

      add_sub_cancel_right]
    have hn1_2c : ((m : ℤ) : ℝ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "C"*env "a"*S + 2*env "C"*env "b") * hP
    · have hdm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
        1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "C"*env "a"^2*env "f"*P*S^2 +
          env "C"*env "a"*env "b"*env "f"*P*S*((m : ℤ) : ℝ) +
          3*env "C"*env "a"*env "b"*env "f"*P*S + env "C"*env "b"^2*env "f"*P*((m : ℤ) : ℝ) +
          2*env "C"*env "b"^2*env "f"*P) * hP

/-! ## rubi4542r19Nondeg -/

theorem rubi4542r19Nondeg_real : rubi4542r19Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4542r19Nondeg.conditions rubi4542r19Nondeg.body
    rubi4542r19Nondeg.result rubi4542r19Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r19Nondeg])
  have hn0v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r19Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int 0)) (by simp [rubi4542r19Nondeg])
  have hn2_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  have hn2_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  have hn2_2 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r19Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  have hb1 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4542r19Nondeg])
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4542r19Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4542r19Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4542r19Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, iv2R, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4542r19Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R,
        Fn.csc] at h hn0 hn2_0 hn2_1 hn2_2 ⊢
    tauto
  · simp only [rubi4542r19Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1)) *
        ((((env "b" * (env "m" + 1)) *
        ((((-1) * env "a") * ((env "b" * env "B") + (((-1) * env "a") * env "C"))) +
        (env "A" * (env "b") ^ 2))) +
        ((((env "b" * env "B") * ((env "a") ^ 2 + ((env "b") ^ 2 * (env "m" + 1)))) +
        (((-1) * env "a") *
        (((env "A" * (env "b") ^ 2) * (env "m" + 2)) +
        (env "C" * ((env "a") ^ 2 + ((env "b") ^ 2 * (env "m" + 1))))))) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹)) +
        ((((((-1) * env "b") * env "C") * (env "m" + 1)) *
        ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))) *
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, iv2R, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4542r19Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4542r19Nondeg.result) =
            fun w => ((((env "a" *
            (((env "A" * (env "b") ^ 2) + ((((-1) * env "a") * env "b") * env "B")) +
            ((env "a") ^ 2 * env "C"))) *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m + 1)) *
            (((((env "b") ^ 2 * env "f") * (env "m" + 1)) *
            ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹) +
            ((-1) *
            ((((env "b") ^ 2 * (env "m" + 1)) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4542r19Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4542r19Nondeg.body =
        (((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2 *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        ((env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) +
        (env "C" * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2)) := by
      simp [rubi4542r19Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hB0⟩ := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((env "a" *
        (((env "A" * (env "b") ^ 2) + ((((-1) * env "a") * env "b") * env "B")) +
        ((env "a") ^ 2 *
        env "C"))))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t ((((((env "b") ^ 2 * env "f") * (env "m" + 1)) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply,

      add_sub_cancel_right]
    have hn2_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "a"^2*env "b"^2*S^2 - 2*env "A"*env "a"*env "b"^3*S +
          env "B"*env "a"^3*env "b"*S^2 + 2*env "B"*env "a"^2*env "b"^2*S - env "C"*env "a"^4*S^2 -
          2*env "C"*env "a"^3*env "b"*S) * hP
    · have hdm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
        1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "a"^3*env "b"^2*env "f"*P*S^3 -
          env "A"*env "a"^2*env "b"^3*env "f"*P*S^2*((m : ℤ) : ℝ) -
          3*env "A"*env "a"^2*env "b"^3*env "f"*P*S^2 -
          env "A"*env "a"*env "b"^4*env "f"*P*S*((m : ℤ) : ℝ) -
          2*env "A"*env "a"*env "b"^4*env "f"*P*S + env "B"*env "a"^4*env "b"*env "f"*P*S^3 +
          env "B"*env "a"^3*env "b"^2*env "f"*P*S^2*((m : ℤ) : ℝ) +
          3*env "B"*env "a"^3*env "b"^2*env "f"*P*S^2 +
          env "B"*env "a"^2*env "b"^3*env "f"*P*S*((m : ℤ) : ℝ) +
          2*env "B"*env "a"^2*env "b"^3*env "f"*P*S - env "C"*env "a"^5*env "f"*P*S^3 -
          env "C"*env "a"^4*env "b"*env "f"*P*S^2*((m : ℤ) : ℝ) -
          3*env "C"*env "a"^4*env "b"*env "f"*P*S^2 -
          env "C"*env "a"^3*env "b"^2*env "f"*P*S*((m : ℤ) : ℝ) -
          2*env "C"*env "a"^3*env "b"^2*env "f"*P*S) * hP

/-! ## rubi4542r20Nondeg -/

theorem rubi4542r20Nondeg_real : rubi4542r20Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4542r20Nondeg.conditions rubi4542r20Nondeg.body
    rubi4542r20Nondeg.result rubi4542r20Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r20Nondeg])
  have hn0v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r20Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int 0)) (by simp [rubi4542r20Nondeg])
  have hn2_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  have hn2_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  have hn2_2 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r20Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  have hb1 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4542r20Nondeg])
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4542r20Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4542r20Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4542r20Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, iv2R, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4542r20Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R,
        Fn.csc] at h hn0 hn2_0 hn2_1 hn2_2 ⊢
    tauto
  · simp only [rubi4542r20Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1)) *
        ((((env "b" * (env "m" + 1)) * (((env "a") ^ 2 * env "C") + (env "A" * (env "b") ^ 2))) +
        ((((-1) * env "a") *
        (((env "A" * (env "b") ^ 2) * (env "m" + 2)) +
        (env "C" * ((env "a") ^ 2 + ((env "b") ^ 2 * (env "m" + 1)))))) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹)) +
        ((((((-1) * env "b") * env "C") * (env "m" + 1)) *
        ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))) *
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, iv2R, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4542r20Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4542r20Nondeg.result) =
            fun w => ((((env "a" * ((env "A" * (env "b") ^ 2) + ((env "a") ^ 2 * env "C"))) *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m + 1)) *
            (((((env "b") ^ 2 * env "f") * (env "m" + 1)) *
            ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹) +
            ((-1) *
            ((((env "b") ^ 2 * (env "m" + 1)) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4542r20Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4542r20Nondeg.body =
        (((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2 *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        (env "A" + (env "C" * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2)) := by
      simp [rubi4542r20Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hB0⟩ := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((env "a" *
        ((env "A" * (env "b") ^ 2) +
        ((env "a") ^ 2 *
        env "C"))))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t ((((((env "b") ^ 2 * env "f") * (env "m" + 1)) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply,

      add_sub_cancel_right]
    have hn2_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "a"^2*env "b"^2*S^2 - 2*env "A"*env "a"*env "b"^3*S -
          env "C"*env "a"^4*S^2 - 2*env "C"*env "a"^3*env "b"*S) * hP
    · have hdm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
        1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "a"^3*env "b"^2*env "f"*P*S^3 -
          env "A"*env "a"^2*env "b"^3*env "f"*P*S^2*((m : ℤ) : ℝ) -
          3*env "A"*env "a"^2*env "b"^3*env "f"*P*S^2 -
          env "A"*env "a"*env "b"^4*env "f"*P*S*((m : ℤ) : ℝ) -
          2*env "A"*env "a"*env "b"^4*env "f"*P*S - env "C"*env "a"^5*env "f"*P*S^3 -
          env "C"*env "a"^4*env "b"*env "f"*P*S^2*((m : ℤ) : ℝ) -
          3*env "C"*env "a"^4*env "b"*env "f"*P*S^2 -
          env "C"*env "a"^3*env "b"^2*env "f"*P*S*((m : ℤ) : ℝ) -
          2*env "C"*env "a"^3*env "b"^2*env "f"*P*S) * hP

/-! ## rubi4542r21Nondeg -/

theorem rubi4542r21Nondeg_real : rubi4542r21Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4542r21Nondeg.conditions rubi4542r21Nondeg.body
    rubi4542r21Nondeg.result rubi4542r21Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r21Nondeg])
  have hn0v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r21Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 3))) (.int 0)) (by simp [rubi4542r21Nondeg])
  have hn2_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "m" + 3 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r21Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  have hb1 : -1 ≤ m := by
    have h := hc (.ge (.var "m") (.int (-1))) (by simp [rubi4542r21Nondeg])
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4542r21Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4542r21Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4542r21Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4542r21Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R,
        Fn.csc] at h hn0 hn2_0 hn2_1 hn2_2 ⊢
    tauto
  · simp only [rubi4542r21Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        (((env "a" * env "C") +
        ((env "b" * ((env "C" * (env "m" + 2)) + (env "A" * (env "m" + 3)))) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹)) +
        (((-1) * (((2 * env "a") * env "C") + ((((-1) * env "b") * env "B") * (env "m" + 3)))) *
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, iv2R, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4542r21Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4542r21Nondeg.result) =
            fun w => ((((((-1) * env "C") * (Real.sin ((env "e" + (env "f" * w))))⁻¹) *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m + 1)) *
            (((env "b" * env "f") * (env "m" + 3)))⁻¹) + (1 * ((env "b" * (env "m" + 3)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4542r21Nondeg, eval, recEnv, Interp.real, em1, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4542r21Nondeg.body =
        (((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2 *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        ((env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) +
        (env "C" * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2)) := by
      simp [rubi4542r21Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hB0⟩ := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        env "C"))).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0)).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t ((((env "b" * env "f") * (env "m" + 3)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply,

      add_sub_cancel_right]
    have hn2_2c : ((m : ℤ) : ℝ) + 3 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (2*env "C"*env "a"*S + 3*env "C"*env "b") * hP
    · have hdm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
        1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (2*env "C"*env "a"^2*env "f"*P*S^2 +
          env "C"*env "a"*env "b"*env "f"*P*S*((m : ℤ) : ℝ) +
          5*env "C"*env "a"*env "b"*env "f"*P*S + env "C"*env "b"^2*env "f"*P*((m : ℤ) : ℝ) +
          3*env "C"*env "b"^2*env "f"*P) * hP

/-! ## rubi4542r22Nondeg -/

theorem rubi4542r22Nondeg_real : rubi4542r22Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4542r22Nondeg.conditions rubi4542r22Nondeg.body
    rubi4542r22Nondeg.result rubi4542r22Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r22Nondeg])
  have hn0v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r22Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 3))) (.int 0)) (by simp [rubi4542r22Nondeg])
  have hn2_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "m" + 3 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r22Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  have hb1 : -1 ≤ m := by
    have h := hc (.ge (.var "m") (.int (-1))) (by simp [rubi4542r22Nondeg])
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4542r22Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4542r22Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4542r22Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4542r22Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R,
        Fn.csc] at h hn0 hn2_0 hn2_1 hn2_2 ⊢
    tauto
  · simp only [rubi4542r22Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        (((env "a" * env "C") +
        ((env "b" * ((env "C" * (env "m" + 2)) + (env "A" * (env "m" + 3)))) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹)) +
        ((((-2) * env "a") * env "C") * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, iv2R, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4542r22Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4542r22Nondeg.result) =
            fun w => ((((((-1) * env "C") * (Real.sin ((env "e" + (env "f" * w))))⁻¹) *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m + 1)) *
            (((env "b" * env "f") * (env "m" + 3)))⁻¹) + (1 * ((env "b" * (env "m" + 3)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4542r22Nondeg, eval, recEnv, Interp.real, em1, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4542r22Nondeg.body =
        (((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2 *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        (env "A" + (env "C" * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2)) := by
      simp [rubi4542r22Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hB0⟩ := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        env "C"))).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0)).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t ((((env "b" * env "f") * (env "m" + 3)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply,

      add_sub_cancel_right]
    have hn2_2c : ((m : ℤ) : ℝ) + 3 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (2*env "C"*env "a"*S + 3*env "C"*env "b") * hP
    · have hdm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
        1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (2*env "C"*env "a"^2*env "f"*P*S^2 +
          env "C"*env "a"*env "b"*env "f"*P*S*((m : ℤ) : ℝ) +
          5*env "C"*env "a"*env "b"*env "f"*P*S + env "C"*env "b"^2*env "f"*P*((m : ℤ) : ℝ) +
          3*env "C"*env "b"^2*env "f"*P) * hP

/-! ## rubi4542r9Nondeg -/

theorem rubi4542r9Nondeg_real : rubi4542r9Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4542r9Nondeg.conditions rubi4542r9Nondeg.body
    rubi4542r9Nondeg.result rubi4542r9Nondeg.integrals
  intro env hc t hF
  have hn1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r9Nondeg])
  have hn1v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r9Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int 0)) (by simp [rubi4542r9Nondeg])
  have hn2_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  have hn2_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  have hn2_2 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r9Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4542r9Nondeg])
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4542r9Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4542r9Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4542r9Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, iv2R, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4542r9Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R,
        Fn.csc] at h hn1 hn2_0 hn2_1 hn2_2 ⊢
    tauto
  · simp only [rubi4542r9Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1)) *
        (((env "b" *
        (((env "a" * env "A") + (((-1) * env "b") * env "B")) + (env "a" * env "C"))) *
        (env "m" + 1)) +
        (((-1) *
        ((((env "A" * (env "b") ^ 2) + ((((-1) * env "a") * env "b") * env "B")) +
        ((env "a") ^ 2 * env "C")) +
        ((env "b" * (((env "A" * env "b") + (((-1) * env "a") * env "B")) + (env "b" * env "C"))) *
        (env "m" + 1)))) * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, iv2R, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4542r9Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4542r9Nondeg.result) =
            fun w => (((((-1) *
            (((env "A" * (env "b") ^ 2) + ((((-1) * env "a") * env "b") * env "B")) +
            ((env "a") ^ 2 * env "C"))) *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m + 1)) *
            ((((env "b" * env "f") * (env "m" + 1)) *
            ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹) +
            (1 * (((env "b" * (env "m" + 1)) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4542r9Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4542r9Nondeg.body =
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        ((env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) +
        (env "C" * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2)) := by
      simp [rubi4542r9Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hB0⟩ := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (((-1) *
        (((env "A" * (env "b") ^ 2) + ((((-1) * env "a") * env "b") * env "B")) +
        ((env "a") ^ 2 *
        env "C"))))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t (((((env "b" * env "f") * (env "m" + 1)) * ((env "a") ^ 2 + ((-1) * (env "b") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply,

      add_sub_cancel_right]
    have hn2_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "A"*env "a"*env "b"^2*S + 2*env "A"*env "b"^3 -
          env "B"*env "a"^2*env "b"*S - 2*env "B"*env "a"*env "b"^2 + env "C"*env "a"^3*S +
          2*env "C"*env "a"^2*env "b") * hP
    · have hdm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
        1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "A"*env "a"^2*env "b"^2*env "f"*P*S^2 +
          env "A"*env "a"*env "b"^3*env "f"*P*S*((m : ℤ) : ℝ) +
          3*env "A"*env "a"*env "b"^3*env "f"*P*S + env "A"*env "b"^4*env "f"*P*((m : ℤ) : ℝ) +
          2*env "A"*env "b"^4*env "f"*P - env "B"*env "a"^3*env "b"*env "f"*P*S^2 -
          env "B"*env "a"^2*env "b"^2*env "f"*P*S*((m : ℤ) : ℝ) -
          3*env "B"*env "a"^2*env "b"^2*env "f"*P*S -
          env "B"*env "a"*env "b"^3*env "f"*P*((m : ℤ) : ℝ) -
          2*env "B"*env "a"*env "b"^3*env "f"*P + env "C"*env "a"^4*env "f"*P*S^2 +
          env "C"*env "a"^3*env "b"*env "f"*P*S*((m : ℤ) : ℝ) +
          3*env "C"*env "a"^3*env "b"*env "f"*P*S +
          env "C"*env "a"^2*env "b"^2*env "f"*P*((m : ℤ) : ℝ) +
          2*env "C"*env "a"^2*env "b"^2*env "f"*P) * hP

end OSR.IntegrationRec278
