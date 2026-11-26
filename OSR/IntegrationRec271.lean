import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: `cos (a + b sin)^m` plus a residual integral

Proofs of RUBI 4.1.2.1 #17, #25 and #27 over ℝ and ℂ: when `a² = b²` and `m < 0` (so `a + b sin ≠ 0`
wherever the integrand is defined),
    the result is an explicit term `K cos (a + b sin)^m [(c + d sin)]`
plus a residual integral with `(a + b sin)^(m + 1)`; the integrand is recovered with
`sin² + cos² = 1` and `a² =
    b²` (`linear_combination` coefficients computed by Gröbner reduction). -/

namespace OSR.IntegrationRec271

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem hasDerivAt_lin {𝕜 : Type} [NontriviallyNormedField 𝕜] (a b t : 𝕜) :
    HasDerivAt (fun w => a + b * w) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

private theorem zsplit {K : Type} [Field K] (X : K) (j : ℤ) (n : ℕ) (h : X ≠ 0 ∨ 0 ≤ j) :
    X ^ (j + n) = X ^ j * X ^ n := by
  rcases h with h | h
  · rw [zpow_add₀ h, zpow_natCast]
  · lift j to ℕ using h
    rw [show ((j : ℤ) + n) = ((j + n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_add]

/-! ## rubi4121r17Nondeg -/

theorem rubi4121r17Nondeg_real : rubi4121r17Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4121r17Nondeg.conditions rubi4121r17Nondeg.body
    rubi4121r17Nondeg.result rubi4121r17Nondeg.integrals
  intro env hc t hF
  have hafm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.app2 .mul (.int 2)
    (.var "m")) (.int 1))) (.int 0)) (by simp [rubi4121r17Nondeg])
  have ha : env "a" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have h2m : 2 * env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hab : env "a" ^ 2 - env "b" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
      (.int 2)))) (.int 0)) (by simp [rubi4121r17Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  have hb : env "b" ≠ 0 := by
    intro h0
    have : env "a" ^ 2 = 0 := by rw [h0] at hab; linear_combination hab
    exact ha ((pow_eq_zero_iff two_ne_zero).1 this)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r17Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hmneg : m < 0 := by
    have h := hc (.gt (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1)))) (.var "m")) (by simp [rubi4121r17Nondeg])
    have h' : env "m" < 0 := by
      simp [Cond.Holds, Defined, eval, Interp.real, ivm1R] at h
      linarith
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4121r17Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r17Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r17Nondeg, Defined, eval, recEnv, Interp.real, hkm, ivm1R, ha, hb, hf, h2m] at h ⊢
    tauto
  · simp only [rubi4121r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m +
        1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4121r17Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r17Nondeg.result) = fun w => (env "b" * env "c" - env "a" * env "d") *
            Real.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Real.sin (env "e" + env "f" * w)) ^ m *
            (env "a" * env "f" * (2 * env "m" + 1))⁻¹ +
            (env "a" * env "d" * env "m" + env "b" * env "c" * (env "m" + 1)) *
            (env "a" * env "b" * (2 * env "m" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4121r17Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi4121r17Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) := by
      simp [rubi4121r17Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    have hAne : env "a" + env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 :=
        hD t hF.self_of_nhds hmneg
    have hS := (Real.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Real.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow m _ (Or.inl hAne)) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def]
    have eA : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m - 1) *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) (m - 1) 1 (Or.inl hAne)
      rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring, pow_one] at this
    have eA2 : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m - 1) *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ 2 := by
      have := zsplit (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) (m - 1) 2 (Or.inl hAne)
      rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
    rw [eA2, eA]
    have h2mc : 2 * ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact h2m
    have h2mc' : ((m : ℤ) : ℝ) * 2 + 1 ≠ 0 := by rw [mul_comm]; exact h2mc
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m - 1) = P
    generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "a"*env "b"^2*env "d"*P*((m : ℤ) : ℝ) +
        env "b"^3*env "c"*P*((m : ℤ) : ℝ)) * hP +
        (env "a"*env "d"*P*((m : ℤ) : ℝ) - env "b"*env "c"*P*((m : ℤ) : ℝ)) * hab

theorem rubi4121r17Nondeg_complex : rubi4121r17Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4121r17Nondeg.conditions rubi4121r17Nondeg.body
    rubi4121r17Nondeg.result rubi4121r17Nondeg.integrals
  intro env hc t hF
  have hafm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.app2 .mul (.int 2)
    (.var "m")) (.int 1))) (.int 0)) (by simp [rubi4121r17Nondeg])
  have ha : env "a" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have h2m : 2 * env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hab : env "a" ^ 2 - env "b" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
      (.int 2)))) (.int 0)) (by simp [rubi4121r17Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  have hb : env "b" ≠ 0 := by
    intro h0
    have : env "a" ^ 2 = 0 := by rw [h0] at hab; linear_combination hab
    exact ha ((pow_eq_zero_iff two_ne_zero).1 this)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r17Nondeg, Defined, eval, Interp.complex, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hmneg : m < 0 := by
    have h := hc (.gt (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1)))) (.var "m")) (by simp [rubi4121r17Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, ivm1C] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (m : ℝ) < 0 := by
      norm_num at h'
      linarith
    exact_mod_cast h''
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4121r17Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r17Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r17Nondeg, Defined, eval, recEnv, Interp.complex, hkm, ivm1C, ha, hb, hf,
        h2m] at h ⊢
    tauto
  · simp only [rubi4121r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ (m + 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4121r17Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r17Nondeg.result) = fun w => (env "b" * env "c" - env "a" * env "d") *
            Complex.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Complex.sin (env "e" + env "f" * w)) ^ m *
            (env "a" * env "f" * (2 * env "m" + 1))⁻¹ +
            (env "a" * env "d" * env "m" + env "b" * env "c" * (env "m" + 1)) *
            (env "a" * env "b" * (2 * env "m" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4121r17Nondeg, eval, recEnv, Interp.complex, hkm, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4121r17Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) := by
      simp [rubi4121r17Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    have hAne : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 :=
        hD t hF.self_of_nhds hmneg
    have hS := (Complex.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Complex.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow m _ (Or.inl hAne)) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def]
    have eA : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m - 1) *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) (m -
          1) 1 (Or.inl hAne)
      rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring, pow_one] at this
    have eA2 : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m - 1) *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ 2 := by
      have := zsplit (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) (m -
          1) 2 (Or.inl hAne)
      rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
    rw [eA2, eA]
    have h2mc : 2 * ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact h2m
    have h2mc' : ((m : ℤ) : ℂ) * 2 + 1 ≠ 0 := by rw [mul_comm]; exact h2mc
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m - 1) = P
    generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "a"*env "b"^2*env "d"*P*((m : ℤ) : ℂ) +
        env "b"^3*env "c"*P*((m : ℤ) : ℂ)) * hP +
        (env "a"*env "d"*P*((m : ℤ) : ℂ) - env "b"*env "c"*P*((m : ℤ) : ℂ)) * hab

/-! ## rubi4121r25Nondeg -/

theorem rubi4121r25Nondeg_real : rubi4121r25Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4121r25Nondeg.conditions rubi4121r25Nondeg.body
    rubi4121r25Nondeg.result rubi4121r25Nondeg.integrals
  intro env hc t hF
  have hafm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.app2 .mul (.int 2)
    (.var "m")) (.int 1))) (.int 0)) (by simp [rubi4121r25Nondeg])
  have ha : env "a" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have h2m : 2 * env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hab : env "a" ^ 2 - env "b" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
      (.int 2)))) (.int 0)) (by simp [rubi4121r25Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  have hb : env "b" ≠ 0 := by
    intro h0
    have : env "a" ^ 2 = 0 := by rw [h0] at hab; linear_combination hab
    exact ha ((pow_eq_zero_iff two_ne_zero).1 this)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r25Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hmneg : m < 0 := by
    have h := hc (.gt (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1)))) (.var "m")) (by simp [rubi4121r25Nondeg])
    have h' : env "m" < 0 := by
      simp [Cond.Holds, Defined, eval, Interp.real, ivm1R] at h
      linarith
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4121r25Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r25Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r25Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r25Nondeg, Defined, eval, recEnv, Interp.real, hkm, ivm1R, iv2R, ha, hf,
        h2m] at h ⊢
    tauto
  · simp only [rubi4121r25Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m +
        1) * (env "a" * env "m" - env "b" * (2 * env "m" + 1) *
        Real.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, sub_eq_add_neg, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4121r25Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r25Nondeg.result) = fun w => env "b" * Real.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Real.sin (env "e" + env "f" * w)) ^ m *
            (env "a" * env "f" * (2 * env "m" + 1))⁻¹ + -(env "a" ^ 2 * (2 * env "m" + 1))⁻¹ *
            Φ "I1" w := by
      funext w
      simp [rubi4121r25Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4121r25Nondeg.body =
        (Real.sin (env "e" + env "f" * t)) ^ 2 *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m := by
      simp [rubi4121r25Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hAne : env "a" + env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 :=
        hD t hF.self_of_nhds hmneg
    have hS := (Real.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Real.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow m _ (Or.inl hAne)) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def]
    have eA : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m - 1) *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) (m - 1) 1 (Or.inl hAne)
      rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring, pow_one] at this
    have eA2 : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m - 1) *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ 2 := by
      have := zsplit (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) (m - 1) 2 (Or.inl hAne)
      rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
    rw [eA2, eA]
    have h2mc : 2 * ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact h2m
    have h2mc' : ((m : ℤ) : ℝ) * 2 + 1 ≠ 0 := by rw [mul_comm]; exact h2mc
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m - 1) = P
    generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (env "a"*env "b"^2*P*((m : ℤ) : ℝ)) * hP +
        (-2*env "a"*P*S^2*((m : ℤ) : ℝ) - env "a"*P*S^2 - env "a"*P*((m : ℤ) : ℝ) -
        2*env "b"*P*S^3*((m : ℤ) : ℝ) - env "b"*P*S^3) * hab

theorem rubi4121r25Nondeg_complex : rubi4121r25Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4121r25Nondeg.conditions rubi4121r25Nondeg.body
    rubi4121r25Nondeg.result rubi4121r25Nondeg.integrals
  intro env hc t hF
  have hafm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.app2 .mul (.int 2)
    (.var "m")) (.int 1))) (.int 0)) (by simp [rubi4121r25Nondeg])
  have ha : env "a" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have h2m : 2 * env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hab : env "a" ^ 2 - env "b" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
      (.int 2)))) (.int 0)) (by simp [rubi4121r25Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  have hb : env "b" ≠ 0 := by
    intro h0
    have : env "a" ^ 2 = 0 := by rw [h0] at hab; linear_combination hab
    exact ha ((pow_eq_zero_iff two_ne_zero).1 this)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r25Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hmneg : m < 0 := by
    have h := hc (.gt (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1)))) (.var "m")) (by simp [rubi4121r25Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, ivm1C] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (m : ℝ) < 0 := by
      norm_num at h'
      linarith
    exact_mod_cast h''
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4121r25Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r25Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r25Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r25Nondeg, Defined, eval, recEnv, Interp.complex, hkm, ivm1C, iv2C, ha, hf,
        h2m] at h ⊢
    tauto
  · simp only [rubi4121r25Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ (m + 1) *
        (env "a" * env "m" - env "b" * (2 * env "m" + 1) *
        Complex.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, sub_eq_add_neg, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4121r25Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r25Nondeg.result) = fun w => env "b" * Complex.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Complex.sin (env "e" + env "f" * w)) ^ m *
            (env "a" * env "f" * (2 * env "m" + 1))⁻¹ + -(env "a" ^ 2 * (2 * env "m" + 1))⁻¹ *
            Φ "I1" w := by
      funext w
      simp [rubi4121r25Nondeg, eval, recEnv, Interp.complex, hkm, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4121r25Nondeg.body =
        (Complex.sin (env "e" + env "f" * t)) ^ 2 *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m := by
      simp [rubi4121r25Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    have hAne : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 :=
        hD t hF.self_of_nhds hmneg
    have hS := (Complex.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Complex.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow m _ (Or.inl hAne)) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def]
    have eA : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m - 1) *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) (m -
          1) 1 (Or.inl hAne)
      rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring, pow_one] at this
    have eA2 : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m - 1) *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ 2 := by
      have := zsplit (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) (m -
          1) 2 (Or.inl hAne)
      rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
    rw [eA2, eA]
    have h2mc : 2 * ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact h2m
    have h2mc' : ((m : ℤ) : ℂ) * 2 + 1 ≠ 0 := by rw [mul_comm]; exact h2mc
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m - 1) = P
    generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (env "a"*env "b"^2*P*((m : ℤ) : ℂ)) * hP +
        (-2*env "a"*P*S^2*((m : ℤ) : ℂ) - env "a"*P*S^2 - env "a"*P*((m : ℤ) : ℂ) -
        2*env "b"*P*S^3*((m : ℤ) : ℂ) - env "b"*P*S^3) * hab

/-! ## rubi4121r27Nondeg -/

theorem rubi4121r27Nondeg_real : rubi4121r27Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4121r27Nondeg.conditions rubi4121r27Nondeg.body
    rubi4121r27Nondeg.result rubi4121r27Nondeg.integrals
  intro env hc t hF
  have hafm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.app2 .mul (.int 2)
    (.var "m")) (.int 1))) (.int 0)) (by simp [rubi4121r27Nondeg])
  have ha : env "a" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have h2m : 2 * env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hab : env "a" ^ 2 - env "b" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
      (.int 2)))) (.int 0)) (by simp [rubi4121r27Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  have hb : env "b" ≠ 0 := by
    intro h0
    have : env "a" ^ 2 = 0 := by rw [h0] at hab; linear_combination hab
    exact ha ((pow_eq_zero_iff two_ne_zero).1 this)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r27Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hmneg : m < 0 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4121r27Nondeg])
    have h' : env "m" < 0 := by
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4121r27Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r27Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r27Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r27Nondeg, Defined, eval, recEnv, Interp.real, hkm, ivm1R, ha, hb, hf, h2m] at h ⊢
    tauto
  · simp only [rubi4121r27Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m +
        1) * (env "a" * env "c" * env "d" * (env "m" - 1) + env "b" *
        (env "d" ^ 2 + env "c" ^ 2 * (env "m" + 1)) + env "d" *
        (env "a" * env "d" * (env "m" - 1) + env "b" * env "c" * (env "m" + 2)) *
        Real.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4121r27Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r27Nondeg.result) = fun w => (env "b" * env "c" - env "a" * env "d") *
            Real.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Real.sin (env "e" + env "f" * w)) ^ m *
            (env "c" + env "d" * Real.sin (env "e" + env "f" * w)) *
            (env "a" * env "f" * (2 * env "m" + 1))⁻¹ + (env "a" * env "b" * (2 * env "m" + 1))⁻¹ *
            Φ "I1" w := by
      funext w
      simp [rubi4121r27Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi4121r27Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ 2 := by
      simp [rubi4121r27Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hAne : env "a" + env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 :=
        hD t hF.self_of_nhds hmneg
    have hS := (Real.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Real.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow m _ (Or.inl hAne)) hA
    have hCl := (hS.const_mul (env "d")).const_add (env "c")
    refine (((((hCd.const_mul _).mul hAp).mul hCl).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply]
    have eA : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m - 1) *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) (m - 1) 1 (Or.inl hAne)
      rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring, pow_one] at this
    have eA2 : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m - 1) *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ 2 := by
      have := zsplit (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) (m - 1) 2 (Or.inl hAne)
      rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
    rw [eA2, eA]
    have h2mc : 2 * ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact h2m
    have h2mc' : ((m : ℤ) : ℝ) * 2 + 1 ≠ 0 := by rw [mul_comm]; exact h2mc
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m - 1) = P
    generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "a"^2*env "b"*env "d"^2*P -
        env "a"*env "b"^2*env "c"*env "d"*P*((m : ℤ) : ℝ) + env "a"*env "b"^2*env "c"*env "d"*P -
        env "a"*env "b"^2*env "d"^2*P*S*((m : ℤ) : ℝ) - env "a"*env "b"^2*env "d"^2*P*S +
        env "b"^3*env "c"^2*P*((m : ℤ) : ℝ) + env "b"^3*env "c"*env "d"*P*S*((m : ℤ) : ℝ) +
        env "b"^3*env "c"*env "d"*P*S) * hP +
        (env "a"*env "c"*env "d"*P*((m : ℤ) : ℝ) - env "a"*env "c"*env "d"*P +
        env "a"*env "d"^2*P*S*((m : ℤ) : ℝ) - env "a"*env "d"^2*P*S -
        env "b"*env "c"^2*P*((m : ℤ) : ℝ) - env "b"*env "c"*env "d"*P*S*((m : ℤ) : ℝ) -
        env "b"*env "c"*env "d"*P*S - env "b"*env "d"^2*P*S^2) * hab

theorem rubi4121r27Nondeg_complex : rubi4121r27Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4121r27Nondeg.conditions rubi4121r27Nondeg.body
    rubi4121r27Nondeg.result rubi4121r27Nondeg.integrals
  intro env hc t hF
  have hafm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.app2 .mul (.int 2)
    (.var "m")) (.int 1))) (.int 0)) (by simp [rubi4121r27Nondeg])
  have ha : env "a" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have h2m : 2 * env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hab : env "a" ^ 2 - env "b" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
      (.int 2)))) (.int 0)) (by simp [rubi4121r27Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  have hb : env "b" ≠ 0 := by
    intro h0
    have : env "a" ^ 2 = 0 := by rw [h0] at hab; linear_combination hab
    exact ha ((pow_eq_zero_iff two_ne_zero).1 this)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r27Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hmneg : m < 0 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4121r27Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (m : ℝ) < 0 := by
      norm_num at h'
      linarith
    exact_mod_cast h''
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4121r27Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r27Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r27Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r27Nondeg, Defined, eval, recEnv, Interp.complex, hkm, ivm1C, ha, hb, hf,
        h2m] at h ⊢
    tauto
  · simp only [rubi4121r27Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ (m + 1) *
        (env "a" * env "c" * env "d" * (env "m" - 1) + env "b" *
        (env "d" ^ 2 + env "c" ^ 2 * (env "m" + 1)) + env "d" *
        (env "a" * env "d" * (env "m" - 1) + env "b" * env "c" * (env "m" + 2)) *
        Complex.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4121r27Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r27Nondeg.result) = fun w => (env "b" * env "c" - env "a" * env "d") *
            Complex.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Complex.sin (env "e" + env "f" * w)) ^ m *
            (env "c" + env "d" * Complex.sin (env "e" + env "f" * w)) *
            (env "a" * env "f" * (2 * env "m" + 1))⁻¹ + (env "a" * env "b" * (2 * env "m" + 1))⁻¹ *
            Φ "I1" w := by
      funext w
      simp [rubi4121r27Nondeg, eval, recEnv, Interp.complex, hkm, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4121r27Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ 2 := by
      simp [rubi4121r27Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    have hAne : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 :=
        hD t hF.self_of_nhds hmneg
    have hS := (Complex.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Complex.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow m _ (Or.inl hAne)) hA
    have hCl := (hS.const_mul (env "d")).const_add (env "c")
    refine (((((hCd.const_mul _).mul hAp).mul hCl).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply]
    have eA : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m - 1) *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) (m -
          1) 1 (Or.inl hAne)
      rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring, pow_one] at this
    have eA2 : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m - 1) *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ 2 := by
      have := zsplit (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) (m -
          1) 2 (Or.inl hAne)
      rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
    rw [eA2, eA]
    have h2mc : 2 * ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact h2m
    have h2mc' : ((m : ℤ) : ℂ) * 2 + 1 ≠ 0 := by rw [mul_comm]; exact h2mc
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m - 1) = P
    generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "a"^2*env "b"*env "d"^2*P -
        env "a"*env "b"^2*env "c"*env "d"*P*((m : ℤ) : ℂ) + env "a"*env "b"^2*env "c"*env "d"*P -
        env "a"*env "b"^2*env "d"^2*P*S*((m : ℤ) : ℂ) - env "a"*env "b"^2*env "d"^2*P*S +
        env "b"^3*env "c"^2*P*((m : ℤ) : ℂ) + env "b"^3*env "c"*env "d"*P*S*((m : ℤ) : ℂ) +
        env "b"^3*env "c"*env "d"*P*S) * hP +
        (env "a"*env "c"*env "d"*P*((m : ℤ) : ℂ) - env "a"*env "c"*env "d"*P +
        env "a"*env "d"^2*P*S*((m : ℤ) : ℂ) - env "a"*env "d"^2*P*S -
        env "b"*env "c"^2*P*((m : ℤ) : ℂ) - env "b"*env "c"*env "d"*P*S*((m : ℤ) : ℂ) -
        env "b"*env "c"*env "d"*P*S - env "b"*env "d"^2*P*S^2) * hab

end OSR.IntegrationRec271
