import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: `cos (a + b sin)^m` plus a residual integral

Proofs of RUBI 4.1.4.1 #10 and #11 over ℝ and ℂ: when `a² = b²` and `m < 0` (so `a + b sin ≠ 0`
wherever the integrand is defined),
    the result is an explicit term `K cos (a + b sin)^m [(c + d sin)]`
plus a residual integral with `(a + b sin)^(m + 1)`; the integrand is recovered with
`sin² + cos² = 1` and `a² =
    b²` (`linear_combination` coefficients computed by Gröbner reduction). -/

namespace OSR.IntegrationRec273

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

/-! ## rubi4141r10Nondeg -/

theorem rubi4141r10Nondeg_real : rubi4141r10Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4141r10Nondeg.conditions rubi4141r10Nondeg.body
    rubi4141r10Nondeg.result rubi4141r10Nondeg.integrals
  intro env hc t hF
  have hafm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.app2 .mul (.int 2)
    (.var "m")) (.int 1))) (.int 0)) (by simp [rubi4141r10Nondeg])
  have ha : env "a" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have h2m : 2 * env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hab : env "a" ^ 2 - env "b" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
      (.int 2)))) (.int 0)) (by simp [rubi4141r10Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  have hb : env "b" ≠ 0 := by
    intro h0
    have : env "a" ^ 2 = 0 := by rw [h0] at hab; linear_combination hab
    exact ha ((pow_eq_zero_iff two_ne_zero).1 this)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r10Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hmneg : m < 0 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4141r10Nondeg])
    have h' : env "m" < 0 := by
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4141r10Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r10Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4141r10Nondeg, Defined, eval, recEnv, Interp.real, hkm, ivm1R, iv2R, ha, hf,
        h2m] at h ⊢
    tauto
  · simp only [rubi4141r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m +
        1) * (env "a" * env "A" * (env "m" + 1) + env "m" *
        (env "b" * env "B" - env "a" * env "C") + env "b" * env "C" * (2 * env "m" + 1) *
        Real.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, sub_eq_add_neg, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4141r10Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r10Nondeg.result) =
            fun w => (env "A" * env "b" - env "a" * env "B" + env "b" * env "C") *
            Real.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Real.sin (env "e" + env "f" * w)) ^ m *
            (env "a" * env "f" * (2 * env "m" + 1))⁻¹ + (env "a" ^ 2 * (2 * env "m" + 1))⁻¹ *
            Φ "I1" w := by
      funext w
      simp [rubi4141r10Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi4141r10Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "B" * Real.sin (env "e" + env "f" * t) + env "C" *
        (Real.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4141r10Nondeg, eval, Interp.real, hkm, iv2R]
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
    linear_combination (env "A"*env "a"*env "b"^2*P*((m : ℤ) : ℝ) -
        env "B"*env "a"^2*env "b"*P*((m : ℤ) : ℝ) + env "C"*env "a"*env "b"^2*P*((m : ℤ) : ℝ)) *
        hP + (-env "A"*env "a"*P*((m : ℤ) : ℝ) - 2*env "B"*env "a"*P*S*((m : ℤ) : ℝ) -
        env "B"*env "b"*P*S^2*((m : ℤ) : ℝ) - 2*env "C"*env "a"*P*S^2*((m : ℤ) : ℝ) -
        env "C"*env "a"*P*S^2 - env "C"*env "a"*P*((m : ℤ) : ℝ) -
        2*env "C"*env "b"*P*S^3*((m : ℤ) : ℝ) - env "C"*env "b"*P*S^3) * hab

theorem rubi4141r10Nondeg_complex : rubi4141r10Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4141r10Nondeg.conditions rubi4141r10Nondeg.body
    rubi4141r10Nondeg.result rubi4141r10Nondeg.integrals
  intro env hc t hF
  have hafm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.app2 .mul (.int 2)
    (.var "m")) (.int 1))) (.int 0)) (by simp [rubi4141r10Nondeg])
  have ha : env "a" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have h2m : 2 * env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hab : env "a" ^ 2 - env "b" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
      (.int 2)))) (.int 0)) (by simp [rubi4141r10Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  have hb : env "b" ≠ 0 := by
    intro h0
    have : env "a" ^ 2 = 0 := by rw [h0] at hab; linear_combination hab
    exact ha ((pow_eq_zero_iff two_ne_zero).1 this)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r10Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hmneg : m < 0 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4141r10Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (m : ℝ) < 0 := by
      norm_num at h'
      linarith
    exact_mod_cast h''
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4141r10Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r10Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4141r10Nondeg, Defined, eval, recEnv, Interp.complex, hkm, ivm1C, iv2C, ha, hf,
        h2m] at h ⊢
    tauto
  · simp only [rubi4141r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ (m + 1) *
        (env "a" * env "A" * (env "m" + 1) + env "m" * (env "b" * env "B" - env "a" * env "C") +
        env "b" * env "C" * (2 * env "m" + 1) * Complex.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, sub_eq_add_neg, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4141r10Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r10Nondeg.result) =
            fun w => (env "A" * env "b" - env "a" * env "B" + env "b" * env "C") *
            Complex.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Complex.sin (env "e" + env "f" * w)) ^ m *
            (env "a" * env "f" * (2 * env "m" + 1))⁻¹ + (env "a" ^ 2 * (2 * env "m" + 1))⁻¹ *
            Φ "I1" w := by
      funext w
      simp [rubi4141r10Nondeg, eval, recEnv, Interp.complex, hkm, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4141r10Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "B" * Complex.sin (env "e" + env "f" * t) + env "C" *
        (Complex.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4141r10Nondeg, eval, Interp.complex, hkm, iv2C]
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
    linear_combination (env "A"*env "a"*env "b"^2*P*((m : ℤ) : ℂ) -
        env "B"*env "a"^2*env "b"*P*((m : ℤ) : ℂ) + env "C"*env "a"*env "b"^2*P*((m : ℤ) : ℂ)) *
        hP + (-env "A"*env "a"*P*((m : ℤ) : ℂ) - 2*env "B"*env "a"*P*S*((m : ℤ) : ℂ) -
        env "B"*env "b"*P*S^2*((m : ℤ) : ℂ) - 2*env "C"*env "a"*P*S^2*((m : ℤ) : ℂ) -
        env "C"*env "a"*P*S^2 - env "C"*env "a"*P*((m : ℤ) : ℂ) -
        2*env "C"*env "b"*P*S^3*((m : ℤ) : ℂ) - env "C"*env "b"*P*S^3) * hab

/-! ## rubi4141r11Nondeg -/

theorem rubi4141r11Nondeg_real : rubi4141r11Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4141r11Nondeg.conditions rubi4141r11Nondeg.body
    rubi4141r11Nondeg.result rubi4141r11Nondeg.integrals
  intro env hc t hF
  have hafm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.app2 .mul (.int 2)
    (.var "m")) (.int 1))) (.int 0)) (by simp [rubi4141r11Nondeg])
  have ha : env "a" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have h2m : 2 * env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hab : env "a" ^ 2 - env "b" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
      (.int 2)))) (.int 0)) (by simp [rubi4141r11Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  have hb : env "b" ≠ 0 := by
    intro h0
    have : env "a" ^ 2 = 0 := by rw [h0] at hab; linear_combination hab
    exact ha ((pow_eq_zero_iff two_ne_zero).1 this)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r11Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hmneg : m < 0 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4141r11Nondeg])
    have h' : env "m" < 0 := by
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4141r11Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r11Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r11Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4141r11Nondeg, Defined, eval, recEnv, Interp.real, hkm, ivm1R, iv2R, ha, hf,
        h2m] at h ⊢
    tauto
  · simp only [rubi4141r11Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m +
        1) * (env "a" * env "A" * (env "m" + 1) - env "a" * env "C" * env "m" + env "b" * env "C" *
        (2 * env "m" + 1) * Real.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, sub_eq_add_neg, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4141r11Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r11Nondeg.result) = fun w => env "b" * (env "A" + env "C") *
            Real.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Real.sin (env "e" + env "f" * w)) ^ m *
            (env "a" * env "f" * (2 * env "m" + 1))⁻¹ + (env "a" ^ 2 * (2 * env "m" + 1))⁻¹ *
            Φ "I1" w := by
      funext w
      simp [rubi4141r11Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4141r11Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "C" * (Real.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4141r11Nondeg, eval, Interp.real, hkm, iv2R]
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
    linear_combination (env "A"*env "a"*env "b"^2*P*((m : ℤ) : ℝ) +
        env "C"*env "a"*env "b"^2*P*((m : ℤ) : ℝ)) * hP +
        (-env "A"*env "a"*P*((m : ℤ) : ℝ) - 2*env "C"*env "a"*P*S^2*((m : ℤ) : ℝ) -
        env "C"*env "a"*P*S^2 - env "C"*env "a"*P*((m : ℤ) : ℝ) -
        2*env "C"*env "b"*P*S^3*((m : ℤ) : ℝ) - env "C"*env "b"*P*S^3) * hab

theorem rubi4141r11Nondeg_complex : rubi4141r11Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4141r11Nondeg.conditions rubi4141r11Nondeg.body
    rubi4141r11Nondeg.result rubi4141r11Nondeg.integrals
  intro env hc t hF
  have hafm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.app2 .mul (.int 2)
    (.var "m")) (.int 1))) (.int 0)) (by simp [rubi4141r11Nondeg])
  have ha : env "a" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have h2m : 2 * env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hafm
  have hab : env "a" ^ 2 - env "b" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
      (.int 2)))) (.int 0)) (by simp [rubi4141r11Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  have hb : env "b" ≠ 0 := by
    intro h0
    have : env "a" ^ 2 = 0 := by rw [h0] at hab; linear_combination hab
    exact ha ((pow_eq_zero_iff two_ne_zero).1 this)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r11Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hmneg : m < 0 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi4141r11Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (m : ℝ) < 0 := by
      norm_num at h'
      linarith
    exact_mod_cast h''
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4141r11Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r11Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r11Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4141r11Nondeg, Defined, eval, recEnv, Interp.complex, hkm, ivm1C, iv2C, ha, hf,
        h2m] at h ⊢
    tauto
  · simp only [rubi4141r11Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ (m + 1) *
        (env "a" * env "A" * (env "m" + 1) - env "a" * env "C" * env "m" + env "b" * env "C" *
        (2 * env "m" + 1) * Complex.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, sub_eq_add_neg, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4141r11Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r11Nondeg.result) = fun w => env "b" * (env "A" + env "C") *
            Complex.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Complex.sin (env "e" + env "f" * w)) ^ m *
            (env "a" * env "f" * (2 * env "m" + 1))⁻¹ + (env "a" ^ 2 * (2 * env "m" + 1))⁻¹ *
            Φ "I1" w := by
      funext w
      simp [rubi4141r11Nondeg, eval, recEnv, Interp.complex, hkm, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4141r11Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "A" + env "C" * (Complex.sin (env "e" + env "f" * t)) ^ 2) := by
      simp [rubi4141r11Nondeg, eval, Interp.complex, hkm, iv2C]
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
    linear_combination (env "A"*env "a"*env "b"^2*P*((m : ℤ) : ℂ) +
        env "C"*env "a"*env "b"^2*P*((m : ℤ) : ℂ)) * hP +
        (-env "A"*env "a"*P*((m : ℤ) : ℂ) - 2*env "C"*env "a"*P*S^2*((m : ℤ) : ℂ) -
        env "C"*env "a"*P*S^2 - env "C"*env "a"*P*((m : ℤ) : ℂ) -
        2*env "C"*env "b"*P*S^3*((m : ℤ) : ℂ) - env "C"*env "b"*P*S^3) * hab

end OSR.IntegrationRec273
