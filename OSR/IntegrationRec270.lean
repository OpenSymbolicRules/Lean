import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: `cos (a + b sin)^(m + 1)` plus a residual integral

Proofs of RUBI 4.1.2.1 #26, #28, #57 and #58 over ℝ and ℂ: the result is an explicit term
`K cos (a + b sin)^(m + 1)` plus a residual integral; the derivative of the explicit term is
`K f (a + b sin)^m (-(a + b sin) sin + (m + 1) b cos²)`, and the integrand is recovered with
`sin² + cos² = 1` (`linear_combination` coefficients computed by Gröbner reduction). -/

namespace OSR.IntegrationRec270

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

/-! ## rubi4121r26Nondeg -/

theorem rubi4121r26Nondeg_real : rubi4121r26Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4121r26Nondeg.conditions rubi4121r26Nondeg.body
    rubi4121r26Nondeg.result rubi4121r26Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 2)))
    (.int 0)) (by simp [rubi4121r26Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hm2 : env "m" + 2 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r26Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4121r26Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r26Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r26Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r26Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, hb, hf, hm2] at h ⊢
    tauto
  · simp only [rubi4121r26Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "b" * (env "m" + 1) - env "a" * Real.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, sub_eq_add_neg, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4121r26Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r26Nondeg.result) = fun w => -1 * Real.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Real.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 2))⁻¹ + (env "b" * (env "m" + 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4121r26Nondeg, eval, recEnv, Interp.real, em1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4121r26Nondeg.body =
        (Real.sin (env "e" + env "f" * t)) ^ 2 *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m := by
      simp [rubi4121r26Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Real.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Real.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hdisj : env "a" + env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "a" + env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hm2c : ((m : ℤ) : ℝ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hm2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m = P
    generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "b"*P*((m : ℤ) : ℝ) - env "b"*P) * hP

theorem rubi4121r26Nondeg_complex : rubi4121r26Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4121r26Nondeg.conditions rubi4121r26Nondeg.body
    rubi4121r26Nondeg.result rubi4121r26Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 2)))
    (.int 0)) (by simp [rubi4121r26Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hm2 : env "m" + 2 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r26Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4121r26Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r26Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r26Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r26Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, hb, hf, hm2] at h ⊢
    tauto
  · simp only [rubi4121r26Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "b" * (env "m" + 1) - env "a" * Complex.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, sub_eq_add_neg, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4121r26Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r26Nondeg.result) = fun w => -1 * Complex.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Complex.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 2))⁻¹ + (env "b" * (env "m" + 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4121r26Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4121r26Nondeg.body =
        (Complex.sin (env "e" + env "f" * t)) ^ 2 *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m := by
      simp [rubi4121r26Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Complex.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Complex.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hdisj : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hm2c : ((m : ℤ) : ℂ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hm2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = P
    generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "b"*P*((m : ℤ) : ℂ) - env "b"*P) * hP

/-! ## rubi4121r28Nondeg -/

theorem rubi4121r28Nondeg_real : rubi4121r28Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4121r28Nondeg.conditions rubi4121r28Nondeg.body
    rubi4121r28Nondeg.result rubi4121r28Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 2)))
    (.int 0)) (by simp [rubi4121r28Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hm2 : env "m" + 2 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r28Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4121r28Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r28Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r28Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r28Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R, hb, hf,
        hm2] at h ⊢
    tauto
  · simp only [rubi4121r28Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "b" * (env "d" ^ 2 * (env "m" + 1) + env "c" ^ 2 * (env "m" + 2)) - env "d" *
        (env "a" * env "d" - 2 * env "b" * env "c" * (env "m" + 2)) *
        Real.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4121r28Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r28Nondeg.result) = fun w => -(env "d" ^ 2) *
            Real.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Real.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 2))⁻¹ + (env "b" * (env "m" + 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4121r28Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4121r28Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ 2 := by
      simp [rubi4121r28Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Real.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Real.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hdisj : env "a" + env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "a" + env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hm2c : ((m : ℤ) : ℝ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hm2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m = P
    generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "b"*env "d"^2*P*((m : ℤ) : ℝ) - env "b"*env "d"^2*P) * hP

theorem rubi4121r28Nondeg_complex : rubi4121r28Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4121r28Nondeg.conditions rubi4121r28Nondeg.body
    rubi4121r28Nondeg.result rubi4121r28Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 2)))
    (.int 0)) (by simp [rubi4121r28Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hm2 : env "m" + 2 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r28Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4121r28Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r28Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r28Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r28Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, hb, hf,
        hm2] at h ⊢
    tauto
  · simp only [rubi4121r28Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "b" * (env "d" ^ 2 * (env "m" + 1) + env "c" ^ 2 * (env "m" + 2)) - env "d" *
        (env "a" * env "d" - 2 * env "b" * env "c" * (env "m" + 2)) *
        Complex.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4121r28Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r28Nondeg.result) = fun w => -(env "d" ^ 2) *
            Complex.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Complex.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 2))⁻¹ + (env "b" * (env "m" + 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4121r28Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4121r28Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ 2 := by
      simp [rubi4121r28Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Complex.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Complex.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hdisj : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hm2c : ((m : ℤ) : ℂ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hm2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = P
    generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "b"*env "d"^2*P*((m : ℤ) : ℂ) - env "b"*env "d"^2*P) * hP

/-! ## rubi4121r58Nondeg -/

theorem rubi4121r58Nondeg_real : rubi4121r58Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4121r58Nondeg.conditions rubi4121r58Nondeg.body
    rubi4121r58Nondeg.result rubi4121r58Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 2)))
    (.int 0)) (by simp [rubi4121r58Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hm2 : env "m" + 2 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r58Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4121r58Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r58Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r58Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r58Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R, hb, hf,
        hm2] at h ⊢
    tauto
  · simp only [rubi4121r58Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "b" * (env "d" ^ 2 * (env "m" + 1) + env "c" ^ 2 * (env "m" + 2)) - env "d" *
        (env "a" * env "d" - 2 * env "b" * env "c" * (env "m" + 2)) *
        Real.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4121r58Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r58Nondeg.result) = fun w => -(env "d" ^ 2) *
            Real.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Real.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 2))⁻¹ + (env "b" * (env "m" + 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4121r58Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4121r58Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ 2 := by
      simp [rubi4121r58Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Real.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Real.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hdisj : env "a" + env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "a" + env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hm2c : ((m : ℤ) : ℝ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hm2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m = P
    generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "b"*env "d"^2*P*((m : ℤ) : ℝ) - env "b"*env "d"^2*P) * hP

theorem rubi4121r58Nondeg_complex : rubi4121r58Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4121r58Nondeg.conditions rubi4121r58Nondeg.body
    rubi4121r58Nondeg.result rubi4121r58Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 2)))
    (.int 0)) (by simp [rubi4121r58Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hm2 : env "m" + 2 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r58Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4121r58Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r58Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r58Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r58Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, hb, hf,
        hm2] at h ⊢
    tauto
  · simp only [rubi4121r58Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "b" * (env "d" ^ 2 * (env "m" + 1) + env "c" ^ 2 * (env "m" + 2)) - env "d" *
        (env "a" * env "d" - 2 * env "b" * env "c" * (env "m" + 2)) *
        Complex.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4121r58Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r58Nondeg.result) = fun w => -(env "d" ^ 2) *
            Complex.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Complex.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 2))⁻¹ + (env "b" * (env "m" + 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4121r58Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4121r58Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ 2 := by
      simp [rubi4121r58Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Complex.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Complex.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hdisj : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hm2c : ((m : ℤ) : ℂ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hm2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = P
    generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "b"*env "d"^2*P*((m : ℤ) : ℂ) - env "b"*env "d"^2*P) * hP

/-! ## rubi4121r57Nondeg -/

theorem rubi4121r57Nondeg_real : rubi4121r57Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4121r57Nondeg.conditions rubi4121r57Nondeg.body
    rubi4121r57Nondeg.result rubi4121r57Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m")
    (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
    (.int 2))))) (.int 0)) (by simp [rubi4121r57Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hm1' : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hab : env "a" ^ 2 - env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
      (.int 2)))) (.int 0)) (by simp [rubi4121r57Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r57Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4121r57Nondeg.body →
      (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r57Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r57Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r57Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R, hb, hf,
        hm1'] at h ⊢
    tauto
  · simp only [rubi4121r57Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m +
        1) * (env "b" * (env "m" + 1) *
        (2 * env "b" * env "c" * env "d" - env "a" * (env "c" ^ 2 + env "d" ^ 2)) +
        (env "a" ^ 2 * env "d" ^ 2 - 2 * env "a" * env "b" * env "c" * env "d" * (env "m" + 2) +
        env "b" ^ 2 * (env "d" ^ 2 * (env "m" + 1) + env "c" ^ 2 * (env "m" + 2))) *
        Real.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4121r57Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r57Nondeg.result) =
            fun w => -(env "b" ^ 2 * env "c" ^ 2 - 2 * env "a" * env "b" * env "c" * env "d" +
            env "a" ^ 2 * env "d" ^ 2) * Real.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Real.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 1) * (env "a" ^ 2 - env "b" ^ 2))⁻¹ +
            -(env "b" * (env "m" + 1) * (env "a" ^ 2 - env "b" ^ 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4121r57Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi4121r57Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ 2 := by
      simp [rubi4121r57Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Real.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Real.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hdisj : env "a" + env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "a" + env "b" * Real.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hm1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hm1'
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m = P
    generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "a"^2*env "b"*env "d"^2*P*((m : ℤ) : ℝ) -
        env "a"^2*env "b"*env "d"^2*P + 2*env "a"*env "b"^2*env "c"*env "d"*P*((m : ℤ) : ℝ) +
        2*env "a"*env "b"^2*env "c"*env "d"*P - env "b"^3*env "c"^2*P*((m : ℤ) : ℝ) -
        env "b"^3*env "c"^2*P) * hP

theorem rubi4121r57Nondeg_complex : rubi4121r57Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4121r57Nondeg.conditions rubi4121r57Nondeg.body
    rubi4121r57Nondeg.result rubi4121r57Nondeg.integrals
  intro env hc t hF
  have hbfm :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m")
    (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
    (.int 2))))) (.int 0)) (by simp [rubi4121r57Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hm1' : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hab : env "a" ^ 2 - env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b")
      (.int 2)))) (.int 0)) (by simp [rubi4121r57Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r57Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4121r57Nondeg.body →
      (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r57Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r57Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r57Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, hb, hf,
        hm1'] at h ⊢
    tauto
  · simp only [rubi4121r57Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ (m + 1) *
        (env "b" * (env "m" + 1) *
        (2 * env "b" * env "c" * env "d" - env "a" * (env "c" ^ 2 + env "d" ^ 2)) +
        (env "a" ^ 2 * env "d" ^ 2 - 2 * env "a" * env "b" * env "c" * env "d" * (env "m" + 2) +
        env "b" ^ 2 * (env "d" ^ 2 * (env "m" + 1) + env "c" ^ 2 * (env "m" + 2))) *
        Complex.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4121r57Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r57Nondeg.result) =
            fun w => -(env "b" ^ 2 * env "c" ^ 2 - 2 * env "a" * env "b" * env "c" * env "d" +
            env "a" ^ 2 * env "d" ^ 2) * Complex.cos (env "e" + env "f" * w) *
            (env "a" + env "b" * Complex.sin (env "e" + env "f" * w)) ^ (m + 1) *
            (env "b" * env "f" * (env "m" + 1) * (env "a" ^ 2 - env "b" ^ 2))⁻¹ +
            -(env "b" * (env "m" + 1) * (env "a" ^ 2 - env "b" ^ 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4121r57Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4121r57Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ 2 := by
      simp [rubi4121r57Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    have hA0 := hD t hF.self_of_nhds
    have hS := (Complex.hasDerivAt_sin _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hCd := (Complex.hasDerivAt_cos _).comp t (hasDerivAt_lin (env "e") (env "f") t)
    have hA := (hS.const_mul (env "b")).const_add (env "a")
    have hdisj : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisj1 : env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisj1) hA
    refine ((((hCd.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hm1c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hm1'
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = P
    generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
    generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
    field_simp
    linear_combination (-env "a"^2*env "b"*env "d"^2*P*((m : ℤ) : ℂ) -
        env "a"^2*env "b"*env "d"^2*P + 2*env "a"*env "b"^2*env "c"*env "d"*P*((m : ℤ) : ℂ) +
        2*env "a"*env "b"^2*env "c"*env "d"*P - env "b"^3*env "c"^2*P*((m : ℤ) : ℂ) -
        env "b"^3*env "c"^2*P) * hP

end OSR.IntegrationRec270
