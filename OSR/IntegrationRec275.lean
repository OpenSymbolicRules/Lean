import OSR.IntegrationNum1

/-! # Strengthened tangent variants: `(a + b tan)^E` plus a residual integral

Proofs of RUBI 4.3.2.1 #7, #8, #20, #21, 4.3.3.1 #4, #5 and 4.3.4.1 #12–#15 over ℝ and ℂ: the
result is an explicit term `K (a + b tan)^E` (`E = m + 1`, or `E = m` when `m > 0`) plus a residual
integral; with `tan' = (1 + tan²) f` the integrand is a rational identity in `tan`. -/

namespace OSR.IntegrationRec275

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem hasDerivAt_lin {𝕜 : Type} [NontriviallyNormedField 𝕜] (a b t : 𝕜) :
    HasDerivAt (fun w => a + b * w) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

private theorem hasDerivAt_quad {𝕜 : Type} [NontriviallyNormedField 𝕜] (a b c t : 𝕜) :
    HasDerivAt (fun w => a + b * w + c * w ^ 2) (b + 2 * c * t) t := by
  have := (hasDerivAt_lin a b t).add ((hasDerivAt_pow 2 t).const_mul c)
  convert this using 1
  push_cast
  ring

private theorem zsplit {K : Type} [Field K] (X : K) (j : ℤ) (n : ℕ) (h : X ≠ 0 ∨ 0 ≤ j) :
    X ^ (j + n) = X ^ j * X ^ n := by
  rcases h with h | h
  · rw [zpow_add₀ h, zpow_natCast]
  · lift j to ℕ using h
    rw [show ((j : ℤ) + n) = ((j + n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_add]

private theorem tan_deriv_R (e f t : ℝ) (h : Real.cos (e + f * t) ≠ 0) :
    HasDerivAt (fun w => Real.tan (e + f * w)) ((1 + Real.tan (e + f * t) ^ 2) * f) t := by
  refine ((Real.hasDerivAt_tan h).comp t (hasDerivAt_lin e f t)).congr_deriv ?_
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  first
  | linear_combination f * Real.sin_sq_add_cos_sq (e + f * t)
  | linear_combination (-f) * Real.sin_sq_add_cos_sq (e + f * t)

private theorem tan_deriv_C (e f t : ℂ) (h : Complex.cos (e + f * t) ≠ 0) :
    HasDerivAt (fun w => Complex.tan (e + f * w)) ((1 + Complex.tan (e + f * t) ^ 2) * f) t := by
  refine ((Complex.hasDerivAt_tan h).comp t (hasDerivAt_lin e f t)).congr_deriv ?_
  rw [Complex.tan_eq_sin_div_cos]
  field_simp
  first
  | linear_combination f * Complex.sin_sq_add_cos_sq (e + f * t)
  | linear_combination (-f) * Complex.sin_sq_add_cos_sq (e + f * t)

/-! ## rubi4321r7Nondeg -/

theorem rubi4321r7Nondeg_real : rubi4321r7Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4321r7Nondeg.conditions rubi4321r7Nondeg.body
    rubi4321r7Nondeg.result rubi4321r7Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4321r7Nondeg])
  have hn1 : (env "a") ^ 2 + (env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)) (by simp [rubi4321r7Nondeg])
  have hc3 := hc (.ne (.app2 .mul (.var "f") (.var "m")) (.int 0)) (by simp [rubi4321r7Nondeg])
  have hn3_0 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "m" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4321r7Nondeg, Defined, eval, Interp.real, hkm] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi4321r7Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hm1lt : ¬ m < 1 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4321r7Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Real.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4321r7Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4321r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emm1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4321r7Nondeg, Defined, eval, recEnv, Interp.real, hkm, ivm1R, hn3_0, hn3_1] at h ⊢
    tauto
  · simp only [rubi4321r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m - 1) *
        (((env "a" * env "c") + (((-1) * env "b") * env "d")) +
        (((env "b" * env "c") + (env "a" * env "d")) * Real.tan ((env "e" + (env "f" * t)))))) t :=
        by
      convert hΦ using 1
      simp [eval, Interp.real, emm1, sub_eq_add_neg, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4321r7Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4321r7Nondeg.result) =
            fun w => ((env "d" *
            ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "f" * env "m"))⁻¹) + Φ "I1" w := by
      funext w
      simp [rubi4321r7Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4321r7Nondeg.body =
        ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "c" + (env "d" * Real.tan ((env "e" + (env "f" * t))))) := by
      simp [rubi4321r7Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisjE : env "a" + env "b" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m :=
        Or.inr (by omega)
    have hT := tan_deriv_R (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add hΦ').congr_deriv ?_
    have eA : (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m =
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ (m - 1) *
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) (m -
          1) 1 (Or.inr (by omega))
      rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring, pow_one] at this
    rw [eA]
    have hn3_1c : ((m : ℤ) : ℝ) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    generalize (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ (m - 1) = P
    generalize Real.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

theorem rubi4321r7Nondeg_complex : rubi4321r7Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4321r7Nondeg.conditions rubi4321r7Nondeg.body
    rubi4321r7Nondeg.result rubi4321r7Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4321r7Nondeg])
  have hn1 : (env "a") ^ 2 + (env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)) (by simp [rubi4321r7Nondeg])
  have hc3 := hc (.ne (.app2 .mul (.var "f") (.var "m")) (.int 0)) (by simp [rubi4321r7Nondeg])
  have hn3_0 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "m" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4321r7Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi4321r7Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (0 : ℝ) < m := by simpa using h'
    exact_mod_cast h''
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hm1lt : ¬ m < 1 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4321r7Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Complex.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4321r7Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4321r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emm1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4321r7Nondeg, Defined, eval, recEnv, Interp.complex, hkm, ivm1C, hn3_0, hn3_1] at h ⊢
    tauto
  · simp only [rubi4321r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m - 1) *
        (((env "a" * env "c") + (((-1) * env "b") * env "d")) +
        (((env "b" * env "c") + (env "a" * env "d")) *
        Complex.tan ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emm1, sub_eq_add_neg, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4321r7Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4321r7Nondeg.result) =
            fun w => ((env "d" *
            ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "f" * env "m"))⁻¹) + Φ "I1" w := by
      funext w
      simp [rubi4321r7Nondeg, eval, recEnv, Interp.complex, hkm, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4321r7Nondeg.body =
        ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "c" + (env "d" * Complex.tan ((env "e" + (env "f" * t))))) := by
      simp [rubi4321r7Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisjE : env "a" + env "b" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m :=
        Or.inr (by omega)
    have hT := tan_deriv_C (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add hΦ').congr_deriv ?_
    have eA : (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m =
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ (m - 1) *
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) (m -
          1) 1 (Or.inr (by omega))
      rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring, pow_one] at this
    rw [eA]
    have hn3_1c : ((m : ℤ) : ℂ) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    generalize (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ (m - 1) = P
    generalize Complex.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

/-! ## rubi4321r8Nondeg -/

theorem rubi4321r8Nondeg_real : rubi4321r8Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4321r8Nondeg.conditions rubi4321r8Nondeg.body
    rubi4321r8Nondeg.result rubi4321r8Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4321r8Nondeg])
  have hn1 : (env "a") ^ 2 + (env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)) (by simp [rubi4321r8Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4321r8Nondeg])
  have hn3_0 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4321r8Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4321r8Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Real.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4321r8Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4321r8Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4321r8Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R, hn1, hn3_0,
        hn3_1] at h ⊢
    tauto
  · simp only [rubi4321r8Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m + 1) *
        (((env "a" * env "c") + (env "b" * env "d")) +
        (((-1) * ((env "b" * env "c") + (((-1) * env "a") * env "d"))) *
        Real.tan ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4321r8Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4321r8Nondeg.result) =
            fun w => ((((env "b" * env "c") + (((-1) * env "a") * env "d")) *
            ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "f" * (env "m" + 1)) * ((env "a") ^ 2 + (env "b") ^ 2)))⁻¹) +
            ((1 * (((env "a") ^ 2 + (env "b") ^ 2))⁻¹) * Φ "I1" w) := by
      funext w
      simp [rubi4321r8Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4321r8Nondeg.body =
        ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "c" + (env "d" * Real.tan ((env "e" + (env "f" * t))))) := by
      simp [rubi4321r8Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "a" + env "b" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "a" + env "b" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_R (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have eA : (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hn3_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m = P
    generalize Real.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

theorem rubi4321r8Nondeg_complex : rubi4321r8Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4321r8Nondeg.conditions rubi4321r8Nondeg.body
    rubi4321r8Nondeg.result rubi4321r8Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4321r8Nondeg])
  have hn1 : (env "a") ^ 2 + (env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)) (by simp [rubi4321r8Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4321r8Nondeg])
  have hn3_0 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4321r8Nondeg, Defined, eval, Interp.complex, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4321r8Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Complex.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4321r8Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4321r8Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4321r8Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, hn1, hn3_0,
        hn3_1] at h ⊢
    tauto
  · simp only [rubi4321r8Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m + 1) *
        (((env "a" * env "c") + (env "b" * env "d")) +
        (((-1) * ((env "b" * env "c") + (((-1) * env "a") * env "d"))) *
        Complex.tan ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4321r8Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4321r8Nondeg.result) =
            fun w => ((((env "b" * env "c") + (((-1) * env "a") * env "d")) *
            ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "f" * (env "m" + 1)) * ((env "a") ^ 2 + (env "b") ^ 2)))⁻¹) +
            ((1 * (((env "a") ^ 2 + (env "b") ^ 2))⁻¹) * Φ "I1" w) := by
      funext w
      simp [rubi4321r8Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4321r8Nondeg.body =
        ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "c" + (env "d" * Complex.tan ((env "e" + (env "f" * t))))) := by
      simp [rubi4321r8Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "a" + env "b" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "a" + env "b" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_C (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have eA : (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hn3_1c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m = P
    generalize Complex.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

/-! ## rubi4321r20Nondeg -/

theorem rubi4321r20Nondeg_real : rubi4321r20Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4321r20Nondeg.conditions rubi4321r20Nondeg.body
    rubi4321r20Nondeg.result rubi4321r20Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4321r20Nondeg])
  have hn2 : (env "a") ^ 2 + (env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)) (by simp [rubi4321r20Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4321r20Nondeg])
  have hn3_0 : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4321r20Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4321r20Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Real.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4321r20Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4321r20Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4321r20Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R, hn2, hn3_0,
        hn3_1, hn3_2] at h ⊢
    tauto
  · simp only [rubi4321r20Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m + 1) *
        ((((env "a" * (env "c") ^ 2) + (((2 * env "b") * env "c") * env "d")) +
        (((-1) * env "a") * (env "d") ^ 2)) +
        (((-1) *
        (((env "b" * (env "c") ^ 2) + (((((-1) * 2) * env "a") * env "c") * env "d")) +
        (((-1) * env "b") * (env "d") ^ 2))) * Real.tan ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4321r20Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4321r20Nondeg.result) =
            fun w => (((((env "b" * env "c") + (((-1) * env "a") * env "d"))) ^ 2 *
            ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            ((((env "b" * env "f") * (env "m" + 1)) * ((env "a") ^ 2 + (env "b") ^ 2)))⁻¹) +
            ((1 * (((env "a") ^ 2 + (env "b") ^ 2))⁻¹) * Φ "I1" w) := by
      funext w
      simp [rubi4321r20Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4321r20Nondeg.body =
        ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Real.tan ((env "e" + (env "f" * t)))))) ^ 2 := by
      simp [rubi4321r20Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "a" + env "b" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "a" + env "b" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_R (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have eA : (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hn3_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m = P
    generalize Real.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

theorem rubi4321r20Nondeg_complex : rubi4321r20Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4321r20Nondeg.conditions rubi4321r20Nondeg.body
    rubi4321r20Nondeg.result rubi4321r20Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4321r20Nondeg])
  have hn2 : (env "a") ^ 2 + (env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)) (by simp [rubi4321r20Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4321r20Nondeg])
  have hn3_0 : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4321r20Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4321r20Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Complex.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4321r20Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4321r20Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4321r20Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, hn2, hn3_0,
        hn3_1, hn3_2] at h ⊢
    tauto
  · simp only [rubi4321r20Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m + 1) *
        ((((env "a" * (env "c") ^ 2) + (((2 * env "b") * env "c") * env "d")) +
        (((-1) * env "a") * (env "d") ^ 2)) +
        (((-1) *
        (((env "b" * (env "c") ^ 2) + (((((-1) * 2) * env "a") * env "c") * env "d")) +
        (((-1) * env "b") * (env "d") ^ 2))) * Complex.tan ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4321r20Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4321r20Nondeg.result) =
            fun w => (((((env "b" * env "c") + (((-1) * env "a") * env "d"))) ^ 2 *
            ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            ((((env "b" * env "f") * (env "m" + 1)) * ((env "a") ^ 2 + (env "b") ^ 2)))⁻¹) +
            ((1 * (((env "a") ^ 2 + (env "b") ^ 2))⁻¹) * Φ "I1" w) := by
      funext w
      simp [rubi4321r20Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4321r20Nondeg.body =
        ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Complex.tan ((env "e" + (env "f" * t)))))) ^ 2 := by
      simp [rubi4321r20Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "a" + env "b" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "a" + env "b" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_C (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have eA : (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hn3_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m = P
    generalize Complex.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

/-! ## rubi4321r21Nondeg -/

theorem rubi4321r21Nondeg_real : rubi4321r21Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4321r21Nondeg.conditions rubi4321r21Nondeg.body
    rubi4321r21Nondeg.result rubi4321r21Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4321r21Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4321r21Nondeg])
  have hn3_0 : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4321r21Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4321r21Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Real.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4321r21Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4321r21Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4321r21Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R, hn3_0, hn3_1,
        hn3_2] at h ⊢
    tauto
  · simp only [rubi4321r21Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (((env "c") ^ 2 + ((-1) * (env "d") ^ 2)) +
        (((2 * env "c") * env "d") * Real.tan ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4321r21Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4321r21Nondeg.result) =
            fun w => (((env "d") ^ 2 *
            ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "b" * env "f") * (env "m" + 1)))⁻¹) + Φ "I1" w := by
      funext w
      simp [rubi4321r21Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4321r21Nondeg.body =
        ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Real.tan ((env "e" + (env "f" * t)))))) ^ 2 := by
      simp [rubi4321r21Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "a" + env "b" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "a" + env "b" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_R (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add hΦ').congr_deriv ?_
    simp only [add_sub_cancel_right]
    have hn3_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m = P
    generalize Real.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

theorem rubi4321r21Nondeg_complex : rubi4321r21Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4321r21Nondeg.conditions rubi4321r21Nondeg.body
    rubi4321r21Nondeg.result rubi4321r21Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4321r21Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4321r21Nondeg])
  have hn3_0 : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4321r21Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4321r21Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Complex.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4321r21Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4321r21Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4321r21Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, hn3_0, hn3_1,
        hn3_2] at h ⊢
    tauto
  · simp only [rubi4321r21Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (((env "c") ^ 2 + ((-1) * (env "d") ^ 2)) +
        (((2 * env "c") * env "d") * Complex.tan ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4321r21Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4321r21Nondeg.result) =
            fun w => (((env "d") ^ 2 *
            ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "b" * env "f") * (env "m" + 1)))⁻¹) + Φ "I1" w := by
      funext w
      simp [rubi4321r21Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4321r21Nondeg.body =
        ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Complex.tan ((env "e" + (env "f" * t)))))) ^ 2 := by
      simp [rubi4321r21Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "a" + env "b" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "a" + env "b" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_C (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add hΦ').congr_deriv ?_
    simp only [add_sub_cancel_right]
    have hn3_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m = P
    generalize Complex.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

/-! ## rubi4331r4Nondeg -/

theorem rubi4331r4Nondeg_real : rubi4331r4Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4331r4Nondeg.conditions rubi4331r4Nondeg.body
    rubi4331r4Nondeg.result rubi4331r4Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4331r4Nondeg])
  have hn2 : (env "a") ^ 2 + (env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)) (by simp [rubi4331r4Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4331r4Nondeg])
  have hn3_0 : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4331r4Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4331r4Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Real.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4331r4Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4331r4Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4331r4Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R, hn2, hn3_0, hn3_1,
        hn3_2] at h ⊢
    tauto
  · simp only [rubi4331r4Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m + 1) *
        ((((((env "a" * env "A") * env "c") + ((env "b" * env "B") * env "c")) +
        ((env "A" * env "b") * env "d")) + ((((-1) * env "a") * env "B") * env "d")) +
        (((-1) *
        (((((env "A" * env "b") * env "c") + ((((-1) * env "a") * env "B") * env "c")) +
        ((((-1) * env "a") * env "A") * env "d")) + ((((-1) * env "b") * env "B") * env "d"))) *
        Real.tan ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4331r4Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4331r4Nondeg.result) =
            fun w => (((((env "b" * env "c") + (((-1) * env "a") * env "d")) *
            ((env "A" * env "b") + (((-1) * env "a") * env "B"))) *
            ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            ((((env "b" * env "f") * (env "m" + 1)) * ((env "a") ^ 2 + (env "b") ^ 2)))⁻¹) +
            ((1 * (((env "a") ^ 2 + (env "b") ^ 2))⁻¹) * Φ "I1" w) := by
      funext w
      simp [rubi4331r4Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4331r4Nondeg.body =
        (((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "c" + (env "d" * Real.tan ((env "e" + (env "f" * t)))))) *
        (env "A" + (env "B" * Real.tan ((env "e" + (env "f" * t))))) := by
      simp [rubi4331r4Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "a" + env "b" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "a" + env "b" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_R (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have eA : (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hn3_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m = P
    generalize Real.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

theorem rubi4331r4Nondeg_complex : rubi4331r4Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4331r4Nondeg.conditions rubi4331r4Nondeg.body
    rubi4331r4Nondeg.result rubi4331r4Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4331r4Nondeg])
  have hn2 : (env "a") ^ 2 + (env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)) (by simp [rubi4331r4Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4331r4Nondeg])
  have hn3_0 : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4331r4Nondeg, Defined, eval, Interp.complex, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4331r4Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Complex.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4331r4Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4331r4Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4331r4Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, hn2, hn3_0,
        hn3_1, hn3_2] at h ⊢
    tauto
  · simp only [rubi4331r4Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m + 1) *
        ((((((env "a" * env "A") * env "c") + ((env "b" * env "B") * env "c")) +
        ((env "A" * env "b") * env "d")) + ((((-1) * env "a") * env "B") * env "d")) +
        (((-1) *
        (((((env "A" * env "b") * env "c") + ((((-1) * env "a") * env "B") * env "c")) +
        ((((-1) * env "a") * env "A") * env "d")) + ((((-1) * env "b") * env "B") * env "d"))) *
        Complex.tan ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4331r4Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4331r4Nondeg.result) =
            fun w => (((((env "b" * env "c") + (((-1) * env "a") * env "d")) *
            ((env "A" * env "b") + (((-1) * env "a") * env "B"))) *
            ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            ((((env "b" * env "f") * (env "m" + 1)) * ((env "a") ^ 2 + (env "b") ^ 2)))⁻¹) +
            ((1 * (((env "a") ^ 2 + (env "b") ^ 2))⁻¹) * Φ "I1" w) := by
      funext w
      simp [rubi4331r4Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4331r4Nondeg.body =
        (((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "c" + (env "d" * Complex.tan ((env "e" + (env "f" * t)))))) *
        (env "A" + (env "B" * Complex.tan ((env "e" + (env "f" * t))))) := by
      simp [rubi4331r4Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "a" + env "b" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "a" + env "b" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_C (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have eA : (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hn3_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m = P
    generalize Complex.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

/-! ## rubi4331r5Nondeg -/

theorem rubi4331r5Nondeg_real : rubi4331r5Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4331r5Nondeg.conditions rubi4331r5Nondeg.body
    rubi4331r5Nondeg.result rubi4331r5Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4331r5Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4331r5Nondeg])
  have hn2_0 : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4331r5Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4331r5Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Real.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4331r5Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4331r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4331r5Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, hn2_0, hn2_1,
        hn2_2] at h ⊢
    tauto
  · simp only [rubi4331r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (((env "A" * env "c") + (((-1) * env "B") * env "d")) +
        (((env "B" * env "c") + (env "A" * env "d")) * Real.tan ((env "e" + (env "f" * t)))))) t :=
        by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4331r5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4331r5Nondeg.result) =
            fun w => (((env "B" * env "d") *
            ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "b" * env "f") * (env "m" + 1)))⁻¹) + Φ "I1" w := by
      funext w
      simp [rubi4331r5Nondeg, eval, recEnv, Interp.real, em1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4331r5Nondeg.body =
        (((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "c" + (env "d" * Real.tan ((env "e" + (env "f" * t)))))) *
        (env "A" + (env "B" * Real.tan ((env "e" + (env "f" * t))))) := by
      simp [rubi4331r5Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "a" + env "b" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "a" + env "b" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_R (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add hΦ').congr_deriv ?_
    simp only [add_sub_cancel_right]
    have hn2_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m = P
    generalize Real.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

theorem rubi4331r5Nondeg_complex : rubi4331r5Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4331r5Nondeg.conditions rubi4331r5Nondeg.body
    rubi4331r5Nondeg.result rubi4331r5Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4331r5Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4331r5Nondeg])
  have hn2_0 : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4331r5Nondeg, Defined, eval, Interp.complex, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4331r5Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Complex.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4331r5Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4331r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4331r5Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, hn2_0, hn2_1,
        hn2_2] at h ⊢
    tauto
  · simp only [rubi4331r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (((env "A" * env "c") + (((-1) * env "B") * env "d")) +
        (((env "B" * env "c") + (env "A" * env "d")) *
        Complex.tan ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4331r5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4331r5Nondeg.result) =
            fun w => (((env "B" * env "d") *
            ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "b" * env "f") * (env "m" + 1)))⁻¹) + Φ "I1" w := by
      funext w
      simp [rubi4331r5Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4331r5Nondeg.body =
        (((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "c" + (env "d" * Complex.tan ((env "e" + (env "f" * t)))))) *
        (env "A" + (env "B" * Complex.tan ((env "e" + (env "f" * t))))) := by
      simp [rubi4331r5Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "a" + env "b" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "a" + env "b" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_C (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add hΦ').congr_deriv ?_
    simp only [add_sub_cancel_right]
    have hn2_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m = P
    generalize Complex.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

/-! ## rubi4341r12Nondeg -/

theorem rubi4341r12Nondeg_real : rubi4341r12Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4341r12Nondeg.conditions rubi4341r12Nondeg.body
    rubi4341r12Nondeg.result rubi4341r12Nondeg.integrals
  intro env hc t hF
  have hn0 : ((env "A" * (env "b") ^ 2) + ((((-1) * env "a") * env "b") * env "B")) +
      ((env "a") ^ 2 * env "C") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4341r12Nondeg])
  have hn2 : (env "a") ^ 2 + (env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)) (by simp [rubi4341r12Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4341r12Nondeg])
  have hn3_0 : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4341r12Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4341r12Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Real.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4341r12Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4341r12Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R, hn2, hn3_0,
        hn3_1, hn3_2] at h ⊢
    tauto
  · simp only [rubi4341r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m + 1) *
        (((env "b" * env "B") + (env "a" * (env "A" + ((-1) * env "C")))) +
        (((-1) *
        (((env "A" * env "b") + (((-1) * env "a") * env "B")) + (((-1) * env "b") * env "C"))) *
        Real.tan ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4341r12Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4341r12Nondeg.result) =
            fun w => (((((env "A" * (env "b") ^ 2) + ((((-1) * env "a") * env "b") * env "B")) +
            ((env "a") ^ 2 * env "C")) *
            ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            ((((env "b" * env "f") * (env "m" + 1)) * ((env "a") ^ 2 + (env "b") ^ 2)))⁻¹) +
            ((1 * (((env "a") ^ 2 + (env "b") ^ 2))⁻¹) * Φ "I1" w) := by
      funext w
      simp [rubi4341r12Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4341r12Nondeg.body =
        ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "A" + (env "B" * Real.tan ((env "e" + (env "f" * t))))) +
        (env "C" * (Real.tan ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4341r12Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "a" + env "b" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "a" + env "b" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_R (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have eA : (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hn3_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m = P
    generalize Real.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

theorem rubi4341r12Nondeg_complex : rubi4341r12Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4341r12Nondeg.conditions rubi4341r12Nondeg.body
    rubi4341r12Nondeg.result rubi4341r12Nondeg.integrals
  intro env hc t hF
  have hn0 : ((env "A" * (env "b") ^ 2) + ((((-1) * env "a") * env "b") * env "B")) +
      ((env "a") ^ 2 * env "C") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4341r12Nondeg])
  have hn2 : (env "a") ^ 2 + (env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)) (by simp [rubi4341r12Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4341r12Nondeg])
  have hn3_0 : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4341r12Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4341r12Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Complex.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4341r12Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4341r12Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, hn2, hn3_0,
        hn3_1, hn3_2] at h ⊢
    tauto
  · simp only [rubi4341r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m + 1) *
        (((env "b" * env "B") + (env "a" * (env "A" + ((-1) * env "C")))) +
        (((-1) *
        (((env "A" * env "b") + (((-1) * env "a") * env "B")) + (((-1) * env "b") * env "C"))) *
        Complex.tan ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4341r12Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4341r12Nondeg.result) =
            fun w => (((((env "A" * (env "b") ^ 2) + ((((-1) * env "a") * env "b") * env "B")) +
            ((env "a") ^ 2 * env "C")) *
            ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            ((((env "b" * env "f") * (env "m" + 1)) * ((env "a") ^ 2 + (env "b") ^ 2)))⁻¹) +
            ((1 * (((env "a") ^ 2 + (env "b") ^ 2))⁻¹) * Φ "I1" w) := by
      funext w
      simp [rubi4341r12Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4341r12Nondeg.body =
        ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "A" + (env "B" * Complex.tan ((env "e" + (env "f" * t))))) +
        (env "C" * (Complex.tan ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4341r12Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "a" + env "b" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "a" + env "b" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_C (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have eA : (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hn3_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m = P
    generalize Complex.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

/-! ## rubi4341r13Nondeg -/

theorem rubi4341r13Nondeg_real : rubi4341r13Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4341r13Nondeg.conditions rubi4341r13Nondeg.body
    rubi4341r13Nondeg.result rubi4341r13Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "A" * (env "b") ^ 2) + ((env "a") ^ 2 * env "C") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4341r13Nondeg])
  have hn2 : (env "a") ^ 2 + (env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)) (by simp [rubi4341r13Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4341r13Nondeg])
  have hn3_0 : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4341r13Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4341r13Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Real.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4341r13Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4341r13Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R, hn2, hn3_0,
        hn3_1, hn3_2] at h ⊢
    tauto
  · simp only [rubi4341r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m + 1) *
        ((env "a" * (env "A" + ((-1) * env "C"))) +
        (((-1) * ((env "A" * env "b") + (((-1) * env "b") * env "C"))) *
        Real.tan ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4341r13Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4341r13Nondeg.result) =
            fun w => ((((env "A" * (env "b") ^ 2) + ((env "a") ^ 2 * env "C")) *
            ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            ((((env "b" * env "f") * (env "m" + 1)) * ((env "a") ^ 2 + (env "b") ^ 2)))⁻¹) +
            ((1 * (((env "a") ^ 2 + (env "b") ^ 2))⁻¹) * Φ "I1" w) := by
      funext w
      simp [rubi4341r13Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4341r13Nondeg.body =
        ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "A" + (env "C" * (Real.tan ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4341r13Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "a" + env "b" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "a" + env "b" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_R (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have eA : (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hn3_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m = P
    generalize Real.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

theorem rubi4341r13Nondeg_complex : rubi4341r13Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4341r13Nondeg.conditions rubi4341r13Nondeg.body
    rubi4341r13Nondeg.result rubi4341r13Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "A" * (env "b") ^ 2) + ((env "a") ^ 2 * env "C") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4341r13Nondeg])
  have hn2 : (env "a") ^ 2 + (env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)) (by simp [rubi4341r13Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4341r13Nondeg])
  have hn3_0 : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4341r13Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4341r13Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Complex.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4341r13Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4341r13Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, hn2, hn3_0,
        hn3_1, hn3_2] at h ⊢
    tauto
  · simp only [rubi4341r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m + 1) *
        ((env "a" * (env "A" + ((-1) * env "C"))) +
        (((-1) * ((env "A" * env "b") + (((-1) * env "b") * env "C"))) *
        Complex.tan ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4341r13Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4341r13Nondeg.result) =
            fun w => ((((env "A" * (env "b") ^ 2) + ((env "a") ^ 2 * env "C")) *
            ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            ((((env "b" * env "f") * (env "m" + 1)) * ((env "a") ^ 2 + (env "b") ^ 2)))⁻¹) +
            ((1 * (((env "a") ^ 2 + (env "b") ^ 2))⁻¹) * Φ "I1" w) := by
      funext w
      simp [rubi4341r13Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4341r13Nondeg.body =
        ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "A" + (env "C" * (Complex.tan ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4341r13Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "a" + env "b" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "a" + env "b" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_C (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have eA : (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) := by
      have := zsplit (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hn3_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m = P
    generalize Complex.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

/-! ## rubi4341r14Nondeg -/

theorem rubi4341r14Nondeg_real : rubi4341r14Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4341r14Nondeg.conditions rubi4341r14Nondeg.body
    rubi4341r14Nondeg.result rubi4341r14Nondeg.integrals
  intro env hc t hF
  have hn0 : ((env "A" * (env "b") ^ 2) + ((((-1) * env "a") * env "b") * env "B")) +
      ((env "a") ^ 2 * env "C") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4341r14Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4341r14Nondeg])
  have hn2_0 : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4341r14Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4341r14Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Real.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4341r14Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r14Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4341r14Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, hn2_0, hn2_1,
        hn2_2] at h ⊢
    tauto
  · simp only [rubi4341r14Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "A" + ((-1) * env "C")) + (env "B" * Real.tan ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4341r14Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4341r14Nondeg.result) =
            fun w => ((env "C" *
            ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "b" * env "f") * (env "m" + 1)))⁻¹) + Φ "I1" w := by
      funext w
      simp [rubi4341r14Nondeg, eval, recEnv, Interp.real, em1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4341r14Nondeg.body =
        ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "A" + (env "B" * Real.tan ((env "e" + (env "f" * t))))) +
        (env "C" * (Real.tan ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4341r14Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "a" + env "b" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "a" + env "b" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_R (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add hΦ').congr_deriv ?_
    simp only [add_sub_cancel_right]
    have hn2_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m = P
    generalize Real.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

theorem rubi4341r14Nondeg_complex : rubi4341r14Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4341r14Nondeg.conditions rubi4341r14Nondeg.body
    rubi4341r14Nondeg.result rubi4341r14Nondeg.integrals
  intro env hc t hF
  have hn0 : ((env "A" * (env "b") ^ 2) + ((((-1) * env "a") * env "b") * env "B")) +
      ((env "a") ^ 2 * env "C") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4341r14Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4341r14Nondeg])
  have hn2_0 : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4341r14Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4341r14Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Complex.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4341r14Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r14Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4341r14Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, hn2_0, hn2_1,
        hn2_2] at h ⊢
    tauto
  · simp only [rubi4341r14Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "A" + ((-1) * env "C")) + (env "B" * Complex.tan ((env "e" + (env "f" * t)))))) t :=
        by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4341r14Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4341r14Nondeg.result) =
            fun w => ((env "C" *
            ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "b" * env "f") * (env "m" + 1)))⁻¹) + Φ "I1" w := by
      funext w
      simp [rubi4341r14Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4341r14Nondeg.body =
        ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "A" + (env "B" * Complex.tan ((env "e" + (env "f" * t))))) +
        (env "C" * (Complex.tan ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4341r14Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "a" + env "b" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "a" + env "b" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_C (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add hΦ').congr_deriv ?_
    simp only [add_sub_cancel_right]
    have hn2_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m = P
    generalize Complex.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

/-! ## rubi4341r15Nondeg -/

theorem rubi4341r15Nondeg_real : rubi4341r15Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4341r15Nondeg.conditions rubi4341r15Nondeg.body
    rubi4341r15Nondeg.result rubi4341r15Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "A" * (env "b") ^ 2) + ((env "a") ^ 2 * env "C") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4341r15Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4341r15Nondeg])
  have hn2_0 : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4341r15Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4341r15Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Real.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4341r15Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4341r15Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, hn2_0, hn2_1,
        hn2_2] at h ⊢
    tauto
  · simp only [rubi4341r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4341r15Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4341r15Nondeg.result) =
            fun w => ((env "C" *
            ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "b" * env "f") * (env "m" + 1)))⁻¹) +
            ((env "A" + ((-1) * env "C")) * Φ "I1" w) := by
      funext w
      simp [rubi4341r15Nondeg, eval, recEnv, Interp.real, em1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4341r15Nondeg.body =
        ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "A" + (env "C" * (Real.tan ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4341r15Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "a" + env "b" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "a" + env "b" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_R (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have hn2_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m = P
    generalize Real.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

theorem rubi4341r15Nondeg_complex : rubi4341r15Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4341r15Nondeg.conditions rubi4341r15Nondeg.body
    rubi4341r15Nondeg.result rubi4341r15Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "A" * (env "b") ^ 2) + ((env "a") ^ 2 * env "C") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4341r15Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4341r15Nondeg])
  have hn2_0 : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4341r15Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4341r15Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Complex.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4341r15Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4341r15Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, hn2_0, hn2_1,
        hn2_2] at h ⊢
    tauto
  · simp only [rubi4341r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4341r15Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4341r15Nondeg.result) =
            fun w => ((env "C" *
            ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "b" * env "f") * (env "m" + 1)))⁻¹) +
            ((env "A" + ((-1) * env "C")) * Φ "I1" w) := by
      funext w
      simp [rubi4341r15Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4341r15Nondeg.body =
        ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (env "A" + (env "C" * (Complex.tan ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4341r15Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "a" + env "b" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "a" + env "b" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_C (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have hn2_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m = P
    generalize Complex.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

end OSR.IntegrationRec275
