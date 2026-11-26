import OSR.IntegrationNum1

/-! # Strengthened tangent variants: `(a + b tan)^E` plus a residual integral

Proofs of RUBI 4.3.4.2 #4, #6, #7 and 4.3.1.1 #10 over ℝ and ℂ: the result is an explicit term
`K [tan] (c + d tan)^E` (`E = n + 1`, or `E = n - 1` when `n > 1`) plus a residual integral; with
`tan' = (1 + tan²) f` the integrand is a rational identity in `tan`. -/

namespace OSR.IntegrationRec276

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

/-! ## rubi4342r4Nondeg -/

theorem rubi4342r4Nondeg_real : rubi4342r4Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4342r4Nondeg.conditions rubi4342r4Nondeg.body
    rubi4342r4Nondeg.result rubi4342r4Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4342r4Nondeg])
  have hn1 : (env "c") ^ 2 + (env "d") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int 0)) (by simp [rubi4342r4Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.var "f")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4342r4Nondeg])
  have hn3_0 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  have hn3_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4342r4Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "n" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4342r4Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "c" + env "d" * Real.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4342r4Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4342r4Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4342r4Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, iv2R, hn1, hn3_0, hn3_1,
        hn3_2] at h ⊢
    tauto
  · simp only [rubi4342r4Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "c" +
        (env "d" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m + 1) *
        (((((env "a" * env "d") *
        (((env "A" * env "c") + (((-1) * env "c") * env "C")) + (env "B" * env "d"))) +
        (env "b" *
        ((((env "c") ^ 2 * env "C") + ((((-1) * env "B") * env "c") * env "d")) +
        (env "A" * (env "d") ^ 2)))) +
        ((env "d" *
        (((((((env "A" * env "b") * env "c") + ((env "a" * env "B") * env "c")) +
        ((((-1) * env "b") * env "c") * env "C")) + ((((-1) * env "a") * env "A") * env "d")) +
        ((env "b" * env "B") * env "d")) + ((env "a" * env "C") * env "d"))) *
        Real.tan ((env "e" + (env "f" * t))))) +
        (((env "b" * env "C") * ((env "c") ^ 2 + (env "d") ^ 2)) *
        (Real.tan ((env "e" + (env "f" * t)))) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4342r4Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4342r4Nondeg.result) =
            fun w => (((((-1) * ((env "b" * env "c") + (((-1) * env "a") * env "d"))) *
            ((((env "c") ^ 2 * env "C") + ((((-1) * env "B") * env "c") * env "d")) +
            (env "A" * (env "d") ^ 2))) *
            ((env "c" + (env "d" * Real.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((((env "d") ^ 2 * env "f") * (env "n" + 1)) * ((env "c") ^ 2 + (env "d") ^ 2)))⁻¹) +
            ((1 * ((env "d" * ((env "c") ^ 2 + (env "d") ^ 2)))⁻¹) * Φ "I1" w) := by
      funext w
      simp [rubi4342r4Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4342r4Nondeg.body =
        ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * t))))) *
        ((env "c" + (env "d" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m)) *
        ((env "A" + (env "B" * Real.tan ((env "e" + (env "f" * t))))) +
        (env "C" * (Real.tan ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4342r4Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "c" + env "d" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "c" + env "d" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_R (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "d")).const_add (env "c")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have eA : (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) := by
      have := zsplit (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hn3_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) ^ m = P
    generalize Real.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

theorem rubi4342r4Nondeg_complex : rubi4342r4Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4342r4Nondeg.conditions rubi4342r4Nondeg.body
    rubi4342r4Nondeg.result rubi4342r4Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4342r4Nondeg])
  have hn1 : (env "c") ^ 2 + (env "d") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int 0)) (by simp [rubi4342r4Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.var "f")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4342r4Nondeg])
  have hn3_0 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  have hn3_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4342r4Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "n" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4342r4Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "c" + env "d" * Complex.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4342r4Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4342r4Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4342r4Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, hn1, hn3_0,
        hn3_1, hn3_2] at h ⊢
    tauto
  · simp only [rubi4342r4Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "c" +
        (env "d" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m + 1) *
        (((((env "a" * env "d") *
        (((env "A" * env "c") + (((-1) * env "c") * env "C")) + (env "B" * env "d"))) +
        (env "b" *
        ((((env "c") ^ 2 * env "C") + ((((-1) * env "B") * env "c") * env "d")) +
        (env "A" * (env "d") ^ 2)))) +
        ((env "d" *
        (((((((env "A" * env "b") * env "c") + ((env "a" * env "B") * env "c")) +
        ((((-1) * env "b") * env "c") * env "C")) + ((((-1) * env "a") * env "A") * env "d")) +
        ((env "b" * env "B") * env "d")) + ((env "a" * env "C") * env "d"))) *
        Complex.tan ((env "e" + (env "f" * t))))) +
        (((env "b" * env "C") * ((env "c") ^ 2 + (env "d") ^ 2)) *
        (Complex.tan ((env "e" + (env "f" * t)))) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4342r4Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4342r4Nondeg.result) =
            fun w => (((((-1) * ((env "b" * env "c") + (((-1) * env "a") * env "d"))) *
            ((((env "c") ^ 2 * env "C") + ((((-1) * env "B") * env "c") * env "d")) +
            (env "A" * (env "d") ^ 2))) *
            ((env "c" + (env "d" * Complex.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((((env "d") ^ 2 * env "f") * (env "n" + 1)) * ((env "c") ^ 2 + (env "d") ^ 2)))⁻¹) +
            ((1 * ((env "d" * ((env "c") ^ 2 + (env "d") ^ 2)))⁻¹) * Φ "I1" w) := by
      funext w
      simp [rubi4342r4Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4342r4Nondeg.body =
        ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * t))))) *
        ((env "c" + (env "d" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m)) *
        ((env "A" + (env "B" * Complex.tan ((env "e" + (env "f" * t))))) +
        (env "C" * (Complex.tan ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4342r4Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "c" + env "d" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "c" + env "d" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_C (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "d")).const_add (env "c")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have eA : (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) := by
      have := zsplit (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hn3_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) ^ m = P
    generalize Complex.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

/-! ## rubi4342r6Nondeg -/

theorem rubi4342r6Nondeg_real : rubi4342r6Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4342r6Nondeg.conditions rubi4342r6Nondeg.body
    rubi4342r6Nondeg.result rubi4342r6Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4342r6Nondeg])
  have hn1 : (env "c") ^ 2 + (env "d") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int 0)) (by simp [rubi4342r6Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "n") (.int 2))) (.int 0)) (by simp [rubi4342r6Nondeg])
  have hn3_0 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "n" + 2 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4342r6Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "n" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4342r6Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "c" + env "d" * Real.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4342r6Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4342r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4342r6Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, hn3_0, hn3_1,
        hn3_2] at h ⊢
    tauto
  · simp only [rubi4342r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "c" +
        (env "d" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (((((env "b" * env "c") * env "C") +
        (((((-1) * env "a") * env "A") * env "d") * (env "n" + 2))) +
        (((((-1) * (((env "A" * env "b") + (env "a" * env "B")) + (((-1) * env "b") * env "C"))) *
        env "d") * (env "n" + 2)) * Real.tan ((env "e" + (env "f" * t))))) +
        (((-1) *
        ((((env "a" * env "C") * env "d") * (env "n" + 2)) +
        (((-1) * env "b") *
        ((env "c" * env "C") + ((((-1) * env "B") * env "d") * (env "n" + 2)))))) *
        (Real.tan ((env "e" + (env "f" * t)))) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4342r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4342r6Nondeg.result) =
            fun w => ((((env "b" * env "C") * Real.tan ((env "e" + (env "f" * w)))) *
            ((env "c" + (env "d" * Real.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "d" * env "f") * (env "n" + 2)))⁻¹) +
            (((-1) * ((env "d" * (env "n" + 2)))⁻¹) * Φ "I1" w) := by
      funext w
      simp [rubi4342r6Nondeg, eval, recEnv, Interp.real, em1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4342r6Nondeg.body =
        ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * t))))) *
        ((env "c" + (env "d" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m)) *
        ((env "A" + (env "B" * Real.tan ((env "e" + (env "f" * t))))) +
        (env "C" * (Real.tan ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4342r6Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "c" + env "d" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "c" + env "d" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_R (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "d")).const_add (env "c")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine ((((hT.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) := by
      have := zsplit (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hn3_2c : ((m : ℤ) : ℝ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) ^ m = P
    generalize Real.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

theorem rubi4342r6Nondeg_complex : rubi4342r6Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4342r6Nondeg.conditions rubi4342r6Nondeg.body
    rubi4342r6Nondeg.result rubi4342r6Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4342r6Nondeg])
  have hn1 : (env "c") ^ 2 + (env "d") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int 0)) (by simp [rubi4342r6Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "n") (.int 2))) (.int 0)) (by simp [rubi4342r6Nondeg])
  have hn3_0 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "n" + 2 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4342r6Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "n" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4342r6Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "c" + env "d" * Complex.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4342r6Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4342r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4342r6Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, hn3_0, hn3_1,
        hn3_2] at h ⊢
    tauto
  · simp only [rubi4342r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "c" +
        (env "d" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (((((env "b" * env "c") * env "C") +
        (((((-1) * env "a") * env "A") * env "d") * (env "n" + 2))) +
        (((((-1) * (((env "A" * env "b") + (env "a" * env "B")) + (((-1) * env "b") * env "C"))) *
        env "d") * (env "n" + 2)) * Complex.tan ((env "e" + (env "f" * t))))) +
        (((-1) *
        ((((env "a" * env "C") * env "d") * (env "n" + 2)) +
        (((-1) * env "b") *
        ((env "c" * env "C") + ((((-1) * env "B") * env "d") * (env "n" + 2)))))) *
        (Complex.tan ((env "e" + (env "f" * t)))) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4342r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4342r6Nondeg.result) =
            fun w => ((((env "b" * env "C") * Complex.tan ((env "e" + (env "f" * w)))) *
            ((env "c" + (env "d" * Complex.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "d" * env "f") * (env "n" + 2)))⁻¹) +
            (((-1) * ((env "d" * (env "n" + 2)))⁻¹) * Φ "I1" w) := by
      funext w
      simp [rubi4342r6Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4342r6Nondeg.body =
        ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * t))))) *
        ((env "c" + (env "d" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m)) *
        ((env "A" + (env "B" * Complex.tan ((env "e" + (env "f" * t))))) +
        (env "C" * (Complex.tan ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4342r6Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "c" + env "d" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "c" + env "d" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_C (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "d")).const_add (env "c")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine ((((hT.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) := by
      have := zsplit (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hn3_2c : ((m : ℤ) : ℂ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) ^ m = P
    generalize Complex.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

/-! ## rubi4342r7Nondeg -/

theorem rubi4342r7Nondeg_real : rubi4342r7Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4342r7Nondeg.conditions rubi4342r7Nondeg.body
    rubi4342r7Nondeg.result rubi4342r7Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4342r7Nondeg])
  have hn1 : (env "c") ^ 2 + (env "d") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int 0)) (by simp [rubi4342r7Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "n") (.int 2))) (.int 0)) (by simp [rubi4342r7Nondeg])
  have hn3_0 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "n" + 2 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4342r7Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "n" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4342r7Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "c" + env "d" * Real.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4342r7Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4342r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4342r7Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R, hn3_0, hn3_1,
        hn3_2] at h ⊢
    tauto
  · simp only [rubi4342r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "c" +
        (env "d" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (((((env "b" * env "c") * env "C") +
        (((((-1) * env "a") * env "A") * env "d") * (env "n" + 2))) +
        (((((-1) * ((env "A" * env "b") + (((-1) * env "b") * env "C"))) * env "d") *
        (env "n" + 2)) * Real.tan ((env "e" + (env "f" * t))))) +
        (((-1) *
        ((((env "a" * env "C") * env "d") * (env "n" + 2)) +
        ((((-1) * env "b") * env "c") * env "C"))) *
        (Real.tan ((env "e" + (env "f" * t)))) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4342r7Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4342r7Nondeg.result) =
            fun w => ((((env "b" * env "C") * Real.tan ((env "e" + (env "f" * w)))) *
            ((env "c" + (env "d" * Real.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "d" * env "f") * (env "n" + 2)))⁻¹) +
            (((-1) * ((env "d" * (env "n" + 2)))⁻¹) * Φ "I1" w) := by
      funext w
      simp [rubi4342r7Nondeg, eval, recEnv, Interp.real, em1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4342r7Nondeg.body =
        ((env "a" + (env "b" * Real.tan ((env "e" + (env "f" * t))))) *
        ((env "c" + (env "d" * Real.tan ((env "e" + (env "f" * t)))))) ^ (m)) *
        (env "A" + (env "C" * (Real.tan ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4342r7Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "c" + env "d" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "c" + env "d" * Real.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_R (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "d")).const_add (env "c")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine ((((hT.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) := by
      have := zsplit (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hn3_2c : ((m : ℤ) : ℝ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) ^ m = P
    generalize Real.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

theorem rubi4342r7Nondeg_complex : rubi4342r7Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4342r7Nondeg.conditions rubi4342r7Nondeg.body
    rubi4342r7Nondeg.result rubi4342r7Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4342r7Nondeg])
  have hn1 : (env "c") ^ 2 + (env "d") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int 0)) (by simp [rubi4342r7Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "n") (.int 2))) (.int 0)) (by simp [rubi4342r7Nondeg])
  have hn3_0 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "n" + 2 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4342r7Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "n" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4342r7Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "c" + env "d" * Complex.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4342r7Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4342r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4342r7Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C, hn3_0, hn3_1,
        hn3_2] at h ⊢
    tauto
  · simp only [rubi4342r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "c" +
        (env "d" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m) *
        (((((env "b" * env "c") * env "C") +
        (((((-1) * env "a") * env "A") * env "d") * (env "n" + 2))) +
        (((((-1) * ((env "A" * env "b") + (((-1) * env "b") * env "C"))) * env "d") *
        (env "n" + 2)) * Complex.tan ((env "e" + (env "f" * t))))) +
        (((-1) *
        ((((env "a" * env "C") * env "d") * (env "n" + 2)) +
        ((((-1) * env "b") * env "c") * env "C"))) *
        (Complex.tan ((env "e" + (env "f" * t)))) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4342r7Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4342r7Nondeg.result) =
            fun w => ((((env "b" * env "C") * Complex.tan ((env "e" + (env "f" * w)))) *
            ((env "c" + (env "d" * Complex.tan ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            (((env "d" * env "f") * (env "n" + 2)))⁻¹) +
            (((-1) * ((env "d" * (env "n" + 2)))⁻¹) * Φ "I1" w) := by
      funext w
      simp [rubi4342r7Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4342r7Nondeg.body =
        ((env "a" + (env "b" * Complex.tan ((env "e" + (env "f" * t))))) *
        ((env "c" + (env "d" * Complex.tan ((env "e" + (env "f" * t)))))) ^ (m)) *
        (env "A" + (env "C" * (Complex.tan ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4342r7Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisj : env "c" + env "d" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m := by
      by_cases hk : m < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hdisjE : env "c" + env "d" * Complex.tan (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ m + 1 :=
        hdisj.imp id (fun h => by omega)
    have hT := tan_deriv_C (env "e") (env "f") t hc0
    have hA := (hT.const_mul (env "d")).const_add (env "c")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ hdisjE) hA
    refine ((((hT.const_mul _).mul hAp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have eA : (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) ^ m *
        (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) := by
      have := zsplit (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) m 1 hdisj
      rwa [pow_one] at this
    rw [eA]
    have hn3_2c : ((m : ℤ) : ℂ) + 2 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) ^ m = P
    generalize Complex.tan (env "e" + env "f" * t) = Y
    field_simp
    ring

/-! ## rubi4311r10Nondeg -/

theorem rubi4311r10Nondeg_real : rubi4311r10Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4311r10Nondeg.conditions rubi4311r10Nondeg.body
    rubi4311r10Nondeg.result rubi4311r10Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "a") ^ 2 + (env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)) (by simp [rubi4311r10Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.var "d") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.int 0)) (by simp [rubi4311r10Nondeg])
  have hn2_0 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "n" + (-1) ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4311r10Nondeg, Defined, eval, Interp.real, hkm] at h
  have hmpos : 1 < m := by
    have h := hc (.gt (.var "n") (.int 1)) (by simp [rubi4311r10Nondeg])
    have h' : (1 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "n" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hm2lt : ¬ m < 2 := by omega
  have hm1lt : ¬ m < 1 := by omega
  have hm1le : ¬ m ≤ 1 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4311r10Nondeg.body →
      Real.cos (env "c" + env "d" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Real.tan (env "c" + env "d" * w) ≠ 0) := by
    intro w h
    simp [rubi4311r10Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4311r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emm2, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4311r10Nondeg, Defined, eval, recEnv, Interp.real, emm1, ivm1R, hn2_0, hn2_1] at h ⊢
    tauto
  · simp only [rubi4311r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) +
        (((2 * env "a") * env "b") * Real.tan ((env "c" + (env "d" * t))))) *
        ((env "a" + (env "b" * Real.tan ((env "c" + (env "d" * t)))))) ^ (m - 2)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emm2, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4311r10Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4311r10Nondeg.result) =
            fun w => ((env "b" *
            ((env "a" + (env "b" * Real.tan ((env "c" + (env "d" * w)))))) ^ (m - 1)) *
            ((env "d" * (env "n" + (-1))))⁻¹) + Φ "I1" w := by
      funext w
      simp [rubi4311r10Nondeg, eval, recEnv, Interp.real, emm1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4311r10Nondeg.body =
        ((env "a" + (env "b" * Real.tan ((env "c" + (env "d" * t)))))) ^ (m) := by
      simp [rubi4311r10Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisjE : env "a" + env "b" * Real.tan (env "c" + env "d" * t) ≠ 0 ∨ 0 ≤ m - 1 :=
        Or.inr (by omega)
    have hT := tan_deriv_R (env "c") (env "d") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m - 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add hΦ').congr_deriv ?_
    have eA : (env "a" + env "b" * Real.tan (env "c" + env "d" * t)) ^ m =
        (env "a" + env "b" * Real.tan (env "c" + env "d" * t)) ^ (m - 2) *
        (env "a" + env "b" * Real.tan (env "c" + env "d" * t)) ^ 2 := by
      have := zsplit (env "a" + env "b" * Real.tan (env "c" + env "d" * t)) (m -
          2) 2 (Or.inr (by omega))
      rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
    rw [eA, show m - 1 - 1 = m - 2 by ring]
    have hn2_1c : ((m : ℤ) : ℝ) + (-1) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Real.tan (env "c" + env "d" * t)) ^ (m - 2) = P
    generalize Real.tan (env "c" + env "d" * t) = Y
    field_simp
    ring

theorem rubi4311r10Nondeg_complex : rubi4311r10Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4311r10Nondeg.conditions rubi4311r10Nondeg.body
    rubi4311r10Nondeg.result rubi4311r10Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "a") ^ 2 + (env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)) (by simp [rubi4311r10Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.var "d") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.int 0)) (by simp [rubi4311r10Nondeg])
  have hn2_0 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "n" + (-1) ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4311r10Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hmpos : 1 < m := by
    have h := hc (.gt (.var "n") (.int 1)) (by simp [rubi4311r10Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (1 : ℝ) < m := by simpa using h'
    exact_mod_cast h''
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "n" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hm1 : m + 1 < 0 → m < 0 := by omega
  have hm2lt : ¬ m < 2 := by omega
  have hm1lt : ¬ m < 1 := by omega
  have hm1le : ¬ m ≤ 1 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4311r10Nondeg.body →
      Complex.cos (env "c" + env "d" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * Complex.tan (env "c" + env "d" * w) ≠ 0) := by
    intro w h
    simp [rubi4311r10Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4311r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emm2, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4311r10Nondeg, Defined, eval, recEnv, Interp.complex, emm1, ivm1C, hn2_0,
        hn2_1] at h ⊢
    tauto
  · simp only [rubi4311r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) +
        (((2 * env "a") * env "b") * Complex.tan ((env "c" + (env "d" * t))))) *
        ((env "a" + (env "b" * Complex.tan ((env "c" + (env "d" * t)))))) ^ (m - 2)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emm2, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4311r10Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4311r10Nondeg.result) =
            fun w => ((env "b" *
            ((env "a" + (env "b" * Complex.tan ((env "c" + (env "d" * w)))))) ^ (m - 1)) *
            ((env "d" * (env "n" + (-1))))⁻¹) + Φ "I1" w := by
      funext w
      simp [rubi4311r10Nondeg, eval, recEnv, Interp.complex, emm1, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4311r10Nondeg.body =
        ((env "a" + (env "b" * Complex.tan ((env "c" + (env "d" * t)))))) ^ (m) := by
      simp [rubi4311r10Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    obtain ⟨hc0, hA0⟩ := hD t hF.self_of_nhds
    have hdisjE : env "a" + env "b" * Complex.tan (env "c" + env "d" * t) ≠ 0 ∨ 0 ≤ m - 1 :=
        Or.inr (by omega)
    have hT := tan_deriv_C (env "c") (env "d") t hc0
    have hA := (hT.const_mul (env "b")).const_add (env "a")
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (m - 1) _ hdisjE) hA
    refine (((hAp.const_mul _).mul_const _).add hΦ').congr_deriv ?_
    have eA : (env "a" + env "b" * Complex.tan (env "c" + env "d" * t)) ^ m =
        (env "a" + env "b" * Complex.tan (env "c" + env "d" * t)) ^ (m - 2) *
        (env "a" + env "b" * Complex.tan (env "c" + env "d" * t)) ^ 2 := by
      have := zsplit (env "a" + env "b" * Complex.tan (env "c" + env "d" * t)) (m -
          2) 2 (Or.inr (by omega))
      rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
    rw [eA, show m - 1 - 1 = m - 2 by ring]
    have hn2_1c : ((m : ℤ) : ℂ) + (-1) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    generalize (env "a" + env "b" * Complex.tan (env "c" + env "d" * t)) ^ (m - 2) = P
    generalize Complex.tan (env "c" + env "d" * t) = Y
    field_simp
    ring

end OSR.IntegrationRec276
