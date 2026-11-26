import OSR.IntegrationNum1

/-! # Strengthened hyperbolic variant: `sinh / (a + b cosh)` with `a² = b²`

Proof of RUBI 6.7.9 #4 over ℝ and ℂ: when `a² = b²`,
    `(e + f x)^m sinh(c + d x) / (a + b cosh(c + d x))`
equals `-(e + f x)^m / b +
    2 (e + f x)^m eᶜ⁺ᵈˣ / (a + b eᶜ⁺ᵈˣ)` (split on `a = ±b`, writing `sinh` and
`cosh` through `exp`). -/

namespace OSR.IntegrationRec259

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem coshE_R (x : ℝ) : Real.cosh x = (Real.exp x + (Real.exp x)⁻¹) / 2 := by
  rw [Real.cosh_eq, Real.exp_neg]
private theorem sinhE_R (x : ℝ) : Real.sinh x = (Real.exp x - (Real.exp x)⁻¹) / 2 := by
  rw [Real.sinh_eq, Real.exp_neg]
private theorem coshE_C (x : ℂ) : Complex.cosh x = (Complex.exp x + (Complex.exp x)⁻¹) / 2 := by
  rw [← Complex.exp_neg]; linear_combination (1 / 2 : ℂ) * Complex.two_cosh x
private theorem sinhE_C (x : ℂ) : Complex.sinh x = (Complex.exp x - (Complex.exp x)⁻¹) / 2 := by
  rw [← Complex.exp_neg]; linear_combination (1 / 2 : ℂ) * Complex.two_sinh x

/-! ## rubi679r4Nondeg -/

theorem rubi679r4Nondeg_real : rubi679r4Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r4Nondeg.conditions rubi679r4Nondeg.body
    rubi679r4Nondeg.result rubi679r4Nondeg.integrals
  intro env hc t hF
  have hab : env "a" ^ 2 - env "b" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1))
      (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi679r4Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  have hpm : env "a" = env "b" ∨ env "a" = -env "b" := by
    have : (env "a" - env "b") * (env "a" + env "b") = 0 := by linear_combination hab
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hbfm := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m")
    (.int 1))) (.int 0)) (by simp [rubi679r4Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hm1 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r4Nondeg, Defined, eval, Interp.real, hkm] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r4Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hm1' : ¬ m + 1 < 0 := by omega
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r4Nondeg.body →
      env "a" + env "b" * Real.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r4Nondeg, Defined, eval, Interp.real, hkm, hm0, ivm1R] at h ⊢
    tauto
  have hDE : ∀ w, env "a" + env "b" * Real.cosh (env "c" + env "d" * w) ≠ 0 →
      env "a" + env "b" * Real.exp (env "c" + env "d" * w) ≠ 0 := by
    intro w hw h
    apply hw
    rcases hpm with ha | ha <;> rw [ha] at h ⊢
    · have h1 : Real.exp (env "c" + env "d" * w) = -1 :=
        mul_left_cancel₀ hb (show env "b" * Real.exp (env "c" + env "d" * w) = env "b" *
            (-1) by linear_combination h)
      rw [coshE_R, h1]
      norm_num
    · have h1 : Real.exp (env "c" + env "d" * w) = 1 :=
        mul_left_cancel₀ hb (show env "b" * Real.exp (env "c" + env "d" * w) = env "b" *
            1 by linear_combination h)
      rw [coshE_R, h1]
      norm_num
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r4Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hEw := hDE w (hD w hw)
    simp [Defined, eval, Interp.real, hkm, hm0, ivm1R, hEw]
  · filter_upwards with w
    simp [rubi679r4Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, em1, hm1', hb, hf, hm1]
  · simp only [rubi679r4Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m * Real.exp (env "c" + env "d" * t) *
        (env "a" + env "b" * Real.exp (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r4Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r4Nondeg.result) = fun w => -(env "e" + env "f" * w) ^ (m + 1) *
        ((env "b")⁻¹ * (env "f")⁻¹ * (env "m" + 1)⁻¹) + 2 * Φ "I1" w := by
      funext w
      simp [rubi679r4Nondeg, eval, recEnv, Interp.real, ivm1R, em1, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r4Nondeg.body =
        (env "e" + env "f" * t) ^ m * Real.sinh (env "c" + env "d" * t) *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r4Nondeg, eval, Interp.real, hkm, ivm1R]
    rw [hfun, hEF]
    have hPd : HasDerivAt (fun w => env "e" + env "f" * w) (env "f") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "f")).const_add (env "e")
    have hPp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (Or.inr (by omega))) hPd
    refine ((hPp.neg.mul_const _).add (hΦ'.const_mul 2)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have hDt := hD t hF.self_of_nhds
    have hEt := hDE t hDt
    rw [(intValue?_eq _ _).1 hkm] at hm1 ⊢
    push_cast
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize hC : env "a" + env "b" * Real.cosh (env "c" + env "d" * t) = Cz at hDt ⊢
    generalize hA : env "a" + env "b" * Real.exp (env "c" + env "d" * t) = Az at hEt ⊢
    field_simp
    rw [← hC, ← hA, sinhE_R, coshE_R]
    have hE := Real.exp_ne_zero (env "c" + env "d" * t)
    generalize Real.exp (env "c" + env "d" * t) = E at hE ⊢
    field_simp
    rcases hpm with ha | ha <;> rw [ha] <;> ring

theorem rubi679r4Nondeg_complex : rubi679r4Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi679r4Nondeg.conditions rubi679r4Nondeg.body
    rubi679r4Nondeg.result rubi679r4Nondeg.integrals
  intro env hc t hF
  have hab : env "a" ^ 2 - env "b" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1))
      (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi679r4Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  have hpm : env "a" = env "b" ∨ env "a" = -env "b" := by
    have : (env "a" - env "b") * (env "a" + env "b") = 0 := by linear_combination hab
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hbfm := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m")
    (.int 1))) (.int 0)) (by simp [rubi679r4Nondeg])
  have hb : env "b" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hf : env "f" ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  have hm1 : env "m" + 1 ≠ 0 := by intro h0; simp [Cond.Holds, Defined, eval, h0] at hbfm
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r4Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r4Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (0 : ℝ) < m := by simpa using h'
    exact_mod_cast h''
  have hm0 : ¬ m < 0 := by omega
  have hm1' : ¬ m + 1 < 0 := by omega
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi679r4Nondeg.body →
      env "a" + env "b" * Complex.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r4Nondeg, Defined, eval, Interp.complex, hkm, hm0, ivm1C] at h ⊢
    tauto
  have hDE : ∀ w, env "a" + env "b" * Complex.cosh (env "c" + env "d" * w) ≠ 0 →
      env "a" + env "b" * Complex.exp (env "c" + env "d" * w) ≠ 0 := by
    intro w hw h
    apply hw
    rcases hpm with ha | ha <;> rw [ha] at h ⊢
    · have h1 : Complex.exp (env "c" + env "d" * w) = -1 :=
        mul_left_cancel₀ hb (show env "b" * Complex.exp (env "c" + env "d" * w) = env "b" *
            (-1) by linear_combination h)
      rw [coshE_C, h1]
      norm_num
    · have h1 : Complex.exp (env "c" + env "d" * w) = 1 :=
        mul_left_cancel₀ hb (show env "b" * Complex.exp (env "c" + env "d" * w) = env "b" *
            1 by linear_combination h)
      rw [coshE_C, h1]
      norm_num
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r4Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hEw := hDE w (hD w hw)
    simp [Defined, eval, Interp.complex, hkm, hm0, ivm1C, hEw]
  · filter_upwards with w
    simp [rubi679r4Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, em1, hm1', hb, hf, hm1]
  · simp only [rubi679r4Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        Complex.exp (env "c" + env "d" * t) *
        (env "a" + env "b" * Complex.exp (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi679r4Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r4Nondeg.result) = fun w => -(env "e" + env "f" * w) ^ (m + 1) *
        ((env "b")⁻¹ * (env "f")⁻¹ * (env "m" + 1)⁻¹) + 2 * Φ "I1" w := by
      funext w
      simp [rubi679r4Nondeg, eval, recEnv, Interp.complex, ivm1C, em1, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.complex (Function.update env "x" t) rubi679r4Nondeg.body =
        (env "e" + env "f" * t) ^ m * Complex.sinh (env "c" + env "d" * t) *
        (env "a" + env "b" * Complex.cosh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r4Nondeg, eval, Interp.complex, hkm, ivm1C]
    rw [hfun, hEF]
    have hPd : HasDerivAt (fun w => env "e" + env "f" * w) (env "f") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "f")).const_add (env "e")
    have hPp := HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (Or.inr (by omega))) hPd
    refine ((hPp.neg.mul_const _).add (hΦ'.const_mul 2)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have hDt := hD t hF.self_of_nhds
    have hEt := hDE t hDt
    rw [(intValue?_eq _ _).1 hkm] at hm1 ⊢
    push_cast
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize hC : env "a" + env "b" * Complex.cosh (env "c" + env "d" * t) = Cz at hDt ⊢
    generalize hA : env "a" + env "b" * Complex.exp (env "c" + env "d" * t) = Az at hEt ⊢
    field_simp
    rw [← hC, ← hA, sinhE_C, coshE_C]
    have hE := Complex.exp_ne_zero (env "c" + env "d" * t)
    generalize Complex.exp (env "c" + env "d" * t) = E at hE ⊢
    field_simp
    rcases hpm with ha | ha <;> rw [ha] <;> ring

end OSR.IntegrationRec259
