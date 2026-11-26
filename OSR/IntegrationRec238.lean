import OSR.IntegrationRec215

/-! # Strengthened inverse hyperbolic tangent rule: a logarithmic factor `ln(f + g x^2)`

Proof over ℝ of RUBI 7.3.1 #164 (and its 7.3.4 #144 twin), integrating
`x (d + e ln(f + g x^2)) (a + b artanh(c x))^2` by parts when `c^2 f + g = 0`: then
`f + g x^2 = f (1 - c^2 x^2)`, so `(f + g x^2) artanh'(c x) / g = -1/c`. The complex statement is
vacuous (no complex interpretation of `transc1#arctanh`) and stays unproved. -/

namespace OSR.IntegrationRec238

open OSR OSR.Calculus OSR.IntegrationNum1 OSR.IntegrationRec215 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem hasDerivAt_quad0 (d e t : ℝ) :
    HasDerivAt (fun w => d + e * w ^ 2) (e * (2 * t)) t := by
  have := ((hasDerivAt_pow 2 t).const_mul e).const_add d
  simpa using this

/-! ## RUBI 7.3.1 #164 (and 7.3.4 #144) -/

theorem rubi731r164Nondeg_real : rubi731r164Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r164Nondeg.conditions rubi731r164Nondeg.body
    rubi731r164Nondeg.result rubi731r164Nondeg.integrals
  intro env hc t hF
  have hrel : env "c" ^ 2 * env "f" + env "g" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "f")) (.var "g"))
      (.int 0)) (by simp [rubi731r164Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hg : env "g" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "g")) (.int 0)) (by simp [rubi731r164Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg' : env "g" = -(env "c" ^ 2 * env "f") := by linear_combination hrel
  have hcz : env "c" ≠ 0 := by
    intro h; apply hg; rw [hg', h]; ring
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r164Nondeg.body →
      0 < env "f" + env "g" * w ^ 2 ∧ (-1 < env "c" * w ∧ env "c" * w < 1) := by
    intro w h
    simp [rubi731r164Nondeg, Defined, eval, Interp.real, iv2R] at h
    tauto
  obtain ⟨hL0, h1, h2⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r164Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have hB := hD w hw
      simp [Defined, eval, Interp.real, iv2R, hB.1, hB.2.1, hB.2.2]
    · filter_upwards [hF] with w hw
      have hB := hD w hw
      have hq := one_sub_sq_mul_ne hB.2.1 hB.2.2
      simp [Defined, eval, Interp.real, ivm1R, iv2R, hB.2.1, hB.2.2, sub_eq_add_neg] at hq ⊢
      exact hq
  · filter_upwards [hF] with w hw
    have hB := hD w hw
    simp [rubi731r164Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hg, hcz, hB.1,
      hB.2.1, hB.2.2]
  · simp only [rubi731r164Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "d" + env "e" * Real.log (env "f" + env "g" * t ^ 2)) *
        (env "a" + env "b" * Real.artanh (env "c" * t))) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") (t ^ 2 * (env "a" + env "b" * Real.artanh (env "c" * t)) *
        (1 - env "c" ^ 2 * t ^ 2)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, ivm1R, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real
        (recEnv env (rubi731r164Nondeg.integrals.map (·.1)) Φ "x" w) rubi731r164Nondeg.result) =
        fun w => (env "f" + env "g" * w ^ 2) *
              (env "d" + env "e" * Real.log (env "f" + env "g" * w ^ 2)) *
              (env "a" + env "b" * Real.artanh (env "c" * w)) ^ 2 * (2 * env "g")⁻¹ +
            -(env "e" * 2⁻¹) * (w ^ 2 * (env "a" + env "b" * Real.artanh (env "c" * w)) ^ 2) +
            env "b" * (env "c")⁻¹ * Φ "I1" w + env "b" * env "c" * env "e" * Φ "I2" w := by
      funext w
      simp [rubi731r164Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r164Nondeg.body =
        t * (env "d" + env "e" * Real.log (env "f" + env "g" * t ^ 2)) *
          (env "a" + env "b" * Real.artanh (env "c" * t)) ^ 2 := by
      simp [rubi731r164Nondeg, eval, Interp.real, iv2R]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_artanh_mul h1 h2).const_mul (env "b")).const_add (env "a")
    have hQ := hasDerivAt_quad0 (env "f") (env "g") t
    have hLn := (hQ.log hL0.ne').const_mul (env "e") |>.const_add (env "d")
    have hA2 := hA.pow 2
    have hX2 := hasDerivAt_pow 2 t
    refine (((((hQ.mul hLn).mul hA2).mul_const _).add
      ((hX2.mul hA2).const_mul _)).add (hΦ1'.const_mul _) |>.add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Pi.pow_apply, Pi.mul_apply]
    have hD' := one_sub_sq_mul_ne h1 h2
    have hD'' : 1 - t ^ 2 * env "c" ^ 2 ≠ 0 := by rwa [mul_comm] at hD'
    have hL' : env "f" + env "g" * t ^ 2 ≠ 0 := hL0.ne'
    have hf : env "f" ≠ 0 := by
      intro h; apply hg; rw [hg', h]; ring
    have hfac : env "f" + env "g" * t ^ 2 = env "f" * (1 - env "c" ^ 2 * t ^ 2) := by
      rw [hg']; ring
    generalize Real.log (env "f" + env "g" * t ^ 2) = L
    generalize env "a" + env "b" * Real.artanh (env "c" * t) = A
    rw [hfac] at hL' ⊢
    rw [hg']
    field_simp
    ring

theorem rubi734r144Nondeg_real : rubi734r144Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r144Nondeg.conditions rubi734r144Nondeg.body
    rubi734r144Nondeg.result rubi734r144Nondeg.integrals
  exact rubi731r164Nondeg_real

end OSR.IntegrationRec238
