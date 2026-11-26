import OSR.IntegrationNum1

/-! # Strengthened reciprocal trigonometric variants over ℝ

Proofs over ℝ of RUBI 4.5.1.2 #3 and #4 (quotients `csc^2 u / (a + b csc u)` and
`csc^3 u / (a + b csc u)`, using `cot' = -csc^2`) and 4.5.10 #5 (the integration by parts of
`(c + d x)^m csc^2(e + f x)` against `-cot`). They are not stated over ℂ: `transc1#sec` and
`transc1#csc` have no complex interpretation. -/

namespace OSR.IntegrationRec247

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv3R : intValue? (3 : ℝ) = some 3 := (intValue?_eq _ _).2 (by norm_num)

private theorem hasDerivAt_lin (a b t : ℝ) : HasDerivAt (fun w => a + b * w) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

private theorem hasDerivAt_cot_lin {e f t : ℝ} (hs : Real.sin (e + f * t) ≠ 0) :
    HasDerivAt (fun w => Real.cot (e + f * w)) (-f / Real.sin (e + f * t) ^ 2) t := by
  have h := ((Real.hasDerivAt_cos (e + f * t)).div (Real.hasDerivAt_sin (e + f * t)) hs).comp
    t (hasDerivAt_lin e f t)
  have hf : (fun w => Real.cot (e + f * w)) =
      (Real.cos / Real.sin) ∘ fun w => e + f * w := by
    funext v; simp [Real.cot_eq_cos_div_sin]
  rw [hf]
  refine h.congr_deriv ?_
  have := Real.sin_sq_add_cos_sq (e + f * t)
  field_simp
  linear_combination -f * this

/-! ## RUBI 4.5.1.2 #3 -/

theorem rubi4512r3Nondeg_real : rubi4512r3Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4512r3Nondeg.conditions rubi4512r3Nondeg.body
    rubi4512r3Nondeg.result rubi4512r3Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4512r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4512r3Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
        env "a" + env "b" * (Real.sin (env "e" + env "f" * w))⁻¹ ≠ 0 := by
    intro w h
    simp [rubi4512r3Nondeg, Defined, eval, Interp.real, ivm1R, iv2R, Fn.csc] at h
    tauto
  obtain ⟨hs0, hq0⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4512r3Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.real, (hD w hw).1]
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.real, ivm1R, Fn.csc, (hD w hw).1, (hD w hw).2]
  · filter_upwards with w
    simp [rubi4512r3Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hb]
  · simp only [rubi4512r3Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((Real.sin (env "e" + env "f" * t))⁻¹) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, Fn.csc]
    have hΦ2' : HasDerivAt (Φ "I2") ((Real.sin (env "e" + env "f" * t))⁻¹ *
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, ivm1R, Fn.csc]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4512r3Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4512r3Nondeg.result) =
        fun w => (env "b")⁻¹ * Φ "I1" w + -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi4512r3Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4512r3Nondeg.body =
        ((Real.sin (env "e" + env "f" * t))⁻¹) ^ 2 *
          (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹)⁻¹ := by
      simp [rubi4512r3Nondeg, eval, Interp.real, ivm1R, iv2R, Fn.csc]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    generalize Real.sin (env "e" + env "f" * t) = S at hs0 hq0 ⊢
    rw [show env "a" + env "b" * S⁻¹ = (env "a" * S + env "b") / S by field_simp] at hq0 ⊢
    have hq1 : env "a" * S + env "b" ≠ 0 := by
      intro h0; apply hq0; rw [h0, zero_div]
    generalize hE : env "a" * S + env "b" = D at hq1 ⊢
    field_simp
    rw [← hE]
    ring

/-! ## RUBI 4.5.1.2 #4 -/

theorem rubi4512r4Nondeg_real : rubi4512r4Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4512r4Nondeg.conditions rubi4512r4Nondeg.body
    rubi4512r4Nondeg.result rubi4512r4Nondeg.integrals
  intro env hc t hF
  have hW : env "b" * env "f" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.var "f")) (.int 0)) (by simp [rubi4512r4Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hb : env "b" ≠ 0 := left_ne_zero_of_mul hW
  have hf : env "f" ≠ 0 := right_ne_zero_of_mul hW
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4512r4Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
        env "a" + env "b" * (Real.sin (env "e" + env "f" * w))⁻¹ ≠ 0 := by
    intro w h
    simp [rubi4512r4Nondeg, Defined, eval, Interp.real, ivm1R, iv3R, Fn.csc] at h
    tauto
  obtain ⟨hs0, hq0⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4512r4Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [Defined, eval, Interp.real, ivm1R, iv2R, Fn.csc, (hD w hw).1, (hD w hw).2]
  · filter_upwards [hF] with w hw
    simp [rubi4512r4Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hb, hf, (hD w hw).1]
  · simp only [rubi4512r4Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((Real.sin (env "e" + env "f" * t))⁻¹) ^ 2 *
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, ivm1R, iv2R, Fn.csc]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4512r4Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4512r4Nondeg.result) =
        fun w => -Real.cot (env "e" + env "f" * w) * (env "b" * env "f")⁻¹ +
          -(env "a" * (env "b")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4512r4Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4512r4Nondeg.body =
        ((Real.sin (env "e" + env "f" * t))⁻¹) ^ 3 *
          (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹)⁻¹ := by
      simp [rubi4512r4Nondeg, eval, Interp.real, ivm1R, iv3R, Fn.csc]
    rw [hfun, hEF]
    refine (((hasDerivAt_cot_lin hs0).neg.mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    generalize Real.sin (env "e" + env "f" * t) = S at hs0 hq0 ⊢
    rw [show env "a" + env "b" * S⁻¹ = (env "a" * S + env "b") / S by field_simp] at hq0 ⊢
    have hq1 : env "a" * S + env "b" ≠ 0 := by
      intro h0; apply hq0; rw [h0, zero_div]
    generalize hE : env "a" * S + env "b" = D at hq1 ⊢
    field_simp
    rw [← hE]
    ring

/-! ## RUBI 4.5.10 #5 -/

theorem rubi4510r5Nondeg_real : rubi4510r5Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4510r5Nondeg.conditions rubi4510r5Nondeg.body
    rubi4510r5Nondeg.result rubi4510r5Nondeg.integrals
  intro env hc t hF
  have hf : env "f" ≠ 0 := by
    have h := hc (.ne (.var "f") (.int 0)) (by simp [rubi4510r5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hgt : (0 : ℝ) < env "m" := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi4510r5Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4510r5Nondeg, Defined, eval, Interp.real, hkm] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hj : 0 < j := by rw [hm] at hgt; exact_mod_cast hgt
  have hj0 : ¬ j < 0 := by omega
  have hj1 : ¬ j - 1 < 0 := by omega
  have em1 : intValue? (env "m" + -1) = some (j - 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4510r5Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simp [rubi4510r5Nondeg, Defined, eval, Interp.real, hkm, hj0, iv2R, Fn.csc] at h
    exact h
  have hs0 := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4510r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [Defined, eval, Interp.real, em1, hj1, hD w hw]
  · filter_upwards [hF] with w hw
    simp [rubi4510r5Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkm, hj0, hf, hD w hw]
  · simp only [rubi4510r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "c" + env "d" * t) ^ (j - 1) *
        Real.cot (env "e" + env "f" * t)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4510r5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4510r5Nondeg.result) =
        fun w => -(env "c" + env "d" * w) ^ j * Real.cot (env "e" + env "f" * w) * (env "f")⁻¹ +
          env "d" * env "m" * (env "f")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4510r5Nondeg, eval, recEnv, Interp.real, ivm1R, hkm]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4510r5Nondeg.body =
        (env "c" + env "d" * t) ^ j * ((Real.sin (env "e" + env "f" * t))⁻¹) ^ 2 := by
      simp [rubi4510r5Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    have hP := (hasDerivAt_zpow j _ (Or.inr (by omega))).comp t
      (hasDerivAt_lin (env "c") (env "d") t)
    refine ((((hP.neg).mul (hasDerivAt_cot_lin hs0)).mul_const _).add
      (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply, Pi.neg_apply]
    rw [show ((j : ℤ) : ℝ) = env "m" from hm.symm]
    generalize (env "c" + env "d" * t) ^ (j - 1) = P
    generalize (env "c" + env "d" * t) ^ j = P1
    generalize Real.cot (env "e" + env "f" * t) = K
    field_simp
    ring

end OSR.IntegrationRec247
