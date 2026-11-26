import OSR.IntegrationRec215

/-! # Strengthened inverse hyperbolic tangent rule with a logarithmic factor

Proof over ℝ of RUBI 7.3.1 #136 (and its 7.3.4 #116 twin), integrating
`(a + b artanh(1/(c x)))^p ln(f + g x) / (d + e x^2)` by parts when `c^2 d + e = 0` and
`p > 0`. The condition `c^2 f^2 = g^2` is not needed for this step. The complex statement is
vacuous (no complex interpretation of `transc1#arctanh`) and stays unproved. -/

namespace OSR.IntegrationRec227

open OSR OSR.Calculus OSR.IntegrationNum1 OSR.IntegrationRec215 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem hasDerivAt_lin (a b t : ℝ) : HasDerivAt (fun w => a + b * w) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

/-! ## RUBI 7.3.1 #136 (and 7.3.4 #116) -/

theorem rubi731r136Nondeg_real : rubi731r136Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r136Nondeg.conditions rubi731r136Nondeg.body
    rubi731r136Nondeg.result rubi731r136Nondeg.integrals
  intro env hc t hF
  have hW : env "b" * env "c" * env "d" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d"))
      (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi731r136Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r136Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r136Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨⟨hb, hcz⟩, hd⟩, hp1⟩ := hW'
  have he' : env "e" = -(env "c" ^ 2 * env "d") := by linear_combination hrel
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r136Nondeg, Defined, eval, Interp.real, hkp] at h
  have hp : env "p" = (l : ℝ) := (intValue?_eq _ _).1 hkp
  have hl : 0 < l := by rw [hp] at hpos; exact_mod_cast hpos
  have hl0 : ¬ l < 0 := by omega
  have hl1 : ¬ l + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + 1) = some (l + 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r136Nondeg.body →
      env "d" + env "e" * w ^ 2 ≠ 0 ∧ 0 < env "f" + env "g" * w ∧
        (¬ env "c" = 0 ∧ ¬ w = 0) ∧ (-1 < w⁻¹ * (env "c")⁻¹ ∧ w⁻¹ * (env "c")⁻¹ < 1) := by
    intro w h
    simp [rubi731r136Nondeg, Defined, eval, Interp.real, hkp, ivm1R, iv2R, hl0] at h
    tauto
  obtain ⟨hD0, hL0, ⟨-, ht0⟩, hc1, hc2⟩ := hBody t hF.self_of_nhds
  have hct : env "c" * t ≠ 0 := mul_ne_zero hcz ht0
  have h1 : -1 < (env "c" * t)⁻¹ := by rw [mul_inv_rev]; exact hc1
  have h2 : (env "c" * t)⁻¹ < 1 := by rw [mul_inv_rev]; exact hc2
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r136Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hB := hBody w hw
    simp [Defined, eval, Interp.real, ep1, ivm1R, hl1, hB.2.1.ne', hB.2.2.1.1, hB.2.2.1.2,
      hB.2.2.2.1, hB.2.2.2.2]
  · filter_upwards [hF] with w hw
    have hB := hBody w hw
    simp [rubi731r136Nondeg, Defined, eval, recEnv, Interp.real, ep1, ivm1R, hb, hcz, hd, hp1,
      hl1, hB.2.1, hB.2.2.1.2, hB.2.2.2.1, hB.2.2.2.2]
  · simp only [rubi731r136Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ (l + 1) *
          (env "f" + env "g" * t)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, ep1, ivm1R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r136Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r136Nondeg.result) =
        fun w => (env "a" + env "b" * Real.artanh (env "c" * w)⁻¹) ^ (l + 1) *
            Real.log (env "f" + env "g" * w) * (env "b" * env "c" * env "d" * (env "p" + 1))⁻¹ +
          -env "g" * (env "b" * env "c" * env "d" * (env "p" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi731r136Nondeg, eval, recEnv, Interp.real, ep1, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r136Nondeg.body =
        (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ l *
          Real.log (env "f" + env "g" * t) * (env "d" + env "e" * t ^ 2)⁻¹ := by
      simp [rubi731r136Nondeg, eval, Interp.real, hkp, ivm1R, iv2R]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_artanh_inv hct h1 h2).const_mul (env "b")).const_add (env "a")
    have hP := (hasDerivAt_zpow (l + 1) _ (Or.inr (by omega))).comp t hA
    have hLog := (hasDerivAt_lin (env "f") (env "g") t).log hL0.ne'
    refine (((hP.mul hLog).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply, add_sub_cancel_right]
    have hl1r : ((l + 1 : ℤ) : ℝ) = env "p" + 1 := by rw [hp]; push_cast; ring
    rw [hl1r]
    have hD := one_sub_sq_inv_ne hct h1 h2
    have hD' : 1 - t ^ 2 * env "c" ^ 2 ≠ 0 := by rwa [mul_comm] at hD
    have hdenD : env "d" + env "e" * t ^ 2 = env "d" * (1 - env "c" ^ 2 * t ^ 2) := by
      rw [he']; ring
    have hL : env "f" + env "g" * t ≠ 0 := hL0.ne'
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ l = R
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ (l + 1) = R1
    generalize Real.log (env "f" + env "g" * t) = L
    rw [hdenD]
    field_simp
    ring

theorem rubi734r116Nondeg_real : rubi734r116Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r116Nondeg.conditions rubi734r116Nondeg.body
    rubi734r116Nondeg.result rubi734r116Nondeg.integrals
  exact rubi731r136Nondeg_real

end OSR.IntegrationRec227
