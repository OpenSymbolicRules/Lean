import OSR.IntegrationRec131

/-! # Strengthened inverse hyperbolic tangent rule: `artanh(tan(a + b x))`

Proof over ℝ of RUBI 7.3.7 #45 (and its 7.3.4 (mixed) #45 twin), integrating
`(e + f x)^m artanh(tan(a + b x))` by parts for an integer `m > 0`: the derivative of
`artanh(tan u)` is `sec(2 u)` wherever `|tan u| < 1`. The complex statement is vacuous (no
complex interpretation of `transc1#arctanh`) and stays unproved. -/

namespace OSR.IntegrationRec232

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)

private theorem hasDerivAt_lin (a b t : ℝ) : HasDerivAt (fun w => a + b * w) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

/-- Where `|tan u| < 1`, `cos^2 u - sin^2 u = cos (2 u)` is positive. -/
private theorem cos_two_pos {u : ℝ} (hc : Real.cos u ≠ 0) (h1 : -1 < Real.tan u)
    (h2 : Real.tan u < 1) : 0 < 2 * Real.cos u ^ 2 - 1 := by
  have hT : Real.tan u ^ 2 < 1 := by
    rw [sq_lt_one_iff_abs_lt_one, abs_lt]; exact ⟨h1, h2⟩
  have hC : 0 < Real.cos u ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hc))
  rw [Real.tan_eq_sin_div_cos, div_pow, div_lt_one hC] at hT
  nlinarith [Real.sin_sq_add_cos_sq u]

private theorem cos_two_ne {a b t : ℝ} (hc : Real.cos (a + b * t) ≠ 0)
    (h1 : -1 < Real.tan (a + b * t)) (h2 : Real.tan (a + b * t) < 1) :
    Real.cos (2 * a + 2 * b * t) ≠ 0 := by
  rw [show 2 * a + 2 * b * t = 2 * (a + b * t) by ring, Real.cos_two_mul]
  exact (cos_two_pos hc h1 h2).ne'

/-- `artanh(tan(a + b x))` has derivative `b sec(2 a + 2 b x)` where `|tan(a + b x)| < 1`. -/
private theorem hasDerivAt_artanh_tan {a b t : ℝ} (hc : Real.cos (a + b * t) ≠ 0)
    (h1 : -1 < Real.tan (a + b * t)) (h2 : Real.tan (a + b * t) < 1) :
    HasDerivAt (fun w => Real.artanh (Real.tan (a + b * w)))
      (b * (Real.cos (2 * a + 2 * b * t))⁻¹) t := by
  have hT := (Real.hasDerivAt_tan hc).comp t (hasDerivAt_lin a b t)
  have hA := (OSR.IntegrationRec131.hasDerivAt_artanh h1 h2).comp t hT
  refine hA.congr_deriv ?_
  have hK := cos_two_pos hc h1 h2
  rw [show 2 * a + 2 * b * t = 2 * (a + b * t) by ring, Real.cos_two_mul,
    Real.tan_eq_sin_div_cos, div_pow, Real.sin_sq]
  have hK' : Real.cos (a + b * t) ^ 2 - (1 - Real.cos (a + b * t) ^ 2) ≠ 0 := by
    intro h; linarith
  generalize Real.cos (a + b * t) = C at hc hK hK' ⊢
  have hK2 : 2 * C ^ 2 - 1 ≠ 0 := hK.ne'
  have hK3 : C ^ 2 * 2 - 1 ≠ 0 := by intro h; apply hK2; linarith
  field_simp
  ring

/-! ## RUBI 7.3.7 #45 (and 7.3.4 (mixed) #45) -/

theorem rubi737r45Nondeg_real : rubi737r45Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi737r45Nondeg.conditions rubi737r45Nondeg.body
    rubi737r45Nondeg.result rubi737r45Nondeg.integrals
  intro env hc t hF
  have hW : env "f" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [rubi737r45Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "m" := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi737r45Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨hf, hm1⟩ := hW'
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi737r45Nondeg, Defined, eval, Interp.real, hkm] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hj : 0 < j := by rw [hm] at hpos; exact_mod_cast hpos
  have hj0 : ¬ j < 0 := by omega
  have hj1 : ¬ j + 1 < 0 := by omega
  have ep1 : intValue? (env "m" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi737r45Nondeg.body →
      Real.cos (env "a" + env "b" * w) ≠ 0 ∧
        (-1 < Real.tan (env "a" + env "b" * w) ∧ Real.tan (env "a" + env "b" * w) < 1) := by
    intro w h
    simp [rubi737r45Nondeg, Defined, eval, Interp.real, hkm, hj0] at h
    tauto
  obtain ⟨hc0, h1, h2⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi737r45Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hcw, hw1, hw2⟩ := hD w hw
    simp [Defined, eval, Interp.real, ep1, hj1, cos_two_ne hcw hw1 hw2]
  · filter_upwards [hF] with w hw
    obtain ⟨hcw, hw1, hw2⟩ := hD w hw
    simp [rubi737r45Nondeg, Defined, eval, recEnv, Interp.real, ep1, ivm1R, hf, hm1, hj1, hcw,
      hw1, hw2]
  · simp only [rubi737r45Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ (j + 1) *
        (Real.cos (2 * env "a" + 2 * env "b" * t))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, ep1, Fn.sec, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi737r45Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi737r45Nondeg.result) =
        fun w => (env "e" + env "f" * w) ^ (j + 1) *
            Real.artanh (Real.tan (env "a" + env "b" * w)) * (env "f" * (env "m" + 1))⁻¹ +
          -env "b" * (env "f" * (env "m" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi737r45Nondeg, eval, recEnv, Interp.real, ep1, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi737r45Nondeg.body =
        (env "e" + env "f" * t) ^ j * Real.artanh (Real.tan (env "a" + env "b" * t)) := by
      simp [rubi737r45Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    have hA := hasDerivAt_artanh_tan hc0 h1 h2
    have hP := (hasDerivAt_zpow (j + 1) _ (Or.inr (by omega))).comp t
      (hasDerivAt_lin (env "e") (env "f") t)
    refine (((hP.mul hA).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    rw [show j + 1 - 1 = j by ring]
    have hjr : ((j + 1 : ℤ) : ℝ) = env "m" + 1 := by rw [hm]; push_cast; ring
    rw [hjr]
    have hC2 := cos_two_ne hc0 h1 h2
    generalize Real.artanh (Real.tan (env "a" + env "b" * t)) = A
    generalize (env "e" + env "f" * t) ^ j = R
    generalize (env "e" + env "f" * t) ^ (j + 1) = R1
    field_simp
    ring

theorem rubi734mr45Nondeg_real : rubi734mr45Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734mr45Nondeg.conditions rubi734mr45Nondeg.body
    rubi734mr45Nondeg.result rubi734mr45Nondeg.integrals
  exact rubi737r45Nondeg_real

end OSR.IntegrationRec232
