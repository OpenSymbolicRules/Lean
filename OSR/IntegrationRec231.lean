import OSR.IntegrationRec131

/-! # Strengthened inverse hyperbolic tangent rules: `artanh(c x / sqrt(a + c^2 x^2))`

Proofs over ℝ of RUBI 7.3.7 #21 and #17 (and their 7.3.4 (mixed) twins), when `b = c^2`:
`∫ artanh(c x / sqrt(a + b x^2))^m / sqrt(a + b x^2) dx = artanh(…)^(m+1) / (c (m+1))`, and
the integration by parts of `(d x)^m artanh(c x / sqrt(a + b x^2))`. Both rest on the
derivative `c / sqrt(a + c^2 x^2)` of `artanh(c x / sqrt(a + c^2 x^2))`.
The complex statement is vacuous (`arith1#root` and `transc1#arctanh` have no complex
interpretation) and stays unproved. -/

namespace OSR.IntegrationRec231

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

/-- `artanh(c x / sqrt(a + c^2 x^2))` has derivative `c / sqrt(a + c^2 x^2)`. -/
private theorem hasDerivAt_artanh_ratio {a c t : ℝ} (hQ : 0 < a + c ^ 2 * t ^ 2)
    (h1 : -1 < c * t * (Real.sqrt (a + c ^ 2 * t ^ 2))⁻¹)
    (h2 : c * t * (Real.sqrt (a + c ^ 2 * t ^ 2))⁻¹ < 1) :
    HasDerivAt (fun w => Real.artanh (c * w * (Real.sqrt (a + c ^ 2 * w ^ 2))⁻¹))
      (c * (Real.sqrt (a + c ^ 2 * t ^ 2))⁻¹) t := by
  have hS0 : Real.sqrt (a + c ^ 2 * t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  have hq : HasDerivAt (fun w => a + c ^ 2 * w ^ 2) (c ^ 2 * (2 * t)) t := by
    have := ((hasDerivAt_pow 2 t).const_mul (c ^ 2)).const_add a
    simpa using this
  have hS := (Real.hasDerivAt_sqrt hQ.ne').comp t hq
  have hU := ((hasDerivAt_id' t).const_mul c).mul (hS.inv hS0)
  have hA := (OSR.IntegrationRec131.hasDerivAt_artanh h1 h2).comp t hU
  refine hA.congr_deriv ?_
  have hS2 : Real.sqrt (a + c ^ 2 * t ^ 2) ^ 2 = a + c ^ 2 * t ^ 2 := Real.sq_sqrt hQ.le
  have hU2 : (c * t * (Real.sqrt (a + c ^ 2 * t ^ 2))⁻¹) ^ 2 < 1 := by
    rw [sq_lt_one_iff_abs_lt_one, abs_lt]; exact ⟨h1, h2⟩
  have h1u : 1 - (c * t * (Real.sqrt (a + c ^ 2 * t ^ 2))⁻¹) ^ 2 =
      a * (Real.sqrt (a + c ^ 2 * t ^ 2) ^ 2)⁻¹ := by
    field_simp
    rw [hS2]; ring
  have ha : a ≠ 0 := by
    intro h
    have : 0 < 1 - (c * t * (Real.sqrt (a + c ^ 2 * t ^ 2))⁻¹) ^ 2 := by linarith
    rw [h1u, h, zero_mul] at this
    exact lt_irrefl 0 this
  simp only [Pi.inv_apply, Function.comp_apply]
  rw [h1u]
  generalize Real.sqrt (a + c ^ 2 * t ^ 2) = S at hS0 hS2 ⊢
  rw [hS2]
  have hQ' : a + c ^ 2 * t ^ 2 ≠ 0 := hQ.ne'
  field_simp
  ring

/-! ## RUBI 7.3.7 #21 (and 7.3.4 (mixed) #21) -/

theorem rubi737r21Nondeg_real : rubi737r21Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi737r21Nondeg.conditions rubi737r21Nondeg.body
    rubi737r21Nondeg.result
  intro env hc t hF
  have hb : env "b" = env "c" ^ 2 := by
    have h := hc (.eq (.var "b") (.pow (.var "c") (.int 2))) (by simp [rubi737r21Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hW : env "c" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "c") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [rubi737r21Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨hcz, hm1⟩ := hW'
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi737r21Nondeg, Defined, eval, Interp.real, hkm] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hj1 : j ≠ -1 := by
    intro h; apply hm1; rw [hm, h]; norm_num
  have ep1 : intValue? (env "m" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi737r21Nondeg.body →
      0 < env "a" + env "c" ^ 2 * w ^ 2 ∧
        (-1 < env "c" * w * (Real.sqrt (env "a" + env "c" ^ 2 * w ^ 2))⁻¹ ∧
          env "c" * w * (Real.sqrt (env "a" + env "c" ^ 2 * w ^ 2))⁻¹ < 1) ∧
        (j < 0 →
          Real.artanh (env "c" * w * (Real.sqrt (env "a" + env "c" ^ 2 * w ^ 2))⁻¹) ≠ 0) := by
    intro w h
    simp [rubi737r21Nondeg, Defined, eval, Interp.real, hkm, ivm1R, iv2R, hb] at h
    have hs : Real.sqrt (env "a" + env "c" ^ 2 * w ^ 2) ≠ 0 := by tauto
    refine ⟨Real.sqrt_pos.mp (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs)), ?_, ?_⟩ <;>
      tauto
  obtain ⟨hQ, ⟨h1, h2⟩, hA0⟩ := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    obtain ⟨hQw, ⟨hw1, hw2⟩, hAw⟩ := hD w hw
    have hj : j + 1 < 0 → j < 0 := by omega
    simp [rubi737r21Nondeg, Defined, eval, Interp.real, ep1, ivm1R, iv2R, hb, hcz, hm1, hQw.le,
      (Real.sqrt_pos.mpr hQw).ne', hw1, hw2]
    exact fun h => hAw (hj h)
  · have hfun : (fun w => eval Interp.real (Function.update env "x" w) rubi737r21Nondeg.result) =
        fun w =>
          Real.artanh (env "c" * w * (Real.sqrt (env "a" + env "c" ^ 2 * w ^ 2))⁻¹) ^ (j + 1) *
            (env "c" * (env "m" + 1))⁻¹ := by
      funext w
      simp [rubi737r21Nondeg, eval, Interp.real, ep1, ivm1R, iv2R, hb]
    have hEF : eval Interp.real (Function.update env "x" t) rubi737r21Nondeg.body =
        Real.artanh (env "c" * t * (Real.sqrt (env "a" + env "c" ^ 2 * t ^ 2))⁻¹) ^ j *
          (Real.sqrt (env "a" + env "c" ^ 2 * t ^ 2))⁻¹ := by
      simp [rubi737r21Nondeg, eval, Interp.real, hkm, ivm1R, iv2R, hb]
    rw [hfun, hEF]
    have hA := hasDerivAt_artanh_ratio hQ h1 h2
    have hor : Real.artanh (env "c" * t * (Real.sqrt (env "a" + env "c" ^ 2 * t ^ 2))⁻¹) ≠ 0 ∨
        0 ≤ j + 1 := by
      by_cases hj : j < 0
      · exact Or.inl (hA0 hj)
      · exact Or.inr (by omega)
    have hP := (hasDerivAt_zpow (j + 1) _ hor).comp t hA
    refine (hP.mul_const _).congr_deriv ?_
    rw [show j + 1 - 1 = j by ring]
    have hjr : ((j + 1 : ℤ) : ℝ) = env "m" + 1 := by rw [hm]; push_cast; ring
    rw [hjr]
    have hS0 : Real.sqrt (env "a" + env "c" ^ 2 * t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
    generalize Real.artanh (env "c" * t * (Real.sqrt (env "a" + env "c" ^ 2 * t ^ 2))⁻¹) ^ j = R
    field_simp

theorem rubi734mr21Nondeg_real : rubi734mr21Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi734mr21Nondeg.conditions rubi734mr21Nondeg.body
    rubi734mr21Nondeg.result
  exact rubi737r21Nondeg_real

/-! ## RUBI 7.3.7 #17 (and 7.3.4 (mixed) #17) -/

theorem rubi737r17Nondeg_real : rubi737r17Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi737r17Nondeg.conditions rubi737r17Nondeg.body
    rubi737r17Nondeg.result rubi737r17Nondeg.integrals
  intro env hc t hF
  have hb : env "b" = env "c" ^ 2 := by
    have h := hc (.eq (.var "b") (.pow (.var "c") (.int 2))) (by simp [rubi737r17Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hW : env "d" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [rubi737r17Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨hd, hm1⟩ := hW'
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi737r17Nondeg, Defined, eval, Interp.real, hkm] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hj1 : j ≠ -1 := by
    intro h; apply hm1; rw [hm, h]; norm_num
  have ep1 : intValue? (env "m" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi737r17Nondeg.body →
      (j < 0 → env "d" * w ≠ 0) ∧ 0 < env "a" + env "c" ^ 2 * w ^ 2 ∧
        (-1 < env "c" * w * (Real.sqrt (env "a" + env "c" ^ 2 * w ^ 2))⁻¹ ∧
          env "c" * w * (Real.sqrt (env "a" + env "c" ^ 2 * w ^ 2))⁻¹ < 1) := by
    intro w h
    simp [rubi737r17Nondeg, Defined, eval, Interp.real, hkm, ivm1R, iv2R, hb] at h
    have hs : Real.sqrt (env "a" + env "c" ^ 2 * w ^ 2) ≠ 0 := by tauto
    refine ⟨?_, Real.sqrt_pos.mp (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs)), ?_⟩
    · simp only [ne_eq, mul_eq_zero, not_or]; tauto
    · tauto
  obtain ⟨hd0, hQ, h1, h2⟩ := hD t hF.self_of_nhds
  have hj1' : j + 1 < 0 → j < 0 := by omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi737r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hdw, hQw, -⟩ := hD w hw
    have hdw' : j + 1 < 0 → env "d" * w ≠ 0 := fun h => hdw (hj1' h)
    simp only [ne_eq, mul_eq_zero, not_or] at hdw'
    simp [Defined, eval, Interp.real, ep1, ivm1R, iv2R, hb, hQw.le, (Real.sqrt_pos.mpr hQw).ne']
    tauto
  · filter_upwards [hF] with w hw
    obtain ⟨hdw, hQw, hw1, hw2⟩ := hD w hw
    have hdw' : j + 1 < 0 → env "d" * w ≠ 0 := fun h => hdw (hj1' h)
    simp only [ne_eq, mul_eq_zero, not_or] at hdw'
    simp [rubi737r17Nondeg, Defined, eval, recEnv, Interp.real, ep1, ivm1R, iv2R, hb, hd, hm1,
      hQw.le, (Real.sqrt_pos.mpr hQw).ne', hw1, hw2]
    tauto
  · simp only [rubi737r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" * t) ^ (j + 1) *
        (Real.sqrt (env "a" + env "c" ^ 2 * t ^ 2))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, ep1, ivm1R, iv2R, hb, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi737r17Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi737r17Nondeg.result) =
        fun w => (env "d" * w) ^ (j + 1) *
            Real.artanh (env "c" * w * (Real.sqrt (env "a" + env "c" ^ 2 * w ^ 2))⁻¹) *
            (env "d" * (env "m" + 1))⁻¹ +
          -env "c" * (env "d" * (env "m" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi737r17Nondeg, eval, recEnv, Interp.real, ep1, ivm1R, iv2R, hb,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi737r17Nondeg.body =
        (env "d" * t) ^ j *
          Real.artanh (env "c" * t * (Real.sqrt (env "a" + env "c" ^ 2 * t ^ 2))⁻¹) := by
      simp [rubi737r17Nondeg, eval, Interp.real, hkm, ivm1R, iv2R, hb]
    rw [hfun, hEF]
    have hA := hasDerivAt_artanh_ratio hQ h1 h2
    have hor : env "d" * t ≠ 0 ∨ 0 ≤ j + 1 := by
      by_cases hj : j < 0
      · exact Or.inl (hd0 hj)
      · exact Or.inr (by omega)
    have hP := (hasDerivAt_zpow (j + 1) _ hor).comp t ((hasDerivAt_id' t).const_mul (env "d"))
    refine (((hP.mul hA).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    rw [show j + 1 - 1 = j by ring]
    have hjr : ((j + 1 : ℤ) : ℝ) = env "m" + 1 := by rw [hm]; push_cast; ring
    rw [hjr]
    have hS0 : Real.sqrt (env "a" + env "c" ^ 2 * t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
    generalize Real.artanh (env "c" * t * (Real.sqrt (env "a" + env "c" ^ 2 * t ^ 2))⁻¹) = A
    generalize (env "d" * t) ^ j = R
    generalize (env "d" * t) ^ (j + 1) = R1
    field_simp
    ring

theorem rubi734mr17Nondeg_real : rubi734mr17Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734mr17Nondeg.conditions rubi734mr17Nondeg.body
    rubi734mr17Nondeg.result rubi734mr17Nondeg.integrals
  exact rubi737r17Nondeg_real

end OSR.IntegrationRec231
