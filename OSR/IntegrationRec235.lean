import OSR.IntegrationRec215

/-! # Strengthened inverse hyperbolic tangent rules: integrations by parts and a substitution

Proofs over ℝ of RUBI 7.3.1 #7 and #8, integrating `(d x)^m (a + b artanh(c x))^p` and
`(d x)^m (a + b artanh(1/(c x)))^p` by parts; of RUBI 7.3.2 #7 and #8 (with their 7.3.5
twins), integrating `(e + f x)^m (a + b artanh(c + d x))^p` and its reciprocal-argument form by
parts for an integer `m < -1`; of RUBI 7.3.1 #9 (with 7.3.3 #1), integrating
`(a + b artanh(c x))^p / (d + e x)` by parts against `-ln(2 / (1 + e x / d)) / e` when
`c^2 d^2 = e^2`; and of RUBI 7.3.5 #6 (with 7.3.2 #6, second form), substituting
`u = c + d x` in `(e + f x)^m (a + b artanh(1/(c + d x)))^p` when `d e = c f`. The complex
statements are vacuous (no complex interpretation of `transc1#arctanh`) and stay unproved. -/

namespace OSR.IntegrationRec235

open OSR OSR.Calculus OSR.IntegrationNum1 OSR.IntegrationRec215 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem hasDerivAt_lin (a b t : ℝ) : HasDerivAt (fun w => a + b * w) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

/-- `artanh(c + d x)` has derivative `d / (1 - (c + d x)^2)`. -/
private theorem hasDerivAt_artanh_lin {c d t : ℝ} (h1 : -1 < c + d * t) (h2 : c + d * t < 1) :
    HasDerivAt (fun w => Real.artanh (c + d * w)) (d * (1 - (c + d * t) ^ 2)⁻¹) t := by
  have h := (OSR.IntegrationRec131.hasDerivAt_artanh h1 h2).comp t (hasDerivAt_lin c d t)
  refine h.congr_deriv ?_
  ring

/-- `artanh(1/(c + d x))` has derivative `d / (1 - (c + d x)^2)`. -/
private theorem hasDerivAt_artanh_inv_lin {c d t : ℝ} (h0 : c + d * t ≠ 0)
    (h1 : -1 < (c + d * t)⁻¹) (h2 : (c + d * t)⁻¹ < 1) :
    HasDerivAt (fun w => Real.artanh (c + d * w)⁻¹) (d * (1 - (c + d * t) ^ 2)⁻¹) t := by
  have h := (OSR.IntegrationRec131.hasDerivAt_artanh h1 h2).comp t
    ((hasDerivAt_lin c d t).inv h0)
  refine h.congr_deriv ?_
  have hY : 1 - (c + d * t) ^ 2 ≠ 0 := by
    have hlt : ((c + d * t)⁻¹) ^ 2 < 1 := by
      rw [sq_lt_one_iff_abs_lt_one, abs_lt]; exact ⟨h1, h2⟩
    have hp : 0 < (c + d * t) ^ 2 := by positivity
    rw [inv_pow, inv_lt_one₀ hp] at hlt
    linarith
  have hY3 : (c + d * t) ^ 2 - 1 ≠ 0 := by intro h; apply hY; linarith
  rw [inv_pow, show (1 - ((c + d * t) ^ 2)⁻¹) = ((c + d * t) ^ 2 - 1) / (c + d * t) ^ 2 by
    field_simp]
  rw [show (1 - (c + d * t) ^ 2) = -((c + d * t) ^ 2 - 1) by ring]
  field_simp

private theorem one_sub_sq_lin_ne {y : ℝ} (h1 : -1 < y) (h2 : y < 1) : 1 - y ^ 2 ≠ 0 := by
  have : y ^ 2 < 1 := by rw [sq_lt_one_iff_abs_lt_one, abs_lt]; exact ⟨h1, h2⟩
  linarith

private theorem one_sub_sq_inv_lin_ne {y : ℝ} (h1 : -1 < y⁻¹) (h2 : y⁻¹ < 1) :
    1 - y ^ 2 ≠ 0 := by
  by_cases h0 : y = 0
  · rw [h0]; norm_num
  have hlt : (y⁻¹) ^ 2 < 1 := by rw [sq_lt_one_iff_abs_lt_one, abs_lt]; exact ⟨h1, h2⟩
  have hp : 0 < y ^ 2 := by positivity
  rw [inv_pow, inv_lt_one₀ hp] at hlt
  linarith

/-! ## RUBI 7.3.1 #7 -/

theorem rubi731r7Nondeg_real : rubi731r7Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r7Nondeg.conditions rubi731r7Nondeg.body
    rubi731r7Nondeg.result rubi731r7Nondeg.integrals
  intro env hc t hF
  have hW : env "d" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [rubi731r7Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r7Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨hd, hm1⟩ := hW'
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r7Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r7Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hk1' : ¬ k < 1 := by omega
  have em1 : intValue? (env "m" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have ep1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hj1' : j + 1 < 0 → j < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r7Nondeg.body →
      (j < 0 → env "d" * w ≠ 0) ∧ (-1 < env "c" * w ∧ env "c" * w < 1) := by
    intro w h
    simp [rubi731r7Nondeg, Defined, eval, Interp.real, hkm, hkp, hk0] at h
    refine ⟨?_, ?_⟩
    · simp only [ne_eq, mul_eq_zero, not_or]; tauto
    · tauto
  obtain ⟨hd0, h1, h2⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hdw, hw1, hw2⟩ := hD w hw
    have hdw' : j + 1 < 0 → env "d" * w ≠ 0 := fun h => hdw (hj1' h)
    have hq := one_sub_sq_mul_ne hw1 hw2
    simp only [ne_eq, mul_eq_zero, not_or] at hdw'
    simp [Defined, eval, Interp.real, em1, ep1, ivm1R, iv2R, hk1', hw1, hw2,
      sub_eq_add_neg] at hq ⊢
    tauto
  · filter_upwards [hF] with w hw
    obtain ⟨hdw, hw1, hw2⟩ := hD w hw
    have hdw' : j + 1 < 0 → env "d" * w ≠ 0 := fun h => hdw (hj1' h)
    simp only [ne_eq, mul_eq_zero, not_or] at hdw'
    simp [rubi731r7Nondeg, Defined, eval, recEnv, Interp.real, em1, hkp, ivm1R, hd, hm1, hk0,
      hw1, hw2]
    tauto
  · simp only [rubi731r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" * t) ^ (j + 1) *
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) *
        (1 - env "c" ^ 2 * t ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, ep1, ivm1R, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r7Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r7Nondeg.result) =
        fun w => (env "d" * w) ^ (j + 1) *
            (env "a" + env "b" * Real.artanh (env "c" * w)) ^ k * (env "d" * (env "m" + 1))⁻¹ +
          -env "b" * env "c" * env "p" * (env "d" * (env "m" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi731r7Nondeg, eval, recEnv, Interp.real, em1, hkp, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r7Nondeg.body =
        (env "d" * t) ^ j * (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k := by
      simp [rubi731r7Nondeg, eval, Interp.real, hkm, hkp]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_artanh_mul h1 h2).const_mul (env "b")).const_add (env "a")
    have hor : env "d" * t ≠ 0 ∨ 0 ≤ j + 1 := by
      by_cases hj : j < 0
      · exact Or.inl (hd0 hj)
      · exact Or.inr (by omega)
    have hP := (hasDerivAt_zpow (j + 1) _ hor).comp t ((hasDerivAt_id' t).const_mul (env "d"))
    have hQ := (hasDerivAt_zpow k _ (Or.inr hk.le)).comp t hA
    refine (((hP.mul hQ).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    rw [show j + 1 - 1 = j by ring]
    have hjr : ((j + 1 : ℤ) : ℝ) = env "m" + 1 := by rw [hm]; push_cast; ring
    have hkr : ((k : ℤ) : ℝ) = env "p" := hp.symm
    rw [hjr, hkr]
    have hD' := one_sub_sq_mul_ne h1 h2
    have hD'' : 1 - t ^ 2 * env "c" ^ 2 ≠ 0 := by rwa [mul_comm] at hD'
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) = R
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k = R1
    generalize (env "d" * t) ^ j = P
    generalize (env "d" * t) ^ (j + 1) = P1
    field_simp
    ring

/-! ## RUBI 7.3.1 #8 -/

theorem rubi731r8Nondeg_real : rubi731r8Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r8Nondeg.conditions rubi731r8Nondeg.body
    rubi731r8Nondeg.result rubi731r8Nondeg.integrals
  intro env hc t hF
  have hW : env "d" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [rubi731r8Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r8Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨hd, hm1⟩ := hW'
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r8Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r8Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hk1' : ¬ k < 1 := by omega
  have em1 : intValue? (env "m" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have ep1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hj1' : j + 1 < 0 → j < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r8Nondeg.body →
      (j < 0 → env "d" * w ≠ 0) ∧ (env "c" ≠ 0 ∧ w ≠ 0) ∧
        (-1 < w⁻¹ * (env "c")⁻¹ ∧ w⁻¹ * (env "c")⁻¹ < 1) := by
    intro w h
    simp [rubi731r8Nondeg, Defined, eval, Interp.real, hkm, hkp, hk0, ivm1R] at h
    refine ⟨?_, ?_, ?_⟩
    · simp only [ne_eq, mul_eq_zero, not_or]; tauto
    · tauto
    · tauto
  obtain ⟨hd0, ⟨hcz, ht0⟩, hc1, hc2⟩ := hD t hF.self_of_nhds
  have hct : env "c" * t ≠ 0 := mul_ne_zero hcz ht0
  have h1 : -1 < (env "c" * t)⁻¹ := by rw [mul_inv_rev]; exact hc1
  have h2 : (env "c" * t)⁻¹ < 1 := by rw [mul_inv_rev]; exact hc2
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r8Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hdw, ⟨hcw, hw0⟩, hw1, hw2⟩ := hD w hw
    have hdw' : j + 1 < 0 → env "d" * w ≠ 0 := fun h => hdw (hj1' h)
    have hq := one_sub_sq_inv_ne (mul_ne_zero hcw hw0) (by rw [mul_inv_rev]; exact hw1)
      (by rw [mul_inv_rev]; exact hw2)
    simp only [ne_eq, mul_eq_zero, not_or] at hdw'
    simp [Defined, eval, Interp.real, em1, ep1, ivm1R, iv2R, hk1', hw1, hw2, hcw, hw0,
      sub_eq_add_neg] at hq ⊢
    tauto
  · filter_upwards [hF] with w hw
    obtain ⟨-, ⟨hcw, hw0⟩, hw1, hw2⟩ := hD w hw
    simp [rubi731r8Nondeg, Defined, eval, recEnv, Interp.real, em1, hkp, ivm1R, hd, hm1, hk0,
      hw1, hw2, hcw, hw0]
  · simp only [rubi731r8Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" * t) ^ (j + 1) *
        (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ (k - 1) *
        (1 - env "c" ^ 2 * t ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, ep1, ivm1R, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r8Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r8Nondeg.result) =
        fun w => (env "d" * w) ^ (j + 1) *
            (env "a" + env "b" * Real.artanh (env "c" * w)⁻¹) ^ k * (env "d" * (env "m" + 1))⁻¹ +
          -env "b" * env "c" * env "p" * (env "d" * (env "m" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi731r8Nondeg, eval, recEnv, Interp.real, em1, hkp, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r8Nondeg.body =
        (env "d" * t) ^ j * (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ k := by
      simp [rubi731r8Nondeg, eval, Interp.real, hkm, hkp, ivm1R]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_artanh_inv hct h1 h2).const_mul (env "b")).const_add (env "a")
    have hor : env "d" * t ≠ 0 ∨ 0 ≤ j + 1 := by
      by_cases hj : j < 0
      · exact Or.inl (hd0 hj)
      · exact Or.inr (by omega)
    have hP := (hasDerivAt_zpow (j + 1) _ hor).comp t ((hasDerivAt_id' t).const_mul (env "d"))
    have hQ := (hasDerivAt_zpow k _ (Or.inr hk.le)).comp t hA
    refine (((hP.mul hQ).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    rw [show j + 1 - 1 = j by ring]
    have hjr : ((j + 1 : ℤ) : ℝ) = env "m" + 1 := by rw [hm]; push_cast; ring
    have hkr : ((k : ℤ) : ℝ) = env "p" := hp.symm
    rw [hjr, hkr]
    have hD' := one_sub_sq_inv_ne hct h1 h2
    have hD'' : 1 - t ^ 2 * env "c" ^ 2 ≠ 0 := by rwa [mul_comm] at hD'
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ (k - 1) = R
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ k = R1
    generalize (env "d" * t) ^ j = P
    generalize (env "d" * t) ^ (j + 1) = P1
    field_simp
    ring

/-! ## RUBI 7.3.2 #7 (and 7.3.5 #7) -/

theorem rubi732r7Nondeg_real : rubi732r7Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi732r7Nondeg.conditions rubi732r7Nondeg.body
    rubi732r7Nondeg.result rubi732r7Nondeg.integrals
  intro env hc t hF
  have hW : env "f" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [rubi732r7Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi732r7Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hmneg : env "m" < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi732r7Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨hf, hm1⟩ := hW'
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi732r7Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi732r7Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have hj : j < -1 := by
    have : (j : ℝ) < -1 := hm ▸ hmneg
    exact_mod_cast this
  have hj0 : j < 0 := by omega
  have hj1 : j + 1 < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hk1' : ¬ k < 1 := by omega
  have em1 : intValue? (env "m" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have ep1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi732r7Nondeg.body →
      env "e" + env "f" * w ≠ 0 ∧
        (-1 < env "c" + env "d" * w ∧ env "c" + env "d" * w < 1) := by
    intro w h
    simp [rubi732r7Nondeg, Defined, eval, Interp.real, hkm, hkp, hk0, hj0] at h
    tauto
  obtain ⟨hL0, h1, h2⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi732r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hLw, hw1, hw2⟩ := hD w hw
    have hq := one_sub_sq_lin_ne hw1 hw2
    simp [Defined, eval, Interp.real, em1, ep1, ivm1R, iv2R, hk1', hw1, hw2, hLw,
      sub_eq_add_neg] at hq ⊢
    exact hq
  · filter_upwards [hF] with w hw
    obtain ⟨hLw, hw1, hw2⟩ := hD w hw
    simp [rubi732r7Nondeg, Defined, eval, recEnv, Interp.real, em1, hkp, ivm1R, hf, hm1, hk0,
      hw1, hw2, hLw]
  · simp only [rubi732r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ (j + 1) *
        (env "a" + env "b" * Real.artanh (env "c" + env "d" * t)) ^ (k - 1) *
        (1 - (env "c" + env "d" * t) ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, ep1, ivm1R, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi732r7Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi732r7Nondeg.result) =
        fun w => (env "e" + env "f" * w) ^ (j + 1) *
            (env "a" + env "b" * Real.artanh (env "c" + env "d" * w)) ^ k *
            (env "f" * (env "m" + 1))⁻¹ +
          -env "b" * env "d" * env "p" * (env "f" * (env "m" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi732r7Nondeg, eval, recEnv, Interp.real, em1, hkp, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi732r7Nondeg.body =
        (env "e" + env "f" * t) ^ j *
          (env "a" + env "b" * Real.artanh (env "c" + env "d" * t)) ^ k := by
      simp [rubi732r7Nondeg, eval, Interp.real, hkm, hkp]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_artanh_lin h1 h2).const_mul (env "b")).const_add (env "a")
    have hP := (hasDerivAt_zpow (j + 1) _ (Or.inl hL0)).comp t
      (hasDerivAt_lin (env "e") (env "f") t)
    have hQ := (hasDerivAt_zpow k _ (Or.inr hk.le)).comp t hA
    refine (((hP.mul hQ).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    rw [show j + 1 - 1 = j by ring]
    have hjr : ((j + 1 : ℤ) : ℝ) = env "m" + 1 := by rw [hm]; push_cast; ring
    have hkr : ((k : ℤ) : ℝ) = env "p" := hp.symm
    rw [hjr, hkr]
    have hY := one_sub_sq_lin_ne h1 h2
    generalize (env "a" + env "b" * Real.artanh (env "c" + env "d" * t)) ^ (k - 1) = R
    generalize (env "a" + env "b" * Real.artanh (env "c" + env "d" * t)) ^ k = R1
    generalize (env "e" + env "f" * t) ^ j = P
    generalize (env "e" + env "f" * t) ^ (j + 1) = P1
    generalize env "c" + env "d" * t = y at hY ⊢
    field_simp
    ring

theorem rubi735r7Nondeg_real : rubi735r7Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi735r7Nondeg.conditions rubi735r7Nondeg.body
    rubi735r7Nondeg.result rubi735r7Nondeg.integrals
  exact rubi732r7Nondeg_real

/-! ## RUBI 7.3.2 #8 (and 7.3.5 #8) -/

theorem rubi732r8Nondeg_real : rubi732r8Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi732r8Nondeg.conditions rubi732r8Nondeg.body
    rubi732r8Nondeg.result rubi732r8Nondeg.integrals
  intro env hc t hF
  have hW : env "f" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [rubi732r8Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi732r8Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hmneg : env "m" < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi732r8Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨hf, hm1⟩ := hW'
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi732r8Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi732r8Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have hj : j < -1 := by
    have : (j : ℝ) < -1 := hm ▸ hmneg
    exact_mod_cast this
  have hj0 : j < 0 := by omega
  have hj1 : j + 1 < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hk1' : ¬ k < 1 := by omega
  have em1 : intValue? (env "m" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have ep1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi732r8Nondeg.body →
      env "e" + env "f" * w ≠ 0 ∧ env "c" + env "d" * w ≠ 0 ∧
        (-1 < (env "c" + env "d" * w)⁻¹ ∧ (env "c" + env "d" * w)⁻¹ < 1) := by
    intro w h
    simp [rubi732r8Nondeg, Defined, eval, Interp.real, hkm, hkp, hk0, hj0, ivm1R] at h
    tauto
  obtain ⟨hL0, h0, h1, h2⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi732r8Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hLw, hw0, hw1, hw2⟩ := hD w hw
    have hq := one_sub_sq_inv_lin_ne hw1 hw2
    simp [Defined, eval, Interp.real, em1, ep1, ivm1R, iv2R, hk1', hw0, hw1, hw2, hLw,
      sub_eq_add_neg] at hq ⊢
    exact hq
  · filter_upwards [hF] with w hw
    obtain ⟨hLw, hw0, hw1, hw2⟩ := hD w hw
    simp [rubi732r8Nondeg, Defined, eval, recEnv, Interp.real, em1, hkp, ivm1R, hf, hm1, hk0,
      hw0, hw1, hw2, hLw]
  · simp only [rubi732r8Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ (j + 1) *
        (env "a" + env "b" * Real.artanh (env "c" + env "d" * t)⁻¹) ^ (k - 1) *
        (1 - (env "c" + env "d" * t) ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, ep1, ivm1R, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi732r8Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi732r8Nondeg.result) =
        fun w => (env "e" + env "f" * w) ^ (j + 1) *
            (env "a" + env "b" * Real.artanh (env "c" + env "d" * w)⁻¹) ^ k *
            (env "f" * (env "m" + 1))⁻¹ +
          -env "b" * env "d" * env "p" * (env "f" * (env "m" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi732r8Nondeg, eval, recEnv, Interp.real, em1, hkp, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi732r8Nondeg.body =
        (env "e" + env "f" * t) ^ j *
          (env "a" + env "b" * Real.artanh (env "c" + env "d" * t)⁻¹) ^ k := by
      simp [rubi732r8Nondeg, eval, Interp.real, hkm, hkp, ivm1R]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_artanh_inv_lin h0 h1 h2).const_mul (env "b")).const_add (env "a")
    have hP := (hasDerivAt_zpow (j + 1) _ (Or.inl hL0)).comp t
      (hasDerivAt_lin (env "e") (env "f") t)
    have hQ := (hasDerivAt_zpow k _ (Or.inr hk.le)).comp t hA
    refine (((hP.mul hQ).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    rw [show j + 1 - 1 = j by ring]
    have hjr : ((j + 1 : ℤ) : ℝ) = env "m" + 1 := by rw [hm]; push_cast; ring
    have hkr : ((k : ℤ) : ℝ) = env "p" := hp.symm
    rw [hjr, hkr]
    have hY := one_sub_sq_inv_lin_ne h1 h2
    generalize (env "a" + env "b" * Real.artanh (env "c" + env "d" * t)⁻¹) ^ (k - 1) = R
    generalize (env "a" + env "b" * Real.artanh (env "c" + env "d" * t)⁻¹) ^ k = R1
    generalize (env "e" + env "f" * t) ^ j = P
    generalize (env "e" + env "f" * t) ^ (j + 1) = P1
    generalize env "c" + env "d" * t = y at hY ⊢
    field_simp
    ring

theorem rubi735r8Nondeg_real : rubi735r8Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi735r8Nondeg.conditions rubi735r8Nondeg.body
    rubi735r8Nondeg.result rubi735r8Nondeg.integrals
  exact rubi732r8Nondeg_real

/-! ## RUBI 7.3.1 #9 (and 7.3.3 #1) -/

theorem rubi731r9Nondeg_real : rubi731r9Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r9Nondeg.conditions rubi731r9Nondeg.body
    rubi731r9Nondeg.result rubi731r9Nondeg.integrals
  intro env hc t hF
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi731r9Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r9Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hrel : env "c" ^ 2 * env "d" ^ 2 = env "e" ^ 2 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2)))
      (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi731r9Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hd : env "d" ≠ 0 := by
    intro h; apply he
    have : env "e" ^ 2 = 0 := by rw [← hrel, h]; ring
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r9Nondeg, Defined, eval, Interp.real, hkp] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hk1' : ¬ k < 1 := by omega
  have ep1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  -- `1 + e x / d > 0` where `|c x| < 1`, since `(e/d)^2 = c^2`
  have hlin : ∀ w : ℝ, -1 < env "c" * w → env "c" * w < 1 →
      0 < 1 + env "e" * w * (env "d")⁻¹ := by
    intro w h1 h2
    have hsq : (env "e" * w * (env "d")⁻¹) ^ 2 = (env "c" * w) ^ 2 := by
      field_simp
      linear_combination w ^ 2 * hrel.symm
    have hab : |env "e" * w * (env "d")⁻¹| < 1 := by
      rw [← sq_lt_one_iff_abs_lt_one, hsq, sq_lt_one_iff_abs_lt_one, abs_lt]; exact ⟨h1, h2⟩
    have := (abs_lt.mp hab).1
    linarith
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r9Nondeg.body →
      env "d" + env "e" * w ≠ 0 ∧ (-1 < env "c" * w ∧ env "c" * w < 1) := by
    intro w h
    simp [rubi731r9Nondeg, Defined, eval, Interp.real, hkp, hk0, ivm1R] at h
    tauto
  obtain ⟨hL0, h1, h2⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r9Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨-, hw1, hw2⟩ := hD w hw
    have hq := one_sub_sq_mul_ne hw1 hw2
    have hl := hlin w hw1 hw2
    simp [Defined, eval, Interp.real, ep1, ivm1R, iv2R, hk1', hw1, hw2, hl, hl.ne', hd,
      sub_eq_add_neg] at hq ⊢
    exact hq
  · filter_upwards [hF] with w hw
    obtain ⟨-, hw1, hw2⟩ := hD w hw
    have hl := hlin w hw1 hw2
    simp [rubi731r9Nondeg, Defined, eval, recEnv, Interp.real, hkp, ivm1R, he, hd, hk0, hw1, hw2,
      hl, hl.ne']
  · simp only [rubi731r9Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) *
          Real.log (2 * (1 + env "e" * t * (env "d")⁻¹)⁻¹) * (1 - env "c" ^ 2 * t ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, ep1, ivm1R, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r9Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r9Nondeg.result) =
        fun w => -(env "a" + env "b" * Real.artanh (env "c" * w)) ^ k *
            Real.log (2 * (1 + env "e" * w * (env "d")⁻¹)⁻¹) * (env "e")⁻¹ +
          env "b" * env "c" * env "p" * (env "e")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi731r9Nondeg, eval, recEnv, Interp.real, hkp, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r9Nondeg.body =
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k * (env "d" + env "e" * t)⁻¹ := by
      simp [rubi731r9Nondeg, eval, Interp.real, hkp, ivm1R]
    rw [hfun, hEF]
    have hl := hlin t h1 h2
    have hA := ((hasDerivAt_artanh_mul h1 h2).const_mul (env "b")).const_add (env "a")
    have hQ := (hasDerivAt_zpow k _ (Or.inr hk.le)).comp t hA
    have hU : HasDerivAt (fun w => 1 + env "e" * w * (env "d")⁻¹) (env "e" * (env "d")⁻¹) t := by
      have := (((hasDerivAt_id' t).const_mul (env "e")).mul_const (env "d")⁻¹).const_add 1
      simpa using this
    have hLg := ((hU.inv hl.ne').const_mul 2).log
      (by positivity : (2 : ℝ) * (1 + env "e" * t * (env "d")⁻¹)⁻¹ ≠ 0)
    refine (((hQ.neg.mul hLg).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Pi.neg_apply, Pi.inv_apply, Function.comp_apply]
    have hkr : ((k : ℤ) : ℝ) = env "p" := hp.symm
    rw [hkr]
    have hD' := one_sub_sq_mul_ne h1 h2
    have hD'' : 1 - t ^ 2 * env "c" ^ 2 ≠ 0 := by rwa [mul_comm] at hD'
    have hl' : env "d" + env "e" * t ≠ 0 := hL0
    have hl'' : 1 + env "e" * t * (env "d")⁻¹ ≠ 0 := hl.ne'
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) = R
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k = R1
    generalize Real.log (2 * (1 + env "e" * t * (env "d")⁻¹)⁻¹) = L
    field_simp
    ring

theorem rubi733r1Nondeg_real : rubi733r1Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi733r1Nondeg.conditions rubi733r1Nondeg.body
    rubi733r1Nondeg.result rubi733r1Nondeg.integrals
  exact rubi731r9Nondeg_real

/-! ## RUBI 7.3.5 #6 (and 7.3.2 #6, second form) -/

theorem rubi735r6Nondeg_real : rubi735r6Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi735r6Nondeg.conditions
    rubi735r6Nondeg.body rubi735r6Nondeg.result rubi735r6Nondeg.integrals
    rubi735r6Nondeg.substs
  intro env hc t hF
  have hne : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi735r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi735r6Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hrel : env "d" * env "e" = env "c" * env "f" := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "d") (.var "e"))
      (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f"))) (.int 0))
      (by simp [rubi735r6Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi735r6Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi735r6Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have hk0 : ¬ k < 0 := by omega
  have hlin : ∀ w, env "f" * (env "c" + env "d" * w) * (env "d")⁻¹ = env "e" + env "f" * w := by
    intro w
    field_simp
    linear_combination -hrel
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi735r6Nondeg.body →
      (m < 0 → env "e" + env "f" * w ≠ 0) ∧
        env "c" + env "d" * w ≠ 0 ∧
        (-1 < (env "c" + env "d" * w)⁻¹ ∧ (env "c" + env "d" * w)⁻¹ < 1) := by
    intro w h
    simp [rubi735r6Nondeg, Defined, eval, Interp.real, hkm, hkp, hk0, ivm1R] at h
    tauto
  obtain ⟨hm0, h0, h1, h2⟩ := hD t hF.self_of_nhds
  have hinv : ContinuousAt (fun u : ℝ => u⁻¹) (env "c" + env "d" * t) :=
    continuousAt_inv₀ h0
  have hcf : ContinuousAt (fun u : ℝ => env "f" * u * (env "d")⁻¹) (env "c" + env "d" * t) := by
    fun_prop
  have hnear : ∀ᶠ u : ℝ in 𝓝 (env "c" + env "d" * t),
      (m < 0 → env "f" * u * (env "d")⁻¹ ≠ 0) ∧ u ≠ 0 ∧ (-1 < u⁻¹ ∧ u⁻¹ < 1) := by
    by_cases hmn : m < 0
    · have hv : env "f" * (env "c" + env "d" * t) * (env "d")⁻¹ ≠ 0 := by
        rw [hlin]; exact hm0 hmn
      filter_upwards [hcf.tendsto.eventually (eventually_ne_nhds hv), eventually_ne_nhds h0,
        hinv.tendsto.eventually (isOpen_Ioi.mem_nhds h1),
        hinv.tendsto.eventually (isOpen_Iio.mem_nhds h2)] with u hz h0 hu hv
      exact ⟨fun _ => hz, h0, hu, hv⟩
    · filter_upwards [eventually_ne_nhds h0, hinv.tendsto.eventually (isOpen_Ioi.mem_nhds h1),
        hinv.tendsto.eventually (isOpen_Iio.mem_nhds h2)] with u h0 hu hv
      exact ⟨fun h => absurd h hmn, h0, hu, hv⟩
  have hsub : substAt Interp.real env rubi735r6Nondeg.substs "x" "I1" t =
      env "c" + env "d" * t := by
    simp [rubi735r6Nondeg, substAt, eval]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi735r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards with w
      intro g hg
      simp only [rubi735r6Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined]
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or] at hu
      simp [Defined, eval, Interp.real, hkm, hkp, hk0, ivm1R, hu.2.1, hu.2.2.1, hu.2.2.2]
      tauto
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi735r6Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hne]
    · simp only [rubi735r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "f" * (env "c" + env "d" * t) * (env "d")⁻¹) ^ m *
            (env "a" + env "b" * Real.artanh (env "c" + env "d" * t)⁻¹) ^ k)
          (env "c" + env "d" * t) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkm, hkp, ivm1R]
      have h := (hΦ'.comp t (hasDerivAt_lin (env "c") (env "d") t)).const_mul (env "d")⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi735r6Nondeg.integrals.map (·.1))
            rubi735r6Nondeg.substs Φ "x" w) rubi735r6Nondeg.result) =
          fun w => (env "d")⁻¹ * Φ "I1" (env "c" + env "d" * w) := by
        funext w
        simp [rubi735r6Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      apply h.congr_deriv
      simp only [hlin]
      simp [rubi735r6Nondeg, eval, Interp.real, hkm, hkp, ivm1R]
      field_simp

theorem rubi732r6yNondeg_real : rubi732r6yNondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi732r6yNondeg.conditions
    rubi732r6yNondeg.body rubi732r6yNondeg.result rubi732r6yNondeg.integrals
    rubi732r6yNondeg.substs
  exact rubi735r6Nondeg_real

end OSR.IntegrationRec235
