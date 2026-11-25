import OSR.IntegrationNum1
import OSR.IntegrationRec131

/-! # Strengthened inverse hyperbolic tangent rules integrated by parts

Proofs over ℝ of strengthened variants of `OSR.IntegrationNum1` that integrate
`(a + b artanh(c x))` against a power by parts, leaving one residual integral. The inverse
hyperbolic tangent has no complex interpretation in the fragment, so the complex statement
is vacuous and stays unproved. Each 7.3.1 rule has a 7.3.3 or 7.3.4 twin with the same
statement, which reuses its proof. -/

namespace OSR.IntegrationRec213

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem hasDerivAt_lin (a b t : ℝ) : HasDerivAt (fun w => a + b * w) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

private theorem hasDerivAt_quad0 (a b t : ℝ) :
    HasDerivAt (fun w => a + b * w ^ 2) (2 * b * t) t := by
  have h := ((hasDerivAt_pow 2 t).const_mul b).const_add a
  refine h.congr_deriv ?_
  simp; ring

private theorem zpow_succ_of (A : ℝ) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem one_sub_sq_ne {u : ℝ} (h1 : -1 < u) (h2 : u < 1) : 1 - u ^ 2 ≠ 0 :=
  (sub_pos.mpr (by nlinarith)).ne'

/-! ## RUBI 7.3.1 #17 (and 7.3.3 #9): `∫ (d + e x)^q (a + b artanh(c x)) dx` -/

theorem rubi731r17Nondeg_real : rubi731r17Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r17Nondeg.conditions rubi731r17Nondeg.body
    rubi731r17Nondeg.result rubi731r17Nondeg.integrals
  intro env hc t hF
  have hW : env "e" * (env "q" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "q") (.int 1))) (.int 0))
      (by simp [rubi731r17Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨he, hq1⟩ := hW'
  rcases hkq : intValue? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r17Nondeg, Defined, eval, Interp.real, hkq] at h
  have hq : env "q" = (k : ℝ) := (intValue?_eq _ _).1 hkq
  have e1 : intValue? (env "q" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r17Nondeg.body →
      (k < 0 → env "d" + env "e" * w ≠ 0) ∧ (-1 < env "c" * w ∧ env "c" * w < 1) := by
    intro w h
    simp [rubi731r17Nondeg, Defined, eval, Interp.real, hkq] at h
    tauto
  have hden : ∀ w, -1 < env "c" * w → env "c" * w < 1 → 1 - env "c" ^ 2 * w ^ 2 ≠ 0 := by
    intro w h1 h2
    have := one_sub_sq_ne h1 h2
    rwa [mul_pow] at this
  obtain ⟨hk0, hc1, hc2⟩ := hBody t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb := hBody w hw
    have hD := hden w hb.2.1 hb.2.2
    simp [Defined, eval, Interp.real, e1, iv2R, ivm1R]
    refine ⟨fun h => hb.1 (by omega), fun h0 => hD (by linear_combination h0)⟩
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [rubi731r17Nondeg, Defined, eval, recEnv, Interp.real, e1, ivm1R, he, hq1, hb.2.1, hb.2.2]
    intro h
    exact hb.1 (by omega)
  · simp only [rubi731r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "d" + env "e" * t) ^ (k + 1) * (1 - env "c" ^ 2 * t ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, e1, iv2R, ivm1R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring_nf
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r17Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r17Nondeg.result) =
        fun w => (env "d" + env "e" * w) ^ (k + 1) * (env "a" + env "b" *
          Real.artanh (env "c" * w)) * (env "e" * (env "q" + 1))⁻¹ +
          -(env "b" * env "c") * (env "e" * (env "q" + 1))⁻¹ * Φ "I1" w := by
      funext w; simp [rubi731r17Nondeg, eval, recEnv, Interp.real, e1, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r17Nondeg.body =
        (env "d" + env "e" * t) ^ k * (env "a" + env "b" * Real.artanh (env "c" * t)) := by
      simp [rubi731r17Nondeg, eval, Interp.real, hkq]
    rw [hfun, hEF]
    have hz : env "d" + env "e" * t ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (hk0 h)
      · exact Or.inr (by omega)
    have hz0 : env "d" + env "e" * t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (hk0 h)
      · exact Or.inr (by omega)
    have hP := (hasDerivAt_zpow (k + 1) _ hz).comp t (hasDerivAt_lin (env "d") (env "e") t)
    have hA := (((OSR.IntegrationRec131.hasDerivAt_artanh hc1 hc2).comp t
      ((hasDerivAt_id' t).const_mul (env "c"))).const_mul (env "b")).const_add (env "a")
    refine (((hP.mul hA).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hz0]
    have hk1 : ((k + 1 : ℤ) : ℝ) = env "q" + 1 := by rw [hq]; push_cast; ring
    rw [hk1, mul_pow]
    have hD := hden t hc1 hc2
    generalize (env "d" + env "e" * t) ^ k = P
    generalize Real.artanh (env "c" * t) = T
    field_simp
    ring

theorem rubi733r9Nondeg_real : rubi733r9Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi733r9Nondeg.conditions rubi733r9Nondeg.body
    rubi733r9Nondeg.result rubi733r9Nondeg.integrals
  exact rubi731r17Nondeg_real

/-! ## RUBI 7.3.1 #123 (and 7.3.4 #103): `∫ x (d + e x^2)^q (a + b artanh(c x)) dx` -/

theorem rubi731r123Nondeg_real : rubi731r123Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r123Nondeg.conditions rubi731r123Nondeg.body
    rubi731r123Nondeg.result rubi731r123Nondeg.integrals
  intro env hc t hF
  have hW : 2 * env "e" * (env "q" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "q") (.int 1)))
      (.int 0)) (by simp [rubi731r123Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨-, he⟩, hq1⟩ := hW'
  rcases hkq : intValue? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r123Nondeg, Defined, eval, Interp.real, hkq] at h
  have hq : env "q" = (k : ℝ) := (intValue?_eq _ _).1 hkq
  have e1 : intValue? (env "q" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r123Nondeg.body →
      (k < 0 → env "d" + env "e" * w ^ 2 ≠ 0) ∧ (-1 < env "c" * w ∧ env "c" * w < 1) := by
    intro w h
    simp [rubi731r123Nondeg, Defined, eval, Interp.real, hkq, iv2R] at h
    tauto
  have hden : ∀ w, -1 < env "c" * w → env "c" * w < 1 → 1 - env "c" ^ 2 * w ^ 2 ≠ 0 := by
    intro w h1 h2
    have := one_sub_sq_ne h1 h2
    rwa [mul_pow] at this
  obtain ⟨hk0, hc1, hc2⟩ := hBody t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r123Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb := hBody w hw
    have hD := hden w hb.2.1 hb.2.2
    simp [Defined, eval, Interp.real, e1, iv2R, ivm1R]
    refine ⟨fun h => hb.1 (by omega), fun h0 => hD (by linear_combination h0)⟩
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [rubi731r123Nondeg, Defined, eval, recEnv, Interp.real, e1, ivm1R, iv2R, he, hq1,
      hb.2.1, hb.2.2]
    intro h
    exact hb.1 (by omega)
  · simp only [rubi731r123Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "d" + env "e" * t ^ 2) ^ (k + 1) * (1 - env "c" ^ 2 * t ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, e1, iv2R, ivm1R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring_nf
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r123Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r123Nondeg.result) =
        fun w => (env "d" + env "e" * w ^ 2) ^ (k + 1) * (env "a" + env "b" *
          Real.artanh (env "c" * w)) * (2 * env "e" * (env "q" + 1))⁻¹ +
          -(env "b" * env "c") * (2 * env "e" * (env "q" + 1))⁻¹ * Φ "I1" w := by
      funext w; simp [rubi731r123Nondeg, eval, recEnv, Interp.real, e1, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r123Nondeg.body =
        t * (env "d" + env "e" * t ^ 2) ^ k * (env "a" + env "b" * Real.artanh (env "c" * t)) := by
      simp [rubi731r123Nondeg, eval, Interp.real, hkq, iv2R]
    rw [hfun, hEF]
    have hz : env "d" + env "e" * t ^ 2 ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (hk0 h)
      · exact Or.inr (by omega)
    have hz0 : env "d" + env "e" * t ^ 2 ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (hk0 h)
      · exact Or.inr (by omega)
    have hP := (hasDerivAt_zpow (k + 1) _ hz).comp t (hasDerivAt_quad0 (env "d") (env "e") t)
    have hA := (((OSR.IntegrationRec131.hasDerivAt_artanh hc1 hc2).comp t
      ((hasDerivAt_id' t).const_mul (env "c"))).const_mul (env "b")).const_add (env "a")
    refine (((hP.mul hA).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hz0]
    have hk1 : ((k + 1 : ℤ) : ℝ) = env "q" + 1 := by rw [hq]; push_cast; ring
    rw [hk1, mul_pow]
    have hD := hden t hc1 hc2
    generalize (env "d" + env "e" * t ^ 2) ^ k = P
    generalize Real.artanh (env "c" * t) = T
    field_simp
    ring

theorem rubi734r103Nondeg_real : rubi734r103Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r103Nondeg.conditions rubi734r103Nondeg.body
    rubi734r103Nondeg.result rubi734r103Nondeg.integrals
  exact rubi731r123Nondeg_real

/-! ## RUBI 7.3.1 #124 (and 7.3.4 #104): `∫ x (d + e x^2)^q (a + b artanh(1/(c x))) dx` -/

theorem rubi731r124Nondeg_real : rubi731r124Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r124Nondeg.conditions rubi731r124Nondeg.body
    rubi731r124Nondeg.result rubi731r124Nondeg.integrals
  intro env hc t hF
  have hW : 2 * env "e" * (env "q" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "q") (.int 1)))
      (.int 0)) (by simp [rubi731r124Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨-, he⟩, hq1⟩ := hW'
  rcases hkq : intValue? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r124Nondeg, Defined, eval, Interp.real, hkq] at h
  have hq : env "q" = (k : ℝ) := (intValue?_eq _ _).1 hkq
  have e1 : intValue? (env "q" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r124Nondeg.body →
      (k < 0 → env "d" + env "e" * w ^ 2 ≠ 0) ∧ (¬ env "c" = 0 ∧ ¬ w = 0) ∧
        (-1 < w⁻¹ * (env "c")⁻¹ ∧ w⁻¹ * (env "c")⁻¹ < 1) := by
    intro w h
    simp [rubi731r124Nondeg, Defined, eval, Interp.real, hkq, iv2R, ivm1R] at h
    tauto
  have hden : ∀ w, w ≠ 0 → env "c" ≠ 0 → -1 < w⁻¹ * (env "c")⁻¹ → w⁻¹ * (env "c")⁻¹ < 1 →
      1 - env "c" ^ 2 * w ^ 2 ≠ 0 := by
    intro w hw hcz h1 h2
    have hcw : env "c" * w ≠ 0 := mul_ne_zero hcz hw
    have hy2 : (w⁻¹ * (env "c")⁻¹) ^ 2 < 1 := by nlinarith
    have hm : (env "c" * w) ^ 2 * (w⁻¹ * (env "c")⁻¹) ^ 2 = 1 := by
      rw [← mul_pow, ← mul_inv_rev, mul_inv_cancel₀ hcw, one_pow]
    have hgt : 1 < (env "c" * w) ^ 2 := by nlinarith [sq_nonneg (w⁻¹ * (env "c")⁻¹)]
    rw [mul_pow] at hgt
    linarith
  obtain ⟨hk0, ⟨hcz, ht0⟩, hc1, hc2⟩ := hBody t hF.self_of_nhds
  have hct : env "c" * t ≠ 0 := mul_ne_zero hcz ht0
  have hinv : (env "c" * t)⁻¹ = t⁻¹ * (env "c")⁻¹ := mul_inv_rev _ _
  have h1 : -1 < (env "c" * t)⁻¹ := by rw [hinv]; exact hc1
  have h2 : (env "c" * t)⁻¹ < 1 := by rw [hinv]; exact hc2
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r124Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb := hBody w hw
    have hD := hden w hb.2.1.2 hb.2.1.1 hb.2.2.1 hb.2.2.2
    simp [Defined, eval, Interp.real, e1, iv2R, ivm1R]
    refine ⟨fun h => hb.1 (by omega), fun h0 => hD (by linear_combination h0)⟩
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [rubi731r124Nondeg, Defined, eval, recEnv, Interp.real, e1, ivm1R, iv2R, he, hq1,
      hb.2.1.1, hb.2.1.2, hb.2.2.1, hb.2.2.2]
    intro h
    exact hb.1 (by omega)
  · simp only [rubi731r124Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "d" + env "e" * t ^ 2) ^ (k + 1) * (1 - env "c" ^ 2 * t ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, e1, iv2R, ivm1R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring_nf
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r124Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r124Nondeg.result) =
        fun w => (env "d" + env "e" * w ^ 2) ^ (k + 1) * (env "a" + env "b" *
          Real.artanh (env "c" * w)⁻¹) * (2 * env "e" * (env "q" + 1))⁻¹ +
          -(env "b" * env "c") * (2 * env "e" * (env "q" + 1))⁻¹ * Φ "I1" w := by
      funext w; simp [rubi731r124Nondeg, eval, recEnv, Interp.real, e1, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r124Nondeg.body =
        t * (env "d" + env "e" * t ^ 2) ^ k *
          (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) := by
      simp [rubi731r124Nondeg, eval, Interp.real, hkq, iv2R, ivm1R]
    rw [hfun, hEF]
    have hz : env "d" + env "e" * t ^ 2 ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (hk0 h)
      · exact Or.inr (by omega)
    have hz0 : env "d" + env "e" * t ^ 2 ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (hk0 h)
      · exact Or.inr (by omega)
    have hP := (hasDerivAt_zpow (k + 1) _ hz).comp t (hasDerivAt_quad0 (env "d") (env "e") t)
    have hA := (((OSR.IntegrationRec131.hasDerivAt_artanh h1 h2).comp t
      (((hasDerivAt_id' t).const_mul (env "c")).inv hct)).const_mul (env "b")).const_add (env "a")
    refine (((hP.mul hA).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply, Pi.inv_apply, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hz0]
    have hk1 : ((k + 1 : ℤ) : ℝ) = env "q" + 1 := by rw [hq]; push_cast; ring
    rw [hk1]
    have hD := hden t ht0 hcz hc1 hc2
    have hD2 : 1 - (env "c" * t) ^ 2 ≠ 0 := by rwa [mul_pow]
    have key : (1 - ((env "c" * t)⁻¹) ^ 2)⁻¹ * (-(env "c" * 1) / (env "c" * t) ^ 2) =
        env "c" * (1 - env "c" ^ 2 * t ^ 2)⁻¹ := by
      have h3 : 1 - ((env "c" * t)⁻¹) ^ 2 = -(1 - (env "c" * t) ^ 2) / (env "c" * t) ^ 2 := by
        field_simp
        ring
      rw [h3, ← mul_pow]
      field_simp
    rw [key]
    generalize (env "d" + env "e" * t ^ 2) ^ k = P
    generalize Real.artanh (env "c" * t)⁻¹ = T
    field_simp
    ring

theorem rubi734r104Nondeg_real : rubi734r104Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r104Nondeg.conditions rubi734r104Nondeg.body
    rubi734r104Nondeg.result rubi734r104Nondeg.integrals
  exact rubi731r124Nondeg_real

/-! ## RUBI 7.3.1 #18 (and 7.3.3 #10): `∫ (d + e x)^q (a + b artanh(1/(c x))) dx` -/

theorem rubi731r18Nondeg_real : rubi731r18Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r18Nondeg.conditions rubi731r18Nondeg.body
    rubi731r18Nondeg.result rubi731r18Nondeg.integrals
  intro env hc t hF
  have hW : env "e" * (env "q" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "q") (.int 1))) (.int 0))
      (by simp [rubi731r18Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨he, hq1⟩ := hW'
  rcases hkq : intValue? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r18Nondeg, Defined, eval, Interp.real, hkq] at h
  have hq : env "q" = (k : ℝ) := (intValue?_eq _ _).1 hkq
  have e1 : intValue? (env "q" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r18Nondeg.body →
      (k < 0 → env "d" + env "e" * w ≠ 0) ∧ (¬ env "c" = 0 ∧ ¬ w = 0) ∧
        (-1 < w⁻¹ * (env "c")⁻¹ ∧ w⁻¹ * (env "c")⁻¹ < 1) := by
    intro w h
    simp [rubi731r18Nondeg, Defined, eval, Interp.real, hkq, ivm1R] at h
    tauto
  have hden : ∀ w, w ≠ 0 → env "c" ≠ 0 → -1 < w⁻¹ * (env "c")⁻¹ → w⁻¹ * (env "c")⁻¹ < 1 →
      1 - env "c" ^ 2 * w ^ 2 ≠ 0 := by
    intro w hw hcz h1 h2
    have hcw : env "c" * w ≠ 0 := mul_ne_zero hcz hw
    have hy2 : (w⁻¹ * (env "c")⁻¹) ^ 2 < 1 := by nlinarith
    have hm : (env "c" * w) ^ 2 * (w⁻¹ * (env "c")⁻¹) ^ 2 = 1 := by
      rw [← mul_pow, ← mul_inv_rev, mul_inv_cancel₀ hcw, one_pow]
    have hgt : 1 < (env "c" * w) ^ 2 := by nlinarith [sq_nonneg (w⁻¹ * (env "c")⁻¹)]
    rw [mul_pow] at hgt
    linarith
  obtain ⟨hk0, ⟨hcz, ht0⟩, hc1, hc2⟩ := hBody t hF.self_of_nhds
  have hct : env "c" * t ≠ 0 := mul_ne_zero hcz ht0
  have hinv : (env "c" * t)⁻¹ = t⁻¹ * (env "c")⁻¹ := mul_inv_rev _ _
  have h1 : -1 < (env "c" * t)⁻¹ := by rw [hinv]; exact hc1
  have h2 : (env "c" * t)⁻¹ < 1 := by rw [hinv]; exact hc2
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r18Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb := hBody w hw
    have hD := hden w hb.2.1.2 hb.2.1.1 hb.2.2.1 hb.2.2.2
    simp [Defined, eval, Interp.real, e1, iv2R, ivm1R]
    refine ⟨fun h => hb.1 (by omega), fun h0 => hD (by linear_combination h0)⟩
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [rubi731r18Nondeg, Defined, eval, recEnv, Interp.real, e1, ivm1R, he, hq1,
      hb.2.1.1, hb.2.1.2, hb.2.2.1, hb.2.2.2]
    intro h
    exact hb.1 (by omega)
  · simp only [rubi731r18Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "d" + env "e" * t) ^ (k + 1) * (1 - env "c" ^ 2 * t ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, e1, iv2R, ivm1R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring_nf
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r18Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r18Nondeg.result) =
        fun w => (env "d" + env "e" * w) ^ (k + 1) * (env "a" + env "b" *
          Real.artanh (env "c" * w)⁻¹) * (env "e" * (env "q" + 1))⁻¹ +
          -(env "b" * env "c") * (env "e" * (env "q" + 1))⁻¹ * Φ "I1" w := by
      funext w; simp [rubi731r18Nondeg, eval, recEnv, Interp.real, e1, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r18Nondeg.body =
        (env "d" + env "e" * t) ^ k *
          (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) := by
      simp [rubi731r18Nondeg, eval, Interp.real, hkq, ivm1R]
    rw [hfun, hEF]
    have hz : env "d" + env "e" * t ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (hk0 h)
      · exact Or.inr (by omega)
    have hz0 : env "d" + env "e" * t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (hk0 h)
      · exact Or.inr (by omega)
    have hP := (hasDerivAt_zpow (k + 1) _ hz).comp t (hasDerivAt_lin (env "d") (env "e") t)
    have hA := (((OSR.IntegrationRec131.hasDerivAt_artanh h1 h2).comp t
      (((hasDerivAt_id' t).const_mul (env "c")).inv hct)).const_mul (env "b")).const_add (env "a")
    refine (((hP.mul hA).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply, Pi.inv_apply, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hz0]
    have hk1 : ((k + 1 : ℤ) : ℝ) = env "q" + 1 := by rw [hq]; push_cast; ring
    rw [hk1]
    have hD := hden t ht0 hcz hc1 hc2
    have hD2 : 1 - (env "c" * t) ^ 2 ≠ 0 := by rwa [mul_pow]
    have key : (1 - ((env "c" * t)⁻¹) ^ 2)⁻¹ * (-(env "c" * 1) / (env "c" * t) ^ 2) =
        env "c" * (1 - env "c" ^ 2 * t ^ 2)⁻¹ := by
      have h3 : 1 - ((env "c" * t)⁻¹) ^ 2 = -(1 - (env "c" * t) ^ 2) / (env "c" * t) ^ 2 := by
        field_simp
        ring
      rw [h3, ← mul_pow]
      field_simp
    rw [key]
    generalize (env "d" + env "e" * t) ^ k = P
    generalize Real.artanh (env "c" * t)⁻¹ = T
    field_simp
    ring

theorem rubi733r10Nondeg_real : rubi733r10Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi733r10Nondeg.conditions rubi733r10Nondeg.body
    rubi733r10Nondeg.result rubi733r10Nondeg.integrals
  exact rubi731r18Nondeg_real

end OSR.IntegrationRec213
