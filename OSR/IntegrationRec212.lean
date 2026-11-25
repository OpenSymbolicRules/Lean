import OSR.IntegrationNum1
import OSR.IntegrationRec131

/-! # Strengthened variants without residual integrals: inverse hyperbolic tangent powers and
a sine power

Proofs of strengthened variants of `OSR.IntegrationNum1` with a closed result (shape
`antideriv`). The inverse hyperbolic tangent has no complex interpretation in the fragment,
so its rules are proved over ℝ only (the complex statement is vacuous and stays unproved). -/

namespace OSR.IntegrationRec212

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem hasDerivAt_lin {𝕜 : Type} [NontriviallyNormedField 𝕜] (a b t : 𝕜) :
    HasDerivAt (fun w => a + b * w) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

private theorem zpow_succ_of {𝕜 : Type} [Field 𝕜] (A : 𝕜) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) :
    A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

/-! ## RUBI 7.3.1 #35 (and 7.3.4 #15): `∫ (a + b artanh(c x))^p / (d + e x^2) dx`,
`c^2 d + e = 0` -/

theorem rubi731r35Nondeg_real : rubi731r35Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi731r35Nondeg.conditions rubi731r35Nondeg.body
    rubi731r35Nondeg.result
  intro env hc t hF
  have hW : env "b" * env "c" * env "d" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d"))
      (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi731r35Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r35Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r35Nondeg, Defined, eval, Interp.real, hkp] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have e1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨⟨hb, hcz⟩, hd⟩, hp1⟩ := hW'
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r35Nondeg.body →
      (-1 < env "c" * w ∧ env "c" * w < 1) ∧
        (k < 0 → env "a" + env "b" * Real.artanh (env "c" * w) ≠ 0) := by
    intro w h
    simp [rubi731r35Nondeg, Defined, eval, Interp.real, hkp, ivm1R, iv2R] at h
    tauto
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi731r35Nondeg, Defined, eval, Interp.real, e1, ivm1R, hb, hcz, hd, hp1, h.1.1, h.1.2]
    intro hk
    exact h.2 (by omega)
  · have ht := hD t hF.self_of_nhds
    set U := env "a" + env "b" * Real.artanh (env "c" * t) with hU
    have hfun : (fun w => eval Interp.real (Function.update env "x" w) rubi731r35Nondeg.result) =
        fun w => (env "a" + env "b" * Real.artanh (env "c" * w)) ^ (k + 1) *
          (env "b" * env "c" * env "d" * (env "p" + 1))⁻¹ := by
      funext w; simp [rubi731r35Nondeg, eval, Interp.real, e1, ivm1R]
    have hE : eval Interp.real (Function.update env "x" t) rubi731r35Nondeg.body =
        U ^ k * (env "d" + env "e" * t ^ 2)⁻¹ := by
      simp [rubi731r35Nondeg, eval, Interp.real, hkp, ivm1R, iv2R, hU]
    rw [hfun, hE]
    have hz : U ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (ht.2 h)
      · exact Or.inr (by omega)
    have hM := (((OSR.IntegrationRec131.hasDerivAt_artanh ht.1.1 ht.1.2).comp t
      ((hasDerivAt_id' t).const_mul (env "c"))).const_mul (env "b")).const_add (env "a")
    refine (((hasDerivAt_zpow (k + 1) U hz).comp t hM).mul_const _).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have hk1 : ((k + 1 : ℤ) : ℝ) = env "p" + 1 := by rw [hp]; push_cast; ring
    have hne : 1 - (env "c" * t) ^ 2 ≠ 0 := (sub_pos.mpr (by nlinarith [ht.1.1, ht.1.2])).ne'
    have hden : env "d" + env "e" * t ^ 2 = env "d" * (1 - (env "c" * t) ^ 2) := by
      linear_combination t ^ 2 * hrel
    rw [hk1, hden]
    generalize U ^ k = P
    field_simp

theorem rubi734r15Nondeg_real : rubi734r15Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi734r15Nondeg.conditions rubi734r15Nondeg.body
    rubi734r15Nondeg.result
  exact rubi731r35Nondeg_real

/-! ## RUBI 7.3.1 #36 (and 7.3.4 #16): `∫ (a + b artanh(1/(c x)))^p / (d + e x^2) dx` -/

theorem rubi731r36Nondeg_real : rubi731r36Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi731r36Nondeg.conditions rubi731r36Nondeg.body
    rubi731r36Nondeg.result
  intro env hc t hF
  have hW : env "b" * env "c" * env "d" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d"))
      (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi731r36Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r36Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r36Nondeg, Defined, eval, Interp.real, hkp] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have e1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨⟨hb, hcz⟩, hd⟩, hp1⟩ := hW'
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r36Nondeg.body →
      w ≠ 0 ∧ (-1 < w⁻¹ * (env "c")⁻¹ ∧ w⁻¹ * (env "c")⁻¹ < 1) ∧
        (k < 0 → env "a" + env "b" * Real.artanh (w⁻¹ * (env "c")⁻¹) ≠ 0) := by
    intro w h
    simp [rubi731r36Nondeg, Defined, eval, Interp.real, hkp, ivm1R, iv2R] at h
    tauto
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi731r36Nondeg, Defined, eval, Interp.real, e1, ivm1R, hb, hcz, hd, hp1, h.1,
      h.2.1.1, h.2.1.2]
    intro hk
    exact h.2.2 (by omega)
  · have ht := hD t hF.self_of_nhds
    have hct : env "c" * t ≠ 0 := mul_ne_zero hcz ht.1
    have hinv : (env "c" * t)⁻¹ = t⁻¹ * (env "c")⁻¹ := mul_inv_rev _ _
    have h1 : -1 < (env "c" * t)⁻¹ := by rw [hinv]; exact ht.2.1.1
    have h2 : (env "c" * t)⁻¹ < 1 := by rw [hinv]; exact ht.2.1.2
    set U := env "a" + env "b" * Real.artanh (env "c" * t)⁻¹ with hU
    have hfun : (fun w => eval Interp.real (Function.update env "x" w) rubi731r36Nondeg.result) =
        fun w => (env "a" + env "b" * Real.artanh (env "c" * w)⁻¹) ^ (k + 1) *
          (env "b" * env "c" * env "d" * (env "p" + 1))⁻¹ := by
      funext w; simp [rubi731r36Nondeg, eval, Interp.real, e1, ivm1R]
    have hE : eval Interp.real (Function.update env "x" t) rubi731r36Nondeg.body =
        U ^ k * (env "d" + env "e" * t ^ 2)⁻¹ := by
      simp [rubi731r36Nondeg, eval, Interp.real, hkp, ivm1R, iv2R, hU]
    rw [hfun, hE]
    have hz : U ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (by rw [hU, hinv]; exact ht.2.2 h)
      · exact Or.inr (by omega)
    have hM := (((OSR.IntegrationRec131.hasDerivAt_artanh h1 h2).comp t
      (((hasDerivAt_id' t).const_mul (env "c")).inv hct)).const_mul (env "b")).const_add (env "a")
    refine (((hasDerivAt_zpow (k + 1) U hz).comp t hM).mul_const _).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have hk1 : ((k + 1 : ℤ) : ℝ) = env "p" + 1 := by rw [hp]; push_cast; ring
    have hy2 : ((env "c" * t)⁻¹) ^ 2 < 1 := by nlinarith [h1, h2]
    have hm : (env "c" * t) ^ 2 * ((env "c" * t)⁻¹) ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hct, one_pow]
    have hgt : 1 < (env "c" * t) ^ 2 := by nlinarith [hm, hy2, sq_nonneg ((env "c" * t)⁻¹)]
    have hne : 1 - (env "c" * t) ^ 2 ≠ 0 := by linarith
    have hne' : 1 - ((env "c" * t)⁻¹) ^ 2 ≠ 0 := by linarith
    have hden : env "d" + env "e" * t ^ 2 = env "d" * (1 - (env "c" * t) ^ 2) := by
      linear_combination t ^ 2 * hrel
    rw [hk1, hden]
    generalize U ^ k = P
    have ht0 : t ≠ 0 := ht.1
    field_simp
    rw [show env "c" ^ 2 * t ^ 2 - 1 = -(1 - env "c" ^ 2 * t ^ 2) by ring, div_neg, neg_neg]

theorem rubi734r16Nondeg_real : rubi734r16Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi734r16Nondeg.conditions rubi734r16Nondeg.body
    rubi734r16Nondeg.result
  exact rubi731r36Nondeg_real

/-! ## RUBI 4.1.4.1 #2: `∫ (b sin u)^m (A + C sin^2 u) dx`, `A (m + 2) + C (m + 1) = 0` -/

theorem rubi4141r2Nondeg_real : rubi4141r2Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi4141r2Nondeg.conditions rubi4141r2Nondeg.body
    rubi4141r2Nondeg.result
  intro env hc t hF
  have hW : env "b" * env "f" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m")
      (.int 1))) (.int 0)) (by simp [rubi4141r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "A" * (env "m" + 2) + env "C" * (env "m" + 1) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "A") (.app2 .add (.var "m") (.int 2)))
      (.app2 .mul (.var "C") (.app2 .add (.var "m") (.int 1)))) (.int 0))
      (by simp [rubi4141r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r2Nondeg, Defined, eval, Interp.real, hkm] at h
  have hm : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hkm
  have e1 : intValue? (env "m" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨hb, hf⟩, hm1⟩ := hW'
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4141r2Nondeg.body →
      (k < 0 → env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r2Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
    intro hk
    simpa using h hk
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4141r2Nondeg, Defined, eval, Interp.real, e1, ivm1R, hb, hf, hm1]
    intro hk
    exact (mul_ne_zero_iff.mp (h (by omega))).2
  · have ht := hD t hF.self_of_nhds
    set V := env "b" * Real.sin (env "e" + env "f" * t) with hV
    have hfun : (fun w => eval Interp.real (Function.update env "x" w) rubi4141r2Nondeg.result) =
        fun w => env "A" * Real.cos (env "e" + env "f" * w) *
          (env "b" * Real.sin (env "e" + env "f" * w)) ^ (k + 1) *
          (env "b" * env "f" * (env "m" + 1))⁻¹ := by
      funext w; simp [rubi4141r2Nondeg, eval, Interp.real, e1, ivm1R]
    have hE : eval Interp.real (Function.update env "x" t) rubi4141r2Nondeg.body =
        V ^ k * (env "A" + env "C" * Real.sin (env "e" + env "f" * t) ^ 2) := by
      simp [rubi4141r2Nondeg, eval, Interp.real, hkm, iv2R, hV]
    rw [hfun, hE]
    have hz : V ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    have hz0 : V ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    have hl := hasDerivAt_lin (env "e") (env "f") t
    have hS := ((Real.hasDerivAt_sin _).comp t hl).const_mul (env "b")
    have hC := ((Real.hasDerivAt_cos _).comp t hl).const_mul (env "A")
    refine ((hC.mul ((hasDerivAt_zpow (k + 1) V hz).comp t hS)).mul_const _).congr_deriv ?_
    simp only [Function.comp_apply, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hz0]
    have hk1 : ((k + 1 : ℤ) : ℝ) = env "m" + 1 := by rw [hm]; push_cast; ring
    rw [hk1, hV]
    have hSC := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "b" * Real.sin (env "e" + env "f" * t)) ^ k = P
    generalize Real.sin (env "e" + env "f" * t) = S at hSC ⊢
    generalize Real.cos (env "e" + env "f" * t) = C at hSC ⊢
    field_simp
    linear_combination (env "A" * P * env "m" + env "A" * P) * hSC + (-P * S ^ 2) * hrel

theorem rubi4141r2Nondeg_complex : rubi4141r2Nondeg.Holds .complex := by
  show AntiderivHoldsUnder Interp.complex "x" rubi4141r2Nondeg.conditions rubi4141r2Nondeg.body
    rubi4141r2Nondeg.result
  intro env hc t hF
  have hW : env "b" * env "f" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m")
      (.int 1))) (.int 0)) (by simp [rubi4141r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "A" * (env "m" + 2) + env "C" * (env "m" + 1) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "A") (.app2 .add (.var "m") (.int 2)))
      (.app2 .mul (.var "C") (.app2 .add (.var "m") (.int 1)))) (.int 0))
      (by simp [rubi4141r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r2Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hm : env "m" = (k : ℂ) := (intValue?_eq _ _).1 hkm
  have e1 : intValue? (env "m" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨hb, hf⟩, hm1⟩ := hW'
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4141r2Nondeg.body →
      (k < 0 → env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r2Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
    intro hk
    simpa using h hk
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4141r2Nondeg, Defined, eval, Interp.complex, e1, ivm1C, hb, hf, hm1]
    intro hk
    exact (mul_ne_zero_iff.mp (h (by omega))).2
  · have ht := hD t hF.self_of_nhds
    set V := env "b" * Complex.sin (env "e" + env "f" * t) with hV
    have hfun : (fun w => eval Interp.complex (Function.update env "x" w)
        rubi4141r2Nondeg.result) =
        fun w => env "A" * Complex.cos (env "e" + env "f" * w) *
          (env "b" * Complex.sin (env "e" + env "f" * w)) ^ (k + 1) *
          (env "b" * env "f" * (env "m" + 1))⁻¹ := by
      funext w; simp [rubi4141r2Nondeg, eval, Interp.complex, e1, ivm1C]
    have hE : eval Interp.complex (Function.update env "x" t) rubi4141r2Nondeg.body =
        V ^ k * (env "A" + env "C" * Complex.sin (env "e" + env "f" * t) ^ 2) := by
      simp [rubi4141r2Nondeg, eval, Interp.complex, hkm, iv2C, hV]
    rw [hfun, hE]
    have hz : V ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    have hz0 : V ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    have hl := hasDerivAt_lin (env "e") (env "f") t
    have hS := ((Complex.hasDerivAt_sin _).comp t hl).const_mul (env "b")
    have hC := ((Complex.hasDerivAt_cos _).comp t hl).const_mul (env "A")
    refine ((hC.mul ((hasDerivAt_zpow (k + 1) V hz).comp t hS)).mul_const _).congr_deriv ?_
    simp only [Function.comp_apply, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hz0]
    have hk1 : ((k + 1 : ℤ) : ℂ) = env "m" + 1 := by rw [hm]; push_cast; ring
    rw [hk1, hV]
    have hSC := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    generalize (env "b" * Complex.sin (env "e" + env "f" * t)) ^ k = P
    generalize Complex.sin (env "e" + env "f" * t) = S at hSC ⊢
    generalize Complex.cos (env "e" + env "f" * t) = C at hSC ⊢
    field_simp
    linear_combination (env "A" * P * env "m" + env "A" * P) * hSC + (-P * S ^ 2) * hrel

end OSR.IntegrationRec212
