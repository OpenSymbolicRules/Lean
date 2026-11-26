import OSR.IntegrationRec215

/-! # Strengthened inverse hyperbolic tangent rules over `(d + e x^2)^2`

Proofs over ℝ of strengthened variants of `OSR.IntegrationNum1` reducing
`∫ (a + b artanh(c x))^p / (d + e x^2)^2 dx` when `c^2 d + e = 0`, with the derivative
`OSR.IntegrationRec215.hasDerivAt_artanh_mul`. The complex statement is vacuous (no complex
interpretation of `transc1#arctanh`) and stays unproved. Each 7.3.1 rule has a 7.3.4 twin with
the same statement, which reuses its proof. -/

namespace OSR.IntegrationRec219

open OSR OSR.Calculus OSR.IntegrationNum1 OSR.IntegrationRec215 Filter Topology

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
private theorem iv3R : intValue? (3 : ℝ) = some 3 := (intValue?_eq _ _).2 (by norm_num)

/-! ## RUBI 7.3.1 #43 (and 7.3.4 #23): `p > 0` -/

theorem rubi731r43Nondeg_real : rubi731r43Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r43Nondeg.conditions rubi731r43Nondeg.body
    rubi731r43Nondeg.result rubi731r43Nondeg.integrals
  intro env hc t hF
  have hW : 2 * env "b" * env "c" * env "d" ^ 2 * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b"))
      (.var "c")) (.pow (.var "d") (.int 2))) (.app2 .add (.var "p") (.int 1)))
      (.int 0)) (by simp [rubi731r43Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, iv2R] using h
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r43Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r43Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff, pow_ne_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    true_and] at hW'
  obtain ⟨⟨⟨hb, hcz⟩, hd⟩, hp1⟩ := hW'
  have he' : env "e" = -(env "c" ^ 2 * env "d") := by linear_combination hrel
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r43Nondeg, Defined, eval, Interp.real, hkp] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have hk0 : ¬ k < 0 := by omega
  have hk1' : ¬ k < 1 := by omega
  have hk1'' : ¬ k - 1 < 0 := by omega
  have hkp1 : ¬ k + 1 < 0 := by omega
  have e1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have ep : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have ep' : intValue? (env "p" - 1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have ep'' : intValue? (-1 + env "p") = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r43Nondeg.body →
      env "d" + env "e" * w ^ 2 ≠ 0 ∧ (-1 < env "c" * w ∧ env "c" * w < 1) := by
    intro w h
    simp [rubi731r43Nondeg, Defined, eval, Interp.real, hkp, ivm1R, iv2R, hk0] at h
    tauto
  obtain ⟨hD0, hc1, hc2⟩ := hBody t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r43Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hB := hBody w hw
    simp [Defined, eval, Interp.real, ep, ivm1R, iv2R, hk1'', hB.1, hB.2.1,
      hB.2.2]
  · filter_upwards [hF] with w hw
    have hB := hBody w hw
    simp [rubi731r43Nondeg, Defined, eval, recEnv, Interp.real, e1, hkp, ivm1R, iv2R, iv2R, hb,
      hcz, hd, hp1, hk0, hkp1, hB.1, hB.2.1, hB.2.2]
  · simp only [rubi731r43Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (t * (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) *
        ((env "d" + env "e" * t ^ 2) ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, ep, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r43Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r43Nondeg.result) =
        fun w => w * (env "a" + env "b" * Real.artanh (env "c" * w)) ^ k *
            (2 * env "d" * (env "d" + env "e" * w ^ 2))⁻¹ +
          (env "a" + env "b" * Real.artanh (env "c" * w)) ^ (k + 1) *
            (2 * env "b" * env "c" * env "d" ^ 2 * (env "p" + 1))⁻¹ +
          -env "b" * env "c" * env "p" * 2⁻¹ * Φ "I1" w := by
      funext w; simp [rubi731r43Nondeg, eval, recEnv, Interp.real, e1, hkp, ivm1R, iv2R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r43Nondeg.body =
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k *
          ((env "d" + env "e" * t ^ 2) ^ 2)⁻¹ := by
      simp [rubi731r43Nondeg, eval, Interp.real, hkp, ivm1R, iv2R]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_artanh_mul hc1 hc2).const_mul (env "b")).const_add (env "a")
    have hP1 := (hasDerivAt_zpow (k + 1) _ (Or.inr (by omega))).comp t hA
    have hP0 := (hasDerivAt_zpow k _ (Or.inr hk.le)).comp t hA
    have hden : 2 * env "d" * (env "d" + env "e" * t ^ 2) ≠ 0 := by
      simp [hd, hD0]
    have hQ := ((hasDerivAt_quad0 (env "d") (env "e") t).const_mul
      (2 * env "d")).inv (by simpa [mul_assoc] using hden)
    refine (((((hasDerivAt_id' t).mul hP0).mul hQ).add (hP1.mul_const _)).add
      (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply, Pi.mul_apply, Pi.inv_apply, add_sub_cancel_right]
    have hAk : (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k =
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) *
          (env "a" + env "b" * Real.artanh (env "c" * t)) := by
      have := zpow_succ_of (env "a" + env "b" * Real.artanh (env "c" * t)) (k - 1)
        (Or.inr (by omega))
      rwa [sub_add_cancel] at this
    rw [hAk]
    have hk1 : ((k + 1 : ℤ) : ℝ) = env "p" + 1 := by rw [hp]; push_cast; ring
    rw [hk1, ← hp]
    have hD := one_sub_sq_mul_ne hc1 hc2
    have hD' : 1 - t ^ 2 * env "c" ^ 2 ≠ 0 := by rwa [mul_comm] at hD
    have hD2 : 1 - t ^ 2 * env "c" ^ 2 * 2 + t ^ 4 * env "c" ^ 4 ≠ 0 := by
      have : 1 - t ^ 2 * env "c" ^ 2 * 2 + t ^ 4 * env "c" ^ 4 = (1 - t ^ 2 * env "c" ^ 2) ^ 2 := by
        ring
      rw [this]; exact pow_ne_zero 2 hD'
    have hdenD : env "d" + env "e" * t ^ 2 = env "d" * (1 - env "c" ^ 2 * t ^ 2) := by
      rw [he']; ring
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) = P
    generalize env "a" + env "b" * Real.artanh (env "c" * t) = T
    rw [hdenD, he']
    field_simp
    ring

theorem rubi734r23Nondeg_real : rubi734r23Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r23Nondeg.conditions rubi734r23Nondeg.body
    rubi734r23Nondeg.result rubi734r23Nondeg.integrals
  exact rubi731r43Nondeg_real

/-! ## RUBI 7.3.1 #44 (and 7.3.4 #24): the reciprocal argument `artanh (1/(c x))` -/

theorem rubi731r44Nondeg_real : rubi731r44Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r44Nondeg.conditions rubi731r44Nondeg.body
    rubi731r44Nondeg.result rubi731r44Nondeg.integrals
  intro env hc t hF
  have hW : 2 * env "b" * env "c" * env "d" ^ 2 * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b"))
      (.var "c")) (.pow (.var "d") (.int 2))) (.app2 .add (.var "p") (.int 1)))
      (.int 0)) (by simp [rubi731r44Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, iv2R] using h
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r44Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r44Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff, pow_ne_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    true_and] at hW'
  obtain ⟨⟨⟨hb, hcz⟩, hd⟩, hp1⟩ := hW'
  have he' : env "e" = -(env "c" ^ 2 * env "d") := by linear_combination hrel
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r44Nondeg, Defined, eval, Interp.real, hkp] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have hk0 : ¬ k < 0 := by omega
  have hk1' : ¬ k < 1 := by omega
  have hk1'' : ¬ k - 1 < 0 := by omega
  have hkp1 : ¬ k + 1 < 0 := by omega
  have e1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have ep : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have ep' : intValue? (env "p" - 1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have ep'' : intValue? (-1 + env "p") = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r44Nondeg.body →
      env "d" + env "e" * w ^ 2 ≠ 0 ∧ (¬ env "c" = 0 ∧ ¬ w = 0) ∧
        (-1 < w⁻¹ * (env "c")⁻¹ ∧ w⁻¹ * (env "c")⁻¹ < 1) := by
    intro w h
    simp [rubi731r44Nondeg, Defined, eval, Interp.real, hkp, ivm1R, iv2R, hk0] at h
    tauto
  obtain ⟨hD0, ⟨-, ht0⟩, hc1, hc2⟩ := hBody t hF.self_of_nhds
  have hct : env "c" * t ≠ 0 := mul_ne_zero hcz ht0
  have h1 : -1 < (env "c" * t)⁻¹ := by rw [mul_inv_rev]; exact hc1
  have h2 : (env "c" * t)⁻¹ < 1 := by rw [mul_inv_rev]; exact hc2
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r44Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hB := hBody w hw
    simp [Defined, eval, Interp.real, ep, ivm1R, iv2R, hk1'', hB.1, hB.2.1,
      hB.2.2]
  · filter_upwards [hF] with w hw
    have hB := hBody w hw
    simp [rubi731r44Nondeg, Defined, eval, recEnv, Interp.real, e1, hkp, ivm1R, iv2R, iv2R, hb,
      hcz, hd, hp1, hk0, hkp1, hB.1, hB.2.1.2, hB.2.2.1, hB.2.2.2]
  · simp only [rubi731r44Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (t * (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ (k - 1) *
        ((env "d" + env "e" * t ^ 2) ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, ep, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r44Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r44Nondeg.result) =
        fun w => w * (env "a" + env "b" * Real.artanh (env "c" * w)⁻¹) ^ k *
            (2 * env "d" * (env "d" + env "e" * w ^ 2))⁻¹ +
          (env "a" + env "b" * Real.artanh (env "c" * w)⁻¹) ^ (k + 1) *
            (2 * env "b" * env "c" * env "d" ^ 2 * (env "p" + 1))⁻¹ +
          -env "b" * env "c" * env "p" * 2⁻¹ * Φ "I1" w := by
      funext w; simp [rubi731r44Nondeg, eval, recEnv, Interp.real, e1, hkp, ivm1R, iv2R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r44Nondeg.body =
        (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ k *
          ((env "d" + env "e" * t ^ 2) ^ 2)⁻¹ := by
      simp [rubi731r44Nondeg, eval, Interp.real, hkp, ivm1R, iv2R]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_artanh_inv hct h1 h2).const_mul (env "b")).const_add (env "a")
    have hP1 := (hasDerivAt_zpow (k + 1) _ (Or.inr (by omega))).comp t hA
    have hP0 := (hasDerivAt_zpow k _ (Or.inr hk.le)).comp t hA
    have hden : 2 * env "d" * (env "d" + env "e" * t ^ 2) ≠ 0 := by
      simp [hd, hD0]
    have hQ := ((hasDerivAt_quad0 (env "d") (env "e") t).const_mul
      (2 * env "d")).inv (by simpa [mul_assoc] using hden)
    refine (((((hasDerivAt_id' t).mul hP0).mul hQ).add (hP1.mul_const _)).add
      (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply, Pi.mul_apply, Pi.inv_apply, add_sub_cancel_right]
    have hAk : (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ k =
        (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ (k - 1) *
          (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) := by
      have := zpow_succ_of (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) (k - 1)
        (Or.inr (by omega))
      rwa [sub_add_cancel] at this
    rw [hAk]
    have hk1 : ((k + 1 : ℤ) : ℝ) = env "p" + 1 := by rw [hp]; push_cast; ring
    rw [hk1, ← hp]
    have hD := one_sub_sq_inv_ne hct h1 h2
    have hD' : 1 - t ^ 2 * env "c" ^ 2 ≠ 0 := by rwa [mul_comm] at hD
    have hD2 : 1 - t ^ 2 * env "c" ^ 2 * 2 + t ^ 4 * env "c" ^ 4 ≠ 0 := by
      have : 1 - t ^ 2 * env "c" ^ 2 * 2 + t ^ 4 * env "c" ^ 4 = (1 - t ^ 2 * env "c" ^ 2) ^ 2 := by
        ring
      rw [this]; exact pow_ne_zero 2 hD'
    have hdenD : env "d" + env "e" * t ^ 2 = env "d" * (1 - env "c" ^ 2 * t ^ 2) := by
      rw [he']; ring
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ (k - 1) = P
    generalize env "a" + env "b" * Real.artanh (env "c" * t)⁻¹ = T
    rw [hdenD, he']
    field_simp
    ring

theorem rubi734r24Nondeg_real : rubi734r24Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r24Nondeg.conditions rubi734r24Nondeg.body
    rubi734r24Nondeg.result rubi734r24Nondeg.integrals
  exact rubi731r44Nondeg_real

end OSR.IntegrationRec219
