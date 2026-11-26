import OSR.IntegrationRec215

/-! # Strengthened inverse hyperbolic tangent rule: `m + 2 q + 3 = 0`, reciprocal argument

Proof over ℝ of RUBI 7.3.1 #94 (and its 7.3.4 #74 twin), integrating
`(f x)^m (d + e x^2)^q (a + b artanh(1/(c x)))^p` by parts when `c^2 d + e = 0` and
`m + 2 q + 3 = 0`, with the derivative `OSR.IntegrationRec215.hasDerivAt_artanh_inv`. The
exponents `m` and `q` may be negative. The complex statement is vacuous (no complex
interpretation of `transc1#arctanh`) and stays unproved. -/

namespace OSR.IntegrationRec222

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

/-! ## RUBI 7.3.1 #94 (and 7.3.4 #74) -/

theorem rubi731r94Nondeg_real : rubi731r94Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r94Nondeg.conditions rubi731r94Nondeg.body
    rubi731r94Nondeg.result rubi731r94Nondeg.integrals
  intro env hc t hF
  have hW : env "d" * env "f" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m")
      (.int 1))) (.int 0)) (by simp [rubi731r94Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r94Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hmq : env "m" + 2 * env "q" + 3 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 3))
      (.int 0)) (by simp [rubi731r94Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r94Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨hd, hf⟩, hm1⟩ := hW'
  have he' : env "e" = -(env "c" ^ 2 * env "d") := by linear_combination hrel
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r94Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r94Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r94Nondeg, Defined, eval, Interp.real, hkm, hkq, hkp] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hq : env "q" = (k : ℝ) := (intValue?_eq _ _).1 hkq
  have hp : env "p" = (l : ℝ) := (intValue?_eq _ _).1 hkp
  have hl : 0 < l := by rw [hp] at hpos; exact_mod_cast hpos
  have hl0 : ¬ l < 0 := by omega
  have hl1 : ¬ l - 1 < 0 := by omega
  have hl1' : ¬ l < 1 := by omega
  have em1 : intValue? (env "m" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have eq1 : intValue? (env "q" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have ep : intValue? (env "p" + -1) = some (l - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have ep' : intValue? (env "p" - 1) = some (l - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r94Nondeg.body →
      (k < 0 → env "d" + env "e" * w ^ 2 ≠ 0) ∧ (¬ env "c" = 0 ∧ ¬ w = 0) ∧
        (-1 < w⁻¹ * (env "c")⁻¹ ∧ w⁻¹ * (env "c")⁻¹ < 1) := by
    intro w h
    simp [rubi731r94Nondeg, Defined, eval, Interp.real, hkm, hkq, hkp, ivm1R, iv2R, hl0] at h
    tauto
  obtain ⟨hk0, ⟨hcz, ht0⟩, hc1, hc2⟩ := hBody t hF.self_of_nhds
  have hct : env "c" * t ≠ 0 := mul_ne_zero hcz ht0
  have hft : env "f" * t ≠ 0 := mul_ne_zero hf ht0
  have h1 : -1 < (env "c" * t)⁻¹ := by rw [mul_inv_rev]; exact hc1
  have h2 : (env "c" * t)⁻¹ < 1 := by rw [mul_inv_rev]; exact hc2
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r94Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hB := hBody w hw
    simp [Defined, eval, Interp.real, em1, hkq, ep, ivm1R, iv2R, hl1, hf, hB.2.1.1,
      hB.2.1.2, hB.2.2.1, hB.2.2.2]
    exact hB.1
  · filter_upwards [hF] with w hw
    have hB := hBody w hw
    simp [rubi731r94Nondeg, Defined, eval, recEnv, Interp.real, em1, eq1, hkp, ivm1R, iv2R, hd,
      hf, hm1, hl0, hB.2.1.1, hB.2.1.2, hB.2.2.1, hB.2.2.2]
    intro h
    exact hB.1 (by omega)
  · simp only [rubi731r94Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "f" * t) ^ (j + 1) * (env "d" + env "e" * t ^ 2) ^ k *
        (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ (l - 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, hkq, ep, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r94Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r94Nondeg.result) =
        fun w => (env "f" * w) ^ (j + 1) * (env "d" + env "e" * w ^ 2) ^ (k + 1) *
            (env "a" + env "b" * Real.artanh (env "c" * w)⁻¹) ^ l *
            (env "d" * env "f" * (env "m" + 1))⁻¹ +
          -env "b" * env "c" * env "p" * (env "f" * (env "m" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi731r94Nondeg, eval, recEnv, Interp.real, em1, eq1, hkp, ivm1R, iv2R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r94Nondeg.body =
        (env "f" * t) ^ j * (env "d" + env "e" * t ^ 2) ^ k *
          (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ l := by
      simp [rubi731r94Nondeg, eval, Interp.real, hkm, hkq, hkp, ivm1R, iv2R]
    rw [hfun, hEF]
    have hz : env "d" + env "e" * t ^ 2 ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (hk0 h)
      · exact Or.inr (by omega)
    have hz0 : env "d" + env "e" * t ^ 2 ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (hk0 h)
      · exact Or.inr (by omega)
    have hA := ((hasDerivAt_artanh_inv hct h1 h2).const_mul (env "b")).const_add (env "a")
    have hFj := (hasDerivAt_zpow (j + 1) _ (Or.inl hft)).comp t
      ((hasDerivAt_id' t).const_mul (env "f"))
    have hQ := (hasDerivAt_zpow (k + 1) _ hz).comp t (hasDerivAt_quad0 (env "d") (env "e") t)
    have hP := (hasDerivAt_zpow l _ (Or.inr hl.le)).comp t hA
    refine ((((hFj.mul hQ).mul hP).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply, Pi.mul_apply, add_sub_cancel_right]
    rw [zpow_add_one₀ hft, zpow_succ_of _ _ hz0]
    have hAl : (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ l =
        (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ (l - 1) *
          (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) := by
      have := zpow_succ_of (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) (l - 1)
        (Or.inr (by omega))
      rwa [sub_add_cancel] at this
    rw [hAl]
    have hj1r : ((j + 1 : ℤ) : ℝ) = env "m" + 1 := by rw [hm]; push_cast; ring
    have hk1r : ((k + 1 : ℤ) : ℝ) = env "q" + 1 := by rw [hq]; push_cast; ring
    have hlr : ((l : ℤ) : ℝ) = env "p" := hp.symm
    rw [hj1r, hk1r, hlr]
    have hD := one_sub_sq_inv_ne hct h1 h2
    have hD' : 1 - t ^ 2 * env "c" ^ 2 ≠ 0 := by rwa [mul_comm] at hD
    have hdenD : env "d" + env "e" * t ^ 2 = env "d" * (1 - env "c" ^ 2 * t ^ 2) := by
      rw [he']; ring
    have hmv : env "m" = -2 * env "q" - 3 := by linear_combination hmq
    generalize (env "f" * t) ^ j = P
    generalize (env "d" + env "e" * t ^ 2) ^ k = Q
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ (l - 1) = R
    generalize env "a" + env "b" * Real.artanh (env "c" * t)⁻¹ = T
    rw [hdenD, he']
    field_simp
    rw [hmv]
    ring

theorem rubi734r74Nondeg_real : rubi734r74Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r74Nondeg.conditions rubi734r74Nondeg.body
    rubi734r74Nondeg.result rubi734r74Nondeg.integrals
  exact rubi731r94Nondeg_real

end OSR.IntegrationRec222
