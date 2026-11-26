import OSR.IntegrationRec215

/-! # Strengthened inverse hyperbolic tangent rule: `x^m (d + e x^2)^q`, `p < -1`

Proof over ℝ of RUBI 7.3.1 #118 (and its 7.3.4 #98 twin), raising the power of
`a + b artanh(1/(c x))` when `c^2 d + e = 0`, `q < -1` and `p < -1`, with two residual
integrals. Every base is nonzero where the integrand is defined (`x ≠ 0` from the reciprocal
argument, `d + e x^2 ≠ 0` and `a + b artanh(1/(c x)) ≠ 0` from the negative exponents), so the
integer exponents `m`, `q + 1` and `p + 1` may have any sign. The complex statement is vacuous
(no complex interpretation of `transc1#arctanh`) and stays unproved. -/

namespace OSR.IntegrationRec225

open OSR OSR.Calculus OSR.IntegrationNum1 OSR.IntegrationRec215 Filter Topology

private theorem hasDerivAt_quad0 (a b t : ℝ) :
    HasDerivAt (fun w => a + b * w ^ 2) (2 * b * t) t := by
  have h := ((hasDerivAt_pow 2 t).const_mul b).const_add a
  refine h.congr_deriv ?_
  simp; ring

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

/-! ## RUBI 7.3.1 #118 (and 7.3.4 #98) -/

theorem rubi731r118Nondeg_real : rubi731r118Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r118Nondeg.conditions rubi731r118Nondeg.body
    rubi731r118Nondeg.result rubi731r118Nondeg.integrals
  intro env hc t hF
  have hW : env "b" * env "c" * env "d" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d"))
      (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi731r118Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r118Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hqneg : env "q" < -1 := by
    have h := hc (.gt (.int (-1)) (.var "q")) (by simp [rubi731r118Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hpneg : env "p" < -1 := by
    have h := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi731r118Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨⟨hb, hcz⟩, hd⟩, hp1⟩ := hW'
  have he' : env "e" = -(env "c" ^ 2 * env "d") := by linear_combination hrel
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r118Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r118Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r118Nondeg, Defined, eval, Interp.real, hkm, hkq, hkp] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hq : env "q" = (k : ℝ) := (intValue?_eq _ _).1 hkq
  have hp : env "p" = (l : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : k < -1 := by rw [hq] at hqneg; exact_mod_cast hqneg
  have hl : l < -1 := by rw [hp] at hpneg; exact_mod_cast hpneg
  have hk0 : k < 0 := by omega
  have hl0 : l < 0 := by omega
  have em1 : intValue? (env "m" + -1) = some (j - 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have ep1 : intValue? (env "m" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have eq1 : intValue? (env "q" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have epp : intValue? (env "p" + 1) = some (l + 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r118Nondeg.body →
      env "d" + env "e" * w ^ 2 ≠ 0 ∧
        env "a" + env "b" * Real.artanh (w⁻¹ * (env "c")⁻¹) ≠ 0 ∧
        (¬ env "c" = 0 ∧ ¬ w = 0) ∧ (-1 < w⁻¹ * (env "c")⁻¹ ∧ w⁻¹ * (env "c")⁻¹ < 1) := by
    intro w h
    simp [rubi731r118Nondeg, Defined, eval, Interp.real, hkm, hkq, hkp, ivm1R, iv2R, hk0, hl0]
      at h
    tauto
  obtain ⟨hD0, hA0, ⟨-, ht0⟩, hc1, hc2⟩ := hBody t hF.self_of_nhds
  have hct : env "c" * t ≠ 0 := mul_ne_zero hcz ht0
  have h1 : -1 < (env "c" * t)⁻¹ := by rw [mul_inv_rev]; exact hc1
  have h2 : (env "c" * t)⁻¹ < 1 := by rw [mul_inv_rev]; exact hc2
  have hA0' : env "a" + env "b" * Real.artanh (env "c" * t)⁻¹ ≠ 0 := by rw [mul_inv_rev]; exact hA0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r118Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have hB := hBody w hw
      simp [Defined, eval, Interp.real, em1, hkq, epp, ivm1R, iv2R, hB.1, hB.2.1, hB.2.2.1.1,
        hB.2.2.1.2, hB.2.2.2.1, hB.2.2.2.2]
    · filter_upwards [hF] with w hw
      have hB := hBody w hw
      simp [Defined, eval, Interp.real, ep1, hkq, epp, ivm1R, iv2R, hB.1, hB.2.1, hB.2.2.1.1,
        hB.2.2.1.2, hB.2.2.2.1, hB.2.2.2.2]
  · filter_upwards [hF] with w hw
    have hB := hBody w hw
    simp [rubi731r118Nondeg, Defined, eval, recEnv, Interp.real, hkm, eq1, epp, ivm1R, iv2R, hb,
      hcz, hd, hp1, hB.1, hB.2.1, hB.2.2.1.2, hB.2.2.2.1, hB.2.2.2.2]
  · simp only [rubi731r118Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") (t ^ (j - 1) * (env "d" + env "e" * t ^ 2) ^ k *
        (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ (l + 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, em1, hkq, epp, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") (t ^ (j + 1) * (env "d" + env "e" * t ^ 2) ^ k *
        (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ (l + 1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, ep1, hkq, epp, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r118Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r118Nondeg.result) =
        fun w => w ^ j * (env "d" + env "e" * w ^ 2) ^ (k + 1) *
            (env "a" + env "b" * Real.artanh (env "c" * w)⁻¹) ^ (l + 1) *
            (env "b" * env "c" * env "d" * (env "p" + 1))⁻¹ +
          -env "m" * (env "b" * env "c" * (env "p" + 1))⁻¹ * Φ "I1" w +
          env "c" * (env "m" + 2 * env "q" + 2) * (env "b" * (env "p" + 1))⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi731r118Nondeg, eval, recEnv, Interp.real, hkm, eq1, epp, ivm1R, iv2R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r118Nondeg.body =
        t ^ j * (env "d" + env "e" * t ^ 2) ^ k *
          (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ l := by
      simp [rubi731r118Nondeg, eval, Interp.real, hkm, hkq, hkp, ivm1R, iv2R]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_artanh_inv hct h1 h2).const_mul (env "b")).const_add (env "a")
    have hX := hasDerivAt_zpow j t (Or.inl ht0)
    have hQ := (hasDerivAt_zpow (k + 1) _ (Or.inl hD0)).comp t
      (hasDerivAt_quad0 (env "d") (env "e") t)
    have hP := (hasDerivAt_zpow (l + 1) _ (Or.inl hA0')).comp t hA
    refine ((((hX.mul hQ).mul hP).mul_const _).add (hΦ1'.const_mul _) |>.add
      (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply, Pi.mul_apply, add_sub_cancel_right]
    have x1 : t ^ j = t ^ (j - 1) * t := by
      rw [← zpow_add_one₀ ht0, sub_add_cancel]
    have x2 : t ^ (j + 1) = t ^ (j - 1) * t ^ 2 := by
      rw [show j + 1 = (j - 1) + 2 by ring, zpow_add₀ ht0]; norm_cast
    rw [x2, x1, zpow_add_one₀ hD0, zpow_add_one₀ hA0']
    have hjr : ((j : ℤ) : ℝ) = env "m" := hm.symm
    have hk1r : ((k + 1 : ℤ) : ℝ) = env "q" + 1 := by rw [hq]; push_cast; ring
    have hl1r : ((l + 1 : ℤ) : ℝ) = env "p" + 1 := by rw [hp]; push_cast; ring
    rw [hjr, hk1r, hl1r]
    have hD := one_sub_sq_inv_ne hct h1 h2
    have hD' : 1 - t ^ 2 * env "c" ^ 2 ≠ 0 := by rwa [mul_comm] at hD
    have hdenD : env "d" + env "e" * t ^ 2 = env "d" * (1 - env "c" ^ 2 * t ^ 2) := by
      rw [he']; ring
    generalize t ^ (j - 1) = P
    generalize (env "d" + env "e" * t ^ 2) ^ k = Q
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ l = R
    generalize env "a" + env "b" * Real.artanh (env "c" * t)⁻¹ = T
    rw [hdenD, he']
    field_simp
    ring

theorem rubi734r98Nondeg_real : rubi734r98Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r98Nondeg.conditions rubi734r98Nondeg.body
    rubi734r98Nondeg.result rubi734r98Nondeg.integrals
  exact rubi731r118Nondeg_real

end OSR.IntegrationRec225
