import OSR.IntegrationRec215

/-! # Strengthened inverse hyperbolic tangent rule: `x / (d + e x^2)^2`, `p < -1`

Proof over ℝ of RUBI 7.3.1 #82 (and its 7.3.4 #62 twin), raising the power of
`a + b artanh(1/(c x))` in `∫ x (a + b artanh(1/(c x)))^p / (d + e x^2)^2 dx` when
`c^2 d + e = 0`, `p < -1` and `p ≠ -2`. The conditions do not state `c, d, e ≠ 0`: they follow
from the domain (the reciprocal argument needs `c x ≠ 0`, and `d + e x^2 = d (1 - c^2 x^2) ≠ 0`
forces `d ≠ 0`). The complex statement is vacuous (no complex interpretation of
`transc1#arctanh`) and stays unproved. -/

namespace OSR.IntegrationRec226

open OSR OSR.Calculus OSR.IntegrationNum1 OSR.IntegrationRec215 Filter Topology

private theorem hasDerivAt_quad0 (a b t : ℝ) :
    HasDerivAt (fun w => a + b * w ^ 2) (2 * b * t) t := by
  have h := ((hasDerivAt_pow 2 t).const_mul b).const_add a
  refine h.congr_deriv ?_
  simp; ring

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

/-! ## RUBI 7.3.1 #82 (and 7.3.4 #62) -/

theorem rubi731r82Nondeg_real : rubi731r82Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r82Nondeg.conditions rubi731r82Nondeg.body
    rubi731r82Nondeg.result rubi731r82Nondeg.integrals
  intro env hc t hF
  have hW : env "b" ^ 2 * (env "p" + 1) * (env "p" + 2) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.var "p")
      (.int 1))) (.app2 .add (.var "p") (.int 2))) (.int 0)) (by simp [rubi731r82Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r82Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hpneg : env "p" < -1 := by
    have h := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi731r82Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff, pow_ne_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    at hW'
  obtain ⟨⟨hb, hp1⟩, hp2⟩ := hW'
  have he' : env "e" = -(env "c" ^ 2 * env "d") := by linear_combination hrel
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r82Nondeg, Defined, eval, Interp.real, hkp] at h
  have hp : env "p" = (l : ℝ) := (intValue?_eq _ _).1 hkp
  have hl : l < -1 := by rw [hp] at hpneg; exact_mod_cast hpneg
  have hl0 : l < 0 := by omega
  have ep1 : intValue? (env "p" + 1) = some (l + 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have ep2 : intValue? (env "p" + 2) = some (l + 2) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r82Nondeg.body →
      env "d" + env "e" * w ^ 2 ≠ 0 ∧
        env "a" + env "b" * Real.artanh (w⁻¹ * (env "c")⁻¹) ≠ 0 ∧
        (¬ env "c" = 0 ∧ ¬ w = 0) ∧ (-1 < w⁻¹ * (env "c")⁻¹ ∧ w⁻¹ * (env "c")⁻¹ < 1) := by
    intro w h
    simp [rubi731r82Nondeg, Defined, eval, Interp.real, hkp, ivm1R, iv2R, hl0] at h
    tauto
  obtain ⟨hD0, hA0, ⟨hcz, ht0⟩, hc1, hc2⟩ := hBody t hF.self_of_nhds
  have hd : env "d" ≠ 0 := by
    intro h; apply hD0; rw [he', h]; ring
  have he : env "e" ≠ 0 := by rw [he']; simp [hcz, hd]
  have hct : env "c" * t ≠ 0 := mul_ne_zero hcz ht0
  have h1 : -1 < (env "c" * t)⁻¹ := by rw [mul_inv_rev]; exact hc1
  have h2 : (env "c" * t)⁻¹ < 1 := by rw [mul_inv_rev]; exact hc2
  have hA0' : env "a" + env "b" * Real.artanh (env "c" * t)⁻¹ ≠ 0 := by rw [mul_inv_rev]; exact hA0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r82Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hB := hBody w hw
    simp [Defined, eval, Interp.real, ep2, ivm1R, iv2R, hB.1, hB.2.1, hB.2.2.1.1, hB.2.2.1.2,
      hB.2.2.2.1, hB.2.2.2.2]
  · filter_upwards [hF] with w hw
    have hB := hBody w hw
    simp [rubi731r82Nondeg, Defined, eval, recEnv, Interp.real, ep1, ep2, ivm1R, iv2R, hb, hcz,
      hd, he, hp1, hp2, hB.1, hB.2.1, hB.2.2.1.2, hB.2.2.2.1, hB.2.2.2.2]
  · simp only [rubi731r82Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (t *
        (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ (l + 2) *
        ((env "d" + env "e" * t ^ 2) ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, ep2, ivm1R, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r82Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r82Nondeg.result) =
        fun w => w * (env "a" + env "b" * Real.artanh (env "c" * w)⁻¹) ^ (l + 1) *
            (env "b" * env "c" * env "d" * (env "p" + 1) * (env "d" + env "e" * w ^ 2))⁻¹ +
          (1 + env "c" ^ 2 * w ^ 2) * (env "a" + env "b" * Real.artanh (env "c" * w)⁻¹) ^ (l + 2) *
            (env "b" ^ 2 * env "e" * (env "p" + 1) * (env "p" + 2) *
              (env "d" + env "e" * w ^ 2))⁻¹ +
          4 * (env "b" ^ 2 * (env "p" + 1) * (env "p" + 2))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi731r82Nondeg, eval, recEnv, Interp.real, ep1, ep2, ivm1R, iv2R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r82Nondeg.body =
        t * (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ l *
          ((env "d" + env "e" * t ^ 2) ^ 2)⁻¹ := by
      simp [rubi731r82Nondeg, eval, Interp.real, hkp, ivm1R, iv2R]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_artanh_inv hct h1 h2).const_mul (env "b")).const_add (env "a")
    have hP1 := (hasDerivAt_zpow (l + 1) _ (Or.inl hA0')).comp t hA
    have hP2 := (hasDerivAt_zpow (l + 2) _ (Or.inl hA0')).comp t hA
    have hk1 : env "b" * env "c" * env "d" * (env "p" + 1) * (env "d" + env "e" * t ^ 2) ≠ 0 := by
      simp [hb, hcz, hd, hp1, hD0]
    have hk2 : env "b" ^ 2 * env "e" * (env "p" + 1) * (env "p" + 2) *
        (env "d" + env "e" * t ^ 2) ≠ 0 := by
      simp [hb, he, hp1, hp2, hD0]
    have hI1 := ((hasDerivAt_quad0 (env "d") (env "e") t).const_mul
      (env "b" * env "c" * env "d" * (env "p" + 1))).inv (by simpa [mul_assoc] using hk1)
    have hI2 := ((hasDerivAt_quad0 (env "d") (env "e") t).const_mul
      (env "b" ^ 2 * env "e" * (env "p" + 1) * (env "p" + 2))).inv (by simpa [mul_assoc] using hk2)
    refine (((((hasDerivAt_id' t).mul hP1).mul hI1).add
      (((hasDerivAt_quad0 1 (env "c" ^ 2) t).mul hP2).mul hI2)).add
      (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply, Pi.mul_apply, Pi.inv_apply, add_sub_cancel_right]
    have a1 : (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ (l + 1) =
        (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ l *
          (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) := zpow_add_one₀ hA0' l
    have a2 : (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ (l + 2) =
        (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ l *
          (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ 2 := by
      rw [zpow_add₀ hA0']; norm_cast
    have a3 : (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ (l + 2 - 1) =
        (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ l *
          (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) := by
      rw [show l + 2 - 1 = l + 1 by ring, a1]
    rw [a3, a2, a1]
    have hl1r : ((l + 1 : ℤ) : ℝ) = env "p" + 1 := by rw [hp]; push_cast; ring
    have hl2r : ((l + 2 : ℤ) : ℝ) = env "p" + 2 := by rw [hp]; push_cast; ring
    rw [hl1r, hl2r]
    have hD := one_sub_sq_inv_ne hct h1 h2
    have hD' : 1 - t ^ 2 * env "c" ^ 2 ≠ 0 := by rwa [mul_comm] at hD
    have hdenD : env "d" + env "e" * t ^ 2 = env "d" * (1 - env "c" ^ 2 * t ^ 2) := by
      rw [he']; ring
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ l = R
    generalize env "a" + env "b" * Real.artanh (env "c" * t)⁻¹ = T
    rw [hdenD, he']
    field_simp
    ring

theorem rubi734r62Nondeg_real : rubi734r62Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r62Nondeg.conditions rubi734r62Nondeg.body
    rubi734r62Nondeg.result rubi734r62Nondeg.integrals
  exact rubi731r82Nondeg_real

end OSR.IntegrationRec226
