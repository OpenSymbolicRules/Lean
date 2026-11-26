import OSR.IntegrationNum1
import OSR.IntegrationRec131

/-! # Strengthened inverse hyperbolic tangent rule: `x^2 (d + e x^2)^q`, `q < -1`

Proof over ℝ of RUBI 7.3.1 #83 (and its 7.3.4 #63 twin), reducing
`∫ x^2 (d + e x^2)^q (a + b artanh(c x)) dx` when `c^2 d + e = 0`. The complex statement is
vacuous (no complex interpretation of `transc1#arctanh`) and stays unproved. -/

namespace OSR.IntegrationRec220

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

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

private theorem one_sub_sq_ne {u : ℝ} (h1 : -1 < u) (h2 : u < 1) : 1 - u ^ 2 ≠ 0 :=
  (sub_pos.mpr (by nlinarith)).ne'

/-! ## RUBI 7.3.1 #83 (and 7.3.4 #63): `q < -1` -/

theorem rubi731r83Nondeg_real : rubi731r83Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r83Nondeg.conditions rubi731r83Nondeg.body
    rubi731r83Nondeg.result rubi731r83Nondeg.integrals
  intro env hc t hF
  have hW : 4 * env "c" ^ 3 * env "d" * (env "q" + 1) ^ 2 ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.pow (.var "c") (.int 3))) (.var "d"))
      (.pow (.app2 .add (.var "q") (.int 1)) (.int 2))) (.int 0)) (by simp [rubi731r83Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, iv3R] using h
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r83Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hneg : env "q" < -1 := by
    have h := hc (.gt (.int (-1)) (.var "q")) (by simp [rubi731r83Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff, pow_ne_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at hW'
  obtain ⟨⟨⟨-, hcz⟩, hd⟩, hq1⟩ := hW'
  rcases hkq : intValue? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r83Nondeg, Defined, eval, Interp.real, hkq] at h
  have hq : env "q" = (k : ℝ) := (intValue?_eq _ _).1 hkq
  have hk : k < -1 := by rw [hq] at hneg; exact_mod_cast hneg
  have e1 : intValue? (env "q" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r83Nondeg.body →
      env "d" + env "e" * w ^ 2 ≠ 0 ∧ (-1 < env "c" * w ∧ env "c" * w < 1) := by
    intro w h
    simp [rubi731r83Nondeg, Defined, eval, Interp.real, hkq, iv2R] at h
    have hk0 : k < 0 := by omega
    tauto
  obtain ⟨hD0, hc1, hc2⟩ := hBody t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r83Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [Defined, eval, Interp.real, e1, iv2R, hb.1, hb.2.1, hb.2.2]
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [rubi731r83Nondeg, Defined, eval, recEnv, Interp.real, e1, ivm1R, iv2R, iv3R, hcz, hd, hq1,
      hb.1, hb.2.1, hb.2.2]
  · simp only [rubi731r83Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t ^ 2) ^ (k + 1) *
        (env "a" + env "b" * Real.artanh (env "c" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, e1, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r83Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r83Nondeg.result) =
        fun w => -env "b" * (env "d" + env "e" * w ^ 2) ^ (k + 1) *
            (4 * env "c" ^ 3 * env "d" * (env "q" + 1) ^ 2)⁻¹ +
          -w * (env "d" + env "e" * w ^ 2) ^ (k + 1) *
            (env "a" + env "b" * Real.artanh (env "c" * w)) *
            (2 * env "c" ^ 2 * env "d" * (env "q" + 1))⁻¹ +
          (2 * env "c" ^ 2 * env "d" * (env "q" + 1))⁻¹ * Φ "I1" w := by
      funext w; simp [rubi731r83Nondeg, eval, recEnv, Interp.real, e1, ivm1R, iv2R, iv3R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r83Nondeg.body =
        t ^ 2 * (env "d" + env "e" * t ^ 2) ^ k *
          (env "a" + env "b" * Real.artanh (env "c" * t)) := by
      simp [rubi731r83Nondeg, eval, Interp.real, hkq, iv2R]
    rw [hfun, hEF]
    have hP := (hasDerivAt_zpow (k + 1) _ (Or.inl hD0)).comp t
      (hasDerivAt_quad0 (env "d") (env "e") t)
    have hA := (((OSR.IntegrationRec131.hasDerivAt_artanh hc1 hc2).comp t
      ((hasDerivAt_id' t).const_mul (env "c"))).const_mul (env "b")).const_add (env "a")
    refine ((((hP.const_mul (-env "b")).mul_const _).add (((((hasDerivAt_id' t).neg).mul hP).mul
      hA).mul_const _)).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply, Pi.mul_apply, Pi.neg_apply, add_sub_cancel_right]
    rw [zpow_succ_of _ _ (Or.inl hD0)]
    have hk1 : ((k + 1 : ℤ) : ℝ) = env "q" + 1 := by rw [hq]; push_cast; ring
    rw [hk1]
    have he : env "e" = -(env "c" ^ 2 * env "d") := by linear_combination hrel
    have hD := one_sub_sq_ne hc1 hc2
    have hD' : 1 - env "c" ^ 2 * t ^ 2 ≠ 0 := by rwa [mul_pow] at hD
    generalize (env "d" + env "e" * t ^ 2) ^ k = P
    generalize Real.artanh (env "c" * t) = T
    rw [he]
    field_simp
    ring

theorem rubi734r63Nondeg_real : rubi734r63Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r63Nondeg.conditions rubi734r63Nondeg.body
    rubi734r63Nondeg.result rubi734r63Nondeg.integrals
  exact rubi731r83Nondeg_real

end OSR.IntegrationRec220
