import OSR.IntegrationRec215

/-! # Strengthened inverse hyperbolic tangent rule over `sqrt(d + e x^2)`

Proof over ℝ of RUBI 7.3.1 #101 (and its 7.3.4 #81 twin), reducing
`∫ (f x)^m (a + b artanh(c x))^p / sqrt(d + e x^2) dx` when `c^2 d + e = 0`, `m > 1` and
`p > 0`, with two residual integrals. The square root is the real principal root
(`arith1#root` with index 2); its derivative is `Real.hasDerivAt_sqrt`, and
`sqrt(d + e x^2)^2 = d (1 - c^2 x^2)`. The complex statement is vacuous (no complex
interpretation of `transc1#arctanh` or `arith1#root`) and stays unproved. -/

namespace OSR.IntegrationRec223

open OSR OSR.Calculus OSR.IntegrationNum1 OSR.IntegrationRec215 Filter Topology

private theorem hasDerivAt_quad0 (a b t : ℝ) :
    HasDerivAt (fun w => a + b * w ^ 2) (2 * b * t) t := by
  have h := ((hasDerivAt_pow 2 t).const_mul b).const_add a
  refine h.congr_deriv ?_
  simp; ring

private theorem zpow_add_nat_of (A : ℝ) (j : ℤ) (n : ℕ) (h : 0 ≤ j) :
    A ^ (j + n) = A ^ j * A ^ n := by
  lift j to ℕ using h
  rw [show ((j : ℤ) + n) = ((j + n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
    pow_add]

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

/-! ## RUBI 7.3.1 #101 (and 7.3.4 #81) -/

theorem rubi731r101Nondeg_real : rubi731r101Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r101Nondeg.conditions rubi731r101Nondeg.body
    rubi731r101Nondeg.result rubi731r101Nondeg.integrals
  intro env hc t hF
  have hW : env "c" ^ 2 * env "d" * env "m" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "m"))
      (.int 0)) (by simp [rubi731r101Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r101Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r101Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hmgt : 1 < env "m" := by
    have h := hc (.gt (.var "m") (.int 1)) (by simp [rubi731r101Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff, pow_ne_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    at hW'
  obtain ⟨⟨hcz, hd⟩, hm0⟩ := hW'
  have he' : env "e" = -(env "c" ^ 2 * env "d") := by linear_combination hrel
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r101Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r101Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hj : 2 ≤ j := by
    have : (1 : ℝ) < j := hm ▸ hmgt
    exact_mod_cast (show (1 : ℤ) < j by exact_mod_cast this)
  have hk : 0 < k := by
    have : (0 : ℝ) < k := hp ▸ hpos
    exact_mod_cast this
  have hj0 : ¬ j < 0 := by omega
  have hj1 : ¬ j - 1 < 0 := by omega
  have hj1' : ¬ j < 1 := by omega
  have hj2 : ¬ j - 2 < 0 := by omega
  have hj2' : ¬ j < 2 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hk1' : ¬ k < 1 := by omega
  have em1 : intValue? (env "m" + -1) = some (j - 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have em2 : intValue? (env "m" + -2) = some (j - 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have ep1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r101Nondeg.body →
      0 < env "d" + env "e" * w ^ 2 ∧ (-1 < env "c" * w ∧ env "c" * w < 1) := by
    intro w h
    simp [rubi731r101Nondeg, Defined, eval, Interp.real, hkm, hkp, ivm1R, iv2R, hj0, hk0] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨?_, h1, h2⟩
    have hs : Real.sqrt (env "d" + env "e" * w ^ 2) ≠ 0 := by tauto
    exact Real.sqrt_pos.mp (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs))
  obtain ⟨hD0, hc1, hc2⟩ := hBody t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r101Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have hB := hBody w hw
      simp [Defined, eval, Interp.real, em1, ep1, ivm1R, iv2R, hj1, hk1, hB.1.le,
        hB.1.ne', hB.2.1, hB.2.2]
    · filter_upwards [hF] with w hw
      have hB := hBody w hw
      simp [Defined, eval, Interp.real, em2, hkp, ivm1R, iv2R, hj2, hk0, hB.1.le,
        hB.1.ne', hB.2.1, hB.2.2]
  · filter_upwards [hF] with w hw
    have hB := hBody w hw
    simp [rubi731r101Nondeg, Defined, eval, recEnv, Interp.real, em1, hkp, ivm1R, iv2R, hcz, hd,
      hm0, hj1, hk0, hB.1.le, hB.2.1, hB.2.2]
  · simp only [rubi731r101Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ (j - 1) *
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) *
        (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, em1, ep1, ivm1R, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (j - 2) *
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k *
        (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, em2, hkp, ivm1R, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r101Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r101Nondeg.result) =
        fun w => -env "f" * (env "f" * w) ^ (j - 1) * Real.sqrt (env "d" + env "e" * w ^ 2) *
            (env "a" + env "b" * Real.artanh (env "c" * w)) ^ k *
            (env "c" ^ 2 * env "d" * env "m")⁻¹ +
          env "b" * env "f" * env "p" * (env "c" * env "m")⁻¹ * Φ "I1" w +
          env "f" ^ 2 * (env "m" - 1) * (env "c" ^ 2 * env "m")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi731r101Nondeg, eval, recEnv, Interp.real, em1, hkp, ivm1R, iv2R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r101Nondeg.body =
        (env "f" * t) ^ j * (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k *
          (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹ := by
      simp [rubi731r101Nondeg, eval, Interp.real, hkm, hkp, ivm1R, iv2R]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_artanh_mul hc1 hc2).const_mul (env "b")).const_add (env "a")
    have hF1 := (hasDerivAt_zpow (j - 1) _ (Or.inr (by omega))).comp t
      ((hasDerivAt_id' t).const_mul (env "f"))
    have hS := (Real.hasDerivAt_sqrt hD0.ne').comp t (hasDerivAt_quad0 (env "d") (env "e") t)
    have hP := (hasDerivAt_zpow k _ (Or.inr hk.le)).comp t hA
    refine (((((hF1.const_mul (-env "f")).mul hS).mul hP).mul_const _).add
      (hΦ1'.const_mul _) |>.add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply, Pi.mul_apply]
    have h2 : (env "f" * t) ^ j = (env "f" * t) ^ (j - 2) * (env "f" * t) ^ 2 := by
      have := zpow_add_nat_of (env "f" * t) (j - 2) 2 (by omega)
      rwa [show j - 2 + ((2 : ℕ) : ℤ) = j by push_cast; ring] at this
    have h1 : (env "f" * t) ^ (j - 1) = (env "f" * t) ^ (j - 2) * (env "f" * t) := by
      have := zpow_add_nat_of (env "f" * t) (j - 2) 1 (by omega)
      rwa [show j - 2 + ((1 : ℕ) : ℤ) = j - 1 by push_cast; ring, pow_one] at this
    have h0 : (env "f" * t) ^ (j - 1 - 1) = (env "f" * t) ^ (j - 2) := by
      rw [show j - 1 - 1 = j - 2 by ring]
    have hAk : (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k =
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) *
          (env "a" + env "b" * Real.artanh (env "c" * t)) := by
      have := zpow_add_nat_of (env "a" + env "b" * Real.artanh (env "c" * t)) (k - 1) 1
        (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [h0, h2, h1, hAk]
    have hjr : ((j - 1 : ℤ) : ℝ) = env "m" - 1 := by rw [hm]; push_cast; ring
    have hkr : ((k : ℤ) : ℝ) = env "p" := hp.symm
    rw [hjr, hkr]
    have hD := one_sub_sq_mul_ne hc1 hc2
    have hD' : 1 - t ^ 2 * env "c" ^ 2 ≠ 0 := by rwa [mul_comm] at hD
    have hS2 : Real.sqrt (env "d" + env "e" * t ^ 2) ^ 2 = env "d" + env "e" * t ^ 2 :=
      Real.sq_sqrt hD0.le
    have hS0 : Real.sqrt (env "d" + env "e" * t ^ 2) ≠ 0 :=
      (Real.sqrt_pos.mpr hD0).ne'
    generalize (env "f" * t) ^ (j - 2) = P at *
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) = R at *
    generalize env "a" + env "b" * Real.artanh (env "c" * t) = T at *
    generalize Real.sqrt (env "d" + env "e" * t ^ 2) = S at *
    rw [he'] at hS2 ⊢
    field_simp
    linear_combination (-P * R * env "f" ^ 2 * (-T * env "c" ^ 2 * env "m" * t ^ 2 +
      T * env "c" ^ 2 * t ^ 2 + T * env "m" - T + env "b" * env "c" * env "p" * t)) * hS2

theorem rubi734r81Nondeg_real : rubi734r81Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r81Nondeg.conditions rubi734r81Nondeg.body
    rubi734r81Nondeg.result rubi734r81Nondeg.integrals
  exact rubi731r101Nondeg_real

end OSR.IntegrationRec223
