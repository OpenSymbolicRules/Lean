import OSR.IntegrationRec215

/-! # Strengthened inverse hyperbolic tangent rule: `(f x)^m (d + e x^2)^q`, `m + 2 q + 2 = 0`, `p > 1`

Proof over ℝ of RUBI 7.3.1 #89 (and its 7.3.4 #69 twin), integrating
`(f x)^m (d + e x^2)^q (a + b artanh(c x))^p` by parts twice when `c^2 d + e = 0` and
`m + 2 q + 2 = 0` (so `m ≥ 2` for `q < -1`), with the derivative
`OSR.IntegrationRec215.hasDerivAt_artanh_mul`. The complex statement is vacuous (no complex
interpretation of `transc1#arctanh`) and stays unproved. -/

namespace OSR.IntegrationRec224

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

/-! ## RUBI 7.3.1 #89 (and 7.3.4 #69) -/

theorem rubi731r89Nondeg_real : rubi731r89Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r89Nondeg.conditions rubi731r89Nondeg.body
    rubi731r89Nondeg.result rubi731r89Nondeg.integrals
  intro env hc t hF
  have hW : env "c" * env "d" * env "m" ^ 2 ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.pow (.var "m") (.int 2)))
      (.int 0)) (by simp [rubi731r89Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r89Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hmq : env "m" + 2 * env "q" + 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 2))
      (.int 0)) (by simp [rubi731r89Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hneg : env "q" < -1 := by
    have h := hc (.gt (.int (-1)) (.var "q")) (by simp [rubi731r89Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hpgt : 1 < env "p" := by
    have h := hc (.gt (.var "p") (.int 1)) (by simp [rubi731r89Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff, pow_ne_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    at hW'
  obtain ⟨⟨hcz, hd⟩, hm0⟩ := hW'
  have he' : env "e" = -(env "c" ^ 2 * env "d") := by linear_combination hrel
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r89Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r89Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r89Nondeg, Defined, eval, Interp.real, hkm, hkq, hkp] at h
  have hp : env "p" = (l : ℝ) := (intValue?_eq _ _).1 hkp
  have hl : 2 ≤ l := by
    have : (1 : ℝ) < l := hp ▸ hpgt
    exact_mod_cast (show (1 : ℤ) < l by exact_mod_cast this)
  have hl0 : ¬ l < 0 := by omega
  have hl1 : ¬ l - 1 < 0 := by omega
  have hl1' : ¬ l < 1 := by omega
  have hl2 : ¬ l - 2 < 0 := by omega
  have hl2' : ¬ l < 2 := by omega
  have ep1 : intValue? (env "p" + -1) = some (l - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have ep2 : intValue? (env "p" + -2) = some (l - 2) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hq : env "q" = (k : ℝ) := (intValue?_eq _ _).1 hkq
  have hk : k < -1 := by rw [hq] at hneg; exact_mod_cast hneg
  have hjk : j = -2 * k - 2 := by
    have : (j : ℝ) = -2 * k - 2 := by rw [← hm, ← hq]; linear_combination hmq
    exact_mod_cast this
  have hj : 2 ≤ j := by omega
  have hj0 : ¬ j < 0 := by omega
  have hj1 : ¬ j - 1 < 0 := by omega
  have hj1' : ¬ j < 1 := by omega
  have hj2 : ¬ j - 2 < 0 := by omega
  have hj2' : ¬ j < 2 := by omega
  have hk0 : k < 0 := by omega
  have hk1 : k + 1 < 0 := by omega
  have eq1 : intValue? (env "q" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have em1 : intValue? (env "m" + -1) = some (j - 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have em1' : intValue? (env "m" - 1) = some (j - 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have em2 : intValue? (env "m" + -2) = some (j - 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have em2' : intValue? (env "m" - 2) = some (j - 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r89Nondeg.body →
      env "d" + env "e" * w ^ 2 ≠ 0 ∧ (-1 < env "c" * w ∧ env "c" * w < 1) := by
    intro w h
    simp [rubi731r89Nondeg, Defined, eval, Interp.real, hkm, hkq, hkp, iv2R, hj0, hk0, hl0] at h
    tauto
  obtain ⟨hD0, hc1, hc2⟩ := hBody t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r89Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have hB := hBody w hw
      simp [Defined, eval, Interp.real, hkm, hkq, ep2, iv2R, hj0, hl2, hB.1, hB.2.1,
        hB.2.2]
    · filter_upwards [hF] with w hw
      have hB := hBody w hw
      simp [Defined, eval, Interp.real, em2, eq1, hkp, iv2R, hj2, hl0, hB.1,
        hB.2.1, hB.2.2]
  · filter_upwards [hF] with w hw
    have hB := hBody w hw
    simp [rubi731r89Nondeg, Defined, eval, recEnv, Interp.real, hkm, hkp, em1, eq1, ep1,
      ivm1R, iv2R, hcz, hd, hm0, hj0, hj1, hl0, hl1, hB.1, hB.2.1, hB.2.2]
  · simp only [rubi731r89Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ j * (env "d" + env "e" * t ^ 2) ^ k *
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 2)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkq, ep2, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (j - 2) *
        (env "d" + env "e" * t ^ 2) ^ (k + 1) *
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ l) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, em2, eq1, hkp, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r89Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r89Nondeg.result) =
        fun w => -env "b" * env "p" * (env "f" * w) ^ j * (env "d" + env "e" * w ^ 2) ^ (k + 1) *
            (env "a" + env "b" * Real.artanh (env "c" * w)) ^ (l - 1) *
            (env "c" * env "d" * env "m" ^ 2)⁻¹ +
          env "f" * (env "f" * w) ^ (j - 1) * (env "d" + env "e" * w ^ 2) ^ (k + 1) *
            (env "a" + env "b" * Real.artanh (env "c" * w)) ^ l *
            (env "c" ^ 2 * env "d" * env "m")⁻¹ +
          env "b" ^ 2 * env "p" * (env "p" - 1) * (env "m" ^ 2)⁻¹ * Φ "I1" w +
          -env "f" ^ 2 * (env "m" - 1) * (env "c" ^ 2 * env "d" * env "m")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi731r89Nondeg, eval, recEnv, Interp.real, hkm, hkp, em1, eq1, ep1, ivm1R, iv2R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r89Nondeg.body =
        (env "f" * t) ^ j * (env "d" + env "e" * t ^ 2) ^ k *
          (env "a" + env "b" * Real.artanh (env "c" * t)) ^ l := by
      simp [rubi731r89Nondeg, eval, Interp.real, hkm, hkq, hkp, iv2R]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_artanh_mul hc1 hc2).const_mul (env "b")).const_add (env "a")
    have hF0 := (hasDerivAt_zpow j _ (Or.inr (by omega))).comp t
      ((hasDerivAt_id' t).const_mul (env "f"))
    have hF1 := (hasDerivAt_zpow (j - 1) _ (Or.inr (by omega))).comp t
      ((hasDerivAt_id' t).const_mul (env "f"))
    have hQ := (hasDerivAt_zpow (k + 1) _ (Or.inl hD0)).comp t
      (hasDerivAt_quad0 (env "d") (env "e") t)
    have hP1 := (hasDerivAt_zpow (l - 1) _ (Or.inr (by omega))).comp t hA
    have hP := (hasDerivAt_zpow l _ (Or.inr (by omega))).comp t hA
    refine ((((((hF0.const_mul (-env "b" * env "p")).mul hQ).mul hP1).mul_const _).add
      ((((hF1.const_mul (env "f")).mul hQ).mul hP).mul_const _)).add
      (hΦ1'.const_mul _) |>.add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply, Pi.mul_apply, add_sub_cancel_right]
    have f2 : (env "f" * t) ^ j = (env "f" * t) ^ (j - 2) * (env "f" * t) ^ 2 := by
      have := zpow_add_nat_of (env "f" * t) (j - 2) 2 (by omega)
      rwa [show j - 2 + ((2 : ℕ) : ℤ) = j by push_cast; ring] at this
    have f1 : (env "f" * t) ^ (j - 1) = (env "f" * t) ^ (j - 2) * (env "f" * t) := by
      have := zpow_add_nat_of (env "f" * t) (j - 2) 1 (by omega)
      rwa [show j - 2 + ((1 : ℕ) : ℤ) = j - 1 by push_cast; ring, pow_one] at this
    have f0 : (env "f" * t) ^ (j - 1 - 1) = (env "f" * t) ^ (j - 2) := by
      rw [show j - 1 - 1 = j - 2 by ring]
    have g2 : (env "a" + env "b" * Real.artanh (env "c" * t)) ^ l =
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 2) *
          (env "a" + env "b" * Real.artanh (env "c" * t)) ^ 2 := by
      have := zpow_add_nat_of (env "a" + env "b" * Real.artanh (env "c" * t)) (l - 2) 2 (by omega)
      rwa [show l - 2 + ((2 : ℕ) : ℤ) = l by push_cast; ring] at this
    have g1 : (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 1) =
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 2) *
          (env "a" + env "b" * Real.artanh (env "c" * t)) := by
      have := zpow_add_nat_of (env "a" + env "b" * Real.artanh (env "c" * t)) (l - 2) 1 (by omega)
      rwa [show l - 2 + ((1 : ℕ) : ℤ) = l - 1 by push_cast; ring, pow_one] at this
    have g0 : (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 1 - 1) =
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 2) := by
      rw [show l - 1 - 1 = l - 2 by ring]
    rw [f0, f2, f1, g0, g2, g1, zpow_add_one₀ hD0]
    have hjr : ((j : ℤ) : ℝ) = env "m" := hm.symm
    have hj1r : ((j - 1 : ℤ) : ℝ) = env "m" - 1 := by rw [hm]; push_cast; ring
    have hk1r : ((k + 1 : ℤ) : ℝ) = env "q" + 1 := by rw [hq]; push_cast; ring
    have hlr : ((l : ℤ) : ℝ) = env "p" := hp.symm
    have hl1r : ((l - 1 : ℤ) : ℝ) = env "p" - 1 := by rw [hp]; push_cast; ring
    rw [hjr, hj1r, hk1r, hlr, hl1r]
    have hD := one_sub_sq_mul_ne hc1 hc2
    have hD' : 1 - t ^ 2 * env "c" ^ 2 ≠ 0 := by rwa [mul_comm] at hD
    have hdenD : env "d" + env "e" * t ^ 2 = env "d" * (1 - env "c" ^ 2 * t ^ 2) := by
      rw [he']; ring
    have hmv : env "m" = -2 * env "q" - 2 := by linear_combination hmq
    generalize (env "f" * t) ^ (j - 2) = P
    generalize (env "d" + env "e" * t ^ 2) ^ k = Q
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 2) = R
    generalize env "a" + env "b" * Real.artanh (env "c" * t) = T
    rw [hdenD, he']
    field_simp
    rw [hmv]
    ring

theorem rubi734r69Nondeg_real : rubi734r69Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r69Nondeg.conditions rubi734r69Nondeg.body
    rubi734r69Nondeg.result rubi734r69Nondeg.integrals
  exact rubi731r89Nondeg_real

end OSR.IntegrationRec224
