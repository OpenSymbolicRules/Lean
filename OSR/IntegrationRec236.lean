import OSR.IntegrationRec215

/-! # Strengthened inverse hyperbolic tangent rules: `(d + e x^2)^q (a + b artanh(c x))^p`

Proofs over ℝ of RUBI 7.3.1 #31 and #51 (and their 7.3.4 #11 and #31 twins), the reductions of
`∫ (d + e x^2)^q (a + b artanh(c x))^p dx` to the exponents `(q - 1, p)` and `(q - 1, p - 2)`
for an integer `q > 0`, and to `(q + 1, p)` and `(q, p - 2)` for an integer `q < -1`, when
`c^2 d + e = 0` and `p > 1`. The complex statement is vacuous (no
complex interpretation of `transc1#arctanh`) and stays unproved. -/

namespace OSR.IntegrationRec236

open OSR OSR.Calculus OSR.IntegrationNum1 OSR.IntegrationRec215 Filter Topology

private theorem zpow_add_nat_of (A : ℝ) (j : ℤ) (n : ℕ) (h : 0 ≤ j) :
    A ^ (j + n) = A ^ j * A ^ n := by
  lift j to ℕ using h
  rw [show ((j : ℤ) + n) = ((j + n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
    pow_add]

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem hasDerivAt_quad0 (d e t : ℝ) :
    HasDerivAt (fun w => d + e * w ^ 2) (e * (2 * t)) t := by
  have := ((hasDerivAt_pow 2 t).const_mul e).const_add d
  simpa using this

/-! ## RUBI 7.3.1 #31 (and 7.3.4 #11) -/

theorem rubi731r31Nondeg_real : rubi731r31Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r31Nondeg.conditions rubi731r31Nondeg.body
    rubi731r31Nondeg.result rubi731r31Nondeg.integrals
  intro env hc t hF
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r31Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hqpos : 0 < env "q" := by
    have h := hc (.gt (.var "q") (.int 0)) (by simp [rubi731r31Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hpgt : 1 < env "p" := by
    have h := hc (.gt (.var "p") (.int 1)) (by simp [rubi731r31Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW : 2 * env "c" * env "q" * (2 * env "q" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "q"))
      (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 1))) (.int 0))
      (by simp [rubi731r31Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW' := hW
  simp only [mul_ne_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, true_and] at hW'
  obtain ⟨⟨hcz, hq0⟩, hq1⟩ := hW'
  have he' : env "e" = -(env "c" ^ 2 * env "d") := by linear_combination hrel
  rcases hkq : intValue? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r31Nondeg, Defined, eval, Interp.real, hkq] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r31Nondeg, Defined, eval, Interp.real, hkq, hkp] at h
  have hq : env "q" = (k : ℝ) := (intValue?_eq _ _).1 hkq
  have hp : env "p" = (l : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hq] at hqpos; exact_mod_cast hqpos
  have hl : 1 < l := by
    have : (1 : ℝ) < l := hp ▸ hpgt
    exact_mod_cast this
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hk1' : ¬ k < 1 := by omega
  have hl0 : ¬ l < 0 := by omega
  have hl1 : ¬ l - 1 < 0 := by omega
  have hl1' : ¬ l < 1 := by omega
  have hl2 : ¬ l - 2 < 0 := by omega
  have hl2' : ¬ l < 2 := by omega
  have eq1 : intValue? (env "q" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have ep1 : intValue? (env "p" + -1) = some (l - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have ep2 : intValue? (env "p" + -2) = some (l - 2) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r31Nondeg.body →
      -1 < env "c" * w ∧ env "c" * w < 1 := by
    intro w h
    simp [rubi731r31Nondeg, Defined, eval, Interp.real, hkq, hkp, hk0, hl0, iv2R] at h
    tauto
  obtain ⟨h1, h2⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r31Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have hB := hD w hw
      simp [Defined, eval, Interp.real, eq1, hkp, iv2R, hk1, hl0, hB.1, hB.2]
    · filter_upwards [hF] with w hw
      have hB := hD w hw
      simp [Defined, eval, Interp.real, eq1, ep2, iv2R, hk1, hl2, hB.1, hB.2]
  · filter_upwards [hF] with w hw
    have hB := hD w hw
    simp [rubi731r31Nondeg, Defined, eval, recEnv, Interp.real, hkq, ep1, hkp, ivm1R, iv2R, hcz,
      hq0, hq1, hk0, hl1, hl0, hB.1, hB.2]
  · simp only [rubi731r31Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t ^ 2) ^ (k - 1) *
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ l) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, eq1, hkp, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "d" + env "e" * t ^ 2) ^ (k - 1) *
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 2)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, eq1, ep2, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r31Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r31Nondeg.result) =
        fun w => env "b" * env "p" * (2 * env "c" * env "q" * (2 * env "q" + 1))⁻¹ *
              ((env "d" + env "e" * w ^ 2) ^ k *
                (env "a" + env "b" * Real.artanh (env "c" * w)) ^ (l - 1)) +
            w * (env "d" + env "e" * w ^ 2) ^ k *
              (env "a" + env "b" * Real.artanh (env "c" * w)) ^ l * (2 * env "q" + 1)⁻¹ +
            2 * env "d" * env "q" * (2 * env "q" + 1)⁻¹ * Φ "I1" w +
            -(env "b" ^ 2 * env "d" * env "p" * (env "p" - 1) *
              (2 * env "q" * (2 * env "q" + 1))⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi731r31Nondeg, eval, recEnv, Interp.real, hkq, ep1, hkp, ivm1R, iv2R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r31Nondeg.body =
        (env "d" + env "e" * t ^ 2) ^ k * (env "a" + env "b" * Real.artanh (env "c" * t)) ^ l := by
      simp [rubi731r31Nondeg, eval, Interp.real, hkq, hkp, iv2R]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_artanh_mul h1 h2).const_mul (env "b")).const_add (env "a")
    have hDq := (hasDerivAt_zpow k _ (Or.inr hk.le)).comp t (hasDerivAt_quad0 (env "d") (env "e") t)
    have hAl1 := (hasDerivAt_zpow (l - 1) _ (Or.inr (by omega))).comp t hA
    have hAl := (hasDerivAt_zpow l _ (Or.inr (by omega))).comp t hA
    refine ((((hDq.mul hAl1).const_mul _).add
      ((((hasDerivAt_id' t).mul hDq).mul hAl).mul_const _)).add (hΦ1'.const_mul _) |>.add
      (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Pi.mul_apply, Function.comp_apply]
    have eD : (env "d" + env "e" * t ^ 2) ^ k =
        (env "d" + env "e" * t ^ 2) ^ (k - 1) * (env "d" + env "e" * t ^ 2) := by
      have := zpow_add_nat_of (env "d" + env "e" * t ^ 2) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    have eA : (env "a" + env "b" * Real.artanh (env "c" * t)) ^ l =
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 2) *
          (env "a" + env "b" * Real.artanh (env "c" * t)) ^ 2 := by
      have := zpow_add_nat_of (env "a" + env "b" * Real.artanh (env "c" * t)) (l - 2) 2 (by omega)
      rwa [show l - 2 + ((2 : ℕ) : ℤ) = l by push_cast; ring] at this
    have eA1 : (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 1) =
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 2) *
          (env "a" + env "b" * Real.artanh (env "c" * t)) := by
      have := zpow_add_nat_of (env "a" + env "b" * Real.artanh (env "c" * t)) (l - 2) 1 (by omega)
      rwa [show l - 2 + ((1 : ℕ) : ℤ) = l - 1 by push_cast; ring, pow_one] at this
    have eA2 : (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 1 - 1) =
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 2) := by
      rw [show l - 1 - 1 = l - 2 by ring]
    rw [eA2, eD, eA, eA1]
    have hkr : ((k : ℤ) : ℝ) = env "q" := hq.symm
    have hlr : ((l : ℤ) : ℝ) = env "p" := hp.symm
    have hl1r : ((l - 1 : ℤ) : ℝ) = env "p" - 1 := by rw [hp]; push_cast; ring
    rw [hkr, hlr, hl1r]
    have hD' := one_sub_sq_mul_ne h1 h2
    have hD'' : 1 - t ^ 2 * env "c" ^ 2 ≠ 0 := by rwa [mul_comm] at hD'
    generalize (env "d" + env "e" * t ^ 2) ^ (k - 1) = P
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 2) = R
    generalize env "a" + env "b" * Real.artanh (env "c" * t) = T
    rw [he']
    field_simp
    ring

theorem rubi734r11Nondeg_real : rubi734r11Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r11Nondeg.conditions rubi734r11Nondeg.body
    rubi734r11Nondeg.result rubi734r11Nondeg.integrals
  exact rubi731r31Nondeg_real

/-! ## RUBI 7.3.1 #51 (and 7.3.4 #31) -/

theorem rubi731r51Nondeg_real : rubi731r51Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r51Nondeg.conditions rubi731r51Nondeg.body
    rubi731r51Nondeg.result rubi731r51Nondeg.integrals
  intro env hc t hF
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r51Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hqlt : env "q" < -1 := by
    have h := hc (.gt (.int (-1)) (.var "q")) (by simp [rubi731r51Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hpgt : 1 < env "p" := by
    have h := hc (.gt (.var "p") (.int 1)) (by simp [rubi731r51Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW : 4 * env "c" * env "d" * (env "q" + 1) ^ 2 ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.var "c")) (.var "d"))
      (.pow (.app2 .add (.var "q") (.int 1)) (.int 2))) (.int 0)) (by simp [rubi731r51Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hW' := hW
  simp only [mul_ne_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, true_and,
    pow_eq_zero_iff] at hW'
  obtain ⟨⟨hcz, hd⟩, hq1⟩ := hW'
  have he' : env "e" = -(env "c" ^ 2 * env "d") := by linear_combination hrel
  rcases hkq : intValue? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r51Nondeg, Defined, eval, Interp.real, hkq] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r51Nondeg, Defined, eval, Interp.real, hkq, hkp] at h
  have hq : env "q" = (k : ℝ) := (intValue?_eq _ _).1 hkq
  have hp : env "p" = (l : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : k < -1 := by
    have : (k : ℝ) < -1 := hq ▸ hqlt
    exact_mod_cast this
  have hl : 1 < l := by
    have : (1 : ℝ) < l := hp ▸ hpgt
    exact_mod_cast this
  have hk0 : k < 0 := by omega
  have hk1 : k + 1 < 0 := by omega
  have hl0 : ¬ l < 0 := by omega
  have hl1 : ¬ l - 1 < 0 := by omega
  have hl1' : ¬ l < 1 := by omega
  have hl2 : ¬ l - 2 < 0 := by omega
  have hl2' : ¬ l < 2 := by omega
  have eq1 : intValue? (env "q" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have ep1 : intValue? (env "p" + -1) = some (l - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have ep2 : intValue? (env "p" + -2) = some (l - 2) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r51Nondeg.body →
      env "d" + env "e" * w ^ 2 ≠ 0 ∧ (-1 < env "c" * w ∧ env "c" * w < 1) := by
    intro w h
    simp [rubi731r51Nondeg, Defined, eval, Interp.real, hkq, hkp, hk0, hl0, iv2R] at h
    tauto
  obtain ⟨hD0, h1, h2⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r51Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have hB := hD w hw
      simp [Defined, eval, Interp.real, eq1, hkp, iv2R, hl0, hB.1, hB.2.1, hB.2.2]
    · filter_upwards [hF] with w hw
      have hB := hD w hw
      simp [Defined, eval, Interp.real, hkq, ep2, iv2R, hl2, hB.1, hB.2.1, hB.2.2]
  · filter_upwards [hF] with w hw
    have hB := hD w hw
    simp [rubi731r51Nondeg, Defined, eval, recEnv, Interp.real, eq1, ep1, hkp, ivm1R, iv2R, hcz,
      hd, hq1, hl1, hl0, hB.1, hB.2.1, hB.2.2]
  · simp only [rubi731r51Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t ^ 2) ^ (k + 1) *
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ l) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, eq1, hkp, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "d" + env "e" * t ^ 2) ^ k *
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 2)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkq, ep2, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r51Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r51Nondeg.result) =
        fun w => -(env "b" * env "p") * (4 * env "c" * env "d" * (env "q" + 1) ^ 2)⁻¹ *
              ((env "d" + env "e" * w ^ 2) ^ (k + 1) *
                (env "a" + env "b" * Real.artanh (env "c" * w)) ^ (l - 1)) +
            w * (env "d" + env "e" * w ^ 2) ^ (k + 1) *
              (env "a" + env "b" * Real.artanh (env "c" * w)) ^ l *
              -(2 * env "d" * (env "q" + 1))⁻¹ +
            (2 * env "q" + 3) * (2 * env "d" * (env "q" + 1))⁻¹ * Φ "I1" w +
            env "b" ^ 2 * env "p" * (env "p" - 1) * (4 * (env "q" + 1) ^ 2)⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi731r51Nondeg, eval, recEnv, Interp.real, eq1, ep1, hkp, ivm1R, iv2R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r51Nondeg.body =
        (env "d" + env "e" * t ^ 2) ^ k * (env "a" + env "b" * Real.artanh (env "c" * t)) ^ l := by
      simp [rubi731r51Nondeg, eval, Interp.real, hkq, hkp, iv2R]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_artanh_mul h1 h2).const_mul (env "b")).const_add (env "a")
    have hDq := (hasDerivAt_zpow (k + 1) _ (Or.inl hD0)).comp t
      (hasDerivAt_quad0 (env "d") (env "e") t)
    have hAl1 := (hasDerivAt_zpow (l - 1) _ (Or.inr (by omega))).comp t hA
    have hAl := (hasDerivAt_zpow l _ (Or.inr (by omega))).comp t hA
    refine ((((hDq.mul hAl1).const_mul _).add
      ((((hasDerivAt_id' t).mul hDq).mul hAl).mul_const _)).add (hΦ1'.const_mul _) |>.add
      (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Pi.mul_apply, Function.comp_apply]
    have eD : (env "d" + env "e" * t ^ 2) ^ (k + 1) =
        (env "d" + env "e" * t ^ 2) ^ k * (env "d" + env "e" * t ^ 2) := zpow_add_one₀ hD0 k
    have eA : (env "a" + env "b" * Real.artanh (env "c" * t)) ^ l =
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 2) *
          (env "a" + env "b" * Real.artanh (env "c" * t)) ^ 2 := by
      have := zpow_add_nat_of (env "a" + env "b" * Real.artanh (env "c" * t)) (l - 2) 2 (by omega)
      rwa [show l - 2 + ((2 : ℕ) : ℤ) = l by push_cast; ring] at this
    have eA1 : (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 1) =
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 2) *
          (env "a" + env "b" * Real.artanh (env "c" * t)) := by
      have := zpow_add_nat_of (env "a" + env "b" * Real.artanh (env "c" * t)) (l - 2) 1 (by omega)
      rwa [show l - 2 + ((1 : ℕ) : ℤ) = l - 1 by push_cast; ring, pow_one] at this
    have eA2 : (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 1 - 1) =
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 2) := by
      rw [show l - 1 - 1 = l - 2 by ring]
    have eD1 : (env "d" + env "e" * t ^ 2) ^ (k + 1 - 1) = (env "d" + env "e" * t ^ 2) ^ k := by
      rw [show k + 1 - 1 = k by ring]
    rw [eA2, eD1, eD, eA, eA1]
    have hkr : ((k + 1 : ℤ) : ℝ) = env "q" + 1 := by rw [hq]; push_cast; ring
    have hlr : ((l : ℤ) : ℝ) = env "p" := hp.symm
    have hl1r : ((l - 1 : ℤ) : ℝ) = env "p" - 1 := by rw [hp]; push_cast; ring
    rw [hkr, hlr, hl1r]
    have hD' := one_sub_sq_mul_ne h1 h2
    have hD'' : 1 - t ^ 2 * env "c" ^ 2 ≠ 0 := by rwa [mul_comm] at hD'
    generalize (env "d" + env "e" * t ^ 2) ^ k = P
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (l - 2) = R
    generalize env "a" + env "b" * Real.artanh (env "c" * t) = T
    rw [he']
    field_simp
    ring

theorem rubi734r31Nondeg_real : rubi734r31Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r31Nondeg.conditions rubi734r31Nondeg.body
    rubi734r31Nondeg.result rubi734r31Nondeg.integrals
  exact rubi731r51Nondeg_real

end OSR.IntegrationRec236
