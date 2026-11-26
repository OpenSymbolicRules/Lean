import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: residual integrals with shifted powers

Proofs of RUBI 4.1.2.2 #48 and #78 over ℝ and ℂ: `(g cos)^p (d sin)^n (a + b sin)²` splits into
`(d sin)^(n + 1)` and `a² + b² sin²` terms, and when `a² = b²`,
`cos⁴ (d sin)^n (a + b sin)^m` equals `(1 ∓ sin)² (d sin)^n (a + b sin)^(m + 2) / a²` (split on
`a = ±b`); the powers are split with `X^(j + n) = X^j X^n` (when `X ≠ 0` or `0 ≤ j`). -/

namespace OSR.IntegrationRec268

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv4R : intValue? (4 : ℝ) = some 4 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv4C : intValue? (4 : ℂ) = some 4 := (intValue?_eq _ _).2 (by norm_num)

private theorem zsplit {K : Type} [Field K] (X : K) (j : ℤ) (n : ℕ) (h : X ≠ 0 ∨ 0 ≤ j) :
    X ^ (j + n) = X ^ j * X ^ n := by
  rcases h with h | h
  · rw [zpow_add₀ h, zpow_natCast]
  · lift j to ℕ using h
    rw [show ((j : ℤ) + n) = ((j + n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_add]

/-! ## rubi4122r78Nondeg -/

theorem rubi4122r78Nondeg_real : rubi4122r78Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4122r78Nondeg.conditions rubi4122r78Nondeg.body
    rubi4122r78Nondeg.result rubi4122r78Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4122r78Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  rcases hkkp : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r78Nondeg, Defined, eval, Interp.real, hkkp] at h
  rcases hkkn : intValue? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r78Nondeg, Defined, eval, Interp.real, hkkp, hkkn] at h
  have enp1 : intValue? (env "n" + 1) = some (kn + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkn]; push_cast; ring)
  have ho0 : kn + 1 < 0 → kn < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4122r78Nondeg.body →
      (kp < 0 → env "g" * Real.cos (env "e" + env "f" * w) ≠ 0) ∧
          (kn < 0 → env "d" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4122r78Nondeg, Defined, eval, Interp.real, hkkp, hkkn, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r78Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, hkkp, hkkn, enp1, iv2R] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi4122r78Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hd]
  · simp only [rubi4122r78Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "g" * Real.cos (env "e" + env "f" * t)) ^ kp *
        (env "d" * Real.sin (env "e" + env "f" * t)) ^ (kn + 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkkp, enp1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "g" * Real.cos (env "e" + env "f" * t)) ^ kp *
        (env "d" * Real.sin (env "e" + env "f" * t)) ^ kn *
        (env "a" ^ 2 + env "b" ^ 2 * (Real.sin (env "e" + env "f" * t)) ^ 2)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkkp, hkkn, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4122r78Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r78Nondeg.result) = fun w => 2 * env "a" * env "b" * (env "d")⁻¹ *
            Φ "I1" w + 1 * Φ "I2" w := by
      funext w
      simp [rubi4122r78Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4122r78Nondeg.body =
        (env "g" * Real.cos (env "e" + env "f" * t)) ^ kp *
        (env "d" * Real.sin (env "e" + env "f" * t)) ^ kn *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ 2 := by
      simp [rubi4122r78Nondeg, eval, Interp.real, hkkp, hkkn, iv2R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨-, hS0⟩ := hD t hF.self_of_nhds
    have eX0 : (env "d" * Real.sin (env "e" + env "f" * t)) ^ (kn + 1) =
        (env "d" * Real.sin (env "e" + env "f" * t)) ^ (kn) *
        (env "d" * Real.sin (env "e" + env "f" * t)) ^ 1 := by
      have := zsplit (env "d" *
          Real.sin (env "e" + env "f" *
          t)) (kn) 1 ((by by_cases hk : kn < 0; exacts [Or.inl (hS0 hk), Or.inr (by omega)]))
      rwa [show kn + ((1 : ℕ) : ℤ) = kn + 1 by push_cast; ring] at this
    rw [eX0]
    rw [pow_one]
    generalize (env "g" * Real.cos (env "e" + env "f" * t)) ^ kp = G0
    generalize (env "d" * Real.sin (env "e" + env "f" * t)) ^ kn = G1
    field_simp
    ring

theorem rubi4122r78Nondeg_complex : rubi4122r78Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4122r78Nondeg.conditions rubi4122r78Nondeg.body
    rubi4122r78Nondeg.result rubi4122r78Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4122r78Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  rcases hkkp : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r78Nondeg, Defined, eval, Interp.complex, hkkp] at h
  rcases hkkn : intValue? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r78Nondeg, Defined, eval, Interp.complex, hkkp, hkkn] at h
  have enp1 : intValue? (env "n" + 1) = some (kn + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkn]; push_cast; ring)
  have ho0 : kn + 1 < 0 → kn < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4122r78Nondeg.body →
      (kp < 0 → env "g" * Complex.cos (env "e" + env "f" * w) ≠ 0) ∧
          (kn < 0 → env "d" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4122r78Nondeg, Defined, eval, Interp.complex, hkkp, hkkn, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r78Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, hkkp, hkkn, enp1, iv2C] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi4122r78Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hd]
  · simp only [rubi4122r78Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "g" * Complex.cos (env "e" + env "f" * t)) ^ kp *
        (env "d" * Complex.sin (env "e" + env "f" * t)) ^ (kn + 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkkp, enp1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "g" * Complex.cos (env "e" + env "f" * t)) ^ kp *
        (env "d" * Complex.sin (env "e" + env "f" * t)) ^ kn *
        (env "a" ^ 2 + env "b" ^ 2 * (Complex.sin (env "e" + env "f" * t)) ^ 2)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkkp, hkkn, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4122r78Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r78Nondeg.result) = fun w => 2 * env "a" * env "b" * (env "d")⁻¹ *
            Φ "I1" w + 1 * Φ "I2" w := by
      funext w
      simp [rubi4122r78Nondeg, eval, recEnv, Interp.complex, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4122r78Nondeg.body =
        (env "g" * Complex.cos (env "e" + env "f" * t)) ^ kp *
        (env "d" * Complex.sin (env "e" + env "f" * t)) ^ kn *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ 2 := by
      simp [rubi4122r78Nondeg, eval, Interp.complex, hkkp, hkkn, iv2C]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨-, hS0⟩ := hD t hF.self_of_nhds
    have eX0 : (env "d" * Complex.sin (env "e" + env "f" * t)) ^ (kn + 1) =
        (env "d" * Complex.sin (env "e" + env "f" * t)) ^ (kn) *
        (env "d" * Complex.sin (env "e" + env "f" * t)) ^ 1 := by
      have := zsplit (env "d" *
          Complex.sin (env "e" + env "f" *
          t)) (kn) 1 ((by by_cases hk : kn < 0; exacts [Or.inl (hS0 hk), Or.inr (by omega)]))
      rwa [show kn + ((1 : ℕ) : ℤ) = kn + 1 by push_cast; ring] at this
    rw [eX0]
    rw [pow_one]
    generalize (env "g" * Complex.cos (env "e" + env "f" * t)) ^ kp = G0
    generalize (env "d" * Complex.sin (env "e" + env "f" * t)) ^ kn = G1
    field_simp
    ring

/-! ## rubi4122r48Nondeg -/

theorem rubi4122r48Nondeg_real : rubi4122r48Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4122r48Nondeg.conditions rubi4122r48Nondeg.body
    rubi4122r48Nondeg.result rubi4122r48Nondeg.integrals
  intro env hc t hF
  have hab : env "a" ^ 2 - env "b" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4122r48Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  have habd : env "a" * env "b" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "d")) (.int 0)) (by simp [rubi4122r48Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  rcases hkkn : intValue? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r48Nondeg, Defined, eval, Interp.real, hkkn, iv4R] at h
  rcases hkkm : intValue? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r48Nondeg, Defined, eval, Interp.real, hkkn, hkkm, iv4R] at h
  have ha : env "a" ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul habd)
  have hb : env "b" ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul habd)
  have hd : env "d" ≠ 0 := right_ne_zero_of_mul habd
  have hpm : env "a" = env "b" ∨ env "a" = -env "b" := by
    have : (env "a" - env "b") * (env "a" + env "b") = 0 := by linear_combination hab
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have enp1 : intValue? (env "n" + 1) = some (kn + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkn]; push_cast; ring)
  have emp2 : intValue? (env "m" + 2) = some (km + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkm]; push_cast; ring)
  have ho0 : kn + 1 < 0 → kn < 0 := by omega
  have ho1 : km + 2 < 0 → km < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4122r48Nondeg.body →
      (kn < 0 → env "d" * Real.sin (env "e" + env "f" * w) ≠ 0) ∧
          (km < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4122r48Nondeg, Defined, eval, Interp.real, hkkn, hkkm, iv4R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r48Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, hkkn, enp1, emp2, iv2R] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi4122r48Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, ha, hb, hd]
  · simp only [rubi4122r48Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "d" * Real.sin (env "e" + env "f" * t)) ^ (kn + 1) *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (km + 2)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, enp1, emp2, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "d" * Real.sin (env "e" + env "f" * t)) ^ kn *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (km + 2) *
        (1 + (Real.sin (env "e" + env "f" * t)) ^ 2)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkkn, emp2, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4122r48Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r48Nondeg.result) = fun w => -2 * (env "a" * env "b" * env "d")⁻¹ *
            Φ "I1" w + (env "a" ^ 2)⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi4122r48Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4122r48Nondeg.body =
        (Real.cos (env "e" + env "f" * t)) ^ 4 *
        (env "d" * Real.sin (env "e" + env "f" * t)) ^ kn *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ km := by
      simp [rubi4122r48Nondeg, eval, Interp.real, hkkn, hkkm, iv4R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hS0, hA0⟩ := hD t hF.self_of_nhds
    have eX0 : (env "d" * Real.sin (env "e" + env "f" * t)) ^ (kn + 1) =
        (env "d" * Real.sin (env "e" + env "f" * t)) ^ (kn) *
        (env "d" * Real.sin (env "e" + env "f" * t)) ^ 1 := by
      have := zsplit (env "d" *
          Real.sin (env "e" + env "f" *
          t)) (kn) 1 ((by by_cases hk : kn < 0; exacts [Or.inl (hS0 hk), Or.inr (by omega)]))
      rwa [show kn + ((1 : ℕ) : ℤ) = kn + 1 by push_cast; ring] at this
    have eX1 : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (km + 2) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (km) *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ 2 := by
      have := zsplit (env "a" + env "b" *
          Real.sin (env "e" + env "f" *
          t)) (km) 2 ((by by_cases hk : km < 0; exacts [Or.inl (hA0 hk), Or.inr (by omega)]))
      rwa [show km + ((2 : ℕ) : ℤ) = km + 2 by push_cast; ring] at this
    rw [eX0, eX1]
    rw [pow_one, show (Real.cos (env "e" + env "f" * t)) ^ 4 =
        ((Real.cos (env "e" + env "f" * t)) ^ 2) ^ 2 by ring, Real.cos_sq']
    generalize (env "d" * Real.sin (env "e" + env "f" * t)) ^ kn = G0
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ km = G1
    generalize Real.sin (env "e" + env "f" * t) = G2
    rcases hpm with hq | hq <;> (rw [hq]; field_simp; ring)

theorem rubi4122r48Nondeg_complex : rubi4122r48Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4122r48Nondeg.conditions rubi4122r48Nondeg.body
    rubi4122r48Nondeg.result rubi4122r48Nondeg.integrals
  intro env hc t hF
  have hab : env "a" ^ 2 - env "b" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4122r48Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  have habd : env "a" * env "b" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "d")) (.int 0)) (by simp [rubi4122r48Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  rcases hkkn : intValue? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r48Nondeg, Defined, eval, Interp.complex, hkkn, iv4C] at h
  rcases hkkm : intValue? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r48Nondeg, Defined, eval, Interp.complex, hkkn, hkkm, iv4C] at h
  have ha : env "a" ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul habd)
  have hb : env "b" ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul habd)
  have hd : env "d" ≠ 0 := right_ne_zero_of_mul habd
  have hpm : env "a" = env "b" ∨ env "a" = -env "b" := by
    have : (env "a" - env "b") * (env "a" + env "b") = 0 := by linear_combination hab
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have enp1 : intValue? (env "n" + 1) = some (kn + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkn]; push_cast; ring)
  have emp2 : intValue? (env "m" + 2) = some (km + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkm]; push_cast; ring)
  have ho0 : kn + 1 < 0 → kn < 0 := by omega
  have ho1 : km + 2 < 0 → km < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4122r48Nondeg.body →
      (kn < 0 → env "d" * Complex.sin (env "e" + env "f" * w) ≠ 0) ∧
          (km < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4122r48Nondeg, Defined, eval, Interp.complex, hkkn, hkkm, iv4C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r48Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, hkkn, enp1, emp2, iv2C] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi4122r48Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, ha, hb, hd]
  · simp only [rubi4122r48Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "d" * Complex.sin (env "e" + env "f" * t)) ^ (kn + 1) *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (km + 2)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, enp1, emp2, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "d" * Complex.sin (env "e" + env "f" * t)) ^ kn *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (km + 2) *
        (1 + (Complex.sin (env "e" + env "f" * t)) ^ 2)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkkn, emp2, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4122r48Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r48Nondeg.result) = fun w => -2 * (env "a" * env "b" * env "d")⁻¹ *
            Φ "I1" w + (env "a" ^ 2)⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi4122r48Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4122r48Nondeg.body =
        (Complex.cos (env "e" + env "f" * t)) ^ 4 *
        (env "d" * Complex.sin (env "e" + env "f" * t)) ^ kn *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ km := by
      simp [rubi4122r48Nondeg, eval, Interp.complex, hkkn, hkkm, iv4C]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hS0, hA0⟩ := hD t hF.self_of_nhds
    have eX0 : (env "d" * Complex.sin (env "e" + env "f" * t)) ^ (kn + 1) =
        (env "d" * Complex.sin (env "e" + env "f" * t)) ^ (kn) *
        (env "d" * Complex.sin (env "e" + env "f" * t)) ^ 1 := by
      have := zsplit (env "d" *
          Complex.sin (env "e" + env "f" *
          t)) (kn) 1 ((by by_cases hk : kn < 0; exacts [Or.inl (hS0 hk), Or.inr (by omega)]))
      rwa [show kn + ((1 : ℕ) : ℤ) = kn + 1 by push_cast; ring] at this
    have eX1 : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (km + 2) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (km) *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ 2 := by
      have := zsplit (env "a" + env "b" *
          Complex.sin (env "e" + env "f" *
          t)) (km) 2 ((by by_cases hk : km < 0; exacts [Or.inl (hA0 hk), Or.inr (by omega)]))
      rwa [show km + ((2 : ℕ) : ℤ) = km + 2 by push_cast; ring] at this
    rw [eX0, eX1]
    rw [pow_one, show (Complex.cos (env "e" + env "f" * t)) ^ 4 =
        ((Complex.cos (env "e" + env "f" * t)) ^ 2) ^ 2 by ring, Complex.cos_sq']
    generalize (env "d" * Complex.sin (env "e" + env "f" * t)) ^ kn = G0
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ km = G1
    generalize Complex.sin (env "e" + env "f" * t) = G2
    rcases hpm with hq | hq <;> (rw [hq]; field_simp; ring)

end OSR.IntegrationRec268
