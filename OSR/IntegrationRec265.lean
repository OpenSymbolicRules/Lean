import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: residual integrals with shifted powers

Proof of RUBI 1.1.3.5 #31 over ℝ and ℂ: `(a + b xⁿ)^p (c + d xⁿ)^q (e + f xⁿ)^r` is
`(b (c + d xⁿ) - d (a + b xⁿ)) / (b c - a d)` times itself, which splits into two residual
integrals with `q + 1` and `p + 1`; the powers are split with `X^(j + n) = X^j X^n` (when `X ≠ 0` or
`0 ≤ j`). -/

namespace OSR.IntegrationRec265

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem zsplit {K : Type} [Field K] (X : K) (j : ℤ) (n : ℕ) (h : X ≠ 0 ∨ 0 ≤ j) :
    X ^ (j + n) = X ^ j * X ^ n := by
  rcases h with h | h
  · rw [zpow_add₀ h, zpow_natCast]
  · lift j to ℕ using h
    rw [show ((j : ℤ) + n) = ((j + n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_add]

/-! ## rubi1135r31Nondeg -/

theorem rubi1135r31Nondeg_real : rubi1135r31Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1135r31Nondeg.conditions rubi1135r31Nondeg.body
    rubi1135r31Nondeg.result rubi1135r31Nondeg.integrals
  intro env hc t hF
  have hbc : env "b" * env "c" - env "a" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi1135r31Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  rcases hkkn : intValue? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r31Nondeg, Defined, eval, Interp.real, hkkn] at h
  rcases hkkp : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r31Nondeg, Defined, eval, Interp.real, hkkn, hkkp] at h
  rcases hkkq : intValue? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r31Nondeg, Defined, eval, Interp.real, hkkn, hkkp, hkkq] at h
  rcases hkkr : intValue? (env "r") with _ | kr
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r31Nondeg, Defined, eval, Interp.real, hkkn, hkkp, hkkq, hkkr] at h
  have hbc' : env "b" * env "c" + -(env "a" * env "d") ≠ 0 := by rwa [← sub_eq_add_neg]
  have epp1 : intValue? (env "p" + 1) = some (kp + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkp]; push_cast; ring)
  have eqp1 : intValue? (env "q" + 1) = some (kq + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkq]; push_cast; ring)
  have ho0 : kp + 1 < 0 → kp < 0 := by omega
  have ho1 : kq + 1 < 0 → kq < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1135r31Nondeg.body →
      (kn < 0 → w ≠ 0) ∧ (kp < 0 → env "a" + env "b" * w ^ kn ≠ 0) ∧
          (kq < 0 → env "c" + env "d" * w ^ kn ≠ 0) ∧ (kr < 0 → env "e" + env "f" * w ^ kn ≠ 0) :=
          by
    intro w h
    simp [rubi1135r31Nondeg, Defined, eval, Interp.real, hkkn, hkkp, hkkq, hkkr] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1135r31Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, hkkn, hkkp, hkkq, hkkr, epp1, eqp1] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi1135r31Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hbc']
  · simp only [rubi1135r31Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" * t ^ kn) ^ kp *
        (env "c" + env "d" * t ^ kn) ^ (kq + 1) * (env "e" + env "f" * t ^ kn) ^ kr) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkkn, hkkp, hkkr, eqp1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "a" + env "b" * t ^ kn) ^ (kp + 1) *
        (env "c" + env "d" * t ^ kn) ^ kq * (env "e" + env "f" * t ^ kn) ^ kr) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkkn, hkkq, hkkr, epp1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1135r31Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1135r31Nondeg.result) = fun w => env "b" *
            (env "b" * env "c" - env "a" * env "d")⁻¹ * Φ "I1" w +
            -(env "d" * (env "b" * env "c" - env "a" * env "d")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi1135r31Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi1135r31Nondeg.body =
        (env "a" + env "b" * t ^ kn) ^ kp * (env "c" + env "d" * t ^ kn) ^ kq *
        (env "e" + env "f" * t ^ kn) ^ kr := by
      simp [rubi1135r31Nondeg, eval, Interp.real, hkkn, hkkp, hkkq, hkkr]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨-, hA0, hC0, -⟩ := hD t hF.self_of_nhds
    have eX0 : (env "c" + env "d" * t ^ kn) ^ (kq + 1) = (env "c" + env "d" * t ^ kn) ^ (kq) *
        (env "c" + env "d" * t ^ kn) ^ 1 := by
      have := zsplit (env "c" + env "d" *
          t ^ kn) (kq) 1 ((by by_cases hk : kq < 0; exacts [Or.inl (hC0 hk), Or.inr (by omega)]))
      rwa [show kq + ((1 : ℕ) : ℤ) = kq + 1 by push_cast; ring] at this
    have eX1 : (env "a" + env "b" * t ^ kn) ^ (kp + 1) = (env "a" + env "b" * t ^ kn) ^ (kp) *
        (env "a" + env "b" * t ^ kn) ^ 1 := by
      have := zsplit (env "a" + env "b" *
          t ^ kn) (kp) 1 ((by by_cases hk : kp < 0; exacts [Or.inl (hA0 hk), Or.inr (by omega)]))
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this
    rw [eX0, eX1]
    rw [pow_one, pow_one]
    generalize (env "a" + env "b" * t ^ kn) ^ kp = G0
    generalize (env "c" + env "d" * t ^ kn) ^ kq = G1
    generalize (env "e" + env "f" * t ^ kn) ^ kr = G2
    generalize t ^ kn = G3
    field_simp
    ring

theorem rubi1135r31Nondeg_complex : rubi1135r31Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1135r31Nondeg.conditions rubi1135r31Nondeg.body
    rubi1135r31Nondeg.result rubi1135r31Nondeg.integrals
  intro env hc t hF
  have hbc : env "b" * env "c" - env "a" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi1135r31Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  rcases hkkn : intValue? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r31Nondeg, Defined, eval, Interp.complex, hkkn] at h
  rcases hkkp : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r31Nondeg, Defined, eval, Interp.complex, hkkn, hkkp] at h
  rcases hkkq : intValue? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r31Nondeg, Defined, eval, Interp.complex, hkkn, hkkp, hkkq] at h
  rcases hkkr : intValue? (env "r") with _ | kr
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r31Nondeg, Defined, eval, Interp.complex, hkkn, hkkp, hkkq, hkkr] at h
  have hbc' : env "b" * env "c" + -(env "a" * env "d") ≠ 0 := by rwa [← sub_eq_add_neg]
  have epp1 : intValue? (env "p" + 1) = some (kp + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkp]; push_cast; ring)
  have eqp1 : intValue? (env "q" + 1) = some (kq + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkq]; push_cast; ring)
  have ho0 : kp + 1 < 0 → kp < 0 := by omega
  have ho1 : kq + 1 < 0 → kq < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1135r31Nondeg.body →
      (kn < 0 → w ≠ 0) ∧ (kp < 0 → env "a" + env "b" * w ^ kn ≠ 0) ∧
          (kq < 0 → env "c" + env "d" * w ^ kn ≠ 0) ∧ (kr < 0 → env "e" + env "f" * w ^ kn ≠ 0) :=
          by
    intro w h
    simp [rubi1135r31Nondeg, Defined, eval, Interp.complex, hkkn, hkkp, hkkq, hkkr] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1135r31Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, hkkn, hkkp, hkkq, hkkr, epp1, eqp1] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi1135r31Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hbc']
  · simp only [rubi1135r31Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" * t ^ kn) ^ kp *
        (env "c" + env "d" * t ^ kn) ^ (kq + 1) * (env "e" + env "f" * t ^ kn) ^ kr) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkkn, hkkp, hkkr, eqp1, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "a" + env "b" * t ^ kn) ^ (kp + 1) *
        (env "c" + env "d" * t ^ kn) ^ kq * (env "e" + env "f" * t ^ kn) ^ kr) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkkn, hkkq, hkkr, epp1, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1135r31Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1135r31Nondeg.result) = fun w => env "b" *
            (env "b" * env "c" - env "a" * env "d")⁻¹ * Φ "I1" w +
            -(env "d" * (env "b" * env "c" - env "a" * env "d")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi1135r31Nondeg, eval, recEnv, Interp.complex, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1135r31Nondeg.body =
        (env "a" + env "b" * t ^ kn) ^ kp * (env "c" + env "d" * t ^ kn) ^ kq *
        (env "e" + env "f" * t ^ kn) ^ kr := by
      simp [rubi1135r31Nondeg, eval, Interp.complex, hkkn, hkkp, hkkq, hkkr]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨-, hA0, hC0, -⟩ := hD t hF.self_of_nhds
    have eX0 : (env "c" + env "d" * t ^ kn) ^ (kq + 1) = (env "c" + env "d" * t ^ kn) ^ (kq) *
        (env "c" + env "d" * t ^ kn) ^ 1 := by
      have := zsplit (env "c" + env "d" *
          t ^ kn) (kq) 1 ((by by_cases hk : kq < 0; exacts [Or.inl (hC0 hk), Or.inr (by omega)]))
      rwa [show kq + ((1 : ℕ) : ℤ) = kq + 1 by push_cast; ring] at this
    have eX1 : (env "a" + env "b" * t ^ kn) ^ (kp + 1) = (env "a" + env "b" * t ^ kn) ^ (kp) *
        (env "a" + env "b" * t ^ kn) ^ 1 := by
      have := zsplit (env "a" + env "b" *
          t ^ kn) (kp) 1 ((by by_cases hk : kp < 0; exacts [Or.inl (hA0 hk), Or.inr (by omega)]))
      rwa [show kp + ((1 : ℕ) : ℤ) = kp + 1 by push_cast; ring] at this
    rw [eX0, eX1]
    rw [pow_one, pow_one]
    generalize (env "a" + env "b" * t ^ kn) ^ kp = G0
    generalize (env "c" + env "d" * t ^ kn) ^ kq = G1
    generalize (env "e" + env "f" * t ^ kn) ^ kr = G2
    generalize t ^ kn = G3
    field_simp
    ring

end OSR.IntegrationRec265
