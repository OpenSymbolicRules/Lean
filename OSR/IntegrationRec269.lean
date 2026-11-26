import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: residual integrals with shifted powers

Proofs of RUBI 4.1.5 #37 and #38 over ℝ and ℂ: `yᵐ (a cos + b sin)ⁿ` for `y = sin, cos` splits into
three residual integrals with the powers shifted by one or two, using
`a² (sin² + cos²) = (a² + b²) sin² - 2 b sin (a cos + b sin) + (a cos + b sin)²` (and its cosine
analogue); the powers are split with `X^(j + n) = X^j X^n` (when `X ≠ 0` or `0 ≤ j`). -/

namespace OSR.IntegrationRec269

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

/-! ## rubi415r37Nondeg -/

theorem rubi415r37Nondeg_real : rubi415r37Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi415r37Nondeg.conditions rubi415r37Nondeg.body
    rubi415r37Nondeg.result rubi415r37Nondeg.integrals
  intro env hc t hF
  have hk2 : env "a" ≠ 0 := by
    have h := hc (.ne (.pow (.var "a") (.int 2)) (.int 0)) (by simp [rubi415r37Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  rcases hkkm : intValue? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi415r37Nondeg, Defined, eval, Interp.real, hkkm] at h
  rcases hkkn : intValue? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi415r37Nondeg, Defined, eval, Interp.real, hkkm, hkkn] at h
  have emp2 : intValue? (env "m" + 2) = some (km + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkm]; push_cast; ring)
  have emp1 : intValue? (env "m" + 1) = some (km + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkm]; push_cast; ring)
  have enp1 : intValue? (env "n" + 1) = some (kn + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkn]; push_cast; ring)
  have enp2 : intValue? (env "n" + 2) = some (kn + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkn]; push_cast; ring)
  have ho0 : km + 2 < 0 → km < 0 := by omega
  have ho1 : km + 1 < 0 → km < 0 := by omega
  have ho2 : kn + 1 < 0 → kn < 0 := by omega
  have ho3 : kn + 2 < 0 → kn < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi415r37Nondeg.body →
      (km < 0 → Real.sin (env "c" + env "d" * w) ≠ 0) ∧
          (kn < 0 → env "a" * Real.cos (env "c" + env "d" * w) + env "b" *
          Real.sin (env "c" + env "d" * w) ≠ 0) := by
    intro w h
    simp [rubi415r37Nondeg, Defined, eval, Interp.real, hkkm, hkkn] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi415r37Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, hkkm, hkkn, emp2, emp1, enp1, enp2] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi415r37Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hk2]
  · simp only [rubi415r37Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2, hΦ3⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((Real.sin (env "c" + env "d" * t)) ^ (km + 2) *
        (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ kn) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkkn, emp2, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((Real.sin (env "c" + env "d" * t)) ^ (km + 1) *
        (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ (kn + 1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, emp1, enp1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ3' : HasDerivAt (Φ "I3") ((Real.sin (env "c" + env "d" * t)) ^ km *
        (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ (kn + 2)) t := by
      convert hΦ3 using 1
      simp [eval, Interp.real, hkkm, enp2, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi415r37Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi415r37Nondeg.result) = fun w => (env "a" ^ 2 + env "b" ^ 2) * (env "a" ^ 2)⁻¹ *
            Φ "I1" w + -(2 * env "b" * (env "a" ^ 2)⁻¹) * Φ "I2" w + (env "a" ^ 2)⁻¹ * Φ "I3" w :=
            by
      funext w
      simp [rubi415r37Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi415r37Nondeg.body =
        (Real.sin (env "c" + env "d" * t)) ^ km *
        (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ kn := by
      simp [rubi415r37Nondeg, eval, Interp.real, hkkm, hkkn]
    rw [hfun, hEF]
    refine (((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).add (hΦ3'.const_mul _)).congr_deriv ?_
    obtain ⟨hS0, hT0⟩ := hD t hF.self_of_nhds
    have eX0 : (Real.sin (env "c" + env "d" * t)) ^ (km + 2) =
        (Real.sin (env "c" + env "d" * t)) ^ (km) * (Real.sin (env "c" + env "d" * t)) ^ 2 := by
      have := zsplit (Real.sin (env "c" + env "d" *
          t)) (km) 2 ((by by_cases hk : km < 0; exacts [Or.inl (hS0 hk), Or.inr (by omega)]))
      rwa [show km + ((2 : ℕ) : ℤ) = km + 2 by push_cast; ring] at this
    have eX1 : (Real.sin (env "c" + env "d" * t)) ^ (km + 1) =
        (Real.sin (env "c" + env "d" * t)) ^ (km) * (Real.sin (env "c" + env "d" * t)) ^ 1 := by
      have := zsplit (Real.sin (env "c" + env "d" *
          t)) (km) 1 ((by by_cases hk : km < 0; exacts [Or.inl (hS0 hk), Or.inr (by omega)]))
      rwa [show km + ((1 : ℕ) : ℤ) = km + 1 by push_cast; ring] at this
    have eX2 : (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ (kn + 1) =
        (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ (kn) *
        (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ 1 := by
      have := zsplit (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
          Real.sin (env "c" + env "d" *
          t)) (kn) 1 ((by by_cases hk : kn < 0; exacts [Or.inl (hT0 hk), Or.inr (by omega)]))
      rwa [show kn + ((1 : ℕ) : ℤ) = kn + 1 by push_cast; ring] at this
    have eX3 : (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ (kn + 2) =
        (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ (kn) *
        (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ 2 := by
      have := zsplit (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
          Real.sin (env "c" + env "d" *
          t)) (kn) 2 ((by by_cases hk : kn < 0; exacts [Or.inl (hT0 hk), Or.inr (by omega)]))
      rwa [show kn + ((2 : ℕ) : ℤ) = kn + 2 by push_cast; ring] at this
    rw [eX0, eX1, eX2, eX3]
    rw [pow_one, pow_one]
    have hP := Real.sin_sq_add_cos_sq (env "c" + env "d" * t)
    generalize (Real.sin (env "c" + env "d" * t)) ^ km = G0
    generalize (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ kn = G1
    generalize Real.sin (env "c" + env "d" * t) = S at hP ⊢
    generalize Real.cos (env "c" + env "d" * t) = C at hP ⊢
    field_simp
    linear_combination (G0 * G1 * env "a" ^ 2) * hP

theorem rubi415r37Nondeg_complex : rubi415r37Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi415r37Nondeg.conditions rubi415r37Nondeg.body
    rubi415r37Nondeg.result rubi415r37Nondeg.integrals
  intro env hc t hF
  have hk2 : env "a" ≠ 0 := by
    have h := hc (.ne (.pow (.var "a") (.int 2)) (.int 0)) (by simp [rubi415r37Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  rcases hkkm : intValue? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi415r37Nondeg, Defined, eval, Interp.complex, hkkm] at h
  rcases hkkn : intValue? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi415r37Nondeg, Defined, eval, Interp.complex, hkkm, hkkn] at h
  have emp2 : intValue? (env "m" + 2) = some (km + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkm]; push_cast; ring)
  have emp1 : intValue? (env "m" + 1) = some (km + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkm]; push_cast; ring)
  have enp1 : intValue? (env "n" + 1) = some (kn + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkn]; push_cast; ring)
  have enp2 : intValue? (env "n" + 2) = some (kn + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkn]; push_cast; ring)
  have ho0 : km + 2 < 0 → km < 0 := by omega
  have ho1 : km + 1 < 0 → km < 0 := by omega
  have ho2 : kn + 1 < 0 → kn < 0 := by omega
  have ho3 : kn + 2 < 0 → kn < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi415r37Nondeg.body →
      (km < 0 → Complex.sin (env "c" + env "d" * w) ≠ 0) ∧
          (kn < 0 → env "a" * Complex.cos (env "c" + env "d" * w) + env "b" *
          Complex.sin (env "c" + env "d" * w) ≠ 0) := by
    intro w h
    simp [rubi415r37Nondeg, Defined, eval, Interp.complex, hkkm, hkkn] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi415r37Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, hkkm, hkkn, emp2, emp1, enp1, enp2] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi415r37Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, hk2]
  · simp only [rubi415r37Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2, hΦ3⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((Complex.sin (env "c" + env "d" * t)) ^ (km + 2) *
        (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ kn) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkkn, emp2, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((Complex.sin (env "c" + env "d" * t)) ^ (km + 1) *
        (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ (kn + 1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, emp1, enp1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ3' : HasDerivAt (Φ "I3") ((Complex.sin (env "c" + env "d" * t)) ^ km *
        (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ (kn + 2)) t := by
      convert hΦ3 using 1
      simp [eval, Interp.complex, hkkm, enp2, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi415r37Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi415r37Nondeg.result) = fun w => (env "a" ^ 2 + env "b" ^ 2) * (env "a" ^ 2)⁻¹ *
            Φ "I1" w + -(2 * env "b" * (env "a" ^ 2)⁻¹) * Φ "I2" w + (env "a" ^ 2)⁻¹ * Φ "I3" w :=
            by
      funext w
      simp [rubi415r37Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi415r37Nondeg.body =
        (Complex.sin (env "c" + env "d" * t)) ^ km *
        (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ kn := by
      simp [rubi415r37Nondeg, eval, Interp.complex, hkkm, hkkn]
    rw [hfun, hEF]
    refine (((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).add (hΦ3'.const_mul _)).congr_deriv ?_
    obtain ⟨hS0, hT0⟩ := hD t hF.self_of_nhds
    have eX0 : (Complex.sin (env "c" + env "d" * t)) ^ (km + 2) =
        (Complex.sin (env "c" + env "d" * t)) ^ (km) * (Complex.sin (env "c" + env "d" * t)) ^ 2 :=
        by
      have := zsplit (Complex.sin (env "c" + env "d" *
          t)) (km) 2 ((by by_cases hk : km < 0; exacts [Or.inl (hS0 hk), Or.inr (by omega)]))
      rwa [show km + ((2 : ℕ) : ℤ) = km + 2 by push_cast; ring] at this
    have eX1 : (Complex.sin (env "c" + env "d" * t)) ^ (km + 1) =
        (Complex.sin (env "c" + env "d" * t)) ^ (km) * (Complex.sin (env "c" + env "d" * t)) ^ 1 :=
        by
      have := zsplit (Complex.sin (env "c" + env "d" *
          t)) (km) 1 ((by by_cases hk : km < 0; exacts [Or.inl (hS0 hk), Or.inr (by omega)]))
      rwa [show km + ((1 : ℕ) : ℤ) = km + 1 by push_cast; ring] at this
    have eX2 : (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ (kn + 1) =
        (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ (kn) *
        (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ 1 := by
      have := zsplit (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
          Complex.sin (env "c" + env "d" *
          t)) (kn) 1 ((by by_cases hk : kn < 0; exacts [Or.inl (hT0 hk), Or.inr (by omega)]))
      rwa [show kn + ((1 : ℕ) : ℤ) = kn + 1 by push_cast; ring] at this
    have eX3 : (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ (kn + 2) =
        (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ (kn) *
        (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ 2 := by
      have := zsplit (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
          Complex.sin (env "c" + env "d" *
          t)) (kn) 2 ((by by_cases hk : kn < 0; exacts [Or.inl (hT0 hk), Or.inr (by omega)]))
      rwa [show kn + ((2 : ℕ) : ℤ) = kn + 2 by push_cast; ring] at this
    rw [eX0, eX1, eX2, eX3]
    rw [pow_one, pow_one]
    have hP := Complex.sin_sq_add_cos_sq (env "c" + env "d" * t)
    generalize (Complex.sin (env "c" + env "d" * t)) ^ km = G0
    generalize (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ kn = G1
    generalize Complex.sin (env "c" + env "d" * t) = S at hP ⊢
    generalize Complex.cos (env "c" + env "d" * t) = C at hP ⊢
    field_simp
    linear_combination (G0 * G1 * env "a" ^ 2) * hP

/-! ## rubi415r38Nondeg -/

theorem rubi415r38Nondeg_real : rubi415r38Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi415r38Nondeg.conditions rubi415r38Nondeg.body
    rubi415r38Nondeg.result rubi415r38Nondeg.integrals
  intro env hc t hF
  have hk2 : env "b" ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi415r38Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  rcases hkkm : intValue? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi415r38Nondeg, Defined, eval, Interp.real, hkkm] at h
  rcases hkkn : intValue? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi415r38Nondeg, Defined, eval, Interp.real, hkkm, hkkn] at h
  have emp2 : intValue? (env "m" + 2) = some (km + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkm]; push_cast; ring)
  have emp1 : intValue? (env "m" + 1) = some (km + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkm]; push_cast; ring)
  have enp1 : intValue? (env "n" + 1) = some (kn + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkn]; push_cast; ring)
  have enp2 : intValue? (env "n" + 2) = some (kn + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkn]; push_cast; ring)
  have ho0 : km + 2 < 0 → km < 0 := by omega
  have ho1 : km + 1 < 0 → km < 0 := by omega
  have ho2 : kn + 1 < 0 → kn < 0 := by omega
  have ho3 : kn + 2 < 0 → kn < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi415r38Nondeg.body →
      (km < 0 → Real.cos (env "c" + env "d" * w) ≠ 0) ∧
          (kn < 0 → env "a" * Real.cos (env "c" + env "d" * w) + env "b" *
          Real.sin (env "c" + env "d" * w) ≠ 0) := by
    intro w h
    simp [rubi415r38Nondeg, Defined, eval, Interp.real, hkkm, hkkn] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi415r38Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, hkkm, hkkn, emp2, emp1, enp1, enp2] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi415r38Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hk2]
  · simp only [rubi415r38Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2, hΦ3⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((Real.cos (env "c" + env "d" * t)) ^ (km + 2) *
        (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ kn) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkkn, emp2, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((Real.cos (env "c" + env "d" * t)) ^ (km + 1) *
        (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ (kn + 1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, emp1, enp1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ3' : HasDerivAt (Φ "I3") ((Real.cos (env "c" + env "d" * t)) ^ km *
        (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ (kn + 2)) t := by
      convert hΦ3 using 1
      simp [eval, Interp.real, hkkm, enp2, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi415r38Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi415r38Nondeg.result) = fun w => (env "a" ^ 2 + env "b" ^ 2) * (env "b" ^ 2)⁻¹ *
            Φ "I1" w + -(2 * env "a" * (env "b" ^ 2)⁻¹) * Φ "I2" w + (env "b" ^ 2)⁻¹ * Φ "I3" w :=
            by
      funext w
      simp [rubi415r38Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi415r38Nondeg.body =
        (Real.cos (env "c" + env "d" * t)) ^ km *
        (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ kn := by
      simp [rubi415r38Nondeg, eval, Interp.real, hkkm, hkkn]
    rw [hfun, hEF]
    refine (((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).add (hΦ3'.const_mul _)).congr_deriv ?_
    obtain ⟨hS0, hT0⟩ := hD t hF.self_of_nhds
    have eX0 : (Real.cos (env "c" + env "d" * t)) ^ (km + 2) =
        (Real.cos (env "c" + env "d" * t)) ^ (km) * (Real.cos (env "c" + env "d" * t)) ^ 2 := by
      have := zsplit (Real.cos (env "c" + env "d" *
          t)) (km) 2 ((by by_cases hk : km < 0; exacts [Or.inl (hS0 hk), Or.inr (by omega)]))
      rwa [show km + ((2 : ℕ) : ℤ) = km + 2 by push_cast; ring] at this
    have eX1 : (Real.cos (env "c" + env "d" * t)) ^ (km + 1) =
        (Real.cos (env "c" + env "d" * t)) ^ (km) * (Real.cos (env "c" + env "d" * t)) ^ 1 := by
      have := zsplit (Real.cos (env "c" + env "d" *
          t)) (km) 1 ((by by_cases hk : km < 0; exacts [Or.inl (hS0 hk), Or.inr (by omega)]))
      rwa [show km + ((1 : ℕ) : ℤ) = km + 1 by push_cast; ring] at this
    have eX2 : (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ (kn + 1) =
        (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ (kn) *
        (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ 1 := by
      have := zsplit (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
          Real.sin (env "c" + env "d" *
          t)) (kn) 1 ((by by_cases hk : kn < 0; exacts [Or.inl (hT0 hk), Or.inr (by omega)]))
      rwa [show kn + ((1 : ℕ) : ℤ) = kn + 1 by push_cast; ring] at this
    have eX3 : (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ (kn + 2) =
        (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ (kn) *
        (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ 2 := by
      have := zsplit (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
          Real.sin (env "c" + env "d" *
          t)) (kn) 2 ((by by_cases hk : kn < 0; exacts [Or.inl (hT0 hk), Or.inr (by omega)]))
      rwa [show kn + ((2 : ℕ) : ℤ) = kn + 2 by push_cast; ring] at this
    rw [eX0, eX1, eX2, eX3]
    rw [pow_one, pow_one]
    have hP := Real.sin_sq_add_cos_sq (env "c" + env "d" * t)
    generalize (Real.cos (env "c" + env "d" * t)) ^ km = G0
    generalize (env "a" * Real.cos (env "c" + env "d" * t) + env "b" *
        Real.sin (env "c" + env "d" * t)) ^ kn = G1
    generalize Real.sin (env "c" + env "d" * t) = S at hP ⊢
    generalize Real.cos (env "c" + env "d" * t) = C at hP ⊢
    field_simp
    linear_combination (G0 * G1 * env "b" ^ 2) * hP

theorem rubi415r38Nondeg_complex : rubi415r38Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi415r38Nondeg.conditions rubi415r38Nondeg.body
    rubi415r38Nondeg.result rubi415r38Nondeg.integrals
  intro env hc t hF
  have hk2 : env "b" ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi415r38Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  rcases hkkm : intValue? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi415r38Nondeg, Defined, eval, Interp.complex, hkkm] at h
  rcases hkkn : intValue? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi415r38Nondeg, Defined, eval, Interp.complex, hkkm, hkkn] at h
  have emp2 : intValue? (env "m" + 2) = some (km + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkm]; push_cast; ring)
  have emp1 : intValue? (env "m" + 1) = some (km + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkm]; push_cast; ring)
  have enp1 : intValue? (env "n" + 1) = some (kn + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkn]; push_cast; ring)
  have enp2 : intValue? (env "n" + 2) = some (kn + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkn]; push_cast; ring)
  have ho0 : km + 2 < 0 → km < 0 := by omega
  have ho1 : km + 1 < 0 → km < 0 := by omega
  have ho2 : kn + 1 < 0 → kn < 0 := by omega
  have ho3 : kn + 2 < 0 → kn < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi415r38Nondeg.body →
      (km < 0 → Complex.cos (env "c" + env "d" * w) ≠ 0) ∧
          (kn < 0 → env "a" * Complex.cos (env "c" + env "d" * w) + env "b" *
          Complex.sin (env "c" + env "d" * w) ≠ 0) := by
    intro w h
    simp [rubi415r38Nondeg, Defined, eval, Interp.complex, hkkm, hkkn] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi415r38Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, hkkm, hkkn, emp2, emp1, enp1, enp2] at h ⊢
      tauto
  · filter_upwards with w
    simp [rubi415r38Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, hk2]
  · simp only [rubi415r38Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2, hΦ3⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((Complex.cos (env "c" + env "d" * t)) ^ (km + 2) *
        (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ kn) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkkn, emp2, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((Complex.cos (env "c" + env "d" * t)) ^ (km + 1) *
        (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ (kn + 1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, emp1, enp1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ3' : HasDerivAt (Φ "I3") ((Complex.cos (env "c" + env "d" * t)) ^ km *
        (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ (kn + 2)) t := by
      convert hΦ3 using 1
      simp [eval, Interp.complex, hkkm, enp2, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi415r38Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi415r38Nondeg.result) = fun w => (env "a" ^ 2 + env "b" ^ 2) * (env "b" ^ 2)⁻¹ *
            Φ "I1" w + -(2 * env "a" * (env "b" ^ 2)⁻¹) * Φ "I2" w + (env "b" ^ 2)⁻¹ * Φ "I3" w :=
            by
      funext w
      simp [rubi415r38Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi415r38Nondeg.body =
        (Complex.cos (env "c" + env "d" * t)) ^ km *
        (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ kn := by
      simp [rubi415r38Nondeg, eval, Interp.complex, hkkm, hkkn]
    rw [hfun, hEF]
    refine (((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).add (hΦ3'.const_mul _)).congr_deriv ?_
    obtain ⟨hS0, hT0⟩ := hD t hF.self_of_nhds
    have eX0 : (Complex.cos (env "c" + env "d" * t)) ^ (km + 2) =
        (Complex.cos (env "c" + env "d" * t)) ^ (km) * (Complex.cos (env "c" + env "d" * t)) ^ 2 :=
        by
      have := zsplit (Complex.cos (env "c" + env "d" *
          t)) (km) 2 ((by by_cases hk : km < 0; exacts [Or.inl (hS0 hk), Or.inr (by omega)]))
      rwa [show km + ((2 : ℕ) : ℤ) = km + 2 by push_cast; ring] at this
    have eX1 : (Complex.cos (env "c" + env "d" * t)) ^ (km + 1) =
        (Complex.cos (env "c" + env "d" * t)) ^ (km) * (Complex.cos (env "c" + env "d" * t)) ^ 1 :=
        by
      have := zsplit (Complex.cos (env "c" + env "d" *
          t)) (km) 1 ((by by_cases hk : km < 0; exacts [Or.inl (hS0 hk), Or.inr (by omega)]))
      rwa [show km + ((1 : ℕ) : ℤ) = km + 1 by push_cast; ring] at this
    have eX2 : (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ (kn + 1) =
        (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ (kn) *
        (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ 1 := by
      have := zsplit (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
          Complex.sin (env "c" + env "d" *
          t)) (kn) 1 ((by by_cases hk : kn < 0; exacts [Or.inl (hT0 hk), Or.inr (by omega)]))
      rwa [show kn + ((1 : ℕ) : ℤ) = kn + 1 by push_cast; ring] at this
    have eX3 : (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ (kn + 2) =
        (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ (kn) *
        (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ 2 := by
      have := zsplit (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
          Complex.sin (env "c" + env "d" *
          t)) (kn) 2 ((by by_cases hk : kn < 0; exacts [Or.inl (hT0 hk), Or.inr (by omega)]))
      rwa [show kn + ((2 : ℕ) : ℤ) = kn + 2 by push_cast; ring] at this
    rw [eX0, eX1, eX2, eX3]
    rw [pow_one, pow_one]
    have hP := Complex.sin_sq_add_cos_sq (env "c" + env "d" * t)
    generalize (Complex.cos (env "c" + env "d" * t)) ^ km = G0
    generalize (env "a" * Complex.cos (env "c" + env "d" * t) + env "b" *
        Complex.sin (env "c" + env "d" * t)) ^ kn = G1
    generalize Complex.sin (env "c" + env "d" * t) = S at hP ⊢
    generalize Complex.cos (env "c" + env "d" * t) = C at hP ⊢
    field_simp
    linear_combination (G0 * G1 * env "b" ^ 2) * hP

end OSR.IntegrationRec269
