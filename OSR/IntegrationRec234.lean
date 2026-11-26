import OSR.IntegrationRec131
import OSR.IntegrationRec134

/-! # Strengthened inverse hyperbolic tangent rules: `artanh(c + d tanh(a + b x))`

Proofs over ℝ of RUBI 7.3.7 #33 and #34 (and their 7.3.4 (mixed) twins), integrating
`(e + f x)^m artanh(c + d tanh(a + b x))` and `(e + f x)^m artanh(1/(c + d tanh(a + b x)))` by
parts for an integer `m > 0` when `(c - d)^2 = 1`: both arguments have the derivative
`-b / (c - d + c exp(2 a + 2 b x))` (with `cosh^2 - sinh^2 = 1` and
`exp(2 u) = (cosh u + sinh u)^2`). The complex statements are vacuous (no complex
interpretation of `transc1#arctanh`) and stay unproved. -/

namespace OSR.IntegrationRec234

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem hasDerivAt_lin (a b t : ℝ) : HasDerivAt (fun w => a + b * w) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

private theorem exp_two_lin (a b t : ℝ) :
    Real.exp (2 * a + 2 * b * t) = (Real.cosh (a + b * t) + Real.sinh (a + b * t)) ^ 2 := by
  rw [Real.cosh_add_sinh, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `1 - (c + d tanh u)^2 = -d (c - d + c exp(2 u)) / cosh^2 u` when `(c - d)^2 = 1`. -/
private theorem one_sub_sq_tanh {c d : ℝ} (hcd : (c - d) ^ 2 = 1) (u : ℝ) :
    1 - (c + d * Real.tanh u) ^ 2 =
      -d * (c - d + c * (Real.cosh u + Real.sinh u) ^ 2) / Real.cosh u ^ 2 := by
  have hC : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
  have hcs := Real.cosh_sq_sub_sinh_sq u
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  linear_combination (-Real.cosh u ^ 2) * hcd + (d ^ 2 - c * d) * hcs

private theorem den_facts {c d : ℝ} (hcd : (c - d) ^ 2 = 1) {u : ℝ}
    (h : 1 - (c + d * Real.tanh u) ^ 2 ≠ 0) :
    d ≠ 0 ∧ c - d + c * (Real.cosh u + Real.sinh u) ^ 2 ≠ 0 := by
  rw [one_sub_sq_tanh hcd] at h
  have h' := div_ne_zero_iff.mp h
  have h'' := mul_ne_zero_iff.mp h'.1
  exact ⟨neg_ne_zero.mp h''.1, h''.2⟩

private theorem deriv_eq {b c d : ℝ} (hcd : (c - d) ^ 2 = 1) {u : ℝ}
    (h : 1 - (c + d * Real.tanh u) ^ 2 ≠ 0) :
    (1 - (c + d * Real.tanh u) ^ 2)⁻¹ * (d * (b / Real.cosh u ^ 2)) =
      -b * (c - d + c * (Real.cosh u + Real.sinh u) ^ 2)⁻¹ := by
  obtain ⟨hd, hD⟩ := den_facts hcd h
  have hC : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
  rw [one_sub_sq_tanh hcd]
  field_simp

/-- The derivative of `artanh(c + d tanh(a + b x))`. -/
private theorem hasDerivAt_artanh_tanh {a b c d t : ℝ} (hcd : (c - d) ^ 2 = 1)
    (h1 : -1 < c + d * Real.tanh (a + b * t)) (h2 : c + d * Real.tanh (a + b * t) < 1) :
    HasDerivAt (fun w => Real.artanh (c + d * Real.tanh (a + b * w)))
      (-b * (c - d + c * Real.exp (2 * a + 2 * b * t))⁻¹) t := by
  have hL := ((OSR.IntegrationRec134.hasDerivAt_tanh_lin a b t).const_mul d).const_add c
  have hA := (OSR.IntegrationRec131.hasDerivAt_artanh h1 h2).comp t hL
  refine hA.congr_deriv ?_
  have hY : 1 - (c + d * Real.tanh (a + b * t)) ^ 2 ≠ 0 := by
    have : (c + d * Real.tanh (a + b * t)) ^ 2 < 1 := by
      rw [sq_lt_one_iff_abs_lt_one, abs_lt]; exact ⟨h1, h2⟩
    linarith
  rw [exp_two_lin]
  exact deriv_eq hcd hY

/-- The derivative of `artanh(1/(c + d tanh(a + b x)))`. -/
private theorem hasDerivAt_artanh_inv_tanh {a b c d t : ℝ} (hcd : (c - d) ^ 2 = 1)
    (h0 : c + d * Real.tanh (a + b * t) ≠ 0)
    (h1 : -1 < (c + d * Real.tanh (a + b * t))⁻¹) (h2 : (c + d * Real.tanh (a + b * t))⁻¹ < 1) :
    HasDerivAt (fun w => Real.artanh (c + d * Real.tanh (a + b * w))⁻¹)
      (-b * (c - d + c * Real.exp (2 * a + 2 * b * t))⁻¹) t := by
  have hL := ((OSR.IntegrationRec134.hasDerivAt_tanh_lin a b t).const_mul d).const_add c
  have hA := (OSR.IntegrationRec131.hasDerivAt_artanh h1 h2).comp t (hL.inv h0)
  refine hA.congr_deriv ?_
  have hY : 1 - (c + d * Real.tanh (a + b * t)) ^ 2 ≠ 0 := by
    have hlt : ((c + d * Real.tanh (a + b * t))⁻¹) ^ 2 < 1 := by
      rw [sq_lt_one_iff_abs_lt_one, abs_lt]; exact ⟨h1, h2⟩
    have hp : 0 < (c + d * Real.tanh (a + b * t)) ^ 2 := by positivity
    rw [inv_pow, inv_lt_one₀ hp] at hlt
    linarith
  have hY' : 1 - ((c + d * Real.tanh (a + b * t))⁻¹) ^ 2 ≠ 0 := by
    rw [inv_pow]
    intro h
    apply hY
    have hp : (c + d * Real.tanh (a + b * t)) ^ 2 ≠ 0 := pow_ne_zero 2 h0
    field_simp at h
    linarith
  rw [exp_two_lin, ← deriv_eq hcd hY]
  generalize c + d * Real.tanh (a + b * t) = y at h0 hY hY' ⊢
  have hY3 : y ^ 2 - 1 ≠ 0 := by intro h; apply hY; linarith
  rw [inv_pow, show (1 - (y ^ 2)⁻¹) = (y ^ 2 - 1) / y ^ 2 by field_simp]
  rw [show (1 - y ^ 2) = -(y ^ 2 - 1) by ring]
  field_simp

/-! ## RUBI 7.3.7 #33 (and 7.3.4 (mixed) #33) -/

theorem rubi737r33Nondeg_real : rubi737r33Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi737r33Nondeg.conditions rubi737r33Nondeg.body
    rubi737r33Nondeg.result rubi737r33Nondeg.integrals
  intro env hc t hF
  have hW : env "f" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [rubi737r33Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "m" := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi737r33Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hcd : (env "c" - env "d") ^ 2 = 1 := by
    have h := hc (.eq (.pow (.app2 .add (.var "c") (.app2 .mul (.int (-1)) (.var "d"))) (.int 2))
      (.int 1)) (by simp [rubi737r33Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    rcases h with h | h <;> rw [sub_eq_add_neg, h] <;> norm_num
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨hf, hm1⟩ := hW'
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi737r33Nondeg, Defined, eval, Interp.real, hkm] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hj : 0 < j := by rw [hm] at hpos; exact_mod_cast hpos
  have hj0 : ¬ j < 0 := by omega
  have hj1 : ¬ j + 1 < 0 := by omega
  have ep1 : intValue? (env "m" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi737r33Nondeg.body →
      -1 < env "c" + env "d" * Real.tanh (env "a" + env "b" * w) ∧
        env "c" + env "d" * Real.tanh (env "a" + env "b" * w) < 1 := by
    intro w h
    simp [rubi737r33Nondeg, Defined, eval, Interp.real, hkm, hj0] at h
    tauto
  have hDen : ∀ w, Defined Interp.real (Function.update env "x" w) rubi737r33Nondeg.body →
      env "c" + -env "d" + env "c" * Real.exp (2 * env "a" + 2 * env "b" * w) ≠ 0 := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := hD w hw
    have hY : 1 - (env "c" + env "d" * Real.tanh (env "a" + env "b" * w)) ^ 2 ≠ 0 := by
      have : (env "c" + env "d" * Real.tanh (env "a" + env "b" * w)) ^ 2 < 1 := by
        rw [sq_lt_one_iff_abs_lt_one, abs_lt]; exact ⟨hw1, hw2⟩
      linarith
    rw [exp_two_lin, ← sub_eq_add_neg]
    exact (den_facts hcd hY).2
  obtain ⟨h1, h2⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi737r33Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have := hDen w hw
    simp [Defined, eval, Interp.real, ep1, ivm1R, hj1, this]
  · filter_upwards [hF] with w hw
    obtain ⟨hw1, hw2⟩ := hD w hw
    simp [rubi737r33Nondeg, Defined, eval, recEnv, Interp.real, ep1, ivm1R, hf, hm1, hj1,
      hw1, hw2]
  · simp only [rubi737r33Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ (j + 1) *
        (env "c" - env "d" + env "c" * Real.exp (2 * env "a" + 2 * env "b" * t))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, ep1, ivm1R, sub_eq_add_neg, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi737r33Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi737r33Nondeg.result) =
        fun w => (env "e" + env "f" * w) ^ (j + 1) *
            Real.artanh (env "c" + env "d" * Real.tanh (env "a" + env "b" * w)) *
            (env "f" * (env "m" + 1))⁻¹ +
          env "b" * (env "f" * (env "m" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi737r33Nondeg, eval, recEnv, Interp.real, ep1, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi737r33Nondeg.body =
        (env "e" + env "f" * t) ^ j *
          Real.artanh (env "c" + env "d" * Real.tanh (env "a" + env "b" * t)) := by
      simp [rubi737r33Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    have hA := hasDerivAt_artanh_tanh hcd h1 h2
    have hP := (hasDerivAt_zpow (j + 1) _ (Or.inr (by omega))).comp t
      (hasDerivAt_lin (env "e") (env "f") t)
    refine (((hP.mul hA).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    rw [show j + 1 - 1 = j by ring]
    have hjr : ((j + 1 : ℤ) : ℝ) = env "m" + 1 := by rw [hm]; push_cast; ring
    rw [hjr]
    have hD0 := hDen t hF.self_of_nhds
    rw [← sub_eq_add_neg] at hD0
    generalize Real.artanh (env "c" + env "d" * Real.tanh (env "a" + env "b" * t)) = A
    generalize env "c" - env "d" + env "c" * Real.exp (2 * env "a" + 2 * env "b" * t) = Dn at hD0 ⊢
    generalize (env "e" + env "f" * t) ^ j = R
    generalize (env "e" + env "f" * t) ^ (j + 1) = R1
    field_simp
    ring

theorem rubi734mr33Nondeg_real : rubi734mr33Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734mr33Nondeg.conditions rubi734mr33Nondeg.body
    rubi734mr33Nondeg.result rubi734mr33Nondeg.integrals
  exact rubi737r33Nondeg_real

/-! ## RUBI 7.3.7 #34 (and 7.3.4 (mixed) #34) -/

theorem rubi737r34Nondeg_real : rubi737r34Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi737r34Nondeg.conditions rubi737r34Nondeg.body
    rubi737r34Nondeg.result rubi737r34Nondeg.integrals
  intro env hc t hF
  have hW : env "f" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [rubi737r34Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "m" := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi737r34Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hcd : (env "c" - env "d") ^ 2 = 1 := by
    have h := hc (.eq (.pow (.app2 .add (.var "c") (.app2 .mul (.int (-1)) (.var "d"))) (.int 2))
      (.int 1)) (by simp [rubi737r34Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    rcases h with h | h <;> rw [sub_eq_add_neg, h] <;> norm_num
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨hf, hm1⟩ := hW'
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi737r34Nondeg, Defined, eval, Interp.real, hkm] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hj : 0 < j := by rw [hm] at hpos; exact_mod_cast hpos
  have hj0 : ¬ j < 0 := by omega
  have hj1 : ¬ j + 1 < 0 := by omega
  have ep1 : intValue? (env "m" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi737r34Nondeg.body →
      env "c" + env "d" * Real.tanh (env "a" + env "b" * w) ≠ 0 ∧
        (-1 < (env "c" + env "d" * Real.tanh (env "a" + env "b" * w))⁻¹ ∧
          (env "c" + env "d" * Real.tanh (env "a" + env "b" * w))⁻¹ < 1) := by
    intro w h
    simp [rubi737r34Nondeg, Defined, eval, Interp.real, hkm, hj0, ivm1R] at h
    tauto
  have hDen : ∀ w, Defined Interp.real (Function.update env "x" w) rubi737r34Nondeg.body →
      env "c" + -env "d" + env "c" * Real.exp (2 * env "a" + 2 * env "b" * w) ≠ 0 := by
    intro w hw
    obtain ⟨hw0, hw1, hw2⟩ := hD w hw
    have hY : 1 - (env "c" + env "d" * Real.tanh (env "a" + env "b" * w)) ^ 2 ≠ 0 := by
      have hlt : ((env "c" + env "d" * Real.tanh (env "a" + env "b" * w))⁻¹) ^ 2 < 1 := by
        rw [sq_lt_one_iff_abs_lt_one, abs_lt]; exact ⟨hw1, hw2⟩
      have hp : 0 < (env "c" + env "d" * Real.tanh (env "a" + env "b" * w)) ^ 2 := by
        positivity
      rw [inv_pow, inv_lt_one₀ hp] at hlt
      linarith
    rw [exp_two_lin, ← sub_eq_add_neg]
    exact (den_facts hcd hY).2
  obtain ⟨h0, h1, h2⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi737r34Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have := hDen w hw
    simp [Defined, eval, Interp.real, ep1, ivm1R, hj1, this]
  · filter_upwards [hF] with w hw
    obtain ⟨hw0, hw1, hw2⟩ := hD w hw
    simp [rubi737r34Nondeg, Defined, eval, recEnv, Interp.real, ep1, ivm1R, hf, hm1, hj1,
      hw0, hw1, hw2]
  · simp only [rubi737r34Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ (j + 1) *
        (env "c" - env "d" + env "c" * Real.exp (2 * env "a" + 2 * env "b" * t))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, ep1, ivm1R, sub_eq_add_neg, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi737r34Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi737r34Nondeg.result) =
        fun w => (env "e" + env "f" * w) ^ (j + 1) *
            Real.artanh (env "c" + env "d" * Real.tanh (env "a" + env "b" * w))⁻¹ *
            (env "f" * (env "m" + 1))⁻¹ +
          env "b" * (env "f" * (env "m" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi737r34Nondeg, eval, recEnv, Interp.real, ep1, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi737r34Nondeg.body =
        (env "e" + env "f" * t) ^ j *
          Real.artanh (env "c" + env "d" * Real.tanh (env "a" + env "b" * t))⁻¹ := by
      simp [rubi737r34Nondeg, eval, Interp.real, hkm, ivm1R]
    rw [hfun, hEF]
    have hA := hasDerivAt_artanh_inv_tanh hcd h0 h1 h2
    have hP := (hasDerivAt_zpow (j + 1) _ (Or.inr (by omega))).comp t
      (hasDerivAt_lin (env "e") (env "f") t)
    refine (((hP.mul hA).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    rw [show j + 1 - 1 = j by ring]
    have hjr : ((j + 1 : ℤ) : ℝ) = env "m" + 1 := by rw [hm]; push_cast; ring
    rw [hjr]
    have hD0 := hDen t hF.self_of_nhds
    rw [← sub_eq_add_neg] at hD0
    generalize Real.artanh (env "c" + env "d" * Real.tanh (env "a" + env "b" * t))⁻¹ = A
    generalize env "c" - env "d" + env "c" * Real.exp (2 * env "a" + 2 * env "b" * t) = Dn at hD0 ⊢
    generalize (env "e" + env "f" * t) ^ j = R
    generalize (env "e" + env "f" * t) ^ (j + 1) = R1
    field_simp
    ring

theorem rubi734mr34Nondeg_real : rubi734mr34Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734mr34Nondeg.conditions rubi734mr34Nondeg.body
    rubi734mr34Nondeg.result rubi734mr34Nondeg.integrals
  exact rubi737r34Nondeg_real

end OSR.IntegrationRec234
