import OSR.IntegrationRec131
import OSR.IntegrationRec134

/-! # Strengthened inverse hyperbolic tangent rules: `artanh(c + d tanh)` and `artanh(c + d coth)`

Proofs over ℝ of RUBI 7.3.7 #37, #38, #39 and #40 (and their 7.3.4 (mixed) twins), integrating
`(e + f x)^m artanh(c + d tanh(a + b x))`, `(e + f x)^m artanh(c + d coth(a + b x))` and their
reciprocal-argument forms by parts for an integer `m > 0` when `(c - d)^2 ≠ 1`. With
`E = exp(2 a + 2 b x)`, the derivative of the inverse hyperbolic tangent splits into the partial
fractions `E / (1 - c + d + (1 - c - d) E)` and `E / (1 + c - d + (1 + c + d) E)` (respectively
their `coth` analogues), whose denominators are nonzero on the domain because
`1 - (c + d tanh u)^2` is their product over `(E + 1)^2`. The complex statements are vacuous
(no complex interpretation of `transc1#arctanh`) and stay unproved. -/

namespace OSR.IntegrationRec237

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem hasDerivAt_lin (a b t : ℝ) : HasDerivAt (fun w => a + b * w) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

private theorem exp_two_lin (a b t : ℝ) :
    Real.exp (2 * a + 2 * b * t) = Real.exp (a + b * t) ^ 2 := by
  rw [show 2 * a + 2 * b * t = ((2 : ℕ) : ℝ) * (a + b * t) by push_cast; ring, Real.exp_nat_mul]

private theorem tanh_exp (u : ℝ) :
    Real.tanh u = (Real.exp u ^ 2 - 1) / (Real.exp u ^ 2 + 1) := by
  have hy := (Real.exp_pos u).ne'
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  field_simp

private theorem cosh_exp (u : ℝ) : Real.cosh u = (Real.exp u ^ 2 + 1) / (2 * Real.exp u) := by
  have hy := (Real.exp_pos u).ne'
  rw [Real.cosh_eq, Real.exp_neg]
  field_simp

private theorem sinh_exp (u : ℝ) : Real.sinh u = (Real.exp u ^ 2 - 1) / (2 * Real.exp u) := by
  have hy := (Real.exp_pos u).ne'
  rw [Real.sinh_eq, Real.exp_neg]
  field_simp

/-! ### The `tanh` partial fractions -/

private theorem one_sub_sq_tanh_factor (c d y : ℝ) (hy : y ≠ 0) :
    1 - (c + d * ((y ^ 2 - 1) / (y ^ 2 + 1))) ^ 2 =
      (1 - c + d + (1 - c - d) * y ^ 2) * (1 + c - d + (1 + c + d) * y ^ 2) /
        (y ^ 2 + 1) ^ 2 := by
  have h1 : y ^ 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

private theorem dens_tanh {a b c d w : ℝ}
    (h : 1 - (c + d * Real.tanh (a + b * w)) ^ 2 ≠ 0) :
    1 - c + d + (1 - c - d) * Real.exp (2 * a + 2 * b * w) ≠ 0 ∧
      1 + c - d + (1 + c + d) * Real.exp (2 * a + 2 * b * w) ≠ 0 := by
  rw [tanh_exp, one_sub_sq_tanh_factor c d _ (Real.exp_pos _).ne'] at h
  rw [exp_two_lin]
  have h' := div_ne_zero_iff.mp h
  exact mul_ne_zero_iff.mp h'.1

private theorem deriv_val_tanh {a b c d t : ℝ}
    (hY : 1 - (c + d * Real.tanh (a + b * t)) ^ 2 ≠ 0) :
    (1 - (c + d * Real.tanh (a + b * t)) ^ 2)⁻¹ * (d * (b / Real.cosh (a + b * t) ^ 2)) =
      b * (-(1 - c - d) * Real.exp (2 * a + 2 * b * t) *
          (1 - c + d + (1 - c - d) * Real.exp (2 * a + 2 * b * t))⁻¹ +
        (1 + c + d) * Real.exp (2 * a + 2 * b * t) *
          (1 + c - d + (1 + c + d) * Real.exp (2 * a + 2 * b * t))⁻¹) := by
  obtain ⟨hD1, hD2⟩ := dens_tanh hY
  rw [exp_two_lin] at hD1 hD2 ⊢
  rw [tanh_exp, one_sub_sq_tanh_factor c d _ (Real.exp_pos _).ne', cosh_exp]
  have hy := (Real.exp_pos (a + b * t)).ne'
  generalize Real.exp (a + b * t) = y at hy hD1 hD2 ⊢
  have h1 : y ^ 2 + 1 ≠ 0 := by positivity
  generalize hE1 : 1 - c + d + (1 - c - d) * y ^ 2 = D1 at hD1 ⊢
  generalize hE2 : 1 + c - d + (1 + c + d) * y ^ 2 = D2 at hD2 ⊢
  field_simp
  rw [← hE1, ← hE2]
  ring

private theorem hasDerivAt_artanh_tanh {a b c d t : ℝ}
    (h1 : -1 < c + d * Real.tanh (a + b * t)) (h2 : c + d * Real.tanh (a + b * t) < 1) :
    HasDerivAt (fun w => Real.artanh (c + d * Real.tanh (a + b * w)))
      (b * (-(1 - c - d) * Real.exp (2 * a + 2 * b * t) *
          (1 - c + d + (1 - c - d) * Real.exp (2 * a + 2 * b * t))⁻¹ +
        (1 + c + d) * Real.exp (2 * a + 2 * b * t) *
          (1 + c - d + (1 + c + d) * Real.exp (2 * a + 2 * b * t))⁻¹)) t := by
  have hL := ((OSR.IntegrationRec134.hasDerivAt_tanh_lin a b t).const_mul d).const_add c
  have hA := (OSR.IntegrationRec131.hasDerivAt_artanh h1 h2).comp t hL
  refine hA.congr_deriv ?_
  have hY : 1 - (c + d * Real.tanh (a + b * t)) ^ 2 ≠ 0 := by
    have : (c + d * Real.tanh (a + b * t)) ^ 2 < 1 := by
      rw [sq_lt_one_iff_abs_lt_one, abs_lt]; exact ⟨h1, h2⟩
    linarith
  exact deriv_val_tanh hY

/-- `(1 - (1/z)^2)⁻¹ (-z' / z^2) = (1 - z^2)⁻¹ z'`. -/
private theorem inv_deriv_val {z z' : ℝ} (h0 : z ≠ 0) (hY : 1 - z ^ 2 ≠ 0) :
    (1 - (z⁻¹) ^ 2)⁻¹ * (-z' / z ^ 2) = (1 - z ^ 2)⁻¹ * z' := by
  have hY3 : z ^ 2 - 1 ≠ 0 := by intro h; apply hY; linarith
  rw [inv_pow, show (1 - (z ^ 2)⁻¹) = (z ^ 2 - 1) / z ^ 2 by field_simp]
  rw [show (1 - z ^ 2) = -(z ^ 2 - 1) by ring]
  field_simp

private theorem one_sub_sq_ne_of_inv {z : ℝ} (h1 : -1 < z⁻¹) (h2 : z⁻¹ < 1) :
    1 - z ^ 2 ≠ 0 := by
  by_cases h0 : z = 0
  · rw [h0]; norm_num
  have hlt : (z⁻¹) ^ 2 < 1 := by rw [sq_lt_one_iff_abs_lt_one, abs_lt]; exact ⟨h1, h2⟩
  have hp : 0 < z ^ 2 := by positivity
  rw [inv_pow, inv_lt_one₀ hp] at hlt
  linarith

private theorem hasDerivAt_artanh_inv_tanh {a b c d t : ℝ}
    (h0 : c + d * Real.tanh (a + b * t) ≠ 0)
    (h1 : -1 < (c + d * Real.tanh (a + b * t))⁻¹) (h2 : (c + d * Real.tanh (a + b * t))⁻¹ < 1) :
    HasDerivAt (fun w => Real.artanh (c + d * Real.tanh (a + b * w))⁻¹)
      (b * (-(1 - c - d) * Real.exp (2 * a + 2 * b * t) *
          (1 - c + d + (1 - c - d) * Real.exp (2 * a + 2 * b * t))⁻¹ +
        (1 + c + d) * Real.exp (2 * a + 2 * b * t) *
          (1 + c - d + (1 + c + d) * Real.exp (2 * a + 2 * b * t))⁻¹)) t := by
  have hL := ((OSR.IntegrationRec134.hasDerivAt_tanh_lin a b t).const_mul d).const_add c
  have hA := (OSR.IntegrationRec131.hasDerivAt_artanh h1 h2).comp t (hL.inv h0)
  refine hA.congr_deriv ?_
  have hY := one_sub_sq_ne_of_inv h1 h2
  rw [inv_deriv_val h0 hY]
  exact deriv_val_tanh hY

/-! ### The `coth` partial fractions -/

private theorem one_sub_sq_coth_factor (c d y : ℝ) (hy : y ^ 2 - 1 ≠ 0) :
    1 - (c + d * ((y ^ 2 + 1) / (y ^ 2 - 1))) ^ 2 =
      (1 + c - d - (1 + c + d) * y ^ 2) * (1 - c + d - (1 - c - d) * y ^ 2) /
        (y ^ 2 - 1) ^ 2 := by
  field_simp
  ring

private theorem coth_exp {u : ℝ} (hs : Real.sinh u ≠ 0) :
    Fn.coth u = (Real.exp u ^ 2 + 1) / (Real.exp u ^ 2 - 1) := by
  have hy := (Real.exp_pos u).ne'
  have hs' : Real.exp u ^ 2 - 1 ≠ 0 := by
    intro h; apply hs; rw [sinh_exp, h, zero_div]
  rw [Fn.coth, tanh_exp]
  field_simp

private theorem dens_coth {a b c d w : ℝ} (hs : Real.sinh (a + b * w) ≠ 0)
    (h : 1 - (c + d * Fn.coth (a + b * w)) ^ 2 ≠ 0) :
    1 + c - d - (1 + c + d) * Real.exp (2 * a + 2 * b * w) ≠ 0 ∧
      1 - c + d - (1 - c - d) * Real.exp (2 * a + 2 * b * w) ≠ 0 := by
  have hs' : Real.exp (a + b * w) ^ 2 - 1 ≠ 0 := by
    intro h; apply hs; rw [sinh_exp, h, zero_div]
  rw [coth_exp hs, one_sub_sq_coth_factor c d _ hs'] at h
  rw [exp_two_lin]
  have h' := div_ne_zero_iff.mp h
  exact mul_ne_zero_iff.mp h'.1

private theorem deriv_val_coth {a b c d t : ℝ} (hs : Real.sinh (a + b * t) ≠ 0)
    (hY : 1 - (c + d * Fn.coth (a + b * t)) ^ 2 ≠ 0) :
    (1 - (c + d * Fn.coth (a + b * t)) ^ 2)⁻¹ * (d * (-b / Real.sinh (a + b * t) ^ 2)) =
      b * (-(1 + c + d) * Real.exp (2 * a + 2 * b * t) *
          (1 + c - d - (1 + c + d) * Real.exp (2 * a + 2 * b * t))⁻¹ +
        (1 - c - d) * Real.exp (2 * a + 2 * b * t) *
          (1 - c + d - (1 - c - d) * Real.exp (2 * a + 2 * b * t))⁻¹) := by
  obtain ⟨hD1, hD2⟩ := dens_coth hs hY
  have hs' : Real.exp (a + b * t) ^ 2 - 1 ≠ 0 := by
    intro h; apply hs; rw [sinh_exp, h, zero_div]
  rw [exp_two_lin] at hD1 hD2 ⊢
  rw [coth_exp hs, one_sub_sq_coth_factor c d _ hs', sinh_exp]
  have hy := (Real.exp_pos (a + b * t)).ne'
  generalize Real.exp (a + b * t) = y at hy hs' hD1 hD2 ⊢
  generalize hE1 : 1 + c - d - (1 + c + d) * y ^ 2 = D1 at hD1 ⊢
  generalize hE2 : 1 - c + d - (1 - c - d) * y ^ 2 = D2 at hD2 ⊢
  field_simp
  rw [← hE1, ← hE2]
  ring

private theorem hasDerivAt_artanh_coth {a b c d t : ℝ} (hs : Real.sinh (a + b * t) ≠ 0)
    (h1 : -1 < c + d * Fn.coth (a + b * t)) (h2 : c + d * Fn.coth (a + b * t) < 1) :
    HasDerivAt (fun w => Real.artanh (c + d * Fn.coth (a + b * w)))
      (b * (-(1 + c + d) * Real.exp (2 * a + 2 * b * t) *
          (1 + c - d - (1 + c + d) * Real.exp (2 * a + 2 * b * t))⁻¹ +
        (1 - c - d) * Real.exp (2 * a + 2 * b * t) *
          (1 - c + d - (1 - c - d) * Real.exp (2 * a + 2 * b * t))⁻¹)) t := by
  have hL := ((OSR.IntegrationRec134.hasDerivAt_coth_lin a b t hs).const_mul d).const_add c
  have hA := (OSR.IntegrationRec131.hasDerivAt_artanh h1 h2).comp t hL
  refine hA.congr_deriv ?_
  have hY : 1 - (c + d * Fn.coth (a + b * t)) ^ 2 ≠ 0 := by
    have : (c + d * Fn.coth (a + b * t)) ^ 2 < 1 := by
      rw [sq_lt_one_iff_abs_lt_one, abs_lt]; exact ⟨h1, h2⟩
    linarith
  exact deriv_val_coth hs hY

private theorem hasDerivAt_artanh_inv_coth {a b c d t : ℝ} (hs : Real.sinh (a + b * t) ≠ 0)
    (h0 : c + d * Fn.coth (a + b * t) ≠ 0)
    (h1 : -1 < (c + d * Fn.coth (a + b * t))⁻¹) (h2 : (c + d * Fn.coth (a + b * t))⁻¹ < 1) :
    HasDerivAt (fun w => Real.artanh (c + d * Fn.coth (a + b * w))⁻¹)
      (b * (-(1 + c + d) * Real.exp (2 * a + 2 * b * t) *
          (1 + c - d - (1 + c + d) * Real.exp (2 * a + 2 * b * t))⁻¹ +
        (1 - c - d) * Real.exp (2 * a + 2 * b * t) *
          (1 - c + d - (1 - c - d) * Real.exp (2 * a + 2 * b * t))⁻¹)) t := by
  have hL := ((OSR.IntegrationRec134.hasDerivAt_coth_lin a b t hs).const_mul d).const_add c
  have hA := (OSR.IntegrationRec131.hasDerivAt_artanh h1 h2).comp t (hL.inv h0)
  refine hA.congr_deriv ?_
  have hY := one_sub_sq_ne_of_inv h1 h2
  rw [inv_deriv_val h0 hY]
  exact deriv_val_coth hs hY

/-! ## RUBI 7.3.7 #37 (and 7.3.4 (mixed) #37) -/

theorem rubi737r37Nondeg_real : rubi737r37Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi737r37Nondeg.conditions rubi737r37Nondeg.body
    rubi737r37Nondeg.result rubi737r37Nondeg.integrals
  intro env hc t hF
  have hW : env "f" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [rubi737r37Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "m" := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi737r37Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨hf, hm1⟩ := hW'
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi737r37Nondeg, Defined, eval, Interp.real, hkm] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hj : 0 < j := by rw [hm] at hpos; exact_mod_cast hpos
  have hj0 : ¬ j < 0 := by omega
  have hj1 : ¬ j + 1 < 0 := by omega
  have ep1 : intValue? (env "m" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi737r37Nondeg.body →
      (-1 < env "c" + env "d" * Real.tanh (env "a" + env "b" * w) ∧ env "c" + env "d" *
          Real.tanh (env "a" + env "b" * w) < 1) := by
    intro w h
    simp [rubi737r37Nondeg, Defined, eval, Interp.real, hkm, hj0] at h
    tauto
  have hDen : ∀ w, Defined Interp.real (Function.update env "x" w) rubi737r37Nondeg.body →
      1 - env "c" + env "d" + (1 - env "c" - env "d") * Real.exp (2 * env "a" + 2 * env "b" *
          w) ≠ 0 ∧ 1 + env "c" - env "d" + (1 + env "c" + env "d") * Real.exp (2 * env "a" + 2 *
          env "b" * w) ≠ 0 := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := hD w hw
    have hY : 1 - (env "c" + env "d" * Real.tanh (env "a" + env "b" * w)) ^ 2 ≠ 0 := by
      have : (env "c" + env "d" * Real.tanh (env "a" + env "b" * w)) ^ 2 < 1 := by
        rw [sq_lt_one_iff_abs_lt_one, abs_lt]; exact ⟨hw1, hw2⟩
      linarith
    exact dens_tanh hY
  obtain ⟨h1, h2⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi737r37Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := (hDen w hw).1
      simp [Defined, eval, Interp.real, ep1, ivm1R, hj1, sub_eq_add_neg] at h ⊢
      exact fun h' => h (by linear_combination h')
    · filter_upwards [hF] with w hw
      have h := (hDen w hw).2
      simp [Defined, eval, Interp.real, ep1, ivm1R, hj1, sub_eq_add_neg] at h ⊢
      exact fun h' => h (by linear_combination h')
  · filter_upwards [hF] with w hw
    obtain ⟨hw1, hw2⟩ := hD w hw
    simp [rubi737r37Nondeg, Defined, eval, recEnv, Interp.real, ep1, ivm1R, hf, hm1, hj1,
      hw1, hw2]
  · simp only [rubi737r37Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ (j + 1) *
        Real.exp (2 * env "a" + 2 * env "b" * t) * (1 - env "c" + env "d" +
            (1 - env "c" - env "d") * Real.exp (2 * env "a" + 2 * env "b" * t))⁻¹) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, ep1, ivm1R, sub_eq_add_neg, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ (j + 1) *
        Real.exp (2 * env "a" + 2 * env "b" * t) * (1 + env "c" - env "d" + (1 + env "c" +
            env "d") * Real.exp (2 * env "a" + 2 * env "b" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, ep1, ivm1R, sub_eq_add_neg, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi737r37Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi737r37Nondeg.result) =
        fun w => (env "e" + env "f" * w) ^ (j + 1) * Real.artanh (env "c" + env "d" *
            Real.tanh (env "a" + env "b" * w)) * (env "f" * (env "m" + 1))⁻¹ +
          env "b" * (1 - env "c" - env "d") * (env "f" * (env "m" + 1))⁻¹ * Φ "I1" w +
          -(env "b" * (1 + env "c" + env "d")) * (env "f" * (env "m" + 1))⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi737r37Nondeg, eval, recEnv, Interp.real, ep1, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi737r37Nondeg.body =
        (env "e" + env "f" * t) ^ j * Real.artanh (env "c" + env "d" * Real.tanh (env "a" +
            env "b" * t)) := by
      simp [rubi737r37Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    have hA := hasDerivAt_artanh_tanh h1 h2
    have hP := (hasDerivAt_zpow (j + 1) _ (Or.inr (by omega))).comp t
      (hasDerivAt_lin (env "e") (env "f") t)
    refine ((((hP.mul hA).mul_const _).add (hΦ1'.const_mul _)).add
      (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    rw [show j + 1 - 1 = j by ring]
    have hjr : ((j + 1 : ℤ) : ℝ) = env "m" + 1 := by rw [hm]; push_cast; ring
    rw [hjr]
    obtain ⟨hD1, hD2⟩ := hDen t hF.self_of_nhds
    generalize Real.artanh (env "c" + env "d" * Real.tanh (env "a" + env "b" * t)) = A
    generalize Real.exp (2 * env "a" + 2 * env "b" * t) = E at hD1 hD2 ⊢
    generalize 1 - env "c" + env "d" + (1 - env "c" - env "d") * E = D1 at hD1 ⊢
    generalize 1 + env "c" - env "d" + (1 + env "c" + env "d") * E = D2 at hD2 ⊢
    generalize (env "e" + env "f" * t) ^ j = R
    generalize (env "e" + env "f" * t) ^ (j + 1) = R1
    field_simp
    ring

theorem rubi734mr37Nondeg_real : rubi734mr37Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734mr37Nondeg.conditions rubi734mr37Nondeg.body
    rubi734mr37Nondeg.result rubi734mr37Nondeg.integrals
  exact rubi737r37Nondeg_real

/-! ## RUBI 7.3.7 #38 (and 7.3.4 (mixed) #38) -/

theorem rubi737r38Nondeg_real : rubi737r38Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi737r38Nondeg.conditions rubi737r38Nondeg.body
    rubi737r38Nondeg.result rubi737r38Nondeg.integrals
  intro env hc t hF
  have hW : env "f" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [rubi737r38Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "m" := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi737r38Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨hf, hm1⟩ := hW'
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi737r38Nondeg, Defined, eval, Interp.real, hkm] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hj : 0 < j := by rw [hm] at hpos; exact_mod_cast hpos
  have hj0 : ¬ j < 0 := by omega
  have hj1 : ¬ j + 1 < 0 := by omega
  have ep1 : intValue? (env "m" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi737r38Nondeg.body →
      env "c" + env "d" * Real.tanh (env "a" + env "b" * w) ≠ 0 ∧
        (-1 < (env "c" + env "d" * Real.tanh (env "a" + env "b" * w))⁻¹ ∧ (env "c" + env "d" *
            Real.tanh (env "a" + env "b" * w))⁻¹ < 1) := by
    intro w h
    simp [rubi737r38Nondeg, Defined, eval, Interp.real, hkm, hj0, ivm1R] at h
    tauto
  have hDen : ∀ w, Defined Interp.real (Function.update env "x" w) rubi737r38Nondeg.body →
      1 - env "c" + env "d" + (1 - env "c" - env "d") * Real.exp (2 * env "a" + 2 * env "b" *
          w) ≠ 0 ∧ 1 + env "c" - env "d" + (1 + env "c" + env "d") * Real.exp (2 * env "a" + 2 *
          env "b" * w) ≠ 0 := by
    intro w hw
    obtain ⟨hw0, hw1, hw2⟩ := hD w hw
    have hY := one_sub_sq_ne_of_inv hw1 hw2
    exact dens_tanh hY
  obtain ⟨h0, h1, h2⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi737r38Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := (hDen w hw).1
      simp [Defined, eval, Interp.real, ep1, ivm1R, hj1, sub_eq_add_neg] at h ⊢
      exact fun h' => h (by linear_combination h')
    · filter_upwards [hF] with w hw
      have h := (hDen w hw).2
      simp [Defined, eval, Interp.real, ep1, ivm1R, hj1, sub_eq_add_neg] at h ⊢
      exact fun h' => h (by linear_combination h')
  · filter_upwards [hF] with w hw
    obtain ⟨hw0, hw1, hw2⟩ := hD w hw
    simp [rubi737r38Nondeg, Defined, eval, recEnv, Interp.real, ep1, ivm1R, hf, hm1, hj1,
      hw0, hw1, hw2]
  · simp only [rubi737r38Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ (j + 1) *
        Real.exp (2 * env "a" + 2 * env "b" * t) * (1 - env "c" + env "d" +
            (1 - env "c" - env "d") * Real.exp (2 * env "a" + 2 * env "b" * t))⁻¹) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, ep1, ivm1R, sub_eq_add_neg, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ (j + 1) *
        Real.exp (2 * env "a" + 2 * env "b" * t) * (1 + env "c" - env "d" + (1 + env "c" +
            env "d") * Real.exp (2 * env "a" + 2 * env "b" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, ep1, ivm1R, sub_eq_add_neg, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi737r38Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi737r38Nondeg.result) =
        fun w => (env "e" + env "f" * w) ^ (j + 1) * Real.artanh (env "c" + env "d" *
            Real.tanh (env "a" + env "b" * w))⁻¹ * (env "f" * (env "m" + 1))⁻¹ +
          env "b" * (1 - env "c" - env "d") * (env "f" * (env "m" + 1))⁻¹ * Φ "I1" w +
          -(env "b" * (1 + env "c" + env "d")) * (env "f" * (env "m" + 1))⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi737r38Nondeg, eval, recEnv, Interp.real, ep1, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi737r38Nondeg.body =
        (env "e" + env "f" * t) ^ j * Real.artanh (env "c" + env "d" * Real.tanh (env "a" +
            env "b" * t))⁻¹ := by
      simp [rubi737r38Nondeg, eval, Interp.real, hkm, ivm1R]
    rw [hfun, hEF]
    have hA := hasDerivAt_artanh_inv_tanh h0 h1 h2
    have hP := (hasDerivAt_zpow (j + 1) _ (Or.inr (by omega))).comp t
      (hasDerivAt_lin (env "e") (env "f") t)
    refine ((((hP.mul hA).mul_const _).add (hΦ1'.const_mul _)).add
      (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    rw [show j + 1 - 1 = j by ring]
    have hjr : ((j + 1 : ℤ) : ℝ) = env "m" + 1 := by rw [hm]; push_cast; ring
    rw [hjr]
    obtain ⟨hD1, hD2⟩ := hDen t hF.self_of_nhds
    generalize Real.artanh (env "c" + env "d" * Real.tanh (env "a" + env "b" * t))⁻¹ = A
    generalize Real.exp (2 * env "a" + 2 * env "b" * t) = E at hD1 hD2 ⊢
    generalize 1 - env "c" + env "d" + (1 - env "c" - env "d") * E = D1 at hD1 ⊢
    generalize 1 + env "c" - env "d" + (1 + env "c" + env "d") * E = D2 at hD2 ⊢
    generalize (env "e" + env "f" * t) ^ j = R
    generalize (env "e" + env "f" * t) ^ (j + 1) = R1
    field_simp
    ring

theorem rubi734mr38Nondeg_real : rubi734mr38Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734mr38Nondeg.conditions rubi734mr38Nondeg.body
    rubi734mr38Nondeg.result rubi734mr38Nondeg.integrals
  exact rubi737r38Nondeg_real

/-! ## RUBI 7.3.7 #39 (and 7.3.4 (mixed) #39) -/

theorem rubi737r39Nondeg_real : rubi737r39Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi737r39Nondeg.conditions rubi737r39Nondeg.body
    rubi737r39Nondeg.result rubi737r39Nondeg.integrals
  intro env hc t hF
  have hW : env "f" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [rubi737r39Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "m" := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi737r39Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨hf, hm1⟩ := hW'
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi737r39Nondeg, Defined, eval, Interp.real, hkm] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hj : 0 < j := by rw [hm] at hpos; exact_mod_cast hpos
  have hj0 : ¬ j < 0 := by omega
  have hj1 : ¬ j + 1 < 0 := by omega
  have ep1 : intValue? (env "m" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi737r39Nondeg.body →
      Real.sinh (env "a" + env "b" * w) ≠ 0 ∧ (-1 < env "c" + env "d" * Fn.coth (env "a" +
          env "b" * w) ∧ env "c" + env "d" * Fn.coth (env "a" + env "b" * w) < 1) := by
    intro w h
    simp [rubi737r39Nondeg, Defined, eval, Interp.real, hkm, hj0] at h
    simp only [ne_eq, Real.sinh_eq_zero]
    tauto
  have hDen : ∀ w, Defined Interp.real (Function.update env "x" w) rubi737r39Nondeg.body →
      1 + env "c" - env "d" - (1 + env "c" + env "d") * Real.exp (2 * env "a" + 2 * env "b" *
          w) ≠ 0 ∧ 1 - env "c" + env "d" - (1 - env "c" - env "d") * Real.exp (2 * env "a" + 2 *
          env "b" * w) ≠ 0 := by
    intro w hw
    obtain ⟨hsw, hw1, hw2⟩ := hD w hw
    have hY : 1 - (env "c" + env "d" * Fn.coth (env "a" + env "b" * w)) ^ 2 ≠ 0 := by
      have : (env "c" + env "d" * Fn.coth (env "a" + env "b" * w)) ^ 2 < 1 := by
        rw [sq_lt_one_iff_abs_lt_one, abs_lt]; exact ⟨hw1, hw2⟩
      linarith
    exact dens_coth hsw hY
  obtain ⟨hs, h1, h2⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi737r39Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := (hDen w hw).1
      simp [Defined, eval, Interp.real, ep1, ivm1R, hj1, sub_eq_add_neg] at h ⊢
      exact fun h' => h (by linear_combination h')
    · filter_upwards [hF] with w hw
      have h := (hDen w hw).2
      simp [Defined, eval, Interp.real, ep1, ivm1R, hj1, sub_eq_add_neg] at h ⊢
      exact fun h' => h (by linear_combination h')
  · filter_upwards [hF] with w hw
    obtain ⟨hsw, hw1, hw2⟩ := hD w hw
    simp [rubi737r39Nondeg, Defined, eval, recEnv, Interp.real, ep1, ivm1R, hf, hm1, hj1,
      Real.sinh_eq_zero.not.mp hsw, hw1, hw2]
  · simp only [rubi737r39Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ (j + 1) *
        Real.exp (2 * env "a" + 2 * env "b" * t) * (1 + env "c" - env "d" - (1 + env "c" +
            env "d") * Real.exp (2 * env "a" + 2 * env "b" * t))⁻¹) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, ep1, ivm1R, sub_eq_add_neg, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
      try ring
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ (j + 1) *
        Real.exp (2 * env "a" + 2 * env "b" * t) * (1 - env "c" +
            env "d" - (1 - env "c" - env "d") * Real.exp (2 * env "a" + 2 * env "b" *
            t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, ep1, ivm1R, sub_eq_add_neg, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
      try ring
    have hfun : (fun w => eval Interp.real (recEnv env (rubi737r39Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi737r39Nondeg.result) =
        fun w => (env "e" + env "f" * w) ^ (j + 1) * Real.artanh (env "c" + env "d" *
            Fn.coth (env "a" + env "b" * w)) * (env "f" * (env "m" + 1))⁻¹ +
          env "b" * (1 + env "c" + env "d") * (env "f" * (env "m" + 1))⁻¹ * Φ "I1" w +
          -(env "b" * (1 - env "c" - env "d")) * (env "f" * (env "m" + 1))⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi737r39Nondeg, eval, recEnv, Interp.real, ep1, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi737r39Nondeg.body =
        (env "e" + env "f" * t) ^ j * Real.artanh (env "c" + env "d" * Fn.coth (env "a" +
            env "b" * t)) := by
      simp [rubi737r39Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    have hA := hasDerivAt_artanh_coth hs h1 h2
    have hP := (hasDerivAt_zpow (j + 1) _ (Or.inr (by omega))).comp t
      (hasDerivAt_lin (env "e") (env "f") t)
    refine ((((hP.mul hA).mul_const _).add (hΦ1'.const_mul _)).add
      (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    rw [show j + 1 - 1 = j by ring]
    have hjr : ((j + 1 : ℤ) : ℝ) = env "m" + 1 := by rw [hm]; push_cast; ring
    rw [hjr]
    obtain ⟨hD1, hD2⟩ := hDen t hF.self_of_nhds
    generalize Real.artanh (env "c" + env "d" * Fn.coth (env "a" + env "b" * t)) = A
    generalize Real.exp (2 * env "a" + 2 * env "b" * t) = E at hD1 hD2 ⊢
    generalize 1 + env "c" - env "d" - (1 + env "c" + env "d") * E = D1 at hD1 ⊢
    generalize 1 - env "c" + env "d" - (1 - env "c" - env "d") * E = D2 at hD2 ⊢
    generalize (env "e" + env "f" * t) ^ j = R
    generalize (env "e" + env "f" * t) ^ (j + 1) = R1
    field_simp
    ring

theorem rubi734mr39Nondeg_real : rubi734mr39Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734mr39Nondeg.conditions rubi734mr39Nondeg.body
    rubi734mr39Nondeg.result rubi734mr39Nondeg.integrals
  exact rubi737r39Nondeg_real

/-! ## RUBI 7.3.7 #40 (and 7.3.4 (mixed) #40) -/

theorem rubi737r40Nondeg_real : rubi737r40Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi737r40Nondeg.conditions rubi737r40Nondeg.body
    rubi737r40Nondeg.result rubi737r40Nondeg.integrals
  intro env hc t hF
  have hW : env "f" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [rubi737r40Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "m" := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi737r40Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨hf, hm1⟩ := hW'
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi737r40Nondeg, Defined, eval, Interp.real, hkm] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hj : 0 < j := by rw [hm] at hpos; exact_mod_cast hpos
  have hj0 : ¬ j < 0 := by omega
  have hj1 : ¬ j + 1 < 0 := by omega
  have ep1 : intValue? (env "m" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi737r40Nondeg.body →
      Real.sinh (env "a" + env "b" * w) ≠ 0 ∧ env "c" + env "d" * Fn.coth (env "a" + env "b" *
          w) ≠ 0 ∧
        (-1 < (env "c" + env "d" * Fn.coth (env "a" + env "b" * w))⁻¹ ∧ (env "c" + env "d" *
            Fn.coth (env "a" + env "b" * w))⁻¹ < 1) := by
    intro w h
    simp [rubi737r40Nondeg, Defined, eval, Interp.real, hkm, hj0, ivm1R] at h
    simp only [ne_eq, Real.sinh_eq_zero]
    tauto
  have hDen : ∀ w, Defined Interp.real (Function.update env "x" w) rubi737r40Nondeg.body →
      1 + env "c" - env "d" - (1 + env "c" + env "d") * Real.exp (2 * env "a" + 2 * env "b" *
          w) ≠ 0 ∧ 1 - env "c" + env "d" - (1 - env "c" - env "d") * Real.exp (2 * env "a" + 2 *
          env "b" * w) ≠ 0 := by
    intro w hw
    obtain ⟨hsw, hw0, hw1, hw2⟩ := hD w hw
    have hY := one_sub_sq_ne_of_inv hw1 hw2
    exact dens_coth hsw hY
  obtain ⟨hs, h0, h1, h2⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi737r40Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := (hDen w hw).1
      simp [Defined, eval, Interp.real, ep1, ivm1R, hj1, sub_eq_add_neg] at h ⊢
      exact fun h' => h (by linear_combination h')
    · filter_upwards [hF] with w hw
      have h := (hDen w hw).2
      simp [Defined, eval, Interp.real, ep1, ivm1R, hj1, sub_eq_add_neg] at h ⊢
      exact fun h' => h (by linear_combination h')
  · filter_upwards [hF] with w hw
    obtain ⟨hsw, hw0, hw1, hw2⟩ := hD w hw
    simp [rubi737r40Nondeg, Defined, eval, recEnv, Interp.real, ep1, ivm1R, hf, hm1, hj1,
      Real.sinh_eq_zero.not.mp hsw, hw0, hw1, hw2]
  · simp only [rubi737r40Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ (j + 1) *
        Real.exp (2 * env "a" + 2 * env "b" * t) * (1 + env "c" - env "d" - (1 + env "c" +
            env "d") * Real.exp (2 * env "a" + 2 * env "b" * t))⁻¹) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, ep1, ivm1R, sub_eq_add_neg, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
      try ring
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ (j + 1) *
        Real.exp (2 * env "a" + 2 * env "b" * t) * (1 - env "c" +
            env "d" - (1 - env "c" - env "d") * Real.exp (2 * env "a" + 2 * env "b" *
            t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, ep1, ivm1R, sub_eq_add_neg, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
      try ring
    have hfun : (fun w => eval Interp.real (recEnv env (rubi737r40Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi737r40Nondeg.result) =
        fun w => (env "e" + env "f" * w) ^ (j + 1) * Real.artanh (env "c" + env "d" *
            Fn.coth (env "a" + env "b" * w))⁻¹ * (env "f" * (env "m" + 1))⁻¹ +
          env "b" * (1 + env "c" + env "d") * (env "f" * (env "m" + 1))⁻¹ * Φ "I1" w +
          -(env "b" * (1 - env "c" - env "d")) * (env "f" * (env "m" + 1))⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi737r40Nondeg, eval, recEnv, Interp.real, ep1, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi737r40Nondeg.body =
        (env "e" + env "f" * t) ^ j * Real.artanh (env "c" + env "d" * Fn.coth (env "a" +
            env "b" * t))⁻¹ := by
      simp [rubi737r40Nondeg, eval, Interp.real, hkm, ivm1R]
    rw [hfun, hEF]
    have hA := hasDerivAt_artanh_inv_coth hs h0 h1 h2
    have hP := (hasDerivAt_zpow (j + 1) _ (Or.inr (by omega))).comp t
      (hasDerivAt_lin (env "e") (env "f") t)
    refine ((((hP.mul hA).mul_const _).add (hΦ1'.const_mul _)).add
      (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    rw [show j + 1 - 1 = j by ring]
    have hjr : ((j + 1 : ℤ) : ℝ) = env "m" + 1 := by rw [hm]; push_cast; ring
    rw [hjr]
    obtain ⟨hD1, hD2⟩ := hDen t hF.self_of_nhds
    generalize Real.artanh (env "c" + env "d" * Fn.coth (env "a" + env "b" * t))⁻¹ = A
    generalize Real.exp (2 * env "a" + 2 * env "b" * t) = E at hD1 hD2 ⊢
    generalize 1 + env "c" - env "d" - (1 + env "c" + env "d") * E = D1 at hD1 ⊢
    generalize 1 - env "c" + env "d" - (1 - env "c" - env "d") * E = D2 at hD2 ⊢
    generalize (env "e" + env "f" * t) ^ j = R
    generalize (env "e" + env "f" * t) ^ (j + 1) = R1
    field_simp
    ring

theorem rubi734mr40Nondeg_real : rubi734mr40Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734mr40Nondeg.conditions rubi734mr40Nondeg.body
    rubi734mr40Nondeg.result rubi734mr40Nondeg.integrals
  exact rubi737r40Nondeg_real

end OSR.IntegrationRec237
