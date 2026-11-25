import OSR.IntegrationNum1
import OSR.IntegrationRec131

/-! # Strengthened variants without residual integrals: trigonometric polynomials and
inverse-function powers

Proofs of strengthened variants of `OSR.IntegrationNum1` with a closed result (shape
`antideriv`). The inverse tangent rules are proved over ℝ only: Mathlib has no derivative
of `Complex.arctan` at this revision. The inverse hyperbolic tangent and cosecant have no
complex interpretation, so those rules hold vacuously over ℂ. -/

namespace OSR.IntegrationRec211

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem hasDerivAt_lin {𝕜 : Type} [NontriviallyNormedField 𝕜] (a b t : 𝕜) :
    HasDerivAt (fun w => a + b * w) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

private theorem zpow_succ_of {𝕜 : Type} [Field 𝕜] (A : 𝕜) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) :
    A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv3R : intValue? (3 : ℝ) = some 3 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv3C : intValue? (3 : ℂ) = some 3 := (intValue?_eq _ _).2 (by norm_num)

/-! ## RUBI 4.3.2.1 #3: `∫ (a + b tan u)(c + d tan u) dx` with `b c + a d = 0` -/

theorem rubi4321r3Nondeg_real : rubi4321r3Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi4321r3Nondeg.conditions rubi4321r3Nondeg.body
    rubi4321r3Nondeg.result
  intro env hc t hF
  have hf : env "f" ≠ 0 := by
    have h := hc (.ne (.var "f") (.int 0)) (by simp [rubi4321r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" * env "c" + env "a" * env "d" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a")
      (.var "d"))) (.int 0)) (by simp [rubi4321r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4321r3Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simpa [rubi4321r3Nondeg, Defined, eval, Interp.real] using h
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    simp [rubi4321r3Nondeg, Defined, eval, Interp.real, ivm1R, hf, hD w hw]
  · have hC := hD t hF.self_of_nhds
    have hfun : (fun w => eval Interp.real (Function.update env "x" w) rubi4321r3Nondeg.result) =
        fun w => (env "a" * env "c" - env "b" * env "d") * w +
          env "b" * env "d" * Real.tan (env "e" + env "f" * w) * (env "f")⁻¹ := by
      funext w; simp [rubi4321r3Nondeg, eval, Interp.real, ivm1R]; ring_nf; simp
    have hE : eval Interp.real (Function.update env "x" t) rubi4321r3Nondeg.body =
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) *
          (env "c" + env "d" * Real.tan (env "e" + env "f" * t)) := by
      simp [rubi4321r3Nondeg, eval, Interp.real]
    rw [hfun, hE]
    refine (((hasDerivAt_id t).const_mul _).add ((((Real.hasDerivAt_tan hC).comp t
      (hasDerivAt_lin _ _ t)).const_mul (env "b" * env "d")).mul_const _)).congr_deriv ?_
    have hSC := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rw [Real.tan_eq_sin_div_cos]
    generalize Real.sin (env "e" + env "f" * t) = S at hSC ⊢
    generalize Real.cos (env "e" + env "f" * t) = C at hSC hC ⊢
    field_simp
    linear_combination (-(env "b" * env "d")) * hSC - S * C * hrel

theorem rubi4321r3Nondeg_complex : rubi4321r3Nondeg.Holds .complex := by
  show AntiderivHoldsUnder Interp.complex "x" rubi4321r3Nondeg.conditions rubi4321r3Nondeg.body
    rubi4321r3Nondeg.result
  intro env hc t hF
  have hf : env "f" ≠ 0 := by
    have h := hc (.ne (.var "f") (.int 0)) (by simp [rubi4321r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" * env "c" + env "a" * env "d" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a")
      (.var "d"))) (.int 0)) (by simp [rubi4321r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4321r3Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 := by
    intro w h
    simpa [rubi4321r3Nondeg, Defined, eval, Interp.complex] using h
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    simp [rubi4321r3Nondeg, Defined, eval, Interp.complex, ivm1C, hf, hD w hw]
  · have hC := hD t hF.self_of_nhds
    have hfun : (fun w => eval Interp.complex (Function.update env "x" w)
        rubi4321r3Nondeg.result) =
        fun w => (env "a" * env "c" - env "b" * env "d") * w +
          env "b" * env "d" * Complex.tan (env "e" + env "f" * w) * (env "f")⁻¹ := by
      funext w; simp [rubi4321r3Nondeg, eval, Interp.complex, ivm1C]; ring_nf; simp
    have hE : eval Interp.complex (Function.update env "x" t) rubi4321r3Nondeg.body =
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) *
          (env "c" + env "d" * Complex.tan (env "e" + env "f" * t)) := by
      simp [rubi4321r3Nondeg, eval, Interp.complex]
    rw [hfun, hE]
    refine (((hasDerivAt_id t).const_mul _).add ((((Complex.hasDerivAt_tan hC).comp t
      (hasDerivAt_lin _ _ t)).const_mul (env "b" * env "d")).mul_const _)).congr_deriv ?_
    have hSC := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rw [Complex.tan_eq_sin_div_cos]
    generalize Complex.sin (env "e" + env "f" * t) = S at hSC ⊢
    generalize Complex.cos (env "e" + env "f" * t) = C at hSC hC ⊢
    field_simp
    linear_combination (-(env "b" * env "d")) * hSC - S * C * hrel

/-! ## RUBI 4.1.1.1 #11: `∫ (a + b sin(c + d x))^2 dx` -/

theorem rubi4111r11Nondeg_real : rubi4111r11Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi4111r11Nondeg.conditions rubi4111r11Nondeg.body
    rubi4111r11Nondeg.result
  intro env hc t _
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4111r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  refine ⟨?_, ?_⟩
  · filter_upwards with w
    simp [rubi4111r11Nondeg, Defined, eval, Interp.real, ivm1R, iv2R, hd]
  · have hfun : (fun w => eval Interp.real (Function.update env "x" w) rubi4111r11Nondeg.result) =
        fun w => (2 * env "a" ^ 2 + env "b" ^ 2) * w * 2⁻¹ +
          (-2 * env "a" * env "b") * Real.cos (env "c" + env "d" * w) * (env "d")⁻¹ +
          (-env "b" ^ 2) * Real.cos (env "c" + env "d" * w) * Real.sin (env "c" + env "d" * w) *
            (2 * env "d")⁻¹ := by
      funext w; simp [rubi4111r11Nondeg, eval, Interp.real, ivm1R, iv2R]
    have hE : eval Interp.real (Function.update env "x" t) rubi4111r11Nondeg.body =
        (env "a" + env "b" * Real.sin (env "c" + env "d" * t)) ^ 2 := by
      simp [rubi4111r11Nondeg, eval, Interp.real, iv2R]
    rw [hfun, hE]
    have hl := hasDerivAt_lin (env "c") (env "d") t
    refine ((((hasDerivAt_id t).const_mul _).mul_const _).add
      ((((Real.hasDerivAt_cos _).comp t hl).const_mul _).mul_const _) |>.add
      (((((Real.hasDerivAt_cos _).comp t hl).const_mul _).mul
        ((Real.hasDerivAt_sin _).comp t hl)).mul_const _)).congr_deriv ?_
    have hSC := Real.sin_sq_add_cos_sq (env "c" + env "d" * t)
    simp only [Function.comp_apply]
    generalize Real.sin (env "c" + env "d" * t) = S at hSC ⊢
    generalize Real.cos (env "c" + env "d" * t) = C at hSC ⊢
    field_simp
    linear_combination (-(env "b" ^ 2)) * hSC

theorem rubi4111r11Nondeg_complex : rubi4111r11Nondeg.Holds .complex := by
  show AntiderivHoldsUnder Interp.complex "x" rubi4111r11Nondeg.conditions rubi4111r11Nondeg.body
    rubi4111r11Nondeg.result
  intro env hc t _
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4111r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  refine ⟨?_, ?_⟩
  · filter_upwards with w
    simp [rubi4111r11Nondeg, Defined, eval, Interp.complex, ivm1C, iv2C, hd]
  · have hfun : (fun w => eval Interp.complex (Function.update env "x" w)
        rubi4111r11Nondeg.result) =
        fun w => (2 * env "a" ^ 2 + env "b" ^ 2) * w * 2⁻¹ +
          (-2 * env "a" * env "b") * Complex.cos (env "c" + env "d" * w) * (env "d")⁻¹ +
          (-env "b" ^ 2) * Complex.cos (env "c" + env "d" * w) *
            Complex.sin (env "c" + env "d" * w) * (2 * env "d")⁻¹ := by
      funext w; simp [rubi4111r11Nondeg, eval, Interp.complex, ivm1C, iv2C]
    have hE : eval Interp.complex (Function.update env "x" t) rubi4111r11Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "c" + env "d" * t)) ^ 2 := by
      simp [rubi4111r11Nondeg, eval, Interp.complex, iv2C]
    rw [hfun, hE]
    have hl := hasDerivAt_lin (env "c") (env "d") t
    refine ((((hasDerivAt_id t).const_mul _).mul_const _).add
      ((((Complex.hasDerivAt_cos _).comp t hl).const_mul _).mul_const _) |>.add
      (((((Complex.hasDerivAt_cos _).comp t hl).const_mul _).mul
        ((Complex.hasDerivAt_sin _).comp t hl)).mul_const _)).congr_deriv ?_
    have hSC := Complex.sin_sq_add_cos_sq (env "c" + env "d" * t)
    simp only [Function.comp_apply]
    generalize Complex.sin (env "c" + env "d" * t) = S at hSC ⊢
    generalize Complex.cos (env "c" + env "d" * t) = C at hSC ⊢
    field_simp
    linear_combination (-(env "b" ^ 2)) * hSC

/-! ## RUBI 4.1.2.1 #1: `∫ (a + b sin u)(c + d sin u) dx` -/

theorem rubi4121r1Nondeg_real : rubi4121r1Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi4121r1Nondeg.conditions rubi4121r1Nondeg.body
    rubi4121r1Nondeg.result
  intro env hc t _
  have hf : env "f" ≠ 0 := by
    have h := hc (.ne (.var "f") (.int 0)) (by simp [rubi4121r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  refine ⟨?_, ?_⟩
  · filter_upwards with w
    simp [rubi4121r1Nondeg, Defined, eval, Interp.real, ivm1R, hf]
  · have hfun : (fun w => eval Interp.real (Function.update env "x" w) rubi4121r1Nondeg.result) =
        fun w => (2 * env "a" * env "c" + env "b" * env "d") * w * 2⁻¹ +
          (-(env "b" * env "c" + env "a" * env "d")) * Real.cos (env "e" + env "f" * w) *
            (env "f")⁻¹ +
          (-(env "b" * env "d")) * Real.cos (env "e" + env "f" * w) *
            Real.sin (env "e" + env "f" * w) * (2 * env "f")⁻¹ := by
      funext w; simp [rubi4121r1Nondeg, eval, Interp.real, ivm1R]
    have hE : eval Interp.real (Function.update env "x" t) rubi4121r1Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) *
          (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) := by
      simp [rubi4121r1Nondeg, eval, Interp.real]
    rw [hfun, hE]
    have hl := hasDerivAt_lin (env "e") (env "f") t
    refine ((((hasDerivAt_id t).const_mul _).mul_const _).add
      ((((Real.hasDerivAt_cos _).comp t hl).const_mul _).mul_const _) |>.add
      (((((Real.hasDerivAt_cos _).comp t hl).const_mul _).mul
        ((Real.hasDerivAt_sin _).comp t hl)).mul_const _)).congr_deriv ?_
    have hSC := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    simp only [Function.comp_apply]
    generalize Real.sin (env "e" + env "f" * t) = S at hSC ⊢
    generalize Real.cos (env "e" + env "f" * t) = C at hSC ⊢
    field_simp
    linear_combination (-(env "b" * env "d")) * hSC

theorem rubi4121r1Nondeg_complex : rubi4121r1Nondeg.Holds .complex := by
  show AntiderivHoldsUnder Interp.complex "x" rubi4121r1Nondeg.conditions rubi4121r1Nondeg.body
    rubi4121r1Nondeg.result
  intro env hc t _
  have hf : env "f" ≠ 0 := by
    have h := hc (.ne (.var "f") (.int 0)) (by simp [rubi4121r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  refine ⟨?_, ?_⟩
  · filter_upwards with w
    simp [rubi4121r1Nondeg, Defined, eval, Interp.complex, ivm1C, hf]
  · have hfun : (fun w => eval Interp.complex (Function.update env "x" w)
        rubi4121r1Nondeg.result) =
        fun w => (2 * env "a" * env "c" + env "b" * env "d") * w * 2⁻¹ +
          (-(env "b" * env "c" + env "a" * env "d")) * Complex.cos (env "e" + env "f" * w) *
            (env "f")⁻¹ +
          (-(env "b" * env "d")) * Complex.cos (env "e" + env "f" * w) *
            Complex.sin (env "e" + env "f" * w) * (2 * env "f")⁻¹ := by
      funext w; simp [rubi4121r1Nondeg, eval, Interp.complex, ivm1C]
    have hE : eval Interp.complex (Function.update env "x" t) rubi4121r1Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) *
          (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) := by
      simp [rubi4121r1Nondeg, eval, Interp.complex]
    rw [hfun, hE]
    have hl := hasDerivAt_lin (env "e") (env "f") t
    refine ((((hasDerivAt_id t).const_mul _).mul_const _).add
      ((((Complex.hasDerivAt_cos _).comp t hl).const_mul _).mul_const _) |>.add
      (((((Complex.hasDerivAt_cos _).comp t hl).const_mul _).mul
        ((Complex.hasDerivAt_sin _).comp t hl)).mul_const _)).congr_deriv ?_
    have hSC := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    simp only [Function.comp_apply]
    generalize Complex.sin (env "e" + env "f" * t) = S at hSC ⊢
    generalize Complex.cos (env "e" + env "f" * t) = C at hSC ⊢
    field_simp
    linear_combination (-(env "b" * env "d")) * hSC

/-! ## RUBI 4.1.7 #1: `∫ (a + b sin^2 u)(A + B sin^2 u) dx` -/

theorem rubi417r1Nondeg_real : rubi417r1Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi417r1Nondeg.conditions rubi417r1Nondeg.body
    rubi417r1Nondeg.result
  intro env hc t _
  have hf : env "f" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 8) (.var "f")) (.int 0)) (by simp [rubi417r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have iv8 : intValue? (8 : ℝ) = some 8 := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some 4 := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨?_, ?_⟩
  · filter_upwards with w
    simp [rubi417r1Nondeg, Defined, eval, Interp.real, ivm1R, iv3R, hf]
  · have hfun : (fun w => eval Interp.real (Function.update env "x" w) rubi417r1Nondeg.result) =
        fun w => (4 * env "A" * (2 * env "a" + env "b") +
            env "B" * (4 * env "a" + 3 * env "b")) * w * 8⁻¹ +
          (-(4 * env "A" * env "b" + env "B" * (4 * env "a" + 3 * env "b"))) *
            Real.cos (env "e" + env "f" * w) * Real.sin (env "e" + env "f" * w) *
            (8 * env "f")⁻¹ +
          (-(env "b" * env "B")) * Real.cos (env "e" + env "f" * w) *
            Real.sin (env "e" + env "f" * w) ^ 3 * (4 * env "f")⁻¹ := by
      funext w; simp [rubi417r1Nondeg, eval, Interp.real, ivm1R, iv3R]
    have hE : eval Interp.real (Function.update env "x" t) rubi417r1Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t) ^ 2) *
          (env "A" + env "B" * Real.sin (env "e" + env "f" * t) ^ 2) := by
      simp [rubi417r1Nondeg, eval, Interp.real, iv2R]
    rw [hfun, hE]
    have hl := hasDerivAt_lin (env "e") (env "f") t
    have hs := (Real.hasDerivAt_sin _).comp t hl
    have hc' := (Real.hasDerivAt_cos _).comp t hl
    refine ((((hasDerivAt_id t).const_mul _).mul_const _).add
      (((hc'.const_mul _).mul hs).mul_const _) |>.add
      (((hc'.const_mul _).mul (hs.pow 3)).mul_const _)).congr_deriv ?_
    have hSC := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    simp only [Pi.pow_apply, Function.comp_apply]
    generalize Real.sin (env "e" + env "f" * t) = S at hSC ⊢
    generalize Real.cos (env "e" + env "f" * t) = C at hSC ⊢
    field_simp
    push_cast
    linear_combination (-4 * (4 * env "A" * env "b" + 6 * env "B" * S ^ 2 * env "b" +
      4 * env "B" * env "a" + 3 * env "B" * env "b")) * hSC

theorem rubi417r1Nondeg_complex : rubi417r1Nondeg.Holds .complex := by
  show AntiderivHoldsUnder Interp.complex "x" rubi417r1Nondeg.conditions rubi417r1Nondeg.body
    rubi417r1Nondeg.result
  intro env hc t _
  have hf : env "f" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 8) (.var "f")) (.int 0)) (by simp [rubi417r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  refine ⟨?_, ?_⟩
  · filter_upwards with w
    simp [rubi417r1Nondeg, Defined, eval, Interp.complex, ivm1C, iv3C, hf]
  · have hfun : (fun w => eval Interp.complex (Function.update env "x" w)
        rubi417r1Nondeg.result) =
        fun w => (4 * env "A" * (2 * env "a" + env "b") +
            env "B" * (4 * env "a" + 3 * env "b")) * w * 8⁻¹ +
          (-(4 * env "A" * env "b" + env "B" * (4 * env "a" + 3 * env "b"))) *
            Complex.cos (env "e" + env "f" * w) * Complex.sin (env "e" + env "f" * w) *
            (8 * env "f")⁻¹ +
          (-(env "b" * env "B")) * Complex.cos (env "e" + env "f" * w) *
            Complex.sin (env "e" + env "f" * w) ^ 3 * (4 * env "f")⁻¹ := by
      funext w; simp [rubi417r1Nondeg, eval, Interp.complex, ivm1C, iv3C]
    have hE : eval Interp.complex (Function.update env "x" t) rubi417r1Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ^ 2) *
          (env "A" + env "B" * Complex.sin (env "e" + env "f" * t) ^ 2) := by
      simp [rubi417r1Nondeg, eval, Interp.complex, iv2C]
    rw [hfun, hE]
    have hl := hasDerivAt_lin (env "e") (env "f") t
    have hs := (Complex.hasDerivAt_sin _).comp t hl
    have hc' := (Complex.hasDerivAt_cos _).comp t hl
    refine ((((hasDerivAt_id t).const_mul _).mul_const _).add
      (((hc'.const_mul _).mul hs).mul_const _) |>.add
      (((hc'.const_mul _).mul (hs.pow 3)).mul_const _)).congr_deriv ?_
    have hSC := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    simp only [Pi.pow_apply, Function.comp_apply]
    generalize Complex.sin (env "e" + env "f" * t) = S at hSC ⊢
    generalize Complex.cos (env "e" + env "f" * t) = C at hSC ⊢
    field_simp
    push_cast
    linear_combination (-4 * (4 * env "A" * env "b" + 6 * env "B" * S ^ 2 * env "b" +
      4 * env "B" * env "a" + 3 * env "B" * env "b")) * hSC

/-! ## RUBI 5.3.6 #13 and #55: `∫ exp(n arctan(a x)) / (c + d x^2) dx`, `d = a^2 c` -/

theorem rubi536r13Nondeg_real : rubi536r13Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi536r13Nondeg.conditions rubi536r13Nondeg.body
    rubi536r13Nondeg.result
  intro env hc t _
  have hW : env "a" * env "c" * env "n" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "n")) (.int 0))
      (by simp [rubi536r13Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "d" = env "a" ^ 2 * env "c" := by
    have h := hc (.eq (.var "d") (.app2 .mul (.pow (.var "a") (.int 2)) (.var "c")))
      (by simp [rubi536r13Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨ha, hcz⟩, hn⟩ := hW'
  refine ⟨?_, ?_⟩
  · filter_upwards with w
    simp [rubi536r13Nondeg, Defined, eval, Interp.real, ivm1R, ha, hcz, hn]
  · have hfun : (fun w => eval Interp.real (Function.update env "x" w) rubi536r13Nondeg.result) =
        fun w => Real.exp (env "n" * Real.arctan (env "a" * w)) *
          (env "a" * env "c" * env "n")⁻¹ := by
      funext w; simp [rubi536r13Nondeg, eval, Interp.real, ivm1R]
    have hE : eval Interp.real (Function.update env "x" t) rubi536r13Nondeg.body =
        Real.exp (env "n" * Real.arctan (env "a" * t)) * (env "c" + env "d" * t ^ 2)⁻¹ := by
      simp [rubi536r13Nondeg, eval, Interp.real, ivm1R, iv2R]
    rw [hfun, hE]
    have hA := ((Real.hasDerivAt_arctan' _).comp t
      ((hasDerivAt_id' t).const_mul (env "a"))).const_mul (env "n")
    refine ((hA.exp).mul_const _).congr_deriv ?_
    have hpos : 0 < 1 + (env "a" * t) ^ 2 := by positivity
    rw [hrel]
    simp only [Function.comp_apply]
    field_simp

theorem rubi536r55Nondeg_real : rubi536r55Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi536r55Nondeg.conditions rubi536r55Nondeg.body
    rubi536r55Nondeg.result
  intro env hc t hF
  have hW : env "a" * env "c" * env "n" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "n")) (.int 0))
      (by simp [rubi536r55Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "d" = env "a" ^ 2 * env "c" := by
    have h := hc (.eq (.var "d") (.app2 .mul (.pow (.var "a") (.int 2)) (.var "c")))
      (by simp [rubi536r55Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨ha, hcz⟩, hn⟩ := hW'
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi536r55Nondeg.body →
      w ≠ 0 := by
    intro w h
    simp [rubi536r55Nondeg, Defined, eval, Interp.real, ivm1R, iv2R] at h
    tauto
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    simp [rubi536r55Nondeg, Defined, eval, Interp.real, ivm1R, ha, hcz, hn, hD w hw]
  · have ht := hD t hF.self_of_nhds
    have hfun : (fun w => eval Interp.real (Function.update env "x" w) rubi536r55Nondeg.result) =
        fun w => -Real.exp (env "n" * Real.arctan (env "a" * w)⁻¹) *
          (env "a" * env "c" * env "n")⁻¹ := by
      funext w; simp [rubi536r55Nondeg, eval, Interp.real, ivm1R]
    have hE : eval Interp.real (Function.update env "x" t) rubi536r55Nondeg.body =
        Real.exp (env "n" * Real.arctan (env "a" * t)⁻¹) * (env "c" + env "d" * t ^ 2)⁻¹ := by
      simp [rubi536r55Nondeg, eval, Interp.real, ivm1R, iv2R]
    rw [hfun, hE]
    have hat : env "a" * t ≠ 0 := mul_ne_zero ha ht
    have hA := ((Real.hasDerivAt_arctan' _).comp t
      (((hasDerivAt_id' t).const_mul (env "a")).inv hat)).const_mul (env "n")
    refine ((hA.exp).neg.mul_const _).congr_deriv ?_
    rw [hrel]
    simp only [Function.comp_apply, Pi.inv_apply]
    field_simp
    ring

/-! ## RUBI 5.3.4 #15 and #16: `∫ (a + b arctan(c x))^p / (d + e x^2) dx`, `e = c^2 d` -/

theorem rubi534r15Nondeg_real : rubi534r15Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi534r15Nondeg.conditions rubi534r15Nondeg.body
    rubi534r15Nondeg.result
  intro env hc t hF
  have hW : env "b" * env "c" * env "d" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d"))
      (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi534r15Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "e" = env "c" ^ 2 * env "d" := by
    have h := hc (.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")))
      (by simp [rubi534r15Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi534r15Nondeg, Defined, eval, Interp.real, hkp] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have e1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨⟨hb, hcz⟩, hd⟩, hp1⟩ := hW'
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi534r15Nondeg.body →
      (k < 0 → env "a" + env "b" * Real.arctan (env "c" * w) ≠ 0) := by
    intro w h
    simp [rubi534r15Nondeg, Defined, eval, Interp.real, hkp, ivm1R, iv2R] at h
    exact h.1
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi534r15Nondeg, Defined, eval, Interp.real, e1, ivm1R, hb, hcz, hd, hp1]
    intro hk
    exact h (by omega)
  · have ht := hD t hF.self_of_nhds
    set U := env "a" + env "b" * Real.arctan (env "c" * t) with hU
    have hfun : (fun w => eval Interp.real (Function.update env "x" w) rubi534r15Nondeg.result) =
        fun w => (env "a" + env "b" * Real.arctan (env "c" * w)) ^ (k + 1) *
          (env "b" * env "c" * env "d" * (env "p" + 1))⁻¹ := by
      funext w; simp [rubi534r15Nondeg, eval, Interp.real, e1, ivm1R]
    have hE : eval Interp.real (Function.update env "x" t) rubi534r15Nondeg.body =
        U ^ k * (env "d" + env "e" * t ^ 2)⁻¹ := by
      simp [rubi534r15Nondeg, eval, Interp.real, hkp, ivm1R, iv2R, hU]
    rw [hfun, hE]
    have hz : U ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    have hz0 : U ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    have hM := (((Real.hasDerivAt_arctan' _).comp t
      ((hasDerivAt_id' t).const_mul (env "c"))).const_mul (env "b")).const_add (env "a")
    refine (((hasDerivAt_zpow (k + 1) U hz).comp t hM).mul_const _).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have hpos : 0 < 1 + (env "c" * t) ^ 2 := by positivity
    have hk1 : ((k + 1 : ℤ) : ℝ) = env "p" + 1 := by rw [hp]; push_cast; ring
    rw [hk1, hrel]
    generalize U ^ k = P
    field_simp

theorem rubi534r16Nondeg_real : rubi534r16Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi534r16Nondeg.conditions rubi534r16Nondeg.body
    rubi534r16Nondeg.result
  intro env hc t hF
  have hW : env "b" * env "c" * env "d" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d"))
      (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi534r16Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "e" = env "c" ^ 2 * env "d" := by
    have h := hc (.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")))
      (by simp [rubi534r16Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi534r16Nondeg, Defined, eval, Interp.real, hkp] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have e1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨⟨hb, hcz⟩, hd⟩, hp1⟩ := hW'
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi534r16Nondeg.body →
      w ≠ 0 ∧ (k < 0 → env "a" + env "b" * Real.arctan (w⁻¹ * (env "c")⁻¹) ≠ 0) := by
    intro w h
    simp [rubi534r16Nondeg, Defined, eval, Interp.real, hkp, ivm1R, iv2R] at h
    tauto
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi534r16Nondeg, Defined, eval, Interp.real, e1, ivm1R, hb, hcz, hd, hp1, h.1]
    intro hk
    exact h.2 (by omega)
  · have ht := hD t hF.self_of_nhds
    set U := env "a" + env "b" * Real.arctan (env "c" * t)⁻¹ with hU
    have hfun : (fun w => eval Interp.real (Function.update env "x" w) rubi534r16Nondeg.result) =
        fun w => -(env "a" + env "b" * Real.arctan (env "c" * w)⁻¹) ^ (k + 1) *
          (env "b" * env "c" * env "d" * (env "p" + 1))⁻¹ := by
      funext w; simp [rubi534r16Nondeg, eval, Interp.real, e1, ivm1R]
    have hE : eval Interp.real (Function.update env "x" t) rubi534r16Nondeg.body =
        U ^ k * (env "d" + env "e" * t ^ 2)⁻¹ := by
      simp [rubi534r16Nondeg, eval, Interp.real, hkp, ivm1R, iv2R, hU]
    rw [hfun, hE]
    have hz : U ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (by rw [hU, mul_inv_rev]; exact ht.2 h)
      · exact Or.inr (by omega)
    have hct : env "c" * t ≠ 0 := mul_ne_zero hcz ht.1
    have hM := (((Real.hasDerivAt_arctan' _).comp t
      (((hasDerivAt_id' t).const_mul (env "c")).inv hct)).const_mul (env "b")).const_add (env "a")
    refine (((hasDerivAt_zpow (k + 1) U hz).comp t hM).neg.mul_const _).congr_deriv ?_
    simp only [Pi.inv_apply, add_sub_cancel_right]
    have hk1 : ((k + 1 : ℤ) : ℝ) = env "p" + 1 := by rw [hp]; push_cast; ring
    rw [hk1, hrel]
    generalize U ^ k = P
    have ht0 := ht.1
    field_simp
    ring

end OSR.IntegrationRec211
