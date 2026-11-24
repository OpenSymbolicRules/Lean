import OSR.IntegrationNum1

open OSR OSR.Calculus Filter Topology
namespace OSR.IntegrationSinSquare

section
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem htwo (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)
private theorem hneg (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem hthree (I : Interp 𝕜) : I.toInt? (3 : 𝕜) = some 3 :=
  (I.toInt?_eq _ _).2 (by simp)

variable [CharZero 𝕜]

theorem sinSquare_holds (I : Interp 𝕜)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u)
    (hc : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u)
    (hsc : ∀ u : 𝕜, I.sin u ^ 2 + I.cos u ^ 2 = 1) :
    AntiderivHoldsUnder I "x" IntegrationNum1.rubi4111r11Nondeg.conditions
      IntegrationNum1.rubi4111r11Nondeg.body IntegrationNum1.rubi4111r11Nondeg.result := by
  intro env hcond t _hF
  have hd : env "d" ≠ 0 := by
    have h := hcond (.ne (.var "d") (.int 0)) (by simp [IntegrationNum1.rubi4111r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  constructor
  · filter_upwards with w
    simp [IntegrationNum1.rubi4111r11Nondeg, Defined, eval, htwo, hneg, hd, (show (2 : 𝕜) ≠ 0 by norm_num)]
  · have hU : HasDerivAt (fun w : 𝕜 => env "c" + env "d" * w) (env "d") t := by
      simpa using (((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c"))
    have hS := (hs _).comp t hU
    have hC := (hc _).comp t hU
    have hfun : (fun w => eval I (Function.update env "x" w) IntegrationNum1.rubi4111r11Nondeg.result) =
        (fun w : 𝕜 => ((2 * env "a" ^ 2 + env "b" ^ 2) * (2 : 𝕜)⁻¹) * w +
          (-2 * env "a" * env "b" * (env "d")⁻¹) * I.cos (env "c" + env "d" * w) +
          (-env "b" ^ 2 * (2 * env "d")⁻¹) * (I.cos (env "c" + env "d" * w) * I.sin (env "c" + env "d" * w))) := by
      funext w
      simp [IntegrationNum1.rubi4111r11Nondeg, eval, htwo, hneg, Function.update, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      ring
    rw [hfun]
    have hresult := (((hasDerivAt_id' t).const_mul ((2 * env "a" ^ 2 + env "b" ^ 2) * (2 : 𝕜)⁻¹)).add
      (hC.const_mul (-2 * env "a" * env "b" * (env "d")⁻¹))).add
      ((hC.mul hS).const_mul (-env "b" ^ 2 * (2 * env "d")⁻¹))
    refine hresult.congr_deriv ?_
    simp [IntegrationNum1.rubi4111r11Nondeg, eval, htwo, Function.update]
    have ht := hsc (env "c" + env "d" * t)
    field_simp [hd]
    linear_combination -(env "b") ^ 2 * ht

omit [CharZero 𝕜] in
/-- The strengthened sine primitive holds under its original nonzero guard. -/
theorem sinLinear_holds (I : Interp 𝕜)
    (hc : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivHoldsUnder I "x" IntegrationNum1.rubi4111r6Nondeg.conditions
      IntegrationNum1.rubi4111r6Nondeg.body IntegrationNum1.rubi4111r6Nondeg.result := by
  intro env hcond t _hF
  have hd : env "d" ≠ 0 := by
    have h := hcond (.ne (.var "d") (.int 0)) (by simp [IntegrationNum1.rubi4111r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  constructor
  · filter_upwards with w
    simp [IntegrationNum1.rubi4111r6Nondeg, Defined, eval, hneg, hd]
  · have hU : HasDerivAt (fun w : 𝕜 => env "c" + env "d" * w) (env "d") t := by
      simpa using (((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c"))
    have hC := (hc _).comp t hU
    have hfun : (fun w => eval I (Function.update env "x" w) IntegrationNum1.rubi4111r6Nondeg.result) =
        (fun w : 𝕜 => (-I.cos (env "c" + env "d" * w)) * (env "d")⁻¹) := by
      funext w
      simp [IntegrationNum1.rubi4111r6Nondeg, eval, hneg, Function.update]
    rw [hfun]
    refine (hC.neg.mul_const _).congr_deriv ?_
    simp [IntegrationNum1.rubi4111r6Nondeg, eval, Function.update]
    field_simp

/-- The half-angle sine-square primitive, with its nonzero denominator guard. -/
theorem sinHalfAngle_holds (I : Interp 𝕜)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u)
    (hsc : ∀ u : 𝕜, I.sin u ^ 2 + I.cos u ^ 2 = 1)
    (hdouble : ∀ u : 𝕜, I.cos (2 * u) = 2 * I.cos u ^ 2 - 1) :
    AntiderivHoldsUnder I "x" IntegrationNum1.rubi4111r2Nondeg.conditions
      IntegrationNum1.rubi4111r2Nondeg.body IntegrationNum1.rubi4111r2Nondeg.result := by
  intro env hcond t _hF
  have hd2 : (2 : 𝕜) * env "d" ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.int 2) (.var "d")) (.int 0))
      (by simp [IntegrationNum1.rubi4111r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hd : env "d" ≠ 0 := by intro h; apply hd2; simp [h]
  have ht2 : (2 : 𝕜) ≠ 0 := by norm_num
  constructor
  · filter_upwards with w
    simp [IntegrationNum1.rubi4111r2Nondeg, Defined, eval, hneg, hd2, ht2]
  · have hU : HasDerivAt (fun w : 𝕜 => 2 * env "c" + env "d" * w) (env "d") t := by
      simpa using (((hasDerivAt_id' t).const_mul (env "d")).const_add (2 * env "c"))
    have hS := (hs _).comp t hU
    have hfun : (fun w => eval I (Function.update env "x" w) IntegrationNum1.rubi4111r2Nondeg.result) =
        (fun w : 𝕜 => (2 : 𝕜)⁻¹ * w - (2 * env "d")⁻¹ * I.sin (2 * env "c" + env "d" * w)) := by
      funext w
      simp [IntegrationNum1.rubi4111r2Nondeg, eval, hneg, Function.update, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      ring
    rw [hfun]
    refine (((hasDerivAt_id' t).const_mul (2 : 𝕜)⁻¹).sub (hS.const_mul (2 * env "d")⁻¹)).congr_deriv ?_
    simp [IntegrationNum1.rubi4111r2Nondeg, eval, htwo, hneg, Function.update]
    have ha : 2 * (env "c" + env "d" * t * (2 : 𝕜)⁻¹) = 2 * env "c" + env "d" * t := by field_simp
    rw [← ha, hdouble]
    have hp := hsc (env "c" + env "d" * t * (2 : 𝕜)⁻¹)
    generalize I.sin (env "c" + env "d" * t * (2 : 𝕜)⁻¹) = S at hp ⊢
    generalize I.cos (env "c" + env "d" * t * (2 : 𝕜)⁻¹) = C at hp ⊢
    field_simp [hd]
    linear_combination -2 * hp

/-- A reusable derivative for products of two affine expressions in sin². -/
theorem quartic_derivative (I : Interp 𝕜)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u)
    (hc : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u)
    (hsc : ∀ u : 𝕜, I.sin u ^ 2 + I.cos u ^ 2 = 1)
    (a b A B e f t : 𝕜) (hf : f ≠ 0) :
    HasDerivAt (fun x : 𝕜 =>
      ((4*A*(2*a+b)+B*(4*a+3*b)) * (8 : 𝕜)⁻¹) * x +
      (-(4*A*b+B*(4*a+3*b)) * (8*f)⁻¹) * (I.cos (e+f*x) * I.sin (e+f*x)) +
      (-b*B*(4*f)⁻¹) * (I.cos (e+f*x) * I.sin (e+f*x)^3))
      ((a+b*I.sin (e+f*t)^2)*(A+B*I.sin (e+f*t)^2)) t := by
  have hU : HasDerivAt (fun x : 𝕜 => e + f*x) f t := by
    simpa using (((hasDerivAt_id' t).const_mul f).const_add e)
  have hS := (hs _).comp t hU
  have hC := (hc _).comp t hU
  have h := (((hasDerivAt_id' t).const_mul ((4*A*(2*a+b)+B*(4*a+3*b)) * (8 : 𝕜)⁻¹)).add
      ((hC.mul hS).const_mul (-(4*A*b+B*(4*a+3*b)) * (8*f)⁻¹))).add
      ((hC.mul (hS.pow 3)).const_mul (-b*B*(4*f)⁻¹))
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Function.comp_apply, Nat.cast_ofNat]
  norm_num only [Nat.reduceSub]
  have hp := hsc (e+f*t)
  generalize I.sin (e+f*t) = S at hp ⊢
  generalize I.cos (e+f*t) = C at hp ⊢
  field_simp [hf]
  linear_combination -4 * (4*A*b + 6*B*S^2*b + 4*B*a + 3*B*b) * hp

/-- Product variant with the existing nonzero denominator condition. -/
theorem sinQuarticProduct_holds (I : Interp 𝕜)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u)
    (hc : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u)
    (hsc : ∀ u : 𝕜, I.sin u ^ 2 + I.cos u ^ 2 = 1) :
    AntiderivHoldsUnder I "x" IntegrationNum1.rubi417r1Nondeg.conditions
      IntegrationNum1.rubi417r1Nondeg.body IntegrationNum1.rubi417r1Nondeg.result := by
  intro env hcond t _hF
  have h8f : (8 : 𝕜) * env "f" ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.int 8) (.var "f")) (.int 0))
      (by simp [IntegrationNum1.rubi417r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hf : env "f" ≠ 0 := by intro h; apply h8f; simp [h]
  constructor
  · filter_upwards with w
    simp [IntegrationNum1.rubi417r1Nondeg, Defined, eval, hthree, hneg, hf]
  · have hfun : (fun w => eval I (Function.update env "x" w) IntegrationNum1.rubi417r1Nondeg.result) =
        (fun w : 𝕜 => ((4*env "A"*(2*env "a"+env "b")+env "B"*(4*env "a"+3*env "b")) * (8 : 𝕜)⁻¹) * w +
        (-(4*env "A"*env "b"+env "B"*(4*env "a"+3*env "b")) * (8*env "f")⁻¹) * (I.cos (env "e"+env "f"*w) * I.sin (env "e"+env "f"*w)) +
        (-env "b"*env "B"*(4*env "f")⁻¹) * (I.cos (env "e"+env "f"*w) * I.sin (env "e"+env "f"*w)^3)) := by
      funext w
      simp [IntegrationNum1.rubi417r1Nondeg, eval, hthree, hneg, Function.update, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      ring
    rw [hfun]
    convert quartic_derivative I hs hc hsc (env "a") (env "b") (env "A") (env "B") (env "e") (env "f") t hf using 1
    simp [IntegrationNum1.rubi417r1Nondeg, eval, htwo, Function.update]

/-- Square variant, obtained from the same quartic derivative. -/
theorem sinQuarticSquare_holds (I : Interp 𝕜)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u)
    (hc : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u)
    (hsc : ∀ u : 𝕜, I.sin u ^ 2 + I.cos u ^ 2 = 1) :
    AntiderivHoldsUnder I "x" IntegrationNum1.rubi417r10Nondeg.conditions
      IntegrationNum1.rubi417r10Nondeg.body IntegrationNum1.rubi417r10Nondeg.result := by
  intro env hcond t _hF
  have h8f : (8 : 𝕜) * env "f" ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.int 8) (.var "f")) (.int 0))
      (by simp [IntegrationNum1.rubi417r10Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hf : env "f" ≠ 0 := by intro h; apply h8f; simp [h]
  constructor
  · filter_upwards with w
    simp [IntegrationNum1.rubi417r10Nondeg, Defined, eval, htwo, hthree, hneg, hf]
  · have hfun : (fun w => eval I (Function.update env "x" w) IntegrationNum1.rubi417r10Nondeg.result) =
        (fun w : 𝕜 => ((4*env "a"*(2*env "a"+env "b")+env "b"*(4*env "a"+3*env "b")) * (8 : 𝕜)⁻¹) * w +
        (-(4*env "a"*env "b"+env "b"*(4*env "a"+3*env "b")) * (8*env "f")⁻¹) * (I.cos (env "e"+env "f"*w) * I.sin (env "e"+env "f"*w)) +
        (-env "b"*env "b"*(4*env "f")⁻¹) * (I.cos (env "e"+env "f"*w) * I.sin (env "e"+env "f"*w)^3)) := by
      funext w
      simp [IntegrationNum1.rubi417r10Nondeg, eval, htwo, hthree, hneg, Function.update, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      ring
    rw [hfun]
    convert quartic_derivative I hs hc hsc (env "a") (env "b") (env "a") (env "b") (env "e") (env "f") t hf using 1
    simp [IntegrationNum1.rubi417r10Nondeg, eval, htwo, Function.update, pow_two]

end

theorem sinSquare_real : IntegrationNum1.rubi4111r11Nondeg.Holds .real :=
  sinSquare_holds Interp.real Real.hasDerivAt_sin Real.hasDerivAt_cos Real.sin_sq_add_cos_sq

theorem sinSquare_complex : IntegrationNum1.rubi4111r11Nondeg.Holds .complex :=
  sinSquare_holds Interp.complex Complex.hasDerivAt_sin Complex.hasDerivAt_cos Complex.sin_sq_add_cos_sq

theorem sinLinear_real : IntegrationNum1.rubi4111r6Nondeg.Holds .real :=
  sinLinear_holds Interp.real Real.hasDerivAt_cos

theorem sinLinear_complex : IntegrationNum1.rubi4111r6Nondeg.Holds .complex :=
  sinLinear_holds Interp.complex Complex.hasDerivAt_cos

theorem sinHalfAngle_real : IntegrationNum1.rubi4111r2Nondeg.Holds .real :=
  sinHalfAngle_holds Interp.real Real.hasDerivAt_sin Real.sin_sq_add_cos_sq Real.cos_two_mul

theorem sinHalfAngle_complex : IntegrationNum1.rubi4111r2Nondeg.Holds .complex :=
  sinHalfAngle_holds Interp.complex Complex.hasDerivAt_sin Complex.sin_sq_add_cos_sq Complex.cos_two_mul

theorem sinQuarticProduct_real : IntegrationNum1.rubi417r1Nondeg.Holds .real :=
  sinQuarticProduct_holds Interp.real Real.hasDerivAt_sin Real.hasDerivAt_cos Real.sin_sq_add_cos_sq

theorem sinQuarticProduct_complex : IntegrationNum1.rubi417r1Nondeg.Holds .complex :=
  sinQuarticProduct_holds Interp.complex Complex.hasDerivAt_sin Complex.hasDerivAt_cos Complex.sin_sq_add_cos_sq

theorem sinQuarticSquare_real : IntegrationNum1.rubi417r10Nondeg.Holds .real :=
  sinQuarticSquare_holds Interp.real Real.hasDerivAt_sin Real.hasDerivAt_cos Real.sin_sq_add_cos_sq

theorem sinQuarticSquare_complex : IntegrationNum1.rubi417r10Nondeg.Holds .complex :=
  sinQuarticSquare_holds Interp.complex Complex.hasDerivAt_sin Complex.hasDerivAt_cos Complex.sin_sq_add_cos_sq

end OSR.IntegrationSinSquare
