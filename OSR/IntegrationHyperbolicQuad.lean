import OSR.IntegrationNum1

open OSR OSR.Calculus Filter Topology
namespace OSR.IntegrationHyperbolicQuad

section
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem htwo (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)
private theorem hneg (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

theorem sinhQuad_holds (I : Interp 𝕜)
    (hdef : ∀ x, I.fnDefined .cosh x)
    (hder : ∀ x, HasDerivAt (I.fn .cosh) (I.fn .sinh x) x) :
    AntiderivHoldsUnder I "x" IntegrationNum1.rubi6113r7Nondeg.conditions
      IntegrationNum1.rubi6113r7Nondeg.body IntegrationNum1.rubi6113r7Nondeg.result := by
  intro env hcond t _hF
  have hEq : env "b" * env "e" + (-1 * 2 * env "c" * env "d") = 0 := by
    have h := hcond (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e"))
      (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0))
      (by simp [IntegrationNum1.rubi6113r7Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hN : (2 : 𝕜) * env "c" ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0))
      (by simp [IntegrationNum1.rubi6113r7Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hc : env "c" ≠ 0 := (mul_ne_zero_iff.mp hN).2
  have ht2 : (2 : 𝕜) ≠ 0 := (mul_ne_zero_iff.mp hN).1
  constructor
  · filter_upwards with w
    simp [IntegrationNum1.rubi6113r7Nondeg, Defined, eval, htwo, hneg, hN, hdef]
  · have hU : HasDerivAt (fun w : 𝕜 => env "a" + env "b"*w + env "c"*w^2)
        (env "b" + env "c"*(2*t)) t := by
      convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
        ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
      simp
    have hC := (hder _).comp t hU
    have hfun : (fun w => eval I (Function.update env "x" w) IntegrationNum1.rubi6113r7Nondeg.result) =
      (fun w : 𝕜 => env "e" * I.fn .cosh (env "a" + env "b"*w + env "c"*w^2) * (2*env "c")⁻¹) := by
      funext w
      simp [IntegrationNum1.rubi6113r7Nondeg, eval, htwo, hneg, Function.update]
    rw [hfun]
    refine ((hC.const_mul _).mul_const _).congr_deriv ?_
    simp [IntegrationNum1.rubi6113r7Nondeg, eval, htwo, Function.update]
    generalize I.fn .sinh (env "a" + env "b"*t + env "c"*t^2) = S
    field_simp [hc, ht2]
    linear_combination S * hEq

theorem coshQuad_holds (I : Interp 𝕜)
    (hdef : ∀ x, I.fnDefined .sinh x)
    (hder : ∀ x, HasDerivAt (I.fn .sinh) (I.fn .cosh x) x) :
    AntiderivHoldsUnder I "x" IntegrationNum1.rubi6113r8Nondeg.conditions
      IntegrationNum1.rubi6113r8Nondeg.body IntegrationNum1.rubi6113r8Nondeg.result := by
  intro env hcond t _hF
  have hEq : env "b" * env "e" + (-1 * 2 * env "c" * env "d") = 0 := by
    have h := hcond (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e"))
      (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0))
      (by simp [IntegrationNum1.rubi6113r8Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hN : (2 : 𝕜) * env "c" ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0))
      (by simp [IntegrationNum1.rubi6113r8Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hc : env "c" ≠ 0 := (mul_ne_zero_iff.mp hN).2
  have ht2 : (2 : 𝕜) ≠ 0 := (mul_ne_zero_iff.mp hN).1
  constructor
  · filter_upwards with w
    simp [IntegrationNum1.rubi6113r8Nondeg, Defined, eval, htwo, hneg, hN, hdef]
  · have hU : HasDerivAt (fun w : 𝕜 => env "a" + env "b"*w + env "c"*w^2)
        (env "b" + env "c"*(2*t)) t := by
      convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
        ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
      simp
    have hS := (hder _).comp t hU
    have hfun : (fun w => eval I (Function.update env "x" w) IntegrationNum1.rubi6113r8Nondeg.result) =
      (fun w : 𝕜 => env "e" * I.fn .sinh (env "a" + env "b"*w + env "c"*w^2) * (2*env "c")⁻¹) := by
      funext w
      simp [IntegrationNum1.rubi6113r8Nondeg, eval, htwo, hneg, Function.update]
    rw [hfun]
    refine ((hS.const_mul _).mul_const _).congr_deriv ?_
    simp [IntegrationNum1.rubi6113r8Nondeg, eval, htwo, Function.update]
    generalize I.fn .cosh (env "a" + env "b"*t + env "c"*t^2) = S
    field_simp [hc, ht2]
    linear_combination S * hEq

end

theorem sinhQuad_real : IntegrationNum1.rubi6113r7Nondeg.Holds .real :=
  sinhQuad_holds Interp.real (by simp [Interp.real]) Real.hasDerivAt_cosh

theorem sinhQuad_complex : IntegrationNum1.rubi6113r7Nondeg.Holds .complex :=
  sinhQuad_holds Interp.complex (by simp [Interp.complex]) Complex.hasDerivAt_cosh

theorem coshQuad_real : IntegrationNum1.rubi6113r8Nondeg.Holds .real :=
  coshQuad_holds Interp.real (by simp [Interp.real]) Real.hasDerivAt_sinh

theorem coshQuad_complex : IntegrationNum1.rubi6113r8Nondeg.Holds .complex :=
  coshQuad_holds Interp.complex (by simp [Interp.complex]) Complex.hasDerivAt_sinh

end OSR.IntegrationHyperbolicQuad
