import OSR.IntegrationNum1

open OSR OSR.Calculus Filter Topology
namespace OSR.IntegrationHyperbolicRec

section
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem htwo (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)
private theorem hneg (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

theorem sinhRec_holds (I : Interp 𝕜)
    (hdefBody : ∀ x, I.fnDefined .sinh x)
    (hdefRes : ∀ x, I.fnDefined .cosh x)
    (hder : ∀ x, HasDerivAt (I.fn .cosh) (I.fn .sinh x) x) :
    AntiderivRecHolds I "x" IntegrationNum1.rubi6113r9Nondeg.conditions
      IntegrationNum1.rubi6113r9Nondeg.body IntegrationNum1.rubi6113r9Nondeg.result IntegrationNum1.rubi6113r9Nondeg.integrals := by
  intro env hcond t _hF
  have hN : (2 : 𝕜) * env "c" ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0))
      (by simp [IntegrationNum1.rubi6113r9Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hc : env "c" ≠ 0 := (mul_ne_zero_iff.mp hN).2
  have ht2 : (2 : 𝕜) ≠ 0 := (mul_ne_zero_iff.mp hN).1
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi6113r9Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    filter_upwards with w
    simp [Defined, eval, htwo, hdefBody]
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi6113r9Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [IntegrationNum1.rubi6113r9Nondeg, Defined, eval, recEnv, htwo, hneg, hN, hdefRes]
    · have hU : HasDerivAt (fun w : 𝕜 => env "a" + env "b"*w + env "c"*w^2)
          (env "b" + env "c"*(2*t)) t := by
        convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
          ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
        simp
      have hT := (hder _).comp t hU
      have hfun : (fun w => eval I (recEnv env (IntegrationNum1.rubi6113r9Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi6113r9Nondeg.result) =
        (fun w : 𝕜 => env "e" * I.fn .cosh (env "a" + env "b"*w + env "c"*w^2) * (2*env "c")⁻¹ +
          (-(env "b"*env "e" - 2*env "c"*env "d") * (2*env "c")⁻¹) * Φ "I1" w) := by
        funext w
        simp [IntegrationNum1.rubi6113r9Nondeg, eval, recEnv, htwo, hneg, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        ring
      rw [hfun]
      simp [eval, htwo] at hΦ
      refine (((hT.const_mul _).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi6113r9Nondeg, eval, htwo, Function.update]
      generalize I.fn .sinh (env "a" + env "b"*t + env "c"*t^2) = S
      field_simp [hc, ht2]
      ring

theorem coshRec_holds (I : Interp 𝕜)
    (hdefBody : ∀ x, I.fnDefined .cosh x)
    (hdefRes : ∀ x, I.fnDefined .sinh x)
    (hder : ∀ x, HasDerivAt (I.fn .sinh) (I.fn .cosh x) x) :
    AntiderivRecHolds I "x" IntegrationNum1.rubi6113r10Nondeg.conditions
      IntegrationNum1.rubi6113r10Nondeg.body IntegrationNum1.rubi6113r10Nondeg.result IntegrationNum1.rubi6113r10Nondeg.integrals := by
  intro env hcond t _hF
  have hN : (2 : 𝕜) * env "c" ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0))
      (by simp [IntegrationNum1.rubi6113r10Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hc : env "c" ≠ 0 := (mul_ne_zero_iff.mp hN).2
  have ht2 : (2 : 𝕜) ≠ 0 := (mul_ne_zero_iff.mp hN).1
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi6113r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    filter_upwards with w
    simp [Defined, eval, htwo, hdefBody]
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi6113r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [IntegrationNum1.rubi6113r10Nondeg, Defined, eval, recEnv, htwo, hneg, hN, hdefRes]
    · have hU : HasDerivAt (fun w : 𝕜 => env "a" + env "b"*w + env "c"*w^2)
          (env "b" + env "c"*(2*t)) t := by
        convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
          ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
        simp
      have hT := (hder _).comp t hU
      have hfun : (fun w => eval I (recEnv env (IntegrationNum1.rubi6113r10Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi6113r10Nondeg.result) =
        (fun w : 𝕜 => env "e" * I.fn .sinh (env "a" + env "b"*w + env "c"*w^2) * (2*env "c")⁻¹ +
          (-(env "b"*env "e" - 2*env "c"*env "d") * (2*env "c")⁻¹) * Φ "I1" w) := by
        funext w
        simp [IntegrationNum1.rubi6113r10Nondeg, eval, recEnv, htwo, hneg, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        ring
      rw [hfun]
      simp [eval, htwo] at hΦ
      refine (((hT.const_mul _).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi6113r10Nondeg, eval, htwo, Function.update]
      generalize I.fn .cosh (env "a" + env "b"*t + env "c"*t^2) = S
      field_simp [hc, ht2]
      ring

end

theorem sinhRec_real : IntegrationNum1.rubi6113r9Nondeg.Holds .real :=
  sinhRec_holds Interp.real (by simp [Interp.real]) (by simp [Interp.real]) Real.hasDerivAt_cosh

theorem sinhRec_complex : IntegrationNum1.rubi6113r9Nondeg.Holds .complex :=
  sinhRec_holds Interp.complex (by simp [Interp.complex]) (by simp [Interp.complex]) Complex.hasDerivAt_cosh

theorem coshRec_real : IntegrationNum1.rubi6113r10Nondeg.Holds .real :=
  coshRec_holds Interp.real (by simp [Interp.real]) (by simp [Interp.real]) Real.hasDerivAt_sinh

theorem coshRec_complex : IntegrationNum1.rubi6113r10Nondeg.Holds .complex :=
  coshRec_holds Interp.complex (by simp [Interp.complex]) (by simp [Interp.complex]) Complex.hasDerivAt_sinh

end OSR.IntegrationHyperbolicRec
