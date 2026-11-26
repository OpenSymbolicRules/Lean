import OSR.IntegrationRec215

/-! # Strengthened inverse hyperbolic sine rules (continued)

Proof over ℝ of RUBI 7.1.6 #2, which substitutes `u = c + d x` in
`(e + f x)^m (a + b arsinh(c + d x))^n`. The complex statement is vacuous (no complex
interpretation of `transc1#arcsinh`) and stays unproved. -/

namespace OSR.IntegrationRec241

open OSR OSR.Calculus OSR.IntegrationNum1 OSR.IntegrationRec215 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)

private theorem hasDerivAt_lin (a b t : ℝ) : HasDerivAt (fun w => a + b * w) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

/-! ## RUBI 7.1.6 #2 -/

theorem rubi716r2Nondeg_real : rubi716r2Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi716r2Nondeg.conditions
    rubi716r2Nondeg.body rubi716r2Nondeg.result rubi716r2Nondeg.integrals
    rubi716r2Nondeg.substs
  intro env hc t hF
  have hne : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi716r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi716r2Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi716r2Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  have hlin : ∀ w, (env "d" * env "e" + -(env "c" * env "f")) * (env "d")⁻¹ +
      env "f" * (env "c" + env "d" * w) * (env "d")⁻¹ = env "e" + env "f" * w := by
    intro w
    field_simp
    ring
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi716r2Nondeg.body →
      (m < 0 → env "e" + env "f" * w ≠ 0) ∧
        (k < 0 → env "a" + env "b" * Real.arsinh (env "c" + env "d" * w) ≠ 0) := by
    intro w h
    simp [rubi716r2Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
    tauto
  obtain ⟨hm0, hA0⟩ := hD t hF.self_of_nhds
  have hcA : ContinuousAt (fun u : ℝ => env "a" + env "b" * Real.arsinh u)
      (env "c" + env "d" * t) :=
    continuousAt_const.add (continuousAt_const.mul Real.continuous_arsinh.continuousAt)
  have hnA : ∀ᶠ u : ℝ in 𝓝 (env "c" + env "d" * t),
      k < 0 → env "a" + env "b" * Real.arsinh u ≠ 0 := by
    by_cases hk : k < 0
    · filter_upwards [hcA.tendsto.eventually (eventually_ne_nhds (hA0 hk))] with u hu
      exact fun _ => hu
    · exact Filter.Eventually.of_forall fun _ h => absurd h hk
  have hcf : ContinuousAt (fun u : ℝ => (env "d" * env "e" + -(env "c" * env "f")) *
      (env "d")⁻¹ + env "f" * u * (env "d")⁻¹) (env "c" + env "d" * t) := by
    fun_prop
  have hnear : ∀ᶠ u : ℝ in 𝓝 (env "c" + env "d" * t),
      (m < 0 → (env "d" * env "e" + -(env "c" * env "f")) * (env "d")⁻¹ +
        env "f" * u * (env "d")⁻¹ ≠ 0) ∧ (k < 0 → env "a" + env "b" * Real.arsinh u ≠ 0) := by
    by_cases hmn : m < 0
    · have hv : (env "d" * env "e" + -(env "c" * env "f")) * (env "d")⁻¹ +
          env "f" * (env "c" + env "d" * t) * (env "d")⁻¹ ≠ 0 := by
        rw [hlin]; exact hm0 hmn
      filter_upwards [hcf.tendsto.eventually (eventually_ne_nhds hv), hnA] with u h0 hu
      exact ⟨fun _ => h0, hu⟩
    · filter_upwards [hnA] with u hu
      exact ⟨fun h => absurd h hmn, hu⟩
  have hsub : substAt Interp.real env rubi716r2Nondeg.substs "x" "I1" t =
      env "c" + env "d" * t := by
    simp [rubi716r2Nondeg, substAt, eval]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi716r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards with w
      intro g hg
      simp only [rubi716r2Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined]
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simp [Defined, eval, Interp.real, hkm, hkp, ivm1R]
      tauto
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi716r2Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hne]
    · simp only [rubi716r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "e" + env "f" * t) ^ m *
            (env "a" + env "b" * Real.arsinh (env "c" + env "d" * t)) ^ k)
          (env "c" + env "d" * t) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkm, hkp, ivm1R, hlin]
      have h := (hΦ'.comp t (hasDerivAt_lin (env "c") (env "d") t)).const_mul (env "d")⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi716r2Nondeg.integrals.map (·.1))
            rubi716r2Nondeg.substs Φ "x" w) rubi716r2Nondeg.result) =
          fun w => (env "d")⁻¹ * Φ "I1" (env "c" + env "d" * w) := by
        funext w
        simp [rubi716r2Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      apply h.congr_deriv
      simp [rubi716r2Nondeg, eval, Interp.real, hkm, hkp]
      field_simp

end OSR.IntegrationRec241
