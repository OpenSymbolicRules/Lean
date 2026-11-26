import OSR.IntegrationNum1

/-! # Strengthened inverse hyperbolic tangent rules: linear substitutions and reciprocal rewrites

Proofs over ℝ of RUBI 7.3.2 #1, #2, #9 and #10 and 7.3.5 #5 (each with its 7.3.5 or 7.3.2
twin), which substitute `u = c + d x` in `(a + b artanh(c + d x))^p`,
`(a + b artanh(1/(c + d x)))^p` and their products with `(e + f x)^m` (7.3.5 #5 assumes
`d e = c f`), and of RUBI 7.3.1 (power) #5 and 7.3.2 #13 (with a factor `x^m`), which rewrite
`artanh(c x^n)` as `artanh(1/(x^(-n)/c))` for an integer `n < 0`. The complex statements are
vacuous (no complex interpretation of `transc1#arctanh`) and stay unproved. -/

namespace OSR.IntegrationRec230

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)

private theorem hasDerivAt_lin (a b t : ℝ) : HasDerivAt (fun w => a + b * w) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

/-! ## RUBI 7.3.2 #1 (and 7.3.5 #1) -/

theorem rubi732r1Nondeg_real : rubi732r1Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi732r1Nondeg.conditions
    rubi732r1Nondeg.body rubi732r1Nondeg.result rubi732r1Nondeg.integrals
    rubi732r1Nondeg.substs
  intro env hc t hF
  have hne : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi732r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi732r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi732r1Nondeg, Defined, eval, Interp.real, hkp] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have hk0 : ¬ k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi732r1Nondeg.body →
      -1 < env "c" + env "d" * w ∧ env "c" + env "d" * w < 1 := by
    intro w h
    simp [rubi732r1Nondeg, Defined, eval, Interp.real, hkp, hk0] at h
    tauto
  obtain ⟨h1, h2⟩ := hD t hF.self_of_nhds
  have hnear : ∀ᶠ u : ℝ in 𝓝 (env "c" + env "d" * t), -1 < u ∧ u < 1 := by
    filter_upwards [isOpen_Ioi.mem_nhds h1, isOpen_Iio.mem_nhds h2] with u hu hv
    exact ⟨hu, hv⟩
  have hsub : substAt Interp.real env rubi732r1Nondeg.substs "x" "I1" t =
      env "c" + env "d" * t := by
    simp [rubi732r1Nondeg, substAt, eval]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi732r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards with w
      intro g hg
      simp only [rubi732r1Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined]
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simp [Defined, eval, Interp.real, hkp, hk0, hu.1, hu.2]
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi732r1Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hne]
    · simp only [rubi732r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "a" + env "b" * Real.artanh (env "c" + env "d" * t)) ^ k)
          (env "c" + env "d" * t) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkp]
      have h := (hΦ'.comp t (hasDerivAt_lin (env "c") (env "d") t)).const_mul (env "d")⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi732r1Nondeg.integrals.map (·.1))
            rubi732r1Nondeg.substs Φ "x" w) rubi732r1Nondeg.result) =
          fun w => (env "d")⁻¹ * Φ "I1" (env "c" + env "d" * w) := by
        funext w
        simp [rubi732r1Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      apply h.congr_deriv
      simp [rubi732r1Nondeg, eval, Interp.real, hkp]
      field_simp

theorem rubi735r1Nondeg_real : rubi735r1Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi735r1Nondeg.conditions
    rubi735r1Nondeg.body rubi735r1Nondeg.result rubi735r1Nondeg.integrals
    rubi735r1Nondeg.substs
  exact rubi732r1Nondeg_real

/-! ## RUBI 7.3.2 #2 (and 7.3.5 #2) -/

theorem rubi732r2Nondeg_real : rubi732r2Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi732r2Nondeg.conditions
    rubi732r2Nondeg.body rubi732r2Nondeg.result rubi732r2Nondeg.integrals
    rubi732r2Nondeg.substs
  intro env hc t hF
  have hne : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi732r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi732r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi732r2Nondeg, Defined, eval, Interp.real, hkp] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have hk0 : ¬ k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi732r2Nondeg.body →
      env "c" + env "d" * w ≠ 0 ∧
        (-1 < (env "c" + env "d" * w)⁻¹ ∧ (env "c" + env "d" * w)⁻¹ < 1) := by
    intro w h
    simp [rubi732r2Nondeg, Defined, eval, Interp.real, hkp, hk0, ivm1R] at h
    tauto
  obtain ⟨h0, h1, h2⟩ := hD t hF.self_of_nhds
  have hinv : ContinuousAt (fun u : ℝ => u⁻¹) (env "c" + env "d" * t) :=
    continuousAt_inv₀ h0
  have hnear : ∀ᶠ u : ℝ in 𝓝 (env "c" + env "d" * t), u ≠ 0 ∧ (-1 < u⁻¹ ∧ u⁻¹ < 1) := by
    filter_upwards [eventually_ne_nhds h0, hinv.tendsto.eventually (isOpen_Ioi.mem_nhds h1),
      hinv.tendsto.eventually (isOpen_Iio.mem_nhds h2)] with u h0 hu hv
    exact ⟨h0, hu, hv⟩
  have hsub : substAt Interp.real env rubi732r2Nondeg.substs "x" "I1" t =
      env "c" + env "d" * t := by
    simp [rubi732r2Nondeg, substAt, eval]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi732r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards with w
      intro g hg
      simp only [rubi732r2Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined]
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simp [Defined, eval, Interp.real, hkp, hk0, ivm1R, hu.1, hu.2.1, hu.2.2]
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi732r2Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hne]
    · simp only [rubi732r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "a" + env "b" * Real.artanh (env "c" + env "d" * t)⁻¹) ^ k)
          (env "c" + env "d" * t) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkp, ivm1R]
      have h := (hΦ'.comp t (hasDerivAt_lin (env "c") (env "d") t)).const_mul (env "d")⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi732r2Nondeg.integrals.map (·.1))
            rubi732r2Nondeg.substs Φ "x" w) rubi732r2Nondeg.result) =
          fun w => (env "d")⁻¹ * Φ "I1" (env "c" + env "d" * w) := by
        funext w
        simp [rubi732r2Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      apply h.congr_deriv
      simp [rubi732r2Nondeg, eval, Interp.real, hkp, ivm1R]
      field_simp

theorem rubi735r2Nondeg_real : rubi735r2Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi735r2Nondeg.conditions
    rubi735r2Nondeg.body rubi735r2Nondeg.result rubi735r2Nondeg.integrals
    rubi735r2Nondeg.substs
  exact rubi732r2Nondeg_real

/-! ## RUBI 7.3.5 #5 (and 7.3.2 #5, second form) -/

theorem rubi735r5Nondeg_real : rubi735r5Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi735r5Nondeg.conditions
    rubi735r5Nondeg.body rubi735r5Nondeg.result rubi735r5Nondeg.integrals
    rubi735r5Nondeg.substs
  intro env hc t hF
  have hne : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi735r5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi735r5Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hrel : env "d" * env "e" = env "c" * env "f" := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "d") (.var "e"))
      (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f"))) (.int 0))
      (by simp [rubi735r5Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi735r5Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi735r5Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have hk0 : ¬ k < 0 := by omega
  have hlin : ∀ w, env "f" * (env "c" + env "d" * w) * (env "d")⁻¹ = env "e" + env "f" * w := by
    intro w
    field_simp
    linear_combination -hrel
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi735r5Nondeg.body →
      (m < 0 → env "e" + env "f" * w ≠ 0) ∧
        (-1 < env "c" + env "d" * w ∧ env "c" + env "d" * w < 1) := by
    intro w h
    simp [rubi735r5Nondeg, Defined, eval, Interp.real, hkm, hkp, hk0] at h
    tauto
  obtain ⟨hm0, h1, h2⟩ := hD t hF.self_of_nhds
  have hcf : ContinuousAt (fun u : ℝ => env "f" * u * (env "d")⁻¹) (env "c" + env "d" * t) := by
    fun_prop
  have hnear : ∀ᶠ u : ℝ in 𝓝 (env "c" + env "d" * t),
      (m < 0 → env "f" * u * (env "d")⁻¹ ≠ 0) ∧ (-1 < u ∧ u < 1) := by
    by_cases hmn : m < 0
    · have hv : env "f" * (env "c" + env "d" * t) * (env "d")⁻¹ ≠ 0 := by
        rw [hlin]; exact hm0 hmn
      filter_upwards [hcf.tendsto.eventually (eventually_ne_nhds hv),
        isOpen_Ioi.mem_nhds h1, isOpen_Iio.mem_nhds h2] with u h0 hu hv
      exact ⟨fun _ => h0, hu, hv⟩
    · filter_upwards [isOpen_Ioi.mem_nhds h1, isOpen_Iio.mem_nhds h2] with u hu hv
      exact ⟨fun h => absurd h hmn, hu, hv⟩
  have hsub : substAt Interp.real env rubi735r5Nondeg.substs "x" "I1" t =
      env "c" + env "d" * t := by
    simp [rubi735r5Nondeg, substAt, eval]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi735r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards with w
      intro g hg
      simp only [rubi735r5Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined]
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or] at hu
      simp [Defined, eval, Interp.real, hkm, hkp, hk0, ivm1R, hu.2.1, hu.2.2]
      tauto
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi735r5Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hne]
    · simp only [rubi735r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "f" * (env "c" + env "d" * t) * (env "d")⁻¹) ^ m *
            (env "a" + env "b" * Real.artanh (env "c" + env "d" * t)) ^ k)
          (env "c" + env "d" * t) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkm, hkp, ivm1R]
      have h := (hΦ'.comp t (hasDerivAt_lin (env "c") (env "d") t)).const_mul (env "d")⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi735r5Nondeg.integrals.map (·.1))
            rubi735r5Nondeg.substs Φ "x" w) rubi735r5Nondeg.result) =
          fun w => (env "d")⁻¹ * Φ "I1" (env "c" + env "d" * w) := by
        funext w
        simp [rubi735r5Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      apply h.congr_deriv
      simp only [hlin]
      simp [rubi735r5Nondeg, eval, Interp.real, hkm, hkp]
      field_simp

theorem rubi732r5yNondeg_real : rubi732r5yNondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi732r5yNondeg.conditions
    rubi732r5yNondeg.body rubi732r5yNondeg.result rubi732r5yNondeg.integrals
    rubi732r5yNondeg.substs
  exact rubi735r5Nondeg_real

/-! ## RUBI 7.3.2 #9 and #10 (and 7.3.5 #9 and #10) -/

theorem rubi732r9Nondeg_real : rubi732r9Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi732r9Nondeg.conditions
    rubi732r9Nondeg.body rubi732r9Nondeg.result rubi732r9Nondeg.integrals
    rubi732r9Nondeg.substs
  intro env hc t hF
  have hne : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi732r9Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi732r9Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi732r9Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi732r9Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have hk0 : ¬ k < 0 := by omega
  have hlin : ∀ w, (env "d" * env "e" + -(env "c" * env "f")) * (env "d")⁻¹ +
      env "f" * (env "c" + env "d" * w) * (env "d")⁻¹ = env "e" + env "f" * w := by
    intro w
    field_simp
    ring
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi732r9Nondeg.body →
      (m < 0 → env "e" + env "f" * w ≠ 0) ∧
        (-1 < env "c" + env "d" * w ∧ env "c" + env "d" * w < 1) := by
    intro w h
    simp [rubi732r9Nondeg, Defined, eval, Interp.real, hkm, hkp, hk0] at h
    tauto
  obtain ⟨hm0, h1, h2⟩ := hD t hF.self_of_nhds
  have hcf : ContinuousAt (fun u : ℝ => (env "d" * env "e" + -(env "c" * env "f")) *
      (env "d")⁻¹ + env "f" * u * (env "d")⁻¹) (env "c" + env "d" * t) := by
    fun_prop
  have hnear : ∀ᶠ u : ℝ in 𝓝 (env "c" + env "d" * t),
      (m < 0 → (env "d" * env "e" + -(env "c" * env "f")) * (env "d")⁻¹ +
        env "f" * u * (env "d")⁻¹ ≠ 0) ∧ (-1 < u ∧ u < 1) := by
    by_cases hmn : m < 0
    · have hv : (env "d" * env "e" + -(env "c" * env "f")) * (env "d")⁻¹ +
          env "f" * (env "c" + env "d" * t) * (env "d")⁻¹ ≠ 0 := by
        rw [hlin]; exact hm0 hmn
      filter_upwards [hcf.tendsto.eventually (eventually_ne_nhds hv),
        isOpen_Ioi.mem_nhds h1, isOpen_Iio.mem_nhds h2] with u h0 hu hv
      exact ⟨fun _ => h0, hu, hv⟩
    · filter_upwards [isOpen_Ioi.mem_nhds h1, isOpen_Iio.mem_nhds h2] with u hu hv
      exact ⟨fun h => absurd h hmn, hu, hv⟩
  have hsub : substAt Interp.real env rubi732r9Nondeg.substs "x" "I1" t =
      env "c" + env "d" * t := by
    simp [rubi732r9Nondeg, substAt, eval]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi732r9Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards with w
      intro g hg
      simp only [rubi732r9Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined]
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simp [Defined, eval, Interp.real, hkm, hkp, hk0, ivm1R, hu.2.1, hu.2.2]
      tauto
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi732r9Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hne]
    · simp only [rubi732r9Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "e" + env "f" * t) ^ m *
            (env "a" + env "b" * Real.artanh (env "c" + env "d" * t)) ^ k)
          (env "c" + env "d" * t) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkm, hkp, ivm1R, hlin]
      have h := (hΦ'.comp t (hasDerivAt_lin (env "c") (env "d") t)).const_mul (env "d")⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi732r9Nondeg.integrals.map (·.1))
            rubi732r9Nondeg.substs Φ "x" w) rubi732r9Nondeg.result) =
          fun w => (env "d")⁻¹ * Φ "I1" (env "c" + env "d" * w) := by
        funext w
        simp [rubi732r9Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      apply h.congr_deriv
      simp [rubi732r9Nondeg, eval, Interp.real, hkm, hkp]
      field_simp

theorem rubi735r9Nondeg_real : rubi735r9Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi735r9Nondeg.conditions
    rubi735r9Nondeg.body rubi735r9Nondeg.result rubi735r9Nondeg.integrals
    rubi735r9Nondeg.substs
  exact rubi732r9Nondeg_real

theorem rubi732r10Nondeg_real : rubi732r10Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi732r10Nondeg.conditions
    rubi732r10Nondeg.body rubi732r10Nondeg.result rubi732r10Nondeg.integrals
    rubi732r10Nondeg.substs
  intro env hc t hF
  have hne : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi732r10Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi732r10Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi732r10Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi732r10Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have hk0 : ¬ k < 0 := by omega
  have hlin : ∀ w, (env "d" * env "e" + -(env "c" * env "f")) * (env "d")⁻¹ +
      env "f" * (env "c" + env "d" * w) * (env "d")⁻¹ = env "e" + env "f" * w := by
    intro w
    field_simp
    ring
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi732r10Nondeg.body →
      (m < 0 → env "e" + env "f" * w ≠ 0) ∧
        env "c" + env "d" * w ≠ 0 ∧
        (-1 < (env "c" + env "d" * w)⁻¹ ∧ (env "c" + env "d" * w)⁻¹ < 1) := by
    intro w h
    simp [rubi732r10Nondeg, Defined, eval, Interp.real, hkm, hkp, hk0, ivm1R] at h
    tauto
  obtain ⟨hm0, h0, h1, h2⟩ := hD t hF.self_of_nhds
  have hinv : ContinuousAt (fun u : ℝ => u⁻¹) (env "c" + env "d" * t) :=
    continuousAt_inv₀ h0
  have hcf : ContinuousAt (fun u : ℝ => (env "d" * env "e" + -(env "c" * env "f")) *
      (env "d")⁻¹ + env "f" * u * (env "d")⁻¹) (env "c" + env "d" * t) := by
    fun_prop
  have hnear : ∀ᶠ u : ℝ in 𝓝 (env "c" + env "d" * t),
      (m < 0 → (env "d" * env "e" + -(env "c" * env "f")) * (env "d")⁻¹ +
        env "f" * u * (env "d")⁻¹ ≠ 0) ∧ u ≠ 0 ∧ (-1 < u⁻¹ ∧ u⁻¹ < 1) := by
    by_cases hmn : m < 0
    · have hv : (env "d" * env "e" + -(env "c" * env "f")) * (env "d")⁻¹ +
          env "f" * (env "c" + env "d" * t) * (env "d")⁻¹ ≠ 0 := by
        rw [hlin]; exact hm0 hmn
      filter_upwards [hcf.tendsto.eventually (eventually_ne_nhds hv), eventually_ne_nhds h0,
        hinv.tendsto.eventually (isOpen_Ioi.mem_nhds h1),
        hinv.tendsto.eventually (isOpen_Iio.mem_nhds h2)] with u hz h0 hu hv
      exact ⟨fun _ => hz, h0, hu, hv⟩
    · filter_upwards [eventually_ne_nhds h0, hinv.tendsto.eventually (isOpen_Ioi.mem_nhds h1),
        hinv.tendsto.eventually (isOpen_Iio.mem_nhds h2)] with u h0 hu hv
      exact ⟨fun h => absurd h hmn, h0, hu, hv⟩
  have hsub : substAt Interp.real env rubi732r10Nondeg.substs "x" "I1" t =
      env "c" + env "d" * t := by
    simp [rubi732r10Nondeg, substAt, eval]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi732r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards with w
      intro g hg
      simp only [rubi732r10Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined]
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simp [Defined, eval, Interp.real, hkm, hkp, hk0, ivm1R, hu.2.1, hu.2.2.1, hu.2.2.2]
      tauto
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi732r10Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hne]
    · simp only [rubi732r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "e" + env "f" * t) ^ m *
            (env "a" + env "b" * Real.artanh (env "c" + env "d" * t)⁻¹) ^ k)
          (env "c" + env "d" * t) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkm, hkp, ivm1R, hlin]
      have h := (hΦ'.comp t (hasDerivAt_lin (env "c") (env "d") t)).const_mul (env "d")⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi732r10Nondeg.integrals.map (·.1))
            rubi732r10Nondeg.substs Φ "x" w) rubi732r10Nondeg.result) =
          fun w => (env "d")⁻¹ * Φ "I1" (env "c" + env "d" * w) := by
        funext w
        simp [rubi732r10Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      apply h.congr_deriv
      simp [rubi732r10Nondeg, eval, Interp.real, hkm, hkp, ivm1R]
      field_simp

theorem rubi735r10Nondeg_real : rubi735r10Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi735r10Nondeg.conditions
    rubi735r10Nondeg.body rubi735r10Nondeg.result rubi735r10Nondeg.integrals
    rubi735r10Nondeg.substs
  exact rubi732r10Nondeg_real

/-! ## RUBI 7.3.1 (power) #5 -/

theorem rubi731pr5Nondeg_real : rubi731pr5Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731pr5Nondeg.conditions rubi731pr5Nondeg.body
    rubi731pr5Nondeg.result rubi731pr5Nondeg.integrals
  intro env hc t hF
  have hcz : env "c" ≠ 0 := by
    have h := hc (.ne (.var "c") (.int 0)) (by simp [rubi731pr5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hneg : env "n" < 0 := by
    have h := hc (.gt (.int 0) (.var "n")) (by simp [rubi731pr5Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hpos : 1 < env "p" := by
    have h := hc (.gt (.var "p") (.int 1)) (by simp [rubi731pr5Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731pr5Nondeg, Defined, eval, Interp.real, hkp] at h
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731pr5Nondeg, Defined, eval, Interp.real, hkp, hkn] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hn : env "n" = (n : ℝ) := (intValue?_eq _ _).1 hkn
  have hk0 : ¬ k < 0 := by
    have : (1 : ℝ) < k := hp ▸ hpos
    have : (1 : ℤ) < k := by exact_mod_cast this
    omega
  have hn0 : n < 0 := by rw [hn] at hneg; exact_mod_cast hneg
  have ivn : intValue? (-env "n") = some (-n) := (intValue?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731pr5Nondeg.body →
      w ≠ 0 ∧ (-1 < env "c" * w ^ n ∧ env "c" * w ^ n < 1) := by
    intro w h
    simp [rubi731pr5Nondeg, Defined, eval, Interp.real, hkp, hkn, hk0, hn0] at h
    tauto
  have hEq : ∀ w, eval Interp.real (Function.update env "x" w) rubi731pr5Nondeg.body =
      eval Interp.real (Function.update env "x" w) (rubi731pr5Nondeg.integrals.head!.2) := by
    intro w
    simp [rubi731pr5Nondeg, eval, Interp.real, hkp, hkn, ivn, ivm1R]
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731pr5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hB := hD w hw
    have hx : w ^ (-n) * (env "c")⁻¹ ≠ 0 := by
      have := zpow_ne_zero (-n) hB.1
      exact mul_ne_zero this (inv_ne_zero hcz)
    simp [Defined, eval, Interp.real, hkp, ivn, ivm1R, hk0, hB.2.1, hB.2.2,
      hB.1, hcz, zpow_ne_zero n hB.1]
  · filter_upwards with w
    simp [rubi731pr5Nondeg, Defined]
  · simp only [rubi731pr5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731pr5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731pr5Nondeg.result) = Φ "I1" := by
      funext w
      simp [rubi731pr5Nondeg, eval, recEnv]
    rw [hfun]
    convert hΦ using 1
    simpa [rubi731pr5Nondeg] using hEq t

/-! ## RUBI 7.3.2 #13 -/

theorem rubi732r13Nondeg_real : rubi732r13Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi732r13Nondeg.conditions rubi732r13Nondeg.body
    rubi732r13Nondeg.result rubi732r13Nondeg.integrals
  intro env hc t hF
  have hcz : env "c" ≠ 0 := by
    have h := hc (.ne (.var "c") (.int 0)) (by simp [rubi732r13Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hneg : env "n" < 0 := by
    have h := hc (.gt (.int 0) (.var "n")) (by simp [rubi732r13Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hpos : 1 < env "p" := by
    have h := hc (.gt (.var "p") (.int 1)) (by simp [rubi732r13Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi732r13Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi732r13Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi732r13Nondeg, Defined, eval, Interp.real, hkm, hkp, hkn] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hn : env "n" = (n : ℝ) := (intValue?_eq _ _).1 hkn
  have hk0 : ¬ k < 0 := by
    have : (1 : ℝ) < k := hp ▸ hpos
    have : (1 : ℤ) < k := by exact_mod_cast this
    omega
  have hn0 : n < 0 := by rw [hn] at hneg; exact_mod_cast hneg
  have ivn : intValue? (-env "n") = some (-n) := (intValue?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi732r13Nondeg.body →
      (m < 0 → w ≠ 0) ∧ w ≠ 0 ∧ (-1 < env "c" * w ^ n ∧ env "c" * w ^ n < 1) := by
    intro w h
    simp [rubi732r13Nondeg, Defined, eval, Interp.real, hkm, hkp, hkn, hk0, hn0] at h
    tauto
  have hEq : ∀ w, eval Interp.real (Function.update env "x" w) rubi732r13Nondeg.body =
      eval Interp.real (Function.update env "x" w) (rubi732r13Nondeg.integrals.head!.2) := by
    intro w
    simp [rubi732r13Nondeg, eval, Interp.real, hkm, hkp, hkn, ivn, ivm1R]
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi732r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hB := (hD w hw).2
    have hx : w ^ (-n) * (env "c")⁻¹ ≠ 0 := by
      have := zpow_ne_zero (-n) hB.1
      exact mul_ne_zero this (inv_ne_zero hcz)
    simp [Defined, eval, Interp.real, hkm, hkp, ivn, ivm1R, hk0, hB.2.1, hB.2.2,
      hB.1, hcz, zpow_ne_zero n hB.1]
  · filter_upwards with w
    simp [rubi732r13Nondeg, Defined]
  · simp only [rubi732r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi732r13Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi732r13Nondeg.result) = Φ "I1" := by
      funext w
      simp [rubi732r13Nondeg, eval, recEnv]
    rw [hfun]
    convert hΦ using 1
    simpa [rubi732r13Nondeg] using hEq t

end OSR.IntegrationRec230
