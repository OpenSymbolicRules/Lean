import OSR.IntegrationNum1

/-! # Strengthened inverse hyperbolic tangent rules: substitution by an integer power

Proofs over ℝ of RUBI 7.3.1 #172 and #173 (and their 7.3.2 #5 and #6 twins), which reduce
`∫ (a + b artanh(c x^n))^p / x dx` and `∫ (a + b artanh(1/(c x^n)))^p / x dx` to
`1/n ∫ (a + b artanh(c u))^p / u du` (respectively with `1/(c u)`) at `u = x^n`, for an integer
`n ≠ 0`. The complex statements are vacuous (no complex interpretation of `transc1#arctanh`) and
stay unproved. -/

namespace OSR.IntegrationRec229

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)

/-! ## RUBI 7.3.1 #172 (and 7.3.2 #5) -/

theorem rubi731r172Nondeg_real : rubi731r172Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi731r172Nondeg.conditions
    rubi731r172Nondeg.body rubi731r172Nondeg.result rubi731r172Nondeg.integrals
    rubi731r172Nondeg.substs
  intro env hc t hF
  have hne : env "n" ≠ 0 := by
    have h := hc (.ne (.var "n") (.int 0)) (by simp [rubi731r172Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r172Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r172Nondeg, Defined, eval, Interp.real, hkp] at h
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r172Nondeg, Defined, eval, Interp.real, hkp, hkn] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hn : env "n" = (n : ℝ) := (intValue?_eq _ _).1 hkn
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have hk0 : ¬ k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r172Nondeg.body →
      (n < 0 → w ≠ 0) ∧ (-1 < env "c" * w ^ n ∧ env "c" * w ^ n < 1) ∧ w ≠ 0 := by
    intro w h
    simp [rubi731r172Nondeg, Defined, eval, Interp.real, hkp, hkn, ivm1R, hk0] at h
    tauto
  obtain ⟨-, ⟨h1, h2⟩, ht0⟩ := hD t hF.self_of_nhds
  have htn : t ^ n ≠ 0 := zpow_ne_zero n ht0
  have hlin : ContinuousAt (fun u : ℝ => env "c" * u) (t ^ n) := by fun_prop
  have hnear : ∀ᶠ u : ℝ in 𝓝 (t ^ n), (-1 < env "c" * u ∧ env "c" * u < 1) ∧ u ≠ 0 := by
    filter_upwards [hlin.tendsto.eventually (isOpen_Ioi.mem_nhds h1),
      hlin.tendsto.eventually (isOpen_Iio.mem_nhds h2), eventually_ne_nhds htn] with u hu hv hw
    exact ⟨⟨hu, hv⟩, hw⟩
  have hsub : substAt Interp.real env rubi731r172Nondeg.substs "x" "I1" t = t ^ n := by
    simp [rubi731r172Nondeg, substAt, eval, Interp.real, hkn]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi731r172Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards [hF] with w hw
      intro g hg
      simp only [rubi731r172Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      have hw' := hD w hw
      simpa [Defined, eval, Interp.real, hkn] using hw'.1
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simp [Defined, eval, Interp.real, hkp, ivm1R, hk0, hu.1.1, hu.1.2, hu.2]
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi731r172Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hne]
    · simp only [rubi731r172Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "a" + env "b" * Real.artanh (env "c" * t ^ n)) ^ k * (t ^ n)⁻¹) (t ^ n) := by
        simpa [rubi731r172Nondeg, substAt, List.lookup, eval, Interp.real, hkn, hkp, ivm1R]
          using hΦ
      have hG : HasDerivAt (fun w : ℝ => w ^ n) ((n : ℝ) * t ^ (n - 1)) t :=
        hasDerivAt_zpow n t (Or.inl ht0)
      have h := (hΦ'.comp t hG).const_mul (env "n")⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi731r172Nondeg.integrals.map (·.1))
            rubi731r172Nondeg.substs Φ "x" w) rubi731r172Nondeg.result) =
          fun w => (env "n")⁻¹ * Φ "I1" (w ^ n) := by
        funext w
        simp [rubi731r172Nondeg, substEnv, substAt, List.lookup, eval, Interp.real, hkn, ivm1R]
      rw [hfun]
      apply h.congr_deriv
      simp [rubi731r172Nondeg, eval, Interp.real, hkp, hkn, ivm1R]
      rw [zpow_sub_one₀ ht0]
      rw [hn] at hne ⊢
      field_simp

theorem rubi732r5Nondeg_real : rubi732r5Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi732r5Nondeg.conditions
    rubi732r5Nondeg.body rubi732r5Nondeg.result rubi732r5Nondeg.integrals
    rubi732r5Nondeg.substs
  exact rubi731r172Nondeg_real

/-! ## RUBI 7.3.1 #173 (and 7.3.2 #6) -/

theorem rubi731r173Nondeg_real : rubi731r173Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi731r173Nondeg.conditions
    rubi731r173Nondeg.body rubi731r173Nondeg.result rubi731r173Nondeg.integrals
    rubi731r173Nondeg.substs
  intro env hc t hF
  have hne : env "n" ≠ 0 := by
    have h := hc (.ne (.var "n") (.int 0)) (by simp [rubi731r173Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r173Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r173Nondeg, Defined, eval, Interp.real, hkp] at h
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r173Nondeg, Defined, eval, Interp.real, hkp, hkn] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hn : env "n" = (n : ℝ) := (intValue?_eq _ _).1 hkn
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have hk0 : ¬ k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r173Nondeg.body →
      (n < 0 → w ≠ 0) ∧ env "c" * w ^ n ≠ 0 ∧
        (-1 < (env "c" * w ^ n)⁻¹ ∧ (env "c" * w ^ n)⁻¹ < 1) ∧ w ≠ 0 := by
    intro w h
    simp [rubi731r173Nondeg, Defined, eval, Interp.real, hkp, hkn, ivm1R, hk0, mul_inv_rev] at h
    simp only [ne_eq, mul_eq_zero, not_or, mul_inv_rev]
    tauto
  obtain ⟨-, hct, ⟨h1, h2⟩, ht0⟩ := hD t hF.self_of_nhds
  have htn : t ^ n ≠ 0 := zpow_ne_zero n ht0
  have hinv : ContinuousAt (fun u : ℝ => (env "c" * u)⁻¹) (t ^ n) :=
    (continuousAt_const.mul continuousAt_id).inv₀ hct
  have hlin : ContinuousAt (fun u : ℝ => env "c" * u) (t ^ n) := by fun_prop
  have hnear : ∀ᶠ u : ℝ in 𝓝 (t ^ n), env "c" * u ≠ 0 ∧
      (-1 < (env "c" * u)⁻¹ ∧ (env "c" * u)⁻¹ < 1) ∧ u ≠ 0 := by
    filter_upwards [hlin.tendsto.eventually (eventually_ne_nhds hct),
      hinv.tendsto.eventually (isOpen_Ioi.mem_nhds h1),
      hinv.tendsto.eventually (isOpen_Iio.mem_nhds h2), eventually_ne_nhds htn] with u h0 hu hv hw
    exact ⟨h0, ⟨hu, hv⟩, hw⟩
  have hsub : substAt Interp.real env rubi731r173Nondeg.substs "x" "I1" t = t ^ n := by
    simp [rubi731r173Nondeg, substAt, eval, Interp.real, hkn]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi731r173Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards [hF] with w hw
      intro g hg
      simp only [rubi731r173Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      have hw' := hD w hw
      simpa [Defined, eval, Interp.real, hkn] using hw'.1
    · rw [hsub]
      filter_upwards [hnear] with u hu
      have hu0 := hu.1
      simp only [ne_eq, mul_eq_zero, not_or] at hu0
      have hu1 := hu.2.1.1
      have hu2 := hu.2.1.2
      rw [mul_inv_rev] at hu1 hu2
      simp [Defined, eval, Interp.real, hkp, ivm1R, hk0, hu0.1, hu0.2, hu1, hu2]
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi731r173Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hne]
    · simp only [rubi731r173Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "a" + env "b" * Real.artanh (env "c" * t ^ n)⁻¹) ^ k * (t ^ n)⁻¹) (t ^ n) := by
        convert hΦ using 1 <;>
        simp [substAt, List.lookup, eval, Interp.real, hkn, hkp, ivm1R,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      have hG : HasDerivAt (fun w : ℝ => w ^ n) ((n : ℝ) * t ^ (n - 1)) t :=
        hasDerivAt_zpow n t (Or.inl ht0)
      have h := (hΦ'.comp t hG).const_mul (env "n")⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi731r173Nondeg.integrals.map (·.1))
            rubi731r173Nondeg.substs Φ "x" w) rubi731r173Nondeg.result) =
          fun w => (env "n")⁻¹ * Φ "I1" (w ^ n) := by
        funext w
        simp [rubi731r173Nondeg, substEnv, substAt, List.lookup, eval, Interp.real, hkn, ivm1R]
      rw [hfun]
      apply h.congr_deriv
      simp [rubi731r173Nondeg, eval, Interp.real, hkp, hkn, ivm1R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
      rw [zpow_sub_one₀ ht0]
      rw [hn] at hne ⊢
      field_simp

theorem rubi732r6Nondeg_real : rubi732r6Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi732r6Nondeg.conditions
    rubi732r6Nondeg.body rubi732r6Nondeg.result rubi732r6Nondeg.integrals
    rubi732r6Nondeg.substs
  exact rubi731r173Nondeg_real

end OSR.IntegrationRec229
