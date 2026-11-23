import OSR.IntegrationNum1

/-! # RUBI 3.1.2 #7: substitution by an integer power -/

namespace OSR.IntegrationRec209

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

theorem rubi312r7Nondeg_real : rubi312r7Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi312r7Nondeg.conditions
    rubi312r7Nondeg.body rubi312r7Nondeg.result rubi312r7Nondeg.integrals
    rubi312r7Nondeg.substs
  intro env hc t hF
  have hne : env "n" ≠ 0 := by
    have h := hc (.ne (.var "n") (.int 0)) (by simp [rubi312r7Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have heq : env "m" = env "n" - 1 := by
    have h := hc (.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))
      (by simp [rubi312r7Nondeg])
    simpa [Cond.Holds, Defined, eval, sub_eq_add_neg] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi312r7Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi312r7Nondeg, Defined, eval, Interp.real, hkm, hkn] at h
  have hm : env "m" = (m : ℝ) := (intValue?_eq _ _).1 hkm
  have hn : env "n" = (n : ℝ) := (intValue?_eq _ _).1 hkn
  have hmn : m = n - 1 := by
    have h : (m : ℝ) = (n : ℝ) - 1 := by simpa [hm, hn] using heq
    exact_mod_cast h
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi312r7Nondeg.body ↔
      (m < 0 → w ≠ 0) ∧ (n < 0 → w ≠ 0) ∧ 0 < env "c" * w ^ n ∧
        Real.log (env "c" * w ^ n) ≠ 0 := by
    intro w
    simp [rubi312r7Nondeg, Defined, eval, Interp.real, hkm, hkn, ivm1]
    tauto
  have ht := (hD t).1 hF.self_of_nhds
  have hn0 : n ≠ 0 := by
    intro h
    apply hne
    rw [hn, h]
    norm_num
  have ht0 : t ≠ 0 := by
    intro h
    have hp := ht.2.2.1
    rw [h, zero_zpow n hn0, mul_zero] at hp
    exact lt_irrefl 0 hp
  have hlin : ContinuousAt (fun u : ℝ => env "c" * u) (t ^ n) := by fun_prop
  have hlog : ContinuousAt (fun u : ℝ => Real.log (env "c" * u)) (t ^ n) :=
    (Real.continuousAt_log ht.2.2.1.ne').comp hlin
  have hnear : ∀ᶠ u : ℝ in 𝓝 (t ^ n),
      0 < env "c" * u ∧ Real.log (env "c" * u) ≠ 0 := by
    filter_upwards [hlin.tendsto.eventually (isOpen_Ioi.mem_nhds ht.2.2.1),
      hlog.tendsto.eventually (eventually_ne_nhds ht.2.2.2)] with u hu hv
    exact ⟨hu, hv⟩
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi312r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards [hF] with w hw
      intro g hg
      simp only [rubi312r7Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      have hw' := (hD w).1 hw
      simpa [Defined, eval, Interp.real, hkn] using hw'.2.1
    · simpa [rubi312r7Nondeg, substAt, List.lookup, Defined, eval, Interp.real, hkn, ivm1]
        using hnear
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi312r7Nondeg, Defined, eval, Interp.real, substEnv, ivm1, hne]
    · simp only [rubi312r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1") (Real.log (env "c" * t ^ n))⁻¹ (t ^ n) := by
        simpa [rubi312r7Nondeg, substAt, List.lookup, eval, Interp.real, hkn, ivm1] using hΦ
      have hG : HasDerivAt (fun w : ℝ => w ^ n) ((n : ℝ) * t ^ (n - 1)) t :=
        hasDerivAt_zpow n t (Or.inl ht0)
      have h := (hΦ'.comp t hG).const_mul (env "n")⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi312r7Nondeg.integrals.map (·.1))
            rubi312r7Nondeg.substs Φ "x" w) rubi312r7Nondeg.result) =
          fun w => (env "n")⁻¹ * Φ "I1" (w ^ n) := by
        funext w
        simp [rubi312r7Nondeg, substEnv, substAt, List.lookup, eval, Interp.real, hkn, ivm1]
      rw [hfun]
      apply h.congr_deriv
      simp [rubi312r7Nondeg, eval, Interp.real, hkm, hkn, ivm1]
      rw [hn] at hne ⊢
      rw [hmn]
      field_simp [hne]

theorem rubi312r7Nondeg_complex : rubi312r7Nondeg.Holds .complex := by
  show AntiderivSubstHolds Interp.complex "x" rubi312r7Nondeg.conditions
    rubi312r7Nondeg.body rubi312r7Nondeg.result rubi312r7Nondeg.integrals
    rubi312r7Nondeg.substs
  intro env hc t hF
  have hne : env "n" ≠ 0 := by
    have h := hc (.ne (.var "n") (.int 0)) (by simp [rubi312r7Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have heq : env "m" = env "n" - 1 := by
    have h := hc (.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))
      (by simp [rubi312r7Nondeg])
    simpa [Cond.Holds, Defined, eval, sub_eq_add_neg] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi312r7Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi312r7Nondeg, Defined, eval, Interp.complex, hkm, hkn] at h
  have hm : env "m" = (m : ℂ) := (intValue?_eq _ _).1 hkm
  have hn : env "n" = (n : ℂ) := (intValue?_eq _ _).1 hkn
  have hmn : m = n - 1 := by
    have h : (m : ℂ) = (n : ℂ) - 1 := by simpa [hm, hn] using heq
    exact_mod_cast h
  have ivm1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi312r7Nondeg.body ↔
      (m < 0 → w ≠ 0) ∧ (n < 0 → w ≠ 0) ∧ env "c" * w ^ n ≠ 0 ∧
        Complex.log (env "c" * w ^ n) ≠ 0 := by
    intro w
    simp [rubi312r7Nondeg, Defined, eval, Interp.complex, hkm, hkn, ivm1]
    tauto
  have ht := (hD t).1 hF.self_of_nhds
  have hn0 : n ≠ 0 := by
    intro h
    apply hne
    rw [hn, h]
    norm_num
  have ht0 : t ≠ 0 := by
    intro h
    apply ht.2.2.1
    rw [h, zero_zpow n hn0, mul_zero]
  have hpoint1 : env "c" * t ^ n ≠ 1 := by
    intro h
    apply ht.2.2.2
    rw [h, Complex.log_one]
  have hlin : ContinuousAt (fun u : ℂ => env "c" * u) (t ^ n) := by fun_prop
  have hnear : ∀ᶠ u : ℂ in 𝓝 (t ^ n),
      env "c" * u ≠ 0 ∧ Complex.log (env "c" * u) ≠ 0 := by
    filter_upwards [hlin.tendsto.eventually (eventually_ne_nhds ht.2.2.1),
      hlin.tendsto.eventually (eventually_ne_nhds hpoint1)] with u hu0 hu1
    refine ⟨hu0, ?_⟩
    intro hlog
    apply hu1
    have h := Complex.exp_log hu0
    rw [hlog, Complex.exp_zero] at h
    exact h.symm
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi312r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards [hF] with w hw
      intro g hg
      simp only [rubi312r7Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      have hw' := (hD w).1 hw
      simpa [Defined, eval, Interp.complex, hkn] using hw'.2.1
    · simpa [rubi312r7Nondeg, substAt, List.lookup, Defined, eval, Interp.complex, hkn, ivm1]
        using hnear
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi312r7Nondeg, Defined, eval, Interp.complex, substEnv, ivm1, hne]
    · simp only [rubi312r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1") (Complex.log (env "c" * t ^ n))⁻¹ (t ^ n) := by
        simpa [rubi312r7Nondeg, substAt, List.lookup, eval, Interp.complex, hkn, ivm1] using hΦ
      have hG : HasDerivAt (fun w : ℂ => w ^ n) ((n : ℂ) * t ^ (n - 1)) t :=
        hasDerivAt_zpow n t (Or.inl ht0)
      have h := (hΦ'.comp t hG).const_mul (env "n")⁻¹
      have hfun : (fun w => eval Interp.complex
          (substEnv Interp.complex env (rubi312r7Nondeg.integrals.map (·.1))
            rubi312r7Nondeg.substs Φ "x" w) rubi312r7Nondeg.result) =
          fun w => (env "n")⁻¹ * Φ "I1" (w ^ n) := by
        funext w
        simp [rubi312r7Nondeg, substEnv, substAt, List.lookup, eval, Interp.complex, hkn, ivm1]
      rw [hfun]
      apply h.congr_deriv
      simp [rubi312r7Nondeg, eval, Interp.complex, hkm, hkn, ivm1]
      rw [hn] at hne ⊢
      rw [hmn]
      field_simp [hne]

end OSR.IntegrationRec209
