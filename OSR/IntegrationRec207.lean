import OSR.IntegrationNum1
import OSR.IntegrationRec7

/-! # RUBI 3.1.2 #2: logarithmic substitution -/

namespace OSR.IntegrationRec207

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

theorem rubi312r2Nondeg_real : rubi312r2Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi312r2Nondeg.conditions
    rubi312r2Nondeg.body rubi312r2Nondeg.result rubi312r2Nondeg.integrals
    rubi312r2Nondeg.substs
  intro env hc t hF
  have hbn : env "b" * env "n" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.var "n")) (.int 0))
      (by simp [rubi312r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi312r2Nondeg, Defined, eval, Interp.real, hkn] at h
  rcases hkp : intValue? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi312r2Nondeg, Defined, eval, Interp.real, hkn, hkp] at h
  have hn : env "n" = (n : ℝ) := (intValue?_eq _ _).1 hkn
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi312r2Nondeg.body ↔
      (n < 0 → w ≠ 0) ∧ 0 < env "c" * w ^ n ∧
      (p < 0 → env "a" + env "b" * Real.log (env "c" * w ^ n) ≠ 0) ∧ w ≠ 0 := by
    intro w
    simp [rubi312r2Nondeg, Defined, eval, Interp.real, hkn, hkp, ivm1]
    tauto
  have ht := (hD t).1 hF.self_of_nhds
  have hnear : ∀ᶠ u : ℝ in 𝓝 (env "a" + env "b" * Real.log (env "c" * t ^ n)),
      p < 0 → u ≠ 0 := by
    by_cases hp : p < 0
    · filter_upwards [eventually_ne_nhds (ht.2.2.1 hp)] with u hu
      exact fun _ => hu
    · exact Eventually.of_forall fun _ h => (hp h).elim
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi312r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards [hF] with w hw
      intro g hg
      simp only [rubi312r2Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      have h := (hD w).1 hw
      simpa [Defined, eval, Interp.real, hkn] using ⟨h.1, h.2.1⟩
    · simpa [rubi312r2Nondeg, substAt, List.lookup, Defined, eval, Interp.real, hkn, hkp]
        using hnear
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi312r2Nondeg, Defined, eval, Interp.real, substEnv, ivm1, hbn]
    · simp only [rubi312r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "a" + env "b" * Real.log (env "c" * t ^ n)) ^ p)
          (env "a" + env "b" * Real.log (env "c" * t ^ n)) := by
        simpa [rubi312r2Nondeg, substAt, List.lookup, eval, Interp.real, hkn, hkp] using hΦ
      have hG : HasDerivAt (fun w => env "a" + env "b" * Real.log (env "c" * w ^ n))
          (env "b" * ((n : ℝ) / t)) t :=
        ((OSR.IntegrationRec7.hasDerivAt_log_monomial (env "c") t n ht.2.1).const_mul
          (env "b")).const_add (env "a")
      have h := (hΦ'.comp t hG).const_mul (env "b" * env "n")⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi312r2Nondeg.integrals.map (·.1))
            rubi312r2Nondeg.substs Φ "x" w) rubi312r2Nondeg.result) =
          fun w => (env "b" * env "n")⁻¹ * Φ "I1"
            (env "a" + env "b" * Real.log (env "c" * w ^ n)) := by
        funext w
        simp [rubi312r2Nondeg, substEnv, substAt, List.lookup, eval, Interp.real, hkn, ivm1]
      rw [hfun]
      apply h.congr_deriv
      simp [rubi312r2Nondeg, eval, Interp.real, hkn, hkp, ivm1]
      rw [hn] at hbn ⊢
      have hnb : (n : ℝ) * env "b" ≠ 0 := by simpa [mul_comm] using hbn
      field_simp [hbn, hnb, ht.2.2.2]
      apply (div_eq_iff hnb).2
      ring

end OSR.IntegrationRec207
