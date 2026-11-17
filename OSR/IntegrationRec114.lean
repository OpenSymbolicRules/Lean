import OSR.IntegrationRec91
import OSR.IntegrationRec7

/-!
# Integration (RUBI): strengthened variant of 3.4 #7 (integration by parts of `(f x)^m (a + b log(c (d + e xⁿ)^p))`)

The named rule `integration.power_log_binomial` is refuted as stated.  With
`f (m + 1) ≠ 0`, `p ≠ 0` and `n ≠ 0` the integration by parts holds over ℝ: the
integrand's logarithm forces `d + e xⁿ ≠ 0`, and `n ≠ 0` excludes the residual
integrand `x^(n-1) (f x)^(m+1)/(d + e xⁿ)` at `x = 0` when `n = 0`.  Proved
over ℝ only, with the real logarithm.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec114

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- power_log_binomial with NeQ[Multiply[f, Add[m, 1]], 0]; NeQ[p, 0]; NeQ[n, 0] -/
def logBinWeightedNondeg : CRule where
  id := "integration.power_log_binomial_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "p")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "p"))))))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "n")) (.var "p")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.ne (.var "m") (.int (-1)),
    .ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.var "p") (.int 0),
    .ne (.var "n") (.int 0)]
  priority := 9321
  description := "power_log_binomial with NeQ[Multiply[f, Add[m, 1]], 0]; NeQ[p, 0]; NeQ[n, 0]"
  provenance := migrated "rubi:3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p:7" "3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p.m#7"

/-! ## Proofs -/

private theorem zpow_succ_of (A : ℝ) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

theorem logBinWeightedNondeg_real : logBinWeightedNondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" logBinWeightedNondeg.conditions logBinWeightedNondeg.body logBinWeightedNondeg.result logBinWeightedNondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hA0 := hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [logBinWeightedNondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hp0 : env "p" ≠ 0 := by have h := hc (.ne (.var "p") (.int 0)) (by simp [logBinWeightedNondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hn0 : env "n" ≠ 0 := by have h := hc (.ne (.var "n") (.int 0)) (by simp [logBinWeightedNondeg]); simpa [Cond.Holds, Defined, eval] using h
  rcases hk_m : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [logBinWeightedNondeg, Defined, eval, Interp.real, hm1, hk_m, -Real.log_eq_zero] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk_m
  rcases hk_n : intValue? (env "n") with _ | jn
  · exfalso
    have h := hF.self_of_nhds
    simp [logBinWeightedNondeg, Defined, eval, Interp.real, hm1, hk_m, hk_n, -Real.log_eq_zero] at h
  have h_n : env "n" = (jn : ℝ) := (intValue?_eq _ _).1 hk_n
  rcases hk_p : intValue? (env "p") with _ | jp
  · exfalso
    have h := hF.self_of_nhds
    simp [logBinWeightedNondeg, Defined, eval, Interp.real, hm1, hk_m, hk_n, hk_p, -Real.log_eq_zero] at h
  have h_p : env "p" = (jp : ℝ) := (intValue?_eq _ _).1 hk_p
  have em1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have en1 : intValue? (env "n" + -1 * 1) = some (jn - 1) := (intValue?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have en1' : intValue? (env "n" + -1) = some (jn - 1) := (intValue?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have hjp0 : jp ≠ 0 := by intro h; apply hp0; rw [h_p, h]; simp
  have hjn0 : jn ≠ 0 := by intro h; apply hn0; rw [h_n, h]; simp
  have hEne : ∀ w : ℝ, 0 < env "c" * (env "d" + env "e" * w ^ jn) ^ jp → (env "d" + env "e" * w ^ jn) ≠ 0 := by
    intro w h h0; rw [h0, zero_zpow jp hjp0, mul_zero] at h; exact lt_irrefl 0 h
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) logBinWeightedNondeg.body →
      (k < 0 → env "f" ≠ 0 ∧ w ≠ 0) ∧ 0 < env "c" * (env "d" + env "e" * w ^ jn) ^ jp ∧ (jn < 0 → w ≠ 0) := by
    intro w h
    simp [logBinWeightedNondeg, Defined, eval, Interp.real, hk_m, hk_n, hk_p, em1, en1, en1', hm1, -Real.log_eq_zero] at h
    first | tauto | (trace_state; sorry)
  have hw0 : ∀ w, Defined Interp.real (Function.update env "x" w) logBinWeightedNondeg.body → (jn - 1 < 0 → w ≠ 0) := by
    intro w hw h
    obtain ⟨_, _, h3⟩ := hBody w hw
    exact h3 (by omega)
  refine ⟨fun i' hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [logBinWeightedNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3⟩ := hBody w hw
    have h4 := hw0 w hw
    simp [Defined, eval, Interp.real, hk_m, hk_n, hk_p, em1, en1, en1', hm1, -Real.log_eq_zero, hEne w h2]
    exact ⟨⟨fun h => h4 (by omega), fun h => h1 (by omega)⟩, h3⟩
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3⟩ := hBody w hw
    simp [logBinWeightedNondeg, Defined, eval, Interp.real, recEnv, hk_m, hk_n, hk_p, em1, en1, en1', hm1, -Real.log_eq_zero, h2, hA0, hEne w h2]
    exact ⟨fun h => (h1 (by omega)).2, h3⟩
  · simp only [logBinWeightedNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨h1, hp2', h3⟩ := hBody t hF.self_of_nhds
    have hE0 := hEne t hp2'
    have hft : env "f" * t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (mul_ne_zero (h1 h).1 (h1 h).2)
      · exact Or.inr (by omega)
    have hft1 : env "f" * t ≠ 0 ∨ 0 ≤ k + 1 := by
      rcases hft with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have htn : t ≠ 0 ∨ 0 ≤ jn := by
      by_cases h : jn < 0
      · exact Or.inl (h3 h)
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") (t ^ (jn - 1) * (env "f" * t) ^ (k + 1) * (env "d" + env "e" * t ^ jn)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hk_m, hk_n, hk_p, em1, en1, en1', hm1, -Real.log_eq_zero]
    have hEF : eval Interp.real (Function.update env "x" t) logBinWeightedNondeg.body = (env "f" * t) ^ k * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t ^ jn) ^ jp)) := by
      simp [logBinWeightedNondeg, eval, Interp.real, hk_m, hk_n, hk_p, em1, en1, en1', hm1, -Real.log_eq_zero]
    have hfun : (fun w => eval Interp.real (recEnv env (logBinWeightedNondeg.integrals.map (·.1)) Φ "x" w) logBinWeightedNondeg.result) =
        fun w => (env "f" * w) ^ (k + 1) * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * w ^ jn) ^ jp)) * (env "f" * (env "m" + 1))⁻¹ + -1 * env "b" * env "e" * env "n" * env "p" * (env "f" * (env "m" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [logBinWeightedNondeg, eval, Interp.real, recEnv, hk_m, hk_n, hk_p, em1, en1, en1', hm1, -Real.log_eq_zero, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hlin : HasDerivAt (fun w => env "f" * w) (env "f") t := by
      simpa using (hasDerivAt_id t).const_mul (env "f")
    have hFp := HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hft1) hlin
    have hEd : HasDerivAt (fun w => (env "d" + env "e" * w ^ jn)) (env "e" * ((jn : ℝ) * t ^ (jn - 1))) t :=
      ((hasDerivAt_zpow jn t htn).const_mul _).const_add _
    have hL2 := (OSR.IntegrationRec7.hasDerivAt_log_monomial (env "c") (env "d" + env "e" * t ^ jn) jp hp2').comp t hEd
    have hΛ := (hL2.const_mul (env "b")).const_add (env "a")
    refine (((hFp.mul hΛ).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hft]
    generalize (env "f" * t) ^ k = Fk
    generalize t ^ (jn - 1) = Tn
    generalize (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t ^ jn) ^ jp)) = Lm
    simp only [div_eq_mul_inv]
    generalize hEe : (env "d" + env "e" * t ^ jn) = E at hE0 ⊢
    simp only [h_m, h_n, h_p] at *
    try casesm* _ ∧ _
    field_simp
    push_cast
    ring

end OSR.IntegrationRec114
