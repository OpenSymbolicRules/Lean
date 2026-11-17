import OSR.IntegrationNum1
import OSR.IntegrationRec7

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, twenty-ninth batch

Proofs over ℝ of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 3.1.2 #3, where
`a (m + 1) = b n` makes `b (d x)^(m+1) log (c xⁿ) / (d (m + 1))` an
antiderivative of `(d x)^m (a + b log (c xⁿ))`.  The proof uses the real
logarithm; the complex domain stays unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec77

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem zpow_succ_of (A : 𝕜) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_four (I : Interp 𝕜) : I.toInt? (4 : 𝕜) = some 4 :=
  (I.toInt?_eq _ _).2 (by simp)








/-- **3.1.2 #3** with `d (m + 1) ≠ 0` and `a (m + 1) = b n`, over ℝ: the derivative of
`b (d x)^(m+1) log (c xⁿ) / (d (m + 1))` is `(d x)^m (b log (c xⁿ) + b n/(m + 1))`. -/
theorem rubi312r3Nondeg_real : rubi312r3Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi312r3Nondeg.conditions rubi312r3Nondeg.body rubi312r3Nondeg.result
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hW : env "d" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi312r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "a" * (env "m" + 1) + -1 * env "b" * env "n" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a") (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n"))) (.int 0)) (by simp [rubi312r3Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  rcases hkm : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi312r3Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi312r3Nondeg, Defined, eval, Interp.real, hkm, hkn] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hkm
  have h_n : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have e1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi312r3Nondeg.body →
      (k < 0 → ¬env "d" = 0 ∧ ¬w = 0) ∧ (j < 0 → ¬w = 0) ∧ 0 < env "c" * w ^ j := by
    intro w h
    simpa [rubi312r3Nondeg, Defined, eval, Interp.real, hkm, hkn] using h
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3⟩ := hD w hw
    simp [rubi312r3Nondeg, Defined, eval, Interp.real, e1, hkn, hm1]
    first
      | exact ⟨⟨fun h => h1 (by omega), h2, h3⟩, hW'⟩
      | exact ⟨⟨⟨fun h => h1 (by omega), h2, h3⟩, hW'⟩, hW'⟩
      | (trace_state; sorry)
  · obtain ⟨hk0, -, hc0⟩ := hD t hF.self_of_nhds
    have hEF : eval Interp.real (Function.update env "x" t) rubi312r3Nondeg.body =
        (env "d" * t) ^ k * (env "a" + env "b" * Real.log (env "c" * t ^ j)) := by
      simp [rubi312r3Nondeg, eval, Interp.real, hkm, hkn]
    set u := (env "d" * (env "m" + 1))⁻¹ with hu_def
    have hU : env "d" * (env "m" + 1) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval Interp.real (Function.update env "x" w) rubi312r3Nondeg.result) =
        fun w => env "b" * (env "d" * w) ^ (k + 1) * Real.log (env "c" * w ^ j) * u := by
      funext w
      simp [rubi312r3Nondeg, eval, Interp.real, e1, hkn, hm1, hu_def]
    rw [hfun, hEF]
    have hz : env "d" * t ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (mul_ne_zero (hk0 h).1 (hk0 h).2)
      · exact Or.inr (by omega)
    have hz0 : env "d" * t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (mul_ne_zero (hk0 h).1 (hk0 h).2)
      · exact Or.inr (by omega)
    have hlog : HasDerivAt (fun w => Real.log (env "c" * w ^ j)) ((j : ℝ) / t) t :=
      OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hc0
    have hP : HasDerivAt (fun w => (env "d" * w) ^ (k + 1)) (((k + 1 : ℤ) : ℝ) * (env "d" * t) ^ (k + 1 - 1) * (env "d" * 1)) t :=
      HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hz) ((hasDerivAt_id' t).const_mul (env "d"))
    refine ((((hP.const_mul (env "b")).mul hlog).mul_const u)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    rw [zpow_succ_of _ _ hz0]
    have htX := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hc0
    generalize (env "d" * t) ^ k = P
    generalize Real.log (env "c" * t ^ j) = Lg
    generalize (j : ℝ) / t = X at htX ⊢
    clear_value u
    simp only [h_m, h_n] at hU hrel ⊢
    push_cast
    linear_combination P * ((env "b" * Lg + env "a") * hU + (env "b" * env "d" * u) * htX - (u * env "d") * hrel)

end Proofs

end OSR.IntegrationRec77
