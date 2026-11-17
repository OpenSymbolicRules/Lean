import OSR.IntegrationNum1
import OSR.IntegrationRec7

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, twenty-fifth batch

Proofs over ℝ of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 3.1.3 #1, the
integration by parts of `(d + e xʳ)^q (a + b log (c xⁿ))` when
`r (q + 1) + 1 = 0`.  The proof uses the real logarithm; the complex domain
stays unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec73

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








/-- **3.1.3 #1** with `d ≠ 0` and `r (q + 1) + 1 = 0`, over ℝ: integration by parts, from
`(d + e xʳ) + r (q + 1) e xʳ = d` and `x (n/x) = n`. -/
theorem rubi313r1Nondeg_real : rubi313r1Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi313r1Nondeg.conditions rubi313r1Nondeg.body
    rubi313r1Nondeg.result rubi313r1Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hd0 : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi313r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel0 : env "r" * (env "q" + 1) + 1 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "r") (.app2 .add (.var "q") (.int 1))) (.int 1)) (.int 0)) (by simp [rubi313r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkq : intValue? (env "q") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi313r1Nondeg, Defined, eval, Interp.real, hkq] at h
  rcases hkr : intValue? (env "r") with _ | r
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi313r1Nondeg, Defined, eval, Interp.real, hkq, hkr] at h
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi313r1Nondeg, Defined, eval, Interp.real, hkq, hkr, hkn] at h
  have hq : env "q" = (l : ℝ) := (intValue?_eq _ _).1 hkq
  have hr : env "r" = (r : ℝ) := (intValue?_eq _ _).1 hkr
  have hn : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have hrel : (r : ℝ) * ((l : ℝ) + 1) + 1 = 0 := by rw [← hr, ← hq]; exact hrel0
  have e2 : intValue? (env "q" + 1) = some (l + 1) := (intValue?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi313r1Nondeg.body →
      ((r < 0 → ¬w = 0) ∧ (l < 0 → ¬env "d" + env "e" * w ^ r = 0)) ∧
        (j < 0 → ¬w = 0) ∧ 0 < env "c" * w ^ j := by
    intro w h
    simpa [rubi313r1Nondeg, Defined, eval, Interp.real, hkq, hkr, hkn] using h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi313r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hD w hw
    simp [Defined, eval, Interp.real, hkr, e2]
    first | exact ⟨h1, fun h => h2 (by omega)⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hD w hw
    simp [rubi313r1Nondeg, Defined, eval, Interp.real, recEnv, e2, hkr, hkn, hm1]
    first
      | exact ⟨⟨⟨h1, fun h => h2 (by omega)⟩, h3, h4⟩, hd0⟩
      | exact ⟨⟨h1, fun h => h2 (by omega)⟩, ⟨h3, h4⟩, hd0⟩
      | (trace_state; sorry)
  · simp only [rubi313r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨⟨hr0, hl0⟩, -, hc0⟩ := hD t hF.self_of_nhds
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t ^ r) ^ (l + 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkr, e2]
    have hEF : eval Interp.real (Function.update env "x" t) rubi313r1Nondeg.body =
        (env "d" + env "e" * t ^ r) ^ l * (env "a" + env "b" * Real.log (env "c" * t ^ j)) := by
      simp [rubi313r1Nondeg, eval, Interp.real, hkq, hkr, hkn]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi313r1Nondeg.integrals.map (·.1)) Φ "x" w) rubi313r1Nondeg.result) =
        fun w => w * (env "d" + env "e" * w ^ r) ^ (l + 1) * (env "a" + env "b" * Real.log (env "c" * w ^ j)) * (env "d")⁻¹ +
          -1 * env "b" * env "n" * (env "d")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi313r1Nondeg, eval, Interp.real, recEnv, e2, hkr, hkn, hm1]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hx : t ≠ 0 ∨ 0 ≤ r := by
      by_cases h : r < 0
      · exact Or.inl (hr0 h)
      · exact Or.inr (by omega)
    have hDz : env "d" + env "e" * t ^ r ≠ 0 ∨ 0 ≤ l + 1 := by
      by_cases h : l < 0
      · exact Or.inl (hl0 h)
      · exact Or.inr (by omega)
    have hDz0 : env "d" + env "e" * t ^ r ≠ 0 ∨ 0 ≤ l := by
      by_cases h : l < 0
      · exact Or.inl (hl0 h)
      · exact Or.inr (by omega)
    have key : (r : ℝ) * t ^ (r - 1) * t = (r : ℝ) * t ^ r := by
      rcases em (r = 0) with h0 | h0
      · subst h0; simp
      · have h' : t ≠ 0 ∨ 0 ≤ r - 1 := by
          by_cases h : r < 0
          · exact Or.inl (hr0 h)
          · exact Or.inr (by omega)
        rw [show t ^ r = t ^ (r - 1) * t by rw [← zpow_succ_of _ _ h', sub_add_cancel]]
        ring
    have hd1 : HasDerivAt (fun w => env "a" + env "b" * Real.log (env "c" * w ^ j)) (env "b" * ((j : ℝ) / t)) t :=
      ((OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hc0).const_mul _).const_add _
    have hin : HasDerivAt (fun w => env "d" + env "e" * w ^ r) (env "e" * ((r : ℝ) * t ^ (r - 1))) t :=
      ((hasDerivAt_zpow r t hx).const_mul (env "e")).const_add (env "d")
    have hDd := HasDerivAt.comp t (hasDerivAt_zpow (l + 1) _ hDz) hin
    refine (((((hasDerivAt_id' t).mul hDd).mul hd1).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, Pi.mul_apply, id]
    rw [zpow_succ_of _ _ hDz0]
    have htX := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hc0
    have hdd := mul_inv_cancel₀ hd0
    generalize (env "d" + env "e" * t ^ r) ^ l = V
    generalize t ^ (r - 1) = R at key ⊢
    generalize t ^ r = Tr at key ⊢
    generalize Real.log (env "c" * t ^ j) = Lg at htX ⊢
    generalize (j : ℝ) / t = X at htX ⊢
    generalize (env "d")⁻¹ = di at hdd ⊢
    simp only [hq, hn]
    push_cast
    linear_combination V * ((env "a" + env "b" * Lg) * hdd + ((env "a" + env "b" * Lg) * di * env "e" * Tr) * hrel +
      ((env "a" + env "b" * Lg) * ((l : ℝ) + 1) * env "e" * di) * key + ((env "d" + env "e" * Tr) * env "b" * di) * htX)

end Proofs

end OSR.IntegrationRec73
