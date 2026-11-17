import OSR.IntegrationNum1
import OSR.IntegrationRec7

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, twenty-third batch

Proofs over ℝ of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 3.1.4 #2 and 3.1.5
#3, integrations by parts of `(f x)^m (d + e xʳ)^q (a + b log (c xⁿ))` when
`m + r (q + 1) + 1 = 0`.  The proofs use the real logarithm; the complex
domain stays unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec71

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








/-- **3.1.4 #2** with `d f (m + 1) ≠ 0` and `m + r (q + 1) + 1 = 0`, over ℝ: integration by parts. -/
theorem rubi314r2Nondeg_real : rubi314r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi314r2Nondeg.conditions rubi314r2Nondeg.body
    rubi314r2Nondeg.result rubi314r2Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hW1 : env "d" * env "f" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi314r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW2 : env "d" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi314r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel0 : env "m" + env "r" * (env "q" + 1) + 1 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "r") (.app2 .add (.var "q") (.int 1)))) (.int 1)) (.int 0)) (by simp [rubi314r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r2Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "q") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r2Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkr : intValue? (env "r") with _ | r
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r2Nondeg, Defined, eval, Interp.real, hkm, hkq, hkr] at h
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r2Nondeg, Defined, eval, Interp.real, hkm, hkq, hkr, hkn] at h
  have hm : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hkm
  have hq : env "q" = (l : ℝ) := (intValue?_eq _ _).1 hkq
  have hr : env "r" = (r : ℝ) := (intValue?_eq _ _).1 hkr
  have hn : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have hrel : (k : ℝ) + (r : ℝ) * ((l : ℝ) + 1) + 1 = 0 := by rw [← hm, ← hr, ← hq]; exact hrel0
  have e1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have e2 : intValue? (env "q" + 1) = some (l + 1) := (intValue?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi314r2Nondeg.body →
      ((k < 0 → ¬env "f" = 0 ∧ ¬w = 0) ∧ (r < 0 → ¬w = 0) ∧ (l < 0 → ¬env "d" + env "e" * w ^ r = 0)) ∧
        (j < 0 → ¬w = 0) ∧ 0 < env "c" * w ^ j := by
    intro w h
    simpa [rubi314r2Nondeg, Defined, eval, Interp.real, hkm, hkq, hkr, hkn] using h
  have hW1' := hW1
  have hW2' := hW2
  simp only [ne_eq, mul_eq_zero, not_or] at hW1' hW2'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi314r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := hD w hw
    simp [Defined, eval, Interp.real, hkm, hkr, e2]
    first | exact ⟨h1, h2, fun h => h3 (by omega)⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := hD w hw
    simp [rubi314r2Nondeg, Defined, eval, Interp.real, recEnv, e1, e2, hkr, hkn, hm1]
    first
      | exact ⟨⟨⟨fun h => h1 (by omega), h2, fun h => h3 (by omega)⟩, h4, h5⟩, hW1', hW2'⟩
      | exact ⟨⟨⟨⟨fun h => h1 (by omega), h2, fun h => h3 (by omega)⟩, h4, h5⟩, hW1'⟩, hW2'⟩
      | (trace_state; sorry)
  · simp only [rubi314r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨⟨hk0, hr0, hl0⟩, -, hc0⟩ := hD t hF.self_of_nhds
    have hΦ' : HasDerivAt (Φ "I1") ((env "f" * t) ^ k * (env "d" + env "e" * t ^ r) ^ (l + 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, hkr, e2]
    have hEF : eval Interp.real (Function.update env "x" t) rubi314r2Nondeg.body = (env "f" * t) ^ k * (env "d" + env "e" * t ^ r) ^ l * (env "a" + env "b" * Real.log (env "c" * t ^ j)) := by
      simp [rubi314r2Nondeg, eval, Interp.real, hkm, hkq, hkr, hkn]
    set u1 := (env "d" * env "f" * (env "m" + 1))⁻¹ with hu1_def
    set u2 := (env "d" * (env "m" + 1))⁻¹ with hu2_def
    have hU1 : env "d" * env "f" * (env "m" + 1) * u1 = 1 := by rw [hu1_def]; exact mul_inv_cancel₀ hW1
    have hU2 : env "d" * (env "m" + 1) * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hW2
    have hfun : (fun w => eval Interp.real (recEnv env (rubi314r2Nondeg.integrals.map (·.1)) Φ "x" w) rubi314r2Nondeg.result) =
        fun w => (env "f" * w) ^ (k + 1) * (env "d" + env "e" * w ^ r) ^ (l + 1) * (env "a" + env "b" * Real.log (env "c" * w ^ j)) * u1 + -1 * env "b" * env "n" * u2 * Φ "I1" w := by
      funext w
      simp [rubi314r2Nondeg, eval, Interp.real, recEnv, e1, e2, hkr, hkn, hm1, hu1_def, hu2_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hz : (env "f" * t) ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (mul_ne_zero (hk0 h).1 (hk0 h).2)
      · exact Or.inr (by omega)
    have hz0 : (env "f" * t) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (mul_ne_zero (hk0 h).1 (hk0 h).2)
      · exact Or.inr (by omega)
    have hx : t ≠ 0 ∨ 0 ≤ r := by
      by_cases h : r < 0
      · exact Or.inl (hr0 h)
      · exact Or.inr (by omega)
    have hDz : (env "d" + env "e" * t ^ r) ≠ 0 ∨ 0 ≤ l + 1 := by
      by_cases h : l < 0
      · exact Or.inl (hl0 h)
      · exact Or.inr (by omega)
    have hDz0 : (env "d" + env "e" * t ^ r) ≠ 0 ∨ 0 ≤ l := by
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
    have hd1 : HasDerivAt (fun w => (env "a" + env "b" * Real.log (env "c" * w ^ j))) (env "b" * ((j : ℝ) / t)) t :=
      ((OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hc0).const_mul _).const_add _
    have hFd : HasDerivAt (fun w => (env "f" * w) ^ (k + 1)) (((k + 1 : ℤ) : ℝ) * (env "f" * t) ^ (k + 1 - 1) * (env "f" * 1)) t :=
      HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hz) ((hasDerivAt_id' t).const_mul (env "f"))
    have hin : HasDerivAt (fun w => (env "d" + env "e" * w ^ r)) (env "e" * ((r : ℝ) * t ^ (r - 1))) t :=
      ((hasDerivAt_zpow r t hx).const_mul (env "e")).const_add (env "d")
    have hDd := HasDerivAt.comp t (hasDerivAt_zpow (l + 1) _ hDz) hin
    refine ((((hFd.mul hDd).mul hd1).mul_const u1).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, Pi.mul_apply]
    rw [zpow_succ_of _ _ hz0, zpow_succ_of _ _ hDz0]
    have htX := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hc0
    generalize (env "f" * t) ^ k = P
    generalize (env "d" + env "e" * t ^ r) ^ l = V
    generalize t ^ (r - 1) = R at key ⊢
    generalize t ^ r = Tr at key ⊢
    generalize Real.log (env "c" * t ^ j) = Lg at htX ⊢
    generalize (j : ℝ) / t = X at htX ⊢
    clear_value u1 u2
    simp only [hm, hq, hn] at hU1 hU2 ⊢
    push_cast
    linear_combination (P * V) * ((env "a" + env "b" * Lg + (env "d" + env "e" * Tr) * env "b" * (j : ℝ) * u2) * hU1 -
      ((env "d" + env "e" * Tr) * env "b" * (j : ℝ) * env "f" * u1) * hU2 +
      ((env "a" + env "b" * Lg) * env "f" * u1 * env "e" * Tr) * hrel +
      ((env "a" + env "b" * Lg) * env "f" * u1 * ((l : ℝ) + 1) * env "e") * key +
      ((env "d" + env "e" * Tr) * env "b" * env "f" * u1) * htX)

/-- **3.1.5 #3** with `d f (m + 1) ≠ 0` and `m + r (q + 1) + 1 = 0`, over ℝ: integration by parts. -/
theorem rubi315r3Nondeg_real : rubi315r3Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi315r3Nondeg.conditions rubi315r3Nondeg.body
    rubi315r3Nondeg.result rubi315r3Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hW1 : env "d" * env "f" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi315r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW2 : env "d" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi315r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel0 : env "m" + env "r" * (env "q" + 1) + 1 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "r") (.app2 .add (.var "q") (.int 1)))) (.int 1)) (.int 0)) (by simp [rubi315r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r3Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "q") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r3Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkr : intValue? (env "r") with _ | r
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r3Nondeg, Defined, eval, Interp.real, hkm, hkq, hkr] at h
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r3Nondeg, Defined, eval, Interp.real, hkm, hkq, hkr, hkn] at h
  have hm : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hkm
  have hq : env "q" = (l : ℝ) := (intValue?_eq _ _).1 hkq
  have hr : env "r" = (r : ℝ) := (intValue?_eq _ _).1 hkr
  have hn : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have hrel : (k : ℝ) + (r : ℝ) * ((l : ℝ) + 1) + 1 = 0 := by rw [← hm, ← hr, ← hq]; exact hrel0
  have e1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have e2 : intValue? (env "q" + 1) = some (l + 1) := (intValue?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi315r3Nondeg.body →
      ((k < 0 → ¬env "f" = 0 ∧ ¬w = 0) ∧ (r < 0 → ¬w = 0) ∧ (l < 0 → ¬env "d" + env "e" * w ^ r = 0)) ∧
        (j < 0 → ¬w = 0) ∧ 0 < env "c" * w ^ j := by
    intro w h
    simpa [rubi315r3Nondeg, Defined, eval, Interp.real, hkm, hkq, hkr, hkn] using h
  have hW1' := hW1
  have hW2' := hW2
  simp only [ne_eq, mul_eq_zero, not_or] at hW1' hW2'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi315r3Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := hD w hw
    simp [Defined, eval, Interp.real, hkm, hkr, e2]
    first | exact ⟨h1, h2, fun h => h3 (by omega)⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := hD w hw
    simp [rubi315r3Nondeg, Defined, eval, Interp.real, recEnv, e1, e2, hkr, hkn, hm1]
    first
      | exact ⟨⟨⟨fun h => h1 (by omega), h2, fun h => h3 (by omega)⟩, h4, h5⟩, hW1', hW2'⟩
      | exact ⟨⟨⟨⟨fun h => h1 (by omega), h2, fun h => h3 (by omega)⟩, h4, h5⟩, hW1'⟩, hW2'⟩
      | (trace_state; sorry)
  · simp only [rubi315r3Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨⟨hk0, hr0, hl0⟩, -, hc0⟩ := hD t hF.self_of_nhds
    have hΦ' : HasDerivAt (Φ "I1") ((env "f" * t) ^ k * (env "d" + env "e" * t ^ r) ^ (l + 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, hkr, e2]
    have hEF : eval Interp.real (Function.update env "x" t) rubi315r3Nondeg.body = (env "f" * t) ^ k * (env "d" + env "e" * t ^ r) ^ l * (env "a" + env "b" * Real.log (env "c" * t ^ j)) := by
      simp [rubi315r3Nondeg, eval, Interp.real, hkm, hkq, hkr, hkn]
    set u1 := (env "d" * env "f" * (env "m" + 1))⁻¹ with hu1_def
    set u2 := (env "d" * (env "m" + 1))⁻¹ with hu2_def
    have hU1 : env "d" * env "f" * (env "m" + 1) * u1 = 1 := by rw [hu1_def]; exact mul_inv_cancel₀ hW1
    have hU2 : env "d" * (env "m" + 1) * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hW2
    have hfun : (fun w => eval Interp.real (recEnv env (rubi315r3Nondeg.integrals.map (·.1)) Φ "x" w) rubi315r3Nondeg.result) =
        fun w => (env "f" * w) ^ (k + 1) * (env "d" + env "e" * w ^ r) ^ (l + 1) * (env "a" + env "b" * Real.log (env "c" * w ^ j)) * u1 + -1 * env "b" * env "n" * u2 * Φ "I1" w := by
      funext w
      simp [rubi315r3Nondeg, eval, Interp.real, recEnv, e1, e2, hkr, hkn, hm1, hu1_def, hu2_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hz : (env "f" * t) ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (mul_ne_zero (hk0 h).1 (hk0 h).2)
      · exact Or.inr (by omega)
    have hz0 : (env "f" * t) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (mul_ne_zero (hk0 h).1 (hk0 h).2)
      · exact Or.inr (by omega)
    have hx : t ≠ 0 ∨ 0 ≤ r := by
      by_cases h : r < 0
      · exact Or.inl (hr0 h)
      · exact Or.inr (by omega)
    have hDz : (env "d" + env "e" * t ^ r) ≠ 0 ∨ 0 ≤ l + 1 := by
      by_cases h : l < 0
      · exact Or.inl (hl0 h)
      · exact Or.inr (by omega)
    have hDz0 : (env "d" + env "e" * t ^ r) ≠ 0 ∨ 0 ≤ l := by
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
    have hd1 : HasDerivAt (fun w => (env "a" + env "b" * Real.log (env "c" * w ^ j))) (env "b" * ((j : ℝ) / t)) t :=
      ((OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hc0).const_mul _).const_add _
    have hFd : HasDerivAt (fun w => (env "f" * w) ^ (k + 1)) (((k + 1 : ℤ) : ℝ) * (env "f" * t) ^ (k + 1 - 1) * (env "f" * 1)) t :=
      HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hz) ((hasDerivAt_id' t).const_mul (env "f"))
    have hin : HasDerivAt (fun w => (env "d" + env "e" * w ^ r)) (env "e" * ((r : ℝ) * t ^ (r - 1))) t :=
      ((hasDerivAt_zpow r t hx).const_mul (env "e")).const_add (env "d")
    have hDd := HasDerivAt.comp t (hasDerivAt_zpow (l + 1) _ hDz) hin
    refine ((((hFd.mul hDd).mul hd1).mul_const u1).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, Pi.mul_apply]
    rw [zpow_succ_of _ _ hz0, zpow_succ_of _ _ hDz0]
    have htX := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hc0
    generalize (env "f" * t) ^ k = P
    generalize (env "d" + env "e" * t ^ r) ^ l = V
    generalize t ^ (r - 1) = R at key ⊢
    generalize t ^ r = Tr at key ⊢
    generalize Real.log (env "c" * t ^ j) = Lg at htX ⊢
    generalize (j : ℝ) / t = X at htX ⊢
    clear_value u1 u2
    simp only [hm, hq, hn] at hU1 hU2 ⊢
    push_cast
    linear_combination (P * V) * ((env "a" + env "b" * Lg + (env "d" + env "e" * Tr) * env "b" * (j : ℝ) * u2) * hU1 -
      ((env "d" + env "e" * Tr) * env "b" * (j : ℝ) * env "f" * u1) * hU2 +
      ((env "a" + env "b" * Lg) * env "f" * u1 * env "e" * Tr) * hrel +
      ((env "a" + env "b" * Lg) * env "f" * u1 * ((l : ℝ) + 1) * env "e") * key +
      ((env "d" + env "e" * Tr) * env "b" * env "f" * u1) * htX)

end Proofs

end OSR.IntegrationRec71
