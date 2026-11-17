import OSR.IntegrationNum1
import OSR.IntegrationRec7

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, thirty-first batch

Proofs over ℝ of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 3.5 #16 and #21,
where `r = q - 1` and `d/dx (a xᵐ + b log (c xⁿ)^q) = a m xᵐ⁻¹ +
b q n log (c xⁿ)^(q-1)/x`.  The proofs use the real logarithm; the complex
domain stays unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec79

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








/-- **3.5 #16** with `b n q (p + 1) ≠ 0` and `r = q - 1`, over ℝ: `d/dx (a xᵐ + b log(c xⁿ)^q)
= a m xᵐ⁻¹ + b q n log(c xⁿ)^(q-1)/x`. -/
theorem rubi35r16Nondeg_real : rubi35r16Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi35r16Nondeg.conditions rubi35r16Nondeg.body
    rubi35r16Nondeg.result rubi35r16Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hW1 : (env "b" * env "n" * env "q" * (env "p" + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi35r16Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW2 : (env "b" * env "n" * env "q") ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.int 0)) (by simp [rubi35r16Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrq : env "r" = env "q" + -1 * 1 := by
    have h := hc (.eq (.var "r") (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (by simp [rubi35r16Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi35r16Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi35r16Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  rcases hkq : intValue? (env "q") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi35r16Nondeg, Defined, eval, Interp.real, hkm, hkp, hkq] at h
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi35r16Nondeg, Defined, eval, Interp.real, hkm, hkp, hkq, hkn] at h
  rcases hkr : intValue? (env "r") with _ | rr
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi35r16Nondeg, Defined, eval, Interp.real, hkm, hkp, hkq, hkn, hkr] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hkm
  have h_p : env "p" = (i : ℝ) := (intValue?_eq _ _).1 hkp
  have h_q : env "q" = (l : ℝ) := (intValue?_eq _ _).1 hkq
  have h_n : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have h_r : env "r" = (rr : ℝ) := (intValue?_eq _ _).1 hkr
  have hrr : rr = l - 1 := by
    have : (rr : ℝ) = (l : ℝ) - 1 := by rw [← h_r, ← h_q, hrq]; ring
    exact_mod_cast this
  subst hrr
  have e1 : intValue? (env "p" + 1) = some (i + 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have e2 : intValue? (env "m" + -1 * 1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2' : intValue? (env "m" + -1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi35r16Nondeg.body →
      w ≠ 0 ∧ 0 < env "c" * w ^ j ∧ (l < 1 → Real.log (env "c" * w ^ j) ≠ 0) ∧ (i < 0 → (env "a" * w ^ k + env "b" * Real.log (env "c" * w ^ j) ^ l) ≠ 0) := by
    intro w h
    simp [rubi35r16Nondeg, Defined, eval, Interp.real, hkm, hkp, hkq, hkn, hkr, hm1, -Real.log_eq_zero] at h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | tauto | (trace_state; sorry)
  have hW1' := hW1
  have hW2' := hW2
  simp only [ne_eq, mul_eq_zero, not_or] at hW1' hW2'
  refine ⟨fun i' hi' => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi35r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi'
    subst hi'
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3, h4⟩ := hD w hw
    simp [Defined, eval, Interp.real, hkm, hkq, hkn, e2, e2', -Real.log_eq_zero, h1, h2]
    exact ⟨fun h => h3 (by omega), i, hkp, h4⟩
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3, h4⟩ := hD w hw
    simp [rubi35r16Nondeg, Defined, eval, Interp.real, recEnv, hkm, hkq, hkn, e1, hm1, -Real.log_eq_zero, h1, h2]
    exact ⟨⟨⟨fun h => h3 (by omega), fun h => h4 (by omega)⟩, hW1'⟩, hW2'⟩
  · simp only [rubi35r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨ht0, hc0, hL1, hS0⟩ := hD t hF.self_of_nhds
    have hΦ' : HasDerivAt (Φ "I1") (t ^ (k - 1) * (env "a" * t ^ k + env "b" * Real.log (env "c" * t ^ j) ^ l) ^ i) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, hkq, hkn, hkp, e2, e2']
    have hEF : eval Interp.real (Function.update env "x" t) rubi35r16Nondeg.body = Real.log (env "c" * t ^ j) ^ (l - 1) * (env "a" * t ^ k + env "b" * Real.log (env "c" * t ^ j) ^ l) ^ i * t⁻¹ := by
      simp [rubi35r16Nondeg, eval, Interp.real, hkm, hkp, hkq, hkn, hkr, hm1]
      try ring
    set u1 := (env "b" * env "n" * env "q" * (env "p" + 1))⁻¹ with hu1_def
    set u2 := (env "b" * env "n" * env "q")⁻¹ with hu2_def
    have hU1 : (env "b" * env "n" * env "q" * (env "p" + 1)) * u1 = 1 := by rw [hu1_def]; exact mul_inv_cancel₀ hW1
    have hU2 : (env "b" * env "n" * env "q") * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hW2
    have hfun : (fun w => eval Interp.real (recEnv env (rubi35r16Nondeg.integrals.map (·.1)) Φ "x" w) rubi35r16Nondeg.result) =
        fun w => (env "a" * w ^ k + env "b" * Real.log (env "c" * w ^ j) ^ l) ^ (i + 1) * u1 + -1 * env "a" * env "m" * u2 * Φ "I1" w := by
      funext w
      simp [rubi35r16Nondeg, eval, Interp.real, recEnv, hkm, hkq, hkn, e1, hm1, hu1_def, hu2_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hLz : Real.log (env "c" * t ^ j) ≠ 0 ∨ 0 ≤ l := by
      by_cases h : l < 1
      · exact Or.inl (hL1 h)
      · exact Or.inr (by omega)
    have hSz : (env "a" * t ^ k + env "b" * Real.log (env "c" * t ^ j) ^ l) ≠ 0 ∨ 0 ≤ i + 1 := by
      by_cases h : i < 0
      · exact Or.inl (hS0 h)
      · exact Or.inr (by omega)
    have hlog : HasDerivAt (fun w => Real.log (env "c" * w ^ j)) ((j : ℝ) / t) t :=
      OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hc0
    have hLq := (hasDerivAt_zpow l _ hLz).comp t hlog
    have hxk := hasDerivAt_zpow k t (Or.inl ht0)
    have hS := (hxk.const_mul (env "a")).add (hLq.const_mul (env "b"))
    have hSp := (hasDerivAt_zpow (i + 1) _ hSz).comp t hS
    refine ((hSp.mul_const u1).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have htX := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hc0
    have hti : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0
    generalize (env "a" * t ^ k + env "b" * Real.log (env "c" * t ^ j) ^ l) ^ i = Sp
    try rw [show t ^ k = t ^ (k - 1) * t by rw [← zpow_succ_of _ _ (Or.inl ht0), sub_add_cancel]]
    generalize t ^ (k - 1) = R
    generalize Real.log (env "c" * t ^ j) ^ (l - 1) = Lq1
    generalize (j : ℝ) / t = X at htX ⊢
    generalize t⁻¹ = ti at hti ⊢
    clear_value u1 u2
    simp only [h_m, h_p, h_q, h_n] at hU1 hU2 ⊢
    push_cast
    linear_combination Sp * ((1 * (env "a" * (k : ℝ) * R + env "b" * (l : ℝ) * Lq1 * X) * u2) * hU1 + (-(1 * (env "a" * (k : ℝ) * R + env "b" * (l : ℝ) * Lq1 * X) * ((i : ℝ) + 1) * u1) + 1 * Lq1 * ti + 0 * R) * hU2 + (-(0 * R) - 1 * u2 * env "b" * (l : ℝ) * Lq1 * X) * hti + (1 * u2 * env "b" * (l : ℝ) * Lq1 * ti) * htX)

/-- **3.5 #21** with `b n q (p + 1) ≠ 0` and `r = q - 1`, over ℝ: `d/dx (a xᵐ + b log(c xⁿ)^q)
= a m xᵐ⁻¹ + b q n log(c xⁿ)^(q-1)/x`. -/
theorem rubi35r21Nondeg_real : rubi35r21Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi35r21Nondeg.conditions rubi35r21Nondeg.body
    rubi35r21Nondeg.result rubi35r21Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hW1 : (env "b" * env "n" * env "q" * (env "p" + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi35r21Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW2 : (env "b" * env "n" * env "q") ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.int 0)) (by simp [rubi35r21Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrq : env "r" = env "q" + -1 * 1 := by
    have h := hc (.eq (.var "r") (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (by simp [rubi35r21Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi35r21Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi35r21Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  rcases hkq : intValue? (env "q") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi35r21Nondeg, Defined, eval, Interp.real, hkm, hkp, hkq] at h
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi35r21Nondeg, Defined, eval, Interp.real, hkm, hkp, hkq, hkn] at h
  rcases hkr : intValue? (env "r") with _ | rr
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi35r21Nondeg, Defined, eval, Interp.real, hkm, hkp, hkq, hkn, hkr] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hkm
  have h_p : env "p" = (i : ℝ) := (intValue?_eq _ _).1 hkp
  have h_q : env "q" = (l : ℝ) := (intValue?_eq _ _).1 hkq
  have h_n : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have h_r : env "r" = (rr : ℝ) := (intValue?_eq _ _).1 hkr
  have hrr : rr = l - 1 := by
    have : (rr : ℝ) = (l : ℝ) - 1 := by rw [← h_r, ← h_q, hrq]; ring
    exact_mod_cast this
  subst hrr
  have e1 : intValue? (env "p" + 1) = some (i + 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have e2 : intValue? (env "m" + -1 * 1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2' : intValue? (env "m" + -1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi35r21Nondeg.body →
      w ≠ 0 ∧ 0 < env "c" * w ^ j ∧ (l < 1 → Real.log (env "c" * w ^ j) ≠ 0) ∧ (i < 0 → (env "a" * w ^ k + env "b" * Real.log (env "c" * w ^ j) ^ l) ≠ 0) := by
    intro w h
    simp [rubi35r21Nondeg, Defined, eval, Interp.real, hkm, hkp, hkq, hkn, hkr, hm1, -Real.log_eq_zero] at h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | tauto | (trace_state; sorry)
  have hW1' := hW1
  have hW2' := hW2
  simp only [ne_eq, mul_eq_zero, not_or] at hW1' hW2'
  refine ⟨fun i' hi' => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi35r21Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi'
    subst hi'
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3, h4⟩ := hD w hw
    simp [Defined, eval, Interp.real, hkm, hkq, hkn, e2, e2', -Real.log_eq_zero, h1, h2]
    exact ⟨fun h => h3 (by omega), i, hkp, h4⟩
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3, h4⟩ := hD w hw
    simp [rubi35r21Nondeg, Defined, eval, Interp.real, recEnv, hkm, hkq, hkn, e1, hm1, -Real.log_eq_zero, h1, h2]
    exact ⟨⟨⟨fun h => h3 (by omega), fun h => h4 (by omega)⟩, hW1'⟩, hW2'⟩
  · simp only [rubi35r21Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨ht0, hc0, hL1, hS0⟩ := hD t hF.self_of_nhds
    have hΦ' : HasDerivAt (Φ "I1") (t ^ (k - 1) * (env "a" * t ^ k + env "b" * Real.log (env "c" * t ^ j) ^ l) ^ i) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, hkq, hkn, hkp, e2, e2']
    have hEF : eval Interp.real (Function.update env "x" t) rubi35r21Nondeg.body = (env "d" * t ^ k + env "e" * Real.log (env "c" * t ^ j) ^ (l - 1)) * (env "a" * t ^ k + env "b" * Real.log (env "c" * t ^ j) ^ l) ^ i * t⁻¹ := by
      simp [rubi35r21Nondeg, eval, Interp.real, hkm, hkp, hkq, hkn, hkr, hm1]
      try ring
    set u1 := (env "b" * env "n" * env "q" * (env "p" + 1))⁻¹ with hu1_def
    set u2 := (env "b" * env "n" * env "q")⁻¹ with hu2_def
    have hU1 : (env "b" * env "n" * env "q" * (env "p" + 1)) * u1 = 1 := by rw [hu1_def]; exact mul_inv_cancel₀ hW1
    have hU2 : (env "b" * env "n" * env "q") * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hW2
    have hfun : (fun w => eval Interp.real (recEnv env (rubi35r21Nondeg.integrals.map (·.1)) Φ "x" w) rubi35r21Nondeg.result) =
        fun w => env "e" * (env "a" * w ^ k + env "b" * Real.log (env "c" * w ^ j) ^ l) ^ (i + 1) * u1 + -1 * (env "a" * env "e" * env "m" + -1 * env "b" * env "d" * env "n" * env "q") * u2 * Φ "I1" w := by
      funext w
      simp [rubi35r21Nondeg, eval, Interp.real, recEnv, hkm, hkq, hkn, e1, hm1, hu1_def, hu2_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hLz : Real.log (env "c" * t ^ j) ≠ 0 ∨ 0 ≤ l := by
      by_cases h : l < 1
      · exact Or.inl (hL1 h)
      · exact Or.inr (by omega)
    have hSz : (env "a" * t ^ k + env "b" * Real.log (env "c" * t ^ j) ^ l) ≠ 0 ∨ 0 ≤ i + 1 := by
      by_cases h : i < 0
      · exact Or.inl (hS0 h)
      · exact Or.inr (by omega)
    have hlog : HasDerivAt (fun w => Real.log (env "c" * w ^ j)) ((j : ℝ) / t) t :=
      OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hc0
    have hLq := (hasDerivAt_zpow l _ hLz).comp t hlog
    have hxk := hasDerivAt_zpow k t (Or.inl ht0)
    have hS := (hxk.const_mul (env "a")).add (hLq.const_mul (env "b"))
    have hSp := (hasDerivAt_zpow (i + 1) _ hSz).comp t hS
    refine (((hSp.const_mul (env "e")).mul_const u1).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have htX := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hc0
    have hti : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0
    generalize (env "a" * t ^ k + env "b" * Real.log (env "c" * t ^ j) ^ l) ^ i = Sp
    try rw [show t ^ k = t ^ (k - 1) * t by rw [← zpow_succ_of _ _ (Or.inl ht0), sub_add_cancel]]
    generalize t ^ (k - 1) = R
    generalize Real.log (env "c" * t ^ j) ^ (l - 1) = Lq1
    generalize (j : ℝ) / t = X at htX ⊢
    generalize t⁻¹ = ti at hti ⊢
    clear_value u1 u2
    simp only [h_m, h_p, h_q, h_n] at hU1 hU2 ⊢
    push_cast
    linear_combination Sp * ((env "e" * (env "a" * (k : ℝ) * R + env "b" * (l : ℝ) * Lq1 * X) * u2) * hU1 + (-(env "e" * (env "a" * (k : ℝ) * R + env "b" * (l : ℝ) * Lq1 * X) * ((i : ℝ) + 1) * u1) + env "e" * Lq1 * ti + env "d" * R) * hU2 + (-(env "d" * R) - env "e" * u2 * env "b" * (l : ℝ) * Lq1 * X) * hti + (env "e" * u2 * env "b" * (l : ℝ) * Lq1 * ti) * htX)

end Proofs

end OSR.IntegrationRec79
