import OSR.IntegrationNum1
import OSR.IntegrationRec7

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, twenty-second batch

Proofs over ℝ of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 3.1.4 #12 and 3.1.5
#8, integrations by parts of `(f x)^m (d + e x)^q (a + b log (c xⁿ))`.  The
proofs use the real logarithm; the complex domain stays unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec70

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








/-- **3.1.4 #12** with `e (q + 1) ≠ 0`, `m > 0` and `q < -1`, over ℝ: integration by parts, from `x (n/x) = n`. -/
theorem rubi314r12Nondeg_real : rubi314r12Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi314r12Nondeg.conditions rubi314r12Nondeg.body
    rubi314r12Nondeg.result rubi314r12Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hW : env "e" * (env "q" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "q") (.int 1))) (.int 0)) (by simp [rubi314r12Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hgm := hc (.gt (.var "m") (.int 0)) (by simp [rubi314r12Nondeg])
  have hgq := hc (.gt (.int (-1)) (.var "q")) (by simp [rubi314r12Nondeg])
  rcases hkm : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r12Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "q") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r12Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r12Nondeg, Defined, eval, Interp.real, hkm, hkq, hkn] at h
  have hm : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hkm
  have hq : env "q" = (l : ℝ) := (intValue?_eq _ _).1 hkq
  have hn : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have hk : 0 < k := by
    simp only [Cond.Holds, Defined, eval, Interp.real, true_and] at hgm
    rw [hm] at hgm; exact_mod_cast hgm
  have hl : l < -1 := by
    simp only [Cond.Holds, Defined, eval, Interp.real, true_and] at hgq
    rw [hq] at hgq; exact_mod_cast hgq
  have e1 : intValue? (env "m" + -1 * 1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have e1' : intValue? (env "m" + -1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have e2 : intValue? (env "q" + 1) = some (l + 1) := (intValue?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi314r12Nondeg.body →
      (env "d" + env "e" * w) ≠ 0 ∧ (j < 0 → w ≠ 0) ∧ 0 < env "c" * w ^ j := by
    intro w h
    simp [rubi314r12Nondeg, Defined, eval, Interp.real, hkm, hkq, hkn] at h
    first | exact ⟨h.1.2 (by omega), h.2.1, h.2.2⟩ | exact ⟨h.1.2 (by omega), h.2⟩ | (trace_state; sorry)
  have ht := hD t hF.self_of_nhds
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi314r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3⟩ := hD w hw
    simp [Defined, eval, Interp.real, hkn, e1, e1', e2]
    first
      | exact ⟨⟨fun h => absurd h (by omega), fun _ => h1⟩, h2, h3⟩
      | exact ⟨⟨⟨fun h => absurd h (by omega), fun _ => h1⟩, h2, h3⟩, hW'⟩
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3⟩ := hD w hw
    simp [rubi314r12Nondeg, Defined, eval, Interp.real, recEnv, hkm, hkn, e2, hm1]
    first
      | exact ⟨⟨fun h => absurd h (by omega), fun _ => h1⟩, h2, h3⟩
      | exact ⟨⟨⟨fun h => absurd h (by omega), fun _ => h1⟩, h2, h3⟩, hW'⟩
  · simp only [rubi314r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hD0, -, hc0⟩ := ht
    have hΦ' : HasDerivAt (Φ "I1") ((env "f" * t) ^ (k - 1) * (env "d" + env "e" * t) ^ (l + 1) * (env "a" * env "m" + env "b" * env "n" + env "b" * env "m" * Real.log (env "c" * t ^ j))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkn, e1, e1', e2]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi314r12Nondeg.body = (env "f" * t) ^ k * (env "d" + env "e" * t) ^ l * (env "a" + env "b" * Real.log (env "c" * t ^ j)) := by
      simp [rubi314r12Nondeg, eval, Interp.real, hkm, hkq, hkn]
    set u := (env "e" * (env "q" + 1))⁻¹ with hu_def
    have hU : env "e" * (env "q" + 1) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval Interp.real (recEnv env (rubi314r12Nondeg.integrals.map (·.1)) Φ "x" w) rubi314r12Nondeg.result) =
        fun w => (env "f" * w) ^ k * (env "d" + env "e" * w) ^ (l + 1) * (env "a" + env "b" * Real.log (env "c" * w ^ j)) * u + -1 * env "f" * u * Φ "I1" w := by
      funext w
      simp [rubi314r12Nondeg, eval, Interp.real, recEnv, hkm, hkn, e2, hm1, hu_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hd1 : HasDerivAt (fun w => (env "a" + env "b" * Real.log (env "c" * w ^ j))) (env "b" * ((j : ℝ) / t)) t :=
      ((OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hc0).const_mul _).const_add _
    have hFd : HasDerivAt (fun w => (env "f" * w) ^ k) ((k : ℝ) * (env "f" * t) ^ (k - 1) * (env "f" * 1)) t :=
      HasDerivAt.comp t (hasDerivAt_zpow k _ (Or.inr hk.le)) ((hasDerivAt_id' t).const_mul (env "f"))
    have hlin : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      have := ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
      convert this using 1 <;> first | ring1 | rfl | (funext w; simp only [id])
    have hDd := HasDerivAt.comp t (hasDerivAt_zpow (l + 1) _ (Or.inl hD0)) hlin
    refine ((((hFd.mul hDd).mul hd1).mul_const u).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, Pi.mul_apply]
    have hFk : (env "f" * t) ^ k = (env "f" * t) ^ (k - 1) * (env "f" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hFk, zpow_succ_of _ _ (Or.inl hD0)]
    have htX := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hc0
    generalize (env "f" * t) ^ (k - 1) = Z
    generalize (env "d" + env "e" * t) ^ l = V
    generalize Real.log (env "c" * t ^ j) = Lg at htX ⊢
    generalize (j : ℝ) / t = X at htX ⊢
    clear_value u
    simp only [hm, hq, hn] at hU ⊢
    push_cast
    linear_combination (Z * env "f" * t * V * (env "a" + env "b" * Lg)) * hU + (Z * env "f" * V * (env "d" + env "e" * t) * env "b" * u) * htX

/-- **3.1.5 #8** with `e (q + 1) ≠ 0`, `m > 0` and `q < -1`, over ℝ: integration by parts, from `x (n/x) = n`. -/
theorem rubi315r8Nondeg_real : rubi315r8Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi315r8Nondeg.conditions rubi315r8Nondeg.body
    rubi315r8Nondeg.result rubi315r8Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hW : env "e" * (env "q" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "q") (.int 1))) (.int 0)) (by simp [rubi315r8Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hgm := hc (.gt (.var "m") (.int 0)) (by simp [rubi315r8Nondeg])
  have hgq := hc (.gt (.int (-1)) (.var "q")) (by simp [rubi315r8Nondeg])
  rcases hkm : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r8Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "q") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r8Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r8Nondeg, Defined, eval, Interp.real, hkm, hkq, hkn] at h
  have hm : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hkm
  have hq : env "q" = (l : ℝ) := (intValue?_eq _ _).1 hkq
  have hn : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have hk : 0 < k := by
    simp only [Cond.Holds, Defined, eval, Interp.real, true_and] at hgm
    rw [hm] at hgm; exact_mod_cast hgm
  have hl : l < -1 := by
    simp only [Cond.Holds, Defined, eval, Interp.real, true_and] at hgq
    rw [hq] at hgq; exact_mod_cast hgq
  have e1 : intValue? (env "m" + -1 * 1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have e1' : intValue? (env "m" + -1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have e2 : intValue? (env "q" + 1) = some (l + 1) := (intValue?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi315r8Nondeg.body →
      (env "d" + env "e" * w) ≠ 0 ∧ (j < 0 → w ≠ 0) ∧ 0 < env "c" * w ^ j := by
    intro w h
    simp [rubi315r8Nondeg, Defined, eval, Interp.real, hkm, hkq, hkn] at h
    first | exact ⟨h.1.2 (by omega), h.2.1, h.2.2⟩ | exact ⟨h.1.2 (by omega), h.2⟩ | (trace_state; sorry)
  have ht := hD t hF.self_of_nhds
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi315r8Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3⟩ := hD w hw
    simp [Defined, eval, Interp.real, hkn, e1, e1', e2]
    first
      | exact ⟨⟨fun h => absurd h (by omega), fun _ => h1⟩, h2, h3⟩
      | exact ⟨⟨⟨fun h => absurd h (by omega), fun _ => h1⟩, h2, h3⟩, hW'⟩
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3⟩ := hD w hw
    simp [rubi315r8Nondeg, Defined, eval, Interp.real, recEnv, hkm, hkn, e2, hm1]
    first
      | exact ⟨⟨fun h => absurd h (by omega), fun _ => h1⟩, h2, h3⟩
      | exact ⟨⟨⟨fun h => absurd h (by omega), fun _ => h1⟩, h2, h3⟩, hW'⟩
  · simp only [rubi315r8Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hD0, -, hc0⟩ := ht
    have hΦ' : HasDerivAt (Φ "I1") ((env "f" * t) ^ (k - 1) * (env "d" + env "e" * t) ^ (l + 1) * (env "a" * env "m" + env "b" * env "n" + env "b" * env "m" * Real.log (env "c" * t ^ j))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkn, e1, e1', e2]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi315r8Nondeg.body = (env "f" * t) ^ k * (env "d" + env "e" * t) ^ l * (env "a" + env "b" * Real.log (env "c" * t ^ j)) := by
      simp [rubi315r8Nondeg, eval, Interp.real, hkm, hkq, hkn]
    set u := (env "e" * (env "q" + 1))⁻¹ with hu_def
    have hU : env "e" * (env "q" + 1) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval Interp.real (recEnv env (rubi315r8Nondeg.integrals.map (·.1)) Φ "x" w) rubi315r8Nondeg.result) =
        fun w => (env "f" * w) ^ k * (env "d" + env "e" * w) ^ (l + 1) * (env "a" + env "b" * Real.log (env "c" * w ^ j)) * u + -1 * env "f" * u * Φ "I1" w := by
      funext w
      simp [rubi315r8Nondeg, eval, Interp.real, recEnv, hkm, hkn, e2, hm1, hu_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hd1 : HasDerivAt (fun w => (env "a" + env "b" * Real.log (env "c" * w ^ j))) (env "b" * ((j : ℝ) / t)) t :=
      ((OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hc0).const_mul _).const_add _
    have hFd : HasDerivAt (fun w => (env "f" * w) ^ k) ((k : ℝ) * (env "f" * t) ^ (k - 1) * (env "f" * 1)) t :=
      HasDerivAt.comp t (hasDerivAt_zpow k _ (Or.inr hk.le)) ((hasDerivAt_id' t).const_mul (env "f"))
    have hlin : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      have := ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
      convert this using 1 <;> first | ring1 | rfl | (funext w; simp only [id])
    have hDd := HasDerivAt.comp t (hasDerivAt_zpow (l + 1) _ (Or.inl hD0)) hlin
    refine ((((hFd.mul hDd).mul hd1).mul_const u).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, Pi.mul_apply]
    have hFk : (env "f" * t) ^ k = (env "f" * t) ^ (k - 1) * (env "f" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hFk, zpow_succ_of _ _ (Or.inl hD0)]
    have htX := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hc0
    generalize (env "f" * t) ^ (k - 1) = Z
    generalize (env "d" + env "e" * t) ^ l = V
    generalize Real.log (env "c" * t ^ j) = Lg at htX ⊢
    generalize (j : ℝ) / t = X at htX ⊢
    clear_value u
    simp only [hm, hq, hn] at hU ⊢
    push_cast
    linear_combination (Z * env "f" * t * V * (env "a" + env "b" * Lg)) * hU + (Z * env "f" * V * (env "d" + env "e" * t) * env "b" * u) * htX

end Proofs

end OSR.IntegrationRec70
