import OSR.IntegrationNum1
import OSR.IntegrationRec7

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, twenty-sixth batch

Proofs over ℝ of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 3.1.3 #10, 3.1.4 #13
and 3.1.5 #9, integrations by parts with `(d + e x²)^q` and `q < -1`, from
`2 (q + 1) ((d + e x²) - e x²) = 2 (q + 1) d`.  The proofs use the real
logarithm; the complex domain stays unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec74

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








/-- **3.1.3 #10** with `2 d (q + 1) ≠ 0` and `q < -1`, over ℝ: `2 (q + 1) ((d + e x²) - e x²) = 2 (q + 1) d`. -/
theorem rubi313r10Nondeg_real : rubi313r10Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi313r10Nondeg.conditions rubi313r10Nondeg.body
    rubi313r10Nondeg.result rubi313r10Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hW : (2 * env "d" * (env "q" + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int 0)) (by simp [rubi313r10Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hgq := hc (.gt (.int (-1)) (.var "q")) (by simp [rubi313r10Nondeg])
  rcases hkq : intValue? (env "q") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi313r10Nondeg, Defined, eval, Interp.real, hkq] at h
  have h_q : env "q" = (l : ℝ) := (intValue?_eq _ _).1 hkq
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi313r10Nondeg, Defined, eval, Interp.real, hkq, hkn] at h
  have h_n : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have hl : l < -1 := by
    simp only [Cond.Holds, Defined, eval, Interp.real, true_and] at hgq
    rw [h_q] at hgq; exact_mod_cast hgq
  have e2 : intValue? (env "q" + 1) = some (l + 1) := (intValue?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi313r10Nondeg.body →
      (env "d" + env "e" * w ^ 2) ≠ 0 ∧ (j < 0 → ¬w = 0) ∧ 0 < env "c" * w ^ j := by
    intro w h
    simp [rubi313r10Nondeg, Defined, eval, Interp.real, hkq, hkn, h2] at h
    first | exact ⟨h.1 (by omega), h.2.1, h.2.2⟩ | exact ⟨h.1 (by omega), h.2⟩ | (trace_state; sorry)
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi313r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      obtain ⟨h1, h3, h4⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkn, e2, h2]
      first | exact fun _ => h1 | exact ⟨fun _ => h1, h3, h4⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h3, h4⟩ := hD w hw
    simp [rubi313r10Nondeg, Defined, eval, Interp.real, recEnv, e2, hkn, h2, hm1]
    exact ⟨⟨fun _ => h1, h3, h4⟩, by simpa using hW'⟩
  · simp only [rubi313r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    obtain ⟨hQ0, -, hc0⟩ := hD t hF.self_of_nhds
    have hΦ1' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t ^ 2) ^ (l + 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, e2, h2]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "d" + env "e" * t ^ 2) ^ (l + 1) * (env "a" + env "b" * Real.log (env "c" * t ^ j))) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, e2, hkn, h2]
    have hEF : eval Interp.real (Function.update env "x" t) rubi313r10Nondeg.body = (env "d" + env "e" * t ^ 2) ^ l * (env "a" + env "b" * Real.log (env "c" * t ^ j)) := by
      simp [rubi313r10Nondeg, eval, Interp.real, hkq, hkn, h2]
    set u := (2 * env "d" * (env "q" + 1))⁻¹ with hu_def
    have hU : (2 * env "d" * (env "q" + 1)) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval Interp.real (recEnv env (rubi313r10Nondeg.integrals.map (·.1)) Φ "x" w) rubi313r10Nondeg.result) =
        fun w => -1 * w * (env "d" + env "e" * w ^ 2) ^ (l + 1) * (env "a" + env "b" * Real.log (env "c" * w ^ j)) * u + env "b" * env "n" * u * Φ "I1" w +
          (2 * env "q" + 3) * u * Φ "I2" w := by
      funext w
      simp [rubi313r10Nondeg, eval, Interp.real, recEnv, e2, hkn, h2, hm1, hu_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hQd : HasDerivAt (fun w => (env "d" + env "e" * w ^ 2)) (env "e" * (2 * t)) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (env "e")).const_add (env "d")
      convert this using 1 <;> first | (norm_num; ring1) | ring1 | rfl | (funext w; ring1)
    have hd1 : HasDerivAt (fun w => (env "a" + env "b" * Real.log (env "c" * w ^ j))) (env "b" * ((j : ℝ) / t)) t :=
      ((OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hc0).const_mul _).const_add _
    have hQp := HasDerivAt.comp t (hasDerivAt_zpow (l + 1) _ (Or.inl hQ0)) hQd
    refine ((((((hasDerivAt_id' t).const_mul (-1)).mul hQp).mul hd1).mul_const u).add (hΦ1'.const_mul _) |>.add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, Pi.mul_apply, id]
    rw [zpow_succ_of _ _ (Or.inl hQ0)]
    have htX := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hc0
    generalize (env "d" + env "e" * t ^ 2) ^ l = V
    generalize Real.log (env "c" * t ^ j) = Lg at htX ⊢
    generalize (j : ℝ) / t = X at htX ⊢
    clear_value u
    simp only [h_q, h_n] at hU ⊢
    push_cast
    linear_combination (V * (env "a" + env "b" * Lg)) * hU - (V * (env "d" + env "e" * t ^ 2) * env "b" * u) * htX

/-- **3.1.4 #13** with `2 d f (q + 1) ≠ 0`, `m < 0` and `q < -1`, over ℝ: integration by parts. -/
theorem rubi314r13Nondeg_real : rubi314r13Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi314r13Nondeg.conditions rubi314r13Nondeg.body
    rubi314r13Nondeg.result rubi314r13Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hW1 : (2 * env "d" * env "f" * (env "q" + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.var "f")) (.app2 .add (.var "q") (.int 1))) (.int 0)) (by simp [rubi314r13Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW2 : (2 * env "d" * (env "q" + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int 0)) (by simp [rubi314r13Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hgq := hc (.gt (.int (-1)) (.var "q")) (by simp [rubi314r13Nondeg])
  have hgm := hc (.gt (.int 0) (.var "m")) (by simp [rubi314r13Nondeg])
  rcases hkm : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r13Nondeg, Defined, eval, Interp.real, hkm] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hkm
  rcases hkq : intValue? (env "q") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r13Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  have h_q : env "q" = (l : ℝ) := (intValue?_eq _ _).1 hkq
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r13Nondeg, Defined, eval, Interp.real, hkm, hkq, hkn] at h
  have h_n : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have hl : l < -1 := by
    simp only [Cond.Holds, Defined, eval, Interp.real, true_and] at hgq
    rw [h_q] at hgq; exact_mod_cast hgq
  have hk : k < 0 := by
    simp only [Cond.Holds, Defined, eval, Interp.real, true_and] at hgm
    rw [h_m] at hgm; exact_mod_cast hgm
  have e1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2 : intValue? (env "q" + 1) = some (l + 1) := (intValue?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi314r13Nondeg.body →
      ¬env "f" = 0 ∧ ¬w = 0 ∧ (env "d" + env "e" * w ^ 2) ≠ 0 ∧ (j < 0 → ¬w = 0) ∧ 0 < env "c" * w ^ j := by
    intro w h
    simp [rubi314r13Nondeg, Defined, eval, Interp.real, hkm, hkq, hkn, h2] at h
    first | exact ⟨(h.1.1 hk).1, (h.1.1 hk).2, h.1.2 (by omega), h.2.1, h.2.2⟩ | (trace_state; sorry)
  have hW1' := hW1
  have hW2' := hW2
  simp only [ne_eq, mul_eq_zero, not_or] at hW1' hW2'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi314r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hf, hw0, h1, h3, h4⟩ := hD w hw
    simp [Defined, eval, Interp.real, hkm, hkn, e2, h2]
    first | exact ⟨⟨fun _ => ⟨hf, hw0⟩, fun _ => h1⟩, h3, h4⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨hf, hw0, h1, h3, h4⟩ := hD w hw
    simp [rubi314r13Nondeg, Defined, eval, Interp.real, recEnv, e1, e2, hkn, h2, hm1]
    exact ⟨⟨⟨⟨fun _ => ⟨hf, hw0⟩, fun _ => h1⟩, h3, h4⟩, by simpa using hW1'⟩, by simpa using hW2'⟩
  · simp only [rubi314r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hf0, ht0, hQ0, -, hc0⟩ := hD t hF.self_of_nhds
    have hΦ' : HasDerivAt (Φ "I1") ((env "f" * t) ^ k * (env "d" + env "e" * t ^ 2) ^ (l + 1) * (env "a" * (env "m" + 2 * env "q" + 3) + env "b" * env "n" + env "b" * (env "m" + 2 * env "q" + 3) * Real.log (env "c" * t ^ j))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, e2, hkn, h2]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi314r13Nondeg.body = (env "f" * t) ^ k * (env "d" + env "e" * t ^ 2) ^ l * (env "a" + env "b" * Real.log (env "c" * t ^ j)) := by
      simp [rubi314r13Nondeg, eval, Interp.real, hkm, hkq, hkn, h2]
    set u1 := (2 * env "d" * env "f" * (env "q" + 1))⁻¹ with hu1_def
    set u2 := (2 * env "d" * (env "q" + 1))⁻¹ with hu2_def
    have hU1 : (2 * env "d" * env "f" * (env "q" + 1)) * u1 = 1 := by rw [hu1_def]; exact mul_inv_cancel₀ hW1
    have hU2 : (2 * env "d" * (env "q" + 1)) * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hW2
    have hfun : (fun w => eval Interp.real (recEnv env (rubi314r13Nondeg.integrals.map (·.1)) Φ "x" w) rubi314r13Nondeg.result) =
        fun w => -1 * (env "f" * w) ^ (k + 1) * (env "d" + env "e" * w ^ 2) ^ (l + 1) * (env "a" + env "b" * Real.log (env "c" * w ^ j)) * u1 + u2 * Φ "I1" w := by
      funext w
      simp [rubi314r13Nondeg, eval, Interp.real, recEnv, e1, e2, hkn, h2, hm1, hu1_def, hu2_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hF0 : (env "f" * t) ≠ 0 := mul_ne_zero hf0 ht0
    have hQd : HasDerivAt (fun w => (env "d" + env "e" * w ^ 2)) (env "e" * (2 * t)) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (env "e")).const_add (env "d")
      convert this using 1 <;> first | (norm_num; ring1) | ring1 | rfl | (funext w; ring1)
    have hd1 : HasDerivAt (fun w => (env "a" + env "b" * Real.log (env "c" * w ^ j))) (env "b" * ((j : ℝ) / t)) t :=
      ((OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hc0).const_mul _).const_add _
    have hFd : HasDerivAt (fun w => (env "f" * w) ^ (k + 1)) (((k + 1 : ℤ) : ℝ) * (env "f" * t) ^ (k + 1 - 1) * (env "f" * 1)) t :=
      HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (Or.inl hF0)) ((hasDerivAt_id' t).const_mul (env "f"))
    have hQp := HasDerivAt.comp t (hasDerivAt_zpow (l + 1) _ (Or.inl hQ0)) hQd
    refine (((((hFd.const_mul (-1)).mul hQp).mul hd1).mul_const u1).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, Pi.mul_apply]
    rw [zpow_succ_of _ _ (Or.inl hF0), zpow_succ_of _ _ (Or.inl hQ0)]
    have htX := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hc0
    generalize (env "f" * t) ^ k = P
    generalize (env "d" + env "e" * t ^ 2) ^ l = V
    generalize Real.log (env "c" * t ^ j) = Lg at htX ⊢
    generalize (j : ℝ) / t = X at htX ⊢
    clear_value u1 u2
    simp only [h_m, h_q, h_n] at hU1 hU2 ⊢
    push_cast
    linear_combination (P * V * (env "a" + env "b" * Lg) + (P * V * (env "a" + env "b" * Lg) * (((k : ℝ) + 1) * (env "d" + env "e" * t ^ 2) + 2 * ((l : ℝ) + 1) * env "e" * t ^ 2) + P * V * (env "d" + env "e" * t ^ 2) * env "b" * (j : ℝ)) * env "f" * u1) * hU2 -
      ((P * V * (env "a" + env "b" * Lg) * (((k : ℝ) + 1) * (env "d" + env "e" * t ^ 2) + 2 * ((l : ℝ) + 1) * env "e" * t ^ 2) + P * V * (env "d" + env "e" * t ^ 2) * env "b" * (j : ℝ)) * u2) * hU1 -
      (P * V * (env "d" + env "e" * t ^ 2) * env "b" * u1 * env "f") * htX

/-- **3.1.5 #9** with `2 d f (q + 1) ≠ 0`, `m < 0` and `q < -1`, over ℝ: integration by parts. -/
theorem rubi315r9Nondeg_real : rubi315r9Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi315r9Nondeg.conditions rubi315r9Nondeg.body
    rubi315r9Nondeg.result rubi315r9Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hW1 : (2 * env "d" * env "f" * (env "q" + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.var "f")) (.app2 .add (.var "q") (.int 1))) (.int 0)) (by simp [rubi315r9Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW2 : (2 * env "d" * (env "q" + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int 0)) (by simp [rubi315r9Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hgq := hc (.gt (.int (-1)) (.var "q")) (by simp [rubi315r9Nondeg])
  have hgm := hc (.gt (.int 0) (.var "m")) (by simp [rubi315r9Nondeg])
  rcases hkm : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r9Nondeg, Defined, eval, Interp.real, hkm] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hkm
  rcases hkq : intValue? (env "q") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r9Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  have h_q : env "q" = (l : ℝ) := (intValue?_eq _ _).1 hkq
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r9Nondeg, Defined, eval, Interp.real, hkm, hkq, hkn] at h
  have h_n : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have hl : l < -1 := by
    simp only [Cond.Holds, Defined, eval, Interp.real, true_and] at hgq
    rw [h_q] at hgq; exact_mod_cast hgq
  have hk : k < 0 := by
    simp only [Cond.Holds, Defined, eval, Interp.real, true_and] at hgm
    rw [h_m] at hgm; exact_mod_cast hgm
  have e1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2 : intValue? (env "q" + 1) = some (l + 1) := (intValue?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi315r9Nondeg.body →
      ¬env "f" = 0 ∧ ¬w = 0 ∧ (env "d" + env "e" * w ^ 2) ≠ 0 ∧ (j < 0 → ¬w = 0) ∧ 0 < env "c" * w ^ j := by
    intro w h
    simp [rubi315r9Nondeg, Defined, eval, Interp.real, hkm, hkq, hkn, h2] at h
    first | exact ⟨(h.1.1 hk).1, (h.1.1 hk).2, h.1.2 (by omega), h.2.1, h.2.2⟩ | (trace_state; sorry)
  have hW1' := hW1
  have hW2' := hW2
  simp only [ne_eq, mul_eq_zero, not_or] at hW1' hW2'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi315r9Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hf, hw0, h1, h3, h4⟩ := hD w hw
    simp [Defined, eval, Interp.real, hkm, hkn, e2, h2]
    first | exact ⟨⟨fun _ => ⟨hf, hw0⟩, fun _ => h1⟩, h3, h4⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨hf, hw0, h1, h3, h4⟩ := hD w hw
    simp [rubi315r9Nondeg, Defined, eval, Interp.real, recEnv, e1, e2, hkn, h2, hm1]
    exact ⟨⟨⟨⟨fun _ => ⟨hf, hw0⟩, fun _ => h1⟩, h3, h4⟩, by simpa using hW1'⟩, by simpa using hW2'⟩
  · simp only [rubi315r9Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hf0, ht0, hQ0, -, hc0⟩ := hD t hF.self_of_nhds
    have hΦ' : HasDerivAt (Φ "I1") ((env "f" * t) ^ k * (env "d" + env "e" * t ^ 2) ^ (l + 1) * (env "a" * (env "m" + 2 * env "q" + 3) + env "b" * env "n" + env "b" * (env "m" + 2 * env "q" + 3) * Real.log (env "c" * t ^ j))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, e2, hkn, h2]
      try ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi315r9Nondeg.body = (env "f" * t) ^ k * (env "d" + env "e" * t ^ 2) ^ l * (env "a" + env "b" * Real.log (env "c" * t ^ j)) := by
      simp [rubi315r9Nondeg, eval, Interp.real, hkm, hkq, hkn, h2]
    set u1 := (2 * env "d" * env "f" * (env "q" + 1))⁻¹ with hu1_def
    set u2 := (2 * env "d" * (env "q" + 1))⁻¹ with hu2_def
    have hU1 : (2 * env "d" * env "f" * (env "q" + 1)) * u1 = 1 := by rw [hu1_def]; exact mul_inv_cancel₀ hW1
    have hU2 : (2 * env "d" * (env "q" + 1)) * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hW2
    have hfun : (fun w => eval Interp.real (recEnv env (rubi315r9Nondeg.integrals.map (·.1)) Φ "x" w) rubi315r9Nondeg.result) =
        fun w => -1 * (env "f" * w) ^ (k + 1) * (env "d" + env "e" * w ^ 2) ^ (l + 1) * (env "a" + env "b" * Real.log (env "c" * w ^ j)) * u1 + u2 * Φ "I1" w := by
      funext w
      simp [rubi315r9Nondeg, eval, Interp.real, recEnv, e1, e2, hkn, h2, hm1, hu1_def, hu2_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hF0 : (env "f" * t) ≠ 0 := mul_ne_zero hf0 ht0
    have hQd : HasDerivAt (fun w => (env "d" + env "e" * w ^ 2)) (env "e" * (2 * t)) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (env "e")).const_add (env "d")
      convert this using 1 <;> first | (norm_num; ring1) | ring1 | rfl | (funext w; ring1)
    have hd1 : HasDerivAt (fun w => (env "a" + env "b" * Real.log (env "c" * w ^ j))) (env "b" * ((j : ℝ) / t)) t :=
      ((OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hc0).const_mul _).const_add _
    have hFd : HasDerivAt (fun w => (env "f" * w) ^ (k + 1)) (((k + 1 : ℤ) : ℝ) * (env "f" * t) ^ (k + 1 - 1) * (env "f" * 1)) t :=
      HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (Or.inl hF0)) ((hasDerivAt_id' t).const_mul (env "f"))
    have hQp := HasDerivAt.comp t (hasDerivAt_zpow (l + 1) _ (Or.inl hQ0)) hQd
    refine (((((hFd.const_mul (-1)).mul hQp).mul hd1).mul_const u1).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, Pi.mul_apply]
    rw [zpow_succ_of _ _ (Or.inl hF0), zpow_succ_of _ _ (Or.inl hQ0)]
    have htX := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hc0
    generalize (env "f" * t) ^ k = P
    generalize (env "d" + env "e" * t ^ 2) ^ l = V
    generalize Real.log (env "c" * t ^ j) = Lg at htX ⊢
    generalize (j : ℝ) / t = X at htX ⊢
    clear_value u1 u2
    simp only [h_m, h_q, h_n] at hU1 hU2 ⊢
    push_cast
    linear_combination (P * V * (env "a" + env "b" * Lg) + (P * V * (env "a" + env "b" * Lg) * (((k : ℝ) + 1) * (env "d" + env "e" * t ^ 2) + 2 * ((l : ℝ) + 1) * env "e" * t ^ 2) + P * V * (env "d" + env "e" * t ^ 2) * env "b" * (j : ℝ)) * env "f" * u1) * hU2 -
      ((P * V * (env "a" + env "b" * Lg) * (((k : ℝ) + 1) * (env "d" + env "e" * t ^ 2) + 2 * ((l : ℝ) + 1) * env "e" * t ^ 2) + P * V * (env "d" + env "e" * t ^ 2) * env "b" * (j : ℝ)) * u2) * hU1 -
      (P * V * (env "d" + env "e" * t ^ 2) * env "b" * u1 * env "f") * htX

end Proofs

end OSR.IntegrationRec74
