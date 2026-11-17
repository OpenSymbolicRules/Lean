import OSR.IntegrationNum1
import OSR.IntegrationRec7

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, twenty-eighth batch

Proofs over ℝ of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 4.7.8 #47 and #48,
`x^(n-1)` times the sine or cosine of `a xⁿ log (b x)` times `log (b x)`, from
`d/dx (a xⁿ log (b x)) = xⁿ⁻¹ (a n log (b x) + a)`.  The proofs use the real
logarithm; the complex domain stays unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec76

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








/-- **4.7.8 #47** with `a n ≠ 0` and `m = n - 1`, over ℝ: `d/dx (a xⁿ log (b x)) = xⁿ⁻¹ (a n log (b x) + a)`. -/
theorem rubi478r47Nondeg_real : rubi478r47Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi478r47Nondeg.conditions rubi478r47Nondeg.body
    rubi478r47Nondeg.result rubi478r47Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hW : env "a" * env "n" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "a") (.var "n")) (.int 0)) (by simp [rubi478r47Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hn0 : env "n" ≠ 0 := by
    have h := hc (.ne (.var "n") (.int 0)) (by simp [rubi478r47Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hmn : env "m" = env "n" + -1 * 1 := by
    have h := hc (.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (by simp [rubi478r47Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi478r47Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi478r47Nondeg, Defined, eval, Interp.real, hkm, hkn] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hkm
  have h_n : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have hkj : k = j - 1 := by
    have : (k : ℝ) = (j : ℝ) - 1 := by rw [← h_m, ← h_n, hmn]; ring
    exact_mod_cast this
  subst hkj
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi478r47Nondeg.body →
      0 < env "b" * w ∧ (j < 0 → ¬w = 0) := by
    intro w h
    simp [rubi478r47Nondeg, Defined, eval, Interp.real, hkm, hkn] at h
    first | exact ⟨h.2, h.1.2.1⟩ | exact ⟨h.1.2.2, h.1.2.1⟩ | tauto | (trace_state; sorry)
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi478r47Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hw' := hw
    simp [rubi478r47Nondeg, Defined, eval, Interp.real, hkm, hkn] at hw'
    simp [Defined, eval, Interp.real, hkm, hkn]
    first | exact hw'.1 | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hD w hw
    simp [rubi478r47Nondeg, Defined, eval, Interp.real, recEnv, hkn, hm1]
    first | exact ⟨⟨⟨h2, h1⟩, hW'⟩, hn0⟩ | exact ⟨⟨h2, h1⟩, hW', hn0⟩ | tauto | (trace_state; sorry)
  · simp only [rubi478r47Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hb0, -⟩ := hD t hF.self_of_nhds
    have ht0 : t ≠ 0 := by rintro rfl; simp at hb0
    have hΦ' : HasDerivAt (Φ "I1") (t ^ (j - 1) * Real.sin (env "a" * t ^ j * Real.log (env "b" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, hkn]
    have hEF : eval Interp.real (Function.update env "x" t) rubi478r47Nondeg.body = t ^ (j - 1) * Real.sin (env "a" * t ^ j * Real.log (env "b" * t)) * Real.log (env "b" * t) := by
      simp [rubi478r47Nondeg, eval, Interp.real, hkm, hkn]
    set v1 := (env "a" * env "n")⁻¹ with hv1_def
    set ni := (env "n")⁻¹ with hni_def
    have hv : env "a" * env "n" * v1 = 1 := by rw [hv1_def]; exact mul_inv_cancel₀ hW
    have hni : env "n" * ni = 1 := by rw [hni_def]; exact mul_inv_cancel₀ hn0
    have hfun : (fun w => eval Interp.real (recEnv env (rubi478r47Nondeg.integrals.map (·.1)) Φ "x" w) rubi478r47Nondeg.result) =
        fun w => -1 * Real.cos (env "a" * w ^ j * Real.log (env "b" * w)) * v1 + -1 * 1 * ni * Φ "I1" w := by
      funext w
      simp [rubi478r47Nondeg, eval, Interp.real, recEnv, hkn, hm1, hv1_def, hni_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hlog : HasDerivAt (fun w => Real.log (env "b" * w)) (env "b" * 1 / (env "b" * t)) t :=
      ((hasDerivAt_id' t).const_mul (env "b")).log hb0.ne'
    have hu : HasDerivAt (fun w => (env "a" * w ^ j * Real.log (env "b" * w))) (env "a" * ((j : ℝ) * t ^ (j - 1)) * Real.log (env "b" * t) + env "a" * t ^ j * (env "b" * 1 / (env "b" * t))) t :=
      ((hasDerivAt_zpow j t (Or.inl ht0)).const_mul (env "a")).mul hlog
    refine ((((((Real.hasDerivAt_cos _).comp t hu).const_mul (-1)).mul_const v1)).add (hΦ'.const_mul _)).congr_deriv ?_
    try simp only [Function.comp_def]
    generalize (env "a" * t ^ j * Real.log (env "b" * t)) = Uv
    rw [show t ^ j = t ^ (j - 1) * t by rw [← zpow_succ_of _ _ (Or.inl ht0), sub_add_cancel], div_eq_mul_inv]
    have hbt : env "b" * t * (env "b" * t)⁻¹ = 1 := mul_inv_cancel₀ hb0.ne'
    generalize t ^ (j - 1) = R
    generalize (env "b" * t)⁻¹ = Y at hbt ⊢
    generalize Real.log (env "b" * t) = Lg
    clear_value v1 ni
    simp only [h_n] at hv hni ⊢
    linear_combination (Real.sin Uv * R) * ((Lg + ni) * hv + (env "a" * v1) * hbt - (env "a" * v1) * hni)

/-- **4.7.8 #48** with `a n ≠ 0` and `m = n - 1`, over ℝ: `d/dx (a xⁿ log (b x)) = xⁿ⁻¹ (a n log (b x) + a)`. -/
theorem rubi478r48Nondeg_real : rubi478r48Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi478r48Nondeg.conditions rubi478r48Nondeg.body
    rubi478r48Nondeg.result rubi478r48Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hW : env "a" * env "n" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "a") (.var "n")) (.int 0)) (by simp [rubi478r48Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hn0 : env "n" ≠ 0 := by
    have h := hc (.ne (.var "n") (.int 0)) (by simp [rubi478r48Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hmn : env "m" = env "n" + -1 * 1 := by
    have h := hc (.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (by simp [rubi478r48Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi478r48Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi478r48Nondeg, Defined, eval, Interp.real, hkm, hkn] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hkm
  have h_n : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have hkj : k = j - 1 := by
    have : (k : ℝ) = (j : ℝ) - 1 := by rw [← h_m, ← h_n, hmn]; ring
    exact_mod_cast this
  subst hkj
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi478r48Nondeg.body →
      0 < env "b" * w ∧ (j < 0 → ¬w = 0) := by
    intro w h
    simp [rubi478r48Nondeg, Defined, eval, Interp.real, hkm, hkn] at h
    first | exact ⟨h.2, h.1.2.1⟩ | exact ⟨h.1.2.2, h.1.2.1⟩ | tauto | (trace_state; sorry)
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi478r48Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hw' := hw
    simp [rubi478r48Nondeg, Defined, eval, Interp.real, hkm, hkn] at hw'
    simp [Defined, eval, Interp.real, hkm, hkn]
    first | exact hw'.1 | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hD w hw
    simp [rubi478r48Nondeg, Defined, eval, Interp.real, recEnv, hkn, hm1]
    first | exact ⟨⟨⟨h2, h1⟩, hW'⟩, hn0⟩ | exact ⟨⟨h2, h1⟩, hW', hn0⟩ | tauto | (trace_state; sorry)
  · simp only [rubi478r48Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hb0, -⟩ := hD t hF.self_of_nhds
    have ht0 : t ≠ 0 := by rintro rfl; simp at hb0
    have hΦ' : HasDerivAt (Φ "I1") (t ^ (j - 1) * Real.cos (env "a" * t ^ j * Real.log (env "b" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, hkn]
    have hEF : eval Interp.real (Function.update env "x" t) rubi478r48Nondeg.body = t ^ (j - 1) * Real.cos (env "a" * t ^ j * Real.log (env "b" * t)) * Real.log (env "b" * t) := by
      simp [rubi478r48Nondeg, eval, Interp.real, hkm, hkn]
    set v1 := (env "a" * env "n")⁻¹ with hv1_def
    set ni := (env "n")⁻¹ with hni_def
    have hv : env "a" * env "n" * v1 = 1 := by rw [hv1_def]; exact mul_inv_cancel₀ hW
    have hni : env "n" * ni = 1 := by rw [hni_def]; exact mul_inv_cancel₀ hn0
    have hfun : (fun w => eval Interp.real (recEnv env (rubi478r48Nondeg.integrals.map (·.1)) Φ "x" w) rubi478r48Nondeg.result) =
        fun w => Real.sin (env "a" * w ^ j * Real.log (env "b" * w)) * v1 + -1 * 1 * ni * Φ "I1" w := by
      funext w
      simp [rubi478r48Nondeg, eval, Interp.real, recEnv, hkn, hm1, hv1_def, hni_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hlog : HasDerivAt (fun w => Real.log (env "b" * w)) (env "b" * 1 / (env "b" * t)) t :=
      ((hasDerivAt_id' t).const_mul (env "b")).log hb0.ne'
    have hu : HasDerivAt (fun w => (env "a" * w ^ j * Real.log (env "b" * w))) (env "a" * ((j : ℝ) * t ^ (j - 1)) * Real.log (env "b" * t) + env "a" * t ^ j * (env "b" * 1 / (env "b" * t))) t :=
      ((hasDerivAt_zpow j t (Or.inl ht0)).const_mul (env "a")).mul hlog
    refine (((((Real.hasDerivAt_sin _).comp t hu).mul_const v1)).add (hΦ'.const_mul _)).congr_deriv ?_
    try simp only [Function.comp_def]
    generalize (env "a" * t ^ j * Real.log (env "b" * t)) = Uv
    rw [show t ^ j = t ^ (j - 1) * t by rw [← zpow_succ_of _ _ (Or.inl ht0), sub_add_cancel], div_eq_mul_inv]
    have hbt : env "b" * t * (env "b" * t)⁻¹ = 1 := mul_inv_cancel₀ hb0.ne'
    generalize t ^ (j - 1) = R
    generalize (env "b" * t)⁻¹ = Y at hbt ⊢
    generalize Real.log (env "b" * t) = Lg
    clear_value v1 ni
    simp only [h_n] at hv hni ⊢
    linear_combination (Real.cos Uv * R) * ((Lg + ni) * hv + (env "a" * v1) * hbt - (env "a" * v1) * hni)

end Proofs

end OSR.IntegrationRec76
