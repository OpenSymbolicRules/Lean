import OSR.IntegrationNum1
import OSR.IntegrationRec7

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, thirty-sixth batch

Proofs over ℝ of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 3.4 #2, the
reduction of `(a + b log (c (d + e/x)^p))^q` for `q > 0`.  The proofs use the real
logarithm; the complex domain stays unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec84

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








/-- **3.4 #2** with `d ≠ 0` and `q > 0`, over ℝ: `d/dx log (c (d + e/x)^p) = -e p / (x (d x + e))`. -/
theorem rubi34r2Nondeg_real : rubi34r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi34r2Nondeg.conditions rubi34r2Nondeg.body
    rubi34r2Nondeg.result rubi34r2Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hd0 : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi34r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg := hc (.gt (.var "q") (.int 0)) (by simp [rubi34r2Nondeg])
  rcases hkp : intValue? (env "p") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi34r2Nondeg, Defined, eval, Interp.real, hkp, hm1] at h
  rcases hkq : intValue? (env "q") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi34r2Nondeg, Defined, eval, Interp.real, hkp, hkq, hm1] at h
  have h_p : env "p" = (j : ℝ) := (intValue?_eq _ _).1 hkp
  have h_q : env "q" = (q : ℝ) := (intValue?_eq _ _).1 hkq
  have hq : 0 < q := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [h_q] at hg
    have h' : Interp.real.lt ((((0 : ℤ)) : ℚ) : ℝ) ((q : ℚ) : ℝ) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (Interp.real_lt_rat _ _).1 h'
  have hq0 : ¬ q < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have e1 : intValue? (env "q" + -1 * 1) = some (q - 1) := (intValue?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have e1' : intValue? (env "q" + -1) = some (q - 1) := (intValue?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi34r2Nondeg.body →
      (¬w = 0 ∧ (j < 0 → ¬env "d" + env "e" * w⁻¹ = 0)) ∧ 0 < env "c" * (env "d" + env "e" * w⁻¹) ^ j := by
    intro w h
    simp [rubi34r2Nondeg, Defined, eval, Interp.real, hkp, hkq, hm1, hq0] at h
    exact h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi34r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [Defined, eval, Interp.real, hkp, e1, e1', hm1, hq1]
    exact ⟨hD w hw, (hD w hw).1.1⟩
  · filter_upwards [hF] with w hw
    simp [rubi34r2Nondeg, Defined, eval, Interp.real, recEnv, hkp, hkq, hm1, hq0, hd0]
    exact hD w hw
  · simp only [rubi34r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨⟨ht0, -⟩, hpos⟩ := hD t hF.self_of_nhds
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t⁻¹) ^ j)) ^ (q - 1) * t⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkp, e1, e1', hm1]
    have hEF : eval Interp.real (Function.update env "x" t) rubi34r2Nondeg.body = (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t⁻¹) ^ j)) ^ q := by
      simp [rubi34r2Nondeg, eval, Interp.real, hkp, hkq, hm1]
    set di := (env "d")⁻¹ with hdi_def
    have hdd : env "d" * di = 1 := by rw [hdi_def]; exact mul_inv_cancel₀ hd0
    have hfun : (fun w => eval Interp.real (recEnv env (rubi34r2Nondeg.integrals.map (·.1)) Φ "x" w) rubi34r2Nondeg.result) =
        fun w => (env "e" + env "d" * w) * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * w⁻¹) ^ j)) ^ q * di +
          env "b" * env "e" * env "p" * env "q" * di * Φ "I1" w := by
      funext w
      simp [rubi34r2Nondeg, eval, Interp.real, recEnv, hkp, hkq, hm1, hdi_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hB : HasDerivAt (fun w => env "d" + env "e" * w⁻¹) (env "e" * (-(t ^ 2)⁻¹)) t :=
      ((hasDerivAt_inv ht0).const_mul (env "e")).const_add (env "d")
    have hL := (OSR.IntegrationRec7.hasDerivAt_log_monomial (env "c") (env "d" + env "e" * t⁻¹) j hpos).comp t hB
    have hZ := OSR.IntegrationRec7.mul_div_of_log_monomial (env "c") (env "d" + env "e" * t⁻¹) j hpos
    have hA : HasDerivAt (fun w => env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * w⁻¹) ^ j))
        (env "b" * ((j : ℝ) / (env "d" + env "e" * t⁻¹) * (env "e" * (-(t ^ 2)⁻¹)))) t :=
      (hL.const_mul (env "b")).const_add (env "a")
    have hAq := HasDerivAt.comp t (hasDerivAt_zpow q _ (Or.inr (by omega))) hA
    have hlin : HasDerivAt (fun w => env "e" + env "d" * w) (env "d") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "d")).const_add (env "e")
    refine (((hlin.mul hAq).mul_const di).add (hΦ'.const_mul (env "b" * env "e" * env "p" * env "q" * di))).congr_deriv ?_
    simp only [Function.comp_def]
    have hAq1 : (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t⁻¹) ^ j)) ^ q =
        (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t⁻¹) ^ j)) ^ (q - 1) *
          (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t⁻¹) ^ j)) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    have ht2 : (t ^ 2)⁻¹ = t⁻¹ ^ 2 := by rw [inv_pow]
    have hT : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0
    rw [hAq1, ht2]
    generalize (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t⁻¹) ^ j)) ^ (q - 1) = Aq1
    generalize (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t⁻¹) ^ j)) = A
    generalize (j : ℝ) / (env "d" + env "e" * t⁻¹) = Z at hZ ⊢
    generalize t⁻¹ = Ti at hZ hT ⊢
    clear_value di
    simp only [h_p, h_q] at hdd ⊢
    linear_combination (-Aq1 * env "b" * di * (q : ℝ) * (Ti * env "d" * t + Ti * env "e" - env "d")) * hZ +
      (-Aq1 * env "b" * env "d" * di * (q : ℝ) * (-Z * env "d" + (j : ℝ))) * hT + (A * Aq1) * hdd

end Proofs

end OSR.IntegrationRec84
