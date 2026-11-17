import OSR.IntegrationNum1
import OSR.IntegrationRec7

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, thirty-seventh batch

Proofs over ℝ of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 3.2.1 #1, the
reduction of `(A + B log (e ((a + b x)/(c + d x))ⁿ))^p` for `p > 0`.  The proofs use the real
logarithm; the complex domain stays unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec85

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








/-- **3.2.1 #1** with `b c - a d ≠ 0`, `b ≠ 0` and `p > 0`, over ℝ: `d/dx log (e ((a + b x)/(c + d x))ⁿ) = n (b c - a d) / ((a + b x)(c + d x))`. -/
theorem rubi321r1Nondeg_real : rubi321r1Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi321r1Nondeg.conditions rubi321r1Nondeg.body
    rubi321r1Nondeg.result rubi321r1Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hb0 : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi321r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg := hc (.gt (.var "p") (.int 0)) (by simp [rubi321r1Nondeg])
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi321r1Nondeg, Defined, eval, Interp.real, hkn, hm1] at h
  rcases hkp : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi321r1Nondeg, Defined, eval, Interp.real, hkn, hkp, hm1] at h
  have h_n : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have h_p : env "p" = (q : ℝ) := (intValue?_eq _ _).1 hkp
  have hq : 0 < q := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [h_p] at hg
    have h' : Interp.real.lt ((((0 : ℤ)) : ℚ) : ℝ) ((q : ℚ) : ℝ) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (Interp.real_lt_rat _ _).1 h'
  have hq0 : ¬ q < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have e1 : intValue? (env "p" + -1 * 1) = some (q - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have e1' : intValue? (env "p" + -1) = some (q - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi321r1Nondeg.body →
      ¬env "c" + env "d" * w = 0 ∧ 0 < env "e" * ((env "a" + env "b" * w) * (env "c" + env "d" * w)⁻¹) ^ j := by
    intro w h
    simp [rubi321r1Nondeg, Defined, eval, Interp.real, hkn, hkp, hm1, hq0] at h
    first | exact h | exact ⟨h.1, h.2⟩ | exact ⟨h.1.1, h.2⟩ | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi321r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hw' := hw
    simp [rubi321r1Nondeg, Defined, eval, Interp.real, hkn, hkp, hm1, hq0] at hw'
    simp [Defined, eval, Interp.real, hkn, e1, e1', hm1, hq1]
    first | exact ⟨hw', (hD w hw).1⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have hw' := hw
    simp [rubi321r1Nondeg, Defined, eval, Interp.real, hkn, hkp, hm1, hq0] at hw'
    simp [rubi321r1Nondeg, Defined, eval, Interp.real, recEnv, hkn, hkp, hm1, hq0, hb0]
    first | exact hw' | exact ⟨hw', hb0⟩ | (trace_state; sorry)
  · simp only [rubi321r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hc0, hpos⟩ := hD t hF.self_of_nhds
    have hΦ' : HasDerivAt (Φ "I1") ((env "A" + env "B" * Real.log (env "e" * ((env "a" + env "b" * t) * (env "c" + env "d" * t)⁻¹) ^ j)) ^ (q - 1) * (env "c" + env "d" * t)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkn, e1, e1', hm1]
    have hEF : eval Interp.real (Function.update env "x" t) rubi321r1Nondeg.body = (env "A" + env "B" * Real.log (env "e" * ((env "a" + env "b" * t) * (env "c" + env "d" * t)⁻¹) ^ j)) ^ q := by
      simp [rubi321r1Nondeg, eval, Interp.real, hkn, hkp, hm1]
    set bi := (env "b")⁻¹ with hbi_def
    have hbb : env "b" * bi = 1 := by rw [hbi_def]; exact mul_inv_cancel₀ hb0
    have hfun : (fun w => eval Interp.real (recEnv env (rubi321r1Nondeg.integrals.map (·.1)) Φ "x" w) rubi321r1Nondeg.result) =
        fun w => (env "a" + env "b" * w) * (env "A" + env "B" * Real.log (env "e" * ((env "a" + env "b" * w) * (env "c" + env "d" * w)⁻¹) ^ j)) ^ q * bi +
          -1 * env "B" * env "n" * env "p" * (env "b" * env "c" + -1 * env "a" * env "d") * bi * Φ "I1" w := by
      funext w
      simp [rubi321r1Nondeg, eval, Interp.real, recEnv, hkn, hkp, hm1, hbi_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hCd : HasDerivAt (fun w => env "c" + env "d" * w) (env "d") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c")
    have hAd : HasDerivAt (fun w => env "a" + env "b" * w) (env "b") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")
    have hQ : HasDerivAt (fun w => (env "a" + env "b" * w) * (env "c" + env "d" * w)⁻¹)
        (env "b" * (env "c" + env "d" * t)⁻¹ + (env "a" + env "b" * t) * (-env "d" / (env "c" + env "d" * t) ^ 2)) t :=
      hAd.mul (hCd.inv hc0)
    have hL := (OSR.IntegrationRec7.hasDerivAt_log_monomial (env "e") ((env "a" + env "b" * t) * (env "c" + env "d" * t)⁻¹) j hpos).comp t hQ
    have hZ := OSR.IntegrationRec7.mul_div_of_log_monomial (env "e") ((env "a" + env "b" * t) * (env "c" + env "d" * t)⁻¹) j hpos
    have hA := (hL.const_mul (env "B")).const_add (env "A")
    have hAq := HasDerivAt.comp t (hasDerivAt_zpow q _ (Or.inr (by omega))) hA
    refine (((hAd.mul hAq).mul_const bi).add (hΦ'.const_mul (-1 * env "B" * env "n" * env "p" * (env "b" * env "c" + -1 * env "a" * env "d") * bi))).congr_deriv ?_
    simp only [Function.comp_def]
    have hL1 : (env "A" + env "B" * Real.log (env "e" * ((env "a" + env "b" * t) * (env "c" + env "d" * t)⁻¹) ^ j)) ^ q =
        (env "A" + env "B" * Real.log (env "e" * ((env "a" + env "b" * t) * (env "c" + env "d" * t)⁻¹) ^ j)) ^ (q - 1) *
          (env "A" + env "B" * Real.log (env "e" * ((env "a" + env "b" * t) * (env "c" + env "d" * t)⁻¹) ^ j)) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    have hC2 : -env "d" / (env "c" + env "d" * t) ^ 2 = -env "d" * (env "c" + env "d" * t)⁻¹ ^ 2 := by
      rw [div_eq_mul_inv, inv_pow]
    have hCC : (env "c" + env "d" * t) * (env "c" + env "d" * t)⁻¹ = 1 := mul_inv_cancel₀ hc0
    rw [hL1, hC2]
    generalize (env "A" + env "B" * Real.log (env "e" * ((env "a" + env "b" * t) * (env "c" + env "d" * t)⁻¹) ^ j)) ^ (q - 1) = L1
    generalize (env "A" + env "B" * Real.log (env "e" * ((env "a" + env "b" * t) * (env "c" + env "d" * t)⁻¹) ^ j)) = L
    generalize (j : ℝ) / ((env "a" + env "b" * t) * (env "c" + env "d" * t)⁻¹) = Z at hZ ⊢
    generalize (env "c" + env "d" * t)⁻¹ = Ci at hZ hCC ⊢
    clear_value bi
    simp only [h_n, h_p] at hbb ⊢
    linear_combination (-env "B" * L1 * bi * (q : ℝ) * (Ci * env "a" * env "d" + Ci * env "b" * env "d" * t - env "b")) * hZ +
      (-env "B" * L1 * env "b" * bi * (j : ℝ) * (q : ℝ)) * hCC + (L * L1) * hbb

end Proofs

end OSR.IntegrationRec85
