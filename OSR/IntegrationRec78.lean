import OSR.IntegrationNum1
import OSR.IntegrationRec7

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, thirtieth batch

Proofs over ℝ of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 3.1.5 #28, the
integration by parts of `(g x)^m (a + b log (c xⁿ))^p (d + e log (f xʳ))^q`.
The proof uses the real logarithm; the complex domain stays unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec78

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








/-- **3.1.5 #28** with `g (m + 1) ≠ 0`, `p > 0` and `q > 0`, over ℝ: integration by parts, from
`x (n/x) = n` and `x (r/x) = r`. -/
theorem rubi315r28Nondeg_real : rubi315r28Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi315r28Nondeg.conditions rubi315r28Nondeg.body
    rubi315r28Nondeg.result rubi315r28Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hW1 : env "g" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "g") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi315r28Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW2 : env "m" + 1 ≠ 0 := by
    have h := hc (.ne (.app2 .add (.var "m") (.int 1)) (.int 0)) (by simp [rubi315r28Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hgp := hc (.gt (.var "p") (.int 0)) (by simp [rubi315r28Nondeg])
  have hgq := hc (.gt (.var "q") (.int 0)) (by simp [rubi315r28Nondeg])
  rcases hkm : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r28Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r28Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  rcases hkq : intValue? (env "q") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r28Nondeg, Defined, eval, Interp.real, hkm, hkp, hkq] at h
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r28Nondeg, Defined, eval, Interp.real, hkm, hkp, hkq, hkn] at h
  rcases hkr : intValue? (env "r") with _ | rr
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r28Nondeg, Defined, eval, Interp.real, hkm, hkp, hkq, hkn, hkr] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hkm
  have h_p : env "p" = (i : ℝ) := (intValue?_eq _ _).1 hkp
  have h_q : env "q" = (l : ℝ) := (intValue?_eq _ _).1 hkq
  have h_n : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have h_r : env "r" = (rr : ℝ) := (intValue?_eq _ _).1 hkr
  have hi : 0 < i := by
    simp only [Cond.Holds, Defined, eval, Interp.real, true_and] at hgp
    rw [h_p] at hgp; exact_mod_cast hgp
  have hl : 0 < l := by
    simp only [Cond.Holds, Defined, eval, Interp.real, true_and] at hgq
    rw [h_q] at hgq; exact_mod_cast hgq
  have e1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2 : intValue? (env "p" + -1 * 1) = some (i - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have e2' : intValue? (env "p" + -1) = some (i - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have e3 : intValue? (env "q" + -1 * 1) = some (l - 1) := (intValue?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have e3' : intValue? (env "q" + -1) = some (l - 1) := (intValue?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi315r28Nondeg.body →
      ((k < 0 → ¬env "g" = 0 ∧ ¬w = 0) ∧
        ((j < 0 → ¬w = 0) ∧ 0 < env "c" * w ^ j) ∧ (i < 0 → ¬(env "a" + env "b" * Real.log (env "c" * w ^ j)) = 0)) ∧
      ((rr < 0 → ¬w = 0) ∧ 0 < env "f" * w ^ rr) ∧ (l < 0 → ¬(env "d" + env "e" * Real.log (env "f" * w ^ rr)) = 0) := by
    intro w h
    simpa [rubi315r28Nondeg, Defined, eval, Interp.real, hkm, hkp, hkq, hkn, hkr] using h
  have hW1' := hW1
  simp only [ne_eq, mul_eq_zero, not_or] at hW1'
  refine ⟨fun i' hi' => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi315r28Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, hkp, hkq, hkn, hkr, e2, e2', e3, e3']
      first
        | exact ⟨⟨h1, h2, h3⟩, h4, fun h => absurd h (by omega)⟩
        | exact ⟨⟨h1, h2, fun h => absurd h (by omega)⟩, h4, h5⟩
        | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := hD w hw
    simp [rubi315r28Nondeg, Defined, eval, Interp.real, recEnv, hkp, hkq, hkn, hkr, e1, hm1]
    first
      | exact ⟨⟨⟨fun h => h1 (by omega), h2, h3⟩, h4, h5⟩, hW1'⟩
      | exact ⟨⟨⟨⟨fun h => h1 (by omega), h2, h3⟩, h4, h5⟩, hW1'⟩, hW2⟩
      | (trace_state; sorry)
  · simp only [rubi315r28Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    obtain ⟨⟨hk0, ⟨-, hc0⟩, -⟩, ⟨-, hf0⟩, -⟩ := hD t hF.self_of_nhds
    have hΦ1' : HasDerivAt (Φ "I1") ((env "g" * t) ^ k * (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ i * (env "d" + env "e" * Real.log (env "f" * t ^ rr)) ^ (l - 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkp, hkn, hkr, e3, e3']
    have hΦ2' : HasDerivAt (Φ "I2") ((env "g" * t) ^ k * (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ (i - 1) * (env "d" + env "e" * Real.log (env "f" * t ^ rr)) ^ l) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, hkq, hkn, hkr, e2, e2']
    have hEF : eval Interp.real (Function.update env "x" t) rubi315r28Nondeg.body = (env "g" * t) ^ k * (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ i * (env "d" + env "e" * Real.log (env "f" * t ^ rr)) ^ l := by
      simp [rubi315r28Nondeg, eval, Interp.real, hkm, hkp, hkq, hkn, hkr]
    set u1 := (env "g" * (env "m" + 1))⁻¹ with hu1_def
    set u2 := (env "m" + 1)⁻¹ with hu2_def
    have hU1 : env "g" * (env "m" + 1) * u1 = 1 := by rw [hu1_def]; exact mul_inv_cancel₀ hW1
    have hU2 : (env "m" + 1) * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hW2
    have hfun : (fun w => eval Interp.real (recEnv env (rubi315r28Nondeg.integrals.map (·.1)) Φ "x" w) rubi315r28Nondeg.result) =
        fun w => (env "g" * w) ^ (k + 1) * (env "a" + env "b" * Real.log (env "c" * w ^ j)) ^ i * (env "d" + env "e" * Real.log (env "f" * w ^ rr)) ^ l * u1 + -1 * env "e" * env "q" * env "r" * u2 * Φ "I1" w +
          -1 * env "b" * env "n" * env "p" * u2 * Φ "I2" w := by
      funext w
      simp [rubi315r28Nondeg, eval, Interp.real, recEnv, hkp, hkq, hkn, hkr, e1, hm1, hu1_def, hu2_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hz : (env "g" * t) ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (mul_ne_zero (hk0 h).1 (hk0 h).2)
      · exact Or.inr (by omega)
    have hz0 : (env "g" * t) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (mul_ne_zero (hk0 h).1 (hk0 h).2)
      · exact Or.inr (by omega)
    have hd1 : HasDerivAt (fun w => (env "a" + env "b" * Real.log (env "c" * w ^ j))) (env "b" * ((j : ℝ) / t)) t :=
      ((OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hc0).const_mul _).const_add _
    have hd2 : HasDerivAt (fun w => (env "d" + env "e" * Real.log (env "f" * w ^ rr))) (env "e" * ((rr : ℝ) / t)) t :=
      ((OSR.IntegrationRec7.hasDerivAt_log_monomial _ t rr hf0).const_mul _).const_add _
    have hGd : HasDerivAt (fun w => (env "g" * w) ^ (k + 1)) (((k + 1 : ℤ) : ℝ) * (env "g" * t) ^ (k + 1 - 1) * (env "g" * 1)) t :=
      HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hz) ((hasDerivAt_id' t).const_mul (env "g"))
    have hAd := (hasDerivAt_zpow i _ (Or.inr hi.le)).comp t hd1
    have hBd := (hasDerivAt_zpow l _ (Or.inr hl.le)).comp t hd2
    refine ((((hGd.mul hAd).mul hBd).mul_const u1).add (hΦ1'.const_mul _) |>.add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, Pi.mul_apply]
    have hAi : (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ i = (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ (i - 1) * (env "a" + env "b" * Real.log (env "c" * t ^ j)) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    have hBl : (env "d" + env "e" * Real.log (env "f" * t ^ rr)) ^ l = (env "d" + env "e" * Real.log (env "f" * t ^ rr)) ^ (l - 1) * (env "d" + env "e" * Real.log (env "f" * t ^ rr)) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [zpow_succ_of _ _ hz0, hAi, hBl]
    have htX1 := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hc0
    have htX2 := OSR.IntegrationRec7.mul_div_of_log_monomial _ t rr hf0
    generalize (env "g" * t) ^ k = P
    generalize (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ (i - 1) = Ya
    generalize (env "d" + env "e" * Real.log (env "f" * t ^ rr)) ^ (l - 1) = Yb
    generalize Real.log (env "c" * t ^ j) = L1 at htX1 ⊢
    generalize Real.log (env "f" * t ^ rr) = L2 at htX2 ⊢
    generalize (j : ℝ) / t = X1 at htX1 ⊢
    generalize (rr : ℝ) / t = X2 at htX2 ⊢
    clear_value u1 u2
    simp only [h_m, h_p, h_q, h_n, h_r] at hU1 hU2 ⊢
    push_cast
    linear_combination
      (P * Ya * (env "a" + env "b" * L1) * Yb * (env "d" + env "e" * L2) +
        (P * Ya * Yb * (env "d" + env "e" * L2) * env "b" * (i : ℝ) * (j : ℝ) +
          P * Ya * (env "a" + env "b" * L1) * Yb * env "e" * (l : ℝ) * (rr : ℝ)) * u2) * hU1 -
      ((P * Ya * Yb * (env "d" + env "e" * L2) * env "b" * (i : ℝ) * (j : ℝ) +
          P * Ya * (env "a" + env "b" * L1) * Yb * env "e" * (l : ℝ) * (rr : ℝ)) * env "g" * u1) * hU2 +
      (P * Ya * Yb * (env "d" + env "e" * L2) * env "b" * (i : ℝ) * env "g" * u1) * htX1 +
      (P * Ya * (env "a" + env "b" * L1) * Yb * env "e" * (l : ℝ) * env "g" * u1) * htX2

end Proofs

end OSR.IntegrationRec78
