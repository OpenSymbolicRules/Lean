import OSR.IntegrationNum1
import OSR.IntegrationRec7

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, thirty-fifth batch

Proofs over ℝ of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 4.7.8 #13 and #14,
the reductions of `(e x)^m sin(d (a + b log (c xⁿ)))^p` and of the cosine
analogue for `p > 1`.  The proofs use the real
logarithm; the complex domain stays unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec83

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








/-- **4.7.8 #13** with `b² d² n² p² + (m + 1)² ≠ 0`, `e ≠ 0` and `p > 1`, over ℝ: the
reduction of `(e x)^m sin(d (a + b log (c xⁿ)))^p`. -/
theorem rubi478r13Nondeg_real : rubi478r13Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi478r13Nondeg.conditions rubi478r13Nondeg.body
    rubi478r13Nondeg.result rubi478r13Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hW0 : env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 * env "p" ^ 2 + (env "m" + 1) ^ 2 ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2))) (.int 0)) (by simp [rubi478r13Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, h2] using h
  have hW1 : env "b" ^ 2 * env "d" ^ 2 * env "e" * env "n" ^ 2 * env "p" ^ 2 + env "e" * (env "m" + 1) ^ 2 ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int 0)) (by simp [rubi478r13Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, h2] using h
  have he0 : env "e" ≠ 0 := by
    intro h; apply hW1; rw [h]; ring
  have hg := hc (.gt (.var "p") (.int 1)) (by simp [rubi478r13Nondeg])
  rcases hkm : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi478r13Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi478r13Nondeg, Defined, eval, Interp.real, hkm, hkn] at h
  rcases hkp : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi478r13Nondeg, Defined, eval, Interp.real, hkm, hkn, hkp] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hkm
  have h_n : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have h_p : env "p" = (q : ℝ) := (intValue?_eq _ _).1 hkp
  have hq : 1 < q := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [h_p] at hg
    have h' : Interp.real.lt ((((1 : ℤ)) : ℚ) : ℝ) ((q : ℚ) : ℝ) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (Interp.real_lt_rat _ _).1 h'
  have hq0 : ¬ q < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hq2 : ¬ q - 2 < 0 := by omega
  have e1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ep1 : intValue? (env "p" + -1 * 1) = some (q - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep1' : intValue? (env "p" + -1) = some (q - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep2 : intValue? (env "p" + -1 * 2) = some (q - 2) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep2' : intValue? (env "p" + -2) = some (q - 2) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi478r13Nondeg.body →
      (k < 0 → ¬env "e" * w = 0) ∧ 0 < env "c" * w ^ j := by
    intro w h
    simp [rubi478r13Nondeg, Defined, eval, Interp.real, hkm, hkn, hkp, hq0] at h
    first | exact ⟨h.1, h.2.2⟩ | exact ⟨h.1, h.2.1⟩ | exact ⟨h.1, h.2⟩ | exact ⟨h.1.1, h.1.2.2⟩ | exact ⟨fun hk => mul_ne_zero (h.1 hk).1 (h.1 hk).2, h.2.2⟩
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi478r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hw' := hw
    simp [rubi478r13Nondeg, Defined, eval, Interp.real, hkm, hkn, hkp, hq0] at hw'
    simp [Defined, eval, Interp.real, hkm, hkn, ep2, ep2', hq2]
    first | exact hw' | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have hw' := hw
    simp [rubi478r13Nondeg, Defined, eval, Interp.real, hkm, hkn, hkp, hq0] at hw'
    simp [rubi478r13Nondeg, Defined, eval, Interp.real, recEnv, hkm, hkn, hkp, e1, ep1, ep1', h2, hm1, hq0, hq1]
    obtain ⟨hE, hpos⟩ := hD w hw
    refine ⟨⟨⟨fun h => ?_, fun h hw0 => ?_, hpos⟩, hW1⟩, hW0⟩
    · have h' := hE (by omega)
      exact ⟨fun h0 => h' (by rw [h0]; ring), fun h0 => h' (by rw [h0]; ring)⟩
    · rw [hw0, zero_zpow j (by omega), mul_zero] at hpos
      exact lt_irrefl 0 hpos
  · simp only [rubi478r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hE, hpos⟩ := hD t hF.self_of_nhds
    have hEt : env "e" * t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (hE h)
      · exact Or.inr (by omega)
    have hEt1 : env "e" * t ≠ 0 ∨ 0 ≤ k + 1 := by
      rcases hEt with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" * t) ^ k * Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) ^ (q - 2)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, hkn, ep2, ep2']
    have hEF : eval Interp.real (Function.update env "x" t) rubi478r13Nondeg.body = (env "e" * t) ^ k * Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) ^ q := by
      simp [rubi478r13Nondeg, eval, Interp.real, hkm, hkn, hkp]
    set W1 := (env "b" ^ 2 * env "d" ^ 2 * env "e" * env "n" ^ 2 * env "p" ^ 2 + env "e" * (env "m" + 1) ^ 2)⁻¹ with hW1_def
    set W0 := (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 * env "p" ^ 2 + (env "m" + 1) ^ 2)⁻¹ with hW0_def
    have hU1 : (env "b" ^ 2 * env "d" ^ 2 * env "e" * env "n" ^ 2 * env "p" ^ 2 + env "e" * (env "m" + 1) ^ 2) * W1 = 1 := by rw [hW1_def]; exact mul_inv_cancel₀ hW1
    have hU0 : (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 * env "p" ^ 2 + (env "m" + 1) ^ 2) * W0 = 1 := by rw [hW0_def]; exact mul_inv_cancel₀ hW0
    have hfun : (fun w => eval Interp.real (recEnv env (rubi478r13Nondeg.integrals.map (·.1)) Φ "x" w) rubi478r13Nondeg.result) =
        fun w => (env "m" + 1) * (env "e" * w) ^ (k + 1) * Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * w ^ j))) ^ q * W1 +
          (-1 * env "b" * env "d" * env "n" * env "p") * (env "e" * w) ^ (k + 1) * Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * w ^ j))) * Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * w ^ j))) ^ (q - 1) * W1 +
          env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 * env "p" * (env "p" + -1) * W0 * Φ "I1" w := by
      funext w
      simp [rubi478r13Nondeg, eval, Interp.real, recEnv, hkm, hkn, hkp, e1, ep1, ep1', h2, hm1, hW1_def, hW0_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hlog : HasDerivAt (fun w => Real.log (env "c" * w ^ j)) ((j : ℝ) / t) t :=
      OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hpos
    have hZ : t * ((j : ℝ) / t) = j := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hpos
    have hu : HasDerivAt (fun w => (env "d" * (env "a" + env "b" * Real.log (env "c" * w ^ j)))) (env "d" * (env "b" * ((j : ℝ) / t))) t :=
      ((hlog.const_mul (env "b")).const_add (env "a")).const_mul (env "d")
    have hMd := (Real.hasDerivAt_sin _).comp t hu
    have hNd := (Real.hasDerivAt_cos _).comp t hu
    have hY : HasDerivAt (fun w => (env "e" * w) ^ (k + 1)) (((k + 1 : ℤ) : ℝ) * (env "e" * t) ^ (k + 1 - 1) * (env "e" * 1)) t :=
      HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hEt1) ((hasDerivAt_id' t).const_mul (env "e"))
    have hMq := HasDerivAt.comp t (hasDerivAt_zpow q _ (Or.inr (by omega))) hMd
    have hMq1 := HasDerivAt.comp t (hasDerivAt_zpow (q - 1) _ (Or.inr (by omega))) hMd
    refine (((((hY.const_mul (env "m" + 1)).mul hMq).mul_const W1).add ((((hY.const_mul (-1 * env "b" * env "d" * env "n" * env "p")).mul hNd).mul hMq1).mul_const W1)).add
      (hΦ'.const_mul (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 * env "p" * (env "p" + -1) * W0))).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    have hY1 : (env "e" * t) ^ (k + 1) = (env "e" * t) ^ k * (env "e" * t) := zpow_succ_of _ _ hEt
    have hM0 : Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) ^ q = Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) ^ (q - 2) * Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) * Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), ← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
    have hM1 : Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) ^ (q - 1) = Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) ^ (q - 2) * Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
    rw [show q - 1 - 1 = q - 2 by ring, hY1, hM0, hM1]
    have hpt := Real.sin_sq_add_cos_sq (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j)))
    generalize Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) ^ (q - 2) = R
    generalize Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) = S at hpt ⊢
    generalize Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) = C at hpt ⊢
    generalize (j : ℝ) / t = Z at hZ ⊢
    generalize (env "e" * t) ^ k = Em
    clear_value W1 W0
    simp only [h_m, h_n, h_p] at hU1 hU0 ⊢
    push_cast
    linear_combination (-Em*R*W1*env "b"*env "d"*env "e"*(q : ℝ)*(C^2*env "b"*env "d"*(j : ℝ)*(q : ℝ) - C^2*env "b"*env "d"*(j : ℝ) - C*S*(k : ℝ) - C*S - S^2*env "b"*env "d"*(j : ℝ))) * hZ + (-Em*R*W1*env "b"^2*env "d"^2*env "e"*(j : ℝ)^2*(q : ℝ)*((q : ℝ) - 1)) * hpt + (Em*R*(S^2 + W0*env "b"^2*env "d"^2*(j : ℝ)^2*(q : ℝ) + W0*(k : ℝ)^2 + 2*W0*(k : ℝ) + W0 - 1)) * hU1 + (-Em*R*(W1*env "b"^2*env "d"^2*env "e"*(j : ℝ)^2*(q : ℝ) + W1*env "e"*(k : ℝ)^2 + 2*W1*env "e"*(k : ℝ) + W1*env "e" - 1)) * hU0

/-- **4.7.8 #14** with `b² d² n² p² + (m + 1)² ≠ 0`, `e ≠ 0` and `p > 1`, over ℝ: the
reduction of `(e x)^m cos(d (a + b log (c xⁿ)))^p`. -/
theorem rubi478r14Nondeg_real : rubi478r14Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi478r14Nondeg.conditions rubi478r14Nondeg.body
    rubi478r14Nondeg.result rubi478r14Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hW0 : env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 * env "p" ^ 2 + (env "m" + 1) ^ 2 ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2))) (.int 0)) (by simp [rubi478r14Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, h2] using h
  have hW1 : env "b" ^ 2 * env "d" ^ 2 * env "e" * env "n" ^ 2 * env "p" ^ 2 + env "e" * (env "m" + 1) ^ 2 ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int 0)) (by simp [rubi478r14Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, h2] using h
  have he0 : env "e" ≠ 0 := by
    intro h; apply hW1; rw [h]; ring
  have hg := hc (.gt (.var "p") (.int 1)) (by simp [rubi478r14Nondeg])
  rcases hkm : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi478r14Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi478r14Nondeg, Defined, eval, Interp.real, hkm, hkn] at h
  rcases hkp : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi478r14Nondeg, Defined, eval, Interp.real, hkm, hkn, hkp] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hkm
  have h_n : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have h_p : env "p" = (q : ℝ) := (intValue?_eq _ _).1 hkp
  have hq : 1 < q := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [h_p] at hg
    have h' : Interp.real.lt ((((1 : ℤ)) : ℚ) : ℝ) ((q : ℚ) : ℝ) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (Interp.real_lt_rat _ _).1 h'
  have hq0 : ¬ q < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hq2 : ¬ q - 2 < 0 := by omega
  have e1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ep1 : intValue? (env "p" + -1 * 1) = some (q - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep1' : intValue? (env "p" + -1) = some (q - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep2 : intValue? (env "p" + -1 * 2) = some (q - 2) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep2' : intValue? (env "p" + -2) = some (q - 2) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi478r14Nondeg.body →
      (k < 0 → ¬env "e" * w = 0) ∧ 0 < env "c" * w ^ j := by
    intro w h
    simp [rubi478r14Nondeg, Defined, eval, Interp.real, hkm, hkn, hkp, hq0] at h
    first | exact ⟨h.1, h.2.2⟩ | exact ⟨h.1, h.2.1⟩ | exact ⟨h.1, h.2⟩ | exact ⟨h.1.1, h.1.2.2⟩ | exact ⟨fun hk => mul_ne_zero (h.1 hk).1 (h.1 hk).2, h.2.2⟩
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi478r14Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hw' := hw
    simp [rubi478r14Nondeg, Defined, eval, Interp.real, hkm, hkn, hkp, hq0] at hw'
    simp [Defined, eval, Interp.real, hkm, hkn, ep2, ep2', hq2]
    first | exact hw' | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have hw' := hw
    simp [rubi478r14Nondeg, Defined, eval, Interp.real, hkm, hkn, hkp, hq0] at hw'
    simp [rubi478r14Nondeg, Defined, eval, Interp.real, recEnv, hkm, hkn, hkp, e1, ep1, ep1', h2, hm1, hq0, hq1]
    obtain ⟨hE, hpos⟩ := hD w hw
    refine ⟨⟨⟨fun h => ?_, fun h hw0 => ?_, hpos⟩, hW1⟩, hW0⟩
    · have h' := hE (by omega)
      exact ⟨fun h0 => h' (by rw [h0]; ring), fun h0 => h' (by rw [h0]; ring)⟩
    · rw [hw0, zero_zpow j (by omega), mul_zero] at hpos
      exact lt_irrefl 0 hpos
  · simp only [rubi478r14Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hE, hpos⟩ := hD t hF.self_of_nhds
    have hEt : env "e" * t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (hE h)
      · exact Or.inr (by omega)
    have hEt1 : env "e" * t ≠ 0 ∨ 0 ≤ k + 1 := by
      rcases hEt with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" * t) ^ k * Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) ^ (q - 2)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, hkn, ep2, ep2']
    have hEF : eval Interp.real (Function.update env "x" t) rubi478r14Nondeg.body = (env "e" * t) ^ k * Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) ^ q := by
      simp [rubi478r14Nondeg, eval, Interp.real, hkm, hkn, hkp]
    set W1 := (env "b" ^ 2 * env "d" ^ 2 * env "e" * env "n" ^ 2 * env "p" ^ 2 + env "e" * (env "m" + 1) ^ 2)⁻¹ with hW1_def
    set W0 := (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 * env "p" ^ 2 + (env "m" + 1) ^ 2)⁻¹ with hW0_def
    have hU1 : (env "b" ^ 2 * env "d" ^ 2 * env "e" * env "n" ^ 2 * env "p" ^ 2 + env "e" * (env "m" + 1) ^ 2) * W1 = 1 := by rw [hW1_def]; exact mul_inv_cancel₀ hW1
    have hU0 : (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 * env "p" ^ 2 + (env "m" + 1) ^ 2) * W0 = 1 := by rw [hW0_def]; exact mul_inv_cancel₀ hW0
    have hfun : (fun w => eval Interp.real (recEnv env (rubi478r14Nondeg.integrals.map (·.1)) Φ "x" w) rubi478r14Nondeg.result) =
        fun w => (env "m" + 1) * (env "e" * w) ^ (k + 1) * Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * w ^ j))) ^ q * W1 +
          (env "b" * env "d" * env "n" * env "p") * (env "e" * w) ^ (k + 1) * Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * w ^ j))) * Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * w ^ j))) ^ (q - 1) * W1 +
          env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 * env "p" * (env "p" + -1) * W0 * Φ "I1" w := by
      funext w
      simp [rubi478r14Nondeg, eval, Interp.real, recEnv, hkm, hkn, hkp, e1, ep1, ep1', h2, hm1, hW1_def, hW0_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hlog : HasDerivAt (fun w => Real.log (env "c" * w ^ j)) ((j : ℝ) / t) t :=
      OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hpos
    have hZ : t * ((j : ℝ) / t) = j := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hpos
    have hu : HasDerivAt (fun w => (env "d" * (env "a" + env "b" * Real.log (env "c" * w ^ j)))) (env "d" * (env "b" * ((j : ℝ) / t))) t :=
      ((hlog.const_mul (env "b")).const_add (env "a")).const_mul (env "d")
    have hMd := (Real.hasDerivAt_cos _).comp t hu
    have hNd := (Real.hasDerivAt_sin _).comp t hu
    have hY : HasDerivAt (fun w => (env "e" * w) ^ (k + 1)) (((k + 1 : ℤ) : ℝ) * (env "e" * t) ^ (k + 1 - 1) * (env "e" * 1)) t :=
      HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hEt1) ((hasDerivAt_id' t).const_mul (env "e"))
    have hMq := HasDerivAt.comp t (hasDerivAt_zpow q _ (Or.inr (by omega))) hMd
    have hMq1 := HasDerivAt.comp t (hasDerivAt_zpow (q - 1) _ (Or.inr (by omega))) hMd
    refine (((((hY.const_mul (env "m" + 1)).mul hMq).mul_const W1).add ((((hY.const_mul (env "b" * env "d" * env "n" * env "p")).mul hNd).mul hMq1).mul_const W1)).add
      (hΦ'.const_mul (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 * env "p" * (env "p" + -1) * W0))).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    have hY1 : (env "e" * t) ^ (k + 1) = (env "e" * t) ^ k * (env "e" * t) := zpow_succ_of _ _ hEt
    have hM0 : Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) ^ q = Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) ^ (q - 2) * Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) * Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), ← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
    have hM1 : Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) ^ (q - 1) = Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) ^ (q - 2) * Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
    rw [show q - 1 - 1 = q - 2 by ring, hY1, hM0, hM1]
    have hpt := Real.sin_sq_add_cos_sq (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j)))
    generalize Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) ^ (q - 2) = R
    generalize Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) = S at hpt ⊢
    generalize Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) = C at hpt ⊢
    generalize (j : ℝ) / t = Z at hZ ⊢
    generalize (env "e" * t) ^ k = Em
    clear_value W1 W0
    simp only [h_m, h_n, h_p] at hU1 hU0 ⊢
    push_cast
    linear_combination (Em*R*W1*env "b"*env "d"*env "e"*(q : ℝ)*(C^2*env "b"*env "d"*(j : ℝ) - C*S*(k : ℝ) - C*S - S^2*env "b"*env "d"*(j : ℝ)*(q : ℝ) + S^2*env "b"*env "d"*(j : ℝ))) * hZ + (-Em*R*W1*env "b"^2*env "d"^2*env "e"*(j : ℝ)^2*(q : ℝ)*((q : ℝ) - 1)) * hpt + (Em*R*(C^2 + W0*env "b"^2*env "d"^2*(j : ℝ)^2*(q : ℝ) + W0*(k : ℝ)^2 + 2*W0*(k : ℝ) + W0 - 1)) * hU1 + (-Em*R*(W1*env "b"^2*env "d"^2*env "e"*(j : ℝ)^2*(q : ℝ) + W1*env "e"*(k : ℝ)^2 + 2*W1*env "e"*(k : ℝ) + W1*env "e" - 1)) * hU0

end Proofs

end OSR.IntegrationRec83
