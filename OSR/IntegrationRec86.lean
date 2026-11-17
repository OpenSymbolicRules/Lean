import OSR.IntegrationNum1
import OSR.IntegrationRec7

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, thirty-eighth batch

Proofs over ℝ of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 3.3 #22, the
integration by parts of `x^(r-1) (f + g xʳ)^q (a + b log (c (d + e x)ⁿ))^p`
for `p > 0`.  The proofs use the real
logarithm; the complex domain stays unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec86

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








/-- **3.3 #22** with `m = r - 1`, `g r (q + 1) ≠ 0`, `n ≠ 0` and `p > 0`, over ℝ:
`d/dx (f + g xʳ)^(q+1) = (q + 1) g r x^(r-1) (f + g xʳ)^q`. -/
theorem rubi33r22Nondeg_real : rubi33r22Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi33r22Nondeg.conditions rubi33r22Nondeg.body
    rubi33r22Nondeg.result rubi33r22Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hW : env "g" * env "r" * (env "q" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "g") (.var "r")) (.app2 .add (.var "q") (.int 1))) (.int 0)) (by simp [rubi33r22Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hn0 : env "n" ≠ 0 := by
    have h := hc (.ne (.var "n") (.int 0)) (by simp [rubi33r22Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hmr : env "m" = env "r" + -1 * 1 := by
    have h := hc (.eq (.var "m") (.app2 .add (.var "r") (.app2 .mul (.int (-1)) (.int 1)))) (by simp [rubi33r22Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg := hc (.gt (.var "p") (.int 0)) (by simp [rubi33r22Nondeg])
  rcases hkm : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi33r22Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkr : intValue? (env "r") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi33r22Nondeg, Defined, eval, Interp.real, hkm, hkr] at h
  rcases hkq : intValue? (env "q") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi33r22Nondeg, Defined, eval, Interp.real, hkm, hkr, hkq] at h
  rcases hkn : intValue? (env "n") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi33r22Nondeg, Defined, eval, Interp.real, hkm, hkr, hkq, hkn] at h
  rcases hkp : intValue? (env "p") with _ | s
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi33r22Nondeg, Defined, eval, Interp.real, hkm, hkr, hkq, hkn, hkp] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hkm
  have h_r : env "r" = (j : ℝ) := (intValue?_eq _ _).1 hkr
  have h_q : env "q" = (q : ℝ) := (intValue?_eq _ _).1 hkq
  have h_n : env "n" = (i : ℝ) := (intValue?_eq _ _).1 hkn
  have h_p : env "p" = (s : ℝ) := (intValue?_eq _ _).1 hkp
  have hkj : k = j - 1 := by
    have : (k : ℝ) = (j : ℝ) - 1 := by rw [← h_m, ← h_r, hmr]; ring
    exact_mod_cast this
  subst hkj
  have hs : 0 < s := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [h_p] at hg
    have h' : Interp.real.lt ((((0 : ℤ)) : ℚ) : ℝ) ((s : ℚ) : ℝ) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (Interp.real_lt_rat _ _).1 h'
  have hi0 : i ≠ 0 := by
    intro h; apply hn0; rw [h_n, h]; simp
  have hq1 : q + 1 ≠ 0 := by
    intro h; apply hW; rw [h_q, show (q : ℝ) = -1 by exact_mod_cast (by omega : q = -1)]; ring
  have hs0 : ¬ s < 0 := by omega
  have hs1 : ¬ s - 1 < 0 := by omega
  have e1 : intValue? (env "q" + 1) = some (q + 1) := (intValue?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have e2 : intValue? (env "p" + -1 * 1) = some (s - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have e2' : intValue? (env "p" + -1) = some (s - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hBne : ∀ w, 0 < env "c" * (env "d" + env "e" * w) ^ i → env "d" + env "e" * w ≠ 0 := by
    intro w h h0
    rw [h0, zero_zpow i hi0, mul_zero] at h
    exact lt_irrefl 0 h
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi33r22Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi33r22Nondeg, Defined, eval, Interp.real, hkm, hkr, hkq, hkn, hkp, hs0] at hw
    simp [Defined, eval, Interp.real, hkr, hkn, e1, e2, e2', hm1, hs1]
    exact ⟨⟨⟨hw.1.2.1, fun h => hw.1.2.2 (by omega)⟩, hw.2⟩, hBne w hw.2.2⟩
  · filter_upwards [hF] with w hw
    simp [rubi33r22Nondeg, Defined, eval, Interp.real, hkm, hkr, hkq, hkn, hkp, hs0] at hw
    simp [rubi33r22Nondeg, Defined, eval, Interp.real, recEnv, hkr, hkn, hkp, e1, hm1, hs0]
    exact ⟨⟨⟨hw.1.2.1, fun h => hw.1.2.2 (by omega)⟩, hw.2⟩, hW'⟩
  · simp only [rubi33r22Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hw := hF.self_of_nhds
    simp [rubi33r22Nondeg, Defined, eval, Interp.real, hkm, hkr, hkq, hkn, hkp, hs0] at hw
    obtain ⟨⟨-, hj0, hV⟩, -, hpos⟩ := hw
    have hx : t ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (hj0 h)
      · exact Or.inr (by omega)
    have hV0 : (env "f" + env "g" * t ^ j) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (hV h)
      · exact Or.inr (by omega)
    have hV1 : (env "f" + env "g" * t ^ j) ≠ 0 ∨ 0 ≤ q + 1 := by
      rcases hV0 with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") ((env "f" + env "g" * t ^ j) ^ (q + 1) * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) ^ (s - 1) * (env "d" + env "e" * t)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkr, hkn, e1, e2, e2', hm1]
    have hEF : eval Interp.real (Function.update env "x" t) rubi33r22Nondeg.body = t ^ (j - 1) * (env "f" + env "g" * t ^ j) ^ q * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) ^ s := by
      simp [rubi33r22Nondeg, eval, Interp.real, hkm, hkr, hkq, hkn, hkp]
    set Wi := (env "g" * env "r" * (env "q" + 1))⁻¹ with hWi_def
    have hWW : env "g" * env "r" * (env "q" + 1) * Wi = 1 := by rw [hWi_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval Interp.real (recEnv env (rubi33r22Nondeg.integrals.map (·.1)) Φ "x" w) rubi33r22Nondeg.result) =
        fun w => (env "f" + env "g" * w ^ j) ^ (q + 1) * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * w) ^ i)) ^ s * Wi + -1 * env "b" * env "e" * env "n" * env "p" * Wi * Φ "I1" w := by
      funext w
      simp [rubi33r22Nondeg, eval, Interp.real, recEnv, hkr, hkn, hkp, e1, hm1, hWi_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hVd : HasDerivAt (fun w => (env "f" + env "g" * w ^ j)) (env "g" * ((j : ℝ) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t hx).const_mul (env "g")).const_add (env "f")
    have hVq := HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hV1) hVd
    have hBd : HasDerivAt (fun w => env "d" + env "e" * w) (env "e") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
    have hL := (OSR.IntegrationRec7.hasDerivAt_log_monomial (env "c") (env "d" + env "e" * t) i hpos).comp t hBd
    have hΛ := (hL.const_mul (env "b")).const_add (env "a")
    have hΛs := HasDerivAt.comp t (hasDerivAt_zpow s _ (Or.inr (by omega))) hΛ
    refine (((hVq.mul hΛs).mul_const Wi).add (hΦ'.const_mul (-1 * env "b" * env "e" * env "n" * env "p" * Wi))).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hV2 : (env "f" + env "g" * t ^ j) ^ (q + 1) = (env "f" + env "g" * t ^ j) ^ q * (env "f" + env "g" * t ^ j) := zpow_succ_of _ _ hV0
    have hΛ2 : (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) ^ s = (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) ^ (s - 1) * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hV2, hΛ2, div_eq_mul_inv]
    generalize (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) ^ (s - 1) = L1
    generalize (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) = Lv
    generalize (env "f" + env "g" * t ^ j) ^ q = Vq
    generalize t ^ (j - 1) = P
    generalize (env "d" + env "e" * t)⁻¹ = Bi
    clear_value Wi
    simp only [h_r, h_q, h_n, h_p] at hWW ⊢
    push_cast
    linear_combination (Vq * P * L1 * Lv) * hWW

end Proofs

end OSR.IntegrationRec86
