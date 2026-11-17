import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, forty-first batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 1.2.1.3 #33, the
reduction of `(d + e x)^m (f + g x)(a + c x²)^p` for `c d² + a e² = 0`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec89

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








/-- **1.2.1.3 #33** with `c d² + a e² = 0` and `c (m + 2 p + 2) ≠ 0 ≠ e (m + 2 p + 2)`. -/
theorem rubi1213r33Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1213r33Nondeg.conditions rubi1213r33Nondeg.body rubi1213r33Nondeg.result rubi1213r33Nondeg.integrals := by
  intro env hc t hF
  have heq : env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1213r33Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hc1 : env "c" * (env "m" + 2 * env "p" + 2) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int 0)) (by simp [rubi1213r33Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hc2 : env "e" * (env "m" + 2 * env "p" + 2) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int 0)) (by simp [rubi1213r33Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have he0 : env "e" ≠ 0 := left_ne_zero_of_mul hc2
  rcases hkm : I.toInt? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r33Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r33Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
  have h_m : env "m" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have e1 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1213r33Nondeg.body →
      (j < 0 → ¬(env "d" + env "e" * w) = 0) ∧ (q < 0 → ¬(env "a" + env "c" * w ^ 2) = 0) := by
    intro w h
    simp [rubi1213r33Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    first | exact h | exact ⟨h.1, h.2⟩ | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r33Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [Defined, eval, hkm, hkp, toInt?_two]
    first | exact hBody w hw | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hBody w hw
    have g2 : q + 1 < 0 → ¬(env "a" + env "c" * w ^ 2) = 0 := fun h => h2 (by omega)
    simp [rubi1213r33Nondeg, Defined, eval, recEnv, hkm, hkp, e1, toInt?_two, toInt?_neg_one]
    have hc1' := hc1
    have hc2' := hc2
    simp only [ne_eq, mul_eq_zero, not_or] at hc1' hc2'
    exact ⟨⟨⟨h1, g2⟩, hc1'⟩, hc2'⟩
  · simp only [rubi1213r33Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hB, hQ⟩ := hBody t hF.self_of_nhds
    have hB0 : (env "d" + env "e" * t) ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (hB h)
      · exact Or.inr (by omega)
    have hQ0 : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (hQ h)
      · exact Or.inr (by omega)
    have hQ1 : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q + 1 := by
      rcases hQ0 with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ j * (env "a" + env "c" * t ^ 2) ^ q) t := by
      convert hΦ using 1
      simp [eval, hkm, hkp, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1213r33Nondeg.body = (env "d" + env "e" * t) ^ j * (env "f" + env "g" * t) * (env "a" + env "c" * t ^ 2) ^ q := by
      simp [rubi1213r33Nondeg, eval, hkm, hkp, toInt?_two]
    set W1 := (env "c" * (env "m" + 2 * env "p" + 2))⁻¹ with hW1_def
    set W2 := (env "e" * (env "m" + 2 * env "p" + 2))⁻¹ with hW2_def
    set ei := (env "e")⁻¹ with hei_def
    have hU1 : env "c" * (env "m" + 2 * env "p" + 2) * W1 = 1 := by rw [hW1_def]; exact mul_inv_cancel₀ hc1
    have hU2 : env "e" * (env "m" + 2 * env "p" + 2) * W2 = 1 := by rw [hW2_def]; exact mul_inv_cancel₀ hc2
    have hei : env "e" * ei = 1 := by rw [hei_def]; exact mul_inv_cancel₀ he0
    have hfun : (fun w => eval I (recEnv env (rubi1213r33Nondeg.integrals.map (·.1)) Φ "x" w) rubi1213r33Nondeg.result) =
        fun w => env "g" * (env "d" + env "e" * w) ^ j * (env "a" + env "c" * w ^ 2) ^ (q + 1) * W1 + (env "m" * (env "d" * env "g" + env "e" * env "f") + 2 * env "e" * env "f" * (env "p" + 1)) * W2 * Φ "I1" w := by
      funext w
      simp [rubi1213r33Nondeg, eval, recEnv, hkm, hkp, e1, toInt?_two, toInt?_neg_one, hW1_def, hW2_def, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hBd : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e" * 1) t :=
      ((hasDerivAt_id' t).const_mul _).const_add _
    have hQd : HasDerivAt (fun w => (env "a" + env "c" * w ^ 2)) (env "c" * (2 * t)) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (env "c")).const_add (env "a")
      convert this using 1
      norm_num
    have hBm := HasDerivAt.comp t (hasDerivAt_zpow j _ hB0) hBd
    have hQp := HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hQ1) hQd
    refine ((((hBm.const_mul (env "g")).mul hQp).mul_const W1).add (hΦ'.const_mul ((env "m" * (env "d" * env "g" + env "e" * env "f") + 2 * env "e" * env "f" * (env "p" + 1)) * W2))).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    have k1 : (j : 𝕜) * (env "d" + env "e" * t) ^ (j - 1) * (env "d" + env "e" * t) = (j : 𝕜) * (env "d" + env "e" * t) ^ j := by
      rcases em (j = 0) with h0 | h0
      · subst h0; simp
      · have h' : (env "d" + env "e" * t) ≠ 0 ∨ 0 ≤ j - 1 := by
          by_cases h : j < 0
          · exact Or.inl (hB h)
          · exact Or.inr (by omega)
        rw [show (env "d" + env "e" * t) ^ j = (env "d" + env "e" * t) ^ (j - 1) * (env "d" + env "e" * t) by rw [← zpow_succ_of _ _ h', sub_add_cancel]]
        ring
    rw [zpow_succ_of _ _ hQ0]
    generalize (env "d" + env "e" * t) ^ (j - 1) = Bm1 at k1 ⊢
    generalize (env "d" + env "e" * t) ^ j = Bm at k1 ⊢
    generalize (env "a" + env "c" * t ^ 2) ^ q = Qp
    clear_value W1 W2 ei
    simp only [h_m, h_p] at hU1 hU2 ⊢
    push_cast
    linear_combination (env "g" * W1 * Qp * ei * env "c" * (env "e" * t - env "d")) * k1 + (env "g" * W1 * Qp * (j : 𝕜) * Bm1 * ei) * heq +
      (-env "g" * W1 * Qp * (j : 𝕜) * Bm1 * env "e" * (env "a" + env "c" * t ^ 2) + env "g" * W1 * env "c" * Bm * Qp * (j : 𝕜) * t - Bm * Qp * (j : 𝕜) * env "d" * env "g" * env "c" * ((j : 𝕜) + 2 * (q : 𝕜) + 2) * W1 * W2) * hei +
      (env "g" * t * Bm * Qp - Bm * Qp * (j : 𝕜) * env "d" * env "g" * W2) * hU1 + (env "f" * Bm * Qp + Bm * Qp * (j : 𝕜) * env "d" * env "g" * env "c" * W1 * ei) * hU2

theorem rubi1213r33Nondeg_real : rubi1213r33Nondeg.Holds .real := rubi1213r33Nondeg_holds Interp.real
theorem rubi1213r33Nondeg_complex : rubi1213r33Nondeg.Holds .complex := rubi1213r33Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec89
