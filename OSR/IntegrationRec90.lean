import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, forty-second batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 1.1.3.3 #16, the
reduction of `(a1 + b1 x^(n/2))^p (a2 + b2 x^(n/2))^p (c + d xⁿ)` for
`a2 b1 + a1 b2 = 0`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec90

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








/-- **1.1.3.3 #16** with `a2 b1 + a1 b2 = 0` and `b1 b2 (n (p + 1) + 1) ≠ 0`:
`(a1 + b1 x^(n/2))(a2 + b2 x^(n/2)) = a1 a2 + b1 b2 xⁿ`. -/
theorem rubi1133r16Nondeg_holds [CharZero 𝕜] (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1133r16Nondeg.conditions rubi1133r16Nondeg.body rubi1133r16Nondeg.result rubi1133r16Nondeg.integrals := by
  intro env hc t hF
  have hn2 : env "non2" = env "n" * 2⁻¹ := by
    have h := hc (.eq (.var "non2") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))) (by simp [rubi1133r16Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_neg_one] using h
  have hab : env "a2" * env "b1" + env "a1" * env "b2" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a2") (.var "b1")) (.app2 .mul (.var "a1") (.var "b2"))) (.int 0)) (by simp [rubi1133r16Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW : (env "b1" * env "b2" * (env "n" * (env "p" + 1) + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b1") (.var "b2")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1))) (.int 0)) (by simp [rubi1133r16Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkh : I.toInt? (env "non2") with _ | h
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1133r16Nondeg, Defined, eval, hkh] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1133r16Nondeg, Defined, eval, hkh, hkp] at h
  rcases hkn : I.toInt? (env "n") with _ | nn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1133r16Nondeg, Defined, eval, hkh, hkp, hkn] at h
  have h_h : env "non2" = (h : 𝕜) := (I.toInt?_eq _ _).1 hkh
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have h_n : env "n" = 2 * (h : 𝕜) := by
    rw [← h_h, hn2]; field_simp
  have hnn : nn = 2 * h := by
    have h1 : I.toInt? (env "n") = some (2 * h) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
    rw [hkn] at h1
    exact Option.some.inj h1
  subst hnn
  have eh : I.toInt? (env "n" * 2⁻¹) = some h := by rw [← hn2]; exact hkh
  have e1 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have h2ne : (2 : 𝕜) ≠ 0 := two_ne_zero
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1133r16Nondeg.body →
      ((h < 0 → ¬w = 0) ∧ (q < 0 → ¬(env "a1" + env "b1" * w ^ h) = 0)) ∧ (q < 0 → ¬(env "a2" + env "b2" * w ^ h) = 0) := by
    intro w hd
    simp [rubi1133r16Nondeg, Defined, eval, hkh, hkp, hkn] at hd
    exact ⟨hd.1.1, hd.1.2.2⟩
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1133r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨⟨h1, h2⟩, h3⟩ := hBody w hw
    simp [Defined, eval, hkp, eh, toInt?_neg_one, h2ne]
    first | exact ⟨⟨h1, h2⟩, h1, h3⟩ | exact ⟨⟨h1, h2⟩, h3⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨⟨h1, h2⟩, h3⟩ := hBody w hw
    have g2 : q + 1 < 0 → ¬(env "a1" + env "b1" * w ^ h) = 0 := fun hh => h2 (by omega)
    have g3 : q + 1 < 0 → ¬(env "a2" + env "b2" * w ^ h) = 0 := fun hh => h3 (by omega)
    have hW' := hW
    simp only [ne_eq, mul_eq_zero, not_or] at hW'
    simp [rubi1133r16Nondeg, Defined, eval, recEnv, hkp, eh, e1, toInt?_neg_one, h2ne]
    first | exact ⟨⟨⟨h1, g2⟩, h1, g3⟩, hW'⟩ | exact ⟨⟨⟨⟨h1, g2⟩, h1, g3⟩, hW'⟩, hW'⟩ | (trace_state; sorry)
  · simp only [rubi1133r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨⟨hT, hA⟩, hB⟩ := hBody t hF.self_of_nhds
    have hx : t ≠ 0 ∨ 0 ≤ h := by
      by_cases hh : h < 0
      · exact Or.inl (hT hh)
      · exact Or.inr (by omega)
    have hA0 : (env "a1" + env "b1" * t ^ h) ≠ 0 ∨ 0 ≤ q := by
      by_cases hh : q < 0
      · exact Or.inl (hA hh)
      · exact Or.inr (by omega)
    have hB0 : (env "a2" + env "b2" * t ^ h) ≠ 0 ∨ 0 ≤ q := by
      by_cases hh : q < 0
      · exact Or.inl (hB hh)
      · exact Or.inr (by omega)
    have hA1 : (env "a1" + env "b1" * t ^ h) ≠ 0 ∨ 0 ≤ q + 1 := by
      rcases hA0 with hh | hh
      · exact Or.inl hh
      · exact Or.inr (by omega)
    have hB1 : (env "a2" + env "b2" * t ^ h) ≠ 0 ∨ 0 ≤ q + 1 := by
      rcases hB0 with hh | hh
      · exact Or.inl hh
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") ((env "a1" + env "b1" * t ^ h) ^ q * (env "a2" + env "b2" * t ^ h) ^ q) t := by
      convert hΦ using 1
      simp [eval, hkp, eh, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1133r16Nondeg.body = (env "a1" + env "b1" * t ^ h) ^ q * (env "a2" + env "b2" * t ^ h) ^ q * (env "c" + env "d" * (t ^ h) ^ 2) := by
      simp [rubi1133r16Nondeg, eval, hkh, hkp, hkn]
      rw [show (2 * h) = h * 2 by ring, zpow_mul]
      norm_cast
      try simp
    set W := ((env "b1" * env "b2" * (env "n" * (env "p" + 1) + 1)))⁻¹ with hW_def
    have hWW : (env "b1" * env "b2" * (env "n" * (env "p" + 1) + 1)) * W = 1 := by rw [hW_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi1133r16Nondeg.integrals.map (·.1)) Φ "x" w) rubi1133r16Nondeg.result) =
        fun w => env "d" * w * (env "a1" + env "b1" * w ^ h) ^ (q + 1) * (env "a2" + env "b2" * w ^ h) ^ (q + 1) * W + (-1 * (env "a1" * env "a2" * env "d" + -1 * env "b1" * env "b2" * env "c" * (env "n" * (env "p" + 1) + 1))) * W * Φ "I1" w := by
      funext w
      simp [rubi1133r16Nondeg, eval, recEnv, hkp, eh, e1, toInt?_neg_one, hW_def, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hY := hasDerivAt_zpow h t hx
    have hU1d : HasDerivAt (fun w => (env "a1" + env "b1" * w ^ h)) (env "b1" * ((h : 𝕜) * t ^ (h - 1))) t := (hY.const_mul _).const_add _
    have hU2d : HasDerivAt (fun w => (env "a2" + env "b2" * w ^ h)) (env "b2" * ((h : 𝕜) * t ^ (h - 1))) t := (hY.const_mul _).const_add _
    have hU1p := HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hA1) hU1d
    have hU2p := HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hB1) hU2d
    have hX : HasDerivAt (fun w => env "d" * w) (env "d" * 1) t := (hasDerivAt_id' t).const_mul _
    refine ((((hX.mul hU1p).mul hU2p).mul_const W).add (hΦ'.const_mul ((-1 * (env "a1" * env "a2" * env "d" + -1 * env "b1" * env "b2" * env "c" * (env "n" * (env "p" + 1) + 1))) * W))).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    have k1 : (h : 𝕜) * t ^ (h - 1) * t = (h : 𝕜) * t ^ h := by
      rcases em (h = 0) with h0 | h0
      · subst h0; simp
      · have h' : t ≠ 0 ∨ 0 ≤ h - 1 := by
          by_cases hh : h < 0
          · exact Or.inl (hT hh)
          · exact Or.inr (by omega)
        rw [show t ^ h = t ^ (h - 1) * t by rw [← zpow_succ_of _ _ h', sub_add_cancel]]
        ring
    rw [zpow_succ_of _ _ hA0, zpow_succ_of _ _ hB0]
    generalize (env "a1" + env "b1" * t ^ h) ^ q = U1q
    generalize (env "a2" + env "b2" * t ^ h) ^ q = U2q
    generalize t ^ (h - 1) = T1 at k1 ⊢
    generalize t ^ h = Y at k1 ⊢
    clear_value W
    simp only [h_n, h_p] at hWW ⊢
    push_cast
    linear_combination (U1q * U2q * W * env "d" * ((q : 𝕜) + 1) * (2 * Y * env "b1" * env "b2" + env "a1" * env "b2" + env "a2" * env "b1")) * k1 +
      (U1q * U2q * W * Y * env "d" * ((h : 𝕜) * (q : 𝕜) + (h : 𝕜) + 1)) * hab + (U1q * U2q * (Y ^ 2 * env "d" + env "c")) * hWW

theorem rubi1133r16Nondeg_real : rubi1133r16Nondeg.Holds .real := rubi1133r16Nondeg_holds Interp.real
theorem rubi1133r16Nondeg_complex : rubi1133r16Nondeg.Holds .complex := rubi1133r16Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec90
