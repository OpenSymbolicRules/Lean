import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, thirty-second batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 1.2.3.1 #5, the
reduction of `(a + b xⁿ + c x²ⁿ)^p` for `p < -1`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec80

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








/-- **1.2.3.1 #5** with `a n (p + 1) (b² - 4 a c) ≠ 0` and `p < -1`: the reduction of
`(a + b xⁿ + c x²ⁿ)^p`. -/
theorem rubi1231r5Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1231r5Nondeg.conditions rubi1231r5Nondeg.body rubi1231r5Nondeg.result rubi1231r5Nondeg.integrals := by
  intro env hc t hF
  have hW : env "a" * env "n" * (env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c") ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int 0)) (by simp [rubi1231r5Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1231r5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1231r5Nondeg])
  rcases hkn : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1231r5Nondeg, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1231r5Nondeg, Defined, eval, hkn, hkp] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hq : q < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [h_p] at hg
    have h' : I.lt ((q : ℚ) : 𝕜) ((((-1 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "n2") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [hn2, h_n]; push_cast; ring)
  have e1' : I.toInt? (2 * env "n") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have e2 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1231r5Nondeg.body →
      ((j < 0 → ¬w = 0) ∧ (2 * j < 0 → ¬w = 0)) ∧ (q < 0 → ¬(env "a" + env "b" * w ^ j + env "c" * w ^ (2 * j)) = 0) := by
    intro w h
    simpa [rubi1231r5Nondeg, Defined, eval, hkn, hkp, e1, toInt?_two] using h
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1231r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨⟨h1, h2⟩, h3⟩ := hD w hw
    simp [Defined, eval, hkn, e1', e2, toInt?_two]
    first | exact ⟨⟨h1, h2⟩, fun h => h3 (by omega)⟩ | exact ⟨h1, ⟨h1, h2⟩, fun h => h3 (by omega)⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨⟨h1, h2⟩, h3⟩ := hD w hw
    simp [rubi1231r5Nondeg, Defined, eval, recEnv, hkn, e1', e2, toInt?_two, toInt?_neg_one]
    exact ⟨⟨h1, ⟨h1, h2⟩, fun h => h3 (by omega)⟩, hW'.1, by simpa using hW'.2⟩
  · simp only [rubi1231r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨⟨hj1, hj2⟩, hA⟩ := hD t hF.self_of_nhds
    have hA0 : (env "a" + env "b" * t ^ j + env "c" * t ^ (2 * j)) ≠ 0 := hA (by omega)
    have hΦ' : HasDerivAt (Φ "I1") (((env "b" ^ 2 + -1 * 2 * env "a" * env "c") + env "n" * (env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c") + env "b" * env "c" * (env "n" * (2 * env "p" + 3) + 1) * t ^ j) * (env "a" + env "b" * t ^ j + env "c" * t ^ (2 * j)) ^ (q + 1)) t := by
      convert hΦ using 1
      simp [eval, hkn, e1', e2, toInt?_two]
      try ring
    have hEF : eval I (Function.update env "x" t) rubi1231r5Nondeg.body = (env "a" + env "b" * t ^ j + env "c" * t ^ (2 * j)) ^ q := by
      simp [rubi1231r5Nondeg, eval, hkn, hkp, e1, toInt?_two]
    set u := (env "a" * env "n" * (env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c"))⁻¹ with hu_def
    have hU : env "a" * env "n" * (env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c") * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi1231r5Nondeg.integrals.map (·.1)) Φ "x" w) rubi1231r5Nondeg.result) =
        fun w => -1 * w * ((env "b" ^ 2 + -1 * 2 * env "a" * env "c") + env "b" * env "c" * w ^ j) * (env "a" + env "b" * w ^ j + env "c" * w ^ (2 * j)) ^ (q + 1) * u + u * Φ "I1" w := by
      funext w
      simp [rubi1231r5Nondeg, eval, recEnv, hkn, e1', e2, toInt?_two, toInt?_neg_one, hu_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hx : t ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (hj1 h)
      · exact Or.inr (by omega)
    have hx2 : t ≠ 0 ∨ 0 ≤ 2 * j := by
      by_cases h : 2 * j < 0
      · exact Or.inl (hj2 h)
      · exact Or.inr (by omega)
    have k1 : (j : 𝕜) * t ^ (j - 1) * t = (j : 𝕜) * t ^ j := by
      rcases em (j = 0) with h0 | h0
      · subst h0; simp
      · have h' : t ≠ 0 ∨ 0 ≤ j - 1 := by
          by_cases h : j < 0
          · exact Or.inl (hj1 h)
          · exact Or.inr (by omega)
        rw [show t ^ j = t ^ (j - 1) * t by rw [← zpow_succ_of _ _ h', sub_add_cancel]]
        ring
    have k2 : ((2 * j : ℤ) : 𝕜) * t ^ (2 * j - 1) * t = ((2 * j : ℤ) : 𝕜) * t ^ (2 * j) := by
      rcases em (2 * j = 0) with h0 | h0
      · rw [h0]; simp
      · have h' : t ≠ 0 ∨ 0 ≤ 2 * j - 1 := by
          by_cases h : 2 * j < 0
          · exact Or.inl (hj2 h)
          · exact Or.inr (by omega)
        rw [show t ^ (2 * j) = t ^ (2 * j - 1) * t by rw [← zpow_succ_of _ _ h', sub_add_cancel]]
        ring
    have hT := hasDerivAt_zpow j t hx
    have hT2 := hasDerivAt_zpow (2 * j) t hx2
    have hAd : HasDerivAt (fun w => (env "a" + env "b" * w ^ j + env "c" * w ^ (2 * j))) (env "b" * ((j : 𝕜) * t ^ (j - 1)) + env "c" * (((2 * j : ℤ) : 𝕜) * t ^ (2 * j - 1))) t :=
      ((hT.const_mul (env "b")).const_add (env "a")).add (hT2.const_mul (env "c"))
    have hN : HasDerivAt (fun w => -1 * w * ((env "b" ^ 2 + -1 * 2 * env "a" * env "c") + env "b" * env "c" * w ^ j))
        (-1 * ((env "b" ^ 2 + -1 * 2 * env "a" * env "c") + env "b" * env "c" * t ^ j) + -1 * t * (env "b" * env "c" * ((j : 𝕜) * t ^ (j - 1)))) t := by
      have := ((hasDerivAt_id' t).const_mul (-1)).mul ((hT.const_mul (env "b" * env "c")).const_add (env "b" ^ 2 + -1 * 2 * env "a" * env "c"))
      convert this using 1 <;> first | ring1 | (funext w; simp only [id]) | (funext w; ring1)
    have hAp := (hasDerivAt_zpow (q + 1) _ (Or.inl hA0)).comp t hAd
    refine (((hN.mul hAp).mul_const u).add (hΦ'.const_mul u)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ (Or.inl hA0)]
    rw [show t ^ (2 * j) = (t ^ j) ^ 2 by rw [mul_comm, zpow_mul]; norm_cast] at k2 ⊢
    generalize (env "a" + env "b" * t ^ j + env "c" * (t ^ j) ^ 2) ^ q = Y
    generalize t ^ (j - 1) = R1 at k1 ⊢
    generalize t ^ (2 * j - 1) = R2 at k2 ⊢
    generalize t ^ j = T at k1 k2 ⊢
    clear_value u
    simp only [h_n, h_p] at hU ⊢
    push_cast at k2 ⊢
    linear_combination Y * hU +
      (u * Y * (-(env "b" * env "c" * (env "a" + env "b" * T + env "c" * T ^ 2)) - ((q : 𝕜) + 1) * ((env "b" ^ 2 + -1 * 2 * env "a" * env "c") + env "b" * env "c" * T) * env "b")) * k1 +
      (u * Y * (-((q : 𝕜) + 1) * ((env "b" ^ 2 + -1 * 2 * env "a" * env "c") + env "b" * env "c" * T) * env "c")) * k2

theorem rubi1231r5Nondeg_real : rubi1231r5Nondeg.Holds .real :=
  rubi1231r5Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1231r5Nondeg_complex : rubi1231r5Nondeg.Holds .complex :=
  rubi1231r5Nondeg_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec80
