import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, second batch

Proof of the strengthened variant of 1.1.3.4 #24, first distributed unproved
(`OSR.IntegrationNum1`, which keeps its definition).  Proved over ℝ and ℂ for
every choice of antiderivatives of the residual integrand.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec50

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








/-- **1.1.3.4 #24** with `b e (m + n (p + 1) + 1) ≠ 0` and `b (m + n (p + 1) + 1) ≠ 0`. -/
theorem binomPowLinNondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" binomPowLinNondeg.conditions binomPowLinNondeg.body binomPowLinNondeg.result binomPowLinNondeg.integrals := by
  intro env hc t hF
  have hW1 : (env "b" * env "e" * (env "m" + env "n" * (env "p" + 1) + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.int 0)) (by simp [binomPowLinNondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW2 : (env "b" * (env "m" + env "n" * (env "p" + 1) + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.int 0)) (by simp [binomPowLinNondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [binomPowLinNondeg, Defined, eval, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [binomPowLinNondeg, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [binomPowLinNondeg, Defined, eval, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hn : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkm1 : I.toInt? (env "m" + 1) = some (k + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) binomPowLinNondeg.body →
      (k < 0 → env "e" ≠ 0 ∧ w ≠ 0) ∧ (j < 0 → w ≠ 0) ∧ (q < 0 → (env "a" + env "b" * w ^ j) ≠ 0) := by
    intro w h
    simp [binomPowLinNondeg, Defined, eval, hkm, hkn, hkp] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [binomPowLinNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1', h2', h3'⟩ := hD w hw
    simp [Defined, eval, hkm, hkn, hkp]
    exact ⟨h1', h2', h3'⟩
  · filter_upwards [hF] with w hw
    obtain ⟨h1', h2', h3'⟩ := hD w hw
    simp [binomPowLinNondeg, Defined, eval, recEnv, hkm1, hkn, hkp1, toInt?_neg_one]
    exact ⟨⟨⟨fun h => h1' (by omega), h2', fun h => h3' (by omega)⟩,
      ⟨left_ne_zero_of_mul (left_ne_zero_of_mul hW1), right_ne_zero_of_mul (left_ne_zero_of_mul hW1)⟩,
      right_ne_zero_of_mul hW1⟩, left_ne_zero_of_mul hW2, right_ne_zero_of_mul hW2⟩
  · simp only [binomPowLinNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" * t) ^ k * (env "a" + env "b" * t ^ j) ^ q) t := by
      convert hΦ using 1
      simp [eval, hkm, hkn, hkp]
    have hEF : eval I (Function.update env "x" t) binomPowLinNondeg.body =
        (env "e" * t) ^ k * (env "a" + env "b" * t ^ j) ^ q * (env "c" + env "d" * t ^ j) := by
      simp [binomPowLinNondeg, eval, hkm, hkn, hkp]
    have hfun : (fun w => eval I (recEnv env (binomPowLinNondeg.integrals.map (·.1)) Φ "x" w) binomPowLinNondeg.result) =
        fun w => env "d" * (env "e" * w) ^ (k + 1) * (env "a" + env "b" * w ^ j) ^ (q + 1) * (env "b" * env "e" * (env "m" + env "n" * (env "p" + 1) + 1))⁻¹ +
          -1 * (env "a" * env "d" * (env "m" + 1) + -1 * env "b" * env "c" * (env "m" + env "n" * (env "p" + 1) + 1)) * (env "b" * (env "m" + env "n" * (env "p" + 1) + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [binomPowLinNondeg, eval, recEnv, hkm1, hkn, hkp1, toInt?_neg_one]
    rw [hfun, hEF]
    have hct : env "e" * t ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (mul_ne_zero (ht.1 h).1 (ht.1 h).2)
      · exact Or.inr (by omega)
    have hct0 : env "e" * t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (mul_ne_zero (ht.1 h).1 (ht.1 h).2)
      · exact Or.inr (by omega)
    have hx : t ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (ht.2.1 h)
      · exact Or.inr (by omega)
    have hu : (env "a" + env "b" * t ^ j) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2.2 (by omega))
      · exact Or.inr (by omega)
    have hu0 : (env "a" + env "b" * t ^ j) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2.2 h)
      · exact Or.inr (by omega)
    have key : (j : 𝕜) * t ^ (j - 1) * t = (j : 𝕜) * t ^ j := by
      rcases em (j = 0) with h0 | h0
      · subst h0; simp
      · have h' : t ≠ 0 ∨ 0 ≤ j - 1 := by
          by_cases h : j < 0
          · exact Or.inl (ht.2.1 h)
          · exact Or.inr (by omega)
        rw [show t ^ j = t ^ (j - 1) * t by rw [← zpow_succ_of _ _ h', sub_add_cancel]]
        ring
    have hin : HasDerivAt (fun w => env "a" + env "b" * w ^ j) (env "b" * ((j : 𝕜) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t hx).const_mul (env "b")).const_add (env "a")
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hct)
      ((hasDerivAt_id' t).const_mul (env "e"))).const_mul (env "d")).mul (HasDerivAt.comp t
        (hasDerivAt_zpow (q + 1) _ hu) hin)).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hct0, zpow_succ_of _ _ hu0]
    generalize (env "e" * t) ^ k = C
    generalize (env "a" + env "b" * t ^ j) ^ q = Y
    generalize t ^ (j - 1) = R at key ⊢
    generalize t ^ j = T at key ⊢
    simp only [hm, hn, hp] at hW1 hW2 ⊢
    set u1 := (env "b" * env "e" * ((k : 𝕜) + (j : 𝕜) * ((q : 𝕜) + 1) + 1))⁻¹ with hu1_def
    set u2 := (env "b" * ((k : 𝕜) + (j : 𝕜) * ((q : 𝕜) + 1) + 1))⁻¹ with hu2_def
    have hU1 : env "b" * env "e" * ((k : 𝕜) + (j : 𝕜) * ((q : 𝕜) + 1) + 1) * u1 = 1 := by rw [hu1_def]; exact mul_inv_cancel₀ hW1
    have hU2 : env "b" * ((k : 𝕜) + (j : 𝕜) * ((q : 𝕜) + 1) + 1) * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hW2
    have hrel : env "e" * u1 = u2 := by
      have h0 : env "b" * ((k : 𝕜) + (j : 𝕜) * ((q : 𝕜) + 1) + 1) * (env "e" * u1 - u2) = 0 := by linear_combination hU1 - hU2
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h hW2
      · linear_combination h
    push_cast
    linear_combination (C * Y * (env "c" + env "d" * T)) * hU2 +
      (u2 * C * Y * env "d" * ((q : 𝕜) + 1) * env "b") * key +
      (env "d" * C * Y * (((k : 𝕜) + 1) * (env "a" + env "b" * T) + t * ((q : 𝕜) + 1) * env "b" * (j : 𝕜) * R)) * hrel

theorem binomPowLinNondeg_real : binomPowLinNondeg.Holds .real :=
  binomPowLinNondeg_holds Interp.real

theorem binomPowLinNondeg_complex : binomPowLinNondeg.Holds .complex :=
  binomPowLinNondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec50
