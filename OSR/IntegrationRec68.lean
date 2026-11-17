import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, twentieth batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 4.1.12 #33 and #34,
integrations by parts of `(e x)^m` times the sine or cosine of `c + d xⁿ`
with `n > 0` and `m + 1 > n`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec68

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








/-- **4.1.12 #33** with `d n ≠ 0`, `n > 0` and `m + 1 > n`: integration by parts, `e^(n-1) (e x)^(m-n+1) x^(n-1) = (e x)^m`. -/
theorem rubi4112r33Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivRecHolds I "x" rubi4112r33Nondeg.conditions rubi4112r33Nondeg.body rubi4112r33Nondeg.result rubi4112r33Nondeg.integrals := by
  intro env hc t hF
  have hW : env "d" * env "n" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "d") (.var "n")) (.int 0)) (by simp [rubi4112r33Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg1 := hc (.gt (.var "n") (.int 0)) (by simp [rubi4112r33Nondeg])
  have hg2 := hc (.gt (.app2 .add (.var "m") (.int 1)) (.var "n")) (by simp [rubi4112r33Nondeg])
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r33Nondeg, Defined, eval, hk_n] at h
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r33Nondeg, Defined, eval, hk_n, hk_m] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg1
    rw [h_n] at hg1
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((j : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg1
    exact_mod_cast (hlt _ _).1 h'
  have hjk : j < k + 1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg2
    rw [h_n, h_m] at hg2
    have h' : I.lt ((j : ℚ) : 𝕜) ((((k + 1 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; push_cast; simpa using hg2
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "n" + -1 * 1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have e2 : I.toInt? (env "m" + -1 * env "n") = some (k - j) := (I.toInt?_eq _ _).2 (by rw [h_n, h_m]; push_cast; ring)
  have e3 : I.toInt? (env "m" + -1 * env "n" + 1) = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_n, h_m]; push_cast; ring)
  have e1' : I.toInt? (env "n" + -1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have e2' : I.toInt? (env "m" + -env "n") = some (k - j) := (I.toInt?_eq _ _).2 (by rw [h_n, h_m]; push_cast; ring)
  have e3' : I.toInt? (env "m" + -env "n" + 1) = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_n, h_m]; push_cast; ring)
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r33Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    exact Eventually.of_forall fun w => by
      simp [Defined, eval, hk_n, e2, e2']
      first | done | (refine ⟨?_, ?_⟩ <;> intro h <;> omega) | (intro h; omega) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4112r33Nondeg, Defined, eval, recEnv, hk_n, e1, e3, e1', e3', toInt?_neg_one]
      exact ⟨⟨⟨⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩, fun h => absurd h (by omega)⟩, hW'⟩,
        fun h => absurd h (by omega), hW'⟩
  · simp only [rubi4112r33Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" * t) ^ (k - j) * I.cos (env "c" + env "d" * t ^ j)) t := by
      convert hΦ using 1
      simp [eval, hk_n, e2, e2']
    have hEF : eval I (Function.update env "x" t) rubi4112r33Nondeg.body = (env "e" * t) ^ k * I.sin (env "c" + env "d" * t ^ j) := by
      simp [rubi4112r33Nondeg, eval, hk_n, hk_m]
    set u := (env "d" * env "n")⁻¹ with hu_def
    have hU : env "d" * env "n" * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi4112r33Nondeg.integrals.map (·.1)) Φ "x" w) rubi4112r33Nondeg.result) =
        fun w => -1 * env "e" ^ (j - 1) * (env "e" * w) ^ (k - j + 1) * I.cos (env "c" + env "d" * w ^ j) * u + env "e" ^ j * (env "m" + -1 * env "n" + 1) * u * Φ "I1" w := by
      funext w
      simp [rubi4112r33Nondeg, eval, recEnv, hk_n, e1, e3, e1', e3', toInt?_neg_one, hu_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hin : HasDerivAt (fun w => (env "c" + env "d" * w ^ j)) (env "d" * ((j : 𝕜) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t (Or.inr hj.le)).const_mul (env "d")).const_add (env "c")
    have hGd := HasDerivAt.comp t (hcs _) hin
    have hpow : HasDerivAt (fun w => (env "e" * w) ^ (k - j + 1)) (((k - j + 1 : ℤ) : 𝕜) * (env "e" * t) ^ (k - j + 1 - 1) * (env "e" * 1)) t :=
      HasDerivAt.comp t (hasDerivAt_zpow (k - j + 1) _ (Or.inr (by omega))) ((hasDerivAt_id' t).const_mul (env "e"))
    refine ((((hpow.const_mul (-1 * env "e" ^ (j - 1))).mul hGd).mul_const u).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hEk : (env "e" * t) ^ k = (env "e" * t) ^ (k - j) * (env "e" * t) * (env "e" ^ (j - 1) * t ^ (j - 1)) := by
      rw [← mul_zpow, ← zpow_succ_of _ _ (Or.inr (by omega)), ← zpow_add' (Or.inr (Or.inl (by omega)))]
      congr 1; ring
    have hE1 : (env "e" * t) ^ (k - j + 1) = (env "e" * t) ^ (k - j) * (env "e" * t) := zpow_succ_of _ _ (Or.inr (by omega))
    have hej : env "e" ^ j = env "e" ^ (j - 1) * env "e" := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hEk, hE1, hej]
    generalize (env "e" * t) ^ (k - j) = R
    generalize env "e" ^ (j - 1) = ej1
    generalize t ^ (j - 1) = tj1
    clear_value u
    simp only [h_m, h_n] at hU ⊢
    push_cast
    linear_combination (R * env "e" * t * ej1 * tj1 * I.sin (env "c" + env "d" * t ^ j)) * hU

theorem rubi4112r33Nondeg_real : rubi4112r33Nondeg.Holds .real :=
  rubi4112r33Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos

theorem rubi4112r33Nondeg_complex : rubi4112r33Nondeg.Holds .complex :=
  rubi4112r33Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos

/-- **4.1.12 #34** with `d n ≠ 0`, `n > 0` and `m + 1 > n`: integration by parts, `e^(n-1) (e x)^(m-n+1) x^(n-1) = (e x)^m`. -/
theorem rubi4112r34Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivRecHolds I "x" rubi4112r34Nondeg.conditions rubi4112r34Nondeg.body rubi4112r34Nondeg.result rubi4112r34Nondeg.integrals := by
  intro env hc t hF
  have hW : env "d" * env "n" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "d") (.var "n")) (.int 0)) (by simp [rubi4112r34Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg1 := hc (.gt (.var "n") (.int 0)) (by simp [rubi4112r34Nondeg])
  have hg2 := hc (.gt (.app2 .add (.var "m") (.int 1)) (.var "n")) (by simp [rubi4112r34Nondeg])
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r34Nondeg, Defined, eval, hk_n] at h
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r34Nondeg, Defined, eval, hk_n, hk_m] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg1
    rw [h_n] at hg1
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((j : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg1
    exact_mod_cast (hlt _ _).1 h'
  have hjk : j < k + 1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg2
    rw [h_n, h_m] at hg2
    have h' : I.lt ((j : ℚ) : 𝕜) ((((k + 1 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; push_cast; simpa using hg2
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "n" + -1 * 1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have e2 : I.toInt? (env "m" + -1 * env "n") = some (k - j) := (I.toInt?_eq _ _).2 (by rw [h_n, h_m]; push_cast; ring)
  have e3 : I.toInt? (env "m" + -1 * env "n" + 1) = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_n, h_m]; push_cast; ring)
  have e1' : I.toInt? (env "n" + -1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have e2' : I.toInt? (env "m" + -env "n") = some (k - j) := (I.toInt?_eq _ _).2 (by rw [h_n, h_m]; push_cast; ring)
  have e3' : I.toInt? (env "m" + -env "n" + 1) = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_n, h_m]; push_cast; ring)
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r34Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    exact Eventually.of_forall fun w => by
      simp [Defined, eval, hk_n, e2, e2']
      first | done | (refine ⟨?_, ?_⟩ <;> intro h <;> omega) | (intro h; omega) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4112r34Nondeg, Defined, eval, recEnv, hk_n, e1, e3, e1', e3', toInt?_neg_one]
      exact ⟨⟨⟨⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩, fun h => absurd h (by omega)⟩, hW'⟩,
        fun h => absurd h (by omega), hW'⟩
  · simp only [rubi4112r34Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" * t) ^ (k - j) * I.sin (env "c" + env "d" * t ^ j)) t := by
      convert hΦ using 1
      simp [eval, hk_n, e2, e2']
    have hEF : eval I (Function.update env "x" t) rubi4112r34Nondeg.body = (env "e" * t) ^ k * I.cos (env "c" + env "d" * t ^ j) := by
      simp [rubi4112r34Nondeg, eval, hk_n, hk_m]
    set u := (env "d" * env "n")⁻¹ with hu_def
    have hU : env "d" * env "n" * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi4112r34Nondeg.integrals.map (·.1)) Φ "x" w) rubi4112r34Nondeg.result) =
        fun w => env "e" ^ (j - 1) * (env "e" * w) ^ (k - j + 1) * I.sin (env "c" + env "d" * w ^ j) * u + -1 * env "e" ^ j * (env "m" + -1 * env "n" + 1) * u * Φ "I1" w := by
      funext w
      simp [rubi4112r34Nondeg, eval, recEnv, hk_n, e1, e3, e1', e3', toInt?_neg_one, hu_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hin : HasDerivAt (fun w => (env "c" + env "d" * w ^ j)) (env "d" * ((j : 𝕜) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t (Or.inr hj.le)).const_mul (env "d")).const_add (env "c")
    have hGd := HasDerivAt.comp t (hs _) hin
    have hpow : HasDerivAt (fun w => (env "e" * w) ^ (k - j + 1)) (((k - j + 1 : ℤ) : 𝕜) * (env "e" * t) ^ (k - j + 1 - 1) * (env "e" * 1)) t :=
      HasDerivAt.comp t (hasDerivAt_zpow (k - j + 1) _ (Or.inr (by omega))) ((hasDerivAt_id' t).const_mul (env "e"))
    refine ((((hpow.const_mul (env "e" ^ (j - 1))).mul hGd).mul_const u).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hEk : (env "e" * t) ^ k = (env "e" * t) ^ (k - j) * (env "e" * t) * (env "e" ^ (j - 1) * t ^ (j - 1)) := by
      rw [← mul_zpow, ← zpow_succ_of _ _ (Or.inr (by omega)), ← zpow_add' (Or.inr (Or.inl (by omega)))]
      congr 1; ring
    have hE1 : (env "e" * t) ^ (k - j + 1) = (env "e" * t) ^ (k - j) * (env "e" * t) := zpow_succ_of _ _ (Or.inr (by omega))
    have hej : env "e" ^ j = env "e" ^ (j - 1) * env "e" := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hEk, hE1, hej]
    generalize (env "e" * t) ^ (k - j) = R
    generalize env "e" ^ (j - 1) = ej1
    generalize t ^ (j - 1) = tj1
    clear_value u
    simp only [h_m, h_n] at hU ⊢
    push_cast
    linear_combination (R * env "e" * t * ej1 * tj1 * I.cos (env "c" + env "d" * t ^ j)) * hU

theorem rubi4112r34Nondeg_real : rubi4112r34Nondeg.Holds .real :=
  rubi4112r34Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos

theorem rubi4112r34Nondeg_complex : rubi4112r34Nondeg.Holds .complex :=
  rubi4112r34Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos

end Proofs

end OSR.IntegrationRec68
