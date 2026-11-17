import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, thirty-fourth batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 4.1.12 #43 and #44,
the reductions of `x^m sin(a + b xⁿ)^p` and `x^m cos(a + b xⁿ)^p` for
`m = 2 n - 1` and `p > 1`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec82

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








/-- **4.1.12 #43** with `m = 2 n - 1`, `p > 1` and `b n p ≠ 0`: the reduction of
`x^m sin(a + b xⁿ)^p`. -/
theorem rubi4112r43Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u)
    (hp : ∀ u : 𝕜, I.sin u ^ 2 + I.cos u ^ 2 = 1) :
    AntiderivRecHolds I "x" rubi4112r43Nondeg.conditions rubi4112r43Nondeg.body rubi4112r43Nondeg.result rubi4112r43Nondeg.integrals := by
  intro env hc t hF
  have hW1 : env "b" * env "n" * env "p" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.int 0)) (by simp [rubi4112r43Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW1' := hW1
  simp only [ne_eq, mul_eq_zero, not_or] at hW1'
  obtain ⟨⟨hb, hn⟩, hp0⟩ := hW1'
  have hmeq : env "m" + -1 * 2 * env "n" + 1 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)) (.int 0)) (by simp [rubi4112r43Nondeg])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    push_cast at h
    linear_combination h
  have hg := hc (.gt (.var "p") (.int 1)) (by simp [rubi4112r43Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r43Nondeg, Defined, eval, hk_m] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r43Nondeg, Defined, eval, hk_m, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r43Nondeg, Defined, eval, hk_m, hk_n, hk_p] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hq : 1 < q := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [h_p] at hg
    have h' : I.lt ((((1 : ℤ)) : ℚ) : 𝕜) ((q : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (hlt _ _).1 h'
  have hkj : k = 2 * j - 1 := by
    have h1 : I.toInt? (env "m") = some (2 * j - 1) :=
      (I.toInt?_eq _ _).2 (by push_cast; rw [← h_n]; linear_combination hmeq)
    rw [hk_m] at h1
    exact Option.some.inj h1
  have hj0 : j ≠ 0 := by
    intro h; apply hn; rw [h_n, h]; simp
  have hq0 : ¬ q < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hq2 : ¬ q - 2 < 0 := by omega
  have e1 : I.toInt? (env "p" + -1 * 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have e1' : I.toInt? (env "p" + -1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have e2 : I.toInt? (env "p" + -1 * 2) = some (q - 2) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have e2' : I.toInt? (env "p" + -2) = some (q - 2) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r43Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi4112r43Nondeg, Defined, eval, hk_m, hk_n, hk_p, e2, e2', hq0, hq2] at hw ⊢
    first | exact hw | exact ⟨hw.1, hw.2.1⟩ | exact ⟨hw.1, hw.2⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi4112r43Nondeg, Defined, eval, recEnv, hk_m, hk_n, hk_p, e1, e1', toInt?_neg_one, toInt?_two, hq0, hq1, hb, hn, hp0] at hw ⊢
    first | exact hw.2 | exact ⟨hw.2, hw.2⟩ | exact ⟨hw.2, hw.2, hw.2⟩ | (trace_state; sorry)
  · simp only [rubi4112r43Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hD0 := hF.self_of_nhds
    simp [rubi4112r43Nondeg, Defined, eval, hk_m, hk_n, hk_p, hq0] at hD0
    have hx : t ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (by first | exact hD0.2 h | exact hD0 h | (trace_state; sorry))
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") (t ^ k * I.sin (env "a" + env "b" * t ^ j) ^ (q - 2)) t := by
      convert hΦ using 1
      simp [eval, hk_m, hk_n, e2, e2']
    have hEF : eval I (Function.update env "x" t) rubi4112r43Nondeg.body = t ^ k * I.sin (env "a" + env "b" * t ^ j) ^ q := by
      simp [rubi4112r43Nondeg, eval, hk_m, hk_n, hk_p]
    set W2 := (env "b" ^ 2 * env "n" ^ 2 * env "p" ^ 2)⁻¹ with hW2_def
    set W1 := (env "b" * env "n" * env "p")⁻¹ with hW1_def
    set P := (env "p")⁻¹ with hP_def
    have hU2 : env "b" ^ 2 * env "n" ^ 2 * env "p" ^ 2 * W2 = 1 := by
      rw [hW2_def]; exact mul_inv_cancel₀ (by simp [hb, hn, hp0])
    have hU1 : env "b" * env "n" * env "p" * W1 = 1 := by rw [hW1_def]; exact mul_inv_cancel₀ hW1
    have hUp : env "p" * P = 1 := by rw [hP_def]; exact mul_inv_cancel₀ hp0
    have hfun : (fun w => eval I (recEnv env (rubi4112r43Nondeg.integrals.map (·.1)) Φ "x" w) rubi4112r43Nondeg.result) =
        fun w => env "n" * I.sin (env "a" + env "b" * w ^ j) ^ q * W2 + -1 * w ^ j * I.cos (env "a" + env "b" * w ^ j) * I.sin (env "a" + env "b" * w ^ j) ^ (q - 1) * W1 + (env "p" + -1) * P * Φ "I1" w := by
      funext w
      simp [rubi4112r43Nondeg, eval, recEnv, hk_m, hk_n, hk_p, e1, e1', toInt?_neg_one, toInt?_two, hW2_def, hW1_def, hP_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hin : HasDerivAt (fun w => (env "a" + env "b" * w ^ j)) (env "b" * ((j : 𝕜) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t hx).const_mul (env "b")).const_add (env "a")
    have hMd := HasDerivAt.comp t (hs _) hin
    have hNd := HasDerivAt.comp t (hcs _) hin
    have hX := hasDerivAt_zpow j t hx
    have hMq := HasDerivAt.comp t (hasDerivAt_zpow q _ (Or.inr (by omega))) hMd
    have hMq1 := HasDerivAt.comp t (hasDerivAt_zpow (q - 1) _ (Or.inr (by omega))) hMd
    refine ((((hMq.const_mul (env "n")).mul_const W2).add ((((hX.const_mul (-1)).mul hNd).mul hMq1).mul_const W1)).add
      (hΦ'.const_mul ((env "p" + -1) * P))).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply]
    have hTk : t ^ k = t ^ j * t ^ (j - 1) := by
      rw [hkj, ← zpow_add' (Or.inr (Or.inl (by omega)))]; congr 1; ring
    have hM0 : I.sin (env "a" + env "b" * t ^ j) ^ q = I.sin (env "a" + env "b" * t ^ j) ^ (q - 2) * I.sin (env "a" + env "b" * t ^ j) * I.sin (env "a" + env "b" * t ^ j) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), ← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
    have hM1 : I.sin (env "a" + env "b" * t ^ j) ^ (q - 1) = I.sin (env "a" + env "b" * t ^ j) ^ (q - 2) * I.sin (env "a" + env "b" * t ^ j) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
    rw [show q - 1 - 1 = q - 2 by ring, hTk, hM0, hM1]
    have hpt := hp (env "a" + env "b" * t ^ j)
    generalize I.sin (env "a" + env "b" * t ^ j) ^ (q - 2) = R
    generalize I.sin (env "a" + env "b" * t ^ j) = S at hpt ⊢
    generalize I.cos (env "a" + env "b" * t ^ j) = C at hpt ⊢
    generalize t ^ (j - 1) = T1
    generalize t ^ j = Tn
    clear_value W2 W1 P
    simp only [h_n, h_p] at hU2 hU1 hUp ⊢
    push_cast
    linear_combination (S * C * R * T1 * (j : 𝕜) * W1) * hU2 + (-C ^ 2 * R * T1 * Tn - S * C * R * T1 * env "b" * (j : 𝕜) ^ 2 * (q : 𝕜) * W2 + R * T1 * Tn * P) * hU1 + (R * T1 * Tn - R * T1 * Tn * env "b" * (j : 𝕜) * W1) * hUp + (R * T1 * Tn * (W1 * env "b" * (j : 𝕜) - 1)) * hpt

theorem rubi4112r43Nondeg_real : rubi4112r43Nondeg.Holds .real :=
  rubi4112r43Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos Real.sin_sq_add_cos_sq

theorem rubi4112r43Nondeg_complex : rubi4112r43Nondeg.Holds .complex :=
  rubi4112r43Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos Complex.sin_sq_add_cos_sq

/-- **4.1.12 #44** with `m = 2 n - 1`, `p > 1` and `b n p ≠ 0`: the reduction of
`x^m cos(a + b xⁿ)^p`. -/
theorem rubi4112r44Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u)
    (hp : ∀ u : 𝕜, I.sin u ^ 2 + I.cos u ^ 2 = 1) :
    AntiderivRecHolds I "x" rubi4112r44Nondeg.conditions rubi4112r44Nondeg.body rubi4112r44Nondeg.result rubi4112r44Nondeg.integrals := by
  intro env hc t hF
  have hW1 : env "b" * env "n" * env "p" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.int 0)) (by simp [rubi4112r44Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW1' := hW1
  simp only [ne_eq, mul_eq_zero, not_or] at hW1'
  obtain ⟨⟨hb, hn⟩, hp0⟩ := hW1'
  have hmeq : env "m" + -1 * 2 * env "n" + 1 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)) (.int 0)) (by simp [rubi4112r44Nondeg])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    push_cast at h
    linear_combination h
  have hg := hc (.gt (.var "p") (.int 1)) (by simp [rubi4112r44Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r44Nondeg, Defined, eval, hk_m] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r44Nondeg, Defined, eval, hk_m, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r44Nondeg, Defined, eval, hk_m, hk_n, hk_p] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hq : 1 < q := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [h_p] at hg
    have h' : I.lt ((((1 : ℤ)) : ℚ) : 𝕜) ((q : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (hlt _ _).1 h'
  have hkj : k = 2 * j - 1 := by
    have h1 : I.toInt? (env "m") = some (2 * j - 1) :=
      (I.toInt?_eq _ _).2 (by push_cast; rw [← h_n]; linear_combination hmeq)
    rw [hk_m] at h1
    exact Option.some.inj h1
  have hj0 : j ≠ 0 := by
    intro h; apply hn; rw [h_n, h]; simp
  have hq0 : ¬ q < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hq2 : ¬ q - 2 < 0 := by omega
  have e1 : I.toInt? (env "p" + -1 * 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have e1' : I.toInt? (env "p" + -1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have e2 : I.toInt? (env "p" + -1 * 2) = some (q - 2) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have e2' : I.toInt? (env "p" + -2) = some (q - 2) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r44Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi4112r44Nondeg, Defined, eval, hk_m, hk_n, hk_p, e2, e2', hq0, hq2] at hw ⊢
    first | exact hw | exact ⟨hw.1, hw.2.1⟩ | exact ⟨hw.1, hw.2⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi4112r44Nondeg, Defined, eval, recEnv, hk_m, hk_n, hk_p, e1, e1', toInt?_neg_one, toInt?_two, hq0, hq1, hb, hn, hp0] at hw ⊢
    first | exact hw.2 | exact ⟨hw.2, hw.2⟩ | exact ⟨hw.2, hw.2, hw.2⟩ | (trace_state; sorry)
  · simp only [rubi4112r44Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hD0 := hF.self_of_nhds
    simp [rubi4112r44Nondeg, Defined, eval, hk_m, hk_n, hk_p, hq0] at hD0
    have hx : t ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (by first | exact hD0.2 h | exact hD0 h | (trace_state; sorry))
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") (t ^ k * I.cos (env "a" + env "b" * t ^ j) ^ (q - 2)) t := by
      convert hΦ using 1
      simp [eval, hk_m, hk_n, e2, e2']
    have hEF : eval I (Function.update env "x" t) rubi4112r44Nondeg.body = t ^ k * I.cos (env "a" + env "b" * t ^ j) ^ q := by
      simp [rubi4112r44Nondeg, eval, hk_m, hk_n, hk_p]
    set W2 := (env "b" ^ 2 * env "n" ^ 2 * env "p" ^ 2)⁻¹ with hW2_def
    set W1 := (env "b" * env "n" * env "p")⁻¹ with hW1_def
    set P := (env "p")⁻¹ with hP_def
    have hU2 : env "b" ^ 2 * env "n" ^ 2 * env "p" ^ 2 * W2 = 1 := by
      rw [hW2_def]; exact mul_inv_cancel₀ (by simp [hb, hn, hp0])
    have hU1 : env "b" * env "n" * env "p" * W1 = 1 := by rw [hW1_def]; exact mul_inv_cancel₀ hW1
    have hUp : env "p" * P = 1 := by rw [hP_def]; exact mul_inv_cancel₀ hp0
    have hfun : (fun w => eval I (recEnv env (rubi4112r44Nondeg.integrals.map (·.1)) Φ "x" w) rubi4112r44Nondeg.result) =
        fun w => env "n" * I.cos (env "a" + env "b" * w ^ j) ^ q * W2 + 1 * w ^ j * I.sin (env "a" + env "b" * w ^ j) * I.cos (env "a" + env "b" * w ^ j) ^ (q - 1) * W1 + (env "p" + -1) * P * Φ "I1" w := by
      funext w
      simp [rubi4112r44Nondeg, eval, recEnv, hk_m, hk_n, hk_p, e1, e1', toInt?_neg_one, toInt?_two, hW2_def, hW1_def, hP_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hin : HasDerivAt (fun w => (env "a" + env "b" * w ^ j)) (env "b" * ((j : 𝕜) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t hx).const_mul (env "b")).const_add (env "a")
    have hMd := HasDerivAt.comp t (hcs _) hin
    have hNd := HasDerivAt.comp t (hs _) hin
    have hX := hasDerivAt_zpow j t hx
    have hMq := HasDerivAt.comp t (hasDerivAt_zpow q _ (Or.inr (by omega))) hMd
    have hMq1 := HasDerivAt.comp t (hasDerivAt_zpow (q - 1) _ (Or.inr (by omega))) hMd
    refine ((((hMq.const_mul (env "n")).mul_const W2).add ((((hX.const_mul (1)).mul hNd).mul hMq1).mul_const W1)).add
      (hΦ'.const_mul ((env "p" + -1) * P))).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply]
    have hTk : t ^ k = t ^ j * t ^ (j - 1) := by
      rw [hkj, ← zpow_add' (Or.inr (Or.inl (by omega)))]; congr 1; ring
    have hM0 : I.cos (env "a" + env "b" * t ^ j) ^ q = I.cos (env "a" + env "b" * t ^ j) ^ (q - 2) * I.cos (env "a" + env "b" * t ^ j) * I.cos (env "a" + env "b" * t ^ j) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), ← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
    have hM1 : I.cos (env "a" + env "b" * t ^ j) ^ (q - 1) = I.cos (env "a" + env "b" * t ^ j) ^ (q - 2) * I.cos (env "a" + env "b" * t ^ j) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
    rw [show q - 1 - 1 = q - 2 by ring, hTk, hM0, hM1]
    have hpt := hp (env "a" + env "b" * t ^ j)
    generalize I.cos (env "a" + env "b" * t ^ j) ^ (q - 2) = R
    generalize I.sin (env "a" + env "b" * t ^ j) = S at hpt ⊢
    generalize I.cos (env "a" + env "b" * t ^ j) = C at hpt ⊢
    generalize t ^ (j - 1) = T1
    generalize t ^ j = Tn
    clear_value W2 W1 P
    simp only [h_n, h_p] at hU2 hU1 hUp ⊢
    push_cast
    linear_combination (-C * S * R * T1 * (j : 𝕜) * W1) * hU2 + (-S ^ 2 * R * T1 * Tn + C * S * R * T1 * env "b" * (j : 𝕜) ^ 2 * (q : 𝕜) * W2 + R * T1 * Tn * P) * hU1 + (R * T1 * Tn - R * T1 * Tn * env "b" * (j : 𝕜) * W1) * hUp + (R * T1 * Tn * (W1 * env "b" * (j : 𝕜) - 1)) * hpt

theorem rubi4112r44Nondeg_real : rubi4112r44Nondeg.Holds .real :=
  rubi4112r44Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos Real.sin_sq_add_cos_sq

theorem rubi4112r44Nondeg_complex : rubi4112r44Nondeg.Holds .complex :=
  rubi4112r44Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos Complex.sin_sq_add_cos_sq

end Proofs

end OSR.IntegrationRec82
