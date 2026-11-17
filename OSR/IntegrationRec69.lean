import OSR.IntegrationNum1
import OSR.IntegrationRec7

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, twenty-first batch

Proofs over ℝ of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 3.1.1 #3, the
reduction of `(a + b log (c xⁿ))^p` for `p < -1`.  The proofs use the real
logarithm; the complex domain stays unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec69

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








/-- **3.1.1 #3** with `b n (p + 1) ≠ 0`, over ℝ: `x (n/x) = n` makes the reduction of
`(a + b log (c xⁿ))^p` exact. -/
theorem rubi311r3Nondeg_real : rubi311r3Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi311r3Nondeg.conditions rubi311r3Nondeg.body
    rubi311r3Nondeg.result rubi311r3Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hW : env "b" * env "n" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi311r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkp : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi311r3Nondeg, Defined, eval, Interp.real, hkp] at h
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi311r3Nondeg, Defined, eval, Interp.real, hkp, hkn] at h
  have hp : env "p" = (q : ℝ) := (intValue?_eq _ _).1 hkp
  have hn : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have hkp1 : intValue? (env "p" + 1) = some (q + 1) := (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi311r3Nondeg.body →
      (j < 0 → w ≠ 0) ∧ 0 < env "c" * w ^ j ∧
        (q < 0 → env "a" + env "b" * Real.log (env "c" * w ^ j) ≠ 0) := by
    intro w h
    simp [rubi311r3Nondeg, Defined, eval, Interp.real, hkp, hkn] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have ht := hD t hF.self_of_nhds
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi311r3Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3⟩ := hD w hw
    simp [Defined, eval, Interp.real, hkn, hkp1]
    first | exact ⟨⟨h1, h2⟩, fun h => h3 (by omega)⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3⟩ := hD w hw
    simp [rubi311r3Nondeg, Defined, eval, Interp.real, recEnv, hkn, hkp1, hm1]
    first | exact ⟨⟨⟨h1, h2⟩, fun h => h3 (by omega)⟩, hW'⟩ | exact ⟨⟨⟨h1, h2⟩, fun h => h3 (by omega)⟩, fun _ => hW'⟩ | (trace_state; sorry)
  · simp only [rubi311r3Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨-, hc0, hL⟩ := ht
    have hL0 : env "a" + env "b" * Real.log (env "c" * t ^ j) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (hL (by omega))
      · exact Or.inr (by omega)
    have hLq : env "a" + env "b" * Real.log (env "c" * t ^ j) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (hL h)
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ (q + 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkn, hkp1]
    have hEF : eval Interp.real (Function.update env "x" t) rubi311r3Nondeg.body =
        (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ q := by
      simp [rubi311r3Nondeg, eval, Interp.real, hkp, hkn]
    set u := (env "b" * env "n" * (env "p" + 1))⁻¹ with hu_def
    have hU : env "b" * env "n" * (env "p" + 1) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval Interp.real (recEnv env (rubi311r3Nondeg.integrals.map (·.1)) Φ "x" w) rubi311r3Nondeg.result) =
        fun w => w * (env "a" + env "b" * Real.log (env "c" * w ^ j)) ^ (q + 1) * u + -1 * u * Φ "I1" w := by
      funext w
      simp [rubi311r3Nondeg, eval, Interp.real, recEnv, hkn, hkp1, hu_def, hm1]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hd1 : HasDerivAt (fun w => env "a" + env "b" * Real.log (env "c" * w ^ j)) (env "b" * ((j : ℝ) / t)) t :=
      ((OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hc0).const_mul _).const_add _
    have hP := (hasDerivAt_zpow (q + 1) _ hL0).comp t hd1
    refine ((((hasDerivAt_id' t).mul hP).mul_const u).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have htX := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hc0
    generalize (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ q = Y
    generalize (j : ℝ) / t = X at htX ⊢
    clear_value u
    simp only [hp, hn] at hU ⊢
    push_cast
    linear_combination Y * hU + (u * ((q : ℝ) + 1) * Y * env "b") * htX

/-- **3.1.2 #5** with `d (m + 1) ≠ 0` and `p > 0`, over ℝ: integration by parts, from `x (n/x) = n`. -/
theorem rubi312r5Nondeg_real : rubi312r5Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi312r5Nondeg.conditions rubi312r5Nondeg.body
    rubi312r5Nondeg.result rubi312r5Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hW1 : (env "d" * (env "m" + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi312r5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW2 : (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .add (.var "m") (.int 1)) (.int 0)) (by simp [rubi312r5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg := hc (.gt (.var "p") (.int 0)) (by simp [rubi312r5Nondeg])
  rcases hkm : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi312r5Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi312r5Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi312r5Nondeg, Defined, eval, Interp.real, hkm, hkp, hkn] at h
  have hm : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hkm
  have hp : env "p" = (q : ℝ) := (intValue?_eq _ _).1 hkp
  have hn : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have hq : 0 < q := by
    simp only [Cond.Holds, Defined, eval, Interp.real, true_and] at hg
    rw [hp] at hg
    exact_mod_cast hg
  have hkm1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkp1 : intValue? (env "p" + 1) = some (q + 1) := (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hkp0 : intValue? (env "p" + -1 * 1) = some (q - 1) := (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hkp0' : intValue? (env "p" + -1) = some (q - 1) := (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi312r5Nondeg.body →
      (k < 0 → env "d" * w ≠ 0) ∧ (j < 0 → w ≠ 0) ∧ 0 < env "c" * w ^ j ∧ (q < 0 → (env "a" + env "b" * Real.log (env "c" * w ^ j)) ≠ 0) := by
    intro w h
    simp [rubi312r5Nondeg, Defined, eval, Interp.real, hkm, hkp, hkn] at h
    first | exact ⟨fun hk => by simpa using h.1 hk, h.2.1.1, h.2.1.2, h.2.2⟩ | (trace_state; sorry)
  have ht := hD t hF.self_of_nhds
  have hW1' := hW1
  have hW2' := hW2
  simp only [ne_eq, mul_eq_zero, not_or] at hW1' hW2'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi312r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3, h4⟩ := hD w hw
    simp [Defined, eval, Interp.real, hkm, hkn, hkp1, hkp0, hkp0']
    first
      | exact ⟨fun hk => by simpa using h1 hk, ⟨h2, h3⟩, fun h => absurd h (by omega)⟩
      | exact ⟨fun hk => by simpa using h1 hk, ⟨h2, h3⟩, fun h => h4 (by omega)⟩
      | exact ⟨⟨⟨fun hk => by simpa using h1 (by omega), ⟨h2, h3⟩, h4⟩, hW1'⟩, hW2⟩
      | exact ⟨⟨⟨fun hk => by simpa using h1 (by omega), ⟨h2, h3⟩, fun h => h4 (by omega)⟩, hW1'⟩, hW2'⟩
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3, h4⟩ := hD w hw
    simp [rubi312r5Nondeg, Defined, eval, Interp.real, recEnv, hkm1, hkn, hkp1, hkp, hm1]
    first
      | exact ⟨fun hk => by simpa using h1 hk, ⟨h2, h3⟩, fun h => absurd h (by omega)⟩
      | exact ⟨fun hk => by simpa using h1 hk, ⟨h2, h3⟩, fun h => h4 (by omega)⟩
      | exact ⟨⟨⟨fun hk => by simpa using h1 (by omega), ⟨h2, h3⟩, h4⟩, hW1'⟩, hW2⟩
      | exact ⟨⟨⟨fun hk => by simpa using h1 (by omega), ⟨h2, h3⟩, fun h => h4 (by omega)⟩, hW1'⟩, hW2'⟩
  · simp only [rubi312r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hdt, -, hc0, hL⟩ := ht
    set u1 := (env "d" * (env "m" + 1))⁻¹ with hu1_def
    set u2 := (env "m" + 1)⁻¹ with hu2_def
    have hU1 : env "d" * (env "m" + 1) * u1 = 1 := by rw [hu1_def]; exact mul_inv_cancel₀ hW1
    have hU2 : (env "m" + 1) * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hW2
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" * t) ^ k * (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ (q - 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, hkn, hkp1, hkp0, hkp0']
    have hEF : eval Interp.real (Function.update env "x" t) rubi312r5Nondeg.body = (env "d" * t) ^ k * (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ q := by
      simp [rubi312r5Nondeg, eval, Interp.real, hkm, hkp, hkn]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi312r5Nondeg.integrals.map (·.1)) Φ "x" w) rubi312r5Nondeg.result) =
        fun w => (env "d" * w) ^ (k + 1) * (env "a" + env "b" * Real.log (env "c" * w ^ j)) ^ q * u1 + -1 * env "b" * env "n" * env "p" * u2 * Φ "I1" w := by
      funext w
      simp [rubi312r5Nondeg, eval, Interp.real, recEnv, hkm1, hkn, hkp1, hkp, hm1, hu1_def, hu2_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hz : (env "d" * t) ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (hdt h)
      · exact Or.inr (by omega)
    have hz0 : (env "d" * t) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (hdt h)
      · exact Or.inr (by omega)
    have hd1 : HasDerivAt (fun w => (env "a" + env "b" * Real.log (env "c" * w ^ j))) (env "b" * ((j : ℝ) / t)) t :=
      ((OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hc0).const_mul _).const_add _
    have hPd : HasDerivAt (fun w => (env "d" * w) ^ (k + 1)) (((k + 1 : ℤ) : ℝ) * (env "d" * t) ^ (k + 1 - 1) * (env "d" * 1)) t :=
      HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hz) ((hasDerivAt_id' t).const_mul (env "d"))
    have hLd := (hasDerivAt_zpow q _ (Or.inr hq.le)).comp t hd1
    refine (((hPd.mul hLd).mul_const u1).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hz0]
    have htX := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hc0
    have hLq : (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ q = (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ (q - 1) * (env "a" + env "b" * Real.log (env "c" * t ^ j)) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hLq]
    generalize (env "d" * t) ^ k = Pk
    generalize (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ (q - 1) = Lq1
    generalize (j : ℝ) / t = X at htX ⊢
    clear_value u1 u2
    simp only [hm, hp, hn] at hU1 hU2 ⊢
    push_cast
    linear_combination (Pk * Lq1 * (env "a" + env "b" * Real.log (env "c" * t ^ j)) + Pk * Lq1 * (q : ℝ) * env "b" * (j : ℝ) * u2) * hU1 +
      (-(Pk * Lq1 * (q : ℝ) * env "b" * (j : ℝ) * env "d" * u1)) * hU2 + (Pk * Lq1 * (q : ℝ) * env "b" * env "d" * u1) * htX

/-- **3.1.2 #6** with `b d n (p + 1) ≠ 0` and `p < -1`, over ℝ: integration by parts, from `x (n/x) = n`. -/
theorem rubi312r6Nondeg_real : rubi312r6Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi312r6Nondeg.conditions rubi312r6Nondeg.body
    rubi312r6Nondeg.result rubi312r6Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hW1 : (env "b" * env "d" * env "n" * (env "p" + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi312r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW2 : (env "b" * env "n" * (env "p" + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi312r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi312r6Nondeg])
  rcases hkm : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi312r6Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi312r6Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi312r6Nondeg, Defined, eval, Interp.real, hkm, hkp, hkn] at h
  have hm : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hkm
  have hp : env "p" = (q : ℝ) := (intValue?_eq _ _).1 hkp
  have hn : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hkn
  have hq : q < -1 := by
    simp only [Cond.Holds, Defined, eval, Interp.real, true_and] at hg
    rw [hp] at hg
    exact_mod_cast hg
  have hkm1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkp1 : intValue? (env "p" + 1) = some (q + 1) := (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hkp0 : intValue? (env "p" + -1 * 1) = some (q - 1) := (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hkp0' : intValue? (env "p" + -1) = some (q - 1) := (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi312r6Nondeg.body →
      (k < 0 → env "d" * w ≠ 0) ∧ (j < 0 → w ≠ 0) ∧ 0 < env "c" * w ^ j ∧ (q < 0 → (env "a" + env "b" * Real.log (env "c" * w ^ j)) ≠ 0) := by
    intro w h
    simp [rubi312r6Nondeg, Defined, eval, Interp.real, hkm, hkp, hkn] at h
    first | exact ⟨fun hk => by simpa using h.1 hk, h.2.1.1, h.2.1.2, h.2.2⟩ | (trace_state; sorry)
  have ht := hD t hF.self_of_nhds
  have hW1' := hW1
  have hW2' := hW2
  simp only [ne_eq, mul_eq_zero, not_or] at hW1' hW2'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi312r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3, h4⟩ := hD w hw
    simp [Defined, eval, Interp.real, hkm, hkn, hkp1, hkp0, hkp0']
    first
      | exact ⟨fun hk => by simpa using h1 hk, ⟨h2, h3⟩, fun h => absurd h (by omega)⟩
      | exact ⟨fun hk => by simpa using h1 hk, ⟨h2, h3⟩, fun h => h4 (by omega)⟩
      | exact ⟨⟨⟨fun hk => by simpa using h1 (by omega), ⟨h2, h3⟩, h4⟩, hW1'⟩, hW2⟩
      | exact ⟨⟨⟨fun hk => by simpa using h1 (by omega), ⟨h2, h3⟩, fun h => h4 (by omega)⟩, hW1'⟩, hW2'⟩
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3, h4⟩ := hD w hw
    simp [rubi312r6Nondeg, Defined, eval, Interp.real, recEnv, hkm1, hkn, hkp1, hkp, hm1]
    first
      | exact ⟨fun hk => by simpa using h1 hk, ⟨h2, h3⟩, fun h => absurd h (by omega)⟩
      | exact ⟨fun hk => by simpa using h1 hk, ⟨h2, h3⟩, fun h => h4 (by omega)⟩
      | exact ⟨⟨⟨fun hk => by simpa using h1 (by omega), ⟨h2, h3⟩, h4⟩, hW1'⟩, hW2⟩
      | exact ⟨⟨⟨fun hk => by simpa using h1 (by omega), ⟨h2, h3⟩, fun h => h4 (by omega)⟩, hW1'⟩, hW2'⟩
  · simp only [rubi312r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hdt, -, hc0, hL⟩ := ht
    set u1 := (env "b" * env "d" * env "n" * (env "p" + 1))⁻¹ with hu1_def
    set u2 := (env "b" * env "n" * (env "p" + 1))⁻¹ with hu2_def
    have hU1 : env "b" * env "d" * env "n" * (env "p" + 1) * u1 = 1 := by rw [hu1_def]; exact mul_inv_cancel₀ hW1
    have hU2 : env "b" * env "n" * (env "p" + 1) * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hW2
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" * t) ^ k * (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ (q + 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, hkn, hkp1, hkp0, hkp0']
    have hEF : eval Interp.real (Function.update env "x" t) rubi312r6Nondeg.body = (env "d" * t) ^ k * (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ q := by
      simp [rubi312r6Nondeg, eval, Interp.real, hkm, hkp, hkn]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi312r6Nondeg.integrals.map (·.1)) Φ "x" w) rubi312r6Nondeg.result) =
        fun w => (env "d" * w) ^ (k + 1) * (env "a" + env "b" * Real.log (env "c" * w ^ j)) ^ (q + 1) * u1 + -1 * (env "m" + 1) * u2 * Φ "I1" w := by
      funext w
      simp [rubi312r6Nondeg, eval, Interp.real, recEnv, hkm1, hkn, hkp1, hkp, hm1, hu1_def, hu2_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hz : (env "d" * t) ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (hdt h)
      · exact Or.inr (by omega)
    have hz0 : (env "d" * t) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (hdt h)
      · exact Or.inr (by omega)
    have hd1 : HasDerivAt (fun w => (env "a" + env "b" * Real.log (env "c" * w ^ j))) (env "b" * ((j : ℝ) / t)) t :=
      ((OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hc0).const_mul _).const_add _
    have hPd : HasDerivAt (fun w => (env "d" * w) ^ (k + 1)) (((k + 1 : ℤ) : ℝ) * (env "d" * t) ^ (k + 1 - 1) * (env "d" * 1)) t :=
      HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hz) ((hasDerivAt_id' t).const_mul (env "d"))
    have hLd := (hasDerivAt_zpow (q + 1) _ (Or.inl (hL (by omega)))).comp t hd1
    refine (((hPd.mul hLd).mul_const u1).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hz0]
    have htX := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hc0
    generalize (env "d" * t) ^ k = Pk
    generalize (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ q = Y
    generalize (env "a" + env "b" * Real.log (env "c" * t ^ j)) ^ (q + 1) = Lq1
    generalize (j : ℝ) / t = X at htX ⊢
    clear_value u1 u2
    simp only [hm, hp, hn] at hU1 hU2 ⊢
    push_cast
    linear_combination (Pk * Y + Pk * Lq1 * ((k : ℝ) + 1) * u2) * hU1 +
      (-(Pk * Lq1 * ((k : ℝ) + 1) * env "d" * u1)) * hU2 + (Pk * Y * ((q : ℝ) + 1) * env "b" * env "d" * u1) * htX

end Proofs

end OSR.IntegrationRec69
