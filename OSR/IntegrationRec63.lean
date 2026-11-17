import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, fifteenth batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 4.7.9 #1, #2, #25 and
#26, from `S / (a + b S) = 1/b - (a/b) / (a + b S)` with `S = sin (c + d x)` or
`cos (c + d x)`; and 4.7.6 #1, #2, #16 and #17, the integrations by parts of
`(c + d x)^m sin^n cos` and its companions, with `m > 0`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec63

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








/-- **4.7.9 #1** with `b ≠ 0`, `m > 0` and `n > 0`: `sin / (a + b sin) = 1/b - (a/b) / (a + b sin)`. -/
theorem rubi479r1Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi479r1Nondeg.conditions rubi479r1Nondeg.body rubi479r1Nondeg.result rubi479r1Nondeg.integrals := by
  intro env hc t hF
  have hb0 : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi479r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg_n := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r1Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r1Nondeg, Defined, eval, hk_m] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r1Nondeg, Defined, eval, hk_m, hk_n] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_n
    rw [h_n] at hg_n
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((j : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_n
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "n" + -1 * 1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have e1' : I.toInt? (env "n" + -1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi479r1Nondeg.body → (env "a" + env "b" * I.sin (env "c" + env "d" * w)) ≠ 0 := by
    intro w h
    simp [rubi479r1Nondeg, Defined, eval, hk_m, hk_n, toInt?_neg_one] at h
    tauto
  have hD' : ∀ w, Defined I (Function.update env "x" w) rubi479r1Nondeg.body →
      Defined I (Function.update env "x" w) rubi479r1Nondeg.body := fun _ h => h
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have hA := hD w hw
      have hw' := hw
      simp [rubi479r1Nondeg, Defined, eval, hk_m, hk_n, toInt?_neg_one] at hw'
      simp [Defined, eval, hk_m, hk_n, e1, e1', toInt?_neg_one, hA]
      exact ⟨hw'.1.1, fun h => absurd h (by omega)⟩
    · filter_upwards [hF] with w hw
      have hA := hD w hw
      have hw' := hw
      simp [rubi479r1Nondeg, Defined, eval, hk_m, hk_n, toInt?_neg_one] at hw'
      simp [Defined, eval, hk_m, hk_n, e1, e1', toInt?_neg_one, hA]
      exact ⟨hw'.1.1, fun h => absurd h (by omega)⟩
  · exact Eventually.of_forall fun w => by
      simp [rubi479r1Nondeg, Defined, eval, recEnv, toInt?_neg_one, hb0]
  · simp only [rubi479r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ k * I.sin (env "c" + env "d" * t) ^ (j - 1)) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, hk_n, e1, e1']
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ k * I.sin (env "c" + env "d" * t) ^ (j - 1) * (env "a" + env "b" * I.sin (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, hk_n, e1, e1', toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi479r1Nondeg.body = (env "e" + env "f" * t) ^ k * I.sin (env "c" + env "d" * t) ^ j * (env "a" + env "b" * I.sin (env "c" + env "d" * t))⁻¹ := by
      simp [rubi479r1Nondeg, eval, hk_m, hk_n, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi479r1Nondeg.integrals.map (·.1)) Φ "x" w) rubi479r1Nondeg.result) =
        fun w => 1 * (env "b")⁻¹ * Φ "I1" w + -1 * env "a" * (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi479r1Nondeg, eval, recEnv, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hS : I.sin (env "c" + env "d" * t) ^ j = I.sin (env "c" + env "d" * t) ^ (j - 1) * I.sin (env "c" + env "d" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hS]
    have hAA : (env "a" + env "b" * I.sin (env "c" + env "d" * t)) * (env "a" + env "b" * I.sin (env "c" + env "d" * t))⁻¹ = 1 := mul_inv_cancel₀ ht
    have hbb : env "b" * (env "b")⁻¹ = 1 := mul_inv_cancel₀ hb0
    generalize (env "e" + env "f" * t) ^ k = P
    generalize I.sin (env "c" + env "d" * t) ^ (j - 1) = R
    generalize (env "a" + env "b" * I.sin (env "c" + env "d" * t))⁻¹ = Ai at hAA ⊢
    generalize (env "b")⁻¹ = bi at hbb ⊢
    linear_combination (-((P * R) * bi)) * hAA + ((P * R) * I.sin (env "c" + env "d" * t) * Ai) * hbb

theorem rubi479r1Nondeg_real : rubi479r1Nondeg.Holds .real :=
  rubi479r1Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi479r1Nondeg_complex : rubi479r1Nondeg.Holds .complex :=
  rubi479r1Nondeg_holds Interp.complex Interp.complex_lt_rat

/-- **4.7.9 #2** with `b ≠ 0`, `m > 0` and `n > 0`: `cos / (a + b cos) = 1/b - (a/b) / (a + b cos)`. -/
theorem rubi479r2Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi479r2Nondeg.conditions rubi479r2Nondeg.body rubi479r2Nondeg.result rubi479r2Nondeg.integrals := by
  intro env hc t hF
  have hb0 : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi479r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg_n := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r2Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r2Nondeg, Defined, eval, hk_m] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r2Nondeg, Defined, eval, hk_m, hk_n] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_n
    rw [h_n] at hg_n
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((j : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_n
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "n" + -1 * 1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have e1' : I.toInt? (env "n" + -1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi479r2Nondeg.body → (env "a" + env "b" * I.cos (env "c" + env "d" * w)) ≠ 0 := by
    intro w h
    simp [rubi479r2Nondeg, Defined, eval, hk_m, hk_n, toInt?_neg_one] at h
    tauto
  have hD' : ∀ w, Defined I (Function.update env "x" w) rubi479r2Nondeg.body →
      Defined I (Function.update env "x" w) rubi479r2Nondeg.body := fun _ h => h
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have hA := hD w hw
      have hw' := hw
      simp [rubi479r2Nondeg, Defined, eval, hk_m, hk_n, toInt?_neg_one] at hw'
      simp [Defined, eval, hk_m, hk_n, e1, e1', toInt?_neg_one, hA]
      exact ⟨hw'.1.1, fun h => absurd h (by omega)⟩
    · filter_upwards [hF] with w hw
      have hA := hD w hw
      have hw' := hw
      simp [rubi479r2Nondeg, Defined, eval, hk_m, hk_n, toInt?_neg_one] at hw'
      simp [Defined, eval, hk_m, hk_n, e1, e1', toInt?_neg_one, hA]
      exact ⟨hw'.1.1, fun h => absurd h (by omega)⟩
  · exact Eventually.of_forall fun w => by
      simp [rubi479r2Nondeg, Defined, eval, recEnv, toInt?_neg_one, hb0]
  · simp only [rubi479r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ k * I.cos (env "c" + env "d" * t) ^ (j - 1)) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, hk_n, e1, e1']
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ k * I.cos (env "c" + env "d" * t) ^ (j - 1) * (env "a" + env "b" * I.cos (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, hk_n, e1, e1', toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi479r2Nondeg.body = (env "e" + env "f" * t) ^ k * I.cos (env "c" + env "d" * t) ^ j * (env "a" + env "b" * I.cos (env "c" + env "d" * t))⁻¹ := by
      simp [rubi479r2Nondeg, eval, hk_m, hk_n, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi479r2Nondeg.integrals.map (·.1)) Φ "x" w) rubi479r2Nondeg.result) =
        fun w => 1 * (env "b")⁻¹ * Φ "I1" w + -1 * env "a" * (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi479r2Nondeg, eval, recEnv, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hS : I.cos (env "c" + env "d" * t) ^ j = I.cos (env "c" + env "d" * t) ^ (j - 1) * I.cos (env "c" + env "d" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hS]
    have hAA : (env "a" + env "b" * I.cos (env "c" + env "d" * t)) * (env "a" + env "b" * I.cos (env "c" + env "d" * t))⁻¹ = 1 := mul_inv_cancel₀ ht
    have hbb : env "b" * (env "b")⁻¹ = 1 := mul_inv_cancel₀ hb0
    generalize (env "e" + env "f" * t) ^ k = P
    generalize I.cos (env "c" + env "d" * t) ^ (j - 1) = R
    generalize (env "a" + env "b" * I.cos (env "c" + env "d" * t))⁻¹ = Ai at hAA ⊢
    generalize (env "b")⁻¹ = bi at hbb ⊢
    linear_combination (-((P * R) * bi)) * hAA + ((P * R) * I.cos (env "c" + env "d" * t) * Ai) * hbb

theorem rubi479r2Nondeg_real : rubi479r2Nondeg.Holds .real :=
  rubi479r2Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi479r2Nondeg_complex : rubi479r2Nondeg.Holds .complex :=
  rubi479r2Nondeg_holds Interp.complex Interp.complex_lt_rat

/-- **4.7.9 #25** with `b ≠ 0`, `m > 0` and `n > 0`: `sin / (a + b sin) = 1/b - (a/b) / (a + b sin)`. -/
theorem rubi479r25Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi479r25Nondeg.conditions rubi479r25Nondeg.body rubi479r25Nondeg.result rubi479r25Nondeg.integrals := by
  intro env hc t hF
  have hb0 : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi479r25Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg_n := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r25Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r25Nondeg, Defined, eval, hk_m] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r25Nondeg, Defined, eval, hk_m, hk_n] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  rcases hk_p : I.toInt? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r25Nondeg, Defined, eval, hk_m, hk_n, hk_p] at h
  have h_p : env "p" = (l : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_n
    rw [h_n] at hg_n
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((j : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_n
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "n" + -1 * 1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have e1' : I.toInt? (env "n" + -1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi479r25Nondeg.body → (env "a" + env "b" * I.sin (env "c" + env "d" * w)) ≠ 0 := by
    intro w h
    simp [rubi479r25Nondeg, Defined, eval, hk_m, hk_n, hk_p, toInt?_neg_one] at h
    tauto
  have hD' : ∀ w, Defined I (Function.update env "x" w) rubi479r25Nondeg.body →
      Defined I (Function.update env "x" w) rubi479r25Nondeg.body := fun _ h => h
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r25Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have hA := hD w hw
      have hw' := hw
      simp [rubi479r25Nondeg, Defined, eval, hk_m, hk_n, hk_p, toInt?_neg_one] at hw'
      simp [Defined, eval, hk_m, hk_n, hk_p, e1, e1', toInt?_neg_one, hA]
      exact ⟨hw'.1.1, fun h => absurd h (by omega)⟩
    · filter_upwards [hF] with w hw
      have hA := hD w hw
      have hw' := hw
      simp [rubi479r25Nondeg, Defined, eval, hk_m, hk_n, hk_p, toInt?_neg_one] at hw'
      simp [Defined, eval, hk_m, hk_n, hk_p, e1, e1', toInt?_neg_one, hA]
      exact ⟨hw'.1.1, fun h => absurd h (by omega)⟩
  · exact Eventually.of_forall fun w => by
      simp [rubi479r25Nondeg, Defined, eval, recEnv, toInt?_neg_one, hb0]
  · simp only [rubi479r25Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ k * I.cos (env "c" + env "d" * t) ^ l * I.sin (env "c" + env "d" * t) ^ (j - 1)) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, hk_n, hk_p, e1, e1']
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ k * I.cos (env "c" + env "d" * t) ^ l * I.sin (env "c" + env "d" * t) ^ (j - 1) * (env "a" + env "b" * I.sin (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, hk_n, hk_p, e1, e1', toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi479r25Nondeg.body = (env "e" + env "f" * t) ^ k * I.cos (env "c" + env "d" * t) ^ l * I.sin (env "c" + env "d" * t) ^ j * (env "a" + env "b" * I.sin (env "c" + env "d" * t))⁻¹ := by
      simp [rubi479r25Nondeg, eval, hk_m, hk_n, hk_p, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi479r25Nondeg.integrals.map (·.1)) Φ "x" w) rubi479r25Nondeg.result) =
        fun w => 1 * (env "b")⁻¹ * Φ "I1" w + -1 * env "a" * (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi479r25Nondeg, eval, recEnv, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hS : I.sin (env "c" + env "d" * t) ^ j = I.sin (env "c" + env "d" * t) ^ (j - 1) * I.sin (env "c" + env "d" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hS]
    have hAA : (env "a" + env "b" * I.sin (env "c" + env "d" * t)) * (env "a" + env "b" * I.sin (env "c" + env "d" * t))⁻¹ = 1 := mul_inv_cancel₀ ht
    have hbb : env "b" * (env "b")⁻¹ = 1 := mul_inv_cancel₀ hb0
    generalize (env "e" + env "f" * t) ^ k = P
    generalize I.sin (env "c" + env "d" * t) ^ (j - 1) = R
    generalize I.cos (env "c" + env "d" * t) ^ l = Q
    generalize (env "a" + env "b" * I.sin (env "c" + env "d" * t))⁻¹ = Ai at hAA ⊢
    generalize (env "b")⁻¹ = bi at hbb ⊢
    linear_combination (-((P * Q * R) * bi)) * hAA + ((P * Q * R) * I.sin (env "c" + env "d" * t) * Ai) * hbb

theorem rubi479r25Nondeg_real : rubi479r25Nondeg.Holds .real :=
  rubi479r25Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi479r25Nondeg_complex : rubi479r25Nondeg.Holds .complex :=
  rubi479r25Nondeg_holds Interp.complex Interp.complex_lt_rat

/-- **4.7.9 #26** with `b ≠ 0`, `m > 0` and `n > 0`: `cos / (a + b cos) = 1/b - (a/b) / (a + b cos)`. -/
theorem rubi479r26Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi479r26Nondeg.conditions rubi479r26Nondeg.body rubi479r26Nondeg.result rubi479r26Nondeg.integrals := by
  intro env hc t hF
  have hb0 : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi479r26Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg_n := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r26Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r26Nondeg, Defined, eval, hk_m] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r26Nondeg, Defined, eval, hk_m, hk_n] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  rcases hk_p : I.toInt? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r26Nondeg, Defined, eval, hk_m, hk_n, hk_p] at h
  have h_p : env "p" = (l : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_n
    rw [h_n] at hg_n
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((j : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_n
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "n" + -1 * 1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have e1' : I.toInt? (env "n" + -1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi479r26Nondeg.body → (env "a" + env "b" * I.cos (env "c" + env "d" * w)) ≠ 0 := by
    intro w h
    simp [rubi479r26Nondeg, Defined, eval, hk_m, hk_n, hk_p, toInt?_neg_one] at h
    tauto
  have hD' : ∀ w, Defined I (Function.update env "x" w) rubi479r26Nondeg.body →
      Defined I (Function.update env "x" w) rubi479r26Nondeg.body := fun _ h => h
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r26Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have hA := hD w hw
      have hw' := hw
      simp [rubi479r26Nondeg, Defined, eval, hk_m, hk_n, hk_p, toInt?_neg_one] at hw'
      simp [Defined, eval, hk_m, hk_n, hk_p, e1, e1', toInt?_neg_one, hA]
      exact ⟨hw'.1.1, fun h => absurd h (by omega)⟩
    · filter_upwards [hF] with w hw
      have hA := hD w hw
      have hw' := hw
      simp [rubi479r26Nondeg, Defined, eval, hk_m, hk_n, hk_p, toInt?_neg_one] at hw'
      simp [Defined, eval, hk_m, hk_n, hk_p, e1, e1', toInt?_neg_one, hA]
      exact ⟨hw'.1.1, fun h => absurd h (by omega)⟩
  · exact Eventually.of_forall fun w => by
      simp [rubi479r26Nondeg, Defined, eval, recEnv, toInt?_neg_one, hb0]
  · simp only [rubi479r26Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ k * I.sin (env "c" + env "d" * t) ^ l * I.cos (env "c" + env "d" * t) ^ (j - 1)) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, hk_n, hk_p, e1, e1']
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ k * I.sin (env "c" + env "d" * t) ^ l * I.cos (env "c" + env "d" * t) ^ (j - 1) * (env "a" + env "b" * I.cos (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, hk_n, hk_p, e1, e1', toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi479r26Nondeg.body = (env "e" + env "f" * t) ^ k * I.sin (env "c" + env "d" * t) ^ l * I.cos (env "c" + env "d" * t) ^ j * (env "a" + env "b" * I.cos (env "c" + env "d" * t))⁻¹ := by
      simp [rubi479r26Nondeg, eval, hk_m, hk_n, hk_p, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi479r26Nondeg.integrals.map (·.1)) Φ "x" w) rubi479r26Nondeg.result) =
        fun w => 1 * (env "b")⁻¹ * Φ "I1" w + -1 * env "a" * (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi479r26Nondeg, eval, recEnv, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hS : I.cos (env "c" + env "d" * t) ^ j = I.cos (env "c" + env "d" * t) ^ (j - 1) * I.cos (env "c" + env "d" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hS]
    have hAA : (env "a" + env "b" * I.cos (env "c" + env "d" * t)) * (env "a" + env "b" * I.cos (env "c" + env "d" * t))⁻¹ = 1 := mul_inv_cancel₀ ht
    have hbb : env "b" * (env "b")⁻¹ = 1 := mul_inv_cancel₀ hb0
    generalize (env "e" + env "f" * t) ^ k = P
    generalize I.cos (env "c" + env "d" * t) ^ (j - 1) = R
    generalize I.sin (env "c" + env "d" * t) ^ l = Q
    generalize (env "a" + env "b" * I.cos (env "c" + env "d" * t))⁻¹ = Ai at hAA ⊢
    generalize (env "b")⁻¹ = bi at hbb ⊢
    linear_combination (-((P * Q * R) * bi)) * hAA + ((P * Q * R) * I.cos (env "c" + env "d" * t) * Ai) * hbb

theorem rubi479r26Nondeg_real : rubi479r26Nondeg.Holds .real :=
  rubi479r26Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi479r26Nondeg_complex : rubi479r26Nondeg.Holds .complex :=
  rubi479r26Nondeg_holds Interp.complex Interp.complex_lt_rat

/-- **4.7.6 #1** with `b (n + 1) ≠ 0` and `m > 0`.** -/
theorem rubi476r1Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivRecHolds I "x" rubi476r1Nondeg.conditions rubi476r1Nondeg.body rubi476r1Nondeg.result rubi476r1Nondeg.integrals := by
  intro env hc t hF
  have hW : (env "b" * (env "n" + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi476r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg_m := hc (.gt (.var "m") (.int 0)) (by simp [rubi476r1Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi476r1Nondeg, Defined, eval, hk_m] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi476r1Nondeg, Defined, eval, hk_m, hk_n] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have hk : 0 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_m
    rw [h_m] at hg_m
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_m
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e1' : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2 : I.toInt? (env "n" + 1) = some (j + 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi476r1Nondeg.body → (j < 0 → I.sin (env "a" + env "b" * w) ≠ 0) := by
    intro w h
    simp [rubi476r1Nondeg, Defined, eval, hk_m, hk_n] at h
    tauto
  have ht := hD t hF.self_of_nhds
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi476r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, e1, e1', e2]
    first | exact ⟨fun h' => absurd h' (by omega), fun h' => h (by omega)⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi476r1Nondeg, Defined, eval, recEnv, hk_m, e2, toInt?_neg_one]
    first | exact ⟨⟨fun h' => absurd h' (by omega), fun h' => h (by omega)⟩, hW'⟩ | (trace_state; sorry)
  · simp only [rubi476r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "c" + env "d" * t) ^ (k - 1) * I.sin (env "a" + env "b" * t) ^ (j + 1)) t := by
      convert hΦ using 1
      simp [eval, e1, e1', e2]
    have hEF : eval I (Function.update env "x" t) rubi476r1Nondeg.body = (env "c" + env "d" * t) ^ k * I.cos (env "a" + env "b" * t) * I.sin (env "a" + env "b" * t) ^ j := by
      simp [rubi476r1Nondeg, eval, hk_m, hk_n]
      try ring
    set u := (env "b" * (env "n" + 1))⁻¹ with hu_def
    have hU : (env "b" * (env "n" + 1)) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi476r1Nondeg.integrals.map (·.1)) Φ "x" w) rubi476r1Nondeg.result) =
        fun w => 1 * (env "c" + env "d" * w) ^ k * I.sin (env "a" + env "b" * w) ^ (j + 1) * u + -1 * env "d" * env "m" * u * Φ "I1" w := by
      funext w
      simp [rubi476r1Nondeg, eval, recEnv, hk_m, e2, toInt?_neg_one, hu_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hG1 : I.sin (env "a" + env "b" * t) ≠ 0 ∨ 0 ≤ j + 1 := by
      by_cases h : j + 1 < 0
      · exact Or.inl (ht (by omega))
      · exact Or.inr (by omega)
    have hG0 : I.sin (env "a" + env "b" * t) ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    have hlinE : HasDerivAt (fun w => (env "c" + env "d" * w)) (env "d") t := by
      have := ((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c")
      convert this using 1 <;> first | ring | (funext w; simp only [id])
    have hlinA : HasDerivAt (fun w => (env "a" + env "b" * w)) (env "b") t := by
      have := ((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")
      convert this using 1 <;> first | ring | (funext w; simp only [id])
    have hGd : HasDerivAt (fun w => I.sin (env "a" + env "b" * w)) (I.cos (env "a" + env "b" * t) * env "b") t := by
      have := HasDerivAt.comp t (hs _) hlinA
      convert this using 1 <;> first | rfl | ring1 | (funext w; rfl)
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow k _ (Or.inr (by omega))) hlinE).const_mul (1)).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (j + 1) _ hG1) hGd)).mul_const u).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hP : (env "c" + env "d" * t) ^ k = (env "c" + env "d" * t) ^ (k - 1) * (env "c" + env "d" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hP, zpow_succ_of _ _ hG0]
    generalize (env "c" + env "d" * t) ^ (k - 1) = P
    generalize I.sin (env "a" + env "b" * t) ^ j = Y
    clear_value u
    simp only [h_m, h_n] at hU ⊢
    push_cast
    linear_combination (P * Y * (env "c" + env "d" * t) * I.cos (env "a" + env "b" * t)) * hU

theorem rubi476r1Nondeg_real : rubi476r1Nondeg.Holds .real :=
  rubi476r1Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos

theorem rubi476r1Nondeg_complex : rubi476r1Nondeg.Holds .complex :=
  rubi476r1Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos

/-- **4.7.6 #2** with `b (n + 1) ≠ 0` and `m > 0`.** -/
theorem rubi476r2Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivRecHolds I "x" rubi476r2Nondeg.conditions rubi476r2Nondeg.body rubi476r2Nondeg.result rubi476r2Nondeg.integrals := by
  intro env hc t hF
  have hW : (env "b" * (env "n" + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi476r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg_m := hc (.gt (.var "m") (.int 0)) (by simp [rubi476r2Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi476r2Nondeg, Defined, eval, hk_m] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi476r2Nondeg, Defined, eval, hk_m, hk_n] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have hk : 0 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_m
    rw [h_m] at hg_m
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_m
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e1' : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2 : I.toInt? (env "n" + 1) = some (j + 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi476r2Nondeg.body → (j < 0 → I.cos (env "a" + env "b" * w) ≠ 0) := by
    intro w h
    simp [rubi476r2Nondeg, Defined, eval, hk_m, hk_n] at h
    tauto
  have ht := hD t hF.self_of_nhds
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi476r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, e1, e1', e2]
    first | exact ⟨fun h' => absurd h' (by omega), fun h' => h (by omega)⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi476r2Nondeg, Defined, eval, recEnv, hk_m, e2, toInt?_neg_one]
    first | exact ⟨⟨fun h' => absurd h' (by omega), fun h' => h (by omega)⟩, hW'⟩ | (trace_state; sorry)
  · simp only [rubi476r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "c" + env "d" * t) ^ (k - 1) * I.cos (env "a" + env "b" * t) ^ (j + 1)) t := by
      convert hΦ using 1
      simp [eval, e1, e1', e2]
    have hEF : eval I (Function.update env "x" t) rubi476r2Nondeg.body = (env "c" + env "d" * t) ^ k * I.sin (env "a" + env "b" * t) * I.cos (env "a" + env "b" * t) ^ j := by
      simp [rubi476r2Nondeg, eval, hk_m, hk_n]
      try ring
    set u := (env "b" * (env "n" + 1))⁻¹ with hu_def
    have hU : (env "b" * (env "n" + 1)) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi476r2Nondeg.integrals.map (·.1)) Φ "x" w) rubi476r2Nondeg.result) =
        fun w => (-1) * (env "c" + env "d" * w) ^ k * I.cos (env "a" + env "b" * w) ^ (j + 1) * u + env "d" * env "m" * u * Φ "I1" w := by
      funext w
      simp [rubi476r2Nondeg, eval, recEnv, hk_m, e2, toInt?_neg_one, hu_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hG1 : I.cos (env "a" + env "b" * t) ≠ 0 ∨ 0 ≤ j + 1 := by
      by_cases h : j + 1 < 0
      · exact Or.inl (ht (by omega))
      · exact Or.inr (by omega)
    have hG0 : I.cos (env "a" + env "b" * t) ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    have hlinE : HasDerivAt (fun w => (env "c" + env "d" * w)) (env "d") t := by
      have := ((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c")
      convert this using 1 <;> first | ring | (funext w; simp only [id])
    have hlinA : HasDerivAt (fun w => (env "a" + env "b" * w)) (env "b") t := by
      have := ((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")
      convert this using 1 <;> first | ring | (funext w; simp only [id])
    have hGd : HasDerivAt (fun w => I.cos (env "a" + env "b" * w)) (-I.sin (env "a" + env "b" * t) * env "b") t := by
      have := HasDerivAt.comp t (hcs _) hlinA
      convert this using 1 <;> first | rfl | ring1 | (funext w; rfl)
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow k _ (Or.inr (by omega))) hlinE).const_mul ((-1))).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (j + 1) _ hG1) hGd)).mul_const u).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hP : (env "c" + env "d" * t) ^ k = (env "c" + env "d" * t) ^ (k - 1) * (env "c" + env "d" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hP, zpow_succ_of _ _ hG0]
    generalize (env "c" + env "d" * t) ^ (k - 1) = P
    generalize I.cos (env "a" + env "b" * t) ^ j = Y
    clear_value u
    simp only [h_m, h_n] at hU ⊢
    push_cast
    linear_combination (P * Y * (env "c" + env "d" * t) * I.sin (env "a" + env "b" * t)) * hU

theorem rubi476r2Nondeg_real : rubi476r2Nondeg.Holds .real :=
  rubi476r2Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos

theorem rubi476r2Nondeg_complex : rubi476r2Nondeg.Holds .complex :=
  rubi476r2Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos

/-- **4.7.6 #16** with `b d (n + 1) ≠ 0` and `m > 0`.** -/
theorem rubi476r16Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivRecHolds I "x" rubi476r16Nondeg.conditions rubi476r16Nondeg.body rubi476r16Nondeg.result rubi476r16Nondeg.integrals := by
  intro env hc t hF
  have hW : (env "b" * env "d" * (env "n" + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi476r16Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg_m := hc (.gt (.var "m") (.int 0)) (by simp [rubi476r16Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi476r16Nondeg, Defined, eval, hk_m] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi476r16Nondeg, Defined, eval, hk_m, hk_n] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have hk : 0 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_m
    rw [h_m] at hg_m
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_m
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e1' : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2 : I.toInt? (env "n" + 1) = some (j + 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi476r16Nondeg.body → (j < 0 → (env "a" + env "b" * I.sin (env "c" + env "d" * w)) ≠ 0) := by
    intro w h
    simp [rubi476r16Nondeg, Defined, eval, hk_m, hk_n] at h
    tauto
  have ht := hD t hF.self_of_nhds
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi476r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, e1, e1', e2]
    first | exact ⟨fun h' => absurd h' (by omega), fun h' => h (by omega)⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi476r16Nondeg, Defined, eval, recEnv, hk_m, e2, toInt?_neg_one]
    first | exact ⟨⟨fun h' => absurd h' (by omega), fun h' => h (by omega)⟩, hW'⟩ | (trace_state; sorry)
  · simp only [rubi476r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ (k - 1) * (env "a" + env "b" * I.sin (env "c" + env "d" * t)) ^ (j + 1)) t := by
      convert hΦ using 1
      simp [eval, e1, e1', e2]
    have hEF : eval I (Function.update env "x" t) rubi476r16Nondeg.body = (env "e" + env "f" * t) ^ k * I.cos (env "c" + env "d" * t) * (env "a" + env "b" * I.sin (env "c" + env "d" * t)) ^ j := by
      simp [rubi476r16Nondeg, eval, hk_m, hk_n]
      try ring
    set u := (env "b" * env "d" * (env "n" + 1))⁻¹ with hu_def
    have hU : (env "b" * env "d" * (env "n" + 1)) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi476r16Nondeg.integrals.map (·.1)) Φ "x" w) rubi476r16Nondeg.result) =
        fun w => 1 * (env "e" + env "f" * w) ^ k * (env "a" + env "b" * I.sin (env "c" + env "d" * w)) ^ (j + 1) * u + -1 * env "f" * env "m" * u * Φ "I1" w := by
      funext w
      simp [rubi476r16Nondeg, eval, recEnv, hk_m, e2, toInt?_neg_one, hu_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hG1 : (env "a" + env "b" * I.sin (env "c" + env "d" * t)) ≠ 0 ∨ 0 ≤ j + 1 := by
      by_cases h : j + 1 < 0
      · exact Or.inl (ht (by omega))
      · exact Or.inr (by omega)
    have hG0 : (env "a" + env "b" * I.sin (env "c" + env "d" * t)) ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    have hlinE : HasDerivAt (fun w => (env "e" + env "f" * w)) (env "f") t := by
      have := ((hasDerivAt_id' t).const_mul (env "f")).const_add (env "e")
      convert this using 1 <;> first | ring | (funext w; simp only [id])
    have hlinA : HasDerivAt (fun w => (env "c" + env "d" * w)) (env "d") t := by
      have := ((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c")
      convert this using 1 <;> first | ring | (funext w; simp only [id])
    have hGd : HasDerivAt (fun w => (env "a" + env "b" * I.sin (env "c" + env "d" * w))) (env "b" * (I.cos (env "c" + env "d" * t) * env "d")) t := by
      have := (HasDerivAt.comp t (hs _) hlinA).const_mul (env "b") |>.const_add (env "a")
      convert this using 1 <;> first | rfl | ring1 | (funext w; rfl)
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow k _ (Or.inr (by omega))) hlinE).const_mul (1)).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (j + 1) _ hG1) hGd)).mul_const u).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hP : (env "e" + env "f" * t) ^ k = (env "e" + env "f" * t) ^ (k - 1) * (env "e" + env "f" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hP, zpow_succ_of _ _ hG0]
    generalize (env "e" + env "f" * t) ^ (k - 1) = P
    generalize (env "a" + env "b" * I.sin (env "c" + env "d" * t)) ^ j = Y
    clear_value u
    simp only [h_m, h_n] at hU ⊢
    push_cast
    linear_combination (P * Y * (env "e" + env "f" * t) * I.cos (env "c" + env "d" * t)) * hU

theorem rubi476r16Nondeg_real : rubi476r16Nondeg.Holds .real :=
  rubi476r16Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos

theorem rubi476r16Nondeg_complex : rubi476r16Nondeg.Holds .complex :=
  rubi476r16Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos

/-- **4.7.6 #17** with `b d (n + 1) ≠ 0` and `m > 0`.** -/
theorem rubi476r17Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivRecHolds I "x" rubi476r17Nondeg.conditions rubi476r17Nondeg.body rubi476r17Nondeg.result rubi476r17Nondeg.integrals := by
  intro env hc t hF
  have hW : (env "b" * env "d" * (env "n" + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi476r17Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg_m := hc (.gt (.var "m") (.int 0)) (by simp [rubi476r17Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi476r17Nondeg, Defined, eval, hk_m] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi476r17Nondeg, Defined, eval, hk_m, hk_n] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have hk : 0 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_m
    rw [h_m] at hg_m
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_m
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e1' : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2 : I.toInt? (env "n" + 1) = some (j + 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi476r17Nondeg.body → (j < 0 → (env "a" + env "b" * I.cos (env "c" + env "d" * w)) ≠ 0) := by
    intro w h
    simp [rubi476r17Nondeg, Defined, eval, hk_m, hk_n] at h
    tauto
  have ht := hD t hF.self_of_nhds
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi476r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, e1, e1', e2]
    first | exact ⟨fun h' => absurd h' (by omega), fun h' => h (by omega)⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi476r17Nondeg, Defined, eval, recEnv, hk_m, e2, toInt?_neg_one]
    first | exact ⟨⟨fun h' => absurd h' (by omega), fun h' => h (by omega)⟩, hW'⟩ | (trace_state; sorry)
  · simp only [rubi476r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ (k - 1) * (env "a" + env "b" * I.cos (env "c" + env "d" * t)) ^ (j + 1)) t := by
      convert hΦ using 1
      simp [eval, e1, e1', e2]
    have hEF : eval I (Function.update env "x" t) rubi476r17Nondeg.body = (env "e" + env "f" * t) ^ k * I.sin (env "c" + env "d" * t) * (env "a" + env "b" * I.cos (env "c" + env "d" * t)) ^ j := by
      simp [rubi476r17Nondeg, eval, hk_m, hk_n]
      try ring
    set u := (env "b" * env "d" * (env "n" + 1))⁻¹ with hu_def
    have hU : (env "b" * env "d" * (env "n" + 1)) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi476r17Nondeg.integrals.map (·.1)) Φ "x" w) rubi476r17Nondeg.result) =
        fun w => (-1) * (env "e" + env "f" * w) ^ k * (env "a" + env "b" * I.cos (env "c" + env "d" * w)) ^ (j + 1) * u + env "f" * env "m" * u * Φ "I1" w := by
      funext w
      simp [rubi476r17Nondeg, eval, recEnv, hk_m, e2, toInt?_neg_one, hu_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hG1 : (env "a" + env "b" * I.cos (env "c" + env "d" * t)) ≠ 0 ∨ 0 ≤ j + 1 := by
      by_cases h : j + 1 < 0
      · exact Or.inl (ht (by omega))
      · exact Or.inr (by omega)
    have hG0 : (env "a" + env "b" * I.cos (env "c" + env "d" * t)) ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    have hlinE : HasDerivAt (fun w => (env "e" + env "f" * w)) (env "f") t := by
      have := ((hasDerivAt_id' t).const_mul (env "f")).const_add (env "e")
      convert this using 1 <;> first | ring | (funext w; simp only [id])
    have hlinA : HasDerivAt (fun w => (env "c" + env "d" * w)) (env "d") t := by
      have := ((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c")
      convert this using 1 <;> first | ring | (funext w; simp only [id])
    have hGd : HasDerivAt (fun w => (env "a" + env "b" * I.cos (env "c" + env "d" * w))) (env "b" * (-I.sin (env "c" + env "d" * t) * env "d")) t := by
      have := (HasDerivAt.comp t (hcs _) hlinA).const_mul (env "b") |>.const_add (env "a")
      convert this using 1 <;> first | rfl | ring1 | (funext w; rfl)
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow k _ (Or.inr (by omega))) hlinE).const_mul ((-1))).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (j + 1) _ hG1) hGd)).mul_const u).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hP : (env "e" + env "f" * t) ^ k = (env "e" + env "f" * t) ^ (k - 1) * (env "e" + env "f" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hP, zpow_succ_of _ _ hG0]
    generalize (env "e" + env "f" * t) ^ (k - 1) = P
    generalize (env "a" + env "b" * I.cos (env "c" + env "d" * t)) ^ j = Y
    clear_value u
    simp only [h_m, h_n] at hU ⊢
    push_cast
    linear_combination (P * Y * (env "e" + env "f" * t) * I.sin (env "c" + env "d" * t)) * hU

theorem rubi476r17Nondeg_real : rubi476r17Nondeg.Holds .real :=
  rubi476r17Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos

theorem rubi476r17Nondeg_complex : rubi476r17Nondeg.Holds .complex :=
  rubi476r17Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos

end Proofs

end OSR.IntegrationRec63
