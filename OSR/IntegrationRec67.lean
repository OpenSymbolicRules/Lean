import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, nineteenth batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 4.7.9 #16, #27 and
#30, which split quotients with `tan` using `tan cos = sin` where `tan` is
defined (a hypothesis instantiated over ℝ and ℂ).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec67

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








/-- **4.7.9 #16** with `a ≠ 0`, `m > 0` and `n > 0`: with `sin = tan cos`, `tan / (a + b cos) = tan/a - (b/a) sin / (a + b cos)`.** -/
theorem rubi479r16Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (htan : ∀ u : 𝕜, I.tanDefined u → I.tan u * I.cos u = I.sin u) :
    AntiderivRecHolds I "x" rubi479r16Nondeg.conditions rubi479r16Nondeg.body rubi479r16Nondeg.result rubi479r16Nondeg.integrals := by
  intro env hc t hF
  have ha0 : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi479r16Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg_m := hc (.gt (.var "m") (.int 0)) (by simp [rubi479r16Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r16Nondeg, Defined, eval, hk_m] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have hp_m : 0 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_m
    rw [h_m] at hg_m
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_m
    exact_mod_cast (hlt _ _).1 h'
  have hg_n := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r16Nondeg])
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r16Nondeg, Defined, eval, hk_m, hk_n] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have hp_n : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_n
    rw [h_n] at hg_n
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((j : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_n
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "n" + -1 * 1) = some (j + -1 * 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have e1' : I.toInt? (env "n" + -1) = some (j + -1 * 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have h0 := hF.self_of_nhds
  simp [rubi479r16Nondeg, Defined, eval, hk_m, hk_n, toInt?_neg_one] at h0
  have htd : I.tanDefined (env "c" + env "d" * t) := by tauto
  have hA0 : (env "a" + env "b" * I.cos (env "c" + env "d" * t)) ≠ 0 := by tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      simp [rubi479r16Nondeg, Defined, eval, hk_m, hk_n, toInt?_neg_one] at hw
      simp [Defined, eval, hk_m, hk_n, e1, e1', toInt?_neg_one]
      first
        | done
        | exact hw.1
        | exact ⟨⟨hw.1.1, hw.1.2.1, fun h => absurd h (by omega)⟩, hw.2⟩
        | exact ⟨⟨hw.1.1.1, fun h => absurd h (by omega)⟩, hw.1.2.1, fun h => absurd h (by omega)⟩
        | exact ⟨⟨⟨hw.1.1.1, fun h => absurd h (by omega)⟩, hw.1.2.1, fun h => absurd h (by omega)⟩, hw.2⟩
  · exact Eventually.of_forall fun w => by simp [rubi479r16Nondeg, Defined, eval, recEnv, toInt?_neg_one, ha0]
  · simp only [rubi479r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") (((env "e" + (env "f" * t)) ^ k * I.tan (env "c" + (env "d" * t)) ^ j)) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, hk_n, e1, e1', toInt?_neg_one]
    have hΦ2' : HasDerivAt (Φ "I2") (((((env "e" + (env "f" * t)) ^ k * I.sin (env "c" + (env "d" * t))) * I.tan (env "c" + (env "d" * t)) ^ (j + ((-1) * 1))) * (env "a" + (env "b" * I.cos (env "c" + (env "d" * t))))⁻¹)) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, hk_n, e1, e1', toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi479r16Nondeg.body = (((env "e" + (env "f" * t)) ^ k * I.tan (env "c" + (env "d" * t)) ^ j) * (env "a" + (env "b" * I.cos (env "c" + (env "d" * t))))⁻¹) := by
      simp [rubi479r16Nondeg, eval, hk_m, hk_n, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi479r16Nondeg.integrals.map (·.1)) Φ "x" w) rubi479r16Nondeg.result) =
        fun w => (((1 * (env "a")⁻¹) * Φ "I1" w) + ((((-1) * env "b") * (env "a")⁻¹) * Φ "I2" w)) := by
      funext w
      simp [rubi479r16Nondeg, eval, recEnv, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hs_j : I.tan (env "c" + env "d" * t) ^ j = I.tan (env "c" + env "d" * t) ^ (j - 1) * I.tan (env "c" + env "d" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hs_j, show j + -1 * 1 = j - 1 by ring]

    have hts := htan _ htd
    have hAA : (env "a" + env "b" * I.cos (env "c" + env "d" * t)) * (env "a" + env "b" * I.cos (env "c" + env "d" * t))⁻¹ = 1 := mul_inv_cancel₀ hA0
    have haa : env "a" * (env "a")⁻¹ = 1 := mul_inv_cancel₀ ha0
    generalize (env "e" + env "f" * t) ^ k = P
    generalize I.tan (env "c" + env "d" * t) ^ (j - 1) = Tn1
    generalize (env "a" + env "b" * I.cos (env "c" + env "d" * t))⁻¹ = Ai at hAA ⊢
    generalize (env "a")⁻¹ = ai at haa ⊢
    linear_combination (P * Tn1) * ((I.tan (env "c" + env "d" * t) * Ai) * haa - (I.tan (env "c" + env "d" * t) * ai) * hAA + (env "b" * ai * Ai) * hts)

theorem rubi479r16Nondeg_real : rubi479r16Nondeg.Holds .real :=
  rubi479r16Nondeg_holds Interp.real Interp.real_lt_rat (fun u hu => by
    show Real.tan u * Real.cos u = Real.sin u
    rw [Real.tan_eq_sin_div_cos]; exact div_mul_cancel₀ _ hu)

theorem rubi479r16Nondeg_complex : rubi479r16Nondeg.Holds .complex :=
  rubi479r16Nondeg_holds Interp.complex Interp.complex_lt_rat (fun u hu => by
    show Complex.tan u * Complex.cos u = Complex.sin u
    rw [Complex.tan]; exact div_mul_cancel₀ _ hu)

/-- **4.7.9 #27** with `b ≠ 0`, `m, n, p > 0`: `cos tan = sin` splits `cos tan / (a + b sin)`.** -/
theorem rubi479r27Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (htan : ∀ u : 𝕜, I.tanDefined u → I.tan u * I.cos u = I.sin u) :
    AntiderivRecHolds I "x" rubi479r27Nondeg.conditions rubi479r27Nondeg.body rubi479r27Nondeg.result rubi479r27Nondeg.integrals := by
  intro env hc t hF
  have hb0 : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi479r27Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg_m := hc (.gt (.var "m") (.int 0)) (by simp [rubi479r27Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r27Nondeg, Defined, eval, hk_m] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have hp_m : 0 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_m
    rw [h_m] at hg_m
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_m
    exact_mod_cast (hlt _ _).1 h'
  have hg_n := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r27Nondeg])
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r27Nondeg, Defined, eval, hk_m, hk_n] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have hp_n : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_n
    rw [h_n] at hg_n
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((j : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_n
    exact_mod_cast (hlt _ _).1 h'
  have hg_p := hc (.gt (.var "p") (.int 0)) (by simp [rubi479r27Nondeg])
  rcases hk_p : I.toInt? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r27Nondeg, Defined, eval, hk_m, hk_n, hk_p] at h
  have h_p : env "p" = (l : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hp_p : 0 < l := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_p
    rw [h_p] at hg_p
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((l : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_p
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "n" + -1 * 1) = some (j + -1 * 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have e1' : I.toInt? (env "n" + -1) = some (j + -1 * 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have e2 : I.toInt? (env "p" + -1 * 1) = some (l + -1 * 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have e2' : I.toInt? (env "p" + -1) = some (l + -1 * 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have h0 := hF.self_of_nhds
  simp [rubi479r27Nondeg, Defined, eval, hk_m, hk_n, hk_p, toInt?_neg_one] at h0
  have htd : I.tanDefined (env "c" + env "d" * t) := by tauto
  have hA0 : (env "a" + env "b" * I.sin (env "c" + env "d" * t)) ≠ 0 := by tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r27Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      simp [rubi479r27Nondeg, Defined, eval, hk_m, hk_n, hk_p, toInt?_neg_one] at hw
      simp [Defined, eval, hk_m, hk_n, hk_p, e1, e1', e2, e2', toInt?_neg_one]
      first
        | done
        | exact hw.1
        | exact ⟨⟨hw.1.1, hw.1.2.1, fun h => absurd h (by omega)⟩, hw.2⟩
        | exact ⟨⟨hw.1.1.1, fun h => absurd h (by omega)⟩, hw.1.2.1, fun h => absurd h (by omega)⟩
        | exact ⟨⟨⟨hw.1.1.1, fun h => absurd h (by omega)⟩, hw.1.2.1, fun h => absurd h (by omega)⟩, hw.2⟩
  · exact Eventually.of_forall fun w => by simp [rubi479r27Nondeg, Defined, eval, recEnv, toInt?_neg_one, hb0]
  · simp only [rubi479r27Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((((env "e" + (env "f" * t)) ^ k * I.cos (env "c" + (env "d" * t)) ^ (l + ((-1) * 1))) * I.tan (env "c" + (env "d" * t)) ^ (j + ((-1) * 1)))) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, hk_n, hk_p, e1, e1', e2, e2', toInt?_neg_one]
    have hΦ2' : HasDerivAt (Φ "I2") (((((env "e" + (env "f" * t)) ^ k * I.cos (env "c" + (env "d" * t)) ^ (l + ((-1) * 1))) * I.tan (env "c" + (env "d" * t)) ^ (j + ((-1) * 1))) * (env "a" + (env "b" * I.sin (env "c" + (env "d" * t))))⁻¹)) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, hk_n, hk_p, e1, e1', e2, e2', toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi479r27Nondeg.body = ((((env "e" + (env "f" * t)) ^ k * I.cos (env "c" + (env "d" * t)) ^ l) * I.tan (env "c" + (env "d" * t)) ^ j) * (env "a" + (env "b" * I.sin (env "c" + (env "d" * t))))⁻¹) := by
      simp [rubi479r27Nondeg, eval, hk_m, hk_n, hk_p, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi479r27Nondeg.integrals.map (·.1)) Φ "x" w) rubi479r27Nondeg.result) =
        fun w => (((1 * (env "b")⁻¹) * Φ "I1" w) + ((((-1) * env "a") * (env "b")⁻¹) * Φ "I2" w)) := by
      funext w
      simp [rubi479r27Nondeg, eval, recEnv, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hs_j : I.tan (env "c" + env "d" * t) ^ j = I.tan (env "c" + env "d" * t) ^ (j - 1) * I.tan (env "c" + env "d" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    have hs_l : I.cos (env "c" + env "d" * t) ^ l = I.cos (env "c" + env "d" * t) ^ (l - 1) * I.cos (env "c" + env "d" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hs_j, hs_l, show j + -1 * 1 = j - 1 by ring, show l + -1 * 1 = l - 1 by ring]

    have hts := htan _ htd
    have hAA : (env "a" + env "b" * I.sin (env "c" + env "d" * t)) * (env "a" + env "b" * I.sin (env "c" + env "d" * t))⁻¹ = 1 := mul_inv_cancel₀ hA0
    have haa : env "b" * (env "b")⁻¹ = 1 := mul_inv_cancel₀ hb0
    generalize (env "e" + env "f" * t) ^ k = P
    generalize I.tan (env "c" + env "d" * t) ^ (j - 1) = Tn1
    generalize I.cos (env "c" + env "d" * t) ^ (l - 1) = Cp1
    generalize (env "a" + env "b" * I.sin (env "c" + env "d" * t))⁻¹ = Ai at hAA ⊢
    generalize (env "b")⁻¹ = ai at haa ⊢
    linear_combination (P * Tn1 * Cp1) * ((-ai) * hAA + (I.sin (env "c" + env "d" * t) * Ai) * haa - Ai * hts)

theorem rubi479r27Nondeg_real : rubi479r27Nondeg.Holds .real :=
  rubi479r27Nondeg_holds Interp.real Interp.real_lt_rat (fun u hu => by
    show Real.tan u * Real.cos u = Real.sin u
    rw [Real.tan_eq_sin_div_cos]; exact div_mul_cancel₀ _ hu)

theorem rubi479r27Nondeg_complex : rubi479r27Nondeg.Holds .complex :=
  rubi479r27Nondeg_holds Interp.complex Interp.complex_lt_rat (fun u hu => by
    show Complex.tan u * Complex.cos u = Complex.sin u
    rw [Complex.tan]; exact div_mul_cancel₀ _ hu)

/-- **4.7.9 #30** with `a ≠ 0`, `m, n, p > 0`: with `sin = tan cos`, `tan / (a + b cos) = tan/a - (b/a) sin / (a + b cos)`.** -/
theorem rubi479r30Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (htan : ∀ u : 𝕜, I.tanDefined u → I.tan u * I.cos u = I.sin u) :
    AntiderivRecHolds I "x" rubi479r30Nondeg.conditions rubi479r30Nondeg.body rubi479r30Nondeg.result rubi479r30Nondeg.integrals := by
  intro env hc t hF
  have ha0 : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi479r30Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg_m := hc (.gt (.var "m") (.int 0)) (by simp [rubi479r30Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r30Nondeg, Defined, eval, hk_m] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have hp_m : 0 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_m
    rw [h_m] at hg_m
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_m
    exact_mod_cast (hlt _ _).1 h'
  have hg_n := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r30Nondeg])
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r30Nondeg, Defined, eval, hk_m, hk_n] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have hp_n : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_n
    rw [h_n] at hg_n
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((j : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_n
    exact_mod_cast (hlt _ _).1 h'
  have hg_p := hc (.gt (.var "p") (.int 0)) (by simp [rubi479r30Nondeg])
  rcases hk_p : I.toInt? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r30Nondeg, Defined, eval, hk_m, hk_n, hk_p] at h
  have h_p : env "p" = (l : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hp_p : 0 < l := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_p
    rw [h_p] at hg_p
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((l : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_p
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "n" + -1 * 1) = some (j + -1 * 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have e1' : I.toInt? (env "n" + -1) = some (j + -1 * 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have e2 : I.toInt? (env "p" + 1) = some (l + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have h0 := hF.self_of_nhds
  simp [rubi479r30Nondeg, Defined, eval, hk_m, hk_n, hk_p, toInt?_neg_one] at h0
  have htd : I.tanDefined (env "c" + env "d" * t) := by tauto
  have hA0 : (env "a" + env "b" * I.cos (env "c" + env "d" * t)) ≠ 0 := by tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r30Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      simp [rubi479r30Nondeg, Defined, eval, hk_m, hk_n, hk_p, toInt?_neg_one] at hw
      simp [Defined, eval, hk_m, hk_n, hk_p, e1, e1', e2, toInt?_neg_one]
      first
        | done
        | exact hw.1
        | exact ⟨⟨hw.1.1, hw.1.2.1, fun h => absurd h (by omega)⟩, hw.2⟩
        | exact ⟨⟨hw.1.1.1, fun h => absurd h (by omega)⟩, hw.1.2.1, fun h => absurd h (by omega)⟩
        | exact ⟨⟨⟨hw.1.1.1, fun h => absurd h (by omega)⟩, hw.1.2.1, fun h => absurd h (by omega)⟩, hw.2⟩
  · exact Eventually.of_forall fun w => by simp [rubi479r30Nondeg, Defined, eval, recEnv, toInt?_neg_one, ha0]
  · simp only [rubi479r30Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((((env "e" + (env "f" * t)) ^ k * I.sin (env "c" + (env "d" * t)) ^ l) * I.tan (env "c" + (env "d" * t)) ^ j)) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, hk_n, hk_p, e1, e1', e2, toInt?_neg_one]
    have hΦ2' : HasDerivAt (Φ "I2") (((((env "e" + (env "f" * t)) ^ k * I.sin (env "c" + (env "d" * t)) ^ (l + 1)) * I.tan (env "c" + (env "d" * t)) ^ (j + ((-1) * 1))) * (env "a" + (env "b" * I.cos (env "c" + (env "d" * t))))⁻¹)) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, hk_n, hk_p, e1, e1', e2, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi479r30Nondeg.body = ((((env "e" + (env "f" * t)) ^ k * I.sin (env "c" + (env "d" * t)) ^ l) * I.tan (env "c" + (env "d" * t)) ^ j) * (env "a" + (env "b" * I.cos (env "c" + (env "d" * t))))⁻¹) := by
      simp [rubi479r30Nondeg, eval, hk_m, hk_n, hk_p, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi479r30Nondeg.integrals.map (·.1)) Φ "x" w) rubi479r30Nondeg.result) =
        fun w => (((1 * (env "a")⁻¹) * Φ "I1" w) + ((((-1) * env "b") * (env "a")⁻¹) * Φ "I2" w)) := by
      funext w
      simp [rubi479r30Nondeg, eval, recEnv, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hs_j : I.tan (env "c" + env "d" * t) ^ j = I.tan (env "c" + env "d" * t) ^ (j - 1) * I.tan (env "c" + env "d" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    have hs_l : I.sin (env "c" + env "d" * t) ^ (l + 1) = I.sin (env "c" + env "d" * t) ^ l * I.sin (env "c" + env "d" * t) := zpow_succ_of _ _ (Or.inr (by omega))
    rw [hs_j, hs_l, show j + -1 * 1 = j - 1 by ring]

    have hts := htan _ htd
    have hAA : (env "a" + env "b" * I.cos (env "c" + env "d" * t)) * (env "a" + env "b" * I.cos (env "c" + env "d" * t))⁻¹ = 1 := mul_inv_cancel₀ hA0
    have haa : env "a" * (env "a")⁻¹ = 1 := mul_inv_cancel₀ ha0
    generalize (env "e" + env "f" * t) ^ k = P
    generalize I.tan (env "c" + env "d" * t) ^ (j - 1) = Tn1
    generalize I.sin (env "c" + env "d" * t) ^ l = Sp
    generalize (env "a" + env "b" * I.cos (env "c" + env "d" * t))⁻¹ = Ai at hAA ⊢
    generalize (env "a")⁻¹ = ai at haa ⊢
    linear_combination (P * Tn1 * Sp) * ((I.tan (env "c" + env "d" * t) * Ai) * haa - (I.tan (env "c" + env "d" * t) * ai) * hAA + (env "b" * ai * Ai) * hts)

theorem rubi479r30Nondeg_real : rubi479r30Nondeg.Holds .real :=
  rubi479r30Nondeg_holds Interp.real Interp.real_lt_rat (fun u hu => by
    show Real.tan u * Real.cos u = Real.sin u
    rw [Real.tan_eq_sin_div_cos]; exact div_mul_cancel₀ _ hu)

theorem rubi479r30Nondeg_complex : rubi479r30Nondeg.Holds .complex :=
  rubi479r30Nondeg_holds Interp.complex Interp.complex_lt_rat (fun u hu => by
    show Complex.tan u * Complex.cos u = Complex.sin u
    rw [Complex.tan]; exact div_mul_cancel₀ _ hu)

end Proofs

end OSR.IntegrationRec67
