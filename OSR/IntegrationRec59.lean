import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, eleventh batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 1.1.3.5 #24, #25 and
#26, which split `(c + d x²)^q (e + f x²)^r / (a + b x²)` by polynomial
identities in `x²`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec59

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








/-- **1.1.3.5 #25** with `b ≠ 0` and `q > 1`: `d (a + b x²) + (b c - a d) = b (c + d x²)`. -/
theorem rubi1135r25Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1135r25Nondeg.conditions rubi1135r25Nondeg.body rubi1135r25Nondeg.result rubi1135r25Nondeg.integrals := by
  intro env hc t hF
  have hb0 : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi1135r25Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hg_q := hc (.gt (.var "q") (.int 1)) (by simp [rubi1135r25Nondeg])
  rcases hk_q : I.toInt? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r25Nondeg, Defined, eval, hk_q] at h
  have h_q : env "q" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_q
  rcases hk_r : I.toInt? (env "r") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r25Nondeg, Defined, eval, hk_q, hk_r] at h
  have h_r : env "r" = (l : 𝕜) := (I.toInt?_eq _ _).1 hk_r
  have hk1 : 1 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_q
    rw [h_q] at hg_q
    have h' : I.lt ((((1 : ℤ)) : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_q
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "q" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have e1' : I.toInt? (env "q" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1135r25Nondeg.body →
      (k < 0 → (env "c" + env "d" * w ^ 2) ≠ 0) ∧ (l < 0 → (env "e" + env "f" * w ^ 2) ≠ 0) ∧ (env "a" + env "b" * w ^ 2) ≠ 0 := by
    intro w h
    simp [rubi1135r25Nondeg, Defined, eval, hk_q, hk_r, toInt?_two, toInt?_neg_one] at h
    refine ⟨?_, ?_, ?_⟩ <;> tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1135r25Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have hw' := hD w hw
      simp [Defined, eval, hk_q, hk_r, e1, e1', toInt?_two, toInt?_neg_one, hw'.2.2]
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> first | exact absurd h (by omega) | exact hw'.1 (by omega) | exact hw'.2.1 (by omega)
    · filter_upwards [hF] with w hw
      have hw' := hD w hw
      simp [Defined, eval, hk_q, hk_r, e1, e1', toInt?_two, toInt?_neg_one, hw'.2.2]
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> first | exact absurd h (by omega) | exact hw'.1 (by omega) | exact hw'.2.1 (by omega)
  · exact Eventually.of_forall fun w => by
      simp [rubi1135r25Nondeg, Defined, eval, recEnv, toInt?_two, toInt?_neg_one]
      first | exact hb0 | (intro h; apply hW; linear_combination (env "b" * env "c" + -1 * env "a" * env "d") * h)
  · simp only [rubi1135r25Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "c" + env "d" * t ^ 2) ^ (k - 1) * (env "e" + env "f" * t ^ 2) ^ l) t := by
      convert hΦ1 using 1
      simp [eval, hk_q, hk_r, e1, e1', toInt?_two, toInt?_neg_one]
      try first | ring1 | simp
    have hΦ2' : HasDerivAt (Φ "I2") ((env "c" + env "d" * t ^ 2) ^ (k - 1) * (env "e" + env "f" * t ^ 2) ^ l * (env "a" + env "b" * t ^ 2)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, hk_q, hk_r, e1, e1', toInt?_two, toInt?_neg_one]
      try first | ring1 | simp
    have hEF : eval I (Function.update env "x" t) rubi1135r25Nondeg.body = (env "c" + env "d" * t ^ 2) ^ k * (env "e" + env "f" * t ^ 2) ^ l * (env "a" + env "b" * t ^ 2)⁻¹ := by
      simp [rubi1135r25Nondeg, eval, hk_q, hk_r, toInt?_two, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi1135r25Nondeg.integrals.map (·.1)) Φ "x" w) rubi1135r25Nondeg.result) =
        fun w => env "d" * (env "b")⁻¹ * Φ "I1" w + (env "b" * env "c" + -1 * env "a" * env "d") * (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1135r25Nondeg, eval, recEnv, toInt?_two, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hZ : (env "c" + env "d" * t ^ 2) ^ k = (env "c" + env "d" * t ^ 2) ^ (k - 1) * (env "c" + env "d" * t ^ 2) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hZ]
    have hA : (env "a" + env "b" * t ^ 2) * (env "a" + env "b" * t ^ 2)⁻¹ = 1 := mul_inv_cancel₀ ht.2.2
    have hb : env "b" * (env "b")⁻¹ = 1 := mul_inv_cancel₀ hb0
    generalize (env "c" + env "d" * t ^ 2) ^ (k - 1) = Z
    generalize (env "e" + env "f" * t ^ 2) ^ l = Y
    generalize (env "a" + env "b" * t ^ 2)⁻¹ = Ai at hA ⊢
    generalize (env "b")⁻¹ = bi at hb ⊢
    linear_combination (Z * Y) * ((Ai * (env "c" + env "d" * t ^ 2)) * hb + (-(env "d" * bi)) * hA)

theorem rubi1135r25Nondeg_real : rubi1135r25Nondeg.Holds .real :=
  rubi1135r25Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1135r25Nondeg_complex : rubi1135r25Nondeg.Holds .complex :=
  rubi1135r25Nondeg_holds Interp.complex Interp.complex_lt_rat

/-- **1.1.3.5 #26** with `(b c - a d)² ≠ 0` and `q < -1`: `b² (c + d x²)² - d (a + b x²) (2 b c - a d + b d x²) = (b c - a d)²`. -/
theorem rubi1135r26Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1135r26Nondeg.conditions rubi1135r26Nondeg.body rubi1135r26Nondeg.result rubi1135r26Nondeg.integrals := by
  intro env hc t hF
  have hW : (env "b" * env "c" + -1 * env "a" * env "d") ^ 2 ≠ 0 := by
    have h := hc (.ne (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2)) (.int 0)) (by simp [rubi1135r26Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hg_q := hc (.gt (.int (-1)) (.var "q")) (by simp [rubi1135r26Nondeg])
  rcases hk_q : I.toInt? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r26Nondeg, Defined, eval, hk_q] at h
  have h_q : env "q" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_q
  rcases hk_r : I.toInt? (env "r") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r26Nondeg, Defined, eval, hk_q, hk_r] at h
  have h_r : env "r" = (l : 𝕜) := (I.toInt?_eq _ _).1 hk_r
  have hk1 : k < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_q
    rw [h_q] at hg_q
    have h' : I.lt ((k : ℚ) : 𝕜) ((((-1 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_q
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "q" + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1135r26Nondeg.body →
      (k < 0 → (env "c" + env "d" * w ^ 2) ≠ 0) ∧ (l < 0 → (env "e" + env "f" * w ^ 2) ≠ 0) ∧ (env "a" + env "b" * w ^ 2) ≠ 0 := by
    intro w h
    simp [rubi1135r26Nondeg, Defined, eval, hk_q, hk_r, toInt?_two, toInt?_neg_one] at h
    refine ⟨?_, ?_, ?_⟩ <;> tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1135r26Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have hw' := hD w hw
      simp [Defined, eval, hk_q, hk_r, e1, toInt?_two, toInt?_neg_one, hw'.2.2]
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> first | exact absurd h (by omega) | exact hw'.1 (by omega) | exact hw'.2.1 (by omega)
    · filter_upwards [hF] with w hw
      have hw' := hD w hw
      simp [Defined, eval, hk_q, hk_r, e1, toInt?_two, toInt?_neg_one, hw'.2.2]
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> first | exact absurd h (by omega) | exact hw'.1 (by omega) | exact hw'.2.1 (by omega)
  · exact Eventually.of_forall fun w => by
      simp [rubi1135r26Nondeg, Defined, eval, recEnv, toInt?_two, toInt?_neg_one]
      first | exact hb0 | (intro h; apply hW; linear_combination (env "b" * env "c" + -1 * env "a" * env "d") * h)
  · simp only [rubi1135r26Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "c" + env "d" * t ^ 2) ^ (k + 2) * (env "e" + env "f" * t ^ 2) ^ l * (env "a" + env "b" * t ^ 2)⁻¹) t := by
      convert hΦ1 using 1
      simp [eval, hk_q, hk_r, e1, toInt?_two, toInt?_neg_one]
      try first | ring1 | simp
    have hΦ2' : HasDerivAt (Φ "I2") ((env "c" + env "d" * t ^ 2) ^ k * (env "e" + env "f" * t ^ 2) ^ l * (2 * env "b" * env "c" + -1 * env "a" * env "d" + env "b" * env "d" * t ^ 2)) t := by
      convert hΦ2 using 1
      simp [eval, hk_q, hk_r, e1, toInt?_two, toInt?_neg_one]
      try first | ring1 | simp
    have hEF : eval I (Function.update env "x" t) rubi1135r26Nondeg.body = (env "c" + env "d" * t ^ 2) ^ k * (env "e" + env "f" * t ^ 2) ^ l * (env "a" + env "b" * t ^ 2)⁻¹ := by
      simp [rubi1135r26Nondeg, eval, hk_q, hk_r, toInt?_two, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi1135r26Nondeg.integrals.map (·.1)) Φ "x" w) rubi1135r26Nondeg.result) =
        fun w => env "b" ^ 2 * ((env "b" * env "c" + -1 * env "a" * env "d") ^ 2)⁻¹ * Φ "I1" w + -1 * env "d" * ((env "b" * env "c" + -1 * env "a" * env "d") ^ 2)⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1135r26Nondeg, eval, recEnv, toInt?_two, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hC0 : (env "c" + env "d" * t ^ 2) ≠ 0 := ht.1 (by omega)
    have hZ : (env "c" + env "d" * t ^ 2) ^ (k + 2) = (env "c" + env "d" * t ^ 2) ^ k * (env "c" + env "d" * t ^ 2) ^ 2 := by
      rw [zpow_add₀ hC0]; norm_cast
    rw [hZ]
    have hA : (env "a" + env "b" * t ^ 2) * (env "a" + env "b" * t ^ 2)⁻¹ = 1 := mul_inv_cancel₀ ht.2.2
    have hu : (env "b" * env "c" + -1 * env "a" * env "d") ^ 2 * ((env "b" * env "c" + -1 * env "a" * env "d") ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hW
    generalize (env "c" + env "d" * t ^ 2) ^ k = Z
    generalize (env "e" + env "f" * t ^ 2) ^ l = Y
    generalize (env "a" + env "b" * t ^ 2)⁻¹ = Ai at hA ⊢
    generalize ((env "b" * env "c" + -1 * env "a" * env "d") ^ 2)⁻¹ = u at hu ⊢
    linear_combination (Z * Y) * (Ai * hu + (env "d" * u * (2 * env "b" * env "c" + -1 * env "a" * env "d" + env "b" * env "d" * t ^ 2)) * hA)

theorem rubi1135r26Nondeg_real : rubi1135r26Nondeg.Holds .real :=
  rubi1135r26Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1135r26Nondeg_complex : rubi1135r26Nondeg.Holds .complex :=
  rubi1135r26Nondeg_holds Interp.complex Interp.complex_lt_rat

/-- **1.1.3.5 #24** with `(b c - a d)² ≠ 0`, `q < -1` and `r > 1`: `b (b e - a f) (c + d x²)² - (a + b x²) K(x) = (b c - a d)² (e + f x²)`. -/
theorem rubi1135r24Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1135r24Nondeg.conditions rubi1135r24Nondeg.body rubi1135r24Nondeg.result rubi1135r24Nondeg.integrals := by
  intro env hc t hF
  have hW : (env "b" * env "c" + -1 * env "a" * env "d") ^ 2 ≠ 0 := by
    have h := hc (.ne (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2)) (.int 0)) (by simp [rubi1135r24Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hg_q := hc (.gt (.int (-1)) (.var "q")) (by simp [rubi1135r24Nondeg])
  have hg_r := hc (.gt (.var "r") (.int 1)) (by simp [rubi1135r24Nondeg])
  rcases hk_q : I.toInt? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r24Nondeg, Defined, eval, hk_q] at h
  have h_q : env "q" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_q
  rcases hk_r : I.toInt? (env "r") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r24Nondeg, Defined, eval, hk_q, hk_r] at h
  have h_r : env "r" = (l : 𝕜) := (I.toInt?_eq _ _).1 hk_r
  have hk1 : k < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_q
    rw [h_q] at hg_q
    have h' : I.lt ((k : ℚ) : 𝕜) ((((-1 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_q
    exact_mod_cast (hlt _ _).1 h'
  have hl1 : 1 < l := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_r
    rw [h_r] at hg_r
    have h' : I.lt ((((1 : ℤ)) : ℚ) : 𝕜) ((l : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_r
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "q" + 2) = some (k + 2) := (I.toInt?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have e2 : I.toInt? (env "r" + -1 * 1) = some (l - 1) := (I.toInt?_eq _ _).2 (by rw [h_r]; push_cast; ring)
  have e2' : I.toInt? (env "r" + -1) = some (l - 1) := (I.toInt?_eq _ _).2 (by rw [h_r]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1135r24Nondeg.body →
      (k < 0 → (env "c" + env "d" * w ^ 2) ≠ 0) ∧ (l < 0 → (env "e" + env "f" * w ^ 2) ≠ 0) ∧ (env "a" + env "b" * w ^ 2) ≠ 0 := by
    intro w h
    simp [rubi1135r24Nondeg, Defined, eval, hk_q, hk_r, toInt?_two, toInt?_neg_one] at h
    refine ⟨?_, ?_, ?_⟩ <;> tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1135r24Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have hw' := hD w hw
      simp [Defined, eval, hk_q, hk_r, e1, e2, e2', toInt?_two, toInt?_neg_one, hw'.2.2]
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> first | exact absurd h (by omega) | exact hw'.1 (by omega) | exact hw'.2.1 (by omega)
    · filter_upwards [hF] with w hw
      have hw' := hD w hw
      simp [Defined, eval, hk_q, hk_r, e1, e2, e2', toInt?_two, toInt?_neg_one, hw'.2.2]
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> first | exact absurd h (by omega) | exact hw'.1 (by omega) | exact hw'.2.1 (by omega)
  · exact Eventually.of_forall fun w => by
      simp [rubi1135r24Nondeg, Defined, eval, recEnv, toInt?_two, toInt?_neg_one]
      first | exact hb0 | (intro h; apply hW; linear_combination (env "b" * env "c" + -1 * env "a" * env "d") * h)
  · simp only [rubi1135r24Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "c" + env "d" * t ^ 2) ^ (k + 2) * (env "e" + env "f" * t ^ 2) ^ (l - 1) * (env "a" + env "b" * t ^ 2)⁻¹) t := by
      convert hΦ1 using 1
      simp [eval, hk_q, hk_r, e1, e2, e2', toInt?_two, toInt?_neg_one]
      try first | ring1 | simp
    have hΦ2' : HasDerivAt (Φ "I2") ((env "c" + env "d" * t ^ 2) ^ k * (env "e" + env "f" * t ^ 2) ^ (l - 1) * (2 * env "b" * env "c" * env "d" * env "e" + -1 * env "a" * env "d" ^ 2 * env "e" + -1 * env "b" * env "c" ^ 2 * env "f" + env "d" ^ 2 * (env "b" * env "e" + -1 * env "a" * env "f") * t ^ 2)) t := by
      convert hΦ2 using 1
      simp [eval, hk_q, hk_r, e1, e2, e2', toInt?_two, toInt?_neg_one]
      try first | ring1 | simp
    have hEF : eval I (Function.update env "x" t) rubi1135r24Nondeg.body = (env "c" + env "d" * t ^ 2) ^ k * (env "e" + env "f" * t ^ 2) ^ l * (env "a" + env "b" * t ^ 2)⁻¹ := by
      simp [rubi1135r24Nondeg, eval, hk_q, hk_r, toInt?_two, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi1135r24Nondeg.integrals.map (·.1)) Φ "x" w) rubi1135r24Nondeg.result) =
        fun w => env "b" * (env "b" * env "e" + -1 * env "a" * env "f") * ((env "b" * env "c" + -1 * env "a" * env "d") ^ 2)⁻¹ * Φ "I1" w + -1 * 1 * ((env "b" * env "c" + -1 * env "a" * env "d") ^ 2)⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1135r24Nondeg, eval, recEnv, toInt?_two, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hC0 : (env "c" + env "d" * t ^ 2) ≠ 0 := ht.1 (by omega)
    have hZ : (env "c" + env "d" * t ^ 2) ^ (k + 2) = (env "c" + env "d" * t ^ 2) ^ k * (env "c" + env "d" * t ^ 2) ^ 2 := by
      rw [zpow_add₀ hC0]; norm_cast
    have hY : (env "e" + env "f" * t ^ 2) ^ l = (env "e" + env "f" * t ^ 2) ^ (l - 1) * (env "e" + env "f" * t ^ 2) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hZ, hY]
    have hA : (env "a" + env "b" * t ^ 2) * (env "a" + env "b" * t ^ 2)⁻¹ = 1 := mul_inv_cancel₀ ht.2.2
    have hu : (env "b" * env "c" + -1 * env "a" * env "d") ^ 2 * ((env "b" * env "c" + -1 * env "a" * env "d") ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hW
    generalize (env "c" + env "d" * t ^ 2) ^ k = Z
    generalize (env "e" + env "f" * t ^ 2) ^ (l - 1) = Y
    generalize (env "a" + env "b" * t ^ 2)⁻¹ = Ai at hA ⊢
    generalize ((env "b" * env "c" + -1 * env "a" * env "d") ^ 2)⁻¹ = u at hu ⊢
    linear_combination (Z * Y) * ((Ai * (env "e" + env "f" * t ^ 2)) * hu + (u * (2 * env "b" * env "c" * env "d" * env "e" + -1 * env "a" * env "d" ^ 2 * env "e" + -1 * env "b" * env "c" ^ 2 * env "f" + env "d" ^ 2 * (env "b" * env "e" + -1 * env "a" * env "f") * t ^ 2)) * hA)

theorem rubi1135r24Nondeg_real : rubi1135r24Nondeg.Holds .real :=
  rubi1135r24Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1135r24Nondeg_complex : rubi1135r24Nondeg.Holds .complex :=
  rubi1135r24Nondeg_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec59
