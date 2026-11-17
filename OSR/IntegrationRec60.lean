import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, twelfth batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 1.1.3.5 #30, from
`d (a + b xⁿ) + (b c - a d) = b (c + d xⁿ)` with `p < 0` and `q > 0`, and
1.2.1.2 #43 and #44 (`m > 1`), whose derivative identity is `(m - 1)` times
the converted condition `c d² - b d e + a e² = 0`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec60

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








/-- **1.1.3.5 #30** with `b ≠ 0`, `p < 0` and `q > 0`: `d (a + b xⁿ) + (b c - a d) = b (c + d xⁿ)`. -/
theorem rubi1135r30Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1135r30Nondeg.conditions rubi1135r30Nondeg.body rubi1135r30Nondeg.result rubi1135r30Nondeg.integrals := by
  intro env hc t hF
  have hb0 : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi1135r30Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hg_p := hc (.gt (.int 0) (.var "p")) (by simp [rubi1135r30Nondeg])
  have hg_q := hc (.gt (.var "q") (.int 0)) (by simp [rubi1135r30Nondeg])
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r30Nondeg, Defined, eval, hk_n] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  rcases hk_p : I.toInt? (env "p") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r30Nondeg, Defined, eval, hk_n, hk_p] at h
  have h_p : env "p" = (i : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  rcases hk_q : I.toInt? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r30Nondeg, Defined, eval, hk_n, hk_p, hk_q] at h
  have h_q : env "q" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_q
  rcases hk_r : I.toInt? (env "r") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r30Nondeg, Defined, eval, hk_n, hk_p, hk_q, hk_r] at h
  have h_r : env "r" = (l : 𝕜) := (I.toInt?_eq _ _).1 hk_r
  have hi0 : i < 0 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_p
    rw [h_p] at hg_p
    have h' : I.lt ((i : ℚ) : 𝕜) ((((0 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_p
    exact_mod_cast (hlt _ _).1 h'
  have hk0 : 0 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_q
    rw [h_q] at hg_q
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_q
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "p" + 1) = some (i + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have e2 : I.toInt? (env "q" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have e2' : I.toInt? (env "q" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1135r30Nondeg.body →
      (j < 0 → w ≠ 0) ∧ (i < 0 → (env "a" + env "b" * w ^ j) ≠ 0) ∧ (k < 0 → (env "c" + env "d" * w ^ j) ≠ 0) ∧ (l < 0 → (env "e" + env "f" * w ^ j) ≠ 0) := by
    intro w h
    simp [rubi1135r30Nondeg, Defined, eval, hk_n, hk_p, hk_q, hk_r, toInt?_two, toInt?_neg_one] at h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1135r30Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have hw' := hD w hw
      simp [Defined, eval, hk_n, hk_p, hk_q, hk_r, e1, e2, e2', toInt?_two, toInt?_neg_one]
      obtain ⟨hj, hi, hk, hl⟩ := hw'
      exact ⟨⟨⟨hj, fun h => hi (by omega)⟩, hj, fun h => absurd h (by omega)⟩, hj, hl⟩
    · filter_upwards [hF] with w hw
      have hw' := hD w hw
      simp [Defined, eval, hk_n, hk_p, hk_q, hk_r, e1, e2, e2', toInt?_two, toInt?_neg_one]
      obtain ⟨hj, hi, hk, hl⟩ := hw'
      exact ⟨⟨⟨hj, fun h => hi (by omega)⟩, hj, fun h => absurd h (by omega)⟩, hj, hl⟩
  · exact Eventually.of_forall fun w => by
      simp [rubi1135r30Nondeg, Defined, eval, recEnv, toInt?_two, toInt?_neg_one]
      exact hb0
  · simp only [rubi1135r30Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "a" + env "b" * t ^ j) ^ (i + 1) * (env "c" + env "d" * t ^ j) ^ (k - 1) * (env "e" + env "f" * t ^ j) ^ l) t := by
      convert hΦ1 using 1
      simp [eval, hk_n, hk_p, hk_q, hk_r, e1, e2, e2', toInt?_two, toInt?_neg_one]
      try first | ring1 | simp
    have hΦ2' : HasDerivAt (Φ "I2") ((env "a" + env "b" * t ^ j) ^ i * (env "c" + env "d" * t ^ j) ^ (k - 1) * (env "e" + env "f" * t ^ j) ^ l) t := by
      convert hΦ2 using 1
      simp [eval, hk_n, hk_p, hk_q, hk_r, e1, e2, e2', toInt?_two, toInt?_neg_one]
      try first | ring1 | simp
    have hEF : eval I (Function.update env "x" t) rubi1135r30Nondeg.body = (env "a" + env "b" * t ^ j) ^ i * (env "c" + env "d" * t ^ j) ^ k * (env "e" + env "f" * t ^ j) ^ l := by
      simp [rubi1135r30Nondeg, eval, hk_n, hk_p, hk_q, hk_r, toInt?_two, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi1135r30Nondeg.integrals.map (·.1)) Φ "x" w) rubi1135r30Nondeg.result) =
        fun w => env "d" * (env "b")⁻¹ * Φ "I1" w + (env "b" * env "c" + -1 * env "a" * env "d") * (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1135r30Nondeg, eval, recEnv, toInt?_two, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hX : (env "a" + env "b" * t ^ j) ^ (i + 1) = (env "a" + env "b" * t ^ j) ^ i * (env "a" + env "b" * t ^ j) := zpow_succ_of _ _ (Or.inl (ht.2.1 (by omega)))
    have hZ : (env "c" + env "d" * t ^ j) ^ k = (env "c" + env "d" * t ^ j) ^ (k - 1) * (env "c" + env "d" * t ^ j) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hX, hZ]
    have hb : env "b" * (env "b")⁻¹ = 1 := mul_inv_cancel₀ hb0
    generalize (env "a" + env "b" * t ^ j) ^ i = X
    generalize (env "c" + env "d" * t ^ j) ^ (k - 1) = Z
    generalize (env "e" + env "f" * t ^ j) ^ l = Y
    generalize (env "b")⁻¹ = bi at hb ⊢
    linear_combination (X * Z * Y * (env "c" + env "d" * t ^ j)) * hb

theorem rubi1135r30Nondeg_real : rubi1135r30Nondeg.Holds .real :=
  rubi1135r30Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1135r30Nondeg_complex : rubi1135r30Nondeg.Holds .complex :=
  rubi1135r30Nondeg_holds Interp.complex Interp.complex_lt_rat

/-- **1.2.1.2 #43** with `c (m + 2 p + 1) ≠ 0` and `m > 1`: the derivative identity is `(m - 1)` times the converted condition. -/
theorem rubi1212r43Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1212r43Nondeg.conditions rubi1212r43Nondeg.body rubi1212r43Nondeg.result rubi1212r43Nondeg.integrals := by
  intro env hc t hF
  have hW : (env "c" * (env "m" + 2 * env "p" + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int 0)) (by simp [rubi1212r43Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hcnd : env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r43Nondeg])
    simp [Cond.Holds, Defined, eval, toInt?_two] at h
    linear_combination h
  have hg := hc (.gt (.var "m") (.int 1)) (by simp [rubi1212r43Nondeg])
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r43Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r43Nondeg, Defined, eval, hkm, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hk1 : 1 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [hm] at hg
    have h' : I.lt ((((1 : ℤ)) : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have e1' : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have e2 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1212r43Nondeg.body →
      (q < 0 → (env "a" + env "b" * w + env "c" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1212r43Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    tauto
  have ht := hD t hF.self_of_nhds
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r43Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, e1, e1', hkp, toInt?_two]
    exact ⟨fun h' => absurd h' (by omega), h⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1212r43Nondeg, Defined, eval, recEnv, e1, e1', e2, toInt?_two, toInt?_neg_one]
    exact ⟨⟨fun h' => absurd h' (by omega), fun h' => h (by omega)⟩, hW'⟩
  · simp only [rubi1212r43Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k - 1) * (env "a" + env "b" * t + env "c" * t ^ 2) ^ q) t := by
      convert hΦ using 1
      simp [eval, e1, e1', hkp, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1212r43Nondeg.body = (env "d" + env "e" * t) ^ k * (env "a" + env "b" * t + env "c" * t ^ 2) ^ q := by
      simp [rubi1212r43Nondeg, eval, hkm, hkp, toInt?_two]
    set u := (env "c" * (env "m" + 2 * env "p" + 1))⁻¹ with hu_def
    have hU : (env "c" * (env "m" + 2 * env "p" + 1)) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi1212r43Nondeg.integrals.map (·.1)) Φ "x" w) rubi1212r43Nondeg.result) =
        fun w => env "e" * (env "d" + env "e" * w) ^ (k - 1) * (env "a" + env "b" * w + env "c" * w ^ 2) ^ (q + 1) * u + (env "m" + env "p") * (2 * env "c" * env "d" + -1 * env "b" * env "e") * u * Φ "I1" w := by
      funext w
      simp [rubi1212r43Nondeg, eval, recEnv, e1, e1', e2, toInt?_two, toInt?_neg_one, hu_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hA1 : (env "a" + env "b" * t + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht (by omega))
      · exact Or.inr (by omega)
    have hA0 : (env "a" + env "b" * t + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    have hin : HasDerivAt (fun w => (env "a" + env "b" * w + env "c" * w ^ 2)) (env "b" + env "c" * (2 * t)) t := by
      have := (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add ((hasDerivAt_pow 2 t).const_mul (env "c"))
      convert this using 1 <;> first | (norm_num; ring) | ring | (funext w; simp only [id]) | (funext w; ring)
    have hlin : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      have := ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
      convert this using 1 <;> first | ring | (funext w; simp only [id])
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (k - 1) _ (Or.inr (by omega))) hlin).const_mul (env "e")).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hA1) hin)).mul_const u).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [show k - 1 - 1 = k - 2 by ring]
    have hZ1 : (env "d" + env "e" * t) ^ (k - 1) = (env "d" + env "e" * t) ^ (k - 2) * (env "d" + env "e" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
    have hZ2 : (env "d" + env "e" * t) ^ k = (env "d" + env "e" * t) ^ (k - 2) * (env "d" + env "e" * t) ^ 2 := by
      rw [← zpow_natCast, ← zpow_add' (Or.inr (Or.inl (by omega)))]; congr 1; push_cast; ring
    rw [hZ1, hZ2, zpow_succ_of _ _ hA0]
    generalize (env "d" + env "e" * t) ^ (k - 2) = Z
    generalize (env "a" + env "b" * t + env "c" * t ^ 2) ^ q = Y
    clear_value u
    simp only [hm, hp] at hU ⊢
    push_cast
    linear_combination (Z * Y) * ((env "d" + env "e" * t) ^ 2 * hU + u * ((k : 𝕜) - 1) * hcnd)

theorem rubi1212r43Nondeg_real : rubi1212r43Nondeg.Holds .real :=
  rubi1212r43Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1212r43Nondeg_complex : rubi1212r43Nondeg.Holds .complex :=
  rubi1212r43Nondeg_holds Interp.complex Interp.complex_lt_rat

/-- **1.2.1.2 #44** with `c (m + 2 p + 1) ≠ 0` and `m > 1`: the derivative identity is `(m - 1)` times the converted condition. -/
theorem rubi1212r44Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1212r44Nondeg.conditions rubi1212r44Nondeg.body rubi1212r44Nondeg.result rubi1212r44Nondeg.integrals := by
  intro env hc t hF
  have hW : (env "c" * (env "m" + 2 * env "p" + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int 0)) (by simp [rubi1212r44Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hcnd : env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r44Nondeg])
    simp [Cond.Holds, Defined, eval, toInt?_two] at h
    linear_combination h
  have hg := hc (.gt (.var "m") (.int 1)) (by simp [rubi1212r44Nondeg])
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r44Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r44Nondeg, Defined, eval, hkm, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hk1 : 1 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [hm] at hg
    have h' : I.lt ((((1 : ℤ)) : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have e1' : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have e2 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1212r44Nondeg.body →
      (q < 0 → (env "a" + env "c" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1212r44Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    tauto
  have ht := hD t hF.self_of_nhds
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r44Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, e1, e1', hkp, toInt?_two]
    exact ⟨fun h' => absurd h' (by omega), h⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1212r44Nondeg, Defined, eval, recEnv, e1, e1', e2, toInt?_two, toInt?_neg_one]
    exact ⟨⟨fun h' => absurd h' (by omega), fun h' => h (by omega)⟩, hW'⟩
  · simp only [rubi1212r44Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k - 1) * (env "a" + env "c" * t ^ 2) ^ q) t := by
      convert hΦ using 1
      simp [eval, e1, e1', hkp, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1212r44Nondeg.body = (env "d" + env "e" * t) ^ k * (env "a" + env "c" * t ^ 2) ^ q := by
      simp [rubi1212r44Nondeg, eval, hkm, hkp, toInt?_two]
    set u := (env "c" * (env "m" + 2 * env "p" + 1))⁻¹ with hu_def
    have hU : (env "c" * (env "m" + 2 * env "p" + 1)) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi1212r44Nondeg.integrals.map (·.1)) Φ "x" w) rubi1212r44Nondeg.result) =
        fun w => env "e" * (env "d" + env "e" * w) ^ (k - 1) * (env "a" + env "c" * w ^ 2) ^ (q + 1) * u + 2 * env "c" * env "d" * (env "m" + env "p") * u * Φ "I1" w := by
      funext w
      simp [rubi1212r44Nondeg, eval, recEnv, e1, e1', e2, toInt?_two, toInt?_neg_one, hu_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hA1 : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht (by omega))
      · exact Or.inr (by omega)
    have hA0 : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    have hin : HasDerivAt (fun w => (env "a" + env "c" * w ^ 2)) (env "c" * (2 * t)) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (env "c")).const_add (env "a")
      convert this using 1 <;> first | (norm_num; ring) | ring | (funext w; simp only [id]) | (funext w; ring)
    have hlin : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      have := ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
      convert this using 1 <;> first | ring | (funext w; simp only [id])
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (k - 1) _ (Or.inr (by omega))) hlin).const_mul (env "e")).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hA1) hin)).mul_const u).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [show k - 1 - 1 = k - 2 by ring]
    have hZ1 : (env "d" + env "e" * t) ^ (k - 1) = (env "d" + env "e" * t) ^ (k - 2) * (env "d" + env "e" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
    have hZ2 : (env "d" + env "e" * t) ^ k = (env "d" + env "e" * t) ^ (k - 2) * (env "d" + env "e" * t) ^ 2 := by
      rw [← zpow_natCast, ← zpow_add' (Or.inr (Or.inl (by omega)))]; congr 1; push_cast; ring
    rw [hZ1, hZ2, zpow_succ_of _ _ hA0]
    generalize (env "d" + env "e" * t) ^ (k - 2) = Z
    generalize (env "a" + env "c" * t ^ 2) ^ q = Y
    clear_value u
    simp only [hm, hp] at hU ⊢
    push_cast
    linear_combination (Z * Y) * ((env "d" + env "e" * t) ^ 2 * hU + u * ((k : 𝕜) - 1) * hcnd)

theorem rubi1212r44Nondeg_real : rubi1212r44Nondeg.Holds .real :=
  rubi1212r44Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1212r44Nondeg_complex : rubi1212r44Nondeg.Holds .complex :=
  rubi1212r44Nondeg_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec60
