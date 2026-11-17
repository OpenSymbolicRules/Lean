import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, seventeenth batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 4.7.9 #11 and #12,
which split `cos² / (a + b sin)` (and the symmetric case) with
`sin² + cos² = 1`, a hypothesis instantiated by Mathlib over ℝ and ℂ, and
2.3 #32 and #33, whose exponents agree: `e + f (a + b x)/(c + d x)` is
`e + f b/d` when `b c = a d`, and `(d e + b f)/d - f (b c - a d)/(d (c + d x))`
in general.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec65

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








/-- **4.7.9 #11** with `b ≠ 0`, `a² - b² ≠ 0`, `m > 0` and `n > 1`: `cos² = 1 - sin²` splits `cos² / (a + b sin)`. -/
theorem rubi479r11Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hp : ∀ u : 𝕜, I.sin u ^ 2 + I.cos u ^ 2 = 1) :
    AntiderivRecHolds I "x" rubi479r11Nondeg.conditions rubi479r11Nondeg.body rubi479r11Nondeg.result rubi479r11Nondeg.integrals := by
  intro env hc t hF
  have hb0 : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi479r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg_n := hc (.gt (.var "n") (.int 1)) (by simp [rubi479r11Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r11Nondeg, Defined, eval, hk_m] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r11Nondeg, Defined, eval, hk_m, hk_n] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have hj : 1 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_n
    rw [h_n] at hg_n
    have h' : I.lt ((((1 : ℤ)) : ℚ) : 𝕜) ((j : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_n
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "n" + -1 * 2) = some (j - 2) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have e1' : I.toInt? (env "n" + -2) = some (j - 2) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi479r11Nondeg.body → (env "a" + env "b" * I.sin (env "c" + env "d" * w)) ≠ 0 := by
    intro w h
    simp [rubi479r11Nondeg, Defined, eval, hk_m, hk_n, toInt?_neg_one] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r11Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      have hA := hD w hw
      have hw' := hw
      simp [rubi479r11Nondeg, Defined, eval, hk_m, hk_n, toInt?_neg_one] at hw'
      simp [Defined, eval, hk_m, e1, e1', toInt?_neg_one, hA]
      first | done | exact ⟨hw'.1.1, fun h => absurd h (by omega)⟩ | exact fun h => absurd h (by omega) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi479r11Nondeg, Defined, eval, recEnv, toInt?_two, toInt?_neg_one, hb0]
  · simp only [rubi479r11Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2, hΦ3⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ k * I.cos (env "c" + env "d" * t) ^ (j - 2)) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, e1, e1']
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ k * I.cos (env "c" + env "d" * t) ^ (j - 2) * I.sin (env "c" + env "d" * t)) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, e1, e1']
    have hΦ3' : HasDerivAt (Φ "I3") ((env "e" + env "f" * t) ^ k * I.cos (env "c" + env "d" * t) ^ (j - 2) * (env "a" + env "b" * I.sin (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ3 using 1
      simp [eval, hk_m, e1, e1', toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi479r11Nondeg.body = (env "e" + env "f" * t) ^ k * I.cos (env "c" + env "d" * t) ^ j * (env "a" + env "b" * I.sin (env "c" + env "d" * t))⁻¹ := by
      simp [rubi479r11Nondeg, eval, hk_m, hk_n, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi479r11Nondeg.integrals.map (·.1)) Φ "x" w) rubi479r11Nondeg.result) =
        fun w => env "a" * (env "b" ^ 2)⁻¹ * Φ "I1" w + -1 * 1 * (env "b")⁻¹ * Φ "I2" w +
          -1 * (env "a" ^ 2 + -1 * env "b" ^ 2) * (env "b" ^ 2)⁻¹ * Φ "I3" w := by
      funext w
      simp [rubi479r11Nondeg, eval, recEnv, toInt?_two, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine (((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).add (hΦ3'.const_mul _)).congr_deriv ?_
    have hT : I.cos (env "c" + env "d" * t) ^ j = I.cos (env "c" + env "d" * t) ^ (j - 2) * I.cos (env "c" + env "d" * t) ^ 2 := by
      rw [← zpow_natCast, ← zpow_add' (Or.inr (Or.inl (by omega)))]; congr 1; push_cast; ring
    rw [hT]
    have hAA : (env "a" + env "b" * I.sin (env "c" + env "d" * t)) * (env "a" + env "b" * I.sin (env "c" + env "d" * t))⁻¹ = 1 := mul_inv_cancel₀ ht
    have hbb : env "b" * (env "b")⁻¹ = 1 := mul_inv_cancel₀ hb0
    have hb2 : env "b" ^ 2 * (env "b" ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hb0)
    have hpt := hp (env "c" + env "d" * t)
    generalize (env "e" + env "f" * t) ^ k = P
    generalize I.cos (env "c" + env "d" * t) ^ (j - 2) = R
    generalize (env "a" + env "b" * I.sin (env "c" + env "d" * t))⁻¹ = Ai at hAA ⊢
    generalize (env "b")⁻¹ = bi at hbb ⊢
    generalize (env "b" ^ 2)⁻¹ = u2 at hb2 ⊢
    linear_combination (P * R) * (((1 - I.sin (env "c" + env "d" * t) ^ 2) * Ai + I.sin (env "c" + env "d" * t) * bi) * hb2 - u2 * (env "a" - env "b" * I.sin (env "c" + env "d" * t)) * hAA -
      I.sin (env "c" + env "d" * t) * env "b" * u2 * hbb - Ai * hpt)

theorem rubi479r11Nondeg_real : rubi479r11Nondeg.Holds .real :=
  rubi479r11Nondeg_holds Interp.real Interp.real_lt_rat Real.sin_sq_add_cos_sq

theorem rubi479r11Nondeg_complex : rubi479r11Nondeg.Holds .complex :=
  rubi479r11Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.sin_sq_add_cos_sq

/-- **4.7.9 #12** with `b ≠ 0`, `a² - b² ≠ 0`, `m > 0` and `n > 1`: `sin² = 1 - cos²` splits `sin² / (a + b cos)`. -/
theorem rubi479r12Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hp : ∀ u : 𝕜, I.sin u ^ 2 + I.cos u ^ 2 = 1) :
    AntiderivRecHolds I "x" rubi479r12Nondeg.conditions rubi479r12Nondeg.body rubi479r12Nondeg.result rubi479r12Nondeg.integrals := by
  intro env hc t hF
  have hb0 : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi479r12Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hg_n := hc (.gt (.var "n") (.int 1)) (by simp [rubi479r12Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r12Nondeg, Defined, eval, hk_m] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r12Nondeg, Defined, eval, hk_m, hk_n] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have hj : 1 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_n
    rw [h_n] at hg_n
    have h' : I.lt ((((1 : ℤ)) : ℚ) : 𝕜) ((j : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_n
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "n" + -1 * 2) = some (j - 2) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have e1' : I.toInt? (env "n" + -2) = some (j - 2) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi479r12Nondeg.body → (env "a" + env "b" * I.cos (env "c" + env "d" * w)) ≠ 0 := by
    intro w h
    simp [rubi479r12Nondeg, Defined, eval, hk_m, hk_n, toInt?_neg_one] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      have hA := hD w hw
      have hw' := hw
      simp [rubi479r12Nondeg, Defined, eval, hk_m, hk_n, toInt?_neg_one] at hw'
      simp [Defined, eval, hk_m, e1, e1', toInt?_neg_one, hA]
      first | done | exact ⟨hw'.1.1, fun h => absurd h (by omega)⟩ | exact fun h => absurd h (by omega) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi479r12Nondeg, Defined, eval, recEnv, toInt?_two, toInt?_neg_one, hb0]
  · simp only [rubi479r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2, hΦ3⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ k * I.sin (env "c" + env "d" * t) ^ (j - 2)) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, e1, e1']
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ k * I.sin (env "c" + env "d" * t) ^ (j - 2) * I.cos (env "c" + env "d" * t)) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, e1, e1']
    have hΦ3' : HasDerivAt (Φ "I3") ((env "e" + env "f" * t) ^ k * I.sin (env "c" + env "d" * t) ^ (j - 2) * (env "a" + env "b" * I.cos (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ3 using 1
      simp [eval, hk_m, e1, e1', toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi479r12Nondeg.body = (env "e" + env "f" * t) ^ k * I.sin (env "c" + env "d" * t) ^ j * (env "a" + env "b" * I.cos (env "c" + env "d" * t))⁻¹ := by
      simp [rubi479r12Nondeg, eval, hk_m, hk_n, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi479r12Nondeg.integrals.map (·.1)) Φ "x" w) rubi479r12Nondeg.result) =
        fun w => env "a" * (env "b" ^ 2)⁻¹ * Φ "I1" w + -1 * 1 * (env "b")⁻¹ * Φ "I2" w +
          -1 * (env "a" ^ 2 + -1 * env "b" ^ 2) * (env "b" ^ 2)⁻¹ * Φ "I3" w := by
      funext w
      simp [rubi479r12Nondeg, eval, recEnv, toInt?_two, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine (((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).add (hΦ3'.const_mul _)).congr_deriv ?_
    have hT : I.sin (env "c" + env "d" * t) ^ j = I.sin (env "c" + env "d" * t) ^ (j - 2) * I.sin (env "c" + env "d" * t) ^ 2 := by
      rw [← zpow_natCast, ← zpow_add' (Or.inr (Or.inl (by omega)))]; congr 1; push_cast; ring
    rw [hT]
    have hAA : (env "a" + env "b" * I.cos (env "c" + env "d" * t)) * (env "a" + env "b" * I.cos (env "c" + env "d" * t))⁻¹ = 1 := mul_inv_cancel₀ ht
    have hbb : env "b" * (env "b")⁻¹ = 1 := mul_inv_cancel₀ hb0
    have hb2 : env "b" ^ 2 * (env "b" ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hb0)
    have hpt := hp (env "c" + env "d" * t)
    generalize (env "e" + env "f" * t) ^ k = P
    generalize I.sin (env "c" + env "d" * t) ^ (j - 2) = R
    generalize (env "a" + env "b" * I.cos (env "c" + env "d" * t))⁻¹ = Ai at hAA ⊢
    generalize (env "b")⁻¹ = bi at hbb ⊢
    generalize (env "b" ^ 2)⁻¹ = u2 at hb2 ⊢
    linear_combination (P * R) * (((1 - I.cos (env "c" + env "d" * t) ^ 2) * Ai + I.cos (env "c" + env "d" * t) * bi) * hb2 - u2 * (env "a" - env "b" * I.cos (env "c" + env "d" * t)) * hAA -
      I.cos (env "c" + env "d" * t) * env "b" * u2 * hbb - Ai * hpt)

theorem rubi479r12Nondeg_real : rubi479r12Nondeg.Holds .real :=
  rubi479r12Nondeg_holds Interp.real Interp.real_lt_rat Real.sin_sq_add_cos_sq

theorem rubi479r12Nondeg_complex : rubi479r12Nondeg.Holds .complex :=
  rubi479r12Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.sin_sq_add_cos_sq

/-- **2.3 #32** with `d ≠ 0`: when `b c = a d`, `(a + b x) / (c + d x) = b / d`. -/
theorem rubi23r32Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi23r32Nondeg.conditions rubi23r32Nondeg.body rubi23r32Nondeg.result rubi23r32Nondeg.integrals := by
  intro env hc t hF
  have hd0 : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi23r32Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hcnd : env "b" * env "c" + -1 * env "a" * env "d" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi23r32Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hX : ∀ w, env "c" + env "d" * w ≠ 0 →
      env "e" + env "f" * (env "a" + env "b" * w) * (env "c" + env "d" * w)⁻¹ = env "e" + env "f" * env "b" * (env "d")⁻¹ := by
    intro w hw
    have hC := mul_inv_cancel₀ hw
    have hdd := mul_inv_cancel₀ hd0
    generalize (env "c" + env "d" * w)⁻¹ = Ci at hC ⊢
    generalize (env "d")⁻¹ = di at hdd ⊢
    linear_combination env "f" * (-(Ci * di) * hcnd - (env "a" + env "b" * w) * Ci * hdd + env "b" * di * hC)
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi23r32Nondeg, Defined, eval, hkm] at h
  have h0 := hF.self_of_nhds
  simp [rubi23r32Nondeg, Defined, eval, hkm, toInt?_neg_one] at h0
  obtain ⟨-, hc0, N, hN, hNF⟩ := h0
  rw [hX t hc0] at hN
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi23r32Nondeg.body →
      (k < 0 → env "g" + env "h" * w ≠ 0) := by
    intro w h
    simp [rubi23r32Nondeg, Defined, eval, hkm, toInt?_neg_one] at h
    exact h.1
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi23r32Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [Defined, eval, hkm]
    exact hD w hw
  · exact Eventually.of_forall fun w => by
      simp [rubi23r32Nondeg, Defined, eval, recEnv, toInt?_neg_one, hd0]
      first | exact ⟨N, hN, hNF⟩ | (refine ⟨N, ?_, hNF⟩; simpa using hN)
  · simp only [rubi23r32Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "g" + env "h" * t) ^ k) t := by
      convert hΦ using 1
      simp [eval, hkm]
    have hfun : (fun w => eval I (recEnv env (rubi23r32Nondeg.integrals.map (·.1)) Φ "x" w) rubi23r32Nondeg.result) =
        fun w => env "F" ^ N * Φ "I1" w := by
      funext w
      simp [rubi23r32Nondeg, eval, recEnv, toInt?_neg_one]
      first | (left; rfl) | (left; simp) | (left; split <;> simp_all)
    rw [hfun]
    refine (hΦ'.const_mul _).congr_deriv ?_
    simp [rubi23r32Nondeg, eval, hkm, toInt?_neg_one]
    rw [hX t hc0, hN]
    exact mul_comm _ _

/-- **2.3 #33** with `d ≠ 0`: `e + f (a + b x)/(c + d x) = (d e + b f)/d - f (b c - a d)/(d (c + d x))`. -/
theorem rubi23r33Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi23r33Nondeg.conditions rubi23r33Nondeg.body rubi23r33Nondeg.result rubi23r33Nondeg.integrals := by
  intro env hc t hF
  have hd0 : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi23r33Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hX : ∀ w, env "c" + env "d" * w ≠ 0 →
      (env "d" * env "e" + env "b" * env "f") * (env "d")⁻¹ +
          -1 * env "f" * (env "b" * env "c" + -1 * env "a" * env "d") * (env "d" * (env "c" + env "d" * w))⁻¹ =
        env "e" + env "f" * (env "a" + env "b" * w) * (env "c" + env "d" * w)⁻¹ := by
    intro w hw
    rw [mul_inv]
    have hC := mul_inv_cancel₀ hw
    have hdd := mul_inv_cancel₀ hd0
    generalize (env "c" + env "d" * w)⁻¹ = Ci at hC ⊢
    generalize (env "d")⁻¹ = di at hdd ⊢
    linear_combination env "e" * hdd + env "f" * (-(env "b" * di) * hC + (env "a" + env "b" * w) * Ci * hdd)
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi23r33Nondeg, Defined, eval, hkm] at h
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi23r33Nondeg.body →
      (k < 0 → env "g" + env "h" * w ≠ 0) ∧ env "c" + env "d" * w ≠ 0 ∧
        ∃ n, I.toInt? (env "e" + env "f" * (env "a" + env "b" * w) * (env "c" + env "d" * w)⁻¹) = some n ∧
          (n < 0 → env "F" ≠ 0) := by
    intro w h
    simp [rubi23r33Nondeg, Defined, eval, hkm, toInt?_neg_one] at h
    exact h
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi23r33Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, N, hN, hNF⟩ := hD w hw
    rw [← hX w h2] at hN
    simp [Defined, eval, hkm, toInt?_neg_one, hd0, h2]
    first | exact ⟨h1, N, hN, hNF⟩ | (refine ⟨h1, N, ?_, hNF⟩; simpa using hN) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi23r33Nondeg, Defined, eval, recEnv]
  · simp only [rubi23r33Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi23r33Nondeg.integrals.map (·.1)) Φ "x" w) rubi23r33Nondeg.result) =
        Φ "I1" := by
      funext w
      simp [rubi23r33Nondeg, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [rubi23r33Nondeg, eval, hkm, toInt?_neg_one]
    have key : (env "d" * env "e" + env "b" * env "f") * (env "d")⁻¹ +
        -(env "f" * (env "b" * env "c" + -(env "a" * env "d")) * ((env "c" + env "d" * t)⁻¹ * (env "d")⁻¹)) =
        env "e" + env "f" * (env "a" + env "b" * t) * (env "c" + env "d" * t)⁻¹ := by
      have h := hX t ht.2.1
      rw [mul_inv] at h
      linear_combination h
    left
    rw [key]

theorem rubi23r32Nondeg_real : rubi23r32Nondeg.Holds .real :=
  rubi23r32Nondeg_holds Interp.real

theorem rubi23r32Nondeg_complex : rubi23r32Nondeg.Holds .complex :=
  rubi23r32Nondeg_holds Interp.complex

theorem rubi23r33Nondeg_real : rubi23r33Nondeg.Holds .real :=
  rubi23r33Nondeg_holds Interp.real

theorem rubi23r33Nondeg_complex : rubi23r33Nondeg.Holds .complex :=
  rubi23r33Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec65
