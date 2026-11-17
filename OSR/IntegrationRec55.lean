import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, seventh batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 1.1.1.3 #12 and
1.1.1.4 #38, partial fractions in `(a + b x) (c + d x)` with `p > 0`, from
`(b e - a f) (c + d x) - (d e - c f) (a + b x) = (b c - a d) (e + f x)`; and
1.2.1.2 #12 and 1.2.1.3 #16, the reduction of `(a + c x²)^p` for `p < -1`,
with `2 a c (p + 1) ≠ 0`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec55

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








/-- **1.1.1.3 #12** with `p > 0`: `(b e - a f) (c + d x) - (d e - c f) (a + b x) = (b c - a d) (e + f x)`. -/
theorem rubi1113r12Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1113r12Nondeg.conditions rubi1113r12Nondeg.body rubi1113r12Nondeg.result rubi1113r12Nondeg.integrals := by
  intro env hc t hF
  have hW : (env "b" * env "c" + -1 * env "a" * env "d") ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi1113r12Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hgp := hc (.gt (.var "p") (.int 0)) (by simp [rubi1113r12Nondeg])
  rcases hkp : I.toInt? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1113r12Nondeg, Defined, eval, hkp] at h
  have hp : env "p" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hk1 : 0 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgp
    rw [hp] at hgp
    have h' : I.lt ((0 : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgp
    exact_mod_cast (hlt _ _).1 h'
  have e3 : I.toInt? (env "p" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e4 : I.toInt? (env "p" - 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e5 : I.toInt? (env "p" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1113r12Nondeg.body →
      (env "a" + env "b" * w) ≠ 0 ∧ (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi1113r12Nondeg, Defined, eval, hkp, toInt?_neg_one] at h
    refine ⟨?_, ?_⟩ <;> tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1113r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      obtain ⟨hA0, hC0⟩ := hD w hw
      simp [Defined, eval, e3, e4, e5, toInt?_neg_one, hA0, hC0]
      first | done | exact ⟨fun h => absurd h (by omega), hG0⟩ | omega | tauto
    · filter_upwards [hF] with w hw
      obtain ⟨hA0, hC0⟩ := hD w hw
      simp [Defined, eval, e3, e4, e5, toInt?_neg_one, hA0, hC0]
      first | done | exact ⟨fun h => absurd h (by omega), hG0⟩ | omega | tauto
  · exact Eventually.of_forall fun w => by
      simp [rubi1113r12Nondeg, Defined, eval, recEnv, toInt?_neg_one]
      first | done | exact hW | tauto | simp_all
  · simp only [rubi1113r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ (k - 1) * (env "a" + env "b" * t)⁻¹) t := by
      convert hΦ1 using 1
      simp [eval, e3, e4, e5, toInt?_neg_one]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ (k - 1) * (env "c" + env "d" * t)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, e3, e4, e5, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1113r12Nondeg.body =
        (env "e" + env "f" * t) ^ k * ((env "a" + env "b" * t) * (env "c" + env "d" * t))⁻¹ := by
      simp [rubi1113r12Nondeg, eval, hkp, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi1113r12Nondeg.integrals.map (·.1)) Φ "x" w) rubi1113r12Nondeg.result) =
        fun w => (env "b" * env "e" + -1 * env "a" * env "f") * (env "b" * env "c" + -1 * env "a" * env "d")⁻¹ * Φ "I1" w + (-1 * (env "d" * env "e" + -1 * env "c" * env "f")) * (env "b" * env "c" + -1 * env "a" * env "d")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1113r12Nondeg, eval, recEnv, toInt?_neg_one]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hYE : (env "e" + env "f" * t) ^ k = (env "e" + env "f" * t) ^ (k - 1) * (env "e" + env "f" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hYE, mul_inv]
    have hU : (env "a" + env "b" * t) * (env "a" + env "b" * t)⁻¹ = 1 := mul_inv_cancel₀ ht.1
    have hV : (env "c" + env "d" * t) * (env "c" + env "d" * t)⁻¹ = 1 := mul_inv_cancel₀ ht.2
    have hu : (env "b" * env "c" + -1 * env "a" * env "d") * (env "b" * env "c" + -1 * env "a" * env "d")⁻¹ = 1 := mul_inv_cancel₀ hW
    generalize (env "e" + env "f" * t) ^ (k - 1) = Y
    generalize (env "a" + env "b" * t)⁻¹ = U at hU ⊢
    generalize (env "c" + env "d" * t)⁻¹ = V at hV ⊢
    generalize (env "b" * env "c" + -1 * env "a" * env "d")⁻¹ = u at hu ⊢
    linear_combination (Y * U * V * (env "e" + env "f" * t)) * hu - (Y * (env "b" * env "e" + -1 * env "a" * env "f") * u * U) * hV +
      (Y * (env "d" * env "e" + -1 * env "c" * env "f") * u * V) * hU

theorem rubi1113r12Nondeg_real : rubi1113r12Nondeg.Holds .real :=
  rubi1113r12Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1113r12Nondeg_complex : rubi1113r12Nondeg.Holds .complex :=
  rubi1113r12Nondeg_holds Interp.complex Interp.complex_lt_rat

/-- **1.1.1.4 #38** with `p > 0`: `(b e - a f) (c + d x) - (d e - c f) (a + b x) = (b c - a d) (e + f x)`. -/
theorem rubi1114r38Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1114r38Nondeg.conditions rubi1114r38Nondeg.body rubi1114r38Nondeg.result rubi1114r38Nondeg.integrals := by
  intro env hc t hF
  have hW : (env "b" * env "c" + -1 * env "a" * env "d") ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi1114r38Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hgp := hc (.gt (.var "p") (.int 0)) (by simp [rubi1114r38Nondeg])
  rcases hkp : I.toInt? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1114r38Nondeg, Defined, eval, hkp] at h
  rcases hkq : I.toInt? (env "q") with _ | qg
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1114r38Nondeg, Defined, eval, hkp, hkq] at h
  have hp : env "p" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hk1 : 0 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgp
    rw [hp] at hgp
    have h' : I.lt ((0 : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgp
    exact_mod_cast (hlt _ _).1 h'
  have e3 : I.toInt? (env "p" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e4 : I.toInt? (env "p" - 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e5 : I.toInt? (env "p" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1114r38Nondeg.body →
      (env "a" + env "b" * w) ≠ 0 ∧ (env "c" + env "d" * w) ≠ 0 ∧ (qg < 0 → (env "g" + env "h" * w) ≠ 0) := by
    intro w h
    simp [rubi1114r38Nondeg, Defined, eval, hkp, hkq, toInt?_neg_one] at h
    refine ⟨?_, ?_, ?_⟩ <;> tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1114r38Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      obtain ⟨hA0, hC0, hG0⟩ := hD w hw
      simp [Defined, eval, e3, e4, e5, hkq, toInt?_neg_one, hA0, hC0]
      first | done | exact ⟨fun h => absurd h (by omega), hG0⟩ | omega | tauto
    · filter_upwards [hF] with w hw
      obtain ⟨hA0, hC0, hG0⟩ := hD w hw
      simp [Defined, eval, e3, e4, e5, hkq, toInt?_neg_one, hA0, hC0]
      first | done | exact ⟨fun h => absurd h (by omega), hG0⟩ | omega | tauto
  · exact Eventually.of_forall fun w => by
      simp [rubi1114r38Nondeg, Defined, eval, recEnv, toInt?_neg_one]
      first | done | exact hW | tauto | simp_all
  · simp only [rubi1114r38Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ (k - 1) * (env "g" + env "h" * t) ^ qg * (env "a" + env "b" * t)⁻¹) t := by
      convert hΦ1 using 1
      simp [eval, e3, e4, e5, hkq, toInt?_neg_one]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ (k - 1) * (env "g" + env "h" * t) ^ qg * (env "c" + env "d" * t)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, e3, e4, e5, hkq, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1114r38Nondeg.body =
        (env "e" + env "f" * t) ^ k * (env "g" + env "h" * t) ^ qg * ((env "a" + env "b" * t) * (env "c" + env "d" * t))⁻¹ := by
      simp [rubi1114r38Nondeg, eval, hkp, hkq, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi1114r38Nondeg.integrals.map (·.1)) Φ "x" w) rubi1114r38Nondeg.result) =
        fun w => (env "b" * env "e" + -1 * env "a" * env "f") * (env "b" * env "c" + -1 * env "a" * env "d")⁻¹ * Φ "I1" w + (-1 * (env "d" * env "e" + -1 * env "c" * env "f")) * (env "b" * env "c" + -1 * env "a" * env "d")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1114r38Nondeg, eval, recEnv, toInt?_neg_one]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hYE : (env "e" + env "f" * t) ^ k = (env "e" + env "f" * t) ^ (k - 1) * (env "e" + env "f" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hYE, mul_inv]
    have hU : (env "a" + env "b" * t) * (env "a" + env "b" * t)⁻¹ = 1 := mul_inv_cancel₀ ht.1
    have hV : (env "c" + env "d" * t) * (env "c" + env "d" * t)⁻¹ = 1 := mul_inv_cancel₀ ht.2.1
    have hu : (env "b" * env "c" + -1 * env "a" * env "d") * (env "b" * env "c" + -1 * env "a" * env "d")⁻¹ = 1 := mul_inv_cancel₀ hW
    generalize (env "e" + env "f" * t) ^ (k - 1) = Y
    generalize (env "g" + env "h" * t) ^ qg = Z
    generalize (env "a" + env "b" * t)⁻¹ = U at hU ⊢
    generalize (env "c" + env "d" * t)⁻¹ = V at hV ⊢
    generalize (env "b" * env "c" + -1 * env "a" * env "d")⁻¹ = u at hu ⊢
    linear_combination ((Y * Z) * U * V * (env "e" + env "f" * t)) * hu - ((Y * Z) * (env "b" * env "e" + -1 * env "a" * env "f") * u * U) * hV +
      ((Y * Z) * (env "d" * env "e" + -1 * env "c" * env "f") * u * V) * hU

theorem rubi1114r38Nondeg_real : rubi1114r38Nondeg.Holds .real :=
  rubi1114r38Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1114r38Nondeg_complex : rubi1114r38Nondeg.Holds .complex :=
  rubi1114r38Nondeg_holds Interp.complex Interp.complex_lt_rat

/-- **1.2.1.3 #16** with `2 a c (p + 1) ≠ 0`: the classical reduction of `p < -1`. -/
theorem rubi1213r16Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1213r16Nondeg.conditions rubi1213r16Nondeg.body rubi1213r16Nondeg.result rubi1213r16Nondeg.integrals := by
  intro env hc t hF
  have hW : 2 * env "a" * env "c" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1213r16Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r16Nondeg, Defined, eval, hkp] at h
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1213r16Nondeg.body →
      (q < 0 → (env "a" + env "c" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1213r16Nondeg, Defined, eval, hkp, toInt?_two] at h
    exact h
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, hkp1, toInt?_two]
    exact fun h' => h (by omega)
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1213r16Nondeg, Defined, eval, recEnv, hkp1, toInt?_two, toInt?_neg_one]
    have hW' := hW
    simp only [ne_eq, mul_eq_zero, not_or] at hW'
    exact ⟨fun h' => h (by omega), hW'⟩
  · simp only [rubi1213r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "c" * t ^ 2) ^ (q + 1)) t := by
      convert hΦ using 1
      simp [eval, hkp1, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1213r16Nondeg.body =
        (env "d" + env "e" * t) * (env "f" + env "g" * t) * (env "a" + env "c" * t ^ 2) ^ q := by
      simp [rubi1213r16Nondeg, eval, hkp, toInt?_two]
    set u := (2 * env "a" * env "c" * (env "p" + 1))⁻¹ with hu_def
    have hU : 2 * env "a" * env "c" * (env "p" + 1) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi1213r16Nondeg.integrals.map (·.1)) Φ "x" w) rubi1213r16Nondeg.result) =
        fun w => (env "a" * (env "e" * env "f" + env "d" * env "g") + -1 * (env "c" * env "d" * env "f" + -1 * env "a" * env "e" * env "g") * w) * u * (env "a" + env "c" * w ^ 2) ^ (q + 1) +
          -1 * (env "a" * env "e" * env "g" + -1 * env "c" * env "d" * env "f" * (2 * env "p" + 3)) * u * Φ "I1" w := by
      funext w
      simp [rubi1213r16Nondeg, eval, recEnv, hkp1, toInt?_two, toInt?_neg_one, hu_def]
      try ring
    rw [hfun, hEF]
    have hA1 : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht (by omega))
      · exact Or.inr (by omega)
    have hA0 : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    have hin : HasDerivAt (fun w => env "a" + env "c" * w ^ 2) (env "c" * (2 * t)) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (env "c")).const_add (env "a")
      convert this using 1; push_cast; ring
    have hN : HasDerivAt (fun w => env "a" * (env "e" * env "f" + env "d" * env "g") + -1 * (env "c" * env "d" * env "f" + -1 * env "a" * env "e" * env "g") * w)
        (-1 * (env "c" * env "d" * env "f" + -1 * env "a" * env "e" * env "g")) t := by
      simpa using ((hasDerivAt_id' t).const_mul (-1 * (env "c" * env "d" * env "f" + -1 * env "a" * env "e" * env "g"))).const_add (env "a" * (env "e" * env "f" + env "d" * env "g"))
    refine (((hN.mul_const u).mul (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hA1) hin)).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hA0]
    generalize (env "a" + env "c" * t ^ 2) ^ q = Y
    clear_value u
    simp only [hp] at hU ⊢
    push_cast
    linear_combination (Y * (env "d" + env "e" * t) * (env "f" + env "g" * t)) * hU

theorem rubi1213r16Nondeg_real : rubi1213r16Nondeg.Holds .real :=
  rubi1213r16Nondeg_holds Interp.real

theorem rubi1213r16Nondeg_complex : rubi1213r16Nondeg.Holds .complex :=
  rubi1213r16Nondeg_holds Interp.complex

/-- **1.2.1.2 #12** with `2 a c (p + 1) ≠ 0` and `2 a (p + 1) ≠ 0`: the classical reduction of `p < -1`. -/
theorem rubi1212r12Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1212r12Nondeg.conditions rubi1212r12Nondeg.body rubi1212r12Nondeg.result rubi1212r12Nondeg.integrals := by
  intro env hc t hF
  have hW : 2 * env "a" * env "c" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1212r12Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW2 : 2 * env "a" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1212r12Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r12Nondeg, Defined, eval, hkp] at h
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1212r12Nondeg.body →
      (q < 0 → (env "a" + env "c" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1212r12Nondeg, Defined, eval, hkp, toInt?_two] at h
    exact h
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, hkp1, toInt?_two]
    exact fun h' => h (by omega)
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1212r12Nondeg, Defined, eval, recEnv, hkp1, toInt?_two, toInt?_neg_one]
    have hW' := hW
    have hW2' := hW2
    simp only [ne_eq, mul_eq_zero, not_or] at hW' hW2'
    exact ⟨⟨hW', fun h' => h (by omega)⟩, hW2'⟩
  · simp only [rubi1212r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "c" * t ^ 2) ^ (q + 1)) t := by
      convert hΦ using 1
      simp [eval, hkp1, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1212r12Nondeg.body =
        (env "d" + env "e" * t) * (env "a" + env "c" * t ^ 2) ^ q := by
      simp [rubi1212r12Nondeg, eval, hkp, toInt?_two]
    set u := (2 * env "a" * env "c" * (env "p" + 1))⁻¹ with hu_def
    set u2 := (2 * env "a" * (env "p" + 1))⁻¹ with hu2_def
    have hU : 2 * env "a" * env "c" * (env "p" + 1) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hU2 : 2 * env "a" * (env "p" + 1) * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hW2
    have hfun : (fun w => eval I (recEnv env (rubi1212r12Nondeg.integrals.map (·.1)) Φ "x" w) rubi1212r12Nondeg.result) =
        fun w => (env "a" * env "e" + -1 * env "c" * env "d" * w) * u * (env "a" + env "c" * w ^ 2) ^ (q + 1) +
          env "d" * (2 * env "p" + 3) * u2 * Φ "I1" w := by
      funext w
      simp [rubi1212r12Nondeg, eval, recEnv, hkp1, toInt?_two, toInt?_neg_one, hu_def, hu2_def]
      try ring
    rw [hfun, hEF]
    have hA1 : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht (by omega))
      · exact Or.inr (by omega)
    have hA0 : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    have hin : HasDerivAt (fun w => env "a" + env "c" * w ^ 2) (env "c" * (2 * t)) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (env "c")).const_add (env "a")
      convert this using 1; push_cast; ring
    have hN : HasDerivAt (fun w => env "a" * env "e" + -1 * env "c" * env "d" * w) (-1 * env "c" * env "d") t := by
      simpa using ((hasDerivAt_id' t).const_mul (-1 * env "c" * env "d")).const_add (env "a" * env "e")
    refine (((hN.mul_const u).mul (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hA1) hin)).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hA0]
    generalize (env "a" + env "c" * t ^ 2) ^ q = Y
    clear_value u u2
    simp only [hp] at hU hU2 ⊢
    push_cast
    linear_combination (Y * ((env "d" + env "e" * t) - env "d" * (2 * (q : 𝕜) + 3) * (env "a" + env "c" * t ^ 2) * u2)) * hU +
      (Y * env "d" * (2 * (q : 𝕜) + 3) * (env "a" + env "c" * t ^ 2) * env "c" * u) * hU2

theorem rubi1212r12Nondeg_real : rubi1212r12Nondeg.Holds .real :=
  rubi1212r12Nondeg_holds Interp.real

theorem rubi1212r12Nondeg_complex : rubi1212r12Nondeg.Holds .complex :=
  rubi1212r12Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec55
