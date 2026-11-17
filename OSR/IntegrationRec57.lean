import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, ninth batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): the reduction
1.2.2.1 #5 of `(a + b x² + c x⁴)^p` for `p < -1`, and 1.2.1.2 #102, where
`m + 2 p + 3 = 0` and `p < -1` make `m ≥ 1`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec57

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








/-- **1.2.2.1 #5** with `2 a (p + 1) (b² - 4 a c) ≠ 0`: the reduction of `(a + b x² + c x⁴)^p` for `p < -1`. -/
theorem rubi1221r5Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1221r5Nondeg.conditions rubi1221r5Nondeg.body rubi1221r5Nondeg.result rubi1221r5Nondeg.integrals := by
  intro env hc t hF
  have hW : 2 * env "a" * (env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c") ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int 0)) (by simp [rubi1221r5Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1221r5Nondeg, Defined, eval, hkp] at h
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1221r5Nondeg.body →
      (q < 0 → (env "a" + env "b" * w ^ 2 + env "c" * w ^ 4) ≠ 0) := by
    intro w h
    simp [rubi1221r5Nondeg, Defined, eval, hkp, toInt?_two, toInt?_four] at h
    exact h
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1221r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, hkp1, toInt?_two, toInt?_four]
    exact fun h' => h (by omega)
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1221r5Nondeg, Defined, eval, recEnv, hkp1, toInt?_two, toInt?_four, toInt?_neg_one]
    first | (refine ⟨⟨fun h' => h (by omega), ?_⟩, ?_⟩ <;> simpa using hW) | (refine ⟨fun h' => h (by omega), ?_⟩; simpa using hW) | (refine ⟨fun h' => h (by omega), ?_, ?_⟩ <;> simpa using hW)
  · simp only [rubi1221r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "b" ^ 2 + -1 * 2 * env "a" * env "c" + 2 * (env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c") +
        env "b" * env "c" * (4 * env "p" + 7) * t ^ 2) * (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ (q + 1)) t := by
      convert hΦ using 1
      simp [eval, hkp1, toInt?_two, toInt?_four]
      try ring
    have hEF : eval I (Function.update env "x" t) rubi1221r5Nondeg.body = (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ q := by
      simp [rubi1221r5Nondeg, eval, hkp, toInt?_two, toInt?_four]
    set u := (2 * env "a" * (env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c"))⁻¹ with hu_def
    have hU : 2 * env "a" * (env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c") * u = 1 := by
      rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi1221r5Nondeg.integrals.map (·.1)) Φ "x" w) rubi1221r5Nondeg.result) =
        fun w => (-(env "b" ^ 2 + -1 * 2 * env "a" * env "c") * w - env "b" * env "c" * w ^ 3) * u *
          (env "a" + env "b" * w ^ 2 + env "c" * w ^ 4) ^ (q + 1) + u * Φ "I1" w := by
      funext w
      simp [rubi1221r5Nondeg, eval, recEnv, hkp1, toInt?_two, toInt?_four, toInt?_neg_one, hu_def]
      try ring
    rw [hfun, hEF]
    have hA1 : (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht (by omega))
      · exact Or.inr (by omega)
    have hA0 : (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    have hin : HasDerivAt (fun w => env "a" + env "b" * w ^ 2 + env "c" * w ^ 4) (2 * env "b" * t + 4 * env "c" * t ^ 3) t := by
      have := (((hasDerivAt_pow 2 t).const_mul (env "b")).const_add (env "a")).add ((hasDerivAt_pow 4 t).const_mul (env "c"))
      convert this using 1 <;> first | (norm_num; ring) | ring | (funext w; ring)
    have hN : HasDerivAt (fun w => -(env "b" ^ 2 + -1 * 2 * env "a" * env "c") * w - env "b" * env "c" * w ^ 3)
        (-(env "b" ^ 2 + -1 * 2 * env "a" * env "c") - 3 * env "b" * env "c" * t ^ 2) t := by
      have := ((hasDerivAt_id' t).const_mul (-(env "b" ^ 2 + -1 * 2 * env "a" * env "c"))).sub ((hasDerivAt_pow 3 t).const_mul (env "b" * env "c"))
      convert this using 1 <;> first | (norm_num; ring) | ring | (funext w; simp only [id])
    refine (((hN.mul_const u).mul (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hA1) hin)).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hA0]
    generalize (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ q = Y
    clear_value u
    simp only [hp] at hU ⊢
    push_cast
    linear_combination Y * hU

theorem rubi1221r5Nondeg_real : rubi1221r5Nondeg.Holds .real :=
  rubi1221r5Nondeg_holds Interp.real

theorem rubi1221r5Nondeg_complex : rubi1221r5Nondeg.Holds .complex :=
  rubi1221r5Nondeg_holds Interp.complex

/-- **1.2.1.2 #102** with `4 a c (p + 1) ≠ 0`: `m + 2 p + 3 = 0` and `p < -1`, so `m ≥ 1`. -/
theorem rubi1212r102Nondeg_holds [CharZero 𝕜] (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1212r102Nondeg.conditions rubi1212r102Nondeg.body rubi1212r102Nondeg.result rubi1212r102Nondeg.integrals := by
  intro env hc t hF
  have hW : 4 * env "a" * env "c" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1212r102Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "m" + 2 * env "p" + 3 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0)) (by simp [rubi1212r102Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hgp := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1212r102Nondeg])
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r102Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r102Nondeg, Defined, eval, hkm, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hq1 : q < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgp
    rw [hp] at hgp
    have h' : I.lt ((q : ℚ) : 𝕜) ((((-1 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hgp
    exact_mod_cast (hlt _ _).1 h'
  have hk : (k : 𝕜) + 2 * (q : 𝕜) + 3 = 0 := by rw [← hm, ← hp]; exact hrel
  have hkz : k + 2 * q + 3 = 0 := by exact_mod_cast hk
  have hk1 : 1 ≤ k := by omega
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have e3 : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have e4 : I.toInt? (env "m" - 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have e5 : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1212r102Nondeg.body →
      (q < 0 → (env "a" + env "c" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1212r102Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    tauto
  have ht := hD t hF.self_of_nhds
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r102Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, e3, e4, e5, hkp1, toInt?_two]
    first | done | exact ⟨fun h' => absurd h' (by omega), fun h' => h (by omega)⟩ | (intro h'; exact h (by omega)) | omega
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1212r102Nondeg, Defined, eval, recEnv, hkm, hkp1, toInt?_two, toInt?_neg_one]
    first | done | exact ⟨⟨⟨fun h' => absurd h' (by omega), fun h' => h (by omega)⟩, by simpa using hW'⟩, by simpa using hW'⟩ |
      exact ⟨⟨fun h' => absurd h' (by omega), fun h' => h (by omega)⟩, by simpa using hW'⟩ |
      (refine ⟨⟨⟨fun h' => absurd h' (by omega), fun h' => h (by omega)⟩, ?_⟩, ?_⟩ <;> simpa using hW')
  · simp only [rubi1212r102Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k - 1) * (env "a" + env "c" * t ^ 2) ^ (q + 1)) t := by
      convert hΦ using 1
      simp [eval, e3, e4, e5, hkp1, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1212r102Nondeg.body =
        (env "d" + env "e" * t) ^ k * (env "a" + env "c" * t ^ 2) ^ q := by
      simp [rubi1212r102Nondeg, eval, hkm, hkp, toInt?_two]
    set u := (4 * env "a" * env "c" * (env "p" + 1))⁻¹ with hu_def
    have hU : 4 * env "a" * env "c" * (env "p" + 1) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi1212r102Nondeg.integrals.map (·.1)) Φ "x" w) rubi1212r102Nondeg.result) =
        fun w => -1 * (env "d" + env "e" * w) ^ k * 2 * env "c" * w * (env "a" + env "c" * w ^ 2) ^ (q + 1) * u +
          -1 * env "m" * 2 * env "c" * env "d" * u * Φ "I1" w := by
      funext w
      simp [rubi1212r102Nondeg, eval, recEnv, hkm, hkp1, toInt?_two, toInt?_neg_one, hu_def]
      try ring
    rw [hfun, hEF]
    have hA1 : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q + 1 := Or.inl (ht (by omega))
    have hA0 : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q := Or.inl (ht (by omega))
    have hin : HasDerivAt (fun w => env "a" + env "c" * w ^ 2) (env "c" * (2 * t)) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (env "c")).const_add (env "a")
      convert this using 1 <;> first | (norm_num; ring) | ring | (funext w; ring)
    have hlin : HasDerivAt (fun w => env "d" + env "e" * w) (env "e") t := by
      have := ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
      convert this using 1 <;> first | ring | (funext w; simp only [id])
    refine (((((((HasDerivAt.comp t (hasDerivAt_zpow k _ (Or.inr (by omega))) hlin).const_mul (-1)).mul_const 2).mul_const (env "c")).mul
      (hasDerivAt_id' t)).mul (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hA1) hin)).mul_const u |>.add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, id, Pi.mul_apply]
    have hZD : (env "d" + env "e" * t) ^ k = (env "d" + env "e" * t) ^ (k - 1) * (env "d" + env "e" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hZD, zpow_succ_of _ _ hA0]
    generalize (env "d" + env "e" * t) ^ (k - 1) = Z
    generalize (env "a" + env "c" * t ^ 2) ^ q = Y
    clear_value u
    simp only [hm, hp] at hU ⊢
    push_cast
    linear_combination (Y * Z * (env "d" + env "e" * t)) * hU +
      (-2 * Y * Z * env "c" * u * (env "a" + env "c" * t ^ 2) * (env "d" + env "e" * t)) * hk

theorem rubi1212r102Nondeg_real : rubi1212r102Nondeg.Holds .real :=
  rubi1212r102Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1212r102Nondeg_complex : rubi1212r102Nondeg.Holds .complex :=
  rubi1212r102Nondeg_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec57
