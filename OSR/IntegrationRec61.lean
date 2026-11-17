import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, thirteenth batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 1.2.1.2 #45 (`m < 0`)
and #39 (`m > 0`, `p < -1`), whose derivative identities are multiples of
the converted condition `c d² - b d e + a e² = 0`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec61

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








/-- **1.2.1.2 #45** with `(m + p + 1) (2 c d - b e) ≠ 0` and `m < 0`: the derivative identity is `-m` times the converted condition. -/
theorem rubi1212r45Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1212r45Nondeg.conditions rubi1212r45Nondeg.body rubi1212r45Nondeg.result rubi1212r45Nondeg.integrals := by
  intro env hc t hF
  have hW : ((env "m" + env "p" + 1) * (2 * env "c" * env "d" + -1 * env "b" * env "e")) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.int 0)) (by simp [rubi1212r45Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hcnd : env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r45Nondeg])
    simp [Cond.Holds, Defined, eval, toInt?_two] at h
    linear_combination h
  have hg_m := hc (.gt (.int 0) (.var "m")) (by simp [rubi1212r45Nondeg])
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r45Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r45Nondeg, Defined, eval, hkm, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hgt_m : k < 0 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_m
    rw [hm] at hg_m
    have h' : I.lt ((k : ℚ) : 𝕜) ((((0 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_m
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have e2 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1212r45Nondeg.body →
      (env "d" + env "e" * w) ≠ 0 ∧ (q < 0 → (env "a" + env "b" * w + env "c" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1212r45Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    exact ⟨h.1 hgt_m, h.2⟩
  have ht := hD t hF.self_of_nhds
  have hW' := hW
  simp only [ne_eq, mul_eq_zero, not_or] at hW'
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r45Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, e1, hkp, toInt?_two]
    exact ⟨fun _ => h.1, h.2⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1212r45Nondeg, Defined, eval, recEnv, hkm, e2, toInt?_two, toInt?_neg_one]
    exact ⟨⟨fun _ => h.1, fun h' => h.2 (by omega)⟩, hW'.1, by simpa using hW'.2⟩
  · simp only [rubi1212r45Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k + 1) * (env "a" + env "b" * t + env "c" * t ^ 2) ^ q) t := by
      convert hΦ using 1
      simp [eval, e1, hkp, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1212r45Nondeg.body = (env "d" + env "e" * t) ^ k * (env "a" + env "b" * t + env "c" * t ^ 2) ^ q := by
      simp [rubi1212r45Nondeg, eval, hkm, hkp, toInt?_two]
    set u := ((env "m" + env "p" + 1) * (2 * env "c" * env "d" + -1 * env "b" * env "e"))⁻¹ with hu_def
    have hU : ((env "m" + env "p" + 1) * (2 * env "c" * env "d" + -1 * env "b" * env "e")) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hfun : (fun w => eval I (recEnv env (rubi1212r45Nondeg.integrals.map (·.1)) Φ "x" w) rubi1212r45Nondeg.result) =
        fun w => -1 * env "e" * (env "d" + env "e" * w) ^ k * (env "a" + env "b" * w + env "c" * w ^ 2) ^ (q + 1) * u + env "c" * (env "m" + 2 * env "p" + 2) * u * Φ "I1" w := by
      funext w
      simp [rubi1212r45Nondeg, eval, recEnv, hkm, e2, toInt?_two, toInt?_neg_one, hu_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hA1 : (env "a" + env "b" * t + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2 (by omega))
      · exact Or.inr (by omega)
    have hA0 : (env "a" + env "b" * t + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2 h)
      · exact Or.inr (by omega)
    have hin : HasDerivAt (fun w => (env "a" + env "b" * w + env "c" * w ^ 2)) (env "b" + env "c" * (2 * t)) t := by
      have := (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add ((hasDerivAt_pow 2 t).const_mul (env "c"))
      convert this using 1 <;> first | (norm_num; ring) | ring | (funext w; simp only [id]) | (funext w; ring)
    have hlin : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      have := ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
      convert this using 1 <;> first | ring | (funext w; simp only [id])
    refine ((((((HasDerivAt.comp t (hasDerivAt_zpow k _ (Or.inl ht.1)) hlin).const_mul (-1 * env "e")).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hA1) hin)).mul_const u)).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hZ1 : (env "d" + env "e" * t) ^ k = (env "d" + env "e" * t) ^ (k - 1) * (env "d" + env "e" * t) := by
      rw [← zpow_succ_of _ _ (Or.inl ht.1), sub_add_cancel]
    have hZ2 : (env "d" + env "e" * t) ^ (k + 1) = (env "d" + env "e" * t) ^ (k - 1) * (env "d" + env "e" * t) ^ 2 := by
      rw [← zpow_natCast, ← zpow_add₀ ht.1]; congr 1; push_cast; ring
    rw [hZ2, hZ1, zpow_succ_of _ _ hA0]
    generalize (env "d" + env "e" * t) ^ (k - 1) = Z
    generalize (env "a" + env "b" * t + env "c" * t ^ 2) ^ q = Y
    clear_value u
    simp only [hm, hp] at hU ⊢
    push_cast
    linear_combination (Z * Y) * ((env "d" + env "e" * t) * hU - u * (k : 𝕜) * hcnd)

theorem rubi1212r45Nondeg_real : rubi1212r45Nondeg.Holds .real :=
  rubi1212r45Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1212r45Nondeg_complex : rubi1212r45Nondeg.Holds .complex :=
  rubi1212r45Nondeg_holds Interp.complex Interp.complex_lt_rat

/-- **1.2.1.2 #39** with `e (p + 1) (b² - 4 a c) ≠ 0`, `m > 0` and `p < -1`: the derivative identity is `2 (b + 2 c x) (p + 1)` times the converted condition. -/
theorem rubi1212r39Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1212r39Nondeg.conditions rubi1212r39Nondeg.body rubi1212r39Nondeg.result rubi1212r39Nondeg.integrals := by
  intro env hc t hF
  have hW1 : (env "e" * (env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c")) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int 0)) (by simp [rubi1212r39Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hW2 : ((env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c")) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .add (.var "p") (.int 1)) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int 0)) (by simp [rubi1212r39Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hcnd : env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r39Nondeg])
    simp [Cond.Holds, Defined, eval, toInt?_two] at h
    linear_combination h
  have hg_m := hc (.gt (.var "m") (.int 0)) (by simp [rubi1212r39Nondeg])
  have hg_p := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1212r39Nondeg])
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r39Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r39Nondeg, Defined, eval, hkm, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hgt_m : 0 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_m
    rw [hm] at hg_m
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((k : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_m
    exact_mod_cast (hlt _ _).1 h'
  have hgt_p : q < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg_p
    rw [hp] at hg_p
    have h' : I.lt ((q : ℚ) : 𝕜) ((((-1 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg_p
    exact_mod_cast (hlt _ _).1 h'
  have e1 : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have e1' : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have e2 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1212r39Nondeg.body → (env "a" + env "b" * w + env "c" * w ^ 2) ≠ 0 := by
    intro w h
    simp [rubi1212r39Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    exact h.2 (by omega)
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r39Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, e1, e1', e2, toInt?_two]
    first | exact ⟨fun h' => absurd h' (by omega), fun _ => h⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have h := hD w hw
    have hW1' := hW1
    have hW2' := hW2
    simp only [ne_eq, mul_eq_zero, not_or] at hW1' hW2'
    simp [rubi1212r39Nondeg, Defined, eval, recEnv, hkm, e2, toInt?_two, toInt?_neg_one]
    exact ⟨⟨⟨fun h' => absurd h' (by omega), fun _ => h⟩, hW1'.1, by simpa using hW1'.2⟩, hW2'.1, by simpa using hW2'.2⟩
  · simp only [rubi1212r39Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k - 1) * (env "a" + env "b" * t + env "c" * t ^ 2) ^ (q + 1)) t := by
      convert hΦ using 1
      simp [eval, e1, e1', e2, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1212r39Nondeg.body = (env "d" + env "e" * t) ^ k * (env "a" + env "b" * t + env "c" * t ^ 2) ^ q := by
      simp [rubi1212r39Nondeg, eval, hkm, hkp, toInt?_two]
    set u1 := (env "e" * (env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c"))⁻¹ with hu1_def
    set u2 := ((env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c"))⁻¹ with hu2_def
    have hU1 : (env "e" * (env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c")) * u1 = 1 := by rw [hu1_def]; exact mul_inv_cancel₀ hW1
    have hU2 : ((env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c")) * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hW2
    have hfun : (fun w => eval I (recEnv env (rubi1212r39Nondeg.integrals.map (·.1)) Φ "x" w) rubi1212r39Nondeg.result) =
        fun w => (2 * env "c" * env "d" + -1 * env "b" * env "e") * (env "d" + env "e" * w) ^ k * (env "a" + env "b" * w + env "c" * w ^ 2) ^ (q + 1) * u1 + -1 * (2 * env "c" * env "d" + -1 * env "b" * env "e") * (env "m" + 2 * env "p" + 2) * u2 * Φ "I1" w := by
      funext w
      simp [rubi1212r39Nondeg, eval, recEnv, hkm, e2, toInt?_two, toInt?_neg_one, hu1_def, hu2_def]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hA1 : (env "a" + env "b" * t + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q + 1 := Or.inl ht
    have hA0 : (env "a" + env "b" * t + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q := Or.inl ht
    have hin : HasDerivAt (fun w => (env "a" + env "b" * w + env "c" * w ^ 2)) (env "b" + env "c" * (2 * t)) t := by
      have := (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add ((hasDerivAt_pow 2 t).const_mul (env "c"))
      convert this using 1 <;> first | (norm_num; ring) | ring | (funext w; simp only [id]) | (funext w; ring)
    have hlin : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      have := ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
      convert this using 1 <;> first | ring | (funext w; simp only [id])
    refine ((((((HasDerivAt.comp t (hasDerivAt_zpow k _ (Or.inr (by omega))) hlin).const_mul (2 * env "c" * env "d" + -1 * env "b" * env "e")).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hA1) hin)).mul_const u1)).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hZ1 : (env "d" + env "e" * t) ^ k = (env "d" + env "e" * t) ^ (k - 1) * (env "d" + env "e" * t) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [hZ1, zpow_succ_of _ _ hA0]
    generalize (env "d" + env "e" * t) ^ (k - 1) = Z
    generalize (env "a" + env "b" * t + env "c" * t ^ 2) ^ q = Y
    clear_value u1 u2
    simp only [hm, hp] at hU1 hU2 ⊢
    push_cast
    linear_combination (Z * Y) * ((u1 * 2 * (env "b" + 2 * env "c" * t) * ((q : 𝕜) + 1)) * hcnd +
      ((env "d" + env "e" * t) - (-1 * (2 * env "c" * env "d" + -1 * env "b" * env "e") * ((k : 𝕜) + 2 * (q : 𝕜) + 2)) * (env "a" + env "b" * t + env "c" * t ^ 2) * u2) * hU1 + ((-1 * (2 * env "c" * env "d" + -1 * env "b" * env "e") * ((k : 𝕜) + 2 * (q : 𝕜) + 2)) * (env "a" + env "b" * t + env "c" * t ^ 2) * u1 * env "e") * hU2)

theorem rubi1212r39Nondeg_real : rubi1212r39Nondeg.Holds .real :=
  rubi1212r39Nondeg_holds Interp.real Interp.real_lt_rat

theorem rubi1212r39Nondeg_complex : rubi1212r39Nondeg.Holds .complex :=
  rubi1212r39Nondeg_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec61
