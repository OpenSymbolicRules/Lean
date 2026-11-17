import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, thirty-ninth batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 1.1.1.4 #6, the
reduction of `(a + b x)^m (c + d x)^n (e + f x)(g + h x)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec87

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








/-- **1.1.1.4 #6** (two linear factors times powers) with `b² d² (m + n + 2)(m + n + 3) ≠ 0`. -/
theorem linFourNondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" linFourNondeg.conditions linFourNondeg.body linFourNondeg.result linFourNondeg.integrals := by
  intro env hc t hF
  have hD : env "b" ^ 2 * env "d" ^ 2 * (env "m" + env "n" + 2) * (env "m" + env "n" + 3) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3))) (.int 0)) (by simp [linFourNondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  rcases hkm : I.toInt? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [linFourNondeg, Defined, eval, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [linFourNondeg, Defined, eval, hkm, hkn] at h
  have h_m : env "m" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have h_n : env "n" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have e1 : I.toInt? (env "m" + 1) = some (j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have e2 : I.toInt? (env "n" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have hBody : ∀ w, Defined I (Function.update env "x" w) linFourNondeg.body →
      (j < 0 → ¬env "a" + env "b" * w = 0) ∧ (k < 0 → ¬env "c" + env "d" * w = 0) := by
    intro w h
    simpa [linFourNondeg, Defined, eval, hkm, hkn] using h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [linFourNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simpa [Defined, eval, hkm, hkn] using hBody w hw
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hBody w hw
    simp [linFourNondeg, Defined, eval, recEnv, hkm, hkn, e1, e2, toInt?_two, toInt?_neg_one]
    first | exact ⟨⟨fun h => h1 (by omega), fun h => h2 (by omega)⟩, by simpa [toInt?_two] using hD⟩ | (trace_state; sorry)
  · simp only [linFourNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hA, hC⟩ := hBody t hF.self_of_nhds
    have hA0 : env "a" + env "b" * t ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (hA h)
      · exact Or.inr (by omega)
    have hC0 : env "c" + env "d" * t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (hC h)
      · exact Or.inr (by omega)
    have hA1 : env "a" + env "b" * t ≠ 0 ∨ 0 ≤ j + 1 := by
      rcases hA0 with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hC1 : env "c" + env "d" * t ≠ 0 ∨ 0 ≤ k + 1 := by
      rcases hC0 with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * t) ^ j * (env "c" + env "d" * t) ^ k) t := by
      convert hΦ using 1
      simp [eval, hkm, hkn]
    have hEF : eval I (Function.update env "x" t) linFourNondeg.body =
        (env "a" + env "b" * t) ^ j * (env "c" + env "d" * t) ^ k * (env "e" + env "f" * t) * (env "g" + env "h" * t) := by
      simp [linFourNondeg, eval, hkm, hkn]
    set W := (env "b" ^ 2 * env "d" ^ 2 * (env "m" + env "n" + 2) * (env "m" + env "n" + 3))⁻¹ with hW_def
    have hWW : env "b" ^ 2 * env "d" ^ 2 * (env "m" + env "n" + 2) * (env "m" + env "n" + 3) * W = 1 := by
      rw [hW_def]; exact mul_inv_cancel₀ hD
    have hfun : (fun w => eval I (recEnv env (linFourNondeg.integrals.map (·.1)) Φ "x" w) linFourNondeg.result) =
        fun w => ((-1 * (env "a" * env "d" * env "f" * env "h" * (env "n" + 2) + env "b" * env "c" * env "f" * env "h" * (env "m" + 2) + -1 * env "b" * env "d" * (env "f" * env "g" + env "e" * env "h") * (env "m" + env "n" + 3))) + (env "b" * env "d" * env "f" * env "h" * (env "m" + env "n" + 2)) * w) * (env "a" + env "b" * w) ^ (j + 1) * (env "c" + env "d" * w) ^ (k + 1) * W +
          (env "a" ^ 2 * env "d" ^ 2 * env "f" * env "h" * (env "n" + 1) * (env "n" + 2) + env "a" * env "b" * env "d" * (env "n" + 1) * (2 * env "c" * env "f" * env "h" * (env "m" + 1) + -1 * env "d" * (env "f" * env "g" + env "e" * env "h") * (env "m" + env "n" + 3)) + env "b" ^ 2 * (env "c" ^ 2 * env "f" * env "h" * (env "m" + 1) * (env "m" + 2) + -1 * env "c" * env "d" * (env "f" * env "g" + env "e" * env "h") * (env "m" + 1) * (env "m" + env "n" + 3) + env "d" ^ 2 * env "e" * env "g" * (env "m" + env "n" + 2) * (env "m" + env "n" + 3))) * W * Φ "I1" w := by
      funext w
      simp [linFourNondeg, eval, recEnv, hkm, hkn, e1, e2, toInt?_two, toInt?_neg_one, hW_def, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hP : HasDerivAt (fun w => (-1 * (env "a" * env "d" * env "f" * env "h" * (env "n" + 2) + env "b" * env "c" * env "f" * env "h" * (env "m" + 2) + -1 * env "b" * env "d" * (env "f" * env "g" + env "e" * env "h") * (env "m" + env "n" + 3))) + (env "b" * env "d" * env "f" * env "h" * (env "m" + env "n" + 2)) * w) ((env "b" * env "d" * env "f" * env "h" * (env "m" + env "n" + 2)) * 1) t :=
      ((hasDerivAt_id' t).const_mul _).const_add _
    have hAd : HasDerivAt (fun w => env "a" + env "b" * w) (env "b" * 1) t :=
      ((hasDerivAt_id' t).const_mul _).const_add _
    have hCd : HasDerivAt (fun w => env "c" + env "d" * w) (env "d" * 1) t :=
      ((hasDerivAt_id' t).const_mul _).const_add _
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (j + 1) _ hA1) hAd
    have hCp := HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hC1) hCd
    refine ((((hP.mul hAp).mul hCp).mul_const W).add (hΦ'.const_mul ((env "a" ^ 2 * env "d" ^ 2 * env "f" * env "h" * (env "n" + 1) * (env "n" + 2) + env "a" * env "b" * env "d" * (env "n" + 1) * (2 * env "c" * env "f" * env "h" * (env "m" + 1) + -1 * env "d" * (env "f" * env "g" + env "e" * env "h") * (env "m" + env "n" + 3)) + env "b" ^ 2 * (env "c" ^ 2 * env "f" * env "h" * (env "m" + 1) * (env "m" + 2) + -1 * env "c" * env "d" * (env "f" * env "g" + env "e" * env "h") * (env "m" + 1) * (env "m" + env "n" + 3) + env "d" ^ 2 * env "e" * env "g" * (env "m" + env "n" + 2) * (env "m" + env "n" + 3))) * W))).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hA0, zpow_succ_of _ _ hC0]
    generalize (env "a" + env "b" * t) ^ j = Am
    generalize (env "c" + env "d" * t) ^ k = Cn
    clear_value W
    simp only [h_m, h_n] at hWW ⊢
    push_cast
    linear_combination (Am * Cn * (env "e" + env "f" * t) * (env "g" + env "h" * t)) * hWW

theorem linFourNondeg_real : linFourNondeg.Holds .real := linFourNondeg_holds Interp.real
theorem linFourNondeg_complex : linFourNondeg.Holds .complex := linFourNondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec87
