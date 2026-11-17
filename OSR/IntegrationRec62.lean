import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, fourteenth batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 1.2.1.2 #54, partial
fractions of `1 / ((d + e x) (a + b x + c x²))` when `2 c d = b e`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec62

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








/-- **1.2.1.2 #54** with `d (b² - 4 a c) ≠ 0` and `d² (b² - 4 a c) ≠ 0`: with `2 c d = b e`, `b (d + e x) = d (b + 2 c x)` and the partial fractions follow. -/
theorem rubi1212r54Nondeg_holds [CharZero 𝕜] (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1212r54Nondeg.conditions rubi1212r54Nondeg.body rubi1212r54Nondeg.result rubi1212r54Nondeg.integrals := by
  intro env hc t hF
  have hdisc : env "b" ^ 2 + -1 * 4 * env "a" * env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1212r54Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hcnd : 2 * env "c" * env "d" + -1 * env "b" * env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)) (by simp [rubi1212r54Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hW1 : env "d" * (env "b" ^ 2 + -1 * 4 * env "a" * env "c") ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "d") (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int 0)) (by simp [rubi1212r54Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hW2 : env "d" ^ 2 * (env "b" ^ 2 + -1 * 4 * env "a" * env "c") ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.var "d") (.int 2)) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int 0)) (by simp [rubi1212r54Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hd0 : env "d" ≠ 0 := left_ne_zero_of_mul hW1
  have hb0 : env "b" ≠ 0 := by
    intro hb
    have hc0 : env "c" = 0 := by
      have : 2 * env "c" * env "d" = 0 := by rw [hb] at hcnd; linear_combination hcnd
      rcases mul_eq_zero.1 this with h | h
      · rcases mul_eq_zero.1 h with h' | h'
        · exact absurd h' two_ne_zero
        · exact h'
      · exact absurd h hd0
    exact hdisc (by rw [hb, hc0]; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1212r54Nondeg.body →
      (env "d" + env "e" * w) ≠ 0 ∧ (env "a" + env "b" * w + env "c" * w ^ 2) ≠ 0 := by
    intro w h
    simp [rubi1212r54Nondeg, Defined, eval, toInt?_two, toInt?_neg_one] at h
    exact ⟨h.1, h.2⟩
  have hB : ∀ w, (env "d" + env "e" * w) ≠ 0 → (env "b" + 2 * env "c" * w) ≠ 0 := by
    intro w h hB0
    apply h
    have : env "b" * (env "d" + env "e" * w) = 0 := by
      linear_combination env "d" * hB0 - w * hcnd
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hb0
    · exact h'
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r54Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, toInt?_neg_one]
      exact hB w h.1
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, toInt?_two, toInt?_neg_one]
      exact h.2
  · exact Eventually.of_forall fun w => by
      simp [rubi1212r54Nondeg, Defined, eval, recEnv, toInt?_two, toInt?_neg_one]
      first | done | exact ⟨by simpa using hW1, by simpa using hW2⟩ | (simp only [ne_eq, mul_eq_zero, not_or] at hW1 hW2; simp_all)
  · simp only [rubi1212r54Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "b" + 2 * env "c" * t)⁻¹) t := by
      convert hΦ1 using 1
      simp [eval, toInt?_neg_one]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "d" + env "e" * t) * (env "a" + env "b" * t + env "c" * t ^ 2)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, toInt?_two, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1212r54Nondeg.body =
        (env "d" + env "e" * t)⁻¹ * (env "a" + env "b" * t + env "c" * t ^ 2)⁻¹ := by
      simp [rubi1212r54Nondeg, eval, toInt?_two, toInt?_neg_one, mul_inv]
      try ring
    have hfun : (fun w => eval I (recEnv env (rubi1212r54Nondeg.integrals.map (·.1)) Φ "x" w) rubi1212r54Nondeg.result) =
        fun w => -4 * env "b" * env "c" * (env "d" * (env "b" ^ 2 + -1 * 4 * env "a" * env "c"))⁻¹ * Φ "I1" w +
          env "b" ^ 2 * (env "d" ^ 2 * (env "b" ^ 2 + -1 * 4 * env "a" * env "c"))⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1212r54Nondeg, eval, recEnv, toInt?_two, toInt?_neg_one]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hBB := mul_inv_cancel₀ (hB t ht.1)
    have hAA := mul_inv_cancel₀ ht.2
    have hDD := mul_inv_cancel₀ ht.1
    have hu1 := mul_inv_cancel₀ hW1
    have hu2 := mul_inv_cancel₀ hW2
    generalize (env "b" + 2 * env "c" * t)⁻¹ = Bi at hBB ⊢
    generalize (env "a" + env "b" * t + env "c" * t ^ 2)⁻¹ = Ai at hAA ⊢
    generalize (env "d" + env "e" * t)⁻¹ = Di at hDD ⊢
    generalize (env "d" * (env "b" ^ 2 + -1 * 4 * env "a" * env "c"))⁻¹ = u1 at hu1 ⊢
    generalize (env "d" ^ 2 * (env "b" ^ 2 + -1 * 4 * env "a" * env "c"))⁻¹ = u2 at hu2 ⊢
    linear_combination
      (Ai * Di * (env "d" ^ 2 * (env "b" ^ 2 + -1 * 4 * env "a" * env "c")) * u2 - u2 * env "b" ^ 2 * (env "d" + env "e" * t) * Ai * (env "d" + env "e" * t) * Di) * hBB +
      (Ai * Di + 4 * env "b" * env "c" * Bi * u1) * hu2 +
      (-u2 * Bi * Ai * Di * (t * (-4 * env "a" * env "c" * env "d" + 2 * env "b" ^ 2 * env "d" + env "b" ^ 2 * env "e" * t + 2 * env "b" * env "c" * env "d" * t + 2 * env "b" * env "c" * env "e" * t ^ 2))) * hcnd +
      (4 * env "b" * env "c" * env "d" * u2 * Bi * (env "d" + env "e" * t) * Di) * hAA +
      (4 * env "b" * env "c" * env "d" * u2 * Bi - u2 * env "b" ^ 2 * (env "d" + env "e" * t) * Ai) * hDD +
      (-4 * env "b" * env "c" * env "d" * Bi * u2) * hu1

theorem rubi1212r54Nondeg_real : rubi1212r54Nondeg.Holds .real :=
  rubi1212r54Nondeg_holds Interp.real

theorem rubi1212r54Nondeg_complex : rubi1212r54Nondeg.Holds .complex :=
  rubi1212r54Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec62
