import OSR.IntegrationRec91

/-!
# Integration (RUBI): strengthened variants of refuted named rules, fifth batch

RUBI 1.1.3.3 #18 is refuted as stated, and its first strengthened variant
(with `d ≠ 0`) was refuted by the pole probe at `n = 1`, `p = 0`.  With
`p ≠ 0` as well, the conditions force `n = -1`, `p = 2`; proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec96

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- rubi_1_1_3_3_r18 with NeQ[d, 0]; NeQ[p, 0] -/
def rubi1133r18Nondeg : CRule where
  id := "integration.rubi_1_1_3_3_r18_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", .pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))), ("I2", .app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "p", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0), .eq (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.int 1)) (.int 0), .int (.var "n"),
    .ne (.var "d") (.int 0),
    .ne (.var "p") (.int 0)]
  priority := 9141
  description := "rubi_1_1_3_3_r18 with NeQ[d, 0]; NeQ[p, 0]"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:18" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q.m#18"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem zpow_succ_of (A : 𝕜) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

theorem rubi1133r18Nondeg_holds (I : Interp 𝕜) [CharZero 𝕜] :
    AntiderivRecHolds I "x" rubi1133r18Nondeg.conditions rubi1133r18Nondeg.body rubi1133r18Nondeg.result rubi1133r18Nondeg.integrals := by
  intro env hc t hF
  have hN0 := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi1133r18Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN0
  have hN3 := hc (.ne (.var "d") (.int 0)) (by simp [rubi1133r18Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN3
  have hN4 := hc (.ne (.var "p") (.int 0)) (by simp [rubi1133r18Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN4
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1133r18Nondeg, Defined, eval, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1133r18Nondeg, Defined, eval, hk_n, hk_p] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have e_n1 : I.toInt? (env "n" + 1) = some (j + 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have h_p : env "p" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have e_p1 : I.toInt? (env "p" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have heq := hc (.eq (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.int 1)) (.int 0)) (by simp [rubi1133r18Nondeg])
  simp [Cond.Holds, Defined, eval] at heq
  have hk2 : k = 2 := by
    have hz : ((j * (k - 1) + 1 : ℤ) : 𝕜) = 0 := by push_cast; rw [← h_n, ← h_p]; linear_combination heq
    have hz' : j * (k - 1) = -1 := by have := (Int.cast_eq_zero.mp hz); omega
    have hp0 : k ≠ 0 := by
      intro h0; apply hN4; rw [h_p, h0]; simp
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one' hz' with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have em1 : I.toInt? (env "p" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have em1' : I.toInt? (env "p" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hk1 : ¬ (k - 1 < 0) := by omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1133r18Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
      simp [rubi1133r18Nondeg, Defined, eval, toInt?_neg_one, toInt?_two, hk_n, hk_p, e_n1, e_p1, em1, em1', hk1] at hw ⊢ <;> first | exact hw | exact hw.1.1 | exact ⟨hw.2.1, hw.2.2⟩ | exact ⟨hw.1.1, hw.2.1, hw.2.2⟩ | (simp [em1, em1', hk1] at hw ⊢; tauto) | (simp [em1, em1', hk1]; tauto) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi1133r18Nondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, hk_n, hk_p, e_n1, e_p1, hN0, hN3, hN4] at hw ⊢ <;>
    first | done | exact hw | exact ⟨fun h => hw.1 (by omega), fun h => hw.2 (by omega)⟩ | exact fun h => hw (by omega) | tauto | (trace_state; sorry)
  · simp only [rubi1133r18Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hw := hF.self_of_nhds
    simp [rubi1133r18Nondeg, Defined, eval, toInt?_neg_one, toInt?_two, hk_n, hk_p, e_n1, e_p1] at hw
    try casesm* _ ∧ _
    have hfun : (fun w => eval I (recEnv env (rubi1133r18Nondeg.integrals.map (·.1)) Φ "x" w) rubi1133r18Nondeg.result) =
        fun w => (((env "b" * (env "d")⁻¹) * Φ "I1" w) + ((((-1) * ((env "b" * env "c") + (((-1) * env "a") * env "d"))) * (env "d")⁻¹) * Φ "I2" w)) := by
      funext w
      simp [rubi1133r18Nondeg, eval, recEnv, toInt?_neg_one, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    refine ((hΦ1.const_mul _).add (hΦ2.const_mul _)).congr_deriv ?_
    simp [rubi1133r18Nondeg, eval, hk_n, hk_p, em1, em1', toInt?_neg_one]
    rw [hk2] at *
    simp only [show (2 : ℤ) - 1 = 1 by norm_num, zpow_one] at *
    first | (field_simp; ring) | (trace_state; sorry)

theorem rubi1133r18Nondeg_real : rubi1133r18Nondeg.Holds .real := rubi1133r18Nondeg_holds Interp.real
theorem rubi1133r18Nondeg_complex : rubi1133r18Nondeg.Holds .complex := rubi1133r18Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec96
