import OSR.IntegrationRec91

/-!
# Integration (RUBI): strengthened variants of refuted named rules, fourteenth batch

RUBI 1.1.3.3 #5 is refuted as stated (at `a n (p + 1) = 0`); with
`a n (p + 1) ≠ 0` it is proved over ℝ and ℂ, the condition
`n (p + q + 1) + 1 = 0` closing the identity.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec109

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- rubi_1_1_3_3_r5 with NeQ[Multiply[a, n, Add[p, 1]], 0]; NeQ[Multiply[a, Add[p, 1]], 0] -/
def rubi1133r5Nondeg : CRule where
  id := "integration.rubi_1_1_3_3_r5_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "q")) (.pow (.app2 .mul (.var "a") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))))]
  independent := ["a", "b", "c", "d", "n", "p", "q"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0), .eq (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))) (.int 1)) (.int 0), .gt (.var "q") (.int 0), .ne (.var "p") (.int (-1)),
    .ne (.app2 .mul (.app2 .mul (.var "a") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0),
    .ne (.app2 .mul (.var "a") (.app2 .add (.var "p") (.int 1))) (.int 0)]
  priority := 9271
  description := "rubi_1_1_3_3_r5 with NeQ[Multiply[a, n, Add[p, 1]], 0]; NeQ[Multiply[a, Add[p, 1]], 0]"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:5" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q.m#5"


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

theorem rubi1133r5Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1133r5Nondeg.conditions rubi1133r5Nondeg.body rubi1133r5Nondeg.result rubi1133r5Nondeg.integrals := by
  intro env hc t hF
  have heq := hc (.eq (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))) (.int 1)) (.int 0)) (by simp [rubi1133r5Nondeg])
  simp [Cond.Holds, Defined, eval] at heq
  have hA0 := hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1133r5Nondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have gq := hc (.gt (.var "q") (.int 0)) (by simp [rubi1133r5Nondeg])
  rcases hk_p : I.toInt? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi1133r5Nondeg, Defined, eval, hk_p] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi1133r5Nondeg, Defined, eval, hk_p, hk_n] at h
  rcases hk_q : I.toInt? (env "q") with _ | kq
  · exfalso; have h := hF.self_of_nhds; simp [rubi1133r5Nondeg, Defined, eval, hk_p, hk_n, hk_q] at h
  have h_p : env "p" = (kp : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_q : env "q" = (kq : 𝕜) := (I.toInt?_eq _ _).1 hk_q
  have hkq : 0 < kq := by
    simp only [Cond.Holds, Defined, eval, true_and] at gq
    rw [h_q] at gq
    have h' : I.lt ((((0 : ℤ)) : ℚ) : 𝕜) ((kq : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using gq
    exact_mod_cast (hlt _ _).1 h'
  have ep1 : I.toInt? (env "p" + 1) = some (kp + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have eq1 : I.toInt? (env "q" + -1 * 1) = some (kq - 1) := (I.toInt?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have eq1' : I.toInt? (env "q" + -1) = some (kq - 1) := (I.toInt?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have hq0 : ¬ kq < 0 := by omega
  have hq1 : ¬ kq - 1 < 0 := by omega
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1133r5Nondeg.body → (j < 0 → w ≠ 0) ∧ (kp < 0 → (env "a" + env "b" * w ^ j) ≠ 0) := by
    intro w h
    simp [rubi1133r5Nondeg, Defined, eval, hk_p, hk_q, hk_n, ep1, eq1, eq1', toInt?_neg_one, hq0] at h
    first | exact ⟨h.1.1, h.1.2⟩ | exact ⟨h.1, h.2.1⟩ | tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1133r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hBody w hw
    simp [Defined, eval, hk_p, hk_q, hk_n, ep1, eq1, eq1', toInt?_neg_one, hq1]
    first | exact ⟨⟨h1, fun h => h2 (by omega)⟩, h1⟩ | exact ⟨h1, fun h => h2 (by omega), h1⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hBody w hw
    simp [rubi1133r5Nondeg, Defined, eval, recEnv, hk_p, hk_q, hk_n, ep1, eq1, eq1', toInt?_neg_one, hq0, hA0]
    first | exact ⟨⟨h1, fun h => h2 (by omega)⟩, h1⟩ | exact ⟨h1, fun h => h2 (by omega), h1⟩ | (trace_state; sorry)
  · simp only [rubi1133r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨ht0, hA0'⟩ := hBody t hF.self_of_nhds
    have hx : t ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (ht0 h)
      · exact Or.inr (by omega)
    have hAk : (env "a" + env "b" * t ^ j) ≠ 0 ∨ 0 ≤ kp := by
      by_cases h : kp < 0
      · exact Or.inl (hA0' h)
      · exact Or.inr (by omega)
    have hAk1 : (env "a" + env "b" * t ^ j) ≠ 0 ∨ 0 ≤ kp + 1 := by
      rcases hAk with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * t ^ j) ^ (kp + 1) * (env "c" + env "d" * t ^ j) ^ (kq - 1)) t := by
      convert hΦ using 1
      simp [eval, hk_p, hk_q, hk_n, ep1, eq1, eq1', toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1133r5Nondeg.body = (env "a" + env "b" * t ^ j) ^ kp * (env "c" + env "d" * t ^ j) ^ kq := by
      simp [rubi1133r5Nondeg, eval, hk_p, hk_q, hk_n, ep1, eq1, eq1', toInt?_neg_one]
    set W1 := (env "a" * env "n" * (env "p" + 1))⁻¹ with hW1_def
    have hW2e : (env "a" * (env "p" + 1))⁻¹ = env "n" * W1 := by
      rw [hW1_def]; casesm* _ ∧ _; field_simp
    have hU : env "a" * env "n" * (env "p" + 1) * W1 = 1 := by
      rw [hW1_def]; exact mul_inv_cancel₀ (by simp only [ne_eq, mul_eq_zero, not_or]; tauto)
    have hfun : (fun w => eval I (recEnv env (rubi1133r5Nondeg.integrals.map (·.1)) Φ "x" w) rubi1133r5Nondeg.result) =
        fun w => -1 * w * (env "a" + env "b" * w ^ j) ^ (kp + 1) * (env "c" + env "d" * w ^ j) ^ kq * W1 + -1 * env "c" * env "q" * (env "n" * W1) * Φ "I1" w := by
      funext w
      rw [← hW2e]
      simp [rubi1133r5Nondeg, eval, recEnv, hk_p, hk_q, hk_n, ep1, eq1, eq1', toInt?_neg_one, hW1_def, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hY := hasDerivAt_zpow j t hx
    have hAd : HasDerivAt (fun w => (env "a" + env "b" * w ^ j)) (env "b" * ((j : 𝕜) * t ^ (j - 1))) t := (hY.const_mul _).const_add _
    have hCd : HasDerivAt (fun w => (env "c" + env "d" * w ^ j)) (env "d" * ((j : 𝕜) * t ^ (j - 1))) t := (hY.const_mul _).const_add _
    have hAp := HasDerivAt.comp t (hasDerivAt_zpow (kp + 1) _ hAk1) hAd
    have hCp := HasDerivAt.comp t (hasDerivAt_zpow kq _ (Or.inr (by omega))) hCd
    have hX : HasDerivAt (fun w : 𝕜 => -1 * w) (-1 * 1) t := (hasDerivAt_id' t).const_mul _
    refine ((((hX.mul hAp).mul hCp).mul_const W1).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    have k1 : (j : 𝕜) * t ^ (j - 1) * t = (j : 𝕜) * t ^ j := by
      rcases em (j = 0) with h0 | h0
      · subst h0; simp
      · have h' : t ≠ 0 ∨ 0 ≤ j - 1 := by
          by_cases h : j < 0
          · exact Or.inl (ht0 h)
          · exact Or.inr (by omega)
        rw [show t ^ j = t ^ (j - 1) * t by rw [← zpow_succ_of _ _ h', sub_add_cancel]]
        ring
    rw [zpow_succ_of _ _ hAk, show (env "c" + env "d" * t ^ j) ^ kq = (env "c" + env "d" * t ^ j) ^ (kq - 1) * (env "c" + env "d" * t ^ j) by rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]]
    generalize (env "a" + env "b" * t ^ j) ^ kp = Ap
    generalize (env "c" + env "d" * t ^ j) ^ (kq - 1) = Cq1
    generalize t ^ (j - 1) = T1 at k1 ⊢
    generalize t ^ j = Y at k1 ⊢
    clear_value W1
    simp only [h_p, h_n, h_q] at hU heq ⊢
    push_cast
    linear_combination (Ap*Cq1*(Y*env "d" + env "c")) * hU + (-Ap*Cq1*W1*Y*env "b"*env "d"*(kp : 𝕜) - Ap*Cq1*W1*Y*env "b"*env "d"*(kq : 𝕜) - Ap*Cq1*W1*Y*env "b"*env "d" - Ap*Cq1*W1*env "a"*env "d"*(kq : 𝕜) - Ap*Cq1*W1*env "b"*env "c"*(kp : 𝕜) - Ap*Cq1*W1*env "b"*env "c") * k1 + (-Ap*Cq1*W1*Y^2*env "b"*env "d" - Ap*Cq1*W1*Y*env "b"*env "c" - Ap*Cq1*W1*env "a"*(Y*env "d" + env "c")) * heq

theorem rubi1133r5Nondeg_real : rubi1133r5Nondeg.Holds .real := rubi1133r5Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi1133r5Nondeg_complex : rubi1133r5Nondeg.Holds .complex := rubi1133r5Nondeg_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec109
