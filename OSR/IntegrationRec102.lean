import OSR.IntegrationRec91

/-!
# Integration (RUBI): strengthened variants of refuted named rules, ninth batch

RUBI 1.2.3.3 #27 is refuted as stated (at `a n (p + 1) = 0`); with
`2 a n (p + 1) ≠ 0` it is proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec102

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- rubi_1_2_3_3_r27 with NeQ[Multiply[2, a, n, Add[p, 1]], 0] -/
def rubi1233r27Nondeg : CRule where
  id := "integration.rubi_1_2_3_3_r27_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.app2 .add (.app2 .mul (.var "d") (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p")) (.app2 .mul (.int 2) (.var "n"))) (.int 1))) (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p")) (.app2 .mul (.int 3) (.var "n"))) (.int 1))) (.pow (.var "x") (.var "n")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1))))]
  independent := ["a", "c", "d", "e", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")), .int (.var "p"), .gt (.int (-1)) (.var "p"),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)]
  priority := 9201
  description := "rubi_1_2_3_3_r27 with NeQ[Multiply[2, a, n, Add[p, 1]], 0]"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:27" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#27"


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

theorem rubi1233r27Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1233r27Nondeg.conditions rubi1233r27Nondeg.body rubi1233r27Nondeg.result rubi1233r27Nondeg.integrals := by
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1233r27Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hA0 := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1233r27Nondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have gp := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1233r27Nondeg])
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi1233r27Nondeg, Defined, eval, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi1233r27Nondeg, Defined, eval, hk_n, hk_p] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hq : q < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at gp
    rw [h_p] at gp
    have h' : I.lt ((q : ℚ) : 𝕜) ((((-1 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using gp
    exact_mod_cast (hlt _ _).1 h'
  have hj0 : j ≠ 0 := by intro h; simp [h_n, h] at hA0
  have e2 : I.toInt? (env "n2") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [hn2, h_n]; push_cast; ring)
  have e2' : I.toInt? (2 * env "n") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have ep1 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hsq : ∀ w : 𝕜, w ^ (2 * j) = (w ^ j) ^ 2 := by
    intro w; rw [mul_comm, zpow_mul]; norm_cast
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1233r27Nondeg.body → (j < 0 → w ≠ 0) ∧ (env "a" + env "c" * (w ^ j) ^ 2) ≠ 0 := by
    intro w h
    simp [rubi1233r27Nondeg, Defined, eval, hk_n, hk_p, e2, e2', hsq] at h
    first | exact ⟨h.1, h.2.2 (by omega)⟩ | exact ⟨h.1.1, h.2.2 (by omega)⟩ | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1233r27Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hBody w hw
    simp [Defined, eval, hk_n, ep1, e2, e2', hsq, toInt?_two]
    exact ⟨h1, fun h => h1 (by omega), fun _ => h2⟩
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hBody w hw
    simp [rubi1233r27Nondeg, Defined, eval, recEnv, hk_n, ep1, e2, e2', hsq, toInt?_two, toInt?_neg_one, hA0]
    exact ⟨h1, fun h => h1 (by omega), fun _ => h2⟩
  · simp only [rubi1233r27Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨ht0, hQ0⟩ := hBody t hF.self_of_nhds
    have hx : t ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (ht0 h)
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" * (2 * env "n" * env "p" + 2 * env "n" + 1) + env "e" * (2 * env "n" * env "p" + 3 * env "n" + 1) * t ^ j) * (env "a" + env "c" * (t ^ j) ^ 2) ^ (q + 1)) t := by
      convert hΦ using 1
      simp [eval, hk_n, ep1, e2, e2', hsq, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1233r27Nondeg.body = (env "d" + env "e" * t ^ j) * (env "a" + env "c" * (t ^ j) ^ 2) ^ q := by
      simp [rubi1233r27Nondeg, eval, hk_n, hk_p, e2, e2', hsq]
    set W := (2 * env "a" * env "n" * (env "p" + 1))⁻¹ with hW_def
    have hWW : 2 * env "a" * env "n" * (env "p" + 1) * W = 1 := by
      rw [hW_def]; exact mul_inv_cancel₀ (by simp only [ne_eq, mul_eq_zero, not_or]; tauto)
    have hfun : (fun w => eval I (recEnv env (rubi1233r27Nondeg.integrals.map (·.1)) Φ "x" w) rubi1233r27Nondeg.result) =
        fun w => -1 * w * (env "d" + env "e" * w ^ j) * (env "a" + env "c" * (w ^ j) ^ 2) ^ (q + 1) * W + 1 * W * Φ "I1" w := by
      funext w
      simp [rubi1233r27Nondeg, eval, recEnv, hk_n, ep1, e2, e2', hsq, toInt?_two, toInt?_neg_one, hW_def, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hY := hasDerivAt_zpow j t hx
    have hDd : HasDerivAt (fun w => (env "d" + env "e" * w ^ j)) (env "e" * ((j : 𝕜) * t ^ (j - 1))) t := (hY.const_mul _).const_add _
    have hQd : HasDerivAt (fun w => (env "a" + env "c" * (w ^ j) ^ 2)) (env "c" * (2 * (t ^ j) ^ (2 - 1) * ((j : 𝕜) * t ^ (j - 1)))) t := by
      have := ((hY.pow 2).const_mul (env "c")).const_add (env "a")
      convert this using 1
      try (push_cast; ring)
    have hQp := HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ (Or.inl hQ0)) hQd
    have hX : HasDerivAt (fun w : 𝕜 => -1 * w) (-1 * 1) t := (hasDerivAt_id' t).const_mul _
    refine ((((hX.mul hDd).mul hQp).mul_const W).add (hΦ'.const_mul _)).congr_deriv ?_
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
    rw [zpow_add_one₀ hQ0]
    generalize (env "a" + env "c" * (t ^ j) ^ 2) ^ q = Qp
    generalize t ^ (j - 1) = T1 at k1 ⊢
    generalize t ^ j = Y at k1 ⊢
    clear_value W
    simp only [h_n, h_p] at hWW ⊢
    norm_num
    linear_combination (Qp * (Y * env "e" + env "d")) * hWW +
      (-Qp * W * (2 * Y ^ 2 * env "c" * env "e" * (q : 𝕜) + 3 * Y ^ 2 * env "c" * env "e" + 2 * Y * env "c" * env "d" * (q : 𝕜) + 2 * Y * env "c" * env "d" + env "a" * env "e")) * k1

theorem rubi1233r27Nondeg_real : rubi1233r27Nondeg.Holds .real := rubi1233r27Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi1233r27Nondeg_complex : rubi1233r27Nondeg.Holds .complex := rubi1233r27Nondeg_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec102
