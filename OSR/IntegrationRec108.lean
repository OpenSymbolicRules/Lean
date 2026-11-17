import OSR.IntegrationRec91

/-!
# Integration (RUBI): strengthened variants of refuted named rules, thirteenth batch

RUBI 1.2.1.3 #26 is refuted as stated (a coefficient the result divides by may
vanish).  With `c (p + 1) (2 c d - b e) ≠ 0` it is proved over ℝ and ℂ: the
conditions force `e ≠ 0`, and `c d² - b d e + a e² = 0` gives
`e² (a + b x + c x²) = (d + e x) (c e x - c d + b e)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec108

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- rubi_1_2_1_3_r26 with NeQ[Multiply[c, Add[p, 1], Add[Multiply[2, c, d], Multiply[-1, b, e]]], 0] -/
def rubi1213r26Nondeg : CRule where
  id := "integration.rubi_1_2_1_3_r26_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:26"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "g") (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.var "f"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.app2 .add (.app2 .mul (.var "m") (.app2 .add (.app2 .mul (.var "g") (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.var "f")))) (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g")))))) (.pow (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0), .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0), .gt (.int (-1)) (.var "p"), .gt (.var "m") (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.int 0)]
  priority := 9261
  description := "rubi_1_2_1_3_r26 with NeQ[Multiply[c, Add[p, 1], Add[Multiply[2, c, d], Multiply[-1, b, e]]], 0]"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:26" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#26"


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

theorem rubi1213r26Nondeg_holds [CharZero 𝕜] (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1213r26Nondeg.conditions rubi1213r26Nondeg.body rubi1213r26Nondeg.result rubi1213r26Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have heq := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1213r26Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at heq
  have hA0 := hc (.ne (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.int 0)) (by simp [rubi1213r26Nondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hc0 : env "c" ≠ 0 := by intro h; simp [h] at hA0
  have hp0 : env "p" + 1 ≠ 0 := by intro h; simp [h] at hA0
  have hB0 : 2 * env "c" * env "d" + -1 * env "b" * env "e" ≠ 0 := by
    intro h; apply hA0.2; linear_combination h
  have he0 : env "e" ≠ 0 := by
    intro h
    have hd : env "d" = 0 := by
      have : env "c" * env "d" ^ 2 = 0 := by rw [h] at heq; linear_combination heq
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd h1 hc0
      · exact pow_eq_zero_iff (by norm_num) |>.1 h1
    apply hB0; rw [h, hd]; ring
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1213r26Nondeg, Defined, eval, hk_m] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi1213r26Nondeg, Defined, eval, hk_m, hk_p, toInt?_two] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hq1 : (q : 𝕜) + 1 ≠ 0 := by rw [← h_p]; exact hp0
  have em1 : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em1' : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ep1 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have gp := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1213r26Nondeg])
  have gm := hc (.gt (.var "m") (.int 0)) (by simp [rubi1213r26Nondeg])
  have hq : q < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at gp; rw [h_p] at gp; exact ord _ _ (by simpa using gp)
  have hk : 0 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm; rw [h_m] at gm; exact ord _ _ (by simpa using gm)
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1213r26Nondeg.body → (env "a" + env "b" * w + env "c" * w ^ 2) ≠ 0 := by
    intro w h
    simp [rubi1213r26Nondeg, Defined, eval, hk_m, hk_p, em1, em1', ep1, toInt?_neg_one, toInt?_two, hk0] at h
    first | exact h (by omega) | exact h.2 (by omega) | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r26Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hQ := hBody w hw
    simp [Defined, eval, hk_m, hk_p, em1, em1', ep1, toInt?_neg_one, toInt?_two, hk1, hQ]
  · filter_upwards [hF] with w hw
    have hQ := hBody w hw
    simp [rubi1213r26Nondeg, Defined, eval, recEnv, hk_m, hk_p, em1, em1', ep1, toInt?_neg_one, toInt?_two, hk0, hQ, hA0]
  · simp only [rubi1213r26Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hQ0 := hBody t hF.self_of_nhds
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k - 1) * (env "a" + env "b" * t + env "c" * t ^ 2) ^ (q + 1)) t := by
      convert hΦ using 1
      simp [eval, hk_m, hk_p, em1, em1', ep1, toInt?_neg_one, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1213r26Nondeg.body = (env "d" + env "e" * t) ^ k * (env "f" + env "g" * t) * (env "a" + env "b" * t + env "c" * t ^ 2) ^ q := by
      simp [rubi1213r26Nondeg, eval, hk_m, hk_p, em1, em1', ep1, toInt?_neg_one, toInt?_two]
    have hfun : (fun w => eval I (recEnv env (rubi1213r26Nondeg.integrals.map (·.1)) Φ "x" w) rubi1213r26Nondeg.result) =
        fun w => (env "g" * (env "c" * env "d" + -1 * env "b" * env "e") + env "c" * env "e" * env "f") * (env "d" + env "e" * w) ^ k * (env "a" + env "b" * w + env "c" * w ^ 2) ^ (q + 1) * (env "c" * (env "p" + 1) * (2 * env "c" * env "d" + -1 * env "b" * env "e"))⁻¹ + (-1 * env "e" * (env "m" * (env "g" * (env "c" * env "d" + -1 * env "b" * env "e") + env "c" * env "e" * env "f") + env "e" * (env "p" + 1) * (2 * env "c" * env "f" + -1 * env "b" * env "g"))) * (env "c" * (env "p" + 1) * (2 * env "c" * env "d" + -1 * env "b" * env "e"))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi1213r26Nondeg, eval, recEnv, hk_m, hk_p, em1, em1', ep1, toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hDd : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
    have hQd : HasDerivAt (fun w => (env "a" + env "b" * w + env "c" * w ^ 2)) (env "b" + env "c" * (2 * t)) t := by
      have := (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add ((hasDerivAt_pow 2 t).const_mul (env "c"))
      convert this using 1
      norm_num
    have hDp := HasDerivAt.comp t (hasDerivAt_zpow k _ (Or.inr (by omega))) hDd
    have hQp := HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ (Or.inl hQ0)) hQd
    refine ((((hDp.const_mul _).mul hQp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hQe : (env "a" + env "b" * t + env "c" * t ^ 2) = (env "d" + env "e" * t) * (env "c" * env "e" * t + -1 * env "c" * env "d" + env "b" * env "e") * (env "e" ^ 2)⁻¹ := by
      field_simp
      first | linear_combination heq | linear_combination -heq | linear_combination (-1) * heq
    rw [show (env "d" + env "e" * t) ^ k = (env "d" + env "e" * t) ^ (k - 1) * (env "d" + env "e" * t) by rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel],
      zpow_add_one₀ hQ0]
    generalize (env "d" + env "e" * t) ^ (k - 1) = Dk
    generalize (env "a" + env "b" * t + env "c" * t ^ 2) ^ q = Qp
    rw [hQe]
    rw [h_m, h_p] at *
    generalize hBe : 2 * env "c" * env "d" + -1 * env "b" * env "e" = Bv at hB0 ⊢
    field_simp
    subst hBe
    push_cast
    ring

theorem rubi1213r26Nondeg_real : rubi1213r26Nondeg.Holds .real := rubi1213r26Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi1213r26Nondeg_complex : rubi1213r26Nondeg.Holds .complex := rubi1213r26Nondeg_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec108
