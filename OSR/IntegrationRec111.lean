import OSR.IntegrationRec91
import OSR.IntegrationRec7

/-!
# Integration (RUBI): strengthened variants of logarithmic rules failing at a vanishing exponent

RUBI 3.3 #29 and #31 and 3.1.5 #33 are refuted as stated, and their first
strengthened variants fail numerically when an exponent vanishes (`n = 0` or
`r = 0`), where the integrand is defined at a pole of a residual integrand.
With that exponent nonzero they are proved over ℝ, with the real logarithm; the
complex domain stays unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec111

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- ∫ log(f x^m) (a + b log(c (d + e x)^n))/x, when 2 m ≠ 0 and n ≠ 0 -/
def logLogLinOverXNondeg : CRule where
  id := "integration.log_monomial_log_linear_over_x_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:29"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m")))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m")))) (.int 2)) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.pow (.app2 .mul (.int 2) (.var "m")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "n")) (.pow (.app2 .mul (.int 2) (.var "m")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.pow (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m")))) (.int 2)) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.ne (.app2 .mul (.int 2) (.var "m")) (.int 0),
    .ne (.var "n") (.int 0)]
  priority := 9291
  description := "∫ log(f x^m) (a + b log(c (d + e x)^n))/x, when 2 m ≠ 0 and n ≠ 0"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:29" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#29"

/-- rubi_3_3_r31 with NeQ[Multiply[2, m], 0]; NeQ[n, 0] -/
def rubi33r31Nondeg : CRule where
  id := "integration.rubi_3_3_r31_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:31"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p"))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m")))) (.int 2)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p"))) (.pow (.app2 .mul (.int 2) (.var "m")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "n")) (.var "p")) (.pow (.app2 .mul (.int 2) (.var "m")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.app2 .mul (.pow (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m")))) (.int 2)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "p"), .gt (.var "p") (.int 0),
    .ne (.app2 .mul (.int 2) (.var "m")) (.int 0),
    .ne (.var "n") (.int 0)]
  priority := 9292
  description := "rubi_3_3_r31 with NeQ[Multiply[2, m], 0]; NeQ[n, 0]"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:31" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#31"

/-- rubi_3_1_5_r33 with NeQ[Multiply[b, n, Add[p, 1]], 0]; NeQ[r, 0] -/
def rubi315r33Nondeg : CRule where
  id := "integration.rubi_3_1_5_r33_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:33"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "d") (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "m")))) (.var "r")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "d") (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "m")))) (.var "r")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.var "r")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "m")))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "f", "r", "m", "n", "p"]
  conditions := [.int (.var "p"), .gt (.var "p") (.int 0), .ne (.app2 .mul (.var "d") (.var "e")) (.int 1),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0),
    .ne (.var "r") (.int 0)]
  priority := 9293
  description := "rubi_3_1_5_r33 with NeQ[Multiply[b, n, Add[p, 1]], 0]; NeQ[r, 0]"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:33" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#33"


/-! ## Proofs -/

section Proofs

private theorem zpow_succ_of (A : ℝ) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

theorem logLogLinOverXNondeg_real : logLogLinOverXNondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" logLogLinOverXNondeg.conditions logLogLinOverXNondeg.body logLogLinOverXNondeg.result logLogLinOverXNondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hi2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have ord : ∀ (x y : ℤ), Interp.real.lt (x : ℝ) (y : ℝ) → x < y := by
    intro x y h
    have h' : Interp.real.lt ((x : ℚ) : ℝ) ((y : ℚ) : ℝ) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (Interp.real_lt_rat _ _).1 h'
  have hA0 := hc (.ne (.app2 .mul (.int 2) (.var "m")) (.int 0)) (by simp [logLogLinOverXNondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hn0 : env "n" ≠ 0 := by have h := hc (.ne (.var "n") (.int 0)) (by simp [logLogLinOverXNondeg]); simpa [Cond.Holds, Defined, eval] using h
  rcases hk_m : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [logLogLinOverXNondeg, Defined, eval, Interp.real, hm1, hk_m, -Real.log_eq_zero] at h
  have h_m : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hk_m
  rcases hk_n : intValue? (env "n") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [logLogLinOverXNondeg, Defined, eval, Interp.real, hm1, hk_m, hk_n, -Real.log_eq_zero] at h
  have h_n : env "n" = (i : ℝ) := (intValue?_eq _ _).1 hk_n

  have hi0 : i ≠ 0 := by intro h; apply hn0; rw [h_n, h]; simp
  have hj0 : j ≠ 0 := by intro h; apply hA0; rw [h_m, h]; simp
  have hDne : ∀ w : ℝ, 0 < env "c" * (env "d" + env "e" * w) ^ i → (env "d" + env "e" * w) ≠ 0 := by
    intro w h h0; rw [h0, zero_zpow i hi0, mul_zero] at h; exact lt_irrefl 0 h
  have hwne : ∀ w : ℝ, 0 < env "f" * w ^ j → w ≠ 0 := by
    intro w h h0; rw [h0, zero_zpow j hj0, mul_zero] at h; exact lt_irrefl 0 h
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) logLogLinOverXNondeg.body →
      0 < env "f" * w ^ j ∧ 0 < env "c" * (env "d" + env "e" * w) ^ i := by
    intro w h
    simp [logLogLinOverXNondeg, Defined, eval, Interp.real, hk_m, hk_n, hm1, hi2, -Real.log_eq_zero] at h
    first | exact ⟨h.1.1.2, h.1.2.2⟩ | exact ⟨h.1.1.2, h.1.2.2.2⟩ | exact ⟨h.1.1.2, h.1.2⟩ | tauto | (trace_state; sorry)
  refine ⟨fun i' hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [logLogLinOverXNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hBody w hw
    simp [Defined, eval, Interp.real, hk_m, hk_n, hm1, hi2, -Real.log_eq_zero, h1, h2, hDne w h2, hwne w h1]
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hBody w hw
    simp [logLogLinOverXNondeg, Defined, eval, Interp.real, recEnv, hk_m, hk_n, hm1, hi2, -Real.log_eq_zero, h1, h2, hDne w h2, hwne w h1, hA0]
  · simp only [logLogLinOverXNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hp1', hp2'⟩ := hBody t hF.self_of_nhds
    have ht0 := hwne t hp1'
    have hD0 := hDne t hp2'
    have hΦ' : HasDerivAt (Φ "I1") (Real.log (env "f" * t ^ j) ^ 2 * (env "d" + env "e" * t)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hk_m, hk_n, hm1, hi2, -Real.log_eq_zero]
    have hEF : eval Interp.real (Function.update env "x" t) logLogLinOverXNondeg.body = Real.log (env "f" * t ^ j) * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) * t⁻¹ := by
      simp [logLogLinOverXNondeg, eval, Interp.real, hk_m, hk_n, hm1, hi2, -Real.log_eq_zero]
    have hfun : (fun w => eval Interp.real (recEnv env (logLogLinOverXNondeg.integrals.map (·.1)) Φ "x" w) logLogLinOverXNondeg.result) =
        fun w => Real.log (env "f" * w ^ j) ^ 2 * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * w) ^ i)) * (2 * env "m")⁻¹ + -1 * env "b" * env "e" * env "n" * (2 * env "m")⁻¹ * Φ "I1" w := by
      funext w
      simp [logLogLinOverXNondeg, eval, Interp.real, recEnv, hk_m, hk_n, hm1, hi2, -Real.log_eq_zero, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hL1 := OSR.IntegrationRec7.hasDerivAt_log_monomial (env "f") t j hp1'
    have hDd : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
    have hL2 := (OSR.IntegrationRec7.hasDerivAt_log_monomial (env "c") (env "d" + env "e" * t) i hp2').comp t hDd
    have hΛ := (hL2.const_mul (env "b")).const_add (env "a")
    have hΛp := hΛ
    refine ((((hL1.pow 2).mul hΛp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    generalize (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) = Lm
    generalize Real.log (env "f" * t ^ j) = L1
    simp only [div_eq_mul_inv]
    generalize hDe : (env "d" + env "e" * t) = D at hD0 ⊢
    simp only [h_m, h_n] at *
    try casesm* _ ∧ _
    field_simp
    push_cast
    ring

theorem rubi33r31Nondeg_real : rubi33r31Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi33r31Nondeg.conditions rubi33r31Nondeg.body rubi33r31Nondeg.result rubi33r31Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hi2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have ord : ∀ (x y : ℤ), Interp.real.lt (x : ℝ) (y : ℝ) → x < y := by
    intro x y h
    have h' : Interp.real.lt ((x : ℚ) : ℝ) ((y : ℚ) : ℝ) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (Interp.real_lt_rat _ _).1 h'
  have hA0 := hc (.ne (.app2 .mul (.int 2) (.var "m")) (.int 0)) (by simp [rubi33r31Nondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hn0 : env "n" ≠ 0 := by have h := hc (.ne (.var "n") (.int 0)) (by simp [rubi33r31Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  rcases hk_m : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi33r31Nondeg, Defined, eval, Interp.real, hm1, hk_m, -Real.log_eq_zero] at h
  have h_m : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hk_m
  rcases hk_n : intValue? (env "n") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi33r31Nondeg, Defined, eval, Interp.real, hm1, hk_m, hk_n, -Real.log_eq_zero] at h
  have h_n : env "n" = (i : ℝ) := (intValue?_eq _ _).1 hk_n
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi33r31Nondeg, Defined, eval, Interp.real, hm1, hk_m, hk_n, hk_p, -Real.log_eq_zero] at h
  have h_p : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have g_p := hc (.gt (.var "p") (.int 0)) (by simp [rubi33r31Nondeg])
  have hkp : 0 < kp := by
    simp only [Cond.Holds, Defined, eval, true_and] at g_p; simp only [h_p] at g_p; exact ord _ _ (by simpa using g_p)
  have ep1 : intValue? (env "p" + -1 * 1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep1' : intValue? (env "p" + -1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hp0 : ¬ kp < 0 := by omega
  have hp1 : ¬ kp - 1 < 0 := by omega
  have hi0 : i ≠ 0 := by intro h; apply hn0; rw [h_n, h]; simp
  have hj0 : j ≠ 0 := by intro h; apply hA0; rw [h_m, h]; simp
  have hDne : ∀ w : ℝ, 0 < env "c" * (env "d" + env "e" * w) ^ i → (env "d" + env "e" * w) ≠ 0 := by
    intro w h h0; rw [h0, zero_zpow i hi0, mul_zero] at h; exact lt_irrefl 0 h
  have hwne : ∀ w : ℝ, 0 < env "f" * w ^ j → w ≠ 0 := by
    intro w h h0; rw [h0, zero_zpow j hj0, mul_zero] at h; exact lt_irrefl 0 h
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi33r31Nondeg.body →
      0 < env "f" * w ^ j ∧ 0 < env "c" * (env "d" + env "e" * w) ^ i := by
    intro w h
    simp [rubi33r31Nondeg, Defined, eval, Interp.real, hk_m, hk_n, hk_p, ep1, ep1', hm1, hi2, -Real.log_eq_zero, hp0, hp1] at h
    first | exact ⟨h.1.1.2, h.1.2.2⟩ | exact ⟨h.1.1.2, h.1.2.2.2⟩ | exact ⟨h.1.1.2, h.1.2⟩ | tauto | (trace_state; sorry)
  refine ⟨fun i' hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi33r31Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hBody w hw
    simp [Defined, eval, Interp.real, hk_m, hk_n, hk_p, ep1, ep1', hm1, hi2, -Real.log_eq_zero, hp0, hp1, h1, h2, hDne w h2, hwne w h1]
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hBody w hw
    simp [rubi33r31Nondeg, Defined, eval, Interp.real, recEnv, hk_m, hk_n, hk_p, ep1, ep1', hm1, hi2, -Real.log_eq_zero, hp0, hp1, h1, h2, hDne w h2, hwne w h1, hA0]
  · simp only [rubi33r31Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hp1', hp2'⟩ := hBody t hF.self_of_nhds
    have ht0 := hwne t hp1'
    have hD0 := hDne t hp2'
    have hΦ' : HasDerivAt (Φ "I1") (Real.log (env "f" * t ^ j) ^ 2 * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) ^ (kp - 1) * (env "d" + env "e" * t)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hk_m, hk_n, hk_p, ep1, ep1', hm1, hi2, -Real.log_eq_zero]
    have hEF : eval Interp.real (Function.update env "x" t) rubi33r31Nondeg.body = Real.log (env "f" * t ^ j) * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) ^ kp * t⁻¹ := by
      simp [rubi33r31Nondeg, eval, Interp.real, hk_m, hk_n, hk_p, ep1, ep1', hm1, hi2, -Real.log_eq_zero]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi33r31Nondeg.integrals.map (·.1)) Φ "x" w) rubi33r31Nondeg.result) =
        fun w => Real.log (env "f" * w ^ j) ^ 2 * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * w) ^ i)) ^ kp * (2 * env "m")⁻¹ + -1 * env "b" * env "e" * env "n" * env "p" * (2 * env "m")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi33r31Nondeg, eval, Interp.real, recEnv, hk_m, hk_n, hk_p, ep1, ep1', hm1, hi2, -Real.log_eq_zero, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hL1 := OSR.IntegrationRec7.hasDerivAt_log_monomial (env "f") t j hp1'
    have hDd : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
    have hL2 := (OSR.IntegrationRec7.hasDerivAt_log_monomial (env "c") (env "d" + env "e" * t) i hp2').comp t hDd
    have hΛ := (hL2.const_mul (env "b")).const_add (env "a")
    have hΛp := HasDerivAt.comp t (hasDerivAt_zpow kp _ (Or.inr (by omega))) hΛ
    refine ((((hL1.pow 2).mul hΛp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    rw [show (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) ^ kp = (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) ^ (kp - 1) * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) by rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]]
    generalize (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) ^ (kp - 1) = Lk
    generalize (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) = Lm
    generalize Real.log (env "f" * t ^ j) = L1
    simp only [div_eq_mul_inv]
    generalize hDe : (env "d" + env "e" * t) = D at hD0 ⊢
    simp only [h_m, h_n, h_p] at *
    try casesm* _ ∧ _
    field_simp
    push_cast
    ring

theorem rubi315r33Nondeg_real : rubi315r33Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi315r33Nondeg.conditions rubi315r33Nondeg.body rubi315r33Nondeg.result rubi315r33Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hi2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have ord : ∀ (x y : ℤ), Interp.real.lt (x : ℝ) (y : ℝ) → x < y := by
    intro x y h
    have h' : Interp.real.lt ((x : ℚ) : ℝ) ((y : ℚ) : ℝ) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (Interp.real_lt_rat _ _).1 h'
  have hA0 := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi315r33Nondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hr0 : env "r" ≠ 0 := by have h := hc (.ne (.var "r") (.int 0)) (by simp [rubi315r33Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  rcases hk_r : intValue? (env "r") with _ | kr
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r33Nondeg, Defined, eval, Interp.real, hm1, hk_r, -Real.log_eq_zero] at h
  have h_r : env "r" = (kr : ℝ) := (intValue?_eq _ _).1 hk_r
  rcases hk_m : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r33Nondeg, Defined, eval, Interp.real, hm1, hk_r, hk_m, -Real.log_eq_zero] at h
  have h_m : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hk_m
  rcases hk_n : intValue? (env "n") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r33Nondeg, Defined, eval, Interp.real, hm1, hk_r, hk_m, hk_n, -Real.log_eq_zero] at h
  have h_n : env "n" = (i : ℝ) := (intValue?_eq _ _).1 hk_n
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi315r33Nondeg, Defined, eval, Interp.real, hm1, hk_r, hk_m, hk_n, hk_p, -Real.log_eq_zero] at h
  have h_p : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have g_p := hc (.gt (.var "p") (.int 0)) (by simp [rubi315r33Nondeg])
  have hkp : 0 < kp := by
    simp only [Cond.Holds, Defined, eval, true_and] at g_p; simp only [h_p] at g_p; exact ord _ _ (by simpa using g_p)
  have ep1 : intValue? (env "p" + 1) = some (kp + 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ej1 : intValue? (env "m" + -1 * 1) = some (j - 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ej1' : intValue? (env "m" + -1) = some (j - 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hp0 : ¬ kp < 0 := by omega
  have hp1 : ¬ kp + 1 < 0 := by omega
  have hkr0 : kr ≠ 0 := by intro h; apply hr0; rw [h_r, h]; simp
  have hEne : ∀ w : ℝ, 0 < env "d" * (env "e" + env "f" * w ^ j) ^ kr → (env "e" + env "f" * w ^ j) ≠ 0 := by
    intro w h h0; rw [h0, zero_zpow kr hkr0, mul_zero] at h; exact lt_irrefl 0 h
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi315r33Nondeg.body →
      0 < env "d" * (env "e" + env "f" * w ^ j) ^ kr ∧ 0 < env "c" * w ^ i ∧ w ≠ 0 ∧ (j < 0 → w ≠ 0) := by
    intro w h
    simp [rubi315r33Nondeg, Defined, eval, Interp.real, hk_m, hk_n, hk_p, hk_r, ep1, ej1, ej1', hm1, hi2, -Real.log_eq_zero, hp0] at h
    first | tauto | (trace_state; sorry)
  refine ⟨fun i' hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi315r33Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3, h4⟩ := hBody w hw
    simp [Defined, eval, Interp.real, hk_m, hk_n, hk_p, hk_r, ep1, ej1, ej1', hm1, hi2, -Real.log_eq_zero, hp1, h2, h3, hEne w h1]
    first | done | exact ⟨fun _ => h3, fun _ => h3⟩ | exact fun _ => h3 | exact fun _ => hEne w h1 | exact ⟨fun _ => h3, fun _ => hEne w h1⟩ | exact ⟨h4, fun _ => hEne w h1⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3, h4⟩ := hBody w hw
    simp [rubi315r33Nondeg, Defined, eval, Interp.real, recEnv, hk_m, hk_n, hk_p, hk_r, ep1, ej1, ej1', hm1, hi2, -Real.log_eq_zero, hp1, h1, h2, h3, hA0]
    first | done | exact ⟨h4, fun _ => h3⟩ | exact h4 | exact fun _ => hEne w h1 | exact ⟨fun _ => hEne w h1, h4⟩ | exact ⟨h4, fun _ => hEne w h1⟩ | exact ⟨⟨h4, fun _ => hEne w h1⟩, fun _ => h3⟩ | (trace_state; sorry)
  · simp only [rubi315r33Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hp1', hp2', ht0, -⟩ := hBody t hF.self_of_nhds
    have hE0 := hEne t hp1'
    have hΦ' : HasDerivAt (Φ "I1") (t ^ (j - 1) * (env "a" + env "b" * Real.log (env "c" * t ^ i)) ^ (kp + 1) * (env "e" + env "f" * t ^ j)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hk_m, hk_n, hk_p, hk_r, ep1, ej1, ej1', hm1, hi2, -Real.log_eq_zero]
    have hEF : eval Interp.real (Function.update env "x" t) rubi315r33Nondeg.body = Real.log (env "d" * (env "e" + env "f" * t ^ j) ^ kr) * (env "a" + env "b" * Real.log (env "c" * t ^ i)) ^ kp * t⁻¹ := by
      simp [rubi315r33Nondeg, eval, Interp.real, hk_m, hk_n, hk_p, hk_r, ep1, ej1, ej1', hm1, hi2, -Real.log_eq_zero]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi315r33Nondeg.integrals.map (·.1)) Φ "x" w) rubi315r33Nondeg.result) =
        fun w => Real.log (env "d" * (env "e" + env "f" * w ^ j) ^ kr) * (env "a" + env "b" * Real.log (env "c" * w ^ i)) ^ (kp + 1) * (env "b" * env "n" * (env "p" + 1))⁻¹ + -1 * env "f" * env "m" * env "r" * (env "b" * env "n" * (env "p" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi315r33Nondeg, eval, Interp.real, recEnv, hk_m, hk_n, hk_p, hk_r, ep1, ej1, ej1', hm1, hi2, -Real.log_eq_zero, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hEd : HasDerivAt (fun w => (env "e" + env "f" * w ^ j)) (env "f" * ((j : ℝ) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t (Or.inl ht0)).const_mul _).const_add _
    have hL1 := (OSR.IntegrationRec7.hasDerivAt_log_monomial (env "d") (env "e" + env "f" * t ^ j) kr hp1').comp t hEd
    have hL2 := ((OSR.IntegrationRec7.hasDerivAt_log_monomial (env "c") t i hp2').const_mul (env "b")).const_add (env "a")
    have hL2p := HasDerivAt.comp t (hasDerivAt_zpow (kp + 1) _ (Or.inr (by omega))) hL2
    refine (((hL1.mul hL2p).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    rw [zpow_sub_one₀ ht0]
    all_goals first
      | (rw [show (env "a" + env "b" * Real.log (env "c" * t ^ i)) ^ (kp + 1) = (env "a" + env "b" * Real.log (env "c" * t ^ i)) ^ kp * (env "a" + env "b" * Real.log (env "c" * t ^ i)) by rw [zpow_succ_of _ _ (Or.inr (by omega))]]
         generalize (env "a" + env "b" * Real.log (env "c" * t ^ i)) ^ kp = Lk
         generalize (env "a" + env "b" * Real.log (env "c" * t ^ i)) = L2
         generalize Real.log (env "d" * (env "e" + env "f" * t ^ j) ^ kr) = L1
         simp only [div_eq_mul_inv]
         generalize hEe : (env "e" + env "f" * t ^ j) = E at hE0 ⊢
         simp only [h_m, h_n, h_p, h_r] at *
         try casesm* _ ∧ _
         field_simp
         push_cast
         ring)
      | (trace_state; sorry)

end Proofs

end OSR.IntegrationRec111
