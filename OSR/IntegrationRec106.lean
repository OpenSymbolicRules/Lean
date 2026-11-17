import OSR.IntegrationRec91
import OSR.IntegrationRec7

/-!
# Integration (RUBI): strengthened variants of logarithmic rules, sampled with their equality conditions solved

RUBI 3.1.4 #10 and #22 and 3.3 #12 are refuted as stated (a coefficient the
result divides by may vanish).  With the non-degeneracy conditions of their
results (and `n ≠ 0` for 3.1.4 #22, which the pole probe required) they are
proved over ℝ, with the real logarithm; the complex domain stays unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec106

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- rubi_3_1_4_r10 with NeQ[Multiply[d, f, Add[q, 1]], 0]; NeQ[Multiply[d, Add[q, 1]], 0] -/
def rubi314r10Nondeg : CRule where
  id := "integration.rubi_3_1_4_r10_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "q", "p"]
  conditions := [.eq (.app2 .add (.app2 .add (.var "m") (.var "q")) (.int 2)) (.int 0), .int (.var "p"), .gt (.var "p") (.int 0), .gt (.int (-1)) (.var "q"),
    .ne (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "q") (.int 1))) (.int 0),
    .ne (.app2 .mul (.var "d") (.app2 .add (.var "q") (.int 1))) (.int 0)]
  priority := 9241
  description := "rubi_3_1_4_r10 with NeQ[Multiply[d, f, Add[q, 1]], 0]; NeQ[Multiply[d, Add[q, 1]], 0]"
  provenance := migrated "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:10" "3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.m#10"

/-- rubi_3_1_4_r22 with NeQ[Multiply[Add[q, 1], Add[Multiply[e, f], Multiply[-1, d, g]]], 0]; NeQ[n, 0] -/
def rubi314r22Nondeg : CRule where
  id := "integration.rubi_3_1_4_r22_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:22"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .mul (.app2 .add (.var "q") (.int 1)) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.var "p")) (.pow (.app2 .mul (.app2 .add (.var "q") (.int 1)) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.var "x") (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "n", "q", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g"))) (.int 0), .eq (.app2 .add (.app2 .add (.var "m") (.var "q")) (.int 2)) (.int 0), .int (.var "p"), .gt (.var "p") (.int 0), .gt (.int (-1)) (.var "q"),
    .ne (.app2 .mul (.app2 .add (.var "q") (.int 1)) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g")))) (.int 0),
    .ne (.var "n") (.int 0)]
  priority := 9242
  description := "rubi_3_1_4_r22 with NeQ[Multiply[Add[q, 1], Add[Multiply[e, f], Multiply[-1, d, g]]], 0]; NeQ[n, 0]"
  provenance := migrated "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:22" "3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.m#22"

/-- rubi_3_3_r12 with NeQ[Multiply[b, e, n, Add[p, 1]], 0]; NeQ[Multiply[b, n, Add[p, 1]], 0] -/
def rubi33r12Nondeg : CRule where
  id := "integration.rubi_3_3_r12_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "q") (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g")))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", .app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.app2 .add (.var "p") (.int 1)))), ("I2", .app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.app2 .add (.var "p") (.int 1))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "n", "p", "q"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g"))) (.int 0), .gt (.int (-1)) (.var "p"), .gt (.var "q") (.int 0),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)]
  priority := 9243
  description := "rubi_3_3_r12 with NeQ[Multiply[b, e, n, Add[p, 1]], 0]; NeQ[Multiply[b, n, Add[p, 1]], 0]"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:12" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#12"


/-! ## Proofs -/

section Proofs

private theorem zpow_succ_of (A : ℝ) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

theorem rubi314r10Nondeg_real : rubi314r10Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi314r10Nondeg.conditions rubi314r10Nondeg.body rubi314r10Nondeg.result rubi314r10Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have ord : ∀ (x y : ℤ), Interp.real.lt (x : ℝ) (y : ℝ) → x < y := by
    intro x y h
    have h' : Interp.real.lt ((x : ℚ) : ℝ) ((y : ℚ) : ℝ) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (Interp.real_lt_rat _ _).1 h'
  have hmq := hc (.eq (.app2 .add (.app2 .add (.var "m") (.var "q")) (.int 2)) (.int 0)) (by simp [rubi314r10Nondeg])
  simp [Cond.Holds, Defined, eval] at hmq
  have hA0 := hc (.ne (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "q") (.int 1))) (.int 0)) (by simp [rubi314r10Nondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hA1 := hc (.ne (.app2 .mul (.var "d") (.app2 .add (.var "q") (.int 1))) (.int 0)) (by simp [rubi314r10Nondeg])
  simp [Cond.Holds, Defined, eval] at hA1
  rcases hk_m : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r10Nondeg, Defined, eval, Interp.real, hm1, hk_m, -Real.log_eq_zero] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk_m
  rcases hk_q : intValue? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r10Nondeg, Defined, eval, Interp.real, hm1, hk_m, hk_q, -Real.log_eq_zero] at h
  have h_q : env "q" = (kq : ℝ) := (intValue?_eq _ _).1 hk_q
  rcases hk_n : intValue? (env "n") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r10Nondeg, Defined, eval, Interp.real, hm1, hk_m, hk_q, hk_n, -Real.log_eq_zero] at h
  have h_n : env "n" = (i : ℝ) := (intValue?_eq _ _).1 hk_n
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r10Nondeg, Defined, eval, Interp.real, hm1, hk_m, hk_q, hk_n, hk_p, -Real.log_eq_zero] at h
  have h_p : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have g_hkp := hc (.gt (.var "p") (.int 0)) (by simp [rubi314r10Nondeg])
  have hkp : 0 < kp := by
    simp only [Cond.Holds, Defined, eval, true_and] at g_hkp; simp only [h_p] at g_hkp
    exact ord _ _ (by push_cast; simpa using g_hkp)
  have g_hkq := hc (.gt (.int (-1)) (.var "q")) (by simp [rubi314r10Nondeg])
  have hkq : kq < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at g_hkq; simp only [h_q] at g_hkq
    exact ord _ _ (by push_cast; simpa using g_hkq)
  have hk : k = -kq - 2 := by
    have : (k : ℝ) = ((-kq - 2 : ℤ) : ℝ) := by push_cast; rw [← h_m, ← h_q]; linear_combination hmq
    exact_mod_cast this
  have eq1 : intValue? (env "q" + 1) = some (kq + 1) := (intValue?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have em1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ep1 : intValue? (env "p" + -1 * 1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep1' : intValue? (env "p" + -1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k + 1 < 0 := by omega
  have hkp0 : ¬ kp < 0 := by omega
  have hkp1 : ¬ kp - 1 < 0 := by omega
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi314r10Nondeg.body →
      (env "d" + env "e" * w) ≠ 0 ∧ (i < 0 → w ≠ 0) ∧ 0 < env "c" * w ^ i := by
    intro w h
    simp [rubi314r10Nondeg, Defined, eval, Interp.real, hk_m, hk_q, hk_p, hk_n, eq1, ep1, ep1', em1, hm1, h2, -Real.log_eq_zero, hk0, hkp0] at h
    first | exact ⟨h.1 (by omega), h.2.1, h.2.2⟩ | exact ⟨h.1.1 (by omega), h.2.1, h.2.2⟩ | exact ⟨h.1.2 (by omega), h.2.1, h.2.2⟩ | (trace_state; sorry)
  refine ⟨fun i' hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi314r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2', h3⟩ := hBody w hw
    simp [Defined, eval, Interp.real, hk_m, hk_q, hk_p, hk_n, eq1, ep1, ep1', em1, hm1, h2, -Real.log_eq_zero, hk0, hkp1, h1]
    first | exact ⟨h2', h3⟩ | done | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2', h3⟩ := hBody w hw
    simp [rubi314r10Nondeg, Defined, eval, Interp.real, recEnv, hk_m, hk_q, hk_p, hk_n, eq1, ep1, ep1', em1, hm1, h2, -Real.log_eq_zero, hk1, hkp0, h1, hA0, hA1]
    first | exact ⟨h2', h3⟩ | done | (trace_state; sorry)
  · simp only [rubi314r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hD0, -, hpos⟩ := hBody t hF.self_of_nhds
    have hΦ' : HasDerivAt (Φ "I1") ((env "f" * t) ^ k * (env "d" + env "e" * t) ^ (kq + 1) * (env "a" + env "b" * Real.log (env "c" * t ^ i)) ^ (kp - 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hk_m, hk_q, hk_p, hk_n, eq1, ep1, ep1', em1, hm1, h2, -Real.log_eq_zero]
    have hEF : eval Interp.real (Function.update env "x" t) rubi314r10Nondeg.body = (env "f" * t) ^ k * (env "d" + env "e" * t) ^ kq * (env "a" + env "b" * Real.log (env "c" * t ^ i)) ^ kp := by
      simp [rubi314r10Nondeg, eval, Interp.real, hk_m, hk_q, hk_p, hk_n, eq1, ep1, ep1', em1, hm1, h2, -Real.log_eq_zero]
    set W1 := (env "d" * env "f" * (env "q" + 1))⁻¹ with hW1_def
    have hW2e : (env "d" * (env "q" + 1))⁻¹ = env "f" * W1 := by
      rw [hW1_def]; casesm* _ ∧ _; field_simp
    have hU : env "d" * env "f" * (env "q" + 1) * W1 = 1 := by
      rw [hW1_def]; exact mul_inv_cancel₀ (by simp only [ne_eq, mul_eq_zero, not_or]; tauto)
    have hfun : (fun w => eval Interp.real (recEnv env (rubi314r10Nondeg.integrals.map (·.1)) Φ "x" w) rubi314r10Nondeg.result) =
        fun w => -1 * (env "f" * w) ^ (k + 1) * (env "d" + env "e" * w) ^ (kq + 1) * (env "a" + env "b" * Real.log (env "c" * w ^ i)) ^ kp * W1 + env "b" * env "n" * env "p" * (env "f" * W1) * Φ "I1" w := by
      funext w
      rw [← hW2e]
      simp [rubi314r10Nondeg, eval, Interp.real, recEnv, hk_m, hk_q, hk_p, hk_n, eq1, ep1, ep1', em1, hm1, h2, -Real.log_eq_zero, hW1_def, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hEp := HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (Or.inr (by omega))) ((hasDerivAt_id' t).const_mul (env "f"))
    have hDd : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
    have hDp := HasDerivAt.comp t (hasDerivAt_zpow (kq + 1) _ (Or.inl hD0)) hDd
    have hL := OSR.IntegrationRec7.hasDerivAt_log_monomial (env "c") t i hpos
    have hZ := OSR.IntegrationRec7.mul_div_of_log_monomial (env "c") t i hpos
    have hΛ := (hL.const_mul (env "b")).const_add (env "a")
    have hΛp := HasDerivAt.comp t (hasDerivAt_zpow kp _ (Or.inr (by omega))) hΛ
    refine (((((hEp.const_mul (-1)).mul hDp).mul hΛp).mul_const W1).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    rw [zpow_succ_of (env "f" * t) k (Or.inr (by omega)), zpow_add_one₀ hD0 kq,
      show (env "a" + env "b" * Real.log (env "c" * t ^ i)) ^ kp = (env "a" + env "b" * Real.log (env "c" * t ^ i)) ^ (kp - 1) * (env "a" + env "b" * Real.log (env "c" * t ^ i)) by rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]]
    generalize (env "f" * t) ^ k = Ek
    generalize (env "d" + env "e" * t) ^ kq = Dq
    generalize (env "a" + env "b" * Real.log (env "c" * t ^ i)) ^ (kp - 1) = Lp
    generalize (env "a" + env "b" * Real.log (env "c" * t ^ i)) = L
    generalize (i : ℝ) / t = Z at hZ ⊢
    clear_value W1
    simp only [h_m, h_q, h_p, h_n] at hU ⊢
    rw [hk]
    push_cast
    linear_combination (-Dq * Ek * Lp * W1 * env "b" * env "d" * env "f" * (kp : ℝ) - Dq * Ek * Lp * W1 * env "b" * env "e" * env "f" * (kp : ℝ) * t) * hZ + (Dq * Ek * L * Lp) * hU

theorem rubi314r22Nondeg_real : rubi314r22Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi314r22Nondeg.conditions rubi314r22Nondeg.body rubi314r22Nondeg.result rubi314r22Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have ord : ∀ (x y : ℤ), Interp.real.lt (x : ℝ) (y : ℝ) → x < y := by
    intro x y h
    have h' : Interp.real.lt ((x : ℚ) : ℝ) ((y : ℚ) : ℝ) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (Interp.real_lt_rat _ _).1 h'
  have hmq := hc (.eq (.app2 .add (.app2 .add (.var "m") (.var "q")) (.int 2)) (.int 0)) (by simp [rubi314r22Nondeg])
  simp [Cond.Holds, Defined, eval] at hmq
  have hA0 := hc (.ne (.app2 .mul (.app2 .add (.var "q") (.int 1)) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g")))) (.int 0)) (by simp [rubi314r22Nondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hn0 : env "n" ≠ 0 := by
    have h := hc (.ne (.var "n") (.int 0)) (by simp [rubi314r22Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  rcases hk_m : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r22Nondeg, Defined, eval, Interp.real, hm1, hk_m, -Real.log_eq_zero] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk_m
  rcases hk_q : intValue? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r22Nondeg, Defined, eval, Interp.real, hm1, hk_m, hk_q, -Real.log_eq_zero] at h
  have h_q : env "q" = (kq : ℝ) := (intValue?_eq _ _).1 hk_q
  rcases hk_n : intValue? (env "n") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r22Nondeg, Defined, eval, Interp.real, hm1, hk_m, hk_q, hk_n, -Real.log_eq_zero] at h
  have h_n : env "n" = (i : ℝ) := (intValue?_eq _ _).1 hk_n
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi314r22Nondeg, Defined, eval, Interp.real, hm1, hk_m, hk_q, hk_n, hk_p, -Real.log_eq_zero] at h
  have h_p : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have g_hkp := hc (.gt (.var "p") (.int 0)) (by simp [rubi314r22Nondeg])
  have hkp : 0 < kp := by
    simp only [Cond.Holds, Defined, eval, true_and] at g_hkp; simp only [h_p] at g_hkp
    exact ord _ _ (by push_cast; simpa using g_hkp)
  have g_hkq := hc (.gt (.int (-1)) (.var "q")) (by simp [rubi314r22Nondeg])
  have hkq : kq < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at g_hkq; simp only [h_q] at g_hkq
    exact ord _ _ (by push_cast; simpa using g_hkq)
  have hk : k = -kq - 2 := by
    have : (k : ℝ) = ((-kq - 2 : ℤ) : ℝ) := by push_cast; rw [← h_m, ← h_q]; linear_combination hmq
    exact_mod_cast this
  have hi0 : i ≠ 0 := by intro h; apply hn0; rw [h_n, h]; simp
  have eq1 : intValue? (env "q" + 1) = some (kq + 1) := (intValue?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have em1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ep1 : intValue? (env "p" + -1 * 1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep1' : intValue? (env "p" + -1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k + 1 < 0 := by omega
  have hkp0 : ¬ kp < 0 := by omega
  have hkp1 : ¬ kp - 1 < 0 := by omega
  have hw0 : ∀ w : ℝ, 0 < env "c" * w ^ i → w ≠ 0 := by
    intro w h h0; rw [h0, zero_zpow i hi0, mul_zero] at h; exact lt_irrefl 0 h
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi314r22Nondeg.body →
      (env "d" + env "e" * w) ≠ 0 ∧ 0 < env "c" * w ^ i := by
    intro w h
    simp [rubi314r22Nondeg, Defined, eval, Interp.real, hk_m, hk_q, hk_p, hk_n, eq1, ep1, ep1', em1, hm1, h2, -Real.log_eq_zero, hk0, hkp0] at h
    first | exact ⟨h.1 (by omega), h.2.2⟩ | exact ⟨h.1.2 (by omega), h.2.2⟩ | exact ⟨h.1.2 (by omega), h.2.2.2⟩ | (trace_state; sorry)
  refine ⟨fun i' hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi314r22Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h3⟩ := hBody w hw
    simp [Defined, eval, Interp.real, hk_m, hk_q, hk_p, hk_n, eq1, ep1, ep1', em1, hm1, h2, -Real.log_eq_zero, hk1, hkp1, h1, hw0 w h3]
    first | exact h3 | done | exact ⟨fun _ => hw0 w h3, h3⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h3⟩ := hBody w hw
    simp [rubi314r22Nondeg, Defined, eval, Interp.real, recEnv, hk_m, hk_q, hk_p, hk_n, eq1, ep1, ep1', em1, hm1, h2, -Real.log_eq_zero, hk1, hkp0, h1, hA0]
    first | exact h3 | done | exact ⟨fun _ => hw0 w h3, h3⟩ | (trace_state; sorry)
  · simp only [rubi314r22Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hD0, hpos⟩ := hBody t hF.self_of_nhds
    have ht0 := hw0 t hpos
    have hΦ' : HasDerivAt (Φ "I1") ((env "f" + env "g" * t) ^ (k + 1) * (env "d" + env "e" * t) ^ (kq + 1) * (env "a" + env "b" * Real.log (env "c" * t ^ i)) ^ (kp - 1) * t⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hk_m, hk_q, hk_p, hk_n, eq1, ep1, ep1', em1, hm1, h2, -Real.log_eq_zero]
    have hEF : eval Interp.real (Function.update env "x" t) rubi314r22Nondeg.body = (env "f" + env "g" * t) ^ k * (env "d" + env "e" * t) ^ kq * (env "a" + env "b" * Real.log (env "c" * t ^ i)) ^ kp := by
      simp [rubi314r22Nondeg, eval, Interp.real, hk_m, hk_q, hk_p, hk_n, eq1, ep1, ep1', em1, hm1, h2, -Real.log_eq_zero]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi314r22Nondeg.integrals.map (·.1)) Φ "x" w) rubi314r22Nondeg.result) =
        fun w => (env "f" + env "g" * w) ^ (k + 1) * (env "d" + env "e" * w) ^ (kq + 1) * (env "a" + env "b" * Real.log (env "c" * w ^ i)) ^ kp * ((env "q" + 1) * (env "e" * env "f" + -1 * env "d" * env "g"))⁻¹ +
          -1 * env "b" * env "n" * env "p" * ((env "q" + 1) * (env "e" * env "f" + -1 * env "d" * env "g"))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi314r22Nondeg, eval, Interp.real, recEnv, hk_m, hk_q, hk_p, hk_n, eq1, ep1, ep1', em1, hm1, h2, -Real.log_eq_zero, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hFd : HasDerivAt (fun w => (env "f" + env "g" * w)) (env "g") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "g")).const_add (env "f")
    have hFp := HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (Or.inr (by omega))) hFd
    have hDd : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
    have hDp := HasDerivAt.comp t (hasDerivAt_zpow (kq + 1) _ (Or.inl hD0)) hDd
    have hL := OSR.IntegrationRec7.hasDerivAt_log_monomial (env "c") t i hpos
    have hΛ := (hL.const_mul (env "b")).const_add (env "a")
    have hΛp := HasDerivAt.comp t (hasDerivAt_zpow kp _ (Or.inr (by omega))) hΛ
    refine ((((hFp.mul hDp).mul hΛp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    rw [zpow_succ_of (env "f" + env "g" * t) k (Or.inr (by omega)), zpow_add_one₀ hD0 kq,
      show (env "a" + env "b" * Real.log (env "c" * t ^ i)) ^ kp = (env "a" + env "b" * Real.log (env "c" * t ^ i)) ^ (kp - 1) * (env "a" + env "b" * Real.log (env "c" * t ^ i)) by rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel],
      div_eq_mul_inv]
    generalize (env "f" + env "g" * t) ^ k = Fk
    generalize (env "a" + env "b" * Real.log (env "c" * t ^ i)) ^ (kp - 1) = Lp
    generalize (env "a" + env "b" * Real.log (env "c" * t ^ i)) = L
    generalize hDe : (env "d" + env "e" * t) = D at hD0 ⊢
    simp only [h_m, h_q, h_p, h_n] at *
    rw [hk]
    have hK0 := hc (.ne (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g"))) (.int 0)) (by simp [rubi314r22Nondeg])
    simp [Cond.Holds, Defined, eval] at hK0
    have hK1 : env "e" * env "f" + -1 * env "d" * env "g" ≠ 0 := by intro h; apply hK0; linear_combination h
    have hq1 : (kq : ℝ) + 1 ≠ 0 := by
      intro h; have : kq = -1 := by exact_mod_cast (show ((kq : ℤ) : ℝ) = ((-1 : ℤ) : ℝ) by push_cast; linear_combination h)
      omega
    generalize hKe : env "e" * env "f" + -1 * env "d" * env "g" = K at hK1 ⊢
    casesm* _ ∧ _
    field_simp
    subst hDe hKe
    push_cast
    ring

theorem rubi33r12Nondeg_real : rubi33r12Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi33r12Nondeg.conditions rubi33r12Nondeg.body rubi33r12Nondeg.result rubi33r12Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have ord : ∀ (x y : ℤ), Interp.real.lt (x : ℝ) (y : ℝ) → x < y := by
    intro x y h
    have h' : Interp.real.lt ((x : ℚ) : ℝ) ((y : ℚ) : ℝ) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (Interp.real_lt_rat _ _).1 h'
  have hA0 := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi33r12Nondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hA1 := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi33r12Nondeg])
  simp [Cond.Holds, Defined, eval] at hA1
  rcases hk_q : intValue? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi33r12Nondeg, Defined, eval, Interp.real, hm1, hk_q, -Real.log_eq_zero] at h
  have h_q : env "q" = (kq : ℝ) := (intValue?_eq _ _).1 hk_q
  rcases hk_n : intValue? (env "n") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi33r12Nondeg, Defined, eval, Interp.real, hm1, hk_q, hk_n, -Real.log_eq_zero] at h
  have h_n : env "n" = (i : ℝ) := (intValue?_eq _ _).1 hk_n
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi33r12Nondeg, Defined, eval, Interp.real, hm1, hk_q, hk_n, hk_p, -Real.log_eq_zero] at h
  have h_p : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have g_hkq := hc (.gt (.var "q") (.int 0)) (by simp [rubi33r12Nondeg])
  have hkq : 0 < kq := by
    simp only [Cond.Holds, Defined, eval, true_and] at g_hkq; simp only [h_q] at g_hkq
    exact ord _ _ (by push_cast; simpa using g_hkq)
  have g_hkp := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi33r12Nondeg])
  have hkp : kp < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at g_hkp; simp only [h_p] at g_hkp
    exact ord _ _ (by push_cast; simpa using g_hkp)
  have hi0 : i ≠ 0 := by intro h; simp [h_n, h] at hA0
  have eq1 : intValue? (env "q" + -1 * 1) = some (kq - 1) := (intValue?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have eq1' : intValue? (env "q" + -1) = some (kq - 1) := (intValue?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have ep1 : intValue? (env "p" + 1) = some (kp + 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hq0 : ¬ kq < 0 := by omega
  have hq1 : ¬ kq - 1 < 0 := by omega
  have hD : ∀ w : ℝ, 0 < env "c" * (env "d" + env "e" * w) ^ i → env "d" + env "e" * w ≠ 0 := by
    intro w h h0; rw [h0, zero_zpow i hi0, mul_zero] at h; exact lt_irrefl 0 h
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi33r12Nondeg.body →
      0 < env "c" * (env "d" + env "e" * w) ^ i ∧ (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * w) ^ i)) ≠ 0 := by
    intro w h
    simp [rubi33r12Nondeg, Defined, eval, Interp.real, hk_q, hk_p, hk_n, eq1, eq1', ep1, hm1, h2, -Real.log_eq_zero, hq0] at h
    first | exact ⟨h.1.2, h.2 (by omega)⟩ | exact ⟨h.1.2.2, h.2 (by omega)⟩ | exact ⟨h.1.2, h.2.2 (by omega)⟩ | (trace_state; sorry)
  refine ⟨fun i' hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi33r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · obtain ⟨h1, h2'⟩ := hBody w hw
      simp [Defined, eval, Interp.real, hk_q, hk_p, hk_n, eq1, eq1', ep1, hm1, h2, -Real.log_eq_zero, hq0, hq1, h1, h2', hD w h1]
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2'⟩ := hBody w hw
    simp [rubi33r12Nondeg, Defined, eval, Interp.real, recEnv, hk_q, hk_p, hk_n, eq1, eq1', ep1, hm1, h2, -Real.log_eq_zero, hq0, h1, h2', hD w h1, hA0, hA1]
  · simp only [rubi33r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    obtain ⟨hpos, hM0⟩ := hBody t hF.self_of_nhds
    have hD0 := hD t hpos
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" + env "g" * t) ^ (kq - 1) * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) ^ (kp + 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hk_q, hk_p, hk_n, eq1, eq1', ep1, hm1, h2, -Real.log_eq_zero]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" + env "g" * t) ^ kq * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) ^ (kp + 1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hk_q, hk_p, hk_n, eq1, eq1', ep1, hm1, h2, -Real.log_eq_zero]
    have hEF : eval Interp.real (Function.update env "x" t) rubi33r12Nondeg.body = (env "f" + env "g" * t) ^ kq * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) ^ kp := by
      simp [rubi33r12Nondeg, eval, Interp.real, hk_q, hk_p, hk_n, eq1, eq1', ep1, hm1, h2, -Real.log_eq_zero]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi33r12Nondeg.integrals.map (·.1)) Φ "x" w) rubi33r12Nondeg.result) =
        fun w => (env "d" + env "e" * w) * (env "f" + env "g" * w) ^ kq * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * w) ^ i)) ^ (kp + 1) * (env "b" * env "e" * env "n" * (env "p" + 1))⁻¹ +
          env "q" * (env "e" * env "f" + -1 * env "d" * env "g") * (env "b" * env "e" * env "n" * (env "p" + 1))⁻¹ * Φ "I1" w +
          -1 * (env "q" + 1) * (env "b" * env "n" * (env "p" + 1))⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi33r12Nondeg, eval, Interp.real, recEnv, hk_q, hk_p, hk_n, eq1, eq1', ep1, hm1, h2, -Real.log_eq_zero, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hDd : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
    have hFd : HasDerivAt (fun w => (env "f" + env "g" * w)) (env "g") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "g")).const_add (env "f")
    have hFp := HasDerivAt.comp t (hasDerivAt_zpow kq _ (Or.inr (by omega))) hFd
    have hL := (OSR.IntegrationRec7.hasDerivAt_log_monomial (env "c") (env "d" + env "e" * t) i hpos).comp t hDd
    have hΛ := (hL.const_mul (env "b")).const_add (env "a")
    have hΛp := HasDerivAt.comp t (hasDerivAt_zpow (kp + 1) _ (Or.inl hM0)) hΛ
    refine (((((hDd.mul hFp).mul hΛp).mul_const _).add (hΦ1'.const_mul _)).add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    rw [zpow_add_one₀ hM0, show (env "f" + env "g" * t) ^ kq = (env "f" + env "g" * t) ^ (kq - 1) * (env "f" + env "g" * t) by rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel],
      div_eq_mul_inv]
    generalize (env "f" + env "g" * t) ^ (kq - 1) = Fk
    generalize (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) ^ kp = Mp
    generalize (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) = M
    generalize hDe : (env "d" + env "e" * t) = D at hD0 ⊢
    simp only [h_q, h_p, h_n] at *
    casesm* _ ∧ _
    field_simp
    subst hDe
    push_cast
    ring

end Proofs

end OSR.IntegrationRec106
