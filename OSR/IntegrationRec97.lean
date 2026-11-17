import OSR.IntegrationRec91
import OSR.IntegrationRec7

/-!
# Integration (RUBI): strengthened variants refuted by the pole probe, corrected

RUBI 3.3 #7, 3.2.1 #13 and 3.5 #23 are refuted as stated, and their first
strengthened variants were refuted by the pole probe at `n = 0`, where the
integrand no longer depends on the logarithm's argument and is defined at the
pole of a residual integrand.  With `n ≠ 0` as well they are proved over ℝ,
with the real logarithm; the complex domain stays unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec97

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- ∫ (f + g x)^q (a + b log(c (d + e x)^n)), when g (q + 1) ≠ 0 and n ≠ 0 -/
def linPowLogLinNondeg : CRule where
  id := "integration.linear_power_log_linear_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "q")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "q") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "n")) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "n", "q"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g"))) (.int 0), .ne (.var "q") (.int (-1)),
    .ne (.app2 .mul (.var "g") (.app2 .add (.var "q") (.int 1))) (.int 0),
    .ne (.var "n") (.int 0)]
  priority := 9151
  description := "∫ (f + g x)^q (a + b log(c (d + e x)^n)), when g (q + 1) ≠ 0 and n ≠ 0"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:7" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#7"

/-- ∫ (f + g x)^m (A + B log(e ((a + b x)/(c + d x))^n)), when g (m + 1) ≠ 0 and n ≠ 0 -/
def powLogRatioNondeg : CRule where
  id := "integration.power_log_ratio_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n"))))))) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.var "n")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "A", "B", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0), .ne (.var "m") (.int (-1)), .ne (.var "m") (.int (-2)),
    .ne (.app2 .mul (.var "g") (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.var "n") (.int 0)]
  priority := 9152
  description := "∫ (f + g x)^m (A + B log(e ((a + b x)/(c + d x))^n)), when g (m + 1) ≠ 0 and n ≠ 0"
  provenance := migrated "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:13" "3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.m#13"

/-- rubi_3_5_r23 with NeQ[a, 0]; NeQ[n, 0] -/
def rubi35r23Nondeg : CRule where
  id := "integration.rubi_3_5_r23_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.5 Miscellaneous logarithms:23"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.pow (.pow (.app2 .add (.app2 .mul (.var "a") (.var "x")) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .mul (.var "a") (.app2 .add (.app2 .mul (.var "a") (.var "x")) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q"))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "n"))) (.pow (.var "a") (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.int 1) (.pow (.app2 .mul (.var "x") (.app2 .add (.app2 .mul (.var "a") (.var "x")) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q"))))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "n", "q"]
  conditions := [.eq (.app2 .add (.var "d") (.app2 .mul (.app2 .mul (.var "e") (.var "n")) (.var "q"))) (.int 0),
    .ne (.var "a") (.int 0),
    .ne (.var "n") (.int 0)]
  priority := 9153
  description := "rubi_3_5_r23 with NeQ[a, 0]; NeQ[n, 0]"
  provenance := migrated "rubi:3 Logarithms/3.5 Miscellaneous logarithms:23" "3 Logarithms/3.5 Miscellaneous logarithms.m#23"


/-! ## Proofs -/

section Proofs

private theorem zpow_succ_of (A : ℝ) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

theorem linPowLogLinNondeg_real : linPowLogLinNondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" linPowLogLinNondeg.conditions linPowLogLinNondeg.body linPowLogLinNondeg.result linPowLogLinNondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hN0 := hc (.ne (.var "q") (.int (-1))) (by simp [linPowLogLinNondeg])
  simp [Cond.Holds, Defined, eval, Interp.real, h2] at hN0
  have hN1 := hc (.ne (.app2 .mul (.var "g") (.app2 .add (.var "q") (.int 1))) (.int 0)) (by simp [linPowLogLinNondeg])
  simp [Cond.Holds, Defined, eval, Interp.real, h2] at hN1
  have hN2 := hc (.ne (.var "n") (.int 0)) (by simp [linPowLogLinNondeg])
  simp [Cond.Holds, Defined, eval, Interp.real, h2] at hN2
  rcases hk_q : intValue? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [linPowLogLinNondeg, Defined, eval, Interp.real, hm1, hk_q] at h
  have h_q : env "q" = (k : ℝ) := (intValue?_eq _ _).1 hk_q
  rcases hk_n : intValue? (env "n") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [linPowLogLinNondeg, Defined, eval, Interp.real, hm1, hk_q, hk_n] at h
  have h_n : env "n" = (i : ℝ) := (intValue?_eq _ _).1 hk_n
  have e1 : intValue? (env "q" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have hi0 : i ≠ 0 := by intro h; apply hN2; rw [h_n, h]; simp
  have hBne : ∀ w, 0 < env "c" * (env "d" + env "e" * w) ^ i → (env "d" + env "e" * w) ≠ 0 := by
    intro w h h0
    rw [h0, zero_zpow i hi0, mul_zero] at h
    exact lt_irrefl 0 h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) linPowLogLinNondeg.body →
      (k < 0 → ¬(env "f" + env "g" * w) = 0) ∧ 0 < env "c" * (env "d" + env "e" * w) ^ i := by
    intro w h
    simp [linPowLogLinNondeg, Defined, eval, Interp.real, hk_q, hk_n] at h
    first | exact ⟨h.1, h.2.2⟩ | exact ⟨h.1, h.2⟩ | tauto
  refine ⟨fun i' hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [linPowLogLinNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2'⟩ := hD w hw
    simp [Defined, eval, Interp.real, hk_q, e1, hm1]
    exact ⟨fun h => h1 (by omega), hBne w h2'⟩
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2'⟩ := hD w hw
    simp [linPowLogLinNondeg, Defined, eval, Interp.real, recEnv, hk_n, e1, hm1, hN1]
    exact ⟨fun h => h1 (by omega), fun _ => hBne w h2', h2'⟩
  · simp only [linPowLogLinNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hF0, hpos⟩ := hD t hF.self_of_nhds
    have hD0 := hBne t hpos
    have hFk : (env "f" + env "g" * t) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (hF0 h)
      · exact Or.inr (by omega)
    have hFk1 : (env "f" + env "g" * t) ≠ 0 ∨ 0 ≤ k + 1 := by
      rcases hFk with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hfun : (fun w => eval Interp.real (recEnv env (linPowLogLinNondeg.integrals.map (·.1)) Φ "x" w) linPowLogLinNondeg.result) =
        fun w => (env "f" + env "g" * w) ^ (k + 1) * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * w) ^ i)) * (env "g" * (env "q" + 1))⁻¹ +
          -1 * env "b" * env "e" * env "n" * (env "g" * (env "q" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [linPowLogLinNondeg, eval, Interp.real, recEnv, hk_n, e1, hm1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    have hFd : HasDerivAt (fun w => (env "f" + env "g" * w)) (env "g") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "g")).const_add (env "f")
    have hDd : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
    have hFp := HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hFk1) hFd
    have hL := (OSR.IntegrationRec7.hasDerivAt_log_monomial (env "c") (env "d" + env "e" * t) i hpos).comp t hDd
    have hΛ := (hL.const_mul (env "b")).const_add (env "a")
    refine (((hFp.mul hΛ).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    simp [linPowLogLinNondeg, eval, Interp.real, hk_q, hk_n, e1, hm1]
    rw [zpow_succ_of _ _ hFk]
    simp only [h_q, h_n] at *
    try casesm* _ ∧ _
    first | (field_simp; ring) | (trace_state; sorry)

theorem powLogRatioNondeg_real : powLogRatioNondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" powLogRatioNondeg.conditions powLogRatioNondeg.body powLogRatioNondeg.result powLogRatioNondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hN0 := hc (.ne (.app2 .mul (.var "g") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [powLogRatioNondeg])
  simp [Cond.Holds, Defined, eval, Interp.real, h2] at hN0
  have hN1 := hc (.ne (.var "n") (.int 0)) (by simp [powLogRatioNondeg])
  simp [Cond.Holds, Defined, eval, Interp.real, h2] at hN1
  rcases hk_m : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [powLogRatioNondeg, Defined, eval, Interp.real, hm1, hk_m] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk_m
  rcases hk_n : intValue? (env "n") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [powLogRatioNondeg, Defined, eval, Interp.real, hm1, hk_m, hk_n] at h
  have h_n : env "n" = (i : ℝ) := (intValue?_eq _ _).1 hk_n
  have e1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hi0 : i ≠ 0 := by intro h; apply hN1; rw [h_n, h]; simp
  have hBne : ∀ w, 0 < env "e" * ((env "a" + env "b" * w) * (env "c" + env "d" * w)⁻¹) ^ i → (env "a" + env "b" * w) ≠ 0 := by
    intro w h h0
    rw [h0, zero_mul, zero_zpow i hi0, mul_zero] at h
    exact lt_irrefl 0 h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) powLogRatioNondeg.body →
      (k < 0 → ¬(env "f" + env "g" * w) = 0) ∧ ¬(env "c" + env "d" * w) = 0 ∧ 0 < env "e" * ((env "a" + env "b" * w) * (env "c" + env "d" * w)⁻¹) ^ i := by
    intro w h
    simp [powLogRatioNondeg, Defined, eval, Interp.real, hk_m, hk_n, hm1] at h
    first | exact ⟨h.1, h.2.1.1, h.2.2⟩ | exact ⟨h.1, h.2.1, h.2.2⟩ | tauto
  refine ⟨fun i' hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [powLogRatioNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2', h3⟩ := hD w hw
    simp [Defined, eval, Interp.real, hk_m, e1, hm1]
    first | exact ⟨fun h => h1 (by omega), hBne w h3, h2'⟩ | exact ⟨fun h => h1 (by omega), mul_ne_zero (hBne w h3) h2'⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2', h3⟩ := hD w hw
    simp [powLogRatioNondeg, Defined, eval, Interp.real, recEnv, hk_n, e1, hm1, hN0]
    exact ⟨fun h => h1 (by omega), ⟨h2', fun _ => ⟨hBne w h3, h2'⟩⟩, h3⟩
  · simp only [powLogRatioNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hF0, hC0, hpos⟩ := hD t hF.self_of_nhds
    have hA0 := hBne t hpos
    have hFk : (env "f" + env "g" * t) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (hF0 h)
      · exact Or.inr (by omega)
    have hFk1 : (env "f" + env "g" * t) ≠ 0 ∨ 0 ≤ k + 1 := by
      rcases hFk with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hfun : (fun w => eval Interp.real (recEnv env (powLogRatioNondeg.integrals.map (·.1)) Φ "x" w) powLogRatioNondeg.result) =
        fun w => (env "f" + env "g" * w) ^ (k + 1) * (env "A" + env "B" * Real.log (env "e" * ((env "a" + env "b" * w) * (env "c" + env "d" * w)⁻¹) ^ i)) * (env "g" * (env "m" + 1))⁻¹ +
          -1 * env "B" * env "n" * (env "b" * env "c" + -1 * env "a" * env "d") * (env "g" * (env "m" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [powLogRatioNondeg, eval, Interp.real, recEnv, hk_n, e1, hm1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    have hFd : HasDerivAt (fun w => (env "f" + env "g" * w)) (env "g") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "g")).const_add (env "f")
    have hAd : HasDerivAt (fun w => (env "a" + env "b" * w)) (env "b") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")
    have hCd : HasDerivAt (fun w => (env "c" + env "d" * w)) (env "d") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c")
    have hQ := hAd.mul (hCd.inv hC0)
    have hFp := HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hFk1) hFd
    have hL := (OSR.IntegrationRec7.hasDerivAt_log_monomial (env "e") ((env "a" + env "b" * t) * (env "c" + env "d" * t)⁻¹) i hpos).comp t hQ
    have hΛ := (hL.const_mul (env "B")).const_add (env "A")
    refine (((hFp.mul hΛ).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    simp [powLogRatioNondeg, eval, Interp.real, hk_m, hk_n, e1, hm1]
    rw [zpow_succ_of _ _ hFk]
    simp only [h_m, h_n] at *
    try casesm* _ ∧ _
    first | (field_simp; ring) | (trace_state; sorry)

theorem rubi35r23Nondeg_real : rubi35r23Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi35r23Nondeg.conditions rubi35r23Nondeg.body rubi35r23Nondeg.result rubi35r23Nondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have heq := hc (.eq (.app2 .add (.var "d") (.app2 .mul (.app2 .mul (.var "e") (.var "n")) (.var "q"))) (.int 0)) (by simp [rubi35r23Nondeg])
  simp [Cond.Holds, Defined, eval] at heq
  have hN0 := hc (.ne (.var "a") (.int 0)) (by simp [rubi35r23Nondeg])
  simp [Cond.Holds, Defined, eval, Interp.real, h2] at hN0
  have hN1 := hc (.ne (.var "n") (.int 0)) (by simp [rubi35r23Nondeg])
  simp [Cond.Holds, Defined, eval, Interp.real, h2] at hN1
  rcases hk_n : intValue? (env "n") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi35r23Nondeg, Defined, eval, Interp.real, hm1, hk_n] at h
  have h_n : env "n" = (i : ℝ) := (intValue?_eq _ _).1 hk_n
  rcases hk_q : intValue? (env "q") with _ | s
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi35r23Nondeg, Defined, eval, Interp.real, hm1, hk_n, hk_q] at h
  have h_q : env "q" = (s : ℝ) := (intValue?_eq _ _).1 hk_q
  have hi0 : i ≠ 0 := by intro h; apply hN1; rw [h_n, h]; simp
  have hw0 : ∀ w : ℝ, 0 < env "c" * w ^ i → w ≠ 0 := by
    intro w h h0
    rw [h0, zero_zpow i hi0, mul_zero] at h
    exact lt_irrefl 0 h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi35r23Nondeg.body →
      0 < env "c" * w ^ i ∧ (s < 0 → ¬Real.log (env "c" * w ^ i) = 0) ∧ ¬(env "a" * w + env "b" * Real.log (env "c" * w ^ i) ^ s) = 0 := by
    intro w h
    simp [rubi35r23Nondeg, Defined, eval, Interp.real, hk_n, hk_q, hm1, h2, -Real.log_eq_zero] at h
    first | exact ⟨h.1.2, h.2.1.2, h.2.2⟩ | (trace_state; sorry)
  refine ⟨fun i' hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi35r23Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2', h3⟩ := hD w hw
    simp [Defined, eval, Interp.real, hk_n, hk_q, hm1, -Real.log_eq_zero]
    first | exact ⟨⟨⟨fun _ => hw0 w h1, h1⟩, h2'⟩, hw0 w h1, h3⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2', h3⟩ := hD w hw
    simp [rubi35r23Nondeg, Defined, eval, Interp.real, recEnv, hk_n, hk_q, hm1, hN0, -Real.log_eq_zero]
    first | exact ⟨⟨fun _ => hw0 w h1, h1⟩, ⟨⟨fun _ => hw0 w h1, h1⟩, h2'⟩, h3⟩ | (trace_state; sorry)
  · simp only [rubi35r23Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hpos, hL0', hU0⟩ := hD t hF.self_of_nhds
    have ht0 := hw0 t hpos
    have hL0 : Real.log (env "c" * t ^ i) ≠ 0 ∨ 0 ≤ s := by
      by_cases h : s < 0
      · exact Or.inl (hL0' h)
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") (1 * (t * (env "a" * t + env "b" * Real.log (env "c" * t ^ i) ^ s))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hk_n, hk_q, hm1]
    have hEF : eval Interp.real (Function.update env "x" t) rubi35r23Nondeg.body = (env "d" + env "e" * Real.log (env "c" * t ^ i)) * ((env "a" * t + env "b" * Real.log (env "c" * t ^ i) ^ s) ^ 2)⁻¹ := by
      simp [rubi35r23Nondeg, eval, Interp.real, hk_n, hk_q, hm1, h2]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi35r23Nondeg.integrals.map (·.1)) Φ "x" w) rubi35r23Nondeg.result) =
        fun w => -1 * env "e" * Real.log (env "c" * w ^ i) * (env "a" * (env "a" * w + env "b" * Real.log (env "c" * w ^ i) ^ s))⁻¹ + (env "d" + env "e" * env "n") * (env "a")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi35r23Nondeg, eval, Interp.real, recEnv, hk_n, hk_q, hm1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hL := OSR.IntegrationRec7.hasDerivAt_log_monomial (env "c") t i hpos
    have hLq := HasDerivAt.comp t (hasDerivAt_zpow s _ hL0) hL
    have hU : HasDerivAt (fun w => (env "a" * w + env "b" * Real.log (env "c" * w ^ i) ^ s)) (env "a" * 1 + env "b" * ((s : ℝ) * Real.log (env "c" * t ^ i) ^ (s - 1) * ((i : ℝ) / t))) t :=
      ((hasDerivAt_id' t).const_mul (env "a")).add (hLq.const_mul (env "b"))
    have hAU0 : env "a" * (env "a" * t + env "b" * Real.log (env "c" * t ^ i) ^ s) ≠ 0 := mul_ne_zero hN0 hU0
    have hInv := (hU.const_mul (env "a")).inv hAU0
    have hT1 := hL.const_mul (-1 * env "e")
    refine ((hT1.mul hInv).add (hΦ'.const_mul _)).congr_deriv ?_
    have k1 : (s : ℝ) * Real.log (env "c" * t ^ i) ^ (s - 1) * Real.log (env "c" * t ^ i) = (s : ℝ) * Real.log (env "c" * t ^ i) ^ s := by
      rcases em (s = 0) with h0 | h0
      · subst h0; simp
      · have h' : Real.log (env "c" * t ^ i) ≠ 0 ∨ 0 ≤ s - 1 := by
          by_cases h : s < 0
          · exact Or.inl (hL0' h)
          · exact Or.inr (by omega)
        rw [show Real.log (env "c" * t ^ i) ^ s = Real.log (env "c" * t ^ i) ^ (s - 1) * Real.log (env "c" * t ^ i) by rw [← zpow_succ_of _ _ h', sub_add_cancel]]
        ring
    have hUU : (env "a" * t + env "b" * Real.log (env "c" * t ^ i) ^ s) * (env "a" * t + env "b" * Real.log (env "c" * t ^ i) ^ s)⁻¹ = 1 := mul_inv_cancel₀ hU0
    have haa : env "a" * (env "a")⁻¹ = 1 := mul_inv_cancel₀ hN0
    have htt : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0
    have r2 : ((env "a" * (env "a" * t + env "b" * Real.log (env "c" * t ^ i) ^ s)) ^ 2)⁻¹ = (env "a")⁻¹ ^ 2 * (env "a" * t + env "b" * Real.log (env "c" * t ^ i) ^ s)⁻¹ ^ 2 := by rw [mul_pow, mul_inv, inv_pow, inv_pow]
    have r1 : (env "a" * (env "a" * t + env "b" * Real.log (env "c" * t ^ i) ^ s))⁻¹ = (env "a")⁻¹ * (env "a" * t + env "b" * Real.log (env "c" * t ^ i) ^ s)⁻¹ := mul_inv _ _
    have r3 : (t * (env "a" * t + env "b" * Real.log (env "c" * t ^ i) ^ s))⁻¹ = t⁻¹ * (env "a" * t + env "b" * Real.log (env "c" * t ^ i) ^ s)⁻¹ := mul_inv _ _
    have r4 : ((env "a" * t + env "b" * Real.log (env "c" * t ^ i) ^ s) ^ 2)⁻¹ = (env "a" * t + env "b" * Real.log (env "c" * t ^ i) ^ s)⁻¹ ^ 2 := (inv_pow _ _).symm
    simp only [div_eq_mul_inv, Pi.inv_apply]
    rw [r2, r1, r3, r4]
    generalize (env "a" * t + env "b" * Real.log (env "c" * t ^ i) ^ s)⁻¹ = ui at hUU ⊢
    generalize (env "a")⁻¹ = ai at haa ⊢
    generalize t⁻¹ = ti at htt ⊢
    generalize Real.log (env "c" * t ^ i) ^ (s - 1) = M at k1 ⊢
    generalize Real.log (env "c" * t ^ i) ^ s = Lq at k1 hUU ⊢
    generalize Real.log (env "c" * t ^ i) = Lg at k1 ⊢
    simp only [h_n, h_q] at heq ⊢
    linear_combination (env "a" * ai ^ 2 * env "b" * env "e" * (i : ℝ) * ti * ui ^ 2) * k1 + (ui * (ai * ti - ui)) * heq +
      (env "e" * (i : ℝ) * (s : ℝ) * ui * ai * ti) * hUU +
      (env "e" * ui ^ 2 * (Lg * env "a" * ai + Lg + Lq * ai * env "b" * (i : ℝ) * (s : ℝ) * ti) - env "e" * (i : ℝ) * (s : ℝ) * ui ^ 2 * t * ti) * haa +
      (-env "e" * (i : ℝ) * (s : ℝ) * ui ^ 2) * htt

end Proofs

end OSR.IntegrationRec97
