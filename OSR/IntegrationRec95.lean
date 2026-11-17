import OSR.IntegrationRec91
import OSR.IntegrationRec7

/-!
# Integration (RUBI): strengthened variants of refuted named rules, fourth batch

The named rules 3.1.2 #1 and #4 and 4.7.8 #11, #12, #45 and #46 are refuted
as stated (a coefficient the result divides by may vanish).  These
strengthened variants append the non-degeneracy condition and are proved over
ℝ, with the real logarithm; the complex domain stays unproved, and the
refutations are kept.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec95

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- ∫ (a + b log(c x^n))/x, when 2 b n ≠ 0 -/
def logLinearOverXNondeg : CRule where
  id := "integration.log_linear_over_x_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:1"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.int 2)) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "n")) (.int (-1))))
  independent := ["a", "b", "c", "n"]
  conditions := [.ne (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "n")) (.int 0)]
  priority := 9131
  description := "∫ (a + b log(c x^n))/x, when 2 b n ≠ 0"
  provenance := migrated "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:1" "3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p.m#1"

/-- ∫ (d x)^m (a + b log(c x^n)), when d (m + 1) ≠ 0 -/
def powerLogLinearNondeg : CRule where
  id := "integration.power_log_linear_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:4"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.var "d") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2))) (.int (-1)))))
  independent := ["a", "b", "c", "d", "m", "n"]
  conditions := [.ne (.var "m") (.int (-1)),
    .ne (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.app2 .mul (.var "d") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2))) (.int 0)]
  priority := 9132
  description := "∫ (d x)^m (a + b log(c x^n)), when d (m + 1) ≠ 0"
  provenance := migrated "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:4" "3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p.m#4"

/-- ∫ (e x)^m sin(d (a + b log(c x^n))), when b² d² e n² + e (m + 1)² ≠ 0 -/
def powSinLogNondeg : CRule where
  id := "integration.power_sin_log_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:11"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .sin (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.app1 .sin (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "n")) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.app1 .cos (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1)))))
  independent := ["a", "b", "c", "d", "e", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int 0)]
  priority := 9133
  description := "∫ (e x)^m sin(d (a + b log(c x^n))), when b² d² e n² + e (m + 1)² ≠ 0"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:11" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#11"

/-- ∫ (e x)^m cos(d (a + b log(c x^n))), when b² d² e n² + e (m + 1)² ≠ 0 -/
def powCosLogNondeg : CRule where
  id := "integration.power_cos_log_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:12"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .cos (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.app1 .cos (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "n")) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.app1 .sin (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1)))))
  independent := ["a", "b", "c", "d", "e", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int 0)]
  priority := 9134
  description := "∫ (e x)^m cos(d (a + b log(c x^n))), when b² d² e n² + e (m + 1)² ≠ 0"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:12" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#12"

/-- ∫ sin(a x log(b x)) log(b x), when a ≠ 0 -/
def sinXLogNondeg : CRule where
  id := "integration.sin_x_log_times_log_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:45"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .sin (.app2 .mul (.app2 .mul (.var "a") (.var "x")) (.app1 .ln (.app2 .mul (.var "b") (.var "x"))))) (.app1 .ln (.app2 .mul (.var "b") (.var "x"))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .cos (.app2 .mul (.app2 .mul (.var "a") (.var "x")) (.app1 .ln (.app2 .mul (.var "b") (.var "x")))))) (.pow (.var "a") (.int (-1)))) (.app2 .mul (.int (-1)) (.var "I1")))
  integrals := [("I1", .app1 .sin (.app2 .mul (.app2 .mul (.var "a") (.var "x")) (.app1 .ln (.app2 .mul (.var "b") (.var "x")))))]
  independent := ["a", "b"]
  conditions := [.ne (.var "a") (.int 0)]
  priority := 9135
  description := "∫ sin(a x log(b x)) log(b x), when a ≠ 0"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:45" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#45"

/-- ∫ cos(a x log(b x)) log(b x), when a ≠ 0 -/
def cosXLogNondeg : CRule where
  id := "integration.cos_x_log_times_log_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:46"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .cos (.app2 .mul (.app2 .mul (.var "a") (.var "x")) (.app1 .ln (.app2 .mul (.var "b") (.var "x"))))) (.app1 .ln (.app2 .mul (.var "b") (.var "x"))))
  result := (.app2 .add (.app2 .mul (.app1 .sin (.app2 .mul (.app2 .mul (.var "a") (.var "x")) (.app1 .ln (.app2 .mul (.var "b") (.var "x"))))) (.pow (.var "a") (.int (-1)))) (.app2 .mul (.int (-1)) (.var "I1")))
  integrals := [("I1", .app1 .cos (.app2 .mul (.app2 .mul (.var "a") (.var "x")) (.app1 .ln (.app2 .mul (.var "b") (.var "x")))))]
  independent := ["a", "b"]
  conditions := [.ne (.var "a") (.int 0)]
  priority := 9136
  description := "∫ cos(a x log(b x)) log(b x), when a ≠ 0"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:46" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#46"


/-! ## Proofs -/

section Proofs

private theorem zpow_succ_of (A : ℝ) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

theorem logLinearOverXNondeg_real : logLinearOverXNondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" logLinearOverXNondeg.conditions logLinearOverXNondeg.body logLinearOverXNondeg.result
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hN0 := hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "n")) (.int 0)) (by simp [logLinearOverXNondeg])
  simp [Cond.Holds, Defined, eval, Interp.real, h2] at hN0
  rcases hk_n : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [logLinearOverXNondeg, Defined, eval, Interp.real, hm1, hk_n] at h
  have h_n : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hk_n
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    simp [logLinearOverXNondeg, Defined, eval, Interp.real, hk_n, hm1] at hw
    simp [logLinearOverXNondeg, Defined, eval, Interp.real, hk_n, h2, hm1, hN0]
    first | exact hw.1 | exact hw.1.2 | tauto | (trace_state; sorry)
  · have hw := hF.self_of_nhds
    simp [logLinearOverXNondeg, Defined, eval, Interp.real, hk_n, hm1] at hw
    have hpos : 0 < env "c" * t ^ j := by first | exact hw.1 | exact hw.1.2 | tauto
    have ht0 : t ≠ 0 := by first | exact hw.2 | tauto
    have hL := OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hpos
    have hfun : (fun w => eval Interp.real (Function.update env "x" w) logLinearOverXNondeg.result) =
        fun w => (env "a" + env "b" * Real.log (env "c" * w ^ j)) ^ 2 * (2 * env "b" * env "n")⁻¹ := by
      funext w
      simp [logLinearOverXNondeg, eval, Interp.real, hk_n, h2, hm1]
    rw [hfun]
    refine ((((hL.const_mul (env "b")).const_add (env "a")).pow 2).mul_const _).congr_deriv ?_
    simp [logLinearOverXNondeg, eval, Interp.real, hk_n, hm1]
    simp only [h_n] at *
    obtain ⟨hb, hj⟩ := hN0
    have hb' : env "b" * (env "b")⁻¹ = 1 := mul_inv_cancel₀ hb
    have hj' : (j : ℝ) * (j : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hj
    have ht' : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0
    rw [div_eq_mul_inv]
    generalize env "a" + env "b" * Real.log (env "c" * t ^ j) = A
    linear_combination (A * t⁻¹) * ((j : ℝ) * (j : ℝ)⁻¹) * hb' + (A * t⁻¹) * hj'

theorem powerLogLinearNondeg_real : powerLogLinearNondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" powerLogLinearNondeg.conditions powerLogLinearNondeg.body powerLogLinearNondeg.result
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hN0 := hc (.ne (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [powerLogLinearNondeg])
  simp [Cond.Holds, Defined, eval, Interp.real, h2] at hN0
  have hN1 := hc (.ne (.app2 .mul (.var "d") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2))) (.int 0)) (by simp [powerLogLinearNondeg])
  simp [Cond.Holds, Defined, eval, Interp.real, h2] at hN1
  rcases hk_m : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [powerLogLinearNondeg, Defined, eval, Interp.real, hm1, hk_m] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk_m
  rcases hk_n : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [powerLogLinearNondeg, Defined, eval, Interp.real, hm1, hk_m, hk_n] at h
  have h_n : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hk_n
  have e1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    simp [powerLogLinearNondeg, Defined, eval, Interp.real, hk_m, hk_n, hm1] at hw
    simp [powerLogLinearNondeg, Defined, eval, Interp.real, hk_n, e1, h2, hm1, hN0, hN1]
    first | exact ⟨⟨⟨fun h => (hw.1 (by omega)).2, hw.2.1, hw.2.2⟩, fun h => (hw.1 (by omega)).2⟩⟩ | exact ⟨⟨fun h => (hw.1 (by omega)).2, hw.2.1, hw.2.2⟩, fun h => (hw.1 (by omega)).2⟩ | (trace_state; sorry)
  · have hw := hF.self_of_nhds
    simp [powerLogLinearNondeg, Defined, eval, Interp.real, hk_m, hk_n, hm1] at hw
    have hpos : 0 < env "c" * t ^ j := by first | exact hw.2.2 | exact hw.2 | tauto
    have hY0 : env "d" * t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · left
        have h' := hw.1 h
        first | exact h' | exact mul_ne_zero h'.1 h'.2 | tauto
      · right; omega
    have hY1 : env "d" * t ≠ 0 ∨ 0 ≤ k + 1 := by
      rcases hY0 with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hL := OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hpos
    have hZ := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hpos
    set W1 := (env "d" * (env "m" + 1))⁻¹ with hW1_def
    set W2 := (env "d" * (env "m" + 1) ^ 2)⁻¹ with hW2_def
    have hU1 : env "d" * (env "m" + 1) * W1 = 1 := by rw [hW1_def]; exact mul_inv_cancel₀ (by simpa using hN0)
    have hU2 : env "d" * (env "m" + 1) ^ 2 * W2 = 1 := by rw [hW2_def]; exact mul_inv_cancel₀ (by simpa using hN1)
    have hfun : (fun w => eval Interp.real (Function.update env "x" w) powerLogLinearNondeg.result) =
        fun w => (env "d" * w) ^ (k + 1) * (env "a" + env "b" * Real.log (env "c" * w ^ j)) * W1 +
          -1 * env "b" * env "n" * (env "d" * w) ^ (k + 1) * W2 := by
      funext w
      simp [powerLogLinearNondeg, eval, Interp.real, hk_n, e1, h2, hm1, hW1_def, hW2_def, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    have hY := HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hY1) ((hasDerivAt_id' t).const_mul (env "d"))
    have hA := (hL.const_mul (env "b")).const_add (env "a")
    refine (((hY.mul hA).mul_const W1).add ((hY.const_mul (-1 * env "b" * env "n")).mul_const W2)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hEF : eval Interp.real (Function.update env "x" t) powerLogLinearNondeg.body =
        (env "d" * t) ^ k * (env "a" + env "b" * Real.log (env "c" * t ^ j)) := by
      simp [powerLogLinearNondeg, eval, Interp.real, hk_m, hk_n]
    rw [hEF, zpow_succ_of _ _ hY0]
    generalize (j : ℝ) / t = Z at hZ ⊢
    generalize (env "d" * t) ^ k = Em
    generalize Real.log (env "c" * t ^ j) = L
    clear_value W1 W2
    simp only [h_m, h_n] at hU1 hU2 ⊢
    push_cast
    linear_combination (Em * W1 * env "b" * env "d") * hZ +
      (Em * (L * env "b" + env "a") + Em * env "b" * env "d" * (j : ℝ) * ((k : ℝ) + 1) * W2) * hU1 +
      (-Em * env "b" * env "d" * (j : ℝ) * W1) * hU2

theorem powSinLogNondeg_real : powSinLogNondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" powSinLogNondeg.conditions powSinLogNondeg.body powSinLogNondeg.result
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hN0 := hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int 0)) (by simp [powSinLogNondeg])
  simp [Cond.Holds, Defined, eval, Interp.real, h2] at hN0
  rcases hk_m : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [powSinLogNondeg, Defined, eval, Interp.real, hm1, hk_m] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk_m
  rcases hk_n : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [powSinLogNondeg, Defined, eval, Interp.real, hm1, hk_m, hk_n] at h
  have h_n : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hk_n
  have e1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    simp [powSinLogNondeg, Defined, eval, Interp.real, hk_m, hk_n, hm1] at hw
    simp [powSinLogNondeg, Defined, eval, Interp.real, hk_n, e1, h2, hm1, hN0]
    exact ⟨fun h => hw.1 (by omega), hw.2.1, hw.2.2⟩
  · have hw := hF.self_of_nhds
    simp [powSinLogNondeg, Defined, eval, Interp.real, hk_m, hk_n, hm1] at hw
    have hpos : 0 < env "c" * t ^ j := by first | exact hw.2.2 | exact hw.2 | tauto
    have hY0 : env "e" * t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · left
        have h' := hw.1 h
        first | exact h' | exact mul_ne_zero h'.1 h'.2 | tauto
      · right; omega
    have hY1 : env "e" * t ≠ 0 ∨ 0 ≤ k + 1 := by
      rcases hY0 with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hL := OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hpos
    have hZ := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hpos
    set W := (((((env "b" ^ 2 * env "d" ^ 2) * env "e") * env "n" ^ 2) + (env "e" * (env "m" + 1) ^ 2)))⁻¹ with hW_def
    have hU : (((((env "b" ^ 2 * env "d" ^ 2) * env "e") * env "n" ^ 2) + (env "e" * (env "m" + 1) ^ 2))) * W = 1 := by rw [hW_def]; exact mul_inv_cancel₀ (by simpa using hN0)
    have hfun : (fun w => eval Interp.real (Function.update env "x" w) powSinLogNondeg.result) =
        fun w => (((((env "m" + 1) * (env "e" * w) ^ (k + 1)) * Real.sin (env "d" * (env "a" + (env "b" * Real.log (env "c" * w ^ j))))) * W) + (((((((-1) * env "b") * env "d") * env "n") * (env "e" * w) ^ (k + 1)) * Real.cos (env "d" * (env "a" + (env "b" * Real.log (env "c" * w ^ j))))) * W)) := by
      funext w
      simp [powSinLogNondeg, eval, Interp.real, hk_n, e1, h2, hm1, hW_def, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    have hY := HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hY1) ((hasDerivAt_id' t).const_mul (env "e"))
    have hT : HasDerivAt (fun w => (env "d" * (env "a" + env "b" * Real.log (env "c" * w ^ j)))) (env "d" * (env "b" * ((j : ℝ) / t))) t :=
      ((hL.const_mul (env "b")).const_add (env "a")).const_mul (env "d")
    have hMd := (Real.hasDerivAt_sin _).comp t hT
    have hNd := (Real.hasDerivAt_cos _).comp t hT
    refine ((((hY.const_mul _).mul hMd).mul_const _).add (((hY.const_mul _).mul hNd).mul_const _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hEF : eval Interp.real (Function.update env "x" t) powSinLogNondeg.body = (env "e" * t) ^ k * Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) := by
      simp [powSinLogNondeg, eval, Interp.real, hk_m, hk_n]
    rw [hEF, zpow_succ_of _ _ hY0]
    have hpt := Real.sin_sq_add_cos_sq (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j)))
    generalize Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) = S at hpt ⊢
    generalize Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) = C at hpt ⊢
    generalize (j : ℝ) / t = Z at hZ ⊢
    generalize (env "e" * t) ^ k = Em
    clear_value W
    simp only [h_m, h_n] at hU ⊢
    push_cast
    linear_combination (Em * W * env "b" * env "d" * env "e" * (C * (k : ℝ) + C + S * env "b" * env "d" * (j : ℝ))) * hZ + (Em * S) * hU

theorem powCosLogNondeg_real : powCosLogNondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" powCosLogNondeg.conditions powCosLogNondeg.body powCosLogNondeg.result
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hN0 := hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int 0)) (by simp [powCosLogNondeg])
  simp [Cond.Holds, Defined, eval, Interp.real, h2] at hN0
  rcases hk_m : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [powCosLogNondeg, Defined, eval, Interp.real, hm1, hk_m] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk_m
  rcases hk_n : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [powCosLogNondeg, Defined, eval, Interp.real, hm1, hk_m, hk_n] at h
  have h_n : env "n" = (j : ℝ) := (intValue?_eq _ _).1 hk_n
  have e1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    simp [powCosLogNondeg, Defined, eval, Interp.real, hk_m, hk_n, hm1] at hw
    simp [powCosLogNondeg, Defined, eval, Interp.real, hk_n, e1, h2, hm1, hN0]
    exact ⟨fun h => hw.1 (by omega), hw.2.1, hw.2.2⟩
  · have hw := hF.self_of_nhds
    simp [powCosLogNondeg, Defined, eval, Interp.real, hk_m, hk_n, hm1] at hw
    have hpos : 0 < env "c" * t ^ j := by first | exact hw.2.2 | exact hw.2 | tauto
    have hY0 : env "e" * t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · left
        have h' := hw.1 h
        first | exact h' | exact mul_ne_zero h'.1 h'.2 | tauto
      · right; omega
    have hY1 : env "e" * t ≠ 0 ∨ 0 ≤ k + 1 := by
      rcases hY0 with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hL := OSR.IntegrationRec7.hasDerivAt_log_monomial _ t j hpos
    have hZ := OSR.IntegrationRec7.mul_div_of_log_monomial _ t j hpos
    set W := (((((env "b" ^ 2 * env "d" ^ 2) * env "e") * env "n" ^ 2) + (env "e" * (env "m" + 1) ^ 2)))⁻¹ with hW_def
    have hU : (((((env "b" ^ 2 * env "d" ^ 2) * env "e") * env "n" ^ 2) + (env "e" * (env "m" + 1) ^ 2))) * W = 1 := by rw [hW_def]; exact mul_inv_cancel₀ (by simpa using hN0)
    have hfun : (fun w => eval Interp.real (Function.update env "x" w) powCosLogNondeg.result) =
        fun w => (((((env "m" + 1) * (env "e" * w) ^ (k + 1)) * Real.cos (env "d" * (env "a" + (env "b" * Real.log (env "c" * w ^ j))))) * W) + (((((env "b" * env "d") * env "n") * (env "e" * w) ^ (k + 1)) * Real.sin (env "d" * (env "a" + (env "b" * Real.log (env "c" * w ^ j))))) * W)) := by
      funext w
      simp [powCosLogNondeg, eval, Interp.real, hk_n, e1, h2, hm1, hW_def, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    have hY := HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hY1) ((hasDerivAt_id' t).const_mul (env "e"))
    have hT : HasDerivAt (fun w => (env "d" * (env "a" + env "b" * Real.log (env "c" * w ^ j)))) (env "d" * (env "b" * ((j : ℝ) / t))) t :=
      ((hL.const_mul (env "b")).const_add (env "a")).const_mul (env "d")
    have hMd := (Real.hasDerivAt_cos _).comp t hT
    have hNd := (Real.hasDerivAt_sin _).comp t hT
    refine ((((hY.const_mul _).mul hMd).mul_const _).add (((hY.const_mul _).mul hNd).mul_const _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hEF : eval Interp.real (Function.update env "x" t) powCosLogNondeg.body = (env "e" * t) ^ k * Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) := by
      simp [powCosLogNondeg, eval, Interp.real, hk_m, hk_n]
    rw [hEF, zpow_succ_of _ _ hY0]
    have hpt := Real.sin_sq_add_cos_sq (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j)))
    generalize Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) = S at hpt ⊢
    generalize Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ j))) = C at hpt ⊢
    generalize (j : ℝ) / t = Z at hZ ⊢
    generalize (env "e" * t) ^ k = Em
    clear_value W
    simp only [h_m, h_n] at hU ⊢
    push_cast
    linear_combination (Em * W * env "b" * env "d" * env "e" * (C * env "b" * env "d" * (j : ℝ) - S * (k : ℝ) - S)) * hZ + (C * Em) * hU

theorem sinXLogNondeg_real : sinXLogNondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" sinXLogNondeg.conditions sinXLogNondeg.body sinXLogNondeg.result sinXLogNondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hN0 := hc (.ne (.var "a") (.int 0)) (by simp [sinXLogNondeg])
  simp [Cond.Holds, Defined, eval, Interp.real, h2] at hN0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) sinXLogNondeg.body → 0 < env "b" * w := by
    intro w h
    simp [sinXLogNondeg, Defined, eval, Interp.real] at h
    first | exact h.1 | exact h.2 | tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [sinXLogNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [Defined, eval, Interp.real]
    first | exact hD w hw | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [sinXLogNondeg, Defined, eval, Interp.real, recEnv, hm1, hN0]
    first | exact hD w hw | (trace_state; sorry)
  · simp only [sinXLogNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hbt := hD t hF.self_of_nhds
    have ht0 : t ≠ 0 := by rintro rfl; simp at hbt
    have hfun : (fun w => eval Interp.real (recEnv env (sinXLogNondeg.integrals.map (·.1)) Φ "x" w) sinXLogNondeg.result) =
        fun w => -1 * Real.cos (env "a" * w * Real.log (env "b" * w)) * (env "a")⁻¹ + -Φ "I1" w := by
      funext w
      simp [sinXLogNondeg, eval, Interp.real, recEnv, hm1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    have hlog : HasDerivAt (fun w => Real.log (env "b" * w)) (env "b" * 1 / (env "b" * t)) t :=
      ((hasDerivAt_id' t).const_mul (env "b")).log hbt.ne'
    have hu : HasDerivAt (fun w => env "a" * w * Real.log (env "b" * w))
        (env "a" * 1 * Real.log (env "b" * t) + env "a" * t * (env "b" * 1 / (env "b" * t))) t :=
      ((hasDerivAt_id' t).const_mul (env "a")).mul hlog
    have hT := (Real.hasDerivAt_cos _).comp t hu
    refine (((hT.const_mul (-1)).mul_const _).add hΦ.neg).congr_deriv ?_
    try simp only [Function.comp_def]
    simp [sinXLogNondeg, eval, Interp.real]
    have hb0 : env "b" ≠ 0 := by rintro h; simp [h] at hbt
    first | (field_simp; ring) | (trace_state; sorry)

theorem cosXLogNondeg_real : cosXLogNondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" cosXLogNondeg.conditions cosXLogNondeg.body cosXLogNondeg.result cosXLogNondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hN0 := hc (.ne (.var "a") (.int 0)) (by simp [cosXLogNondeg])
  simp [Cond.Holds, Defined, eval, Interp.real, h2] at hN0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) cosXLogNondeg.body → 0 < env "b" * w := by
    intro w h
    simp [cosXLogNondeg, Defined, eval, Interp.real] at h
    first | exact h.1 | exact h.2 | tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [cosXLogNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [Defined, eval, Interp.real]
    first | exact hD w hw | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [cosXLogNondeg, Defined, eval, Interp.real, recEnv, hm1, hN0]
    first | exact hD w hw | (trace_state; sorry)
  · simp only [cosXLogNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hbt := hD t hF.self_of_nhds
    have ht0 : t ≠ 0 := by rintro rfl; simp at hbt
    have hfun : (fun w => eval Interp.real (recEnv env (cosXLogNondeg.integrals.map (·.1)) Φ "x" w) cosXLogNondeg.result) =
        fun w => Real.sin (env "a" * w * Real.log (env "b" * w)) * (env "a")⁻¹ + -Φ "I1" w := by
      funext w
      simp [cosXLogNondeg, eval, Interp.real, recEnv, hm1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    have hlog : HasDerivAt (fun w => Real.log (env "b" * w)) (env "b" * 1 / (env "b" * t)) t :=
      ((hasDerivAt_id' t).const_mul (env "b")).log hbt.ne'
    have hu : HasDerivAt (fun w => env "a" * w * Real.log (env "b" * w))
        (env "a" * 1 * Real.log (env "b" * t) + env "a" * t * (env "b" * 1 / (env "b" * t))) t :=
      ((hasDerivAt_id' t).const_mul (env "a")).mul hlog
    have hT := (Real.hasDerivAt_sin _).comp t hu
    refine ((hT.mul_const _).add hΦ.neg).congr_deriv ?_
    try simp only [Function.comp_def]
    simp [cosXLogNondeg, eval, Interp.real]
    have hb0 : env "b" ≠ 0 := by rintro h; simp [h] at hbt
    first | (field_simp; ring) | (trace_state; sorry)

end Proofs

end OSR.IntegrationRec95
