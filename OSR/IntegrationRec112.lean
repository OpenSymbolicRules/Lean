import OSR.IntegrationRec91
import OSR.IntegrationRec7

/-!
# Integration (RUBI): strengthened variants of logarithmic rules failing at a vanishing exponent, second batch

RUBI 3.3 #30 and #39, 3.4 #27 and 3.5 #3 are refuted as stated, and their first
strengthened variants fail numerically when an exponent vanishes (`n = 0` or
`p = 0`), where the integrand is defined at a pole of a residual integrand.
With that exponent nonzero they are proved over ℝ, with the real logarithm; the
complex domain stays unproved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec112

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- ∫ x^m (a + b log(c (d + e x)^n)) (f + g log(c (d + e x)^n)), when m + 1 ≠ 0 and n ≠ 0 -/
def powTwoLogLinNondeg : CRule where
  id := "integration.power_two_log_linear_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:39"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "n")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.var "f")) (.app2 .mul (.var "a") (.var "g"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "g")) (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "n", "m"]
  conditions := [.ne (.var "m") (.int (-1)),
    .ne (.app2 .add (.var "m") (.int 1)) (.int 0),
    .ne (.var "n") (.int 0)]
  priority := 9301
  description := "∫ x^m (a + b log(c (d + e x)^n)) (f + g log(c (d + e x)^n)), when m + 1 ≠ 0 and n ≠ 0"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:39" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#39"

/-- ∫ log(f x^q)^m (a + b log(c (d + e x^n)^p))/x, when q (m + 1) ≠ 0 and p ≠ 0 -/
def logPowLogBinOverXNondeg : CRule where
  id := "integration.log_power_log_binomial_over_x_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "q")))) (.var "m")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "p"))))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "q")))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "p"))))))) (.pow (.app2 .mul (.var "q") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "n")) (.var "p")) (.pow (.app2 .mul (.var "q") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "q")))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p", "q"]
  conditions := [.ne (.var "m") (.int (-1)),
    .ne (.app2 .mul (.var "q") (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.var "p") (.int 0)]
  priority := 9302
  description := "∫ log(f x^q)^m (a + b log(c (d + e x^n)^p))/x, when q (m + 1) ≠ 0 and p ≠ 0"
  provenance := migrated "rubi:3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p:27" "3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p.m#27"

/-- ∫ (e x)^m (a + b log(c log(d x^n)^p)), when e (m + 1) ≠ 0 and p ≠ 0 -/
def logLogWeightedNondeg : CRule where
  id := "integration.power_log_log_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.5 Miscellaneous logarithms:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "p")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "p"))))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.var "p")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "p"]
  conditions := [.ne (.var "m") (.int (-1)),
    .ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.app2 .add (.var "m") (.int 1)) (.int 0),
    .ne (.var "p") (.int 0)]
  priority := 9303
  description := "∫ (e x)^m (a + b log(c log(d x^n)^p)), when e (m + 1) ≠ 0 and p ≠ 0"
  provenance := migrated "rubi:3 Logarithms/3.5 Miscellaneous logarithms:3" "3 Logarithms/3.5 Miscellaneous logarithms.m#3"

/-- ∫ (g x)^q log(f x^m) (a + b log(c (d + e x)^n)), when g (q + 1) ≠ 0 and n ≠ 0 -/
def powLogLogLinNondeg : CRule where
  id := "integration.power_log_monomial_log_linear_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:30"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "q")) (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m"))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .add (.app2 .mul (.app2 .mul (.var "m") (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "q") (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "q") (.int 1)))) (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m"))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.var "m")) (.var "n")) (.pow (.app2 .mul (.var "g") (.pow (.app2 .add (.var "q") (.int 1)) (.int 2))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "n")) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", .app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))), ("I2", .app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "q") (.int 1))) (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m"))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "n", "q"]
  conditions := [.ne (.var "q") (.int (-1)),
    .ne (.app2 .mul (.var "g") (.app2 .add (.var "q") (.int 1))) (.int 0),
    .ne (.app2 .add (.var "q") (.int 1)) (.int 0),
    .ne (.app2 .mul (.var "g") (.pow (.app2 .add (.var "q") (.int 1)) (.int 2))) (.int 0),
    .ne (.var "n") (.int 0)]
  priority := 9304
  description := "∫ (g x)^q log(f x^m) (a + b log(c (d + e x)^n)), when g (q + 1) ≠ 0 and n ≠ 0"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:30" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#30"


/-! ## Proofs -/

section Proofs

private theorem zpow_succ_of (A : ℝ) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

theorem powTwoLogLinNondeg_real : powTwoLogLinNondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" powTwoLogLinNondeg.conditions powTwoLogLinNondeg.body powTwoLogLinNondeg.result powTwoLogLinNondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hi2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have ord : ∀ (x y : ℤ), Interp.real.lt (x : ℝ) (y : ℝ) → x < y := by
    intro x y h
    have h' : Interp.real.lt ((x : ℚ) : ℝ) ((y : ℚ) : ℝ) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (Interp.real_lt_rat _ _).1 h'
  have hA0 := hc (.ne (.app2 .add (.var "m") (.int 1)) (.int 0)) (by simp [powTwoLogLinNondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hn0 : env "n" ≠ 0 := by have h := hc (.ne (.var "n") (.int 0)) (by simp [powTwoLogLinNondeg]); simpa [Cond.Holds, Defined, eval] using h
  rcases hk_m : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [powTwoLogLinNondeg, Defined, eval, Interp.real, hm1, hk_m, -Real.log_eq_zero] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk_m
  rcases hk_n : intValue? (env "n") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [powTwoLogLinNondeg, Defined, eval, Interp.real, hm1, hk_m, hk_n, -Real.log_eq_zero] at h
  have h_n : env "n" = (i : ℝ) := (intValue?_eq _ _).1 hk_n
  have em1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hi0 : i ≠ 0 := by intro h; apply hn0; rw [h_n, h]; simp
  have hDne : ∀ w : ℝ, 0 < env "c" * (env "d" + env "e" * w) ^ i → (env "d" + env "e" * w) ≠ 0 := by
    intro w h h0; rw [h0, zero_zpow i hi0, mul_zero] at h; exact lt_irrefl 0 h
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) powTwoLogLinNondeg.body →
      (k < 0 → w ≠ 0) ∧ 0 < env "c" * (env "d" + env "e" * w) ^ i := by
    intro w h
    simp [powTwoLogLinNondeg, Defined, eval, Interp.real, hk_m, hk_n, em1, hm1, hi2, -Real.log_eq_zero] at h
    first | exact ⟨h.1.1, h.1.2.2⟩ | exact ⟨h.1.1, h.2.2⟩ | tauto | (trace_state; sorry)
  refine ⟨fun i' hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [powTwoLogLinNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hBody w hw
    simp [Defined, eval, Interp.real, hk_m, hk_n, em1, hm1, hi2, -Real.log_eq_zero, h2, hDne w h2]
    first | done | exact fun h => h1 (by omega) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hBody w hw
    simp [powTwoLogLinNondeg, Defined, eval, Interp.real, recEnv, hk_m, hk_n, em1, hm1, hi2, -Real.log_eq_zero, h2, hA0]
    first | done | exact fun h => h1 (by omega) | exact ⟨fun h => h1 (by omega), fun _ => hDne w h2⟩ | (trace_state; sorry)
  · simp only [powTwoLogLinNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hx', hpos⟩ := hBody t hF.self_of_nhds
    have hD0 := hDne t hpos
    have hx1 : t ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k + 1 < 0
      · exact Or.inl (hx' (by omega))
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") (t ^ (k + 1) * (env "b" * env "f" + env "a" * env "g" + 2 * env "b" * env "g" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) * (env "d" + env "e" * t)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hk_m, hk_n, em1, hm1, hi2, -Real.log_eq_zero]
    have hEF : eval Interp.real (Function.update env "x" t) powTwoLogLinNondeg.body = t ^ k * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) * (env "f" + env "g" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) := by
      simp [powTwoLogLinNondeg, eval, Interp.real, hk_m, hk_n, em1, hm1, hi2, -Real.log_eq_zero]
    have hfun : (fun w => eval Interp.real (recEnv env (powTwoLogLinNondeg.integrals.map (·.1)) Φ "x" w) powTwoLogLinNondeg.result) =
        fun w => ((((w ^ (k + 1) * (env "a" + (env "b" * Real.log (env "c" * (env "d" + (env "e" * w)) ^ i)))) * (env "f" + (env "g" * Real.log (env "c" * (env "d" + (env "e" * w)) ^ i)))) * (env "m" + 1)⁻¹) + (((((-1) * env "e") * env "n") * (env "m" + 1)⁻¹) * Φ "I1" w)) := by
      funext w
      simp [powTwoLogLinNondeg, eval, Interp.real, recEnv, hk_m, hk_n, em1, hm1, hi2, -Real.log_eq_zero, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hDd : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
    have hL := (OSR.IntegrationRec7.hasDerivAt_log_monomial (env "c") (env "d" + env "e" * t) i hpos).comp t hDd
    have hA := (hL.const_mul (env "b")).const_add (env "a")
    have hG := (hL.const_mul (env "g")).const_add (env "f")
    have hX := hasDerivAt_zpow (k + 1) t hx1
    refine ((((hX.mul hA).mul hG).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    generalize Real.log (env "c" * (env "d" + env "e" * t) ^ i) = L
    simp only [div_eq_mul_inv]
    generalize hDe : (env "d" + env "e" * t) = D at hD0 ⊢
    simp only [h_m, h_n] at *
    try casesm* _ ∧ _
    field_simp
    push_cast
    ring

theorem logPowLogBinOverXNondeg_real : logPowLogBinOverXNondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" logPowLogBinOverXNondeg.conditions logPowLogBinOverXNondeg.body logPowLogBinOverXNondeg.result logPowLogBinOverXNondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hi2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have ord : ∀ (x y : ℤ), Interp.real.lt (x : ℝ) (y : ℝ) → x < y := by
    intro x y h
    have h' : Interp.real.lt ((x : ℚ) : ℝ) ((y : ℚ) : ℝ) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (Interp.real_lt_rat _ _).1 h'
  have hA0 := hc (.ne (.app2 .mul (.var "q") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [logPowLogBinOverXNondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hp0 : env "p" ≠ 0 := by have h := hc (.ne (.var "p") (.int 0)) (by simp [logPowLogBinOverXNondeg]); simpa [Cond.Holds, Defined, eval] using h
  rcases hk_m : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [logPowLogBinOverXNondeg, Defined, eval, Interp.real, hm1, hk_m, -Real.log_eq_zero] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk_m
  rcases hk_q : intValue? (env "q") with _ | jq
  · exfalso
    have h := hF.self_of_nhds
    simp [logPowLogBinOverXNondeg, Defined, eval, Interp.real, hm1, hk_m, hk_q, -Real.log_eq_zero] at h
  have h_q : env "q" = (jq : ℝ) := (intValue?_eq _ _).1 hk_q
  rcases hk_n : intValue? (env "n") with _ | jn
  · exfalso
    have h := hF.self_of_nhds
    simp [logPowLogBinOverXNondeg, Defined, eval, Interp.real, hm1, hk_m, hk_q, hk_n, -Real.log_eq_zero] at h
  have h_n : env "n" = (jn : ℝ) := (intValue?_eq _ _).1 hk_n
  rcases hk_p : intValue? (env "p") with _ | jp
  · exfalso
    have h := hF.self_of_nhds
    simp [logPowLogBinOverXNondeg, Defined, eval, Interp.real, hm1, hk_m, hk_q, hk_n, hk_p, -Real.log_eq_zero] at h
  have h_p : env "p" = (jp : ℝ) := (intValue?_eq _ _).1 hk_p
  have em1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have en1 : intValue? (env "n" + -1 * 1) = some (jn - 1) := (intValue?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have en1' : intValue? (env "n" + -1) = some (jn - 1) := (intValue?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have hjp0 : jp ≠ 0 := by intro h; apply hp0; rw [h_p, h]; simp
  have hEne : ∀ w : ℝ, 0 < env "c" * (env "d" + env "e" * w ^ jn) ^ jp → (env "d" + env "e" * w ^ jn) ≠ 0 := by
    intro w h h0; rw [h0, zero_zpow jp hjp0, mul_zero] at h; exact lt_irrefl 0 h
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) logPowLogBinOverXNondeg.body →
      0 < env "f" * w ^ jq ∧ (k < 0 → Real.log (env "f" * w ^ jq) ≠ 0) ∧ 0 < env "c" * (env "d" + env "e" * w ^ jn) ^ jp ∧ w ≠ 0 := by
    intro w h
    simp [logPowLogBinOverXNondeg, Defined, eval, Interp.real, hk_m, hk_q, hk_n, hk_p, em1, en1, en1', hm1, hi2, -Real.log_eq_zero] at h
    first | tauto | (trace_state; sorry)
  refine ⟨fun i' hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [logPowLogBinOverXNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3, h4⟩ := hBody w hw
    simp [Defined, eval, Interp.real, hk_m, hk_q, hk_n, hk_p, em1, en1, en1', hm1, hi2, -Real.log_eq_zero, h1, h4, hEne w h3]
    first | done | exact fun h => h2 (by omega) | exact ⟨fun _ => h4, fun h => h2 (by omega)⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3, h4⟩ := hBody w hw
    simp [logPowLogBinOverXNondeg, Defined, eval, Interp.real, recEnv, hk_m, hk_q, hk_n, hk_p, em1, en1, en1', hm1, hi2, -Real.log_eq_zero, h1, h3, h4, hA0]
    first | done | exact fun h => h2 (by omega) | exact ⟨fun h => h2 (by omega), fun _ => h4⟩ | exact ⟨fun h => h2 (by omega), fun _ => hEne w h3⟩ | (trace_state; sorry)
  · simp only [logPowLogBinOverXNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hp1', hL0', hp2', ht0⟩ := hBody t hF.self_of_nhds
    have hE0 := hEne t hp2'
    have hL1 : Real.log (env "f" * t ^ jq) ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k + 1 < 0
      · exact Or.inl (hL0' (by omega))
      · exact Or.inr (by omega)
    have hL0 : Real.log (env "f" * t ^ jq) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (hL0' h)
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") (t ^ (jn - 1) * Real.log (env "f" * t ^ jq) ^ (k + 1) * (env "d" + env "e" * t ^ jn)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hk_m, hk_q, hk_n, hk_p, em1, en1, en1', hm1, hi2, -Real.log_eq_zero]
    have hEF : eval Interp.real (Function.update env "x" t) logPowLogBinOverXNondeg.body = Real.log (env "f" * t ^ jq) ^ k * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t ^ jn) ^ jp)) * t⁻¹ := by
      simp [logPowLogBinOverXNondeg, eval, Interp.real, hk_m, hk_q, hk_n, hk_p, em1, en1, en1', hm1, hi2, -Real.log_eq_zero]
    have hfun : (fun w => eval Interp.real (recEnv env (logPowLogBinOverXNondeg.integrals.map (·.1)) Φ "x" w) logPowLogBinOverXNondeg.result) =
        fun w => (((Real.log (env "f" * w ^ jq) ^ (k + 1) * (env "a" + (env "b" * Real.log (env "c" * (env "d" + (env "e" * w ^ jn)) ^ jp)))) * (env "q" * (env "m" + 1))⁻¹) + (((((((-1) * env "b") * env "e") * env "n") * env "p") * (env "q" * (env "m" + 1))⁻¹) * Φ "I1" w)) := by
      funext w
      simp [logPowLogBinOverXNondeg, eval, Interp.real, recEnv, hk_m, hk_q, hk_n, hk_p, em1, en1, en1', hm1, hi2, -Real.log_eq_zero, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hL1d := OSR.IntegrationRec7.hasDerivAt_log_monomial (env "f") t jq hp1'
    have hEd : HasDerivAt (fun w => (env "d" + env "e" * w ^ jn)) (env "e" * ((jn : ℝ) * t ^ (jn - 1))) t :=
      ((hasDerivAt_zpow jn t (Or.inl ht0)).const_mul _).const_add _
    have hL2 := (OSR.IntegrationRec7.hasDerivAt_log_monomial (env "c") (env "d" + env "e" * t ^ jn) jp hp2').comp t hEd
    have hΛ := (hL2.const_mul (env "b")).const_add (env "a")
    have hL1p := HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hL1) hL1d
    refine (((hL1p.mul hΛ).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hL0, zpow_sub_one₀ ht0]
    generalize Real.log (env "f" * t ^ jq) ^ k = Lk
    generalize Real.log (env "f" * t ^ jq) = L1
    generalize (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t ^ jn) ^ jp)) = Lm
    simp only [div_eq_mul_inv]
    generalize hEe : (env "d" + env "e" * t ^ jn) = E at hE0 ⊢
    simp only [h_m, h_q, h_n, h_p] at *
    try casesm* _ ∧ _
    field_simp
    push_cast
    ring

theorem logLogWeightedNondeg_real : logLogWeightedNondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" logLogWeightedNondeg.conditions logLogWeightedNondeg.body logLogWeightedNondeg.result logLogWeightedNondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hi2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have ord : ∀ (x y : ℤ), Interp.real.lt (x : ℝ) (y : ℝ) → x < y := by
    intro x y h
    have h' : Interp.real.lt ((x : ℚ) : ℝ) ((y : ℚ) : ℝ) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (Interp.real_lt_rat _ _).1 h'
  have hA0 := hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [logLogWeightedNondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hA1 := hc (.ne (.app2 .add (.var "m") (.int 1)) (.int 0)) (by simp [logLogWeightedNondeg])
  simp [Cond.Holds, Defined, eval] at hA1
  have hp0 : env "p" ≠ 0 := by have h := hc (.ne (.var "p") (.int 0)) (by simp [logLogWeightedNondeg]); simpa [Cond.Holds, Defined, eval] using h
  rcases hk_m : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [logLogWeightedNondeg, Defined, eval, Interp.real, hm1, hk_m, -Real.log_eq_zero] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk_m
  rcases hk_n : intValue? (env "n") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [logLogWeightedNondeg, Defined, eval, Interp.real, hm1, hk_m, hk_n, -Real.log_eq_zero] at h
  have h_n : env "n" = (i : ℝ) := (intValue?_eq _ _).1 hk_n
  rcases hk_p : intValue? (env "p") with _ | jp
  · exfalso
    have h := hF.self_of_nhds
    simp [logLogWeightedNondeg, Defined, eval, Interp.real, hm1, hk_m, hk_n, hk_p, -Real.log_eq_zero] at h
  have h_p : env "p" = (jp : ℝ) := (intValue?_eq _ _).1 hk_p
  have em1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hjp0 : jp ≠ 0 := by intro h; apply hp0; rw [h_p, h]; simp
  have hLne : ∀ w : ℝ, 0 < env "c" * Real.log (env "d" * w ^ i) ^ jp → Real.log (env "d" * w ^ i) ≠ 0 := by
    intro w h h0; rw [h0, zero_zpow jp hjp0, mul_zero] at h; exact lt_irrefl 0 h
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) logLogWeightedNondeg.body →
      (k < 0 → env "e" * w ≠ 0) ∧ 0 < env "d" * w ^ i ∧ 0 < env "c" * Real.log (env "d" * w ^ i) ^ jp := by
    intro w h
    simp [logLogWeightedNondeg, Defined, eval, Interp.real, hk_m, hk_n, hk_p, em1, hm1, hi2, -Real.log_eq_zero] at h
    exact ⟨fun hk => mul_ne_zero (h.1 hk).1 (h.1 hk).2, h.2.1.1.2, h.2.2⟩
  refine ⟨fun i' hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [logLogWeightedNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3⟩ := hBody w hw
    simp [Defined, eval, Interp.real, hk_m, hk_n, hk_p, em1, hm1, hi2, -Real.log_eq_zero, h2, hLne w h3]
    first | done | exact ⟨fun hk => ⟨left_ne_zero_of_mul (h1 hk), right_ne_zero_of_mul (h1 hk)⟩, fun hi => by intro h0; rw [h0, zero_zpow i (by omega), mul_zero] at h2; exact lt_irrefl 0 h2⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3⟩ := hBody w hw
    simp [logLogWeightedNondeg, Defined, eval, Interp.real, recEnv, hk_m, hk_n, hk_p, em1, hm1, hi2, -Real.log_eq_zero, h2, h3, hA0, hA1]
    first | done | exact ⟨fun hk => right_ne_zero_of_mul (h1 (by omega)), fun hi => by intro h0; rw [h0, zero_zpow i (by omega), mul_zero] at h2; exact lt_irrefl 0 h2, fun _ => hLne w h3⟩ | (trace_state; sorry)
  · simp only [logLogWeightedNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hE', hp1', hp2'⟩ := hBody t hF.self_of_nhds
    have hLn0 := hLne t hp2'
    have hE0 : env "e" * t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (hE' h)
      · exact Or.inr (by omega)
    have hE1 : env "e" * t ≠ 0 ∨ 0 ≤ k + 1 := by
      rcases hE0 with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" * t) ^ k * (Real.log (env "d" * t ^ i))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hk_m, hk_n, hk_p, em1, hm1, hi2, -Real.log_eq_zero, -Real.log_inv]
    have hEF : eval Interp.real (Function.update env "x" t) logLogWeightedNondeg.body = (env "e" * t) ^ k * (env "a" + env "b" * Real.log (env "c" * Real.log (env "d" * t ^ i) ^ jp)) := by
      simp [logLogWeightedNondeg, eval, Interp.real, hk_m, hk_n, hk_p, em1, hm1, hi2, -Real.log_eq_zero]
    set W1 := (env "e" * (env "m" + 1))⁻¹ with hW1_def
    have hW2e : (env "m" + 1)⁻¹ = env "e" * W1 := by
      rw [hW1_def]; try casesm* _ ∧ _; field_simp
    have hU : env "e" * (env "m" + 1) * W1 = 1 := by
      rw [hW1_def]; exact mul_inv_cancel₀ (by simp only [ne_eq, mul_eq_zero, not_or]; tauto)
    have hfun : (fun w => eval Interp.real (recEnv env (logLogWeightedNondeg.integrals.map (·.1)) Φ "x" w) logLogWeightedNondeg.result) =
        fun w => (env "e" * w) ^ (k + 1) * (env "a" + env "b" * Real.log (env "c" * Real.log (env "d" * w ^ i) ^ jp)) * W1 +
          -1 * env "b" * env "n" * env "p" * (env "e" * W1) * Φ "I1" w := by
      funext w
      rw [← hW2e]
      simp [logLogWeightedNondeg, eval, Interp.real, recEnv, hk_m, hk_n, hk_p, em1, hm1, hi2, -Real.log_eq_zero, hW1_def, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hLn := OSR.IntegrationRec7.hasDerivAt_log_monomial (env "d") t i hp1'
    have hZ := OSR.IntegrationRec7.mul_div_of_log_monomial (env "d") t i hp1'
    have hL2 := (OSR.IntegrationRec7.hasDerivAt_log_monomial (env "c") (Real.log (env "d" * t ^ i)) jp hp2').comp t hLn
    have hΛ := (hL2.const_mul (env "b")).const_add (env "a")
    have hEp := HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hE1) ((hasDerivAt_id' t).const_mul (env "e"))
    refine (((hEp.mul hΛ).mul_const W1).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hE0, div_eq_mul_inv (jp : ℝ)]
    have hLi : (Real.log (env "d" * t ^ i)) * (Real.log (env "d" * t ^ i))⁻¹ = 1 := mul_inv_cancel₀ hLn0
    generalize (env "e" * t) ^ k = Em
    generalize (i : ℝ) / t = Z at hZ ⊢
    generalize (Real.log (env "d" * t ^ i))⁻¹ = Li at hLi ⊢
    generalize (env "a" + env "b" * Real.log (env "c" * Real.log (env "d" * t ^ i) ^ jp)) = Lam
    clear_value W1
    simp only [h_m, h_n, h_p] at hU ⊢
    push_cast
    linear_combination (Em * Lam) * hU + (Em * env "e" * env "b" * (jp : ℝ) * Li * W1) * hZ

theorem powLogLogLinNondeg_real : powLogLogLinNondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" powLogLogLinNondeg.conditions powLogLogLinNondeg.body powLogLogLinNondeg.result powLogLogLinNondeg.integrals
  intro env hc t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hi2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have ord : ∀ (x y : ℤ), Interp.real.lt (x : ℝ) (y : ℝ) → x < y := by
    intro x y h
    have h' : Interp.real.lt ((x : ℚ) : ℝ) ((y : ℚ) : ℝ) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (Interp.real_lt_rat _ _).1 h'
  have hA0 := hc (.ne (.app2 .mul (.var "g") (.app2 .add (.var "q") (.int 1))) (.int 0)) (by simp [powLogLogLinNondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hA1 := hc (.ne (.app2 .add (.var "q") (.int 1)) (.int 0)) (by simp [powLogLogLinNondeg])
  simp [Cond.Holds, Defined, eval] at hA1
  have hA2 := hc (.ne (.app2 .mul (.var "g") (.pow (.app2 .add (.var "q") (.int 1)) (.int 2))) (.int 0)) (by simp [powLogLogLinNondeg])
  simp [Cond.Holds, Defined, eval, hi2] at hA2
  have hn0 : env "n" ≠ 0 := by have h := hc (.ne (.var "n") (.int 0)) (by simp [powLogLogLinNondeg]); simpa [Cond.Holds, Defined, eval] using h
  rcases hk_q : intValue? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [powLogLogLinNondeg, Defined, eval, Interp.real, hm1, hk_q, -Real.log_eq_zero] at h
  have h_q : env "q" = (kq : ℝ) := (intValue?_eq _ _).1 hk_q
  rcases hk_m : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [powLogLogLinNondeg, Defined, eval, Interp.real, hm1, hk_q, hk_m, -Real.log_eq_zero] at h
  have h_m : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hk_m
  rcases hk_n : intValue? (env "n") with _ | i
  · exfalso
    have h := hF.self_of_nhds
    simp [powLogLogLinNondeg, Defined, eval, Interp.real, hm1, hk_q, hk_m, hk_n, -Real.log_eq_zero] at h
  have h_n : env "n" = (i : ℝ) := (intValue?_eq _ _).1 hk_n
  have eq1 : intValue? (env "q" + 1) = some (kq + 1) := (intValue?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have hi0 : i ≠ 0 := by intro h; apply hn0; rw [h_n, h]; simp
  have hDne : ∀ w : ℝ, 0 < env "c" * (env "d" + env "e" * w) ^ i → (env "d" + env "e" * w) ≠ 0 := by
    intro w h h0; rw [h0, zero_zpow i hi0, mul_zero] at h; exact lt_irrefl 0 h
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) powLogLogLinNondeg.body →
      (kq < 0 → env "g" * w ≠ 0) ∧ 0 < env "f" * w ^ j ∧ 0 < env "c" * (env "d" + env "e" * w) ^ i := by
    intro w h
    simp [powLogLogLinNondeg, Defined, eval, Interp.real, hk_q, hk_m, hk_n, eq1, hm1, hi2, -Real.log_eq_zero] at h
    first | exact ⟨fun hk => mul_ne_zero (h.1.1 hk).1 (h.1.1 hk).2, h.1.2.2, h.2.2⟩ | exact ⟨fun hk => mul_ne_zero (h.1.1 hk).1 (h.1.1 hk).2, h.1.2.2, h.2.2.2⟩ | (trace_state; sorry)
  refine ⟨fun i' hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [powLogLogLinNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · obtain ⟨h1, h2, h3⟩ := hBody w hw
      simp [Defined, eval, Interp.real, hk_q, hk_m, hk_n, eq1, hm1, hi2, -Real.log_eq_zero, h2, h3, hDne w h3]
      first | done | exact fun hk => ⟨left_ne_zero_of_mul (h1 (by omega)), right_ne_zero_of_mul (h1 (by omega))⟩ | exact ⟨fun hk => ⟨left_ne_zero_of_mul (h1 (by omega)), right_ne_zero_of_mul (h1 (by omega))⟩, fun hj => by intro h0; rw [h0, zero_zpow j (by omega), mul_zero] at h2; exact lt_irrefl 0 h2⟩ | exact ⟨fun hk => ⟨left_ne_zero_of_mul (h1 (by omega)), right_ne_zero_of_mul (h1 (by omega))⟩, fun hj => by intro h0; rw [h0, zero_zpow j (by omega), mul_zero] at h2; exact lt_irrefl 0 h2⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3⟩ := hBody w hw
    simp [powLogLogLinNondeg, Defined, eval, Interp.real, recEnv, hk_q, hk_m, hk_n, eq1, hm1, hi2, -Real.log_eq_zero, h2, h3, hA0, hA1, hA2]
    first | done | exact fun hk => ⟨left_ne_zero_of_mul (h1 (by omega)), right_ne_zero_of_mul (h1 (by omega))⟩ | exact ⟨fun hk => ⟨left_ne_zero_of_mul (h1 (by omega)), right_ne_zero_of_mul (h1 (by omega))⟩, fun hk => ⟨left_ne_zero_of_mul (h1 (by omega)), right_ne_zero_of_mul (h1 (by omega))⟩⟩ | exact ⟨⟨fun hk => right_ne_zero_of_mul (h1 (by omega)), fun hj => by intro h0; rw [h0, zero_zpow j (by omega), mul_zero] at h2; exact lt_irrefl 0 h2⟩, fun _ => hDne w h3⟩ | (trace_state; sorry)
  · simp only [powLogLogLinNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    obtain ⟨hG', hp1', hp2'⟩ := hBody t hF.self_of_nhds
    have hD0 := hDne t hp2'
    have hG0 : (env "g" * t) ≠ 0 ∨ 0 ≤ kq := by
      by_cases h : kq < 0
      · exact Or.inl (hG' h)
      · exact Or.inr (by omega)
    have hG1 : (env "g" * t) ≠ 0 ∨ 0 ≤ kq + 1 := by
      rcases hG0 with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hΦ1' : HasDerivAt (Φ "I1") ((env "g" * t) ^ (kq + 1) * (env "d" + env "e" * t)⁻¹) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hk_q, hk_m, hk_n, eq1, hm1, hi2, -Real.log_eq_zero]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "g" * t) ^ (kq + 1) * Real.log (env "f" * t ^ j) * (env "d" + env "e" * t)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hk_q, hk_m, hk_n, eq1, hm1, hi2, -Real.log_eq_zero]
    have hEF : eval Interp.real (Function.update env "x" t) powLogLogLinNondeg.body = (env "g" * t) ^ kq * Real.log (env "f" * t ^ j) * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) := by
      simp [powLogLogLinNondeg, eval, Interp.real, hk_q, hk_m, hk_n, eq1, hm1, hi2, -Real.log_eq_zero]
    set W := (env "g" * (env "q" + 1))⁻¹ with hW_def
    set V := (env "q" + 1)⁻¹ with hV_def
    have hWg : (env "g" * (env "q" + 1) ^ 2)⁻¹ = W * V := by rw [hW_def, hV_def]; try casesm* _ ∧ _; field_simp
    have hU1 : env "g" * (env "q" + 1) * W = 1 := by
      rw [hW_def]; exact mul_inv_cancel₀ (by simp only [ne_eq, mul_eq_zero, not_or]; tauto)
    have hU2 : (env "q" + 1) * V = 1 := by rw [hV_def]; exact mul_inv_cancel₀ (by tauto)
    have hfun : (fun w => eval Interp.real (recEnv env (powLogLogLinNondeg.integrals.map (·.1)) Φ "x" w) powLogLogLinNondeg.result) =
        fun w => -1 * W * (env "m" * (env "g" * w) ^ (kq + 1) * V + -1 * (env "g" * w) ^ (kq + 1) * Real.log (env "f" * w ^ j)) * (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * w) ^ i)) +
          env "b" * env "e" * env "m" * env "n" * (W * V) * Φ "I1" w + -1 * env "b" * env "e" * env "n" * W * Φ "I2" w := by
      funext w
      rw [← hWg]
      simp [powLogLogLinNondeg, eval, Interp.real, recEnv, hk_q, hk_m, hk_n, eq1, hm1, hi2, -Real.log_eq_zero, hW_def, hV_def, hi2, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hGp := HasDerivAt.comp t (hasDerivAt_zpow (kq + 1) _ hG1) ((hasDerivAt_id' t).const_mul (env "g"))
    have hL1 := OSR.IntegrationRec7.hasDerivAt_log_monomial (env "f") t j hp1'
    have hZ := OSR.IntegrationRec7.mul_div_of_log_monomial (env "f") t j hp1'
    have hDd : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
      simpa using ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
    have hL2 := (OSR.IntegrationRec7.hasDerivAt_log_monomial (env "c") (env "d" + env "e" * t) i hp2').comp t hDd
    have hΛ := (hL2.const_mul (env "b")).const_add (env "a")
    have hIn := ((hGp.const_mul (env "m")).mul_const V).add ((hGp.const_mul (-1)).mul hL1)
    refine ((((hIn.const_mul (-1 * W)).mul hΛ).add (hΦ1'.const_mul _)).add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, Pi.add_apply, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hG0, div_eq_mul_inv (i : ℝ)]
    have hDi : (env "d" + env "e" * t) * (env "d" + env "e" * t)⁻¹ = 1 := mul_inv_cancel₀ hD0
    generalize (env "g" * t) ^ kq = Gq
    generalize Real.log (env "f" * t ^ j) = L1
    generalize (j : ℝ) / t = Z1 at hZ ⊢
    generalize (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ i)) = Lam
    generalize (env "d" + env "e" * t)⁻¹ = Di at hDi ⊢
    generalize (env "d" + env "e" * t) = D at hDi ⊢
    clear_value W V
    simp only [h_q, h_m, h_n] at hU1 hU2 ⊢
    push_cast
    linear_combination (Gq * L1 * Lam) * hU1 + (-Gq * Lam * (j : ℝ) * W * env "g") * hU2 + (Gq * Lam * W * env "g") * hZ

end Proofs

end OSR.IntegrationRec112
