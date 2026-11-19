import OSR.IntegrationRec91

/-!
# Integration (RUBI): refutations of 4.7.6 #4, #5 and 6.7.6 #4

`(c + d x)^m cos^n(a + b x) cot^p(a + b x)` is split into residual integrands
with `cos^(n - 2)` and `cot^(p - 2)`.  At `n = 1`, `p = 2`, `a = c = d = m = 0`,
`b = 1` the integrand `cos x cot² x` is defined near `x = π/2`, but the
residual integrand `cos^(-1) x cot² x` is not defined at `x = π/2`.  In the
same way 4.7.6 #4 (`sin^n tan^p`) and 6.7.6 #4 (`sinh^n tanh^p`) leave
`sin^(-1) x` (`sinh^(-1) x`) in a residual integrand at `x = 0`.  Refuted over
ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec157

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 4.7.6 #5 -/
def rubi476r5 : CRule where
  id := "integration.rubi_4_7_6_r5"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app1 .cot (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.int (-1)) (.var "I1")) (.var "I2"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app1 .cot (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.pow (.app1 .cot (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 11870
  description := "RUBI 4.7.6 #5"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:5" "4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p.m#5"

/-- RUBI 4.7.6 #4 -/
def rubi476r4 : CRule where
  id := "integration.rubi_4_7_6_r4"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.int (-1)) (.var "I1")) (.var "I2"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.pow (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 11871
  description := "RUBI 4.7.6 #4"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:4" "4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p.m#4"

/-- RUBI 6.7.6 #4 -/
def rubi676r4 : CRule where
  id := "integration.rubi_6_7_6_r4"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app1 .tanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p")))
  result := (.app2 .add (.var "I1") (.app2 .mul (.int (-1)) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app1 .tanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.pow (.app1 .tanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 11872
  description := "RUBI 6.7.6 #4"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:4" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p.m#4"

/-! ## Refutations -/

theorem rubi476r5_counterexample_real : ¬ rubi476r5.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi476r5.conditions rubi476r5.body rubi476r5.result rubi476r5.integrals
  have i1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have hs : Real.sin (Real.pi / 2 : ℝ) ≠ 0 := by rw [Real.sin_pi_div_two]; norm_num
  have hc0 : Real.cos (Real.pi / 2 : ℝ) = 0 := by exact Real.cos_pi_div_two
  have hev : ∀ᶠ v in 𝓝 (Real.pi / 2 : ℝ), Real.sin v ≠ 0 := (Real.continuous_sin.continuousAt).eventually_ne hs
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "n" then 1 else if s = "p" then 2 else 0) (Real.pi / 2 : ℝ) ?_ ?_ ?_
  · simp [rubi476r5, Cond.Holds, Defined, eval, Interp.real, i0, i1, i2, im1]
  · filter_upwards [hev] with v hv
    simp [rubi476r5, Defined, eval, Interp.real, i0, i1, i2, im1]
    first | exact hv | skip
  · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    simp [rubi476r5, Defined, eval, Interp.real, i0, i1, i2, im1, hc0]
    intro k hk
    rw [show (1 : ℝ) + -2 = -1 by norm_num, im1] at hk
    cases hk; norm_num

theorem rubi476r5_counterexample_complex : ¬ rubi476r5.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi476r5.conditions rubi476r5.body rubi476r5.result rubi476r5.integrals
  have i1 : intValue? (1 : ℂ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i0 : intValue? (0 : ℂ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have hs : Complex.sin ((Real.pi / 2 : ℝ) : ℂ) ≠ 0 := by rw [← Complex.ofReal_sin, Real.sin_pi_div_two]; norm_num
  have hc0 : Complex.cos ((Real.pi / 2 : ℝ) : ℂ) = 0 := by rw [← Complex.ofReal_cos, Real.cos_pi_div_two]; simp
  have hev : ∀ᶠ v in 𝓝 ((Real.pi / 2 : ℝ) : ℂ), Complex.sin v ≠ 0 := (Complex.continuous_sin.continuousAt).eventually_ne hs
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "n" then 1 else if s = "p" then 2 else 0) ((Real.pi / 2 : ℝ) : ℂ) ?_ ?_ ?_
  · simp [rubi476r5, Cond.Holds, Defined, eval, Interp.complex, i0, i1, i2, im1]
  · filter_upwards [hev] with v hv
    simp [rubi476r5, Defined, eval, Interp.complex, i0, i1, i2, im1]
    first | exact hv | skip
  · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    simp [rubi476r5, Defined, eval, Interp.complex, i0, i1, i2, im1, hc0]
    intro k hk
    rw [show (1 : ℂ) + -2 = -1 by norm_num, im1] at hk
    cases hk; norm_num

theorem rubi476r4_counterexample_real : ¬ rubi476r4.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi476r4.conditions rubi476r4.body rubi476r4.result rubi476r4.integrals
  have i1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have hc : Real.cos (0 : ℝ) ≠ 0 := by simp
  have hev : ∀ᶠ v in 𝓝 (0 : ℝ), Real.cos v ≠ 0 := (Real.continuous_cos.continuousAt).eventually_ne hc
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "n" then 1 else if s = "p" then 2 else 0) (0 : ℝ) ?_ ?_ ?_
  · simp [rubi476r4, Cond.Holds, Defined, eval, Interp.real, i0, i1, i2, im1]
  · filter_upwards [hev] with v hv
    simp [rubi476r4, Defined, eval, Interp.real, i0, i1, i2, im1, Real.tan_eq_sin_div_cos, Real.tanh_eq_sinh_div_cosh]
    first | exact hv | (intro h; exact hv h) | skip
  · first
      | (refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
         simp [rubi476r4, Defined, eval, Interp.real, i0, i1, i2, im1]
         intro k hk
         rw [show (1 : ℝ) + -2 = -1 by norm_num, im1] at hk
         cases hk; norm_num)
      | (refine ⟨_, List.mem_cons_self, ?_⟩
         simp [rubi476r4, Defined, eval, Interp.real, i0, i1, i2, im1]
         intro k hk
         rw [show (1 : ℝ) + -2 = -1 by norm_num, im1] at hk
         cases hk; norm_num)
      | (trace_state; sorry)

theorem rubi476r4_counterexample_complex : ¬ rubi476r4.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi476r4.conditions rubi476r4.body rubi476r4.result rubi476r4.integrals
  have i1 : intValue? (1 : ℂ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i0 : intValue? (0 : ℂ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have hc : Complex.cos (0 : ℂ) ≠ 0 := by simp
  have hev : ∀ᶠ v in 𝓝 (0 : ℂ), Complex.cos v ≠ 0 := (Complex.continuous_cos.continuousAt).eventually_ne hc
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "n" then 1 else if s = "p" then 2 else 0) (0 : ℂ) ?_ ?_ ?_
  · simp [rubi476r4, Cond.Holds, Defined, eval, Interp.complex, i0, i1, i2, im1]
  · filter_upwards [hev] with v hv
    simp [rubi476r4, Defined, eval, Interp.complex, i0, i1, i2, im1]
    first | exact hv | (intro h; exact hv h) | skip
  · first
      | (refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
         simp [rubi476r4, Defined, eval, Interp.complex, i0, i1, i2, im1]
         intro k hk
         rw [show (1 : ℂ) + -2 = -1 by norm_num, im1] at hk
         cases hk; norm_num)
      | (refine ⟨_, List.mem_cons_self, ?_⟩
         simp [rubi476r4, Defined, eval, Interp.complex, i0, i1, i2, im1]
         intro k hk
         rw [show (1 : ℂ) + -2 = -1 by norm_num, im1] at hk
         cases hk; norm_num)
      | (trace_state; sorry)

theorem rubi676r4_counterexample_real : ¬ rubi676r4.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi676r4.conditions rubi676r4.body rubi676r4.result rubi676r4.integrals
  have i1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have hc : Real.cosh (0 : ℝ) ≠ 0 := by simp
  have hev : ∀ᶠ v in 𝓝 (0 : ℝ), Real.cosh v ≠ 0 := (Real.continuous_cosh.continuousAt).eventually_ne hc
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "n" then 1 else if s = "p" then 2 else 0) (0 : ℝ) ?_ ?_ ?_
  · simp [rubi676r4, Cond.Holds, Defined, eval, Interp.real, i0, i1, i2, im1]
  · filter_upwards [hev] with v hv
    simp [rubi676r4, Defined, eval, Interp.real, i0, i1, i2, im1, Real.tan_eq_sin_div_cos, Real.tanh_eq_sinh_div_cosh]
    first | exact hv | (intro h; exact hv h) | skip
  · first
      | (refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
         simp [rubi676r4, Defined, eval, Interp.real, i0, i1, i2, im1]
         intro k hk
         rw [show (1 : ℝ) + -2 = -1 by norm_num, im1] at hk
         cases hk; norm_num)
      | (refine ⟨_, List.mem_cons_self, ?_⟩
         simp [rubi676r4, Defined, eval, Interp.real, i0, i1, i2, im1]
         intro k hk
         rw [show (1 : ℝ) + -2 = -1 by norm_num, im1] at hk
         cases hk; norm_num)
      | (trace_state; sorry)

theorem rubi676r4_counterexample_complex : ¬ rubi676r4.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi676r4.conditions rubi676r4.body rubi676r4.result rubi676r4.integrals
  have i1 : intValue? (1 : ℂ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i0 : intValue? (0 : ℂ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have hc : Complex.cosh (0 : ℂ) ≠ 0 := by simp
  have hev : ∀ᶠ v in 𝓝 (0 : ℂ), Complex.cosh v ≠ 0 := (Complex.continuous_cosh.continuousAt).eventually_ne hc
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "n" then 1 else if s = "p" then 2 else 0) (0 : ℂ) ?_ ?_ ?_
  · simp [rubi676r4, Cond.Holds, Defined, eval, Interp.complex, i0, i1, i2, im1]
  · filter_upwards [hev] with v hv
    simp [rubi676r4, Defined, eval, Interp.complex, i0, i1, i2, im1]
    first | exact hv | (intro h; exact hv h) | skip
  · first
      | (refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
         simp [rubi676r4, Defined, eval, Interp.complex, i0, i1, i2, im1]
         intro k hk
         rw [show (1 : ℂ) + -2 = -1 by norm_num, im1] at hk
         cases hk; norm_num)
      | (refine ⟨_, List.mem_cons_self, ?_⟩
         simp [rubi676r4, Defined, eval, Interp.complex, i0, i1, i2, im1]
         intro k hk
         rw [show (1 : ℂ) + -2 = -1 by norm_num, im1] at hk
         cases hk; norm_num)
      | (trace_state; sorry)

end OSR.IntegrationRec157
