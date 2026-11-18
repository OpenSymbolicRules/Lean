import OSR.IntegrationRec91

/-!
# Integration (RUBI): linear splits with integer exponents

Rules whose result is a combination of residual integrals with constant
coefficients, the integrand being the same combination by linearity, by
`artanh u = (log(1 + u) - log(1 - u))/2`, or by the addition formulas of sinh
and cosh.  Proved over ℝ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec139

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 7.3.4 #107 -/
def rubi734r107 : CRule where
  id := "integration.rubi_7_3_4_r107"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:107"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.var "b") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "q"]
  priority := 11501
  description := "RUBI 7.3.4 #107"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:107" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#107"

/-- RUBI 7.3.1 #127 -/
def rubi731r127 : CRule where
  id := "integration.rubi_7_3_1_r127"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:127"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.var "b") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "q"]
  priority := 11502
  description := "RUBI 7.3.1 #127"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:127" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#127"

/-- RUBI 7.3.4 #130 -/
def rubi734r130 : CRule where
  id := "integration.rubi_7_3_4_r130"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:130"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "m")))) (.app1 .arctanh (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "m")))) (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "m")))) (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.pow (.var "x") (.var "n")))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["c", "d", "m", "n"]
  priority := 11503
  description := "RUBI 7.3.4 #130"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:130" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#130"

/-- RUBI 7.3.1 #150 -/
def rubi731r150 : CRule where
  id := "integration.rubi_7_3_1_r150"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:150"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "m")))) (.app1 .arctanh (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "m")))) (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "m")))) (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.pow (.var "x") (.var "n")))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["c", "d", "m", "n"]
  priority := 11504
  description := "RUBI 7.3.1 #150"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:150" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#150"

/-- RUBI 7.3.7 #3 -/
def rubi737r3 : CRule where
  id := "integration.rubi_7_3_7_r3"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .arctanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .add (.app2 .add (.int 1) (.var "a")) (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .ln (.app2 .add (.app2 .add (.int 1) (.app2 .mul (.int (-1)) (.var "a"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "x") (.var "n"))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "n"]
  priority := 11505
  description := "RUBI 7.3.7 #3"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:3" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent.m#3"

/-- RUBI 7.3.4 #3 -/
def rubi734mr3 : CRule where
  id := "integration.rubi_7_3_4_misc_r3"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .arctanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .add (.app2 .add (.int 1) (.var "a")) (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .ln (.app2 .add (.app2 .add (.int 1) (.app2 .mul (.int (-1)) (.var "a"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "x") (.var "n"))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "n"]
  priority := 11506
  description := "RUBI 7.3.4 #3"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:3" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent.m#3"

/-- RUBI 6.1.12 #19 -/
def rubi6112r19 : CRule where
  id := "integration.rubi_6_1_12_r19"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app1 .sinh (.var "c")) (.var "I1")) (.app2 .mul (.app1 .cosh (.var "c")) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .cosh (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .sinh (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.pow (.var "x") (.int (-1)))))]
  independent := ["c", "d", "n"]
  priority := 11507
  description := "RUBI 6.1.12 #19"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:19" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#19"

/-- RUBI 6.1.12 #20 -/
def rubi6112r20 : CRule where
  id := "integration.rubi_6_1_12_r20"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:20"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app1 .cosh (.var "c")) (.var "I1")) (.app2 .mul (.app1 .sinh (.var "c")) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .cosh (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .sinh (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.pow (.var "x") (.int (-1)))))]
  independent := ["c", "d", "n"]
  priority := 11508
  description := "RUBI 6.1.12 #20"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:20" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#20"

/-! ## Proofs -/

private theorem ti0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
private theorem ti1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ti2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
private theorem ti3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
private theorem ti4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
private theorem tim1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem tim2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
private theorem tim3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
private theorem tim4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)

private theorem artanh_split' (u : ℝ) (h1 : -1 < u) (h2 : u < 1) :
    Real.artanh u = 1 / 2 * Real.log (1 + u) - 1 / 2 * Real.log (1 - u) := by
  rw [Real.artanh_eq_half_log ⟨h1.le, h2.le⟩, Real.log_div (by linarith) (by linarith)]
  ring

theorem rubi734r107_real : rubi734r107.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r107.conditions rubi734r107.body rubi734r107.result rubi734r107.integrals
  intro env hc t hF
  rcases hk_m : intValue? (env "m") with _ | k_m
  · exfalso; have h := hF.self_of_nhds; simp [rubi734r107, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m] at h
  rcases hk_q : intValue? (env "q") with _ | k_q
  · exfalso; have h := hF.self_of_nhds; simp [rubi734r107, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_q] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734r107, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;>
      simp [rubi734r107, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_q] at hw ⊢ <;>
      repeat' (first | assumption | linarith | (constructor; done) | constructor | tauto | (trace_state; sorry))
  · exact Eventually.of_forall fun w => by simp [rubi734r107, Defined, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_q]
  · simp only [rubi734r107, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hb := hF.self_of_nhds
    simp [rubi734r107, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_q] at hb
    have hfun : (fun w => eval Interp.real (recEnv env (rubi734r107.integrals.map (·.1)) Φ "x" w) rubi734r107.result) =
        fun w => eval Interp.real env (.var "a") * Φ "I1" w + eval Interp.real env (.var "b") * Φ "I2" w := by
      funext w; simp [rubi734r107, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_q]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi734r107, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_q]
    first | ring1 | ring_nf | (trace_state; sorry)

theorem rubi731r127_real : rubi731r127.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r127.conditions rubi731r127.body rubi731r127.result rubi731r127.integrals
  intro env hc t hF
  rcases hk_m : intValue? (env "m") with _ | k_m
  · exfalso; have h := hF.self_of_nhds; simp [rubi731r127, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m] at h
  rcases hk_q : intValue? (env "q") with _ | k_q
  · exfalso; have h := hF.self_of_nhds; simp [rubi731r127, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_q] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r127, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;>
      simp [rubi731r127, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_q] at hw ⊢ <;>
      repeat' (first | assumption | linarith | (constructor; done) | constructor | tauto | (trace_state; sorry))
  · exact Eventually.of_forall fun w => by simp [rubi731r127, Defined, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_q]
  · simp only [rubi731r127, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hb := hF.self_of_nhds
    simp [rubi731r127, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_q] at hb
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r127.integrals.map (·.1)) Φ "x" w) rubi731r127.result) =
        fun w => eval Interp.real env (.var "a") * Φ "I1" w + eval Interp.real env (.var "b") * Φ "I2" w := by
      funext w; simp [rubi731r127, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_q]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi731r127, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_q]
    first | ring1 | ring_nf | (trace_state; sorry)

theorem rubi734r130_real : rubi734r130.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r130.conditions rubi734r130.body rubi734r130.result rubi734r130.integrals
  intro env hc t hF
  rcases hk_m : intValue? (env "m") with _ | k_m
  · exfalso; have h := hF.self_of_nhds; simp [rubi734r130, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | k_n
  · exfalso; have h := hF.self_of_nhds; simp [rubi734r130, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_n] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734r130, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;>
      simp [rubi734r130, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_n] at hw ⊢ <;>
      repeat' (first | assumption | linarith | (constructor; done) | constructor | tauto | (trace_state; sorry))
  · exact Eventually.of_forall fun w => by simp [rubi734r130, Defined, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_n]
  · simp only [rubi734r130, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hb := hF.self_of_nhds
    simp [rubi734r130, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_n] at hb
    have hfun : (fun w => eval Interp.real (recEnv env (rubi734r130.integrals.map (·.1)) Φ "x" w) rubi734r130.result) =
        fun w => eval Interp.real env (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) * Φ "I1" w + eval Interp.real env (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) * Φ "I2" w := by
      funext w; simp [rubi734r130, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_n]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi734r130, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_n]
    rw [artanh_split']
    · ring_nf
    all_goals (first | tauto | linarith | (trace_state; sorry))

theorem rubi731r150_real : rubi731r150.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r150.conditions rubi731r150.body rubi731r150.result rubi731r150.integrals
  intro env hc t hF
  rcases hk_m : intValue? (env "m") with _ | k_m
  · exfalso; have h := hF.self_of_nhds; simp [rubi731r150, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | k_n
  · exfalso; have h := hF.self_of_nhds; simp [rubi731r150, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_n] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r150, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;>
      simp [rubi731r150, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_n] at hw ⊢ <;>
      repeat' (first | assumption | linarith | (constructor; done) | constructor | tauto | (trace_state; sorry))
  · exact Eventually.of_forall fun w => by simp [rubi731r150, Defined, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_n]
  · simp only [rubi731r150, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hb := hF.self_of_nhds
    simp [rubi731r150, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_n] at hb
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r150.integrals.map (·.1)) Φ "x" w) rubi731r150.result) =
        fun w => eval Interp.real env (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) * Φ "I1" w + eval Interp.real env (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) * Φ "I2" w := by
      funext w; simp [rubi731r150, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_n]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi731r150, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_m, hk_n]
    rw [artanh_split']
    · ring_nf
    all_goals (first | tauto | linarith | (trace_state; sorry))

theorem rubi737r3_real : rubi737r3.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi737r3.conditions rubi737r3.body rubi737r3.result rubi737r3.integrals
  intro env hc t hF
  rcases hk_n : intValue? (env "n") with _ | k_n
  · exfalso; have h := hF.self_of_nhds; simp [rubi737r3, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi737r3, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;>
      simp [rubi737r3, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n] at hw ⊢ <;>
      repeat' (first | assumption | linarith | (constructor; done) | constructor | tauto | (trace_state; sorry))
  · exact Eventually.of_forall fun w => by simp [rubi737r3, Defined, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n]
  · simp only [rubi737r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hb := hF.self_of_nhds
    simp [rubi737r3, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n] at hb
    have hfun : (fun w => eval Interp.real (recEnv env (rubi737r3.integrals.map (·.1)) Φ "x" w) rubi737r3.result) =
        fun w => eval Interp.real env (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) * Φ "I1" w + eval Interp.real env (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) * Φ "I2" w := by
      funext w; simp [rubi737r3, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi737r3, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n]
    rw [artanh_split']
    · ring_nf
    all_goals (first | tauto | linarith | (trace_state; sorry))

theorem rubi734mr3_real : rubi734mr3.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734mr3.conditions rubi734mr3.body rubi734mr3.result rubi734mr3.integrals
  intro env hc t hF
  rcases hk_n : intValue? (env "n") with _ | k_n
  · exfalso; have h := hF.self_of_nhds; simp [rubi734mr3, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734mr3, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;>
      simp [rubi734mr3, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n] at hw ⊢ <;>
      repeat' (first | assumption | linarith | (constructor; done) | constructor | tauto | (trace_state; sorry))
  · exact Eventually.of_forall fun w => by simp [rubi734mr3, Defined, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n]
  · simp only [rubi734mr3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hb := hF.self_of_nhds
    simp [rubi734mr3, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n] at hb
    have hfun : (fun w => eval Interp.real (recEnv env (rubi734mr3.integrals.map (·.1)) Φ "x" w) rubi734mr3.result) =
        fun w => eval Interp.real env (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) * Φ "I1" w + eval Interp.real env (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) * Φ "I2" w := by
      funext w; simp [rubi734mr3, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi734mr3, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n]
    rw [artanh_split']
    · ring_nf
    all_goals (first | tauto | linarith | (trace_state; sorry))

theorem rubi6112r19_real : rubi6112r19.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6112r19.conditions rubi6112r19.body rubi6112r19.result rubi6112r19.integrals
  intro env hc t hF
  rcases hk_n : intValue? (env "n") with _ | k_n
  · exfalso; have h := hF.self_of_nhds; simp [rubi6112r19, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r19, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;>
      simp [rubi6112r19, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n] at hw ⊢ <;>
      repeat' (first | assumption | linarith | (constructor; done) | constructor | tauto | (trace_state; sorry))
  · exact Eventually.of_forall fun w => by simp [rubi6112r19, Defined, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n]
  · simp only [rubi6112r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hb := hF.self_of_nhds
    simp [rubi6112r19, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n] at hb
    have hfun : (fun w => eval Interp.real (recEnv env (rubi6112r19.integrals.map (·.1)) Φ "x" w) rubi6112r19.result) =
        fun w => eval Interp.real env (.app1 .sinh (.var "c")) * Φ "I1" w + eval Interp.real env (.app1 .cosh (.var "c")) * Φ "I2" w := by
      funext w; simp [rubi6112r19, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi6112r19, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n]
    simp only [Real.sinh_add, Real.cosh_add]
    ring

theorem rubi6112r20_real : rubi6112r20.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6112r20.conditions rubi6112r20.body rubi6112r20.result rubi6112r20.integrals
  intro env hc t hF
  rcases hk_n : intValue? (env "n") with _ | k_n
  · exfalso; have h := hF.self_of_nhds; simp [rubi6112r20, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r20, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;>
      simp [rubi6112r20, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n] at hw ⊢ <;>
      repeat' (first | assumption | linarith | (constructor; done) | constructor | tauto | (trace_state; sorry))
  · exact Eventually.of_forall fun w => by simp [rubi6112r20, Defined, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n]
  · simp only [rubi6112r20, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hb := hF.self_of_nhds
    simp [rubi6112r20, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n] at hb
    have hfun : (fun w => eval Interp.real (recEnv env (rubi6112r20.integrals.map (·.1)) Φ "x" w) rubi6112r20.result) =
        fun w => eval Interp.real env (.app1 .cosh (.var "c")) * Φ "I1" w + eval Interp.real env (.app1 .sinh (.var "c")) * Φ "I2" w := by
      funext w; simp [rubi6112r20, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi6112r20, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4, hk_n]
    simp only [Real.sinh_add, Real.cosh_add]
    ring


end OSR.IntegrationRec139
