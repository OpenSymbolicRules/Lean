import OSR.IntegrationRec91

/-!
# Integration (RUBI): arctanh split into logarithms

`artanh u = (log(1 + u) - log(1 - u))/2` for `-1 < u < 1` splits each integrand
into the two residual integrands.  Proved over ℝ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec138

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 7.3.4 #39 -/
def rubi734r39 : CRule where
  id := "integration.rubi_7_3_4_r39"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:39"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x")))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "x")))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["c", "d", "e"]
  priority := 11401
  description := "RUBI 7.3.4 #39"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:39" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#39"

/-- RUBI 7.3.1 #59 -/
def rubi731r59 : CRule where
  id := "integration.rubi_7_3_1_r59"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:59"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x")))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "x")))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["c", "d", "e"]
  priority := 11402
  description := "RUBI 7.3.1 #59"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:59" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#59"





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

/-- `artanh u = log(1 + u)/2 - log(1 - u)/2` on `(-1, 1)`. -/
theorem artanh_split (u : ℝ) (h1 : -1 < u) (h2 : u < 1) :
    Real.artanh u = 1 / 2 * Real.log (1 + u) - 1 / 2 * Real.log (1 - u) := by
  rw [Real.artanh_eq_half_log ⟨h1.le, h2.le⟩, Real.log_div (by linarith) (by linarith)]
  ring

theorem rubi734r39_real : rubi734r39.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r39.conditions rubi734r39.body rubi734r39.result rubi734r39.integrals
  intro env hc t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734r39, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;>
      simp [rubi734r39, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4] at hw ⊢ <;>
      repeat' (first | assumption | linarith | (constructor; done) | constructor | tauto | (trace_state; sorry))
  · exact Eventually.of_forall fun w => by simp [rubi734r39, Defined, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
  · simp only [rubi734r39, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hb := hF.self_of_nhds
    simp [rubi734r39, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4] at hb
    have hfun : (fun w => eval Interp.real (recEnv env (rubi734r39.integrals.map (·.1)) Φ "x" w) rubi734r39.result) =
        fun w => eval Interp.real env (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) * Φ "I1" w + eval Interp.real env (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) * Φ "I2" w := by
      funext w; simp [rubi734r39, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi734r39, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    rw [artanh_split]
    · ring_nf
    all_goals (first | tauto | linarith | (trace_state; sorry))

theorem rubi731r59_real : rubi731r59.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r59.conditions rubi731r59.body rubi731r59.result rubi731r59.integrals
  intro env hc t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r59, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;>
      simp [rubi731r59, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4] at hw ⊢ <;>
      repeat' (first | assumption | linarith | (constructor; done) | constructor | tauto | (trace_state; sorry))
  · exact Eventually.of_forall fun w => by simp [rubi731r59, Defined, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
  · simp only [rubi731r59, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hb := hF.self_of_nhds
    simp [rubi731r59, Defined, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4] at hb
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r59.integrals.map (·.1)) Φ "x" w) rubi731r59.result) =
        fun w => eval Interp.real env (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) * Φ "I1" w + eval Interp.real env (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) * Φ "I2" w := by
      funext w; simp [rubi731r59, eval, recEnv, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi731r59, eval, Interp.real, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    rw [artanh_split]
    · ring_nf
    all_goals (first | tauto | linarith | (trace_state; sorry))


end OSR.IntegrationRec138
