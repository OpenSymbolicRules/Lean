import OSR.IntegrationRec91
import OSR.IntegrationRec138

/-!
# Integration (RUBI): `artanh(a + b f^(c + d x))` split into logarithms

`artanh u = (log(1 + u) - log(1 - u))/2` on `(-1, 1)`.  7.3.4 #7, #9 and
7.3.7 #7, #9 (miscellaneous inverse hyperbolic tangent) are proved over ℝ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec149

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 7.3.4 #7 -/
def rubi734mr7 : CRule where
  id := "integration.rubi_7_3_4_misc_r7"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:7"
  shape := .antiderivRec; x := "x"
  body := (.app1 .arctanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "f") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app1 .ln (.app2 .add (.app2 .add (.int 1) (.var "a")) (.app2 .mul (.var "b") (.pow (.var "f") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))))),
    ("I2", (.app1 .ln (.app2 .add (.app2 .add (.int 1) (.app2 .mul (.int (-1)) (.var "a"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "f") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "f"]
  priority := 11831
  description := "RUBI 7.3.4 #7"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:7" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent.m#7"

/-- RUBI 7.3.4 #9 -/
def rubi734mr9 : CRule where
  id := "integration.rubi_7_3_4_misc_r9"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.app1 .arctanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "f") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.app1 .ln (.app2 .add (.app2 .add (.int 1) (.var "a")) (.app2 .mul (.var "b") (.pow (.var "f") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))))),
    ("I2", (.app2 .mul (.pow (.var "x") (.var "m")) (.app1 .ln (.app2 .add (.app2 .add (.int 1) (.app2 .mul (.int (-1)) (.var "a"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "f") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))))))]
  independent := ["a", "b", "c", "d", "f", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0)]
  priority := 11832
  description := "RUBI 7.3.4 #9"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:9" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent.m#9"

/-- RUBI 7.3.7 #7 -/
def rubi737r7 : CRule where
  id := "integration.rubi_7_3_7_r7"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:7"
  shape := .antiderivRec; x := "x"
  body := (.app1 .arctanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "f") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app1 .ln (.app2 .add (.app2 .add (.int 1) (.var "a")) (.app2 .mul (.var "b") (.pow (.var "f") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))))),
    ("I2", (.app1 .ln (.app2 .add (.app2 .add (.int 1) (.app2 .mul (.int (-1)) (.var "a"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "f") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "f"]
  priority := 11833
  description := "RUBI 7.3.7 #7"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:7" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent.m#7"

/-- RUBI 7.3.7 #9 -/
def rubi737r9 : CRule where
  id := "integration.rubi_7_3_7_r9"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.app1 .arctanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "f") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.app1 .ln (.app2 .add (.app2 .add (.int 1) (.var "a")) (.app2 .mul (.var "b") (.pow (.var "f") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))))),
    ("I2", (.app2 .mul (.pow (.var "x") (.var "m")) (.app1 .ln (.app2 .add (.app2 .add (.int 1) (.app2 .mul (.int (-1)) (.var "a"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "f") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))))))]
  independent := ["a", "b", "c", "d", "f", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0)]
  priority := 11834
  description := "RUBI 7.3.7 #9"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:9" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent.m#9"

/-! ## Proofs -/

theorem rubi734mr7_real : rubi734mr7.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734mr7.conditions rubi734mr7.body rubi734mr7.result rubi734mr7.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734mr7, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    rcases hq : intValue? (env "c" + env "d" * w) with _ | q <;>
    simp [rubi734mr7, Defined, eval, Interp.real, i2, im1, hq] at hw ⊢ <;>
    first | (refine ⟨?_, ?_⟩ <;> first | tauto | linarith | (refine ⟨by tauto, ?_⟩; linarith)) | (constructor <;> first | tauto | linarith) | linarith | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi734mr7, Defined, eval, recEnv, Interp.real, i2, im1]
  · simp only [rubi734mr7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi734mr7.integrals.map (·.1)) Φ "x" w) rubi734mr7.result) =
        fun w => 1 / 2 * Φ "I1" w - 1 / 2 * Φ "I2" w := by
      funext w; simp [rubi734mr7, eval, recEnv, Interp.real, i2, im1]; ring
    rw [hfun]
    refine ((hΦ1.const_mul (1 / 2)).sub (hΦ2.const_mul (1 / 2))).congr_deriv ?_
    have ht := hF.self_of_nhds
    rcases hq : intValue? (env "c" + env "d" * t) with _ | q <;>
    simp [rubi734mr7, Defined, eval, Interp.real, i2, im1, hq] at ht ⊢
    have h1 : -1 < env "a" + env "b" * env "f" ^ q := by tauto
    have h2 : env "a" + env "b" * env "f" ^ q < 1 := by tauto
    rw [OSR.IntegrationRec138.artanh_split _ h1 h2, show 1 + env "a" + env "b" * env "f" ^ q = 1 + (env "a" + env "b" * env "f" ^ q) by ring,
      show 1 + -env "a" + -(env "b" * env "f" ^ q) = 1 - (env "a" + env "b" * env "f" ^ q) by ring]
    ring

theorem rubi734mr9_real : rubi734mr9.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734mr9.conditions rubi734mr9.body rubi734mr9.result rubi734mr9.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi734mr9, Defined, eval, Interp.real, hk_m] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734mr9, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    rcases hq : intValue? (env "c" + env "d" * w) with _ | q <;>
    simp [rubi734mr9, Defined, eval, Interp.real, i2, im1, hk_m, hq] at hw ⊢ <;>
    first | (refine ⟨?_, ?_⟩ <;> first | tauto | linarith | (refine ⟨by tauto, ?_⟩; linarith)) | (constructor <;> first | tauto | linarith) | linarith | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi734mr9, Defined, eval, recEnv, Interp.real, i2, im1]
  · simp only [rubi734mr9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi734mr9.integrals.map (·.1)) Φ "x" w) rubi734mr9.result) =
        fun w => 1 / 2 * Φ "I1" w - 1 / 2 * Φ "I2" w := by
      funext w; simp [rubi734mr9, eval, recEnv, Interp.real, i2, im1]; ring
    rw [hfun]
    refine ((hΦ1.const_mul (1 / 2)).sub (hΦ2.const_mul (1 / 2))).congr_deriv ?_
    have ht := hF.self_of_nhds
    rcases hq : intValue? (env "c" + env "d" * t) with _ | q <;>
    simp [rubi734mr9, Defined, eval, Interp.real, i2, im1, hk_m, hq] at ht ⊢
    have h1 : -1 < env "a" + env "b" * env "f" ^ q := by tauto
    have h2 : env "a" + env "b" * env "f" ^ q < 1 := by tauto
    rw [OSR.IntegrationRec138.artanh_split _ h1 h2, show 1 + env "a" + env "b" * env "f" ^ q = 1 + (env "a" + env "b" * env "f" ^ q) by ring,
      show 1 + -env "a" + -(env "b" * env "f" ^ q) = 1 - (env "a" + env "b" * env "f" ^ q) by ring]
    ring

theorem rubi737r7_real : rubi737r7.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi737r7.conditions rubi737r7.body rubi737r7.result rubi737r7.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi737r7, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    rcases hq : intValue? (env "c" + env "d" * w) with _ | q <;>
    simp [rubi737r7, Defined, eval, Interp.real, i2, im1, hq] at hw ⊢ <;>
    first | (refine ⟨?_, ?_⟩ <;> first | tauto | linarith | (refine ⟨by tauto, ?_⟩; linarith)) | (constructor <;> first | tauto | linarith) | linarith | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi737r7, Defined, eval, recEnv, Interp.real, i2, im1]
  · simp only [rubi737r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi737r7.integrals.map (·.1)) Φ "x" w) rubi737r7.result) =
        fun w => 1 / 2 * Φ "I1" w - 1 / 2 * Φ "I2" w := by
      funext w; simp [rubi737r7, eval, recEnv, Interp.real, i2, im1]; ring
    rw [hfun]
    refine ((hΦ1.const_mul (1 / 2)).sub (hΦ2.const_mul (1 / 2))).congr_deriv ?_
    have ht := hF.self_of_nhds
    rcases hq : intValue? (env "c" + env "d" * t) with _ | q <;>
    simp [rubi737r7, Defined, eval, Interp.real, i2, im1, hq] at ht ⊢
    have h1 : -1 < env "a" + env "b" * env "f" ^ q := by tauto
    have h2 : env "a" + env "b" * env "f" ^ q < 1 := by tauto
    rw [OSR.IntegrationRec138.artanh_split _ h1 h2, show 1 + env "a" + env "b" * env "f" ^ q = 1 + (env "a" + env "b" * env "f" ^ q) by ring,
      show 1 + -env "a" + -(env "b" * env "f" ^ q) = 1 - (env "a" + env "b" * env "f" ^ q) by ring]
    ring

theorem rubi737r9_real : rubi737r9.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi737r9.conditions rubi737r9.body rubi737r9.result rubi737r9.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi737r9, Defined, eval, Interp.real, hk_m] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi737r9, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    rcases hq : intValue? (env "c" + env "d" * w) with _ | q <;>
    simp [rubi737r9, Defined, eval, Interp.real, i2, im1, hk_m, hq] at hw ⊢ <;>
    first | (refine ⟨?_, ?_⟩ <;> first | tauto | linarith | (refine ⟨by tauto, ?_⟩; linarith)) | (constructor <;> first | tauto | linarith) | linarith | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi737r9, Defined, eval, recEnv, Interp.real, i2, im1]
  · simp only [rubi737r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi737r9.integrals.map (·.1)) Φ "x" w) rubi737r9.result) =
        fun w => 1 / 2 * Φ "I1" w - 1 / 2 * Φ "I2" w := by
      funext w; simp [rubi737r9, eval, recEnv, Interp.real, i2, im1]; ring
    rw [hfun]
    refine ((hΦ1.const_mul (1 / 2)).sub (hΦ2.const_mul (1 / 2))).congr_deriv ?_
    have ht := hF.self_of_nhds
    rcases hq : intValue? (env "c" + env "d" * t) with _ | q <;>
    simp [rubi737r9, Defined, eval, Interp.real, i2, im1, hk_m, hq] at ht ⊢
    have h1 : -1 < env "a" + env "b" * env "f" ^ q := by tauto
    have h2 : env "a" + env "b" * env "f" ^ q < 1 := by tauto
    rw [OSR.IntegrationRec138.artanh_split _ h1 h2, show 1 + env "a" + env "b" * env "f" ^ q = 1 + (env "a" + env "b" * env "f" ^ q) by ring,
      show 1 + -env "a" + -(env "b" * env "f" ^ q) = 1 - (env "a" + env "b" * env "f" ^ q) by ring]
    ring

end OSR.IntegrationRec149
