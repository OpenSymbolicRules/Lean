import OSR.IntegrationRec91

/-!
# Integration (RUBI): refutations of 4.7.9 #94 and #95

`sec(a + b x) sec(c + d x)` and `csc(a + b x) csc(c + d x)` with `b² = d²` and
`b c - a d ≠ 0` are rewritten with `csc((b c - a d)/d)` and `csc((b c - a d)/b)`.
At `a = 0`, `b = d = 1`, `c = π` the conditions hold and the integrand is defined
near `x = 0` (resp. `x = 1`), but `csc π` is not.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec154

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 4.7.9 #94 -/
def rubi479r94 : CRule where
  id := "integration.rubi_4_7_9_r94"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:94"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .sec (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app1 .sec (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .csc (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "d") (.int (-1)))))) (.var "I1")) (.app2 .mul (.app1 .csc (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "b") (.int (-1))))) (.var "I2")))
  integrals := [("I1", (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))),
    ("I2", (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 11855
  description := "RUBI 4.7.9 #94"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:94" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#94"

/-- RUBI 4.7.9 #95 -/
def rubi479r95 : CRule where
  id := "integration.rubi_4_7_9_r95"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:95"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .csc (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app1 .csc (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.app2 .add (.app2 .mul (.app1 .csc (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "b") (.int (-1))))) (.var "I1")) (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .csc (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "d") (.int (-1)))))) (.var "I2")))
  integrals := [("I1", (.app1 .cot (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))),
    ("I2", (.app1 .cot (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 11856
  description := "RUBI 4.7.9 #95"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:95" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#95"

/-! ## Refutations -/

theorem rubi479r94_counterexample_real : ¬ rubi479r94.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi479r94.conditions rubi479r94.body rubi479r94.result rubi479r94.integrals
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h0 : Real.cos (0 : ℝ) ≠ 0 := by simp
  have hev : ∀ᶠ v in 𝓝 (0 : ℝ), Real.cos v ≠ 0 :=
    (Real.continuous_cos.continuousAt).eventually_ne h0
  refine not_antiderivRecHolds_result (fun s => if s = "c" then Real.pi else if s = "b" ∨ s = "d" then 1 else 0) (0 : ℝ) ?_ ?_
    (fun h w => w * (((rubi479r94.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then Real.pi else if s = "b" ∨ s = "d" then 1 else 0) "x" (0 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi479r94, Cond.Holds, Defined, eval, Interp.real, i2, im1, Real.pi_ne_zero]
  · filter_upwards [hev] with v hv
    simp [rubi479r94, Defined, eval, Interp.real, i2, im1]
    first
      | (exact ⟨hv, by rw [add_comm, Real.cos_add_pi]; simpa using hv⟩)
      | (refine ⟨hv, ?_⟩; rw [add_comm, Real.cos_add_pi]; simpa using hv)
      | (trace_state; sorry)
  · simp only [rubi479r94, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    exact ⟨hasDerivAt_mul_const _, hasDerivAt_mul_const _⟩
  · intro h
    simp [rubi479r94, Defined, eval, Interp.real, i2, im1, recEnv] at h

theorem rubi479r95_counterexample_real : ¬ rubi479r95.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi479r95.conditions rubi479r95.body rubi479r95.result rubi479r95.integrals
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h0 : Real.sin (1 : ℝ) ≠ 0 := by exact (Real.sin_pos_of_pos_of_lt_pi one_pos (by linarith [Real.pi_gt_three])).ne'
  have hev : ∀ᶠ v in 𝓝 (1 : ℝ), Real.sin v ≠ 0 :=
    (Real.continuous_sin.continuousAt).eventually_ne h0
  refine not_antiderivRecHolds_result (fun s => if s = "c" then Real.pi else if s = "b" ∨ s = "d" then 1 else 0) (1 : ℝ) ?_ ?_
    (fun h w => w * (((rubi479r95.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then Real.pi else if s = "b" ∨ s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi479r95, Cond.Holds, Defined, eval, Interp.real, i2, im1, Real.pi_ne_zero]
  · filter_upwards [hev] with v hv
    simp [rubi479r95, Defined, eval, Interp.real, i2, im1]
    first
      | (exact ⟨hv, by rw [add_comm, Real.sin_add_pi]; simpa using hv⟩)
      | (refine ⟨hv, ?_⟩; rw [add_comm, Real.sin_add_pi]; simpa using hv)
      | (trace_state; sorry)
  · simp only [rubi479r95, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    exact ⟨hasDerivAt_mul_const _, hasDerivAt_mul_const _⟩
  · intro h
    simp [rubi479r95, Defined, eval, Interp.real, i2, im1, recEnv] at h

end OSR.IntegrationRec154
