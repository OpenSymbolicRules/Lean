import OSR.IntegrationRec91

/-!
# Integration (RUBI): refutations of rules not considered before

RUBI rules transcribed as stated.  Each is refuted by an explicit assignment:
the conditions hold and the integrand is defined near a point where the
result or a residual integrand is not (RUBI excludes these cases by its rule
order).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec167

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/









/-- RUBI 7.2.5 #17 -/
def rubi725r17 : CRule where
  id := "integration.rubi_7_2_5_r17"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.5 u (a+b arccosh(c x))^n:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "h") (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "d1") (.app2 .mul (.var "e1") (.var "x"))) (.int 2)) (.app2 .root (.app2 .add (.var "d2") (.app2 .mul (.var "e2") (.var "x"))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "h") (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.app2 .mul (.app2 .mul (.int (-1)) (.var "d1")) (.var "d2")) (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "g")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.app2 .mul (.app2 .mul (.int (-1)) (.var "d1")) (.var "d2")) (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d1", "e1", "d2", "e2", "f", "g", "h", "m", "n"]
  conditions := [.eq (.app2 .add (.var "e1") (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d1"))) (.int 0),
    .eq (.app2 .add (.var "e2") (.app2 .mul (.var "c") (.var "d2"))) (.int 0),
    .gt (.var "d1") (.int 0),
    .gt (.int 0) (.var "d2"),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 11998
  description := "RUBI 7.2.5 #17"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.5 u (a+b arccosh(c x))^n:17" "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.5 u (a+b arccosh(c x))^n.m#17"


/-! ## Refutations -/

theorem rubi725r17_counterexample_real : ¬ rubi725r17.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi725r17.conditions rubi725r17.body rubi725r17.result rubi725r17.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-3 : ℝ) else if s = "c" then (-1 : ℝ) else if s = "d1" then ((1 : ℝ) / 2) else if s = "d2" then ((-1 : ℝ) / 2) else if s = "e1" then ((-1 : ℝ) / 2) else if s = "e2" then ((-1 : ℝ) / 2) else if s = "f" then (4 : ℝ) else if s = "g" then (3 : ℝ) else if s = "h" then (4 : ℝ) else if s = "n" then (2 : ℝ) else 0) (-2 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi725r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (-2 : ℝ) - 1/16 < -2 by norm_num) (show (-2 : ℝ) < -2 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi725r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi725r17.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-3 : ℝ) else if s = "c" then (-1 : ℝ) else if s = "d1" then ((1 : ℝ) / 2) else if s = "d2" then ((-1 : ℝ) / 2) else if s = "e1" then ((-1 : ℝ) / 2) else if s = "e2" then ((-1 : ℝ) / 2) else if s = "f" then (4 : ℝ) else if s = "g" then (3 : ℝ) else if s = "h" then (4 : ℝ) else if s = "n" then (2 : ℝ) else 0) "x" (-2 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi725r17, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi725r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi725r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

end OSR.IntegrationRec167
