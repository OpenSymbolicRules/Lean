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

namespace OSR.IntegrationRec165

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 3.2.3 #9 -/
def rubi323r9 : CRule where
  id := "integration.rubi_3_2_3_r9"; legacyId := some "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "s") (.app2 .mul (.var "t") (.app1 .ln (.app2 .mul (.var "i") (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "n")))))) (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r"))))) (.pow (.app2 .add (.var "j") (.app2 .mul (.var "k") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .add (.app2 .add (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.app2 .mul (.int (-1)) (.app1 .ln (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "p") (.var "r")))))) (.app2 .mul (.int (-1)) (.app1 .ln (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .mul (.var "q") (.var "r")))))) (.var "I1")) (.var "I2")) (.var "I3"))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "s") (.app2 .mul (.var "t") (.app1 .ln (.app2 .mul (.var "i") (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "n")))))) (.pow (.app2 .add (.var "j") (.app2 .mul (.var "k") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "p") (.var "r")))) (.app2 .add (.var "s") (.app2 .mul (.var "t") (.app1 .ln (.app2 .mul (.var "i") (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "n"))))))) (.pow (.app2 .add (.var "j") (.app2 .mul (.var "k") (.var "x"))) (.int (-1))))),
    ("I3", (.app2 .mul (.app2 .mul (.app1 .ln (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .mul (.var "q") (.var "r")))) (.app2 .add (.var "s") (.app2 .mul (.var "t") (.app1 .ln (.app2 .mul (.var "i") (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "n"))))))) (.pow (.app2 .add (.var "j") (.app2 .mul (.var "k") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "s", "t", "n", "p", "q", "r"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 11930
  description := "RUBI 3.2.3 #9"
  provenance := migrated "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:9" "3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s.m#9"

/-- RUBI 3.4 #1 -/
def rubi34r1 : CRule where
  id := "integration.rubi_3_4_r1"; legacyId := some "rubi:3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "p"))))
  result := (.app2 .add (.app2 .mul (.var "x") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "p"))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "n")) (.var "p")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "n")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.int (-1)))))]
  independent := ["c", "d", "e", "n", "p"]
  priority := 11931
  description := "RUBI 3.4 #1"
  provenance := migrated "rubi:3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p:1" "3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p.m#1"

/-- RUBI 3.5 #1 -/
def rubi35r1 : CRule where
  id := "integration.rubi_3_5_r1"; legacyId := some "rubi:3 Logarithms/3.5 Miscellaneous logarithms:1"
  shape := .antiderivRec; x := "x"
  body := (.app1 .ln (.app2 .mul (.var "c") (.pow (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "p"))))
  result := (.app2 .add (.app2 .mul (.var "x") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "p"))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "n")) (.var "p")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.int (-1)))))]
  independent := ["c", "d", "n", "p"]
  priority := 11932
  description := "RUBI 3.5 #1"
  provenance := migrated "rubi:3 Logarithms/3.5 Miscellaneous logarithms:1" "3 Logarithms/3.5 Miscellaneous logarithms.m#1"

/-! ## Refutations -/

theorem rubi323r9_counterexample_real : ¬ rubi323r9.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi323r9.conditions rubi323r9.body rubi323r9.result rubi323r9.integrals
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
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then (-1 : ℝ) else if s = "c" then (-2 : ℝ) else if s = "d" then (1 : ℝ) else if s = "e" then (2 : ℝ) else if s = "f" then (-1 : ℝ) else if s = "h" then (-1 : ℝ) else if s = "i" then (3 : ℝ) else if s = "j" then (1 : ℝ) else if s = "p" then (3 : ℝ) else if s = "r" then (1 : ℝ) else if s = "s" then (3 : ℝ) else if s = "t" then (1 : ℝ) else 0) (1 : ℝ) ?_ (Eventually.of_forall fun w => by simp [rubi323r9, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))) ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
  · simp [rubi323r9, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi323r9, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi34r1_counterexample_real : ¬ rubi34r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi34r1.conditions rubi34r1.body rubi34r1.result rubi34r1.integrals
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
  refine not_antiderivRecHolds_integrand (fun s => if s = "c" then (1 : ℝ) else 0) (1 : ℝ) ?_ (Eventually.of_forall fun w => by simp [rubi34r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi34r1, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi34r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi35r1_counterexample_real : ¬ rubi35r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi35r1.conditions rubi35r1.body rubi35r1.result rubi35r1.integrals
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
  refine not_antiderivRecHolds_integrand (fun s => if s = "c" then (2 : ℝ) else if s = "d" then (1 : ℝ) else 0) (1 : ℝ) ?_ (Eventually.of_forall fun w => by simp [rubi35r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi35r1, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi35r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

end OSR.IntegrationRec165
