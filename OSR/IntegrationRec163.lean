import OSR.IntegrationRec91

/-!
# Integration (RUBI): two identities and three degenerate refutations

1.3.3 #24 rewrites `√(e x (a x + b √(c + d x²)))` by distributing, and 6.7.9
#76 uses `2 (b cosh² u + c sinh² u) = b - c + (b + c) cosh 2u`; both are proved
over ℝ.  1.3.3 #36, 1.2.1.5 #17 and 1.2.1.6 #26 divide by `d`, `f` or `2 f`,
which the conditions allow to vanish while the integrand is defined; they are
refuted over ℝ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec163

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.3.3 #24 -/
def rubi133r24 : CRule where
  id := "integration.rubi_1_3_3_r24"; legacyId := some "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions:24"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .root (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.app2 .mul (.var "a") (.var "x")) (.app2 .mul (.var "b") (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2))))) (.int 2)) (.pow (.app2 .mul (.var "x") (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1))))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .root (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.pow (.var "x") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.var "x")) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2)))) (.int 2)) (.pow (.app2 .mul (.var "x") (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "c")) (.var "e")) (.var "a")) (.int 0)]
  priority := 11910
  description := "RUBI 1.3.3 #24"
  provenance := migrated "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions:24" "1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions.m#24"

/-- RUBI 6.7.9 #76 -/
def rubi679r76 : CRule where
  id := "integration.rubi_6_7_9_r76"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:76"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "b") (.pow (.app1 .coth (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2)))) (.int (-1))))
  result := (.app2 .mul (.int 2) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "b") (.app2 .mul (.int (-1)) (.var "c"))) (.app2 .mul (.app2 .add (.var "b") (.var "c")) (.app1 .cosh (.app2 .add (.app2 .mul (.int 2) (.var "d")) (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.var "x")))))) (.int (-1)))))]
  independent := ["b", "c", "d", "e", "f", "g", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0)]
  priority := 11911
  description := "RUBI 6.7.9 #76"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:76" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#76"

/-- RUBI 1.3.3 #36 -/
def rubi133r36 : CRule where
  id := "integration.rubi_1_3_3_r36"; legacyId := some "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions:36"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 3)))) (.int 2)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.pow (.pow (.var "d") (.int 3)) (.int (-1)))) (.var "I2"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.pow (.var "c") (.int 3))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "d") (.int 3))))) (.pow (.pow (.var "d") (.int 3)) (.int (-1)))) (.var "I3")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.int 2)) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 3)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "x"))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 3)))) (.int 2)) (.int (-1))))),
    ("I3", (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 3)))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.pow (.var "c") (.int 3))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "d") (.int 3)))) (.int 0)]
  priority := 11912
  description := "RUBI 1.3.3 #36"
  provenance := migrated "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions:36" "1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions.m#36"

/-- RUBI 1.2.1.5 #17 -/
def rubi1215r17 : CRule where
  id := "integration.rubi_1_2_1_5_r17"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.5 (a+b x+c x^2)^p (d+e x+f x^2)^q:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "f") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.var "f") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "f")) (.var "x"))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .add (.var "d") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "f"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)]
  priority := 11913
  description := "RUBI 1.2.1.5 #17"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.5 (a+b x+c x^2)^p (d+e x+f x^2)^q:17" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.5 (a+b x+c x^2)^p (d+e x+f x^2)^q.m#17"

/-- RUBI 1.2.1.6 #26 -/
def rubi1216r26 : CRule where
  id := "integration.rubi_1_2_1_6_r26"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:26"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.pow (.app2 .mul (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "h") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "g")) (.var "f")))) (.pow (.app2 .mul (.int 2) (.var "f")) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.var "h") (.pow (.app2 .mul (.int 2) (.var "f")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.var "e") (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.var "x"))) (.pow (.app2 .mul (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "d")) (.var "f"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "c") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "f"))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "h") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "g")) (.var "f"))) (.int 0)]
  priority := 11914
  description := "RUBI 1.2.1.6 #26"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:26" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q.m#26"

/-! ## Proofs and refutations -/

theorem rubi133r36_counterexample_real : ¬ rubi133r36.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi133r36.conditions rubi133r36.body rubi133r36.result rubi133r36.integrals
  have i0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have i1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have i3 : intValue? (3 : ℝ) = some 3 := (intValue?_eq _ _).2 (by norm_num)
  have i4 : intValue? (4 : ℝ) = some 4 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have im2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" then 1 else 0) (1 : ℝ) ?_ ?_
    (fun h w => w * (((rubi133r36.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "c" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi133r36, Cond.Holds, Defined, eval, Interp.real, i0, i1, i2, i3, i4, im1, im2]
  · filter_upwards [Ioo_mem_nhds (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 3/2)] with v hv
    obtain ⟨h1, h2⟩ := hv
    simp [rubi133r36, Defined, eval, Interp.real, i0, i1, i2, i3, i4, im1, im2]
    first | exact pow_nonneg (by linarith) 3 | linarith | exact ⟨by linarith, by linarith, (Real.sqrt_pos.2 (by linarith)).ne'⟩ | (trace_state; sorry)
  · simp only [rubi133r36, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    first | exact hasDerivAt_mul_const _ | exact ⟨hasDerivAt_mul_const _, hasDerivAt_mul_const _⟩ | exact ⟨hasDerivAt_mul_const _, hasDerivAt_mul_const _, hasDerivAt_mul_const _⟩
  · intro h
    simp [rubi133r36, Defined, eval, Interp.real, i0, i1, i2, i3, i4, im1, im2, recEnv] at h

theorem rubi1215r17_counterexample_real : ¬ rubi1215r17.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1215r17.conditions rubi1215r17.body rubi1215r17.result rubi1215r17.integrals
  have i0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have i1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have i3 : intValue? (3 : ℝ) = some 3 := (intValue?_eq _ _).2 (by norm_num)
  have i4 : intValue? (4 : ℝ) = some 4 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have im2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "b" ∨ s = "d" then 1 else 0) (0 : ℝ) ?_ ?_
    (fun h w => w * (((rubi1215r17.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "b" ∨ s = "d" then 1 else 0) "x" (0 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1215r17, Cond.Holds, Defined, eval, Interp.real, i0, i1, i2, i3, i4, im1, im2]
  · filter_upwards [Ioo_mem_nhds (by norm_num : (-1/2 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1/2)] with v hv
    obtain ⟨h1, h2⟩ := hv
    simp [rubi1215r17, Defined, eval, Interp.real, i0, i1, i2, i3, i4, im1, im2]
    first | exact pow_nonneg (by linarith) 3 | linarith | exact ⟨by linarith, by linarith, (Real.sqrt_pos.2 (by linarith)).ne'⟩ | (trace_state; sorry)
  · simp only [rubi1215r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    first | exact hasDerivAt_mul_const _ | exact ⟨hasDerivAt_mul_const _, hasDerivAt_mul_const _⟩ | exact ⟨hasDerivAt_mul_const _, hasDerivAt_mul_const _, hasDerivAt_mul_const _⟩
  · intro h
    simp [rubi1215r17, Defined, eval, Interp.real, i0, i1, i2, i3, i4, im1, im2, recEnv] at h

theorem rubi1216r26_counterexample_real : ¬ rubi1216r26.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1216r26.conditions rubi1216r26.body rubi1216r26.result rubi1216r26.integrals
  have i0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have i1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have i3 : intValue? (3 : ℝ) = some 3 := (intValue?_eq _ _).2 (by norm_num)
  have i4 : intValue? (4 : ℝ) = some 4 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have im2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "e" ∨ s = "h" then 1 else 0) (0 : ℝ) ?_ ?_
    (fun h w => w * (((rubi1216r26.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "e" ∨ s = "h" then 1 else 0) "x" (0 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1216r26, Cond.Holds, Defined, eval, Interp.real, i0, i1, i2, i3, i4, im1, im2]
  · filter_upwards [Ioo_mem_nhds (by norm_num : (-1/2 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1/2)] with v hv
    obtain ⟨h1, h2⟩ := hv
    simp [rubi1216r26, Defined, eval, Interp.real, i0, i1, i2, i3, i4, im1, im2]
    first | exact pow_nonneg (by linarith) 3 | linarith | exact ⟨by linarith, by linarith, (Real.sqrt_pos.2 (by linarith)).ne'⟩ | (trace_state; sorry)
  · simp only [rubi1216r26, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    first | exact hasDerivAt_mul_const _ | exact ⟨hasDerivAt_mul_const _, hasDerivAt_mul_const _⟩ | exact ⟨hasDerivAt_mul_const _, hasDerivAt_mul_const _, hasDerivAt_mul_const _⟩
  · intro h
    simp [rubi1216r26, Defined, eval, Interp.real, i0, i1, i2, i3, i4, im1, im2, recEnv] at h

theorem rubi133r24_real : rubi133r24.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi133r24.conditions rubi133r24.body rubi133r24.result rubi133r24.integrals
  intro env hc t hF
  have i0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have i1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have i3 : intValue? (3 : ℝ) = some 3 := (intValue?_eq _ _).2 (by norm_num)
  have i4 : intValue? (4 : ℝ) = some 4 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have im2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have hd : ∀ w : ℝ, env "e" * w * (env "a" * w + env "b" * √(env "c" + env "d" * w ^ 2)) =
      env "a" * env "e" * w ^ 2 + env "b" * env "e" * w * √(env "c" + env "d" * w ^ 2) := fun w => by ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi133r24, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi133r24, Defined, eval, Interp.real, i0, i1, i2, i3, i4, im1, im2] at hw ⊢
    first | (simp only [hd] at hw; tauto) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi133r24, Defined, eval, recEnv]
  · simp only [rubi133r24, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    simp [rubi133r24, eval, recEnv, Interp.real, i0, i1, i2, i3, i4, im1, im2] at hΦ ⊢
    first | (simp only [hd]; exact hΦ) | (rw [hd]; exact hΦ) | (trace_state; sorry)

theorem rubi679r76_real : rubi679r76.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r76.conditions rubi679r76.body rubi679r76.result rubi679r76.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi679r76, Defined, eval, Interp.real, hk_m] at h
  have hc2 : ∀ w : ℝ, Real.cosh (2 * env "d" + 2 * env "e" * w) = 2 * Real.cosh (env "d" + env "e" * w) ^ 2 - 1 := by
    intro w; rw [show 2 * env "d" + 2 * env "e" * w = 2 * (env "d" + env "e" * w) by ring, Real.cosh_two_mul]
    linear_combination -Real.cosh_sq_sub_sinh_sq (env "d" + env "e" * w)
  have ht := hF.self_of_nhds
  simp [rubi679r76, Defined, eval, Interp.real, i2, im1, hk_m] at ht
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r76, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi679r76, Defined, eval, Interp.real, i2, im1, hk_m, hc2, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢
    have hr := Real.cosh_sq_sub_sinh_sq (env "d" + env "e" * w)
    have hC0 : Real.cosh (env "d" + env "e" * w) ≠ 0 := (Real.cosh_pos _).ne'
    have hS0 : Real.sinh (env "d" + env "e" * w) ≠ 0 := by intro h; rw [Real.sinh_eq_zero] at h; exact hw.2.1 h
    generalize Real.sinh (env "d" + env "e" * w) = S at *
    generalize Real.cosh (env "d" + env "e" * w) = C at *
    refine ⟨hw.1.1, ?_⟩
    intro hN; apply hw.2.2; field_simp; linear_combination (1 / 2 : ℝ) * hN - env "c" * hr
  · filter_upwards [hF] with w hw
    simp [rubi679r76, Defined, eval, recEnv, Interp.real, i2, im1, hk_m, hc2, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢
    try tauto
  · simp only [rubi679r76, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine (hΦ.const_mul 2).congr_deriv ?_
    simp [rubi679r76, Defined, eval, Interp.real, i2, im1, hk_m, hc2, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at ht ⊢
    obtain ⟨-, hX⟩ := ht
    have hr := Real.cosh_sq_sub_sinh_sq (env "d" + env "e" * t)
    have hC0 : Real.cosh (env "d" + env "e" * t) ≠ 0 := (Real.cosh_pos _).ne'
    have hS0 : Real.sinh (env "d" + env "e" * t) ≠ 0 := by intro h; rw [Real.sinh_eq_zero] at h; exact hX.1 h
    generalize Real.sinh (env "d" + env "e" * t) = S at *
    generalize Real.cosh (env "d" + env "e" * t) = C at *
    have hN : env "b" + -env "c" + (env "b" + env "c") * (2 * C ^ 2 - 1) ≠ 0 := by
      intro hN; apply hX.2; field_simp; linear_combination (1 / 2 : ℝ) * hN - env "c" * hr
    have hX' : env "c" * S ^ 2 + env "b" * C ^ 2 ≠ 0 := by intro h; apply hX.2; field_simp; linear_combination h
    field_simp
    first
      | linear_combination (-2 * env "c" * (env "f" + env "g" * t) ^ km) * hr
      | linear_combination (2 * env "c" * (env "f" + env "g" * t) ^ km) * hr
      | (trace_state; sorry)

end OSR.IntegrationRec163
