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

namespace OSR.IntegrationRec159

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/



















/-- RUBI 5.3.4 #144 -/
def rubi534r144 : CRule where
  id := "integration.rubi_5_3_4_r144"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:144"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.var "x") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.int 2)))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.int 2))) (.pow (.app2 .mul (.int 2) (.var "g")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "x") (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.int 2))) (.pow (.int 2) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "c") (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "e")) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 2)) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  conditions := [.eq (.var "g") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "f"))]
  priority := 11898
  description := "RUBI 5.3.4 #144"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:144" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#144"

/-- RUBI 6.3.12 #3 -/
def rubi6312r3 : CRule where
  id := "integration.rubi_6_3_12_r3"; legacyId := some "rubi:6 Hyperbolic functions/6.3 Hyperbolic tangent/6.3.12 (d+e x)^m tanh(a+b x+c x^2)^n:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app1 .tanh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "e") (.app1 .ln (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app1 .tanh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))]
  independent := ["a", "b", "c", "d", "e"]
  priority := 11899
  description := "RUBI 6.3.12 #3"
  provenance := migrated "rubi:6 Hyperbolic functions/6.3 Hyperbolic tangent/6.3.12 (d+e x)^m tanh(a+b x+c x^2)^n:3" "6 Hyperbolic functions/6.3 Hyperbolic tangent/6.3.12 (d+e x)^m tanh(a+b x+c x^2)^n.m#3"

/-- RUBI 6.3.12 #4 -/
def rubi6312r4 : CRule where
  id := "integration.rubi_6_3_12_r4"; legacyId := some "rubi:6 Hyperbolic functions/6.3 Hyperbolic tangent/6.3.12 (d+e x)^m tanh(a+b x+c x^2)^n:4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app1 .coth (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "e") (.app1 .ln (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app1 .coth (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))]
  independent := ["a", "b", "c", "d", "e"]
  priority := 11900
  description := "RUBI 6.3.12 #4"
  provenance := migrated "rubi:6 Hyperbolic functions/6.3 Hyperbolic tangent/6.3.12 (d+e x)^m tanh(a+b x+c x^2)^n:4" "6 Hyperbolic functions/6.3 Hyperbolic tangent/6.3.12 (d+e x)^m tanh(a+b x+c x^2)^n.m#4"






/-! ## Refutations -/

section
variable {α : Type} [Field α] [CharZero α]
private theorem iv0 : intValue? (0 : α) = some 0 := by simpa using intValue?_intCast (α := α) 0
private theorem iv1 : intValue? (1 : α) = some 1 := by simpa using intValue?_intCast (α := α) 1
private theorem iv2 : intValue? (2 : α) = some 2 := by simpa using intValue?_intCast (α := α) 2
private theorem iv3 : intValue? (3 : α) = some 3 := by simpa using intValue?_intCast (α := α) 3
private theorem iv4 : intValue? (4 : α) = some 4 := by simpa using intValue?_intCast (α := α) 4
private theorem ivm1 : intValue? (-1 : α) = some (-1) := by simpa using intValue?_intCast (α := α) (-1)
private theorem ivm2 : intValue? (-2 : α) = some (-2) := by simpa using intValue?_intCast (α := α) (-2)
private theorem ivm3 : intValue? (-3 : α) = some (-3) := by simpa using intValue?_intCast (α := α) (-3)
private theorem ivm4 : intValue? (-4 : α) = some (-4) := by simpa using intValue?_intCast (α := α) (-4)
private theorem ivm5 : intValue? (-5 : α) = some (-5) := by simpa using intValue?_intCast (α := α) (-5)
private theorem ivm6 : intValue? (-6 : α) = some (-6) := by simpa using intValue?_intCast (α := α) (-6)
private theorem ivm7 : intValue? (-7 : α) = some (-7) := by simpa using intValue?_intCast (α := α) (-7)
private theorem ivm8 : intValue? (-8 : α) = some (-8) := by simpa using intValue?_intCast (α := α) (-8)
private theorem ivm9 : intValue? (-9 : α) = some (-9) := by simpa using intValue?_intCast (α := α) (-9)
private theorem ivm10 : intValue? (-10 : α) = some (-10) := by simpa using intValue?_intCast (α := α) (-10)
private theorem ivm11 : intValue? (-11 : α) = some (-11) := by simpa using intValue?_intCast (α := α) (-11)
private theorem ivm12 : intValue? (-12 : α) = some (-12) := by simpa using intValue?_intCast (α := α) (-12)
private theorem ivnat (n : ℕ) [n.AtLeastTwo] : intValue? (OfNat.ofNat n : α) = some (OfNat.ofNat n) := by
  simpa using intValue?_intCast (α := α) (OfNat.ofNat n : ℤ)
private theorem ivneg (n : ℕ) [n.AtLeastTwo] :
    intValue? (-(OfNat.ofNat n : α)) = some (-(OfNat.ofNat n)) := by
  simpa using intValue?_intCast (α := α) (-(OfNat.ofNat n : ℤ))
end


theorem rubi534r144_counterexample_real : ¬ rubi534r144.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r144.conditions rubi534r144.body rubi534r144.result rubi534r144.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "e" ∨ s = "f" then 1 else 0) (1 : ℝ) (by simp [rubi534r144, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | (norm_num [iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg]; done) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 1) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 2) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 3) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 1); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 2); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 3); linarith) | (intro h; have := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩ (x := 1); linarith) | (intro h; have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 2) (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 3) (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]); linarith) | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r144, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | (norm_num [iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg]; done) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 1) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 2) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 3) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 1); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 2); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 3); linarith) | (intro h; have := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩ (x := 1); linarith) | (intro h; have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 2) (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 3) (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]); linarith) | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r144.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "e" ∨ s = "f" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r144, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r144, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6312r3_counterexample_real : ¬ rubi6312r3.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6312r3.conditions rubi6312r3.body rubi6312r3.result rubi6312r3.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi6312r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | (norm_num [iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg]; done) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 1) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 2) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 3) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 1); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 2); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 3); linarith) | (intro h; have := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩ (x := 1); linarith) | (intro h; have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 2) (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 3) (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]); linarith) | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6312r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | (norm_num [iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg]; done) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 1) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 2) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 3) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 1); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 2); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 3); linarith) | (intro h; have := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩ (x := 1); linarith) | (intro h; have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 2) (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 3) (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]); linarith) | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6312r3.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "e" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6312r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6312r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6312r3_counterexample_complex : ¬ rubi6312r3.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6312r3.conditions rubi6312r3.body rubi6312r3.result rubi6312r3.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" then 1 else 0) (1 : ℂ) (by simp [rubi6312r3, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | (norm_num [iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg]; done) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 1) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 2) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 3) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 1); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 2); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 3); linarith) | (intro h; have := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩ (x := 1); linarith) | (intro h; have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 2) (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 3) (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]); linarith) | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6312r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | (norm_num [iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg]; done) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 1) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 2) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 3) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 1); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 2); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 3); linarith) | (intro h; have := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩ (x := 1); linarith) | (intro h; have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 2) (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 3) (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]); linarith) | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6312r3.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "e" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6312r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6312r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6312r4_counterexample_real : ¬ rubi6312r4.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6312r4.conditions rubi6312r4.body rubi6312r4.result rubi6312r4.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi6312r4, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | (norm_num [iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg]; done) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 1) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 2) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 3) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 1); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 2); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 3); linarith) | (intro h; have := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩ (x := 1); linarith) | (intro h; have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 2) (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 3) (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]); linarith) | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6312r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | (norm_num [iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg]; done) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 1) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 2) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0:ℝ) < 3) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 1); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 2); linarith) | (intro h; have := Real.sinh_pos_iff.2 (by norm_num : (0:ℝ) < 3); linarith) | (intro h; have := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩ (x := 1); linarith) | (intro h; have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 2) (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]); linarith) | (intro h; have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := 3) (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]); linarith) | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6312r4.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6312r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6312r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

end OSR.IntegrationRec159
