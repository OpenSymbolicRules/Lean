import OSR.IntegrationRec14

/-!
# Integration (RUBI): more `EqQ` rules

Refutations found by random sampling or by reading the result (4.7.8 #47
and #48 divide by `a n`, and the optional `a` may vanish).
The rules of this module were selected by a numerical search for
counterexamples under the real definedness semantics of the fragment: an
assignment satisfying the conditions, a point near which the integrand is
defined, at which the result or a residual integrand is not.  The search only
proposes; each refutation below is a Lean theorem, stated per domain.  The
rule declarations are transcribed by a tool and checked by the Integration
repository's `scripts/v1_faithfulness.py`.  Variables that RUBI constrains
by numeric predicates (`IntegerQ`, `GtQ`, …) but does not list in `FreeQ` are
declared independent of `x`, with an `independence:` finding.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec15

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 3.2.1 #7 -/
def rubi321r7 : CRule where
  id := "integration.rubi_3_2_1_r7"; legacyId := some "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n")))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .ln (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.int (-1)))))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n"))))))) (.pow (.var "g") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "B") (.var "n")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.var "g") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.int (-1))))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "A", "B", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "b") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "g"))) (.int 0)]
  priority := 3500
  description := "RUBI 3.2.1 #7"
  provenance := migrated "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:7" "3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.m#7"

/-- RUBI 4.7.8 #47 -/
def rubi478r47 : CRule where
  id := "integration.rubi_4_7_8_r47"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:47"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.app1 .sin (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "x") (.var "n"))) (.app1 .ln (.app2 .mul (.var "b") (.var "x")))))) (.app1 .ln (.app2 .mul (.var "b") (.var "x"))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .cos (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "x") (.var "n"))) (.app1 .ln (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app2 .mul (.var "a") (.var "n")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.var "n") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.app1 .sin (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "x") (.var "n"))) (.app1 .ln (.app2 .mul (.var "b") (.var "x")))))))]
  independent := ["a", "b", "m", "n"]
  conditions := [.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))]
  priority := 3510
  description := "RUBI 4.7.8 #47"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:47" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#47"

/-- RUBI 4.7.8 #48 -/
def rubi478r48 : CRule where
  id := "integration.rubi_4_7_8_r48"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:48"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.app1 .cos (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "x") (.var "n"))) (.app1 .ln (.app2 .mul (.var "b") (.var "x")))))) (.app1 .ln (.app2 .mul (.var "b") (.var "x"))))
  result := (.app2 .add (.app2 .mul (.app1 .sin (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "x") (.var "n"))) (.app1 .ln (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app2 .mul (.var "a") (.var "n")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.var "n") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.app1 .cos (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "x") (.var "n"))) (.app1 .ln (.app2 .mul (.var "b") (.var "x")))))))]
  independent := ["a", "b", "m", "n"]
  conditions := [.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))]
  priority := 3520
  description := "RUBI 4.7.8 #48"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:48" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#48"


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
private theorem ivnat (n : ℕ) [n.AtLeastTwo] : intValue? (OfNat.ofNat n : α) = some (OfNat.ofNat n) := by
  simpa using intValue?_intCast (α := α) (OfNat.ofNat n : ℤ)
private theorem ivneg (n : ℕ) [n.AtLeastTwo] :
    intValue? (-(OfNat.ofNat n : α)) = some (-(OfNat.ofNat n)) := by
  simpa using intValue?_intCast (α := α) (-(OfNat.ofNat n : ℤ))
private theorem ivm6 : intValue? (-6 : α) = some (-6) := by simpa using intValue?_intCast (α := α) (-6)
private theorem ivex2 : ∃ n, intValue? (2 : α) = some n ∧ 0 ≤ n := ⟨2, iv2, by norm_num⟩
private theorem ivexInt (z : ℤ) : ∃ n, intValue? (z : α) = some n := ⟨z, intValue?_intCast z⟩
private theorem ivexm1 : ∃ n, intValue? (-1 : α) = some n := ⟨_, ivm1⟩
private theorem ivm4 : intValue? (-4 : α) = some (-4) := by simpa using intValue?_intCast (α := α) (-4)
private theorem ivexm4 : ∃ n, intValue? (-4 : α) = some n := ⟨_, ivm4⟩
private theorem ivexm6 : ∃ n, intValue? (-6 : α) = some n := ⟨_, ivm6⟩
end


private theorem rsin1 : Real.sin 1 ≠ 0 :=
  (Real.sin_pos_of_pos_of_lt_pi one_pos (by linarith [Real.pi_gt_three])).ne'

private theorem csin1 : Complex.sin 1 ≠ 0 := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sin]; exact_mod_cast rsin1

theorem rubi321r7_counterexample_real : ¬ rubi321r7.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi321r7.conditions rubi321r7.body rubi321r7.result rubi321r7.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "g" then -2 else if s = "b" ∨ s = "c" then -3 else if s = "e" then 2 else 0) (1 : ℝ) (by simp [rubi321r7, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi321r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi321r7.integrals[0]!, by simp [rubi321r7], ?_⟩
  intro h
  simp [rubi321r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi321r7_counterexample_complex : ¬ rubi321r7.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi321r7.conditions rubi321r7.body rubi321r7.result rubi321r7.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "g" then -2 else if s = "b" ∨ s = "c" then -3 else if s = "e" then 2 else 0) (1 : ℂ) (by simp [rubi321r7, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi321r7, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi321r7.integrals[0]!, by simp [rubi321r7], ?_⟩
  intro h
  simp [rubi321r7, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi478r47_counterexample_real : ¬ rubi478r47.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi478r47.conditions rubi478r47.body rubi478r47.result rubi478r47.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi478r47, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with w hw; simp [rubi478r47, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw, hw.ne'] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi478r47.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi478r47, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi478r47, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi478r47_counterexample_complex : ¬ rubi478r47.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi478r47.conditions rubi478r47.body rubi478r47.result rubi478r47.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi478r47, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi478r47, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi478r47.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi478r47, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi478r47, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi478r48_counterexample_real : ¬ rubi478r48.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi478r48.conditions rubi478r48.body rubi478r48.result rubi478r48.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi478r48, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with w hw; simp [rubi478r48, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw, hw.ne'] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi478r48.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi478r48, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi478r48, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi478r48_counterexample_complex : ¬ rubi478r48.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi478r48.conditions rubi478r48.body rubi478r48.result rubi478r48.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi478r48, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi478r48, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi478r48.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi478r48, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi478r48, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

end OSR.IntegrationRec15
