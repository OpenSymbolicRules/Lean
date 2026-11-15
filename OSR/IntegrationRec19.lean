import OSR.IntegrationRec18

/-!
# Integration (RUBI): a refutation at `x = π`

RUBI 4.7.9 #78 divides by `sin(a x)` and its residual integrand is
`1/sin²(a x)` (4.7.9 #82, at `b = m = n = 1`, has `1/(x sin(a x))`); at `a = c = 1`, `d = -1` (so `a c + d = 0`) the integrand
`x²/(sin x - x cos x)²` is defined near `x = π`, where both are undefined.
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

namespace OSR.IntegrationRec19

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 4.7.9 #78 -/
def rubi479r78 : CRule where
  id := "integration.rubi_4_7_9_r78"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:78"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.int 2)) (.pow (.pow (.app2 .add (.app2 .mul (.var "c") (.app1 .sin (.app2 .mul (.var "a") (.var "x")))) (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.app1 .cos (.app2 .mul (.var "a") (.var "x"))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "x") (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app1 .sin (.app2 .mul (.var "a") (.var "x")))) (.app2 .add (.app2 .mul (.var "c") (.app1 .sin (.app2 .mul (.var "a") (.var "x")))) (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.app1 .cos (.app2 .mul (.var "a") (.var "x")))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "d") (.int 2)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.pow (.app1 .sin (.app2 .mul (.var "a") (.var "x"))) (.int 2)) (.int (-1)))))]
  independent := ["a", "c", "d"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.var "d")) (.int 0)]
  priority := 3800
  description := "RUBI 4.7.9 #78"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:78" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#78"

/-- RUBI 4.7.9 #82 -/
def rubi479r82 : CRule where
  id := "integration.rubi_4_7_9_r82"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:82"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "b") (.var "x")) (.var "m")) (.pow (.app1 .sin (.app2 .mul (.var "a") (.var "x"))) (.var "n"))) (.pow (.pow (.app2 .add (.app2 .mul (.var "c") (.app1 .sin (.app2 .mul (.var "a") (.var "x")))) (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.app1 .cos (.app2 .mul (.var "a") (.var "x"))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .mul (.var "b") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app1 .sin (.app2 .mul (.var "a") (.var "x"))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.app2 .mul (.var "c") (.app1 .sin (.app2 .mul (.var "a") (.var "x")))) (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.app1 .cos (.app2 .mul (.var "a") (.var "x")))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.pow (.var "d") (.int 2)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "b") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app1 .sin (.app2 .mul (.var "a") (.var "x"))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.var "d")) (.int 0),
    .eq (.var "m") (.app2 .add (.int 2) (.app2 .mul (.int (-1)) (.var "n")))]
  priority := 3810
  description := "RUBI 4.7.9 #82"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:82" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#82"

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


theorem rubi479r78_counterexample_real : ¬ rubi479r78.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi479r78.conditions rubi479r78.body rubi479r78.result rubi479r78.integrals
  have hg : ∀ᶠ w in 𝓝 (Real.pi), Real.sin w + -1 * w * Real.cos w ≠ 0 := by
    have hc : ContinuousAt (fun w : ℝ => Real.sin w + -1 * w * Real.cos w) (Real.pi) := by fun_prop
    refine hc.eventually_ne ?_
    simp [Real.sin_pi, Real.cos_pi]
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" ∨ s = "c" then 1 else if s = "d" then -1 else 0) (Real.pi) ?_ ?_ ⟨rubi479r78.integrals[0]!, by simp [rubi479r78], ?_⟩
  · simp [rubi479r78, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, ivm1]
  · filter_upwards [hg] with w hw
    simp [rubi479r78, Defined, eval, Interp.real, iv0, iv1, iv2, ivm1]
    simpa [neg_mul] using hw
  · simp [rubi479r78, Defined, eval, Interp.real, iv0, iv1, iv2, ivm1, Real.sin_pi]

theorem rubi479r78_counterexample_complex : ¬ rubi479r78.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi479r78.conditions rubi479r78.body rubi479r78.result rubi479r78.integrals
  have hg : ∀ᶠ w in 𝓝 ((Real.pi : ℂ)), Complex.sin w + -1 * w * Complex.cos w ≠ 0 := by
    have hc : ContinuousAt (fun w : ℂ => Complex.sin w + -1 * w * Complex.cos w) ((Real.pi : ℂ)) := by fun_prop
    refine hc.eventually_ne ?_
    simp [Complex.sin_pi, Complex.cos_pi]
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" ∨ s = "c" then 1 else if s = "d" then -1 else 0) ((Real.pi : ℂ)) ?_ ?_ ⟨rubi479r78.integrals[0]!, by simp [rubi479r78], ?_⟩
  · simp [rubi479r78, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, ivm1]
  · filter_upwards [hg] with w hw
    simp [rubi479r78, Defined, eval, Interp.complex, iv0, iv1, iv2, ivm1]
    simpa [neg_mul] using hw
  · simp [rubi479r78, Defined, eval, Interp.complex, iv0, iv1, iv2, ivm1, Complex.sin_pi]

theorem rubi479r82_counterexample_real : ¬ rubi479r82.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi479r82.conditions rubi479r82.body rubi479r82.result rubi479r82.integrals
  have hg : ∀ᶠ w in 𝓝 (Real.pi), Real.sin w + -1 * w * Real.cos w ≠ 0 := by
    have hc : ContinuousAt (fun w : ℝ => Real.sin w + -1 * w * Real.cos w) (Real.pi) := by fun_prop
    refine hc.eventually_ne ?_
    simp [Real.sin_pi, Real.cos_pi]
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "m" ∨ s = "n" then 1 else if s = "d" then -1 else 0) (Real.pi) ?_ ?_ ⟨rubi479r82.integrals[0]!, by simp [rubi479r82], ?_⟩
  · simp [rubi479r82, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, ivm1] <;> norm_num
  · filter_upwards [hg] with w hw
    simp [rubi479r82, Defined, eval, Interp.real, iv0, iv1, iv2, ivm1]
    simpa [neg_mul] using hw
  · simp [rubi479r82, Defined, eval, Interp.real, iv0, iv1, iv2, ivm1, Real.sin_pi]
    norm_num [ivm1]

theorem rubi479r82_counterexample_complex : ¬ rubi479r82.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi479r82.conditions rubi479r82.body rubi479r82.result rubi479r82.integrals
  have hg : ∀ᶠ w in 𝓝 ((Real.pi : ℂ)), Complex.sin w + -1 * w * Complex.cos w ≠ 0 := by
    have hc : ContinuousAt (fun w : ℂ => Complex.sin w + -1 * w * Complex.cos w) ((Real.pi : ℂ)) := by fun_prop
    refine hc.eventually_ne ?_
    simp [Complex.sin_pi, Complex.cos_pi]
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "m" ∨ s = "n" then 1 else if s = "d" then -1 else 0) ((Real.pi : ℂ)) ?_ ?_ ⟨rubi479r82.integrals[0]!, by simp [rubi479r82], ?_⟩
  · simp [rubi479r82, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, ivm1] <;> norm_num
  · filter_upwards [hg] with w hw
    simp [rubi479r82, Defined, eval, Interp.complex, iv0, iv1, iv2, ivm1]
    simpa [neg_mul] using hw
  · simp [rubi479r82, Defined, eval, Interp.complex, iv0, iv1, iv2, ivm1, Complex.sin_pi]
    norm_num [ivm1]

end OSR.IntegrationRec19
