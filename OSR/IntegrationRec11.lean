import OSR.IntegrationRec10

/-!
# Integration (RUBI): more results dividing by a vanishing coefficient

RUBI 1.2.2.2 #19 divides by `c`, which `b² - 4 a c ≠ 0` allows to vanish
when `b ≠ 0`; 3.1.4 #11 divides by `d f (q + 1)`, and `f = 0` keeps
`(f x)^m = 0` defined for `m > 0`.  The witnesses were checked numerically under the
fragment's real definedness semantics; each refutation is a Lean theorem.

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

namespace OSR.IntegrationRec11

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.2.2.2 #19 -/
def rubi1222r19 : CRule where
  id := "integration.rubi_1_2_2_2_r19"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.2 (d x)^m (a+b x^2+c x^4)^p:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 3)) (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 3))))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 3)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 4))) (.pow (.var "c") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 4)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "m"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.var "m") (.int 3)]
  priority := 2760
  description := "RUBI 1.2.2.2 #19"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.2 (d x)^m (a+b x^2+c x^4)^p:19" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.2 (d x)^m (a+b x^2+c x^4)^p.m#19"

/-- RUBI 3.1.4 #11 -/
def rubi314r11 : CRule where
  id := "integration.rubi_3_1_4_r11"; legacyId := some "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.var "q")) (.int 2)) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "m", "p", "q"]
  conditions := [.int (.app2 .add (.app2 .add (.var "m") (.var "q")) (.int 2)),
    .gt (.int 0) (.app2 .add (.app2 .add (.var "m") (.var "q")) (.int 2)),
    .int (.var "p"),
    .gt (.var "p") (.int 0),
    .gt (.int (-1)) (.var "q"),
    .gt (.var "m") (.int 0)]
  priority := 2770
  description := "RUBI 3.1.4 #11"
  provenance := migrated "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:11" "3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.m#11"

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

theorem rubi1222r19_counterexample_real : ¬ rubi1222r19.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1222r19.conditions rubi1222r19.body rubi1222r19.result rubi1222r19.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "b" ∨ s = "d" then 1 else if s = "m" then 4 else 0) (1 : ℝ) (by simp [rubi1222r19, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1222r19, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1222r19.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "b" ∨ s = "d" then 1 else if s = "m" then 4 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1222r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1222r19, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi314r11_counterexample_real : ¬ rubi314r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi314r11.conditions rubi314r11.body rubi314r11.result rubi314r11.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -4 else if s = "a" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi314r11, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi314r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi314r11.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "q" then -4 else if s = "a" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi314r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi314r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi314r11_counterexample_complex : ¬ rubi314r11.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi314r11.conditions rubi314r11.body rubi314r11.result rubi314r11.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -4 else if s = "a" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi314r11, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi314r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi314r11.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "q" then -4 else if s = "a" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi314r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi314r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

end OSR.IntegrationRec11
