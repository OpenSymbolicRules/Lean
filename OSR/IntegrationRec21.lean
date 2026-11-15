import OSR.IntegrationRec20

/-!
# Integration (RUBI): more EqQ leftovers

4.7.7 #34 and #35 split the numerator under the integral,
`h + i cos u = 2 i cos u + (h - i cos u)` (and the same with `sin`): they
hold over ℝ and ℂ for every value of the metavariables, the conditions are
not needed.

1.2.1.2 #54 and #59 are refuted over ℝ and ℂ at `d = 0` (hence `b = 0` by
`2 c d = b e`, with `a = c = e = 1`): the integrand is defined near `x = 1`,
but the result divides by `d` (#54) or by `b (p + 1)` (#59). The numerical
search cannot meet an `EqQ` condition exactly; these witnesses were chosen
by hand and checked numerically before the Lean proofs.
Variables that RUBI constrains by numeric predicates but does not list in
`FreeQ` are declared independent of `x`, with an `independence:` finding.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec21

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.2.1.2 #54 -/
def rubi1212r54 : CRule where
  id := "integration.rubi_1_2_1_2_r54"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:54"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-4)) (.var "b")) (.var "c")) (.pow (.app2 .mul (.var "d") (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.app2 .mul (.pow (.var "d") (.int 2)) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)]
  priority := 4100
  description := "RUBI 1.2.1.2 #54"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:54" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#54"

/-- RUBI 1.2.1.2 #59 -/
def rubi1212r59 : CRule where
  id := "integration.rubi_1_2_1_2_r59"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:59"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "e")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.int 1),
    .int (.app2 .mul (.int 2) (.var "p"))]
  priority := 4110
  description := "RUBI 1.2.1.2 #59"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:59" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#59"

/-- h + i cos u = 2 i cos u + (h - i cos u) over f + g sin u -/
def expLinCosOverSin : CRule where
  id := "integration.exp_linear_cos_over_sin"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:34"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.app2 .add (.var "h") (.app2 .mul (.var "i") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "i")) (.var "I1")) (.var "I2"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.app2 .add (.var "h") (.app2 .mul (.app2 .mul (.int (-1)) (.var "i")) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1)))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "h", "i"]
  conditions := [.eq (.app2 .add (.pow (.var "f") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "g") (.int 2)))) (.int 0),
    .eq (.app2 .add (.pow (.var "h") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "i") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "g") (.var "h")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "i"))) (.int 0)]
  priority := 4120
  description := "h + i cos u = 2 i cos u + (h - i cos u) over f + g sin u"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:34" "4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n.m#34"
/-- h + i sin u = 2 i sin u + (h - i sin u) over f + g cos u -/
def expLinSinOverCos : CRule where
  id := "integration.exp_linear_sin_over_cos"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:35"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.app2 .add (.var "h") (.app2 .mul (.var "i") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "i")) (.var "I1")) (.var "I2"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.app2 .add (.var "h") (.app2 .mul (.app2 .mul (.int (-1)) (.var "i")) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1)))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "h", "i"]
  conditions := [.eq (.app2 .add (.pow (.var "f") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "g") (.int 2)))) (.int 0),
    .eq (.app2 .add (.pow (.var "h") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "i") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "g") (.var "h")) (.app2 .mul (.var "f") (.var "i"))) (.int 0)]
  priority := 4130
  description := "h + i sin u = 2 i sin u + (h - i sin u) over f + g cos u"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:35" "4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n.m#35"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

/-- **4.7.7 #34**: linearity of the numerator. -/
theorem expLinCosOverSin_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" expLinCosOverSin.conditions expLinCosOverSin.body expLinCosOverSin.result expLinCosOverSin.integrals := by
  intro env _ t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [expLinCosOverSin, List.mem_cons, List.not_mem_nil, or_false] at hi
    filter_upwards [hF] with w hw
    rcases hi with rfl | rfl <;> simp only [expLinCosOverSin, Defined, true_and, and_true] at hw ⊢ <;> tauto
  · exact Eventually.of_forall fun _ => by simp [expLinCosOverSin, Defined]
  · simp only [expLinCosOverSin, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (expLinCosOverSin.integrals.map (·.1)) Φ "x" w)
        expLinCosOverSin.result) = fun w => 2 * env "i" * Φ "I1" w + Φ "I2" w := by
      funext w
      simp [expLinCosOverSin, eval, recEnv]
    rw [hfun]
    refine ((hΦ.1.const_mul _).add hΦ.2).congr_deriv ?_
    simp [expLinCosOverSin, eval, toInt?_neg_one]
    ring

theorem expLinCosOverSin_real : expLinCosOverSin.Holds .real := expLinCosOverSin_holds Interp.real

theorem expLinCosOverSin_complex : expLinCosOverSin.Holds .complex := expLinCosOverSin_holds Interp.complex

/-- **4.7.7 #35**: linearity of the numerator. -/
theorem expLinSinOverCos_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" expLinSinOverCos.conditions expLinSinOverCos.body expLinSinOverCos.result expLinSinOverCos.integrals := by
  intro env _ t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [expLinSinOverCos, List.mem_cons, List.not_mem_nil, or_false] at hi
    filter_upwards [hF] with w hw
    rcases hi with rfl | rfl <;> simp only [expLinSinOverCos, Defined, true_and, and_true] at hw ⊢ <;> tauto
  · exact Eventually.of_forall fun _ => by simp [expLinSinOverCos, Defined]
  · simp only [expLinSinOverCos, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (expLinSinOverCos.integrals.map (·.1)) Φ "x" w)
        expLinSinOverCos.result) = fun w => 2 * env "i" * Φ "I1" w + Φ "I2" w := by
      funext w
      simp [expLinSinOverCos, eval, recEnv]
    rw [hfun]
    refine ((hΦ.1.const_mul _).add hΦ.2).congr_deriv ?_
    simp [expLinSinOverCos, eval, toInt?_neg_one]
    ring

theorem expLinSinOverCos_real : expLinSinOverCos.Holds .real := expLinSinOverCos_holds Interp.real

theorem expLinSinOverCos_complex : expLinSinOverCos.Holds .complex := expLinSinOverCos_holds Interp.complex

end Proofs

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

theorem rubi1212r54_counterexample_real : ¬ rubi1212r54.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r54.conditions rubi1212r54.body rubi1212r54.result rubi1212r54.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi1212r54, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm4, ivexm4] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1212r54, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm4, ivexm4, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1212r54.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "e" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r54, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r54, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm4, ivexm4, recEnv] at h <;> norm_num at h

theorem rubi1212r54_counterexample_complex : ¬ rubi1212r54.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1212r54.conditions rubi1212r54.body rubi1212r54.result rubi1212r54.integrals
  have hq : ∀ᶠ w in 𝓝 (1 : ℂ), 1 + w ^ 2 ≠ 0 := by
    have hc : ContinuousAt (fun w : ℂ => 1 + w ^ 2) 1 := by fun_prop
    exact hc.eventually_ne (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "e" then 1 else 0) (1 : ℂ) (by simp [rubi1212r54, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm4, ivexm4] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num), hq] with w hw hw2; simp [rubi1212r54, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm4, ivexm4, hw, hw2])
    (fun h w => w * (((rubi1212r54.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "e" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r54, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r54, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm4, ivexm4, recEnv] at h <;> norm_num at h

theorem rubi1212r59_counterexample_real : ¬ rubi1212r59.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r59.conditions rubi1212r59.body rubi1212r59.result rubi1212r59.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -2 else if s = "a" ∨ s = "c" ∨ s = "e" then 1 else if s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi1212r59, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm4, ivexm4] <;> (try norm_num) <;> exact ⟨-4, ivm4⟩)
    (Eventually.of_forall fun w => by simp [rubi1212r59, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm4, ivexm4] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1212r59.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -2 else if s = "a" ∨ s = "c" ∨ s = "e" then 1 else if s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r59, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r59, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm4, ivexm4, recEnv] at h <;> norm_num at h

theorem rubi1212r59_counterexample_complex : ¬ rubi1212r59.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1212r59.conditions rubi1212r59.body rubi1212r59.result rubi1212r59.integrals
  have hq : ∀ᶠ w in 𝓝 (1 : ℂ), 1 + w ^ 2 ≠ 0 := by
    have hc : ContinuousAt (fun w : ℂ => 1 + w ^ 2) 1 := by fun_prop
    exact hc.eventually_ne (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -2 else if s = "a" ∨ s = "c" ∨ s = "e" then 1 else if s = "m" then 2 else 0) (1 : ℂ) (by simp [rubi1212r59, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm4, ivexm4] <;> (try norm_num) <;> exact ⟨-4, ivm4⟩)
    (by filter_upwards [hq] with w hw2; simp [rubi1212r59, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm4, ivexm4, hw2])
    (fun h w => w * (((rubi1212r59.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then -2 else if s = "a" ∨ s = "c" ∨ s = "e" then 1 else if s = "m" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r59, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r59, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm4, ivexm4, recEnv] at h <;> norm_num at h

end OSR.IntegrationRec21
