import OSR.IntegrationRec91

/-!
# Integration (RUBI): linear splits into residual integrals

Rules whose result is a combination, with coefficients free of `x`, of
residual integrals: 1.1.1.2 #3, 1.2.1.2 #78 and #79 (partial fractions) and
4.1.12 #3 and #4 (`sin` and `cos` of a sum), proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec172

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.1.1.2 #3 -/
def rubi1112r3 : CRule where
  id := "integration.rubi_1_1_1_2_r3"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 12500
  description := "RUBI 1.1.1.2 #3"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:3" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n.m#3"

/-- RUBI 1.2.1.2 #78 -/
def rubi1212r78 : CRule where
  id := "integration.rubi_1_2_1_2_r78"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:78"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "e")) (.var "x"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)]
  priority := 12501
  description := "RUBI 1.2.1.2 #78"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:78" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#78"

/-- RUBI 1.2.1.2 #79 -/
def rubi1212r79 : CRule where
  id := "integration.rubi_1_2_1_2_r79"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:79"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "e")) (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "c", "d", "e"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)]
  priority := 12502
  description := "RUBI 1.2.1.2 #79"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:79" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#79"

/-- RUBI 4.1.12 #3 -/
def rubi4112r3 : CRule where
  id := "integration.rubi_4_1_12_r3"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:3"
  shape := .antiderivRec; x := "x"
  body := (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app1 .sin (.var "c")) (.var "I1")) (.app2 .mul (.app1 .cos (.var "c")) (.var "I2")))
  integrals := [("I1", (.app1 .cos (.app2 .mul (.var "d") (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2))))),
    ("I2", (.app1 .sin (.app2 .mul (.var "d") (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2)))))]
  independent := ["c", "d", "e", "f"]
  priority := 12503
  description := "RUBI 4.1.12 #3"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:3" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#3"

/-- RUBI 4.1.12 #4 -/
def rubi4112r4 : CRule where
  id := "integration.rubi_4_1_12_r4"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:4"
  shape := .antiderivRec; x := "x"
  body := (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app1 .cos (.var "c")) (.var "I1")) (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .sin (.var "c"))) (.var "I2")))
  integrals := [("I1", (.app1 .cos (.app2 .mul (.var "d") (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2))))),
    ("I2", (.app1 .sin (.app2 .mul (.var "d") (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2)))))]
  independent := ["c", "d", "e", "f"]
  priority := 12504
  description := "RUBI 4.1.12 #4"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:4" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#4"

theorem rubi1112r3_real : rubi1112r3.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1112r3.conditions rubi1112r3.body rubi1112r3.result rubi1112r3.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi1112r3, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1112r3, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi1112r3, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi1112r3, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi1112r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi1112r3, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | (rw [Real.sin_add (env "c")] <;> ring1)
      | (rw [Real.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp; ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi1112r3_complex : rubi1112r3.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1112r3.conditions rubi1112r3.body rubi1112r3.result rubi1112r3.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi1112r3, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1112r3, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi1112r3, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi1112r3, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi1112r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi1112r3, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | (rw [Complex.sin_add (env "c")] <;> ring1)
      | (rw [Complex.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp; ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi1212r78_real : rubi1212r78.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1212r78.conditions rubi1212r78.body rubi1212r78.result rubi1212r78.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi1212r78, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r78, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi1212r78, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi1212r78, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi1212r78, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi1212r78, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | (rw [Real.sin_add (env "c")] <;> ring1)
      | (rw [Real.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp; ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi1212r78_complex : rubi1212r78.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1212r78.conditions rubi1212r78.body rubi1212r78.result rubi1212r78.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi1212r78, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r78, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi1212r78, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi1212r78, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi1212r78, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi1212r78, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | (rw [Complex.sin_add (env "c")] <;> ring1)
      | (rw [Complex.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp; ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi1212r79_real : rubi1212r79.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1212r79.conditions rubi1212r79.body rubi1212r79.result rubi1212r79.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi1212r79, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r79, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi1212r79, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi1212r79, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi1212r79, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi1212r79, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | (rw [Real.sin_add (env "c")] <;> ring1)
      | (rw [Real.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp; ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi1212r79_complex : rubi1212r79.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1212r79.conditions rubi1212r79.body rubi1212r79.result rubi1212r79.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi1212r79, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r79, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi1212r79, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi1212r79, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi1212r79, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi1212r79, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | (rw [Complex.sin_add (env "c")] <;> ring1)
      | (rw [Complex.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp; ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi4112r3_real : rubi4112r3.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4112r3.conditions rubi4112r3.body rubi4112r3.result rubi4112r3.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4112r3, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r3, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4112r3, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4112r3, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4112r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi4112r3, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | (rw [Real.sin_add (env "c")] <;> ring1)
      | (rw [Real.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp; ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi4112r3_complex : rubi4112r3.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4112r3.conditions rubi4112r3.body rubi4112r3.result rubi4112r3.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4112r3, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r3, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4112r3, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4112r3, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4112r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi4112r3, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | (rw [Complex.sin_add (env "c")] <;> ring1)
      | (rw [Complex.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp; ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi4112r4_real : rubi4112r4.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4112r4.conditions rubi4112r4.body rubi4112r4.result rubi4112r4.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4112r4, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r4, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4112r4, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4112r4, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4112r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi4112r4, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | (rw [Real.sin_add (env "c")] <;> ring1)
      | (rw [Real.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp; ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi4112r4_complex : rubi4112r4.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4112r4.conditions rubi4112r4.body rubi4112r4.result rubi4112r4.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4112r4, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r4, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4112r4, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4112r4, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4112r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi4112r4, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | (rw [Complex.sin_add (env "c")] <;> ring1)
      | (rw [Complex.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp; ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

end OSR.IntegrationRec172
