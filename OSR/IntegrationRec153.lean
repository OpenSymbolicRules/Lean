import OSR.IntegrationRec91

/-!
# Integration (RUBI): products `F(a + b x) G(c + d x)` with `b² = d²`

With `d = ± b` the arguments differ (or add up) by a constant, and the addition
formulas split the product.  6.7.9 #86 to #89 and 4.7.9 #96, #97 are proved
over ℝ (sech, csch, coth, sec and csc have no complex interpretation in the
fragment).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec153

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 6.7.9 #86 -/
def rubi679r86 : CRule where
  id := "integration.rubi_6_7_9_r86"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:86"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .sech (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .csch (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "d") (.int (-1)))))) (.var "I1")) (.app2 .mul (.app1 .csch (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "b") (.int (-1))))) (.var "I2")))
  integrals := [("I1", (.app1 .tanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))),
    ("I2", (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 11849
  description := "RUBI 6.7.9 #86"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:86" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#86"

/-- RUBI 6.7.9 #87 -/
def rubi679r87 : CRule where
  id := "integration.rubi_6_7_9_r87"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:87"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .csch (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.app2 .add (.app2 .mul (.app1 .csch (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "b") (.int (-1))))) (.var "I1")) (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .csch (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "d") (.int (-1)))))) (.var "I2")))
  integrals := [("I1", (.app1 .coth (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))),
    ("I2", (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 11850
  description := "RUBI 6.7.9 #87"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:87" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#87"

/-- RUBI 6.7.9 #88 -/
def rubi679r88 : CRule where
  id := "integration.rubi_6_7_9_r88"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:88"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .tanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "x")) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "d") (.int (-1)))) (.app1 .cosh (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "d") (.int (-1)))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app1 .sech (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 11851
  description := "RUBI 6.7.9 #88"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:88" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#88"

/-- RUBI 6.7.9 #89 -/
def rubi679r89 : CRule where
  id := "integration.rubi_6_7_9_r89"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:89"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .coth (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "x")) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app1 .cosh (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "d") (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app1 .csch (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 11852
  description := "RUBI 6.7.9 #89"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:89" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#89"

/-- RUBI 4.7.9 #96 -/
def rubi479r96 : CRule where
  id := "integration.rubi_4_7_9_r96"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:96"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "x")) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.pow (.var "d") (.int (-1)))) (.app1 .cos (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "d") (.int (-1)))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app1 .sec (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app1 .sec (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 11853
  description := "RUBI 4.7.9 #96"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:96" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#96"

/-- RUBI 4.7.9 #97 -/
def rubi479r97 : CRule where
  id := "integration.rubi_4_7_9_r97"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:97"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .cot (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app1 .cot (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "x")) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app1 .cos (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "d") (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app1 .csc (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app1 .csc (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 11854
  description := "RUBI 4.7.9 #97"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:97" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#97"

/-! ## Proofs -/

theorem rubi679r86_real : rubi679r86.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r86.conditions rubi679r86.body rubi679r86.result rubi679r86.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hbd : env "b" ^ 2 = env "d" ^ 2 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi679r86])
    simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at h; linear_combination h
  have hne : env "b" * env "c" - env "a" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi679r86])
    simp [Cond.Holds, Defined, eval, Interp.real] at h
    intro h0; apply h; linear_combination h0
  have hb0 : env "b" ≠ 0 := by
    intro h0; apply hne; rw [h0] at hbd ⊢; have : env "d" = 0 := by nlinarith
    rw [this]; ring
  have hd0 : env "d" ≠ 0 := by
    intro h0; apply hne; rw [h0] at hbd ⊢; have : env "b" = 0 := by nlinarith
    rw [this]; ring
  have hK1 : (env "b" * env "c" + -(env "a" * env "d")) * (env "d")⁻¹ ≠ 0 :=
    mul_ne_zero (by intro h; apply hne; linear_combination h) (inv_ne_zero hd0)
  have hK2 : (env "b" * env "c" + -(env "a" * env "d")) * (env "b")⁻¹ ≠ 0 :=
    mul_ne_zero (by intro h; apply hne; linear_combination h) (inv_ne_zero hb0)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r86, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi679r86, Defined, eval, Interp.real, i2, im1, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢ <;>
    first | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi679r86, Defined, eval, recEnv, Interp.real, i2, im1, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢
    first | tauto | (trace_state; sorry)
  · simp only [rubi679r86, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi679r86, Defined, eval, recEnv, Interp.real, i2, im1, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)) ?_
    have hdb : env "d" = env "b" ∨ env "d" = -env "b" := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hbd with h | h
      · exact Or.inl h.symm
      · right; linear_combination h
    rcases hdb with hdb | hdb
    · try rw [hdb] at ht
      rw [hdb]
      have hδ : env "c" - env "a" ≠ 0 := by intro h; apply hne; rw [hdb]; linear_combination env "b" * h
      try rw [show (env "b" * env "c" + -(env "a" * env "b")) * (env "b")⁻¹ = env "c" - env "a" by field_simp; ring]
      rw [show env "c" + env "b" * t = (env "a" + env "b" * t) + (env "c" - env "a") by ring] at *
      have nC : Real.cosh (env "a" + env "b" * t) ≠ 0 := (Real.cosh_pos _).ne'
      have nCv : Real.cosh ((env "a" + env "b" * t) + (env "c" - env "a")) ≠ 0 := (Real.cosh_pos _).ne'
      have nD : Real.sinh (env "c" - env "a") ≠ 0 := by
        first | (intro h; rw [Real.sinh_eq_zero] at h; exact hδ h) | (intro h; exact absurd h (by tauto)) | exact fun _ => trivial | skip
      simp only [Real.sinh_add (env "a" + env "b" * t) (env "c" - env "a"), Real.cosh_add (env "a" + env "b" * t) (env "c" - env "a")] at *
      have hr := Real.cosh_sq_sub_sinh_sq (env "a" + env "b" * t)
      have hrD := Real.cosh_sq_sub_sinh_sq (env "c" - env "a")
      generalize Real.sinh (env "a" + env "b" * t) = S at *
      generalize Real.cosh (env "a" + env "b" * t) = C at *
      generalize Real.sinh (env "c" - env "a") = SD at *
      generalize Real.cosh (env "c" - env "a") = CD at *
      have hD0 : C * CD + SD * S ≠ 0 := by
        intro h; first | exact nCv (by linear_combination h) | exact nSv (by linear_combination h) | exact nCv (by linear_combination -h) | exact nSv (by linear_combination -h)
      field_simp
      linear_combination (SD) * hr + (0) * hrD
    · try rw [hdb] at ht
      rw [hdb]
      have hσ : env "a" + env "c" ≠ 0 := by intro h; apply hne; rw [hdb]; linear_combination env "b" * h
      try rw [show (env "b" * env "c" + -(env "a" * -env "b")) * (-env "b")⁻¹ = -(env "a" + env "c") by field_simp; ring]
      try rw [show (env "b" * env "c" + -(env "a" * -env "b")) * (env "b")⁻¹ = env "a" + env "c" by field_simp; ring]
      rw [show env "c" + -env "b" * t = (env "a" + env "c") - (env "a" + env "b" * t) by ring] at *
      have nC : Real.cosh (env "a" + env "b" * t) ≠ 0 := (Real.cosh_pos _).ne'
      have nCv : Real.cosh ((env "a" + env "c") - (env "a" + env "b" * t)) ≠ 0 := (Real.cosh_pos _).ne'
      have nD : Real.sinh (env "a" + env "c") ≠ 0 := by intro h; rw [Real.sinh_eq_zero] at h; exact hσ h
      simp only [Real.sinh_sub (env "a" + env "c") (env "a" + env "b" * t), Real.cosh_sub (env "a" + env "c") (env "a" + env "b" * t), Real.sinh_neg, Real.cosh_neg] at *
      have hr := Real.cosh_sq_sub_sinh_sq (env "a" + env "b" * t)
      have hrD := Real.cosh_sq_sub_sinh_sq (env "a" + env "c")
      generalize Real.sinh (env "a" + env "b" * t) = S at *
      generalize Real.cosh (env "a" + env "b" * t) = C at *
      generalize Real.sinh (env "a" + env "c") = SD at *
      generalize Real.cosh (env "a" + env "c") = CD at *
      have hD0 : C * CD - SD * S ≠ 0 := by
        intro h; first | exact nCv (by linear_combination h) | exact nSv (by linear_combination h) | exact nCv (by linear_combination -h) | exact nSv (by linear_combination -h)
      field_simp
      linear_combination (SD) * hr + (0) * hrD

theorem rubi679r87_real : rubi679r87.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r87.conditions rubi679r87.body rubi679r87.result rubi679r87.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hbd : env "b" ^ 2 = env "d" ^ 2 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi679r87])
    simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at h; linear_combination h
  have hne : env "b" * env "c" - env "a" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi679r87])
    simp [Cond.Holds, Defined, eval, Interp.real] at h
    intro h0; apply h; linear_combination h0
  have hb0 : env "b" ≠ 0 := by
    intro h0; apply hne; rw [h0] at hbd ⊢; have : env "d" = 0 := by nlinarith
    rw [this]; ring
  have hd0 : env "d" ≠ 0 := by
    intro h0; apply hne; rw [h0] at hbd ⊢; have : env "b" = 0 := by nlinarith
    rw [this]; ring
  have hK1 : (env "b" * env "c" + -(env "a" * env "d")) * (env "d")⁻¹ ≠ 0 :=
    mul_ne_zero (by intro h; apply hne; linear_combination h) (inv_ne_zero hd0)
  have hK2 : (env "b" * env "c" + -(env "a" * env "d")) * (env "b")⁻¹ ≠ 0 :=
    mul_ne_zero (by intro h; apply hne; linear_combination h) (inv_ne_zero hb0)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r87, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi679r87, Defined, eval, Interp.real, i2, im1, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢ <;>
    first | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi679r87, Defined, eval, recEnv, Interp.real, i2, im1, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢
    first | tauto | (trace_state; sorry)
  · simp only [rubi679r87, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi679r87, Defined, eval, recEnv, Interp.real, i2, im1, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)) ?_
    have hdb : env "d" = env "b" ∨ env "d" = -env "b" := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hbd with h | h
      · exact Or.inl h.symm
      · right; linear_combination h
    rcases hdb with hdb | hdb
    · try rw [hdb] at ht
      rw [hdb]
      have hδ : env "c" - env "a" ≠ 0 := by intro h; apply hne; rw [hdb]; linear_combination env "b" * h
      try rw [show (env "b" * env "c" + -(env "a" * env "b")) * (env "b")⁻¹ = env "c" - env "a" by field_simp; ring]
      rw [show env "c" + env "b" * t = (env "a" + env "b" * t) + (env "c" - env "a") by ring] at *
      have nC : Real.cosh (env "a" + env "b" * t) ≠ 0 := (Real.cosh_pos _).ne'
      have nCv : Real.cosh ((env "a" + env "b" * t) + (env "c" - env "a")) ≠ 0 := (Real.cosh_pos _).ne'
      have nS : Real.sinh (env "a" + env "b" * t) ≠ 0 := by intro h; rw [Real.sinh_eq_zero] at h; tauto
      have nSv : Real.sinh ((env "a" + env "b" * t) + (env "c" - env "a")) ≠ 0 := by intro h; rw [Real.sinh_eq_zero] at h; apply ht.2; linear_combination h
      have nD : Real.sinh (env "c" - env "a") ≠ 0 := by
        first | (intro h; rw [Real.sinh_eq_zero] at h; exact hδ h) | (intro h; exact absurd h (by tauto)) | exact fun _ => trivial | skip
      simp only [Real.sinh_add (env "a" + env "b" * t) (env "c" - env "a"), Real.cosh_add (env "a" + env "b" * t) (env "c" - env "a")] at *
      have hr := Real.cosh_sq_sub_sinh_sq (env "a" + env "b" * t)
      have hrD := Real.cosh_sq_sub_sinh_sq (env "c" - env "a")
      generalize Real.sinh (env "a" + env "b" * t) = S at *
      generalize Real.cosh (env "a" + env "b" * t) = C at *
      generalize Real.sinh (env "c" - env "a") = SD at *
      generalize Real.cosh (env "c" - env "a") = CD at *
      have hD0 : S * CD + SD * C ≠ 0 := by
        intro h; first | exact nCv (by linear_combination h) | exact nSv (by linear_combination h) | exact nCv (by linear_combination -h) | exact nSv (by linear_combination -h)
      field_simp
      linear_combination (SD) * hr + (0) * hrD
    · try rw [hdb] at ht
      rw [hdb]
      have hσ : env "a" + env "c" ≠ 0 := by intro h; apply hne; rw [hdb]; linear_combination env "b" * h
      try rw [show (env "b" * env "c" + -(env "a" * -env "b")) * (-env "b")⁻¹ = -(env "a" + env "c") by field_simp; ring]
      try rw [show (env "b" * env "c" + -(env "a" * -env "b")) * (env "b")⁻¹ = env "a" + env "c" by field_simp; ring]
      rw [show env "c" + -env "b" * t = (env "a" + env "c") - (env "a" + env "b" * t) by ring] at *
      have nC : Real.cosh (env "a" + env "b" * t) ≠ 0 := (Real.cosh_pos _).ne'
      have nCv : Real.cosh ((env "a" + env "c") - (env "a" + env "b" * t)) ≠ 0 := (Real.cosh_pos _).ne'
      have nS : Real.sinh (env "a" + env "b" * t) ≠ 0 := by intro h; rw [Real.sinh_eq_zero] at h; tauto
      have nSv : Real.sinh ((env "a" + env "c") - (env "a" + env "b" * t)) ≠ 0 := by intro h; rw [Real.sinh_eq_zero] at h; apply ht.2; linear_combination h
      have nD : Real.sinh (env "a" + env "c") ≠ 0 := by intro h; rw [Real.sinh_eq_zero] at h; exact hσ h
      simp only [Real.sinh_sub (env "a" + env "c") (env "a" + env "b" * t), Real.cosh_sub (env "a" + env "c") (env "a" + env "b" * t), Real.sinh_neg, Real.cosh_neg] at *
      have hr := Real.cosh_sq_sub_sinh_sq (env "a" + env "b" * t)
      have hrD := Real.cosh_sq_sub_sinh_sq (env "a" + env "c")
      generalize Real.sinh (env "a" + env "b" * t) = S at *
      generalize Real.cosh (env "a" + env "b" * t) = C at *
      generalize Real.sinh (env "a" + env "c") = SD at *
      generalize Real.cosh (env "a" + env "c") = CD at *
      have hD0 : SD * C - S * CD ≠ 0 := by
        intro h; first | exact nCv (by linear_combination h) | exact nSv (by linear_combination h) | exact nCv (by linear_combination -h) | exact nSv (by linear_combination -h)
      field_simp
      linear_combination (SD) * hr + (0) * hrD

theorem rubi679r88_real : rubi679r88.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r88.conditions rubi679r88.body rubi679r88.result rubi679r88.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hbd : env "b" ^ 2 = env "d" ^ 2 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi679r88])
    simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at h; linear_combination h
  have hne : env "b" * env "c" - env "a" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi679r88])
    simp [Cond.Holds, Defined, eval, Interp.real] at h
    intro h0; apply h; linear_combination h0
  have hb0 : env "b" ≠ 0 := by
    intro h0; apply hne; rw [h0] at hbd ⊢; have : env "d" = 0 := by nlinarith
    rw [this]; ring
  have hd0 : env "d" ≠ 0 := by
    intro h0; apply hne; rw [h0] at hbd ⊢; have : env "b" = 0 := by nlinarith
    rw [this]; ring
  have hK1 : (env "b" * env "c" + -(env "a" * env "d")) * (env "d")⁻¹ ≠ 0 :=
    mul_ne_zero (by intro h; apply hne; linear_combination h) (inv_ne_zero hd0)
  have hK2 : (env "b" * env "c" + -(env "a" * env "d")) * (env "b")⁻¹ ≠ 0 :=
    mul_ne_zero (by intro h; apply hne; linear_combination h) (inv_ne_zero hb0)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r88, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi679r88, Defined, eval, Interp.real, i2, im1, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢ <;>
    first | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi679r88, Defined, eval, recEnv, Interp.real, i2, im1, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢
    first | tauto | (trace_state; sorry)
  · simp only [rubi679r88, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi679r88, Defined, eval, recEnv, Interp.real, i2, im1, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at ht hΦ ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (((hasDerivAt_id t).const_mul _).mul_const _).add ((hΦ.const_mul _).neg)
        | exact (((hasDerivAt_id t).const_mul _).mul_const _).add (hΦ.const_mul _)
        | exact ((((hasDerivAt_id t).const_mul _).mul_const _).neg).add (hΦ.const_mul _)) ?_
    have hdb : env "d" = env "b" ∨ env "d" = -env "b" := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hbd with h | h
      · exact Or.inl h.symm
      · right; linear_combination h
    rcases hdb with hdb | hdb
    · try rw [hdb] at ht
      rw [hdb]
      have hδ : env "c" - env "a" ≠ 0 := by intro h; apply hne; rw [hdb]; linear_combination env "b" * h
      try rw [show (env "b" * env "c" + -(env "a" * env "b")) * (env "b")⁻¹ = env "c" - env "a" by field_simp; ring]
      rw [show env "c" + env "b" * t = (env "a" + env "b" * t) + (env "c" - env "a") by ring] at *
      have nC : Real.cosh (env "a" + env "b" * t) ≠ 0 := (Real.cosh_pos _).ne'
      have nCv : Real.cosh ((env "a" + env "b" * t) + (env "c" - env "a")) ≠ 0 := (Real.cosh_pos _).ne'
      have nD : Real.sinh (env "c" - env "a") ≠ 0 := by
        first | (intro h; rw [Real.sinh_eq_zero] at h; exact hδ h) | (intro h; exact absurd h (by tauto)) | exact fun _ => trivial | skip
      simp only [Real.sinh_add (env "a" + env "b" * t) (env "c" - env "a"), Real.cosh_add (env "a" + env "b" * t) (env "c" - env "a")] at *
      have hr := Real.cosh_sq_sub_sinh_sq (env "a" + env "b" * t)
      have hrD := Real.cosh_sq_sub_sinh_sq (env "c" - env "a")
      generalize Real.sinh (env "a" + env "b" * t) = S at *
      generalize Real.cosh (env "a" + env "b" * t) = C at *
      generalize Real.sinh (env "c" - env "a") = SD at *
      generalize Real.cosh (env "c" - env "a") = CD at *
      have hD0 : CD * C + S * SD ≠ 0 := by
        intro h; first | exact nCv (by linear_combination h) | exact nSv (by linear_combination h) | exact nCv (by linear_combination -h) | exact nSv (by linear_combination -h)
      field_simp
      linear_combination (CD) * hr + (0) * hrD
    · try rw [hdb] at ht
      rw [hdb]
      have hσ : env "a" + env "c" ≠ 0 := by intro h; apply hne; rw [hdb]; linear_combination env "b" * h
      try rw [show (env "b" * env "c" + -(env "a" * -env "b")) * (-env "b")⁻¹ = -(env "a" + env "c") by field_simp; ring]
      try rw [show (env "b" * env "c" + -(env "a" * -env "b")) * (env "b")⁻¹ = env "a" + env "c" by field_simp; ring]
      rw [show env "c" + -env "b" * t = (env "a" + env "c") - (env "a" + env "b" * t) by ring] at *
      have nC : Real.cosh (env "a" + env "b" * t) ≠ 0 := (Real.cosh_pos _).ne'
      have nCv : Real.cosh ((env "a" + env "c") - (env "a" + env "b" * t)) ≠ 0 := (Real.cosh_pos _).ne'
      have nD : Real.sinh (env "a" + env "c") ≠ 0 := by intro h; rw [Real.sinh_eq_zero] at h; exact hσ h
      simp only [Real.sinh_sub (env "a" + env "c") (env "a" + env "b" * t), Real.cosh_sub (env "a" + env "c") (env "a" + env "b" * t), Real.sinh_neg, Real.cosh_neg] at *
      have hr := Real.cosh_sq_sub_sinh_sq (env "a" + env "b" * t)
      have hrD := Real.cosh_sq_sub_sinh_sq (env "a" + env "c")
      generalize Real.sinh (env "a" + env "b" * t) = S at *
      generalize Real.cosh (env "a" + env "b" * t) = C at *
      generalize Real.sinh (env "a" + env "c") = SD at *
      generalize Real.cosh (env "a" + env "c") = CD at *
      field_simp
      linear_combination (-CD) * hr + (0) * hrD

theorem rubi679r89_real : rubi679r89.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r89.conditions rubi679r89.body rubi679r89.result rubi679r89.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hbd : env "b" ^ 2 = env "d" ^ 2 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi679r89])
    simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at h; linear_combination h
  have hne : env "b" * env "c" - env "a" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi679r89])
    simp [Cond.Holds, Defined, eval, Interp.real] at h
    intro h0; apply h; linear_combination h0
  have hb0 : env "b" ≠ 0 := by
    intro h0; apply hne; rw [h0] at hbd ⊢; have : env "d" = 0 := by nlinarith
    rw [this]; ring
  have hd0 : env "d" ≠ 0 := by
    intro h0; apply hne; rw [h0] at hbd ⊢; have : env "b" = 0 := by nlinarith
    rw [this]; ring
  have hK1 : (env "b" * env "c" + -(env "a" * env "d")) * (env "d")⁻¹ ≠ 0 :=
    mul_ne_zero (by intro h; apply hne; linear_combination h) (inv_ne_zero hd0)
  have hK2 : (env "b" * env "c" + -(env "a" * env "d")) * (env "b")⁻¹ ≠ 0 :=
    mul_ne_zero (by intro h; apply hne; linear_combination h) (inv_ne_zero hb0)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r89, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi679r89, Defined, eval, Interp.real, i2, im1, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢ <;>
    first | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi679r89, Defined, eval, recEnv, Interp.real, i2, im1, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢
    first | tauto | (trace_state; sorry)
  · simp only [rubi679r89, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi679r89, Defined, eval, recEnv, Interp.real, i2, im1, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at ht hΦ ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (((hasDerivAt_id t).const_mul _).mul_const _).add ((hΦ.const_mul _).neg)
        | exact (((hasDerivAt_id t).const_mul _).mul_const _).add (hΦ.const_mul _)
        | exact ((((hasDerivAt_id t).const_mul _).mul_const _).neg).add (hΦ.const_mul _)) ?_
    have hdb : env "d" = env "b" ∨ env "d" = -env "b" := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hbd with h | h
      · exact Or.inl h.symm
      · right; linear_combination h
    rcases hdb with hdb | hdb
    · try rw [hdb] at ht
      rw [hdb]
      have hδ : env "c" - env "a" ≠ 0 := by intro h; apply hne; rw [hdb]; linear_combination env "b" * h
      try rw [show (env "b" * env "c" + -(env "a" * env "b")) * (env "b")⁻¹ = env "c" - env "a" by field_simp; ring]
      rw [show env "c" + env "b" * t = (env "a" + env "b" * t) + (env "c" - env "a") by ring] at *
      have nC : Real.cosh (env "a" + env "b" * t) ≠ 0 := (Real.cosh_pos _).ne'
      have nCv : Real.cosh ((env "a" + env "b" * t) + (env "c" - env "a")) ≠ 0 := (Real.cosh_pos _).ne'
      have nS : Real.sinh (env "a" + env "b" * t) ≠ 0 := by intro h; rw [Real.sinh_eq_zero] at h; tauto
      have nSv : Real.sinh ((env "a" + env "b" * t) + (env "c" - env "a")) ≠ 0 := by intro h; rw [Real.sinh_eq_zero] at h; apply ht.2; linear_combination h
      have nD : Real.sinh (env "c" - env "a") ≠ 0 := by
        first | (intro h; rw [Real.sinh_eq_zero] at h; exact hδ h) | (intro h; exact absurd h (by tauto)) | exact fun _ => trivial | skip
      simp only [Real.sinh_add (env "a" + env "b" * t) (env "c" - env "a"), Real.cosh_add (env "a" + env "b" * t) (env "c" - env "a")] at *
      have hr := Real.cosh_sq_sub_sinh_sq (env "a" + env "b" * t)
      have hrD := Real.cosh_sq_sub_sinh_sq (env "c" - env "a")
      generalize Real.sinh (env "a" + env "b" * t) = S at *
      generalize Real.cosh (env "a" + env "b" * t) = C at *
      generalize Real.sinh (env "c" - env "a") = SD at *
      generalize Real.cosh (env "c" - env "a") = CD at *
      have hD0 : CD * S + C * SD ≠ 0 := by
        intro h; first | exact nCv (by linear_combination h) | exact nSv (by linear_combination h) | exact nCv (by linear_combination -h) | exact nSv (by linear_combination -h)
      field_simp
      linear_combination (-CD) * hr + (0) * hrD
    · try rw [hdb] at ht
      rw [hdb]
      have hσ : env "a" + env "c" ≠ 0 := by intro h; apply hne; rw [hdb]; linear_combination env "b" * h
      try rw [show (env "b" * env "c" + -(env "a" * -env "b")) * (-env "b")⁻¹ = -(env "a" + env "c") by field_simp; ring]
      try rw [show (env "b" * env "c" + -(env "a" * -env "b")) * (env "b")⁻¹ = env "a" + env "c" by field_simp; ring]
      rw [show env "c" + -env "b" * t = (env "a" + env "c") - (env "a" + env "b" * t) by ring] at *
      have nC : Real.cosh (env "a" + env "b" * t) ≠ 0 := (Real.cosh_pos _).ne'
      have nCv : Real.cosh ((env "a" + env "c") - (env "a" + env "b" * t)) ≠ 0 := (Real.cosh_pos _).ne'
      have nS : Real.sinh (env "a" + env "b" * t) ≠ 0 := by intro h; rw [Real.sinh_eq_zero] at h; tauto
      have nSv : Real.sinh ((env "a" + env "c") - (env "a" + env "b" * t)) ≠ 0 := by intro h; rw [Real.sinh_eq_zero] at h; apply ht.2; linear_combination h
      have nD : Real.sinh (env "a" + env "c") ≠ 0 := by intro h; rw [Real.sinh_eq_zero] at h; exact hσ h
      simp only [Real.sinh_sub (env "a" + env "c") (env "a" + env "b" * t), Real.cosh_sub (env "a" + env "c") (env "a" + env "b" * t), Real.sinh_neg, Real.cosh_neg] at *
      have hr := Real.cosh_sq_sub_sinh_sq (env "a" + env "b" * t)
      have hrD := Real.cosh_sq_sub_sinh_sq (env "a" + env "c")
      generalize Real.sinh (env "a" + env "b" * t) = S at *
      generalize Real.cosh (env "a" + env "b" * t) = C at *
      generalize Real.sinh (env "a" + env "c") = SD at *
      generalize Real.cosh (env "a" + env "c") = CD at *
      field_simp
      linear_combination (-CD) * hr + (0) * hrD

theorem rubi479r96_real : rubi479r96.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r96.conditions rubi479r96.body rubi479r96.result rubi479r96.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hbd : env "b" ^ 2 = env "d" ^ 2 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi479r96])
    simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at h; linear_combination h
  have hne : env "b" * env "c" - env "a" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi479r96])
    simp [Cond.Holds, Defined, eval, Interp.real] at h
    intro h0; apply h; linear_combination h0
  have hb0 : env "b" ≠ 0 := by
    intro h0; apply hne; rw [h0] at hbd ⊢; have : env "d" = 0 := by nlinarith
    rw [this]; ring
  have hd0 : env "d" ≠ 0 := by
    intro h0; apply hne; rw [h0] at hbd ⊢; have : env "b" = 0 := by nlinarith
    rw [this]; ring
  have hK1 : (env "b" * env "c" + -(env "a" * env "d")) * (env "d")⁻¹ ≠ 0 :=
    mul_ne_zero (by intro h; apply hne; linear_combination h) (inv_ne_zero hd0)
  have hK2 : (env "b" * env "c" + -(env "a" * env "d")) * (env "b")⁻¹ ≠ 0 :=
    mul_ne_zero (by intro h; apply hne; linear_combination h) (inv_ne_zero hb0)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r96, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi479r96, Defined, eval, Interp.real, i2, im1, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at hw ⊢ <;>
    first | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi479r96, Defined, eval, recEnv, Interp.real, i2, im1, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at hw ⊢
    first | tauto | (trace_state; sorry)
  · simp only [rubi479r96, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi479r96, Defined, eval, recEnv, Interp.real, i2, im1, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at ht hΦ ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (((hasDerivAt_id t).const_mul _).mul_const _).add ((hΦ.const_mul _).neg)
        | exact (((hasDerivAt_id t).const_mul _).mul_const _).add (hΦ.const_mul _)
        | exact ((((hasDerivAt_id t).const_mul _).mul_const _).neg).add (hΦ.const_mul _)) ?_
    have hdb : env "d" = env "b" ∨ env "d" = -env "b" := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hbd with h | h
      · exact Or.inl h.symm
      · right; linear_combination h
    rcases hdb with hdb | hdb
    · try rw [hdb] at ht
      rw [hdb]
      have hδ : env "c" - env "a" ≠ 0 := by intro h; apply hne; rw [hdb]; linear_combination env "b" * h
      try rw [show (env "b" * env "c" + -(env "a" * env "b")) * (env "b")⁻¹ = env "c" - env "a" by field_simp; ring]
      rw [show env "c" + env "b" * t = (env "a" + env "b" * t) + (env "c" - env "a") by ring] at *
      have nC : Real.cos (env "a" + env "b" * t) ≠ 0 := ht.1
      have nCv : Real.cos ((env "a" + env "b" * t) + (env "c" - env "a")) ≠ 0 := by have := ht.2; rwa [show ((env "a" + env "b" * t) + (env "c" - env "a")) = (env "a" + env "b" * t) + (env "c" - env "a") by ring] at this
      simp only [Real.sin_add (env "a" + env "b" * t) (env "c" - env "a"), Real.cos_add (env "a" + env "b" * t) (env "c" - env "a")] at *
      have hr := Real.sin_sq_add_cos_sq (env "a" + env "b" * t)
      have hrD := Real.sin_sq_add_cos_sq (env "c" - env "a")
      generalize Real.sin (env "a" + env "b" * t) = S at *
      generalize Real.cos (env "a" + env "b" * t) = C at *
      generalize Real.sin (env "c" - env "a") = SD at *
      generalize Real.cos (env "c" - env "a") = CD at *
      have hD0 : CD * C - S * SD ≠ 0 := by
        intro h; first | exact nCv (by linear_combination h) | exact nSv (by linear_combination h) | exact nCv (by linear_combination -h) | exact nSv (by linear_combination -h)
      field_simp
      linear_combination (-CD) * hr + (0) * hrD
    · try rw [hdb] at ht
      rw [hdb]
      have hσ : env "a" + env "c" ≠ 0 := by intro h; apply hne; rw [hdb]; linear_combination env "b" * h
      try rw [show (env "b" * env "c" + -(env "a" * -env "b")) * (-env "b")⁻¹ = -(env "a" + env "c") by field_simp; ring]
      try rw [show (env "b" * env "c" + -(env "a" * -env "b")) * (env "b")⁻¹ = env "a" + env "c" by field_simp; ring]
      rw [show env "c" + -env "b" * t = (env "a" + env "c") - (env "a" + env "b" * t) by ring] at *
      have nC : Real.cos (env "a" + env "b" * t) ≠ 0 := ht.1
      have nCv : Real.cos ((env "a" + env "c") - (env "a" + env "b" * t)) ≠ 0 := by have := ht.2; rwa [show ((env "a" + env "c") - (env "a" + env "b" * t)) = (env "a" + env "c") - (env "a" + env "b" * t) by ring] at this
      simp only [Real.sin_sub (env "a" + env "c") (env "a" + env "b" * t), Real.cos_sub (env "a" + env "c") (env "a" + env "b" * t), Real.sin_neg, Real.cos_neg] at *
      have hr := Real.sin_sq_add_cos_sq (env "a" + env "b" * t)
      have hrD := Real.sin_sq_add_cos_sq (env "a" + env "c")
      generalize Real.sin (env "a" + env "b" * t) = S at *
      generalize Real.cos (env "a" + env "b" * t) = C at *
      generalize Real.sin (env "a" + env "c") = SD at *
      generalize Real.cos (env "a" + env "c") = CD at *
      field_simp
      linear_combination (CD) * hr + (0) * hrD

theorem rubi479r97_real : rubi479r97.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r97.conditions rubi479r97.body rubi479r97.result rubi479r97.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hbd : env "b" ^ 2 = env "d" ^ 2 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi479r97])
    simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at h; linear_combination h
  have hne : env "b" * env "c" - env "a" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi479r97])
    simp [Cond.Holds, Defined, eval, Interp.real] at h
    intro h0; apply h; linear_combination h0
  have hb0 : env "b" ≠ 0 := by
    intro h0; apply hne; rw [h0] at hbd ⊢; have : env "d" = 0 := by nlinarith
    rw [this]; ring
  have hd0 : env "d" ≠ 0 := by
    intro h0; apply hne; rw [h0] at hbd ⊢; have : env "b" = 0 := by nlinarith
    rw [this]; ring
  have hK1 : (env "b" * env "c" + -(env "a" * env "d")) * (env "d")⁻¹ ≠ 0 :=
    mul_ne_zero (by intro h; apply hne; linear_combination h) (inv_ne_zero hd0)
  have hK2 : (env "b" * env "c" + -(env "a" * env "d")) * (env "b")⁻¹ ≠ 0 :=
    mul_ne_zero (by intro h; apply hne; linear_combination h) (inv_ne_zero hb0)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r97, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi479r97, Defined, eval, Interp.real, i2, im1, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at hw ⊢ <;>
    first | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi479r97, Defined, eval, recEnv, Interp.real, i2, im1, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at hw ⊢
    first | tauto | (trace_state; sorry)
  · simp only [rubi479r97, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi479r97, Defined, eval, recEnv, Interp.real, i2, im1, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at ht hΦ ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (((hasDerivAt_id t).const_mul _).mul_const _).add ((hΦ.const_mul _).neg)
        | exact (((hasDerivAt_id t).const_mul _).mul_const _).add (hΦ.const_mul _)
        | exact ((((hasDerivAt_id t).const_mul _).mul_const _).neg).add (hΦ.const_mul _)) ?_
    have hdb : env "d" = env "b" ∨ env "d" = -env "b" := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hbd with h | h
      · exact Or.inl h.symm
      · right; linear_combination h
    rcases hdb with hdb | hdb
    · try rw [hdb] at ht
      rw [hdb]
      have hδ : env "c" - env "a" ≠ 0 := by intro h; apply hne; rw [hdb]; linear_combination env "b" * h
      try rw [show (env "b" * env "c" + -(env "a" * env "b")) * (env "b")⁻¹ = env "c" - env "a" by field_simp; ring]
      rw [show env "c" + env "b" * t = (env "a" + env "b" * t) + (env "c" - env "a") by ring] at *
      have nS : Real.sin (env "a" + env "b" * t) ≠ 0 := ht.1
      have nSv : Real.sin ((env "a" + env "b" * t) + (env "c" - env "a")) ≠ 0 := by have := ht.2; rwa [show ((env "a" + env "b" * t) + (env "c" - env "a")) = (env "a" + env "b" * t) + (env "c" - env "a") by ring] at this
      simp only [Real.sin_add (env "a" + env "b" * t) (env "c" - env "a"), Real.cos_add (env "a" + env "b" * t) (env "c" - env "a")] at *
      have hr := Real.sin_sq_add_cos_sq (env "a" + env "b" * t)
      have hrD := Real.sin_sq_add_cos_sq (env "c" - env "a")
      generalize Real.sin (env "a" + env "b" * t) = S at *
      generalize Real.cos (env "a" + env "b" * t) = C at *
      generalize Real.sin (env "c" - env "a") = SD at *
      generalize Real.cos (env "c" - env "a") = CD at *
      have hD0 : CD * S + C * SD ≠ 0 := by
        intro h; first | exact nCv (by linear_combination h) | exact nSv (by linear_combination h) | exact nCv (by linear_combination -h) | exact nSv (by linear_combination -h)
      field_simp
      linear_combination (-CD) * hr + (0) * hrD
    · try rw [hdb] at ht
      rw [hdb]
      have hσ : env "a" + env "c" ≠ 0 := by intro h; apply hne; rw [hdb]; linear_combination env "b" * h
      try rw [show (env "b" * env "c" + -(env "a" * -env "b")) * (-env "b")⁻¹ = -(env "a" + env "c") by field_simp; ring]
      try rw [show (env "b" * env "c" + -(env "a" * -env "b")) * (env "b")⁻¹ = env "a" + env "c" by field_simp; ring]
      rw [show env "c" + -env "b" * t = (env "a" + env "c") - (env "a" + env "b" * t) by ring] at *
      have nS : Real.sin (env "a" + env "b" * t) ≠ 0 := ht.1
      have nSv : Real.sin ((env "a" + env "c") - (env "a" + env "b" * t)) ≠ 0 := by have := ht.2; rwa [show ((env "a" + env "c") - (env "a" + env "b" * t)) = (env "a" + env "c") - (env "a" + env "b" * t) by ring] at this
      simp only [Real.sin_sub (env "a" + env "c") (env "a" + env "b" * t), Real.cos_sub (env "a" + env "c") (env "a" + env "b" * t), Real.sin_neg, Real.cos_neg] at *
      have hr := Real.sin_sq_add_cos_sq (env "a" + env "b" * t)
      have hrD := Real.sin_sq_add_cos_sq (env "a" + env "c")
      generalize Real.sin (env "a" + env "b" * t) = S at *
      generalize Real.cos (env "a" + env "b" * t) = C at *
      generalize Real.sin (env "a" + env "c") = SD at *
      generalize Real.cos (env "a" + env "c") = CD at *
      field_simp
      linear_combination (-CD) * hr + (0) * hrD

end OSR.IntegrationRec153
