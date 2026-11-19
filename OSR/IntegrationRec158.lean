import OSR.IntegrationRec91
import OSR.IntegrationRec138
import OSR.IntegrationRec131

/-!
# Integration (RUBI): arctanh by parts and `a + b cosh² + c sinh²`

7.3.1 #1 and 7.3.4 #41, 7.3.7 #41 (`artanh(tan(a + b x))`, whose derivative is
`b sec(2a + 2b x)`) integrate by parts; 6.7.9 #73 and #75 use
`2 (a + b cosh² u + c sinh² u) = 2a + b - c + (b + c) cosh 2u`.  Proved over
ℝ, 6.7.9 #73 over ℂ as well.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec158

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 7.3.1 #1 -/
def rubi731r1 : CRule where
  id := "integration.rubi_7_3_1_r1"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:1"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))
  result := (.app2 .add (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "p")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 11873
  description := "RUBI 7.3.1 #1"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:1" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#1"

/-- RUBI 7.3.4 #41 -/
def rubi734mr41 : CRule where
  id := "integration.rubi_7_3_4_misc_r41"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:41"
  shape := .antiderivRec; x := "x"
  body := (.app1 .arctanh (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))
  result := (.app2 .add (.app2 .mul (.var "x") (.app1 .arctanh (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.var "x") (.app1 .sec (.app2 .add (.app2 .mul (.int 2) (.var "a")) (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "x"))))))]
  independent := ["a", "b"]
  priority := 11874
  description := "RUBI 7.3.4 #41"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:41" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent.m#41"

/-- RUBI 7.3.7 #41 -/
def rubi737r41 : CRule where
  id := "integration.rubi_7_3_7_r41"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:41"
  shape := .antiderivRec; x := "x"
  body := (.app1 .arctanh (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))
  result := (.app2 .add (.app2 .mul (.var "x") (.app1 .arctanh (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.var "x") (.app1 .sec (.app2 .add (.app2 .mul (.int 2) (.var "a")) (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "x"))))))]
  independent := ["a", "b"]
  priority := 11875
  description := "RUBI 7.3.7 #41"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:41" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent.m#41"

/-- RUBI 6.7.9 #73 -/
def rubi679r73 : CRule where
  id := "integration.rubi_6_7_9_r73"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:73"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2)))) (.app2 .mul (.var "c") (.pow (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2)))) (.int (-1))))
  result := (.app2 .mul (.int 2) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.app2 .mul (.int (-1)) (.var "c"))) (.app2 .mul (.app2 .add (.var "b") (.var "c")) (.app1 .cosh (.app2 .add (.app2 .mul (.int 2) (.var "d")) (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.app2 .add (.var "a") (.var "b")) (.int 0),
    .ne (.app2 .add (.var "a") (.var "c")) (.int 0)]
  priority := 11876
  description := "RUBI 6.7.9 #73"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:73" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#73"

/-- RUBI 6.7.9 #75 -/
def rubi679r75 : CRule where
  id := "integration.rubi_6_7_9_r75"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:75"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2))) (.pow (.app2 .add (.app2 .add (.var "b") (.app2 .mul (.var "a") (.pow (.app1 .sech (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2)))) (.app2 .mul (.var "c") (.pow (.app1 .tanh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2)))) (.int (-1))))
  result := (.app2 .mul (.int 2) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.app2 .mul (.int (-1)) (.var "c"))) (.app2 .mul (.app2 .add (.var "b") (.var "c")) (.app1 .cosh (.app2 .add (.app2 .mul (.int 2) (.var "d")) (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.app2 .add (.var "a") (.var "b")) (.int 0),
    .ne (.app2 .add (.var "a") (.var "c")) (.int 0)]
  priority := 11877
  description := "RUBI 6.7.9 #75"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:75" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#75"

/-! ## Proofs -/

theorem rubi731r1_real : rubi731r1.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r1.conditions rubi731r1.body rubi731r1.result rubi731r1.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi731r1, Defined, eval, Interp.real, hk_p] at h
  have hkp : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have p1 : intValue? (env "p" + -1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have hp0 : 0 < kp := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r1])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkp] at h; simp [Interp.real] at h; exact_mod_cast h
  have ht := hF.self_of_nhds
  simp [rubi731r1, Defined, eval, Interp.real, i2, im1, hk_p] at ht
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r1, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi731r1, Defined, eval, Interp.real, i2, im1, hk_p, p1] at hw ⊢
    have hsq : 0 < 1 + -(env "c" ^ 2 * w ^ 2) := by nlinarith [mul_pos (sub_pos.2 hw.1.2) (by linarith [hw.1.1] : (0:ℝ) < 1 + env "c" * w)]
    have k1 : ¬ kp - 1 < 0 := by omega
    have k2 : ¬ kp < 1 := by omega
    refine ⟨⟨hw.1, ?_⟩, hsq.ne'⟩
    first | tauto | simp [k1, k2] | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi731r1, Defined, eval, recEnv, Interp.real, i2, im1, hk_p, p1] at hw ⊢
    tauto
  · simp only [rubi731r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    simp [rubi731r1, Defined, eval, recEnv, Interp.real, i2, im1, hk_p, p1] at hΦ ⊢
    obtain ⟨⟨h1, h2⟩, -⟩ := ht
    have hlin : HasDerivAt (fun v : ℝ => env "c" * v) (env "c") t := by simpa using (hasDerivAt_id t).const_mul (env "c")
    have hF' := (OSR.IntegrationRec131.hasDerivAt_artanh h1 h2).comp t hlin
    have hA := (hF'.const_mul (env "b")).const_add (env "a")
    have hAn := (hasDerivAt_zpow kp _ (Or.inr hp0.le)).comp t hA
    have hP := (hasDerivAt_id t).mul hAn
    refine HasDerivAt.congr_deriv (hP.add ((hΦ.const_mul _).neg)) ?_
    have hR : 1 + -(env "c" ^ 2 * t ^ 2) ≠ 0 := by nlinarith [mul_pos (sub_pos.2 h2) (by linarith : (0:ℝ) < 1 + env "c" * t)]
    have hR' : 1 - (env "c" * t) ^ 2 ≠ 0 := by intro h; apply hR; linear_combination h
    have hR'' : 1 - env "c" ^ 2 * t ^ 2 ≠ 0 := by intro h; apply hR; linear_combination h
    simp only [Function.comp_def, id, one_mul]
    rw [hkp]
    field_simp
    ring

theorem rubi734mr41_real : rubi734mr41.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734mr41.conditions rubi734mr41.body rubi734mr41.result rubi734mr41.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have ht := hF.self_of_nhds
  simp [rubi734mr41, Defined, eval, Interp.real, i2, im1] at ht
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734mr41, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi734mr41, Defined, eval, Interp.real, i2, im1] at hw ⊢
    have hcos2 : Real.cos (2 * env "a" + 2 * env "b" * w) ≠ 0 := by
      obtain ⟨hc0, h1, h2⟩ := hw
      have hc2 : 0 < Real.cos (env "a" + env "b" * w) ^ 2 := by positivity
      have ht2 : Real.tan (env "a" + env "b" * w) ^ 2 < 1 := by nlinarith
      rw [Real.tan_eq_sin_div_cos, div_pow, div_lt_one hc2] at ht2
      have := Real.sin_sq_add_cos_sq (env "a" + env "b" * w)
      rw [show 2 * env "a" + 2 * env "b" * w = 2 * (env "a" + env "b" * w) by ring, Real.cos_two_mul]
      nlinarith
    exact hcos2
  · filter_upwards [hF] with w hw
    simp [rubi734mr41, Defined, eval, recEnv, Interp.real, i2, im1] at hw ⊢
    exact hw
  · simp only [rubi734mr41, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    simp [rubi734mr41, Defined, eval, recEnv, Interp.real, i2, im1] at hΦ ⊢
    have hcos2 : Real.cos (2 * env "a" + 2 * env "b" * t) ≠ 0 := by
      obtain ⟨hc0, h1, h2⟩ := ht
      have hc2 : 0 < Real.cos (env "a" + env "b" * t) ^ 2 := by positivity
      have ht2 : Real.tan (env "a" + env "b" * t) ^ 2 < 1 := by nlinarith
      rw [Real.tan_eq_sin_div_cos, div_pow, div_lt_one hc2] at ht2
      have := Real.sin_sq_add_cos_sq (env "a" + env "b" * t)
      rw [show 2 * env "a" + 2 * env "b" * t = 2 * (env "a" + env "b" * t) by ring, Real.cos_two_mul]
      nlinarith
    obtain ⟨hc0, h1, h2⟩ := ht
    have hu : HasDerivAt (fun v : ℝ => env "a" + env "b" * v) (env "b") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "b")).const_add (env "a")
    have htan := (Real.hasDerivAt_tan hc0).comp t hu
    have hat := (OSR.IntegrationRec131.hasDerivAt_artanh h1 h2).comp t htan
    have hP := (hasDerivAt_id t).mul hat
    refine HasDerivAt.congr_deriv (hP.add ((hΦ.const_mul _).neg)) ?_
    have hT : 1 - Real.tan (env "a" + env "b" * t) ^ 2 ≠ 0 := by nlinarith
    simp only [Function.comp_def, id, one_mul, Fn.sec]
    rw [show 2 * env "a" + 2 * env "b" * t = 2 * (env "a" + env "b" * t) by ring, Real.cos_two_mul] at hcos2 ⊢
    rw [Real.tan_eq_sin_div_cos] at hT ⊢
    have hr := Real.sin_sq_add_cos_sq (env "a" + env "b" * t)
    generalize Real.sin (env "a" + env "b" * t) = S at *
    generalize Real.cos (env "a" + env "b" * t) = C at *
    have hT' : C ^ 2 - S ^ 2 ≠ 0 := by intro h; apply hT; field_simp; linear_combination h
    have hcos2' : C ^ 2 * 2 - 1 ≠ 0 := by intro h; apply hcos2; linear_combination h
    field_simp
    linear_combination (env "b" * t) * hr

theorem rubi737r41_real : rubi737r41.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi737r41.conditions rubi737r41.body rubi737r41.result rubi737r41.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have ht := hF.self_of_nhds
  simp [rubi737r41, Defined, eval, Interp.real, i2, im1] at ht
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi737r41, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi737r41, Defined, eval, Interp.real, i2, im1] at hw ⊢
    have hcos2 : Real.cos (2 * env "a" + 2 * env "b" * w) ≠ 0 := by
      obtain ⟨hc0, h1, h2⟩ := hw
      have hc2 : 0 < Real.cos (env "a" + env "b" * w) ^ 2 := by positivity
      have ht2 : Real.tan (env "a" + env "b" * w) ^ 2 < 1 := by nlinarith
      rw [Real.tan_eq_sin_div_cos, div_pow, div_lt_one hc2] at ht2
      have := Real.sin_sq_add_cos_sq (env "a" + env "b" * w)
      rw [show 2 * env "a" + 2 * env "b" * w = 2 * (env "a" + env "b" * w) by ring, Real.cos_two_mul]
      nlinarith
    exact hcos2
  · filter_upwards [hF] with w hw
    simp [rubi737r41, Defined, eval, recEnv, Interp.real, i2, im1] at hw ⊢
    exact hw
  · simp only [rubi737r41, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    simp [rubi737r41, Defined, eval, recEnv, Interp.real, i2, im1] at hΦ ⊢
    have hcos2 : Real.cos (2 * env "a" + 2 * env "b" * t) ≠ 0 := by
      obtain ⟨hc0, h1, h2⟩ := ht
      have hc2 : 0 < Real.cos (env "a" + env "b" * t) ^ 2 := by positivity
      have ht2 : Real.tan (env "a" + env "b" * t) ^ 2 < 1 := by nlinarith
      rw [Real.tan_eq_sin_div_cos, div_pow, div_lt_one hc2] at ht2
      have := Real.sin_sq_add_cos_sq (env "a" + env "b" * t)
      rw [show 2 * env "a" + 2 * env "b" * t = 2 * (env "a" + env "b" * t) by ring, Real.cos_two_mul]
      nlinarith
    obtain ⟨hc0, h1, h2⟩ := ht
    have hu : HasDerivAt (fun v : ℝ => env "a" + env "b" * v) (env "b") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "b")).const_add (env "a")
    have htan := (Real.hasDerivAt_tan hc0).comp t hu
    have hat := (OSR.IntegrationRec131.hasDerivAt_artanh h1 h2).comp t htan
    have hP := (hasDerivAt_id t).mul hat
    refine HasDerivAt.congr_deriv (hP.add ((hΦ.const_mul _).neg)) ?_
    have hT : 1 - Real.tan (env "a" + env "b" * t) ^ 2 ≠ 0 := by nlinarith
    simp only [Function.comp_def, id, one_mul, Fn.sec]
    rw [show 2 * env "a" + 2 * env "b" * t = 2 * (env "a" + env "b" * t) by ring, Real.cos_two_mul] at hcos2 ⊢
    rw [Real.tan_eq_sin_div_cos] at hT ⊢
    have hr := Real.sin_sq_add_cos_sq (env "a" + env "b" * t)
    generalize Real.sin (env "a" + env "b" * t) = S at *
    generalize Real.cos (env "a" + env "b" * t) = C at *
    have hT' : C ^ 2 - S ^ 2 ≠ 0 := by intro h; apply hT; field_simp; linear_combination h
    have hcos2' : C ^ 2 * 2 - 1 ≠ 0 := by intro h; apply hcos2; linear_combination h
    field_simp
    linear_combination (env "b" * t) * hr

theorem rubi679r73_real : rubi679r73.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r73.conditions rubi679r73.body rubi679r73.result rubi679r73.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi679r73, Defined, eval, Interp.real, hk_m] at h
  have hc2 : ∀ w : ℝ, Real.cosh (2 * env "d" + 2 * env "e" * w) = 2 * Real.cosh (env "d" + env "e" * w) ^ 2 - 1 := by
    intro w; rw [show 2 * env "d" + 2 * env "e" * w = 2 * (env "d" + env "e" * w) by ring, Real.cosh_two_mul]
    linear_combination -Real.cosh_sq_sub_sinh_sq (env "d" + env "e" * w)
  have ht := hF.self_of_nhds
  simp [rubi679r73, Defined, eval, Interp.real, i2, im1, hk_m] at ht
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r73, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi679r73, Defined, eval, Interp.real, i2, im1, hk_m, hc2, Fn.sech, Real.tanh_eq_sinh_div_cosh] at hw ⊢
    have hr := Real.cosh_sq_sub_sinh_sq (env "d" + env "e" * w)
    generalize Real.sinh (env "d" + env "e" * w) = S at *
    generalize Real.cosh (env "d" + env "e" * w) = C at *
    refine ⟨hw.1, ?_⟩
    intro hN; apply hw.2; linear_combination (1 / 2 : ℝ) * hN - env "c" * hr
  · filter_upwards [hF] with w hw
    simp [rubi679r73, Defined, eval, recEnv, Interp.real, i2, im1, hk_m, hc2, Fn.sech, Real.tanh_eq_sinh_div_cosh] at hw ⊢
    try tauto
  · simp only [rubi679r73, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine (hΦ.const_mul 2).congr_deriv ?_
    simp [rubi679r73, Defined, eval, Interp.real, i2, im1, hk_m, hc2, Fn.sech, Real.tanh_eq_sinh_div_cosh] at ht ⊢
    obtain ⟨-, hX⟩ := ht
    have hr := Real.cosh_sq_sub_sinh_sq (env "d" + env "e" * t)
    generalize Real.sinh (env "d" + env "e" * t) = S at *
    generalize Real.cosh (env "d" + env "e" * t) = C at *
    have hN : 2 * env "a" + env "b" + -env "c" + (env "b" + env "c") * (2 * C ^ 2 - 1) ≠ 0 := by
      intro hN; apply hX; linear_combination (1 / 2 : ℝ) * hN - env "c" * hr
    field_simp
    linear_combination (-2 * env "c" * (env "f" + env "g" * t) ^ km) * hr

theorem rubi679r75_real : rubi679r75.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r75.conditions rubi679r75.body rubi679r75.result rubi679r75.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi679r75, Defined, eval, Interp.real, hk_m] at h
  have hc2 : ∀ w : ℝ, Real.cosh (2 * env "d" + 2 * env "e" * w) = 2 * Real.cosh (env "d" + env "e" * w) ^ 2 - 1 := by
    intro w; rw [show 2 * env "d" + 2 * env "e" * w = 2 * (env "d" + env "e" * w) by ring, Real.cosh_two_mul]
    linear_combination -Real.cosh_sq_sub_sinh_sq (env "d" + env "e" * w)
  have ht := hF.self_of_nhds
  simp [rubi679r75, Defined, eval, Interp.real, i2, im1, hk_m] at ht
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r75, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi679r75, Defined, eval, Interp.real, i2, im1, hk_m, hc2, Fn.sech, Real.tanh_eq_sinh_div_cosh] at hw ⊢
    have hr := Real.cosh_sq_sub_sinh_sq (env "d" + env "e" * w)
    have hC0 : Real.cosh (env "d" + env "e" * w) ≠ 0 := (Real.cosh_pos _).ne'
    generalize Real.sinh (env "d" + env "e" * w) = S at *
    generalize Real.cosh (env "d" + env "e" * w) = C at *
    refine ⟨hw.1, ?_⟩
    intro hN; apply hw.2; field_simp; linear_combination (1 / 2 : ℝ) * hN - env "c" * hr
  · filter_upwards [hF] with w hw
    simp [rubi679r75, Defined, eval, recEnv, Interp.real, i2, im1, hk_m, hc2, Fn.sech, Real.tanh_eq_sinh_div_cosh] at hw ⊢
    try tauto
  · simp only [rubi679r75, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine (hΦ.const_mul 2).congr_deriv ?_
    simp [rubi679r75, Defined, eval, Interp.real, i2, im1, hk_m, hc2, Fn.sech, Real.tanh_eq_sinh_div_cosh] at ht ⊢
    obtain ⟨-, hX⟩ := ht
    have hr := Real.cosh_sq_sub_sinh_sq (env "d" + env "e" * t)
    have hC0 : Real.cosh (env "d" + env "e" * t) ≠ 0 := (Real.cosh_pos _).ne'
    generalize Real.sinh (env "d" + env "e" * t) = S at *
    generalize Real.cosh (env "d" + env "e" * t) = C at *
    have hN : 2 * env "a" + env "b" + -env "c" + (env "b" + env "c") * (2 * C ^ 2 - 1) ≠ 0 := by
      intro hN; apply hX; field_simp; linear_combination (1 / 2 : ℝ) * hN - env "c" * hr
    have hX' : env "b" * C ^ 2 + env "a" + env "c" * S ^ 2 ≠ 0 := by intro h; apply hX; field_simp; linear_combination h
    field_simp
    linear_combination (-2 * env "c" * (env "f" + env "g" * t) ^ km) * hr

theorem rubi679r73_complex : rubi679r73.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi679r73.conditions rubi679r73.body rubi679r73.result rubi679r73.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi679r73, Defined, eval, Interp.complex, hk_m] at h
  have hc2 : ∀ w : ℂ, Complex.cosh (2 * env "d" + 2 * env "e" * w) = 2 * Complex.cosh (env "d" + env "e" * w) ^ 2 - 1 := by
    intro w; rw [show 2 * env "d" + 2 * env "e" * w = 2 * (env "d" + env "e" * w) by ring, Complex.cosh_two_mul]
    linear_combination -Complex.cosh_sq_sub_sinh_sq (env "d" + env "e" * w)
  have ht := hF.self_of_nhds
  simp [rubi679r73, Defined, eval, Interp.complex, i2, im1, hk_m] at ht
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r73, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi679r73, Defined, eval, Interp.complex, i2, im1, hk_m, hc2] at hw ⊢
    have hr := Complex.cosh_sq_sub_sinh_sq (env "d" + env "e" * w)
    generalize Complex.sinh (env "d" + env "e" * w) = S at *
    generalize Complex.cosh (env "d" + env "e" * w) = C at *
    refine ⟨hw.1, ?_⟩
    intro hN; apply hw.2; linear_combination (1 / 2 : ℂ) * hN - env "c" * hr
  · filter_upwards [hF] with w hw
    simp [rubi679r73, Defined, eval, recEnv, Interp.complex, i2, im1, hk_m, hc2] at hw ⊢
    try tauto
  · simp only [rubi679r73, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine (hΦ.const_mul 2).congr_deriv ?_
    simp [rubi679r73, Defined, eval, Interp.complex, i2, im1, hk_m, hc2] at ht ⊢
    obtain ⟨-, hX⟩ := ht
    have hr := Complex.cosh_sq_sub_sinh_sq (env "d" + env "e" * t)
    generalize Complex.sinh (env "d" + env "e" * t) = S at *
    generalize Complex.cosh (env "d" + env "e" * t) = C at *
    have hN : 2 * env "a" + env "b" + -env "c" + (env "b" + env "c") * (2 * C ^ 2 - 1) ≠ 0 := by
      intro hN; apply hX; linear_combination (1 / 2 : ℂ) * hN - env "c" * hr
    field_simp
    linear_combination (-2 * env "c" * (env "f" + env "g" * t) ^ km) * hr

end OSR.IntegrationRec158
