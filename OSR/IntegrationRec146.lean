import OSR.IntegrationRec91

/-!
# Integration (RUBI): `sec² u/(b + a sec² u + c tan² u) = 2/(2a + b + c + (b - c) cos 2u)`

Multiplying by `cos² u` (or `sin² u` for the csc/cot forms) gives
`b cos² u + c sin² u + a`, which is half of `2a + b + c + (b - c) cos 2u`.
4.7.9 #72 to #75 are proved over ℝ (sec and csc have no complex interpretation
in the fragment).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec146

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 4.7.9 #72 -/
def rubi479r72 : CRule where
  id := "integration.rubi_4_7_9_r72"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:72"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app1 .sec (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2))) (.pow (.app2 .add (.var "b") (.app2 .mul (.var "c") (.pow (.app1 .tan (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2)))) (.int (-1))))
  result := (.app2 .mul (.int 2) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "b") (.var "c")) (.app2 .mul (.app2 .add (.var "b") (.app2 .mul (.int (-1)) (.var "c"))) (.app1 .cos (.app2 .add (.app2 .mul (.int 2) (.var "d")) (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.var "x")))))) (.int (-1)))))]
  independent := ["b", "c", "d", "e", "f", "g", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0)]
  priority := 11810
  description := "RUBI 4.7.9 #72"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:72" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#72"

/-- RUBI 4.7.9 #73 -/
def rubi479r73 : CRule where
  id := "integration.rubi_4_7_9_r73"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:73"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app1 .sec (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2))) (.pow (.app2 .add (.app2 .add (.var "b") (.app2 .mul (.var "a") (.pow (.app1 .sec (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2)))) (.app2 .mul (.var "c") (.pow (.app1 .tan (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2)))) (.int (-1))))
  result := (.app2 .mul (.int 2) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.var "c")) (.app2 .mul (.app2 .add (.var "b") (.app2 .mul (.int (-1)) (.var "c"))) (.app1 .cos (.app2 .add (.app2 .mul (.int 2) (.var "d")) (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.app2 .add (.var "a") (.var "b")) (.int 0),
    .ne (.app2 .add (.var "a") (.var "c")) (.int 0)]
  priority := 11811
  description := "RUBI 4.7.9 #73"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:73" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#73"

/-- RUBI 4.7.9 #74 -/
def rubi479r74 : CRule where
  id := "integration.rubi_4_7_9_r74"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:74"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app1 .csc (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "b") (.pow (.app1 .cot (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2)))) (.int (-1))))
  result := (.app2 .mul (.int 2) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "b") (.var "c")) (.app2 .mul (.app2 .add (.var "b") (.app2 .mul (.int (-1)) (.var "c"))) (.app1 .cos (.app2 .add (.app2 .mul (.int 2) (.var "d")) (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.var "x")))))) (.int (-1)))))]
  independent := ["b", "c", "d", "e", "f", "g", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0)]
  priority := 11812
  description := "RUBI 4.7.9 #74"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:74" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#74"

/-- RUBI 4.7.9 #75 -/
def rubi479r75 : CRule where
  id := "integration.rubi_4_7_9_r75"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:75"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app1 .csc (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2))) (.pow (.app2 .add (.app2 .add (.var "c") (.app2 .mul (.var "b") (.pow (.app1 .cot (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2)))) (.app2 .mul (.var "a") (.pow (.app1 .csc (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2)))) (.int (-1))))
  result := (.app2 .mul (.int 2) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.var "c")) (.app2 .mul (.app2 .add (.var "b") (.app2 .mul (.int (-1)) (.var "c"))) (.app1 .cos (.app2 .add (.app2 .mul (.int 2) (.var "d")) (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.app2 .add (.var "a") (.var "b")) (.int 0),
    .ne (.app2 .add (.var "a") (.var "c")) (.int 0)]
  priority := 11813
  description := "RUBI 4.7.9 #75"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:75" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#75"

/-! ## Proofs -/

theorem rubi479r72_real : rubi479r72.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r72.conditions rubi479r72.body rubi479r72.result rubi479r72.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hc2 : ∀ w : ℝ, Real.cos (2 * env "d" + 2 * env "e" * w) = 2 * Real.cos (env "d" + env "e" * w) ^ 2 - 1 := by
    intro w; rw [show 2 * env "d" + 2 * env "e" * w = 2 * (env "d" + env "e" * w) by ring, Real.cos_two_mul]
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi479r72, Defined, eval, Interp.real, hk_m] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r72, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi479r72, Defined, eval, Interp.real, i2, im1, hk_m, hc2, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at hw ⊢
    have hSC := Real.sin_sq_add_cos_sq (env "d" + env "e" * w)
    generalize Real.sin (env "d" + env "e" * w) = S at *
    generalize Real.cos (env "d" + env "e" * w) = C at *
    have hSUB : S ^ 2 = 1 - C ^ 2 := by linarith
    obtain ⟨⟨hf, hZ⟩, -, hX⟩ := hw
    simp only [div_pow, hSUB] at hX ⊢
    have hZ2 : C ^ 2 ≠ 0 := pow_ne_zero 2 hZ
    have key : env "b" + env "c" * ((1 - C ^ 2) / C ^ 2) = (env "b" + env "c" + (env "b" + -env "c") * (2 * C ^ 2 - 1)) / (2 * (C ^ 2)) := by field_simp; ring
    rw [key] at hX
    have hN : env "b" + env "c" + (env "b" + -env "c") * (2 * C ^ 2 - 1) ≠ 0 := by intro h; apply hX; rw [h, zero_div]
    exact ⟨hf, hN⟩
  · exact Eventually.of_forall fun w => by simp [rubi479r72, Defined, eval, recEnv]
  · simp only [rubi479r72, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi479r72.integrals.map (·.1)) Φ "x" w) rubi479r72.result) = fun w => 2 * Φ "I1" w := by
      funext w; simp [rubi479r72, eval, recEnv]
    rw [hfun]
    have ht := hF.self_of_nhds
    refine (hΦ.const_mul 2).congr_deriv ?_
    simp [rubi479r72, Defined, eval, Interp.real, i2, im1, hk_m, hc2, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at ht ⊢
    have hSC := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    generalize Real.sin (env "d" + env "e" * t) = S at *
    generalize Real.cos (env "d" + env "e" * t) = C at *
    have hSUB : S ^ 2 = 1 - C ^ 2 := by linarith
    obtain ⟨⟨hf, hZ⟩, -, hX⟩ := ht
    simp only [div_pow, hSUB] at hX ⊢
    have hZ2 : C ^ 2 ≠ 0 := pow_ne_zero 2 hZ
    have key : env "b" + env "c" * ((1 - C ^ 2) / C ^ 2) = (env "b" + env "c" + (env "b" + -env "c") * (2 * C ^ 2 - 1)) / (2 * (C ^ 2)) := by field_simp; ring
    rw [key] at hX
    have hN : env "b" + env "c" + (env "b" + -env "c") * (2 * C ^ 2 - 1) ≠ 0 := by intro h; apply hX; rw [h, zero_div]
    rw [key]
    field_simp

theorem rubi479r73_real : rubi479r73.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r73.conditions rubi479r73.body rubi479r73.result rubi479r73.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hc2 : ∀ w : ℝ, Real.cos (2 * env "d" + 2 * env "e" * w) = 2 * Real.cos (env "d" + env "e" * w) ^ 2 - 1 := by
    intro w; rw [show 2 * env "d" + 2 * env "e" * w = 2 * (env "d" + env "e" * w) by ring, Real.cos_two_mul]
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi479r73, Defined, eval, Interp.real, hk_m] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r73, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi479r73, Defined, eval, Interp.real, i2, im1, hk_m, hc2, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at hw ⊢
    have hSC := Real.sin_sq_add_cos_sq (env "d" + env "e" * w)
    generalize Real.sin (env "d" + env "e" * w) = S at *
    generalize Real.cos (env "d" + env "e" * w) = C at *
    have hSUB : S ^ 2 = 1 - C ^ 2 := by linarith
    obtain ⟨⟨hf, hZ⟩, -, hX⟩ := hw
    simp only [div_pow, hSUB] at hX ⊢
    have hZ2 : C ^ 2 ≠ 0 := pow_ne_zero 2 hZ
    have key : env "b" + env "a" * (C ^ 2)⁻¹ + env "c" * ((1 - C ^ 2) / C ^ 2) = (2 * env "a" + env "b" + env "c" + (env "b" + -env "c") * (2 * C ^ 2 - 1)) / (2 * (C ^ 2)) := by field_simp; ring
    rw [key] at hX
    have hN : 2 * env "a" + env "b" + env "c" + (env "b" + -env "c") * (2 * C ^ 2 - 1) ≠ 0 := by intro h; apply hX; rw [h, zero_div]
    exact ⟨hf, hN⟩
  · exact Eventually.of_forall fun w => by simp [rubi479r73, Defined, eval, recEnv]
  · simp only [rubi479r73, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi479r73.integrals.map (·.1)) Φ "x" w) rubi479r73.result) = fun w => 2 * Φ "I1" w := by
      funext w; simp [rubi479r73, eval, recEnv]
    rw [hfun]
    have ht := hF.self_of_nhds
    refine (hΦ.const_mul 2).congr_deriv ?_
    simp [rubi479r73, Defined, eval, Interp.real, i2, im1, hk_m, hc2, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at ht ⊢
    have hSC := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    generalize Real.sin (env "d" + env "e" * t) = S at *
    generalize Real.cos (env "d" + env "e" * t) = C at *
    have hSUB : S ^ 2 = 1 - C ^ 2 := by linarith
    obtain ⟨⟨hf, hZ⟩, -, hX⟩ := ht
    simp only [div_pow, hSUB] at hX ⊢
    have hZ2 : C ^ 2 ≠ 0 := pow_ne_zero 2 hZ
    have key : env "b" + env "a" * (C ^ 2)⁻¹ + env "c" * ((1 - C ^ 2) / C ^ 2) = (2 * env "a" + env "b" + env "c" + (env "b" + -env "c") * (2 * C ^ 2 - 1)) / (2 * (C ^ 2)) := by field_simp; ring
    rw [key] at hX
    have hN : 2 * env "a" + env "b" + env "c" + (env "b" + -env "c") * (2 * C ^ 2 - 1) ≠ 0 := by intro h; apply hX; rw [h, zero_div]
    rw [key]
    field_simp

theorem rubi479r74_real : rubi479r74.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r74.conditions rubi479r74.body rubi479r74.result rubi479r74.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hc2 : ∀ w : ℝ, Real.cos (2 * env "d" + 2 * env "e" * w) = 2 * Real.cos (env "d" + env "e" * w) ^ 2 - 1 := by
    intro w; rw [show 2 * env "d" + 2 * env "e" * w = 2 * (env "d" + env "e" * w) by ring, Real.cos_two_mul]
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi479r74, Defined, eval, Interp.real, hk_m] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r74, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi479r74, Defined, eval, Interp.real, i2, im1, hk_m, hc2, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at hw ⊢
    have hSC := Real.sin_sq_add_cos_sq (env "d" + env "e" * w)
    generalize Real.sin (env "d" + env "e" * w) = S at *
    generalize Real.cos (env "d" + env "e" * w) = C at *
    have hSUB : C ^ 2 = 1 - S ^ 2 := by linarith
    obtain ⟨⟨hf, hZ⟩, -, hX⟩ := hw
    simp only [div_pow, hSUB] at hX ⊢
    have hZ2 : S ^ 2 ≠ 0 := pow_ne_zero 2 hZ
    have key : env "c" + env "b" * ((1 - S ^ 2) / S ^ 2) = (env "b" + env "c" + (env "b" + -env "c") * (2 * (1 - S ^ 2) - 1)) / (2 * (S ^ 2)) := by field_simp; ring
    rw [key] at hX
    have hN : env "b" + env "c" + (env "b" + -env "c") * (2 * (1 - S ^ 2) - 1) ≠ 0 := by intro h; apply hX; rw [h, zero_div]
    exact ⟨hf, hN⟩
  · exact Eventually.of_forall fun w => by simp [rubi479r74, Defined, eval, recEnv]
  · simp only [rubi479r74, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi479r74.integrals.map (·.1)) Φ "x" w) rubi479r74.result) = fun w => 2 * Φ "I1" w := by
      funext w; simp [rubi479r74, eval, recEnv]
    rw [hfun]
    have ht := hF.self_of_nhds
    refine (hΦ.const_mul 2).congr_deriv ?_
    simp [rubi479r74, Defined, eval, Interp.real, i2, im1, hk_m, hc2, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at ht ⊢
    have hSC := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    generalize Real.sin (env "d" + env "e" * t) = S at *
    generalize Real.cos (env "d" + env "e" * t) = C at *
    have hSUB : C ^ 2 = 1 - S ^ 2 := by linarith
    obtain ⟨⟨hf, hZ⟩, -, hX⟩ := ht
    simp only [div_pow, hSUB] at hX ⊢
    have hZ2 : S ^ 2 ≠ 0 := pow_ne_zero 2 hZ
    have key : env "c" + env "b" * ((1 - S ^ 2) / S ^ 2) = (env "b" + env "c" + (env "b" + -env "c") * (2 * (1 - S ^ 2) - 1)) / (2 * (S ^ 2)) := by field_simp; ring
    rw [key] at hX
    have hN : env "b" + env "c" + (env "b" + -env "c") * (2 * (1 - S ^ 2) - 1) ≠ 0 := by intro h; apply hX; rw [h, zero_div]
    rw [key]
    field_simp

theorem rubi479r75_real : rubi479r75.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r75.conditions rubi479r75.body rubi479r75.result rubi479r75.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hc2 : ∀ w : ℝ, Real.cos (2 * env "d" + 2 * env "e" * w) = 2 * Real.cos (env "d" + env "e" * w) ^ 2 - 1 := by
    intro w; rw [show 2 * env "d" + 2 * env "e" * w = 2 * (env "d" + env "e" * w) by ring, Real.cos_two_mul]
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi479r75, Defined, eval, Interp.real, hk_m] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r75, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi479r75, Defined, eval, Interp.real, i2, im1, hk_m, hc2, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at hw ⊢
    have hSC := Real.sin_sq_add_cos_sq (env "d" + env "e" * w)
    generalize Real.sin (env "d" + env "e" * w) = S at *
    generalize Real.cos (env "d" + env "e" * w) = C at *
    have hSUB : C ^ 2 = 1 - S ^ 2 := by linarith
    obtain ⟨⟨hf, hZ⟩, -, hX⟩ := hw
    simp only [div_pow, hSUB] at hX ⊢
    have hZ2 : S ^ 2 ≠ 0 := pow_ne_zero 2 hZ
    have key : env "c" + env "b" * ((1 - S ^ 2) / S ^ 2) + env "a" * (S ^ 2)⁻¹ = (2 * env "a" + env "b" + env "c" + (env "b" + -env "c") * (2 * (1 - S ^ 2) - 1)) / (2 * (S ^ 2)) := by field_simp; ring
    rw [key] at hX
    have hN : 2 * env "a" + env "b" + env "c" + (env "b" + -env "c") * (2 * (1 - S ^ 2) - 1) ≠ 0 := by intro h; apply hX; rw [h, zero_div]
    exact ⟨hf, hN⟩
  · exact Eventually.of_forall fun w => by simp [rubi479r75, Defined, eval, recEnv]
  · simp only [rubi479r75, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi479r75.integrals.map (·.1)) Φ "x" w) rubi479r75.result) = fun w => 2 * Φ "I1" w := by
      funext w; simp [rubi479r75, eval, recEnv]
    rw [hfun]
    have ht := hF.self_of_nhds
    refine (hΦ.const_mul 2).congr_deriv ?_
    simp [rubi479r75, Defined, eval, Interp.real, i2, im1, hk_m, hc2, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at ht ⊢
    have hSC := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    generalize Real.sin (env "d" + env "e" * t) = S at *
    generalize Real.cos (env "d" + env "e" * t) = C at *
    have hSUB : C ^ 2 = 1 - S ^ 2 := by linarith
    obtain ⟨⟨hf, hZ⟩, -, hX⟩ := ht
    simp only [div_pow, hSUB] at hX ⊢
    have hZ2 : S ^ 2 ≠ 0 := pow_ne_zero 2 hZ
    have key : env "c" + env "b" * ((1 - S ^ 2) / S ^ 2) + env "a" * (S ^ 2)⁻¹ = (2 * env "a" + env "b" + env "c" + (env "b" + -env "c") * (2 * (1 - S ^ 2) - 1)) / (2 * (S ^ 2)) := by field_simp; ring
    rw [key] at hX
    have hN : 2 * env "a" + env "b" + env "c" + (env "b" + -env "c") * (2 * (1 - S ^ 2) - 1) ≠ 0 := by intro h; apply hX; rw [h, zero_div]
    rw [key]
    field_simp

end OSR.IntegrationRec146
