import OSR.IntegrationRec91

/-!
# Integration (RUBI): `(f x)^m (a + b A(c x))^p/(d + e x)` split

`1/(d + e x) = 1/d - e x/(d (d + e x))`, with `(f x)^(m+1) = (f x)^m f x`; the
condition forces `d ≠ 0` (otherwise `e = 0` and the integrand is nowhere
defined).  Proved over ℝ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec140

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 7.3.4 #5 -/
def rubi734r5 : CRule where
  id := "integration.rubi_7_3_4_r5"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .mul (.var "d") (.var "f")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 11601
  description := "RUBI 7.3.4 #5"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:5" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#5"

/-- RUBI 7.3.1 #25 -/
def rubi731r25 : CRule where
  id := "integration.rubi_7_3_1_r25"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:25"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .mul (.var "d") (.var "f")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 11602
  description := "RUBI 7.3.1 #25"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:25" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#25"

/-- RUBI 5.3.4 #5 -/
def rubi534r5 : CRule where
  id := "integration.rubi_5_3_4_r5"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .mul (.var "d") (.var "f")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "e") (.int 2))) (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 11603
  description := "RUBI 5.3.4 #5"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:5" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#5"

/-! ## Proofs -/

theorem rubi734r5_real : rubi734r5.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r5.conditions rubi734r5.body rubi734r5.result rubi734r5.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi734r5, Defined, eval, Interp.real, hk_m, i2, im1] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi734r5, Defined, eval, Interp.real, hk_m, hk_p, i2, im1] at h
  have h_m : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  have h_p : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have hkm : km < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi734r5])
    simp [Cond.Holds, Defined, eval, Interp.real, h_m] at h; exact_mod_cast h
  have hkp : 0 < kp := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi734r5])
    simp [Cond.Holds, Defined, eval, Interp.real, h_p] at h; exact_mod_cast h
  have heq : env "e" ^ 2 = env "c" ^ 2 * env "d" ^ 2 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi734r5])
    simp [Cond.Holds, Defined, eval, Interp.real, i2] at h; linear_combination -h
  have em1 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi734r5.body →
      env "f" ≠ 0 ∧ w ≠ 0 ∧ env "d" + env "e" * w ≠ 0 ∧ -1 < env "c" * w ∧ env "c" * w < 1 := by
    intro w h
    simp [rubi734r5, Defined, eval, Interp.real, hk_m, hk_p, i2, im1, show km < 0 by omega, show ¬ kp < 0 by omega] at h
    first | tauto | (trace_state; sorry)
  obtain ⟨hf0, ht0, hde, -, -⟩ := hBody t hF.self_of_nhds
  have hd0 : env "d" ≠ 0 := by
    intro h0
    have he : env "e" = 0 := by
      have : env "e" ^ 2 = 0 := by rw [heq, h0]; ring
      exact pow_eq_zero_iff (by norm_num) |>.1 this
    apply hde; rw [h0, he]; ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734r5, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hb := hBody w hw
      simp [Defined, eval, Interp.real, hk_m, hk_p, em1, i2, im1, show ¬ kp < 0 by omega] at hw ⊢
      first | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi734r5, Defined, eval, recEnv, Interp.real, i2, im1, hd0, hf0]
  · simp only [rubi734r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi734r5.integrals.map (·.1)) Φ "x" w) rubi734r5.result) =
        fun w => 1 * (env "d")⁻¹ * Φ "I1" w + -1 * env "e" * (env "d" * env "f")⁻¹ * Φ "I2" w := by
      funext w; simp [rubi734r5, eval, recEnv, Interp.real, i2, im1]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi734r5, eval, Interp.real, hk_m, hk_p, em1, i2, im1]
    have hft : env "f" * t ≠ 0 := mul_ne_zero hf0 ht0
    rw [zpow_add_one₀ hft km]
    generalize (env "f" * t) ^ km = X
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)) ^ kp = P
    field_simp
    ring

theorem rubi731r25_real : rubi731r25.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r25.conditions rubi731r25.body rubi731r25.result rubi731r25.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi731r25, Defined, eval, Interp.real, hk_m, i2, im1] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi731r25, Defined, eval, Interp.real, hk_m, hk_p, i2, im1] at h
  have h_m : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  have h_p : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have hkm : km < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi731r25])
    simp [Cond.Holds, Defined, eval, Interp.real, h_m] at h; exact_mod_cast h
  have hkp : 0 < kp := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r25])
    simp [Cond.Holds, Defined, eval, Interp.real, h_p] at h; exact_mod_cast h
  have heq : env "e" ^ 2 = env "c" ^ 2 * env "d" ^ 2 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi731r25])
    simp [Cond.Holds, Defined, eval, Interp.real, i2] at h; linear_combination -h
  have em1 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r25.body →
      env "f" ≠ 0 ∧ w ≠ 0 ∧ env "d" + env "e" * w ≠ 0 ∧ -1 < env "c" * w ∧ env "c" * w < 1 := by
    intro w h
    simp [rubi731r25, Defined, eval, Interp.real, hk_m, hk_p, i2, im1, show km < 0 by omega, show ¬ kp < 0 by omega] at h
    first | tauto | (trace_state; sorry)
  obtain ⟨hf0, ht0, hde, -, -⟩ := hBody t hF.self_of_nhds
  have hd0 : env "d" ≠ 0 := by
    intro h0
    have he : env "e" = 0 := by
      have : env "e" ^ 2 = 0 := by rw [heq, h0]; ring
      exact pow_eq_zero_iff (by norm_num) |>.1 this
    apply hde; rw [h0, he]; ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r25, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hb := hBody w hw
      simp [Defined, eval, Interp.real, hk_m, hk_p, em1, i2, im1, show ¬ kp < 0 by omega] at hw ⊢
      first | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi731r25, Defined, eval, recEnv, Interp.real, i2, im1, hd0, hf0]
  · simp only [rubi731r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r25.integrals.map (·.1)) Φ "x" w) rubi731r25.result) =
        fun w => 1 * (env "d")⁻¹ * Φ "I1" w + -1 * env "e" * (env "d" * env "f")⁻¹ * Φ "I2" w := by
      funext w; simp [rubi731r25, eval, recEnv, Interp.real, i2, im1]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi731r25, eval, Interp.real, hk_m, hk_p, em1, i2, im1]
    have hft : env "f" * t ≠ 0 := mul_ne_zero hf0 ht0
    rw [zpow_add_one₀ hft km]
    generalize (env "f" * t) ^ km = X
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)) ^ kp = P
    field_simp
    ring

theorem rubi534r5_real : rubi534r5.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi534r5.conditions rubi534r5.body rubi534r5.result rubi534r5.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi534r5, Defined, eval, Interp.real, hk_m, i2, im1] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi534r5, Defined, eval, Interp.real, hk_m, hk_p, i2, im1] at h
  have h_m : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  have h_p : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have hkm : km < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi534r5])
    simp [Cond.Holds, Defined, eval, Interp.real, h_m] at h; exact_mod_cast h
  have hkp : 0 < kp := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi534r5])
    simp [Cond.Holds, Defined, eval, Interp.real, h_p] at h; exact_mod_cast h
  have heq : env "e" ^ 2 = -(env "c" ^ 2 * env "d" ^ 2) := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "e") (.int 2))) (.int 0)) (by simp [rubi534r5])
    simp [Cond.Holds, Defined, eval, Interp.real, i2] at h; linear_combination h
  have em1 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi534r5.body →
      env "f" ≠ 0 ∧ w ≠ 0 ∧ env "d" + env "e" * w ≠ 0 := by
    intro w h
    simp [rubi534r5, Defined, eval, Interp.real, hk_m, hk_p, i2, im1, show km < 0 by omega, show ¬ kp < 0 by omega] at h
    first | tauto | (trace_state; sorry)
  obtain ⟨hf0, ht0, hde⟩ := hBody t hF.self_of_nhds
  have hd0 : env "d" ≠ 0 := by
    intro h0
    have he : env "e" = 0 := by
      have : env "e" ^ 2 = 0 := by rw [heq, h0]; ring
      exact pow_eq_zero_iff (by norm_num) |>.1 this
    apply hde; rw [h0, he]; ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi534r5, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hb := hBody w hw
      simp [Defined, eval, Interp.real, hk_m, hk_p, em1, i2, im1, show ¬ kp < 0 by omega] at hw ⊢
      first | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi534r5, Defined, eval, recEnv, Interp.real, i2, im1, hd0, hf0]
  · simp only [rubi534r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi534r5.integrals.map (·.1)) Φ "x" w) rubi534r5.result) =
        fun w => 1 * (env "d")⁻¹ * Φ "I1" w + -1 * env "e" * (env "d" * env "f")⁻¹ * Φ "I2" w := by
      funext w; simp [rubi534r5, eval, recEnv, Interp.real, i2, im1]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi534r5, eval, Interp.real, hk_m, hk_p, em1, i2, im1]
    have hft : env "f" * t ≠ 0 := mul_ne_zero hf0 ht0
    rw [zpow_add_one₀ hft km]
    generalize (env "f" * t) ^ km = X
    generalize (env "a" + env "b" * Real.arctan (env "c" * t)) ^ kp = P
    field_simp
    ring


end OSR.IntegrationRec140
